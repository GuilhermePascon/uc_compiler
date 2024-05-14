import argparse
import pathlib
import sys
from typing import List, Tuple
from uc.uc_ast import FuncDef, Node
from uc.uc_block import CFG, BasicBlock, ConditionBlock, EmitBlocks, format_instruction
from uc.uc_code import CodeGenerator
from uc.uc_interpreter import Interpreter
from uc.uc_parser import UCParser
from uc.uc_sema import NodeVisitor, Visitor
import pdb


class DataFlow(NodeVisitor):
    def __init__(self, viewcfg: bool):
        # flag to show the optimized control flow graph
        self.viewcfg: bool = viewcfg
        # list of code instructions after optimizations
        self.code: List[Tuple[str]] = []

        self.DEFS = dict()
        self.GEN = dict()
        self.KILL = dict()
        self.RD_OUT = dict()
        self.RD_IN = dict()
        self.USE = dict()
        self.DEF = dict()
        self.LV_OUT = dict()
        self.LV_IN = dict()
        # Reference to each block object
        self.block_nodes = dict()

        self.assign_ops = {
            "add",
            "and",
            "call",
            "div",
            "elem",
            "eq",
            "ge",
            "get",
            "gt",
            "le",
            "literal",
            "load",
            "store",
            "lt",
            "mod",
            "mul",
            "ne",
            "not",
            "or",
            "sub",
        }
        # target is 4th pos
        self.assign_ops_4len = {"elem", "add", "sub", "div", "mod"}

        self.bin_ops = {
            "add": lambda x, y: x + y,
            "sub": lambda x, y: x - y,
            "mul": lambda x, y: x * y,
            "div": lambda x, y: x / y,
            "mod": lambda x, y: x % y,
            "lt": lambda x, y: 1 if x < y else 0,
            "le": lambda x, y: 1 if x <= y else 0,
            "ge": lambda x, y: 1 if x >= y else 0,
            "gt": lambda x, y: 1 if x > y else 0,
            "eq": lambda x, y: 1 if x == y else 0,
            "ne": lambda x, y: 1 if x != y else 0,
        }

        # define ops that use variables for Liveness Analysis
        self.mem_ops = {"load", "store"}
        self.vector_ops = {"elem"}
        self.relational_ops = {"lt", "le", "ge", "gt", "eq", "ne", "and", "or", "not"}
        self.unary_ops = {"not"}
        self.branch_ops = {"cbranch"}
        self.func_builtin_ops = {"return", "print", "param"}

        # TODO

    def show(self, buf=sys.stdout):
        _str = ""
        for i, _code in enumerate(self.code):
            _str += f"{i} " + format_instruction(_code) + "\n"
        buf.write(_str)

    def get_target(self, inst):
        return inst[-1]

    def appendOptimizedCode(self, cfg):
        bb = EmitBlocks()
        bb.visit(cfg)
        for _code in bb.code:
            self.code.append(_code)

    def buildRD_blocks(self, block, visited_blocks=[]):
        # Keys are var names, value is a list of insts where it was assigned

        if block is not None and block.label not in visited_blocks:
            for i, inst in enumerate(block.instructions):
                inst_prefix = inst[0].split("_")[0]
                if inst_prefix in self.assign_ops:
                    var_name = self.get_target(inst)
                    inst_label = (block.label, i)
                    if var_name in self.DEFS.keys():
                        self.DEFS[var_name].add(inst_label)
                    else:
                        self.DEFS[var_name] = set()
                        self.DEFS[var_name].add(inst_label)
            visited_blocks.append(block.label)

            if isinstance(block, BasicBlock):
                self.buildRD_blocks(block.branch, visited_blocks)
            else:
                # Conditional block
                self.buildRD_blocks(block.taken, visited_blocks)
                self.buildRD_blocks(block.fall_through, visited_blocks)

    def computeRD_gen_kill(self, block, visited_blocks=[]):
        if block is not None and block.label not in visited_blocks:
            for i, inst in enumerate(block.instructions):
                if block.label not in self.KILL.keys():
                    self.GEN[block.label] = set()
                    self.KILL[block.label] = set()
                inst_prefix = inst[0].split("_")[0]
                if inst_prefix in self.assign_ops:
                    var_name = self.get_target(inst)
                    inst_label = (block.label, i)
                    self.GEN[block.label].add(inst_label)
                    self.KILL[block.label] = (
                        self.KILL[block.label] | self.DEFS[var_name]
                    )

            if block.label in self.KILL:
                self.KILL[block.label] = self.KILL[block.label] - self.GEN[block.label]
            else:
                self.GEN[block.label] = set()
                self.KILL[block.label] = set()

            visited_blocks.append(block.label)

            if isinstance(block, BasicBlock):
                self.computeRD_gen_kill(block.branch, visited_blocks)
            else:
                # Conditional block
                self.computeRD_gen_kill(block.taken, visited_blocks)
                self.computeRD_gen_kill(block.fall_through, visited_blocks)

    def start_empty_outset(self, block):
        """Set all blocks out set to empty set, recursively"""
        if block is not None and block.label not in self.RD_OUT.keys():
            self.RD_OUT[block.label] = set()
            self.block_nodes[block.label] = block
            if isinstance(block, BasicBlock):
                self.start_empty_outset(block.branch)
            else:
                # Conditional block
                self.start_empty_outset(block.taken)
                self.start_empty_outset(block.fall_through)

    def computeRD_in_out(self, orig_block):
        self.start_empty_outset(orig_block)

        changed = list(self.RD_OUT.keys()).copy()

        while len(changed) > 0:
            b_label = changed[0]
            del changed[0]

            self.RD_IN[b_label] = set()
            for p in self.block_nodes[b_label].predecessors:
                self.RD_IN[b_label] = self.RD_IN[b_label] | self.RD_OUT[p.label]

            oldout = self.RD_OUT[b_label].copy()
            self.RD_OUT[b_label] = self.GEN[b_label] | (
                self.RD_IN[b_label] - self.KILL[b_label]
            )

            if oldout != self.RD_OUT[b_label]:
                if (
                    isinstance(self.block_nodes[b_label], BasicBlock)
                    and self.block_nodes[b_label].branch is not None
                    and self.block_nodes[b_label].branch.label not in changed
                ):
                    changed.append(self.block_nodes[b_label].branch.label)
                elif isinstance(self.block_nodes[b_label], ConditionBlock):
                    if (
                        self.block_nodes[b_label].taken is not None
                        and self.block_nodes[b_label].taken.label not in changed
                    ):
                        changed.append(self.block_nodes[b_label].taken.label)
                    if (
                        self.block_nodes[b_label].fall_through is not None
                        and self.block_nodes[b_label].fall_through.label not in changed
                    ):
                        changed.append(self.block_nodes[b_label].fall_through.label)

    def constant_propagation(self):
        CTES = dict()

        for b_label, b_node in self.block_nodes.items():
            for decl_block, inst_idx in self.RD_IN[b_label]:
                inst = self.block_nodes[decl_block].instructions[inst_idx]
                if "literal" in inst[0]:
                    var_name = inst[2]
                    var_value = inst[1]
                    if var_name in CTES and var_value != CTES[var_name]:
                        CTES[var_name] = "NAC"
                    elif var_name not in CTES:
                        CTES[var_name] = var_value
                # Aqui da pra otimizar verificando se o store é de uma constante e, se for
                # adicionar a variável em CTES, teria que adicionar store em assign_ops
                elif "store" in inst[0]:
                    source = inst[1]
                    target = inst[2]

                    if target in CTES and source not in CTES:
                        CTES[target] = "NAC"
                    else:
                        if source in CTES and target not in CTES:
                            CTES[target] = CTES[source]
                        elif (
                            source in CTES
                            and target in CTES
                            and CTES[source] != CTES[target]
                        ):
                            CTES[target] = "NAC"

            for i, inst in enumerate(b_node.instructions):
                op_code = inst[0]

                new_inst = inst
                if "load" in op_code and inst[1] in CTES and CTES[inst[1]] != "NAC":
                    # varname is a cte
                    target = inst[2]
                    var_type = op_code.split("_")[1]
                    # print("FEZ OTMIZAÇÃO LOAD")
                    new_inst = (f"literal_{var_type}", CTES[inst[1]], target)
                    b_node.instructions[i] = new_inst
                elif (
                    "cbranch" in op_code and inst[1] in CTES and CTES[inst[1]] != "NAC"
                ):
                    # breakpoint()
                    if CTES[inst[1]] == 1:
                        # TRUE
                        jump_target = inst[2]
                    elif CTES[inst[1]] == 0:
                        # FALSE
                        jump_target = inst[3]
                    else:
                        print("ERRO")
                    new_inst = (f"jump", jump_target)
                    b_node.instructions[i] = new_inst

                #     pdb.set_trace()
                elif op_code.split("_")[0] in self.bin_ops:
                    # AQUI TALVEZ COLOCAR "AND", "OR" EM BIN_OPS
                    left = inst[1]
                    right = inst[2]
                    target = inst[3]
                    type = op_code.split("_")[1]
                    if (
                        left in CTES
                        and CTES[left] != "NAC"
                        and right in CTES
                        and CTES[right] != "NAC"
                    ):
                        # AQUI TALVEZ TESTAR O TIPO, TAMO ASSUMINDO QUE É SEMPRE INT
                        result = self.bin_ops[op_code.split("_")[0]](
                            CTES[left], CTES[right]
                        )
                        new_inst = (f"literal_{type}", result, target)
                        b_node.instructions[i] = new_inst
                        # print("FEZ OTIMIZAÇÃO BIN OP")

                # Add new instructions to CTE dict if necessary
                if new_inst is not None:
                    if "literal" in new_inst[0]:
                        var_name = new_inst[2]
                        var_value = new_inst[1]
                        if var_name in CTES and var_value != CTES[var_name]:
                            CTES[var_name] = "NAC"
                        elif var_name not in CTES:
                            CTES[var_name] = var_value
                    elif "store" in new_inst[0]:
                        source = new_inst[1]
                        target = new_inst[2]

                        if target in CTES and source not in CTES:
                            CTES[target] = "NAC"
                        else:
                            if source in CTES and target not in CTES:
                                CTES[target] = CTES[source]
                            elif (
                                source in CTES
                                and target in CTES
                                and CTES[source] != CTES[target]
                            ):
                                CTES[target] = "NAC"

    def buildLV_blocks(self, block, visited_blocks=[]):
        if block is not None and block.label not in visited_blocks:
            for i, inst in enumerate(block.instructions):
                self.USE[(block.label, i)] = set()
                self.DEF[(block.label, i)] = set()
                self.LV_OUT[(block.label, i)] = set()
                self.LV_IN[(block.label, i)] = set()

            visited_blocks.append(block.label)

            if isinstance(block, BasicBlock):
                self.buildLV_blocks(block.branch, visited_blocks)
            else:
                # Conditional block
                self.buildLV_blocks(block.taken, visited_blocks)
                self.buildLV_blocks(block.fall_through, visited_blocks)

    def computeLV_use_def(self, block, visited_blocks=[]):
        if block is not None and block.label not in visited_blocks:
            for i, inst in enumerate(block.instructions):
                inst_prefix = inst[0].split("_")[0]

                # Compute USE
                if inst_prefix in self.bin_ops or inst_prefix in self.relational_ops:
                    left = inst[1]
                    right = inst[2]
                    self.USE[(block.label, i)].add(left)
                    self.USE[(block.label, i)].add(right)
                elif (
                    inst_prefix in self.mem_ops
                    or inst_prefix in self.unary_ops
                    or inst_prefix in self.branch_ops
                    or inst_prefix in self.func_builtin_ops
                ):
                    try:
                        if inst[0] != "return_void" and inst[0] != "print_void":
                            used = inst[1]
                            self.USE[(block.label, i)].add(used)
                    except:
                        breakpoint()
                elif inst_prefix in self.vector_ops:
                    src = inst[1]
                    idx = inst[2]
                    self.USE[(block.label, i)].add(src)
                    self.USE[(block.label, i)].add(idx)

                # Compute DEF
                if inst_prefix in self.assign_ops:
                    target = self.get_target(inst)
                    self.DEF[(block.label, i)].add(target)

            visited_blocks.append(block.label)
            if isinstance(block, BasicBlock):
                self.computeLV_use_def(block.branch, visited_blocks)
            else:
                # Conditional block
                self.computeLV_use_def(block.taken, visited_blocks)
                self.computeLV_use_def(block.fall_through, visited_blocks)

    def get_node_succ(self, node_key):
        # AQUI TALVEZ MORRA NUM NÓ CASO O BLOCO NÃO TENHA NENHUMA INSTRUÇÃO
        b_label, inst_idx = node_key
        successor = []
        if inst_idx == len(self.block_nodes[b_label].instructions) - 1:
            # if b_label == "%while.body":
            #     breakpoint()
            # last inst of block
            if isinstance(self.block_nodes[b_label], BasicBlock):
                if (
                    self.block_nodes[b_label].branch is not None
                    and len(self.block_nodes[b_label].branch.instructions) > 0
                ):
                    successor.append((self.block_nodes[b_label].branch.label, 0))

            elif isinstance(self.block_nodes[b_label], ConditionBlock):
                if (
                    self.block_nodes[b_label].taken is not None
                    and len(self.block_nodes[b_label].taken.instructions) > 0
                ):
                    successor.append((self.block_nodes[b_label].taken.label, 0))
                if (
                    self.block_nodes[b_label].fall_through is not None
                    and len(self.block_nodes[b_label].fall_through.instructions) > 0
                ):
                    successor.append((self.block_nodes[b_label].fall_through.label, 0))
        else:
            successor.append((b_label, inst_idx + 1))

        return successor

    def get_node_pred(self, node_key):
        b_label, inst_idx = node_key
        predecessor = []
        if inst_idx == 0:
            # first inst of block
            for p in self.block_nodes[b_label].predecessors:
                if len(p.instructions) > 0:
                    predecessor.append((p.label, len(p.instructions) - 1))
        else:
            predecessor.append((b_label, inst_idx - 1))

        return predecessor

    def computeLV_in_out(self):
        changed = list(self.LV_OUT.keys()).copy()

        while len(changed) > 0:
            curr_node = changed[0]
            del changed[0]
            # print(f"Len changed = {len(changed)}")

            # The set of variables that are live out of a node is the union of all the variables
            # that are live in to the node's successors
            for succ in self.get_node_succ(curr_node):
                self.LV_OUT[curr_node] = self.LV_OUT[curr_node] | self.LV_IN[succ]

            oldin = self.LV_IN[curr_node].copy()
            self.LV_IN[curr_node] = (
                self.LV_OUT[curr_node] - self.DEF[curr_node]
            ) | self.USE[curr_node]

            # if curr_node[0] == "%while.cond" or curr_node[0] == "%while.body":
            #     print(f"---nó: {curr_node}-----")
            #     # breakpoint()
            #     print(
            #         f"inst: {self.block_nodes[curr_node[0]].instructions[curr_node[1]]}"
            #     )
            #     print(f"USE: {self.USE[curr_node]}")
            #     print(f"DEF: {self.DEF[curr_node]}")
            #     print(f"LV_IN: {self.LV_IN[curr_node]}")
            #     print(f"LV_OUT: {self.LV_OUT[curr_node]}")
            #     print(f"Len changed: {len(changed)}")

            if oldin != self.LV_IN[curr_node]:
                for p in self.get_node_pred(curr_node):
                    changed.append(p)
                    changed.append(curr_node)

            #     if curr_node[0] == "%while.cond" or curr_node[0] == "%while.body":
            #         print("MUDOU O LIVE IN EIN")
            #         print(f"Len changed ALTERADO: {len(changed)}")
            # if curr_node[0] == "%while.cond" or curr_node[0] == "%while.body":
            #     print("--------------")

    def deadcode_elimination(self):
        to_be_terminated = []
        for b_label, b_node in self.block_nodes.items():
            for i, inst in enumerate(b_node.instructions):
                inst_prefix = inst[0].split("_")[0]

                if inst_prefix in self.assign_ops:
                    target = self.get_target(inst)
                    if target not in self.LV_OUT[(b_label, i)]:
                        to_be_terminated.append(
                            (b_label, self.block_nodes[b_label].instructions[i])
                        )

        for inst_id in to_be_terminated:
            b_label, to_del_inst = inst_id
            self.block_nodes[b_label].instructions.remove(to_del_inst)

    def discard_unused_allocs(self):
        to_be_terminated = []
        for b_label, b_node in self.block_nodes.items():
            for i, inst in enumerate(b_node.instructions):
                inst_prefix = inst[0].split("_")[0]
                if inst_prefix == "alloc":
                    target = inst[1]
                    used = False
                    for _, var_lst in self.USE.items():
                        for var in var_lst:
                            if var == target:
                                used = True
                    if not used:
                        to_be_terminated.append(
                            (b_label, self.block_nodes[b_label].instructions[i])
                        )

        for inst_id in to_be_terminated:
            b_label, to_del_inst = inst_id
            self.block_nodes[b_label].instructions.remove(to_del_inst)

    def get_instructions_n(self):
        total_inst = 0
        for b_label, b_node in self.block_nodes.items():
            total_inst += len(b_node.instructions)
        return total_inst

    def visit_Program(self, node: Node):
        # First, save the global instructions on code member
        self.code = node.text[:]  # [:] to do a copy
        for _decl in node.gdecls:
            self.block_nodes = dict()
            # Reaching Definitions
            self.DEFS = dict()
            self.GEN = dict()
            self.KILL = dict()
            self.RD_OUT = dict()
            self.RD_IN = dict()

            if isinstance(_decl, FuncDef):
                # TALVEZ TENHA QUE RESETAR IN, OUT, DEFS ETC AQUI SE OS BLOCOS TIVEREM LABELS EM COMUM
                # start with Reach Definitions Analysis
                self.buildRD_blocks(_decl.cfg, [])
                self.computeRD_gen_kill(_decl.cfg, [])
                self.computeRD_in_out(_decl.cfg)

                # # and do constant propagation optimization
                self.constant_propagation()

                # after do live variable analysis
                n_insts_opt = -1
                n_insts = 0
                while n_insts != n_insts_opt:
                    n_insts = self.get_instructions_n()
                    self.USE = dict()
                    self.DEF = dict()
                    self.LV_OUT = dict()
                    self.LV_IN = dict()
                    self.buildLV_blocks(_decl.cfg, [])
                    self.computeLV_use_def(_decl.cfg, [])
                    self.computeLV_in_out()
                    # # and do dead code elimination
                    self.deadcode_elimination()
                    self.discard_unused_allocs()
                    n_insts_opt = self.get_instructions_n()

                # # after that do cfg simplify (optional)
                # self.short_circuit_jumps(_decl.cfg)
                # self.merge_blocks(_decl.cfg)

                # # finally save optimized instructions in self.code
                self.appendOptimizedCode(_decl.cfg)

        if self.viewcfg:
            for _decl in node.gdecls:
                if isinstance(_decl, FuncDef):
                    dot = CFG(_decl.decl.name.name + ".opt")
                    dot.view(_decl.cfg)


if __name__ == "__main__":
    # create argument parser
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "input_file",
        help="Path to file to be used to generate uCIR. By default, this script runs the interpreter on the optimized uCIR \
              and shows the speedup obtained from comparing original uCIR with its optimized version.",
        type=str,
    )
    parser.add_argument(
        "--opt",
        help="Print optimized uCIR generated from input_file.",
        action="store_true",
    )
    parser.add_argument(
        "--speedup",
        help="Show speedup from comparing original uCIR with its optimized version.",
        action="store_true",
        default=True,
    )
    parser.add_argument(
        "--debug", help="Run interpreter in debug mode.", action="store_true"
    )
    parser.add_argument(
        "-c",
        "--cfg",
        help="show the CFG of the optimized uCIR for each function in pdf format",
        action="store_true",
    )
    args = parser.parse_args()

    speedup = args.speedup
    print_opt_ir = args.opt
    create_cfg = args.cfg
    interpreter_debug = args.debug

    # get input path
    input_file = args.input_file
    input_path = pathlib.Path(input_file)

    # check if file exists
    if not input_path.exists():
        print("Input", input_path, "not found", file=sys.stderr)
        sys.exit(1)

    # set error function
    p = UCParser()
    # open file and parse it
    with open(input_path) as f:
        ast = p.parse(f.read())

    sema = Visitor()
    sema.visit(ast)

    gen = CodeGenerator(False)
    gen.visit(ast)
    gencode = gen.code

    opt = DataFlow(create_cfg)
    opt.visit(ast)
    optcode = opt.code
    if print_opt_ir:
        print("Optimized uCIR: --------")
        opt.show()
        print("------------------------\n")
    speedup = len(gencode) / len(optcode)
    sys.stderr.write(
        "[SPEEDUP] Default: %d Optimized: %d Speedup: %.2f\n\n"
        % (len(gencode), len(optcode), speedup)
    )

    vm = Interpreter(interpreter_debug)
    vm.run(optcode)
