import argparse
import pathlib
import sys
from typing import Dict, List, Tuple

from uc.uc_ast import (
    ArrayDecl,
    FuncDef,
    Node,
    VarDecl,
    ExprList,
    FuncDecl,
    ArrayRef,
    Constant,
)
from uc.uc_block import (
    CFG,
    BasicBlock,
    Block,
    ConditionBlock,
    EmitBlocks,
    format_instruction,
)
from uc.uc_interpreter import Interpreter
from uc.uc_parser import UCParser
from uc.uc_sema import NodeVisitor, Visitor, Environment, SymbolTable
import pdb


class LabelSymbolTable(SymbolTable):
    def __init__(self):
        super().__init__()

    def add(self, name: str) -> None:
        """Increments in the LabelSymbolTable.="""
        curr_value = self.lookup(name)
        if curr_value is not None:
            self.change_value(name, curr_value + 1)
        else:
            super().add(name, 1)

    def clear_table(self):
        self.__data = {}


class CodeGenerator(NodeVisitor):
    """
    Node visitor class that creates 3-address encoded instruction sequences
    with Basic Blocks & Control Flow Graph.
    """

    def __init__(self, viewcfg: bool):
        self.viewcfg: bool = viewcfg
        self.current_block: Block = None

        # version dictionary for temporaries. We use the name as a Key
        self.fname: str = "_glob_"
        self.versions: Dict[str, int] = {self.fname: 0}

        # The generated code (list of tuples)
        # At the end of visit_program, we call each function definition to emit
        # the instructions inside basic blocks. The global instructions that
        # are stored in self.text are appended at beginning of the code
        self.code: List[Tuple[str]] = []

        self.text: List[
            Tuple[str]
        ] = []  # Used for global declarations & constants (list, strings)

        # Map binary ops
        self.binary_ops = {
            "*": "mul",
            "==": "eq",
            "+": "add",
            "-": "sub",
            "<": "lt",
            "<=": "le",
            ">=": "ge",
            ">": "gt",
            "!=": "ne",
            "/": "div",
            "&&": "and",
            "||": "or",
            "%": "mod",
        }

        self.unary_ops = {"!": "not", "-": "minus"}

        self.env = Environment()
        self.label_st = LabelSymbolTable()
        # Store params node for each func
        self.f_params_nodes = {}
        # Stores params types and respective register for each func
        self.f_params_types_reg = {}
        # Stores return register for each func
        self.f_return_reg = {}
        # Store current return block
        self.return_block = None

        # TODO: Complete if needed.

    def show(self, buf=sys.stdout):
        _str = ""
        for _code in self.code:
            _str += format_instruction(_code) + "\n"
        buf.write(_str)

    def new_temp(self) -> str:
        """
        Create a new temporary variable of a given scope (function name).
        """
        if self.fname not in self.versions:
            self.versions[self.fname] = 1
        name = "%" + "%d" % (self.versions[self.fname])
        self.versions[self.fname] += 1
        return name

    def new_text(self, typename: str) -> str:
        """
        Create a new literal constant on global section (text).
        """
        name = "@." + typename + "." + "%d" % (self.versions["_glob_"])
        self.versions["_glob_"] += 1
        return name

    # You must implement visit_Nodename methods for all of the other
    # AST nodes.  In your code, you will need to make instructions
    # and append them to the current block code list.
    #
    # A few sample methods follow. Do not hesitate to complete or change
    # them if needed.

    def get_label(self, label: str) -> str:
        """Get label considering LabelSymbolTable"""
        label_curr_value = self.label_st.lookup(label)
        if label_curr_value is None:
            self.label_st.add(label)
            return label
        else:
            self.label_st.add(label)
            label = label + f".{label_curr_value}"
            return label

    def visit_Type(self, node: Node):
        pass

    def visit_Return(self, node: Node):
        if node.expr is not None:
            self.visit(node.expr)
            node.gen_location = node.expr.gen_location
            return_type = node.expr.uc_type.typename

            if return_type != "void":
                inst = (
                    f"store_{return_type}",
                    node.gen_location,
                    self.f_return_reg[self.fname],
                )
                self.current_block.append(inst)

        self.current_block.branch = self.return_block
        self.return_block.predecessors.append(self.current_block)
        self.current_block.append(("jump", f"%exit"))

    def visit_FuncDef(self, node: Node):
        self.env.push()
        self.label_st.clear_table()
        node.cfg = BasicBlock(f"%{node.decl.name.name}")
        return_block = BasicBlock(f"%exit")
        self.return_block = return_block
        # node.cfg.predecessors.append(self.current_block)
        # self.current_block.next_block = node.cfg
        # self.current_block.branch = node.cfg
        self.current_block = node.cfg

        self.visit(node.decl)
        # TA ALOCANDO PRO RETURN ANTES DO ENTRY, TALVEZ DÊ PROBLEMA
        self.current_block.append((f"entry:",))
        # visit params declaration
        if self.fname in self.f_params_nodes.keys():
            for param_node, (param_type, param_reg) in zip(
                self.f_params_nodes[self.fname], self.f_params_types_reg[self.fname]
            ):
                self.visit(param_node)
                inst = (f"store_{param_type}", param_reg, param_node.name.gen_location)
                self.current_block.append(inst)

        self.visit(node.body)
        self.current_block.next_block = return_block
        return_block.append(("exit:",))
        return_type = node.type.name

        if return_type == "void":
            inst = (f"return_void",)
            return_block.append(inst)
        else:
            return_tmp = self.new_temp()
            inst = (f"load_{return_type}", self.f_return_reg[self.fname], return_tmp)
            return_block.append(inst)
            inst = (f"return_{return_type}", return_tmp)
            return_block.append(inst)

        self.env.pop()

    def visit_FuncDecl(self, node: Node):
        # Emit function
        func_name = node.type.declname.name
        self.fname = func_name

        # Allocating return
        return_type = node.uc_type.return_type.typename
        if return_type != "void":
            return_reg = self.new_temp()
        # Creating param tuples
        params_lst = []
        if node.params is not None:
            for _param in node.params.params:
                reg = self.new_temp()
                type = _param.type.type.uc_type.typename
                params_lst.append((type, reg))
            self.f_params_nodes[func_name] = node.params.params
            self.f_params_types_reg[func_name] = params_lst

        self.current_block.append(
            (f"define_{return_type}", f"@{func_name}", params_lst)
        )

        # Return register
        if return_type != "void":
            self.current_block.append((f"alloc_{return_type}", return_reg))
            self.f_return_reg[func_name] = return_reg

    def visit_FuncCall(self, node: Node):
        if node.args is not None:
            if not isinstance(node.args, ExprList):
                params = [node.args]
            else:
                params = node.args.exprs

            for param in params:
                self.visit(param)
                inst = (f"param_{param.uc_type.typename}", param.gen_location)
                self.current_block.append(inst)
        source = f"@{node.name.name}"
        target = self.new_temp()
        inst = (f"call_{node.uc_type.typename}", source, target)
        self.current_block.append(inst)
        node.gen_location = target

    def visit_Compound(self, node: Node):
        for _citen in node.citens:
            self.visit(_citen)

    def visit_Decl(self, node: Node):
        if isinstance(node.type, ArrayDecl):
            node.type.init = node.init
        self.visit(node.type)

    def visit_DeclList(self, node: Node):
        if node.decls is not None:
            for _decl in node.decls:
                self.visit(_decl)

    def visit_Break(self, node: Node):
        curr_loop_label = self.env.get_curr_loop()
        inst = ("jump", curr_loop_label)
        self.current_block.append(inst)

    def visit_If(self, node: Node):
        have_else = node.iffalse is not None
        if_label = self.get_label("if")
        condition_block = ConditionBlock(f"%{if_label}")
        if_then_label = self.get_label("if.then")
        if_then_block = BasicBlock(f"%{if_then_label}")
        if have_else:
            if_else_label = self.get_label("if.else")
            if_else_block = BasicBlock(f"%{if_else_label}")
        if_end_label = self.get_label("if.end")
        if_end_block = BasicBlock(f"%{if_end_label}")

        if_next_block = self.current_block.next_block
        if_branch_block = self.current_block.branch

        self.current_block.branch = condition_block
        self.current_block.next_block = condition_block
        condition_block.predecessors.append(self.current_block)
        condition_block.taken = if_then_block
        if have_else:
            condition_block.fall_through = if_else_block
        condition_block.next_block = if_then_block

        if_then_block.predecessors.append(condition_block)
        if have_else:
            if_then_block.next_block = if_else_block
            if_then_block.branch = if_else_block
        else:
            if_then_block.next_block = if_end_block
            if_then_block.branch = if_end_block

        if have_else:
            if_else_block.predecessors.append(if_then_block)
            if_else_block.next_block = if_end_block
            if_else_block.branch = if_end_block

        if have_else:
            if_end_block.predecessors.append(if_else_block)
        else:
            if_end_block.predecessors.append(if_then_block)
        if_end_block.next_block = if_next_block
        if_end_block.branch = if_branch_block

        self.current_block = condition_block
        self.visit(node.cond)
        if have_else:
            if_false_label = if_else_block.label
        else:
            if_false_label = if_end_block.label
        inst = (
            "cbranch",
            node.cond.gen_location,
            if_then_block.label,
            if_false_label,
        )
        self.current_block.append(inst)

        self.current_block = if_then_block
        inst = (f"{if_then_label}:",)
        if_then_block.append(inst)
        self.visit(node.iftrue)
        inst = (
            "jump",
            if_end_block.label,
        )
        self.current_block.append(inst)

        if have_else:
            self.current_block = if_else_block
            inst = (f"{if_else_label}:",)
            if_else_block.append(inst)
            self.visit(node.iffalse)
            inst = (
                "jump",
                if_end_block.label,
            )
            self.current_block.append(inst)

        self.current_block = if_end_block
        inst = (f"{if_end_label}:",)
        if_end_block.append(inst)

    def visit_Assert(self, node: Node):
        self.visit(node.expr)
        assert_label = self.get_label("assert")
        condition_block = ConditionBlock(f"%{assert_label}")
        assert_false_label = self.get_label("assert.false")
        assert_false_block = BasicBlock(f"%{assert_false_label}")
        assert_true_label = self.get_label("assert.true")
        assert_true_block = BasicBlock(f"%{assert_true_label}")
        assert_exit_label = self.get_label("assert.exit")
        exit_block = BasicBlock(f"%{assert_exit_label}")
        condition_block.taken = assert_true_block
        condition_block.fall_through = assert_false_block

        assert_next_block = self.current_block.next_block
        assert_branch_block = self.current_block.branch

        self.current_block.branch = condition_block
        self.current_block.next_block = condition_block

        condition_block.predecessors.append(self.current_block)
        condition_block.branch = assert_false_block
        condition_block.next_block = assert_false_block

        assert_false_block.predecessors.append(condition_block)
        assert_false_block.branch = exit_block
        assert_false_block.next_block = assert_true_block

        assert_true_block.predecessors.append(condition_block)
        assert_true_block.branch = exit_block
        assert_true_block.next_block = exit_block

        exit_block.predecessors.append(assert_false_block)
        exit_block.predecessors.append(assert_true_block)
        exit_block.next_block = assert_next_block
        exit_block.branch = assert_branch_block

        self.current_block = condition_block
        inst = (
            "cbranch",
            node.expr.gen_location,
            condition_block.taken.label,
            condition_block.fall_through.label,
        )
        self.current_block.append(inst)

        error_msg = self.new_text("str")
        self.text.append(
            (
                "global_string",
                error_msg,
                "assertion_fail on" + str(node.expr.coord).replace("@", ""),
            )
        )
        inst_fall_through = ("print_string", error_msg)
        assert_false_block.append((f"{assert_false_label}:",))
        assert_false_block.append(inst_fall_through)
        assert_false_block.append(("jump", f"%exit"))

        assert_true_block.append((f"{assert_true_label}:",))

        self.current_block = exit_block

    def visit_Assignment(self, node: Node):
        self.visit(node.rvalue)
        self.visit(node.lvalue)
        store_type = node.rvalue.uc_type.typename
        source = node.rvalue.gen_location
        # pdb.set_trace()
        if isinstance(node.lvalue, ArrayRef):
            target = node.lvalue.mem_pos
            inst = (f"store_{store_type}_*", source, target)
        else:
            target = self.env.lookup(node.lvalue.name)
            inst = (f"store_{store_type}", source, target)
        # target = node.lvalue.gen_location
        # target = f"%{node.lvalue.name}"

        self.current_block.append(inst)

    def visit_While(self, node: Node):
        self.env.push()
        while_cond_label = self.get_label("while.cond")
        condition_block = ConditionBlock(f"%{while_cond_label}")
        while_body_label = self.get_label("while.body")
        body_block = BasicBlock(f"%{while_body_label}")
        while_end_label = self.get_label("while.end")
        end_block = BasicBlock(f"%{while_end_label}")

        self.env.add_curr_loop(end_block.label)

        while_next_block = self.current_block.next_block
        while_branch_block = self.current_block.branch

        self.current_block.branch = condition_block
        self.current_block.next_block = condition_block

        condition_block.predecessors.append(self.current_block)
        condition_block.predecessors.append(body_block)
        condition_block.taken = body_block
        condition_block.fall_through = end_block

        condition_block.next_block = body_block

        body_block.predecessors.append(condition_block)
        body_block.branch = condition_block
        body_block.next_block = end_block

        end_block.predecessors.append(condition_block)
        end_block.next_block = while_next_block
        end_block.branch = while_branch_block

        inst = (
            "jump",
            condition_block.label,
        )
        self.current_block.append(inst)

        self.current_block = condition_block
        inst = (f"{while_cond_label}:",)
        condition_block.append(inst)
        self.visit(node.cond)
        inst = (
            "cbranch",
            node.cond.gen_location,
            condition_block.taken.label,
            condition_block.fall_through.label,
        )
        self.current_block.append(inst)

        self.current_block = body_block
        inst = (f"{while_body_label}:",)
        body_block.append(inst)
        self.visit(node.body)
        inst = (
            "jump",
            condition_block.label,
        )
        self.current_block.append(inst)

        self.current_block = end_block
        inst = (f"{while_end_label}:",)
        self.current_block.append(inst)
        self.env.pop()

    def visit_For(self, node: Node):
        self.env.push()
        self.visit(node.init)
        for_cond_label = self.get_label("for.cond")
        condition_block = ConditionBlock(f"%{for_cond_label}")
        for_body_label = self.get_label("for.body")
        body_block = BasicBlock(f"%{for_body_label}")
        for_end_label = self.get_label("for.end")
        end_block = BasicBlock(f"%{for_end_label}")
        for_inc_label = self.get_label("for.inc")
        inc_block = BasicBlock(f"%{for_inc_label}")

        self.env.add_curr_loop(end_block.label)

        for_next_block = self.current_block.next_block
        for_branch_block = self.current_block.branch

        self.current_block.branch = condition_block
        self.current_block.next_block = condition_block

        condition_block.predecessors.append(self.current_block)
        condition_block.predecessors.append(inc_block)
        condition_block.taken = body_block
        condition_block.fall_through = end_block

        condition_block.next_block = body_block

        body_block.predecessors.append(condition_block)
        body_block.branch = inc_block
        body_block.next_block = inc_block

        inc_block.predecessors.append(body_block)
        inc_block.branch = condition_block
        inc_block.next_block = end_block

        end_block.predecessors.append(condition_block)
        end_block.next_block = for_next_block
        end_block.branch = for_branch_block

        inst = (
            "jump",
            condition_block.label,
        )
        self.current_block.append(inst)

        self.current_block = condition_block
        inst = (f"{for_cond_label}:",)
        condition_block.append(inst)
        self.visit(node.cond)
        inst = (
            "cbranch",
            node.cond.gen_location,
            condition_block.taken.label,
            condition_block.fall_through.label,
        )
        self.current_block.append(inst)

        self.current_block = body_block
        inst = (f"{for_body_label}:",)
        body_block.append(inst)
        self.visit(node.body)
        inst = (
            "jump",
            inc_block.label,
        )
        self.current_block.append(inst)
        self.current_block = inc_block
        inst = (f"{for_inc_label}:",)
        inc_block.append(inst)
        self.visit(node.next)
        inst = (
            "jump",
            condition_block.label,
        )
        self.current_block.append(inst)

        self.current_block = end_block
        inst = (f"{for_end_label}:",)
        self.current_block.append(inst)
        self.env.pop()

    def visit_Constant(self, node: Node):
        if node.type == "string":
            _target = self.new_text("str")
            inst = ("global_string", _target, node.value)
            self.text.append(inst)
        else:
            # Create a new temporary variable name
            _target = self.new_temp()
            # Make the SSA opcode and append to list of generated instructions
            inst = ("literal_" + node.type, node.value, _target)
            self.current_block.append(inst)
        # Save the name of the temporary variable where the value was placed
        node.gen_location = _target

    def visit_ID(self, node: Node):
        # FALTA VER SE É VARIÁVEL GLOBAL
        id_location = self.env.lookup(node.name)
        target = self.new_temp()
        inst = (f"load_{node.uc_type.typename}", id_location, target)
        self.current_block.append(inst)
        node.gen_location = target

    def visit_ArrayRef(self, node: Node):
        if not isinstance(node.name, ArrayRef):
            # single dimension
            self.visit(node.subscript)
            index = node.subscript.gen_location
            source = self.env.lookup(node.name.name)
        else:
            self.visit(node.name.subscript)
            first_index_target = node.name.subscript.gen_location
            #  AQUI TA HARD CODED, DEVERIA VIR INT SEMPRE DIRETO, PODE DAR PROBLEMA
            if isinstance(node.name.name.uc_type.type.size, Constant):
                first_length = node.name.name.uc_type.type.size.value
            else:
                first_length = node.name.name.uc_type.type.size

            # desloca index pelo tamanho do vetor
            length_target = self.new_temp()
            inst = ("literal_int", first_length, length_target)
            self.current_block.append(inst)
            mul_target = self.new_temp()
            inst = (f"mul_int", first_index_target, length_target, mul_target)
            self.current_block.append(inst)

            self.visit(node.subscript)
            second_index_target = node.subscript.gen_location

            index = self.new_temp()
            inst = (f"add_int", mul_target, second_index_target, index)
            self.current_block.append(inst)
            source = self.env.lookup(node.name.name.name)

        target = self.new_temp()
        array_type = node.uc_type.typename
        inst = (f"elem_{array_type}", source, index, target)
        self.current_block.append(inst)
        # load value reference
        final_target = self.new_temp()
        inst = (f"load_{array_type}_*", target, final_target)
        self.current_block.append(inst)
        node.mem_pos = target
        node.gen_location = final_target

    def visit_UnaryOp(self, node: Node):
        self.visit(node.expr)
        # TODO - EM CASO DE VETOR: LOAD ARRAY REF VALUE
        target = self.new_temp()

        # Create the opcode and append to list
        if node.op == "-":
            # Transforms - unary to binary  by making 0 - var
            tmp_reg = self.new_temp()
            inst = (f"literal_{node.expr.uc_type.typename}", 0, tmp_reg)
            self.current_block.append(inst)
            inst = (
                f"sub_{node.expr.uc_type.typename}",
                tmp_reg,
                node.expr.gen_location,
                target,
            )
        else:
            opcode = self.unary_ops[node.op] + "_" + node.expr.uc_type.typename
            inst = (opcode, node.expr.gen_location, target)
        self.current_block.append(inst)
        node.gen_location = target

    def visit_BinaryOp(self, node: Node):
        # Visit the left and right expressions
        self.visit(node.lvalue)
        self.visit(node.rvalue)
        # TODO - EM CASO DE VETOR:
        # - Load the location containing the left expression
        # - Load the location containing the right expression

        # Make a new temporary for storing the result
        target = self.new_temp()

        # Create the opcode and append to list
        opcode = self.binary_ops[node.op] + "_" + node.lvalue.uc_type.typename
        inst = (opcode, node.lvalue.gen_location, node.rvalue.gen_location, target)
        self.current_block.append(inst)

        # Store location of the result on the node
        node.gen_location = target

    def visit_ExprList(self, node: Node):
        pass

    def visit_Print(self, node: Node):
        # Visit the expression
        if node.expr is not None:
            if not isinstance(node.expr, ExprList):
                self.visit(node.expr)
                # Create the opcode and append to list
                inst = ("print_" + node.expr.uc_type.typename, node.expr.gen_location)
                self.current_block.append(inst)
            else:
                # ExprList
                for _expr in node.expr.exprs:
                    self.visit(_expr)
                    inst = ("print_" + _expr.uc_type.typename, _expr.gen_location)
                    self.current_block.append(inst)
        else:
            inst = ("print_void",)
            self.current_block.append(inst)

    def visit_ArrayDecl(self, node: Node):
        if len(node.array_dim) == 2:
            decl_name = node.type.type.declname.name
            typename = node.type.type.type.name
        else:
            decl_name = node.type.declname.name
            typename = node.type.type.name

        if self.fname == "_glob_":
            _varname = "@" + decl_name
        else:
            temp_reg = self.env.lookup(decl_name)
            _varname = "%" + decl_name
            if temp_reg is not None:
                if "." not in temp_reg:
                    current_value = 1
                else:
                    current_value = int(temp_reg.split(".")[-1])
                _varname = _varname + "." + str(current_value + 1)

        self.env.add(decl_name, _varname)
        if len(node.array_dim) == 2:
            node.type.type.declname.gen_location = _varname
        else:
            node.type.declname.gen_location = _varname

        if len(node.array_dim) == 1:
            array_type = f"{typename}_{ node.array_dim[0]}"
        elif len(node.array_dim) == 2:
            array_type = f"{typename}_{node.array_dim[0]}_{node.array_dim[1]}"
        else:
            print(
                "ISSO AQUI NAO DEVERIA ESTAR SENDO PRINTADO, MANDAMOS MAL EM ASSUMIR QUE OS TESTES SÓ IAM TER 2 DIM"
            )

        if self.fname != "_glob_":
            inst = (
                f"alloc_{array_type}",
                _varname,
            )
            self.current_block.append(inst)

        # Store optional init val
        if node.init is not None:
            if isinstance(node.init, Constant):
                # String
                if self.fname != "_glob_":
                    _target = self.new_text(f"str")
                else:
                    _target = _varname
                inst = ("global_string", _target, node.init.value)
                self.text.append(inst)
                inst = (
                    "store_" + array_type,
                    _target,
                    _varname,
                )
            elif len(node.array_dim) == 1:
                # 1-D array

                init_value = []
                for _const in node.init.exprs:
                    init_value.append(_const.value)
                if self.fname != "_glob_":
                    _target = self.new_text(f"const_{decl_name}")
                else:
                    _target = _varname
                inst = (f"global_{array_type}", _target, init_value)
                self.text.append(inst)
                inst = (
                    "store_" + array_type,
                    _target,
                    _varname,
                )
            elif len(node.array_dim) == 2:
                # 2-D array
                init_value = []
                for init_lst in node.init.exprs:
                    init_value_2 = []
                    for _const in init_lst.exprs:
                        init_value_2.append(_const.value)
                    init_value.append(init_value_2)
                if self.fname != "_glob_":
                    _target = self.new_text(f"const_{decl_name}")
                else:
                    _target = _varname
                inst = (f"global_{array_type}", _target, init_value)
                self.text.append(inst)
                inst = (
                    "store_" + array_type,
                    _target,
                    _varname,
                )
            if self.fname != "_glob_":
                self.current_block.append(inst)

        # self.visit(node.type)

    def visit_VarDecl(self, node: Node):
        # Allocate on stack memory
        temp_reg = self.env.lookup(node.declname.name)
        if self.fname == "_glob_":
            _varname = "@" + node.declname.name
            self.env.add(node.declname.name, _varname)

            node.declname.gen_location = _varname

            # optional init val
            _init = node.init
            value = None
            if _init is not None:
                # self.visit(_init)
                value = _init.value
            if value is not None:
                inst = (f"global_{node.type.name}", _varname, value)
            else:
                inst = (f"global_{node.type.name}", _varname)

            self.text.append(inst)

        else:
            _varname = "%" + node.declname.name
            if temp_reg is not None:
                if "." not in temp_reg:
                    current_value = 1
                else:
                    current_value = int(temp_reg.split(".")[-1])
                _varname = _varname + "." + str(current_value + 1)

            self.env.add(node.declname.name, _varname)

            node.declname.gen_location = _varname
            inst = ("alloc_" + node.type.name, _varname)
            self.current_block.append(inst)
            # Store optional init val
            _init = node.init
            if _init is not None:
                self.visit(_init)
                inst = (
                    "store_" + node.type.name,
                    _init.gen_location,
                    node.declname.gen_location,
                )
                self.current_block.append(inst)

    def visit_GlobalDecl(self, node: Node):
        for decl in node.decls:
            if not isinstance(decl.type, FuncDef) and not isinstance(
                decl.type, FuncDecl
            ):
                # COMPLETAR AQUI PRA CRIAR BLOCO PRA GLOBAL DECLARATION E ARRUMAR AS VISITAS
                self.visit(decl)

    def visit_Program(self, node: Node):
        self.env.push()
        # Visit all of the global declarations
        for _decl in node.gdecls:
            self.visit(_decl)
        self.env.pop()
        # At the end of codegen, first init the self.code with
        # the list of global instructions allocated in self.text
        self.code = self.text.copy()
        # Also, copy the global instructions into the Program node
        node.text = self.text.copy()
        # After, visit all the function definitions and emit the
        # code stored inside basic blocks.
        for _decl in node.gdecls:
            if isinstance(_decl, FuncDef):
                # _decl.cfg contains the Control Flow Graph for the function
                # cfg points to start basic block
                bb = EmitBlocks()
                bb.visit(_decl.cfg)
                for _code in bb.code:
                    self.code.append(_code)

        if self.viewcfg:  # evaluate to True if -cfg flag is present in command line
            for _decl in node.gdecls:
                if isinstance(_decl, FuncDef):
                    dot = CFG(_decl.decl.name.name)
                    dot.view(_decl.cfg)  # _decl.cfg contains the CFG for the function

    # TODO: Complete.


if __name__ == "__main__":
    # create argument parser
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "input_file",
        help="Path to file to be used to generate uCIR. By default, this script only runs the interpreter on the uCIR. \
              Use the other options for printing the uCIR, generating the CFG or for the debug mode.",
        type=str,
    )
    parser.add_argument(
        "--ir",
        help="Print uCIR generated from input_file.",
        action="store_true",
    )
    parser.add_argument(
        "--cfg", help="Show the cfg of the input_file.", action="store_true"
    )
    parser.add_argument(
        "--debug", help="Run interpreter in debug mode.", action="store_true"
    )
    args = parser.parse_args()

    print_ir = args.ir
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

    gen = CodeGenerator(create_cfg)
    gen.visit(ast)
    gencode = gen.code

    if print_ir:
        print("Generated uCIR: --------")
        gen.show()
        print("------------------------\n")

    vm = Interpreter(interpreter_debug)
    vm.run(gencode)
