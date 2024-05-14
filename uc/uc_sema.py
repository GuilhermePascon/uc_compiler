import argparse
import pathlib
import sys
from copy import deepcopy
from typing import Any, Dict, Union
from uc.uc_ast import (
    ID,
    Assignment,
    VarDecl,
    ArrayDecl,
    ArrayRef,
    InitList,
    Compound,
    ExprList,
    BinaryOp,
    Constant,
    Decl,
)
from uc.uc_parser import UCParser
from uc.uc_type import (
    uCType,
    CharType,
    IntType,
    BoolType,
    StringType,
    VoidType,
    ArrayType,
    FuncType,
)
import pdb


class SymbolTable:
    """Class representing a symbol table.

    `add` and `lookup` methods are given, however you still need to find a way to
    deal with scopes.

    ## Attributes
    - :attr data: the content of the SymbolTable
    """

    def __init__(self) -> None:
        """Initializes the SymbolTable."""
        self.__data = dict()
        self.curr_func = None
        self.curr_loop = None

    @property
    def data(self) -> Dict[str, Any]:
        """Returns a copy of the SymbolTable."""
        return deepcopy(self.__data)

    def add(self, name: str, value: uCType) -> None:
        """Adds to the SymbolTable.

        ## Parameters
        - :param name: the identifier on the SymbolTable
        - :param value: the value to assign to the given `name`
        """
        self.__data[name] = value

    def add_curr_func(self, func):
        """Add current function reference to symble table"""
        self.curr_func = func

    def add_curr_loop(self, loop):
        """Add current loop reference to symble table"""
        self.curr_loop = loop

    def change_value(self, name: str, new_value: uCType):
        """Changes a given identifier's value"""
        self.__data[name] = new_value

    def lookup(self, name: str) -> Union[Any, None]:
        """Searches `name` on the SymbolTable and returns the value
        assigned to it.

        ## Parameters
        - :param name: the identifier that will be searched on the SymbolTable

        ## Return
        - :return: the value assigned to `name` on the SymbolTable. If `name` is not found, `None` is returned.
        """
        return self.__data.get(name)


class Environment:
    """
    Environment class to manage symbol tables scopes
    """

    def __init__(self) -> None:
        self.symtabs_lst = []

    def push(self) -> None:
        self.symtabs_lst.append(SymbolTable())

    def pop(self) -> None:
        self.symtabs_lst.pop(-1)

    def add(self, name: str, value: uCType) -> None:
        self.symtabs_lst[-1].add(name, value)

    def add_curr_func(self, func):
        self.symtabs_lst[-1].add_curr_func(func)

    def get_curr_func(self):
        return self.symtabs_lst[-1].curr_func

    def add_curr_loop(self, loop):
        self.symtabs_lst[-1].add_curr_loop(loop)

    def get_curr_loop(self):
        return self.symtabs_lst[-1].curr_loop

    def change_symbol(self, name: str, new_value: uCType) -> None:
        """
        Change symbol value in the local scope
        """
        self.symtabs_lst[-1].change_value(name, new_value)

    def lookup(
        self, name: str, idx: int = -1, only_local: bool = False
    ) -> Union[Any, None]:
        data = self.symtabs_lst[idx].lookup(name)
        if data is None:
            if idx > -(len(self.symtabs_lst)) and not only_local:
                return self.lookup(name, idx - 1)
            else:
                return None
        else:
            return data

    def peek_symtab(self, idx=-1):
        return self.symtabs_lst[idx].data


class NodeVisitor:
    """A base NodeVisitor class for visiting uc_ast nodes.
    Subclass it and define your own visit_XXX methods, where
    XXX is the class name you want to visit with these
    methods.
    """

    _method_cache = None

    def visit(self, node):
        """Visit a node."""

        if self._method_cache is None:
            self._method_cache = {}

        visitor = self._method_cache.get(node.__class__.__name__)
        if visitor is None:
            method = "visit_" + node.__class__.__name__
            visitor = getattr(self, method, self.generic_visit)
            self._method_cache[node.__class__.__name__] = visitor

        return visitor(node)

    def generic_visit(self, node):
        """Called if no explicit visitor function exists for a
        node. Implements preorder visiting of the node.
        """
        for _, child in node.children():
            self.visit(child)


class Visitor(NodeVisitor):
    """
    Program visitor class. This class uses the visitor pattern. You need to define methods
    of the form visit_NodeName() for each kind of AST node that you want to process.
    """

    def __init__(self):
        # Initialize the symbol table
        self.environment = Environment()
        self.typemap = {
            "int": IntType,
            "char": CharType,
            "bool": BoolType,
            "string": StringType,
            "void": VoidType,
            "array": ArrayType,
            "function": FuncType,
        }
        # TODO: Complete...

    def _assert_semantic(
        self, condition: bool, msg_code: int, coord, name: str = "", ltype="", rtype=""
    ):
        """Check condition, if false print selected error message and exit"""
        error_msgs = {
            1: f"{name} is not defined",
            2: f"subscript must be of type(int), not {ltype}",
            3: "Expression must be of type(bool)",
            4: f"Cannot assign {rtype} to {ltype}",
            5: f"Binary operator {name} does not have matching LHS/RHS types",
            6: f"Binary operator {name} is not supported by {ltype}",
            7: "Break statement must be inside a loop",
            8: "Array dimension mismatch",
            9: f"Size mismatch on {name} initialization",
            10: f"{name} initialization type mismatch",
            11: f"{name} initialization must be a single element",
            12: "Lists have different sizes",
            13: "List & variable have different sizes",
            14: f"conditional expression is {ltype}, not type(bool)",
            15: f"{name} is not a function",
            16: f"no. arguments to call {name} function mismatch",
            17: f"Type mismatch with parameter {name}",
            18: "The condition expression must be of type(bool)",
            19: "Expression must be a constant",
            20: "Expression is not of basic type",
            21: f"{name} does not reference a variable of basic type",
            22: f"{name} is not a variable",
            23: f"Return of {ltype} is incompatible with {rtype} function definition",
            24: f"Name {name} is already defined in this scope",
            25: f"Unary operator {name} is not supported",
        }
        if not condition:
            msg = error_msgs[msg_code]  # invalid msg_code raises Exception
            print("SemanticError: %s %s" % (msg, coord), file=sys.stdout)
            sys.exit(1)

    def visit_Program(self, node):
        # Visit all of the global declarations
        self.environment.push()
        for _decl in node.gdecls:
            self.visit(_decl)
        self.environment.pop()
        # TODO: Manage the symbol table

    def visit_GlobalDecl(self, node):
        for _decl in node.decls:
            self.visit(_decl)

    def visit_Constant(self, node):
        node.uc_type = self.typemap[node.type]

        if node.type == "int":
            node.value = int(node.value)
        if node.type == "bool":
            node.value = bool(node.value)

    def visit_VarDecl(self, node):
        self.visit(node.type)
        self._assert_semantic(
            self.environment.lookup(node.declname.name, only_local=True) is None,
            24,
            node.declname.coord,
            node.declname.name,
        )
        self.environment.add(node.declname.name, node.type.uc_type)
        self.visit(node.declname)
        # aqui tem um if pra ver se o ID era de função ou variável

    def visit_ArrayRef(self, node):
        self.visit(node.subscript)
        if isinstance(node.subscript, ID):
            self._assert_semantic(
                self.environment.lookup(node.subscript.name) is not None,
                1,
                node.subscript.coord,
                node.subscript.name,
            )
        self._assert_semantic(
            node.subscript.uc_type == IntType,
            2,
            node.subscript.coord,
            ltype=f"type({node.subscript.uc_type.typename})",
        )
        self.visit(node.name)
        if not isinstance(node.name, ArrayRef):
            new_type = self.environment.lookup(node.name.name).type
            # If type is array of array, get only basic type os array
            if isinstance(new_type, ArrayType):
                new_type = new_type.type
            node.uc_type = new_type
        else:
            new_type = self.environment.lookup(node.name.name.name).type
            # If type is array of array, get only basic type os array
            if isinstance(new_type, ArrayType):
                new_type = new_type.type
            node.uc_type = new_type

    def lookup_array_declname(self, node):
        if isinstance(node, VarDecl):
            return node.declname
        else:
            return self.lookup_array_declname(node.type)

    def visit_ArrayDecl(self, node):
        self.visit(node.type)
        if node.dim is not None:
            self.visit(node.dim)
            dim = node.dim
        else:
            dim = None
        # modify type
        array_name = self.lookup_array_declname(node.type).name
        old_type = self.environment.lookup(array_name, only_local=True)
        new_type = ArrayType(old_type, dim)
        self.environment.change_symbol(array_name, new_type)

    def visit_FuncDecl(self, node):
        self.environment.push()
        self.visit(node.type)

        args_type_lst = []
        if node.params is not None:
            for _param in node.params.params:
                self.visit(_param)
                args_type_lst.append(_param.type.type.uc_type)
        self.environment.pop()

        func_type = FuncType(node.type.type.uc_type, args_type_lst)
        node.uc_type = func_type

        # Update symbol so it is a FuncType
        self.environment.change_symbol(node.type.declname.name, func_type)

    def visit_FuncDef(self, node):
        self.visit(node.type)
        self.visit(node.decl)
        self.environment.push()
        if node.decl.type.params is not None:
            self.visit(node.decl.type.params)
        self.environment.add_curr_func(node)
        self.visit(node.body)

        # If there is no return in the body check if func type is void
        # TALVEZ ABRIR ESCOPO NO COMPOUND DENTRO DE COMPOUND PODE FAZER COM QUE O HAS RETURN SUMA
        # POIS NO VISIT_RETURN SÓ BUSCA FUNÇÃO DENTRO DO ESCOPO
        if not node.has_return:
            self._assert_semantic(
                node.type.uc_type == VoidType,
                23,
                coord=node.body.coord,
                ltype=f"type(void)",
                rtype=f"type({node.type.uc_type.typename})",
            )
        # if node.body.citens is None:
        self.environment.pop()

    def visit_Compound(self, node):
        if node.citens is not None:
            for _citen in node.citens:
                if isinstance(_citen, Compound):
                    self.environment.push()
                    self.visit(_citen)
                    self.environment.pop()
                else:
                    self.visit(_citen)

    def visit_FuncCall(self, node):
        func_type = self.environment.lookup(node.name.name)
        self._assert_semantic(
            isinstance(func_type, FuncType), 15, node.name.coord, node.name.name
        )
        node.uc_type = func_type.return_type
        called_args = (
            node.args.exprs if isinstance(node.args, ExprList) else [node.args]
        )

        # When function is called with 0 arguments
        if len(called_args) == 1 and called_args[0] is None:
            called_args = []

        # assert has same number of args
        self._assert_semantic(
            len(called_args) == len(func_type.arguments_type),
            16,
            node.name.coord,
            node.name.name,
        )

        for called_arg, def_type in zip(called_args, func_type.arguments_type):
            self.visit(called_arg)
            called_type = called_arg.uc_type
            if isinstance(called_arg, ID) or isinstance(called_arg, ArrayRef):
                called_name = called_arg.name
            elif isinstance(called_arg, BinaryOp):
                called_name = called_arg.op
            else:
                called_name = called_arg.value
            self._assert_semantic(
                called_type == def_type, 17, called_arg.coord, called_name
            )

    def visit_Return(self, node):
        if node.expr is not None:
            self.visit(node.expr)
            expr_type = node.expr.uc_type
        else:
            expr_type = VoidType
        func = self.environment.get_curr_func()
        func.has_return = True
        func_type = func.type.uc_type
        self._assert_semantic(
            expr_type == func_type,
            23,
            node.coord,
            ltype=f"type({expr_type.typename})",
            rtype=f"type({func_type.typename})",
        )

    def visit_ParamList(self, node):
        for _param in node.params:
            self.visit(_param)

    def has_dim(self, node):
        """Search recursively if node arraydecl and sub arrays have dim"""
        if node.dim is None:
            return False
        elif isinstance(node.type, VarDecl):
            return True
        else:
            return self.has_dim(node.type)

    def check_init_lst_len(
        self, node_parent: Decl, init: Union[Constant, InitList], dimension: int
    ):
        if isinstance(init, Constant):
            self._assert_semantic(
                init.uc_type == StringType, 10, node_parent.name.coord
            )
            init_lst_len = len(init.value)
            self._assert_semantic(
                init_lst_len == dimension,
                9,
                node_parent.name.coord,
                node_parent.name.name,
            )
        else:
            init_lst_len = len(init.exprs)
            self._assert_semantic(init_lst_len == dimension, 13, node_parent.name.coord)

    def visit_Decl(self, node):
        self.visit(node.type)
        if isinstance(node.type, VarDecl):
            if node.init is not None:
                self.visit(node.init)
                self._assert_semantic(
                    not isinstance(node.init, InitList),
                    11,
                    node.type.declname.coord,
                    node.type.declname.name,
                )
                init_type = node.init.uc_type
                self._assert_semantic(
                    init_type == node.type.type.uc_type,
                    10,
                    node.type.declname.coord,
                    node.type.declname.name,
                )
                node.type.init = node.init

        if isinstance(node.type, ArrayDecl):
            if node.init is not None:
                self.visit(node.init)
                # One dimension array
                if isinstance(node.type.type, VarDecl):
                    # verify size only if dim was defined
                    if self.has_dim(node.type):
                        # verify size
                        dimension = node.type.dim.value
                        self.check_init_lst_len(node, node.init, dimension)
                        node.type.array_dim = [dimension]
                    else:
                        if isinstance(node.init, Constant):
                            self._assert_semantic(
                                node.init.uc_type == StringType, 10, node.name.coord
                            )
                            init_lst_len = len(node.init.value)
                        else:
                            init_lst_len = len(node.init.exprs)
                        old_type = self.environment.lookup(
                            node.type.type.declname.name, only_local=True
                        )
                        old_type.size = init_lst_len
                        node.type.array_dim = [init_lst_len]

                    # verify init type
                    if not isinstance(node.init, Constant):
                        for _init_value in node.init.exprs:
                            self.visit(_init_value)
                            self._assert_semantic(
                                isinstance(_init_value, Constant), 19, _init_value.coord
                            )
                            value_type = _init_value.uc_type
                            self._assert_semantic(
                                value_type == node.type.type.type.uc_type,
                                10,
                                node.coord,
                            )
                # Two dimensional array
                elif isinstance(node.type.type, ArrayDecl):
                    # verify size only if dim was defined
                    # pdb.set_trace()
                    if self.has_dim(node.type):
                        # check dimension 1
                        dimension_1 = node.type.dim.value
                        self.check_init_lst_len(node, node.init, dimension_1)

                        # then check if itens in dimension 2 have different size
                        exprs_len = [len(_init.exprs) for _init in node.init.exprs]
                        self._assert_semantic(
                            all(x == exprs_len[0] for x in exprs_len),
                            12,
                            node.name.coord,
                        )
                        # check dimension 2
                        dimension_2 = node.type.type.dim.value
                        for _init in node.init.exprs:
                            self.check_init_lst_len(node, _init, dimension_2)
                        node.type.array_dim = [dimension_1, dimension_2]
                    # AQUI PODE DAR PROBLEMA POIS NÃO FIZEMOS PRA DIM NÃO DEFINIDA EM MATRIZ 2D
                    else:
                        if isinstance(node.init, Constant):
                            self._assert_semantic(
                                node.init.uc_type == StringType, 10, node.name.coord
                            )
                            init_lst_len = len(node.init.value)
                        else:
                            init_lst_len = len(node.init.exprs)
                        old_type = self.environment.lookup(
                            node.name.name, only_local=True
                        )
                        old_type.size = init_lst_len
                        dimension1 = init_lst_len
                        # get length 2
                        dimension2 = len(node.init.exprs[0].exprs)
                        old_type.type.size = dimension2
                        node.type.array_dim = [dimension1, dimension2]

                    # verify init type
                    for _init_lst in node.init.exprs:
                        for _init_value in _init_lst.exprs:
                            self.visit(_init_value)
                            self._assert_semantic(
                                isinstance(_init_value, Constant), 19, _init_value.coord
                            )
                            value_type = _init_value.uc_type
                            self._assert_semantic(
                                value_type == node.type.type.type.type.uc_type,
                                10,
                                node.coord,
                            )

            else:
                # If there is no initialization then dim should be specified
                self._assert_semantic(
                    self.has_dim(node.type),
                    8,
                    self.lookup_array_declname(node.type).coord,
                )
                dimension1 = node.type.dim.value
                if isinstance(node.type.type, ArrayDecl):
                    # 2d array
                    dimension2 = node.type.type.dim.value
                    node.type.array_dim = [dimension1, dimension2]
                else:
                    # 1d array
                    node.type.array_dim = [dimension1]

    def visit_ID(self, node):
        # TODO: insert kind
        data_type = self.environment.lookup(node.name)
        self._assert_semantic(data_type is not None, 1, node.coord, node.name)
        node.uc_type = data_type
        # node.scope = len(self.environment.symtabs_lst) - 1

    def visit_Type(self, node):
        node.uc_type = self.typemap[node.name]

    def visit_BinaryOp(self, node):
        # Visit the left and right expression
        self.visit(node.lvalue)
        ltype = node.lvalue.uc_type
        self.visit(node.rvalue)
        rtype = node.rvalue.uc_type

        self._assert_semantic(ltype == rtype, 5, node.coord, node.op)

        self._assert_semantic(
            node.op in ltype.binary_ops or node.op in ltype.rel_ops,
            6,
            node.coord,
            node.op,
            f"type({ltype.typename})",
            f"type({rtype.typename})",
        )

        if node.op in ltype.rel_ops:
            node.uc_type = self.typemap["bool"]
        elif node.op in ltype.binary_ops:
            node.uc_type = ltype

    def visit_UnaryOp(self, node):
        self.visit(node.expr)
        operand_type = node.expr.uc_type

        self._assert_semantic(
            node.op in operand_type.unary_ops,
            25,
            node.coord,
            node.op,
            f"type({operand_type.typename})",
        )

        node.uc_type = operand_type

    def visit_Print(self, node):
        if node.expr is not None:
            self.visit(node.expr)
            vars_lst = (
                node.expr.exprs if isinstance(node.expr, ExprList) else [node.expr]
            )
            for var in vars_lst:
                if isinstance(var.uc_type, ArrayType):
                    self._assert_semantic(False, 21, var.coord, var.name)
                else:
                    self._assert_semantic(
                        var.uc_type in [CharType, BoolType, StringType, IntType],
                        20,
                        var.coord,
                    )

    def visit_Assert(self, node):
        self.visit(node.expr)
        expr_type = node.expr.uc_type
        self._assert_semantic(expr_type == BoolType, 3, node.expr.coord)

    def visit_ExprList(self, node):
        if node.exprs is not None:
            for _expr in node.exprs:
                self.visit(_expr)

    def visit_Read(self, node):
        self.visit(node.names)

        vars_lst = (
            node.names.exprs if isinstance(node.names, ExprList) else [node.names]
        )
        for var in vars_lst:
            self._assert_semantic(
                isinstance(var, ID) or isinstance(var, ArrayRef),
                22,
                var.coord,
                name=var.__class__.__name__,
            )

    def visit_If(self, node):
        self.visit(node.cond)
        cond_type = node.cond.uc_type if not isinstance(node.cond, Assignment) else None
        self._assert_semantic(cond_type == BoolType, 18, node.cond.coord)
        self.visit(node.iftrue)
        if node.iffalse is not None:
            self.visit(node.iffalse)

    def visit_While(self, node):
        # TALVEZ NÃO TENHA QUE ABRIR ESCOPO AQUI
        self.environment.push()
        self.environment.add_curr_loop(node)
        self.visit(node.cond)
        cond_type = node.cond.uc_type

        self._assert_semantic(
            cond_type == BoolType, 14, node.coord, ltype=f"type({cond_type.typename})"
        )
        self.visit(node.body)
        self.environment.pop()

    def visit_For(self, node):
        self.environment.push()
        self.environment.add_curr_loop(node)
        self.visit(node.init)
        self.visit(node.cond)
        cond_type = node.cond.uc_type
        self._assert_semantic(
            cond_type == BoolType, 14, node.coord, ltype=f"type({cond_type.typename})"
        )
        self.visit(node.next)
        self.visit(node.body)
        self.environment.pop()

    def visit_Break(self, node):
        self._assert_semantic(
            self.environment.get_curr_loop() is not None, 7, node.coord
        )
        node.bind = self.environment.get_curr_loop()

    def visit_Assignment(self, node):
        # visit right side
        self.visit(node.rvalue)
        rtype = node.rvalue.uc_type
        # visit left side (must be a location)
        _var = node.lvalue
        self.visit(_var)
        if isinstance(_var, ID):
            self._assert_semantic(
                self.environment.lookup(_var.name), 1, node.coord, name=_var.name
            )
        ltype = node.lvalue.uc_type
        # Check that assignment is allowed
        self._assert_semantic(
            ltype == rtype,
            4,
            node.coord,
            ltype=f"type({ltype.typename})",
            rtype=f"type({rtype.typename})",
        )
        # Check that assign_ops is supported by the type
        self._assert_semantic(
            node.op in ltype.assign_ops,
            5,
            node.coord,
            name=node.op,
            ltype=f"type({ltype.typename})",
        )


if __name__ == "__main__":
    # create argument parser
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "input_file", help="Path to file to be semantically checked", type=str
    )
    args = parser.parse_args()

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
