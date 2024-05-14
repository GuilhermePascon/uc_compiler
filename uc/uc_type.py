from typing import List


class uCType:
    """
    Class that represents a type in the uC language.  Basic
    Types are declared as singleton instances of this type.
    """

    def __init__(
        self, name, binary_ops=set(), unary_ops=set(), rel_ops=set(), assign_ops=set()
    ):
        """
        You must implement yourself and figure out what to store.
        """
        self.typename = name
        self.unary_ops = unary_ops
        self.binary_ops = binary_ops
        self.rel_ops = rel_ops
        self.assign_ops = assign_ops


# Create specific instances of basic types. You will need to add
# appropriate arguments depending on your definition of uCType
IntType = uCType(
    "int",
    unary_ops={"-", "+"},
    binary_ops={"+", "-", "*", "/", "%"},
    rel_ops={"==", "!=", "<", ">", "<=", ">="},
    assign_ops={"="},
)
# TODO: add other basic types
# CharType = uCType("char", ...)
CharType = uCType(
    "char",
    unary_ops={},
    binary_ops={},
    rel_ops={"==", "!=", "&&", "||"},
    assign_ops={"="},
)

BoolType = uCType(
    "bool",
    unary_ops={"!"},
    binary_ops={},
    rel_ops={"==", "!=", "&&", "||"},
    assign_ops={"="},
)

StringType = uCType(
    "string",
    unary_ops={},
    binary_ops={"+"},
    rel_ops={"==", "!="},
    assign_ops={},
)

VoidType = uCType("void")


# TODO: add array and function types
# Array and Function types need to be instantiated for each declaration
class ArrayType(uCType):
    def __init__(self, element_type: uCType, size: int = None):
        """
        type: Any of the uCTypes can be used as the array's type. This
              means that there's support for nested types, like matrices.
        size: Integer with the length of the array.
        """
        self.type = element_type
        self.size = size
        super().__init__("array", rel_ops={"==", "!="})


class FuncType(uCType):
    def __init__(
        self, return_type: uCType, arguments_type: List, has_return: bool = False
    ):
        """
        return_type: Any of the basic uCTypes (int, char, bool and string) can be used as the functions's type.
        arguments_type: Type of arguments to call.

        """
        self.return_type = return_type
        self.arguments_type = arguments_type
        super().__init__(
            "func",
            unary_ops=return_type.unary_ops,
            binary_ops=return_type.binary_ops,
            rel_ops=return_type.rel_ops,
            assign_ops=return_type.assign_ops,
        )
