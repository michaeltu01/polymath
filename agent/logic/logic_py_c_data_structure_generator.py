# Copyright (c) Meta Platforms, Inc. and affiliates.
# All rights reserved.
#
# This source code is licensed under the license found in the
# LICENSE file in the root directory of this source tree.

from abc import ABC
from typing import Optional, Sequence

from libcst import CSTVisitor

from libcst._nodes.expression import (
    Arg,
    BaseAssignTargetExpression,
    BaseElement,
    BaseExpression,
    BaseSlice,
    Call,
    Index,
    Integer,
    List,
    Name,
    SimpleString,
    Subscript,
)
from libcst._nodes.module import Module
from libcst._nodes.statement import AnnAssign, ClassDef


class FieldDomain(ABC):
    """
    Parent class for all LogicPy `Domain` type annotations.
    """

    def get_allowed_values(self) -> list[str]:
        """
        Returns all allowed values for the domain as C expressions.
        """
        ...


class RangeFieldDomain(FieldDomain):
    """
    `FieldDomain` implementation for LogicPy range-based domains, e.g.
    `Domain[int, range(0, 10)]`.
    """

    def __init__(self, start: Arg, stop: Arg) -> None:
        first: int = RangeFieldDomain.to_int(start)
        last: int = RangeFieldDomain.to_int(stop)
        self.allowed_values = [str(number) for number in range(first, last)]

    def get_allowed_values(self) -> list[str]:
        return self.allowed_values

    @staticmethod
    def to_int(arg: Arg) -> int:
        """
        Converts an argument to `range(n, m)` to a C `int` literal.
        """
        value: BaseExpression = arg.value
        if not isinstance(value, Integer):
            raise ValueError(f"Expected integer, got {value}")
        return int(value.value)


class ValuesFieldDomain(FieldDomain):
    """
    `FieldDomain` implementation for LogicPy values-based domains, e.g.
    `Domain[str, "Hello", "How are you?"]`.
    """

    def __init__(self, allowed_values: list[str]) -> None:
        self.allowed_values = allowed_values

    def get_allowed_values(self) -> list[str]:
        return self.allowed_values


class FieldInitialiser:
    """
    Represents a LogicPy field with all information necessary to correctly
    initialise and constrain it in a C harness.
    """

    def __init__(self) -> None:
        self.class_name: Optional[str] = None
        self.field_name: Optional[str] = None
        self.c_type: str = "void"
        self.init_fn_name: str = ""
        self.is_unique: bool = False
        self.domain: Optional[FieldDomain] = None
        self.array_size: Optional[int] = None
        self.value: Optional[BaseExpression] = None


# Maps Python types to C types.
_PYTHON_TO_C_TYPE: dict[str, str] = {
    "int": "int",
    "str": "const char *",
}


class LogicPyCDataStructureGenerator(CSTVisitor):
    """
    Converts LogicPy data structures with `Unique` and `Domain` type
    annotations to an equivalent C `struct`.
    """

    def __init__(self, module: Module) -> None:
        self.module = module
        self.field_initialisers: list[FieldInitialiser] = []
        self.current_class: Optional[str] = None
        self.seen_classes = set()
        self.last_field_initialiser = FieldInitialiser()
        self.c_harness = ""
        self.is_in_init_fn = False

    def visit_ClassDef(self, node: ClassDef) -> Optional[bool]:
        self.current_class = node.name.value
        self.c_harness += f"""struct {self.current_class} {{
"""

    def leave_ClassDef(self, original_node: ClassDef) -> None:
        self.c_harness += """};

"""
        for field_initialiser in self.field_initialisers:
            if field_initialiser.domain is not None:
                domain: FieldDomain = field_initialiser.domain
                allowed_values: list[str] = domain.get_allowed_values()
                self.c_harness += f"""static {field_initialiser.c_type} {field_initialiser.class_name}_{field_initialiser.field_name}[] = {{{", ".join(allowed_values)}}};
"""
                if field_initialiser.is_unique:
                    self.c_harness += f"""static bool {field_initialiser.class_name}_{field_initialiser.field_name}_used[{len(allowed_values)}];
"""

        has_static_field_initialiser_constants: bool = any(
            field_initialiser.domain is not None
            for field_initialiser in self.field_initialisers
        )
        if has_static_field_initialiser_constants:
            self.c_harness += f"\n"

        self.c_harness += f"""static void init_{self.current_class}(struct {self.current_class} * instance) {{
"""
        self.is_in_init_fn = True
        for field_initialiser in self.field_initialisers:
            if field_initialiser.is_unique and field_initialiser.domain is not None:
                self.c_harness += f"""    __CPROVER_unique_domain(instance->{field_initialiser.field_name}, {field_initialiser.class_name}_{field_initialiser.field_name});
"""
            elif field_initialiser.array_size is not None:
                if field_initialiser.value is not None:
                    self.c_harness += f"    __CPROVER_array_copy(instance->{field_initialiser.field_name}, ({field_initialiser.c_type}[])"
                    field_initialiser.value.visit(self)
                    self.c_harness += ");\n"
                else:
                    self.c_harness += f"""    for (size_t i = 0; i < sizeof(instance->{field_initialiser.field_name}) / sizeof(instance->{field_initialiser.field_name}[0]); ++i) {{
        init_{field_initialiser.init_fn_name}(&instance->{field_initialiser.field_name}[i]);
    }}
"""
            elif field_initialiser.value is not None:
                self.c_harness += f"    instance->{field_initialiser.field_name} = "
                field_initialiser.value.visit(self)
                self.c_harness += ";\n"
            elif field_initialiser.c_type.startswith("struct "):
                self.c_harness += f"    init_{field_initialiser.init_fn_name}(&instance->{field_initialiser.field_name});\n"
        self.c_harness += f"""}}

"""
        self.is_in_init_fn = False
        self.field_initialisers.clear()
        self.seen_classes.add(self.current_class)
        self.current_class = None

    def visit_Integer(self, node: Integer) -> Optional[bool]:
        if self.is_in_init_fn:
            self.c_harness += self.module.code_for_node(node)

    def visit_SimpleString(self, node: SimpleString) -> Optional[bool]:
        if self.is_in_init_fn:
            self.c_harness += self.module.code_for_node(node)

    def visit_List(self, node: List) -> Optional[bool]:
        if self.is_in_init_fn:
            self.c_harness += "{"
            elements: Sequence[BaseElement] = node.elements
            if elements:
                elements[0].visit(self)
                for element in node.elements[1:]:
                    self.c_harness += ", "
                    element.visit(self)
            self.c_harness += "}"
            return False

    def visit_Name(self, node: Name) -> Optional[bool]:
        name: str = node.value
        c_type: Optional[str] = _PYTHON_TO_C_TYPE.get(name)
        if c_type is not None:
            self.last_field_initialiser.c_type = c_type
            self.last_field_initialiser.init_fn_name = c_type
        elif name in self.seen_classes:
            self.last_field_initialiser.c_type = f"struct {name}"
            self.last_field_initialiser.init_fn_name = name

    def visit_Subscript(self, node: Subscript) -> Optional[bool]:
        value: BaseExpression = node.value
        if isinstance(value, Name):
            name: str = value.value
            if name == "Unique":
                self.last_field_initialiser.is_unique = True
            elif name == "Domain":
                allowed_values: list[str] = []
                for element in node.slice[1:]:
                    slice: BaseSlice = element.slice
                    if isinstance(slice, Index):
                        value: BaseExpression = slice.value
                        if isinstance(value, Call):
                            func_name: BaseExpression = value.func
                            if isinstance(func_name, Name):
                                if func_name.value == "range":
                                    start: Arg = value.args[0]
                                    stop: Arg = value.args[1]
                                    self.last_field_initialiser.domain = (
                                        RangeFieldDomain(start, stop)
                                    )
                        elif isinstance(value, SimpleString):
                            allowed_values.append(value.value)

                if allowed_values:
                    self.last_field_initialiser.domain = ValuesFieldDomain(
                        allowed_values
                    )
            elif name == "list":
                slice: BaseSlice = node.slice[1].slice
                if isinstance(slice, Index):
                    value: BaseExpression = slice.value
                    if isinstance(value, Integer):
                        self.last_field_initialiser.array_size = int(value.value)

    def leave_AnnAssign(self, original_node: AnnAssign) -> None:
        if self.current_class is not None:
            value: Optional[BaseExpression] = original_node.value
            if value is not None:
                self.last_field_initialiser.value = value
            target: BaseAssignTargetExpression = original_node.target
            if isinstance(target, Name):
                field_name: str = target.value
                self.last_field_initialiser.field_name = field_name
                self.last_field_initialiser.class_name = self.current_class
                self.field_initialisers.append(self.last_field_initialiser)

                array_size: Optional[int] = self.last_field_initialiser.array_size
                array_suffix: str = f"[{array_size}]" if array_size is not None else ""
                self.c_harness += f"""    {self.last_field_initialiser.c_type} {field_name}{array_suffix};
"""
                self.last_field_initialiser = FieldInitialiser()
