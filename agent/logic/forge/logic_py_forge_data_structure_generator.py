"""
Forge Data Structure Generator

This module should implement the logic to convert Logic.py class definitions
into Forge data structures.

TODO:
- Implement the visitor pattern to traverse the CST and extract Logic.py classes.
- Map Logic.py types and constraints to Forge equivalents.
- Store any metadata needed for constraint generation.
"""

from libcst import AnnAssign, CSTVisitor, Call, ClassDef, Index, Integer, MetadataWrapper, Module, Name, SimpleString, List, Subscript, SubscriptElement
from libcst.display import dump
from dataclasses import dataclass


@dataclass
class DomainProps:
    type_name: str
    values: list[any]

@dataclass
class ClassProps:
    isOneSig: bool
    fields: list[str]

@dataclass
class ListProps:
    type_name: str
    length: int

class LogicPyForgeDataStructureGenerator(CSTVisitor):
    """
    Visits the CST to extract Logic.py data structures and prepares them for Forge code generation.
    """
    def __init__(self):
        super().__init__()
        # TODO: Initialize data structures to store class/type info
        self.domains: dict[str, DomainProps] = {} # field -> DomainProps
        self.classes: dict[str, ClassProps] = {} # class_name -> ClassProps
        self.list_fields: dict[str, ListProps] = {} # field -> ListProps
        self.forge_code: str = ""
        self.unique_fields: set = set()

    # TODO: Implement visit_ClassDef and other relevant visitor methods
    def visit_ClassDef(self, node: ClassDef):
        class_name = node.name.value
        self.current_class = class_name
        self.classes[class_name] = ClassProps(isOneSig=(class_name == "Solution"), fields=[])
    
    def visit_AnnAssign(self, node: AnnAssign):
        field_name = getattr(node.target, "value", None)

        node = node.annotation

        # Unwrap Unique[...] -> inner
        if node.annotation:
            node = node.annotation
            if isinstance(node, Subscript) and isinstance(node.value, Name) and node.value.value == "Unique":
                if node.slice:
                    subEl = node.slice[0] # SubscriptElement
                    index = subEl.slice # Index
                    subScript = index.value # Domain Subscript Element
                    node = subScript
                self.unique_fields.add(field_name)

        # Handle Domain[T, ...] where ann is now Subscript(Name("Domain"), ...)
        if isinstance(node, Subscript) and isinstance(node.value, Name) and node.value.value == "Domain":
            domain_type = None
            domain_values: list[str] = []

            elements = node.slice or []
            if elements:
                # First element is the logical type name (e.g., int/str/Name/Laptop/etc.)
                first: SubscriptElement = elements[0]
                firstIndex: Index = first.slice
                if isinstance(firstIndex.value, Name):
                    domain_type = firstIndex.value.value

                # Remaining elements are literals or constructors (e.g., "green", range(...))
                for el in elements[1:]:
                    elIndex: Index = el.slice
                    v = elIndex.value
                    if isinstance(v, SimpleString):
                        domain_values.append(v.evaluated_value)
                    elif isinstance(v, Call) and isinstance(v.func, Name) and v.func.value == "range":
                        # Expand simple range(start, stop)
                        args = v.args
                        if len(args) >= 2 and all(a.value.__class__.__name__ == "Integer" for a in args[:2]):
                            start = int(args[0].value.value)
                            stop = int(args[1].value.value)
                            domain_values.extend([str(i) for i in range(start, stop)])
                        # TODO: handle range with step if needed

            # Record field under the current class
            if field_name:
                self.domains[field_name] = DomainProps(type_name=domain_type, values=domain_values)
                self.classes[self.current_class].fields = self.classes[self.current_class].fields + [field_name]
            return

        # TODO: handle other annotations (e.g., list[Volcanologist, 4]) so Solution.volcanologists is captured
        # Example: detect Subscript(Name("list"), elements=[Volcanologist, 4]) and record the field on Solution.

        # Handle list[T, N]
        # Add list fields to class variable `list_fields`
        if isinstance(node, Subscript) and isinstance(node.value, Name) and node.value.value == "list":
            elements = node.slice or []
            if elements and len(elements) >= 1:
                first: SubscriptElement = elements[0]
                firstIndex: Index = first.slice
                second: SubscriptElement = elements[1]
                secondIndex: Index = second.slice
                list_type: str

                if isinstance(firstIndex.value, Name):
                    list_type = firstIndex.value.value
                
                if isinstance(secondIndex.value, Integer):
                    list_length = int(secondIndex.value.value)
                    if field_name:
                        self.classes[self.current_class].fields = self.classes[self.current_class].fields + [field_name]
                        self.list_fields[field_name] = ListProps(type_name=list_type, length=list_length)
            return

    # TODO: Add methods to output Forge data structure code as a string
    def leave_Module(self, original_node):
        # Generate Forge code for domains
        forge_lines = []

        # Generate the Forge abstract sigs and one sigs corresponding to the Logic.py domains
        for field, domain_props in self.domains.items():
            values = domain_props.values

            field_name = field.capitalize() if field.islower() else field
            forge_lines.append(f"abstract sig {field_name} {{}}")
            for v in values:
                sig_name = v.capitalize() if v.islower() else v
                forge_lines.append(f"one sig {sig_name} extends {field_name} {{}}")

        # Generate Forge sigs corresponding to classes
        forge_lines.append("")
        for class_name, class_props in self.classes.items():
            sig_annotation = "one " if class_props.isOneSig else ""
            forge_lines.append(f"{sig_annotation}sig {class_name} {{")
            for i, field in enumerate(class_props.fields):
                field_type: str
                if field in self.list_fields:
                    field_type = f"pfunc Int->{self.list_fields[field].type_name}"
                else:
                    field_annotation = "one " if field in self.unique_fields else ""
                    field_type = f"{field_annotation}{field.capitalize() if field.islower() else field}"
                
                comma = "," if i < len(class_props.fields) - 1 else ""
                forge_lines.append(f"    {field}: {field_type}{comma}")
            forge_lines.append("}")
        
        self.forge_code = "\n".join(forge_lines)
