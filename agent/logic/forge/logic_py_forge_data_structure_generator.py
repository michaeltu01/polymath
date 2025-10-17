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

class LogicPyForgeDataStructureGenerator(CSTVisitor):
    """
    Visits the CST to extract Logic.py data structures and prepares them for Forge code generation.
    """
    def __init__(self):
        super().__init__()
        # TODO: Initialize data structures to store class/type info
        self.domains = {} # field -> (type_name, [values])
        self.classes = {} # class_name -> [field_names]
        self.forge_code = ""
        self.unique_fields = set()

    # TODO: Implement visit_ClassDef and other relevant visitor methods
    def visit_ClassDef(self, node: ClassDef):
        class_name = node.name.value
        self.current_class = class_name
        self.classes[class_name] = []
    
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
                self.domains[field_name] = (domain_type, domain_values)
                self.classes[self.current_class] = self.classes[self.current_class] + [field_name]
            return

        # TODO: handle other annotations (e.g., list[Volcanologist, 4]) so Solution.volcanologists is captured
        # Example: detect Subscript(Name("list"), elements=[Volcanologist, 4]) and record the field on Solution.

        # Handle list[T, N]
        # Unroll the type T for N elements
        if isinstance(node, Subscript) and isinstance(node.value, Name) and node.value.value == "list":
            # FIXME: Fix the `list` primitive conversion
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
                        self.domains[list_type] = (list_type, [f"{list_type.capitalize() if list_type.islower() else list_type}{i}" for i in range(1, list_length + 1)])
                        self.classes[self.current_class] = self.classes[self.current_class] + [field_name]
            return

    # TODO: Add methods to output Forge data structure code as a string
    def leave_Module(self, original_node):
        # Generate Forge code for domains
        forge_lines = []

        # Generate the Forge sigs corresponding to the Logic.py domains
        for field, (type_name, values) in self.domains.items():
            forge_lines.append(f"abstract sig {field.capitalize() if field.islower() else field} {{}}")
            for v in values:
                sig_name = v.capitalize() if v.islower() else v
                forge_lines.append(f"one sig {sig_name} extends {field.capitalize() if field.islower() else field} {{}}")

        # Solution sig
        forge_lines.append("")
        forge_lines.append("one sig Solution {")
        for field, (type_name, values) in self.domains.items():
            if field not in self.classes:
                forge_lines.append(f"    {field}:{" func " if field in self.unique_fields else " "}Volcanologist -> {field.capitalize() if field.islower() else field},")
        forge_lines.append("}")
        self.forge_code = "\n".join(forge_lines)
