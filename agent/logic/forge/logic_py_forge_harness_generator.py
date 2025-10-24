"""
Forge Harness Generator

This module should combine the data structure and constraint generators
to produce a complete Forge "h" (i.e., a program that can be solved by Forge).

TODO:
- Integrate data structure and constraint generators.
- Define the output format for a Forge harness.
- Provide a static method to generate the full Forge code from a CST.
"""

from abc import ABC
from libcst import MetadataWrapper

from agent.logic.forge.logic_py_forge_data_structure_generator import LogicPyForgeDataStructureGenerator
from agent.logic.forge.logic_py_forge_constraint_generator import LogicPyForgeConstraintGenerator

SOLUTION_CLASS_NAME = "Solution"

class LogicPyForgeHarnessGenerator(ABC):
    """
    Converts LogicPy data structures and constraints to Forge code.
    """

    @staticmethod
    def generate(metadata: MetadataWrapper) -> str:
        """
        Generate Forge code from the provided CST metadata.

        - Visit the CST to extract data structures and constraints.
        - Combine them into a single Forge program.
        - Return the Forge code as a string.
        """

        data_structures = LogicPyForgeDataStructureGenerator()
        metadata.visit(data_structures)
        constraints = LogicPyForgeConstraintGenerator()
        metadata.visit(constraints)

        solution_type: str = ""
        solution_field: str = ""

        # Extract solution type and field from data structures
        for field in data_structures.classes[SOLUTION_CLASS_NAME].fields:
            if field in data_structures.list_fields:
                solution_field = field
                solution_type = data_structures.list_fields[field].type_name
                break  # Use the first matching field

        def _wellformed() -> str:
            lines = []

            # Wellformedness predicate header
            lines.append("pred wellformed {")

            # Multiplicity constraint
            for field in data_structures.classes[SOLUTION_CLASS_NAME].fields:
                if field in data_structures.list_fields:
                    multiplicityConstraint = f"    #{{{SOLUTION_CLASS_NAME}.{field}}} = {data_structures.list_fields[field].length}"
                    lines.append(multiplicityConstraint)
            
            # Unique one-to-one constraints
            for unique_field in data_structures.unique_fields:
                some_var_name = unique_field[0]
                unique_field_constraint = f"    all {some_var_name}: {unique_field.capitalize()} | some {unique_field}.{some_var_name}"
                lines.append(unique_field_constraint)

            for list_field in data_structures.list_fields.keys():
                some_var_name = list_field[0]
                list_type = data_structures.list_fields[list_field].type_name
                list_field_constraint = f"    all {some_var_name}: {list_type.capitalize()} | some {list_field}.{some_var_name}"
                lines.append(list_field_constraint)
            
            lines.append("}")
            wellformed_code = "\n".join(lines)
            return wellformed_code


        # Combine Forge code sections
        return f"""#lang forge

-- DATA STRUCTURES
        
{getattr(data_structures, 'forge_code', '')}


-- HELPER PREDICATES

{_wellformed()}

pred immediatelyBefore[va, vb: {solution_type if solution_type else "MISSING_TYPE"}] {{
    {SOLUTION_CLASS_NAME}.{solution_field if solution_field else "MISSING_FIELD"}[add[({SOLUTION_CLASS_NAME}.{solution_field if solution_field else "MISSING_FIELD"}).va, 1]] = vb
}}


-- SOLUTION CONSTRAINTS

{getattr(constraints, 'forge_code', '')}

run {{ solution and wellformed }}
"""
