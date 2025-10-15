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

class LogicPyForgeHarnessGenerator(ABC):
    """
    Converts LogicPy data structures and constraints to Forge code.
    """

    @staticmethod
    def generate(metadata: MetadataWrapper) -> str:
        """
        Generate Forge code from the provided CST metadata.

        TODO:
        - Visit the CST to extract data structures and constraints.
        - Combine them into a single Forge program.
        - Return the Forge code as a string.
        """
        data_structures = LogicPyForgeDataStructureGenerator()
        metadata.visit(data_structures)
        constraints = LogicPyForgeConstraintGenerator(
            getattr(data_structures, 'class_metadata', None),
            getattr(data_structures, 'attribute_metadata', None)
        )
        metadata.visit(constraints)
        # Combine Forge code sections
        return f"""#lang forge

{getattr(data_structures, 'forge_code', '')}

{getattr(constraints, 'forge_code', '')}
"""
