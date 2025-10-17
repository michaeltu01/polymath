from unittest import TestCase

from libcst import Module, parse_module

from agent.logic.forge.logic_py_forge_constraint_generator import LogicPyForgeConstraintGenerator

class TestLogicPyForgeConstraintGenerator(TestCase):
    def __init__(self, methodName="runTest") -> None:
        super().__init__(methodName)
        self.maxDiff = None
        
        # Parse the example Python program
        self.visit_module()
    
    def visit_module(self) -> None:
        self.__test_input = """

"""
        self.__expected_forge_code = """
"""
        self.constraints = LogicPyForgeConstraintGenerator()
        source_module: Module = parse_module(self.__test_input)
        source_module.visit(self.constraints)