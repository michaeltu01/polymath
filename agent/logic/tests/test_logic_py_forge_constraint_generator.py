from unittest import TestCase

from libcst import Module, parse_module

from agent.logic.forge.logic_py_forge_constraint_generator import LogicPyForgeConstraintGenerator, ForgeConstraint, ForgeExpr, ForgePredicateCall, ForgeAttributeAccess, ForgeFunctionLookup, ForgeOperator, ForgeSymbol

class TestLogicPyForgeConstraintGenerator(TestCase):
    def __init__(self, methodName="runTest") -> None:
        super().__init__(methodName)
        self.maxDiff = None
        
        # Parse the example Python program
        self.visit_module()
    
    def visit_module(self) -> None:
        self.__test_input = """
def validate(solution: Solution) -> None:
    # The volcanologist monitoring a volcano with a Very high activity level is in the second position.
    very_high_volcanologist = nondet(solution.volcanologists)
    assume(very_high_volcanologist.activity == "veryhigh")
    assert immediatelyBefore(solution.volcanologists[1], very_high_volcanologist)

    # The scientist studying the Supervolcano is in the third position.
    supervolcano_volcanologist = nondet(solution.volcanologists)
    assume(supervolcano_volcanologist.volcano == "supervolcano")
    assert immediatelyBefore(supervolcano_volcanologist, solution.volcanologists[2])

    # The scientist observing a volcano with a Stable activity level is next to Samantha.
    stable_volcanologist = nondet(solution.volcanologists)
    assume(stable_volcanologist.activity == "stable")
    samantha_volcanologist = nondet(solution.volcanologists)
    assume(samantha_volcanologist.name == "samantha")
    assert immediatelyBefore(stable_volcanologist, samantha_volcanologist) or immediatelyBefore(samantha_volcanologist, stable_volcanologist)
"""

        self.__expected_forge_code = """pred solution {
    some very_high_volcanologist, supervolcano_volcanologist, stable_volcanologist, samantha_volcanologist: Volcanologist | {
        very_high_volcanologist.activity = Veryhigh
        immediatelyBefore[Solution.volcanologists[1], very_high_volcanologist]
        supervolcano_volcanologist.volcano = Supervolcano
        immediatelyBefore[supervolcano_volcanologist, Solution.volcanologists[2]]
        stable_volcanologist.activity = Stable
        samantha_volcanologist.name = Samantha
        immediatelyBefore[stable_volcanologist, samantha_volcanologist] or immediatelyBefore[samantha_volcanologist, stable_volcanologist]
    }
}"""
        self.constraints = LogicPyForgeConstraintGenerator()
        source_module: Module = parse_module(self.__test_input)
        source_module.visit(self.constraints)

    def test_forge_code(self) -> None:
        # print(self.constraints.forge_code)
        self.assertEqual(self.constraints.forge_code, self.__expected_forge_code)

    def test_constraint_extraction(self) -> None:
        """
        self.expected_constraints = {
            "very_high_volcanologist": ForgeExpr(operator=ForgeOperator.EQUALS, lhs=ForgeAttributeAccess(object=ForgeSymbol(name="very_high_volcanologist"), attr_name=ForgeSymbol(name="activity"))),
            "supervolcano_volcanologist": ...,
            "stable_volcanologist": ...,
            "samantha_volcanologist": ...,
        }
        """
        # print(self.constraints.nondet_vars_to_constraints)