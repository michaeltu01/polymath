from unittest import TestCase

from libcst import Module, parse_module

from agent.logic.forge.logic_py_forge_constraint_generator import LogicPyForgeConstraintGenerator
from agent.logic.forge.logic_py_forge_data_structure_generator import LogicPyForgeDataStructureMetadata, DomainProps, ListProps, ClassProps


# MOCK VARIABLES

MOCK_DOMAINS = {
    "laptop": DomainProps(type_name="str", values=["green", "pink", "purple", "yellow"]),
    "name": DomainProps(type_name="str", values=["emily", "kimberly", "lauren", "samantha"]),
    "volcano": DomainProps(type_name="str", values=["lavadome", "scoriacone", "submarine", "supervolcano"]),
    "activity": DomainProps(type_name="str", values=["fluctuating", "increasing", "stable", "veryhigh"])
}

MOCK_CLASSES = {
    "Solution": ClassProps(isOneSig=True, fields=["volcanologists"]),
    "Volcanologist": ClassProps(isOneSig=False, fields=["laptop", "name", "volcano", "activity"])
}

MOCK_LIST_FIELDS = {
    "volcanologists": ListProps(type_name="Volcanologist", length=4)
}

MOCK_DS_METADATA = LogicPyForgeDataStructureMetadata(
    domains=MOCK_DOMAINS,
    classes=MOCK_CLASSES,
    list_fields=MOCK_LIST_FIELDS
)


def visit_module(module, ds_metadata=MOCK_DS_METADATA) -> LogicPyForgeConstraintGenerator:
    """
    Helper to visit a module and collect constraints.
    """
    constraints = LogicPyForgeConstraintGenerator(ds_metadata)
    source_module: Module = parse_module(module)
    source_module.visit(constraints)
    return constraints


class TestLogicPyForgeConstraintGenerator(TestCase):
    def __init__(self, methodName="runTest") -> None:
        super().__init__(methodName)
        self.maxDiff = None

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

    def test_forge_code(self) -> None:
        expected_forge_code = """pred solution {
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
        self.constraints = visit_module(self.__test_input)
        print(self.constraints.forge_code)
        self.assertEqual(self.constraints.forge_code, expected_forge_code)

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

class TestLogicPyForgeConstraintGeneratorDuplicate(TestCase):
    def __init__(self, methodName="runTest") -> None:
        super().__init__(methodName)
        self.maxDiff = None

    def test_duplicate_constraints(self) -> None:
        duplicate_constraint_clue = """def validate(solution: Solution) -> None:
    # The volcanologist who is monitoring the Scoria cone volcano is observing a Fluctuating activity level.
    scoriacone_scientist = nondet(solution.volcanologists)
    assume(scoriacone_scientist.volcano == "scoriacone")
    assert scoriacone_scientist.activity == "fluctuating\""""
        constraints = visit_module(duplicate_constraint_clue)
        expected_forge_code = """pred solution {
    some scoriacone_scientist: Volcanologist | {
        scoriacone_scientist.volcano = Scoriacone
        scoriacone_scientist.activity = Fluctuating
    }
}"""
        self.assertEqual(constraints.forge_code, expected_forge_code)

class TestLogicPyForgeConstraintGeneratorRegularAssignment(TestCase):
    def __init__(self, methodName="runTest") -> None:
        super().__init__(methodName)
        self.maxDiff = None

    def test_regular_assignment(self) -> None:
        regular_assignment = """def validate(solution: Solution) -> None:
    supervolcano_scientist = solution.volcanologists[2]"""
        constraints = visit_module(regular_assignment)
        expected_forge_code = """pred solution {
    some supervolcano_scientist: Volcanologist | {
        supervolcano_scientist = Solution.volcanologists[2]
    }
}"""
        self.assertEqual(constraints.forge_code, expected_forge_code)