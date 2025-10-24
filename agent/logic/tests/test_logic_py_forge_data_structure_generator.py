from unittest import TestCase

from libcst import Module, parse_module

from agent.logic.forge.logic_py_forge_data_structure_generator import LogicPyForgeDataStructureGenerator, ClassProps, DomainProps, ListProps

class TestLogicPyForgeDataStructureGenerator(TestCase):

    def __init__(self, methodName="runTest"):
        super().__init__(methodName)
        self.maxDiff = None

        # Parse the example Python program
        self.visit_module()

    def visit_module(self) -> None:
        self.__test_input = """
class Volcanologist:
    laptop: Unique[Domain[str, "green", "pink", "purple", "yellow"]]  # Unique laptop colors
    name: Unique[Domain[str, "emily", "kimberly", "lauren", "samantha"]]  # Unique names
    volcano: Unique[Domain[str, "lavadome", "scoriacone", "submarine", "supervolcano"]]  # Unique volcano types
    activity: Unique[Domain[str, "fluctuating", "increasing", "stable", "veryhigh"]]  # Unique activity levels

class Solution:
    volcanologists: list[Volcanologist, 4]  # List of 4 volcanologists
"""
        self.__expected_forge_code = """abstract sig Laptop {}
one sig Green extends Laptop {}
one sig Pink extends Laptop {}
one sig Purple extends Laptop {}
one sig Yellow extends Laptop {}
abstract sig Name {}
one sig Emily extends Name {}
one sig Kimberly extends Name {}
one sig Lauren extends Name {}
one sig Samantha extends Name {}
abstract sig Volcano {}
one sig Lavadome extends Volcano {}
one sig Scoriacone extends Volcano {}
one sig Submarine extends Volcano {}
one sig Supervolcano extends Volcano {}
abstract sig Activity {}
one sig Fluctuating extends Activity {}
one sig Increasing extends Activity {}
one sig Stable extends Activity {}
one sig Veryhigh extends Activity {}

sig Volcanologist {
    laptop: one Laptop,
    name: one Name,
    volcano: one Volcano,
    activity: one Activity
}
one sig Solution {
    volcanologists: pfunc Int->Volcanologist
}"""
        self.data_structures = LogicPyForgeDataStructureGenerator()
        source_module: Module = parse_module(self.__test_input)
        source_module.visit(self.data_structures)

    def test_forge_code(self) -> None:
        print(self.data_structures.forge_code)
        self.assertEqual(self.data_structures.forge_code, self.__expected_forge_code)
    
    def test_classes(self) -> None:
        expected_classes = {
            "Solution": ClassProps(isOneSig=True, fields=["volcanologists"]),
            "Volcanologist": ClassProps(isOneSig=False, fields=["laptop", "name", "volcano", "activity"])
        }
        self.assertEqual(self.data_structures.classes, expected_classes)
    
    def test_domains(self) -> None:
        expected_domains = {
            "laptop": DomainProps(type_name="str", values=["green", "pink", "purple", "yellow"]),
            "name": DomainProps(type_name="str", values=["emily", "kimberly", "lauren", "samantha"]),
            "volcano": DomainProps(type_name="str", values=["lavadome", "scoriacone", "submarine", "supervolcano"]),
            "activity": DomainProps(type_name="str", values=["fluctuating", "increasing", "stable", "veryhigh"])
        }
        self.assertEqual(self.data_structures.domains, expected_domains)
    
    def test_list_fields(self) -> None:
        expected_list_fields = {
            "volcanologists": ListProps(type_name="Volcanologist", length=4)
        }
        self.assertEqual(self.data_structures.list_fields, expected_list_fields)