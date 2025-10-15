from unittest import TestCase

from libcst import Module, parse_module

from agent.logic.forge.logic_py_forge_data_structure_generator import LogicPyForgeDataStructureGenerator

class TestLogicPyForgeDataStructureGenerator(TestCase):

    def __init__(self, methodName="runTest"):
        super().__init__(methodName)
        self.maxDiff = None

        # Parse the example Python program
        self.visit_module()

    def visit_module(self) -> None:
        self.__test_input = """
class Volcanologist:
    id: Unique[Domain[int, range(1, 5)]]  # Each volcanologist has a unique ID from 1 to 4
    laptop: Unique[Domain[str, "green", "pink", "purple", "yellow"]]  # Unique laptop colors
    name: Unique[Domain[str, "emily", "kimberly", "lauren", "samantha"]]  # Unique names
    volcano: Unique[Domain[str, "lavadome", "scoriacone", "submarine", "supervolcano"]]  # Unique volcano types
    activity: Unique[Domain[str, "fluctuating", "increasing", "stable", "veryhigh"]]  # Unique activity levels

class Solution:
    volcanologists: list[Volcanologist, 4]  # List of 4 volcanologists
"""
        self.__expected_forge_code = """abstract sig Volcanologist {}
abstract sig Id {}
one sig Id1 extends Id {}
one sig Id2 extends Id {}
one sig Id3 extends Id {}
one sig Id4 extends Id {}
abstract sig Laptop {}
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

one sig Solution {
    id: func Volcanologist -> Id,
    laptop: func Volcanologist -> Laptop,
    name: func Volcanologist -> Name,
    volcano: func Volcanologist -> Volcano,
    activity: func Volcanologist -> Activity,
}
"""
        self.data_structures = LogicPyForgeDataStructureGenerator()
        source_module: Module = parse_module(self.__test_input)
        source_module.visit(self.data_structures)

    def test_forge_code(self) -> None:
        print(self.data_structures.forge_code)
        self.assertEqual(self.data_structures.forge_code, self.__expected_forge_code)
    
    def test_classes(self) -> None:
        expected_classes = {
            "Solution": [
                "volcanologists"
            ],
            "Volcanologist": [
                "id",
                "laptop",
                "name",
                "volcano",
                "activity"
            ]
        }
        self.assertEqual(self.data_structures.classes, expected_classes)
    
    def test_domains(self) -> None:
        expected_domains = {
            "id": ("int", ["1", "2", "3", "4"]),
            "laptop": ("str", ["green", "pink", "purple", "yellow"]),
            "name": ("str", ["emily", "kimberly", "lauren", "samantha"]),
            "volcano": ("str", ["lavadome", "scoriacone", "submarine", "supervolcano"]),
            "activity": ("str", ["fluctuating", "increasing", "stable", "veryhigh"])
        }
        self.assertEqual(self.data_structures.domains, expected_domains)