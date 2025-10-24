from unittest import TestCase
from libcst import Module, parse_module

from agent.logic.forge.logic_py_forge_harness_generator import LogicPyForgeHarnessGenerator

class TestLogicPyForgeHarnessGenerator(TestCase):

    def __init__(self, methodName="runTest"):
        super().__init__(methodName)
        self.maxDiff = None

        self.source_code = """class Volcanologist:
    laptop: Unique[Domain[str, "green", "pink", "purple", "yellow"]]  # Unique laptop colors
    name: Unique[Domain[str, "emily", "kimberly", "lauren", "samantha"]]  # Unique names
    volcano: Unique[Domain[str, "lavadome", "scoriacone", "submarine", "supervolcano"]]  # Unique volcano types
    activity: Unique[Domain[str, "fluctuating", "increasing", "stable", "veryhigh"]]  # Unique activity levels

class Solution:
    volcanologists: list[Volcanologist, 4]  # List of 4 volcanologists


def validate(solution: Solution) -> None:
    # The volcanologist monitoring a volcano with a Very high activity level is in the second position.
    very_high_volcanologist = nondet(solution.volcanologists)
    assume(very_high_volcanologist.activity == "veryhigh")
    assert immediatelyBefore(solution.volcanologists[1], very_high_volcanologist)

    # The scientist studying the Supervolcano is in the third position.
    supervolcano_volcanologist = nondet(solution.volcanologists)
    assume(supervolcano_volcanologist.volcano == "supervolcano")
    assert immediatelyBefore(supervolcano_volcanologist, solution.volcanologists[2])

    # The scientist who is monitoring the Lava dome volcano is immediately after the scientist studying the Supervolcano.
    lavadome_volcanologist = nondet(solution.volcanologists)
    assume(lavadome_volcanologist.volcano == "lavadome")
    assert immediatelyBefore(supervolcano_volcanologist, lavadome_volcanologist)

    # The volcanologist who is monitoring the Scoria cone volcano is observing a Fluctuating activity level.
    scoriacone_volcanologist = nondet(solution.volcanologists)
    assume(scoriacone_volcanologist.volcano == "scoriacone")
    assume(scoriacone_volcanologist.activity == "fluctuating")

    # Lauren is in the second position.
    lauren_volcanologist = nondet(solution.volcanologists)
    assume(lauren_volcanologist.name == "lauren")
    assert immediatelyBefore(lauren_volcanologist, solution.volcanologists[1])

    # The scientist observing a volcano with a Stable activity level is next to Samantha.
    stable_volcanologist = nondet(solution.volcanologists)
    assume(stable_volcanologist.activity == "stable")
    samantha_volcanologist = nondet(solution.volcanologists)
    assume(samantha_volcanologist.name == "samantha")
    assert immediatelyBefore(stable_volcanologist, samantha_volcanologist) or immediatelyBefore(samantha_volcanologist, stable_volcanologist)

    # The volcanologist studying the Submarine volcano is immediately after the scientist using the Yellow laptop.
    yellow_laptop_volcanologist = nondet(solution.volcanists)
    assume(yellow_laptop_volcanologist.laptop == "yellow")
    submarine_volcanologist = nondet(solution.volcanologists)
    assume(submarine_volcanologist.volcano == "submarine")
    assert immediatelyBefore(yellow_laptop_volcanologist, submarine_volcanologist)

    # The volcanologist monitoring a volcano with an Increasing activity level is immediately after the scientist using the Pink laptop.
    pink_laptop_volcanologist = nondet(solution.volcanists)
    assume(pink_laptop_volcanologist.laptop == "pink")
    increasing_volcanologist = nondet(solution.volcanologists)
    assume(increasing_volcanologist.activity == "increasing")
    assert immediatelyBefore(pink_laptop_volcanologist, increasing_volcanologist)

    # Emily is immediately after the volcanologist who is using the Purple laptop.
    purple_laptop_volcanologist = nondet(solution.volcanologists)
    assume(purple_laptop_volcanologist.laptop == "purple")
    emily_volcanologist = nondet(solution.volcanologists)
    assume(emily_volcanologist.name == "emily")
    assert immediatelyBefore(purple_laptop_volcanologist, emily_volcanologist)

    # Lauren is immediately before Emily.
    assert immediatelyBefore(lauren_volcanologist, emily_volcanologist)"""

    def test_harness(self):
        source_module: Module = parse_module(self.source_code)
        harness = LogicPyForgeHarnessGenerator.generate(source_module)
        print(harness)
