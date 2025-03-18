# Copyright (c) Meta Platforms, Inc. and affiliates.
# All rights reserved.
#
# This source code is licensed under the license found in the
# LICENSE file in the root directory of this source tree.

from typing import Any
from unittest import TestCase

from training.lowercase_json import LowerCaseJson


_LOWER_CASE: dict[str, Any] = {
    "header": [
        "house",
        "name",
        "height",
        "spouse",
        "spirit animal",
        "pet",
        "hobby",
    ],
    "rows": [
        ["1", "bob", "short", "holly", "bird", "fish", "basketball"],
        ["2", "peter", "very tall", "aniya", "dog", "cat", "baseball"],
        ["3", "arnold", "tall", "penny", "fish", "horse", "soccer"],
        ["4", "eric", "very short", "kailyn", "cat", "dog", "tennis"],
        ["5", "alice", "average", "janelle", "hamster", "bird", "swimming"],
    ],
}

_CAMEL_CASE: dict[str, Any] = {
    "header": [
        "House",
        "Name",
        "Height",
        "Spouse",
        "Spirit Animal",
        "Pet",
        "Hobby",
    ],
    "rows": [
        ["1", "Bob", "short", "Holly", "bird", "fish", "basketball"],
        ["2", "Peter", "very tall", "Aniya", "dog", "cat", "baseball"],
        ["3", "Arnold", "tall", "Penny", "fish", "horse", "soccer"],
        ["4", "Eric", "very short", "Kailyn", "cat", "dog", "tennis"],
        [
            "5",
            "Alice",
            "average",
            "Janelle",
            "hamster",
            "bird",
            "swimming",
        ],
    ],
}


class TestLowerCaseJson(TestCase):

    def __init__(self, methodName="runTest"):
        super().__init__(methodName)
        self.maxDiff = None

    def test_convert(self) -> None:
        self.assertEqual(_LOWER_CASE, LowerCaseJson.convert(_CAMEL_CASE))

    def test_are_equal_both_lower(self) -> None:
        self.assertTrue(LowerCaseJson.are_equal(_LOWER_CASE, _LOWER_CASE))

    def test_are_equal_both_camel(self) -> None:
        self.assertTrue(LowerCaseJson.are_equal(_CAMEL_CASE, _CAMEL_CASE))

    def test_are_equal_different(self) -> None:
        self.assertTrue(LowerCaseJson.are_equal(_CAMEL_CASE, _LOWER_CASE))
