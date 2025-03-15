# Copyright (c) Meta Platforms, Inc. and affiliates.
# All rights reserved.
#
# This source code is licensed under the license found in the
# LICENSE file in the root directory of this source tree.

from json import dumps
from typing import Any
from unittest import TestCase

from libcst import Module, parse_module

from training.training_data_structure_converter import (
    PythonDataStructureToJsonSchemaConverter,
)


class TestPythonDataStructureToJsonConverter(TestCase):

    def __init__(self, methodName="runTest"):
        super().__init__(methodName)
        self.maxDiff = None

    def test_convert(self) -> None:
        self.__test_harness(
            """class Person:
    name: Unique[Domain[str, "Alice", "Eric", "Arnold", "Peter"]]
    occupation: Unique[Domain[str, "artist", "engineer", "teacher", "doctor"]]
    book_genre: Unique[Domain[str, "fantasy", "science fiction", "mystery", "romance"]]
    phone_model: Unique[Domain[str, "google pixel 6", "iphone 13", "oneplus 9", "samsung galaxy s21"]]
    age: int = 10
    share: float = 0.75

class House:
    id: Unique[Domain[int, range(1, 5)]]
    person: Person

class Solution:
    header: list[str, 7] = ["House", "Name", "MusicGenre", "Mother", "Child", "Height", "Animal"]
    houses: list[House, 4]
""",
            """{
    "type": "object",
    "properties": {
        "header": {
            "type": "array",
            "items": {
                "type": "string"
            }
        },
        "houses": {
            "type": "array",
            "items": {
                "type": "object",
                "properties": {
                    "id": {
                        "type": "integer"
                    },
                    "person": {
                        "type": "object",
                        "properties": {
                            "name": {
                                "type": "string"
                            },
                            "occupation": {
                                "type": "string"
                            },
                            "book_genre": {
                                "type": "string"
                            },
                            "phone_model": {
                                "type": "string"
                            },
                            "age": {
                                "type": "integer"
                            },
                            "share": {
                                "type": "number"
                            }
                        }
                    }
                }
            }
        }
    }
}""",
        )

    def __test_harness(self, code: str, expected_json: Any) -> None:
        source_tree: Module = parse_module(code)
        visitor = PythonDataStructureToJsonSchemaConverter()
        source_tree.visit(visitor)
        self.assertEqual(expected_json, dumps(visitor.json_schema, indent=4))
