# Copyright (c) Meta Platforms, Inc. and affiliates.
# All rights reserved.
#
# This source code is licensed under the license found in the
# LICENSE file in the root directory of this source tree.

from typing import Any


class LowerCaseJson:
    """
    Helper to convert every `str` in a JSON data structure to lower case.
    """

    @staticmethod
    def convert(json: Any) -> Any:
        """
        Converts every `str` in json to lower case.

        Args:
            json (Any): JSON object to convert.
        Returns:
            Potentially a copy of json, with all `str` objects in it converted
            to lower case.
        """
        if isinstance(json, dict):
            return {k.lower(): LowerCaseJson.convert(v) for k, v in json.items()}
        elif isinstance(json, list):
            return [LowerCaseJson.convert(item) for item in json]
        elif isinstance(json, str):
            return json.lower()
        else:
            return json

    @staticmethod
    def are_equal(lhs: Any, rhs: Any) -> bool:
        """
        Compares lhs and rhs, ignoring case.

        Args:
            lhs (Any): JSON object to compare.
            rhs (Any): JSON object to compare.
        Returns:
            True iff lhs and rhs are equal when converted to all lowercase.
        """
        return LowerCaseJson.convert(lhs) == LowerCaseJson.convert(rhs)
