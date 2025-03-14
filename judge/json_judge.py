# Copyright (c) Meta Platforms, Inc. and affiliates.
# All rights reserved.
#
# This source code is licensed under the license found in the
# LICENSE file in the root directory of this source tree.

from json import loads
from typing import Any, Optional

from judge.result_trace import ResultTrace


class JsonJudge:
    """
    Provides a ScoredResultTrace for a give ResultTrace, assuming that the
    expected and actual solution can be compared as JSON objects.
    """

    def __call__(self, result_trace: ResultTrace, expected_solution: Any) -> bool:
        """
        Compare solution in result_trace with expected_solution and produce a
        ScoredResultTrace.

        Args:
            result_trace (ResultTrace): Trace to score.
            expected_solution (Any): Expected JSON output.
        Returns:
            True iff the solution is correct.
        """
        solution: Optional[str] = result_trace.solution
        is_correct: bool = solution is not None and loads(solution) == expected_solution
        return is_correct
