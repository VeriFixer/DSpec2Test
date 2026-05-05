"""Property-based tests for MutantResult serialization.

# Feature: mutation-testing-evaluation, Property 7: Results serialization round-trip

Uses Hypothesis with min 100 iterations.
"""

import json

from hypothesis import given, settings
from hypothesis import strategies as st

from src.mt_eval.core.models import MutantResult, MutantStatus

# ---------------------------------------------------------------------------
# Strategies
# ---------------------------------------------------------------------------

_mutant_status = st.sampled_from(list(MutantStatus))

_mutant_result = st.builds(
    MutantResult,
    mutant_name=st.text(min_size=1, max_size=50),
    original_name=st.text(min_size=1, max_size=50),
    status=_mutant_status,
    execution_time=st.floats(min_value=0.0, max_value=1e6, allow_nan=False, allow_infinity=False),
)

_mutant_result_list = st.lists(_mutant_result, min_size=0, max_size=20)

# ---------------------------------------------------------------------------
# Property 7: Results serialization round-trip
# **Validates: Requirements 5.2**
#
# For any list of MutantResults, serializing to JSON and deserializing
# back SHALL produce an equivalent list with all fields preserved.
# ---------------------------------------------------------------------------


@given(results=_mutant_result_list)
@settings(max_examples=100)
def test_results_serialization_round_trip(results):
    """Property 7: Results serialization round-trip — serialize MutantResult
    list to JSON and back preserves all fields.

    **Validates: Requirements 5.2**
    """
    # Serialize
    json_str = json.dumps([r.to_dict() for r in results])

    # Deserialize
    raw = json.loads(json_str)
    restored = [MutantResult.from_dict(d) for d in raw]

    # Assert equality
    assert len(restored) == len(results)
    for orig, rest in zip(results, restored):
        assert rest.mutant_name == orig.mutant_name
        assert rest.original_name == orig.original_name
        assert rest.status == orig.status
        assert rest.execution_time == orig.execution_time
