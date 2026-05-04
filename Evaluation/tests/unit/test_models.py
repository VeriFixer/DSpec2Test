"""Tests for MutantResult model and MutantStatus enum."""

import pytest

from src.mt_eval.core.models import MutantResult, MutantStatus


class TestMutantStatus:
    def test_enum_values(self):
        assert MutantStatus.KILLED.value == "killed"
        assert MutantStatus.SURVIVED.value == "survived"
        assert MutantStatus.TIMEOUT.value == "timeout"
        assert MutantStatus.ERROR.value == "error"

    def test_all_statuses_present(self):
        names = {s.name for s in MutantStatus}
        assert names == {"KILLED", "SURVIVED", "TIMEOUT", "ERROR"}

    def test_from_value(self):
        assert MutantStatus("killed") is MutantStatus.KILLED
        assert MutantStatus("survived") is MutantStatus.SURVIVED
        assert MutantStatus("timeout") is MutantStatus.TIMEOUT
        assert MutantStatus("error") is MutantStatus.ERROR

    def test_invalid_value_raises(self):
        with pytest.raises(ValueError):
            MutantStatus("unknown")


class TestMutantResult:
    def test_basic_construction(self):
        r = MutantResult(
            mutant_name="abs__10-20_CBE.dfy",
            original_name="abs.dfy",
            status=MutantStatus.KILLED,
            execution_time=1.5,
        )
        assert r.mutant_name == "abs__10-20_CBE.dfy"
        assert r.original_name == "abs.dfy"
        assert r.status is MutantStatus.KILLED
        assert r.execution_time == 1.5

    def test_to_dict(self):
        r = MutantResult("m.dfy", "o.dfy", MutantStatus.SURVIVED, 3.14)
        d = r.to_dict()
        assert d == {
            "mutant_name": "m.dfy",
            "original_name": "o.dfy",
            "status": "survived",
            "execution_time": 3.14,
            "test_gen_command": "",
            "kill_check_command": "",
        }

    def test_from_dict(self):
        d = {
            "mutant_name": "m.dfy",
            "original_name": "o.dfy",
            "status": "timeout",
            "execution_time": 300.0,
        }
        r = MutantResult.from_dict(d)
        assert r.mutant_name == "m.dfy"
        assert r.original_name == "o.dfy"
        assert r.status is MutantStatus.TIMEOUT
        assert r.execution_time == 300.0

    def test_round_trip(self):
        original = MutantResult("a.dfy", "b.dfy", MutantStatus.ERROR, 0.001)
        restored = MutantResult.from_dict(original.to_dict())
        assert restored == original

    def test_from_dict_coerces_execution_time_to_float(self):
        d = {
            "mutant_name": "m.dfy",
            "original_name": "o.dfy",
            "status": "killed",
            "execution_time": 5,  # int, not float
        }
        r = MutantResult.from_dict(d)
        assert isinstance(r.execution_time, float)
        assert r.execution_time == 5.0

    def test_from_dict_invalid_status_raises(self):
        d = {
            "mutant_name": "m.dfy",
            "original_name": "o.dfy",
            "status": "invalid",
            "execution_time": 1.0,
        }
        with pytest.raises(ValueError):
            MutantResult.from_dict(d)
