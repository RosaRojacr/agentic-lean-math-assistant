from __future__ import annotations

import json
from itertools import pairwise
from pathlib import Path
from tempfile import TemporaryDirectory

import pytest
from hypothesis import given
from hypothesis import strategies as st

from agentic_lean_math_assistant.agent_runner import _StreamingRedactor
from agentic_lean_math_assistant.config import ConfigurationError
from agentic_lean_math_assistant.journal import (
    JournalError,
    append_state_snapshot,
    journal_path,
    load_state_snapshot,
)
from agentic_lean_math_assistant.semantic import SemanticReview

_JSON_SCALAR = (
    st.none()
    | st.booleans()
    | st.integers()
    | st.text(alphabet=st.characters(blacklist_categories=("Cs",)), max_size=40)
)
_JSON_VALUE = st.recursive(
    _JSON_SCALAR,
    lambda children: (
        st.lists(children, max_size=5)
        | st.dictionaries(
            st.text(alphabet=st.characters(blacklist_categories=("Cs",)), max_size=20),
            children,
            max_size=5,
        )
    ),
    max_leaves=20,
)
_JSON_NON_OBJECT = _JSON_SCALAR | st.lists(_JSON_VALUE, max_size=5)
_JSON_OBJECT = st.dictionaries(
    st.text(alphabet=st.characters(blacklist_categories=("Cs",)), max_size=20),
    _JSON_VALUE,
    max_size=8,
)
_TEXT = st.text(
    alphabet=st.characters(blacklist_categories=("Cs",)), min_size=1, max_size=40
).filter(lambda value: bool(value.strip()))
_SEMANTIC_FIELDS = (
    "schema_version",
    "declaration",
    "informal_statement",
    "relation",
    "added_hypotheses",
    "omitted_hypotheses",
    "quantifier_issues",
    "domain_issues",
    "boundary_issues",
    "symbol_mismatches",
    "critical_errors",
    "reason",
)


def _semantic_payload() -> dict[str, object]:
    return {
        "schema_version": 1,
        "declaration": "Fixture.theorem",
        "informal_statement": "Fixture statement",
        "relation": "equivalent",
        "added_hypotheses": [],
        "omitted_hypotheses": [],
        "quantifier_issues": [],
        "domain_issues": [],
        "boundary_issues": [],
        "symbol_mismatches": [],
        "critical_errors": [],
        "reason": "All boundaries match.",
    }


@given(state=_JSON_OBJECT, reason=_TEXT)
def test_journal_round_trips_arbitrary_json_state(
    state: dict[str, object], reason: str
) -> None:
    with TemporaryDirectory() as temporary:
        run_dir = Path(temporary)
        sequence = append_state_snapshot(run_dir, state, reason=reason)
        loaded = load_state_snapshot(run_dir)

    assert sequence == loaded.sequence == 1
    assert loaded.state == state
    assert loaded.repaired_truncated_tail is False


@given(states=st.lists(_JSON_OBJECT, min_size=1, max_size=4))
def test_journal_preserves_latest_state_across_arbitrary_chains(
    states: list[dict[str, object]],
) -> None:
    with TemporaryDirectory() as temporary:
        run_dir = Path(temporary)
        for sequence, state in enumerate(states, start=1):
            assert (
                append_state_snapshot(run_dir, state, reason=f"property:{sequence}")
                == sequence
            )
        loaded = load_state_snapshot(run_dir)
        record_count = journal_path(run_dir).read_bytes().count(b"\n")

    assert loaded.sequence == len(states)
    assert loaded.state == states[-1]
    assert record_count == len(states)


def test_journal_repairs_an_incomplete_tail_before_the_next_append() -> None:
    with TemporaryDirectory() as temporary:
        run_dir = Path(temporary)
        append_state_snapshot(run_dir, {"step": 1}, reason="complete")
        with journal_path(run_dir).open("ab") as stream:
            stream.write(b'{"truncated":')
        sequence = append_state_snapshot(run_dir, {"step": 2}, reason="recovered")
        loaded = load_state_snapshot(run_dir)
        record_count = journal_path(run_dir).read_bytes().count(b"\n")

    assert sequence == loaded.sequence == 2
    assert loaded.state == {"step": 2}
    assert record_count == 2


@given(state=_JSON_OBJECT)
def test_journal_rejects_any_undigested_state_mutation(
    state: dict[str, object],
) -> None:
    with TemporaryDirectory() as temporary:
        run_dir = Path(temporary)
        append_state_snapshot(run_dir, state, reason="property mutation")
        path = journal_path(run_dir)
        record = json.loads(path.read_text(encoding="utf-8"))
        record["state"]["__property_tamper__"] = not bool(
            record["state"].get("__property_tamper__")
        )
        path.write_text(json.dumps(record, sort_keys=True) + "\n", encoding="utf-8")

        with pytest.raises(JournalError, match="invalid digest"):
            load_state_snapshot(run_dir)


@given(value=_JSON_NON_OBJECT)
def test_semantic_review_rejects_every_non_object_json_root(value: object) -> None:
    with TemporaryDirectory() as temporary:
        path = Path(temporary) / "semantic.json"
        path.write_text(json.dumps(value), encoding="utf-8")

        with pytest.raises(ConfigurationError, match="must be a JSON object"):
            SemanticReview.load(path)


@given(declaration=_TEXT, statement=_TEXT, reason=_TEXT)
def test_equivalent_semantic_review_round_trips_strict_payload(
    declaration: str, statement: str, reason: str
) -> None:
    payload = _semantic_payload()
    payload.update(
        declaration=declaration,
        informal_statement=statement,
        reason=reason,
    )
    with TemporaryDirectory() as temporary:
        path = Path(temporary) / "semantic.json"
        path.write_text(json.dumps(payload), encoding="utf-8")
        review = SemanticReview.load(path)

    assert review.declaration == declaration.strip()
    assert review.informal_statement == statement.strip()
    assert review.relation == "equivalent"
    assert review.issues == ()


@given(
    relation=st.sampled_from(
        [
            "formal_stronger",
            "formal_weaker",
            "conditional_fragment",
            "mismatch",
            "unclear",
        ]
    )
)
def test_non_equivalent_semantic_review_requires_specific_issue(
    relation: str,
) -> None:
    payload = _semantic_payload()
    payload["relation"] = relation
    payload["reason"] = "No issue supplied"
    with TemporaryDirectory() as temporary:
        path = Path(temporary) / "semantic.json"
        path.write_text(json.dumps(payload), encoding="utf-8")

        with pytest.raises(ConfigurationError, match="must report a specific issue"):
            SemanticReview.load(path)


@given(field=st.sampled_from(_SEMANTIC_FIELDS))
def test_semantic_review_rejects_every_missing_required_field(field: str) -> None:
    payload = _semantic_payload()
    del payload[field]
    with TemporaryDirectory() as temporary:
        path = Path(temporary) / "semantic.json"
        path.write_text(json.dumps(payload), encoding="utf-8")

        with pytest.raises(ConfigurationError, match="is missing keys"):
            SemanticReview.load(path)


@given(
    field=_TEXT.filter(lambda value: value not in _SEMANTIC_FIELDS),
    value=_JSON_VALUE,
)
def test_semantic_review_rejects_every_unknown_field(field: str, value: object) -> None:
    payload = _semantic_payload()
    payload[field] = value
    with TemporaryDirectory() as temporary:
        path = Path(temporary) / "semantic.json"
        path.write_text(json.dumps(payload), encoding="utf-8")

        with pytest.raises(ConfigurationError, match="has unknown keys"):
            SemanticReview.load(path)


@pytest.mark.parametrize(
    ("field", "value", "message"),
    [
        ("schema_version", None, "schema_version must be 1"),
        ("declaration", None, "must be a nonempty string"),
        ("informal_statement", [], "must be a nonempty string"),
        ("relation", 1, "must be a nonempty string"),
        ("added_hypotheses", "not-an-array", "must be an array"),
        ("reason", {}, "must be a nonempty string"),
    ],
)
def test_semantic_review_rejects_invalid_required_field_types(
    field: str, value: object, message: str
) -> None:
    payload = _semantic_payload()
    payload[field] = value
    with TemporaryDirectory() as temporary:
        path = Path(temporary) / "semantic.json"
        path.write_text(json.dumps(payload), encoding="utf-8")

        with pytest.raises(ConfigurationError, match=message):
            SemanticReview.load(path)


@given(
    prefix=st.text(alphabet=st.characters(blacklist_categories=("Cs",)), max_size=30),
    suffix=st.text(alphabet=st.characters(blacklist_categories=("Cs",)), max_size=30),
    secret=_TEXT,
    cuts=st.lists(st.integers(min_value=0, max_value=100), max_size=10),
)
def test_streaming_redaction_never_leaks_secret_across_chunks(
    prefix: str, suffix: str, secret: str, cuts: list[int]
) -> None:
    value = prefix + secret + suffix
    points = sorted({0, len(value), *(cut % (len(value) + 1) for cut in cuts)})
    chunks = [value[start:end] for start, end in pairwise(points)]
    redactor = _StreamingRedactor((secret,))
    output = "".join(redactor.feed(chunk) for chunk in chunks)
    output += redactor.feed("", final=True)

    assert secret not in output
    assert "[REDACTED]" in output
