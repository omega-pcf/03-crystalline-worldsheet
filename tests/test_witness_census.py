"""
Witness census — every numerical witness of the manuscript is backed by a test
================================================================================
The manuscript tags its claims with the verification tags of the family
convention:

    \\witness[KEY]{N}           numerical witness, inline or block
                                  (the position of the call picks the render)
    \\NumericalWitness{...}     legacy form, still parsed

A numerical tag is only honest if (a) KEY is a real \\label of the document,
(b) at least one test in this suite refers to KEY, and (c) no single witness
call repeats a key.  This test turns that contract into a rule the suite keeps,
so a retag or a new claim cannot drift away from its backing.

Proof witnesses (\\witness[ids]{P}) are backed by lean/, not by
pytest; their resolution is checked against lean/CW6_complete_v2.lean by the
Lean build, not here.
"""
import re
from pathlib import Path

import pytest

REPO_ROOT = Path(__file__).resolve().parents[1]
CHAPTERS = sorted((REPO_ROOT / "src" / "chapters").glob("*.tex"))
TEST_FILES = sorted((REPO_ROOT / "tests").glob("test_*.py"))


def _unescape(key: str) -> str:
    return key.replace(r"\_", "_").strip()


def _split_ids(arg: str) -> list[str]:
    """Top-level commas only: a comma inside ``\\testref{...}`` does not split."""
    parts: list[str] = []
    depth, current = 0, ""
    for char in arg:
        if char == "{":
            depth += 1
        elif char == "}":
            depth -= 1
        if char == "," and depth == 0:
            parts.append(current)
            current = ""
        else:
            current += char
    parts.append(current)
    return [key for key in (_unescape(part) for part in parts) if key.strip()]


def _numeric_keys(text: str):
    """All numerical-witness keys of one chapter, one list per witness call."""
    calls = []
    for m in re.finditer(r"\\witness\s*\[([^\]]+)\]\{N\}", text):
        calls.append(_split_ids(m.group(1)))
    for m in re.finditer(r"\\NumericalWitness(?:Block)?\{([^}]*)\}", text):
        calls.append([_unescape(k) for k in m.group(1).split(",") if k.strip()])
    return calls


@pytest.fixture(scope="module")
def witness_calls():
    assert CHAPTERS, "no src/chapters/*.tex found"
    calls = []
    for chapter in CHAPTERS:
        for keys in _numeric_keys(chapter.read_text(encoding="utf-8", errors="replace")):
            calls.append((chapter.name, [k for k in keys if k != "..."]))
    return [c for c in calls if c[1]]          # drop the {...} legend placeholders


@pytest.fixture(scope="module")
def labels():
    found = set()
    for chapter in CHAPTERS:
        found.update(re.findall(r"\\label\{([^}]*)\}",
                                chapter.read_text(encoding="utf-8", errors="replace")))
    return found


def test_every_numerical_key_is_a_label(witness_calls, labels):
    """(a) a numerical tag points at a label that exists in the manuscript."""
    orphan = sorted({k for _, keys in witness_calls for k in keys if k not in labels})
    assert not orphan, f"numerical witness keys with no \\\\label: {orphan}"


def test_every_numerical_key_is_backed_by_a_test(witness_calls):
    """(b) each numerical tag is named by at least one test module."""
    assert TEST_FILES, "no tests/test_*.py found"
    corpus = "\n".join(f.read_text(encoding="utf-8", errors="replace") for f in TEST_FILES)
    unbacked = sorted({k for _, keys in witness_calls for k in keys if k not in corpus})
    assert not unbacked, f"numerical witness keys no test refers to: {unbacked}"


def test_no_key_repeated_inside_one_call(witness_calls):
    """(c) a witness call names each key once (duplication inside a call is a
    copy/paste, not two witnesses)."""
    repeated = []
    for chapter, keys in witness_calls:
        seen = set()
        for key in keys:
            if key in seen:
                repeated.append(f"{chapter}:{key}")
            seen.add(key)
    assert not repeated, f"keys repeated inside one witness call: {repeated}"


def test_the_census_sees_a_real_set_of_tags(witness_calls):
    """Sanity: the census is looking at a non-trivial set of numerical tags,
    not at an empty parse."""
    assert len(witness_calls) >= 10
