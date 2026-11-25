"""The citation-key rule of the tag grammar (docs/witness-contract.md §6.5).

The tag macro reads a bracket as an arbitrary string, so it cannot know
whether a part is one of OUR ids or one of the BIBLIOGRAPHY's keys; the key
set exists only outside TeX, so the rule is measured here, in the suite (a
check that needs external data runs outside the typesetting).  Ported from
``02-odd-zeta/tests/test_witness_census.py``, adapted to this repository's
manuscript sources and key set.

Rule: no part of a ``\\tier[...]`` or ``\\witness{...}{...}`` argument may
equal the id of a record of ``citation.csl.json`` or carry a ``\\cite``
token; an external source stays an adjacent ``\\cite`` in the prose.
"""

from __future__ import annotations

import json
import re
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[1]
TEX_SOURCES = [REPO_ROOT / "main.tex", *sorted((REPO_ROOT / "src" / "chapters").glob("*.tex"))]
TEX_SOURCES = [source for source in TEX_SOURCES if source.exists()]

# Two real keys of citation.csl.json, used only by the synthetic fixture.
FIXTURE_KEYS = ("Strominger01", "Maldacena98")

_TAG_SITE = re.compile(r"\\tier\[|\\witness\{")
_TESTREF_WRAPPED = re.compile(r"^\\testref\{(.*)\}$", re.DOTALL)
_KEYS: set[str] | None = None


def citation_keys() -> set[str]:
    """The documented citation keys of this repository (the CSL ``id`` field)."""
    global _KEYS
    if _KEYS is None:
        records = json.loads((REPO_ROOT / "citation.csl.json").read_text(encoding="utf-8"))
        _KEYS = {record["id"] for record in records}
    return _KEYS


def _read_group(text: str, start: int) -> tuple[str, int] | None:
    """The balanced ``{...}`` group that opens at ``start``; else ``None``."""
    if start >= len(text) or text[start] != "{":
        return None
    depth = 0
    for index in range(start, len(text)):
        if text[index] == "{":
            depth += 1
        elif text[index] == "}":
            depth -= 1
            if depth == 0:
                return text[start + 1 : index], index + 1
    return None


def _read_optional(text: str, start: int) -> tuple[str, int] | None:
    """The ``[...]`` optional argument that opens at ``start``, braces aware."""
    if start >= len(text) or text[start] != "[":
        return None
    depth = 0
    for index in range(start, len(text)):
        if text[index] == "{":
            depth += 1
        elif text[index] == "}":
            depth -= 1
        elif text[index] == "]" and depth == 0:
            return text[start + 1 : index], index + 1
    return None


def tag_arguments(text: str) -> list[tuple[int, str, str]]:
    """``(line, macro, argument)`` for every ``\\tier[...]`` and ``\\witness{...}{...}``.

    A ``%`` before the site on its line comments it out in TeX, so such a
    site is not part of the manuscript and is not read as one here.
    """
    sites: list[tuple[int, str, str]] = []
    for match in _TAG_SITE.finditer(text):
        line_start = text.rfind("\n", 0, match.start()) + 1
        if "%" in text[line_start : match.start()]:
            continue
        line = text.count("\n", 0, match.start()) + 1
        if match.group(0) == "\\tier[":
            parsed = _read_optional(text, match.end() - 1)
            if parsed is None:
                continue
            sites.append((line, "tier", parsed[0]))
        else:
            first = _read_group(text, match.end() - 1)
            if first is None:
                continue
            second = _read_group(text, first[1])
            if second is None:
                continue
            sites.append((line, "witness", second[0]))
    return sites


def split_on_top_level_commas(argument: str) -> list[str]:
    """Split on the commas that sit OUTSIDE ``\\testref{...}`` (brace count)."""
    parts: list[str] = []
    depth, current = 0, []
    for char in argument:
        if char == "," and depth == 0:
            parts.append("".join(current))
            current = []
            continue
        if char == "{":
            depth += 1
        elif char == "}":
            depth -= 1
        current.append(char)
    parts.append("".join(current))
    return parts


def without_testref(part: str) -> str:
    """Drop an outer ``\\testref{...}`` wrapper and the surrounding spaces."""
    stripped = part.strip()
    wrapped = _TESTREF_WRAPPED.match(stripped)
    return (wrapped.group(1) if wrapped else stripped).strip()


def citation_offenders(text: str, keys: set[str], label: str) -> list[str]:
    """One ``file:line`` row per part of a bracket that holds a citation key.

    Equality against the loaded key set decides -- never a character
    heuristic: a part equal to the id of a record of ``citation.csl.json``,
    or one carrying the ``\\cite`` token, is a violation.
    """
    offenders: list[str] = []
    for line, macro, argument in tag_arguments(text):
        for part in split_on_top_level_commas(argument):
            part = without_testref(part)
            if part in keys:
                offenders.append(
                    f"{label}:{line} \\{macro}: the part {part!r} is the id of a "
                    f"record of citation.csl.json"
                )
            elif "\\cite" in part:
                # the report stops at the token, so the message stays readable
                clipped = part[: part.index("\\cite") + len("\\cite")]
                offenders.append(
                    f"{label}:{line} \\{macro}: the part {clipped!r} carries the "
                    f"\\cite token (an external source is an adjacent \\cite)"
                )
    return offenders


def test_no_citation_key_sits_inside_a_tag() -> None:
    """No part of any tag bracket equals a citation key or carries ``\\cite``.

    The corpus is every ``\\tier[...]`` and ``\\witness{...}{...}`` of the
    manuscript, split on the commas that sit outside ``\\testref{...}``; the
    keys are the ids of ``citation.csl.json``.  The tag macro accepts an
    arbitrary string, so this test -- not the macro -- is the whole of the
    citation-key rule (contract §6.5).
    """
    keys = citation_keys()
    assert keys, "citation.csl.json declares no id: the key set is empty"
    offenders: list[str] = []
    sites = 0
    for source in TEX_SOURCES:
        text = source.read_text(encoding="utf-8")
        sites += len(tag_arguments(text))
        offenders.extend(citation_offenders(text, keys, source.name))
    assert sites > 0, "the extractor found no tag argument: the pattern or the corpus broke"
    assert not offenders, (
        "a citation key (or a \\cite token) sits inside a tag: an external "
        "source stays an adjacent \\cite, never fused into the mark: "
        + "; ".join(offenders)
    )


def test_the_tag_lint_catches_a_synthetic_insertion() -> None:
    """The rule is not vacuous: a key inserted into a bracket fails the check."""
    keys = citation_keys()
    assert set(FIXTURE_KEYS) <= keys, "the fixture keys left citation.csl.json"
    first, second = FIXTURE_KEYS
    synthetic = (
        f"\\tier[{first}]{{P}}\n"
        f"\\witness{{P}}{{{second}, a_valid_internal_id}}\n"
        f"\\tier[\\cite{{{first}}}]{{N}}\n"
        "\\tier[\\testref{a_valid_id, other_valid_id}]{N}\n"
        "\\tier[a_valid_id]{N}\n"
    )
    offenders = citation_offenders(synthetic, keys, "synthetic.tex")
    assert len(offenders) == 3, offenders
    assert offenders[0].startswith("synthetic.tex:1"), offenders[0]
    assert any(second in row for row in offenders), offenders
    assert any("\\cite" in row for row in offenders), offenders
    # the ids the character-shape grammar used to reject are not violations
    assert all("a_valid_id" not in row and "other_valid_id" not in row for row in offenders)
