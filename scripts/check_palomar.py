#!/usr/bin/env python3
"""Check the standalone Palomar reference against its original Lean source.

This stdlib-only check is read-only. It checks an explicit source-copy recipe,
not Lean syntax or semantics. It does not replace Lean elaboration, Comparator's
transitive declaration comparison, NanoDa replay, or the full Palomar workflow.
Run it from any directory with: python scripts/check_palomar.py
"""

from __future__ import annotations

import hashlib
import json
from pathlib import Path
import re
import sys

ROOT = Path(__file__).resolve().parents[1]
CHALLENGE = "PalomarChallenge.lean"
CONFIG = "Verification/palomar-principals.json"
THEOREMS = [
    "KungTraub.entire_counterexample",
    "KungTraub.no_entire_universal_order_above",
    "KungTraub.no_universal_order_above",
    "KungTraub.grouped_entire_counterexample",
    "KungTraub.no_grouped_entire_universal_order_above",
    "KungTraub.no_grouped_universal_order_above",
    "KungTraub.simultaneous_entire_counterexample",
    "KungTraubAppendices.complex_entire_counterexample",
    "KungTraubAppendices.no_complex_universal_order_above",
    "KungTraubAppendices.inverseHermite_universal_local_order",
    "KungTraubAppendices.inverseHermite_exp_asymptotic",
    "KungTraubAppendices.inverseHermite_not_local_order_exp",
]
PREAMBLES = {
    "KungTraub/Definitions.lean": (
        "KungTraub", "noncomputable section open Filter open scoped BigOperators Topology"
    ),
    "KungTraub/LocalAndStoppingAlgorithms.lean": ("KungTraub", "noncomputable section"),
    "KungTraubAppendices/ComplexDefinitions.lean": (
        "KungTraubAppendices", "noncomputable section open Filter open scoped Topology"
    ),
    "KungTraubAppendices/HermiteInterpolation.lean": (
        "KungTraubAppendices", "noncomputable section open Polynomial"
    ),
    "KungTraubAppendices/SharpnessDefinitions.lean": (
        "KungTraubAppendices", "noncomputable section open scoped BigOperators"
    ),
    "Challenge.lean": ("KungTraub", ""),
}


def require(condition: bool, message: str) -> None:
    if not condition:
        raise ValueError(message)


def read(path: str) -> str:
    # Universal newline conversion permits Windows and Linux checkouts.
    return (ROOT / path).read_text(encoding="utf-8").rstrip()


def between(source: str, start: str, end: str) -> str:
    require(start in source, f"Missing source marker: {start}")
    first = source.index(start)
    require(end in source[first:], f"Missing source marker: {end}")
    return source[first:source.index(end, first)].rstrip()


def namespace_body(path: str, namespace: str) -> str:
    source = read(path)
    marker = "namespace " + namespace
    require(marker in source, f"Missing namespace in {path}")
    return source[source.index(marker):]


def strip_module_doc(source: str) -> str:
    # This is deliberately a narrow check of these files' single module header,
    # not a general Lean comment parser. A changed header shape fails closed.
    require(source.startswith("/-!"), "Expected a module documentation block")
    end = source.find("-/", 3)
    require(end >= 0, "Unclosed module documentation block")
    require("/-" not in source[3:end], "Nested module documentation needs review")
    return source[end + 2:].strip()


def check_source_contexts() -> None:
    for path, (namespace, expected) in PREAMBLES.items():
        prefix = read(path).split("namespace " + namespace, 1)[0]
        prefix = re.sub(r"^import [^\n]+\n?", "", prefix, flags=re.MULTILINE).strip()
        prefix = strip_module_doc(prefix)
        require(prefix.split() == expected.split(), f"Source declaration context changed: {path}")
    hermite_prefix = between(
        read("KungTraubAppendices/HermiteInterpolation.lean"),
        "namespace KungTraubAppendices", "/-- Interpolate the values"
    )
    require(
        hermite_prefix.split() == (
            "namespace KungTraubAppendices variable {𝕜 ι : Type*} [Field 𝕜] [DecidableEq ι]"
        ).split(),
        "Hermite declaration variables or context changed",
    )


def expected_body() -> str:
    stopping = read("KungTraub/LocalAndStoppingAlgorithms.lean")
    stopping_blocks = [between(stopping, start, end) for start, end in [
        ("/-- An observation tree", "/-- Execution of a bounded tree"),
        ("/-- The padded query", "/-- The true answer vector"),
        ("/-- A stationary stopping algorithm", "/-- The output of the bounded stopping algorithm"),
        ("/-- Fixed-length scalar representation", "/-- Every prefix of the padded execution"),
    ]]
    hermite = between(
        read("KungTraubAppendices/HermiteInterpolation.lean"),
        "/-- Interpolate the values", "/-- Distinct interpolation nodes"
    )
    # Keep namespace, variable, local-instance, recursive-definition, termination,
    # and theorem contexts intact. The whole generated body must match: extra
    # declarations outside the copied blocks are rejected too.
    return "\n".join([
        "set_option autoImplicit false", "", "noncomputable section", "",
        "open Filter", "open scoped BigOperators Topology", "",
        namespace_body("KungTraub/Definitions.lean", "KungTraub"), "",
        "/-! ## The bounded tree and padding used by the attaining method -/", "",
        "namespace KungTraub", "",
        *[line for block in stopping_blocks for line in (block, "")],
        "end KungTraub", "",
        "/-! ## Complex observations and local domains -/", "",
        namespace_body("KungTraubAppendices/ComplexDefinitions.lean", "KungTraubAppendices"), "",
        "/-! ## The concrete inverse Hermite update -/", "",
        "namespace KungTraubAppendices", "", "open Polynomial", "",
        "variable {𝕜 ι : Type*} [Field 𝕜] [DecidableEq ι]", "", hermite, "",
        "end KungTraubAppendices", "",
        namespace_body("KungTraubAppendices/SharpnessDefinitions.lean", "KungTraubAppendices"), "",
        "/-! ## Principal reference statements -/", "",
        namespace_body("Challenge.lean", "KungTraub"),
    ])


def main() -> None:
    check_source_contexts()
    source = read(CHALLENGE)
    imports = re.findall(r"^import (.+)$", source, flags=re.MULTILINE)
    expected_imports = re.findall(
        r"^import (.+)$", read("KungTraub/Definitions.lean"), flags=re.MULTILINE
    ) + [
        "Mathlib.Analysis.SpecialFunctions.ExpDeriv",
        "Mathlib.LinearAlgebra.Lagrange",
        "Mathlib.Tactic",
    ]
    require(imports == expected_imports, "Challenge imports differ from the reviewed copy recipe")
    require(all(name.startswith("Mathlib.") for name in imports), "Only Mathlib imports are allowed here")
    import_prefix = "\n".join("import " + name for name in imports) + "\n\n"
    require(source.startswith(import_prefix), "Unexpected text before the module documentation")
    actual_body = strip_module_doc(source[len(import_prefix):])
    require(actual_body == expected_body(), "Challenge body differs from the exact source-copy recipe")

    statements = namespace_body("Challenge.lean", "KungTraub")
    require(len(re.findall(r"^theorem ", statements, flags=re.MULTILINE)) == 12,
            "Expected exactly twelve principal theorem declarations")
    placeholders = re.findall(r":= by\n  sorry(?=\n|$)", source)
    require(len(placeholders) == 12, "Expected exactly twelve theorem proof placeholders")
    remainder = re.sub(r":= by\n  sorry(?=\n|$)", "", source)
    require(not re.search(r"\b(?:sorry|admit|axiom)\b", remainder),
            "Additional proof-hole/axiom token needs review (including in comments)")
    require(len(re.findall(r"^theorem ", source, flags=re.MULTILINE)) == 12,
            "Unexpected additional theorem declaration")

    original_config = json.loads(read("Verification/principals.json"))
    require(original_config["theorem_names"] == THEOREMS, "Original principal selection changed")
    require(original_config["solution_module"] == "All", "Original solution module changed")
    require(original_config["definition_names"] == [], "Original unspecified definitions changed")
    require(original_config["permitted_axioms"] == ["propext", "Classical.choice", "Quot.sound"],
            "Original permitted axioms changed")
    expected_config = dict(original_config, challenge_module="PalomarChallenge", enable_nanoda=True)
    current_config = json.loads(read(CONFIG))
    require(current_config == expected_config, "Palomar verification configuration differs")
    require(current_config["enable_nanoda"] is True, "NanoDa must be enabled")
    require(re.search(r'\[\[lean_lib\]\]\s*name = "PalomarChallenge"', read("lakefile.toml")) is not None,
            "Missing PalomarChallenge Lake library target")

    data = (ROOT / CHALLENGE).read_bytes()
    lines = len(data.decode("utf-8").splitlines())
    require(lines <= 1000, f"Challenge exceeds 1,000 lines: {lines}")
    require(len(data) <= 100 * 1024, f"Challenge exceeds 100 KiB: {len(data)} bytes")
    print("PASS: exact source copies and declaration contexts; twelve principal statements/placeholders.")
    print("PASS: Mathlib-only imports, empty definition_names, All solution, NanoDa enabled, Lake target.")
    print(f"PASS: {lines} lines; {len(data)} bytes; SHA-256 {hashlib.sha256(data).hexdigest()}.")
    print("STATIC CHECK ONLY: Lean elaboration, Comparator, NanoDa, and the full Palomar workflow remain required.")


if __name__ == "__main__":
    try:
        main()
    except (OSError, ValueError, KeyError) as error:
        print(f"FAIL: {error}", file=sys.stderr)
        sys.exit(1)
