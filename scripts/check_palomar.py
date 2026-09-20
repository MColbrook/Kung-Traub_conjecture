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
MODEL = "KungTraub/Model.lean"

def require(condition: bool, message: str) -> None:
    if not condition:
        raise ValueError(message)


def read(path: str) -> str:
    # Universal newline conversion permits Windows and Linux checkouts.
    return (ROOT / path).read_text(encoding="utf-8").rstrip()


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


def module_parts(path: str) -> tuple[list[str], str]:
    source = read(path)
    imports = re.findall(r"^import (.+)$", source, flags=re.MULTILINE)
    prefix = "\n".join("import " + name for name in imports) + "\n\n"
    require(source.startswith(prefix), f"Unexpected import/header shape: {path}")
    return imports, strip_module_doc(source[len(prefix):])


def expected_body() -> str:
    _, model_body = module_parts(MODEL)
    return (
        model_body + "\n\n/-! ## Principal reference statements -/\n\n"
        + namespace_body("Challenge.lean", "KungTraub")
    )


def check_reexports() -> None:
    expected = {
        "KungTraub/Definitions.lean": ["KungTraub.Model"],
        "KungTraubAppendices/ComplexDefinitions.lean": ["KungTraub.Definitions"],
        "KungTraubAppendices/SharpnessDefinitions.lean": [
            "KungTraub.Model", "KungTraub.LocalAndStoppingAlgorithms",
            "KungTraubAppendices.HermiteInterpolation",
            "Mathlib.Analysis.SpecialFunctions.ExpDeriv",
        ],
    }
    for path, imports in expected.items():
        actual_imports, body = module_parts(path)
        require(actual_imports == imports and body == "",
                f"Legacy definition reexport changed: {path}")
    require(read("KungTraubAppendices/HermiteInterpolation.lean").startswith("import KungTraub.Model\n"),
            "Hermite interpolation proofs must import their shared model")


def main() -> None:
    check_reexports()
    source = read(CHALLENGE)
    imports, actual_body = module_parts(CHALLENGE)
    model_imports, model_body = module_parts(MODEL)
    require(imports == model_imports, "Challenge and model import contexts differ")
    require(all(name.startswith("Mathlib.") for name in imports), "Only Mathlib imports are allowed here")
    require(model_body.startswith("set_option autoImplicit false\n\nnoncomputable section\n"),
            "Shared model declaration context changed")
    require(not re.search(r"\b(?:sorry|admit|axiom)\b", model_body),
            "Shared model contains a proof-hole/axiom token")
    require(not re.search(r"^theorem ", model_body, flags=re.MULTILINE),
            "Shared model must contain only the concrete model declarations")
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
    print("PASS: exact shared model copy and import context; twelve principal statements/placeholders.")
    print("PASS: Mathlib-only imports, empty definition_names, All solution, NanoDa enabled, Lake target.")
    print(f"PASS: {lines} lines; {len(data)} bytes; SHA-256 {hashlib.sha256(data).hexdigest()}.")
    print("STATIC CHECK ONLY: Lean elaboration, Comparator, NanoDa, and the full Palomar workflow remain required.")


if __name__ == "__main__":
    try:
        main()
    except (OSError, ValueError, KeyError) as error:
        print(f"FAIL: {error}", file=sys.stderr)
        sys.exit(1)
