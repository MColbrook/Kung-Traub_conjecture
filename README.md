# Kung–Traub in Lean

A Lean formalization of Matthew J. Colbrook's *Adversarial Wronskians: A proof of the Kung–Traub conjecture*, including the main real theorem, the grouped-observation corollary, inverse Hermite attainment and sharpness, and the complex-observation theorem.

For deterministic stationary methods without memory, the formalization proves the scalar upper bound `2^(n-1)` for `n ≥ 1`. It constructs the inverse Hermite method attaining this exponent for `n ≥ 2`, and proves the corresponding upper bound for complex derivative observations. The [mathematical overview](docs/Mathematics.md) gives the precise domains, quantifiers and theorem locations.

## Build

The project uses **Lean 4.33.1** and Mathlib revision `0df444a360eaa60ab8c11dca51a86af692955474`. The toolchain and all dependency revisions are fixed by [lean-toolchain](lean-toolchain) and [lake-manifest.json](lake-manifest.json).

From the repository root, with Lean's `elan` toolchain manager installed:

```sh
lake exe cache get
lake build
```

The first command downloads the matching Mathlib build cache. The second builds the project libraries and aggregate module. The [verification instructions](docs/Verification.md) cover the axiom audit and independent statement comparisons.

## Source map

| Entry point | Contents |
| --- | --- |
| [KungTraub.lean](KungTraub.lean) | Real observation models, polynomial Wronskians, finite adversaries, entire constructions and grouped bounds. |
| [Solution.lean](Solution.lean) | The main real and grouped endpoints, including simultaneous failure of all larger exponents. |
| [KungTraubAppendices.lean](KungTraubAppendices.lean) | Inverse Hermite interpolation and exact order; complex observations, adversaries and local-domain consequences. |
| [All.lean](All.lean) | The complete formalization. |

For use in another Lean file:

```lean
import All

#check KungTraub.entire_counterexample
#check KungTraub.grouped_entire_counterexample
#check KungTraubAppendices.inverseHermite_optimal_universal_exponent
#check KungTraubAppendices.complex_entire_counterexample
```

The proofs use Lean's standard axioms `propext`, `Classical.choice` and `Quot.sound`. Numerical estimates are established by exact algebraic, analytic and series arguments.

The release passed a clean build, an axiom audit of 1,202 declarations and secure Comparator checks of all 1,058 named theorems. The [verification results](docs/Verification.md#release-checks) include commands, source hashes and checking output.

The [mathematical review guide](docs/Review.md) gives a reading order for checking the statements, definitions and their correspondence with the paper.

## Attribution

The mathematical source is Matthew J. Colbrook's manuscript. The attaining methods are attributed there to H. T. Kung and J. F. Traub; the divided-difference estimate is attributed to C. de Boor. The formalization builds on Mathlib, with specific library contributions credited in the source. Bibliographic details appear in [Mathematics.md](docs/Mathematics.md).

Copyright © 2026 Matthew J. Colbrook. All rights reserved; see [COPYRIGHT.md](COPYRIGHT.md). Third-party components retain their own licences.
