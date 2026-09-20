# Mathematical scope

The formalization covers the real upper bound and grouped-observation corollary, their supporting constructions, inverse Hermite attainment and sharpness, and the complex upper bound in Matthew J. Colbrook's *Adversarial Wronskians: A proof of the Kung–Traub conjecture*.

## Observation models and local order

An algorithm is deterministic, stationary and without memory between updates. Within one update it may choose each query using the starting point and all earlier answers. A query returns one derivative value of arbitrary natural order, including order zero. The decision and output rules are arbitrary functions; continuity, measurability and computability are not required. Bounded stopping trees and partial rules have extensions preserving their defined executions.

For an update `T`, local order `p` at a simple zero `α` means that there are `C > 0` and `δ > 0` such that

```text
|T(f,x) − α| ≤ C |x − α|^p   whenever 0 < |x − α| < δ.
```

Complex statements use norms in the same estimate. The constants may depend on the fixed method, function, root and exponent. The estimate applies to every start in a punctured neighbourhood. Witness sequences are sequences of independent starting points. Local-domain predicates additionally require defined, admissible executions throughout that neighbourhood.

The shared definitions are collected in [KungTraub/Model.lean](../KungTraub/Model.lean):

| Model section | Definitions to inspect |
| --- | --- |
| Opening real and grouped models, in the first `KungTraub` namespace | `orderBound`, `RealAlgorithm`, `GroupedRealAlgorithm`, local-order predicates, entire witnesses and counterexamples, through `SimultaneousEntireCounterexample`. |
| “The bounded tree and padding used by the attaining method” | `BoundedRealTree`, `paddedQuery`, `paddedOutput`, `StoppingRealAlgorithm` and its `padded` fixed-slot representation. |
| “Complex observations and local domains” | `ComplexQuery`, `ComplexAlgorithm`, admissible executions, local-order predicates, witness data and `ComplexEntireCounterexample`. |
| “The concrete inverse Hermite update” | The `hermiteWithDerivative` formula, `inverseHermiteTail`, `inverseHermiteTree`, `inverseHermiteAlgorithm`, interval admissibility and order, and `sharpnessCoefficient`. |

[Definitions.lean](../KungTraub/Definitions.lean), [ComplexDefinitions.lean](../KungTraubAppendices/ComplexDefinitions.lean) and [SharpnessDefinitions.lean](../KungTraubAppendices/SharpnessDefinitions.lean) re-export this model for existing imports. The stopping execution and counting definitions, padding-preservation theorems and partial real rules remain in [LocalAndStoppingAlgorithms.lean](../KungTraub/LocalAndStoppingAlgorithms.lean). The characteristic theorems for the interpolation formula remain in [HermiteInterpolation.lean](../KungTraubAppendices/HermiteInterpolation.lean).

## Real upper bounds

For every budget `n ≥ 1`, every `RealAlgorithm n`, and every real `p > 2^(n-1)`, `KungTraub.entire_counterexample` constructs an entire function `F : ℂ → ℂ` real on the real axis. Its real restriction `f` has a unique real zero `α` and satisfies

```text
3/4 ≤ f′(t) ≤ 5/4   for every real t.
```

There are nonroot starts `x_s → α` for which `|A(f,x_s) − α| / |x_s − α|^p → +∞`. The related impossibility theorems cover both the entire real-type class and the broader class of functions analytic everywhere on the real line. `KungTraub.simultaneous_entire_counterexample` chooses one function and one sequence that work for every real `p > 2^(n-1)`.

For `k ≥ 1` prescribed groups of positive sizes `ℓ₁,…,ℓₖ`, all queries in a group are selected before receiving any answer from that group. The grouped counterexample and universal-order consequences have threshold

```text
ℓ₁ × ∏_{j=2}^k (ℓⱼ + 1).
```

Its special cases are `n` for one group of size `n`, `2^(n-1)` for `n` singleton groups, and `ℓ(ℓ+1)^(k-1)` for `k` equal groups. These are upper-bound results for the prescribed grouping.

The seven principal real and grouped endpoints are in [Solution.lean](../Solution.lean). The special-case identities are in [GroupedSpecialCases.lean](../KungTraub/GroupedSpecialCases.lean).

## Attainment on real intervals

For `n ≥ 2`, `inverseHermiteAlgorithm n` first observes `f(x)` and `f′(x)`, then uses inverse Hermite interpolation and further function values, with immediate stopping at an observed zero. It uses at most `n` observations. The case `n = 2` is Newton's update.

`KungTraubAppendices.inverseHermite_universal_local_order` proves order `2^(n-1)` near every simple zero of every analytic function on an arbitrary open real interval. It also proves that all actual query locations stay inside the interval for sufficiently close starts.

For `f(x) = exp(x) − 1`, the same algorithm satisfies the two-sided punctured limit

```text
A_n(f,x) / x^(2^(n-1)) → κ_(n-1) > 0   as x → 0,
κ₁ = 1/2,   κ_(j+1) = (∏_{i=1}^j κ_i) / (j+2).
```

Thus the exponential example has exact order `2^(n-1)`. Combining attainment with the real upper bound gives the optimal universal exponent in this interval-local model for every `n ≥ 2`.

The endpoints are in [HermiteLocalOrder.lean](../KungTraubAppendices/HermiteLocalOrder.lean), [ExponentialAsymptotic.lean](../KungTraubAppendices/ExponentialAsymptotic.lean), [SharpnessConclusion.lean](../KungTraubAppendices/SharpnessConclusion.lean) and [IntervalOptimalOrder.lean](../KungTraubAppendices/IntervalOptimalOrder.lean).

## Complex observations

A complex derivative value counts as one observation. For every `n ≥ 1`, every `ComplexAlgorithm n`, and every real `p > 2^(n-1)`, `KungTraubAppendices.complex_entire_counterexample` constructs an entire function `F` with

```text
‖F′(z) − 1‖ ≤ 1/4   for ‖z‖ ≤ 1.
```

The function has a simple zero `α` in the open unit disc, unique among zeros in the closed unit disc, and a sequence of nonroot complex starts tending to `α` along which the order-`p` error ratios tend to infinity. Query locations and derivative orders are unrestricted in the entire-input model.

`no_complex_universal_order_above` gives the consequence for holomorphic functions on arbitrary open complex domains, with query admissibility included in the local-order property. `no_complex_partial_universal_order_above` gives the corresponding result for partial query and output rules.

See [ComplexConclusion.lean](../KungTraubAppendices/ComplexConclusion.lean) and [ComplexPartialAlgorithms.lean](../KungTraubAppendices/ComplexPartialAlgorithms.lean).

## Proof structure and library use

Polynomial Wronskians control exceptional query locations. Finite-dimensional adversaries retain indistinguishable inputs through adaptive observations. Compatible correction stages then produce entire witnesses while preserving earlier derivative observations exactly. The interpolation development supplies the local inverse analysis, confluent remainder bounds and the exponential asymptotic coefficient.

The formal proof uses polynomial factorization and evaluation estimates for root persistence, and coefficientwise synthetic division with compact root tuples for limiting multiplicities. For the complex construction's near-identity root-existence steps, a contraction on the closed unit disc supplies the existence, uniqueness, location and simplicity conclusions under the stated value and derivative bounds. These arguments replace the corresponding uses of Rouché's theorem. Numerical estimates use exact symbolic proofs.

Mathlib supplies the surrounding algebra, analysis and topology. Central reused developments include Lagrange interpolation and nodal polynomials by Kenny Lau and Wrenna Robson; analytic and strict-derivative local inverses by David Loeffler, Sébastien Gouëzel and Yury Kudryashov; logarithm series by Geoffrey Irving; and analytic power-factor derivative identities by Michail Karatarakis. Source module comments give the specific reuse and attribution.

## Mathematical sources

- Matthew J. Colbrook, *Adversarial Wronskians: A proof of the Kung–Traub conjecture*, manuscript. The main theorem, grouped corollary, supporting arguments and Appendices A–B supply the mathematical statements and constructions.
- H. T. Kung and J. F. Traub, “Optimal order of one-point and multipoint iteration,” *Journal of the ACM* **21**(4) (1974), 643–651. Attribution for the attaining methods.
- C. de Boor, “Divided differences,” *Surveys in Approximation Theory* **1** (2005), 46–69, Section 8, equation (44). Source of the cited divided-difference estimate.
