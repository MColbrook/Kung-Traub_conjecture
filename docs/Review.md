# Mathematical review guide

Successful kernel checking establishes the formal conclusions from their formal hypotheses. Successful Comparator checking establishes agreement with the reference statements under the permitted axioms. The remaining mathematical review is the correspondence between those statements, their definitions and the paper. Comparator cannot decide whether a definition expresses the intended meaning of “algorithm”, “observation” or “local order”.

The principal references import definitions also used by the solution. Agreement between the two sides therefore does not replace inspection of those definitions. Under the stated trust in the checking process, individual tactics need not be audited again. Human judgment remains necessary for the translation from the paper to the formal statements.

## 1. Fix the statements being reviewed

Begin with [Challenge.lean](../Challenge.lean), beside the main theorem, grouped corollary and appendices of the paper. Use [Mathematics.md](Mathematics.md) as an index, then inspect the Lean declarations themselves.

The twelve principal statements comprise seven real/grouped results, two complex results and three attainment/sharpness results. Check every binder before the colon, including implicit binders in braces. For example, `{n : ℕ}`, `(hn : 1 ≤ n)` and `(A : RealAlgorithm n)` mean every positive integer budget and every algorithm in the specified model. They do not assert a result for one chosen budget or algorithm.

Confirm these thresholds and quantifiers:

- The upper bounds require `n ≥ 1`; attainment and the exponential sharpness example require `n ≥ 2`.
- The forbidden exponent `p` ranges over real numbers and satisfies a strict inequality.
- The grouped theorem requires a positive number of groups and positive prescribed group sizes.
- An ordinary counterexample may depend on `p`. In the simultaneous result, one function and one sequence work for every larger real exponent.

The `sorry` declarations here are reference placeholders. The checked solution is the import closure of [All.lean](../All.lean), which does not import `Challenge` or the reference modules. The solution has no such proof holes.

## 2. Inspect the real oracle and the meaning of order

Read [KungTraub/Definitions.lean](../KungTraub/Definitions.lean) in full. This is the most important file for the main theorem and corollary.

| Definitions | Mathematical points to verify |
| --- | --- |
| `orderBound`, `groupedOrderBound` | For positive `n`, the bound is `2^(n-1)`. The grouped bound is `ℓ₁ ∏_{j=2}^k (ℓⱼ+1)`, with the first group treated differently. |
| `RealQuery`, `RealQuery.answer` | One answer is one derivative value of any natural order; order zero is a function value. An idle slot provides no information. |
| `RealAlgorithm`, `prefix`, `run` | A query receives the starting point and precisely the earlier answers. Neither query selection nor output receives the input function, root, or future answers. The rules are arbitrary functions, with no continuity, measurability or computability hypothesis. There is no state carried between updates. |
| `GroupedRealAlgorithm`, its `prefix` and `run` | Every query in a group is chosen from earlier groups alone. No answer from the current group influences another query in that group. |
| `EntireRealType`, `realRestriction` | The witness is entire on the complex plane and real on the real axis. Taking its real restriction loses no real-axis information. |
| `SimpleRealRoot`, `LocalOrderAt` | The root is simple. Positive constants `C` and `δ` precede the universal quantifier over starts, so they cannot depend on the individual start. The estimate uses the real power of the absolute distance and holds throughout a punctured neighbourhood. |
| `EntireUniversalLocalOrder`, `AnalyticUniversalLocalOrder` | Every input and every simple root are covered; local constants may depend on that input and root. The second input class consists of functions analytic at every real point. |
| `EntireWitnessData` | The derivative bounds are globally `3/4 ≤ f′ ≤ 5/4`; the zero is unique on the real line; all starts differ from it and converge to it. Uniqueness in the whole complex plane is not asserted. |
| `errorRatio`, `ErrorRatioDiverges`, `EntireCounterexample` | The numerator is the actual output error. The denominator is the starting error to the real exponent `p`. The ratios tend to positive infinity, rather than merely exceeding one bound at one point. |
| `SimultaneousEntireCounterexample` | The existential function, root and sequence precede `∀ p`, preserving the stronger quantifier order. |

The starting sequence consists of independent inputs to one update. It need not be an orbit of repeated updates. Check that this is the local-order notion intended in the paper. Lean sequence indices start at zero; positive manuscript stage indices correspond to an index shift.

Next read the statements in [Consequences.lean](../KungTraub/Consequences.lean) and [AnalyticRestriction.lean](../KungTraub/AnalyticRestriction.lean). They connect the constructed witness to failure of universal order and to the broader real-analytic class. The seven real/grouped endpoints are collected in [Solution.lean](../Solution.lean).

## 3. Check stopping and partial rules

Read the definitions and theorem statements in [LocalAndStoppingAlgorithms.lean](../KungTraub/LocalAndStoppingAlgorithms.lean), especially:

- `BoundedRealTree`, `observationCount` and `observationCount_le`;
- `StoppingRealAlgorithm.padded` and `padded_run_eq`;
- `PartialRealAlgorithm`, `totalExtension_run_eq` and `totalExtension_actualQuery_eq`;
- `DefinedNear`, the partial `LocalOrderAt`, and `localOrderAt_totalExtension_iff`.

Check that padding preserves the actual output and that total extension preserves every defined execution. Local order for a partial method requires an output at every sufficiently close nonroot start. It does not become true by omitting difficult starts. The reverse implication for total extension explicitly assumes a full neighbourhood of defined executions.

These definitions and preservation results justify representing the paper's stopping and partial procedures by the total fixed-budget oracle.

## 4. Check Appendix A: the actual attaining method

Read [SharpnessDefinitions.lean](../KungTraubAppendices/SharpnessDefinitions.lean) in full, together with the definition and characteristic theorem statements of `hermiteWithDerivative` in [HermiteInterpolation.lean](../KungTraubAppendices/HermiteInterpolation.lean).

Follow one execution of `inverseHermiteTree` and `inverseHermiteTail`: the initial observations are `f(x)` and `f′(x)`; subsequent observations are function values. The inverse interpolation nodes are observed values, their ordinates are the corresponding query locations, and the derivative datum is `1/f′(x)`. The next location is the interpolant evaluated at zero. A queried zero causes immediate stopping; the final output requires no extra observation.

The formulas are defined on arbitrary transcripts, including degenerate ones. Their interpolation properties carry the necessary distinctness hypotheses. The final local-order theorem must establish validity near simple roots, rather than assume that every arbitrary transcript is valid.

Inspect these statements:

| File | Points to verify |
| --- | --- |
| [SharpnessElementary.lean](../KungTraubAppendices/SharpnessElementary.lean) | At most `n` observations, equality of padded and stopping outputs, Newton's method when `n = 2`, and the coefficient recurrence and positivity. |
| [HermiteObservationCount.lean](../KungTraubAppendices/HermiteObservationCount.lean) | Exactly `n` observations on the stated nonstopping executions; eventually exactly `n` on the exponential example. |
| [HermiteLocalOrder.lean](../KungTraubAppendices/HermiteLocalOrder.lean) | The concluding theorem concerns the concrete algorithm for every analytic input on an arbitrary open real interval. |
| [ExponentialAsymptotic.lean](../KungTraubAppendices/ExponentialAsymptotic.lean) | The limit concerns the actual algorithm on `exp(x)-1`, uses `x^(2^(n-1))`, and is two-sided through `𝓝[≠] 0`. Its coefficient is `sharpnessCoefficient (n-1)`. |
| [SharpnessConclusion.lean](../KungTraubAppendices/SharpnessConclusion.lean) | Every strictly larger real exponent fails for that same example and algorithm. |
| [IntervalOptimalOrder.lean](../KungTraubAppendices/IntervalOptimalOrder.lean) | Attainment and impossibility are combined in the same interval-local model, for the same observation budget. |

Expand `RealIntervalUniversalLocalOrder` in `SharpnessDefinitions.lean`: it requires both the error estimate and membership of every actual query location in the input interval, throughout a full punctured neighbourhood. The analytic input hypothesis is local to the interval. Lean represents the function by a total map, but no analyticity outside that interval is assumed.

Check the coefficient indexing against the paper: `κ₁ = 1/2`, `κ_(j+1) = (∏_{i=1}^j κ_i)/(j+2)`, and the `n`-observation method has coefficient `κ_(n-1)`. The value at index zero is an initial convention.

## 5. Check Appendix B: complex observations

Read [ComplexDefinitions.lean](../KungTraubAppendices/ComplexDefinitions.lean) in full, then [ComplexConclusion.lean](../KungTraubAppendices/ComplexConclusion.lean).

Verify that one complex derivative value counts as one observation; derivative order and complex query location are unrestricted in the entire-input model. The same restriction to previous answers holds as in the real model.

Expand `ComplexWitnessData` and `ComplexEntireCounterexample`. The witness is entire, satisfies `‖f′(z)-1‖ ≤ 1/4` on the closed unit disc, has its zero strictly inside that disc, and has no other zero in the closed disc. The derivative bound implies simplicity. The nonroot complex starts converge to the root and their norm-based error ratios tend to positive infinity. The exponent remains real.

Expand `ComplexUniversalLocalOrder`: the domains are arbitrary open subsets of the complex plane, and both query admissibility and the order estimate hold on one full punctured neighbourhood. For the extension to partial rules, inspect `PartialComplexAlgorithm`, `DefinedNear`, `LocalOrderAt`, `UniversalLocalOrder` and `no_complex_partial_universal_order_above` in [ComplexPartialAlgorithms.lean](../KungTraubAppendices/ComplexPartialAlgorithms.lean).

## 6. Relate the statements to the recorded checks

Read [Verification/principals.json](../Verification/principals.json) alongside `Challenge.lean`. Its twelve theorem names are compared against the solution module `All`. The three supporting configurations add the remaining named theorems, with overlaps between lists. The union has 1,058 targets.

[Verification/Axioms.lean](../Verification/Axioms.lean) requests the dependencies of 1,202 declarations, including every target. [Verification.md](Verification.md#release-checks) links the actual checking output and [results.json](../Verification/Results/results.json), which binds the checked sources and configurations by their hashes. The permitted axioms are `propext`, `Classical.choice` and `Quot.sound`.

Given trust in those successful checks, there is no need to reread all 232 supporting reference files to establish the principal results. Their statements are relevant when separately matching individual supporting claims in the paper. Likewise, auditing the checking scripts is a separate task if the checking process itself is placed in question.

## 7. Optional reading of the proof construction

For comparison with the argument in the paper, follow these routes, starting from the endpoints and following their imports and cited declarations:

- Real upper bound: [PolynomialWronskians.lean](../KungTraub/PolynomialWronskians.lean), [FiniteAdversary.lean](../KungTraub/FiniteAdversary.lean), [EntireStageConstruction.lean](../KungTraub/EntireStageConstruction.lean), [EntireStageSequence.lean](../KungTraub/EntireStageSequence.lean), then `Solution.lean`.
- Grouped bound: [GroupedStageConstruction.lean](../KungTraub/GroupedStageConstruction.lean) and [GroupedEntireWitness.lean](../KungTraub/GroupedEntireWitness.lean).
- Attainment: the interpolation, remainder and local-data developments leading to `HermiteLocalOrder.lean`; the exponential asymptotic development leading to `SharpnessConclusion.lean`.
- Complex upper bound: [ComplexPolynomialStage.lean](../KungTraubAppendices/ComplexPolynomialStage.lean), [ComplexEntireStages.lean](../KungTraubAppendices/ComplexEntireStages.lean), [ComplexStageSequence.lean](../KungTraubAppendices/ComplexStageSequence.lean), then `ComplexConclusion.lean`.

The formal arguments use factorization and evaluation estimates for polynomial root persistence, synthetic division for limiting multiplicities, and a contraction argument for the complex near-identity root-existence step. These adaptations are described in [Mathematics.md](Mathematics.md#proof-structure-and-library-use). A kernel-checked proof of the stated results does not, by itself, certify every sentence of the informal manuscript or require the formal proof to follow it line by line.

The essential review is complete when every hypothesis, definition, domain, count, constant and quantifier in the principal results has been matched to its intended mathematical meaning, including the stopping, partial-rule and local-domain interpretations. Any unfamiliar custom definition should be followed to its definition; familiar standard Mathlib notions provide the remaining mathematical vocabulary.
