# Kung–Traub in Lean

A Lean formalization of Matthew J. Colbrook's [*Adversarial Wronskians: A proof of the Kung–Traub conjecture*](https://doi.org/10.5281/zenodo.22850057), including the main real theorem, the grouped-observation corollary, inverse Hermite attainment and sharpness, and the complex-observation theorem.

For deterministic stationary methods without memory, the formalization proves the scalar upper bound `2^(n-1)` for `n ≥ 1`. It constructs the inverse Hermite method attaining this exponent for `n ≥ 2`, and proves the corresponding upper bound for complex derivative observations. The [mathematical overview](docs/Mathematics.md) gives the precise domains, quantifiers and theorem locations.

## Mathematical statements and model

One observation returns one derivative value of any natural order, with order zero meaning a function value. Each query and the final output depend only on the starting point and earlier answers. The rules receive neither the input function nor its root, and retain no state between updates. They need not be continuous, measurable, or computable. An idle padding slot has no location and gives no information. In the complex model, one complex derivative value counts as one observation.

Local order at a specified simple root `α` means that there are fixed `C > 0` and `δ > 0` such that `|T(f,x)-α| ≤ C |x-α|^p` for **every** start with `0 < |x-α| < δ`; complex statements use norms. The constants may depend on the fixed method, input, root, and real exponent, but not on the individual start. Universal order quantifies over every input and every simple root. Interval/domain-local properties also require defined executions and every actual query location to lie in the input domain throughout that neighborhood. Inputs are represented by total maps, with analytic or holomorphic hypotheses imposed only on the stated domain.

The principal counterexamples use total fixed-budget rules. Supporting theorems represent early stopping by idle padding and preserve every defined execution of a partial rule under an arbitrary total extension. The partial-method local-order property requires an output at every sufficiently close nonroot start; transferring a total extension's local order back to a partial method requires this full neighborhood of defined executions. A counterexample for an arbitrary extension is not, by itself, a claim that the original partial method is defined along the counterexample sequence.

Write `B(n) = 2^(n-1)` for `n ≥ 1`. The real counterexample property below means that there is an entire complex function real on the real axis, whose real restriction `f` has a unique real root `α` and satisfies `3/4 ≤ f′(t) ≤ 5/4` for every real `t`. There are independent nonroot starts `x_s → α` with `|A(f,x_s)-α| / |x_s-α|^p → +∞`. These starts need not form an iteration orbit, and uniqueness among complex zeros is not claimed. Unless the statement says simultaneous, the witness may depend on `p`.

For prescribed groups, `k ≥ 1` and each fixed size `ℓ_j ≥ 1`; every query in a group is selected before any answer from that group is received. Write `G = ℓ₁ ∏_(j=2)^k (ℓ_j+1)`.

The selected [Palomar configuration](Verification/palomar-principals.json) compares these twelve declarations:

| Declaration | Precise scope |
| --- | --- |
| `KungTraub.entire_counterexample` | For every budget `n ≥ 1`, every real algorithm with that budget, and every real `p > B(n)`, the real counterexample property above holds. |
| `KungTraub.no_entire_universal_order_above` | Under the same budget and exponent conditions, no such algorithm has universal local order `p` on entire real-type inputs. |
| `KungTraub.no_universal_order_above` | Under the same conditions, universal local order `p` also fails on the class of functions analytic at every real point. |
| `KungTraub.grouped_entire_counterexample` | For every prescribed positive group schedule, every algorithm following it, and every real `p > G`, the real counterexample property holds. |
| `KungTraub.no_grouped_entire_universal_order_above` | Under the same group and exponent conditions, universal local order `p` fails on entire real-type inputs. |
| `KungTraub.no_grouped_universal_order_above` | Under the same conditions, universal local order `p` fails on functions analytic at every real point. |
| `KungTraub.simultaneous_entire_counterexample` | For every `n ≥ 1` and every real algorithm with that budget, one entire real-type function, one root, and one nonroot starting sequence have the stated derivative/root properties and divergent error ratios for **every** real `p > B(n)`. |
| `KungTraubAppendices.complex_entire_counterexample` | For every `n ≥ 1`, every complex algorithm with that budget, and every real `p > B(n)`, an entire input has `‖f′(z)-1‖ ≤ 1/4` on the closed unit disc and a zero strictly inside it, unique in the closed disc. Nonroot complex starts converge to this simple zero with norm-based error ratios tending to `+∞`. |
| `KungTraubAppendices.no_complex_universal_order_above` | Under the same complex budget and exponent conditions, universal local order `p`, including query admissibility, fails for holomorphic inputs on arbitrary open complex domains. |
| `KungTraubAppendices.inverseHermite_universal_local_order` | For every `n ≥ 2`, the concrete inverse Hermite algorithm has order `B(n)` near every simple zero of every analytic input on an arbitrary open real interval, including admissibility of all actual queries. |
| `KungTraubAppendices.inverseHermite_exp_asymptotic` | For every `n ≥ 2`, on `f(x)=exp(x)-1`, the same algorithm satisfies `A(f,x)/x^B(n) → κ_(n-1)` through the full two-sided punctured neighborhood of zero. |
| `KungTraubAppendices.inverseHermite_not_local_order_exp` | For every `n ≥ 2` and every real `p > B(n)`, that same algorithm and exponential input fail the local-order-`p` estimate at zero. |

The attaining method observes `f(x)` and `f′(x)`, then further function values, with immediate stopping at a queried zero; its final computed output requires no observation. It uses at most `n` observations, and eventually exactly `n` on the exponential example. Its coefficients satisfy `κ₀=1`, `κ₁=1/2`, and `κ_(j+1)=(∏_(i=1)^j κ_i)/(j+2)`; all are positive. Budgets zero and one have arbitrary total extensions in this construction, and attainment is asserted only for `n ≥ 2`. The interpolation formulas are total even on degenerate transcripts; their validity near a simple root is proved, not assumed. Combining attainment with the real upper bound also proves the optimal universal exponent in the same interval-local model.

The Lean proofs use factorization and evaluation estimates for polynomial root persistence, synthetic division and compact root tuples for limiting multiplicities, and contraction for the complex near-identity root-existence argument in place of Rouché's theorem. Stage indices start at zero. The grouped entire witnesses and simultaneous real counterexample strengthen the corresponding upper-bound statements. These are declared proof adaptations and scope distinctions, not additional unproved assumptions.

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

The recorded release snapshot passed a clean build, an axiom audit of 1,202 declarations and secure Comparator checks of all 1,058 named theorems. Those historical checks used Comparator revision `3927ad383f208ae977c340a91c48ac9b497d2097` with NanoDa disabled. The [verification results](docs/Verification.md#release-checks) identify the checked sources, commands and output; they do not certify later repository changes.

## Palomar registration

The twelve principal results at commit [902bb22e24fb5c4e8e319305fb75378fb32d9eb4](https://github.com/MColbrook/Kung-Traub_conjecture/tree/902bb22e24fb5c4e8e319305fb75378fb32d9eb4) are registered as [PALOMAR-2026-09-20-000006, version 1](https://palomar-registry.org/entry?id=PALOMAR-2026-09-20-000006&version=1). The registration records that fixed snapshot; later commits do not change version 1.

The registered entry uses [Verification/palomar-principals.json](https://github.com/MColbrook/Kung-Traub_conjecture/blob/902bb22e24fb5c4e8e319305fb75378fb32d9eb4/Verification/palomar-principals.json), the standalone statement module [PalomarChallenge.lean](https://github.com/MColbrook/Kung-Traub_conjecture/blob/902bb22e24fb5c4e8e319305fb75378fb32d9eb4/PalomarChallenge.lean), and solution module `All`. The original [Challenge.lean](Challenge.lean) and four release configurations remain part of the historical verification record. Challenge/reference `sorry` declarations are deliberate statement placeholders; they are excluded from the solution's zero-proof-hole claim and from its import closure.

The [full preflight for the registered commit](https://github.com/MColbrook/Kung-Traub_conjecture/actions/runs/35509148070) passed Comparator, Lean, and independent NanoDa verification of the twelve principal results. The [preparation guide](docs/Palomar.md) records the workflow and checks performed before registration.

The [mathematical review guide](docs/Review.md) gives a reading order for checking the statements, definitions and their correspondence with the paper.

## Attribution

The source result and proof are Matthew J. Colbrook's [paper](https://doi.org/10.5281/zenodo.22850057). This repository formalizes that source; it is not presented as a result first introduced by the formalization. The attaining methods are attributed to H. T. Kung and J. F. Traub, [“Optimal order of one-point and multipoint iteration,” *Journal of the ACM* 21(4) (1974), 643–651](https://doi.org/10.1145/321850.321860). The divided-difference estimate is attributed to C. de Boor, [“Divided differences,” *Surveys in Approximation Theory* 1 (2005), 46–69, Section 8, equation (44)](https://arxiv.org/abs/math/0502036). The formalization builds on the pinned Mathlib library, with specific reused formal results and their contributors credited in the source. Further bibliographic details appear in [Mathematics.md](docs/Mathematics.md).

As disclosed in the paper, ChatGPT 6 assisted with the Lean formalization. ChatGPT 5.6 and 6 were also interactive aids for discussing and checking mathematical arguments. Matthew J. Colbrook reviewed and adopted the mathematical arguments, statements, and proofs and takes responsibility for the work. Automated assistance is credited as part of the production process; the project's human author and responsible maintainer is Matthew J. Colbrook. The recorded build, axiom audit, and Comparator results are separate mechanical evidence and do not establish novelty or independent mathematical peer review.

The repository also provides a [GitHub citation file](CITATION.cff) identifying the paper as the preferred citation.

Copyright © 2026 Matthew J. Colbrook. The repository is licensed under [Apache-2.0](LICENSE); see [COPYRIGHT.md](COPYRIGHT.md) for attribution. Cited works and third-party components retain their own licences.
