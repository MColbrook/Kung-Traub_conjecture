import KungTraubAppendices.ExponentialAsymptotic
import KungTraubAppendices.ExactOrderObstruction

/-! The exponential example excludes every larger real local exponent. -/

namespace KungTraubAppendices

/-- No larger real local exponent holds on the exponential witness for the
same observation algorithm whose interval-local order was established. -/
theorem inverseHermite_not_local_order_exp (n : ℕ) (hn : 2 ≤ n)
    (p : ℝ) (hp : (KungTraub.orderBound n : ℝ) < p) :
    ¬ KungTraub.LocalOrderAt (inverseHermiteAlgorithm n).run
      (fun t => Real.exp t - 1) 0 p :=
  not_localOrderAt_zero_of_normalized_limit
    (sharpnessCoefficient_pos (n - 1)).ne' (inverseHermite_exp_asymptotic n hn) p hp

end KungTraubAppendices
