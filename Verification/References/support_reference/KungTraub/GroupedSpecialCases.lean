import support_reference.KungTraub.GroupedExponents

/-!
# Special cases of the prescribed-group bound

These exact identities are the specializations stated after Corollary 1.2 in
Matthew J. Colbrook's manuscript: one group, singleton groups, and groups of
equal size. The natural-number formulas and their real casts use Mathlib's
finite-product identities.
-/

namespace KungTraub

/-- A single group of n observations has threshold n. -/
theorem groupedOrderBound_single (n : ℕ) :
    groupedOrderBound (fun _ : Fin 1 => n) = n := by
  sorry

/-- A positive number k of equal-sized groups has threshold ℓ(ℓ+1)^(k-1).
The identity itself also holds when the common size is zero. -/
theorem groupedOrderBound_equal {k : ℕ} (hk : 0 < k) (ℓ : ℕ) :
    groupedOrderBound (fun _ : Fin k => ℓ) = ℓ * (ℓ + 1) ^ (k - 1) := by
  sorry

/-- n singleton groups have the unrestricted scalar threshold 2^(n-1). -/
theorem groupedOrderBound_singletons {n : ℕ} (hn : 0 < n) :
    groupedOrderBound (fun _ : Fin n => 1) = 2 ^ (n - 1) := by
  sorry

/-- The single-group identity in the real field used to compare exponents. -/
theorem groupedOrderBound_single_real (n : ℕ) :
    (groupedOrderBound (fun _ : Fin 1 => n) : ℝ) = (n : ℝ) := by
  sorry

/-- The equal-group identity in the real field used to compare exponents. -/
theorem groupedOrderBound_equal_real {k : ℕ} (hk : 0 < k) (ℓ : ℕ) :
    (groupedOrderBound (fun _ : Fin k => ℓ) : ℝ) =
      (ℓ : ℝ) * ((ℓ : ℝ) + 1) ^ (k - 1) := by
  sorry

/-- The singleton-group identity in the real field used to compare exponents. -/
theorem groupedOrderBound_singletons_real {n : ℕ} (hn : 0 < n) :
    (groupedOrderBound (fun _ : Fin n => 1) : ℝ) = (2 : ℝ) ^ (n - 1) := by
  sorry

end KungTraub

