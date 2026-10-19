/-
Copyright (c) 2026 Carter Hastings. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carter Hastings
-/

import Mathlib.NumberTheory.ModularForms.EisensteinSeries.QExpansion

/-!
# Eisenstein series indexed by integer weights

`ModularForm.Eis k` extends the normalized level-one Eisenstein series to all
integer weights by setting it to zero below weight three. This file proves its
vanishing in odd weights and gives its Bernoulli and divisor-sum coefficient formula.
-/


open ModularForm MatrixGroups UpperHalfPlane ArithmeticFunction.sigma

namespace ModularForm

/-- The normalized level-one Eisenstein series of integer weight `k`, set to zero when `k < 3`. -/
noncomputable def Eis (k : ℤ) : ModularForm 𝒮ℒ k :=
  if hk : 3 ≤ k then
    mcast (by lia) (E (show 3 ≤ k.toNat by lia))
  else 0

/-- The negative identity matrix belongs to the full modular group. -/
@[simp] theorem neg_one_mem_SL2Z : -1 ∈ 𝒮ℒ :=
  ⟨-1, by ext; simp⟩


/-- The integer-weight Eisenstein series vanishes in every odd weight. -/
theorem Eis_odd {k : ℤ} (hk : Odd k) : ModularForm.Eis k = 0 :=
  eq_zero_of_neg_one_mem neg_one_mem_SL2Z hk _


/-- The Bernoulli and divisor-sum coefficient formula for the Eisenstein series, including its
zero cases. -/
theorem qExpansion_Eis (k : ℤ) (m : ℕ) :
  (qExpansion 1 (ModularForm.Eis k)).coeff m =
  if 3 ≤ k then if Even k then
    if m = 0 then 1 else -(2 * k / bernoulli k.toNat : ℂ) * (σ (k.toNat - 1) m)
      else 0 else 0 := by
  by_cases hk : 3 ≤ k
  · by_cases hk2 : Even k
    · lift k to ℕ using by lia
      simp_all [ModularForm.Eis, EisensteinSeries.E_qExpansion_coeff (mod_cast hk) (mod_cast hk2)]
    · simpa [Eis_odd (Int.not_even_iff_odd.mp hk2), qExpansion_zero]
        using fun _ t => hk2 t |>.elim
  · simp [ModularForm.Eis, hk, qExpansion_zero]

end ModularForm
