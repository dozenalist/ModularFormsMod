import Mathlib.NumberTheory.ModularForms.EisensteinSeries.QExpansion




open ModularForm MatrixGroups UpperHalfPlane ArithmeticFunction.sigma

namespace ModularForm

noncomputable def Eis (k : ℤ) : ModularForm 𝒮ℒ k :=
  if hk : 3 ≤ k then
    mcast (by lia) (E (show 3 ≤ k.toNat by lia))
  else 0

@[simp] theorem neg_one_mem_SL2Z : -1 ∈ 𝒮ℒ :=
  ⟨-1, by ext; simp⟩


theorem Eis_odd {k : ℤ} (hk : Odd k) : ModularForm.Eis k = 0 :=
  eq_zero_of_neg_one_mem neg_one_mem_SL2Z hk _


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
