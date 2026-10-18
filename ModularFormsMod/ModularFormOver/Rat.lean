import ModularFormsMod.ModularFormOver.PInteger


/-!
# Rational Eisenstein series and scalar extension

`ModularFormOver.Eis` bundles the integer-weight Eisenstein series with its
rationality proof. Its Fourier coefficients are expressed using Bernoulli
numbers and divisor sums, and rational forms extend to characteristic-zero
fields equipped with an algebra map to `ℂ`.
-/



open ModularForm ModularFormOver UpperHalfPlane MatrixGroups ArithmeticFunction.sigma


/-- Forms with rational Fourier coefficients extend to any characteristic-zero field equipped
with an algebra map to `ℂ`. -/
instance ModularFormOverClass.towerℚ {F : Type*} [FunLike F ℍ ℂ]
  {Γ : Subgroup (GL (Fin 2) ℝ)} {k : ℤ} [hF : ModularFormOverClass F ℚ Γ k]
    (R : Type) [Field R] [CharZero R] [Algebra R ℂ] : ModularFormOverClass F R Γ k :=
  hF.tower ℚ R

@[coe]
noncomputable instance {Γ k} (R : Type) [Field R] [CharZero R] [Algebra R ℂ] :
  Coe (ModularFormOver ℚ Γ k) (ModularFormOver R Γ k) := ⟨ModularFormOver.tower R⟩

namespace ModularFormOver

/-- The integer-weight normalized Eisenstein series, regarded as a modular form over `ℚ`. -/
noncomputable def Eis (k : ℤ) : ModularFormOver ℚ 𝒮ℒ k where
  toModularForm := ModularForm.Eis k
  isOver' := by
    rw [isOver_iff]
    intro n
    rw [qExp_SL2Z, qExpansion_Eis]
    split_ifs
    · exact one_mem _
    · norm_cast; exact Map_mem_rangeMap _
    · exact zero_mem _
    · exact zero_mem _


/-- For even weights at least four, the Eisenstein coefficients are given by Bernoulli numbers
and divisor sums. -/
theorem coeff_Eis {k : ℤ} (hk : 3 ≤ k) (hk2 : Even k) (n : ℕ)
  (R S : Type := ℚ) [Field R] [CharZero R] [Algebra R ℂ] [Field S]
    [CharZero S] [Algebra R S] [Algebra S ℂ] [IsScalarTower R S ℂ] :
  coeff R n (Eis k) S = if n = 0 then (1 : S) else
    -(2 * k / bernoulli k.toNat ) * σ (k.toNat - 1) n := by
  rw [coeff_eq_iff, show qExp (Eis k) = qExpansion 1 (ModularForm.Eis k) by
    rw [qExp_SL2Z]; rfl, qExpansion_Eis, ite_eq_left hk, ite_eq_left hk2]
  split_ifs
  · exact map_one _ |>.symm
  · norm_cast
    change _ = algebraMap S ℂ (algebraMap ℚ S _)
    rw [← IsScalarTower.algebraMap_apply ℚ S ℂ]
    simp




end ModularFormOver
