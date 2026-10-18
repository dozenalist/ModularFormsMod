import ModularFormsMod.ModularFormOver.GradedRing
import ModularFormsMod.ModularFormOver.Derivative
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.NumberTheory.ModularForms.RamanujanFormula

/-!
# The Serre derivation on polynomials

`MvPolynomial.Del` is the derivation determined by `Del X₀ = -4 X₁` and
`Del X₁ = -6 X₀²`. Polynomial representation identifies it with the normalized
Serre derivative `12 θ - k E₂` on level-one modular forms.
-/

set_option linter.style.header false

noncomputable section

open MatrixGroups
open scoped DirectSum

namespace MvPolynomial

variable {R : Type} [CommRing R]

/-- The polynomial form of the normalized Serre derivative, with variable weights four and six. -/
def Del : Derivation R (MvPolynomial (Fin 2) R) (MvPolynomial (Fin 2) R) :=
  mkDerivation R ![(-4 : R) • X 1, (-6 : R) • (X 0) ^ 2]

@[simp] theorem Del_X_zero : Del (X 0 : MvPolynomial (Fin 2) R) = (-4 : R) • X 1 := by
  simp [Del]

@[simp] theorem Del_X_one : Del (X 1 : MvPolynomial (Fin 2) R) = (-6 : R) • (X 0) ^ 2 := by
  simp [Del]

/-- The formula for `Del` in terms of partial derivatives. -/
theorem Del_apply (p : MvPolynomial (Fin 2) R) :
    Del p = (-4 : R) • (X 1 * pderiv 0 p) +
      (-6 : R) • ((X 0) ^ 2 * pderiv 1 p) := by
  have h : (Del : Derivation R (MvPolynomial (Fin 2) R) (MvPolynomial (Fin 2) R)) =
      ((-4 : R) • (X 1 : MvPolynomial (Fin 2) R)) • pderiv (R := R) 0 +
        ((-6 : R) • (X 0 : MvPolynomial (Fin 2) R) ^ 2) • pderiv (R := R) 1 := by
    apply derivation_ext
    intro i
    fin_cases i <;> simp [smul_eq_mul]
  rw [h, Derivation.add_apply, Derivation.smul_apply, Derivation.smul_apply]
  simp only [smul_eq_mul, Algebra.smul_def, map_neg, map_ofNat]
  ring

end MvPolynomial

namespace ModularFormOver

variable {R : Type} [CommRing R] [Algebra R ℂ] [FaithfulSMul R ℂ]
  {k j : ℤ}

private def serreLinearMap (k : ℤ) :
    ModularFormOver R 𝒮ℒ k →ₗ[R] ModularFormOver R 𝒮ℒ (k + 2) where
  toFun := normalizedSerreDerivative R
  map_add' f g := by
    apply fourier_inj R R
    simp only [fourier_normalizedSerreDerivative, fourier_add, normalizedSerreFourier,
      map_add, mul_add, smul_add]
    abel
  map_smul' a f := by
    apply fourier_inj R R
    simp only [fourier_normalizedSerreDerivative, fourier_smul, normalizedSerreFourier,
      Derivation.map_smul, mul_smul_comm, smul_sub]
    simp only [PowerSeries.smul_eq_C_mul, map_mul, map_ofNat, RingHom.id_apply]
    ring

private theorem serre_apply (f : ModularFormOver R 𝒮ℒ k) (z : UpperHalfPlane) :
    normalizedSerreDerivative R f z =
      12 * Derivative.serreDerivative (k : ℂ) f z := by
  change ((12 : ℂ) * cuspWidth 𝒮ℒ) * _ = _
  simp only [cuspWidth_SL2Z, Nat.cast_one, mul_one]
  rfl

private theorem serre_mul (f : ModularFormOver R 𝒮ℒ k)
    (g : ModularFormOver R 𝒮ℒ j) :
    normalizedSerreDerivative R (f.mul g) =
      ((normalizedSerreDerivative R f).mul g).cast (by omega) +
        (f.mul (normalizedSerreDerivative R g)).cast (by omega) := by
  apply ext₂
  intro z
  simp only [serre_apply, add_apply, cast_apply, mul_apply]
  change 12 * Derivative.serreDerivative ((k + j : ℤ) : ℂ) (⇑f * ⇑g) z = _
  rw [Int.cast_add, Derivative.serreDerivative_mul (k : ℂ) (j : ℂ)
    (F := ⇑f) (G := ⇑g) (ModularFormClass.holo f) (ModularFormClass.holo g)]
  simp only [Pi.add_apply, Pi.mul_apply]
  ring

private theorem serre_E₄ :
    normalizedSerreDerivative R (E₄.tower R) = (-4 : R) • E₆.tower R := by
  apply ext₂
  intro z
  rw [serre_apply]
  simp only [FunLike.coe_smul, Pi.smul_apply, Algebra.smul_def, map_neg, map_ofNat, tower_apply]
  change 12 * Derivative.serreDerivative 4 ModularForm.E₄ z =
    (-4 : ℂ) * ModularForm.E₆ z
  rw [Derivative.serreDerivative_E₄]
  norm_num [Pi.smul_apply, smul_eq_mul]
  ring

private theorem serre_E₆ :
    normalizedSerreDerivative R (E₆.tower R) =
      (-6 : R) • (E₄.tower R).mul (E₄.tower R) := by
  apply ext₂
  intro z
  rw [serre_apply]
  simp only [FunLike.coe_smul, Pi.smul_apply, Algebra.smul_def, map_neg, map_ofNat,
    mul_apply, tower_apply]
  change 12 * Derivative.serreDerivative 6 ModularForm.E₆ z =
    (-6 : ℂ) * (ModularForm.E₄ z * ModularForm.E₄ z)
  rw [Derivative.serreDerivative_E₆]
  norm_num [Pi.smul_apply, Pi.pow_apply, smul_eq_mul]
  ring

private def gradedSerre : GradedRing R →ₗ[R] GradedRing R :=
  DirectSum.toModule R ℤ (GradedRing R) fun k =>
    (DirectSum.lof R ℤ (ModularFormOver R 𝒮ℒ) (k + 2)).comp (serreLinearMap k)

@[simp] private theorem gradedSerre_of (f : ModularFormOver R 𝒮ℒ k) :
    gradedSerre (DirectSum.of (ModularFormOver R 𝒮ℒ) k f) =
      DirectSum.of (ModularFormOver R 𝒮ℒ) (k + 2) (normalizedSerreDerivative R f) := by
  change DirectSum.toModule R ℤ (GradedRing R) _
    (DirectSum.lof R ℤ (ModularFormOver R 𝒮ℒ) k f) = _
  rw [DirectSum.toModule_lof]
  rfl

omit [FaithfulSMul R ℂ] in
@[simp] private theorem of_cast {a b : ℤ} (h : a = b) (f : ModularFormOver R 𝒮ℒ a) :
    DirectSum.of (ModularFormOver R 𝒮ℒ) b (f.cast h) =
      DirectSum.of (ModularFormOver R 𝒮ℒ) a f := by
  subst b
  rfl

private theorem gradedSerre_mul (f g : GradedRing R) :
    gradedSerre (f * g) = gradedSerre f * g + f * gradedSerre g := by
  induction f using DirectSum.induction_on with
  | zero => simp
  | of k f =>
    induction g using DirectSum.induction_on with
    | zero => simp
    | of j g =>
      simp only [DirectSum.of_mul_of, gradedSerre_of]
      change DirectSum.of _ _ (normalizedSerreDerivative R (f.mul g)) = _
      rw [serre_mul, map_add]
      simp only [of_cast]
      rfl
    | add f g hf hg =>
      simp only [mul_add, map_add, hf, hg]
      abel
  | add f g hf hg =>
    simp only [add_mul, map_add, hf, hg]
    abel

private theorem gradedSerre_algebraMap (a : R) :
    gradedSerre (algebraMap R (GradedRing R) a) = 0 := by
  rw [DirectSum.algebraMap_apply]
  change gradedSerre (DirectSum.of (ModularFormOver R 𝒮ℒ) 0 (const a)) = 0
  have h : normalizedSerreDerivative R (const (Γ := 𝒮ℒ) a) = 0 := by
    apply fourier_inj R R
    rw [fourier_normalizedSerreDerivative]
    simp [normalizedSerreFourier]
  simp [h]

private theorem gradedSerre_eisensteinEval (p : MvPolynomial (Fin 2) R) :
    gradedSerre (eisensteinEval R p) = eisensteinEval R (MvPolynomial.Del p) := by
  induction p using MvPolynomial.induction_on with
  | C a => simp [gradedSerre_algebraMap]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p i hp =>
    rw [map_mul, gradedSerre_mul, hp, Derivation.leibniz]
    fin_cases i <;>
      simp [eisensteinEval_X_zero, eisensteinEval_X_one, serre_E₄, serre_E₆,
        DirectSum.of_smul, pow_two, DirectSum.of_mul_of, smul_eq_mul,
        GradedMonoid.GMul.mul] <;> ring

/-- Polynomial representation intertwines the normalized Serre derivative with `MvPolynomial.Del`.
The normalization is `12 θ - k E₂`, so the images of `E₄` and `E₆` are `-4 E₆` and `-6 E₄²`. -/
@[simp] theorem toPolynomial_normalizedSerreDerivative [Invertible (6 : R)]
    (f : ModularFormOver R 𝒮ℒ k) :
    (normalizedSerreDerivative R f).toPolynomial = MvPolynomial.Del f.toPolynomial := by
  apply eisensteinEval_injective R
  rw [eisensteinEval_toPolynomial, ← gradedSerre_eisensteinEval,
    eisensteinEval_toPolynomial, gradedSerre_of]

end ModularFormOver
