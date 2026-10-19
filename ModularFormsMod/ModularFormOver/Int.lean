/-
Copyright (c) 2026 Carter Hastings. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carter Hastings
-/

import ModularFormsMod.ModularFormOver.Basic
import Mathlib.NumberTheory.ModularForms.EisensteinSeries.QExpansion
import Mathlib.NumberTheory.ModularForms.EisensteinSeries.E2.Summable
import Mathlib.NumberTheory.ModularForms.EisensteinSeries.E2.MDifferentiable
import Mathlib.NumberTheory.ModularForms.EisensteinSeries.E2.Transform
import Mathlib.NumberTheory.ModularForms.NormTrace
import Mathlib.NumberTheory.ModularForms.LevelOne.GradedRing
import ModularFormsMod.qExp_discriminant


/-!
# Integral Eisenstein series and the discriminant

The normalized forms `E₄`, `E₆`, and `Δ` have integer Fourier coefficients.
This file bundles them as forms over `ℤ`, gives their coefficient formulas
after scalar extension, defines the formal series for `E₂`, and proves
the identity `1728 • Δ = E₄³ - E₆²` over the integers.
-/

open ModularForm hiding E₄ E₆
open ModularFormOver UpperHalfPlane CongruenceSubgroup MatrixGroups ArithmeticFunction.sigma


variable {F : Type*} [FunLike F ℍ ℂ] {f : F} {Γ : Subgroup (GL (Fin 2) ℝ)} {k : ℤ}

@[coe]
instance ModularFormOverClass.towerℤ [hF : ModularFormOverClass F ℤ Γ k]
    (R : Type) [CommRing R] [Algebra R ℂ] : ModularFormOverClass F R Γ k :=
  hF.tower ℤ R

@[coe] instance (R : Type) [CommRing R] [Algebra R ℂ] :
    Coe (ModularFormOver ℤ Γ k) (ModularFormOver R Γ k) :=
  ⟨ModularFormOver.tower R⟩


namespace ModularFormOver


section LevelOne


theorem qExp_SL2Z {F : Type*} [FunLike F ℍ ℂ] [ModularFormClass F 𝒮ℒ k]
    (f : F) : qExp f = qExpansion 1 f := by
  rw [qExp, Subgroup.strictWidthInfty_SL2Z]

section bernoulli

private lemma bernoulli_four : bernoulli 4 = -(1 / 30) := by
  decide +kernel

private lemma bernoulli_six : bernoulli 6 = 1 / 42 := by
  decide +kernel

end bernoulli


/-- The normalized weight-four Eisenstein series, bundled with its integral Fourier coefficients. -/
noncomputable def E₄ : ModularFormOver ℤ 𝒮ℒ 4 where
  toModularForm := ModularForm.E₄
  isOver' := by
    rw [isOver_iff, qExp_SL2Z, ModularForm.E₄]
    intro n
    rw [EisensteinSeries.E_qExpansion_coeff (by decide) (by decide)]
    rw [bernoulli_four]
    use if n = 0 then 1 else 240 * σ 3 n
    norm_num

/-- The normalized weight-six Eisenstein series, bundled with its integral Fourier coefficients. -/
noncomputable def E₆ : ModularFormOver ℤ 𝒮ℒ 6 where
  toModularForm := ModularForm.E₆
  isOver' := by
    rw [isOver_iff, qExp_SL2Z, ModularForm.E₆]
    intro n
    rw [EisensteinSeries.E_qExpansion_coeff (by decide) (by decide)]
    rw [bernoulli_six]
    use if n = 0 then 1 else -504 * σ 5 n
    norm_num

/-- The weight-twelve discriminant cusp form, regarded as a modular form over `ℤ`. -/
noncomputable def discriminant : ModularFormOver ℤ 𝒮ℒ 12 where
  toModularForm := CuspForm.discriminant
  isOver' := by
    rw [isOver, qExp_SL2Z, qExpansion_discriminant]
    exact RingHom.mem_range_self _ _

scoped notation "Δ" => discriminant


/-- The complex Fourier coefficients of `E₄` are one in degree zero and `240 * σ 3 n` in positive
degrees. -/
theorem E₄_qExp_coeff (n : ℕ) : (qExp E₄).coeff n =
    if n = 0 then (1 : ℂ) else 240 * σ 3 n := by
  simp only [qExp_SL2Z, ← toModularForm_coe, E₄, ModularForm.E₄]
  rw [EisensteinSeries.E_qExpansion_coeff (by decide) (by decide), bernoulli_four]
  norm_num

/-- The complex Fourier coefficients of `E₆` are one in degree zero and `-504 * σ 5 n` in
positive degrees. -/
theorem E₆_qExp_coeff (n : ℕ) : (qExp E₆).coeff n =
    if n = 0 then (1 : ℂ) else -504 * σ 5 n := by
  simp only [qExp_SL2Z, ← toModularForm_coe, E₆, ModularForm.E₆]
  rw [EisensteinSeries.E_qExpansion_coeff (by decide) (by decide), bernoulli_six]
  norm_num

/-- The complex Fourier coefficients of `Δ` are the stabilized coefficients of the finite
discriminant products. -/
theorem discriminant_qExp_coeff (n : ℕ) :
    (qExp discriminant).coeff n = (discProduct n).coeff n := by
  simp only [qExp_SL2Z, ← toModularForm_coe, discriminant, qExpansion_discriminant,
    PowerSeries.coeff_map, PowerSeries.coeff_mk, map_coeff_discProduct]

variable {R S} [CommRing R] [Algebra R ℂ] [CommRing S]
  [Algebra S ℂ] [FaithfulSMul S ℂ] [Algebra R S] [IsScalarTower R S ℂ]

/-- The divisor-sum formula for the Fourier coefficients of `E₄` in a compatible coefficient
ring. -/
theorem coeff_E₄ (n : ℕ) : coeff R n E₄ S = if n = 0 then (1 : S)
    else 240 * σ 3 n := by
  rw [coeff_eq_iff, E₄_qExp_coeff]
  split_ifs with h
  · exact algebraMap.coe_one.symm
  · rw [map_mul, map_natCast, ← Nat.cast_ofNat (R := S),
      map_natCast, Nat.cast_ofNat]


/-- The divisor-sum formula for the Fourier coefficients of `E₆` in a compatible coefficient
ring. -/
theorem coeff_E₆ (n : ℕ) : coeff R n E₆ S =
    if n = 0 then (1 : S) else -504 * σ 5 n := by
  rw [coeff_eq_iff, E₆_qExp_coeff]
  split_ifs with h
  · exact algebraMap.coe_one.symm
  · rw [map_mul, map_natCast, ← Nat.cast_ofNat (R := S),
      map_neg, map_natCast, Nat.cast_ofNat]

@[simp] theorem coeff_zero_E₄ : coeff R 0 E₄ S = 1 := by
  simp only [coeff_E₄, reduceIte]

@[simp] theorem coeff_one_E₄ : coeff R 1 E₄ S = 240 := by
  simp [coeff_E₄]

@[simp] theorem coeff_zero_E₆ : coeff R 0 E₆ S = 1 := by
  simp only [coeff_E₆, reduceIte]

@[simp] theorem coeff_one_E₆ : coeff R 1 E₆ S = -504 := by
  simp [coeff_E₆]

/-- The Fourier coefficient of `Δ` in degree `n` is the degree-`n` coefficient of `discProduct
n`. -/
theorem coeff_discriminant (n : ℕ) : coeff R n Δ S = (discProduct n).coeff n := by
  rw [coeff_eq_iff, discriminant_qExp_coeff, map_coeff_discProduct]

@[simp] theorem coeff_zero_discriminant : coeff R 0 Δ S = 0 := by
  simp [coeff_discriminant, discProduct]

@[simp] theorem coeff_one_discriminant : coeff R 1 Δ S = 1 := by
  simp [coeff_discriminant, discProduct]

@[simp] theorem coeff_two_discriminant : coeff R 2 Δ S = -24 := by
  simp only [coeff_discriminant, discProduct, Finset.prod_range, Fin.prod_univ_two, Fin.isValue,
    Fin.coe_ofNat_eq_mod, Nat.zero_mod, zero_add, pow_one, Nat.mod_succ, Nat.reduceAdd,
    PowerSeries.coeff_succ_X_mul]
  ring_nf
  simpa only [map_add, map_sub, PowerSeries.coeff_one, one_ne_zero, ↓reduceIte,
    PowerSeries.coeff_one_mul, PowerSeries.coeff_one_X, one_mul,
    PowerSeries.constantCoeff_X, MulZeroClass.mul_zero, add_zero, zero_sub,
    PowerSeries.coeff_X_pow_mul', Nat.not_ofNat_le_one, sub_zero,
    PowerSeries.coeff_X_pow, OfNat.one_ne_ofNat,Int.reduceNeg, neg_inj, Nat.cast_ofNat]
      using (map_natCast _ _ : PowerSeries.constantCoeff 24 = (24 : S))


/-- The formal Eisenstein series `E₂ = 1 - 24 ∑ n ≥ 1, σ₁(n) X^n` over a coefficient ring. -/
noncomputable def E2fourier (R : Type := ℤ) [CommRing R] [Algebra R ℂ] : PowerSeries R :=
  .mk fun n => if n = 0 then 1 else -24 * σ 1 n

/-- The coefficient formula defining the formal weight-two Eisenstein series. -/
@[simp] theorem coeff_E2fourier (R : Type) [CommRing R] [Algebra R ℂ] (n : ℕ) :
    (E2fourier R).coeff n = if n = 0 then 1 else (-24 : R) * σ 1 n := by
  rw [E2fourier, PowerSeries.coeff_mk]


/-- The integral relation `1728 • Δ = E₄³ - E₆²`, with the powers transported to weight twelve. -/
theorem smul_discriminant_eq_E₄E₆ :
    1728 • Δ = (E₄.pow 3).cast (by rfl) - (E₆.pow 2).cast (by rfl) :=
  ext₂ fun z => by
    simp only [smul_apply, show Δ z = ModularForm.discriminant z by rfl,
      discriminant_eq_E₄_cube_sub_E₆_sq, nsmul_eq_mul, Nat.cast_ofNat,
        Int.reduceMul, sub_apply, cast_apply, pow_apply E₄, pow_apply E₆]
    field_simp
    rfl


end LevelOne
end ModularFormOver
open ModularFormOver
