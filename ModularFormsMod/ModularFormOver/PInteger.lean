/-
Copyright (c) 2026 Carter Hastings. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carter Hastings
-/

module

public import ModularFormsMod.ModularFormOver.Int
public import ModularFormsMod.PInteger
public import ModularFormsMod.ModularForm
public import ModularFormsMod.LdvdBernoulliNum
public import ModularFormsMod.KummerCongruence

/-!
# Eisenstein series over the local integers

The Eisenstein series of weights `p - 1` and `p + 1` have coefficients in
`ℤ(p)`. Their Fourier coefficient formulas follow from valuation estimates
for the corresponding Bernoulli factors. This file also supplies scalar
extension from `ℤ[1/6]` and expresses `Δ` in terms of `E₄` and `E₆` when
`6` is invertible.
-/

@[expose] public section


open PInteger UpperHalfPlane ModularForm ModularFormOver
  MatrixGroups ArithmeticFunction.sigma

variable {F} [FunLike F ℍ ℂ] {Γ k}

/-- Extend forms over `ℤ[1/6]` to a compatible characteristic-zero ring in which `6` is
invertible. -/
instance ModularFormOverClass.towerℤAway6
  [hF : ModularFormOverClass F ℤ[1/6] Γ k]
    (R : Type) [CommRing R] [Algebra R ℂ]
      [CharZero R] [Invertible ((6 : ℤ) : R)] :
  ModularFormOverClass F R Γ k := hF.tower ℤ[1/6] R

@[coe]
noncomputable instance {Γ k} (R : Type) [CommRing R] [Algebra ℤ[1/6] R] [Algebra R ℂ]
  [IsScalarTower ℤ[1/6] R ℂ] : Coe (ModularFormOver ℤ[1/6] Γ k) (ModularFormOver R Γ k) :=
    ⟨ModularFormOver.tower R⟩


variable {F : Type*} [FunLike F ℍ ℂ] {f : F} {Γ : Subgroup (GL (Fin 2) ℝ)} {k : ℤ}

namespace ModularFormOver

/-- The Eisenstein series of weight `p - 1`, with Fourier coefficients in the local integers
`ℤ(p)`. -/
noncomputable def Esubone (p : ℕ) [Fact p.Prime] :
    ModularFormOver ℤ(p) 𝒮ℒ (p - 1) where
  toModularForm := Eis (p - 1)
  isOver' := by
    rw [isOver_iff]
    intro n
    rw [qExp_SL2Z, qExpansion_Eis]
    split_ifs with hk hk2 n0
    · exact one_mem _
    · refine mul_mem (neg_mem ?_) (by apply natCast_mem)
      use mk' (2 * (p - 1) / bernoulli (p - 1))
        (by exact padicVal_bernoulli_sub_one p) -- need the by exact
      simp [algebraMap_mk', ← Nat.cast_pred (n := p) (by lia)]
    · exact zero_mem _
    · exact zero_mem _

/-- The Eisenstein series of weight `p + 1`, with Fourier coefficients in the local integers
`ℤ(p)`. -/
noncomputable def Eaddone (p : ℕ) [Fact p.Prime] :
    ModularFormOver ℤ(p) 𝒮ℒ (p + 1) where
  toModularForm := Eis (p + 1)
  isOver' := by
    rw [isOver_iff]
    intro n
    rw [qExp_SL2Z, qExpansion_Eis]
    split_ifs with hk hk2 n0
    · exact one_mem _
    · refine mul_mem (neg_mem ?_) (by apply natCast_mem)
      use mk' (2 * (p + 1) / bernoulli (p + 1))
        (by exact padicVal_bernoulli_add_one p)
      simp [algebraMap_mk']
    · exact zero_mem _
    · exact zero_mem _


/-- For primes `p ≥ 5`, the complex coefficients of `Esubone p` have the usual Bernoulli and
divisor-sum formula. -/
theorem qExp_Esubone (p : ℕ) [Fact p.Prime] (hp : p ≥ 5) (n : ℕ) :
  (qExp (Esubone p)).coeff n = if n = 0 then 1 else
    -((2 : ℂ) * (p - 1) / (bernoulli (p - 1))) * σ (p - 2) n := by
  rw [show qExp (Esubone p) = qExpansion 1 (Eis (p - 1)) by
    rw [qExp_SL2Z]; rfl, qExpansion_Eis]
  rw [ite_eq_left (by lia), ite_eq_left]
  · congr! 5
    · simp
    · grind
    · grind
  · have hpp : p.Prime := Fact.out
    have hp2 : p ≠ 2 := by lia
    have hpo : Odd p :=  Nat.Prime.odd_of_ne_two hpp hp2
    grind

/-- For primes `p ≥ 3`, the complex coefficients of `Eaddone p` have the usual Bernoulli and
divisor-sum formula. -/
theorem qExp_Eaddone (p : ℕ) [Fact p.Prime] (hp : p ≥ 3) (n : ℕ) :
  (qExp (Eaddone p)).coeff n = if n = 0 then 1 else
    -((2 : ℂ) * (p + 1) / (bernoulli (p + 1))) * σ p n := by
  rw [show qExp (Eaddone p) = qExpansion 1 (Eis (p + 1)) by
    rw [qExp_SL2Z]; rfl, qExpansion_Eis]
  rw [ite_eq_left (by lia), ite_eq_left]
  · congr! 5
    norm_cast
  · have hpp : p.Prime := Fact.out
    have hp2 : p ≠ 2 := by lia
    have hpo : Odd p :=  Nat.Prime.odd_of_ne_two hpp hp2
    grind


/-- The Fourier coefficient formula for `Esubone p` in `ℤ(p)`, using the p-integral Bernoulli
factor. -/
theorem coeff_Esubone (p : ℕ) [Fact p.Prime] (hp : p ≥ 5) (n : ℕ) :
  coeff ℤ(p) n (Esubone p) = if n = 0 then 1 else
    -mk' (2 * (p - 1) / bernoulli (p - 1)) (padicVal_bernoulli_sub_one p)
      * σ (p - 2) n := by
  rw [coeff_eq_iff, qExp_Esubone p hp]
  split_ifs
  · exact map_one _ |>.symm
  · simp

/-- The Fourier coefficient formula for `Eaddone p` in `ℤ(p)`, using the p-integral Bernoulli
factor. -/
theorem coeff_Eaddone (p : ℕ) [Fact p.Prime] (hp : p ≥ 3) (n : ℕ) :
  coeff ℤ(p) n (Eaddone p) = if n = 0 then 1 else
    -mk' (2 * (p + 1) / bernoulli (p + 1)) (padicVal_bernoulli_add_one p)
      * σ p n := by
  rw [coeff_eq_iff, qExp_Eaddone p hp]
  split_ifs
  · exact map_one _ |>.symm
  · simp


/-- The coefficients of `Esubone p` after extension to a compatible characteristic-zero field. -/
theorem coeff_cast_Esubone (R : Type) [Field R] [CharZero R] [Algebra R ℂ]
  (p : ℕ) [Fact p.Prime] (hp : p ≥ 5) (n : ℕ) :
    coeff ℤ(p) n (Esubone p) R  = if n = 0 then (1 : R) else
      -(2 * (p - 1) / bernoulli (p - 1)) * σ (p - 2) n := by
  rw [coeff_ring_cast ℤ(p) R ℤ(p), coeff_Esubone p hp]
  split_ifs
  · exact map_one _
  · simp

/-- The coefficients of `Eaddone p` after extension to a compatible characteristic-zero field. -/
theorem coeff_cast_Eaddone (R : Type) [Field R] [CharZero R] [Algebra R ℂ]
  (p : ℕ) [Fact p.Prime] (hp : p ≥ 3) (n : ℕ) :
    coeff ℤ(p) n (Eaddone p) R  = if n = 0 then (1 : R) else
      -(2 * (p + 1) / bernoulli (p + 1)) * σ p n := by
  rw [coeff_ring_cast ℤ(p) R ℤ(p), coeff_Eaddone p hp]
  split_ifs
  · exact map_one _
  · simp


/-- When `6` is invertible, `Δ` is `(E₄³ - E₆²) / 1728` over the coefficient ring. -/
theorem discriminant_eq_E₄E₆ {R} [CommRing R] [Algebra R ℂ] [Invertible (6 : R)] :
    (Δ).tower R = ⅟ (1728 : R) •
      (((E₄.tower R).pow 3).cast (by rfl) -
        ((E₆.tower R).pow 2).cast (by rfl)) := by
  apply (smul_eq_iff_eq_invOf_smul (c := (1728 : R))).mp
  apply ext₂
  intro z
  have tower_apply {j : ℤ} (f : ModularFormOver ℤ 𝒮ℒ j) :
      (f.tower R) z = f z := rfl
  have h := congrArg (fun f : ModularFormOver ℤ 𝒮ℒ 12 => f z)
    smul_discriminant_eq_E₄E₆
  simpa only [smul_apply, sub_apply, cast_apply, pow_apply E₄, pow_apply E₆,
    pow_apply (E₄.tower R), pow_apply (E₆.tower R),
    tower_apply Δ, tower_apply E₄, tower_apply E₆,
    Algebra.smul_def, map_ofNat, nsmul_eq_mul, Nat.cast_ofNat] using h

end ModularFormOver
