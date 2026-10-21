/-
Copyright (c) 2026 Carter Hastings. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carter Hastings
-/

module

public import ModularFormsMod.ModularFormOver.PInteger
public import ModularFormsMod.ModularFormOver.Derivative
public import ModularFormsMod.ModularFormMod.Basic
public import Mathlib.RingTheory.PowerSeries.Expand
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.Tactic.NormNum.Prime

/-!
# Scalar multiplication on modular forms reduced modulo an integer

Every ring homomorphism to `ZMod n` is surjective, so reduced modular forms
inherit a module structure over `ZMod n`. The Eisenstein series of weights
`p - 1` and `p + 1` reduce to `1` and the formal `E₂` series, respectively.
-/

@[expose] public section

open ModularFormOver ModularFormMod PInteger MatrixGroups

namespace ModularFormMod

/-- Every coefficient reduction into `ZMod n` is surjective. -/
instance instRingHomSurjectiveZMod {R : Type} [CommRing R] {n : ℕ}
    (r : R →+* ZMod n) : RingHomSurjective r :=
  ⟨ZMod.ringHom_surjective r⟩


set_option quotPrecheck false in
scoped[ModularFormMod.ZMod] notation "𝓜" prime:max weight:max =>
  (let _ : Fact (Nat.Prime prime) := by
     all_goals first | infer_instance | exact ⟨by norm_num⟩
   ModularFormMod (PInteger.reduce (p := prime))
     (Matrix.SpecialLinearGroup.mapGL (n := Fin 2) (R := ℤ) ℝ).range weight)

private theorem reduce_mk'_eq_ratCast {p : ℕ} [Fact p.Prime]
    (q : ℚ) (hq : padicValRat p q ≥ 0) :
    reduce (mk' q hq) = (q : ZMod p) := by
  rw [mk', PInteger.mk, reduce, IsLocalization.lift_mk']
  rw [Units.val_inv_eq_inv_val]
  change (q.num : ZMod p) * ((q.den : ℤ) : ZMod p)⁻¹ = _
  simp only [Int.cast_natCast, Rat.cast_def, div_eq_mul_inv]

/-- The weight `p - 1` Eisenstein series reduces to the constant series `1` for `p ≥ 5`. -/
theorem Reduce_Esubone (p : ℕ) [isLargePrime p] :
    ((Esubone p).Reduce reduce).fourier = 1 := by
  have hp : 5 ≤ p := isLargePrime.AtLeastFive
  have hnum : (p : ℤ) ∣ (2 * (p - 1) / bernoulli (p - 1) : ℚ).num := by
    have h := Int.modEq_zero_iff_dvd.mp (ldvd_bernoulli_num p Fact.out hp)
    simpa only [Nat.cast_sub (by omega : 1 ≤ p), Nat.cast_one] using h
  have hfactor : reduce (mk' (2 * (p - 1) / bernoulli (p - 1))
      (padicVal_bernoulli_sub_one p)) = 0 := by
    rw [reduce_mk'_eq_ratCast, Rat.cast_def,
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hnum, zero_div]
  ext n
  change reduce (ModularFormOver.coeff ℤ(p) n (Esubone p)) = _
  rw [coeff_Esubone p hp]
  split_ifs with hn
  · subst n
    simp
  · simp [hn, hfactor]

private theorem reduce_factor_addone (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p) :
    reduce (mk' (2 * (p + 1) / bernoulli (p + 1))
      (padicVal_bernoulli_add_one p)) = 24 := by
  have hprime : p.Prime := Fact.out
  have hmod : p + 1 ≡ 2 [MOD p - 1] := by
    exact Nat.ModEq.symm (Nat.modEq_iff_dvd.mpr ⟨1, by omega⟩)
  have hndvd : ¬ p - 1 ∣ p + 1 := by
    intro h
    have htwo : p - 1 ∣ 2 := by
      simpa [show p + 1 - (p - 1) = 2 by omega] using Nat.dvd_sub h (dvd_refl (p - 1))
    have := Nat.le_of_dvd (by decide : 0 < 2) htwo
    omega
  have hcongr := Bernoulli.kummer_congr hmod hndvd (by omega) (by decide)
  have h6 : (6 : ZMod p) ≠ 0 := by
    intro h
    have hdiv := (ZMod.natCast_eq_zero_iff 6 p).mp h
    rcases hprime.dvd_mul.mp (show p ∣ 2 * 3 from hdiv) with h2 | h3
    · have := Nat.le_of_dvd (by decide : 0 < 2) h2; omega
    · have := Nat.le_of_dvd (by decide : 0 < 3) h3; omega
  have hB2 : (bernoulli 2 : ZMod p) = (6 : ZMod p)⁻¹ := by
    rw [bernoulli_two, Rat.cast_inv_of_ne_zero (by simpa using h6)]
    norm_cast
  simp only [hB2, Nat.cast_add, Nat.cast_one, ZMod.natCast_self, zero_add, one_mul] at hcongr
  have hB : (bernoulli (p + 1) : ZMod p) ≠ 0 := by
    intro h
    rw [h, mul_zero] at hcongr
    exact (inv_ne_zero h6) hcongr.symm
  have hnum : ((bernoulli (p + 1)).num : ZMod p) ≠ 0 := by
    intro h
    exact hB (by rw [Rat.cast_def, h, zero_div])
  rw [reduce_mk'_eq_ratCast]
  have hnat : (2 * (p + 1) : ℚ) = ((2 * (p + 1) : ℕ) : ℚ) := by push_cast; ring
  have hden : (((2 * (p + 1) : ℚ).den : ℕ) : ZMod p) ≠ 0 := by
    rw [hnat, Rat.den_natCast]
    simp
  rw [Rat.cast_div_of_ne_zero hden hnum, hnat, Rat.cast_natCast]
  push_cast
  simp only [ZMod.natCast_self, zero_add, mul_one]
  apply (div_eq_iff hB).mpr
  have h := congrArg (fun x : ZMod p => x * 6) hcongr
  rw [inv_mul_cancel₀ h6] at h
  linear_combination -2 * h

/-- For odd primes, the weight `p + 1` Eisenstein series reduces to the formal `E₂` series. -/
theorem Reduce_Eaddone (p : ℕ) [Fact p.Prime] (hp : 3 ≤ p) :
    ((Eaddone p).Reduce reduce).fourier = e2Fourier (ZMod p) := by
  have hfactor : reduce (mk' (2 * (p + 1) / bernoulli (p + 1))
      (padicVal_bernoulli_add_one p)) = 24 := by
    by_cases hp5 : 5 ≤ p
    · exact reduce_factor_addone p hp5
    · have : p = 3 := by
        have := (Fact.out : p.Prime).eq_two_or_odd
        omega
      subst p
      rw [reduce_mk'_eq_ratCast]
      norm_num [bernoulli, Rat.cast_def]
      decide +revert
  ext n
  change reduce (ModularFormOver.coeff ℤ(p) n (Eaddone p)) = _
  rw [coeff_Eaddone p hp]
  simp only [e2Fourier, PowerSeries.coeff_mk]
  split_ifs with hn
  · simp
  · simp only [map_mul, map_neg, hfactor, map_natCast]
    congr 1
    simp only [ArithmeticFunction.sigma_apply, Nat.cast_sum, Nat.cast_pow]
    apply Finset.sum_congr rfl
    intro d hd
    simp [ZMod.pow_card]

end ModularFormMod

/-
This section proves `coeff_pow_card (n) : (f.pow ℓ).coeff n = if ℓ ∣ n then f.coeff (n / ℓ) else 0`
-/

open PowerSeries ModularFormMod.ZMod

theorem FiniteField.PowerSeries_expand_card {K : Type*} [Fintype K] [Field K] (f : K⟦X⟧) :
    expand (Fintype.card K) NeZero.out f = f ^ (Fintype.card K) := by
  obtain ⟨p, hp⟩ := CharP.exists K
  rcases FiniteField.card K p with ⟨⟨n, npos⟩, ⟨hp, hn⟩⟩
  have : Fact p.Prime := ⟨hp⟩
  dsimp at hn
  simp_rw [hn, ← MvPowerSeries.map_iterateFrobenius_expand p NeZero.out, iterateFrobenius_eq_pow,
    FiniteField.frobenius_pow hn, RingHom.one_def, MvPowerSeries.map_id]
  rfl


namespace PowerSeries.ZMod

variable (p : ℕ) [Fact (Nat.Prime p)]

instance : CharP ((ZMod p) ⟦X⟧) p :=
  (CharP.charP_iff_prime_eq_zero Fact.out).mpr <|
    show C _ = 0 by rw [CharP.cast_eq_zero, map_zero]

theorem expand_card (f : PowerSeries (ZMod p)) :
    f.expand p NeZero.out = f ^ p := by
  simpa only [ZMod.card p] using FiniteField.PowerSeries_expand_card f


theorem coeff_pow_card (f : PowerSeries (ZMod p)) (n) :
    (f ^ p).coeff n = if p ∣ n then f.coeff (n / p) else 0 := by
  rw [← expand_card, coeff_expand]


end PowerSeries.ZMod

namespace ModularFormMod


theorem coeff_pow_card {p : ℕ} [Fact p.Prime] {k : ℤ}
  (f : 𝓜 p k) (n) : (f.pow p).coeff n =
    if p ∣ n then f.coeff (n / p) else 0 := by
  simp only [coeff, pow_fourier, ZMod.coeff_pow_card]


end ModularFormMod
