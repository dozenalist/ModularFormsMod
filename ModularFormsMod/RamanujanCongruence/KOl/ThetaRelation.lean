/-
Copyright (c) 2026 Carter Hastings. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carter Hastings
-/

import ModularFormsMod.RamanujanCongruence.KOl.WeightDecomposition
import ModularFormsMod.RamanujanCongruence.KOl.Reduction
import Mathlib.Algebra.Ring.GeomSum

/-!
# The theta relation forced by a nonzero simple congruence

The specialization of Kiming--Olsson, Proposition 3, needed here: the terms of
weights `k + (p + 1)` and `k + ((p + 1) / 2) * (p + 1)` cancel each other.
-/

noncomputable section

open ModularFormMod ModularFormMod.ZMod Finset

namespace RamanujanCongruence.KOl

variable {p : ℕ} [isLargePrime p] {k : ℤ}

private theorem simpleCongruence_theta_sum (f : 𝓜 p k) {a : ZMod p}
    (ha : a ≠ 0) (hf : SimpleCongruence f.fourier a) :
    ∑ i ∈ range (p - 1),
      (a ^ (p - 1 - (i + 1)) • f.Theta_pow (i + 1)).fourier = 0 := by
  have hp : 1 ≤ p := by have := isLargePrime.AtLeastFive (ℓ := p); omega
  ext n
  simp only [map_sum, coeff_fourier, coeff_smul_of_surjective, coeff_Theta_pow,
    _root_.map_zero]
  by_cases hn : (n : ZMod p) = a
  · simp [show coeff n f = 0 from hf n hn]
  have hgeom : ∑ i ∈ range p, (n : ZMod p) ^ i * a ^ (p - 1 - i) = 1 := by
    have h := geom_sum₂_mul (n : ZMod p) a p
    rw [ZMod.pow_card, ZMod.pow_card] at h
    exact (mul_eq_right₀ (sub_ne_zero.mpr hn)).mp h
  have hgeom' := hgeom
  conv at hgeom' => lhs; arg 1; rw [show p = (p - 1) + 1 by omega]
  rw [sum_range_succ'] at hgeom'
  have hsum : ∑ i ∈ range (p - 1),
      a ^ (p - 1 - (i + 1)) * (n : ZMod p) ^ (i + 1) = 0 := by
    have ha1 := ZMod.pow_card_sub_one_eq_one ha
    have hgeom'' : (∑ i ∈ range (p - 1),
        a ^ (p - 1 - (i + 1)) * (n : ZMod p) ^ (i + 1)) + 1 = 1 := by
      simpa only [pow_zero, one_mul, Nat.sub_zero, ha1, mul_comm] using hgeom'
    exact add_right_cancel (hgeom''.trans (zero_add 1).symm)
  simp only [← mul_assoc, ← sum_mul, hsum, zero_mul]

private theorem theta_weight_class (i : ℕ) (hi : i < p - 1) :
    ((k + (i + 1) * (p + 1) : ℤ) : ZMod (p - 1)) =
        ((k + (p + 1) : ℤ) : ZMod (p - 1)) ↔
      i = 0 ∨ i = (p - 1) / 2 := by
  have hp : 5 ≤ p := isLargePrime.AtLeastFive
  have hh : 2 * ((p - 1) / 2) = p - 1 := by
    have := prime_half (p := p)
    omega
  rw [← sub_eq_zero, ← Int.cast_sub, ZMod.intCast_zmod_eq_zero_iff_dvd]
  have heq : (k + (i + 1) * (p + 1) : ℤ) - (k + (p + 1)) =
      (p - 1 : ℤ) * i + 2 * i := by ring
  rw [heq, Nat.cast_sub (by omega : 1 ≤ p), Nat.cast_one,
    dvd_add_right (dvd_mul_right _ _)]
  constructor
  · rintro ⟨t, ht⟩
    have hi0 : 0 ≤ (i : ℤ) := Int.natCast_nonneg i
    have hile : (i : ℤ) < (p : ℤ) - 1 := by omega
    have ht0 : 0 ≤ t := by nlinarith
    have ht2 : t < 2 := by nlinarith
    have : t = 0 ∨ t = 1 := by omega
    rcases this with rfl | rfl <;> omega
  · rintro (rfl | rfl)
    · simp
    · refine ⟨1, ?_⟩
      omega

/-- The two theta iterates in the first weight class have equal filtration. -/
theorem filtration_theta_half (f : 𝓜 p k) {a : ZMod p}
    (ha : a ≠ 0) (hf : SimpleCongruence f.fourier a) :
    f.Theta.Filtration = (f.Theta_pow ((p + 1) / 2)).Filtration := by
  have hp : 5 ≤ p := isLargePrime.AtLeastFive
  have hh : 2 * ((p - 1) / 2) = p - 1 := by
    have := prime_half (p := p)
    omega
  let h := (p - 1) / 2
  have hrel := sum_fourier_eq_zero_by_weight (range (p - 1))
    (fun i => k + (i + 1) * (p + 1))
    (fun i => a ^ (p - 1 - (i + 1)) • f.Theta_pow (i + 1))
    (simpleCongruence_theta_sum f ha hf) ((k + (p + 1) : ℤ) : ZMod (p - 1))
  have hfilter : (range (p - 1)).filter
      (fun i : ℕ => ((k + (i + 1) * (p + 1) : ℤ) : ZMod (p - 1)) =
        ((k + (p + 1) : ℤ) : ZMod (p - 1))) = {0, h} := by
    ext i
    simp only [mem_filter, mem_range, mem_insert, mem_singleton]
    constructor
    · rintro ⟨hi, heq⟩
      exact (theta_weight_class i hi).mp heq
    · intro hi
      have hil : i < p - 1 := by
        rcases hi with rfl | rfl
        · omega
        · change (p - 1) / 2 < p - 1
          omega
      exact ⟨hil, (theta_weight_class i hil).mpr hi⟩
  rw [hfilter, sum_pair (show (0 : ℕ) ≠ h by dsimp [h]; omega)] at hrel
  have heq : (a ^ (p - 2) • f.Theta).fourier =
      (-a ^ (p - 1 - (h + 1)) • f.Theta_pow (h + 1)).fourier := by
    simpa only [zero_add, show p - 1 - 1 = p - 2 by omega,
      show f.Theta_pow 1 = f.Theta.cast (by ring) from rfl,
      smul_fourier_of_surjective, cast_fourier, neg_smul, neg_fourier] using
        (eq_neg_iff_add_eq_zero.mpr hrel)
  have hw := Filtration_eq_of_fourier_eq heq
  rw [Filtration_smul_eq (isUnit_iff_ne_zero.mpr (pow_ne_zero _ ha)),
    Filtration_smul_eq (isUnit_iff_ne_zero.mpr (neg_ne_zero.mpr (pow_ne_zero _ ha)))] at hw
  have hindex : h + 1 = (p + 1) / 2 := by dsimp [h]; omega
  rw [hindex] at hw
  exact hw

end RamanujanCongruence.KOl
