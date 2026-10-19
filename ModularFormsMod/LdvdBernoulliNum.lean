/-
Copyright (c) 2026 Carter Hastings. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carter Hastings
-/

import Mathlib.NumberTheory.Bernoulli

/-!
# Bernoulli coefficients at weight `p - 1`

Mathlib's von Staudt–Clausen valuation formula shows that the Eisenstein
coefficient factor at weight `p - 1` has positive p-adic valuation for `p ≥ 5`.
The factor is also p-integral at the two smaller primes.
-/

/-- The Eisenstein coefficient factor at weight `p - 1` has positive p-adic valuation
for primes at least five. -/
theorem padicVal_bernoulli_sub_one_pos (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p) :
    0 < padicValRat p (2 * (p - 1) / bernoulli (p - 1)) := by
  have hodd := (Fact.out : p.Prime).odd_of_ne_two (by omega)
  have htwo : 2 * ((p - 1) / 2) = p - 1 := by
    obtain ⟨k, hk⟩ := hodd
    omega
  have hv : padicValRat p (bernoulli (p - 1)) = -1 := by
    simpa only [htwo] using
      (Bernoulli.padicValRat_bernoulli (p := p) (k := (p - 1) / 2)
        (by omega) (by rw [htwo]))
  have hne : bernoulli (p - 1) ≠ 0 := by
    intro hz
    simp [hz] at hv
  have hpq : (1 : ℚ) < p := by exact_mod_cast (show 1 < p by omega)
  rw [padicValRat.div (mul_ne_zero (by norm_num) (ne_of_gt (sub_pos.mpr hpq))) hne, hv]
  have hn := zero_le_padicValRat_of_nat (p := p) (2 * (p - 1))
  push_cast [Nat.cast_sub (by omega : 1 ≤ p)] at hn
  omega

/-- For a prime `ℓ ≥ 5`, the numerator of `2 * (ℓ - 1) / bernoulli (ℓ - 1)` is zero modulo `ℓ`. -/
theorem ldvd_bernoulli_num (ℓ : ℕ) (hprime : ℓ.Prime) (hg5 : 5 ≤ ℓ) :
    (2 * ↑(ℓ - 1) / bernoulli (ℓ - 1)).num ≡ 0 [ZMOD ℓ] := by
  let : Fact ℓ.Prime := ⟨hprime⟩
  have hpos := padicVal_bernoulli_sub_one_pos ℓ hg5
  rw [← Nat.cast_one, ← Nat.cast_sub (by omega : 1 ≤ ℓ)] at hpos
  rw [Int.modEq_zero_iff_dvd]
  by_contra hd
  rw [padicValRat_def, padicValInt.eq_zero_of_not_dvd hd] at hpos
  omega

/-- The Eisenstein coefficient factor at weight `p - 1` has nonnegative p-adic valuation. -/
theorem padicVal_bernoulli_sub_one (p : ℕ) [Fact p.Prime] :
    padicValRat p (2 * (p - 1) / bernoulli (p - 1)) ≥ 0 := by
  by_cases hp : 5 ≤ p
  · exact (padicVal_bernoulli_sub_one_pos p hp).le
  · have hp2 : p = 2 ∨ p = 3 := by
      have := (Fact.out : p.Prime).two_le
      have := (Fact.out : p.Prime).eq_two_or_odd
      omega
    rcases hp2 with rfl | rfl <;> norm_num [bernoulli] <;>
      exact zero_le_padicValRat_of_nat _
