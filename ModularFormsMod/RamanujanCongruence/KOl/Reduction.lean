/-
Copyright (c) 2026 Carter Hastings. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carter Hastings
-/

import ModularFormsMod.RamanujanCongruence.Basic

/-!
# From a partition congruence to a simple congruence of `fl p`

The standard-partition specialization of the reduction in Section 4 of
Kiming--Olsson. Multiplication by a `p`-th power preserves a simple congruence,
and the Euler product shifts its residue from `-β` to `δ p - β`.
-/

noncomputable section

open ModularFormMod ModularFormMod.ZMod

namespace RamanujanCongruence.KOl

variable {p : ℕ} [isLargePrime p]

/-- A power series has a simple congruence at `a` if its coefficients in that
residue class vanish. -/
def SimpleCongruence (f : PowerSeries (ZMod p)) (a : ZMod p) : Prop :=
  ∀ n : ℕ, (n : ZMod p) = a → f.coeff n = 0

theorem SimpleCongruence.pow_mul {bSeries : PowerSeries (ZMod p)} {a : ZMod p}
    (hB : SimpleCongruence bSeries a) (aSeries : PowerSeries (ZMod p)) :
    SimpleCongruence (aSeries ^ p * bSeries) a := by
  intro n hn
  rw [PowerSeries.coeff_mul]
  apply Finset.sum_eq_zero
  intro ij hij
  by_cases hi : p ∣ ij.1
  · have hi0 : (ij.1 : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr hi
    have hj : (ij.2 : ZMod p) = a := by
      have hsum := congrArg (fun m : ℕ => (m : ZMod p))
        (Finset.mem_antidiagonal.mp hij)
      simpa only [Nat.cast_add, hi0, zero_add, hn] using hsum
    rw [hB _ hj, mul_zero]
  · rw [PowerSeries.ZMod.coeff_pow_card, ite_eq_right hi, zero_mul]

/-- Section 4's Euler-product reduction, for the partition function of `Partition.lean`. -/
theorem simpleCongruence_fl {β : ℤ} (hβ : RamanujanCongruenceWith p β) :
    SimpleCongruence (fl p).fourier ((δ p : ZMod p) - (β : ZMod p)) := by
  obtain ⟨E, hE0, hfactor⟩ := fl_euler_factor p
  let P : PowerSeries (ZMod p) := PowerSeries.mk fun n => (partition n : ZMod p)
  let H := PowerSeries.X ^ δ p * P
  have hH : SimpleCongruence H ((δ p : ZMod p) - (β : ZMod p)) := by
    intro n hn
    rw [show H = PowerSeries.X ^ δ p *
      PowerSeries.mk (fun n : ℕ => (partition n : ZMod p)) from rfl,
      coeff_shift_partition]
    have hd : (p : ℤ) ∣ (n : ℤ) - δ p + β := by
      apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp
      push_cast
      rw [hn]
      ring
    obtain ⟨t, ht⟩ := hd
    have heq : (p : ℤ) * t - β = (n : ℤ) - δ p := by linear_combination -ht
    have hz := (ZMod.natCast_eq_zero_iff _ p).mpr
      (Nat.modEq_zero_iff_dvd.mp (hβ t))
    simpa only [heq] using hz
  rw [hfactor]
  exact hH.pow_mul _

/-- The integer parameter of a Ramanujan congruence depends only on its residue. -/
theorem congruenceWith_of_cast_eq {β γ : ℤ}
    (h : (β : ZMod p) = (γ : ZMod p)) (hβ : RamanujanCongruenceWith p β) :
    RamanujanCongruenceWith p γ := by
  have hd : (p : ℤ) ∣ γ - β := by
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp
    simp only [Int.cast_sub, h, sub_self]
  obtain ⟨t, ht⟩ := hd
  intro n
  have heq : (p : ℤ) * (n - t) - β = (p : ℤ) * n - γ := by
    linear_combination ht
  simpa only [heq] using hβ (n - t)

end RamanujanCongruence.KOl
