/-
Copyright (c) 2026 Carter Hastings. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carter Hastings
-/

module

public import ModularFormsMod.RamanujanCongruence.Basic

/-!
# The partition congruence and the U operator

The Euler product writes `fl p` as a `p`-th power times the shifted partition
series. Extracting coefficients at multiples of `p` moves that power outside
the extraction operator; its constant coefficient is one, so it can be cancelled.
-/

@[expose] public section

noncomputable section

open ModularFormMod.ZMod ModularFormMod Finset
open scoped PowerSeries.WithPiTopology

private def uSeries {R : Type*} [Semiring R] (p : ℕ) (f : PowerSeries R) : PowerSeries R :=
  PowerSeries.mk fun n => f.coeff (p * n)

private theorem uSeries_expand_mul {R : Type*} [CommRing R] {p : ℕ} (hp : p ≠ 0)
    (aSeries bSeries : PowerSeries R) :
    uSeries p (PowerSeries.expand p hp aSeries * bSeries) = aSeries * uSeries p bSeries := by
  classical
  ext n
  simp only [uSeries, PowerSeries.coeff_mk, PowerSeries.coeff_mul]
  symm
  apply Finset.sum_of_injOn (fun ij : ℕ × ℕ => (p * ij.1, p * ij.2))
  · intro a ha b hb hab
    exact Prod.ext
      (Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hp) (congrArg Prod.fst hab))
      (Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hp) (congrArg Prod.snd hab))
  · intro ij hij
    change ij ∈ antidiagonal n at hij
    change (p * ij.1, p * ij.2) ∈ antidiagonal (p * n)
    rw [Finset.mem_antidiagonal] at hij ⊢
    simpa only [← Nat.mul_add] using congrArg (p * ·) hij
  · intro ij hij hnot
    have hndvd : ¬p ∣ ij.1 := by
      intro ha
      have hsum : p ∣ ij.1 + ij.2 := by
        rw [Finset.mem_antidiagonal.mp hij]
        exact dvd_mul_right p n
      have hb : p ∣ ij.2 := by
        exact (Nat.dvd_add_iff_right ha).mpr hsum
      obtain ⟨a, ha⟩ := ha
      obtain ⟨b, hb⟩ := hb
      apply hnot
      refine ⟨(a, b), ?_, Prod.ext ha.symm hb.symm⟩
      change (a, b) ∈ antidiagonal n
      rw [Finset.mem_antidiagonal]
      apply Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hp)
      simpa only [ha, hb, Nat.mul_add] using Finset.mem_antidiagonal.mp hij
    rw [PowerSeries.coeff_expand_of_not_dvd _ _ _ hndvd, zero_mul]
  · intro ij hij
    simp only [PowerSeries.coeff_expand_mul]

private theorem shifted_partition_u_eq_zero (p : ℕ) [isLargePrime p] :
    uSeries p (PowerSeries.X ^ δ p *
      PowerSeries.mk (fun n : ℕ => (partition n : ZMod p))) = 0 ↔
        RamanujanCongruenceWith p (δ p) := by
  have hp : 0 < p := (Fact.out : p.Prime).pos
  have hcast (n : ℤ) : (partition n : ZMod p) = 0 ↔
      (partition n ≡ 0 [MOD p]) := by
    rw [Nat.modEq_zero_iff_dvd, ZMod.natCast_eq_zero_iff]
  rw [PowerSeries.ext_iff]
  simp only [uSeries, PowerSeries.coeff_mk, coeff_shift_partition, _root_.map_zero]
  constructor
  · intro h n
    cases n with
    | ofNat n =>
      apply (hcast _).mp
      simpa only [Nat.cast_mul, Int.ofNat_eq_natCast] using h n
    | negSucc n =>
      have hn : (p : ℤ) * Int.negSucc n - δ p < 0 := by
        have : (0 : ℤ) < p := by exact_mod_cast hp
        have : Int.negSucc n < 0 := Int.negSucc_lt_zero n
        nlinarith [Int.natCast_nonneg (δ p)]
      simpa only [partition_of_neg hn] using (Nat.ModEq.refl (n := p) 0)
  · intro h n
    apply (hcast _).mpr
    simpa only [Nat.cast_mul] using h (n : ℤ)

/-- The U image of the discriminant power vanishes exactly when the corresponding
partition progression satisfies a Ramanujan congruence. -/
theorem flu_eq_zero_iff {p : ℕ} [isLargePrime p] :
    (fl p).UOp = 0 ↔ RamanujanCongruenceWith p (δ p) := by
  obtain ⟨E, hE0, hfactor⟩ := fl_euler_factor p
  let P : PowerSeries (ZMod p) := PowerSeries.mk fun n => (partition n : ZMod p)
  let H := PowerSeries.X ^ δ p * P
  have hUne : E ^ p ≠ 0 := by
    apply pow_ne_zero
    intro h
    simp [h] at hE0
  have hU : uSeries p (fl p).fourier = E ^ p * uSeries p H := by
    rw [hfactor, ← PowerSeries.ZMod.expand_card p (E ^ p)]
    exact uSeries_expand_mul NeZero.out _ _
  have hzero : (fl p).UOp = 0 ↔ uSeries p (fl p).fourier = 0 := by
    constructor
    · intro h
      ext n
      have hc := congrArg (coeff n) h
      simpa [uSeries, ModularFormMod.coeff, Nat.mul_comm] using hc
    · intro h
      apply ext_coeff
      intro n
      have hc := congrArg (PowerSeries.coeff n) h
      simpa [uSeries, ModularFormMod.coeff, Nat.mul_comm] using hc
  rw [hzero, hU, mul_eq_zero]
  simpa only [hUne, false_or, H, P] using shifted_partition_u_eq_zero p
