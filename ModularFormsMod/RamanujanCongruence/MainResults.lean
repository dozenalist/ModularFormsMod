/-
Copyright (c) 2026 Carter Hastings. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carter Hastings
-/

module

public import ModularFormsMod.RamanujanCongruence.AhBo.DescentArgument
public import ModularFormsMod.RamanujanCongruence.KOl.Basic

/-!
# Main results on Ramanujan congruences

This file collects the main results on Ramanujan congruences, proving that
there exists a Ramanujan congruence for a prime p if and only if p = 5, 7, 11.
-/

@[expose] public section


open ModularFormMod.ZMod RamanujanCongruence.KOl ModularFormMod

/- There are no Ramanujan congruences for primes ≥ 13 -/
theorem not_RamanujanCongruence (p : ℕ) [isLargerPrime p] :
    ¬ RamanujanCongruence p := by
  rw [RamanujanCongruence_iff_delta]
  exact not_RamanujanCongruenceWith_delta


instance : isLargePrime 5 := {Prime := Nat.prime_five, AtLeastFive := le_rfl}
instance : isLargePrime 7 := {Prime := Nat.prime_seven, AtLeastFive := by decide}
instance : isLargePrime 11 := {Prime := Nat.prime_eleven, AtLeastFive := by decide}


private theorem RamanujanCongruence_of_filtration_lt {p : ℕ} [isLargePrime p]
    (hbound : (fl p).UOp.Filtration < 12) : RamanujanCongruence p := by
  rw [RamanujanCongruence_iff_delta, ← flu_eq_zero_iff]
  by_contra h
  have := twelve_le_Filtration_UOp_fl h
  omega

/-- Ramanujan's partition congruence modulo five. -/
theorem RamanujanCongruence_5 : RamanujanCongruence 5 := by
  apply RamanujanCongruence_of_filtration_lt
  have hhigh := Filtration_UOp_le (fl 5)
  norm_num [Filtration_fl, delta] at hhigh
  omega

/-- Ramanujan's partition congruence modulo seven. -/
theorem RamanujanCongruence_7 : RamanujanCongruence 7 := by
  apply RamanujanCongruence_of_filtration_lt
  have hhigh := Filtration_UOp_le (fl 7)
  norm_num [Filtration_fl, delta] at hhigh
  omega

/-- Ramanujan's partition congruence modulo eleven. -/
theorem RamanujanCongruence_11 : RamanujanCongruence 11 := by
  rw [RamanujanCongruence_iff_delta, ← flu_eq_zero_iff]
  by_contra h
  have hlow := twelve_le_Filtration_UOp_fl h
  have hhigh := Filtration_UOp_le (fl 11)
  have hcong := Filtration_congr (fl 11).UOp h
  norm_num [Filtration_fl, delta, Int.ModEq] at *
  omega


section verbose

theorem not_RamanujanCongruence_verbose (p : ℕ) (hp : p.Prime) (hp13 : 13 ≤ p) :
    ∀ β : ℤ, ∃ n : ℤ, ¬ partition (p * n - β) ≡ 0 [MOD p] := by
  have : isLargerPrime p := {Prime := hp, AtLeastThirteen := hp13}
  simpa only [← not_forall, ← not_exists] using! not_RamanujanCongruence p

theorem RamanujanCongruence_5_verbose (n : ℤ) :
    partition (5 * n + 4) ≡ 0 [MOD 5] := by
  rw [show 5 * n + 4 = 5 * (n + 1) - 1 by ring]
  exact RamanujanCongruence_iff_delta.mp RamanujanCongruence_5 <| n + 1

theorem RamanujanCongruence_7_verbose (n : ℤ) :
    partition (7 * n + 5) ≡ 0 [MOD 7] := by
  rw [show 7 * n + 5 = 7 * (n + 1) - 2 by ring]
  exact RamanujanCongruence_iff_delta.mp RamanujanCongruence_7 <| n + 1

theorem RamanujanCongruence_11_verbose (n : ℤ) :
    partition (11 * n + 6) ≡ 0 [MOD 11] := by
  rw [show 11 * n + 6 = 11 * (n + 1) - 5 by ring]
  exact RamanujanCongruence_iff_delta.mp RamanujanCongruence_11 <| n + 1


#print axioms not_RamanujanCongruence_verbose
#print axioms RamanujanCongruence_5_verbose
#print axioms RamanujanCongruence_7_verbose
#print axioms RamanujanCongruence_11_verbose

end verbose
