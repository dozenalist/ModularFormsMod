/-
Copyright (c) 2026 Carter Hastings. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carter Hastings
-/
module

import ModularFormsMod.RamanujanCongruence.MainResults

/-!
# Solution

These proofs live in `ModularFormsMod/RamanujanCongruence/MainResults`
The declarations in this file match those in `Challenge.lean` exactly.

-/

namespace Partition

/-- The number of unordered partitions of a nonnegative integer, and zero on
negative integers. Here `n.Partition` is Mathlib's type of multisets of positive
natural numbers whose sum is `n`; thus `partition 0 = 1`. -/
def partition : ℤ → ℕ
  | Int.ofNat n => Fintype.card n.Partition
  | Int.negSucc _ => 0

/-- For a prime `p ≥ 13`, no integer shift gives a partition congruence modulo
`p` on the entire progression with step `p` (Ahlgren–Boylan, Theorem 1). -/
theorem not_RamanujanCongruence_verbose (p : ℕ) (hp : p.Prime) (hp13 : 13 ≤ p) :
    ∀ β : ℤ, ∃ n : ℤ, ¬ partition (p * n - β) ≡ 0 [MOD p] :=
  _root_.not_RamanujanCongruence_verbose p hp hp13

/-- Ramanujan's congruence `partition (5n + 4) ≡ 0 (mod 5)` for every integer `n`. -/
theorem RamanujanCongruence_5_verbose (n : ℤ) :
    partition (5 * n + 4) ≡ 0 [MOD 5] :=
  _root_.RamanujanCongruence_5_verbose n

/-- Ramanujan's congruence `partition (7n + 5) ≡ 0 (mod 7)` for every integer `n`. -/
theorem RamanujanCongruence_7_verbose (n : ℤ) :
    partition (7 * n + 5) ≡ 0 [MOD 7] :=
  _root_.RamanujanCongruence_7_verbose n

/-- Ramanujan's congruence `partition (11n + 6) ≡ 0 (mod 11)` for every integer `n`. -/
theorem RamanujanCongruence_11_verbose (n : ℤ) :
    partition (11 * n + 6) ≡ 0 [MOD 11] :=
  _root_.RamanujanCongruence_11_verbose n


end Partition
