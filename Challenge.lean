/-
Copyright (c) 2026 Carter Hastings. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carter Hastings
-/
module

public import Mathlib.Combinatorics.Enumerative.Partition.Basic
public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Nat.Prime.Defs

/-!
# Ramanujan congruences for the partition function

The only project definition to audit is `partition` below. It counts ordinary
unordered partitions, including the empty partition at zero, and is extended
by zero to negative integers. Its body is specified, rather than left as a
definition hole, so Comparator must preserve this meaning in the Solution.

The three positive results are Ramanujan's classical congruences. The negative
result formalizes the nonexistence theorem of Ahlgren and Boylan: for every
prime `p ≥ 13` and every integer shift `β`, some term of the progression
`p * n - β` has partition count not divisible by `p`. The parameter `n` is an
integer in all four statements; negative arguments use the zero extension.

These statements concern progressions with step equal to the prime modulus.
They do not rule out partition congruences on progressions of larger step or
modulo prime powers, and do not assert the cases of primes two and three.
The sources, proof provenance, automation, and review status are recorded in
`formalization.yaml` and the README.
-/

@[expose] public section

/-- The number of unordered partitions of a nonnegative integer, and zero on
negative integers. Here `n.Partition` is Mathlib's type of multisets of positive
natural numbers whose sum is `n`; thus `partition 0 = 1`. -/
def partition : ℤ → ℕ
  | Int.ofNat n => Fintype.card n.Partition
  | Int.negSucc _ => 0

/-- For a prime `p ≥ 13`, no integer shift gives a partition congruence modulo
`p` on the entire progression with step `p` (Ahlgren–Boylan, Theorem 1). -/
theorem not_RamanujanCongruence_verbose (p : ℕ) (hp : p.Prime) (hp13 : 13 ≤ p) :
    ∀ β : ℤ, ∃ n : ℤ, ¬ partition (p * n - β) ≡ 0 [MOD p] := by
  sorry

/-- Ramanujan's congruence `partition (5n + 4) ≡ 0 (mod 5)` for every integer `n`. -/
theorem RamanujanCongruence_5_verbose (n : ℤ) :
    partition (5 * n + 4) ≡ 0 [MOD 5] := by
  sorry

/-- Ramanujan's congruence `partition (7n + 5) ≡ 0 (mod 7)` for every integer `n`. -/
theorem RamanujanCongruence_7_verbose (n : ℤ) :
    partition (7 * n + 5) ≡ 0 [MOD 7] := by
  sorry

/-- Ramanujan's congruence `partition (11n + 6) ≡ 0 (mod 11)` for every integer `n`. -/
theorem RamanujanCongruence_11_verbose (n : ℤ) :
    partition (11 * n + 6) ≡ 0 [MOD 11] := by
  sorry
