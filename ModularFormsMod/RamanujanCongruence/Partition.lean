/-
Copyright (c) 2026 Carter Hastings. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carter Hastings
-/

import Mathlib.Combinatorics.Enumerative.Partition.GenFun
import Mathlib.Data.Int.ModEq
import Mathlib.Algebra.Field.Basic
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.Topology.Algebra.InfiniteSum.NatInt


/-!
### Partitions
This file defines the partition function and proves its generating function
-/


def partition : ℤ → ℕ
  | Int.ofNat n => Fintype.card n.Partition
  | Int.negSucc _ => 0


def RamanujanCongruenceWith (p : ℕ) (β : ℤ) : Prop :=
  ∀ n : ℤ, (partition ((p : ℤ) * n - β) ≡ 0 [MOD p])


def RamanujanCongruence (p : ℕ) : Prop :=
  ∃ β : ℤ, RamanujanCongruenceWith p β


section GeneratingFunction

open Finset PowerSeries
open scoped PowerSeries.WithPiTopology

noncomputable def partitionProduct {α} (m : ℕ) [Field α] :=
  ∏ i ∈ range m, (1 - (X : α⟦X⟧) ^ (i + 1) )⁻¹


theorem partition_eq_coeff_Product {α} [Field α] {n m : ℕ} (h : n ≤ m) :
    (partition n : α) = coeff (R := α) n (partitionProduct m) := by
  classical
  let : TopologicalSpace α := ⊥
  let : DiscreteTopology α := ⟨rfl⟩
  have hgeom (i : ℕ) :
      (1 : α⟦X⟧) + ∑' j : ℕ, (1 : α) • X ^ ((i + 1) * (j + 1)) =
        (1 - X ^ (i + 1))⁻¹ := by
    have hs := WithPiTopology.summable_pow_of_constantCoeff_eq_zero
      (f := (X : α⟦X⟧) ^ (i + 1)) (by simp)
    rw [eq_inv_iff_mul_eq_one (by simp)]
    simp only [one_smul, pow_mul]
    have hsplit : (∑' j : ℕ, ((X : α⟦X⟧) ^ (i + 1)) ^ j) =
        1 + ∑' j : ℕ, ((X : α⟦X⟧) ^ (i + 1)) ^ (j + 1) := by
      simpa only [pow_zero] using hs.tsum_eq_zero_add
    rw [← hsplit]
    exact WithPiTopology.tsum_pow_mul_one_sub_of_constantCoeff_eq_zero (by simp)
  have hprod := Nat.Partition.hasProd_genFun (fun _ _ ↦ (1 : α))
  simp_rw [hgeom] at hprod
  have hlim := (WithPiTopology.continuous_coeff α n).tendsto
    (Nat.Partition.genFun (fun _ _ ↦ (1 : α))) |>.comp hprod.tendsto_prod_nat
  have hstable (k : ℕ) (hk : m ≤ k) :
      coeff (R := α) n (partitionProduct k) = coeff n (partitionProduct m) := by
    induction k, hk using Nat.le_induction with
    | base => rfl
    | succ k hk ih =>
      rw [partitionProduct, prod_range_succ]
      change coeff n (partitionProduct k * (1 - X ^ (k + 1))⁻¹) = _
      have hc := coeff_mul_one_sub_of_lt_order
        (φ := partitionProduct k * (1 - (X : α⟦X⟧) ^ (k + 1))⁻¹)
        (ψ := X ^ (k + 1)) n (by
          rw [order_X_pow]
          exact_mod_cast (show n < k + 1 by omega))
      rw [mul_assoc, PowerSeries.inv_mul_cancel _ (by simp), mul_one] at hc
      exact hc.symm.trans ih
  have hconst : Filter.Tendsto (fun k ↦ coeff (R := α) n (partitionProduct k))
      Filter.atTop (nhds (coeff n (partitionProduct m))) :=
    tendsto_atTop_of_eventually_const hstable
  have heq := tendsto_nhds_unique hlim hconst
  simpa [Nat.Partition.coeff_genFun, Finsupp.prod, partition] using heq

end GeneratingFunction
