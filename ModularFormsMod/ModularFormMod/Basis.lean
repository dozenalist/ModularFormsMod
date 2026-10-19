/-
Copyright (c) 2026 Carter Hastings. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carter Hastings
-/

import ModularFormsMod.ModularFormMod.Kernel
import ModularFormsMod.ModularFormOver.Basis
import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
import Mathlib.RingTheory.Ideal.Operations

/-!
# Level-one bases and congruence Sturm bounds

The triangular integral `G` basis detects congruences along every ring homomorphism.
For surjective maps its reductions form a basis over the target ring. The fixed-weight
reduction kernel is exactly the coefficient kernel times the module of original forms.
-/

open PowerSeries MatrixGroups ModularFormOver.Basis

noncomputable section

variable {R S : Type} [CommRing R] [Algebra R ℂ] [FaithfulSMul R ℂ]
  [CommRing S] {r : R →+* S} {k : ℤ}

namespace ModularFormOver

/-- Initial coefficient congruences force the same congruences for the `G` coordinates. -/
theorem map_Gcoeffs_eq_zero_of_coeff (f : ModularFormOver R 𝒮ℒ k)
    (h : ∀ n < dim k, r (coeff R n f) = 0) :
    ∀ (n : ℕ) (hn : n < dim k), r (Gcoeffs f n hn) = 0 := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro hn
    cases n with
    | zero => simpa only [Gcoeffs] using h 0 hn
    | succ n =>
      simp only [Gcoeffs, map_sub, map_sum, map_mul, h (n + 1) hn]
      have hz : ∑ i : Fin (n + 1),
          r (Gcoeffs f i.val (i.isLt.trans hn)) *
            r (coeff R (n + 1) (G (R := R) k i.val (i.isLt.trans hn))) = 0 := by
        apply Finset.sum_eq_zero
        intro i _
        rw [ih i.val (by omega) (i.isLt.trans hn), zero_mul]
      rw [hz, sub_self]

/-- A level-one form reduces to zero when its first `dim k` coefficients do. -/
theorem Reduce_eq_zero_of_coeff (f : ModularFormOver R 𝒮ℒ k)
    (h : ∀ n < dim k, r (coeff R n f) = 0) : f.Reduce r = 0 := by
  have hc := map_Gcoeffs_eq_zero_of_coeff f h
  rw [← Gcoeffs_smul_G f]
  apply ModularFormMod.ext
  change (map r) ((fourierLinearMap (R := R))
    (∑ i : Fin (dim k), Gcoeffs f i.val i.isLt • G (R := R) k i.val i.isLt)) = 0
  rw [map_sum, map_sum]
  apply Finset.sum_eq_zero
  intro i _
  rw [map_smul]
  change map r (Gcoeffs f i.val i.isLt • fourier R (G (R := R) k i.val i.isLt)) = 0
  simp only [PowerSeries.smul_eq_C_mul, map_mul, map_C, hc, map_zero, zero_mul]

/-- Vanishing after reduction is detected by the first `dim k` Fourier coefficients. -/
theorem Reduce_eq_zero_iff_coeff (f : ModularFormOver R 𝒮ℒ k) :
    f.Reduce r = 0 ↔ ∀ n < dim k, r (coeff R n f) = 0 :=
  ⟨fun h n _ => (Reduce_eq_zero_iff f).mp h n, Reduce_eq_zero_of_coeff f⟩

end ModularFormOver

namespace ModularFormMod

/-- The congruence Sturm bound at level one, for arbitrary coefficient homomorphisms. -/
theorem sturm_bound {f g : ModularFormMod r 𝒮ℒ k}
    (h : ∀ n < dim k, coeff n f = coeff n g) : f = g := by
  obtain ⟨f, rfl⟩ := f.existsReduce
  obtain ⟨g, rfl⟩ := g.existsReduce
  apply sub_eq_zero.mp
  rw [← ModularFormOver.Reduce_sub]
  apply ModularFormOver.Reduce_eq_zero_of_coeff
  intro n hn
  rw [ModularFormOver.coeff_sub, map_sub]
  exact sub_eq_zero.mpr (h n hn)

theorem eq_iff_coeff_lt_dim {f g : ModularFormMod r 𝒮ℒ k} :
    f = g ↔ ∀ n < dim k, coeff n f = coeff n g :=
  ⟨fun h _ _ => congrArg _ h, sturm_bound⟩

/-- The reduced triangular basis family, available for every coefficient homomorphism. -/
def G (r : R →+* S) (k : ℤ) (n : ℕ) (hn : n < dim k) : ModularFormMod r 𝒮ℒ k :=
  (ModularFormOver.Basis.G (R := R) k n hn).Reduce r

@[simp] theorem coeff_order_G (r : R →+* S) (k : ℤ) (n : ℕ) (hn : n < dim k) :
    coeff n (G r k n hn) = 1 := by
  simp [G, ModularFormOver.Basis.coeff_order_G]

theorem coeff_lt_order_G (r : R →+* S) (k : ℤ) (c : ℕ) (hc : c < dim k)
    {n : ℕ} (hn : n < c) : coeff n (G r k c hc) = 0 := by
  simp [G, ModularFormOver.Basis.coeff_lt_order_G k c hc hn]

/-- At level one the coefficient kernel generates the whole fixed-weight reduction kernel. -/
theorem reductionSubmodule_eq_smul_top (r : R →+* S) :
    reductionSubmodule (Γ := 𝒮ℒ) (k := k) r =
      RingHom.ker r • (⊤ : Submodule R (ModularFormOver R 𝒮ℒ k)) := by
  apply le_antisymm
  · intro f hf
    have hc := ModularFormOver.map_Gcoeffs_eq_zero_of_coeff f
      (fun n _ => (mem_reductionSubmodule r f).mp hf n)
    rw [← ModularFormOver.Basis.Gcoeffs_smul_G f]
    apply Submodule.sum_mem
    intro i _
    exact Submodule.smul_mem_smul (hc i.val i.isLt) (Submodule.mem_top)
  · apply Submodule.smul_le.mpr
    intro a ha f _
    rw [mem_reductionSubmodule]
    intro n
    simp [ModularFormOver.coeff_smul, RingHom.mem_ker.mp ha]

section Surjective

variable (r : R →+* S) [RingHomSurjective r]

/-- The reduced `G` family is linearly independent over an arbitrary target ring. -/
theorem G_LI (k : ℤ) :
    LinearIndependent S (fun n : Fin (dim k) => G r k n.val n.isLt) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro a ha ⟨n, hn⟩
  induction n using Nat.strong_induction_on with
  | h n ih =>
    have hcoeff := congrArg (coeffLinearMap (r := r) n) ha
    simp only [map_sum, map_smul, coeffLinearMap_apply, smul_eq_mul] at hcoeff
    have hsingle : ∑ j : Fin (dim k), a j * coeff n (G r k j.val j.isLt) =
        a ⟨n, hn⟩ * coeff n (G r k n hn) := by
      apply Finset.sum_eq_single (⟨n, hn⟩ : Fin (dim k))
      · intro j _ hj
        by_cases hnj : n < j.val
        · rw [coeff_lt_order_G r k j.val j.isLt hnj, mul_zero]
        · have hjn : j.val < n := by
            have hne : j.val ≠ n := fun h => hj (Fin.ext h)
            omega
          rw [ih j.val hjn j.isLt, zero_mul]
      · intro h
        exact (h (Finset.mem_univ _)).elim
    rw [hsingle, coeff_order_G, mul_one] at hcoeff
    exact hcoeff

/-- The reduced `G` family spans all reduced forms when `r` is onto. -/
theorem G_span (k : ℤ) :
    ⊤ ≤ Submodule.span S {G r k n.val n.isLt | n : Fin (dim k)} := by
  classical
  intro f _
  obtain ⟨g, rfl⟩ := f.existsReduce
  have h := congrArg (ModularFormOver.ReduceLinearMap (r := r))
    (ModularFormOver.Basis.Gcoeffs_smul_G g)
  rw [map_sum] at h
  simp only [ModularFormOver.ReduceLinearMap_apply,
    ModularFormOver.Reduce_smul_of_surjective] at h
  rw [← h]
  exact Submodule.sum_mem _ fun i _ =>
    Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

/-- The level-one basis obtained by reducing the integral triangular `G` basis. -/
def GBasis (k : ℤ) : Module.Basis (Fin (dim k)) S (ModularFormMod r 𝒮ℒ k) :=
  Module.Basis.mk (G_LI r k) (G_span r k)

@[simp] theorem GBasis_apply (k : ℤ) (i : Fin (dim k)) :
    GBasis r k i = G r k i.val i.isLt := Module.Basis.mk_apply ..

instance instFree (k : ℤ) : Module.Free S (ModularFormMod r 𝒮ℒ k) :=
  Module.Free.of_basis (GBasis r k)

instance instFinite (k : ℤ) : Module.Finite S (ModularFormMod r 𝒮ℒ k) :=
  Module.Finite.of_basis (GBasis r k)

/-- Coordinates identify level-one reductions with `dim k` copies of the target ring. -/
def coordinatesEquiv (k : ℤ) : ModularFormMod r 𝒮ℒ k ≃ₗ[S] (Fin (dim k) → S) :=
  (GBasis r k).equivFun

theorem finrank_eq_dim [StrongRankCondition S] (k : ℤ) :
    Module.finrank S (ModularFormMod r 𝒮ℒ k) = dim k := by
  rw [Module.finrank_eq_card_basis (GBasis r k), Fintype.card_fin]

end Surjective

end ModularFormMod

namespace ModularFormOver

/-- Equality of reduced level-one forms is detected by their initial coefficients. -/
theorem Reduce_eq_iff_coeff_lt_dim (f g : ModularFormOver R 𝒮ℒ k) :
    f.Reduce r = g.Reduce r ↔ ∀ n < dim k, r (coeff R n f) = r (coeff R n g) :=
  ModularFormMod.eq_iff_coeff_lt_dim

end ModularFormOver
