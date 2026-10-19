/-
Copyright (c) 2026 Carter Hastings. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carter Hastings
-/

import ModularFormsMod.ModularFormMod.Basis
import Mathlib.LinearAlgebra.TensorProduct.Basis

/-!
# Base change and independence of the lifting ring at level one

The reduced triangular basis is defined by integral Fourier series, so surjective reductions
onto the same target ring have canonically identical Fourier expansions. For a surjective
`r : R →+* S`, scalar extension `S ⊗[R] M_k(R)` is the module of reduced forms.
-/

open PowerSeries MatrixGroups ModularFormOver.Basis
open scoped TensorProduct

noncomputable section

namespace ModularFormMod

variable {R S T : Type} [CommRing R] [Algebra R ℂ] [FaithfulSMul R ℂ]
  [CommRing S] [CommRing T] [Algebra T ℂ] [FaithfulSMul T ℂ]

/-- The reduced `G` family is obtained from one universal integral Fourier series. -/
theorem G_fourier (r : R →+* S) (k : ℤ) (n : ℕ) (hn : n < dim k) :
    (G r k n hn).fourier = PowerSeries.map (Int.castRingHom S)
      (ModularFormOver.fourier ℤ (ModularFormOver.Basis.G (R := ℤ) k n hn)) := by
  have h : ModularFormOver.fourier R (ModularFormOver.Basis.G (R := R) k n hn) =
      ModularFormOver.fourier ℤ (ModularFormOver.Basis.G (R := ℤ) k n hn) R := by
    apply map_algebraMap_injective ℂ
    rw [ModularFormOver.map_fourier, ModularFormOver.map_fourier]
    rfl
  change PowerSeries.map r (ModularFormOver.fourier R
    (ModularFormOver.Basis.G (R := R) k n hn)) = _
  rw [h, ModularFormOver.fourier_ring_cast ℤ R ℤ]
  ext m
  simp

variable (r : R →+* S) [RingHomSurjective r]

/-- Reduction maps the coordinates of the original `G` basis coefficientwise. -/
@[simp] theorem GBasis_repr_Reduce (k : ℤ) (f : ModularFormOver R 𝒮ℒ k)
    (i : Fin (dim k)) :
    (GBasis r k).repr (f.Reduce r) i = r ((ModularFormOver.Basis.GBasis R k).repr f i) := by
  classical
  let b := ModularFormOver.Basis.GBasis R k
  have h : f.Reduce r = ∑ j : Fin (dim k), r (b.repr f j) • GBasis r k j := by
    have h := congrArg (ModularFormOver.ReduceLinearMap (r := r)) (b.sum_repr f)
    rw [_root_.map_sum] at h
    simp only [ModularFormOver.ReduceLinearMap_apply,
      ModularFormOver.Reduce_smul_of_surjective] at h
    refine h.symm.trans (Finset.sum_congr rfl fun j _ => ?_)
    congr 1
    change ((ModularFormOver.Basis.GBasis R k) j).Reduce r = GBasis r k j
    rw [GBasis_apply, ModularFormOver.Basis.GBasis_apply]
    rfl
  rw [h]
  exact congrFun ((GBasis r k).repr_sum_self (fun j => r (b.repr f j))) i

/-- Scalar extension along a surjective coefficient map is the space of reduced forms. -/
def baseChangeEquiv (k : ℤ) :
    letI := r.toAlgebra
    (S ⊗[R] ModularFormOver R 𝒮ℒ k) ≃ₗ[S] ModularFormMod r 𝒮ℒ k := by
  letI := r.toAlgebra
  exact ((ModularFormOver.Basis.GBasis R k).baseChange S).equiv (GBasis r k) (Equiv.refl _)

/-- On pure tensors the base-change equivalence is scalar multiplication after reduction. -/
@[simp] theorem baseChangeEquiv_tmul (k : ℤ) (a : S) (f : ModularFormOver R 𝒮ℒ k) :
    letI := r.toAlgebra
    baseChangeEquiv r k (a ⊗ₜ[R] f) = a • f.Reduce r := by
  let := r.toAlgebra
  apply (GBasis r k).repr.injective
  ext i
  simp [baseChangeEquiv, Module.Basis.equiv, Algebra.smul_def, mul_comm,
    RingHom.algebraMap_toAlgebra]

/-- Changing the lifting ring, while keeping a surjective map to `S`, preserves level-one forms. -/
def sourceEquiv (s : T →+* S) [RingHomSurjective s] (k : ℤ) :
    ModularFormMod r 𝒮ℒ k ≃ₗ[S] ModularFormMod s 𝒮ℒ k :=
  (GBasis r k).equiv (GBasis s k) (Equiv.refl _)

@[simp] theorem sourceEquiv_G (s : T →+* S) [RingHomSurjective s]
    (k : ℤ) (i : Fin (dim k)) :
    sourceEquiv r s k (G r k i.val i.isLt) = G s k i.val i.isLt := by
  simpa only [sourceEquiv, GBasis_apply, Equiv.refl_apply] using
    (Module.Basis.equiv_apply (GBasis r k) i (GBasis s k) (Equiv.refl _))

/-- The canonical change of lifting ring preserves the entire Fourier expansion. -/
@[simp] theorem sourceEquiv_fourier (s : T →+* S) [RingHomSurjective s]
    (k : ℤ) (f : ModularFormMod r 𝒮ℒ k) :
    (sourceEquiv r s k f).fourier = f.fourier := by
  have h : (fourierLinearMap (r := s)).comp (sourceEquiv r s k).toLinearMap =
      fourierLinearMap (r := r) := by
    apply (GBasis r k).ext
    intro i
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, GBasis_apply,
      sourceEquiv_G, fourierLinearMap_apply, G_fourier]
  exact congrArg (fun l => l f) h

end ModularFormMod
