/-
Copyright (c) 2026 Carter Hastings. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carter Hastings
-/

module

public import ModularFormsMod.ModularFormMod.Map
public import Mathlib.LinearAlgebra.Isomorphisms
public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# Fixed-weight congruence kernels

`reductionSubmodule r` consists of forms all of whose coefficients belong to `ker r`.
The quotient by this submodule is the module of reduced forms. Equal coefficient kernels
give canonical linear equivalences, and reduced forms carry scalars from `R ⧸ ker r`.
-/

@[expose] public section

open MatrixGroups

noncomputable section

variable {R S T : Type} [CommRing R] [Algebra R ℂ] [FaithfulSMul R ℂ]
  [CommRing S] [CommRing T] {Γ : Subgroup (GL (Fin 2) ℝ)}
  [Γ.IsArithmetic] [Γ.HasDetOne] {k : ℤ}

namespace ModularFormMod

/-- The submodule of forms whose Fourier coefficients vanish under `r`. -/
def reductionSubmodule (r : R →+* S) : Submodule R (ModularFormOver R Γ k) :=
  LinearMap.ker (ModularFormOver.ReduceLinearMap (r := r))

@[simp] theorem mem_reductionSubmodule (r : R →+* S) (f : ModularFormOver R Γ k) :
    f ∈ reductionSubmodule r ↔ ∀ n, r (ModularFormOver.coeff R n f) = 0 :=
  ModularFormOver.Reduce_eq_zero_iff f

/-- The fixed-weight quotient presentation of reduced modular forms. -/
def quotientEquiv (r : R →+* S) :
    (ModularFormOver R Γ k ⧸ reductionSubmodule r) ≃ₗ[R] ModularFormMod r Γ k :=
  (ModularFormOver.ReduceLinearMap (r := r)).quotKerEquivOfSurjective
    (ModularFormOver.Reduce_surjective r)

@[simp] theorem quotientEquiv_mk (r : R →+* S) (f : ModularFormOver R Γ k) :
    quotientEquiv r (Submodule.Quotient.mk f) = f.Reduce r := rfl

@[simp] theorem quotientEquiv_symm_Reduce (r : R →+* S) (f : ModularFormOver R Γ k) :
    (quotientEquiv r).symm (f.Reduce r) = Submodule.Quotient.mk f := by
  apply (quotientEquiv r).injective
  rw [LinearEquiv.apply_symm_apply, quotientEquiv_mk]

/-- The congruence submodule depends only on the kernel of the coefficient map. -/
theorem reductionSubmodule_eq_of_ker_eq {r : R →+* S} {s : R →+* T}
    (h : RingHom.ker r = RingHom.ker s) :
    reductionSubmodule (Γ := Γ) (k := k) r = reductionSubmodule s := by
  ext f
  simp only [mem_reductionSubmodule, ← RingHom.mem_ker, h]

/-- Maps with the same coefficient kernel have canonically equivalent reduced modules. -/
def equivOfKerEq {r : R →+* S} {s : R →+* T} (h : RingHom.ker r = RingHom.ker s) :
    ModularFormMod r Γ k ≃ₗ[R] ModularFormMod s Γ k :=
  (quotientEquiv r).symm.trans
    ((Submodule.quotEquivOfEq _ _ (reductionSubmodule_eq_of_ker_eq h)).trans (quotientEquiv s))

@[simp] theorem equivOfKerEq_Reduce {r : R →+* S} {s : R →+* T}
    (h : RingHom.ker r = RingHom.ker s) (f : ModularFormOver R Γ k) :
    equivOfKerEq h (f.Reduce r) = f.Reduce s := by
  simp [equivOfKerEq]

/-- Every scalar in the coefficient kernel annihilates every reduced form. -/
theorem smul_eq_zero_of_mem_ker {r : R →+* S} {a : R} (ha : a ∈ RingHom.ker r)
    (f : ModularFormMod r Γ k) : a • f = 0 := by
  apply ext
  simp only [smul_fourier, Algebra.algebraMap_self, RingHom.id_apply,
    RingHom.mem_ker.mp ha, zero_smul, zero_fourier]

/-- Reduced forms are annihilated by the coefficient kernel. -/
theorem isTorsionBySet_ker (r : R →+* S) :
    Module.IsTorsionBySet R (ModularFormMod r Γ k) (RingHom.ker r) := by
  intro f a
  exact smul_eq_zero_of_mem_ker a.property f

/-- The scalar action of the quotient of the source by the coefficient kernel. -/
instance instModuleQuotientKer (r : R →+* S) :
    Module (R ⧸ RingHom.ker r) (ModularFormMod r Γ k) :=
  (isTorsionBySet_ker r).module

@[simp] theorem quotient_mk_smul (r : R →+* S) (a : R) (f : ModularFormMod r Γ k) :
    Ideal.Quotient.mk (RingHom.ker r) a • f = a • f := rfl

/-- Factoring through the quotient of the source does not change the reduced module. -/
def quotientKerEquiv (r : R →+* S) :
    ModularFormMod (Ideal.Quotient.mk (RingHom.ker r)) Γ k ≃ₗ[R]
      ModularFormMod r Γ k :=
  equivOfKerEq Ideal.mk_ker

end ModularFormMod
