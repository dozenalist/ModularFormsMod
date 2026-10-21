/-
Copyright (c) 2026 Carter Hastings. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carter Hastings
-/

module

public import ModularFormsMod.ModularFormMod.BaseChange

/-!
# Reduced forms as modules over the effective coefficient ring

The effective coefficient ring of an arbitrary map `r` is `R ⧸ ker r`. Reduction along the
quotient map gives the same module over this ring. At level one this yields a basis and
coordinates over `R ⧸ ker r`, with no surjectivity assumption on `r` itself.
-/

@[expose] public section

open MatrixGroups ModularFormOver.Basis

noncomputable section

namespace ModularFormMod

variable {R S : Type} [CommRing R] [Algebra R ℂ] [FaithfulSMul R ℂ]
  [CommRing S] {Γ : Subgroup (GL (Fin 2) ℝ)} [Γ.IsArithmetic] [Γ.HasDetOne]

/-- Factoring the coefficient map through `R ⧸ ker r` preserves the module over this quotient. -/
def quotientKerLinearEquiv (r : R →+* S) (k : ℤ) :
    ModularFormMod (Ideal.Quotient.mk (RingHom.ker r)) Γ k ≃ₗ[R ⧸ RingHom.ker r]
      ModularFormMod r Γ k := by
  let e := quotientKerEquiv (Γ := Γ) (k := k) r
  refine { e.toEquiv with map_add' := e.map_add, map_smul' := ?_ }
  intro a f
  refine Quotient.inductionOn' a fun a => ?_
  have hsource : Ideal.Quotient.mk (RingHom.ker r) a • f = a • f := by
    apply ext
    rfl
  change e (Ideal.Quotient.mk (RingHom.ker r) a • f) =
    Ideal.Quotient.mk (RingHom.ker r) a • e f
  rw [hsource, quotient_mk_smul]
  exact e.map_smul a f

/-- A basis of reduced level-one forms over the quotient of the source by the coefficient
kernel, for an arbitrary coefficient homomorphism. -/
def quotientGBasis (r : R →+* S) (k : ℤ) :
    Module.Basis (Fin (dim k)) (R ⧸ RingHom.ker r) (ModularFormMod r 𝒮ℒ k) :=
  (GBasis (Ideal.Quotient.mk (RingHom.ker r)) k).map (quotientKerLinearEquiv r k)

/-- Reduced level-one forms are `dim k` copies of the effective coefficient ring. -/
def quotientCoordinatesEquiv (r : R →+* S) (k : ℤ) :
    ModularFormMod r 𝒮ℒ k ≃ₗ[R ⧸ RingHom.ker r] (Fin (dim k) → R ⧸ RingHom.ker r) :=
  (quotientGBasis r k).equivFun

end ModularFormMod
