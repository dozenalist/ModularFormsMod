/-
Copyright (c) 2026 Carter Hastings. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carter Hastings
-/

import ModularFormsMod.ModularFormMod.RAlgebra
import ModularFormsMod.ModularFormMod.Basic

/-!
# The kernel of Fourier expansion across weights

`hasseIdeal r` records relations between the Fourier expansions of different weights.
Its quotient is `rAlgebra r Γ`, and it meets every individual weight summand trivially.
The construction applies to every surjective coefficient homomorphism.
-/

open PowerSeries MatrixGroups DirectSum

namespace ModularFormMod

noncomputable section

variable {R S : Type} [CommRing R] [Algebra R ℂ] [FaithfulSMul R ℂ] [CommRing S]
  {Γ : Subgroup (GL (Fin 2) ℝ)} [Γ.IsArithmetic] [Γ.HasDetOne] {k j : ℤ}
    (r : R →+* S) [RingHomSurjective r]

/-- The ideal of relations between reduced Fourier expansions across weights. -/
def hasseIdeal : Ideal (⨁ k : ℤ, ModularFormMod r Γ k) :=
  RingHom.ker (fourierAlgHom r)

@[simp] theorem mem_hasseIdeal (f : ⨁ k : ℤ, ModularFormMod r Γ k) :
    f ∈ hasseIdeal r ↔ fourierAlgHom r f = 0 := Iff.rfl

/-- The Hasse ideal has trivial intersection with each individual weight summand. -/
@[simp] theorem of_mem_hasseIdeal_iff (f : ModularFormMod r Γ k) :
    DirectSum.of (ModularFormMod r Γ) k f ∈ hasseIdeal r ↔ f = 0 := by
  rw [mem_hasseIdeal, fourierAlgHom_of]
  exact ⟨fun h => ext h, fun h => by simp [h]⟩

/-- A difference of homogeneous elements lies in the ideal precisely when their Fourier
expansions agree, even if their weights differ. -/
theorem of_sub_of_mem_hasseIdeal_iff (f : ModularFormMod r Γ k) (g : ModularFormMod r Γ j) :
    DirectSum.of (ModularFormMod r Γ) k f - DirectSum.of (ModularFormMod r Γ) j g ∈
      hasseIdeal r ↔ f.fourier = g.fourier := by
  rw [mem_hasseIdeal, map_sub, fourierAlgHom_of, fourierAlgHom_of, sub_eq_zero]

/-- The reduced Fourier algebra is the quotient of the graded algebra by the Hasse ideal. -/
def hasseQuotientEquiv :
    ((⨁ k : ℤ, ModularFormMod r Γ k) ⧸ hasseIdeal (Γ := Γ) r) ≃ₐ[S] rAlgebra r Γ := by
  change ((⨁ k : ℤ, ModularFormMod r Γ k) ⧸ RingHom.ker (fourierAlgHom (Γ := Γ) r)) ≃ₐ[S]
    (fourierAlgHom (Γ := Γ) r).range
  exact Ideal.quotientKerEquivRange (fourierAlgHom (Γ := Γ) r)

@[simp] theorem coe_hasseQuotientEquiv_mk (f : ⨁ k : ℤ, ModularFormMod r Γ k) :
    (hasseQuotientEquiv (Γ := Γ) r (Ideal.Quotient.mk (hasseIdeal (Γ := Γ) r) f) : S⟦X⟧) =
      fourierAlgHom r f := rfl

/-- A graded lift reduces into the Hasse ideal exactly when its total Fourier expansion
vanishes coefficientwise under reduction. -/
@[simp] theorem ReduceAlgHom_mem_hasseIdeal_iff (f : ⨁ k : ℤ, ModularFormOver R Γ k) :
    ModularFormOver.ReduceAlgHom r f ∈ hasseIdeal r ↔
      PowerSeries.map r (ModularFormOver.fourierAlgHom f) = 0 := by
  rw [mem_hasseIdeal, fourierAlgHom_ReduceAlgHom]

end

end ModularFormMod
