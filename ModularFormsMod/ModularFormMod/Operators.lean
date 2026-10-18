import ModularFormsMod.ModularFormMod.Kernel

set_option linter.style.header false

/-!
# Descent of linear operators through coefficient reduction

A linear operator descends exactly when it preserves the coefficient congruence kernels.
This provides a common interface for Hecke operators and other operators whose Fourier
coefficient formulas preserve congruences.
-/

open MatrixGroups

noncomputable section

namespace ModularFormMod

variable {R S : Type} [CommRing R] [Algebra R ℂ] [FaithfulSMul R ℂ]
  [CommRing S] {r : R →+* S} {Γ : Subgroup (GL (Fin 2) ℝ)}
  [Γ.IsArithmetic] [Γ.HasDetOne] {k j : ℤ}

/-- Descend an operator that preserves coefficientwise congruences. -/
def descend (L : ModularFormOver R Γ k →ₗ[R] ModularFormOver R Γ j)
    (hL : reductionSubmodule r ≤ (reductionSubmodule r).comap L) :
    ModularFormMod r Γ k →ₗ[R] ModularFormMod r Γ j :=
  (quotientEquiv r).toLinearMap.comp
    (((reductionSubmodule r).mapQ (reductionSubmodule r) L hL).comp
      (quotientEquiv r).symm.toLinearMap)

/-- A descended operator acts on a reduction by applying the original operator to any lift. -/
@[simp] theorem descend_Reduce
    (L : ModularFormOver R Γ k →ₗ[R] ModularFormOver R Γ j)
    (hL : reductionSubmodule r ≤ (reductionSubmodule r).comap L)
    (f : ModularFormOver R Γ k) :
    descend L hL (f.Reduce r) = (L f).Reduce r := by
  simp [descend, Submodule.mapQ_apply]

/-- The descended linear operator is uniquely determined by its action on lifts. -/
theorem descend_unique
    (L : ModularFormOver R Γ k →ₗ[R] ModularFormOver R Γ j)
    (hL : reductionSubmodule r ≤ (reductionSubmodule r).comap L)
    (A : ModularFormMod r Γ k →ₗ[R] ModularFormMod r Γ j)
    (hA : ∀ f, A (f.Reduce r) = (L f).Reduce r) : A = descend L hL := by
  ext f
  obtain ⟨g, rfl⟩ := f.existsReduce
  rw [hA, descend_Reduce]

/-- A coefficient formula that sends zero reductions to zero reductions supplies the
kernel condition needed for descent. -/
def descendOfCoeff
    (L : ModularFormOver R Γ k →ₗ[R] ModularFormOver R Γ j)
    (hL : ∀ f, (∀ n, r (ModularFormOver.coeff R n f) = 0) →
      ∀ n, r (ModularFormOver.coeff R n (L f)) = 0) :
    ModularFormMod r Γ k →ₗ[R] ModularFormMod r Γ j :=
  descend L (fun f hf => (mem_reductionSubmodule r (L f)).mpr
    (hL f ((mem_reductionSubmodule r f).mp hf)))

end ModularFormMod
