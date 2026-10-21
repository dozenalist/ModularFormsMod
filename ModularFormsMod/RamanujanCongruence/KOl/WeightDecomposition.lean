/-
Copyright (c) 2026 Carter Hastings. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carter Hastings
-/

module

public import ModularFormsMod.ModularFormMod.ZMod.Filtration

/-!
# Separating Fourier relations by weight modulo `p - 1`

This is the direct-sum observation used in Kiming--Olsson, Proposition 3.
The Hasse relation `Abar - 1` is homogeneous of degree zero for this grading.
-/

@[expose] public section

noncomputable section

open ModularFormMod PInteger
open ModularFormOver (eisensteinWeights)
open scoped ModularFormMod.ZMod

namespace RamanujanCongruence.KOl

variable {p : ℕ} [isLargePrime p]

/-- The Eisenstein weights four and six, reduced modulo `p - 1`. -/
def residueWeights (p : ℕ) (i : Fin 2) : ZMod (p - 1) :=
  (eisensteinWeights i : ZMod (p - 1))

private theorem homogeneous_residue {F : MvPolynomial (Fin 2) (ZMod p)} {k : ℤ}
    (hF : F.IsWeightedHomogeneous eisensteinWeights k) :
    F.IsWeightedHomogeneous (residueWeights p) (k : ZMod (p - 1)) := by
  intro d hd
  have h := congrArg (fun n : ℤ => (n : ZMod (p - 1))) (hF hd)
  simpa [Finsupp.weight_apply, Finsupp.sum_fintype, Fin.sum_univ_two,
    residueWeights, Finsupp.sum, map_sum, nsmul_eq_mul] using h

/-- Every residue-weight component of a Fourier relation is again a relation. -/
theorem fourierEval_component_eq_zero {F : MvPolynomial (Fin 2) (ZMod p)}
    (hF : eisensteinFourierEval (reduce (p := p)) F = 0) (s : ZMod (p - 1)) :
    eisensteinFourierEval reduce
      (MvPolynomial.weightedHomogeneousComponent (residueWeights p) s F) = 0 := by
  classical
  let := MvPolynomial.weightedGradedAlgebra (ZMod p) (residueWeights p)
  have hA : (ModularFormMod.ZMod.Abar p).IsWeightedHomogeneous
      (residueWeights p) 0 := by
    have h := homogeneous_residue (ModularFormMod.ZMod.Abar_isWeightedHomogeneous p)
    have hp : 1 ≤ p := by have := isLargePrime.AtLeastFive (ℓ := p); omega
    have hz : (((p : ℤ) - 1 : ℤ) : ZMod (p - 1)) = 0 := by
      have heq : (p : ℤ) - 1 = ((p - 1 : ℕ) : ℤ) := by omega
      rw [heq, Int.cast_natCast, ZMod.natCast_self]
    simpa only [hz] using h
  have hI : (ModularFormMod.ZMod.hasseIdeal p).IsHomogeneous
      (MvPolynomial.weightedHomogeneousSubmodule (ZMod p) (residueWeights p)) := by
    rw [ModularFormMod.ZMod.hasseIdeal_eq_span]
    apply Ideal.homogeneous_span
    intro F hF
    obtain rfl := Set.mem_singleton_iff.mp hF
    exact ⟨0, hA.sub (MvPolynomial.isWeightedHomogeneous_one _ _)⟩
  exact MvPolynomial.weightedHomogeneousComponent_mem_of_mem
    (ZMod p) (residueWeights p) hI hF s

/-- In a vanishing sum, the summands in each weight class vanish separately. -/
theorem sum_fourier_eq_zero_by_weight {ι : Type*} (I : Finset ι) (k : ι → ℤ)
    (f : (i : ι) → 𝓜 p(k i))
    (h : ∑ i ∈ I, (f i).fourier = 0) (s : ZMod (p - 1)) :
    ∑ i ∈ I with (k i : ZMod (p - 1)) = s, (f i).fourier = 0 := by
  classical
  have hF : eisensteinFourierEval reduce (∑ i ∈ I, (f i).toPolynomial) = 0 := by
    simpa only [map_sum, eisensteinFourierEval_toPolynomial] using h
  have hc := fourierEval_component_eq_zero hF s
  simpa only [map_sum, MvPolynomial.weightedHomogeneousComponent_of_mem
    (homogeneous_residue (toPolynomial_isWeightedHomogeneous _)),
    apply_ite, eisensteinFourierEval_toPolynomial, _root_.map_zero, Finset.sum_filter,
    eq_comm] using hc

end RamanujanCongruence.KOl
