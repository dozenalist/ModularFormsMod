/-
Copyright (c) 2026 Carter Hastings. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carter Hastings
-/

import ModularFormsMod.ModularFormMod.BaseChange
import ModularFormsMod.ModularFormMod.HasseIdeal

/-!
# Polynomial presentation of the graded algebra of reduced level-one forms

If `r` is surjective and six is invertible in its source, reduced monomials in `E₄` and `E₆`
form a basis in each weight. Consequently the full graded algebra is a polynomial algebra
over the target ring. Its Fourier relations pull back to the kernel of Eisenstein evaluation.
-/

open PowerSeries MatrixGroups ModularFormOver.Basis
open scoped DirectSum TensorProduct

noncomputable section

namespace ModularFormMod

variable {R S : Type} [CommRing R] [Algebra R ℂ] [FaithfulSMul R ℂ]
  [CommRing S] (r : R →+* S) [RingHomSurjective r]

/-- The graded ring of reduced level-one modular forms. -/
abbrev GradedRing := ⨁ k : ℤ, ModularFormMod r 𝒮ℒ k

/-- Evaluate variables of weights four and six at the reduced Eisenstein series. -/
def eisensteinEval : MvPolynomial (Fin 2) S →ₐ[S] GradedRing r :=
  MvPolynomial.aeval
    ![DirectSum.of (ModularFormMod r 𝒮ℒ) 4 ((ModularFormOver.E₄.tower R).Reduce r),
      DirectSum.of (ModularFormMod r 𝒮ℒ) 6 ((ModularFormOver.E₆.tower R).Reduce r)]

@[simp] theorem eisensteinEval_X_zero :
    eisensteinEval r (MvPolynomial.X 0) =
      DirectSum.of (ModularFormMod r 𝒮ℒ) 4 ((ModularFormOver.E₄.tower R).Reduce r) := by
  simp [eisensteinEval]

@[simp] theorem eisensteinEval_X_one :
    eisensteinEval r (MvPolynomial.X 1) =
      DirectSum.of (ModularFormMod r 𝒮ℒ) 6 ((ModularFormOver.E₆.tower R).Reduce r) := by
  simp [eisensteinEval]

/-- Polynomial evaluation in the graded ring commutes with reduction of coefficients. -/
theorem eisensteinEval_map (p : MvPolynomial (Fin 2) R) :
    eisensteinEval r (MvPolynomial.map r p) =
      ModularFormOver.ReduceAlgHom r (ModularFormOver.eisensteinEval R p) := by
  induction p using MvPolynomial.induction_on with
  | C a =>
    simp only [MvPolynomial.map_C, eisensteinEval, ModularFormOver.eisensteinEval,
      MvPolynomial.aeval_C, AlgHom.commutes]
    change DirectSum.of (ModularFormMod r 𝒮ℒ) 0 (const (r a)) =
      DirectSum.of (ModularFormMod r 𝒮ℒ) 0 (a • 1)
    congr 1
    apply ext
    simp [PowerSeries.smul_eq_C_mul]
  | add p q hp hq => simp only [_root_.map_add, hp, hq]
  | mul_X p i hp =>
    fin_cases i <;> simp [hp]

section SixInvertible

variable [Invertible (6 : R)]

/-- The reduced monomial basis, transported from the original basis by base change. -/
def PBasis (k : ℤ) : Module.Basis (Fin (dim k)) S (ModularFormMod r 𝒮ℒ k) := by
  letI := r.toAlgebra
  exact ((ModularFormOver.Basis.PBasis R k).baseChange S).map (baseChangeEquiv r k)

@[simp] theorem PBasis_apply (k : ℤ) (i : Fin (dim k)) :
    PBasis r k i = (P (R := R) k i.val i.isLt).Reduce r := by
  let := r.toAlgebra
  change baseChangeEquiv r k ((ModularFormOver.Basis.PBasis R k).baseChange S i) = _
  rw [Module.Basis.baseChange_apply, baseChangeEquiv_tmul, one_smul,
    ModularFormOver.Basis.PBasis_apply]

private def monomialWeight (d : Fin 2 →₀ ℕ) : ℤ := d 0 * 4 + d 1 * 6

private theorem monomialIndex_lt (d : Fin 2 →₀ ℕ) :
    d 0 / 3 < dim (monomialWeight d) := by
  have hd := dim_monomial (d 0) (d 1)
  have hw : monomialWeight d = (d 0 * 4 + d 1 * 6 : ℕ) := by simp [monomialWeight]
  rw [hw, hd]
  omega

private def monomialIndex (d : Fin 2 →₀ ℕ) : Σ k : ℤ, Fin (dim k) :=
  ⟨monomialWeight d, ⟨d 0 / 3, monomialIndex_lt d⟩⟩

private theorem powers_monomialIndex (d : Fin 2 →₀ ℕ) :
    (Ppowers (monomialWeight d))[d 0 / 3]'(by
      rw [Ppowers_length]; exact monomialIndex_lt d) = ![d 0, d 1] := by
  rw [Ppowers_getElem_eq _ _ (monomialIndex_lt d)]
  have hw : monomialWeight d = (d 0 * 4 + d 1 * 6 : ℕ) := by simp [monomialWeight]
  have hd : dim (monomialWeight d) = d 0 / 3 + d 1 / 2 + 1 := by
    rw [hw]; exact dim_monomial _ _
  ext i
  fin_cases i <;> dsimp <;> rw [hd, hw, Int.toNat_natCast] <;> omega

private theorem monomialIndex_injective : Function.Injective monomialIndex := by
  intro d e h
  have hp := congrArg (fun i : Σ k : ℤ, Fin (dim k) =>
    (Ppowers i.1)[i.2.val]'(by rw [Ppowers_length]; exact i.2.isLt)) h
  have hp' := (powers_monomialIndex d).symm.trans (hp.trans (powers_monomialIndex e))
  ext i
  fin_cases i
  · exact congrFun hp' 0
  · exact congrFun hp' 1

omit [Algebra R ℂ] [FaithfulSMul R ℂ] [Invertible (6 : R)] in
private theorem monomial_eq_PPolynomial (d : Fin 2 →₀ ℕ) :
    MvPolynomial.monomial d (1 : R) =
      ModularFormOver.PPolynomial R (monomialWeight d) (d 0 / 3) (monomialIndex_lt d) := by
  simp only [ModularFormOver.PPolynomial, powers_monomialIndex,
    Matrix.cons_val_zero, Matrix.cons_val_one,
    MvPolynomial.monomial_eq, map_one, one_mul]
  rw [Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Fin.prod_univ_two]

omit [Invertible (6 : R)] in
private theorem eisensteinEval_monomial_one (d : Fin 2 →₀ ℕ) :
    eisensteinEval r (MvPolynomial.monomial d 1) =
      DirectSum.of (ModularFormMod r 𝒮ℒ) (monomialWeight d)
        ((P (R := R) (monomialWeight d) (d 0 / 3) (monomialIndex_lt d)).Reduce r) := by
  have h := eisensteinEval_map r (MvPolynomial.monomial d 1)
  simp only [MvPolynomial.map_monomial, map_one] at h
  rw [h, monomial_eq_PPolynomial, ModularFormOver.eisensteinEval_PPolynomial,
    ModularFormOver.ReduceAlgHom_of]

/-- Monomials remain independent after coefficient reduction because the corresponding
fixed-weight `P` families remain bases over `S`. -/
theorem eisensteinEval_injective : Function.Injective (eisensteinEval r) := by
  have h := DFinsupp.linearIndependent_single (R := S)
    (fun k (n : Fin (dim k)) => (P (R := R) k n.val n.isLt).Reduce r)
    (fun k => by
      have h := (PBasis r k).linearIndependent
      change LinearIndependent S (fun n : Fin (dim k) =>
        (P (R := R) k n.val n.isLt).Reduce r)
      convert h using 1
      funext n
      exact (PBasis_apply r k n).symm)
  have hc := h.comp monomialIndex monomialIndex_injective
  have hmon : LinearIndependent S (fun d : Fin 2 →₀ ℕ =>
      eisensteinEval r (MvPolynomial.monomial d 1)) := by
    convert! hc using 1
    funext d
    exact eisensteinEval_monomial_one r d
  change Function.Injective (eisensteinEval r).toLinearMap
  refine LinearMap.injective_of_linearIndependent
    (f := (eisensteinEval r).toLinearMap)
    (MvPolynomial.basisMonomials (Fin 2) S).span_eq ?_
  exact hmon

/-- Every graded reduced form is a polynomial in the reduced Eisenstein series. -/
theorem eisensteinEval_surjective : Function.Surjective (eisensteinEval r) := by
  intro f
  obtain ⟨g, rfl⟩ := ModularFormOver.ReduceAlgHom_surjective r f
  obtain ⟨p, rfl⟩ := ModularFormOver.eisensteinEval_surjective R g
  exact ⟨MvPolynomial.map r p, eisensteinEval_map r p⟩

/-- The graded algebra of reduced level-one forms is polynomial in weights four and six. -/
def eisensteinAlgEquiv : MvPolynomial (Fin 2) S ≃ₐ[S] GradedRing r :=
  AlgEquiv.ofBijective (eisensteinEval r)
    ⟨eisensteinEval_injective r, eisensteinEval_surjective r⟩

@[simp] theorem eisensteinAlgEquiv_X_zero :
    eisensteinAlgEquiv r (MvPolynomial.X 0) =
      DirectSum.of (ModularFormMod r 𝒮ℒ) 4 ((ModularFormOver.E₄.tower R).Reduce r) :=
  eisensteinEval_X_zero r

@[simp] theorem eisensteinAlgEquiv_X_one :
    eisensteinAlgEquiv r (MvPolynomial.X 1) =
      DirectSum.of (ModularFormMod r 𝒮ℒ) 6 ((ModularFormOver.E₆.tower R).Reduce r) :=
  eisensteinEval_X_one r

end SixInvertible

/-- Fourier expansion after graded polynomial evaluation is Eisenstein Fourier evaluation. -/
theorem fourierAlgHom_comp_eisensteinEval :
    (fourierAlgHom r (Γ := 𝒮ℒ)).comp (eisensteinEval r) = eisensteinFourierEval r := by
  apply MvPolynomial.algHom_ext
  intro i
  fin_cases i <;> simp

/-- The polynomial Fourier relations are exactly the preimage of the Hasse ideal. -/
theorem comap_hasseIdeal_eisensteinEval :
    Ideal.comap (eisensteinEval r) (hasseIdeal (Γ := 𝒮ℒ) r) =
      RingHom.ker (eisensteinFourierEval r) := by
  ext p
  change fourierAlgHom r (eisensteinEval r p) = 0 ↔ eisensteinFourierEval r p = 0
  rw [← AlgHom.comp_apply, fourierAlgHom_comp_eisensteinEval]

/-- The reduced Fourier algebra is the polynomial algebra modulo the Fourier relations. -/
def eisensteinFourierQuotientEquiv [Invertible (6 : R)] :
    (MvPolynomial (Fin 2) S ⧸ RingHom.ker (eisensteinFourierEval r)) ≃ₐ[S] rAlgebra r 𝒮ℒ :=
  (Ideal.quotientKerEquivRange (eisensteinFourierEval r)).trans
    (Subalgebra.equivOfEq _ _ (rAlgebra_eq r).symm)

end ModularFormMod
