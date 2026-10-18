import ModularFormsMod.ModularFormOver.Basis
import Mathlib.Algebra.DirectSum.Algebra
import Mathlib.LinearAlgebra.Finsupp.VectorSpace
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
# The polynomial presentation of level-one modular forms

For coefficient rings embedded in `ℂ` in which `6` is invertible, the full graded
ring is a polynomial algebra in `E₄` and `E₆`, of weights four and six.
Its weight-`k` piece corresponds to the weighted homogeneous polynomials of degree `k`.
The linear map `toPolynomial` gives the polynomial representing a form of a fixed weight.
-/

noncomputable section

open ModularFormOver.Basis MatrixGroups UpperHalfPlane
open scoped DirectSum

namespace ModularFormOver

variable (R : Type) [CommRing R] [Algebra R ℂ]

/-- The graded ring of level-one modular forms over `R`. -/
abbrev GradedRing := ⨁ k : ℤ, ModularFormOver R 𝒮ℒ k

/-- Constants equip the weight-indexed family of forms with a graded algebra structure over `R`. -/
instance instGAlgebraSL {Γ : Subgroup (GL (Fin 2) ℝ)} [Γ.IsArithmetic] [Γ.HasDetOne] :
    DirectSum.GAlgebra R (ModularFormOver R Γ) where
  toFun :=
    { toFun := fun r => const r
      map_zero' := ext₂ fun z => by simp [const_apply]
      map_add' := fun r s => ext₂ fun z => by simp [const_apply] }
  map_one := const_one
  map_mul r s := by
    apply gradedMonoid_eq_of_cast (by rfl)
    apply ext₂
    intro z
    change algebraMap R ℂ (r * s) = algebraMap R ℂ r * algebraMap R ℂ s
    exact map_mul _ r s
  commutes r x := by
    obtain ⟨k, f⟩ := x
    apply gradedMonoid_eq_of_cast (by change 0 + k = k + 0; omega)
    apply ext₂
    intro z
    change algebraMap R ℂ r * f z = f z * algebraMap R ℂ r
    exact mul_comm _ _
  smul_def r x := by
    obtain ⟨k, f⟩ := x
    apply gradedMonoid_eq_of_cast (by change k = 0 + k; omega)
    apply ext₂
    intro z
    change (r • f) z = algebraMap R ℂ r * f z
    simp [smul_apply, Algebra.smul_def]

/-- The weights of the two polynomial variables corresponding to `E₄` and `E₆`. -/
def eisensteinWeights : Fin 2 → ℤ := ![4, 6]

/-- Evaluate the two polynomial variables at `E₄` and `E₆` in the graded ring. -/
def eisensteinEval : MvPolynomial (Fin 2) R →ₐ[R] GradedRing R :=
  MvPolynomial.aeval
    ![DirectSum.of (ModularFormOver R 𝒮ℒ) 4 (E₄.tower R),
      DirectSum.of (ModularFormOver R 𝒮ℒ) 6 (E₆.tower R)]

/-- The first polynomial variable evaluates to `E₄` in the weight-four summand. -/
@[simp] theorem eisensteinEval_X_zero :
    eisensteinEval R (MvPolynomial.X 0) =
      DirectSum.of (ModularFormOver R 𝒮ℒ) 4 (E₄.tower R) := by
  simp [eisensteinEval]

/-- The second polynomial variable evaluates to `E₆` in the weight-six summand. -/
@[simp] theorem eisensteinEval_X_one :
    eisensteinEval R (MvPolynomial.X 1) =
      DirectSum.of (ModularFormOver R 𝒮ℒ) 6 (E₆.tower R) := by
  simp [eisensteinEval]

private theorem of_pow {k : ℤ} (f : ModularFormOver R 𝒮ℒ k) (n : ℕ) :
    DirectSum.of (ModularFormOver R 𝒮ℒ) k f ^ n =
      DirectSum.of (ModularFormOver R 𝒮ℒ) (n * k) (f.pow n) := by
  induction n with
  | zero =>
    change DirectSum.of _ 0 (1 : ModularFormOver R 𝒮ℒ 0) = _
    apply DirectSum.of_eq_of_gradedMonoid_eq
    apply gradedMonoid_eq_of_cast (by change (0 : ℤ) = 0 * k; simp)
    apply ext₂
    intro z
    change (1 : ℂ) = f z ^ 0
    simp
  | succ n ih =>
    rw [pow_succ, ih, DirectSum.of_mul_of]
    apply DirectSum.of_eq_of_gradedMonoid_eq
    apply gradedMonoid_eq_of_cast (by
      change (n : ℤ) * k + k = (n + 1 : ℕ) * k
      push_cast
      ring)
    apply ext₂
    intro z
    change (((f.pow n).mul f).cast _) z = (f.pow (n + 1)) z
    simp only [cast_apply, mul_apply, pow_apply, pow_succ]

private def monomialWeight (d : Fin 2 →₀ ℕ) : ℤ := d 0 * 4 + d 1 * 6

private theorem weight_eq (d : Fin 2 →₀ ℕ) :
    Finsupp.weight eisensteinWeights d = monomialWeight d := by
  rw [Finsupp.weight_eq_sum, Fin.sum_univ_two]
  simp [eisensteinWeights, monomialWeight]

private theorem dim_monomial (a b : ℕ) :
    dim (a * 4 + b * 6 : ℕ) = a / 3 + b / 2 + 1 := by
  rw [dim_eq_dim', dim']
  simp only [Int.natCast_nonneg, Int.even_iff, Int.ModEq, Int.toNat_natCast, ite_true]
  split_ifs <;> omega

private theorem monomialIndex_lt (d : Fin 2 →₀ ℕ) :
    d 0 / 3 < dim (monomialWeight d) := by
  have hd := dim_monomial (d 0) (d 1)
  have hw : monomialWeight d = (d 0 * 4 + d 1 * 6 : ℕ) := by
    simp [monomialWeight]
  rw [hw, hd]
  omega

private def monomialIndex (d : Fin 2 →₀ ℕ) : Σ k : ℤ, Fin (dim k) :=
  ⟨monomialWeight d, ⟨d 0 / 3, monomialIndex_lt d⟩⟩

private theorem powers_monomialIndex (d : Fin 2 →₀ ℕ) :
    (Ppowers (monomialWeight d))[d 0 / 3]'(by
      rw [Ppowers_length]; exact monomialIndex_lt d) = ![d 0, d 1] := by
  rw [Ppowers_getElem_eq _ _ (monomialIndex_lt d)]
  have hw : monomialWeight d = (d 0 * 4 + d 1 * 6 : ℕ) := by
    simp [monomialWeight]
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

private theorem eisensteinEval_monomial_one (d : Fin 2 →₀ ℕ) :
    eisensteinEval R (MvPolynomial.monomial d 1) =
      DirectSum.of (ModularFormOver R 𝒮ℒ) (monomialWeight d)
        (P (R := R) (monomialWeight d) (d 0 / 3) (monomialIndex_lt d)) := by
  rw [eisensteinEval, MvPolynomial.aeval_monomial, map_one, one_mul,
    Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Fin.prod_univ_two]
  dsimp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
  rw [of_pow, of_pow, DirectSum.of_mul_of]
  congr 1
  apply ext₂
  intro z
  change (((E₄.tower R).pow (d 0)).mul ((E₆.tower R).pow (d 1))) z = _
  simp only [mul_apply, pow_apply, tower_apply]
  change _ = ((E₄.pow _).mul (E₆.pow _)) z
  simp only [mul_apply, pow_apply]
  rw [powers_monomialIndex]
  rfl

/-- The polynomial monomial corresponding to the basis element `P k n`. -/
def PPolynomial (k : ℤ) (n : ℕ) (hn : n < dim k) : MvPolynomial (Fin 2) R :=
  let p := (Ppowers k)[n]'(by rwa [Ppowers_length])
  MvPolynomial.X 0 ^ (p 0) * MvPolynomial.X 1 ^ (p 1)

omit [Algebra R ℂ] in
/-- The polynomial corresponding to `P k n` is homogeneous of weight `k` for weights four and
six. -/
theorem PPolynomial_isWeightedHomogeneous (k : ℤ) (n : ℕ) (hn : n < dim k) :
    (PPolynomial R k n hn).IsWeightedHomogeneous eisensteinWeights k := by
  let p := (Ppowers k)[n]'(by rwa [Ppowers_length])
  have h := ((MvPolynomial.isWeightedHomogeneous_X (R := R) eisensteinWeights 0).pow
    (p 0)).mul
    ((MvPolynomial.isWeightedHomogeneous_X (R := R) eisensteinWeights 1).pow (p 1))
  have hw : (p 0 : ℤ) * 4 + p 1 * 6 = k := Ppowers_getElem_weight k n hn
  simpa [eisensteinWeights, PPolynomial, p, hw] using h

/-- Evaluating the polynomial for `P k n` gives that basis element in the weight-`k` summand. -/
@[simp] theorem eisensteinEval_PPolynomial (k : ℤ) (n : ℕ) (hn : n < dim k) :
    eisensteinEval R (PPolynomial R k n hn) =
      DirectSum.of (ModularFormOver R 𝒮ℒ) k (P (R := R) k n hn) := by
  dsimp only [PPolynomial]
  rw [map_mul, map_pow, map_pow, eisensteinEval_X_zero, eisensteinEval_X_one,
    of_pow, of_pow, DirectSum.of_mul_of]
  apply DirectSum.of_eq_of_gradedMonoid_eq
  apply gradedMonoid_eq_of_cast (by
    change _ + _ = k
    exact Ppowers_getElem_weight k n hn)
  apply ext₂
  intro z
  change ((E₄.pow _).mul (E₆.pow _)) z = ((E₄.pow _).mul (E₆.pow _)) z
  rfl

private theorem eisensteinEval_monomials_linearIndependent
    [FaithfulSMul R ℂ] [Invertible (6 : R)] :
    LinearIndependent R (fun d : Fin 2 →₀ ℕ =>
      eisensteinEval R (MvPolynomial.monomial d 1)) := by
  have h := DFinsupp.linearIndependent_single
    (fun k (n : Fin (dim k)) => P (R := R) k n.val n.isLt)
    (fun k => P_LI (R := R) k)
  have hc := h.comp monomialIndex monomialIndex_injective
  convert! hc using 1
  funext d
  exact eisensteinEval_monomial_one R d

/-- When `6` is invertible and `R` embeds faithfully in `ℂ`, evaluation at `E₄` and `E₆` is
injective. -/
theorem eisensteinEval_injective [FaithfulSMul R ℂ] [Invertible (6 : R)] :
    Function.Injective (eisensteinEval R) := by
  change Function.Injective (eisensteinEval R).toLinearMap
  refine LinearMap.injective_of_linearIndependent
    (f := (eisensteinEval R).toLinearMap)
    (MvPolynomial.basisMonomials (Fin 2) R).span_eq ?_
  convert! eisensteinEval_monomials_linearIndependent R using 1

/-- When `6` is invertible, every graded level-one form is a polynomial in `E₄` and `E₆`. -/
theorem eisensteinEval_surjective [Invertible (6 : R)] :
    Function.Surjective (eisensteinEval R) := by
  change Function.Surjective (eisensteinEval R).toLinearMap
  apply LinearMap.range_eq_top.mp
  apply top_unique
  intro f hf
  clear hf
  induction f using DirectSum.induction_on with
  | zero => exact Submodule.zero_mem _
  | of k f =>
    have hle :
        Submodule.span R {P (R := R) k n.val n.isLt | n : Fin (dim k)} ≤
          (eisensteinEval R).toLinearMap.range.comap
            (DirectSum.lof R ℤ (ModularFormOver R 𝒮ℒ) k) := by
      apply Submodule.span_le.mpr
      rintro _ ⟨n, rfl⟩
      exact ⟨PPolynomial R k n.val n.isLt, eisensteinEval_PPolynomial R k n.val n.isLt⟩
    exact hle (P_span (R := R) k (Submodule.mem_top))
  | add f g hf hg => exact Submodule.add_mem _ hf hg

/-- The graded ring of level-one modular forms is a polynomial algebra in `E₄` and `E₆`. -/
def eisensteinAlgEquiv [FaithfulSMul R ℂ] [Invertible (6 : R)] :
    MvPolynomial (Fin 2) R ≃ₐ[R] GradedRing R :=
  AlgEquiv.ofBijective (eisensteinEval R)
    ⟨eisensteinEval_injective R, eisensteinEval_surjective R⟩

/-- The polynomial presentation sends the first variable to the weight-four Eisenstein series. -/
@[simp] theorem eisensteinAlgEquiv_X_zero [FaithfulSMul R ℂ] [Invertible (6 : R)] :
    eisensteinAlgEquiv R (MvPolynomial.X 0) =
      DirectSum.of (ModularFormOver R 𝒮ℒ) 4 (E₄.tower R) :=
  eisensteinEval_X_zero R

/-- The polynomial presentation sends the second variable to the weight-six Eisenstein series. -/
@[simp] theorem eisensteinAlgEquiv_X_one [FaithfulSMul R ℂ] [Invertible (6 : R)] :
    eisensteinAlgEquiv R (MvPolynomial.X 1) =
      DirectSum.of (ModularFormOver R 𝒮ℒ) 6 (E₆.tower R) :=
  eisensteinEval_X_one R

/-- Polynomials homogeneous for the weights `deg X₀ = 4` and `deg X₁ = 6`. -/
abbrev HomogeneousPolynomial (k : ℤ) :=
  MvPolynomial.weightedHomogeneousSubmodule R eisensteinWeights k

/-- Evaluate a weighted homogeneous polynomial and take its weight-`k` component. -/
def homogeneousEval (k : ℤ) : HomogeneousPolynomial R k →ₗ[R] ModularFormOver R 𝒮ℒ k :=
  (DirectSum.component R ℤ (ModularFormOver R 𝒮ℒ) k).comp
    ((eisensteinEval R).toLinearMap.comp
      (MvPolynomial.weightedHomogeneousSubmodule R eisensteinWeights k).subtype)

/-- A polynomial homogeneous of weight `k` evaluates entirely into the weight-`k` summand. -/
theorem eisensteinEval_homogeneous (k : ℤ) (p : HomogeneousPolynomial R k) :
    DirectSum.of (ModularFormOver R 𝒮ℒ) k (homogeneousEval R k p) =
      eisensteinEval R p.val := by
  obtain ⟨p, hp⟩ := p
  change (DirectSum.lof R ℤ (ModularFormOver R 𝒮ℒ) k)
    ((DirectSum.component R ℤ (ModularFormOver R 𝒮ℒ) k) (eisensteinEval R p)) =
      eisensteinEval R p
  induction hp using MvPolynomial.IsWeightedHomogeneous.induction_on with
  | zero => simp
  | add p q hp hq ihp ihq =>
    simp only [map_add, ihp, ihq]
  | monomial d r hw =>
    have hw' : monomialWeight d = k := (weight_eq d).symm.trans hw
    have hm : MvPolynomial.monomial d r = r • MvPolynomial.monomial d (1 : R) := by
      symm
      rw [MvPolynomial.smul_monomial, smul_eq_mul, mul_one]
    rw [hm, map_smul, eisensteinEval_monomial_one]
    have hs {i : ℤ} (hi : i = k) (f : ModularFormOver R 𝒮ℒ i) :
        (DirectSum.lof R ℤ (ModularFormOver R 𝒮ℒ) k)
            ((DirectSum.component R ℤ (ModularFormOver R 𝒮ℒ) k)
              (DirectSum.of (ModularFormOver R 𝒮ℒ) i f)) =
          DirectSum.of (ModularFormOver R 𝒮ℒ) i f := by
      subst i
      exact congrArg (DirectSum.lof R ℤ (ModularFormOver R 𝒮ℒ) k)
        (DirectSum.component.lof_self (R := R) (ι := ℤ)
          (M := ModularFormOver R 𝒮ℒ) k f)
    simpa only [map_smul] using
      congrArg (fun f : GradedRing R => r • f)
        (hs hw' (P (R := R) _ _ (monomialIndex_lt d)))

/-- Evaluation on weight-`k` homogeneous polynomials is injective when `6` is invertible and `R`
acts faithfully on `ℂ`. -/
theorem homogeneousEval_injective [FaithfulSMul R ℂ] [Invertible (6 : R)] (k : ℤ) :
    Function.Injective (homogeneousEval R k) := by
  intro p q h
  apply Subtype.ext
  apply eisensteinEval_injective R
  rw [← eisensteinEval_homogeneous R k p, ← eisensteinEval_homogeneous R k q, h]

/-- When `6` is invertible, every weight-`k` form comes from a weighted homogeneous polynomial. -/
theorem homogeneousEval_surjective [Invertible (6 : R)] (k : ℤ) :
    Function.Surjective (homogeneousEval R k) := by
  apply LinearMap.range_eq_top.mp
  apply top_unique
  refine (P_span (R := R) k).trans (Submodule.span_le.mpr ?_)
  rintro _ ⟨n, rfl⟩
  refine ⟨⟨PPolynomial R k n.val n.isLt,
    PPolynomial_isWeightedHomogeneous R k n.val n.isLt⟩, ?_⟩
  change (eisensteinEval R (PPolynomial R k n.val n.isLt)) k = P k n.val n.isLt
  simp only [eisensteinEval_PPolynomial, DirectSum.of_eq_same]

/-- Weighted homogeneous polynomials of weight `k` are exactly modular forms of weight `k`. -/
def homogeneousEquiv [FaithfulSMul R ℂ] [Invertible (6 : R)] (k : ℤ) :
    HomogeneousPolynomial R k ≃ₗ[R] ModularFormOver R 𝒮ℒ k :=
  LinearEquiv.ofBijective (homogeneousEval R k)
    ⟨homogeneousEval_injective R k, homogeneousEval_surjective R k⟩

/-- The weight-`k` version of the polynomial presentation. -/
def modularFormEquivHomogeneous [FaithfulSMul R ℂ] [Invertible (6 : R)] (k : ℤ) :
    ModularFormOver R 𝒮ℒ k ≃ₗ[R] HomogeneousPolynomial R k :=
  (homogeneousEquiv R k).symm

/-- The homogeneous polynomial for `P k n` corresponds to that monomial basis element. -/
@[simp] theorem homogeneousEquiv_PPolynomial [FaithfulSMul R ℂ] [Invertible (6 : R)]
    (k : ℤ) (n : ℕ) (hn : n < dim k) :
    homogeneousEquiv R k
      ⟨PPolynomial R k n hn, PPolynomial_isWeightedHomogeneous R k n hn⟩ =
        P (R := R) k n hn := by
  change (eisensteinEval R (PPolynomial R k n hn)) k = P k n hn
  simp only [eisensteinEval_PPolynomial, DirectSum.of_eq_same]

variable {R} [FaithfulSMul R ℂ] [Invertible (6 : R)] {k j : ℤ}

/-- The polynomial in `E₄` and `E₆` representing a level-one modular form.
For a form of weight `k`, it is homogeneous of weight `k` for variable weights four and six. -/
def toPolynomial : ModularFormOver R 𝒮ℒ k →ₗ[R] MvPolynomial (Fin 2) R :=
  (MvPolynomial.weightedHomogeneousSubmodule R eisensteinWeights k).subtype.comp
    (modularFormEquivHomogeneous R k).toLinearMap

/-- The polynomial representing a weight-`k` form is weighted homogeneous of degree `k`. -/
theorem toPolynomial_isWeightedHomogeneous (f : ModularFormOver R 𝒮ℒ k) :
    f.toPolynomial.IsWeightedHomogeneous eisensteinWeights k :=
  (modularFormEquivHomogeneous R k f).property

/-- Evaluating the polynomial representation recovers the form in its weight summand. -/
@[simp] theorem eisensteinEval_toPolynomial (f : ModularFormOver R 𝒮ℒ k) :
    eisensteinEval R f.toPolynomial = DirectSum.of (ModularFormOver R 𝒮ℒ) k f := by
  have h := eisensteinEval_homogeneous R k (modularFormEquivHomogeneous R k f)
  have hf : homogeneousEval R k (modularFormEquivHomogeneous R k f) = f :=
    (homogeneousEquiv R k).apply_symm_apply f
  rw [hf] at h
  exact h.symm

/-- Taking the polynomial of an evaluated homogeneous polynomial recovers that polynomial. -/
@[simp] theorem toPolynomial_homogeneousEval (p : HomogeneousPolynomial R k) :
    (homogeneousEval R k p).toPolynomial = p.val :=
  congrArg Subtype.val ((homogeneousEquiv R k).symm_apply_apply p)

/-- Forms of a fixed weight are determined by their polynomial representations. -/
theorem toPolynomial_injective : Function.Injective (toPolynomial (R := R) (k := k)) :=
  Subtype.val_injective.comp (modularFormEquivHomogeneous R k).injective

/-- Polynomial representation respects the product of forms of possibly different weights. -/
@[simp] theorem toPolynomial_mul (f : ModularFormOver R 𝒮ℒ k)
    (g : ModularFormOver R 𝒮ℒ j) :
    (f.mul g).toPolynomial = f.toPolynomial * g.toPolynomial := by
  apply eisensteinEval_injective R
  simp only [map_mul, eisensteinEval_toPolynomial, DirectSum.of_mul_of]
  rfl

@[simp] theorem toPolynomial_E₄ : (E₄.tower R).toPolynomial = MvPolynomial.X 0 := by
  apply eisensteinEval_injective R
  rw [eisensteinEval_toPolynomial, eisensteinEval_X_zero]

@[simp] theorem toPolynomial_E₆ : (E₆.tower R).toPolynomial = MvPolynomial.X 1 := by
  apply eisensteinEval_injective R
  rw [eisensteinEval_toPolynomial, eisensteinEval_X_one]

end ModularFormOver
