import ModularFormsMod.ModularFormMod.Del
import ModularFormsMod.ModularFormMod.GradedRing
import ModularFormsMod.ModularFormMod.Derivative
import ModularFormsMod.ModularFormMod.ZMod.Basic

/-!
# The Eisenstein polynomials modulo a large prime

The polynomials `A` and `B` represent `E_{p-1}` and `E_{p+1}` over `ℤ(p)`.
Lemma 1.39 identifies the reductions of `Del A` and `Del B` with `Bbar` and `-X₀ Abar`.
The proof first compares Fourier expansions, then uses injectivity in a fixed weight.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

noncomputable section

open MatrixGroups PInteger
open scoped DirectSum Manifold

namespace ModularFormMod.ZMod

open ModularFormOver

private theorem e2_ramanujan_complex :
    (12 : ℂ) • (PowerSeries.X * (e2Fourier ℂ).derivative) - (e2Fourier ℂ) ^ 2 =
      -fourier ℂ (E₄.tower ℂ) := by
  have hperiod : (1 : ℝ) ∈ (𝒮ℒ).strictPeriods := by
    simpa only [Subgroup.strictWidthInfty_SL2Z] using
      (𝒮ℒ).strictWidthInfty_mem_strictPeriods
  have hE2 := UpperHalfPlane.analyticAt_cuspFunction_zero (by norm_num : (0 : ℝ) < 1)
    EisensteinSeries.E2_periodic E2_mdifferentiable EisensteinSeries.isBoundedAtImInfty_E2
  have hE4 := ModularFormClass.analyticAt_cuspFunction_zero ModularForm.E₄
    (by norm_num : (0 : ℝ) < 1) hperiod
  have hsq : AnalyticAt ℂ
      (UpperHalfPlane.cuspFunction 1 (EisensteinSeries.E2 ^ 2)) 0 := by
    rw [pow_two, UpperHalfPlane.cuspFunction_mul hE2.continuousAt hE2.continuousAt]
    exact hE2.mul hE2
  have hsub : AnalyticAt ℂ (UpperHalfPlane.cuspFunction 1
      (EisensteinSeries.E2 ^ 2 - ⇑ModularForm.E₄)) 0 := by
    rw [UpperHalfPlane.cuspFunction_sub hsq.continuousAt hE4.continuousAt]
    exact hsq.sub hE4
  have hd := qExpansion_normalizedDeriv EisensteinSeries.E2 E2_mdifferentiable
    EisensteinSeries.isBoundedAtImInfty_E2 (h := 1) (by norm_num)
    EisensteinSeries.E2_periodic
  simp only [Complex.ofReal_one, one_smul, qExpansion_E2] at hd
  rw [Derivative.normalizedDerivOfComplex_E₂,
    UpperHalfPlane.qExpansion_smul hsub, UpperHalfPlane.qExpansion_sub hsq hE4] at hd
  have hqsq : UpperHalfPlane.qExpansion 1 (EisensteinSeries.E2 ^ 2) =
      (e2Fourier ℂ) ^ 2 := by
    simpa only [pow_two, qExpansion_E2] using UpperHalfPlane.qExpansion_mul hE2 hE2
  have hq4 : UpperHalfPlane.qExpansion 1 (⇑ModularForm.E₄) = fourier ℂ (E₄.tower ℂ) := by
    rw [fourierℂ, qExp_SL2Z]
    rfl
  rw [hqsq, hq4] at hd
  have hd12 := congrArg (fun F : PowerSeries ℂ => (12 : ℂ) • F) hd
  norm_num [smul_smul] at hd12
  rw [← hd12, fourierℂ]
  abel

private theorem e2_ramanujan (R : Type) [CommRing R] [Algebra R ℂ] [FaithfulSMul R ℂ] :
    (12 : R) • (PowerSeries.X * (e2Fourier R).derivative) - (e2Fourier R) ^ 2 =
      -fourier R (E₄.tower R) := by
  apply PowerSeries.map_injective (algebraMap R ℂ) (FaithfulSMul.algebraMap_injective R ℂ)
  have hq4 : ModularForm.qExp (E₄.tower R) = ModularForm.qExp (E₄.tower ℂ) := by
    rw [qExp_SL2Z, qExp_SL2Z]
    congr 1
  simpa only [PowerSeries.smul_eq_C_mul, _root_.map_sub, _root_.map_mul,
    PowerSeries.map_C, _root_.map_ofNat, PowerSeries.map_X, _root_.map_pow,
    _root_.map_neg, ModularFormMod.map_derivative,
    ModularFormMod.map_e2Fourier, ModularFormOver.map_fourier,
    ModularFormOver.fourierℂ, hq4] using e2_ramanujan_complex

variable (p : ℕ) [isLargePrime p]

/-- The polynomial representing the Eisenstein series of weight `p - 1`. -/
def A : MvPolynomial (Fin 2) ℤ(p) := (Esubone p).toPolynomial

/-- The polynomial representing the Eisenstein series of weight `p + 1`. -/
def B : MvPolynomial (Fin 2) ℤ(p) := (Eaddone p).toPolynomial

/-- Coefficientwise reduction of `A` modulo `p`. -/
def Abar : MvPolynomial (Fin 2) (ZMod p) := MvPolynomial.map PInteger.reduce (A p)

/-- Coefficientwise reduction of `B` modulo `p`. -/
def Bbar : MvPolynomial (Fin 2) (ZMod p) := MvPolynomial.map PInteger.reduce (B p)

theorem A_isWeightedHomogeneous : (A p).IsWeightedHomogeneous eisensteinWeights (p - 1 : ℤ) :=
  toPolynomial_isWeightedHomogeneous (Esubone p)

theorem B_isWeightedHomogeneous : (B p).IsWeightedHomogeneous eisensteinWeights (p + 1 : ℤ) :=
  toPolynomial_isWeightedHomogeneous (Eaddone p)

private theorem map_toPolynomial_eq_of_fourier_eq {k j : ℤ}
    (f : ModularFormOver ℤ(p) 𝒮ℒ k) (g : ModularFormOver ℤ(p) 𝒮ℒ j) (hk : k = j)
    (h : (f.Reduce PInteger.reduce).fourier = (g.Reduce PInteger.reduce).fourier) :
    MvPolynomial.map PInteger.reduce f.toPolynomial =
      MvPolynomial.map PInteger.reduce g.toPolynomial := by
  subst j
  apply ModularFormMod.eisensteinEval_injective PInteger.reduce
  rw [ModularFormMod.eisensteinEval_map, ModularFormMod.eisensteinEval_map,
    ModularFormOver.eisensteinEval_toPolynomial, ModularFormOver.eisensteinEval_toPolynomial,
    ModularFormOver.ReduceAlgHom_of, ModularFormOver.ReduceAlgHom_of]
  congr 1
  exact ModularFormMod.ext h

/-- Lemma 1.39, first identity: reduce the derivative of `A` to obtain `Bbar`. -/
@[simp] theorem reduce_Del_A :
    MvPolynomial.map PInteger.reduce (MvPolynomial.Del (A p)) = Bbar p := by
  have hp : 5 ≤ p := isLargePrime.AtLeastFive
  have h : ((ModularFormOver.normalizedSerreDerivative ℤ(p) (Esubone p)).Reduce
      PInteger.reduce).fourier = ((Eaddone p).Reduce PInteger.reduce).fourier := by
    rw [← ModularFormMod.normalizedSerreDerivative_Reduce,
      ModularFormMod.normalizedSerreDerivative_fourier, ModularFormMod.normalizedSerreFourier,
      ModularFormMod.Reduce_Esubone, ModularFormMod.Reduce_Eaddone p (by omega)]
    simp [cuspWidth_SL2Z, e2FourierAt_SL2Z, Int.cast_sub]
  change MvPolynomial.map PInteger.reduce (MvPolynomial.Del (Esubone p).toPolynomial) =
    MvPolynomial.map PInteger.reduce (Eaddone p).toPolynomial
  rw [← toPolynomial_normalizedSerreDerivative]
  exact map_toPolynomial_eq_of_fourier_eq p _ _ (by omega) h

/-- Lemma 1.39, second identity, as established in the PDF's proof: the reduction of `Del B`
is `-X₀ Abar`. The displayed statement of the lemma has an extra derivative on `A`. -/
@[simp] theorem reduce_Del_B :
    MvPolynomial.map PInteger.reduce (MvPolynomial.Del (B p)) =
      -MvPolynomial.X 0 * Abar p := by
  have hp : 5 ≤ p := isLargePrime.AtLeastFive
  let g := -((E₄.tower ℤ(p)).mul (Esubone p))
  have hRam := congrArg (PowerSeries.map (PInteger.reduce (p := p))) (e2_ramanujan ℤ(p))
  have hA : PowerSeries.map (PInteger.reduce (p := p)) (fourier ℤ(p) (Esubone p)) = 1 :=
    ModularFormMod.Reduce_Esubone p
  have hX : (E₄.tower ℤ(p)).toPolynomial = MvPolynomial.X 0 :=
    ModularFormOver.toPolynomial_E₄
  have h : ((ModularFormOver.normalizedSerreDerivative ℤ(p) (Eaddone p)).Reduce
      PInteger.reduce).fourier = (g.Reduce PInteger.reduce).fourier := by
    rw [← ModularFormMod.normalizedSerreDerivative_Reduce,
      ModularFormMod.normalizedSerreDerivative_fourier, ModularFormMod.normalizedSerreFourier,
      ModularFormMod.Reduce_Eaddone p (by omega)]
    convert hRam using 1
    · simp [PowerSeries.smul_eq_C_mul, cuspWidth_SL2Z, e2FourierAt_SL2Z,
        Int.cast_add, ModularFormMod.map_derivative, ModularFormMod.map_e2Fourier,
        _root_.map_ofNat, pow_two]
    · simp only [g, ModularFormOver.Reduce_fourier, ModularFormOver.fourier_neg,
        ModularFormOver.fourier_mul, _root_.map_neg, _root_.map_mul, hA, mul_one]
      congr!
      exact Subsingleton.elim _ _
  have hpoly := map_toPolynomial_eq_of_fourier_eq p
    (ModularFormOver.normalizedSerreDerivative ℤ(p) (Eaddone p)) g (by omega) h
  dsimp only [g] at hpoly
  rw [_root_.map_neg, toPolynomial_mul, hX] at hpoly
  simpa [g, Abar, A, B, toPolynomial_normalizedSerreDerivative,
    toPolynomial_mul, toPolynomial_E₄] using hpoly


end ModularFormMod.ZMod

scoped[ModularFormMod.ZMod] notation "A" p:max => ModularFormMod.ZMod.A p
scoped[ModularFormMod.ZMod] notation "B" p:max => ModularFormMod.ZMod.B p
scoped[ModularFormMod.ZMod] notation "Abar" p:max => ModularFormMod.ZMod.Abar p
scoped[ModularFormMod.ZMod] notation "Bbar" p:max => ModularFormMod.ZMod.Bbar p
