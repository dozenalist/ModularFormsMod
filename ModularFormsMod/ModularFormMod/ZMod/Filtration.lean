import ModularFormsMod.ModularFormMod.Filtration
import ModularFormsMod.ModularFormMod.ZMod.HasseIdeal
import ModularFormsMod.ModularFormMod.ZMod.CoprimeAbarBbar
import ModularFormsMod.ModularFormMod.ZMod.UOperator

/-!
# Filtration, theta, and U modulo a large prime

Proposition 1.44: divisibility by the Hasse polynomial detects a drop in
filtration, and theta raises filtration by at most `p + 1`, with equality
exactly when the original filtration is not divisible by `p`.

For nonzero forms, filtration is congruent to the bundled weight modulo `p - 1`.
Filtration is multiplied by the exponent under natural powers.
Iterating theta bounds the filtration of the U operator by
`p + (f.Filtration - 1) / p`.

The strict-drop criterion is stated in positive weight so that it includes
the zero form, whose filtration in this development is zero.
-/

set_option linter.style.header false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

noncomputable section

open MatrixGroups PInteger ModularFormOver
open scoped ModularFormMod.ZMod

namespace ModularFormMod

variable {p : ℕ} [isLargePrime p] {k j : ℤ}

/-- The polynomial in the reduced Eisenstein series representing a fixed-weight form. -/
def toPolynomial (f : 𝓜 p k) : MvPolynomial (Fin 2) (ZMod p) :=
  (eisensteinAlgEquiv (reduce (p := p))).symm (DirectSum.of _ k f)

@[simp] theorem eisensteinEval_toPolynomial (f : 𝓜 p k) :
    eisensteinEval reduce f.toPolynomial = DirectSum.of _ k f :=
  (eisensteinAlgEquiv reduce).apply_symm_apply _

@[simp] theorem toPolynomial_Reduce (f : ModularFormOver ℤ(p) 𝒮ℒ k) :
    (f.Reduce reduce).toPolynomial = MvPolynomial.map reduce f.toPolynomial := by
  apply eisensteinEval_injective reduce
  rw [eisensteinEval_toPolynomial, eisensteinEval_map,
    ModularFormOver.eisensteinEval_toPolynomial, ReduceAlgHom_of]

theorem toPolynomial_isWeightedHomogeneous (f : 𝓜 p k) :
    f.toPolynomial.IsWeightedHomogeneous eisensteinWeights k := by
  obtain ⟨g, rfl⟩ := f.existsReduce
  rw [toPolynomial_Reduce]
  intro d hd
  apply ModularFormOver.toPolynomial_isWeightedHomogeneous g
  intro h
  exact hd (by simp [MvPolynomial.coeff_map, h])

@[simp] theorem eisensteinFourierEval_toPolynomial (f : 𝓜 p k) :
    eisensteinFourierEval reduce f.toPolynomial = f.fourier := by
  rw [← fourierAlgHom_comp_eisensteinEval, AlgHom.comp_apply,
    eisensteinEval_toPolynomial, fourierAlgHom_of]

@[simp] theorem toPolynomial_zero : (0 : 𝓜 p k).toPolynomial = 0 := by
  apply eisensteinEval_injective reduce
  simp

@[simp] theorem toPolynomial_cast (f : 𝓜 p k) (h : k = j) :
    (f.cast h).toPolynomial = f.toPolynomial := by
  subst j
  rfl

@[simp] theorem toPolynomial_add (f g : 𝓜 p k) :
    (f + g).toPolynomial = f.toPolynomial + g.toPolynomial := by
  apply eisensteinEval_injective reduce
  simp

@[simp] theorem toPolynomial_smul (a : ZMod p) (f : 𝓜 p k) :
    (a • f).toPolynomial = a • f.toPolynomial := by
  apply eisensteinEval_injective reduce
  simp [DirectSum.of_smul]

@[simp] theorem toPolynomial_mul (f : 𝓜 p k) (g : 𝓜 p j) :
    (f.mul g).toPolynomial = f.toPolynomial * g.toPolynomial := by
  apply eisensteinEval_injective reduce
  simp only [eisensteinEval_toPolynomial, _root_.map_mul, DirectSum.of_mul_of]
  rfl

@[simp] theorem toPolynomial_pow (f : 𝓜 p k) (m : ℕ) :
    (f.pow m).toPolynomial = f.toPolynomial ^ m := by
  induction m with
  | zero =>
    have hpow : f.pow 0 = (1 : 𝓜 p 0).cast (by simp) := by
      apply ext
      simp
    rw [hpow, toPolynomial_cast, pow_zero]
    apply eisensteinEval_injective reduce
    rw [eisensteinEval_toPolynomial, _root_.map_one (eisensteinEval reduce)]
    rfl
  | succ m ih =>
    have hpow : f.pow (m + 1) = ((f.pow m).mul f).cast (by push_cast; ring) := by
      apply ext
      simp [pow_succ]
    rw [hpow, toPolynomial_cast, toPolynomial_mul, ih, pow_succ]

private theorem exists_toPolynomial
    (F : MvPolynomial (Fin 2) (ZMod p))
    (hF : F.IsWeightedHomogeneous eisensteinWeights k) :
    ∃ f : 𝓜 p k, f.toPolynomial = F := by
  obtain ⟨G, hG⟩ := MvPolynomial.map_surjective
    (reduce (p := p)) (ZMod.ringHom_surjective reduce) F
  let H := MvPolynomial.weightedHomogeneousComponent eisensteinWeights k G
  have hH : MvPolynomial.map reduce H = F := by
    ext d
    simp only [H, MvPolynomial.coeff_map, MvPolynomial.coeff_weightedHomogeneousComponent]
    by_cases hd : Finsupp.weight eisensteinWeights d = k
    · simpa [hd, MvPolynomial.coeff_map] using
        congrArg (fun P : MvPolynomial (Fin 2) (ZMod p) => P.coeff d) hG
    · simp [hd, hF.coeff_eq_zero d hd]
  let g := homogeneousEval ℤ(p) k
    ⟨H, MvPolynomial.weightedHomogeneousComponent_isWeightedHomogeneous k G⟩
  refine ⟨g.Reduce reduce, ?_⟩
  rw [toPolynomial_Reduce]
  exact (congrArg (MvPolynomial.map reduce)
    (toPolynomial_homogeneousEval _)).trans hH

private theorem component_mul_left
    {F : MvPolynomial (Fin 2) (ZMod p)}
    (hF : F.IsWeightedHomogeneous eisensteinWeights j)
    (G : MvPolynomial (Fin 2) (ZMod p)) (n : ℤ) :
    MvPolynomial.weightedHomogeneousComponent eisensteinWeights n (F * G) =
      F * MvPolynomial.weightedHomogeneousComponent eisensteinWeights (n - j) G := by
  let := MvPolynomial.weightedGradedAlgebra (ZMod p) eisensteinWeights
  have h := DirectSum.coe_decompose_mul_add_of_left_mem
    (MvPolynomial.weightedHomogeneousSubmodule (ZMod p) eisensteinWeights)
    (j := n - j) hF (b := G)
  have hc (P : MvPolynomial (Fin 2) (ZMod p)) (m : ℤ) :
      (DirectSum.decompose
        (MvPolynomial.weightedHomogeneousSubmodule (ZMod p) eisensteinWeights) P m :
          MvPolynomial (Fin 2) (ZMod p)) =
        MvPolynomial.weightedHomogeneousComponent eisensteinWeights m P :=
    MvPolynomial.weightedDecomposition.decompose'_apply _ _ P m
  rw [hc, hc] at h
  simpa only [show j + (n - j) = n by omega] using h

private theorem Abar_dvd_of_lower_weight
    {F G : MvPolynomial (Fin 2) (ZMod p)}
    (hF : F.IsWeightedHomogeneous eisensteinWeights k)
    (hG : G.IsWeightedHomogeneous eisensteinWeights j)
    (hjk : j < k)
    (h : eisensteinFourierEval reduce F = eisensteinFourierEval reduce G) :
    ZMod.Abar p ∣ F := by
  classical
  have hp : 5 ≤ p := isLargePrime.AtLeastFive
  have hmem : F - G ∈ ZMod.hasseIdeal p := by
    change eisensteinFourierEval reduce (F - G) = 0
    rw [_root_.map_sub, h, sub_self]
  rw [ZMod.hasseIdeal_eq_span, Ideal.mem_span_singleton] at hmem
  obtain ⟨Q, hQ⟩ := hmem
  have hQk : MvPolynomial.weightedHomogeneousComponent eisensteinWeights k Q = 0 := by
    by_cases hQ0 : Q = 0
    · simp [hQ0]
    obtain ⟨d, hd, hmax⟩ := Finset.exists_max_image Q.support
      (Finsupp.weight eisensteinWeights) (by simpa using hQ0)
    let n := Finsupp.weight eisensteinWeights d
    have htop : MvPolynomial.weightedHomogeneousComponent eisensteinWeights n Q ≠ 0 := by
      intro hz
      have hc := congrArg (fun P : MvPolynomial (Fin 2) (ZMod p) => P.coeff d) hz
      simp only [MvPolynomial.coeff_weightedHomogeneousComponent, n, ite_true,
        AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply] at hc
      exact (MvPolynomial.mem_support_iff.mp hd) hc
    have habove (m : ℤ) (hm : n < m) :
        MvPolynomial.weightedHomogeneousComponent eisensteinWeights m Q = 0 :=
      MvPolynomial.weightedHomogeneousComponent_eq_zero' m Q
        (fun e he => ne_of_lt ((hmax e he).trans_lt hm))
    have hnk : n < k := by
      by_contra hnk
      have he := congrArg
        (MvPolynomial.weightedHomogeneousComponent eisensteinWeights (n + (p - 1 : ℤ))) hQ
      rw [_root_.map_sub, sub_mul, one_mul, _root_.map_sub,
        component_mul_left (ZMod.Abar_isWeightedHomogeneous p),
        show n + (p - 1 : ℤ) - (p - 1 : ℤ) = n by omega,
        habove (n + (p - 1 : ℤ)) (by omega),
        hF.weightedHomogeneousComponent_ne (n + (p - 1 : ℤ)) (by omega),
        hG.weightedHomogeneousComponent_ne (n + (p - 1 : ℤ)) (by omega)] at he
      have : ZMod.Abar p *
          MvPolynomial.weightedHomogeneousComponent eisensteinWeights n Q = 0 := by
        simpa using he.symm
      exact (mul_ne_zero (ZMod.Abar_ne_zero p) htop) this
    exact habove k hnk
  have he := congrArg (MvPolynomial.weightedHomogeneousComponent eisensteinWeights k) hQ
  rw [_root_.map_sub, hF.weightedHomogeneousComponent_same,
    hG.weightedHomogeneousComponent_ne _ (by omega), sub_zero,
    sub_mul, one_mul, _root_.map_sub,
    component_mul_left (ZMod.Abar_isWeightedHomogeneous p), hQk, sub_zero] at he
  exact ⟨_, he⟩

private theorem hasWeight_of_Abar_dvd (f : 𝓜 p k)
    (h : ZMod.Abar p ∣ f.toPolynomial) : f.hasWeight (k - (p - 1 : ℤ)) := by
  obtain ⟨Q, hQ⟩ := h
  let H := MvPolynomial.weightedHomogeneousComponent eisensteinWeights (k - (p - 1 : ℤ)) Q
  have hF : f.toPolynomial = ZMod.Abar p * H := by
    rw [← f.toPolynomial_isWeightedHomogeneous.weightedHomogeneousComponent_same, hQ,
      component_mul_left (ZMod.Abar_isWeightedHomogeneous p)]
  obtain ⟨g, hg⟩ := exists_toPolynomial H
    (MvPolynomial.weightedHomogeneousComponent_isWeightedHomogeneous _ _)
  have hfg : f.fourier = g.fourier := by
    rw [← eisensteinFourierEval_toPolynomial f, hF, _root_.map_mul,
      ZMod.eisensteinFourierEval_Abar, one_mul, ← hg,
      eisensteinFourierEval_toPolynomial]
  exact (hasWeight_ext hfg _).mpr g.hasWeight_self

/-- Proposition 1.44 (1), including the zero form in every positive weight. -/
theorem Filtration_lt_iff_Abar_dvd (f : 𝓜 p k) (hk : 0 < k) :
    f.Filtration < k ↔ ZMod.Abar p ∣ f.toPolynomial := by
  by_cases hf : f = 0
  · simp [hf, hk]
  let : NeZero f := ⟨hf⟩
  constructor
  · intro hlt
    let g := f.Filtration_choose.Reduce reduce
    apply Abar_dvd_of_lower_weight f.toPolynomial_isWeightedHomogeneous
      g.toPolynomial_isWeightedHomogeneous hlt
    simpa only [eisensteinFourierEval_toPolynomial, g, Reduce_fourier] using
      f.Filtration_choose_spec
  · intro hdiv
    have hw := hasWeight_of_Abar_dvd f hdiv
    have hp : 5 ≤ p := isLargePrime.AtLeastFive
    exact (Filtration_le hw).trans_lt (by omega)

/-- The filtration of a nonzero form is congruent to its weight modulo `p - 1`. -/
theorem Filtration_congr (f : 𝓜 p k) (hf : f ≠ 0) :
    f.Filtration ≡ k [ZMOD (p - 1 : ℤ)] := by
  induction hn : k.toNat using Nat.strong_induction_on generalizing k with
  | h n ih =>
    have hle := Filtration_le_of_nonneg f.hasWeight_self (f.hasWeight_self.nonneg hf)
    by_cases heq : f.Filtration = k
    · rw [heq]
    have hlt : f.Filtration < k := lt_of_le_of_ne hle heq
    have hk : 0 < k := f.Filtration_nonneg.trans_lt hlt
    obtain ⟨g, hg⟩ := (hasWeight_of_Abar_dvd f
      ((Filtration_lt_iff_Abar_dvd f hk).mp hlt)).exists
    have hfg : f.fourier = g.fourier := PowerSeries.ext hg
    have hg0 : g ≠ 0 := by
      intro h
      apply hf
      apply ext
      simpa [h] using hfg
    have hsmall : (k - (p - 1 : ℤ)).toNat < n := by
      have hp : 5 ≤ p := isLargePrime.AtLeastFive
      omega
    rw [Filtration_eq_of_fourier_eq hfg]
    exact Int.modEq_sub_modulus_iff.mp (ih _ hsmall g hg0 rfl)

/-- At level one modulo a large prime, filtration is bounded under addition. -/
theorem Filtration_add_le (f g : 𝓜 p k) :
    (f + g).Filtration ≤ max f.Filtration g.Filtration := by
  induction hn : k.toNat using Nat.strong_induction_on generalizing k with
  | h n ih =>
    by_cases hf : f = 0
    · rw [hf, zero_add, Filtration_zero]
      exact le_max_right _ _
    by_cases hle : k ≤ max f.Filtration g.Filtration
    · exact (Filtration_le_of_nonneg (f + g).hasWeight_self
        (f.hasWeight_self.nonneg hf)).trans hle
    have hfk : f.Filtration < k := (le_max_left _ _).trans_lt (lt_of_not_ge hle)
    have hgk : g.Filtration < k := (le_max_right _ _).trans_lt (lt_of_not_ge hle)
    have hk : 0 < k := f.Filtration_nonneg.trans_lt hfk
    obtain ⟨f', hf'⟩ := (hasWeight_of_Abar_dvd f
      ((Filtration_lt_iff_Abar_dvd f hk).mp hfk)).exists
    obtain ⟨g', hg'⟩ := (hasWeight_of_Abar_dvd g
      ((Filtration_lt_iff_Abar_dvd g hk).mp hgk)).exists
    have hff' : f.fourier = f'.fourier := PowerSeries.ext hf'
    have hgg' : g.fourier = g'.fourier := PowerSeries.ext hg'
    have hsmall : (k - (p - 1 : ℤ)).toNat < n := by
      have hp : 5 ≤ p := isLargePrime.AtLeastFive
      omega
    calc
      (f + g).Filtration = (f' + g').Filtration :=
        Filtration_eq_of_fourier_eq (by simp only [add_fourier, hff', hgg'])
      _ ≤ max f'.Filtration g'.Filtration := ih _ hsmall f' g' rfl
      _ = max f.Filtration g.Filtration := by
        rw [← Filtration_eq_of_fourier_eq hff', ← Filtration_eq_of_fourier_eq hgg']

/-- At level one modulo a large prime, filtration is bounded under subtraction. -/
theorem Filtration_sub_le (f g : 𝓜 p k) :
    (f - g).Filtration ≤ max f.Filtration g.Filtration := by
  simpa only [sub_eq_add_neg, Filtration_neg] using Filtration_add_le f (-g)

/-- Taking a natural power multiplies the filtration by the exponent. -/
@[simp] theorem Filtration_pow (f : 𝓜 p k) (m : ℕ) :
    (f.pow m).Filtration = m * f.Filtration := by
  apply le_antisymm (Filtration_pow_le f m)
  by_contra h
  have hlt : (f.pow m).Filtration < m * f.Filtration := lt_of_not_ge h
  have hpos : 0 < (m : ℤ) * f.Filtration := (f.pow m).Filtration_nonneg.trans_lt hlt
  have hm : m ≠ 0 := by
    intro hm
    simp [hm] at hpos
  have hfpos : 0 < f.Filtration := by
    by_contra hfpos
    have hfzero : f.Filtration = 0 := le_antisymm (le_of_not_gt hfpos) f.Filtration_nonneg
    simp [hfzero] at hpos
  let g := f.Filtration_choose.Reduce reduce
  have hfg : f.fourier = g.fourier := f.Filtration_choose_spec
  have hfil : g.Filtration = f.Filtration := (Filtration_eq_of_fourier_eq hfg).symm
  have hpowfil : (g.pow m).Filtration = (f.pow m).Filtration :=
    Filtration_eq_of_fourier_eq (by simp only [pow_fourier, hfg])
  have hdiv : ZMod.Abar p ∣ g.toPolynomial ^ m := by
    rw [← toPolynomial_pow]
    apply (Filtration_lt_iff_Abar_dvd (g.pow m) hpos).mp
    simpa only [hpowfil] using hlt
  have hgdiv := ((ZMod.squarefree_Abar p).dvd_pow_iff_dvd hm).mp hdiv
  have hdrop := (Filtration_lt_iff_Abar_dvd g hfpos).mpr hgdiv
  rw [hfil] at hdrop
  exact (lt_irrefl _ hdrop)

/-- Proposition 1.44 (2): theta raises filtration by at most `p + 1`. -/
theorem Filtration_Theta_le (f : 𝓜 p k) :
    f.Theta.Filtration ≤ f.Filtration + (p + 1) := by
  let g := f.Filtration_choose.Reduce reduce
  have hfg : f.Theta.fourier = g.Theta.fourier := by
    rw [Theta_fourier, Theta_fourier, f.Filtration_choose_spec]
    rfl
  apply Filtration_le_of_nonneg ((hasWeight_ext hfg _).mpr g.Theta.hasWeight_self)
  have := f.Filtration_nonneg
  have := Nat.zero_le p
  omega

private theorem twelve_smul_Theta_toPolynomial (f : 𝓜 p k) :
    (12 : ZMod p) • f.Theta.toPolynomial =
      ZMod.Abar p * (normalizedSerreDerivative f).toPolynomial +
        (k : ZMod p) • (ZMod.Bbar p * f.toPolynomial) := by
  have h : (12 : ZMod p) • f.Theta =
      (((Esubone p).Reduce reduce).mul (normalizedSerreDerivative f)).cast (by omega) +
        (k : ZMod p) • (((Eaddone p).Reduce reduce).mul f).cast (by omega) := by
    apply ext
    have hp : 5 ≤ p := isLargePrime.AtLeastFive
    simp only [smul_fourier_of_surjective, Theta_fourier, add_fourier, cast_fourier,
      mul_fourier, Reduce_Esubone, Reduce_Eaddone p (by omega),
      normalizedSerreDerivative_fourier, normalizedSerreFourier,
      cuspWidth_SL2Z, Nat.cast_one, mul_one, e2FourierAt_SL2Z, one_mul,
      PowerSeries.smul_eq_C_mul]
    ring
  simpa only [toPolynomial_smul, toPolynomial_add, toPolynomial_cast, toPolynomial_mul,
    toPolynomial_Reduce, ZMod.Abar, ZMod.A, ZMod.Bbar, ZMod.B] using
      congrArg toPolynomial h

private theorem Abar_dvd_Theta_iff (f : 𝓜 p k)
    (hf : ¬ ZMod.Abar p ∣ f.toPolynomial) :
    ZMod.Abar p ∣ f.Theta.toPolynomial ↔ (k : ZMod p) = 0 := by
  have hp : 5 ≤ p := isLargePrime.AtLeastFive
  have h12 : (12 : ZMod p) ≠ 0 := by
    intro h
    have hd := (ZMod.natCast_eq_zero_iff 12 p).mp h
    have hprime : p.Prime := Fact.out
    rcases hprime.dvd_mul.mp (show p ∣ 4 * 3 from hd) with h4 | h3
    · have h2 := hprime.dvd_of_dvd_pow (show p ∣ 2 ^ 2 from h4)
      have := Nat.le_of_dvd (by decide : 0 < 2) h2
      omega
    · have := Nat.le_of_dvd (by decide : 0 < 3) h3
      omega
  have hunit12 : IsUnit (MvPolynomial.C (12 : ZMod p) : MvPolynomial (Fin 2) (ZMod p)) :=
    (isUnit_iff_ne_zero.mpr h12).map MvPolynomial.C
  have hformula := twelve_smul_Theta_toPolynomial f
  simp only [Algebra.smul_def, MvPolynomial.algebraMap_eq] at hformula
  constructor
  · intro hdiv
    by_contra hk
    have hdiv' : ZMod.Abar p ∣ MvPolynomial.C (k : ZMod p) *
        (ZMod.Bbar p * f.toPolynomial) := by
      have h := (dvd_mul_of_dvd_right hdiv (MvPolynomial.C (12 : ZMod p))).sub
        (dvd_mul_right (ZMod.Abar p) (normalizedSerreDerivative f).toPolynomial)
      rw [hformula, add_sub_cancel_left] at h
      exact h
    have hunit : IsUnit (MvPolynomial.C (k : ZMod p) : MvPolynomial (Fin 2) (ZMod p)) :=
      (isUnit_iff_ne_zero.mpr hk).map MvPolynomial.C
    exact hf ((ZMod.isRelPrime_Abar_Bbar p).dvd_of_dvd_mul_left
      (hunit.dvd_mul_left.mp hdiv'))
  · intro hk
    have hdiv : ZMod.Abar p ∣ MvPolynomial.C (12 : ZMod p) * f.Theta.toPolynomial := by
      rw [hformula, hk]
      simp
    exact hunit12.dvd_mul_left.mp hdiv

/-- Proposition 1.44 (2): equality holds exactly away from filtration divisible by `p`.
No nonvanishing hypothesis is needed, since the filtration of zero is zero. -/
theorem Filtration_Theta_iff (f : 𝓜 p k) :
    f.Theta.Filtration = f.Filtration + (p + 1) ↔ ¬ ↑p ∣ f.Filtration := by
  by_cases hf : f = 0
  · simp [hf]
    omega
  let g := f.Filtration_choose.Reduce reduce
  have hfg : f.fourier = g.fourier := f.Filtration_choose_spec
  have hg0 : g ≠ 0 := by
    intro hg
    apply hf
    apply ext
    simpa [hg] using hfg
  let : NeZero g := ⟨hg0⟩
  have hfil : g.Filtration = f.Filtration := (Filtration_eq_of_fourier_eq hfg).symm
  have hTheta : f.Theta.Filtration = g.Theta.Filtration :=
    Filtration_eq_of_fourier_eq (by rw [Theta_fourier, Theta_fourier, hfg])
  have hnot : ¬ ZMod.Abar p ∣ g.toPolynomial := by
    intro hdiv
    have hle := Filtration_le (hasWeight_of_Abar_dvd g hdiv)
    rw [hfil] at hle
    have hp : 5 ≤ p := isLargePrime.AtLeastFive
    omega
  have hpos : 0 < f.Filtration + (p + 1 : ℤ) := by
    have := f.Filtration_nonneg
    omega
  have hdrop : g.Theta.Filtration < f.Filtration + (p + 1) ↔ (p : ℤ) ∣ f.Filtration := by
    rw [Filtration_lt_iff_Abar_dvd g.Theta hpos, Abar_dvd_Theta_iff g hnot,
      ZMod.intCast_zmod_eq_zero_iff_dvd]
  have hle := f.Filtration_Theta_le
  rw [hTheta] at hle ⊢
  constructor
  · intro heq hdiv
    have := hdrop.mpr hdiv
    omega
  · intro hdiv
    have := mt hdrop.mp hdiv
    omega

/-- Iterating theta raises filtration by at most `m * (p + 1)`. -/
theorem Filtration_Theta_pow_le (f : 𝓜 p k) (m : ℕ) :
    (f.Theta_pow m).Filtration ≤ f.Filtration + m * (p + 1) := by
  induction m with
  | zero => simp [Theta_pow]
  | succ m ih =>
    rw [Theta_pow, Filtration_cast]
    calc
      (f.Theta_pow m).Theta.Filtration ≤ (f.Theta_pow m).Filtration + (p + 1) :=
        Filtration_Theta_le _
      _ ≤ (f.Filtration + m * (p + 1)) + (p + 1) := add_le_add ih le_rfl
      _ = f.Filtration + (m + 1 : ℕ) * (p + 1) := by push_cast; ring

/-- The `(p - 1)`-st theta iterate raises filtration by at most `p² - 1`. -/
theorem Filtration_Theta_pow_card_sub_one_le (f : 𝓜 p k) :
    (f.Theta_pow (p - 1)).Filtration ≤ f.Filtration + (p : ℤ) ^ 2 - 1 := by
  have hp : 1 ≤ p := by
    have hp : 5 ≤ p := isLargePrime.AtLeastFive
    omega
  convert Filtration_Theta_pow_le f (p - 1) using 1
  rw [Nat.cast_sub hp, Nat.cast_one]
  ring

/-- The `p`-th power of `f.UOp` has filtration at most `f.Filtration + p² - 1`. -/
theorem Filtration_UOp_pow_card_le (f : 𝓜 p k) :
    (f.UOp.pow p).Filtration ≤ f.Filtration + (p : ℤ) ^ 2 - 1 := by
  have hp : 1 ≤ p := by
    have hp : 5 ≤ p := isLargePrime.AtLeastFive
    omega
  let g : 𝓜 p (k + (p - 1 : ℕ) * (p + 1)) :=
    (f.mul (((Esubone p).Reduce reduce).pow (p + 1))).cast (by
      simp only [Nat.cast_add, Nat.cast_sub hp, Nat.cast_one]
      ring)
  have hg : g.fourier = f.fourier := by
    simp only [g, cast_fourier, mul_fourier, pow_fourier, Reduce_Esubone,
      one_pow, mul_one]
  have hpow : (f.UOp.pow p).Filtration = (g - f.Theta_pow (p - 1)).Filtration :=
    Filtration_eq_of_fourier_eq (by rw [UOp_pow_card, sub_fourier, hg])
  rw [hpow]
  refine (Filtration_sub_le g _).trans ?_
  rw [Filtration_eq_of_fourier_eq hg]
  apply max_le
  · have hp' : (1 : ℤ) ≤ p := by exact_mod_cast hp
    nlinarith
  · exact Filtration_Theta_pow_card_sub_one_le f

/-- The U operator has filtration at most `p + (f.Filtration - 1) / p`. -/
theorem Filtration_UOp_le (f : 𝓜 p k) :
    f.UOp.Filtration ≤ p + (f.Filtration - 1) / p := by
  have hp : (0 : ℤ) < p := by
    have hp : 5 ≤ p := isLargePrime.AtLeastFive
    omega
  calc
    f.UOp.Filtration ≤ (f.Filtration + (p : ℤ) ^ 2 - 1) / p := by
      apply (Int.le_ediv_iff_mul_le hp).2
      simpa only [Filtration_pow, mul_comm] using Filtration_UOp_pow_card_le f
    _ = p + (f.Filtration - 1) / p := by
      rw [show f.Filtration + (p : ℤ) ^ 2 - 1 =
        (f.Filtration - 1) + (p : ℤ) * p by ring,
        Int.add_mul_ediv_right _ _ hp.ne.symm, add_comm]

end ModularFormMod
