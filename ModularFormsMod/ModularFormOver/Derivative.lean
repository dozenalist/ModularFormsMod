import ModularFormsMod.ModularFormOver.Basic
import Mathlib.NumberTheory.ModularForms.Derivative
import Mathlib.NumberTheory.ModularForms.EisensteinSeries.QExpansion
import Mathlib.RingTheory.PowerSeries.Expand

/-!
# Normalized Serre derivative over a coefficient ring

At infinity, let `h = Γ.strictWidthInfty`. The operator is scaled by `12 h`, so it
preserves arbitrary coefficient rings without inverting either 12 or the cusp width.
In the parameter `q = exp (2 π i τ / h)`, its Fourier expansion is
`12 X f' - k h E₂(X^h) f`. At width one this is the usual 12-scaled Serre derivative.
-/

open UpperHalfPlane ModularForm
open Real Complex
open scoped MatrixGroups Topology

namespace ModularFormOver

variable {Γ : Subgroup (GL (Fin 2) ℝ)} {k : ℤ}

/-- The strict width at infinity, as a natural number. -/
noncomputable def cuspWidth (Γ : Subgroup (GL (Fin 2) ℝ)) : ℕ :=
  Nat.ceil Γ.strictWidthInfty

theorem cuspWidth_cast [hΓ : Γ.le_SL2Z] :
    (cuspWidth Γ : ℝ) = Γ.strictWidthInfty := by
  have hm : Γ.strictWidthInfty ∈ (𝒮ℒ).strictPeriods := by
    rw [Subgroup.mem_strictPeriods_iff]
    exact hΓ.le (Subgroup.mem_strictPeriods_iff.mp Γ.strictWidthInfty_mem_strictPeriods)
  rw [Subgroup.strictPeriods_SL2Z, AddSubgroup.mem_zmultiples_iff] at hm
  obtain ⟨z, hz⟩ := hm
  simp only [zsmul_eq_mul, mul_one] at hz
  have hz0 : 0 ≤ z := by
    exact_mod_cast (hz.symm ▸ Γ.strictWidthInfty_nonneg)
  have hn : (z.toNat : ℝ) = Γ.strictWidthInfty := by
    have hc : (z.toNat : ℝ) = (z : ℝ) := by
      exact_mod_cast Int.toNat_of_nonneg hz0
    exact hc.trans hz
  rw [cuspWidth, ← hn, Nat.ceil_natCast]

theorem cuspWidth_pos [Γ.le_SL2Z] [Γ.IsArithmetic] : 0 < cuspWidth Γ := by
  exact_mod_cast (cuspWidth_cast (Γ := Γ)).symm ▸ Γ.strictWidthInfty_pos

@[simp] theorem cuspWidth_SL2Z : cuspWidth 𝒮ℒ = 1 := by
  simp [cuspWidth, Subgroup.strictWidthInfty_SL2Z]

private theorem qParam_deriv (h : ℝ) (z : ℂ) :
    deriv (Function.Periodic.qParam h) z =
      (2 * π * Complex.I / h) * Function.Periodic.qParam h z := by
  change deriv (fun x : ℂ => cexp (2 * π * Complex.I * x / h)) z = _
  rw [deriv_cexp (by fun_prop)]
  simp [Function.Periodic.qParam]; ring

private theorem cuspFunction_normalizedDeriv (f : ModularForm Γ k)
    {h : ℝ} (hh : 0 < h) (hp : h ∈ Γ.strictPeriods) :
    UpperHalfPlane.cuspFunction h ((h : ℂ) • Derivative.normalizedDerivOfComplex f) =ᶠ[𝓝 0]
      (fun q : ℂ => q * deriv (UpperHalfPlane.cuspFunction h f) q) := by
  have : Fact (IsCusp OnePoint.infty Γ) := ⟨Γ.isCusp_of_mem_strictPeriods hh hp⟩
  filter_upwards [Metric.ball_mem_nhds (0 : ℂ) zero_lt_one] with q hq
  by_cases hq0 : q = 0
  · subst q
    have hf0 : Function.Periodic.cuspFunction h
        (((h : ℂ) • Derivative.normalizedDerivOfComplex f) ∘ UpperHalfPlane.ofComplex) 0 = 0 := by
      rw [Function.Periodic.cuspFunction_zero_of_zero_at_inf hh]
      exact Filter.ZeroAtFilter.smul (h : ℂ)
        ((Derivative.isZeroAtImInfty_normalizedDerivOfComplex f.holo'
        (ModularFormClass.bdd_at_infty f)).comp
          UpperHalfPlane.tendsto_comap_im_ofComplex)
    simp only [UpperHalfPlane.cuspFunction, hf0, zero_mul]
  · have hqnorm : ‖q‖ < 1 := mem_ball_zero_iff.mp hq
    let τ : ℍ := ⟨Function.Periodic.invQParam h q,
      Function.Periodic.im_invQParam_pos_of_norm_lt_one hh hqnorm hq0⟩
    have hτof : τ = UpperHalfPlane.ofComplex (Function.Periodic.invQParam h q) := by
      simpa [τ] using (ofComplex_apply_of_im_pos τ.im_pos).symm
    have hqτ : Function.Periodic.qParam h (τ : ℂ) = q :=
      Function.Periodic.qParam_right_inv hh.ne' hq0
    let g : ℂ → ℂ := UpperHalfPlane.cuspFunction h f
    have hfper : Function.Periodic ((f : ℍ → ℂ) ∘ UpperHalfPlane.ofComplex) h :=
      SlashInvariantFormClass.periodic_comp_ofComplex (f := f) hp
    have hloc : ((f : ℍ → ℂ) ∘ UpperHalfPlane.ofComplex) =ᶠ[𝓝 (τ : ℂ)]
        g ∘ Function.Periodic.qParam h := by
      filter_upwards [isOpen_upperHalfPlaneSet.mem_nhds τ.im_pos] with z hz
      have heq := UpperHalfPlane.eq_cuspFunction ⟨z, hz⟩ hh.ne' hfper
      simpa [g, Function.comp_apply, ofComplex_apply_of_im_pos hz] using heq.symm
    have hGdiff : DifferentiableAt ℂ g q := by
      dsimp [g]
      exact UpperHalfPlane.differentiableAt_cuspFunction hh hfper f.holo'
        (ModularFormClass.bdd_at_infty f) hqnorm
    have hGdiff' : DifferentiableAt ℂ g (Function.Periodic.qParam h (τ : ℂ)) :=
      hqτ ▸ hGdiff
    have hqdiff : DifferentiableAt ℂ (Function.Periodic.qParam h) (τ : ℂ) :=
      Function.Periodic.differentiable_qParam (h := h) (τ : ℂ)
    have hderiv : deriv ((f : ℍ → ℂ) ∘ UpperHalfPlane.ofComplex) (τ : ℂ) =
        deriv g q * deriv (Function.Periodic.qParam h) (τ : ℂ) := by
      rw [hloc.deriv_eq, deriv_comp (hh₂ := hGdiff') (hh := hqdiff), hqτ]
    have hD : ((h : ℂ) • Derivative.normalizedDerivOfComplex f) τ = q * deriv g q := by
      simp only [Pi.smul_apply, smul_eq_mul, Derivative.normalizedDerivOfComplex]
      rw [hderiv, qParam_deriv, hqτ]
      have hhC : (h : ℂ) ≠ 0 := by exact_mod_cast hh.ne'
      field_simp
    change Function.Periodic.cuspFunction h
        (((h : ℂ) • Derivative.normalizedDerivOfComplex f) ∘ UpperHalfPlane.ofComplex) q = _
    rw [Function.Periodic.cuspFunction_eq_of_nonzero (h := h)
      (f := ((h : ℂ) • Derivative.normalizedDerivOfComplex f) ∘ UpperHalfPlane.ofComplex) hq0]
    simpa [g, hqτ, hτof] using hD

private theorem qExpansion_normalizedDeriv (f : ModularForm Γ k)
    {h : ℝ} (hh : 0 < h) (hp : h ∈ Γ.strictPeriods) :
    UpperHalfPlane.qExpansion h ((h : ℂ) • Derivative.normalizedDerivOfComplex f) =
      PowerSeries.X * (UpperHalfPlane.qExpansion h f).derivative := by
  ext n
  rw [UpperHalfPlane.qExpansion_coeff,
    (cuspFunction_normalizedDeriv f hh hp).iteratedDeriv_eq n]
  cases n with
  | zero => simp
  | succ n =>
    rw [show PowerSeries.X = PowerSeries.X ^ 1 by simp,
      PowerSeries.coeff_X_pow_mul, PowerSeries.coeff_derivative]
    rw [UpperHalfPlane.qExpansion_coeff]
    have hG : AnalyticAt ℂ (UpperHalfPlane.cuspFunction h f) 0 :=
      ModularFormClass.analyticAt_cuspFunction_zero f hh hp
    have hGprime : ContDiffAt ℂ n.succ
        (deriv (UpperHalfPlane.cuspFunction h f)) 0 :=
      (hG.contDiffAt : ContDiffAt ℂ (n.succ + 1)
        (UpperHalfPlane.cuspFunction h f) 0).derivWithin (m := n.succ) le_rfl
    have hmul := iteratedDeriv_mul (n := n.succ)
      (contDiffAt_id : ContDiffAt ℂ n.succ (fun z : ℂ => z) 0) hGprime
    have hfun : id * deriv (UpperHalfPlane.cuspFunction h f) =
        (fun q : ℂ => q * deriv (UpperHalfPlane.cuspFunction h f) q) := by
      funext q
      rfl
    rw [hfun] at hmul
    have hmul' : iteratedDeriv n.succ (fun q : ℂ => q *
        deriv (UpperHalfPlane.cuspFunction h f) q) 0 =
        ∑ i ∈ Finset.range (n.succ + 1),
          (n.succ.choose i : ℂ) * iteratedDeriv i id 0 *
            iteratedDeriv (n.succ - i) (deriv (UpperHalfPlane.cuspFunction h f)) 0 := by
      simpa only [Pi.mul_apply, id_eq] using hmul
    have hsum : ∑ i ∈ Finset.range (n.succ + 1),
        (n.succ.choose i : ℂ) * iteratedDeriv i id 0 *
          iteratedDeriv (n.succ - i) (deriv (UpperHalfPlane.cuspFunction h f)) 0 =
        (n.succ : ℂ) * iteratedDeriv n
          (deriv (UpperHalfPlane.cuspFunction h f)) 0 := by
      rw [Finset.sum_eq_single 1]
      · simp [iteratedDeriv_id]
      · intro i hi hi1
        simp [iteratedDeriv_id, hi1]
      · simp
    rw [hmul', hsum]
    rw [← iteratedDeriv_succ']
    push_cast
    ring

noncomputable def e2Fourier (R : Type) [CommRing R] : PowerSeries R :=
  PowerSeries.mk fun n => if n = 0 then 1 else -24 * (ArithmeticFunction.sigma 1 n : R)

/-- The integral E₂ series in the parameter at infinity for `Γ`. -/
noncomputable def e2FourierAt (Γ : Subgroup (GL (Fin 2) ℝ))
    [Γ.le_SL2Z] [Γ.IsArithmetic] (R : Type) [CommRing R] : PowerSeries R :=
  PowerSeries.expand (cuspWidth Γ) (cuspWidth_pos.ne') (e2Fourier R)

@[simp] theorem e2FourierAt_SL2Z (R : Type) [CommRing R] :
    e2FourierAt 𝒮ℒ R = e2Fourier R := by
  simp [e2FourierAt]

theorem coeff_e2FourierAt [Γ.le_SL2Z] [Γ.IsArithmetic]
    (R : Type) [CommRing R] (n : ℕ) :
    (e2FourierAt Γ R).coeff n =
      if cuspWidth Γ ∣ n then
        if n / cuspWidth Γ = 0 then 1
        else -24 * (ArithmeticFunction.sigma 1 (n / cuspWidth Γ) : R)
      else 0 := by
  simp only [e2FourierAt, PowerSeries.coeff_expand, e2Fourier, PowerSeries.coeff_mk]

private theorem qExpansion_E2_nat (h : ℕ) (hh : h ≠ 0) :
    qExpansion (h : ℝ) EisensteinSeries.E2 =
      PowerSeries.expand h hh (e2Fourier ℂ) := by
  have hpos : (0 : ℝ) < h := by exact_mod_cast Nat.pos_of_ne_zero hh
  have hper : Function.Periodic (EisensteinSeries.E2 ∘ UpperHalfPlane.ofComplex) (h : ℝ) := by
    simpa using EisensteinSeries.E2_periodic.nat_mul h
  have han := UpperHalfPlane.analyticAt_cuspFunction_zero hpos hper
    E2_mdifferentiable EisensteinSeries.isBoundedAtImInfty_E2
  ext n
  symm
  refine UpperHalfPlane.qExpansion_coeff_unique (f := EisensteinSeries.E2)
    (c := fun m => (PowerSeries.expand h hh (e2Fourier ℂ)).coeff m) hpos han ?_ n
  intro τ
  have hinj : Function.Injective (fun m : ℕ => h * m) := by
    intro a b hab
    exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hh) hab
  apply (hinj.hasSum_iff (f := fun m =>
    (PowerSeries.expand h hh (e2Fourier ℂ)).coeff m •
      Function.Periodic.qParam (h : ℝ) (τ : ℂ) ^ m) ?_).mp
  · have hq : Function.Periodic.qParam (h : ℝ) (τ : ℂ) ^ h =
        cexp (2 * π * Complex.I * (τ : ℂ)) := by
      rw [Function.Periodic.qParam, ← Complex.exp_nat_mul]
      congr 1
      have hhC : (h : ℂ) ≠ 0 := by exact_mod_cast hh
      push_cast
      field_simp
    convert EisensteinSeries.hasSum_qExpansion_E2 τ using 1
    · funext m
      rw [Function.comp_apply, PowerSeries.coeff_expand_mul, pow_mul, hq]
      simp only [e2Fourier, PowerSeries.coeff_mk]
    · rfl
  · intro m hm
    have hnd : ¬ h ∣ m := by
      rintro ⟨a, rfl⟩
      exact hm ⟨a, rfl⟩
    simp [PowerSeries.coeff_expand_of_not_dvd h hh _ hnd]

private theorem qExpansion_E2_at [Γ.le_SL2Z] [Γ.IsArithmetic] :
    qExpansion Γ.strictWidthInfty EisensteinSeries.E2 = e2FourierAt Γ ℂ := by
  rw [← cuspWidth_cast (Γ := Γ)]
  exact qExpansion_E2_nat (cuspWidth Γ) cuspWidth_pos.ne'

/-- Fourier expansion of the Serre derivative scaled by `12` times the strict cusp width. -/
theorem qExp_normalizedSerre [hΓ : Γ.le_SL2Z] [Γ.IsArithmetic] (f : ModularForm Γ k) :
    qExp (((12 : ℂ) * cuspWidth Γ) • Derivative.serreDerivativeMF k f hΓ.le) =
      (12 : ℂ) • (PowerSeries.X * (qExp f).derivative) -
        ((k : ℂ) * cuspWidth Γ) • (e2FourierAt Γ ℂ * qExp f) := by
  let h := Γ.strictWidthInfty
  have hh : 0 < h := Γ.strictWidthInfty_pos
  have hp : h ∈ Γ.strictPeriods := Γ.strictWidthInfty_mem_strictPeriods
  have hF : AnalyticAt ℂ (UpperHalfPlane.cuspFunction h f) 0 :=
    ModularFormClass.analyticAt_cuspFunction_zero f hh hp
  have hD : AnalyticAt ℂ
      (UpperHalfPlane.cuspFunction h ((h : ℂ) • Derivative.normalizedDerivOfComplex f)) 0 := by
    apply (analyticAt_id.mul hF.deriv).congr
    exact (cuspFunction_normalizedDeriv f hh hp).symm
  have hw : (cuspWidth Γ : ℂ) = (h : ℂ) := by
    exact_mod_cast cuspWidth_cast (Γ := Γ)
  have hper : Function.Periodic (EisensteinSeries.E2 ∘ UpperHalfPlane.ofComplex) h := by
    simpa only [mul_one, hw] using EisensteinSeries.E2_periodic.nat_mul (cuspWidth Γ)
  have hE2 : AnalyticAt ℂ (UpperHalfPlane.cuspFunction h EisensteinSeries.E2) 0 :=
    UpperHalfPlane.analyticAt_cuspFunction_zero hh hper
      E2_mdifferentiable EisensteinSeries.isBoundedAtImInfty_E2
  have hE2F : AnalyticAt ℂ
      (UpperHalfPlane.cuspFunction h (EisensteinSeries.E2 * (f : ℍ → ℂ))) 0 := by
    rw [UpperHalfPlane.cuspFunction_mul hE2.continuousAt hF.continuousAt]
    exact hE2.mul hF
  have hsd : (((12 : ℂ) * (h : ℂ)) • Derivative.serreDerivative k (f : ℍ → ℂ)) =
      (12 : ℂ) • ((h : ℂ) • Derivative.normalizedDerivOfComplex f) -
        ((k : ℂ) * h) • (EisensteinSeries.E2 * (f : ℍ → ℂ)) := by
    funext z
    simp [smul_eq_mul]
    ring
  have hD12 : AnalyticAt ℂ (UpperHalfPlane.cuspFunction h
      ((12 : ℂ) • ((h : ℂ) • Derivative.normalizedDerivOfComplex f))) 0 := by
    rw [UpperHalfPlane.cuspFunction_smul hD.continuousAt]
    exact hD.const_smul
  have hE2Fc : AnalyticAt ℂ (UpperHalfPlane.cuspFunction h
      (((k : ℂ) * h) • (EisensteinSeries.E2 * (f : ℍ → ℂ)))) 0 := by
    rw [UpperHalfPlane.cuspFunction_smul hE2F.continuousAt]
    exact hE2F.const_smul
  simp only [qExp_def, hw]
  change qExpansion h (((12 : ℂ) * (h : ℂ)) • Derivative.serreDerivative k f) = _
  rw [hsd, UpperHalfPlane.qExpansion_sub hD12 hE2Fc,
    UpperHalfPlane.qExpansion_smul hD, UpperHalfPlane.qExpansion_smul hE2F,
    UpperHalfPlane.qExpansion_mul hE2 hF, qExpansion_normalizedDeriv f hh hp,
    qExpansion_E2_at]

/-- The usual Serre derivative, expressed using `qExp` at the strict cusp width. -/
theorem qExp_serreDerivative [hΓ : Γ.le_SL2Z] [Γ.IsArithmetic] (f : ModularForm Γ k) :
    qExp (Derivative.serreDerivativeMF k f hΓ.le) =
      (cuspWidth Γ : ℂ)⁻¹ • (PowerSeries.X * (qExp f).derivative) -
        ((k : ℂ) / 12) • (e2FourierAt Γ ℂ * qExp f) := by
  have hw : (cuspWidth Γ : ℂ) ≠ 0 := by exact_mod_cast (cuspWidth_pos (Γ := Γ)).ne'
  have hc : (12 : ℂ) * cuspWidth Γ ≠ 0 := mul_ne_zero (by norm_num) hw
  have h1 : ((12 : ℂ) * cuspWidth Γ)⁻¹ * 12 = (cuspWidth Γ : ℂ)⁻¹ := by
    field_simp
  have h2 : ((12 : ℂ) * cuspWidth Γ)⁻¹ * ((k : ℂ) * cuspWidth Γ) = (k : ℂ) / 12 := by
    field_simp
  have heq := qExp_normalizedSerre f
  rw [ModularForm.qExp_smul] at heq
  have hinv := congrArg (fun p : PowerSeries ℂ => ((12 : ℂ) * cuspWidth Γ)⁻¹ • p) heq
  simpa only [smul_sub, smul_smul, inv_mul_cancel₀ hc, one_smul, h1, h2] using hinv

noncomputable def normalizedSerreFourier (R : Type) [CommRing R] [Algebra R ℂ]
    [FaithfulSMul R ℂ] [Γ.le_SL2Z] [Γ.IsArithmetic]
    (f : ModularFormOver R Γ k) : PowerSeries R :=
  (12 : R) • (PowerSeries.X * (fourier R f).derivative) -
    ((k : R) * cuspWidth Γ) • (e2FourierAt Γ R * fourier R f)

private theorem map_e2Fourier (R : Type) [CommRing R] [Algebra R ℂ] :
    PowerSeries.map (algebraMap R ℂ) (e2Fourier R) = e2Fourier ℂ := by
  ext n
  simp only [e2Fourier, PowerSeries.coeff_map, PowerSeries.coeff_mk]
  split_ifs
  · exact map_one (algebraMap R ℂ)
  · simp only [map_mul, map_neg, map_ofNat, map_natCast]

private theorem map_e2FourierAt [Γ.le_SL2Z] [Γ.IsArithmetic]
    (R : Type) [CommRing R] [Algebra R ℂ] :
    PowerSeries.map (algebraMap R ℂ) (e2FourierAt Γ R) = e2FourierAt Γ ℂ := by
  simp only [e2FourierAt, PowerSeries.map_expand, map_e2Fourier]

private theorem map_derivative {R S : Type} [CommSemiring R] [CommSemiring S]
    (f : R →+* S) (g : PowerSeries R) :
    PowerSeries.map f g.derivative = (PowerSeries.map f g).derivative := by
  ext n
  simp [PowerSeries.coeff_map, PowerSeries.coeff_derivative]

private theorem map_smul_series {R S : Type} [CommSemiring R] [CommSemiring S]
    (f : R →+* S) (a : R) (g : PowerSeries R) :
    PowerSeries.map f (a • g) = f a • PowerSeries.map f g := by
  ext n
  simp [PowerSeries.coeff_map]

private theorem map_normalizedSerreFourier (R : Type) [CommRing R]
    [Algebra R ℂ] [FaithfulSMul R ℂ] [hΓ : Γ.le_SL2Z] [Γ.IsArithmetic]
    (f : ModularFormOver R Γ k) :
    PowerSeries.map (algebraMap R ℂ) (normalizedSerreFourier R f) =
      qExp (((12 : ℂ) * cuspWidth Γ) •
        Derivative.serreDerivativeMF k (f : ModularForm Γ k) hΓ.le) := by
  simp only [normalizedSerreFourier, map_sub, map_smul_series, map_mul, PowerSeries.map_X,
    map_derivative, map_fourier R R f, map_e2FourierAt, map_ofNat, map_intCast, map_natCast]
  exact (qExp_normalizedSerre (f := (f : ModularForm Γ k))).symm

/-- The Serre derivative scaled by `12 * cuspWidth Γ`, preserving coefficients over `R`. -/
noncomputable def normalizedSerreDerivative (R : Type) [CommRing R] [Algebra R ℂ]
    [FaithfulSMul R ℂ] [hΓ : Γ.le_SL2Z] [Γ.IsArithmetic] (f : ModularFormOver R Γ k) :
      ModularFormOver R Γ (k + 2) where
  toModularForm := ((12 : ℂ) * cuspWidth Γ) • Derivative.serreDerivativeMF k f hΓ.le
  isOver' := by
    rw [ModularForm.isOver_iff]
    intro n
    refine ⟨(normalizedSerreFourier R f).coeff n, ?_⟩
    have h := map_normalizedSerreFourier R f
    have hn := congrArg (PowerSeries.coeff n) h
    simpa only [PowerSeries.coeff_map] using hn

@[simp] theorem normalizedSerreDerivative_toModularForm (R : Type)
    [CommRing R] [Algebra R ℂ] [FaithfulSMul R ℂ] [hΓ : Γ.le_SL2Z] [Γ.IsArithmetic]
    (f : ModularFormOver R Γ k) :
    (normalizedSerreDerivative R f).toModularForm =
      ((12 : ℂ) * cuspWidth Γ) • Derivative.serreDerivativeMF k f hΓ.le := rfl

theorem fourier_normalizedSerreDerivative (R : Type) [CommRing R] [Algebra R ℂ]
    [FaithfulSMul R ℂ] [Γ.le_SL2Z] [Γ.IsArithmetic] (f : ModularFormOver R Γ k) :
    fourier R (normalizedSerreDerivative R f) = normalizedSerreFourier R f := by
  apply map_algebraMap_injective ℂ
  rw [map_fourier R R (normalizedSerreDerivative R f), map_normalizedSerreFourier]
  rfl

theorem coeff_normalizedSerreDerivative (R : Type) [CommRing R] [Algebra R ℂ]
    [FaithfulSMul R ℂ] [Γ.le_SL2Z] [Γ.IsArithmetic] (f : ModularFormOver R Γ k) (n : ℕ) :
    coeff R n (normalizedSerreDerivative R f) =
      PowerSeries.coeff n (normalizedSerreFourier R f) := by
  change PowerSeries.coeff n (fourier R (normalizedSerreDerivative R f)) = _
  rw [fourier_normalizedSerreDerivative]

theorem coeff_normalizedSerreDerivative_explicit (R : Type) [CommRing R]
    [Algebra R ℂ] [FaithfulSMul R ℂ] [Γ.le_SL2Z] [Γ.IsArithmetic] (f : ModularFormOver R Γ k)
    (n : ℕ) :
    coeff R n (normalizedSerreDerivative R f) =
      (12 : R) * (n : R) * coeff R n f -
        ((k : R) * cuspWidth Γ) * PowerSeries.coeff n (e2FourierAt Γ R * fourier R f) := by
  rw [coeff_normalizedSerreDerivative, normalizedSerreFourier]
  cases n with
  | zero =>
      simp
  | succ n =>
      simp only [map_sub, map_smul, PowerSeries.coeff_succ_X_mul,
        PowerSeries.coeff_derivative, smul_eq_mul, coeff_def, Nat.cast_add, Nat.cast_one]
      ring

end ModularFormOver
