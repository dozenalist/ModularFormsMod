import Mathlib.NumberTheory.ModularForms.Discriminant
import ModularFormsMod.discProduct



open ModularForm PowerSeries MatrixGroups UpperHalfPlane Set DirectSum Filter Function
open scoped PowerSeries.WithPiTopology Topology

namespace ModularForm

noncomputable section

/-!
  Independent proof draft for `Delta.carrier_eq`.

  The coefficientwise part is complete: the finite products converge in the
  coefficientwise topology to the power series whose coefficients are the
  coefficients of `Delta`.  The remaining step is to connect this formal
  power-series identity to analytic evaluation at `𝕢 1 τ`.
-/


theorem qExpansion_discriminant : qExpansion 1 (CuspForm.discriminant : ModularForm 𝒮ℒ 12) =
    PowerSeries.map (algebraMap ℤ ℂ) (.mk fun m => (discProduct m).coeff m) := by

  let D : ℕ → ℤ := fun n => (discProduct n).coeff n
  let c : ℕ → ℂ := fun n ↦ ((discProduct n).coeff n : ℂ)
  let F : ℂ⟦X⟧ := PowerSeries.mk c
  let disc : ModularForm (Matrix.SpecialLinearGroup.mapGL ℝ).range 12 := ModularFormClass.modularForm CuspForm.discriminant

  have hF : Tendsto (discProduct (α := ℂ)) atTop (𝓝 F) := by
    rw [PowerSeries.WithPiTopology.tendsto_iff_coeff_tendsto]
    intro d
    obtain ⟨m, hm⟩ := discProduct_eventually_sum (α := ℂ) d
    refine tendsto_atTop_of_eventually_const (i₀ := max (d + 1) m) ?_
    intro n hn
    have hdn : d < n := lt_of_lt_of_le d.lt_succ_self
      (le_trans (le_max_left _ _) hn)
    have hnm : m ≤ n := le_trans (le_max_right _ _) hn
    rw [hm d (le_refl d) n hnm]
    simp only [F, c, PowerSeries.coeff_mk]
    simp only [map_sum]
    have hcoeff (i : ℕ) :
        PowerSeries.coeff d ((D i : ℤ) • (X : ℂ⟦X⟧) ^ i) =
          if d = i then (D i : ℂ) else 0 := by
      have hcast : (D i : ℂ⟦X⟧) = C (D i : ℂ) := by simp
      rw [zsmul_eq_mul]
      simp only [hcast, PowerSeries.coeff_C_mul_X_pow]
    simp [hdn]

  let p : ℕ → ℂ⟦X⟧ := fun i ↦ (1 - (X : ℂ⟦X⟧) ^ (i + 1)) ^ 24
  have hp : Multipliable p := by
    exact (PowerSeries.WithPiTopology.multipliable_one_sub_X_pow ℂ).pow 24
  have hpLim : Tendsto (fun n ↦ (X : ℂ⟦X⟧) * ∏ i ∈ Finset.range n, p i) atTop
      (𝓝 ((X : ℂ⟦X⟧) * ∏' i, p i)) := by
    simpa [p] using tendsto_const_nhds.mul hp.tendsto_prod_tprod_nat
  have hprod : (X : ℂ⟦X⟧) * ∏' i, p i = F :=
    tendsto_nhds_unique hpLim hF

  let U : Set ℂ := Metric.ball 0 1
  let G : ℕ → ℂ → ℂ := fun n q ↦ q * ∏ i ∈ Finset.range n, (1 - q ^ (i + 1)) ^ 24
  let Ginf : ℂ → ℂ := fun q ↦ q * ∏' i, (1 - q ^ (i + 1)) ^ 24
  have hprod_loc : TendstoLocallyUniformlyOn
      (fun n q ↦ ∏ i ∈ Finset.range n, (1 - q ^ (i + 1)) ^ 24)
      (fun q ↦ (∏' i, (1 - q ^ (i + 1))) ^ 24) atTop U := by
    have hbase := (MultipliableLocallyUniformlyOn.hasProdLocallyUniformlyOn
      ModularForm.multipliableLocallyUniformlyOn_one_sub_pow).tendstoLocallyUniformlyOn_finsetRange
    have hone : TendstoLocallyUniformlyOn (fun _ : ℕ ↦ fun _ : ℂ ↦ (1 : ℂ))
        (fun _ : ℂ ↦ (1 : ℂ)) atTop U := by
      intro v hv q hq
      exact ⟨U, self_mem_nhdsWithin,
        Filter.Eventually.of_forall fun n z hz ↦ refl_mem_uniformity hv⟩
    have hpow : ∀ k : ℕ, TendstoLocallyUniformlyOn
        (fun n q ↦ (∏ i ∈ Finset.range n, (1 - q ^ (i + 1))) ^ k)
        (fun q ↦ (∏' i, (1 - q ^ (i + 1))) ^ k) atTop U := by
      intro k
      induction k with
      | zero => simpa using hone
      | succ k ih =>
          have h := ih.mul₀ hbase ((differentiableOn_tprod_one_sub_pow.fun_pow k).continuousOn)
            (differentiableOn_tprod_one_sub_pow.continuousOn)
          convert h using 1 <;> ext <;> simp [pow_succ, mul_comm]
    convert hpow 24 using 1; ext; simp [Finset.prod_pow]
  have h_id : TendstoLocallyUniformlyOn (fun _ : ℕ ↦ fun q : ℂ ↦ q) id atTop U := by
    intro v hv q hq
    refine ⟨U, self_mem_nhdsWithin, ?_⟩
    exact Filter.Eventually.of_forall fun n z hz ↦ by simpa using refl_mem_uniformity hv
  have hG : TendstoLocallyUniformlyOn G Ginf atTop U := by
    have h := h_id.mul₀ hprod_loc continuousOn_id
      ((differentiableOn_tprod_one_sub_pow.fun_pow 24).continuousOn)
    have h' := h.congr (fun n ↦ by
      intro q hq
      change q * ∏ i ∈ Finset.range n, (1 - q ^ (i + 1)) ^ 24 = G n q
      rfl)
    apply h'.congr_right
    intro q hq
    change q * (∏' i, (1 - q ^ (i + 1))) ^ 24 = Ginf q
    simp only [Ginf]
    rw [Multipliable.tprod_pow]
    exact ModularForm.multipliable_one_sub_pow (by
      simpa [U, Metric.mem_ball] using hq)

  let P : ℕ → Polynomial ℂ := fun n ↦ Polynomial.X *
    ∏ i ∈ Finset.range n, (1 - Polynomial.X ^ (i + 1)) ^ 24
  have hG_eval (n : ℕ) : G n = fun q ↦ (P n).eval q := by
    funext q
    simp [G, P, Polynomial.eval_prod]
  have hiter_eval (Q : Polynomial ℂ) (d : ℕ) :
      iteratedDeriv d (fun q ↦ Q.eval q) =
        fun q ↦ (Polynomial.derivative^[d] Q).eval q := by
    induction d with
    | zero => simp
    | succ d ih =>
        rw [iteratedDeriv_succ, ih]
        funext q
        rw [Polynomial.deriv]
        congr 1
        rw [← Function.iterate_succ_apply' (f := Polynomial.derivative) d Q]
  have hiter : ∀ d : ℕ, TendstoLocallyUniformlyOn
      (fun n ↦ iteratedDeriv d (G n)) (iteratedDeriv d Ginf) atTop U := by
    intro d
    induction d with
    | zero => simpa [iteratedDeriv_zero] using hG
    | succ d ih =>
        have hdiff : ∀ᶠ n in atTop,
            DifferentiableOn ℂ (iteratedDeriv d (G n)) U := by
          filter_upwards [] with n
          rw [hG_eval n]
          exact (Polynomial.contDiff_aeval (P n) (d + 1)).differentiable_iteratedDeriv' d |>.differentiableOn
        simpa [iteratedDeriv_succ, Function.comp_def] using
          ih.deriv hdiff Metric.isOpen_ball

  apply PowerSeries.ext
  intro d
  rw [PowerSeries.coeff_map]
  have hq : c d = (qExpansion 1 (disc : ℍ → ℂ)).coeff d :=
    ModularFormClass.qExpansion_coeff_unique (f := disc)
    zero_lt_one one_mem_strictPeriods_SL (m := d) (by
      have hcoeff (m : ℕ) :
          c m = (qExpansion 1 (disc : ℍ → ℂ)).coeff m := by
        have h0 : (0 : ℂ) ∈ U := by
          simp [U, Metric.mem_ball]
        have hlim := (hiter m).tendsto_at (a := (0 : ℂ)) h0
        have hstable : ∀ᶠ n in atTop,
            iteratedDeriv m (G n) 0 = (m.factorial : ℂ) * c m := by
          filter_upwards [eventually_ge_atTop (m + 1)] with n hn
          rw [hG_eval n, hiter_eval]
          have hP : (P n : ℂ⟦X⟧) = discProduct (α := ℂ) n := by
            change
              ((Polynomial.X * ∏ i ∈ Finset.range n,
                (1 - Polynomial.X ^ (i + 1)) ^ 24 : Polynomial ℂ) : ℂ⟦X⟧) =
                (X : ℂ⟦X⟧) * ∏ i ∈ Finset.range n, (1 - X ^ (i + 1)) ^ 24
            rw [Polynomial.coe_mul]
            have hprod :
                ((∏ i ∈ Finset.range n, (1 - Polynomial.X ^ (i + 1)) ^ 24 :
                    Polynomial ℂ) : ℂ⟦X⟧) =
                  ∏ i ∈ Finset.range n,
                    (((1 - Polynomial.X ^ (i + 1)) ^ 24 : Polynomial ℂ) : ℂ⟦X⟧) := by
              simpa only [Polynomial.coeToPowerSeries.ringHom_apply] using
                (map_prod (Polynomial.coeToPowerSeries.ringHom (R := ℂ))
                  (fun i : ℕ ↦ (1 - Polynomial.X ^ (i + 1)) ^ 24)
                  (Finset.range n))
            rw [hprod]
            simp
          have hPcoeff : (P n).coeff m = (discProduct (α := ℂ) n).coeff m := by
            have h := congr_arg (PowerSeries.coeff m) hP
            simpa using h
          have hstable' : D m = (discProduct (α := ℤ) n).coeff m := by
            exact discProduct_coeff_le (α := ℤ) (n := m) (m := m) (j := n)
              le_rfl (Nat.le_of_lt hn)
          have hcast : (discProduct (α := ℂ) n).coeff m = c m := by
            rw [← Int.cast_coeff_discProduct (S := ℂ) m n]
            simp [c, ← hstable', D]
          change ((Polynomial.derivative^[m] (P n)).eval 0) = _
          rw [← Polynomial.coeff_zero_eq_eval_zero,
            Polynomial.coeff_iterate_derivative]
          simp [hPcoeff, hcast, Nat.descFactorial_self]
        have hconst : Tendsto (fun _ : ℕ ↦ (m.factorial : ℂ) * c m) atTop
            (𝓝 ((m.factorial : ℂ) * c m)) := tendsto_const_nhds
        have hderiv : iteratedDeriv m Ginf 0 = (m.factorial : ℂ) * c m :=
          tendsto_nhds_unique hlim
            (hconst.congr' (hstable.mono fun n hn ↦ hn.symm))
        have hderiv_eq : iteratedDeriv m
              (cuspFunction 1 (ModularForm.discriminant : ℍ → ℂ)) 0 =
            iteratedDeriv m Ginf 0 := by
          have h := discriminant_cuspFunction_eqOn.iteratedDeriv_of_isOpen
            Metric.isOpen_ball m (Metric.mem_ball_self one_pos)
          simpa [Ginf] using h
        rw [qExpansion_coeff]
        change c m = (m.factorial : ℂ)⁻¹ *
          iteratedDeriv m (cuspFunction 1 (ModularForm.discriminant : ℍ → ℂ)) 0
        rw [hderiv_eq, hderiv]
        have hfac : (m.factorial : ℂ) ≠ 0 := by
          exact_mod_cast Nat.factorial_ne_zero m
        field_simp [hfac]
      intro τ
      rw [← SlashInvariantFormClass.eq_cuspFunction disc τ
        one_mem_strictPeriods_SL zero_ne_one.symm]
      change HasSum (fun m : ℕ ↦ c m • Periodic.qParam 1 τ ^ m)
        (cuspFunction 1 (ModularForm.discriminant : ℍ → ℂ) (Periodic.qParam 1 τ))
      rw [discriminant_cuspFunction_eqOn
        (by simpa [mem_ball_zero_iff] using
          Periodic.norm_qParam_lt_one zero_lt_one τ.im_pos)]
      have hsum := UpperHalfPlane.hasSum_qExpansion (h := (1 : ℝ))
        (f := disc) one_pos
        (SlashInvariantFormClass.periodic_comp_ofComplex disc
          (by simp))
        (ModularFormClass.holo disc)
        (ModularFormClass.bdd_at_infty disc) τ
      rw [← SlashInvariantFormClass.eq_cuspFunction disc τ
        (by simp) one_ne_zero] at hsum
      change HasSum (fun m : ℕ ↦
        (qExpansion 1 (disc : ℍ → ℂ)).coeff m • Periodic.qParam 1 τ ^ m)
        (cuspFunction 1 (ModularForm.discriminant : ℍ → ℂ)
          (Periodic.qParam 1 τ)) at hsum
      rw [discriminant_cuspFunction_eqOn
        (by simpa [mem_ball_zero_iff] using
          Periodic.norm_qParam_lt_one zero_lt_one τ.im_pos)] at hsum
      simpa only [hcoeff] using hsum)
  rw [← hq]
  unfold c
  simp only [coeff_mk, eq_intCast, Int.cast_coeff_discProduct]

end


end ModularForm
