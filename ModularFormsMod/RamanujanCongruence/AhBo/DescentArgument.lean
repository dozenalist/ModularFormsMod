/-
Copyright (c) 2026 Carter Hastings. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carter Hastings
-/

module

public import ModularFormsMod.RamanujanCongruence.AhBo.PrimaryLemmas

/-!
# The descent argument for Ramanujan congruences

The theta cycle forces a low point of filtration `12 * δ p + 4`. The Sturm bound
then identifies this iterate with a multiple of `E₄ * fl p`. Comparing the next
Fourier coefficient gives the contradiction in Theorem 3.1 of Ahlgren--Boylan.
-/

@[expose] public section

noncomputable section

open ModularFormMod ModularFormMod.ZMod PInteger

variable {p : ℕ} [hp : isLargerPrime p]

/-- Equation (3.6): vanishing under U forces a high point at `p - 2`. -/
theorem dvd_Filtration_Theta_pow_sub_two (flu : (fl p).UOp = 0) :
    (p : ℤ) ∣ ((fl p).Theta_pow (p - 2)).Filtration := by
  by_contra h
  have hp13 := hp.AtLeastThirteen
  have hstep := (Filtration_Theta_iff' (fl p)
    (show p - 1 = (p - 2) + 1 by omega)).mpr h
  rw [Filtration_Theta_pow_sub_one flu] at hstep
  have hle := le_Filtration_Theta_pow_fl (p := p) (p - 2)
  rw [Filtration_fl] at hle
  omega

/-- Equations (3.7)--(3.8): the first low point is four above the initial filtration. -/
theorem Filtration_Theta_pow_low_point (flu : (fl p).UOp = 0) :
    ((fl p).Theta_pow ((p + 3) / 2)).Filtration = 12 * (δ p : ℤ) + 4 := by
  let r := (p + 1) / 2
  let t := (p - 5) / 2
  let amax := (p + 5) / 2
  have hp13 := hp.AtLeastThirteen
  have hhalf := prime_half (p := p)
  have hδ := delta_exponent_int (p := p)
  have hr : 2 * (r : ℤ) = (p : ℤ) + 1 := by dsimp [r]; omega
  have hA : 2 * (amax : ℤ) = (p : ℤ) + 5 := by dsimp [amax]; omega
  have ht : r + t = p - 2 := by dsimp [r, t]; omega
  have htpos : 1 ≤ t := by dsimp [t]; omega
  have hlow : (p + 3) / 2 = r + 1 := by dsimp [r]; omega
  have hhigh : ((fl p).Theta_pow r).Filtration = (p : ℤ) * (p + 1) := by
    rw [Filtration_Theta_pow_initial (le_refl r)]
    nlinarith
  have hdiv : (p : ℤ) ∣ ((fl p).Theta_pow r).Filtration := by
    rw [hhigh]
    exact dvd_mul_right _ _
  obtain ⟨α, hα, hdrop⟩ := Filtration_Theta_congruence_of_dvd' (fl p) hdiv rfl
  have hbound := le_Filtration_Theta_pow_fl (p := p) (r + 1)
  rw [Filtration_fl] at hbound
  rw [hhigh] at hdrop
  have hαle : α ≤ amax := by
    by_contra! h
    have hprod := mul_nonneg (show 0 ≤ α - ((amax : ℤ) + 1) by omega)
      (show 0 ≤ (p : ℤ) - 1 by omega)
    nlinarith
  have hαeq : α = amax := by
    by_contra hne
    have hαlt : α < amax := lt_of_le_of_ne hαle hne
    -- If the drop is smaller, no further high point can occur by `p - 2`.
    have hnot (j : ℕ) (hj : 1 ≤ j) (hjt : j ≤ t)
        (hw : ((fl p).Theta_pow (r + j)).Filtration =
          (p : ℤ) * (p + 1) + j * (p + 1) - α * (p - 1)) :
        ¬ (p : ℤ) ∣ ((fl p).Theta_pow (r + j)).Filtration := by
      intro hd
      have hsmall : 0 < (j : ℤ) + α ∧ (j : ℤ) + α < p := by
        dsimp [r, t, amax] at *
        omega
      have hd' : (p : ℤ) ∣ (j : ℤ) + α := by
        convert dvd_sub hd
          (dvd_mul_right (p : ℤ) ((p + 1) + j - α)) using 1
        nlinarith [hw]
      have := Int.eq_zero_of_dvd_of_nonneg_of_lt hsmall.1.le hsmall.2 hd'
      omega
    have hcycle (i : ℕ) (hi : i + 1 ≤ t) :
        ((fl p).Theta_pow (r + (i + 1))).Filtration =
          (p : ℤ) * (p + 1) + (i + 1) * (p + 1) - α * (p - 1) := by
      induction i with
      | zero => simpa using hdrop
      | succ i ih =>
        have hw := ih (by omega)
        rw [(Filtration_Theta_iff' (fl p)
          (show r + (i + 1 + 1) = (r + (i + 1)) + 1 by omega)).mpr
            (hnot (i + 1) (by omega) (by omega) hw), hw]
        push_cast
        ring
    have hw := hcycle (t - 1) (by omega)
    have hidx : r + (t - 1 + 1) = r + t := by omega
    have htint : ((t - 1 : ℕ) : ℤ) + 1 = (t : ℤ) := by omega
    have hw' := (congrArg (fun m => ((fl p).Theta_pow m).Filtration) hidx).symm.trans hw
    have hlast := hnot t htpos le_rfl (by simpa only [htint] using hw')
    rw [ht] at hlast
    exact hlast (dvd_Filtration_Theta_pow_sub_two flu)
  rw [hlow, hdrop, hαeq]
  nlinarith

private def reducedE4 : 𝓜 p 4 :=
  (ModularFormOver.E₄.tower ℤ(p)).Reduce reduce

private lemma coeff_zero_reducedE4 : coeff 0 (reducedE4 (p := p)) = 1 := by
  change reduce (ModularFormOver.coeff ℤ 0 ModularFormOver.E₄ ℤ(p)) = 1
  simp

private lemma coeff_one_reducedE4 : coeff 1 (reducedE4 (p := p)) = 240 := by
  change reduce (ModularFormOver.coeff ℤ 1 ModularFormOver.E₄ ℤ(p)) = 240
  rw [ModularFormOver.coeff_one_E₄, map_ofNat]

private lemma coeff_E4_fl_add_delta (n : ℕ) :
    coeff (n + δ p) ((reducedE4 (p := p)).mul (fl p)) =
      PowerSeries.coeff n
        ((reducedE4 (p := p)).fourier * (fl p).fourier.divXPowOrder) := by
  have hf : (fl p).fourier =
      PowerSeries.X ^ δ p * (fl p).fourier.divXPowOrder := by
    simpa only [order_fl, ENat.toNat_natCast] using
      (PowerSeries.X_pow_order_mul_divXPowOrder (f := (fl p).fourier)).symm
  change PowerSeries.coeff (n + δ p) ((reducedE4 (p := p)).fourier * (fl p).fourier) = _
  conv_lhs => rw [hf]
  rw [show (reducedE4 (p := p)).fourier *
      (PowerSeries.X ^ δ p * (fl p).fourier.divXPowOrder) =
        PowerSeries.X ^ δ p *
          ((reducedE4 (p := p)).fourier * (fl p).fourier.divXPowOrder) by ring,
    PowerSeries.coeff_X_pow_mul]

private lemma coeff_delta_E4_fl :
    coeff (δ p) ((reducedE4 (p := p)).mul (fl p)) = 1 := by
  have h := coeff_E4_fl_add_delta (p := p) 0
  rw [zero_add, PowerSeries.coeff_zero_eq_constantCoeff, _root_.map_mul,
    PowerSeries.constantCoeff_divXPowOrder, order_fl, ENat.toNat_natCast,
    coeff_fourier, coeff_delta_fl, mul_one] at h
  rw [← PowerSeries.coeff_zero_eq_constantCoeff] at h
  exact h.trans (coeff_zero_reducedE4 (p := p))

private lemma coeff_delta_add_one_E4_fl :
    coeff (δ p + 1) ((reducedE4 (p := p)).mul (fl p)) =
      240 - 24 * (δ p : ZMod p) := by
  rw [Nat.add_comm, coeff_E4_fl_add_delta, PowerSeries.coeff_one_mul]
  simp only [PowerSeries.coeff_divXPowOrder, order_fl, ENat.toNat_natCast,
    PowerSeries.constantCoeff_divXPowOrder, ← PowerSeries.coeff_zero_eq_constantCoeff,
    coeff_fourier, coeff_zero_reducedE4, coeff_one_reducedE4,
    coeff_delta_fl, Nat.add_comm 1, coeff_delta_add_one_fl]
  ring

/-- The Sturm-bound version of the basis comparison in (3.9)--(3.11). -/
private lemma Theta_pow_low_point_fourier (flu : (fl p).UOp = 0) :
    ((fl p).Theta_pow ((p + 3) / 2)).fourier =
      ((δ p : ZMod p) ^ ((p + 3) / 2) •
        (reducedE4 (p := p)).mul (fl p)).fourier := by
  have hw : ((fl p).Theta_pow ((p + 3) / 2)).hasWeight (12 * (δ p : ℤ) + 4) := by
    rw [← Filtration_Theta_pow_low_point flu]
    exact Filtration_spec _
  obtain ⟨g, hg⟩ := hw.exists
  let e := ((reducedE4 (p := p)).mul (fl p)).cast (by ring :
    4 + (δ p : ℤ) * 12 = 12 * (δ p : ℤ) + 4)
  have heq : g = (δ p : ZMod p) ^ ((p + 3) / 2) • e := by
    apply sturm_bound
    intro n hn
    have hdim := ModularFormOver.Basis.dim_le_div_twelve (12 * (δ p : ℤ) + 4)
    have hnle : n ≤ δ p := by omega
    rw [← hg, coeff_Theta_pow, coeff_smul_of_surjective]
    by_cases hlt : n < δ p
    · rw [coeff_lt_delta_fl p hlt, mul_zero]
      have he0 : coeff n e = 0 := by
        change PowerSeries.coeff n ((reducedE4 (p := p)).fourier * (fl p).fourier) = 0
        apply PowerSeries.coeff_mul_of_lt_order
        simpa only [order_fl] using (show (n : ℕ∞) < δ p by exact_mod_cast hlt)
      rw [he0, mul_zero]
    · have hnδ : n = δ p := by omega
      subst n
      change _ = _ * coeff (δ p) ((reducedE4 (p := p)).mul (fl p))
      rw [coeff_delta_fl, coeff_delta_E4_fl]
  apply PowerSeries.ext
  intro n
  change coeff n _ = coeff n _
  rw [hg, heq, coeff_smul_of_surjective, coeff_smul_of_surjective]
  rfl

/-- Equation (3.13), obtained from the coefficient immediately after the leading term. -/
theorem theta_low_point_coefficient_congruence (flu : (fl p).UOp = 0) :
    ((δ p : ZMod p) + 1) ^ ((p + 3) / 2) =
      241 * (δ p : ZMod p) ^ ((p + 3) / 2) := by
  have hδ : -24 * (δ p : ZMod p) = 1 := by
    have h := congrArg (fun n : ℕ => (n : ZMod p)) (delta_exponent p)
    push_cast at h
    simp only [ZMod.natCast_self, zero_mul] at h
    linear_combination -h
  have hc := congrArg (PowerSeries.coeff (δ p + 1)) (Theta_pow_low_point_fourier flu)
  change coeff (δ p + 1) _ = coeff (δ p + 1) _ at hc
  rw [coeff_Theta_pow, coeff_delta_add_one_fl, coeff_smul_of_surjective,
    coeff_delta_add_one_E4_fl] at hc
  simpa only [Nat.cast_add, Nat.cast_one, hδ, mul_one, one_mul, show (240 : ZMod p) -
    24 * (δ p : ZMod p) = 241 by linear_combination hδ, mul_comm] using hc

/-- Theorem 3.1: there is no Ramanujan congruence at the discriminant shift
for a prime at least thirteen. -/
theorem not_RamanujanCongruenceWith_delta : ¬ RamanujanCongruenceWith p (δ p) := by
  intro hcong
  have flu := flu_eq_zero_iff.mpr hcong
  have hc := theta_low_point_coefficient_congruence flu
  have hδ : (-24 : ZMod p) * (δ p : ZMod p) = 1 := by
    have h := congrArg (fun n : ℕ => (n : ZMod p)) (delta_exponent p)
    push_cast at h
    simp only [ZMod.natCast_self, zero_mul] at h
    linear_combination -h
  have ha : (-24 : ZMod p) * ((δ p : ZMod p) + 1) = -23 := by
    linear_combination hδ
  have hpow : (-23 : ZMod p) ^ ((p + 3) / 2) = 241 := by
    calc
      _ = ((-24 : ZMod p) * ((δ p : ZMod p) + 1)) ^ ((p + 3) / 2) := by rw [ha]
      _ = (-24 : ZMod p) ^ ((p + 3) / 2) *
          ((δ p : ZMod p) + 1) ^ ((p + 3) / 2) := mul_pow _ _ _
      _ = 241 * ((-24 : ZMod p) * (δ p : ZMod p)) ^ ((p + 3) / 2) := by
        rw [hc, mul_pow]
        ring
      _ = 241 := by rw [hδ, one_pow, mul_one]
  have hhalf := prime_half (p := p)
  have hexp : ((p + 3) / 2) * 2 = p + 3 := by omega
  -- Squaring and using Frobenius also covers `p = 23` directly.
  have hsq := congrArg (fun a : ZMod p => a ^ 2) hpow
  rw [← pow_mul, hexp, pow_add, ZMod.pow_card] at hsq
  have hz : (221760 : ZMod p) = 0 := by linear_combination hsq
  have hdvd : p ∣ 221760 := (ZMod.natCast_eq_zero_iff 221760 p).mp hz
  have hprime : p.Prime := Fact.out
  rw [show 221760 = 2 ^ 6 * 3 ^ 2 * 5 * 7 * 11 by norm_num] at hdvd
  simp only [hprime.dvd_mul, or_assoc] at hdvd
  have hp13 := hp.AtLeastThirteen
  rcases hdvd with h2 | h3 | h5 | h7 | h11
  · have := Nat.le_of_dvd (by decide : 0 < 2) (hprime.dvd_of_dvd_pow h2)
    omega
  · have := Nat.le_of_dvd (by decide : 0 < 3) (hprime.dvd_of_dvd_pow h3)
    omega
  · have := Nat.le_of_dvd (by decide : 0 < 5) h5
    omega
  · have := Nat.le_of_dvd (by decide : 0 < 7) h7
    omega
  · have := Nat.le_of_dvd (by decide : 0 < 11) h11
    omega
