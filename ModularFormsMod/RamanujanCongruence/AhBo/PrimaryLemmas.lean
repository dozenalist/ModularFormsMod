/-
Copyright (c) 2026 Carter Hastings. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carter Hastings
-/

module

public import ModularFormsMod.RamanujanCongruence.AhBo.FluEqZero

/-!
# Theta-filtration steps used in the descent argument

Positive filtration drops and the return at the end of the theta cycle.
-/

@[expose] public section

open ModularFormMod ModularFormMod.ZMod

variable {p : ℕ} [hp : isLargePrime p]

lemma Filtration_Theta_iff' {k} (f : 𝓜 p k) {m j : ℕ} (h : m = j + 1) :
  (f.Theta_pow m).Filtration = (f.Theta_pow j).Filtration + (p + 1) ↔
    ¬ ↑p ∣ (f.Theta_pow j).Filtration := by
  subst h
  simpa only [Theta_pow_succ, Filtration_cast] using Filtration_Theta_iff <| f.Theta_pow j


lemma Filtration_Theta_congruence_of_dvd {k} (f : 𝓜 p k)
  [hfT : NeZero f.Theta] (ldiv : ↑p ∣ f.Filtration) :
    ∃ α > 0, f.Theta.Filtration = f.Filtration + (p + 1) - α * (p - 1) := by
  have hpmod : 0 < (p : ℤ) - 1 := by
    have hp5 := hp.AtLeastFive
    omega
  have hf0 : f ≠ 0 := by
    intro h
    subst f
    exact hfT.out (by simp)
  have hcong : f.Theta.Filtration ≡ f.Filtration + (p + 1) [ZMOD (p - 1 : ℤ)] := by
    calc
      f.Theta.Filtration ≡ (k + (p + 1)) [ZMOD (p - 1 : ℤ)] :=
        Filtration_congr f.Theta hfT.out
      _ ≡ f.Filtration + (p + 1) [ZMOD (p - 1 : ℤ)] :=
        (Filtration_congr f hf0).add_right (p + 1) |>.symm
  obtain ⟨α, hα⟩ := Int.modEq_iff_add_fac.mp hcong
  have hbase : f.Theta.Filtration = f.Filtration + (p + 1) - α * (p - 1) := by
    rw [hα]
    ring
  have bound : f.Theta.Filtration < f.Filtration + (p + 1) :=
    lt_of_le_of_ne (Filtration_Theta_le f) fun h => (Filtration_Theta_iff f).1 h ldiv
  rw [hbase] at bound
  have hprod : 0 < α * (p - 1) := by omega
  have hαpos : 0 < α := by
    by_contra h
    have hαnonpos : α ≤ 0 := by omega
    have hnonpos : α * (p - 1) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg hαnonpos (le_of_lt hpmod)
    omega
  exact ⟨α, hαpos, hbase⟩


lemma Filtration_Theta_congruence_of_dvd' {k} (f : 𝓜 p k) {m j : ℕ}
    [hfT : NeZero (f.Theta_pow m)] (ldiv : (p : ℤ) ∣ (f.Theta_pow j).Filtration)
    (h : m = j + 1) :
    ∃ α > 0, (f.Theta_pow m).Filtration =
      (f.Theta_pow j).Filtration + (p + 1) - α * (p - 1) := by
  subst h
  have hne : NeZero ((f.Theta_pow j).Theta) := by
    refine ⟨?_⟩
    intro hz
    apply hfT.out
    rw [Theta_pow_succ, hz]
    apply ext
    rfl
  simpa only [Theta_pow_succ, Filtration_cast] using
    (Filtration_Theta_congruence_of_dvd (f.Theta_pow j) ldiv)


theorem le_Filtration_Theta_pow_fl (m : ℕ) :
    (fl p).Filtration ≤ ((fl p).Theta_pow m).Filtration :=
  Filtration_fl p ▸ le_Filtration _ NeZero.out fun n nlt => by
    simp only [coeff_Theta_pow, coeff_lt_delta_fl p nlt, mul_zero]

theorem Filtration_Theta_fl : (fl p).Theta.Filtration = 12 * δ p + (p + 1) := by
  rw [← Filtration_fl, Filtration_Theta_iff (fl p)|>.2 not_dvd_Filtration_fl]


theorem Filtration_Theta_pow_card : ((fl p).Theta_pow p).Filtration = 12 * δ p + (p + 1) := by
  rw [Filtration_eq_of_fourier_eq (Theta_pow_card (fl p)), Filtration_Theta_fl]


theorem Filtration_Theta_pow_sub_one_of_not_dvd :
  ¬ ↑p ∣ ((fl p).Theta_pow (p - 1)).Filtration →
    ((fl p).Theta_pow (p - 1)).Filtration = 12 * δ p  := by
  intro h
  have hp5 : 5 ≤ p := isLargePrime.AtLeastFive
  have hsucc : p = p - 1 + 1 := by omega
  have hstep := (Filtration_Theta_iff' (fl p) hsucc).mpr h
  rw [Filtration_Theta_pow_card] at hstep
  omega


theorem Filtration_Theta_pow_sub_one (flu : (fl p).UOp = 0) :
    ((fl p).Theta_pow (p - 1)).Filtration = 12 * δ p := by
  apply Filtration_Theta_pow_sub_one_of_not_dvd
  rw [Filtration_eq_of_fourier_eq (g := fl p)]
  · exact not_dvd_Filtration_fl
  · rw [Eq.comm, ← sub_eq_zero, ← UOp_pow_card,
      flu, pow_fourier, zero_fourier, zero_pow]
    exact NeZero.out
