/-
Copyright (c) 2026 Carter Hastings. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carter Hastings
-/

import ModularFormsMod.RamanujanCongruence.Partition
import ModularFormsMod.ModularFormMod.ZMod.Filtration

/-!
# Shared facts for Ramanujan congruences

The reduced discriminant has expansion `q - 24q² + …`. The form `fl p` is its
`δ p`-th power, where `δ p = (p² - 1) / 24`. Its first nonzero coefficient
is one in degree `δ p`.

This file also contains the Euler-product factorization, arithmetic of the
discriminant shift, and initial theta-filtration formula used by both the
Ahlgren–Boylan and Kiming–Olsson arguments.
-/

noncomputable section


open ModularFormMod PInteger


namespace ModularFormMod.ZMod

/-- The exponent of the discriminant used in Ramanujan congruences. -/
def delta (p : ℕ) : ℕ := (p ^ 2 - 1) / 24

scoped notation "δ" => delta


/-- The integral discriminant, extended to the local integers and reduced modulo `p`. -/
def discriminant {p : ℕ} [Fact p.Prime] : 𝓜 p 12 :=
  (ModularFormOver.discriminant.tower ℤ(p)).Reduce reduce


scoped notation (priority := high) "Δ" =>
  ModularFormMod.ZMod.discriminant


variable (p : ℕ) [Fact p.Prime]

/-- The coefficients of the reduced discriminant are the finite discriminant-product
coefficients over `ZMod p`. -/
theorem coeff_discriminant (n : ℕ) :
    coeff n (Δ : 𝓜 p 12) = PowerSeries.coeff n (discProduct (α := ZMod p) n) := by
  change reduce (ModularFormOver.coeff ℤ n ModularFormOver.discriminant ℤ(p)) = _
  rw [ModularFormOver.coeff_discriminant, map_coeff_discProduct]

@[simp] theorem coeff_zero_discriminant : coeff 0 (Δ : 𝓜 p 12) = 0 := by
  change reduce (ModularFormOver.coeff ℤ 0 ModularFormOver.discriminant ℤ(p)) = _
  simp

@[simp] theorem coeff_one_discriminant : coeff 1 (Δ : 𝓜 p 12) = 1 := by
  change reduce (ModularFormOver.coeff ℤ 1 ModularFormOver.discriminant ℤ(p)) = _
  simp

@[simp] theorem coeff_two_discriminant : coeff 2 (Δ : 𝓜 p 12) = -24 := by
  change reduce (ModularFormOver.coeff ℤ 2 ModularFormOver.discriminant ℤ(p)) = _
  rw [ModularFormOver.coeff_two_discriminant]
  simpa only [Int.cast_neg, Int.cast_ofNat] using
    (map_intCast (reduce (p := p)) (-24))

/-- The reduced discriminant vanishes to order exactly one. -/
@[simp] theorem order_discriminant : (Δ : 𝓜 p 12).fourier.order = 1 := by
  apply PowerSeries.order_eq_nat.mpr
  constructor
  · change coeff 1 (Δ : 𝓜 p 12) ≠ 0
    simp
  · intro i hi
    have : i = 0 := by omega
    subst i
    exact coeff_zero_discriminant p

/-- The reduced discriminant has filtration twelve at every prime. -/
@[simp] theorem Filtration_discriminant : (Δ : 𝓜 p 12).Filtration = 12 := by
  apply le_antisymm
  · exact Filtration_le_of_nonneg (Δ : 𝓜 p 12).hasWeight_self (by norm_num)
  · have hne : (Δ : 𝓜 p 12) ≠ 0 := by
      intro h
      have hc := coeff_one_discriminant p
      simp [h] at hc
    simpa using le_Filtration (m := 1) (Δ : 𝓜 p 12) hne (by
      intro n hn
      have : n = 0 := by omega
      subst n
      exact coeff_zero_discriminant p)

/-- The discriminant power used to study Ramanujan congruences modulo `p`. -/
def fl : 𝓜 p ((δ p : ℤ) * 12) := (Δ : 𝓜 p 12).pow (δ p)

@[simp] theorem fl_fourier :
    (fl p).fourier = (Δ : 𝓜 p 12).fourier ^ δ p := rfl

/-- The order of vanishing of `fl p` is its discriminant exponent. -/
@[simp] theorem order_fl : (fl p).fourier.order = δ p := by
  simp only [fl_fourier, PowerSeries.order_pow, order_discriminant, nsmul_one]

/-- All coefficients preceding the leading term of `fl p` vanish. -/
theorem coeff_lt_delta_fl {n : ℕ} (h : n < δ p) : coeff n (fl p) = 0 := by
  apply PowerSeries.coeff_of_lt_order
  rw [order_fl]
  exact_mod_cast h

/-- Removing the initial power of `q` from `fl p` gives a power of the normalized
discriminant series. -/
theorem coeff_fl_add_delta (n : ℕ) :
    coeff (n + δ p) (fl p) =
      PowerSeries.coeff n ((Δ : 𝓜 p 12).fourier.divXPowOrder ^ δ p) := by
  have hfactor : (Δ : 𝓜 p 12).fourier =
      PowerSeries.X * (Δ : 𝓜 p 12).fourier.divXPowOrder := by
    simpa only [order_discriminant, ENat.toNat_one, pow_one] using
      (PowerSeries.X_pow_order_mul_divXPowOrder (f := (Δ : 𝓜 p 12).fourier)).symm
  change PowerSeries.coeff (n + δ p) ((Δ : 𝓜 p 12).fourier ^ δ p) = _
  conv_lhs => rw [hfactor, mul_pow, PowerSeries.coeff_X_pow_mul]

/-- The leading coefficient of `fl p` is one. -/
@[simp] theorem coeff_delta_fl : coeff (δ p) (fl p) = 1 := by
  simpa [PowerSeries.coeff_zero_eq_constantCoeff,
    PowerSeries.constantCoeff_divXPowOrder, order_discriminant,
    coeff_fourier] using coeff_fl_add_delta p 0

/-- The constant coefficient accounts for the zero exponents at the primes two and three. -/
@[simp] theorem coeff_zero_fl : coeff 0 (fl p) = if δ p = 0 then 1 else 0 := by
  split_ifs with h
  · simpa [h] using coeff_delta_fl p
  · exact coeff_lt_delta_fl p (Nat.pos_of_ne_zero h)

/-- The coefficient immediately after the leading coefficient of `fl p`. -/
theorem coeff_delta_add_one_fl :
    coeff (δ p + 1) (fl p) = -24 * (δ p : ZMod p) := by
  rw [Nat.add_comm, coeff_fl_add_delta, PowerSeries.coeff_one_pow]
  simp [PowerSeries.coeff_divXPowOrder, PowerSeries.constantCoeff_divXPowOrder,
    order_discriminant, coeff_fourier]
  ring

/-- The discriminant power is nonzero, including when its exponent is zero. -/
instance fl_ne_zero : NeZero (fl p) where
  out := by
    intro h
    have hc := coeff_delta_fl p
    simp [h] at hc


/-- The discriminant power has filtration twelve times its exponent. -/
@[simp] theorem Filtration_fl : (fl p).Filtration = 12 * (δ p : ℤ) := by
  apply le_antisymm
  · simpa only [mul_comm] using
      Filtration_le_of_nonneg (fl p).hasWeight_self (by positivity)
  · exact le_Filtration (fl p) NeZero.out fun n hn => coeff_lt_delta_fl p hn

end ModularFormMod.ZMod

open ModularFormMod.ZMod Finset
open scoped PowerSeries.WithPiTopology

theorem delta_exponent (p : ℕ) [isLargePrime p] : 24 * δ p + 1 = p * p := by
  have hp : p.Prime := Fact.out
  have hp5 : 5 ≤ p := isLargePrime.AtLeastFive
  have hc : p.Coprime 24 := by
    apply hp.coprime_iff_not_dvd.mpr
    intro h
    have hd : p ∣ 2 ^ 3 * 3 := by simpa using h
    rcases hp.dvd_mul.mp hd with h2 | h3
    · have := Nat.le_of_dvd (by decide : 0 < 2) (hp.dvd_of_dvd_pow h2)
      omega
    · have := Nat.le_of_dvd (by decide : 0 < 3) h3
      omega
  have hfinite : ∀ a : Fin 24, a.val.Coprime 24 → (a.val * a.val) % 24 = 1 := by decide
  have hres : (p % 24).Coprime 24 := by
    change Nat.gcd (p % 24) 24 = 1
    rw [← Nat.gcd_rec, Nat.gcd_comm]
    exact hc
  have hmod : (p * p) % 24 = 1 := by
    simpa only [Nat.mul_mod, Nat.mod_mod] using
      hfinite ⟨p % 24, Nat.mod_lt _ (by decide)⟩ hres
  dsimp [delta]
  rw [pow_two]
  omega

theorem exists_euler_series (p : ℕ) [Fact p.Prime] :
    ∃ E : PowerSeries (ZMod p), E.constantCoeff = 1 ∧
      (discriminant : 𝓜 p 12).fourier = PowerSeries.X * E ^ 24 ∧
      E * PowerSeries.mk (fun n : ℕ => (partition n : ZMod p)) = 1 := by
  classical
  let : TopologicalSpace (ZMod p) := ⊥
  let : DiscreteTopology (ZMod p) := ⟨rfl⟩
  let e : ℕ → PowerSeries (ZMod p) := fun i => 1 - PowerSeries.X ^ (i + 1)
  let E := ∏' i, e i
  let P : PowerSeries (ZMod p) := PowerSeries.mk fun n => (partition n : ZMod p)
  have he := PowerSeries.WithPiTopology.multipliable_one_sub_X_pow (ZMod p)
  have hE : Filter.Tendsto (fun m => ∏ i ∈ range m, e i) Filter.atTop (nhds E) :=
    he.tendsto_prod_tprod_nat
  have hP : Filter.Tendsto (fun m => partitionProduct (α := ZMod p) m)
      Filter.atTop (nhds P) := by
    rw [PowerSeries.WithPiTopology.tendsto_iff_coeff_tendsto]
    intro n
    apply tendsto_atTop_of_eventually_const (i₀ := n)
    intro m hm
    simpa only [P, PowerSeries.coeff_mk] using
      (partition_eq_coeff_Product (α := ZMod p) hm).symm
  have hD : Filter.Tendsto (discProduct (α := ZMod p)) Filter.atTop
      (nhds (discriminant : 𝓜 p 12).fourier) := by
    rw [PowerSeries.WithPiTopology.tendsto_iff_coeff_tendsto]
    intro n
    apply tendsto_atTop_of_eventually_const (i₀ := n)
    intro m hm
    rw [coeff_fourier, coeff_discriminant]
    exact discProduct_coeff_le hm le_rfl
  have hDE : (discriminant : 𝓜 p 12).fourier = PowerSeries.X * E ^ 24 := by
    apply tendsto_nhds_unique hD
    have hlim : Filter.Tendsto
        (fun m => PowerSeries.X * (∏ i ∈ range m, e i) ^ 24)
        Filter.atTop (nhds (PowerSeries.X * E ^ 24)) :=
      tendsto_const_nhds.mul (hE.pow 24)
    have hfn : (fun m => PowerSeries.X * (∏ i ∈ range m, e i) ^ 24) =
        discProduct (α := ZMod p) := by
      funext m
      simp only [discProduct, e, Finset.prod_pow]
    rwa [hfn] at hlim
  have hfinite (m : ℕ) : (∏ i ∈ range m, e i) * partitionProduct (α := ZMod p) m = 1 := by
    rw [partitionProduct, ← Finset.prod_mul_distrib]
    apply Finset.prod_eq_one
    intro i hi
    exact PowerSeries.mul_inv_cancel _ (by simp [e])
  have hEP : E * P = 1 := by
    have hlim := hE.mul hP
    simp_rw [hfinite] at hlim
    exact tendsto_nhds_unique hlim tendsto_const_nhds
  have hP0 : P.constantCoeff = 1 := by
    simp [P, partition]
  refine ⟨E, ?_, hDE, hEP⟩
  simpa only [_root_.map_mul, _root_.map_one, hP0, mul_one] using
    congrArg PowerSeries.constantCoeff hEP

theorem partition_of_neg {n : ℤ} (hn : n < 0) : partition n = 0 := by
  cases n with
  | ofNat n =>
    have : (0 : ℤ) ≤ Int.ofNat n := Int.natCast_nonneg n
    omega
  | negSucc n => rfl

theorem coeff_shift_partition (p d n : ℕ) :
    PowerSeries.coeff n (PowerSeries.X ^ d *
      PowerSeries.mk (fun k : ℕ => (partition k : ZMod p))) =
        (partition ((n : ℤ) - d) : ZMod p) := by
  rw [PowerSeries.coeff_X_pow_mul']
  split_ifs with h
  · rw [PowerSeries.coeff_mk, Int.natCast_sub h]
  · rw [partition_of_neg (by omega), Nat.cast_zero]

/-- The discriminant shift identity over the integers. -/
theorem delta_exponent_int {p : ℕ} [isLargePrime p] :
    24 * (δ p : ℤ) + 1 = (p : ℤ) * p := by
  exact_mod_cast delta_exponent p

/-- Factor the discriminant power into a p-th power and the shifted partition series. -/
theorem fl_euler_factor (p : ℕ) [isLargePrime p] :
    ∃ E : PowerSeries (ZMod p), E.constantCoeff = 1 ∧
      (fl p).fourier = (E ^ p) ^ p *
        (PowerSeries.X ^ δ p * PowerSeries.mk (fun n : ℕ => (partition n : ZMod p))) := by
  obtain ⟨E, hE0, hD, hEP⟩ := exists_euler_series p
  refine ⟨E, hE0, ?_⟩
  rw [fl_fourier, hD, mul_pow, ← pow_mul]
  calc
    PowerSeries.X ^ δ p * E ^ (24 * δ p) =
        PowerSeries.X ^ δ p * E ^ (24 * δ p) *
          (E * PowerSeries.mk (fun n : ℕ => (partition n : ZMod p))) := by rw [hEP, mul_one]
    _ = _ := by
      rw [← pow_mul, ← delta_exponent p, pow_add, pow_one]
      ring

variable {p : ℕ} [hp : isLargePrime p]

theorem delta_cast_ne_zero : (δ p : ZMod p) ≠ 0 := by
  intro hz
  have hcast := congrArg (fun n : ℕ => (n : ZMod p)) (delta_exponent p)
  simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] at hcast
  rw [hz] at hcast
  simp at hcast

theorem twelve_cast_ne_zero : (12 : ZMod p) ≠ 0 := by
  intro hz
  have hdvd := (ZMod.natCast_eq_zero_iff 12 p).mp hz
  have hprime : p.Prime := Fact.out
  have hp5 : 5 ≤ p := isLargePrime.AtLeastFive
  rcases hprime.dvd_mul.mp (show p ∣ 3 * 4 from by simpa using hdvd) with h3 | h4
  · have := Nat.le_of_dvd (by decide : 0 < 3) h3
    omega
  · have := Nat.le_of_dvd (by decide : 0 < 4) h4
    omega

theorem not_dvd_Filtration_fl : ¬ (p : ℤ) ∣ (fl p).Filtration := by
  rw [Filtration_fl]
  intro hdiv
  have hzero : (12 : ZMod p) * (δ p : ZMod p) = 0 := by
    have hz := (ZMod.intCast_zmod_eq_zero_iff_dvd
      (12 * (δ p : ℤ)) p).2 hdiv
    simpa only [Int.cast_mul, Int.cast_ofNat, Int.cast_natCast] using hz
  exact (mul_ne_zero twelve_cast_ne_zero delta_cast_ne_zero) hzero

theorem delta_pos : δ p > 0 := by
  grw [delta, hp.AtLeastFive]
  grind


instance (m : ℕ) : NeZero ((fl p).Theta_pow m) where
  out := fun h => by
    have hc := congrArg (coeff (δ p)) h
    rw [coeff_Theta_pow, coeff_delta_fl, coeff_zero] at hc
    exact (pow_ne_zero m delta_cast_ne_zero) (by simpa only [mul_one] using hc)

/-- Twice the rounded-up half of an odd prime. -/
theorem prime_half : 2 * ((p + 1) / 2) = p + 1 := by
  have hp : 5 ≤ p := isLargePrime.AtLeastFive
  obtain ⟨u, hu⟩ := (Fact.out : p.Prime).odd_of_ne_two (by omega)
  omega

private theorem not_dvd_initial_weight (m : ℕ) (hm : m < (p + 1) / 2) :
    ¬ (p : ℤ) ∣ 12 * (δ p : ℤ) + m * (p + 1) := by
  intro hdvd
  have hp : 5 ≤ p := isLargePrime.AtLeastFive
  have hδ : 24 * (δ p : ℤ) + 1 = (p : ℤ) * p := by
    exact_mod_cast delta_exponent p
  have hhalf := prime_half (p := p)
  have hd : (p : ℤ) ∣ 2 * (m : ℤ) - 1 := by
    convert dvd_sub (dvd_mul_of_dvd_right hdvd 2)
      (dvd_mul_right (p : ℤ) ((p : ℤ) + 2 * m)) using 1
    nlinarith
  by_cases hm0 : m = 0
  · have h1 : (p : ℤ) ∣ 1 := by simpa [hm0] using hd
    have := Int.le_of_dvd (by norm_num : (0 : ℤ) < 1) h1
    omega
  have hsmall : 0 < 2 * (m : ℤ) - 1 ∧ 2 * (m : ℤ) - 1 < p := by omega
  have := Int.eq_zero_of_dvd_of_nonneg_of_lt hsmall.1.le hsmall.2 hd
  omega

/-- The initial theta steps of the discriminant power all raise filtration. -/
theorem Filtration_Theta_pow_initial {m : ℕ} (hm : m ≤ (p + 1) / 2) :
    ((fl p).Theta_pow m).Filtration = 12 * (δ p : ℤ) + m * (p + 1) := by
  induction m with
  | zero => simp [Theta_pow]
  | succ m ih =>
    have hi := ih (by omega)
    rw [Theta_pow_succ, Filtration_cast, (Filtration_Theta_iff _).mpr (by
      rw [hi]
      exact not_dvd_initial_weight m (by omega)), hi]
    push_cast
    ring

/-- A nonzero U image of the discriminant power has filtration at least twelve. -/
theorem twelve_le_Filtration_UOp_fl (hf : (fl p).UOp ≠ 0) :
    12 ≤ (fl p).UOp.Filtration := by
  apply le_Filtration (m := 1) (fl p).UOp hf
  intro n hn
  have : n = 0 := by omega
  subst n
  rw [coeff_zero_UOp]
  exact coeff_lt_delta_fl p delta_pos
