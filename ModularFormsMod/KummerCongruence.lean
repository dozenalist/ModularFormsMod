import Mathlib.NumberTheory.Bernoulli
import Mathlib.Data.Nat.Squarefree

/-!
# Kummer's congruence for Bernoulli numbers

This file records part (2) of Theorem 1.35.  For a prime `p`, the residue of a
`p`-integral rational number is represented in `ZMod p` by reducing its
numerator and multiplying by the inverse of its denominator.

The substantive theorem below is Kummer's congruence.  Its proof is the
remaining number-theoretic ingredient needed here; the surrounding API makes
the intended statement precise and exposes the two auxiliary assertions
(`p`-integrality and equality of residues) separately.
-/



section ImportedKummer



@[expose] public section


open Nat Finset Finset.Nat PowerSeries

variable (A : Type*) [CommRing A] [Algebra ℚ A]



namespace Bernoulli

/- Indicator function that is `1` if `(p - 1) ∣ k` and `0` otherwise. -/
private noncomputable def vonStaudtIndicator (k p : ℕ) : ℚ :=
  if (p - 1) ∣ k then 1 else 0

/- The primes `q < 2k + 2` with `(q - 1) ∣ 2k` — the primes appearing in the
von Staudt-Clausen correction sum. -/
private abbrev vonStaudtPrimes (k : ℕ) : Finset ℕ :=
  (range (k + 2)).filter fun q ↦ q.Prime ∧ (q - 1) ∣ k

/- Over `ZMod p`, the nonzero `l`-th power sum equals the negative indicator of `(p - 1) ∣ l`. -/
private lemma sum_pow_add_indicator_eq_zero {p : ℕ} (l : ℕ) [Fact p.Prime] :
    (∑ v ∈ Ico 1 p, (v : ZMod p) ^ l) + (if (p - 1) ∣ l then (1 : ZMod p) else 0) = 0 := by
  have hbij : (∑ v ∈ Ico 1 p, (v : ZMod p) ^ l) = ∑ u : (ZMod p)ˣ, (u : ZMod p) ^ l :=
    Finset.sum_bij'
      (fun v hv ↦ Units.mk0 (v : ZMod p) (mt (ZMod.natCast_eq_zero_iff v p).mp (by
        grind [not_dvd_of_pos_of_lt])))
      (fun u _ ↦ (u : ZMod p).val)
      (fun _ _ ↦ Finset.mem_univ _)
      (fun u _ ↦ by grind [u.ne_zero, ZMod.val_ne_zero, ZMod.val_lt])
      (fun v hv ↦ by simp [ZMod.val_cast_of_lt (Finset.mem_Ico.mp hv).2])
      (fun u _ ↦ Units.ext (ZMod.natCast_zmod_val _))
      (fun _ _ ↦ rfl)
  rw [hbij, FiniteField.sum_pow_units, ZMod.card]
  grind

/- A rational number `x` is `p`-integral if `p` does not divide its denominator, i.e. it lies in
the valuation subring of the `p`-adic valuation. -/
private abbrev pIntegral (p : ℕ) (x : ℚ) [Fact p.Prime] : Prop := x ∈ (Rat.padicValuation p).integer

private lemma pIntegral_iff_not_dvd_den {p : ℕ} [Fact p.Prime] {x : ℚ} :
    pIntegral p x ↔ ¬ p ∣ x.den :=
  Rat.padicValuation_le_one_iff

@[simp]
lemma Rat.padicValuation_natCast (p : ℕ) [Fact p.Prime] (x : ℕ) :
    Rat.padicValuation p x = Int.padicValuation p x :=
  rfl

/- Dividing a `p`-integral rational by a `p`-coprime nat stays `p`-integral. -/
private lemma pIntegral_div_natCast {p : ℕ} [Fact p.Prime] {a : ℚ} {n : ℕ}
    (ha : pIntegral p a) (hn : ¬ p ∣ n) : pIntegral p (a / n) := by
  have hvn : Rat.padicValuation p n = 1 := by
    simpa [Int.padicValuation_eq_one_iff, Int.natCast_dvd_natCast]
  rw [div_eq_mul_inv]
  exact mul_mem ha (by simp [Valuation.mem_integer_iff, hvn])

/- Denominators of the "other primes" part of the indicator sum
stay coprime to a fixed prime `p`. -/
private lemma prod_one_div_prime_den_coprime (k : ℕ) {p : ℕ} [Fact p.Prime] :
    (∏ q ∈ vonStaudtPrimes k with q ≠ p, ((1 : ℚ) / q).den).Coprime p := by
  refine Nat.Coprime.prod_left fun q hq ↦ ?_
  simp only [Finset.mem_filter, Finset.mem_range] at hq
  obtain ⟨⟨_, hq_prime, _⟩, hne⟩ := hq
  rw [show ((1 : ℚ) / q).den = q by simp [hq_prime.ne_zero]]
  exact (Nat.coprime_primes hq_prime Fact.out).mpr hne

/- Splits the prime-indexed correction sum into the `p`-term (`vonStaudtIndicator / p`)
plus the rest. -/
private lemma sum_one_div_prime_eq_indicator_div_add {k p : ℕ} (hk : k > 0) [Fact p.Prime] :
    (∑ q ∈ vonStaudtPrimes k, (1 : ℚ) / q) =
    vonStaudtIndicator k p / p + ∑ q ∈ vonStaudtPrimes k with q ≠ p, (1 : ℚ) / q := by
  rw [Finset.sum_congr (Finset.filter_ne' (vonStaudtPrimes k) p) fun _ _ ↦ rfl]
  by_cases hdvd : (p - 1) ∣ k
  · have hp_mem : p ∈ vonStaudtPrimes k := Finset.mem_filter.mpr
      ⟨Finset.mem_range.mpr (by have := Nat.le_of_dvd (by lia) hdvd; lia), Fact.out, hdvd⟩
    rw [← Finset.add_sum_erase _ _ hp_mem]
    simp [vonStaudtIndicator, hdvd]
  · rw [Finset.erase_eq_of_notMem fun h ↦ hdvd (Finset.mem_filter.mp h).2.2]
    simp [vonStaudtIndicator, hdvd]

/- If the `p`-adic valuation of `M` is at most `N`, then `p^N / M` is `p`-integral. -/
private lemma pIntegral_pow_div {p M N : ℕ} [Fact p.Prime] (hM : M ≠ 0)
    (hv : M.factorization p ≤ N) : pIntegral p ((p : ℚ) ^ N / M) := by
  set e := M.factorization p
  set M' := M / p ^ e
  have hM'_cop : M'.Coprime p := (Nat.coprime_ordCompl Fact.out hM).symm
  have hp_ne : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.Prime.ne_zero Fact.out)
  -- Rewrite p^N / M as p^(N-e) / M' where M' = M / p^e is coprime to p
  have hdecomp : p ^ e * M' = M := Nat.ordProj_mul_ordCompl_eq_self M p
  have hM_eq : (M : ℚ) = ↑(p ^ e) * ↑M' := by rw [← hdecomp]; simp
  have hrw : (p : ℚ) ^ N / M = (p : ℚ) ^ (N - e) / M' := by
    rw [hM_eq, Nat.cast_pow, div_mul_eq_div_div]
    congr 1
    rw [div_eq_iff (pow_ne_zero e hp_ne), ← pow_add, Nat.sub_add_cancel hv]
  have hM'_eq : ((p : ℚ) ^ (N - e) / (M' : ℚ)) = Rat.divInt (p ^ (N - e) : ℤ) (M' : ℤ) := by
    norm_cast
    simp
  rw [hrw]
  exact pIntegral_iff_not_dvd_den.2 ((Nat.Prime.coprime_iff_not_dvd Fact.out).1
    (hM'_cop.coprime_dvd_left (by
      rw [hM'_eq]; exact Int.natCast_dvd_natCast.mp (Rat.den_dvd _ _))).symm)

/- Main valuation estimate behind the contradiction step for even-index summands. -/
private lemma factorization_succ_le_sub_one {p d : ℕ} [Fact p.Prime] (hd : d ≥ 2) :
    (d + 1).factorization p ≤ d - 1 := by
  by_cases hcase : p = 2 ∧ d = 2
  · obtain ⟨rfl, rfl⟩ := hcase
    simp [Nat.factorization_eq_zero_of_not_dvd (by decide : ¬(2 ∣ 3))]
  · apply Nat.factorization_le_of_le_pow
    have hp2 := (Fact.out : p.Prime).two_le
    suffices ∀ n : ℕ, n ≥ 2 → ¬(p = 2 ∧ n = 2) → n + 1 ≤ p ^ (n - 1) from this d hd hcase
    intro n hn hne'
    induction hn with
    | refl => norm_num at hne' ⊢; lia
    | @step m hm IH =>
      by_cases hm2 : p = 2 ∧ m = 2
      · obtain ⟨rfl, rfl⟩ := hm2; norm_num
      · calc m + 1 + 1 ≤ p ^ (m - 1) + 1 := by linarith [IH hm2]
          _ ≤ p ^ (m - 1) * p := by nlinarith [Nat.one_le_pow (m - 1) p (by lia)]
          _ = p ^ m := by rw [show m = m - 1 + 1 by lia]; exact pow_succ ..

/- Multiplicative variant of the binomial coefficient denominator rewrite
as in Rado's summand. -/
private lemma choose_two_mul_succ_mul_div_eq {k m : ℕ} (x : ℚ) (hm_lt : m < k) :
    ((2 * k + 1).choose (2 * m) : ℚ) * x / (2 * k + 1) =
    ((2 * k).choose (2 * m) : ℚ) * x / (2 * k - 2 * m + 1) := by
  rw [div_eq_div_iff (by norm_cast) (by norm_cast; lia), mul_right_comm _ x, mul_right_comm _ x]
  refine congrArg (· * x) ?_
  rw [show (2 * (k : ℚ) - 2 * (m : ℚ) + 1) = (↑(2 * k + 1 - 2 * m) : ℚ) by norm_cast; lia]
  exact_mod_cast Nat.choose_mul_succ_eq (2 * k) (2 * m) |>.symm

/- `p`-integrality of the core even-index summand after denominator normalization. -/
private lemma pIntegral_choose_mul_pow_div {k m p : ℕ} (hm_lt : m < k) [Fact p.Prime]
    (hd : 2 * k - 2 * m ≥ 2) :
    pIntegral p (((2 * k).choose (2 * m) : ℚ) * p ^ (2 * k - 2 * m - 1) / (2 * k - 2 * m + 1)) := by
  set d := 2 * k - 2 * m with hd_def
  have ⟨hd_plus_one_ne_zero, h_exp, hkm⟩ :
      d + 1 ≠ 0 ∧ 2 * k - 2 * m - 1 = d - 1 ∧ 2 * m ≤ 2 * k := by lia
  have h_denom_rat : (2 * (k : ℚ) - 2 * m + 1) = ((d + 1 : ℕ) : ℚ) := by
    simp only [hd_def]; push_cast [Nat.cast_sub hkm]; ring
  rw [h_exp, h_denom_rat, mul_div_assoc]
  exact mul_mem (natCast_mem _ ((2 * k).choose (2 * m)))
    (pIntegral_pow_div hd_plus_one_ne_zero (factorization_succ_le_sub_one hd))

/- Uses the induction hypothesis on `B_{2m} + e_{2m}(p)/p`
to prove `p`-integrality of the even term. -/
private lemma pIntegral_bernoulli_even_term {k m p : ℕ} (hm_lt : m < k) [Fact p.Prime]
    (ih : pIntegral p (bernoulli (2 * m) + vonStaudtIndicator (2 * m) p / p)) :
    pIntegral p (bernoulli (2 * m) * ((2 * k + 1).choose (2 * m)) *
      (p : ℚ) ^ (2 * k - 2 * m) / (2 * k + 1)) := by
  have hp_ne : (p : ℚ) ≠ 0 := mod_cast (Nat.Prime.ne_zero Fact.out)
  set P := (p : ℚ) ^ (2 * k - 2 * m - 1)
  have hpow : (p : ℚ) ^ (2 * k - 2 * m) = P * p := by
    rw [show 2 * k - 2 * m = (2 * k - 2 * m - 1) + 1 by lia, pow_succ]
  have hdecomp : bernoulli (2 * m) * ((2 * k + 1).choose (2 * m)) *
      (p : ℚ) ^ (2 * k - 2 * m) / (2 * k + 1) =
    (bernoulli (2 * m) + vonStaudtIndicator (2 * m) p / p) *
      ((2 * k + 1).choose (2 * m)) * (p : ℚ) ^ (2 * k - 2 * m) / (2 * k + 1) -
    vonStaudtIndicator (2 * m) p * ((2 * k + 1).choose (2 * m)) *
      P / (2 * k + 1) := by rw [hpow]; field_simp [hp_ne]; ring
  rw [hdecomp]
  have hcmp := pIntegral_choose_mul_pow_div (p := p) hm_lt (by lia)
  have H x := choose_two_mul_succ_mul_div_eq x hm_lt
  apply sub_mem
  · rw [mul_assoc, mul_div_assoc]
    apply mul_mem ih
    have hpow_mul : ((2 * k).choose (2 * m) : ℚ) * (p : ℚ) ^ (2 * k - 2 * m) /
        (2 * k - 2 * m + 1) =
        (p : ℚ) * (((2 * k).choose (2 * m) : ℚ) * P / (2 * k - 2 * m + 1)) := by
      rw [hpow]; ring
    rw [H, hpow_mul]
    exact mul_mem (natCast_mem _ p) hcmp
  · unfold vonStaudtIndicator
    split_ifs
    · grind
    · simp

/- The full remainder sum in Faulhaber's formula is `p`-integral. -/
private lemma pIntegral_faulhaber_sum {k p : ℕ} [Fact p.Prime]
    (ih : ∀ m < k, 0 < m → pIntegral p (bernoulli (2 * m) + vonStaudtIndicator (2 * m) p / p)) :
    pIntegral p (∑ i ∈ range (2 * k),
      bernoulli i * ((2 * k + 1).choose i) * p ^ (2 * k - i) / (2 * k + 1)) := by
  refine (Rat.padicValuation p).map_sum_le fun i hi ↦ ?_
  rw [Finset.mem_range] at hi
  rcases i with _ | _ | i
  · simp only [bernoulli_zero, one_mul, Nat.choose_zero_right, Nat.cast_one, Nat.sub_zero]
    exact_mod_cast pIntegral_pow_div (by lia)
      (factorization_succ_le_sub_one (by lia) |>.trans tsub_le_self)
  · rw [zero_add, Nat.choose_one_right, bernoulli_one]
    push_cast
    field_simp
    obtain rfl | hp2 := eq_or_ne p 2
    · push_cast
      rw [show 2 * k - 1 = (2 * k - 2) + 1 by lia, pow_succ, mul_div_cancel_right₀ _ two_ne_zero]
      exact_mod_cast Int.padicValuation_le_one ..
    · rw [Valuation.map_neg]
      refine pIntegral_pow_div two_ne_zero <|
         (factorization_eq_zero_of_lt ?_).trans_le (by lia)
      exact (Prime.odd_iff Fact.out).mp <| Prime.odd_of_ne_two Fact.out hp2
  · rcases Nat.even_or_odd (i + 2) with ⟨m, hm⟩ | hodd
    · have ⟨hm_pos, hm_lt, hi_eq⟩ : 0 < m ∧ m < k ∧ i + 2 = 2 * m := by lia
      simp only [hi_eq]
      exact pIntegral_bernoulli_even_term hm_lt (ih m hm_lt hm_pos)
    · simp [bernoulli_eq_zero_of_odd hodd (by lia)]

private lemma sum_pow_filter_eq_faulhaber {k : ℕ} (p : ℕ) (hk : 0 < k) :
    (∑ v ∈ Ico 1 p, (v : ℚ) ^ (2 * k)) =
      (∑ i ∈ range (2 * k), bernoulli i * ((2 * k + 1).choose i) *
        (p : ℚ) ^ (2 * k + 1 - i) / (2 * k + 1)) + p * bernoulli (2 * k) := by
  have hfilter : (∑ v ∈ Ico 1 p, (v : ℚ) ^ (2 * k)) = ∑ v ∈ range p, (v : ℚ) ^ (2 * k) := by
    cases p <;> simp [Finset.sum_range_eq_add_Ico, show 2 * k ≠ 0 by lia]
  rw [hfilter, sum_range_pow, Finset.sum_range_succ, Nat.choose_succ_self_right,
    show 2 * k + 1 - 2 * k = 1 by lia]
  push_cast
  field_simp

private lemma faulhaber_sum_div_prime_eq {k p : ℕ} [Fact p.Prime] :
    (∑ i ∈ range (2 * k), bernoulli i * ((2 * k + 1).choose i : ℚ) *
      (p : ℚ) ^ (2 * k + 1 - i) / (2 * k + 1 : ℚ)) / (p : ℚ) =
      ∑ i ∈ range (2 * k), bernoulli i * ((2 * k + 1).choose i : ℚ) *
        (p : ℚ) ^ (2 * k - i) / (2 * k + 1 : ℚ) := by
  have hp_ne : (p : ℚ) ≠ 0 := mod_cast (Fact.out : p.Prime).ne_zero
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl fun i hi ↦ ?_
  have := Finset.mem_range.mp hi
  rw [show 2 * k + 1 - i = (2 * k - i) + 1 by lia, pow_succ]
  field_simp [hp_ne]

/- Rearranges the Faulhaber identity and power-sum congruence to isolate
`bernoulli (2*k) + vonStaudtIndicator (2*k) p / p`. -/
private lemma bernoulli_add_indicator_eq_sub {k p : ℕ} (hk : k > 0) [Fact p.Prime] :
    ∃ T : ℤ, bernoulli (2 * k) + vonStaudtIndicator (2 * k) p / p =
      T - (∑ i ∈ range (2 * k),
        bernoulli i * ((2 * k + 1).choose i) * (p : ℚ) ^ (2 * k - i) / (2 * k + 1)) := by
  have hcast : (↑((∑ v ∈ Ico 1 p, (v : ℤ) ^ (2 * k)) +
      (if (p - 1) ∣ 2 * k then 1 else 0)) : ZMod p) = 0 :=
    mod_cast sum_pow_add_indicator_eq_zero (p := p) _
  obtain ⟨T, hT_int⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hcast
  use T
  have hT : (∑ v ∈ Ico 1 p, (v : ℚ) ^ (2 * k)) + vonStaudtIndicator (2 * k) p =
      p * T := by unfold vonStaudtIndicator; exact_mod_cast hT_int
  have hp_ne : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
  have hAlg : bernoulli (2 * k) + vonStaudtIndicator (2 * k) p / p =
      T - (∑ i ∈ range (2 * k), bernoulli i * ((2 * k + 1).choose i) *
        (p : ℚ) ^ (2 * k + 1 - i) / (2 * k + 1)) / p := by
    field_simp [hp_ne]; linarith [hT, sum_pow_filter_eq_faulhaber p hk]
  rw [hAlg]; congr 1; simpa using faulhaber_sum_div_prime_eq

/- For fixed prime `p`, the denominator of `B_{2k} + e_{2k}(p)/p` is not divisible by `p`. -/
private lemma pIntegral_bernoulli_add_indicator {p : ℕ} [Fact p.Prime] :
    ∀ {k}, k > 0 → Even k → pIntegral p (bernoulli k + vonStaudtIndicator k p / p) := by
  suffices ∀ k > 0, pIntegral p (bernoulli (2 * k) + vonStaudtIndicator (2 * k) p / p) by
    grind [even_iff_exists_two_mul]
  intro k hk
  induction k using Nat.strong_induction_on with
  | h k ih =>
    obtain ⟨T, hT⟩ := bernoulli_add_indicator_eq_sub (p := p) hk
    rw [hT]
    exact sub_mem (intCast_mem _ T) (pIntegral_faulhaber_sum ih)

lemma not_dvd_den_bernoulli_add_ite {p k : ℕ} (hp : p.Prime)
    (hk₀ : k ≠ 0) (hk : Even k) : ¬ p ∣ (bernoulli k + (if p - 1 ∣ k then 1 else 0) / p).den := by
  have : Fact p.Prime := ⟨hp⟩
  rw [← pIntegral_iff_not_dvd_den]
  exact pIntegral_bernoulli_add_indicator hk₀.bot_lt hk

/-- For even `m > 0`, a prime `p` divides the denominator of `bernoulli m` exactly when
`(p - 1) ∣ m`. See `sub_one_dvd_of_dvd_den_bernoulli` -/
theorem dvd_den_bernoulli_iff {p k : ℕ} (hp : p.Prime) (hm : Even k) (hm0 : k ≠ 0) :
    p ∣ (bernoulli k).den ↔ p - 1 ∣ k := by
  have : Fact p.Prime := ⟨hp⟩
  rw [← not_iff_not, ← pIntegral_iff_not_dvd_den]
  have : pIntegral p (bernoulli k + vonStaudtIndicator k p / p) :=
    pIntegral_bernoulli_add_indicator (by lia) hm
  refine ⟨fun h ↦ ?_, by grind [vonStaudtIndicator]⟩
  have h1p : ¬ pIntegral p (1 / p) := by simp [pIntegral_iff_not_dvd_den, hp.ne_zero]
  contrapose! h1p
  simpa [vonStaudtIndicator, h1p] using sub_mem this h

/--
If a prime `p` divides the denominator of a Bernoulli number `bernoulli k` then `p - 1 ∣ k`.
A convenient corollary of the von Staudt-Clausen theorem, see `vonStaudt_clausen`.
See also `dvd_den_bernoulli_iff` for the double implication, with stronger hypotheses.
-/
theorem sub_one_dvd_of_dvd_den_bernoulli {p k : ℕ} (hp : p.Prime) (hk : p ∣ (bernoulli k).den) :
    p - 1 ∣ k := by
  obtain rfl | rfl | he | ⟨ho, hk₁⟩ : k = 0 ∨ k = 1 ∨ (Even k ∧ k ≠ 0) ∨ (Odd k ∧ 1 < k) := by grind
  · simp
  · obtain rfl : p = 2 := by revert hk; rw [← Nat.prime_dvd_prime_iff_eq hp (by decide)]; norm_num
    grind
  · grind [dvd_den_bernoulli_iff]
  · simp [bernoulli_eq_zero_of_odd ho hk₁, hp.ne_one] at hk

/- For `(p - 1) ∤ k`, `bernoulli k` is `p`-integral (contrapositive of
`sub_one_dvd_of_dvd_den_bernoulli`). -/
private theorem pIntegral_bernoulli_of_not_dvd {p k : ℕ} [Fact p.Prime] (hk : ¬ p - 1 ∣ k) :
    pIntegral p (bernoulli k) :=
  pIntegral_iff_not_dvd_den.2 (mt (sub_one_dvd_of_dvd_den_bernoulli Fact.out) hk)

private theorem pIntegral_mul_bernoulli {p k : ℕ} [Fact p.Prime] :
    pIntegral p (p * bernoulli k) := by
  have hp : p.Prime := Fact.out
  obtain rfl | rfl | he | ⟨ho, hk₁⟩ : k = 0 ∨ k = 1 ∨ (Even k ∧ k ≠ 0) ∨ (Odd k ∧ 1 < k) := by grind
  · simp
  · obtain rfl | hodd := hp.eq_two_or_odd'
    · norm_num
    have : p * bernoulli 1 = (-p) / (2 : ℕ) := by norm_num; ring
    rw [this]
    apply pIntegral_div_natCast (by simp)
    rw [Nat.prime_dvd_prime_iff_eq hp (by decide)]
    grind
  · have hid : p * (bernoulli k + vonStaudtIndicator k p / p) - vonStaudtIndicator k p =
        p * bernoulli k := by
      field [hp.ne_zero]
    rw [← hid]
    apply sub_mem (mul_mem (natCast_mem _ p) (pIntegral_bernoulli_add_indicator (by lia) (by lia)))
    simp [vonStaudtIndicator, apply_ite]
  · simp [bernoulli_eq_zero_of_odd ho hk₁]

theorem not_dvd_mul_bernoulli {p k : ℕ} (hp : p.Prime) :
    ¬ p ∣ (p * bernoulli k).den := by
  have : Fact p.Prime := ⟨hp⟩
  rw [← pIntegral_iff_not_dvd_den]
  exact pIntegral_mul_bernoulli

theorem squarefree_den_bernoulli {k : ℕ} :
    Squarefree (bernoulli k).den := by
  rw [Nat.squarefree_iff_prime_squarefree]
  intro p hp h
  suffices p ∣ (p * bernoulli k).den by grind [not_dvd_mul_bernoulli]
  apply Nat.dvd_of_mul_dvd_mul_left hp.pos
  calc
    p * p ∣ (bernoulli k).den := h
    _ = ((1 / p) * (p * bernoulli k)).den := by congr! 1; field [hp.ne_zero]
    _ ∣ (1 / p : ℚ).den * (p * bernoulli k).den := Rat.mul_den_dvd _ _
    _ = _ := by simp [hp.ne_zero]

/- Extends the fixed-prime nondivisibility result to the full prime correction sum. -/
private lemma not_dvd_den_vonStaudt_sum {k p : ℕ} (hk : Even k) [Fact p.Prime] :
    pIntegral p (bernoulli k + ∑ q ∈ vonStaudtPrimes k, (1 : ℚ) / q) := by
  obtain rfl | hk₀ : k = 0 ∨ k > 0 := by grind [even_iff_exists_two_mul]
  · simp [vonStaudtPrimes, range_add_one, not_prime_one, not_prime_zero, Finset.filter_insert,
      Finset.filter_singleton]
  rw [sum_one_div_prime_eq_indicator_div_add (p := p) (by lia), ← add_assoc]
  apply add_mem (pIntegral_bernoulli_add_indicator hk₀ hk) (_ : pIntegral _ _)
  rw [pIntegral_iff_not_dvd_den, ← Nat.Prime.coprime_iff_not_dvd Fact.out]
  exact (prod_one_div_prime_den_coprime _).symm.of_dvd_right (Rat.den_sum_dvd_prod_den _ _)


/- `p · bernoulli i` is `p`-integral for every `i` (von Staudt: `v_p(B_i) ≥ -1`). -/
private theorem pIntegral_p_mul_bernoulli {p : ℕ} [Fact p.Prime] (i : ℕ) :
    pIntegral p (p * bernoulli i) := by
  have hp : p.Prime := Fact.out
  rcases Nat.even_or_odd i with he | ho
  · obtain ⟨l, rfl⟩ := even_iff_exists_two_mul.1 he
    rcases Nat.eq_zero_or_pos l with rfl | hl
    · simp
    · have hid : p * (bernoulli (2 * l) + vonStaudtIndicator (2 * l) p / p)
                 - vonStaudtIndicator (2 * l) p = p * bernoulli (2 * l) := by
        field [hp.ne_zero]
      rw [← hid]
      apply sub_mem (mul_mem (natCast_mem _ p) (pIntegral_bernoulli_add_indicator (by lia) he))
      simp [vonStaudtIndicator, apply_ite]
  · obtain rfl | hne := eq_or_ne i 1
    · rw [bernoulli_one]
      obtain rfl | hp2 := eq_or_ne p 2
      · norm_num
      · have h2 : ¬ p ∣ 2 := fun hd => hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp hd)
        have hph : ((p : ℚ) * (-1 / 2) : ℚ) = -((p : ℚ) / (2 : ℕ)) := by push_cast; ring
        rw [hph]
        exact neg_mem (pIntegral_div_natCast (natCast_mem _ p) h2)
    · obtain ⟨m, rfl⟩ := ho
      rw [bernoulli_eq_zero_of_odd ⟨m, rfl⟩ (by lia), mul_zero]
      exact zero_mem _

/-- `(p : ℚ) · bernoulli i` is `p`-integral: `p` does not divide the denominator of `p · Bᵢ`
(equivalently `v_p(Bᵢ) ≥ -1`). -/
theorem not_dvd_den_p_mul_bernoulli {p : ℕ} [Fact p.Prime] (i : ℕ) :
    ¬ p ∣ ((p : ℚ) * bernoulli i).den :=
  Rat.padicValuation_le_one_iff.mp (pIntegral_p_mul_bernoulli i)

/- The denominator of a `p`-integral rational is a unit mod `p`. -/
private theorem den_ne {p : ℕ} [Fact p.Prime] {x : ℚ} (hx : pIntegral p x) :
    (x.den : ZMod p) ≠ 0 := by
  rw [Ne, ZMod.natCast_eq_zero_iff]
  exact Rat.padicValuation_le_one_iff.mp hx

/- Casting respects addition of two `p`-integral rationals. -/
private theorem cast_add_pIntegral {p : ℕ} [Fact p.Prime] {a b : ℚ}
    (ha : pIntegral p a) (hb : pIntegral p b) :
    (((a + b : ℚ)) : ZMod p) = (a : ZMod p) + (b : ZMod p) :=
  Rat.cast_add_of_ne_zero (den_ne ha) (den_ne hb)

/- Casting respects multiplication of two `p`-integral rationals. -/
private theorem cast_mul_pIntegral {p : ℕ} [Fact p.Prime] {a b : ℚ}
    (ha : pIntegral p a) (hb : pIntegral p b) :
    (((a * b : ℚ)) : ZMod p) = (a : ZMod p) * (b : ZMod p) :=
  Rat.cast_mul_of_ne_zero (den_ne ha) (den_ne hb)

/- `w + 4 ≤ 5 ^ (w + 1)`. -/
private theorem five_pow_ge (w : ℕ) : w + 4 ≤ 5 ^ (w + 1) := by
  induction w with
  | zero => norm_num
  | succ n ih =>
    have hps : (5 : ℕ) ^ (n + 1 + 1) = 5 ^ (n + 1) * 5 := pow_succ 5 (n + 1)
    nlinarith [ih, hps]

/- For `q ≥ 5` and `j ≥ 3`, the `q`-adic valuation of `j` undershoots `j` by at least `3`. -/
private theorem factorization_add_three_le {q : ℕ} (hq5 : 5 ≤ q) {j : ℕ} (hj : 3 ≤ j) :
    j.factorization q + 3 ≤ j := by
  have hj0 : j ≠ 0 := by omega
  have hqv : q ^ j.factorization q ≤ j := Nat.ordProj_le q hj0
  have key : ∀ v : ℕ, q ^ v ≤ j → v + 3 ≤ j := by
    intro v hqvj
    rcases Nat.eq_zero_or_pos v with h0 | hpos
    · omega
    · obtain ⟨w, rfl⟩ : ∃ w, v = w + 1 := ⟨v - 1, by omega⟩
      have hgrow := five_pow_ge w
      have hmono : (5 : ℕ) ^ (w + 1) ≤ q ^ (w + 1) := Nat.pow_le_pow_left hq5 (w + 1)
      omega
  exact key _ hqv

/-- **Faulhaber mod `p²`.** For even `k ≥ 2` with `(p - 1) ∤ k`, the power sum `∑_{a<p} aᵏ`
equals `p·Bₖ` up to a `p²`-multiple of a `p`-integral rational: there is `W` with
`p ∤ W.den` and `∑_{a<p} aᵏ − p·Bₖ = p²·W`. -/
theorem faulhaber_mod_sq {p : ℕ} [Fact p.Prime] {k : ℕ} (hk : Even k) (hk2 : 2 ≤ k)
    (hk1 : ¬ (p - 1) ∣ k) :
    ∃ W : ℚ, ¬ p ∣ W.den ∧
      (∑ a ∈ range p, (a : ℚ) ^ k) - (p : ℚ) * bernoulli k = (p : ℚ) ^ 2 * W := by
  have hp : p.Prime := Fact.out
  have hpodd : Odd p := hp.odd_of_ne_two (fun h => hk1 (h ▸ one_dvd k))
  have hp5 : 5 ≤ p := by
    have h2 := hp.two_le
    by_contra hlt
    have hlt5 : p < 5 := by omega
    interval_cases p
    · exact (by decide : ¬ Odd 2) hpodd
    · exact hk1 hk.two_dvd
    · exact absurd hp (by decide)
  have hkm1 : ¬ (p - 1) ∣ (k - 1) := by
    obtain ⟨s, hs⟩ := hpodd
    obtain ⟨r, hr⟩ := hk
    rintro ⟨t, ht⟩
    have hp1 : p - 1 = 2 * s := by omega
    have hev : k - 1 = 2 * (s * t) := by rw [ht, hp1]; ring
    omega
  refine ⟨∑ i ∈ range k, bernoulli i * ((k + 1).choose i : ℚ) * (p : ℚ) ^ (k - 1 - i) / (k + 1),
    ?_, ?_⟩
  · rw [← Rat.padicValuation_le_one_iff]
    refine (Rat.padicValuation p).map_sum_le fun i hi => ?_
    rw [mem_range] at hi
    have hden2 : ((k + 1 - i : ℕ) : ℚ) ≠ 0 := by rw [Ne, Nat.cast_eq_zero]; omega
    have habs : bernoulli i * ((k + 1).choose i : ℚ) * (p : ℚ) ^ (k - 1 - i) / (k + 1)
        = bernoulli i * (k.choose i : ℚ) * (p : ℚ) ^ (k - 1 - i) / ((k + 1 - i : ℕ) : ℚ) := by
      have hk1' : ((k : ℚ) + 1) = ((k + 1 : ℕ) : ℚ) := by push_cast; ring
      rw [div_eq_div_iff (by positivity) hden2, hk1']
      have hnat : ((k + 1).choose i : ℚ) * ((k + 1 - i : ℕ) : ℚ)
          = (k.choose i : ℚ) * ((k + 1 : ℕ) : ℚ) := by
        exact_mod_cast (Nat.choose_mul_succ_eq k i).symm
      linear_combination (bernoulli i * (p : ℚ) ^ (k - 1 - i)) * hnat
    rw [habs]
    rcases Nat.lt_or_ge i (k - 1) with hlt | hge
    · have hpeel : (p : ℚ) ^ (k - 1 - i) = (p : ℚ) * (p : ℚ) ^ (k - 2 - i) := by
        rw [show k - 1 - i = 1 + (k - 2 - i) by omega, pow_add, pow_one]
      have hregroup : bernoulli i * (k.choose i : ℚ) * ((p : ℚ) * (p : ℚ) ^ (k - 2 - i))
            / ((k + 1 - i : ℕ) : ℚ)
          = ((p : ℚ) * bernoulli i)
            * ((k.choose i : ℚ) * ((p : ℚ) ^ (k - 2 - i) / ((k + 1 - i : ℕ) : ℚ))) := by ring
      rw [hpeel, hregroup]
      refine mul_mem (pIntegral_p_mul_bernoulli i) (mul_mem (natCast_mem _ _) ?_)
      refine pIntegral_pow_div (by omega) ?_
      have h3 : 3 ≤ k + 1 - i := by omega
      have hb := factorization_add_three_le hp5 h3
      omega
    · have hik : i = k - 1 := by omega
      subst hik
      have hz : k - 1 - (k - 1) = 0 := by omega
      have htwo : k + 1 - (k - 1) = 2 := by omega
      rw [hz, pow_zero, mul_one, htwo]
      refine pIntegral_div_natCast
        (mul_mem (pIntegral_bernoulli_of_not_dvd hkm1) (natCast_mem _ _)) ?_
      intro hd
      have := Nat.le_of_dvd (by norm_num) hd
      omega
  · rw [sum_range_pow p k, Finset.sum_range_succ]
    have hfk : bernoulli k * ((k + 1).choose k : ℚ) * (p : ℚ) ^ (k + 1 - k) / (k + 1)
        = (p : ℚ) * bernoulli k := by
      have hone : k + 1 - k = 1 := by omega
      rw [Nat.choose_succ_self_right, hone, pow_one]
      push_cast
      field_simp
    rw [hfk, Finset.mul_sum]
    have hcancel :
        (∑ i ∈ range k, bernoulli i * ((k + 1).choose i : ℚ) * (p : ℚ) ^ (k + 1 - i) / (k + 1))
          + (p : ℚ) * bernoulli k - (p : ℚ) * bernoulli k
        = ∑ i ∈ range k,
            bernoulli i * ((k + 1).choose i : ℚ) * (p : ℚ) ^ (k + 1 - i) / (k + 1) := by
      ring
    rw [hcancel]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [mem_range] at hi
    have hsplit : k + 1 - i = (k - 1 - i) + 2 := by omega
    rw [hsplit, pow_add]
    ring

lemma sq_dvd_add_pow_sub_pow_sub {R} [CommRing R] (x y : R) :
    ∀ n : ℕ, y ^ 2 ∣ (x + y) ^ n - x ^ n - n * x ^ (n - 1) * y
  | 0 => ⟨0, by simp⟩
  | 1 => ⟨0, by simp⟩
  | n + 2 => by
    obtain ⟨z, hz⟩ := sq_dvd_add_pow_sub_pow_sub x y (n + 1)
    exists x * z + (n + 1) * x ^ n + z * y
    grind

/- The first two binomial terms; `y²` divides the rest. -/
private theorem binom_sub_two_terms_dvd_sq (y r : ℤ) (k : ℕ) :
    (y ^ 2 : ℤ) ∣ (y + r) ^ k - r ^ k - (k : ℤ) * r ^ (k - 1) * y := by
  rw [add_comm y r]
  exact sq_dvd_add_pow_sub_pow_sub r y k

/- `j ↦ (c·j) mod p` permutes `[1, p-1]`, so the power sum is unchanged. -/
private theorem sum_pow_mod_perm {p : ℕ} [Fact p.Prime] {c : ℕ} (hc : ¬ p ∣ c) (k : ℕ) :
    ∑ j ∈ Ico 1 p, ((c * j) % p) ^ k = ∑ j ∈ Ico 1 p, j ^ k := by
  have hp : p.Prime := Fact.out
  have hp1 : 1 < p := hp.one_lt
  have hc0 : (c : ZMod p) ≠ 0 := by rw [Ne, ZMod.natCast_eq_zero_iff]; exact hc
  set d := ((c : ZMod p)⁻¹).val with hd
  have hd0 : ¬ p ∣ d := by
    rw [← ZMod.natCast_eq_zero_iff, hd, ZMod.natCast_zmod_val]; exact inv_ne_zero hc0
  have hcd : c * d ≡ 1 [MOD p] := by
    rw [← ZMod.natCast_eq_natCast_iff]
    push_cast
    rw [hd, ZMod.natCast_zmod_val, mul_inv_cancel₀ hc0]
  have key : ∀ a b : ℕ, a * b ≡ 1 [MOD p] → ∀ x, a * ((b * x) % p) % p = x % p := by
    intro a b hab x
    calc a * ((b * x) % p) % p
        = (a * (b * x)) % p := ((Nat.mod_modEq _ _).mul_left a)
      _ = ((a * b) * x) % p := by rw [mul_assoc]
      _ = (1 * x) % p := (hab.mul_right x)
      _ = x % p := by rw [one_mul]
  have mem_of : ∀ a : ℕ, ¬ p ∣ a → ∀ j ∈ Ico 1 p, (a * j) % p ∈ Ico 1 p := by
    intro a ha j hj
    rw [mem_Ico] at hj ⊢
    obtain ⟨hj1, hj2⟩ := hj
    have hpj : ¬ p ∣ j := fun h => by have := Nat.le_of_dvd (by lia) h; lia
    have hpaj : ¬ p ∣ (a * j) := fun h => (hp.dvd_mul.1 h).elim ha hpj
    exact ⟨Nat.one_le_iff_ne_zero.2 (fun h0 => hpaj (Nat.dvd_of_mod_eq_zero h0)),
      Nat.mod_lt _ (by lia)⟩
  refine Finset.sum_bij' (fun j _ => (c * j) % p) (fun y _ => (d * y) % p)
    (fun j hj => mem_of c hc j hj) (fun y hy => mem_of d hd0 y hy) ?_ ?_ (fun j _ => rfl)
  · intro j hj
    rw [mem_Ico] at hj
    rw [key d c (by rw [Nat.mul_comm]; exact hcd) j, Nat.mod_eq_of_lt hj.2]
  · intro y hy
    rw [mem_Ico] at hy
    rw [key c d hcd y, Nat.mod_eq_of_lt hy.2]

/- The integer heart of Voronoi's congruence: `p² ∣ (cᵏ−1)·S − k·p·c^{k-1}·V` where `S = ∑ jᵏ`
and `V = ∑ ⌊cj/p⌋·j^{k-1}` over `[1, p-1]`. -/
private theorem voronoi_int {p : ℕ} [Fact p.Prime] {c k : ℕ} (hc : ¬ p ∣ c) :
    (p ^ 2 : ℤ) ∣ ((c : ℤ) ^ k - 1) * (∑ j ∈ Ico 1 p, (j : ℤ) ^ k)
      - (k : ℤ) * p * (c : ℤ) ^ (k - 1) *
        (∑ j ∈ Ico 1 p, ((c * j / p : ℕ) : ℤ) * (j : ℤ) ^ (k - 1)) := by
  set S : ℤ := ∑ j ∈ Ico 1 p, (j : ℤ) ^ k with hS
  set A : ℤ := ∑ j ∈ Ico 1 p, ((c * j : ℕ) : ℤ) ^ k with hA
  set R : ℤ := ∑ j ∈ Ico 1 p, (((c * j) % p : ℕ) : ℤ) ^ k with hR
  set Q : ℤ := ∑ j ∈ Ico 1 p, ((c * j / p : ℕ) : ℤ) * (((c * j) % p : ℕ) : ℤ) ^ (k - 1) with hQ
  set V : ℤ := ∑ j ∈ Ico 1 p, ((c * j / p : ℕ) : ℤ) * (j : ℤ) ^ (k - 1) with hV
  have e1 : (c : ℤ) ^ k * S = A := by
    rw [hS, hA, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by push_cast; rw [mul_pow]
  have e2 : R = S := by
    rw [hR, hS]; exact_mod_cast sum_pow_mod_perm hc k
  have e3 : (p ^ 2 : ℤ) ∣ (A - R - (k : ℤ) * p * Q) := by
    rw [hA, hR, hQ, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
    refine Finset.dvd_sum fun j _ => ?_
    have hyr : ((c * j : ℕ) : ℤ) = (p : ℤ) * ((c * j / p : ℕ) : ℤ) + (((c * j) % p : ℕ) : ℤ) := by
      exact_mod_cast (Nat.div_add_mod (c * j) p).symm
    have hb := binom_sub_two_terms_dvd_sq ((p : ℤ) * ((c * j / p : ℕ) : ℤ))
      (((c * j) % p : ℕ) : ℤ) k
    have hpq : (p ^ 2 : ℤ) ∣ ((p : ℤ) * ((c * j / p : ℕ) : ℤ)) ^ 2 :=
      ⟨((c * j / p : ℕ) : ℤ) ^ 2, by ring⟩
    have hd := dvd_trans hpq hb
    rw [← hyr] at hd
    have heq : ((c * j : ℕ) : ℤ) ^ k - (((c * j) % p : ℕ) : ℤ) ^ k
        - (k : ℤ) * p * (((c * j / p : ℕ) : ℤ) * (((c * j) % p : ℕ) : ℤ) ^ (k - 1))
        = ((c * j : ℕ) : ℤ) ^ k - (((c * j) % p : ℕ) : ℤ) ^ k
          - (k : ℤ) * (((c * j) % p : ℕ) : ℤ) ^ (k - 1) * ((p : ℤ) * ((c * j / p : ℕ) : ℤ)) := by
      ring
    rw [heq]
    exact hd
  have e4 : (p : ℤ) ∣ (Q - (c : ℤ) ^ (k - 1) * V) := by
    rw [hQ, hV, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.dvd_sum fun j _ => ?_
    have hcong : (((c * j) % p : ℕ) : ℤ) ≡ (c : ℤ) * (j : ℤ) [ZMOD p] := by
      have hmul : (c : ℤ) * (j : ℤ) = ((c * j : ℕ) : ℤ) := by push_cast; ring
      rw [hmul]
      exact_mod_cast Nat.mod_modEq (c * j) p
    have hpow : (((c * j) % p : ℕ) : ℤ) ^ (k - 1) ≡ ((c : ℤ) * (j : ℤ)) ^ (k - 1) [ZMOD p] :=
      hcong.pow _
    have hpd : (p : ℤ) ∣
        (((c * j) % p : ℕ) : ℤ) ^ (k - 1) - (c : ℤ) ^ (k - 1) * (j : ℤ) ^ (k - 1) := by
      rw [mul_pow] at hpow
      exact (Int.modEq_iff_dvd.mp hpow.symm)
    have hfactor : ((c * j / p : ℕ) : ℤ) * (((c * j) % p : ℕ) : ℤ) ^ (k - 1)
          - (c : ℤ) ^ (k - 1) * (((c * j / p : ℕ) : ℤ) * (j : ℤ) ^ (k - 1))
        = ((c * j / p : ℕ) : ℤ) * ((((c * j) % p : ℕ) : ℤ) ^ (k - 1)
          - (c : ℤ) ^ (k - 1) * (j : ℤ) ^ (k - 1)) := by ring
    rw [hfactor]
    exact hpd.mul_left _
  obtain ⟨u, hu⟩ := e3
  obtain ⟨w, hw⟩ := e4
  refine ⟨u + (k : ℤ) * w, ?_⟩
  rw [sub_mul, one_mul, e1, ← e2]
  linear_combination hu + ((k : ℤ) * p) * hw

/-- The floor-weighted power sum `∑_{j=1}^{p-1} ⌊cj/p⌋ · j^{k-1}` over `ZMod p`, appearing in
Voronoi's congruence for Bernoulli numbers. -/
noncomputable def voronoiSum {p : ℕ} (c k : ℕ) : ZMod p :=
  ∑ j ∈ Ico 1 p, (c * j / p : ℕ) * j ^ (k - 1)

/-- **Voronoi's congruence.** For `c` coprime to a prime `p`, even `k ≥ 2` with `(p - 1) ∤ k`,
`(cᵏ − 1) · Bₖ ≡ k · c^{k-1} · voronoiSum c k (mod p)`.  The hypothesis `(p - 1) ∤ k` makes
`bernoulli k` `p`-integral, so its cast to `ZMod p` is the genuine value. -/
theorem voronoi_congr {p : ℕ} [Fact p.Prime] {c k : ℕ} (hc : ¬ p ∣ c) (hk1 : ¬ (p - 1) ∣ k)
    (hk : Even k) (hk2 : 2 ≤ k) :
    ((c : ZMod p) ^ k - 1) * (bernoulli k : ZMod p)
      = (k : ZMod p) * (c : ZMod p) ^ (k - 1) * voronoiSum (p := p) c k := by
  have hp : p.Prime := Fact.out
  have hp0 : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  obtain ⟨C, hC⟩ := voronoi_int (p := p) hc
  obtain ⟨W, hWden, hWeq⟩ := faulhaber_mod_sq (p := p) hk hk2 hk1
  have hWpint : pIntegral p W := Rat.padicValuation_le_one_iff.mpr hWden
  set Sz : ℤ := ∑ j ∈ Ico 1 p, (j : ℤ) ^ k with hSz
  set Vz : ℤ := ∑ j ∈ Ico 1 p, ((c * j / p : ℕ) : ℤ) * (j : ℤ) ^ (k - 1) with hVz
  have hpck : pIntegral p ((c : ℚ) ^ k) := by
    have hck : (c : ℚ) ^ k = ((c ^ k : ℕ) : ℚ) := by push_cast; ring
    rw [hck]
    exact natCast_mem _ _
  have hpc : pIntegral p ((c : ℚ) ^ k - 1) := sub_mem hpck (one_mem _)
  have hpB : pIntegral p (bernoulli k) := pIntegral_bernoulli_of_not_dvd hk1
  have cast_sub_pIntegral : ∀ {a b : ℚ}, pIntegral p a → pIntegral p b →
      (((a - b : ℚ)) : ZMod p) = (a : ZMod p) - (b : ZMod p) := by
    intro a b ha hb
    rw [sub_eq_add_neg, cast_add_pIntegral ha (neg_mem hb), Rat.cast_neg, ← sub_eq_add_neg]
  have hSQ : (∑ a ∈ range p, (a : ℚ) ^ k) = (Sz : ℚ) := by
    rw [hSz]
    push_cast
    refine (Finset.sum_subset ?_ ?_).symm
    · intro x hx; rw [mem_Ico] at hx; rw [mem_range]; lia
    · intro x hx hx2
      rw [mem_range] at hx
      rw [mem_Ico] at hx2
      have hx0 : x = 0 := by lia
      have hk0 : k ≠ 0 := by lia
      rw [hx0]
      simp [zero_pow hk0]
  have hCq : ((c : ℚ) ^ k - 1) * (Sz : ℚ) - (k : ℚ) * p * (c : ℚ) ^ (k - 1) * (Vz : ℚ)
      = (p : ℚ) ^ 2 * (C : ℚ) := by
    exact_mod_cast hC
  have hWq : (Sz : ℚ) - (p : ℚ) * bernoulli k = (p : ℚ) ^ 2 * W := by rw [← hSQ]; exact hWeq
  set M : ℚ := (C : ℚ) - ((c : ℚ) ^ k - 1) * W with hM
  have hMpint : pIntegral p M :=
    sub_mem (intCast_mem _ C) (mul_mem hpc hWpint)
  have hstar : ((c : ℚ) ^ k - 1) * bernoulli k
      = (k : ℚ) * (c : ℚ) ^ (k - 1) * (Vz : ℚ) + (p : ℚ) * M := by
    refine mul_left_cancel₀ hp0 ?_
    rw [hM]
    linear_combination hCq - ((c : ℚ) ^ k - 1) * hWq
  have hVzcast : ((Vz : ℤ) : ZMod p) = voronoiSum (p := p) c k := by
    rw [hVz, voronoiSum, Int.cast_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Int.cast_mul, Int.cast_pow, Int.cast_natCast, Int.cast_natCast]
  have castL : ((((c : ℚ) ^ k - 1) * bernoulli k : ℚ) : ZMod p)
      = ((c : ZMod p) ^ k - 1) * (bernoulli k : ZMod p) := by
    have hck : (c : ℚ) ^ k = ((c ^ k : ℕ) : ℚ) := by push_cast; ring
    rw [cast_mul_pIntegral hpc hpB, cast_sub_pIntegral hpck (one_mem _), Rat.cast_one,
      hck, Rat.cast_natCast]
    push_cast
    ring
  have hck1 : (c : ℚ) ^ (k - 1) = ((c ^ (k - 1) : ℕ) : ℚ) := by push_cast; ring
  have hpck1 : pIntegral p ((c : ℚ) ^ (k - 1)) := by
    rw [hck1]
    exact natCast_mem _ _
  have castR : (((k : ℚ) * (c : ℚ) ^ (k - 1) * (Vz : ℚ) + (p : ℚ) * M : ℚ) : ZMod p)
      = (k : ZMod p) * (c : ZMod p) ^ (k - 1) * voronoiSum (p := p) c k := by
    rw [cast_add_pIntegral
        (mul_mem (mul_mem (natCast_mem _ k) hpck1) (intCast_mem _ Vz))
        (mul_mem (natCast_mem _ p) hMpint),
      cast_mul_pIntegral (mul_mem (natCast_mem _ k) hpck1) (intCast_mem _ Vz),
      cast_mul_pIntegral (natCast_mem _ k) hpck1,
      cast_mul_pIntegral (natCast_mem _ p) hMpint,
      Rat.cast_natCast, Rat.cast_natCast, ZMod.natCast_self, zero_mul, add_zero,
      hck1, Rat.cast_natCast, Rat.cast_intCast, hVzcast]
    push_cast
    ring
  rw [← castL, ← castR, hstar]

/- A primitive root mod `p`: `c : ℕ` coprime to `p` whose powers hit `1` exactly on multiples
of `p - 1`. -/
private theorem exists_primitiveRoot {p : ℕ} [Fact p.Prime] :
    ∃ c : ℕ, ¬ p ∣ c ∧ ∀ k : ℕ, (c : ZMod p) ^ k = 1 ↔ (p - 1) ∣ k := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := (ZMod p)ˣ)
  have hord : orderOf g = p - 1 := by
    rw [hg, Nat.card_eq_fintype_card, ZMod.card_units_eq_totient, Nat.totient_prime Fact.out]
  refine ⟨(g : ZMod p).val, ?_, ?_⟩
  · rw [← ZMod.natCast_eq_zero_iff, ZMod.natCast_zmod_val]
    exact Units.ne_zero g
  · intro k
    have hcast : ((g : ZMod p).val : ZMod p) = (g : ZMod p) := ZMod.natCast_zmod_val _
    rw [hcast, ← Units.val_pow_eq_pow_val, ← Units.val_one (α := ZMod p),
      Units.val_inj, ← orderOf_dvd_iff_pow_eq_one, hord]

/-- **Kummer's congruence** (weak form, mod `p`).  For even indices `m ≡ n (mod p - 1)` with
`(p - 1) ∤ m`, the denominator-cleared residues satisfy `n · Bₘ ≡ m · Bₙ (mod p)`.  This is
`Bₘ / m ≡ Bₙ / n` with denominators cleared, and it holds even when `p ∣ m` (both sides vanish). -/
theorem kummer_congr {p : ℕ} [Fact p.Prime] {m n : ℕ} (hmn : m ≡ n [MOD p - 1])
    (hm : ¬ (p - 1) ∣ m) (hm1 : m ≠ 1) (hn1 : n ≠ 1) :
    (n : ZMod p) * (bernoulli m : ZMod p) = (m : ZMod p) * (bernoulli n : ZMod p) := by
  have hp : p.Prime := Fact.out
  have hpodd : Odd p := hp.odd_of_ne_two (fun h => hm (h ▸ one_dvd m))
  have h2dvd : 2 ∣ (p - 1) := by obtain ⟨s, hs⟩ := hpodd; omega
  have hpar : m % 2 = n % 2 := Nat.ModEq.of_dvd h2dvd hmn
  have hm2 : 2 ≤ m := by
    have hm0 : m ≠ 0 := by rintro rfl; exact hm (dvd_zero _)
    omega
  have hn2 : 2 ≤ n := by
    have hn0 : n ≠ 0 := by rintro rfl; exact hm (Nat.modEq_zero_iff_dvd.mp hmn)
    omega
  rcases Nat.even_or_odd m with hmeven | hmodd
  · have hneven : Even n := by rw [Nat.even_iff] at hmeven ⊢; omega
    obtain ⟨c, hc, hcord⟩ := exists_primitiveRoot (p := p)
    have hc0 : (c : ZMod p) ≠ 0 := by rw [Ne, ZMod.natCast_eq_zero_iff]; exact hc
    have hn : ¬ (p - 1) ∣ n := fun hdvd =>
      hm (Nat.modEq_zero_iff_dvd.mp (hmn.trans (Nat.modEq_zero_iff_dvd.mpr hdvd)))
    have hper : ∀ (x : ZMod p) (a b : ℕ), x ≠ 0 → a ≡ b [MOD p - 1] → x ^ a = x ^ b := by
      intro x a b hx hab
      have hx1 : x ^ (p - 1) = 1 := ZMod.pow_card_sub_one_eq_one hx
      rcases Nat.le_total b a with hle | hle
      · obtain ⟨t, ht⟩ := (Nat.modEq_iff_dvd' hle).mp hab.symm
        have hsplit : a = b + (p - 1) * t := by lia
        rw [hsplit, pow_add, pow_mul, hx1, one_pow, mul_one]
      · obtain ⟨t, ht⟩ := (Nat.modEq_iff_dvd' hle).mp hab
        have hsplit : b = a + (p - 1) * t := by lia
        rw [hsplit, pow_add, pow_mul, hx1, one_pow, mul_one]
    have hmn1 : m - 1 ≡ n - 1 [MOD p - 1] := by
      have h := hmn
      have hm1' : 1 ≤ m := by lia
      have hn1' : 1 ≤ n := by lia
      rw [← Nat.sub_add_cancel hm1', ← Nat.sub_add_cancel hn1'] at h
      exact Nat.ModEq.add_right_cancel' 1 h
    have hcm : (c : ZMod p) ^ m = (c : ZMod p) ^ n := hper _ _ _ hc0 hmn
    have hcm1 : (c : ZMod p) ^ (m - 1) = (c : ZMod p) ^ (n - 1) := hper _ _ _ hc0 hmn1
    have hvsum : voronoiSum (p := p) c m = voronoiSum (p := p) c n := by
      refine Finset.sum_congr rfl fun j hj => ?_
      have hj0 : (j : ZMod p) ≠ 0 := by
        rw [mem_Ico] at hj
        rw [Ne, ZMod.natCast_eq_zero_iff]
        exact fun hd => absurd (Nat.le_of_dvd (by lia) hd) (by lia)
      rw [hper _ _ _ hj0 hmn1]
    have hVm := voronoi_congr hc hm hmeven hm2
    have hVn := voronoi_congr hc hn hneven hn2
    rw [hcm, hcm1, hvsum] at hVm
    have hw : (c : ZMod p) ^ n - 1 ≠ 0 := by
      rw [sub_ne_zero]; exact fun h => hn ((hcord n).mp h)
    refine mul_left_cancel₀ hw ?_
    calc ((c : ZMod p) ^ n - 1) * ((n : ZMod p) * (bernoulli m : ZMod p))
          = (n : ZMod p) * (((c : ZMod p) ^ n - 1) * (bernoulli m : ZMod p)) := by ring
      _ = (n : ZMod p) * ((m : ZMod p) * (c : ZMod p) ^ (n - 1) * voronoiSum (p := p) c n) := by
            rw [hVm]
      _ = (m : ZMod p) * ((n : ZMod p) * (c : ZMod p) ^ (n - 1) * voronoiSum (p := p) c n) := by
            ring
      _ = (m : ZMod p) * (((c : ZMod p) ^ n - 1) * (bernoulli n : ZMod p)) := by rw [hVn]
      _ = ((c : ZMod p) ^ n - 1) * ((m : ZMod p) * (bernoulli n : ZMod p)) := by ring
  · have hnodd : Odd n := by rw [Nat.odd_iff] at hmodd ⊢; omega
    rw [bernoulli_eq_zero_of_odd hmodd (by lia), bernoulli_eq_zero_of_odd hnodd (by lia)]
    simp

end Bernoulli

end

end ImportedKummer

theorem padicVal_bernoulli_add_one (p) [Fact p.Prime] :
    padicValRat p (2 * (p + 1) / bernoulli (p + 1)) ≥ 0 := by
  have hp : p.Prime := Fact.out
  by_cases hp5 : 5 ≤ p
  · have hmod : p + 1 ≡ 2 [MOD p - 1] := by
      apply Nat.ModEq.symm
      exact Nat.modEq_iff_dvd.mpr ⟨1, by omega⟩
    have hndvd : ¬ p - 1 ∣ p + 1 := by
      intro h
      have htwo : p - 1 ∣ 2 := by
        have := Nat.dvd_sub h (dvd_refl (p - 1))
        simpa [show p + 1 - (p - 1) = 2 by omega] using this
      have := Nat.le_of_dvd (by decide : 0 < 2) htwo
      omega
    have hcongr := Bernoulli.kummer_congr hmod hndvd (by omega) (by decide)
    have hpcast : (p : ZMod p) = 0 := by simp
    have h6 : (6 : ZMod p) ≠ 0 := by
      intro h
      have hdiv : p ∣ 6 := (ZMod.natCast_eq_zero_iff 6 p).mp h
      rcases hp.dvd_mul.mp (show p ∣ 2 * 3 from hdiv) with h2 | h3
      · have := Nat.le_of_dvd (by decide : 0 < 2) h2; omega
      · have := Nat.le_of_dvd (by decide : 0 < 3) h3; omega
    have hB : (bernoulli (p + 1) : ZMod p) ≠ 0 := by
      intro hzero
      have hB2 : (bernoulli 2 : ZMod p) = (6 : ZMod p)⁻¹ := by
        rw [bernoulli_two, Rat.cast_inv_of_ne_zero (by simpa using h6)]
        norm_cast
      simp only [hzero, mul_zero, hB2, Nat.cast_add, Nat.cast_one, hpcast,
        zero_add, one_mul] at hcongr
      exact (inv_ne_zero h6) hcongr.symm
    have hnum : ¬ (p : ℤ) ∣ (bernoulli (p + 1)).num := by
      intro h
      apply hB
      rw [Rat.cast_def, (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr h, zero_div]
    have hval : padicValRat p (bernoulli (p + 1)) ≤ 0 := by
      rw [padicValRat_def, padicValInt.eq_zero_of_not_dvd hnum]
      simp
    by_cases hzero : bernoulli (p + 1) = 0
    · simp [hzero]
    · rw [padicValRat.div (by positivity) hzero]
      have hnat := zero_le_padicValRat_of_nat (p := p) (2 * (p + 1))
      push_cast at hnat
      omega
  · have hsmall : p = 2 ∨ p = 3 := by
      have := hp.two_le
      have := hp.eq_two_or_odd
      omega
    rcases hsmall with rfl | rfl
    · norm_num [bernoulli]
    · norm_num [bernoulli]
      exact zero_le_padicValRat_of_nat 240


open scoped Nat

namespace ThetaOperator.KummerCongruence

noncomputable section

/- A rational number is `p`-integral when its denominator is prime to `p`. -/
def PIntegral (p : ℕ) (x : ℚ) [Fact p.Prime] : Prop :=
  Rat.padicValuation p x ≤ 1

/- The residue of a rational number in `ZMod p`. -/
def residue (p : ℕ) (x : ℚ) : ZMod p :=
  (x.num : ZMod p) * (x.den : ZMod p)⁻¹

theorem pIntegral_iff {p : ℕ} [Fact p.Prime] (x : ℚ) :
    PIntegral p x ↔ ¬p ∣ x.den := by
  exact Rat.padicValuation_le_one_iff

theorem residue_eq_inv (p : ℕ) (x : ℚ) :
    residue p x = (x.num : ZMod p) * (x.den : ZMod p)⁻¹ := by
  rfl

/- The normalized Bernoulli value occurring in Kummer's congruence. -/
def normalizedBernoulli (n : ℕ) : ℚ := bernoulli n / n

/- The power sum used in the Faulhaber argument. -/
def powerSum (N n : ℕ) : ℚ :=
  ∑ a ∈ Finset.range N, (a : ℚ) ^ n

/- The von Staudt correction attached to an even Bernoulli index. -/
def vonStaudtCorrection (n : ℕ) : ℚ :=
  ∑ q ∈ Finset.range (n + 2) with q.Prime ∧ (q - 1) ∣ n, (1 : ℚ) / q

/-!
## Step 1: the identities used by the proof

The first two statements are wrappers around the existing Faulhaber and
von Staudt--Clausen theorems.  Keeping them in this file makes the later
`p`-local argument independent of the exact shape of the upstream API.
-/

theorem powerSum_eq_faulhaber (N n : ℕ) :
    powerSum N n =
      ∑ i ∈ Finset.range (n + 1),
        bernoulli i * ((n + 1).choose i) * (N : ℚ) ^ (n + 1 - i) / (n + 1) := by
  simpa [powerSum] using (sum_range_pow N n)

theorem bernoulli_add_vonStaudtCorrection_is_integer (n : ℕ) :
    bernoulli (2 * n) + vonStaudtCorrection (2 * n) ∈ Set.range Int.cast := by
  simpa [vonStaudtCorrection] using (Bernoulli.vonStaudt_clausen n)



end

end ThetaOperator.KummerCongruence
