import Mathlib.NumberTheory.Bernoulli

open Nat Finset Finset.Nat PowerSeries

private theorem rat_den_sum_dvd_prod_den {α : Type*} (s : Finset α) (f : α → ℚ) :
    (∑ a ∈ s, f a).den ∣ ∏ a ∈ s, (f a).den := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      rw [sum_insert ha, prod_insert ha]
      exact (Rat.add_den_dvd _ _).trans (Nat.mul_dvd_mul (dvd_refl _) ih)

section vonStaudtClausen

/-!
### The von Staudt-Clausen Theorem

Here we formalize Rado's proof of von Staudt-Clausen's theorem, which states that for any $k \ge 0$,
$$B_{2k} + \sum_{p \text{ prime}, (p - 1) \mid 2k} \frac{1}{p} \in \mathbb{Z}.$$
Rado's proof is based on Faulhaber's theorem and induction on $k$.
-/

namespace Bernoulli

/- Indicator function that is `1` if `(p - 1) ∣ k` and `0` otherwise. -/
private noncomputable def vonStaudtIndicator (k p : ℕ) : ℚ :=
  if (p - 1) ∣ k then 1 else 0

/- The primes `q < 2k + 2` with `(q - 1) ∣ 2k` — the primes appearing in the
von Staudt-Clausen correction sum. -/
private abbrev vonStaudtPrimes (k : ℕ) : Finset ℕ :=
  (range (2 * k + 2)).filter fun q ↦ q.Prime ∧ (q - 1) ∣ 2 * k

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

/- A rational number `x` is `p`-integral if `p` does not divide its denominator. -/
private abbrev pIntegral (p : ℕ) (x : ℚ) [Fact p.Prime] : Prop := Rat.padicValuation p x ≤ 1

private lemma pIntegral_mul {p : ℕ} [Fact p.Prime] {x y : ℚ}
    (hx : pIntegral p x) (hy : pIntegral p y) : pIntegral p (x * y) :=
  ((Rat.padicValuation p).map_mul x y).trans_le (mul_le_one' hx hy)

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
    vonStaudtIndicator (2 * k) p / p + ∑ q ∈ vonStaudtPrimes k with q ≠ p, (1 : ℚ) / q := by
  rw [Finset.sum_congr (Finset.filter_ne' (vonStaudtPrimes k) p) fun _ _ ↦ rfl]
  by_cases hdvd : (p - 1) ∣ 2 * k
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
  exact Rat.padicValuation_le_one_iff.2 ((Nat.Prime.coprime_iff_not_dvd Fact.out).1
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
  exact pIntegral_mul (mod_cast Int.padicValuation_le_one p ((2 * k).choose (2 * m)))
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
  apply (Rat.padicValuation p).map_sub_le
  · rw [mul_assoc, mul_div_assoc]
    apply pIntegral_mul ih
    have hpow_mul : ((2 * k).choose (2 * m) : ℚ) * (p : ℚ) ^ (2 * k - 2 * m) /
        (2 * k - 2 * m + 1) =
        (p : ℚ) * (((2 * k).choose (2 * m) : ℚ) * P / (2 * k - 2 * m + 1)) := by
      rw [hpow]; ring
    rw [H, hpow_mul]
    exact pIntegral_mul (Int.padicValuation_le_one p p) hcmp
  · unfold vonStaudtIndicator
    split_ifs
    · grind
    · simp

/- The full remainder sum in Faulhaber's formula is `p`-integral. -/
private lemma pIntegral_faulhaber_sum {k p : ℕ} (hk : k > 0) [Fact p.Prime]
    (ih : ∀ m, 0 < m → m < k → pIntegral p (bernoulli (2 * m) + vonStaudtIndicator (2 * m) p / p)) :
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
      exact pIntegral_bernoulli_even_term hm_lt (ih m hm_pos hm_lt)
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
private lemma not_dvd_den_bernoulli_add_indicator {k p : ℕ} (hk : k > 0) [Fact p.Prime] :
    ¬ p ∣ (bernoulli (2 * k) + vonStaudtIndicator (2 * k) p / p).den := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    obtain ⟨T, hT⟩ := bernoulli_add_indicator_eq_sub (p := p) hk
    rw [hT]
    have hT_int : pIntegral p T := Int.padicValuation_le_one p T
    have hR := pIntegral_faulhaber_sum hk fun m hm_pos hm_lt ↦
      Rat.padicValuation_le_one_iff.mpr (ih m hm_lt hm_pos)
    exact Rat.padicValuation_le_one_iff.mp ((Rat.padicValuation p).map_sub_le hT_int hR)

/- Extends the fixed-prime nondivisibility result to the full prime correction sum. -/


end Bernoulli

end vonStaudtClausen

theorem ldvd_bernoulli_num (ℓ) (hprime : Nat.Prime ℓ) (hg5 : ℓ ≥ 5) :
    (2 * ↑(ℓ - 1) / bernoulli (ℓ - 1)).num ≡ 0 [ZMOD ℓ] := by
  let : Fact (Nat.Prime ℓ) := ⟨hprime⟩
  have hℓodd : Odd ℓ := (Nat.Prime.odd_iff hprime).mpr (by omega)
  obtain ⟨t, ht⟩ := hℓodd
  let k := (ℓ - 1) / 2
  have hk : 0 < k := by
    dsimp [k]
    omega
  have htwo : 2 * k = ℓ - 1 := by
    dsimp [k]
    omega
  have hAden : ¬ ℓ ∣ (bernoulli (2 * k) + (1 : ℚ) / ℓ).den := by
    have h := Bernoulli.not_dvd_den_bernoulli_add_indicator (p := ℓ) hk
    simpa [Bernoulli.vonStaudtIndicator, htwo] using h
  have hinv : 1 < Rat.padicValuation ℓ ((1 : ℚ) / ℓ) := by
    simp [Rat.padicValuation, padicValRat, hprime.ne_zero]
  have hAden' : ¬ ℓ ∣ (bernoulli (ℓ - 1) + (1 : ℚ) / ℓ).den := by
    simpa [htwo] using hAden
  have hBden : ℓ ∣ (bernoulli (ℓ - 1)).den := by
    by_contra h
    have hBval : Rat.padicValuation ℓ (bernoulli (ℓ - 1)) ≤ 1 :=
      Rat.padicValuation_le_one_iff.mpr h
    have hsum := (Rat.padicValuation ℓ).map_add_eq_of_lt_right
      (lt_of_le_of_lt hBval hinv)
    have hAval : Rat.padicValuation ℓ (bernoulli (ℓ - 1) + (1 : ℚ) / ℓ) ≤ 1 :=
      Rat.padicValuation_le_one_iff.mpr hAden'
    rw [hsum] at hAval
    exact (not_le_of_gt hinv) hAval
  have hBnum : ¬ (ℓ : ℤ) ∣ (bernoulli (ℓ - 1)).num := by
    intro h
    have hnat : ℓ ∣ (bernoulli (ℓ - 1)).num.natAbs :=
      Int.natCast_dvd_natCast.1 (Int.dvd_natAbs.2 h)
    have hone : ℓ = 1 := Nat.eq_one_of_dvd_coprimes
      (bernoulli (ℓ - 1)).reduced.symm hBden hnat
    exact hprime.ne_one hone
  rw [Int.modEq_zero_iff_dvd]
  let C : ℚ := ((2 * (ℓ : ℤ) - 2 : ℤ) : ℚ)
  have hCnum : C.num = 2 * (ℓ : ℤ) - 2 := by
    change (((2 * (ℓ : ℤ) - 2 : ℤ) : ℚ).num) = _
    simp only [Rat.num_intCast]
  have hCden : C.den = 1 := by
    change (((2 * (ℓ : ℤ) - 2 : ℤ) : ℚ).den) = _
    simp only [Rat.den_intCast]
  have hCeq : C = 2 * (ℓ - 1) := by
    dsimp [C]
    push_cast
    ring
  have hform : C / bernoulli (ℓ - 1) =
      Rat.divInt (C.num * (bernoulli (ℓ - 1)).den)
        (C.den * (bernoulli (ℓ - 1)).num) :=
    Rat.div_def' C (bernoulli (ℓ - 1))
  have hBnum0 : (bernoulli (ℓ - 1)).num ≠ 0 := by
    intro hzero
    apply hBnum
    simp [hzero]
  obtain ⟨c, hcn, hcd⟩ := Rat.num_den_mk
    (by simp [hBnum0] : (C.den * (bernoulli (ℓ - 1)).num : ℤ) ≠ 0) hform
  have hrawnum : (ℓ : ℤ) ∣ C.num * (bernoulli (ℓ - 1)).den := by
    rw [hCnum]
    exact dvd_mul_of_dvd_right (Int.natCast_dvd_natCast.2 hBden) _
  have hrawden : ¬ (ℓ : ℤ) ∣ C.den * (bernoulli (ℓ - 1)).num := by
    simpa [hCden] using hBnum
  have hpint : Prime (ℓ : ℤ) := Nat.prime_iff_prime_int.1 hprime
  have hcn_not : ¬ (ℓ : ℤ) ∣ c := by
    intro hc
    apply hrawden
    rw [hcd]
    exact dvd_mul_of_dvd_left hc _
  have hqraw : (ℓ : ℤ) ∣ c * (C / bernoulli (ℓ - 1)).num := by
    rw [← hcn]
    exact hrawnum
  rcases hpint.dvd_mul.mp hqraw with h | h
  · exact False.elim (hcn_not h)
  · have htarget : (2 * (↑(ℓ - 1) : ℚ)) = C := by
      calc
        2 * (↑(ℓ - 1) : ℚ) = 2 * ((ℓ : ℚ) - 1) := by
          rw [Nat.cast_sub (by omega)]
          norm_num
        _ = C := hCeq.symm
    rwa [htarget]


theorem padicVal_bernoulli_sub_one (p) [Fact p.Prime] :
    padicValRat p (2 * (p - 1) / bernoulli (p - 1)) ≥ 0 := by
  by_cases hp : p ≥ 5
  · rw [show (p : ℚ) - 1 = (↑(p - 1) : ℚ) by
      rw [Nat.cast_sub (by omega)]; simp]
    have hdiv := ldvd_bernoulli_num p Fact.out hp
    have hnum : (p : ℤ) ∣ (2 * (↑(p - 1) : ℚ) / bernoulli (p - 1)).num :=
      Int.modEq_zero_iff_dvd.mp hdiv
    have hnum' : p ∣ (2 * (↑(p - 1) : ℚ) / bernoulli (p - 1)).num.natAbs :=
      Int.natCast_dvd_natCast.mp (Int.dvd_natAbs.2 hnum)
    have hden : ¬ p ∣ (2 * (↑(p - 1) : ℚ) / bernoulli (p - 1)).den := by
      intro hd
      have hone := Nat.eq_one_of_dvd_coprimes
        (2 * (↑(p - 1) : ℚ) / bernoulli (p - 1)).reduced.symm hd hnum'
      exact (Fact.out : Nat.Prime p).ne_one hone
    rw [padicValRat_def, padicValInt, padicValNat.eq_zero_of_not_dvd hden]
    simp
  · have hp2 : p = 2 ∨ p = 3 := by
      have := (Fact.out : Nat.Prime p).two_le
      have := (Fact.out : Nat.Prime p).eq_two_or_odd
      omega
    rcases hp2 with rfl | rfl <;> norm_num [bernoulli] <;>
      exact zero_le_padicValRat_of_nat _
