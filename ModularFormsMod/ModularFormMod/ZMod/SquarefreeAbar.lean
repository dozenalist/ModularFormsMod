import ModularFormsMod.ModularFormMod.ZMod.Polynomial
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Polynomial.SpecificDegree
import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
import Mathlib.Algebra.Squarefree.Basic
import Mathlib.RingTheory.MvPolynomial.EulerIdentity
import Mathlib.RingTheory.Polynomial.UniqueFactorization
import Mathlib.RingTheory.UniqueFactorizationDomain.Multiplicity

/-!
# Squarefreeness of the Hasse polynomial

The first part of Lemma 1.40: `Abar p` has no repeated irreducible factors.
The proof uses the two differential identities of Lemma 1.39 and the bound on
the degree of `Abar`. Euler's identity replaces the classification of weighted
homogeneous factors in the paper's proof.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

noncomputable section

open PInteger MvPolynomial

namespace ModularFormMod.ZMod

variable (p : ℕ) [isLargePrime p]

private theorem Del_map {R S : Type} [CommRing R] [CommRing S]
    (r : R →+* S) (f : MvPolynomial (Fin 2) R) :
    Del (MvPolynomial.map r f) = MvPolynomial.map r (Del f) := by
  simp only [Del_apply, pderiv_map, Algebra.smul_def, MvPolynomial.algebraMap_eq,
    _root_.map_add, _root_.map_mul, _root_.map_neg, _root_.map_ofNat,
    MvPolynomial.map_X, _root_.map_pow]

@[simp] theorem Del_Abar : Del (Abar p) = Bbar p := by
  rw [ModularFormMod.ZMod.Abar, Del_map, reduce_Del_A]

@[simp] theorem Del_Bbar : Del (Bbar p) = -X 0 * Abar p := by
  rw [ModularFormMod.ZMod.Bbar, Del_map, reduce_Del_B]

theorem Abar_isWeightedHomogeneous :
    (Abar p).IsWeightedHomogeneous ModularFormOver.eisensteinWeights (p - 1 : ℤ) := by
  intro d hd
  apply A_isWeightedHomogeneous p
  intro h
  exact hd (by rw [ModularFormMod.ZMod.Abar, MvPolynomial.coeff_map, h, _root_.map_zero])

private theorem Abar_weight {d : Fin 2 →₀ ℕ} (hd : (Abar p).coeff d ≠ 0) :
    4 * d 0 + 6 * d 1 = p - 1 := by
  have h := Abar_isWeightedHomogeneous p hd
  simp [Finsupp.weight_apply, Finsupp.sum_fintype, ModularFormOver.eisensteinWeights,
    Fin.sum_univ_two] at h
  have hp : 5 ≤ p := isLargePrime.AtLeastFive
  omega

theorem Abar_totalDegree_lt : (Abar p).totalDegree < p := by
  have hp : 5 ≤ p := isLargePrime.AtLeastFive
  apply lt_of_le_of_lt (b := p - 1) ?_ (by omega)
  rw [MvPolynomial.totalDegree, Finset.sup_le_iff]
  intro d hd
  have h := Abar_weight p (MvPolynomial.mem_support_iff.mp hd)
  rw [Finsupp.sum_fintype _ _ (by simp), Fin.sum_univ_two]
  omega

theorem eisensteinFourierEval_Abar :
    ModularFormMod.eisensteinFourierEval (PInteger.reduce (p := p)) (Abar p) = 1 := by
  rw [ModularFormMod.ZMod.Abar, ModularFormMod.eisensteinFourierEval_map,
    ModularFormMod.ZMod.A,
    ModularFormOver.eisensteinFourierEval_toPolynomial]
  exact ModularFormMod.Reduce_Esubone p

theorem Abar_ne_zero : Abar p ≠ 0 := by
  intro h
  have := eisensteinFourierEval_Abar p
  rw [h, _root_.map_zero] at this
  exact zero_ne_one this

/-- The value at the cusp, where the Eisenstein generators both have constant term one. -/
theorem Abar_eval_one : MvPolynomial.eval (fun _ => 1) (Abar p) = 1 := by
  have h : (PowerSeries.constantCoeff (R := ZMod p)).comp
      (ModularFormMod.eisensteinFourierEval (PInteger.reduce (p := p))).toRingHom =
      MvPolynomial.eval (fun _ => 1) := by
    ext i
    · simp
    · fin_cases i <;>
        simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
          ModularFormMod.eisensteinFourierEval, MvPolynomial.aeval_X,
          ModularFormOver.Reduce_fourier, ← PowerSeries.coeff_zero_eq_constantCoeff,
          MvPolynomial.eval_X]
      · change PInteger.reduce (ModularFormOver.coeff ℤ 0 ModularFormOver.E₄ ℤ(p)) = 1
        simp
      · change PInteger.reduce (ModularFormOver.coeff ℤ 0 ModularFormOver.E₆ ℤ(p)) = 1
        simp
  rw [← h, RingHom.comp_apply]
  change PowerSeries.constantCoeff
    (ModularFormMod.eisensteinFourierEval (PInteger.reduce (p := p)) (Abar p)) = 1
  rw [eisensteinFourierEval_Abar]
  simp

private theorem derivation_pow_succ_mul {K S : Type*} [CommRing K] [CommRing S]
    [Algebra K S] (D : Derivation K S S) (q a : S) (n : ℕ) :
    D (q ^ (n + 1) * a) = q ^ n * (q * D a + (n + 1) * (a * D q)) := by
  rw [D.leibniz, D.leibniz_pow]
  simp only [smul_eq_mul, nsmul_eq_mul, Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one,
    pow_succ]
  ring

private theorem discriminant_irreducible {K : Type*} [Field K] :
    Irreducible ((X 0 : MvPolynomial (Fin 2) K) ^ 3 - X 1 ^ 2) := by
  apply (MulEquiv.irreducible_iff (MvPolynomial.finSuccEquiv K 1)).mp
  simp only [_root_.map_sub, _root_.map_pow, finSuccEquiv_X_zero,
    show (1 : Fin 2) = (0 : Fin 1).succ from rfl, finSuccEquiv_X_succ]
  rw [← _root_.map_pow Polynomial.C]
  have hm := Polynomial.monic_X_pow_sub_C
    ((X (0 : Fin 1) : MvPolynomial (Fin 1) K) ^ 2) (by decide : 3 ≠ 0)
  apply (hm.irreducible_iff_roots_eq_zero_of_degree_le_three
    (by rw [Polynomial.natDegree_X_pow_sub_C]; decide)
    (by rw [Polynomial.natDegree_X_pow_sub_C])).mpr
  apply Multiset.eq_zero_of_forall_notMem
  intro a ha
  have h := (Polynomial.mem_roots (Polynomial.X_pow_sub_C_ne_zero (by decide) _)).mp ha
  have heq : a ^ 3 = (X (0 : Fin 1) : MvPolynomial (Fin 1) K) ^ 2 := by
    simpa [Polynomial.IsRoot, sub_eq_zero] using h
  have ha0 : a ≠ 0 := by
    intro hzero
    exact pow_ne_zero 2 (X_ne_zero (R := K) (0 : Fin 1))
      (by simpa [hzero] using heq.symm)
  have hdeg := congrArg (MvPolynomial.degreeOf 0) heq
  rw [degreeOf_pow_eq _ _ _ ha0, degreeOf_pow_eq _ _ _ (X_ne_zero 0), degreeOf_X_self] at hdeg
  omega

private def euler {K : Type*} [CommRing K] :
    Derivation K (MvPolynomial (Fin 2) K) (MvPolynomial (Fin 2) K) :=
  (4 * X 0 : MvPolynomial (Fin 2) K) • pderiv 0 +
    (6 * X 1 : MvPolynomial (Fin 2) K) • pderiv 1

private theorem euler_apply {K : Type*} [CommRing K] (f : MvPolynomial (Fin 2) K) :
    euler f = 4 * X 0 * pderiv 0 f + 6 * X 1 * pderiv 1 f := by
  simp [euler, smul_eq_mul]

private theorem euler_Abar : euler (Abar p) = (p - 1 : ℕ) * Abar p := by
  have h : (Abar p).IsWeightedHomogeneous ![4, 6] (p - 1 : ℕ) := by
    intro d hd
    simpa [Finsupp.weight_apply, Finsupp.sum_fintype, Fin.sum_univ_two,
      nsmul_eq_mul, Nat.mul_comm] using Abar_weight p hd
  simpa [euler_apply, Fin.sum_univ_two, nsmul_eq_mul, mul_assoc] using
    h.sum_weight_X_mul_pderiv

private theorem prime_dvd_derivation {K S : Type*} [CommRing K] [CommRing S]
    [IsDomain S] [Algebra K S] (D : Derivation K S S) {q a f : S} {n : ℕ}
    (hq : Prime q) (ha : ¬q ∣ a) (hn : ¬q ∣ (n + 1 : ℕ))
    (hf : f = q ^ (n + 1) * a) (hD : q ^ (n + 1) ∣ D f) : q ∣ D q := by
  rw [hf, derivation_pow_succ_mul] at hD
  have h : q ∣ q * D a + (n + 1) * (a * D q) := by
    apply (mul_dvd_mul_iff_left (pow_ne_zero n hq.ne_zero)).mp
    simpa only [pow_succ] using hD
  have h' : q ∣ (n + 1) * (a * D q) := by
    simpa using h.sub (dvd_mul_right q (D a))
  exact ((hq.dvd_mul.mp ((hq.dvd_mul.mp h').resolve_left
    (by simpa only [Nat.cast_add, Nat.cast_one] using hn)))).resolve_left ha

private theorem not_dvd_natCast_of_lt {q : MvPolynomial (Fin 2) (ZMod p)}
    (hq : Prime q) {n : ℕ} (hn : 0 < n) (hnp : n < p) : ¬q ∣ (n : ℕ) := by
  have hne : (n : ZMod p) ≠ 0 := by
    exact (_root_.ZMod.natCast_eq_zero_iff n p).not.mpr
      (Nat.not_dvd_of_pos_of_lt hn hnp)
  have hu : IsUnit (n : MvPolynomial (Fin 2) (ZMod p)) := by
    exact_mod_cast (isUnit_iff_ne_zero.mpr hne).map (MvPolynomial.C (σ := Fin 2))
  exact fun h => hq.not_isUnit (isUnit_of_dvd_unit h hu)

private theorem factor_power_lt {q a : MvPolynomial (Fin 2) (ZMod p)} {n : ℕ}
    (hq : Irreducible q) (h : Abar p = q ^ n * a) : n < p := by
  have hqdeg : 0 < q.totalDegree := by
    by_contra! hdeg
    have hc := totalDegree_eq_zero_iff_eq_C.mp (Nat.eq_zero_of_le_zero hdeg)
    exact hq.not_isUnit (hc ▸ by
      have hcoeff : q.coeff 0 ≠ 0 := by
        intro hz
        exact hq.ne_zero (by simpa [hz] using hc)
      exact (isUnit_iff_ne_zero.mpr hcoeff).map MvPolynomial.C)
  have ha : a ≠ 0 := by
    intro hz
    exact Abar_ne_zero p (by simp [h, hz])
  have hpow : ∀ n : ℕ, (q ^ n).totalDegree = n * q.totalDegree := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ, totalDegree_mul_of_isDomain (pow_ne_zero n hq.ne_zero) hq.ne_zero, ih]
      simp [Nat.add_mul]
  have hdeg := Abar_totalDegree_lt p
  rw [h, totalDegree_mul_of_isDomain (pow_ne_zero n hq.ne_zero) ha, hpow] at hdeg
  nlinarith

private theorem pderiv_totalDegree_lt {K : Type*} [Field K]
    {f : MvPolynomial (Fin 2) K} (i : Fin 2) (h : pderiv i f ≠ 0) :
    (pderiv i f).totalDegree < f.totalDegree := by
  have bound {d : Fin 2 →₀ ℕ} (hd : (pderiv i f).coeff d ≠ 0) :
      d.sum (fun _ e => e) + 1 ≤ f.totalDegree := by
    have hfd : f.coeff (d + Finsupp.single i 1) ≠ 0 := by
      rw [coeff_pderiv] at hd
      exact left_ne_zero_of_mul hd
    have hh := le_totalDegree (mem_support_iff.mpr hfd)
    simpa [Finsupp.sum_add_index] using hh
  have hpos : 0 < f.totalDegree := by
    obtain ⟨d, hd⟩ := exists_coeff_ne_zero h
    have := bound hd
    omega
  rw [MvPolynomial.totalDegree, Finset.sup_lt_iff hpos]
  intro d hd
  have := bound (mem_support_iff.mp hd)
  omega

private theorem pderiv_eq_zero_of_dvd {K : Type*} [Field K]
    {f : MvPolynomial (Fin 2) K} (i : Fin 2) (h : f ∣ pderiv i f) :
    pderiv i f = 0 := by
  by_contra hn
  exact (not_le_of_gt (pderiv_totalDegree_lt i hn))
    (totalDegree_le_of_dvd_of_isDomain h hn)

private theorem eq_C_of_pderiv_eq_zero_of_totalDegree_lt
    {f : MvPolynomial (Fin 2) (ZMod p)} (hf : f.totalDegree < p)
    (hd : ∀ i, pderiv i f = 0) : f = C (f.coeff 0) := by
  classical
  apply MvPolynomial.ext
  intro d
  by_cases hzero : d = 0
  · subst d; simp
  have hdne : ∃ i, d i ≠ 0 := by
    simpa only [Finsupp.ext_iff, Finsupp.coe_zero, Pi.zero_apply, not_forall] using hzero
  obtain ⟨i, hi⟩ := hdne
  rw [coeff_C, ite_eq_right (Ne.symm hzero)]
  by_contra hcoeff
  have hexp : d i < p := by
    have := (degreeOf_le_totalDegree f i).trans_lt hf
    exact lt_of_le_of_lt (le_degreeOf_of_mem_support i (mem_support_iff.mpr hcoeff)) this
  have hcast : (d i : ZMod p) ≠ 0 := by
    exact (_root_.ZMod.natCast_eq_zero_iff (d i) p).not.mpr
      (Nat.not_dvd_of_pos_of_lt (Nat.pos_of_ne_zero hi) hexp)
  have hderiv := congrArg (fun g : MvPolynomial (Fin 2) (ZMod p) =>
    g.coeff (d - Finsupp.single i 1)) (hd i)
  rw [coeff_pderiv, Finsupp.sub_add_single_one_cancel hi] at hderiv
  have hcount : ((d - Finsupp.single i 1 : Fin 2 →₀ ℕ) i) + 1 = d i := by
    simp [Finsupp.tsub_apply, Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hi)]
  have hcount' : (↑((d - Finsupp.single i 1 : Fin 2 →₀ ℕ) i) + 1 : ZMod p) =
      (d i : ZMod p) := by
    simpa only [Nat.cast_add, Nat.cast_one] using
      congrArg (fun n : ℕ => (n : ZMod p)) hcount
  have : f.coeff d * (d i : ZMod p) = 0 := by
    simpa only [hcount', AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply] using hderiv
  exact mul_ne_zero hcoeff hcast this

private theorem not_dvd_discriminant_of_dvd_Abar
    {q : MvPolynomial (Fin 2) (ZMod p)} (hq : Irreducible q) (hA : q ∣ Abar p) :
    ¬q ∣ X 0 ^ 3 - X 1 ^ 2 := by
  intro hd
  have hass := hq.associated_of_dvd discriminant_irreducible hd
  obtain ⟨a, ha⟩ := hass.symm.dvd.trans hA
  have h := congrArg (MvPolynomial.eval (fun _ => 1)) ha
  simp [Abar_eval_one] at h

/-- An irreducible factor of `Abar` is not preserved by the Serre derivation.
Euler's identity and `Del` have determinant a nonzero scalar times `X₀³ - X₁²`;
this discriminant cannot divide `Abar`, since its value at `(1, 1)` is zero. -/
theorem irreducible_not_dvd_Del_of_dvd_Abar
    {q : MvPolynomial (Fin 2) (ZMod p)} (hq : Irreducible q) (hA : q ∣ Abar p) :
    ¬q ∣ Del q := by
  intro hD
  have hprime : Prime q := UniqueFactorizationMonoid.irreducible_iff_prime.mp hq
  obtain ⟨n, a, ha, hf⟩ := WfDvdMonoid.max_power_factor (Abar_ne_zero p) hq
  have hE : q ∣ euler q := by
    cases n with
    | zero => exact False.elim (ha (by simpa [hf] using hA))
    | succ n =>
      apply prime_dvd_derivation euler hprime ha
        (not_dvd_natCast_of_lt p hprime (by omega) (factor_power_lt p hq hf)) hf
      rw [euler_Abar, hf]
      exact (dvd_mul_right (q ^ (n + 1)) a).mul_left _
  have hdelta := not_dvd_discriminant_of_dvd_Abar p hq hA
  have h4 := not_dvd_natCast_of_lt p hprime (by decide : 0 < 4)
    (by have := isLargePrime.AtLeastFive (ℓ := p); omega)
  have h6 : ¬q ∣ (6 : MvPolynomial (Fin 2) (ZMod p)) := by
    have hne : (6 : ZMod p) ≠ 0 := by
      intro hz
      have hd := (_root_.ZMod.natCast_eq_zero_iff 6 p).mp hz
      have hp : 5 ≤ p := isLargePrime.AtLeastFive
      have hle := Nat.le_of_dvd (by decide : 0 < 6) hd
      have hprimep : p.Prime := Fact.out
      have hp56 : p = 5 ∨ p = 6 := by omega
      rcases hp56 with rfl | rfl
      · norm_num at hd
      · exact (by decide : ¬Nat.Prime 6) hprimep
    have hu : IsUnit (6 : MvPolynomial (Fin 2) (ZMod p)) := by
      exact_mod_cast (isUnit_iff_ne_zero.mpr hne).map (MvPolynomial.C (σ := Fin 2))
    exact fun h => hprime.not_isUnit (isUnit_of_dvd_unit h hu)
  have h0 : q ∣ 4 * (X 0 ^ 3 - X 1 ^ 2) * pderiv 0 q := by
    convert (hE.mul_left (X 0 ^ 2)).add (hD.mul_left (X 1)) using 1
    simp only [euler_apply, Del_apply, Algebra.smul_def, MvPolynomial.algebraMap_eq,
      _root_.map_neg, _root_.map_ofNat]
    ring
  have h1 : q ∣ 6 * (X 0 ^ 3 - X 1 ^ 2) * pderiv 1 q := by
    convert ((hE.mul_left (X 1)).add (hD.mul_left (X 0))).neg_right using 1
    simp only [euler_apply, Del_apply, Algebra.smul_def, MvPolynomial.algebraMap_eq,
      _root_.map_neg, _root_.map_ofNat]
    ring
  have hd0 : pderiv 0 q = 0 := pderiv_eq_zero_of_dvd 0
    ((hprime.dvd_mul.mp h0).resolve_left (fun h =>
      ((hprime.dvd_mul.mp h).resolve_left h4) |> hdelta))
  have hd1 : pderiv 1 q = 0 := pderiv_eq_zero_of_dvd 1
    ((hprime.dvd_mul.mp h1).resolve_left (fun h =>
      ((hprime.dvd_mul.mp h).resolve_left h6) |> hdelta))
  have hc := eq_C_of_pderiv_eq_zero_of_totalDegree_lt p
    (lt_of_le_of_lt (totalDegree_le_of_dvd_of_isDomain hA (Abar_ne_zero p))
      (Abar_totalDegree_lt p)) (fun i => by fin_cases i <;> assumption)
  have hcoeff : q.coeff 0 ≠ 0 := by
    intro hz
    exact hq.ne_zero (by simpa [hz] using hc)
  exact hq.not_isUnit (hc ▸ (isUnit_iff_ne_zero.mpr hcoeff).map MvPolynomial.C)

/-- Lemma 1.40 (i): the reduction of the Hasse polynomial has no repeated factors. -/
theorem squarefree_Abar : Squarefree (Abar p) := by
  apply (squarefree_iff_no_irreducibles (Abar_ne_zero p)).mpr
  intro q hq hq2
  have hprime : Prime q := UniqueFactorizationMonoid.irreducible_iff_prime.mp hq
  have hqA : q ∣ Abar p := (dvd_mul_right q q).trans hq2
  have hnotD := irreducible_not_dvd_Del_of_dvd_Abar p hq hqA
  obtain ⟨n, a, ha, hf⟩ := WfDvdMonoid.max_power_factor (Abar_ne_zero p) hq
  have hn : 2 ≤ n := by
    apply (pow_dvd_pow_iff hq.ne_zero hq.not_isUnit).mp
    apply hprime.pow_dvd_of_dvd_mul_right 2 ha
    simpa only [pow_two, ← hf] using hq2
  let m := n - 2
  have hnm : n = m + 2 := by dsimp [m]; omega
  rw [hnm] at hf
  have hnp := factor_power_lt p hq hf
  have hn1 := not_dvd_natCast_of_lt p hprime (by omega : 0 < m + 1)
    (by omega : m + 1 < p)
  have hn2 := not_dvd_natCast_of_lt p hprime (by omega : 0 < m + 2) hnp
  let s := q * Del a + (m + 2) * (a * Del q)
  have hB : Bbar p = q ^ (m + 1) * s := by
    rw [← Del_Abar, hf]
    simpa only [s, Nat.add_assoc, Nat.cast_add, Nat.cast_one, add_assoc,
      one_add_one_eq_two] using derivation_pow_succ_mul (Del (R := ZMod p)) q a (m + 1)
  have hD : q ^ (m + 1) ∣ Del (Bbar p) := by
    rw [Del_Bbar, hf]
    exact ((pow_dvd_pow q (by omega : m + 1 ≤ m + 2)).mul_right a).mul_left _
  rw [hB, derivation_pow_succ_mul] at hD
  have hs : q ∣ q * Del s + (m + 1) * (s * Del q) := by
    apply (mul_dvd_mul_iff_left (pow_ne_zero m hq.ne_zero)).mp
    simpa only [pow_succ] using hD
  have hs' : q ∣ (m + 1) * (s * Del q) := by
    simpa using hs.sub (dvd_mul_right q (Del s))
  have hqs : q ∣ s := ((hprime.dvd_mul.mp ((hprime.dvd_mul.mp hs').resolve_left
    (by simpa using hn1)))).resolve_right hnotD
  have hs'' : q ∣ (m + 2) * (a * Del q) := by
    simpa only [s, add_sub_cancel_left] using hqs.sub (dvd_mul_right q (Del a))
  exact hnotD (((hprime.dvd_mul.mp ((hprime.dvd_mul.mp hs'').resolve_left
    (by simpa using hn2)))).resolve_left ha)

end ModularFormMod.ZMod
