import ModularFormsMod.ModularFormMod.ZMod.Theta
import ModularFormsMod.ModularFormMod.Hecke
import ModularFormsMod.ModularFormMod.Basis

set_option linter.style.header false

/-!
# The U operator on modular forms modulo a prime

The operator selects the coefficients whose indices are divisible by `p`.
In weights at least two it is the reduction of the prime Hecke operator `T_p`.
In weight zero it fixes constants, extending the coefficient formula to every weight.
-/

open PowerSeries MatrixGroups CongruenceSubgroup ModularFormOver PInteger

noncomputable section

namespace CongruenceSubgroup

/-- The level-one subgroup `Γ₁(1)` is the full modular group. -/
theorem Gamma1_one_coe_eq_SL : (Gamma1 1 : Subgroup (GL (Fin 2) ℝ)) = 𝒮ℒ := by
  have h : Gamma1 1 = ⊤ := by
    apply top_unique
    intro A _
    rw [Gamma1_mem]
    exact ⟨Subsingleton.elim _ _, Subsingleton.elim _ _, Subsingleton.elim _ _⟩
  change (Gamma1 1).map _ = _
  rw [h, Subgroup.map_top]

end CongruenceSubgroup

namespace ModularFormOver

variable {p : ℕ} [isLargePrime p] {k : ℤ}

private theorem mem_trivialChar_one (f : ModularForm (Gamma1 1) k) :
    f ∈ HeckeRing.GL2.modFormCharSpace k (trivialChar 1) := by
  rw [HeckeRing.GL2.mem_modFormCharSpace_iff]
  intro d
  have hd : d = 1 := Subsingleton.elim _ _
  simp [hd, trivialChar]

private def T_pIntegralGamma1 (hk : 1 ≤ k) (f : ModularFormOver ℤ(p) (Gamma1 1) k) :
    ModularFormOver ℤ(p) (Gamma1 1) k where
  toModularForm := (T_p 1 p (by simp)).1 k f.toModularForm
  isOver' := by
    rw [ModularForm.isOver_iff]
    intro n
    refine ⟨∑ d ∈ (Nat.gcd n p).divisors,
      (d : ℤ(p)) ^ (k - 1).toNat * coeff ℤ(p) (n * p / (d * d)) f, ?_⟩
    rw [T_p_coeff 1 p (by simp) k _ (mem_trivialChar_one _) n, map_sum]
    apply Finset.sum_congr rfl
    intro d hd
    have hk' : k - 1 = ((k - 1).toNat : ℤ) := by omega
    have hpow : (d : ℂ) ^ (k - 1) = (d : ℂ) ^ (k - 1).toNat := by
      conv_lhs => rw [hk', zpow_natCast]
    simp only [map_mul, map_pow, map_natCast, map_coeff_eq_qExp, hpow]
    rfl

private theorem coeff_T_pIntegralGamma1 (hk : 1 ≤ k)
    (f : ModularFormOver ℤ(p) (Gamma1 1) k) (n : ℕ) :
    coeff ℤ(p) n (T_pIntegralGamma1 hk f) =
      ∑ d ∈ (Nat.gcd n p).divisors,
        (d : ℤ(p)) ^ (k - 1).toNat * coeff ℤ(p) (n * p / (d * d)) f := by
  rw [coeff_eq_iff]
  change (ModularForm.qExp ((T_p 1 p (by simp)).1 k f.toModularForm)).coeff n = _
  rw [T_p_coeff 1 p (by simp) k _ (mem_trivialChar_one _) n, map_sum]
  apply Finset.sum_congr rfl
  intro d hd
  have hk' : k - 1 = ((k - 1).toNat : ℤ) := by omega
  have hpow : (d : ℂ) ^ (k - 1) = (d : ℂ) ^ (k - 1).toNat := by
    conv_lhs => rw [hk', zpow_natCast]
  simp only [map_mul, map_pow, map_natCast, map_coeff_eq_qExp, hpow]
  rfl

private def T_pIntegralAt {Γ : Subgroup (GL (Fin 2) ℝ)}
    (hΓ : Γ = (Gamma1 1 : Subgroup (GL (Fin 2) ℝ))) (hk : 1 ≤ k)
    (f : ModularFormOver ℤ(p) Γ k) : ModularFormOver ℤ(p) Γ k := by
  subst Γ
  exact T_pIntegralGamma1 hk f

private theorem coeff_T_pIntegralAt {Γ : Subgroup (GL (Fin 2) ℝ)}
    [Γ.IsArithmetic] (hΓ : Γ = (Gamma1 1 : Subgroup (GL (Fin 2) ℝ))) (hk : 1 ≤ k)
    (f : ModularFormOver ℤ(p) Γ k) (n : ℕ) :
    coeff ℤ(p) n (T_pIntegralAt hΓ hk f) =
      ∑ d ∈ (Nat.gcd n p).divisors,
        (d : ℤ(p)) ^ (k - 1).toNat * coeff ℤ(p) (n * p / (d * d)) f := by
  subst Γ
  exact coeff_T_pIntegralGamma1 hk f n

/-- In positive weight the prime Hecke operator preserves `p`-integral coefficients.
The underlying complex operator is `T_p 1 p`, transported to the full modular group. -/
def T_pIntegral (hk : 1 ≤ k) (f : ModularFormOver ℤ(p) 𝒮ℒ k) :
    ModularFormOver ℤ(p) 𝒮ℒ k :=
  T_pIntegralAt Gamma1_one_coe_eq_SL.symm hk f

/-- The integral divisor formula for the prime Hecke operator in positive weight. -/
theorem coeff_T_pIntegral (hk : 1 ≤ k) (f : ModularFormOver ℤ(p) 𝒮ℒ k) (n : ℕ) :
    coeff ℤ(p) n (T_pIntegral hk f) =
      ∑ d ∈ (Nat.gcd n p).divisors,
        (d : ℤ(p)) ^ (k - 1).toNat * coeff ℤ(p) (n * p / (d * d)) f :=
  coeff_T_pIntegralAt Gamma1_one_coe_eq_SL.symm hk f n

end ModularFormOver

namespace ModularFormMod

open scoped ModularFormMod.ZMod

variable {p : ℕ} [isLargePrime p] {k : ℤ}

private theorem coeff_reduce_T_pIntegral (hk : 2 ≤ k)
    (f : ModularFormOver ℤ(p) 𝒮ℒ k) (n : ℕ) :
    coeff n ((T_pIntegral (by omega) f).Reduce reduce) = coeff (n * p) (f.Reduce reduce) := by
  rw [coeff_Reduce, coeff_T_pIntegral, map_sum]
  rw [Finset.sum_eq_single 1]
  · simp
  · intro d hd hd1
    have hdp : d ∣ p := dvd_trans (Nat.mem_divisors.mp hd).1 (Nat.gcd_dvd_right n p)
    have hd : d = p := ((Nat.dvd_prime (Fact.out : p.Prime)).mp hdp).resolve_left hd1
    subst d
    have hk' : (k - 1).toNat ≠ 0 := by omega
    simp only [_root_.map_mul, _root_.map_pow, map_natCast, ZMod.natCast_self,
      zero_pow hk', zero_mul]
  · intro h
    exact (h (Nat.mem_divisors.mpr ⟨one_dvd _, Nat.gcd_ne_zero_right (NeZero.ne p)⟩)).elim

private theorem coeff_mul_prime_of_lt_two (hk : k < 2) (f : 𝓜 p k) (n : ℕ) :
    coeff (n * p) f = coeff n f := by
  by_cases hk0 : k = 0
  · subst k
    have hf : f = const (coeff 0 f) := by
      apply sturm_bound
      intro m hm
      have hm0 : m = 0 := by
        simpa [ModularFormOver.Basis.dim, ModularFormOver.Basis.dimNat] using hm
      subst m
      simp [coeff]
    rw [hf]
    have hp : p ≠ 0 := NeZero.ne p
    simp [coeff, PowerSeries.coeff_C, hp]
  · have hf : f = 0 := by
      apply sturm_bound
      intro m hm
      have hdim : ModularFormOver.Basis.dim k = 0 := by
        by_cases hkneg : k < 0
        · exact ModularFormOver.Basis.dim_neg k hkneg
        · have : k = 1 := by omega
          subst k
          rfl
      omega
    simp [hf]

/-- The U operator selects coefficients at multiples of `p`. In weight at least two
it is obtained by reducing `T_p 1 p`; in weight zero it fixes constants. -/
def UOp (f : 𝓜 p k) : 𝓜 p k where
  fourier := PowerSeries.mk fun n => coeff (n * p) f
  modular := by
    by_cases hk : 2 ≤ k
    · obtain ⟨g, rfl⟩ := f.existsReduce
      refine ⟨T_pIntegral (by omega) g, ?_⟩
      ext n
      simpa only [PowerSeries.coeff_mk, coeff, Reduce_fourier] using
        (coeff_reduce_T_pIntegral hk g n).symm
    · have hfourier : (PowerSeries.mk fun n => coeff (n * p) f) = f.fourier := by
        ext n
        simpa only [PowerSeries.coeff_mk, coeff] using
          coeff_mul_prime_of_lt_two (by omega) f n
      exact hfourier ▸ f.modular

@[simp] theorem UOp_fourier (f : 𝓜 p k) :
    f.UOp.fourier = PowerSeries.mk (fun n => coeff (n * p) f) := rfl

/-- The degree-`n` coefficient of `UOp f` is the degree-`np` coefficient of `f`. -/
@[simp] theorem coeff_UOp (f : 𝓜 p k) (n : ℕ) :
    coeff n f.UOp = coeff (n * p) f := by
  simp only [coeff, UOp, PowerSeries.coeff_mk]

@[simp] theorem coeff_zero_UOp (f : 𝓜 p k) : coeff 0 f.UOp = coeff 0 f := by
  simp

@[simp] theorem coeff_one_UOp (f : 𝓜 p k) : coeff 1 f.UOp = coeff p f := by
  simp

/-- Repeated application of U selects coefficients at multiples of powers of `p`. -/
theorem coeff_iterate_UOp (f : 𝓜 p k) (m n : ℕ) :
    coeff n (UOp^[m] f) = coeff (n * p ^ m) f := by
  induction m generalizing n with
  | zero => simp
  | succ m ih =>
    rw [Function.iterate_succ_apply', coeff_UOp, ih]
    congr 1
    ring

/-- In weights at least two, U agrees with reduction of the prime Hecke operator. -/
theorem UOp_Reduce (hk : 2 ≤ k) (f : ModularFormOver ℤ(p) 𝒮ℒ k) :
    (f.Reduce reduce).UOp = (T_pIntegral (by omega) f).Reduce reduce := by
  apply ext_coeff
  intro n
  rw [coeff_UOp]
  exact (coeff_reduce_T_pIntegral hk f n).symm

@[simp] theorem UOp_zero : UOp (0 : 𝓜 p k) = 0 := by
  apply ext_coeff
  intro n
  simp

@[simp] theorem UOp_add (f g : 𝓜 p k) : (f + g).UOp = f.UOp + g.UOp := by
  apply ext_coeff
  intro n
  simp

@[simp] theorem UOp_smul (a : ZMod p) (f : 𝓜 p k) : (a • f).UOp = a • f.UOp := by
  apply ext_coeff
  intro n
  simp only [coeff_UOp, coeff_smul_of_surjective]

/-- The U operator as an endomorphism over the residue field. -/
def UOpLinearMap : Module.End (ZMod p) (𝓜 p k) where
  toFun := UOp
  map_add' := UOp_add
  map_smul' := UOp_smul

/-- In weights below two the U operator is the identity. -/
theorem UOp_of_lt_two (hk : k < 2) (f : 𝓜 p k) : f.UOp = f := by
  apply ext_coeff
  intro n
  rw [coeff_UOp]
  exact coeff_mul_prime_of_lt_two hk f n

@[simp] theorem UOp_one : UOp (1 : 𝓜 p 0) = 1 :=
  UOp_of_lt_two (by decide) _


@[simp] theorem UOp_pow_card (f : 𝓜 p k) : (f.UOp.pow p).fourier =
    f.fourier - (f.Theta_pow (p - 1)).fourier := by
  ext n
  simp only [map_sub, coeff_fourier, coeff_pow_card, coeff_UOp,
    coeff_Theta_pow, ZMod.pow_card_sub_one, ne_eq, ZMod.natCast_eq_zero_iff,
    ite_not, ite_mul, zero_mul, one_mul, sub_ite, sub_zero, sub_self]
  congr! with h
  exact Nat.div_mul_cancel h


end ModularFormMod
