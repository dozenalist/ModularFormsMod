/-
Copyright (c) 2026 Carter Hastings. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carter Hastings
-/

import Lean.Elab.Tactic.Simproc
import Lean.Meta.Reduce
import Mathlib.LinearAlgebra.Dimension.OrzechProperty
import ModularFormsMod.ModularFormOver.Rat

/-!
# Bases and the Sturm bound for level-one modular forms

`dim` gives the dimension in each integer weight. The monomials `G` in `E₄`,
`E₆`, and `Δ` form the basis `GBasis`, with leading coefficients equal to one
and increasing orders of vanishing. This yields `ModularFormOver.sturm_bound`
and the rank and finrank formulas.

When `6` is invertible in the coefficient ring, monomials `P` in `E₄` and `E₆`
alone form the alternative basis `PBasis`.
-/

open ModularForm MatrixGroups UpperHalfPlane ModularFormOver PowerSeries


namespace ModularFormOver.Basis

/-- The dimension of level-one modular forms in natural weight, defined recursively in steps of
twelve. -/
def dimNat : ℕ → ℕ
  | 0 => 1 | 4 => 1 | 6 => 1
  | 8 => 1 | 10 => 1 | 14 => 1
  | n + 12 => match dimNat n with
    | 0 => 0
    | d + 1 => d + 2
  | _ => 0


/-- The level-one dimension function for integer weights, equal to zero at negative weights. -/
def dim : ℤ → ℕ
  | Int.ofNat n => dimNat n
  | Int.negSucc _ => 0


/-- The closed dimension formula, with the exceptional residue class `k ≡ 2 [ZMOD 12]`. -/
def dim' (k : ℤ) : ℕ :=
  if 0 ≤ k then if Even k then if k ≡ 2 [ZMOD 12] then k.toNat / 12 else k.toNat / 12 + 1
    else 0 else 0

/-- The recursive dimension formula agrees with the closed formula in natural weights. -/
theorem dimNat_eq_dim' (n : ℕ) : dimNat n = dim' n := by
  fun_induction dimNat n with
  | case9 n _ _ _ _ _ _ h =>
    have hn : n < 12 := by
      by_contra! hn
      exact h (n - 12) (by omega)
    simp only [dim', Int.even_iff, Int.ModEq]
    grind
  | _ =>
    simp only [dim', Int.even_iff, Int.ModEq] at *
    grind

/-- The recursive and closed dimension functions agree for all integer weights. -/
theorem dim_eq_dim' : dim = dim' := by
  funext k
  cases k with
  | ofNat n => exact dimNat_eq_dim' n
  | negSucc n => simp [dim, dim']

/-- The dimension function vanishes in negative weights. -/
theorem dim_neg (k : ℤ) (hk : k < 0) : dim k = 0 := by
  simp_all only [dim_eq_dim', dim', ite_eq_right_iff, isEmpty_Prop, not_le, IsEmpty.forall_iff]


/-- The level-one dimension is at most `k.toNat / 12 + 1`. -/
theorem dim_le_div_twelve (k : ℤ) : dim k ≤ k.toNat / 12 + 1 := by
  rw [dim_eq_dim']
  grind [dim']

/-- The complex space of level-one forms of weight `k` has rank `dim k`. -/
theorem _root_.ModularForm.rank_eq_dim (k : ℤ) : Module.rank ℂ (ModularForm 𝒮ℒ k) = dim k := by
  rw [dim_eq_dim', dim']
  split_ifs with hk hk2 kcon
  · lift k to ℕ using hk
    rw [dimension_level_one k (by grind), ite_eq_left (by grind [Nat.ModEq, Int.ModEq])]
    rfl
  · lift k to ℕ using hk
    rw [dimension_level_one k (by grind), ite_eq_right (by grind [Nat.ModEq, Int.ModEq])]
    rfl
  · simp only [Int.not_even_iff_odd] at hk2
    rw [ModularForm.levelOne_odd_weight_rank_zero hk2, Nat.cast_zero]
  · rw [ModularForm.levelOne_neg_weight_rank_zero (not_le.1 hk), Nat.cast_zero]


/-- A level-one form of natural weight vanishes if its Fourier expansion has order at least `dim
k`. -/
theorem _root_.ModularForm.better_sturm_bound_levelOne_nat {k : ℕ} {f : ModularForm 𝒮ℒ (k : ℤ)}
    (h : (dim k : ℕ∞) ≤ (qExpansion 1 f).order) : f = 0 := by
  induction k using Nat.strong_induction_on with | _ k ih =>
  have h0 : (qExpansion 1 f).coeff 0 = 0 := by
    by_cases hord : (qExpansion 1 ⇑f).order = 0
    · have : dim k = 0 := by rw [hord] at h; norm_cast at *; exact Nat.eq_zero_of_le_zero h
      rw [← Nat.cast_eq_zero (R := Cardinal.{0}), ← ModularForm.rank_eq_dim,
        rank_zero_iff_forall_zero] at this
      simp only [this f, FunLike.coe_zero, qExpansion_zero, map_zero]
    · exact PowerSeries.coeff_of_lt_order _
        (by simpa only [CharP.cast_eq_zero] using pos_iff_ne_zero.mpr hord)
  suffices CuspForm.discriminantEquiv (toCuspForm f h0) = 0 by
    simpa [CuspForm.discriminantEquiv.map_eq_zero_iff, DFunLike.ext_iff]
  by_cases hk : k < 12 ∨ Odd k ∨ k = 14
  · obtain (hk12 | kodd | k14) := hk
    · apply rank_zero_iff_forall_zero.mp (levelOne_neg_weight_rank_zero (by lia))
    · apply rank_zero_iff_forall_zero.mp (ModularForm.levelOne_odd_weight_rank_zero (by grind))
    subst k14; apply rank_zero_iff_forall_zero.mp levelOne_weight_two_rank_zero
  · rw [← mcast_eq_zero_iff (b := ↑(k - 12)) (by lia) rfl]
    refine ih (k - 12) (by lia) ?_
    have hsucc : dim k = dim (k - 12) + 1 := by
      simp only [dim_eq_dim', dim', Int.ModEq]
      grind
    rw [qExpansion_eq_qExpansion_discriminant_mul f h0, PowerSeries.order_mul,
      discriminant_qExpansion_order, add_comm, hsucc, Nat.cast_add, Nat.cast_one] at h
    simp_rw [@Nat.cast_sub _ _ 12 k (by lia)]
    exact (ENat.add_le_add_iff_right (ENat.one_ne_top)).mp h


/-- A level-one form of integer weight vanishes if its Fourier expansion has order at least `dim
k`. -/
theorem _root_.ModularFormOver.better_sturm_bound_levelOne {k : ℤ} {f : ModularForm 𝒮ℒ k}
    (h : (dim k : ℕ∞) ≤ (qExpansion 1 f).order) : f = 0 := by
  rcases lt_or_ge k 0 with hk | hk
  · exact rank_zero_iff_forall_zero.mp (levelOne_neg_weight_rank_zero hk) f
  · lift k to ℕ using hk
    exact better_sturm_bound_levelOne_nat (mod_cast h)


section GBasis

/-! The entries are the exponents of `E4`, `E6`, and `Delta`, respectively. -/

/-- Exponent triples for the basis `E4^a * E6^b * Delta^c` of weight `k`,
ordered by increasing `c`. Odd weights and weight `2` give the empty list. -/
def GpowersNat : ℕ → List (Fin 3 → ℕ)
  | 0 => [![0,0,0]]
  | 4 => [![1,0,0]]
  | 6 => [![0,1,0]]
  | 8 => [![2,0,0]]
  | 10 => [![1,1,0]]
  | 14 => [![2,1,0]]
  | n + 12 => match GpowersNat n with
    | [] => []
    | p :: ps =>
      ![p 0 + 3, p 1, 0] :: (p :: ps).map (fun q => ![q 0, q 1, q 2 + 1])
  | _ => []

example : GpowersNat 12 = [![3,0,0], ![0,0,1]] := rfl

example : GpowersNat 16 = [![4,0,0], ![1,0,1]] := rfl

example : GpowersNat 18 = [![3,1,0], ![0,1,1]] := rfl

/-- The exponent triples for the weight-`k` basis, with an empty list at negative weights. -/
def Gpowers : ℤ → List (Fin 3 → ℕ)
  | Int.ofNat n => GpowersNat n
  | Int.negSucc _ => []


/-- The natural-weight exponent list has one entry per basis element. -/
@[simp] theorem GpowersNat_length (k : ℕ) : (GpowersNat k).length = dimNat k := by
  fun_induction GpowersNat k with
  | case7 n _ hps ih =>
    simp only [hps, List.length_nil] at ih
    simp [dimNat, ← ih]
  | case8 n _ p ps hps ih =>
    simp only [hps, List.length_cons] at ih
    simp [dimNat, ← ih]
  | _ => simp_all [dimNat]

/-- The exponent list has one entry per basis element. -/
@[simp] theorem Gpowers_length (k : ℤ) : (Gpowers k).length = dim k := by
  cases k with
  | ofNat n => exact GpowersNat_length n
  | negSucc n => rfl

private theorem GpowersNat_head_delta (k : ℕ) :
    ∀ p ps, GpowersNat k = p :: ps → p 2 = 0 := by
  fun_induction GpowersNat k <;> simp_all

/-- Every exponent triple in `GpowersNat k` has total weight `k`. -/
theorem GpowersNat_weight (k : ℕ) :
    ∀ p ∈ GpowersNat k, p 0 * 4 + p 1 * 6 + p 2 * 12 = k := by
  fun_induction GpowersNat k with
  | case8 n _ p ps hps ih =>
    intro q hq
    rcases List.mem_cons.mp hq with hq | hq
    · subst q
      have hw := ih p (by simp [hps])
      have hzero := GpowersNat_head_delta n p ps hps
      change (p 0 + 3) * 4 + p 1 * 6 + 0 * 12 = n + 12
      omega
    · obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hq
      have hw := ih r (by rwa [hps])
      change r 0 * 4 + r 1 * 6 + (r 2 + 1) * 12 = n + 12
      omega
  | _ => simp_all

/-- Every exponent triple in `Gpowers k` has total weight `k`. -/
theorem Gpowers_weight {k : ℤ} {p : Fin 3 → ℕ} (hp : p ∈ Gpowers k) :
    p 0 * 4 + p 1 * 6 + p 2 * 12 = k := by
  cases k with
  | ofNat n =>
    change p 0 * 4 + p 1 * 6 + p 2 * 12 = (n : ℤ)
    exact_mod_cast GpowersNat_weight n p hp
  | negSucc n => simp [Gpowers] at hp


/-- The exponent triple at any index below `dim k` has total weight `k`. -/
theorem Gpowers_getElem_weight (k : ℤ) (n : ℕ) (hn : n < dim k) :
    let p := (Gpowers k)[n]'(by rwa [Gpowers_length])
    p 0 * 4 + p 1 * 6 + p 2 * 12 = k := by
  exact Gpowers_weight (List.getElem_mem _)


private theorem GpowersNat_getElem_properties (k : ℕ) :
    ∀ n (hn : n < (GpowersNat k).length),
      (GpowersNat k)[n] 1 ≤ 1 ∧ (GpowersNat k)[n] 2 = n := by
  fun_induction GpowersNat k with
  | case8 k _ p ps hps ih =>
    rw [hps] at ih
    intro n hn
    cases n with
    | zero =>
      have hp := (ih 0 (by simp)).1
      simpa using hp
    | succ n =>
      have hn' : n < (p :: ps).length := by simpa using hn
      have hp := ih n hn'
      simpa using hp
  | _ => simp_all

/-- The exponents of `E₄`, `E₆`, and `Δ` at index `n`, without list lookups. -/
theorem Gpowers_getElem_eq (k : ℤ) (n : ℕ) (hn : n < dim k) :
    (Gpowers k)[n]'(by rwa [Gpowers_length]) =
      ![(k.toNat - 12 * n - 6 * (k.toNat % 4 / 2)) / 4, k.toNat % 4 / 2, n] := by
  cases k with
  | ofNat k =>
    change n < dimNat k at hn
    have hn' : n < (GpowersNat k).length := by rwa [GpowersNat_length]
    have hp := GpowersNat_getElem_properties k n hn'
    have hw := GpowersNat_weight k _ (List.getElem_mem hn')
    change (GpowersNat k)[n]'hn' =
      ![(k - 12 * n - 6 * (k % 4 / 2)) / 4, k % 4 / 2, n]
    ext i
    fin_cases i <;> dsimp <;> omega
  | negSucc k => simp [dim] at hn


/-- The weight-`k` monomial in `E₄`, `E₆`, and `Δ` whose Fourier expansion starts with `q^n`. -/
noncomputable def G {R} [CommRing R] [Algebra R ℂ]
    (k : ℤ) (n : ℕ) (hn : n < dim k := by decide) : ModularFormOver R 𝒮ℒ k :=
  let p := (Gpowers k)[n]'(by rwa [Gpowers_length])
  (((E₄.pow (p 0)).mul (E₆.pow (p 1))).mul ((Δ).pow (p 2))).cast
    (Gpowers_getElem_weight k n hn)

/-- An explicit product formula for the basis element, with discriminant exponent `n`. -/
theorem G_eq {R} [CommRing R] [Algebra R ℂ]
    (k : ℤ) (n : ℕ) (hn : n < dim k) :
    G (R := R) k n hn =
      (((E₄.pow ((k.toNat - 12 * n - 6 * (k.toNat % 4 / 2)) / 4)).mul
        (E₆.pow (k.toNat % 4 / 2))).mul ((Δ).pow n)).cast (b := k) (by
          have hw := Gpowers_getElem_weight k n hn
          dsimp only at hw
          rw [Gpowers_getElem_eq k n hn] at hw
          exact hw) := by
  apply ext₂
  intro z
  change (((E₄.pow _).mul (E₆.pow _)).mul ((Δ).pow _)) z =
    (((E₄.pow _).mul (E₆.pow _)).mul ((Δ).pow _)) z
  simp only [mul_apply, pow_apply]
  rw [Gpowers_getElem_eq k n hn]
  rfl

/-- The Fourier expansion of `G k n` is the product of the corresponding expansions of `E₄`,
`E₆`, and `Δ`. -/
theorem qExp_G {R} [CommRing R] [Algebra R ℂ]
    (k : ℤ) (n : ℕ) (hn : n < dim k) :
    qExp (G (R := R) k n hn) =
      qExp E₄ ^ ((k.toNat - 12 * n - 6 * (k.toNat % 4 / 2)) / 4) *
        qExp E₆ ^ (k.toNat % 4 / 2) * qExp Δ ^ n := by
  rw [G_eq k n hn]
  change qExp (((E₄.toModularForm.pow _).mul (E₆.toModularForm.pow _)).mul
    ((Δ).toModularForm.pow n)) = _
  rw [qExp_mul, qExp_mul, qExp_pow, qExp_pow, qExp_pow]
  rfl

open Lean Meta in
/-- Unfold `G k n hn` when `k` and `n` are numerals, computing the exponent triple
and removing the weight cast and identity bundling coercions by definitional equality.
Runs automatically with `simp` and `dsimp`, or explicitly with `simp only [reduceG]`.
Symbolic weights and indices are left unchanged. -/
dsimproc reduceG (@G _ _ _ _ _ _) := fun e => do
  let_expr G _ _ _ k n _ := e | return .continue
  unless (← getIntValue? k).isSome && (← getNatValue? n).isSome do
    return .continue
  let some unfolded ← unfoldDefinition? e (ignoreTransparency := true) | return .continue
  let .letE _ _ powers body _ := unfolded | return .continue
  -- Evaluate the exponent lookups while preserving the modular-form operations.
  let body ← transform (body.instantiate1 powers) (pre := fun t => do
    if t.isApp && t.appFn! == powers then
      return .done (← withTransparency .all <| reduce t)
    return .continue)
  let isWrapper := fun (t : Expr) =>
    t.isAppOf ``ModularFormOver.cast || t.isAppOf `cast ||
      t.isAppOf ``ModularFormOverClass.modularFormOver
  let mut result := body
  while true do
    let candidate ← if isWrapper result then pure result else whnfR result
    unless isWrapper candidate do break
    let value := candidate.appArg!
    let canErase ← withTransparency .default do
      return (← isDefEq (← inferType value) (← inferType e)) &&
        (← isDefEq result value)
    unless canErase do break
    result := value
  return .continue result


private theorem qExp_discriminant_eq_shift_mul_X :
    qExp Δ = (PowerSeries.mk fun m => (qExp Δ).coeff (m + 1)) * X := by
  have h0 : constantCoeff (qExp Δ) = 0 := by
    rw [← coeff_zero_eq_constantCoeff, discriminant_qExp_coeff]
    simp [discProduct]
  simpa only [h0, map_zero, add_zero] using eq_shift_mul_X_add_const (qExp Δ)

/-- The coefficient of degree `n` in `G k n` is one. -/
theorem coeff_order_G {R} [CommRing R] [Algebra R ℂ] [FaithfulSMul R ℂ] (k : ℤ)
    (n : ℕ) (hn : n < dim k) : coeff R n (G (R := R) k n hn) = 1 := by
  rw [coeff_eq_iff, map_one, qExp_G k n hn, qExp_discriminant_eq_shift_mul_X,
    mul_pow, ← mul_assoc]
  nth_rw 1 [← zero_add n]
  rw [coeff_mul_X_pow, coeff_zero_eq_constantCoeff]
  simp only [map_mul, map_pow, constantCoeff_mk, zero_add,
    ← coeff_zero_eq_constantCoeff, E₄_qExp_coeff, E₆_qExp_coeff, reduceIte,
    discriminant_qExp_coeff]
  simp [discProduct]

/-- The coefficients of `G k c` vanish in degrees below `c`. -/
theorem coeff_lt_order_G {R} [CommRing R] [Algebra R ℂ] [FaithfulSMul R ℂ]
    (k : ℤ) (c : ℕ) (hc : c < dim k) {n} (hn : n < c) :
    coeff R n (G (R := R) k c hc) = 0 := by
  rw [coeff_eq_iff, map_zero, qExp_G k c hc, qExp_discriminant_eq_shift_mul_X,
    mul_pow, ← mul_assoc,
    coeff_mul_X_pow', ite_eq_right (Nat.not_le.mpr hn)]


/-- The complex Fourier expansion of `G k n` has order exactly `n`. -/
theorem order_G {R} [CommRing R] [Algebra R ℂ] [FaithfulSMul R ℂ] (k : ℤ)
    (n : ℕ) (hn : n < dim k) : order (qExp (G (R := ℂ) k n hn)) = n := by
  apply PowerSeries.order_eq_nat.mpr
  constructor
  · have h := coeff_order_G (R := ℂ) k n hn
    rw [coeff_def, fourierℂ] at h
    rw [h]
    exact one_ne_zero
  · intro i hi
    simpa only [coeff_def, fourierℂ] using coeff_lt_order_G (R := ℂ) k n hn hi


/-- The `G` monomials of a fixed weight are linearly independent over the coefficient ring. -/
theorem G_LI {R} [CommRing R] [Algebra R ℂ] [FaithfulSMul R ℂ] (k : ℤ) :
    LinearIndependent R (fun n : Fin (dim k) => G (R := R) k n.val n.isLt) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro a ha ⟨n, hn⟩
  induction n using Nat.strong_induction_on with
  | h n ih =>
    let c : ModularFormOver R 𝒮ℒ k →ₗ[R] R :=
      { toFun := coeff R n
        map_add' := coeff_add R R n
        map_smul' := coeff_smul R R n }
    have hcoeff : ∑ j : Fin (dim k), a j * coeff R n (G (R := R) k j.val j.isLt) = 0 := by
      have h := congrArg c ha
      simp only [map_sum, map_smul, map_zero, smul_eq_mul] at h
      simpa only [c, LinearMap.coe_mk, AddHom.coe_mk] using h
    have hsingle :
        ∑ j : Fin (dim k), a j * coeff R n (G (R := R) k j.val j.isLt) =
          a ⟨n, hn⟩ * coeff R n (G (R := R) k n hn) := by
      apply Finset.sum_eq_single (⟨n, hn⟩ : Fin (dim k))
      · intro j _ hj
        by_cases hnj : n < j.val
        · rw [coeff_lt_order_G k j.val j.isLt hnj, mul_zero]
        · have hjn : j.val < n := by
            have hne : j.val ≠ n := fun h => hj (Fin.ext h)
            omega
          rw [ih j.val hjn j.isLt, zero_mul]
      · intro h
        exact (h (Finset.mem_univ _)).elim
    rw [hsingle, coeff_order_G k n hn, mul_one] at hcoeff
    exact hcoeff


/-- Compute coordinates in the `G` basis recursively from the initial Fourier coefficients. -/
noncomputable def Gcoeffs {R} [CommRing R] [Algebra R ℂ] [FaithfulSMul R ℂ] {k}
    (f : ModularFormOver R 𝒮ℒ k) : (n : ℕ) → n < dim k → R
  | 0, _ => coeff R 0 f
  | n + 1, nlt => coeff R (n + 1) f - ∑ i : Fin (n + 1),
    let hi := (i.isLt).trans nlt
    Gcoeffs f i.val hi * coeff R (n + 1) (G (R := R) k i.val hi)

/-- A level-one form is determined by its coefficients below `dim k`. -/
theorem _root_.ModularFormOver.sturm_bound {R} [CommRing R] [Algebra R ℂ] [FaithfulSMul R ℂ]
  {k} {f g : ModularFormOver R 𝒮ℒ k}
    (h : ∀ n < dim k, coeff R n f = coeff R n g) : f = g := by
  have hfg : f.toModularForm - g.toModularForm = 0 := by
    apply better_sturm_bound_levelOne
    apply PowerSeries.nat_le_order
    intro n hn
    rw [← qExp_SL2Z (f.toModularForm - g.toModularForm)]
    change (qExp (f - g)).coeff n = 0
    rw [← map_coeff_eq_qExp R R n (f - g), coeff_sub, h n hn, sub_self, map_zero]
  exact ext₂ fun z => DFunLike.congr_fun (sub_eq_zero.mp hfg) z

/-- The recursively computed coefficients reconstruct the form in the family `G`. -/
theorem Gcoeffs_smul_G {R} [CommRing R] [Algebra R ℂ] [FaithfulSMul R ℂ]
  {k} (f : ModularFormOver R 𝒮ℒ k) :
    ∑ i : Fin (dim k), Gcoeffs f i.val i.isLt • G (R := R) k i.val i.isLt = f := by
  classical
  apply sturm_bound
  intro n hn
  let c : ModularFormOver R 𝒮ℒ k →ₗ[R] R :=
    { toFun := coeff R n
      map_add' := coeff_add R R n
      map_smul' := coeff_smul R R n }
  change c (∑ i : Fin (dim k), Gcoeffs f i.val i.isLt • G (R := R) k i.val i.isLt) = c f
  rw [map_sum]
  simp only [map_smul, smul_eq_mul]
  change (∑ i : Fin (dim k), Gcoeffs f i.val i.isLt *
    coeff R n (G (R := R) k i.val i.isLt)) = coeff R n f
  calc
    _ = ∑ i : Fin (dim k) with i.val ≤ n,
        Gcoeffs f i.val i.isLt * coeff R n (G (R := R) k i.val i.isLt) := by
      symm
      apply Finset.sum_subset (Finset.filter_subset _ _)
      intro i _ hi
      have hni : n < i.val := by simpa using hi
      rw [coeff_lt_order_G k i.val i.isLt hni, mul_zero]
    _ = ∑ i : Fin (n + 1),
        Gcoeffs f i.val (i.isLt.trans_le (Nat.succ_le_of_lt hn)) *
          coeff R n (G (R := R) k i.val (i.isLt.trans_le (Nat.succ_le_of_lt hn))) := by
      apply Finset.sum_bij (fun i hi =>
        (⟨i.val, Nat.lt_succ_of_le (Finset.mem_filter.mp hi).2⟩ : Fin (n + 1)))
      · intro i hi
        exact Finset.mem_univ _
      · intro i hi j hj hij
        exact Fin.ext (congrArg (fun i : Fin (n + 1) => i.val) hij)
      · intro i hi
        refine ⟨⟨i.val, i.isLt.trans_le (Nat.succ_le_of_lt hn)⟩, ?_, rfl⟩
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact Nat.le_of_lt_succ i.isLt
      · intro i hi
        rfl
    _ = coeff R n f := by
      cases n with
      | zero => simp [Gcoeffs, coeff_order_G]
      | succ n =>
        rw [Fin.sum_univ_castSucc]
        simp only [Fin.val_castSucc, Fin.val_last, coeff_order_G, mul_one]
        rw [Gcoeffs]
        ring


/-- The `G` monomials span all level-one modular forms of weight `k` over the coefficient ring. -/
theorem G_span {R} [CommRing R] [Algebra R ℂ] (k : ℤ) :
    ⊤ ≤ Submodule.span R {G (R := R) k n.val n.isLt | n : Fin (dim k)} := by
  classical
  rintro f -
  -- Apply reconstruction over the image of `R` in `ℂ`, where the action is faithful.
  let S : Subring ℂ := (algebraMap R ℂ).range
  have hf : isOver S f := by
    rw [isOver_iff]
    intro n
    exact ⟨⟨_, (isOver_iff R f).mp f.isOver' n⟩, rfl⟩
  let g : ModularFormOver S 𝒮ℒ k := {f.toModularForm with isOver' := hf}
  choose a ha using fun i : Fin (dim k) => (Gcoeffs g i.val i.isLt).property
  have hsum : ∑ i : Fin (dim k), a i • G (R := R) k i.val i.isLt = f := by
    apply ext₂
    intro z
    let ev : ModularFormOver S 𝒮ℒ k →+ ℂ :=
      { toFun := fun h => h z
        map_zero' := rfl
        map_add' := fun _ _ => rfl }
    have h := congrArg ev (Gcoeffs_smul_G g)
    rw [map_sum] at h
    change (∑ i : Fin (dim k),
      (Gcoeffs g i.val i.isLt).val * (G (R := S) k i.val i.isLt) z) = f z at h
    rw [← h]
    change (∑ i : Fin (dim k), a i • G (R := R) k i.val i.isLt) z = _
    let evR : ModularFormOver R 𝒮ℒ k →+ ℂ :=
      { toFun := fun h => h z
        map_zero' := rfl
        map_add' := fun _ _ => rfl }
    change evR (∑ i : Fin (dim k), a i • G (R := R) k i.val i.isLt) = _
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro i _
    change (a i • G (R := R) k i.val i.isLt) z = _
    rw [smul_apply, Algebra.smul_def]
    rw [ha i]
    rfl
  rw [← hsum]
  exact Submodule.sum_mem _ fun i _ =>
    Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)


/-- The basis of weight-`k` forms given by `G` monomials with leading coefficient one and
increasing vanishing order. -/
noncomputable def GBasis (R) [CommRing R] [Algebra R ℂ] [FaithfulSMul R ℂ] (k : ℤ) :
    Module.Basis (Fin (dim k)) R (ModularFormOver R 𝒮ℒ k) :=
  Module.Basis.mk (G_LI k) (G_span k)


/-- The element indexed by `c` in `GBasis` is the corresponding `G` monomial. -/
@[simp] theorem GBasis_apply {R} [CommRing R] [Algebra R ℂ] [FaithfulSMul R ℂ]
    (k : ℤ) (c : Fin (dim k)) : GBasis R k c = G k c.1 c.2 :=
  Module.Basis.mk_apply ..


end GBasis

end Basis

open ModularFormOver.Basis


variable {R : Type} [CommRing R] [Algebra R ℂ] [FaithfulSMul R ℂ]

/-- The rank of level-one forms over a ring with the strong rank condition is `dim k`. -/
theorem dimension_eq_dim [StrongRankCondition R] :
    Module.rank R (ModularFormOver R 𝒮ℒ k) = dim k := by
  rw [rank_eq_card_basis <| GBasis R k, Fintype.card_fin]

/-- The finrank of level-one forms over a ring with the strong rank condition is `dim k`. -/
theorem finrank_eq_dim [StrongRankCondition R] :
    Module.finrank R (ModularFormOver R 𝒮ℒ k) = dim k := by
  rw [Module.finrank_eq_card_basis <| GBasis R k, Fintype.card_fin]


/-- Forms of order at least `dim k - 1` are equal if their Fourier coefficients in that
degree agree. -/
theorem eq_of_eq_order_max {f g : ModularFormOver R 𝒮ℒ k}
    (hao : (dim k - 1 : ℕ∞) ≤ (qExp f).order)
    (hbo : (dim k - 1 : ℕ∞) ≤ (qExp g).order)
    (heq : coeff R (dim k - 1) f = coeff R (dim k - 1) g) : f = g := by
  apply sturm_bound
  intro n hn
  by_cases h : n < dim k - 1
  · have hlt : (n : ℕ∞) < (qExp f).order := by
      exact lt_of_lt_of_le (by exact_mod_cast h) hao
    have hlt' : (n : ℕ∞) < (qExp g).order := by
      exact lt_of_lt_of_le (by exact_mod_cast h) hbo
    have hf0 : coeff R n f = 0 := by
      apply FaithfulSMul.algebraMap_injective R ℂ
      rw [map_coeff_eq_qExp, map_zero]
      exact PowerSeries.coeff_of_lt_order _ hlt
    have hg0 : coeff R n g = 0 := by
      apply FaithfulSMul.algebraMap_injective R ℂ
      rw [map_coeff_eq_qExp, map_zero]
      exact PowerSeries.coeff_of_lt_order _ hlt'
    rw [hf0, hg0]
  · have hn' : n = dim k - 1 := by omega
    simpa [hn'] using heq

/-- A form with vanishing order at least `dim k - 1` is a scalar multiple of the last `G` basis
element. -/
theorem eq_G_of_order_max (f : ModularFormOver R 𝒮ℒ k)
    (hk : 0 < dim k) (hord : (dim k - 1 : ℕ∞) ≤ (qExp f).order) :
    f = coeff R (dim k - 1) f • G (k := k) (dim k - 1) (by omega) := by
  apply sturm_bound
  intro n hn
  by_cases h : n < dim k - 1
  · have hlt : (n : ℕ∞) < (qExp f).order := by
      exact lt_of_lt_of_le (by exact_mod_cast h) hord
    have hf0 : coeff R n f = 0 := by
      apply FaithfulSMul.algebraMap_injective R ℂ
      rw [map_coeff_eq_qExp, map_zero]
      exact PowerSeries.coeff_of_lt_order _ hlt
    rw [coeff_smul, hf0, coeff_lt_order_G k (dim k - 1) (by omega) h]
    simp
  · have hn' : n = dim k - 1 := by omega
    subst n
    rw [coeff_smul, coeff_order_G, smul_eq_mul, mul_one]

section PBasis


namespace Basis
/-! The entries here are the exponents of `E4` and `E6`. -/

/-- Exponent pairs for the monomial basis `E4^a * E6^b` of weight `k`.
The list is ordered by decreasing exponent of `E6`. -/
def PpowersNat : ℕ → List (Fin 2 → ℕ)
  | 0 => [![0,0]]
  | 4 => [![1,0]]
  | 6 => [![0,1]]
  | 8 => [![2,0]]
  | 10 => [![1,1]]
  | 14 => [![2,1]]
  | n + 12 => match PpowersNat n with
    | [] => []
    | p :: ps => ![p 0, p 1 + 2] :: (p :: ps).map (fun q => ![q 0 + 3, q 1])
  | _ => []

/-- The exponent pairs for the weight-`k` monomials in `E₄` and `E₆`. -/
def Ppowers : ℤ → List (Fin 2 → ℕ)
  | Int.ofNat n => PpowersNat n
  | Int.negSucc _ => []

/-- The natural-weight exponent list has one entry per basis element. -/
@[simp] theorem PpowersNat_length (k : ℕ) : (PpowersNat k).length = dimNat k := by
  fun_induction PpowersNat k with
  | case7 n _ hps ih =>
    simp only [hps, List.length_nil] at ih
    simp [dimNat, ← ih]
  | case8 n _ p ps hps ih =>
    simp only [hps, List.length_cons] at ih
    simp [dimNat, ← ih]
  | _ => simp_all [dimNat]

/-- Every exponent pair in `PpowersNat k` has total weight `k`. -/
theorem PpowersNat_weight (k : ℕ) :
    ∀ p ∈ PpowersNat k, p 0 * 4 + p 1 * 6 = k := by
  fun_induction PpowersNat k with
  | case8 n _ p ps hps ih =>
    intro q hq
    rcases List.mem_cons.mp hq with hq | hq
    · subst q
      have hw := ih p (by simp [hps])
      change p 0 * 4 + (p 1 + 2) * 6 = n + 12
      omega
    · obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hq
      have hw := ih r (by rwa [hps])
      change (r 0 + 3) * 4 + r 1 * 6 = n + 12
      omega
  | _ => simp_all

/-- Every exponent pair in `Ppowers k` has total weight `k`. -/
theorem Ppowers_weight {k : ℤ} {p : Fin 2 → ℕ} (hp : p ∈ Ppowers k) :
    p 0 * 4 + p 1 * 6 = k := by
  cases k with
  | ofNat n =>
    change p 0 * 4 + p 1 * 6 = (n : ℤ)
    exact_mod_cast PpowersNat_weight n p hp
  | negSucc n => simp [Ppowers] at hp

/-- The exponent list has one entry per basis element. -/
@[simp] theorem Ppowers_length (k : ℤ) : (Ppowers k).length = dim k := by
  cases k with
  | ofNat n => exact PpowersNat_length n
  | negSucc n => rfl

private theorem PpowersNat_getElem_properties (k : ℕ) :
    ∀ n (hn : n < (PpowersNat k).length),
      (PpowersNat k)[n] 1 = k % 4 / 2 + 2 * ((PpowersNat k).length - 1 - n) := by
  fun_induction PpowersNat k with
  | case8 k _ p ps hps ih =>
    rw [hps] at ih
    have hmod : (k + 12) % 4 / 2 = k % 4 / 2 := by omega
    intro n hn
    cases n with
    | zero =>
      have hp := ih 0 (by simp)
      simp only [List.length_cons, List.getElem_cons_zero, Nat.sub_zero,
        Nat.add_sub_cancel] at hp
      simp only [List.length_cons, List.length_map, List.getElem_cons_zero]
      change p 1 + 2 = (k + 12) % 4 / 2 + 2 * (ps.length + 1 + 1 - 1 - 0)
      omega
    | succ n =>
      have hn' : n < (p :: ps).length := by simpa using hn
      have hp := ih n hn'
      simp only [List.length_cons, List.length_map, List.getElem_cons_succ,
        List.getElem_map]
      change (p :: ps)[n] 1 =
        (k + 12) % 4 / 2 + 2 * ((p :: ps).length + 1 - 1 - (n + 1))
      omega
  | _ => simp_all

/-- The exponent pair at any index below `dim k` has total weight `k`. -/
theorem Ppowers_getElem_weight (k : ℤ) (n : ℕ) (hn : n < dim k) :
    let p := (Ppowers k)[n]'(by rwa [Ppowers_length])
    p 0 * 4 + p 1 * 6 = k := by
  exact Ppowers_weight (List.getElem_mem _)

/-- The exponents of `E4` and `E6` at index `n`, without a list lookup. -/
theorem Ppowers_getElem_eq (k : ℤ) (n : ℕ) (hn : n < dim k) :
    (Ppowers k)[n]'(by rwa [Ppowers_length]) =
      ![(k.toNat - 6 * (k.toNat % 4 / 2 + 2 * (dim k - 1 - n))) / 4,
        k.toNat % 4 / 2 + 2 * (dim k - 1 - n)] := by
  cases k with
  | ofNat k =>
    change n < dimNat k at hn
    have hn' : n < (PpowersNat k).length := by rwa [PpowersNat_length]
    have hp := PpowersNat_getElem_properties k n hn'
    simp only [PpowersNat_length] at hp
    have hw := PpowersNat_weight k _ (List.getElem_mem hn')
    change (PpowersNat k)[n]'hn' =
      ![(k - 6 * (k % 4 / 2 + 2 * (dimNat k - 1 - n))) / 4,
        k % 4 / 2 + 2 * (dimNat k - 1 - n)]
    ext i
    fin_cases i <;> dsimp at * <;> omega
  | negSucc k => simp [dim] at hn

/-- The weight-`k` monomial in `E₄` and `E₆` specified by the `n`-th exponent pair. -/
noncomputable def P {R} [CommRing R] [Algebra R ℂ]
    (k : ℤ) (n : ℕ) (hn : n < dim k := by decide) : ModularFormOver R 𝒮ℒ k :=
  let p := (Ppowers k)[n]'(by rwa [Ppowers_length])
  ((E₄.pow (p 0)).mul (E₆.pow (p 1))).cast (Ppowers_getElem_weight k n hn)

/-- An explicit product formula for the basis element. -/
theorem P_eq {R} [CommRing R] [Algebra R ℂ]
    (k : ℤ) (n : ℕ) (hn : n < dim k) :
    P (R := R) k n hn =
      ((E₄.pow ((k.toNat - 6 * (k.toNat % 4 / 2 + 2 * (dim k - 1 - n))) / 4)).mul
        (E₆.pow (k.toNat % 4 / 2 + 2 * (dim k - 1 - n)))).cast (b := k) (by
          have hw := Ppowers_getElem_weight k n hn
          dsimp only at hw
          rw [Ppowers_getElem_eq k n hn] at hw
          exact hw) := by
  apply ext₂
  intro z
  change ((E₄.pow _).mul (E₆.pow _)) z = ((E₄.pow _).mul (E₆.pow _)) z
  simp only [mul_apply, pow_apply]
  rw [Ppowers_getElem_eq k n hn]
  rfl

/-- The Fourier expansion of `P k n` is the corresponding product of the expansions of `E₄` and
`E₆`. -/
theorem qExp_P {R} [CommRing R] [Algebra R ℂ]
    (k : ℤ) (n : ℕ) (hn : n < dim k) :
    qExp (P (R := R) k n hn) =
      qExp E₄ ^ ((k.toNat - 6 * (k.toNat % 4 / 2 + 2 * (dim k - 1 - n))) / 4) *
        qExp E₆ ^ (k.toNat % 4 / 2 + 2 * (dim k - 1 - n)) := by
  rw [P_eq k n hn]
  change qExp ((E₄.toModularForm.pow _).mul (E₆.toModularForm.pow _)) = _
  rw [qExp_mul, qExp_pow, qExp_pow]
  rfl

open Lean Meta in
/-- Unfold `P k n hn` when `k` and `n` are numerals, computing the exponent pair
and removing the weight cast and identity bundling coercions by definitional equality.
Runs automatically with `simp` and `dsimp`, or explicitly with `simp only [reduceP]`.
Symbolic weights and indices are left unchanged. -/
dsimproc reduceP (@P _ _ _ _ _ _) := fun e => do
  let_expr P _ _ _ k n _ := e | return .continue
  unless (← getIntValue? k).isSome && (← getNatValue? n).isSome do
    return .continue
  let some unfolded ← unfoldDefinition? e (ignoreTransparency := true) | return .continue
  let .letE _ _ powers body _ := unfolded | return .continue
  -- Evaluate the exponent lookups while preserving the modular-form operations.
  let body ← transform (body.instantiate1 powers) (pre := fun t => do
    if t.isApp && t.appFn! == powers then
      return .done (← withTransparency .all <| reduce t)
    return .continue)
  let isWrapper := fun (t : Expr) =>
    t.isAppOf ``ModularFormOver.cast || t.isAppOf `cast ||
      t.isAppOf ``ModularFormOverClass.modularFormOver
  let mut result := body
  while true do
    let candidate ← if isWrapper result then pure result else whnfR result
    unless isWrapper candidate do break
    let value := candidate.appArg!
    let canErase ← withTransparency .default do
      return (← isDefEq (← inferType value) (← inferType e)) &&
        (← isDefEq result value)
    unless canErase do break
    result := value
  return .continue result


/-- Every monomial in the family `P` has constant q-expansion coefficient one. -/
@[simp] theorem qExp_P_coeff_zero {R} [CommRing R] [Algebra R ℂ]
    (k : ℤ) (n : ℕ) (hn : n < dim k) :
    (qExp (P (R := R) k n hn)).coeff 0 = 1 := by
  rw [qExp_P, coeff_zero_eq_constantCoeff, map_mul, map_pow, map_pow]
  simp [← coeff_zero_eq_constantCoeff, E₄_qExp_coeff, E₆_qExp_coeff]

/-- The leading coefficient of `P k n` is its constant coefficient, which is one. -/
@[simp] theorem coeff_zero_P {R} [CommRing R] [Algebra R ℂ] [FaithfulSMul R ℂ]
    (k : ℤ) (n : ℕ) (hn : n < dim k) : coeff R 0 (P (R := R) k n hn) = 1 := by
  rw [coeff_eq_iff, map_one, qExp_P_coeff_zero]

/-- Every `P` monomial has Fourier expansion of order zero. -/
@[simp] theorem order_P {R} [CommRing R] [Algebra R ℂ]
    (k : ℤ) (n : ℕ) (hn : n < dim k) : order (qExp (P (R := R) k n hn)) = 0 := by
  apply PowerSeries.order_eq_nat.mpr
  exact ⟨by simp, by simp⟩

/-- The dimension in the weight of an Eisenstein monomial. -/
theorem dim_monomial (a b : ℕ) :
    dim (a * 4 + b * 6 : ℕ) = a / 3 + b / 2 + 1 := by
  rw [dim_eq_dim', dim']
  simp only [Int.natCast_nonneg, Int.even_iff, Int.ModEq, Int.toNat_natCast, ite_true]
  split_ifs <;> omega

private theorem monomial_mem_span_P {R} [CommRing R] [Algebra R ℂ]
    (k : ℤ) (a b : ℕ) (hw : (a : ℤ) * 4 + b * 6 = k) :
    (((E₄.pow a).mul (E₆.pow b)).cast hw : ModularFormOver R 𝒮ℒ k) ∈
      Submodule.span R {P (R := R) k n.val n.isLt | n : Fin (dim k)} := by
  have hk : k = (a * 4 + b * 6 : ℕ) := by omega
  have hd : dim k = a / 3 + b / 2 + 1 := by rw [hk]; exact dim_monomial a b
  have hn : a / 3 < dim k := by omega
  have hP : P (R := R) k (a / 3) hn =
      (((E₄.pow a).mul (E₆.pow b)).cast hw : ModularFormOver R 𝒮ℒ k) := by
    have hb : k.toNat % 4 / 2 + 2 * (dim k - 1 - a / 3) = b := by
      rw [hd, hk, Int.toNat_natCast]
      omega
    have ha : (k.toNat - 6 * b) / 4 = a := by
      rw [hk, Int.toNat_natCast]
      omega
    apply ext₂
    intro z
    simp only [ModularFormOver.cast_apply]
    change ((E₄.pow _).mul (E₆.pow _)) z = ((E₄.pow a).mul (E₆.pow b)) z
    simp only [mul_apply, pow_apply]
    rw [Ppowers_getElem_eq k (a / 3) hn]
    change E₄ z ^ ((k.toNat - 6 * (k.toNat % 4 / 2 + 2 * (dim k - 1 - a / 3))) / 4) *
      E₆ z ^ (k.toNat % 4 / 2 + 2 * (dim k - 1 - a / 3)) = E₄ z ^ a * E₆ z ^ b
    rw [hb, ha]
  rw [← hP]
  exact Submodule.subset_span ⟨⟨a / 3, hn⟩, rfl⟩

private theorem delta_monomial_mem_span_P {R} [CommRing R] [Algebra R ℂ]
    [Invertible (6 : R)] (k : ℤ) (c a b : ℕ)
    (hw : (a : ℤ) * 4 + b * 6 + c * 12 = k) :
    ((((E₄.pow a).mul (E₆.pow b)).mul ((Δ).pow c)).cast hw : ModularFormOver R 𝒮ℒ k) ∈
      Submodule.span R {P (R := R) k n.val n.isLt | n : Fin (dim k)} := by
  induction c generalizing a b with
  | zero =>
    have hw' : (a : ℤ) * 4 + b * 6 = k := by simpa using hw
    have heq :
        ((((E₄.pow a).mul (E₆.pow b)).mul ((Δ).pow 0)).cast hw :
          ModularFormOver R 𝒮ℒ k) = ((E₄.pow a).mul (E₆.pow b)).cast hw' := by
      apply ext₂
      intro z
      have hcoe {j : ℤ} (f : ModularFormOver ℤ 𝒮ℒ j) :
          (↑f : ModularFormOver R 𝒮ℒ j) z = f z := rfl
      simp only [hcoe, cast_apply, mul_apply, pow_apply, pow_zero, mul_one]
    rw [heq]
    exact monomial_mem_span_P k a b hw'
  | succ c ih =>
    have hw₄ : ((a + 3 : ℕ) : ℤ) * 4 + b * 6 + c * 12 = k := by omega
    have hw₆ : (a : ℤ) * 4 + ((b + 2 : ℕ) : ℤ) * 6 + c * 12 = k := by omega
    let f₄ : ModularFormOver R 𝒮ℒ k :=
      (((E₄.pow (a + 3)).mul (E₆.pow b)).mul ((Δ).pow c)).cast hw₄
    let f₆ : ModularFormOver R 𝒮ℒ k :=
      (((E₄.pow a).mul (E₆.pow (b + 2))).mul ((Δ).pow c)).cast hw₆
    have hf₄ := ih (a + 3) b hw₄
    have hf₆ := ih a (b + 2) hw₆
    have heq :
        ((((E₄.pow a).mul (E₆.pow b)).mul ((Δ).pow (c + 1))).cast hw :
          ModularFormOver R 𝒮ℒ k) = ⅟ (1728 : R) • (f₄ - f₆) := by
      apply ext₂
      intro z
      have hcoe {j : ℤ} (f : ModularFormOver ℤ 𝒮ℒ j) :
          (↑f : ModularFormOver R 𝒮ℒ j) z = f z := rfl
      have hΔ := congrArg (fun f : ModularFormOver R 𝒮ℒ 12 => f z)
        (discriminant_eq_E₄E₆ (R := R))
      simp only [tower_apply, smul_apply, sub_apply, cast_apply, pow_apply,
        Algebra.smul_def] at hΔ
      change Δ z = algebraMap R ℂ (⅟ (1728 : R)) * (E₄ z ^ 3 - E₆ z ^ 2) at hΔ
      dsimp only [f₄, f₆]
      simp only [hcoe, smul_apply, sub_apply, cast_apply, mul_apply, pow_apply,
        Algebra.smul_def]
      change E₄ z ^ a * E₆ z ^ b * Δ z ^ (c + 1) =
        algebraMap R ℂ (⅟ (1728 : R)) *
          (E₄ z ^ (a + 3) * E₆ z ^ b * Δ z ^ c -
            E₄ z ^ a * E₆ z ^ (b + 2) * Δ z ^ c)
      rw [pow_succ, hΔ]
      simp only [pow_add]
      ring
    rw [heq]
    exact Submodule.smul_mem _ _ (Submodule.sub_mem _ hf₄ hf₆)

/-- The monomials in `P` span when six is invertible in the coefficient ring. -/
theorem P_span {R} [CommRing R] [Algebra R ℂ] [Invertible (6 : R)] (k : ℤ) :
    ⊤ ≤ Submodule.span R {P (R := R) k n.val n.isLt | n : Fin (dim k)} := by
  refine (G_span (R := R) k).trans (Submodule.span_le.mpr ?_)
  rintro _ ⟨i, rfl⟩
  dsimp only [G]
  apply delta_monomial_mem_span_P

/-- The spanning family `P` is linearly independent, since it has `dim k` elements. -/
theorem P_LI {R} [CommRing R] [Algebra R ℂ] [FaithfulSMul R ℂ]
    [Invertible (6 : R)] (k : ℤ) :
    LinearIndependent R (fun n : Fin (dim k) => P (R := R) k n.val n.isLt) := by
  nontriviality R
  apply linearIndependent_of_top_le_span_of_card_eq_finrank (P_span (R := R) k)
  simpa only [Fintype.card_fin] using (finrank_eq_dim (R := R) (k := k)).symm


/-- The basis of weight-`k` forms consisting of monomials in `E₄` and `E₆`, available when `6` is
invertible. -/
noncomputable def PBasis (R) [CommRing R] [Algebra R ℂ]
  [FaithfulSMul R ℂ] [Invertible (6 : R)] (k : ℤ) :
    Module.Basis (Fin (dim k)) R (ModularFormOver R 𝒮ℒ k) :=
  Module.Basis.mk (P_LI k) (P_span k)


/-- The element indexed by `c` in `PBasis` is the corresponding `P` monomial. -/
@[simp] theorem PBasis_apply {R} [CommRing R] [Algebra R ℂ]
  [FaithfulSMul R ℂ] [Invertible (6 : R)] (k : ℤ) (c : Fin (dim k)) :
    PBasis R k c = P k c.1 c.2 :=
  Module.Basis.mk_apply ..


end Basis
end PBasis

end ModularFormOver
