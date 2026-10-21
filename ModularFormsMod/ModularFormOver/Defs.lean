/-
Copyright (c) 2026 Carter Hastings. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carter Hastings
-/

import Mathlib.NumberTheory.ModularForms.QExpansion

/-!
# Modular forms with Fourier coefficients in a chosen ring

`ModularForm.isOver R f` asserts that the Fourier expansion of `f` comes from
`R⟦X⟧` under the algebra map to `ℂ`. `ModularFormOver R Γ k` bundles this
condition with a modular form, and `ModularFormOverClass` extends it to other
types of modular forms. The file supplies arithmetic operations, changes of
weight, and the graded commutative ring structure.
-/

open UpperHalfPlane PowerSeries MatrixGroups ModularForm CongruenceSubgroup


instance UpperHalfPlane.FunLike : FunLike (ℍ → ℂ) ℍ ℂ where
  coe := id
  coe_injective _ _ := id

instance : IsZeroApply (ℍ → ℂ) ℍ ℂ where
instance : IsOneApply (ℍ → ℂ) ℍ ℂ where
instance : IsAddApply (ℍ → ℂ) ℍ ℂ where
instance : IsNegApply (ℍ → ℂ) ℍ ℂ where
instance : IsSubApply (ℍ → ℂ) ℍ ℂ where
instance : IsMulApply (ℍ → ℂ) ℍ ℂ where
instance {α} [SMul α ℂ] : IsSMulApply α (ℍ → ℂ) ℍ ℂ where


/-- The subgroup `Γ` is contained in the image of SL(2, ℤ) in GL(2, ℝ). -/
class Subgroup.le_SL2Z (Γ : Subgroup (GL (Fin 2) ℝ)) where
  le : Γ ≤ 𝒮ℒ := by rfl

instance (Γ : Subgroup (GL (Fin 2) ℝ)) [h : Γ.le_SL2Z] : Γ.HasDetOne where
  det_eq {g} hg := by
    obtain ⟨g, rfl⟩ := h.le hg
    exact Matrix.SpecialLinearGroup.det_mapGL g

instance : Subgroup.le_SL2Z 𝒮ℒ where
instance (Γ : Subgroup SL(2, ℤ)) : Γ.le_SL2Z where
  le := by rintro g ⟨y, hy, hy'⟩; use y

instance ModularForm.instIsOneApply {Γ : Subgroup (GL (Fin 2) ℝ)} [Γ.HasDetPlusMinusOne] :
  IsOneApply (ModularForm Γ 0) ℍ ℂ where

open Function in
/-- The Fourier expansion of a constant function is the corresponding constant power series. -/
@[simp] theorem qExpansion_const (h) (c : ℂ) :
    qExpansion h (Function.const ℍ c) = C c := by
  rw [show Function.const ℍ c = fun _ => c by rfl]
  ext m
  have h1 : cuspFunction h (fun _ => c) = fun _ => c := by
    ext q
    rcases eq_or_ne q 0 with rfl | hq
    · simp only [cuspFunction, Periodic.cuspFunction,
        show (fun x ↦ c) ∘ ↑ofComplex = fun _ => c by rfl, update_self]
      unfold Periodic.invQParam
      conv => lhs; rhs; intro r; simp
      rw [tendsto_const_nhds.limUnder_eq]
    · simp [cuspFunction, show (fun x ↦ c) ∘ ↑ofComplex = fun _ => c by rfl,
        Periodic.cuspFunction_eq_of_nonzero _ _ hq]
  have h2 : iteratedDeriv m (fun _ => c : ℂ → ℂ) 0 = if m = 0 then c else 0 :=
    iteratedDeriv_const
  simp [qExpansion_coeff,  h1, h2, coeff_C]
  split_ifs with h
  · simp [h]
  · rfl

namespace ModularForm


variable {k j : ℤ}


/-- The Fourier expansion at infinity, with parameter determined by the strict cusp width of `Γ`. -/
noncomputable abbrev qExp {Γ'} {F : Type*} [FunLike F ℍ ℂ] [ModularFormClass F Γ' k]
    (f : F) (Γ : Subgroup (GL (Fin 2) ℝ) := Γ') : ℂ⟦X⟧ :=
  qExpansion Γ.strictWidthInfty f


variable {Γ : Subgroup (GL (Fin 2) ℝ)} {F : Type*}
  [FunLike F ℍ ℂ] [ModularFormClass F Γ k]

theorem qExp_def (f : F) : qExp f = qExpansion Γ.strictWidthInfty f := rfl

@[simp] theorem qExp_add [Γ.IsArithmetic] [Add F] [IsAddApply F ℍ ℂ] (f g : F) :
    qExp (f + g) = qExp f + qExp g := by
  rw [qExp, FunLike.coe_add]
  exact ModularForm.qExpansion_add Γ.strictWidthInfty_pos
    Γ.strictWidthInfty_mem_strictPeriods f g

@[simp] theorem qExp_neg [Γ.IsArithmetic] [Neg F] [IsNegApply F ℍ ℂ] (f : F) :
    qExp (-f) = -qExp f := by
  rw [qExp, FunLike.coe_neg]
  exact ModularForm.qExpansion_neg Γ.strictWidthInfty_pos
    Γ.strictWidthInfty_mem_strictPeriods f

@[simp] theorem qExp_sub [Γ.IsArithmetic] [Sub F] [IsSubApply F ℍ ℂ] (f g : F) :
    qExp (f - g) = qExp f - qExp g := by
  rw [qExp, FunLike.coe_sub]
  exact ModularForm.qExpansion_sub Γ.strictWidthInfty_pos
    Γ.strictWidthInfty_mem_strictPeriods f g

@[simp] theorem qExp_smul [Γ.IsArithmetic] {α} [SMul α F] [CommSemiring α]
  [Algebra α ℂ] [IsSMulApply α F ℍ ℂ] (c : α) (f : F) :
    qExp (c • f) = c • qExp f := by
  unfold qExp
  simp only [FunLike.coe_smul, ← algebraMap_smul ℂ c]
  exact ModularForm.qExpansion_smul Γ.strictWidthInfty_pos
    Γ.strictWidthInfty_mem_strictPeriods _ f

/-- Modular forms for an arithmetic group are determined by their Fourier expansions at infinity. -/
theorem qExp_inj [Γ.IsArithmetic] {f g : F} (h : qExp f = qExp g) : f = g := by
  apply DFunLike.coe_injective
  change ⇑(f : ModularForm Γ k) = ⇑(g : ModularForm Γ k)
  congr 1
  rwa [← qExpansion_inj Γ.strictWidthInfty_pos
    Γ.strictWidthInfty_mem_strictPeriods]


@[simp] theorem qExp_mul [Γ.IsArithmetic] [Γ.HasDetPlusMinusOne] (f : ModularForm Γ k)
    (g : ModularForm Γ j) : qExp (f.mul g) = qExp f * qExp g :=
  ModularForm.qExpansion_mul Γ.strictWidthInfty_pos
    Γ.strictWidthInfty_mem_strictPeriods f g

@[simp] theorem qExp_pow [Γ.IsArithmetic] (f : ModularForm Γ k) (m) :
    qExp (f.pow m) = (qExp f) ^ m :=
  ModularForm.qExpansion_pow Γ.strictWidthInfty_pos
    Γ.strictWidthInfty_mem_strictPeriods f m

@[simp] theorem qExp_zero [Zero F] [IsZeroApply F ℍ ℂ] : qExp (0 : F) = 0 := by
  rw [qExp, FunLike.coe_zero, qExpansion_zero]

@[simp] theorem qExp_one [Γ.HasDetPlusMinusOne] [One F] [IsOneApply F ℍ ℂ] :
    qExp (1 : F) = 1 := by
  rw [qExp, show ⇑(1 : F) = ⇑(1 : ModularForm Γ 0) by simp, ModularForm.qExpansion_one]

open Function in
@[simp] theorem qExp_const [Γ.HasDetOne] (c : ℂ) :
    qExp (const c : ModularForm Γ 0) = C c := by
  rw [qExp, coe_const, qExpansion_const]

@[simp] theorem qExp_constℝ [Γ.HasDetPlusMinusOne] (r : ℝ) :
    qExp (constℝ r : ModularForm Γ 0) = C (r : ℂ) := by
  rw [qExp, coe_constℝ, qExpansion_const]


@[simp] theorem qExp_natCast [Γ.HasDetPlusMinusOne] (n : ℕ) : qExp (n : ModularForm Γ 0) = n := by
  rw [show (n : ModularForm Γ 0) = constℝ n by rfl, qExp_constℝ]
  exact map_natCast _ _

@[simp] theorem qExp_intCast [Γ.HasDetPlusMinusOne] (z : ℤ) : qExp (z : ModularForm Γ 0) = z := by
  rw [show (z : ModularForm Γ 0) = constℝ z by rfl, qExp_constℝ]
  exact map_intCast _ _


end ModularForm

/-- The image of the algebra map `R` → `S`, viewed as a subring of `S`. -/
def rangeMap (R S : Type*) [CommRing R] [CommRing S]
  [Algebra R S] : Subring S := RingHom.range (algebraMap R S)

scoped [ModularFormOver] notation R:max " // " S:max => rangeMap R S

open ModularFormOver

@[simp] theorem Map_mem_rangeMap {R S : Type*} [CommRing R] [CommRing S]
  [Algebra R S] (r : R) : algebraMap R S r ∈ R // S := ⟨r, rfl⟩


theorem rangeMapPowerSeries (R S : Type*) [CommRing R] [CommRing S] [Algebra R S] :
  R⟦X⟧ // S⟦X⟧ = (map (algebraMap R S)).range := rfl

theorem MapPowerSeries (R S : Type*) [CommRing R] [CommRing S] [Algebra R S] :
    algebraMap R⟦X⟧ S⟦X⟧ = map (algebraMap R S) := rfl


/-- Taking constant coefficients of series defined over `R` gives exactly the image of `R` in
`ℂ`. -/
theorem rangeMap_map_constantCoeff (R : Type*) [CommRing R] [Algebra R ℂ] :
    (R⟦X⟧ // ℂ⟦X⟧).map constantCoeff = R // ℂ := by
  ext z
  constructor
  · intro hz
    rcases Subring.mem_map.mp hz with ⟨p, hp, hpz⟩
    change ∃ q, PowerSeries.map (algebraMap R ℂ) q = p at hp
    rcases hp with ⟨q, rfl⟩
    refine ⟨q.constantCoeff, ?_⟩
    simpa [← coeff_zero_eq_constantCoeff] using hpz
  · intro hz
    refine ⟨PowerSeries.C z, ?_, ?_⟩
    · change ∃ q, PowerSeries.map (algebraMap R ℂ) q = PowerSeries.C z
      obtain ⟨r, rfl⟩ := hz
      exact ⟨PowerSeries.C r, by simp⟩
    · simp

/-- Coefficientwise extension of scalars is injective when the algebra map is injective. -/
theorem map_algebraMap_injective {R : Type*} (S : Type*)
  [CommRing R] [CommRing S] [Algebra R S] [FaithfulSMul R S] :
    Function.Injective (map (algebraMap R S)) :=
  PowerSeries.map_injective (algebraMap R S) (FaithfulSMul.algebraMap_injective R S)


/-- Identify `R` with its image in an algebra on which it acts faithfully. -/
noncomputable def rangeMapEquiv (R S : Type*) [CommRing R] [CommRing S]
    [Algebra R S] [FaithfulSMul R S] : R ≃+* R // S :=
  RingEquiv.ofBijective (algebraMap R S).rangeRestrict ⟨
    fun x y h => by
      apply FaithfulSMul.algebraMap_injective R S
      rw [← RingHom.coe_rangeRestrict _ x,
        ← RingHom.coe_rangeRestrict _ y]; congr 1,
    RingHom.rangeRestrict_surjective _⟩


/-- Identify power series over `R` with their coefficientwise image in `S`⟦X⟧. -/
noncomputable def rangeMapPowerSeriesEquiv (R S : Type*) [CommRing R] [CommRing S]
    [Algebra R S] [FaithfulSMul R S] : R⟦X⟧ ≃+* R⟦X⟧ // S⟦X⟧ :=
  RingEquiv.ofBijective (map (algebraMap R S)).rangeRestrict ⟨
    fun f g h => by
      apply map_algebraMap_injective S
      rw [← RingHom.coe_rangeRestrict _ f,
        ← RingHom.coe_rangeRestrict _ g]; congr 1,
    RingHom.rangeRestrict_surjective _⟩


instance (R S : Type*) [CommRing R] [CommRing S]
    [Algebra R S] [FaithfulSMul R S] : FaithfulSMul R S⟦X⟧ where
  eq_of_smul_eq_smul {m n} h :=
    eq_of_smul_eq_smul (α := S) fun a => by
      simpa only [constantCoeff_smul, constantCoeff_C]
        using congrArg constantCoeff (h (C a))


namespace ModularForm

open ModularFormOver

variable {Γ : Subgroup (GL (Fin 2) ℝ)} {k j : ℤ}
  {F : Type*} [FunLike F ℍ ℂ] [hF : ModularFormClass F Γ k]


/-- The Fourier expansion of `f` is obtained from a formal power series over `R`. -/
def isOver (R : Type*) [CommRing R] [Algebra R ℂ] (f : F) : Prop :=
  qExp f ∈ R⟦X⟧ // ℂ⟦X⟧


/-- A modular form is defined over `R` exactly when each Fourier coefficient lies in the image of
`R`. -/
theorem isOver_iff (R : Type*) [CommRing R] [Algebra R ℂ] (f : F) :
    isOver R f ↔ ∀ n, (qExp f).coeff n ∈ R // ℂ := by
  simp only [isOver, RingHom.mem_range, ← rangeMap_map_constantCoeff,
    Subring.mem_map, exists_exists_eq_and, rangeMapPowerSeries]
  constructor
  · rintro ⟨a, ha⟩ n
    use C (coeff n a)
    simp [← ha]
  · rintro h
    use PowerSeries.mk fun n => constantCoeff (h n).choose
    ext n
    simp_rw [coeff_map, coeff_mk, ← coeff_zero_eq_constantCoeff,
      ← coeff_map, coeff_zero_eq_constantCoeff, (h n).choose_spec]


variable {H} [FunLike H ℍ ℂ] [ModularFormClass H Γ k] {f f' : F} {g : H}
  {R : Type*} [CommRing R] [Algebra R ℂ]

/-- Recover the Fourier expansion over `R` from its complex image and the proof that it is over
`R`. -/
protected noncomputable def isOver.fourier [FaithfulSMul R ℂ]
    (hf : isOver R f) : PowerSeries R :=
  (rangeMapPowerSeriesEquiv R ℂ).symm ⟨qExp f, hf⟩


theorem isOver.fourier_def [FaithfulSMul R ℂ] (hf : isOver R f) :
  hf.fourier = (rangeMapPowerSeriesEquiv R ℂ).symm ⟨qExp f, hf⟩ := rfl


/-- Extending the recovered coefficients to `ℂ` gives the original Fourier expansion. -/
@[simp]
protected theorem isOver.map_fourier [FaithfulSMul R ℂ] (hf : isOver R f) :
    map (algebraMap R ℂ) hf.fourier = qExp f := by
  change ((rangeMapPowerSeriesEquiv R ℂ)
    ((rangeMapPowerSeriesEquiv R ℂ).symm ⟨qExp f, hf⟩)).val = _
  simp only [RingEquiv.apply_symm_apply]


/-- Each recovered coefficient maps to the corresponding complex Fourier coefficient. -/
@[simp]
protected theorem isOver.map_coeff_fourier [FaithfulSMul R ℂ] (hf : isOver R f) :
    ∀ n, (algebraMap R ℂ) (coeff n hf.fourier) = coeff n (qExp f) := by
  simpa only [coeff_map] using PowerSeries.ext_iff.mp hf.map_fourier


@[simp] theorem isOver_zero [Zero F] [IsZeroApply F ℍ ℂ] : isOver R (0 : F) := by
  rw [isOver, qExp_zero]; exact zero_mem _


@[simp] theorem isOver_one [Γ.HasDetPlusMinusOne] [One F] [IsOneApply F ℍ ℂ] :
    isOver R (1 : ModularForm Γ 0) := by
  rw [isOver, qExp_one]; exact one_mem _

include hF

/-- Forms whose Fourier coefficients lie over `R` are closed under addition. -/
theorem isOver_add [Γ.IsArithmetic] [Add F] [IsAddApply F ℍ ℂ]
    (hf : isOver R f) (hf' : isOver R f') : isOver R (f + f') := by
  rw [isOver, qExp_add (Γ := Γ)]; exact add_mem hf hf'

/-- Negation preserves the condition of having Fourier coefficients over `R`. -/
theorem isOver_neg [Γ.IsArithmetic] (hf : isOver R f)
    [Neg F] [IsNegApply F ℍ ℂ] : isOver R (-f) := by
  rw [isOver, qExp_neg]; exact neg_mem hf

/-- Forms whose Fourier coefficients lie over `R` are closed under subtraction. -/
theorem isOver_sub [Γ.IsArithmetic] [Sub F] [IsSubApply F ℍ ℂ]
    (hf : isOver R f) (hf' : isOver R f') : isOver R (f - f') := by
  rw [isOver, qExp_sub]; exact sub_mem hf hf'

omit hF

/-- The product of forms over `R` also has Fourier coefficients over `R`. -/
theorem isOver_mul [Γ.IsArithmetic] {f : ModularForm Γ k} {g : ModularForm Γ j}
  (hf : isOver R f) (hg : isOver R g) : isOver R (f.mul g) := by
  rw [isOver, qExp_mul]; exact mul_mem hf hg

/-- Natural powers preserve the condition of having Fourier coefficients over `R`. -/
theorem isOver_pow [Γ.IsArithmetic] {f : ModularForm Γ k}
    (m : ℕ) (hf : isOver R f) : isOver R (f.pow m) := by
  rw [isOver, qExp_pow]; exact pow_mem hf m

@[simp] theorem isOver_intCast [Γ.HasDetPlusMinusOne] (z : ℤ) :
    isOver R (z : ModularForm Γ 0) := by
  rw [isOver, qExp_intCast]; exact intCast_mem _ _

@[simp] theorem isOver_natCast [Γ.HasDetPlusMinusOne] (n : ℕ) :
    isOver R (n : ModularForm Γ 0) := by
  rw [isOver, qExp_natCast]; exact natCast_mem _ _

/-- A constant in the image of `R` defines a weight-zero form over `R`. -/
theorem isOver_const [Γ.HasDetOne] {r : ℂ} (hr : r ∈ R // ℂ) :
    isOver R (const (Γ := Γ) r) := by
  rw [isOver, qExp_const]
  obtain ⟨g, rfl⟩ := hr
  use C g, by simp only [MapPowerSeries, map_C]

include hF

/-- Multiplication by a complex scalar in the image of `R` preserves forms over `R`. -/
theorem isOver_csmul [Γ.IsArithmetic] {r : ℂ} (hr : r ∈ R // ℂ) (hf : isOver R f)
    [SMul ℂ F] [IsSMulApply ℂ F ℍ ℂ] : isOver R (r • f) := by
  rw [isOver_iff]; intro n
  obtain ⟨g, hg⟩ := by simpa only [isOver, rangeMapPowerSeries] using hf
  use hr.choose • coeff n g
  rw [smul_eq_mul, map_mul, hr.choose_spec, ← coeff_map,
    hg, qExp_smul, map_smul, smul_eq_mul]


/-- Compatible scalar multiplication preserves forms over `R`. -/
theorem isOver_smul [Γ.IsArithmetic] {α} [CommSemiring α] [Algebra α R]
  [Algebra α ℂ] [IsScalarTower α R ℂ] [SMul α F] [IsSMulApply α F ℍ ℂ]
    (c : α) (f : F) (hf : isOver R f) : isOver R (c • f) := by
  rw [isOver_iff]; intro n
  obtain ⟨g, hg⟩ := by simpa only [isOver, rangeMapPowerSeries] using hf
  use algebraMap α R c • coeff n g
  rw [smul_eq_mul, map_mul, ← IsScalarTower.algebraMap_apply, qExp_smul,
    LinearMap.map_smul_of_tower, ← smul_eq_mul, algebraMap_smul, ← coeff_map, hg]


end ModularForm


/-- A weight-`k` modular form for `Γ` whose Fourier expansion comes from `R⟦X⟧`. -/
structure ModularFormOver (R : Type) [CommRing R] [Algebra R ℂ]
  (Γ : outParam <| Subgroup (GL (Fin 2) ℝ)) (k : outParam ℤ)
    extends ModularForm Γ k where
  /-- The Fourier expansion of the underlying modular form is defined over `R`. -/
  isOver' : isOver R toModularForm


/-- A type of weight-`k` modular forms for `Γ` whose Fourier expansions are defined over `R`. -/
class ModularFormOverClass (F : Type*) [FunLike F ℍ ℂ]
  (R : Type) [CommRing R] [Algebra R ℂ]
    (Γ : outParam <| Subgroup (GL (Fin 2) ℝ)) (k : outParam ℤ) : Prop
      extends ModularFormClass F Γ k where
  /-- Every form in the class has Fourier coefficients in the image of `R`. -/
  isOver_self (R) (f : F) : isOver R f


namespace ModularFormOver

export ModularFormOverClass (isOver_self)
attribute [simp] isOver_self


variable {R : Type} {F : Type*} [FunLike F ℍ ℂ] [CommRing R] [Algebra R ℂ]
  {Γ : Subgroup (GL (Fin 2) ℝ)} {k j : ℤ}


instance : FunLike (ModularFormOver R Γ k) ℍ ℂ where
  coe f := f.toFun
  coe_injective f g h := by cases f; cases g; congr; exact DFunLike.ext' h


/-- Two bundled forms over `R` are equal if their values agree on the upper half-plane. -/
theorem ext₂ {f g : ModularFormOver R Γ k} (h : ∀ z, f z = g z) : f = g :=
  DFunLike.ext f g h

initialize_simps_projections ModularFormOver (toFun → coe, as_prefix coe)

/-- Bundle an element of a modular-form class together with its coefficient-ring condition. -/
@[simps -fullyApplied, coe]
def ModularFormOverClass.modularFormOver [ModularFormOverClass F R Γ k] (f : F) :
    ModularFormOver R Γ k where
  toFun := f
  slash_action_eq' := SlashInvariantFormClass.slash_action_eq f
  holo' := ModularFormClass.holo f
  bdd_at_cusps' := ModularFormClass.bdd_at_cusps f
  isOver' := isOver_self R f

instance : ModularFormOverClass (ModularFormOver R Γ k) R Γ k where
  slash_action_eq f := f.slash_action_eq'
  holo f := f.holo'
  bdd_at_cusps f := f.bdd_at_cusps'
  isOver_self f := f.isOver'


instance [ModularFormOverClass F R Γ k] : CoeTC F (ModularFormOver R Γ k) :=
  ⟨ModularFormOverClass.modularFormOver⟩

theorem toFun_eq_coe (f : ModularFormOver R Γ k) : f.toFun = (f : ℍ → ℂ) :=
  rfl

theorem toModularForm_coe (f : ModularFormOver R Γ k) : ⇑f.1 = f :=
  rfl

theorem toModularForm_apply (f : ModularFormOver R Γ k) (z : ℍ) :
  f.toModularForm z = f z := rfl

instance : Zero (ModularFormOver R Γ k) :=
  ⟨{ toModularForm := 0, isOver' := isOver_zero }⟩

instance [Γ.HasDetPlusMinusOne] : One (ModularFormOver R Γ 0) :=
  ⟨{ toModularForm := 1, isOver' := isOver_one (F := ModularForm Γ 0) }⟩

instance [Γ.IsArithmetic] : Add (ModularFormOver R Γ k) where add f g :=
  { toModularForm := f.1 + g.1
    isOver' := isOver_add (F := ModularForm Γ k) f.isOver' g.isOver' }

instance [Γ.IsArithmetic] : Neg (ModularFormOver R Γ k) where neg f :=
  { toModularForm := -f.1, isOver' := isOver_neg (F := ModularForm Γ k) f.isOver' }

instance [Γ.IsArithmetic] : Sub (ModularFormOver R Γ k) where sub f g :=
  { toModularForm := f.1 - g.1, isOver' := isOver_sub (F := ModularForm Γ k) f.isOver' g.isOver' }


instance instSMulℝ {α : Type*} [SMul α ℝ] [CommSemiring α] [Algebra α R]
  [Algebra α ℂ] [IsScalarTower α R ℂ] [IsScalarTower α ℝ ℂ] [Γ.IsArithmetic] :
    SMul α (ModularFormOver R Γ k) where smul a f :=
  { toModularForm := a • f.1
    isOver' := isOver_smul (F := ModularForm Γ k) a f f.isOver' }


instance instSMulℂ {α : Type*} [CommSemiring α] [Algebra α R]
  [Algebra α ℂ] [IsScalarTower α R ℂ] [Γ.IsArithmetic] [Γ.HasDetOne] :
    SMul α (ModularFormOver R Γ k) where smul a f :=
  { toModularForm := a • f.1
    isOver' := isOver_smul (F := ModularForm Γ k) a f f.isOver' }

instance [Γ.HasDetPlusMinusOne] : NatCast (ModularFormOver R Γ 0) where
  natCast n := ⟨n, isOver_natCast n⟩

instance [Γ.HasDetPlusMinusOne] : IntCast (ModularFormOver R Γ 0) where
  intCast z := ⟨z, isOver_intCast z⟩

@[simp, norm_cast]
lemma coe_natCast [Γ.HasDetPlusMinusOne] (n : ℕ) :
  ⇑(n : ModularFormOver R Γ 0) = n := rfl

@[simp, norm_cast]
lemma coe_intCast [Γ.HasDetPlusMinusOne] (n : ℤ) :
    ⇑(n : ModularFormOver R Γ 0) = n := rfl

@[simp] theorem natCast_apply [Γ.HasDetPlusMinusOne] (n : ℕ) (z : ℍ) :
    (n : ModularFormOver R Γ 0) z = n := rfl

@[simp] theorem intCast_apply [Γ.HasDetPlusMinusOne] (n : ℤ) (z : ℍ) :
    (n : ModularFormOver R Γ 0) z = n := rfl


instance : IsZeroApply (ModularFormOver R Γ k) ℍ ℂ where
instance [Γ.HasDetPlusMinusOne] : IsOneApply (ModularFormOver R Γ 0) ℍ ℂ where
instance [Γ.IsArithmetic] : IsAddApply (ModularFormOver R Γ k) ℍ ℂ where
instance [Γ.IsArithmetic] : IsNegApply (ModularFormOver R Γ k) ℍ ℂ where
instance [Γ.IsArithmetic] : IsSubApply (ModularFormOver R Γ k) ℍ ℂ where
instance {α : Type*} [SMul α ℝ] [CommSemiring α] [Algebra α R] [Algebra α ℂ]
    [IsScalarTower α R ℂ] [IsScalarTower α ℝ ℂ] [Γ.IsArithmetic] :
  IsSMulApply α (ModularFormOver R Γ k) ℍ ℂ where
instance {α : Type*} [CommSemiring α] [Algebra α R] [Algebra α ℂ]
    [IsScalarTower α R ℂ] [Γ.IsArithmetic] [Γ.HasDetOne] :
  IsSMulApply α (ModularFormOver R Γ k) ℍ ℂ where


instance [Γ.IsArithmetic] : AddCommGroup (ModularFormOver R Γ k) :=
  fast_instance% FunLike.addCommGroup

instance {α : Type*} [SMul α ℝ] [CommSemiring α] [Algebra α R] [Algebra α ℂ]
    [IsScalarTower α R ℂ] [IsScalarTower α ℝ ℂ] [Γ.IsArithmetic] :
  Module α (ModularFormOver R Γ k) := fast_instance% FunLike.module

instance {α : Type*} [CommSemiring α] [Algebra α R] [Algebra α ℂ]
    [IsScalarTower α R ℂ] [Γ.IsArithmetic] [Γ.HasDetOne] :
  Module α (ModularFormOver R Γ k) := fast_instance% FunLike.module

instance : Inhabited (ModularFormOver R Γ k) := ⟨0⟩

/-- Multiply forms over `R`, adding their weights. -/
@[simps! -fullyApplied coe]
def mul [Γ.IsArithmetic] (f : ModularFormOver R Γ k) (g : ModularFormOver R Γ j) :
    ModularFormOver R Γ (k + j) :=
  { toModularForm := f.1.mul g.1, isOver' := isOver_mul f.isOver' g.isOver' }

@[simp] theorem mul_apply [Γ.IsArithmetic] (f : ModularFormOver R Γ k)
  (g : ModularFormOver R Γ j) (z : ℍ) : (f.mul g) z = f z * g z := rfl


/-- Raise a form over `R` to a natural power, multiplying its weight by the exponent. -/
def pow [Γ.IsArithmetic] (f : ModularFormOver R Γ k) (m : ℕ) : ModularFormOver R Γ (m * k) :=
  { toModularForm := f.1.pow m, isOver' := isOver_pow m f.isOver' }

@[simp] theorem pow_apply [Γ.IsArithmetic] (f : ModularFormOver R Γ k)
    (m : ℕ) (z : ℍ) : (f.pow m) z = f z ^ m := by
  change f.toModularForm.pow m z = f.toModularForm z ^ m
  rw [coe_pow]; rfl


/-- The weight-zero modular form with constant value given by the image of r in `ℂ`. -/
@[simps! -fullyApplied coe]
def const [Γ.IsArithmetic] [Γ.HasDetOne] (r : R) : ModularFormOver R Γ 0 :=
  { toModularForm := ModularForm.const (algebraMap R ℂ r)
    isOver' := isOver_const ⟨r,rfl⟩ }

@[simp] theorem const_apply [Γ.IsArithmetic] [Γ.HasDetOne] (r : R) (z : ℍ) :
  const (Γ := Γ) r z = (algebraMap R ℂ r) := rfl


@[simp] theorem const_one [Γ.IsArithmetic] [Γ.HasDetOne] :
    const 1 = (1 : ModularFormOver R Γ 0) :=
  ext₂ fun _ => by rw [const_apply, map_one, one_apply]

/-- Transport a modular form along an equality of weights. -/
@[simps! -fullyApplied coe]
def cast {a b : ℤ} (h : a = b) (f : ModularFormOver R Γ a) :
    ModularFormOver R Γ b :=
  { toModularForm := ModularForm.mcast h f.1
    isOver' := by subst h; exact f.isOver' }


@[simp] theorem cast_apply {a b z} (h : a = b) (f : ModularFormOver R Γ a) :
  f.cast h z = f z := rfl

/-- Graded modular forms are equal when their weights agree and their forms agree after
transport. -/
theorem gradedMonoid_eq_of_cast {a b : GradedMonoid (ModularFormOver R Γ)}
    (h : a.1 = b.1) (h' : cast h a.2 = b.2) : a = b := by
  obtain ⟨i, x⟩ := a
  obtain ⟨j, y⟩ := b
  cases h
  exact congrArg (Sigma.mk i) h'

instance (priority := 100) instGOne [Γ.HasDetPlusMinusOne] :
  GradedMonoid.GOne (ModularFormOver R Γ) where one := 1

instance (priority := 100) instGMul [Γ.IsArithmetic] :
  GradedMonoid.GMul (ModularFormOver R Γ) where mul := mul

@[simp] theorem gmul_form [Γ.IsArithmetic] {a b : ℤ} (f : ModularFormOver R Γ a)
  (g : ModularFormOver R Γ b) : (GradedMonoid.GMul.mul f g).1 = f.1.mul g.1 := rfl

@[simp] theorem gone_form [Γ.IsArithmetic] :
    (GradedMonoid.GOne.one : ModularFormOver R Γ 0).1 = 1 := rfl


/-- The weight-indexed family of modular forms over `R` is a graded commutative ring. -/
instance instGCommRing [Γ.IsArithmetic] : DirectSum.GCommRing (ModularFormOver R Γ) where
  one_mul x := gradedMonoid_eq_of_cast (zero_add _) <| ext₂ fun _ => one_mul _
  mul_one x := gradedMonoid_eq_of_cast (add_zero _) <| ext₂ fun _ => mul_one _
  mul_assoc x y z := gradedMonoid_eq_of_cast (add_assoc ..) <| ext₂ fun _ => mul_assoc ..
  mul_zero {_ _} x := ext₂ fun _ => mul_zero _
  zero_mul {_ _} x :=  ext₂ fun _ => zero_mul _
  mul_add {_ _} x y z := ext₂ fun _ => mul_add ..
  add_mul {_ _} x y z := ext₂ fun _ => add_mul ..
  mul_comm x y := gradedMonoid_eq_of_cast (add_comm _ _) <| ext₂ fun _ => mul_comm ..
  natCast := Nat.cast
  natCast_zero := ext₂ fun _ => by rw [natCast_apply, zero_apply, Nat.cast_zero]
  natCast_succ n := ext₂ fun _ => show ((n + 1 : ℕ) : ℂ) = (n : ℂ) + 1 by norm_num
  intCast := Int.cast
  intCast_ofNat n := ext₂ fun _ => show ((n : ℤ) : ℂ) = (n : ℂ) by norm_num
  intCast_negSucc_ofNat n := ext₂ fun _ =>
    show ((Int.negSucc n : ℤ) : ℂ) = -((n + 1 : ℕ) : ℂ) by norm_num


end ModularFormOver
