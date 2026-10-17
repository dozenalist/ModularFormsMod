import Mathlib.NumberTheory.ModularForms.Basic
import Mathlib.NumberTheory.ModularForms.QExpansion


/-!
This file defines isOver as a predicate on ModularFormClass and defines
ModularFormOver R as those modular forms whose q-expansions lie over R
-/


open UpperHalfPlane PowerSeries MatrixGroups ModularForm

attribute [simp] qExpansion_zero


section toSubringClass

namespace PowerSeries
variable {R} [Ring R] {G} [SetLike G R] [SubringClass G R]
  (p : PowerSeries R) (T : G) (hp : ∀ n, p.coeff n ∈ T)

/-- Given a formal power series `p` and a subring `T` that contains the
coefficients of `p`, return the corresponding formal power series
whose coefficients are in `T`. -/
noncomputable def toSubringClass : PowerSeries T := mk fun n => ⟨p.coeff n, hp n⟩

@[simp]
theorem coeff_toSubringClass {n : ℕ} : (p.toSubringClass T hp).coeff n = p.coeff n := by
  rw [toSubringClass, coeff_mk]

@[simp]
theorem constantCoeff_toSubringClass : (p.toSubringClass T hp).constantCoeff = p.constantCoeff :=
  coeff_zero_eq_constantCoeff_apply p

@[simp]
theorem map_toSubringClass : (p.toSubringClass T hp).map (SubringClass.subtype T) = p :=
  ext fun n => by simp


end PowerSeries
end toSubringClass


class Subgroup.OneStrictPeriod {R} [Ring R] (Γ : Subgroup (GL (Fin 2) R)) : Prop where
  one_mem : 1 ∈ Γ.strictPeriods

class Subgroup.isLawful {R} [CommRing R] (Γ : Subgroup (GL (Fin 2) R)) extends
  Γ.HasDetOne, Γ.OneStrictPeriod

instance {Γ : Subgroup (GL (Fin 2) ℝ)} [Γ.HasDetPlusMinusOne] :
  IsOneApply (ModularForm Γ 0) ℍ ℂ where


namespace ModularForm



variable {Γ : Subgroup (GL (Fin 2) ℝ)} [hΓ : Γ.isLawful] {k j : ℤ}
  {F : Type*} [FunLike F ℍ ℂ] [ModularFormClass F Γ k]


-- should redo with qExpansion 1
noncomputable abbrev qExp {Γ : Subgroup (GL (Fin 2) ℝ)} [Γ.isLawful] {k : ℤ}
    {F : Type*} [FunLike F ℍ ℂ] [ModularFormClass F Γ k] (f : F) : ℂ⟦X⟧ :=
  qExpansion 1 f

theorem qExp_def (f : F) : qExp f = qExpansion 1 f := rfl

@[simp] theorem qExp_add [Add F] [IsAddApply F ℍ ℂ] (f g : F) :
    qExp (f + g) = qExp f + qExp g := by
  unfold qExp
  rw [FunLike.coe_add]
  exact ModularForm.qExpansion_add zero_lt_one hΓ.one_mem f g

@[simp] theorem qExp_neg [Neg F] [IsNegApply F ℍ ℂ] (f : F) :
    qExp (-f) = -qExp f := by
  unfold qExp
  rw [FunLike.coe_neg]
  exact ModularForm.qExpansion_neg zero_lt_one hΓ.one_mem f

@[simp] theorem qExp_sub [Sub F] [IsSubApply F ℍ ℂ] (f g : F) :
    qExp (f - g) = qExp f - qExp g := by
  unfold qExp
  rw [FunLike.coe_sub]
  exact ModularForm.qExpansion_sub zero_lt_one hΓ.one_mem f g


@[simp] theorem qExp_smul {α} [SMul α F] [CommSemiring α]
  [Algebra α ℂ] [IsSMulApply α F ℍ ℂ] (c : α) (f : F) :
    qExp (c • f) = c • qExp f := by
  unfold qExp
  simp only [FunLike.coe_smul, ← algebraMap_smul ℂ c]
  exact ModularForm.qExpansion_smul zero_lt_one hΓ.one_mem _ f


theorem qExp_inj {f g : F} (h : qExp f = qExp g) : f = g := by
    apply DFunLike.coe_injective
    change ⇑(f : ModularForm Γ k) = ⇑(g : ModularForm Γ k)
    congr 1
    rwa [← qExpansion_inj zero_lt_one hΓ.one_mem]

@[simp] theorem qExp_mul (f : ModularForm Γ k)
    (g : ModularForm Γ j) : qExp (f.mul g) = qExp f * qExp g :=
  ModularForm.qExpansion_mul zero_lt_one hΓ.one_mem f g

@[simp] theorem qExp_pow (f : ModularForm Γ k) (m) : qExp (f.pow m) = (qExp f) ^ m :=
  ModularForm.qExpansion_pow zero_lt_one hΓ.one_mem f m

@[simp] theorem qExp_zero [Zero F] [IsZeroApply F ℍ ℂ] : qExp (0 : F) = 0 := by
  rw [qExp, FunLike.coe_zero, qExpansion_zero]

@[simp] theorem qExp_one [One F] [IsOneApply F ℍ ℂ] : qExp (1 : F) = 1 := by
  rw [qExp, show ⇑(1 : F) = ⇑(1 : ModularForm Γ 0) by simp]
  exact ModularForm.qExpansion_one

@[simp] theorem qExp_const (c : ℂ) : qExp (const c : ModularForm Γ 0) = C c := by
  rw [show (const c : ModularForm Γ 0) = c • 1 from ext fun _ => by simp,
    qExp_smul, qExp_one, smul_eq_C_mul, mul_one]

@[simp] theorem qExp_natCast (n : ℕ) : qExp (n : ModularForm Γ 0) = n := by
  rw [show (n : ModularForm Γ 0) = const n by rfl, qExp_const]
  exact map_natCast PowerSeries.C n

@[simp] theorem qExp_intCast (z : ℤ) : qExp (z : ModularForm Γ 0) = z := by
  rw [show (z : ModularForm Γ 0) = const z by rfl, qExp_const]
  exact map_intCast PowerSeries.C z


end ModularForm

abbrev rangeMap (R S : Type*) [CommRing R] [CommRing S]
  [Algebra R S] : Subring S := RingHom.range (algebraMap R S)

scoped [ModularFormOver] notation R:max " / " S:max => rangeMap R S

open ModularFormOver

@[simp] theorem Map_mem_rangeMap {R S : Type*} [CommRing R] [CommRing S]
  [Algebra R S] (r : R) : algebraMap R S r ∈ R / S := ⟨r, rfl⟩


theorem rangeMapPowerSeries (R S : Type*) [CommRing R] [CommRing S] [Algebra R S] :
  R⟦X⟧ / S⟦X⟧ = (map (algebraMap R S)).range := rfl

theorem MapPowerSeries (R S : Type*) [CommRing R] [CommRing S] [Algebra R S] :
    algebraMap R⟦X⟧ S⟦X⟧ = map (algebraMap R S) := rfl


theorem rangeMap_map_constantCoeff (R : Type*) [CommRing R] [Algebra R ℂ] :
    (R⟦X⟧ / ℂ⟦X⟧).map constantCoeff = R / ℂ := by
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

theorem map_algebraMap_injective {R : Type*} (S : Type*)
  [CommRing R] [CommRing S] [Algebra R S] [FaithfulSMul R S] :
    Function.Injective (map (algebraMap R S)) :=
  PowerSeries.map_injective (algebraMap R S) (FaithfulSMul.algebraMap_injective R S)


noncomputable def rangeMapEquiv (R S : Type*) [CommRing R] [CommRing S]
    [Algebra R S] [FaithfulSMul R S] : R ≃+* R / S :=
  RingEquiv.ofBijective (algebraMap R S).rangeRestrict ⟨
    fun x y h => by
      apply FaithfulSMul.algebraMap_injective R S
      rw [← RingHom.coe_rangeRestrict _ x,
        ← RingHom.coe_rangeRestrict _ y, h],
    RingHom.rangeRestrict_surjective _⟩


noncomputable def rangeMapPowerSeriesEquiv (R S : Type*) [CommRing R] [CommRing S]
    [Algebra R S] [FaithfulSMul R S] : R⟦X⟧ ≃+* R⟦X⟧ / S⟦X⟧ :=
  RingEquiv.ofBijective (map (algebraMap R S)).rangeRestrict ⟨
    fun f g h => by
      apply map_algebraMap_injective S
      rw [← RingHom.coe_rangeRestrict _ f,
        ← RingHom.coe_rangeRestrict _ g, h],
    RingHom.rangeRestrict_surjective _⟩


-- @[simp]
-- theorem rangeMapPowerSeriesEquiv_apply (R S : Type*) [CommRing R] [CommRing S]
--     [Algebra R S] [FaithfulSMul R S] ()


instance (R S : Type*) [CommRing R] [CommRing S]
    [Algebra R S] [FaithfulSMul R S] : FaithfulSMul R S⟦X⟧ where
  eq_of_smul_eq_smul {m n} h :=
    eq_of_smul_eq_smul (α := S) fun a => by
      simpa only [constantCoeff_smul, constantCoeff_C]
        using congrArg constantCoeff (h (C a))


namespace ModularForm

open ModularFormOver

variable {Γ : Subgroup (GL (Fin 2) ℝ)} [hΓ : Γ.isLawful] {k j : ℤ}
  {F : Type*} [FunLike F ℍ ℂ] [ModularFormClass F Γ k]


abbrev isOver (R : Type*) [CommRing R] [Algebra R ℂ] (f : F) : Prop :=
  qExp f ∈ R⟦X⟧ / ℂ⟦X⟧


theorem isOver_iff (R : Type*) [CommRing R] [Algebra R ℂ] (f : F) :
    isOver R f ↔ ∀ n, (qExp f).coeff n ∈ R / ℂ := by
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

protected noncomputable def isOver.fourier [FaithfulSMul R ℂ]
    (hf : isOver R f) : PowerSeries R :=
  (rangeMapPowerSeriesEquiv R ℂ).symm ⟨qExp f, hf⟩


theorem isOver.fourier_def [FaithfulSMul R ℂ] (hf : isOver R f) :
  hf.fourier = (rangeMapPowerSeriesEquiv R ℂ).symm ⟨qExp f, hf⟩ := rfl


-- protected theorem isOver.fourier_map_subtype (hf : isOver R f) :
--     PowerSeries.map (SubringClass.subtype R) hf.fourier = qExp f := by
--   rw [isOver.fourier, map_toSubringClass (hp := hf)]

@[simp]
protected theorem isOver.map_fourier [FaithfulSMul R ℂ] (hf : isOver R f) :
    map (algebraMap R ℂ) hf.fourier = qExp f := by
  change ((rangeMapPowerSeriesEquiv R ℂ)
    ((rangeMapPowerSeriesEquiv R ℂ).symm ⟨qExp f, hf⟩)).val = _
  simp only [RingEquiv.apply_symm_apply]


@[simp]
protected theorem isOver.map_coeff_fourier [FaithfulSMul R ℂ] (hf : isOver R f) :
    ∀ n, (algebraMap R ℂ) (coeff n hf.fourier) = coeff n (qExp f) := by
  simpa only [coeff_map] using PowerSeries.ext_iff.mp hf.map_fourier


@[simp] theorem isOver_zero [Zero F] [IsZeroApply F ℍ ℂ] : isOver R (0 : F) := by
  rw [isOver, qExp_zero]; exact zero_mem _

@[simp] theorem isOver_one [One F] [IsOneApply F ℍ ℂ] : isOver R (1 : ModularForm Γ 0) := by
    rw [isOver, qExp_one]; exact one_mem _

theorem isOver_add [Add F] [IsAddApply F ℍ ℂ] (hf : isOver R f) (hf' : isOver R f') :
    isOver R (f + f') := by
  rw [isOver, qExp_add]; exact add_mem hf hf'

theorem isOver_neg (hf : isOver R f) [Neg F] [IsNegApply F ℍ ℂ] : isOver R (-f) := by
  rw [isOver, qExp_neg]; exact neg_mem hf

theorem isOver_sub [Sub F] [IsSubApply F ℍ ℂ] (hf : isOver R f) (hf' : isOver R f') :
    isOver R (f - f') := by
  rw [isOver, qExp_sub]; exact sub_mem hf hf'

theorem isOver_mul {f : ModularForm Γ k} {g : ModularForm Γ j} (hf : isOver R f) (hg : isOver R g) :
    isOver R (f.mul g) := by
  rw [isOver, qExp_mul]; exact mul_mem hf hg

theorem isOver_pow {f : ModularForm Γ k} (m : ℕ) (hf : isOver R f) :
    isOver R (f.pow m) := by
  rw [isOver, qExp_pow]; exact pow_mem hf m

@[simp] theorem isOver_intCast (z : ℤ) : isOver R (z : ModularForm Γ 0) := by
  rw [isOver, qExp_intCast]; exact intCast_mem _ _

@[simp] theorem isOver_natCast (n : ℕ) : isOver R (n : ModularForm Γ 0) := by
  rw [isOver, qExp_natCast]; exact natCast_mem _ _

theorem isOver_const {r : ℂ} (hr : r ∈ R / ℂ) : isOver R (const (Γ := Γ) r) := by
  rw [isOver, qExp_const]
  obtain ⟨g, rfl⟩ := hr
  use C g, by simp only [MapPowerSeries, map_C]


theorem isOver_csmul {r : ℂ} (hr : r ∈ R / ℂ) (hf : isOver R f)
    [SMul ℂ F] [IsSMulApply ℂ F ℍ ℂ] : isOver R (r • f) := by
  rw [isOver_iff]; intro n
  obtain ⟨g, hg⟩ := by simpa only [isOver, rangeMapPowerSeries] using hf
  use hr.choose • coeff n g
  simp only [smul_eq_mul, map_mul, hr.choose_spec,
    ← coeff_map, hg, qExp_smul, map_smul]


theorem isOver_smul {α} [CommSemiring α] [Algebra α R] [Algebra α ℂ]
    [IsScalarTower α R ℂ] [SMul α F] [IsSMulApply α F ℍ ℂ]
    (c : α) (f : F) (hf : isOver R f) : isOver R (c • f) := by
  rw [isOver_iff]; intro n
  obtain ⟨g, hg⟩ := by simpa only [isOver, rangeMapPowerSeries] using hf
  use algebraMap α R c • coeff n g
  rw [smul_eq_mul, map_mul, ← IsScalarTower.algebraMap_apply,
    qExp_smul, LinearMap.map_smul_of_tower]
  rw [← smul_eq_mul, algebraMap_smul, ← coeff_map, hg]


end ModularForm

-- should extend ModularForm
structure ModularFormOver (R : Type*) [CommRing R] [Algebra R ℂ]
  (Γ : Subgroup (GL (Fin 2) ℝ) := 𝒮ℒ) [Γ.isLawful] (k : ℤ) where
  form : ModularForm Γ k
  isOver' : isOver R form


class ModularFormOverClass (F : Type*) [FunLike F ℍ ℂ] [ModularFormClass F Γ k]

namespace ModularFormOver


variable {R : Type*} [CommRing R] [Algebra R ℂ]
  {Γ : Subgroup (GL (Fin 2) ℝ)} [hΓ : Γ.isLawful] {k j : ℤ}


theorem mk_inj {f g : ModularFormOver R Γ k} (h : f.form = g.form) : f = g := by
  cases f; cases g; congr

instance : FunLike (ModularFormOver R Γ k) ℍ ℂ where
  coe f := f.form
  coe_injective _ _ h := mk_inj <| DFunLike.coe_injective h


theorem ext₂ {f g : ModularFormOver R Γ k} (h : ∀ z, f z = g z) : f = g :=
  mk_inj <| ModularForm.ext h

theorem coe_def (f : ModularFormOver R Γ k) : ⇑f = ⇑f.form := rfl

instance : ModularFormClass (ModularFormOver R Γ k) Γ k where
  slash_action_eq f := f.form.slash_action_eq'
  holo f := f.form.holo'
  bdd_at_cusps f := f.form.bdd_at_cusps'



@[simp] theorem isOver_self (f : ModularFormOver R Γ k) : isOver R f :=
  f.isOver'

theorem qExp_form (f : ModularFormOver R Γ k) : qExp f.form = qExp f := rfl

@[simps]
instance : Zero (ModularFormOver R Γ k) :=
  ⟨{ form := 0, isOver' := isOver_zero }⟩

@[simps]
instance : One (ModularFormOver R Γ 0) :=
  ⟨{ form := 1, isOver' := isOver_one (F := ModularForm Γ 0) }⟩

@[simps]
instance : Add (ModularFormOver R Γ k) :=
  ⟨fun f g => {
    form := f.form + g.form
    isOver' := isOver_add f.isOver' g.isOver' }⟩

@[simps]
instance : Neg (ModularFormOver R Γ k) :=
  ⟨fun f => { form := -f.form, isOver' := isOver_neg f.isOver' }⟩

@[simps]
instance : Sub (ModularFormOver R Γ k) :=
  ⟨fun f g => { form := f.form - g.form, isOver' := isOver_sub f.isOver' g.isOver' }⟩


instance : IsZeroApply (ModularFormOver R Γ k) ℍ ℂ where
instance : IsOneApply (ModularFormOver R Γ 0) ℍ ℂ where
instance : IsAddApply (ModularFormOver R Γ k) ℍ ℂ where
instance : IsNegApply (ModularFormOver R Γ k) ℍ ℂ where
instance : IsSubApply (ModularFormOver R Γ k) ℍ ℂ where


-- instance : SMul ℕ (ModularFormOver R Γ k) where
--   smul n f :=
--     ⟨n • f.form, fun m => by
--       rw [← Nat.cast_smul_eq_nsmul ℂ n f.form, qExp_smul,
--         PowerSeries.coeff_smul, smul_eq_mul]
--       exact mul_mem (intCast_mem R (n : ℤ)) (f.isOver' m)⟩

-- instance : SMul ℤ (ModularFormOver R Γ k) where
--   smul z f :=
--     ⟨z • f.form, fun m => by
--       rw [← Int.cast_smul_eq_zsmul ℂ z f.form, qExp_smul,
--         PowerSeries.coeff_smul, smul_eq_mul]
--       exact mul_mem (intCast_mem R z) (f.isOver' m)⟩

-- instance : SMul R (ModularFormOver R Γ k) where
--   smul r f := ⟨r • f.form, isOver_smul r f.form f.isOver' ⟩

variable {α} [CommSemiring α] [Algebra α R] [Algebra α ℂ]
  [IsScalarTower α R ℂ]

instance : SMul α (ModularFormOver R Γ k) where
  smul a f := ⟨a • f.form, isOver_smul a f.form f.isOver'⟩


-- instance : IsSMulApply ℕ (ModularFormOver R Γ k) ℍ ℂ where
-- instance : IsSMulApply ℤ (ModularFormOver R Γ k) ℍ ℂ where
-- instance : IsSMulApply R (ModularFormOver R Γ k) ℍ ℂ where
instance : IsSMulApply α (ModularFormOver R Γ k) ℍ ℂ where

instance : AddCommGroup (ModularFormOver R Γ k) := fast_instance% FunLike.addCommGroup

instance : Inhabited (ModularFormOver R Γ k) := ⟨0⟩


@[simps]
def mul (f : ModularFormOver R Γ k) (g : ModularFormOver R Γ j) :
    ModularFormOver R Γ (k + j) where
  form := f.form.mul g.form
  isOver' := isOver_mul f.isOver' g.isOver'

@[simps]
def pow (f : ModularFormOver R Γ k) (m : ℕ) : ModularFormOver R Γ (m * k) where
  form := f.form.pow m
  isOver' := isOver_pow m f.isOver'


@[simps]
def const (r : R) : ModularFormOver R Γ 0 where
  form := ModularForm.const (algebraMap R ℂ r)
  isOver' := isOver_const ⟨r,rfl⟩


@[simp] theorem const_one : const 1 = (1 : ModularFormOver R Γ 0) :=
  mk_inj <| DFunLike.coe_injective (by simp)


@[simps]
def cast {a b : ℤ} (h : a = b) (f : ModularFormOver R Γ a) :
    ModularFormOver R Γ b where
  form := ModularForm.mcast h f.form
  isOver' := by subst h; exact f.isOver'

@[simp]
theorem cast_apply {a b z} (h : a = b) (f : ModularFormOver R Γ a) :
  f.cast h z = f z := rfl

theorem gradedMonoid_eq_of_cast {a b : GradedMonoid (ModularFormOver R Γ)}
    (h : a.1 = b.1) (h' : cast h a.2 = b.2) : a = b := by
  obtain ⟨i, x⟩ := a
  obtain ⟨j, y⟩ := b
  cases h
  exact congrArg (Sigma.mk i) h'

instance (priority := 100) instGOne : GradedMonoid.GOne (ModularFormOver R Γ) where
  one := 1

instance (priority := 100) instGMul : GradedMonoid.GMul (ModularFormOver R Γ) where
  mul f g := ModularFormOver.mul f g

@[simp] theorem gmul_form {a b : ℤ} (f : ModularFormOver R Γ a)
    (g : ModularFormOver R Γ b) :
    (GradedMonoid.GMul.mul f g).form = f.form.mul g.form := rfl

@[simp] theorem gone_form :
    (GradedMonoid.GOne.one : ModularFormOver R Γ 0).form = 1 := rfl

@[simps]
instance : NatCast (ModularFormOver R Γ 0) where
  natCast n := ⟨n, isOver_natCast n⟩

@[simps]
instance : IntCast (ModularFormOver R Γ 0) where
  intCast z := ⟨z, isOver_intCast z⟩

instance instModule : Module α (ModularFormOver R Γ k) := fast_instance% FunLike.module

instance instGCommRing : DirectSum.GCommRing (ModularFormOver R Γ) where
  one_mul x := gradedMonoid_eq_of_cast (zero_add _) (by
    apply mk_inj
    exact ModularForm.ext fun _ => by simp [cast, ModularForm.mcast_apply, gmul_form, gone_form])
  mul_one x := gradedMonoid_eq_of_cast (add_zero _) (by
    apply mk_inj
    exact ModularForm.ext fun _ => by simp [cast, ModularForm.mcast_apply, gmul_form, gone_form])
  mul_assoc x y z := gradedMonoid_eq_of_cast (add_assoc _ _ _) (by
    apply mk_inj
    exact ModularForm.ext fun τ => mul_assoc (x.snd.form τ) (y.snd.form τ) (z.snd.form τ))
  mul_zero {_ _} x := by
    apply mk_inj
    exact ModularForm.ext fun _ => by simp [gmul_form, zero_form]
  zero_mul {_ _} x := by
    apply mk_inj
    exact ModularForm.ext fun _ => by simp [gmul_form, zero_form]
  mul_add {_ _} x y z := by
    apply mk_inj
    exact ModularForm.ext fun τ => by
      simp only [gmul_form, add_form]
      exact mul_add (x.form τ) (y.form τ) (z.form τ)
  add_mul {_ _} x y z := by
    apply mk_inj
    exact ModularForm.ext fun τ => by
      simp only [gmul_form, add_form]
      exact add_mul (x.form τ) (y.form τ) (z.form τ)
  mul_comm x y := gradedMonoid_eq_of_cast (add_comm _ _) (by
    apply mk_inj
    exact ModularForm.ext fun τ => mul_comm (x.snd.form τ) (y.snd.form τ))
  natCast := Nat.cast
  natCast_zero := by
    apply mk_inj
    exact ModularForm.ext fun τ => by
      change ((0 : ℕ) : ModularForm Γ 0) τ = 0
      simp [ModularForm.coe_natCast]
  natCast_succ n := by
    apply mk_inj
    exact ModularForm.ext fun τ => by
      change ((n + 1 : ℕ) : ℂ) = (n : ℂ) + 1
      norm_num
  intCast := Int.cast
  intCast_ofNat n := by
    apply mk_inj
    exact ModularForm.ext fun τ => by
      change ((n : ℤ) : ℂ) = (n : ℂ)
      norm_num
  intCast_negSucc_ofNat n := by
    apply mk_inj
    exact ModularForm.ext fun τ => by
      change ((Int.negSucc n : ℤ) : ℂ) = -((n + 1 : ℕ) : ℂ)
      norm_num


variable [FaithfulSMul R ℂ]

noncomputable def fourier : ModularFormOver R Γ k →ₗ[R] PowerSeries R where
  toFun f := f.isOver_self.fourier
  map_add' f g := by
    ext n
    apply FaithfulSMul.algebraMap_injective R ℂ
    simp only [isOver.map_coeff_fourier, qExp_add, map_add]
  map_smul' r f := by
    ext n
    apply FaithfulSMul.algebraMap_injective R ℂ
    simp only [isOver.map_coeff_fourier, qExp_smul, LinearMap.map_smul_of_tower,
      RingHom.id_apply, map_smul, smul_eq_mul, map_mul]
    rw [← smul_eq_mul, ← algebraMap_smul ℂ r]


theorem fourier_def (f : ModularFormOver R Γ k) :
    f.fourier = f.isOver_self.fourier := rfl

theorem map_fourier (f : ModularFormOver R Γ k) :
    map (algebraMap R ℂ) f.fourier = qExp f :=
  isOver.map_fourier f.isOver_self

theorem fourier_inj {f f' : ModularFormOver R Γ k}
    (h : f.fourier = f'.fourier) : f = f' :=
  qExp_inj <| by simp only [← map_fourier, h]

theorem fourier_eq_iff (f : ModularFormOver R Γ k) (g : R⟦X⟧) :
    fourier f = g ↔ qExp f = map (algebraMap R ℂ) g :=
  ⟨fun h => by rw [← h, map_fourier],
    fun h => map_algebraMap_injective ℂ <| by rw [← h, map_fourier] ⟩

@[simp] theorem fourier_smul (a : α) (f : ModularFormOver R Γ k) :
    (a • f).fourier = a • f.fourier := by
  rw [← show (a • 1 : R) • f = a • f from ext₂ fun n => by
      simp only [smul_apply, smul_assoc, one_smul],
    map_smul, smul_assoc, one_smul]

@[simp] theorem fourier_zero : fourier (0 : ModularFormOver R Γ k) = 0 := by
  simp only [fourier, isOver.fourier, LinearMap.coe_mk, AddHom.coe_mk,
    qExp_zero, EmbeddingLike.map_eq_zero_iff]
  rfl

@[simp] theorem fourier_one : fourier (1 : ModularFormOver R Γ 0) = 1 := by
  simp only [fourier, isOver.fourier, LinearMap.coe_mk, AddHom.coe_mk,
    qExp_one, EmbeddingLike.map_eq_one_iff]
  rfl

@[simp] theorem fourier_const (r : R) : fourier (const (Γ := Γ) r) = C r := by
  rw [fourier_eq_iff, ← qExp_form, const_form, qExp_const, map_C]

@[simp] theorem fourier_natCast (n : ℕ) : fourier (n : ModularFormOver R Γ 0) = n := by
  rw [fourier_eq_iff, ← qExp_form, natCast_form, qExp_natCast, map_natCast]

@[simp] theorem fourier_intCast (z : ℤ) : fourier (z : ModularFormOver R Γ 0) = z := by
  rw [fourier_eq_iff, ← qExp_form, intCast_form, qExp_intCast, map_intCast]

@[simp] theorem fourier_mul (f : ModularFormOver R Γ k) (g : ModularFormOver R Γ j) :
    fourier (f.mul g) = fourier f * fourier g := by
  simp only [fourier_eq_iff, ← qExp_form, mul_form, qExp_mul, map_mul, map_fourier]

@[simp] theorem fourier_pow (f : ModularFormOver R Γ k) (m : ℕ) :
    fourier (f.pow m) = fourier f ^ m := by
  simp only [fourier_eq_iff, ← qExp_form, pow_form, qExp_pow, map_pow, map_fourier]


noncomputable def coeff (n : ℕ) : ModularFormOver R Γ k →ₗ[R] R :=
  (PowerSeries.coeff n).comp fourier

theorem coeff_def (n : ℕ) (f : ModularFormOver R Γ k) :
  f.coeff n = f.fourier.coeff n := rfl

@[ext]
protected theorem ext {f g : ModularFormOver R Γ k}
    (h : ∀ n, coeff n f = coeff n g) : f = g :=
  fourier_inj <| PowerSeries.ext h


variable (n : ℕ)

@[simp] theorem coeff_zero : coeff n (0 : ModularFormOver R Γ k) = 0 :=
  PowerSeries.ext_iff.mp fourier_zero n

@[simp] theorem coeff_const (r : R) :
    coeff n (const (Γ := Γ) r) = if n = 0 then r else 0 := by
  rw [coeff_def, fourier_const, coeff_C]

@[simp] theorem coeff_smul (n : ℕ) (a : α) (f : ModularFormOver R Γ k) :
    (a • f).coeff n = a • f.coeff n := by
  rw [coeff_def, fourier_smul,
    ← show (a • 1 : R) • f.fourier = a • f.fourier from ext fun n => by
      simp only [smul_assoc, one_smul], map_smul, smul_assoc, one_smul, coeff_def]


end ModularFormOver
