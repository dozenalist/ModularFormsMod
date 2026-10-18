import ModularFormsMod.ModularFormOver.Defs

/-!
# Fourier expansions and extension of coefficient rings

Modular forms over `R` remain defined over compatible larger coefficient rings.
This file constructs their Fourier expansions and individual coefficients in
such rings, proves compatibility with arithmetic and scalar extension, and
establishes that a modular form is determined by its Fourier coefficients.
-/

set_option linter.style.header false


namespace ModularFormOver

open ModularForm PowerSeries UpperHalfPlane

variable {Γ : Subgroup (GL (Fin 2) ℝ)} {k : ℤ} {F : Type*} [FunLike F ℍ ℂ]



/-- A Fourier expansion defined over `R` is also defined over a compatible algebra `S`. -/
theorem isOver.tower {R : Type} [CommRing R] [Algebra R ℂ]
  [ModularFormOverClass F R Γ k] (S : Type) [CommRing S]
    [Algebra R S] [Algebra S ℂ] [IsScalarTower R S ℂ]
      {f : F} (hf : isOver R f) : isOver S f := by
  rw [isOver_iff] at hf ⊢
  intro n
  obtain ⟨r, hr⟩ := hf n
  use algebraMap R S r, by rw [← IsScalarTower.algebraMap_apply, hr]


variable (R S : Type) [CommRing R] [Algebra R ℂ] [CommRing S] [Algebra R S]
  [Algebra S ℂ] [IsScalarTower R S ℂ] [hF : ModularFormOverClass F R Γ k]
include hF

/-- Every member of a class of forms over `R` is defined over a compatible larger ring `S`. -/
theorem isOver_tower (f : F) : isOver S f :=
  isOver.tower S (isOver_self R f)


/-- Extend the coefficient-ring condition of a modular-form class along an algebra tower. -/
theorem _root_.ModularFormOverClass.tower : ModularFormOverClass F S Γ k where
  isOver_self f := isOver_tower R S f

/-- Regard a form over `R` as a form over a compatible coefficient ring `S`. -/
protected def tower {R : Type} (S : Type) [CommRing R] [Algebra R ℂ]
  [CommRing S] [Algebra R S] [Algebra S ℂ] [IsScalarTower R S ℂ]
    (f : ModularFormOver R Γ k) : ModularFormOver S Γ k :=
  {f.toModularForm with isOver' := isOver_tower R S f}

omit hF in
@[simp] theorem tower_apply {R : Type} (S : Type) [CommRing R] [Algebra R ℂ]
  [CommRing S] [Algebra R S] [Algebra S ℂ] [IsScalarTower R S ℂ]
    (f : ModularFormOver R Γ k) (z : ℍ) :
  f.tower S z = f z := rfl



/-- The Fourier expansion of a form over `R`, with coefficients in a compatible ring `S`. -/
noncomputable def fourier (f : F) (S : Type := R) [CommRing S] [Algebra R S]
    [Algebra S ℂ] [IsScalarTower R S ℂ] [FaithfulSMul S ℂ] : PowerSeries S :=
  (isOver_tower R S f).fourier

variable (S : Type) [CommRing S] [Algebra R S]
  [Algebra S ℂ] [IsScalarTower R S ℂ] [FaithfulSMul S ℂ]


/-- The expansion in `S` is independent of which compatible source ring certifies the coefficient
condition. -/
theorem fourier_ring_change (T : Type) [CommRing T] [Algebra T ℂ] [Algebra T S]
  [IsScalarTower T S ℂ] [ModularFormOverClass F T Γ k] (f : F) :
    fourier R f S = fourier T f S := rfl


theorem fourier_def (f : F) : fourier R f S = (isOver_tower R S f).fourier := rfl

/-- Mapping the coefficients of `fourier` to `ℂ` recovers the complex Fourier expansion. -/
theorem map_fourier (f : F) : map (algebraMap S ℂ) (fourier R f S) = qExp f :=
  isOver.map_fourier (isOver_tower R S f)

@[simp] theorem fourierℂ (f : F) : fourier R f ℂ = qExp f := by
  rw [← map_fourier R ℂ]; rfl

/-- Equality of Fourier expansions over a faithful coefficient ring implies equality of modular
forms. -/
theorem fourier_inj [Γ.IsArithmetic] {f g : F}
    (h : fourier R f S = fourier R g S) : f = g :=
  qExp_inj <| by simp only [← map_fourier R S, h]

/-- Identify an expansion over `S` by checking its image in the complex power-series ring. -/
theorem fourier_eq_iff (f : F) (g : S⟦X⟧) :
    fourier R f S = g ↔ qExp f = map (algebraMap S ℂ) g :=
  ⟨fun h => by rw [← h, map_fourier],
    fun h => map_algebraMap_injective ℂ <| by rw [← h, map_fourier] ⟩

/-- Fourier expansion commutes with extension from an intermediate coefficient ring `T` to `S`. -/
theorem fourier_ring_cast (T : Type) [CommRing T] [Algebra R T] [Algebra T S]
  [Algebra T ℂ] [IsScalarTower R T ℂ] [FaithfulSMul T ℂ] [IsScalarTower T S ℂ] (f : F) :
    fourier R f S = map (algebraMap T S) (fourier R f T) := by
  rw [fourier_eq_iff]; ext n
  simp only [coeff_map, ← IsScalarTower.algebraMap_apply T S ℂ]
  rw [← coeff_map, map_fourier]


variable {α} [CommSemiring α] [Algebra α S] [Algebra α ℂ]
  [IsScalarTower α S ℂ] [SMul α F] [IsSMulApply α F ℍ ℂ]

@[simp] theorem fourier_smul [Γ.IsArithmetic] (a : α) (f : F) :
    fourier R (a • f) S = a • fourier R f S := by
  rw [← algebraMap_smul S, fourier_eq_iff, qExp_smul]
  ext n
  rw [coeff_map, coeff_smul _ (fourier R f S), smul_eq_mul,
    map_mul, ← coeff_map, map_fourier, ← IsScalarTower.algebraMap_apply,
      ← smul_eq_mul, algebraMap_smul, coeff_smul]

@[simp] theorem fourier_zero [Zero F] [IsZeroApply F ℍ ℂ] :
    fourier R (0 : F) S = 0 := by
  simp only [fourier, isOver.fourier, qExp_zero, EmbeddingLike.map_eq_zero_iff]
  rfl

@[simp] theorem fourier_one [One F] [IsOneApply F ℍ ℂ] [Γ.HasDetPlusMinusOne] :
    fourier R (1 : F) S = 1 := by
  simp only [fourier, isOver.fourier, qExp_one (Γ := Γ), EmbeddingLike.map_eq_one_iff]
  rfl

@[simp] theorem fourier_add [Add F] [IsAddApply F ℍ ℂ] [Γ.IsArithmetic] (f g : F) :
    fourier R (f + g) S = fourier R f S + fourier R g S := by
  simp only [fourier_eq_iff, map_add, map_fourier, qExp_add f]

@[simp] theorem fourier_neg [Neg F] [IsNegApply F ℍ ℂ] [Γ.IsArithmetic] (f : F) :
    fourier R (-f) S = - fourier R f S := by
  simp only [fourier_eq_iff, map_neg, map_fourier, qExp_neg f]

@[simp] theorem fourier_sub [Sub F] [IsSubApply F ℍ ℂ] [Γ.IsArithmetic] (f g : F) :
    fourier R (f - g) S = fourier R f S - fourier R g S := by
  simp only [fourier_eq_iff, map_sub, map_fourier, qExp_sub f]

omit hF

@[simp] theorem fourier_const [Γ.IsArithmetic] [Γ.HasDetOne] (r : R) :
    fourier R (const (Γ := Γ) r) S = C (algebraMap R S r) := by
  rw [fourier_eq_iff, qExp_def, coe_const, ← ModularForm.coe_const (Γ := Γ),
    ← qExp_def, qExp_const, map_C, ← IsScalarTower.algebraMap_apply]

@[simp] theorem fourier_natCast [Γ.HasDetPlusMinusOne] (n : ℕ) :
    fourier R (n : ModularFormOver R Γ 0) S = n := by
  rw [fourier_eq_iff, qExp_def, coe_natCast, ← ModularForm.coe_natCast (Γ := Γ),
    ← qExp_def, qExp_natCast, map_natCast]

@[simp] theorem fourier_intCast [Γ.HasDetPlusMinusOne] (n : ℤ) :
    fourier R (n : ModularFormOver R Γ 0) S = n := by
  rw [fourier_eq_iff, qExp_def, coe_intCast, ← ModularForm.coe_intCast (Γ := Γ),
    ← qExp_def, qExp_intCast, map_intCast]


/-- The Fourier expansion of a product is the product of the expansions. -/
@[simp] theorem fourier_mul [Γ.IsArithmetic] {k j}
  (f : ModularFormOver R Γ k) (g : ModularFormOver R Γ j) :
    fourier R (f.mul g) S = fourier R f S * fourier R g S := by
  rw [fourier_eq_iff, show qExp (f.mul g) = qExp (f.1.mul g.1) by rfl]
  simp only [qExp_mul, map_mul, map_fourier]; rfl


/-- The Fourier expansion of a natural power is the corresponding power of the expansion. -/
@[simp] theorem fourier_pow [Γ.IsArithmetic] (f : ModularFormOver R Γ k) (m : ℕ) :
    fourier R (f.pow m) S = fourier R f S ^ m := by
  rw [fourier_eq_iff, show qExp (f.pow m) = qExp (f.1.pow m) by rfl]
  simp only [qExp_pow, map_pow, map_fourier]; rfl

/-- Fourier expansion as an `R`-linear map on forms of a fixed weight. -/
@[simps]
noncomputable def fourierLinearMap {R} [CommRing R] [Algebra R ℂ] [FaithfulSMul R ℂ]
    [Γ.IsArithmetic] [Γ.HasDetOne] : ModularFormOver R Γ k →ₗ[R] R⟦X⟧ where
  toFun := fourier R
  map_add' := fourier_add R R
  map_smul' := fourier_smul R R

include hF

/-- The `n`-th Fourier coefficient, taken in the compatible coefficient ring `S`. -/
noncomputable def coeff (n : ℕ) (f : F) (S : Type := R) [CommRing S] [Algebra R S]
    [Algebra S ℂ] [IsScalarTower R S ℂ] [FaithfulSMul S ℂ] : S :=
  PowerSeries.coeff n (fourier R f S)


theorem coeff_def (n : ℕ) (f : F) :
  coeff R n f S = (fourier R f S).coeff n := rfl

/-- Forms of a fixed weight are determined by all of their Fourier coefficients. -/
theorem coeff_inj [Γ.IsArithmetic] {f g : F}
    (h : ∀ n, coeff R n f S = coeff R n g S) : f = g :=
  fourier_inj _ _ <| PowerSeries.ext h

/-- A coefficient over `S` maps to the corresponding complex Fourier coefficient. -/
@[simp] theorem map_coeff_eq_qExp (n : ℕ) (f : F) :
    algebraMap S ℂ (coeff R n f S) = (qExp f).coeff n := by
  rw [coeff, ← coeff_map, map_fourier]

/-- Identify a coefficient in `S` by comparing its image with the complex Fourier coefficient. -/
theorem coeff_eq_iff (n : ℕ) (f : F) (s : S) :
    coeff R n f S = s ↔ (qExp f).coeff n = algebraMap S ℂ s :=
  ⟨fun h => by rw [← h, coeff, ← coeff_map, map_fourier],
    fun h => FaithfulSMul.algebraMap_injective S ℂ <| by
      rw [← h, coeff, ← coeff_map, map_fourier]⟩

/-- The coefficient in `S` is independent of the compatible source ring used to define it. -/
theorem coeff_ring_change (T : Type) [CommRing T] [Algebra T ℂ] [Algebra T S]
  [IsScalarTower T S ℂ] [ModularFormOverClass F T Γ k] (f : F) (n : ℕ) :
    coeff R n f S = coeff T n f S := rfl

/-- Fourier coefficients commute with extension from an intermediate ring `T` to `S`. -/
theorem coeff_ring_cast (T : Type) [CommRing T] [Algebra R T] [Algebra T S]
  [Algebra T ℂ] [IsScalarTower R T ℂ] [FaithfulSMul T ℂ] [IsScalarTower T S ℂ] (f : F) (n : ℕ) :
    coeff R n f S = (algebraMap T S) (coeff R n f T) := by
  simp only [coeff_def, fourier_ring_cast R S T, coeff_map]

omit hF in
/-- Two forms over `R` are equal if all their Fourier coefficients agree. -/
@[ext]
protected theorem ext [Γ.IsArithmetic] {R : Type} [CommRing R]
  [Algebra R ℂ] [FaithfulSMul R ℂ] {f g : ModularFormOver R Γ k}
    (h : ∀ n, coeff R n f = coeff R n g) : f = g :=
  coeff_inj R R h


variable (n : ℕ)

@[simp] theorem coeff_zero [Zero F] [IsZeroApply F ℍ ℂ] : coeff R n (0 : F) S = 0 :=
  PowerSeries.ext_iff.mp (fourier_zero R S) n

@[simp] theorem coeff_one [Γ.HasDetPlusMinusOne] [One F] [IsOneApply F ℍ ℂ] :
    coeff R n (1 : F) S = if n = 0 then 1 else 0 := by
  rw [coeff_def, fourier_one, PowerSeries.coeff_one]

@[simp] theorem coeff_smul [Γ.IsArithmetic] (a : α) (f : F) :
    coeff R n (a • f) S = a • coeff R n f S := by
  rw [coeff_def, fourier_smul, PowerSeries.coeff_smul]; rfl

@[simp] theorem coeff_add [Γ.IsArithmetic] [Add F] [IsAddApply F ℍ ℂ] (f g : F) :
    coeff R n (f + g) S = coeff R n f S + coeff R n g S := by
  rw [coeff_def, fourier_add, map_add]; rfl

@[simp] theorem coeff_neg [Γ.IsArithmetic] [Neg F] [IsNegApply F ℍ ℂ] (f : F) :
    coeff R n (-f) S = - coeff R n f S := by
  rw [coeff_def, fourier_neg, map_neg]; rfl

@[simp] theorem coeff_sub [Γ.IsArithmetic] [Sub F] [IsSubApply F ℍ ℂ] (f g : F) :
    coeff R n (f - g) S = coeff R n f S - coeff R n g S := by
  rw [coeff_def, fourier_sub, map_sub]; rfl

omit hF

@[simp] theorem coeff_const [Γ.IsArithmetic] [Γ.HasDetOne] (r : R) :
    coeff R n (const (Γ := Γ) r) S = if n = 0 then algebraMap R S r else 0 := by
  rw [coeff_def, fourier_const, coeff_C]

@[simp] theorem coeff_natCast [Γ.HasDetPlusMinusOne] (m : ℕ) :
    coeff R n (m : ModularFormOver R Γ 0) S = if n = 0 then (m : S) else 0 := by
  rw [coeff_def, fourier_natCast, show (m : S⟦X⟧) = C (m : S) by rfl, coeff_C]

@[simp] theorem coeff_intCast [Γ.HasDetPlusMinusOne] (m : ℤ) :
    coeff R n (m : ModularFormOver R Γ 0) S = if n = 0 then (m : S) else 0 := by
  rw [coeff_def, fourier_intCast, show (m : S⟦X⟧) = C (m : S) by rw [map_intCast], coeff_C]

/-- The coefficient of a product is the convolution of the two coefficient sequences. -/
theorem coeff_mul {k j} [Γ.IsArithmetic] (f : ModularFormOver R Γ k) (g : ModularFormOver R Γ j) :
    coeff R n (f.mul g) S = ∑ x ∈ Finset.antidiagonal n, coeff R x.1 f S * coeff R x.2 g S := by
  simp only [coeff, fourier_mul, PowerSeries.coeff_mul]

/-- The coefficient of a natural power is a sum over exponent distributions of total degree `n`. -/
theorem coeff_pow [Γ.IsArithmetic] (f : ModularFormOver R Γ k) (m : ℕ) :
  coeff R n (f.pow m) S = ∑ l ∈ (Finset.range m).finsuppAntidiag n,
    ∏ i ∈ Finset.range m, coeff R (l i) f S := by
  simp only [coeff, fourier_pow, PowerSeries.coeff_pow]

/-- Extraction of the `n`-th Fourier coefficient as an `R`-linear map. -/
@[simps]
noncomputable def coeffLinearMap {R} [CommRing R] [Algebra R ℂ] [FaithfulSMul R ℂ]
    [Γ.IsArithmetic] [Γ.HasDetOne] (n : ℕ) : ModularFormOver R Γ k →ₗ[R] R where
  toFun := coeff R n
  map_add' := coeff_add R R n
  map_smul' := coeff_smul R R n


section isOverℂ

/-- Every complex modular form has its Fourier expansion over `ℂ`. -/
theorem isOverℂ {F : Type*} [FunLike F ℍ ℂ]
    [ModularFormClass F Γ k] (f : F) : isOver ℂ f :=
  ⟨qExp f, rfl⟩

/-- Bundle any element of a modular-form class as a form over `ℂ`. -/
def _root_.ModularFormClass.modularFormOverℂ {F : Type*} [FunLike F ℍ ℂ]
    [ModularFormClass F Γ k] (f : F) : ModularFormOver ℂ Γ k :=
  {ModularFormClass.modularForm f with isOver' := isOverℂ f}

instance {F : Type*} [FunLike F ℍ ℂ] [ModularFormClass F Γ k] :
  CoeTC F (ModularFormOver ℂ Γ k) := ⟨ModularFormClass.modularFormOverℂ⟩

end isOverℂ

end ModularFormOver
