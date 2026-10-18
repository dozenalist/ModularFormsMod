import ModularFormsMod.ModularFormMod.Defs

/-!
# Fourier coefficients and congruences of reduced modular forms

The coefficient API identifies equality and vanishing of reductions with coefficientwise
congruences. Reduction is surjective for every coefficient homomorphism and injective when
the coefficient homomorphism is injective.
-/

open PowerSeries MatrixGroups

noncomputable section

variable {R S : Type} [CommRing R] [Algebra R ℂ] [FaithfulSMul R ℂ]
  [CommRing S] {r : R →+* S} {Γ : Subgroup (GL (Fin 2) ℝ)} {k : ℤ}

namespace ModularFormMod

/-- The `n`-th Fourier coefficient of a reduced modular form. -/
def coeff (n : ℕ) (f : ModularFormMod r Γ k) : S := f.fourier.coeff n

theorem coeff_fourier (n : ℕ) (f : ModularFormMod r Γ k) :
    f.fourier.coeff n = coeff n f := rfl

/-- Reduced forms of the same weight are determined by their coefficients. -/
theorem ext_coeff {f g : ModularFormMod r Γ k} (h : ∀ n, coeff n f = coeff n g) :
    f = g := ext (PowerSeries.ext h)

theorem eq_iff_coeff_eq {f g : ModularFormMod r Γ k} :
    f = g ↔ ∀ n, coeff n f = coeff n g :=
  ⟨fun h _ => congrArg _ h, ext_coeff⟩

@[simp] theorem coeff_zero (n : ℕ) : coeff n (0 : ModularFormMod r Γ k) = 0 := by
  simp [coeff]

@[simp] theorem coeff_add [Γ.IsArithmetic] (n : ℕ) (f g : ModularFormMod r Γ k) :
    coeff n (f + g) = coeff n f + coeff n g := by simp [coeff]

@[simp] theorem coeff_neg [Γ.IsArithmetic] (n : ℕ) (f : ModularFormMod r Γ k) :
    coeff n (-f) = -coeff n f := by simp [coeff]

@[simp] theorem coeff_sub [Γ.IsArithmetic] (n : ℕ) (f g : ModularFormMod r Γ k) :
    coeff n (f - g) = coeff n f - coeff n g := by simp [coeff]

@[simp] theorem coeff_smul [Γ.IsArithmetic] [Γ.HasDetOne]
    (n : ℕ) (a : R) (f : ModularFormMod r Γ k) :
    coeff n (a • f) = r a * coeff n f := by simp [coeff]

@[simp] theorem coeff_smul_of_surjective [Γ.IsArithmetic] [Γ.HasDetOne]
    [RingHomSurjective r] (n : ℕ) (a : S) (f : ModularFormMod r Γ k) :
    coeff n (a • f) = a * coeff n f := by
  simp only [coeff, smul_fourier_of_surjective, PowerSeries.coeff_smul, smul_eq_mul]

/-- Fourier expansion as an additive homomorphism, without surjectivity of `r`. -/
@[simps]
def fourierAddHom [Γ.IsArithmetic] : ModularFormMod r Γ k →+ S⟦X⟧ where
  toFun := ModularFormMod.fourier
  map_zero' := rfl
  map_add' := add_fourier

/-- Coefficient extraction over the target ring of a surjective reduction. -/
@[simps]
def coeffLinearMap [Γ.IsArithmetic] [Γ.HasDetOne] [RingHomSurjective r] (n : ℕ) :
    ModularFormMod r Γ k →ₗ[S] S where
  toFun := coeff n
  map_add' := coeff_add n
  map_smul' := coeff_smul_of_surjective n

end ModularFormMod

namespace ModularFormOver

@[simp] theorem coeff_Reduce (n : ℕ) (f : ModularFormOver R Γ k) :
    ModularFormMod.coeff n (f.Reduce r) = r (coeff R n f) := rfl

/-- Every reduced form lifts, regardless of whether the coefficient map is onto. -/
theorem Reduce_surjective (r : R →+* S) :
    Function.Surjective (Reduce (Γ := Γ) (k := k) r) := by
  intro f
  obtain ⟨g, hg⟩ := f.existsReduce
  exact ⟨g, hg.symm⟩

/-- Vanishing under reduction is the coefficientwise kernel condition. -/
theorem Reduce_eq_zero_iff (f : ModularFormOver R Γ k) :
    f.Reduce r = 0 ↔ ∀ n, r (coeff R n f) = 0 := by
  rw [ModularFormMod.eq_iff_coeff_eq]
  simp

/-- Two reductions agree exactly when all their reduced coefficients agree. -/
theorem Reduce_eq_iff (f g : ModularFormOver R Γ k) :
    f.Reduce r = g.Reduce r ↔ ∀ n, r (coeff R n f) = r (coeff R n g) := by
  rw [ModularFormMod.eq_iff_coeff_eq]
  simp

/-- An injective coefficient homomorphism loses no information about a form. -/
theorem Reduce_injective [Γ.IsArithmetic] (hr : Function.Injective r) :
    Function.Injective (Reduce (Γ := Γ) (k := k) r) := by
  intro f g h
  apply fourier_inj R R
  exact PowerSeries.map_injective r hr (congrArg ModularFormMod.fourier h)

/-- Reduction along an injective coefficient homomorphism is an equivalence. -/
def reduceEquivOfInjective [Γ.IsArithmetic] (hr : Function.Injective r) :
    ModularFormOver R Γ k ≃ ModularFormMod r Γ k :=
  Equiv.ofBijective (Reduce r) ⟨Reduce_injective hr, Reduce_surjective r⟩

/-- Reduction along the identity coefficient map recovers the original forms. -/
def reduceIdEquiv [Γ.IsArithmetic] :
    ModularFormOver R Γ k ≃ ModularFormMod (RingHom.id R) Γ k :=
  reduceEquivOfInjective Function.injective_id

/-- Source scalar multiplication agrees with target scalar multiplication after reduction. -/
theorem Reduce_smul_of_surjective [Γ.IsArithmetic] [Γ.HasDetOne] [RingHomSurjective r]
    (a : R) (f : ModularFormOver R Γ k) :
    Reduce r (a • f) = r a • Reduce r f := by
  apply ModularFormMod.ext
  simp [PowerSeries.smul_eq_C_mul]

end ModularFormOver
