import ModularFormsMod.ModularFormOver.Basic

/-!
# Modular forms reduced along a coefficient homomorphism

`ModularFormMod r Γ k` is a power series over the target of `r : R →+* S`
that lifts to the Fourier expansion of a weight-`k` modular form over `R`.
The file constructs arithmetic, scalar actions, and graded ring operations,
together with the reduction map `ModularFormOver.Reduce`. Surjective `r`
also gives scalar multiplication and a Fourier linear map over `S`.
-/

open PowerSeries MatrixGroups ModularForm
open ModularFormOver hiding coeff


/-- A power series over `S` that is the coefficientwise reduction of a weight-`k` form over `R`. -/
structure ModularFormMod {R S : Type} [CommRing R] [Algebra R ℂ]
  [FaithfulSMul R ℂ] [CommRing S] (r : R →+* S)
    (Γ : outParam <| Subgroup (GL (Fin 2) ℝ)) (k : ℤ) : Type where
  /-- The Fourier expansion with coefficients in the target ring. -/
  protected fourier : PowerSeries S
  /-- The expansion lifts to a modular form of the same weight over the source ring. -/
  modular : ∃ g : ModularFormOver R Γ k, fourier = map r (ModularFormOver.fourier R g)


variable {R S : Type} [CommRing R] [Algebra R ℂ]
  [FaithfulSMul R ℂ] [CommRing S] {r : R →+* S}
    {Γ : Subgroup (GL (Fin 2) ℝ)} {k j : ℤ}


namespace ModularFormMod


instance : CoeOut (ModularFormMod r Γ k) (PowerSeries S) :=
  ⟨ModularFormMod.fourier⟩

/-- Reduced modular forms of a fixed weight are equal when their Fourier expansions agree. -/
@[ext]
theorem ext {f g : ModularFormMod r Γ k} (h : f.fourier = g.fourier) : f = g := by
  cases f; cases g; congr

@[simps]
instance : Zero (ModularFormMod r Γ k) :=
  ⟨0, 0, by rw [fourier_zero, map_zero]⟩

@[simps]
noncomputable instance [Γ.HasDetPlusMinusOne] : One (ModularFormMod r Γ 0) :=
  ⟨1, 1, by rw [fourier_one, map_one]⟩

@[simps]
noncomputable instance [Γ.IsArithmetic] : Add (ModularFormMod r Γ k) where add f g :=
  ⟨f.fourier + g.fourier, by
    obtain ⟨f, f', hf'⟩ := f
    obtain ⟨g, g', hg'⟩ := g
    use f' + g', by rw [fourier_add, map_add, ← hg', ← hf']⟩

@[simps]
noncomputable instance [Γ.IsArithmetic] : Neg (ModularFormMod r Γ k) where neg f :=
  ⟨-f.fourier, by
    obtain ⟨f, f', hf'⟩ := f
    use -f', by simp only [hf', fourier_neg, map_neg]⟩

@[simps]
noncomputable instance [Γ.IsArithmetic] : Sub (ModularFormMod r Γ k) where sub f g :=
  ⟨f.fourier - g.fourier, by
    obtain ⟨f, f', hf'⟩ := f
    obtain ⟨g, g', hg'⟩ := g
    use f' - g', by rw [fourier_sub, map_sub, ← hg', ← hf']⟩

/-- Act on reduced forms by mapping real-compatible source scalars through the coefficient
homomorphism. -/
noncomputable instance instSMulℝ {α : Type*} [SMul α ℝ] [CommSemiring α] [Algebra α R]
    [Algebra α ℂ] [IsScalarTower α R ℂ] [IsScalarTower α ℝ ℂ] [Γ.IsArithmetic] :
    SMul α (ModularFormMod r Γ k) where
  smul a f := ⟨r (algebraMap α R a) • f.fourier, by
    obtain ⟨g, hg⟩ := f.modular
    refine ⟨a • g, ?_⟩
    rw [ModularFormOver.fourier_smul, ← algebraMap_smul R a]
    simp only [PowerSeries.smul_eq_C_mul, map_mul, map_C, hg]⟩

/-- Act on reduced forms by mapping scalars through `R` and then through the coefficient
homomorphism. -/
noncomputable instance instSMulℂ {α : Type*} [CommSemiring α] [Algebra α R]
    [Γ.IsArithmetic] [Γ.HasDetOne] :
    SMul α (ModularFormMod r Γ k) where
  smul a f := ⟨r (algebraMap α R a) • f.fourier, by
    obtain ⟨g, hg⟩ := f.modular
    refine ⟨algebraMap α R a • g, ?_⟩
    rw [ModularFormOver.fourier_smul]
    simp only [PowerSeries.smul_eq_C_mul, map_mul, map_C, hg]⟩

/-- For the real-compatible scalar action, the Fourier series is scaled by the image of the
scalar under reduction. -/
@[simp] theorem smul_fourierℝ {α : Type*} [SMul α ℝ] [CommSemiring α] [Algebra α R]
  [Algebra α ℂ] [IsScalarTower α R ℂ] [IsScalarTower α ℝ ℂ] [Γ.IsArithmetic]
    (a : α) (f : ModularFormMod r Γ k) :
  (a • f).fourier = r (algebraMap α R a) • f.fourier := rfl

/-- Source-ring scalar multiplication acts on Fourier expansions through the reduction
homomorphism. -/
@[simp] theorem smul_fourier {α : Type*} [CommSemiring α] [Algebra α R]
  [Γ.IsArithmetic] [Γ.HasDetOne]
    (a : α) (f : ModularFormMod r Γ k) :
  (a • f).fourier = r (algebraMap α R a) • f.fourier := rfl

noncomputable instance [Γ.IsArithmetic] : AddCommGroup (ModularFormMod r Γ k) :=
  Function.Injective.addCommGroup ModularFormMod.fourier
    (fun _ _ => ext) rfl (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl)
    (fun f n => by
      change r (algebraMap ℕ R n) • f.fourier = n • f.fourier
      rw [show algebraMap ℕ R n = (n : R) from map_natCast (algebraMap ℕ R) n,
        map_natCast r]
      exact Nat.cast_smul_eq_nsmul S n f.fourier)
    (fun f z => by
      change r (algebraMap ℤ R z) • f.fourier = z • f.fourier
      rw [show algebraMap ℤ R z = (z : R) from map_intCast (algebraMap ℤ R) z,
        map_intCast r]
      exact Int.cast_smul_eq_zsmul S z f.fourier)

/-- The real-compatible scalar action makes reduced forms of a fixed weight a module. -/
noncomputable instance instModuleℝ {α : Type*} [SMul α ℝ] [CommSemiring α] [Algebra α R]
    [Algebra α ℂ] [IsScalarTower α R ℂ] [IsScalarTower α ℝ ℂ] [Γ.IsArithmetic] :
    Module α (ModularFormMod r Γ k) where
  one_smul f := ext (by simp)
  mul_smul a b f := ext (by simp [mul_smul])
  smul_zero a := ext (by simp)
  smul_add a f g := ext (by simp [smul_add])
  add_smul a b f := ext (by simp [add_smul])
  zero_smul f := ext (by simp)

/-- Compatible source scalars make reduced forms of a fixed weight a module. -/
noncomputable instance instModuleℂ {α : Type*} [CommSemiring α] [Algebra α R]
    [Γ.IsArithmetic] [Γ.HasDetOne] :
    Module α (ModularFormMod r Γ k) where
  one_smul f := ext (by simp)
  mul_smul a b f := ext (by simp [mul_smul])
  smul_zero a := ext (by simp)
  smul_add a f g := ext (by simp [smul_add])
  add_smul a b f := ext (by simp [add_smul])
  zero_smul f := ext (by simp)

section TargetScalars

variable [RingHomSurjective r]
  [Γ.IsArithmetic] [Γ.HasDetOne] {α : Type*} [CommSemiring α] [Algebra α S]

/-- Scalars in a surjective coefficient reduction can be lifted to the original ring.
No algebra structure on `ℂ` over the target ring is needed. -/
noncomputable instance (priority := 900) instSMulOfSurjective :
    SMul α (ModularFormMod r Γ k) where
  smul a f := ⟨a • f.fourier, by
    obtain ⟨b, hb⟩ := r.surjective (algebraMap α S a)
    obtain ⟨g, hg⟩ := f.modular
    refine ⟨b • g, ?_⟩
    rw [ModularFormOver.fourier_smul, ← algebraMap_smul S a, ← hb]
    simp only [PowerSeries.smul_eq_C_mul, map_mul, map_C, hg]⟩

/-- Target-ring scalar multiplication agrees with scalar multiplication of Fourier series. -/
@[simp] theorem smul_fourier_of_surjective (a : α)
    (f : ModularFormMod r Γ k) :
    (a • f).fourier = a • f.fourier := rfl

/-- For a surjective reduction map, reduced forms form a module over any compatible scalar ring
of `S`. -/
noncomputable instance (priority := 900) instModuleOfSurjective :
    Module α (ModularFormMod r Γ k) where
  one_smul f := ext (by simp)
  mul_smul a b f := ext (by simp [mul_smul])
  smul_zero a := ext (by simp)
  smul_add a f g := ext (by simp [smul_add])
  add_smul a b f := ext (by simp [add_smul])
  zero_smul f := ext (by simp)

end TargetScalars



@[simps]
noncomputable instance [Γ.HasDetPlusMinusOne] : NatCast (ModularFormMod r Γ 0) where
  natCast n := ⟨n, n, by rw [ModularFormOver.fourier_natCast, map_natCast]⟩

@[simps]
noncomputable instance [Γ.HasDetPlusMinusOne] : IntCast (ModularFormMod r Γ 0) where
  intCast z := ⟨z, z, by rw [ModularFormOver.fourier_intCast, map_intCast]⟩

instance : Inhabited (ModularFormMod r Γ k) := ⟨0⟩

/-- The reduced weight-zero form with constant Fourier expansion `s`, obtained by lifting `s`
along a surjective map. -/
@[simps]
noncomputable def const [Γ.IsArithmetic] [Γ.HasDetOne]
  [RingHomSurjective r] (s : S) : ModularFormMod r Γ 0 where
  fourier := C s
  modular := by
    obtain ⟨a, rfl⟩ := r.surjective s
    use ModularFormOver.const a, by simp

/-- Multiply reduced forms by multiplying their Fourier series and adding their weights. -/
@[simps]
noncomputable def mul [Γ.IsArithmetic] (f : ModularFormMod r Γ k) (g : ModularFormMod r Γ j) :
    ModularFormMod r Γ (k + j) :=
  ⟨f.fourier * g.fourier, by
    obtain ⟨f, f', hf'⟩ := f
    obtain ⟨g, g', hg'⟩ := g
    use f'.mul g', by rw [fourier_mul, map_mul, ← hg', ← hf']⟩

/-- Raise a reduced form to a natural power, multiplying its weight by the exponent. -/
@[simps]
noncomputable def pow [Γ.IsArithmetic] (f : ModularFormMod r Γ k) (m : ℕ) :
    ModularFormMod r Γ (m * k) :=
  ⟨f.fourier ^ m, by
    obtain ⟨f, f', hf'⟩ := f
    use f'.pow m, by rw [fourier_pow, map_pow, ← hf']⟩

/-- Transport a reduced form along an equality of weights, preserving its Fourier series. -/
@[simps]
def cast {a b : ℤ} (h : a = b) (f : ModularFormMod r Γ a) : ModularFormMod r Γ b where
  fourier := f.fourier
  modular := h ▸ f.modular

/-- Graded reduced forms agree when their weights and transported forms agree. -/
theorem gradedMonoid_eq_of_cast {a b : GradedMonoid (ModularFormMod r Γ)}
    (h : a.1 = b.1) (h' : ModularFormMod.cast h a.2 = b.2) : a = b := by
  obtain ⟨i, x⟩ := a
  obtain ⟨j, y⟩ := b
  cases h
  exact congrArg (Sigma.mk i) h'

noncomputable instance (priority := 100) instGOne [Γ.HasDetPlusMinusOne] :
  GradedMonoid.GOne (ModularFormMod r Γ) where
  one := (1 : ModularFormMod r Γ 0)

noncomputable instance (priority := 100) instGMul [Γ.IsArithmetic] :
  GradedMonoid.GMul (ModularFormMod r Γ) where
  mul := mul

@[simp] theorem gmul_fourier [Γ.IsArithmetic] {a b : ℤ}
    (f : ModularFormMod r Γ a) (g : ModularFormMod r Γ b) :
    (GradedMonoid.GMul.mul f g).fourier = f.fourier * g.fourier := rfl

@[simp] theorem gone_fourier [Γ.IsArithmetic] [Γ.HasDetPlusMinusOne] :
    (GradedMonoid.GOne.one : ModularFormMod r Γ 0).fourier = 1 := rfl

/-- Reduced modular forms, indexed by weight, form a graded commutative ring. -/
noncomputable instance instGCommRing [Γ.IsArithmetic] [Γ.HasDetPlusMinusOne] :
    DirectSum.GCommRing (ModularFormMod r Γ) where
  one_mul x := gradedMonoid_eq_of_cast (zero_add _) <| ModularFormMod.ext (by simp)
  mul_one x := gradedMonoid_eq_of_cast (add_zero _) <| ModularFormMod.ext (by simp)
  mul_assoc x y z := gradedMonoid_eq_of_cast (add_assoc ..) <|
    ModularFormMod.ext (by simp [mul_assoc])
  mul_zero {_ _} x := ModularFormMod.ext (by simp)
  zero_mul {_ _} x := ModularFormMod.ext (by simp)
  mul_add {_ _} x y z := ModularFormMod.ext (by simp [mul_add])
  add_mul {_ _} x y z := ModularFormMod.ext (by simp [add_mul])
  mul_comm x y := gradedMonoid_eq_of_cast (add_comm _ _) <|
    ModularFormMod.ext (by simp [mul_comm])
  natCast := Nat.cast
  natCast_zero := ModularFormMod.ext (by simp)
  natCast_succ n := ModularFormMod.ext (by norm_num)
  intCast := Int.cast
  intCast_ofNat n := ModularFormMod.ext (by norm_num)
  intCast_negSucc_ofNat n := ModularFormMod.ext (by norm_num)



/-- The Fourier expansion map as an `S`-linear map for a surjective coefficient reduction. -/
@[simps]
noncomputable def fourierLinearMap [Γ.IsArithmetic] [Γ.HasDetOne]
    [RingHomSurjective r] : ModularFormMod r Γ k →ₗ[S] S⟦X⟧ where
  toFun f := f.fourier
  map_add' := add_fourier
  map_smul' := smul_fourier_of_surjective


end ModularFormMod

/-- Reduce the Fourier coefficients of a form over `R` along `r : R →+* S`. -/
@[simps]
noncomputable def ModularFormOver.Reduce (r : R →+* S) (f : ModularFormOver R Γ k) :
    ModularFormMod r Γ k where
  fourier := map r (fourier R f)
  modular := ⟨f, rfl⟩


/-- Every reduced modular form has a lift to a modular form over the source ring. -/
theorem ModularFormMod.existsReduce (f : ModularFormMod r Γ k) :
    ∃ g : ModularFormOver R Γ k, f = g.Reduce r := by
  obtain ⟨g, hg⟩ := f.modular
  use g, ext hg

namespace ModularFormOver

variable (r)

@[simp] theorem Reduce_zero : Reduce r (0 : ModularFormOver R Γ k) = 0 := by
  apply ModularFormMod.ext
  simp

@[simp] theorem Reduce_one [Γ.HasDetPlusMinusOne] :
    Reduce r (1 : ModularFormOver R Γ 0) = 1 := by
  apply ModularFormMod.ext
  simp

@[simp] theorem Reduce_add [Γ.IsArithmetic] (f g : ModularFormOver R Γ k) :
    Reduce r (f + g) = Reduce r f + Reduce r g := by
  apply ModularFormMod.ext
  simp

@[simp] theorem Reduce_neg [Γ.IsArithmetic] (f : ModularFormOver R Γ k) :
    Reduce r (-f) = -Reduce r f := by
  apply ModularFormMod.ext
  simp

@[simp] theorem Reduce_sub [Γ.IsArithmetic] (f g : ModularFormOver R Γ k) :
    Reduce r (f - g) = Reduce r f - Reduce r g := by
  apply ModularFormMod.ext
  simp

/-- Reducing a product gives the product of the reduced forms. -/
@[simp] theorem Reduce_mul [Γ.IsArithmetic] (f : ModularFormOver R Γ k)
    (g : ModularFormOver R Γ j) :
    Reduce r (f.mul g) = (Reduce r f).mul (Reduce r g) := by
  apply ModularFormMod.ext
  simp

/-- Reduction commutes with natural powers. -/
@[simp] theorem Reduce_pow [Γ.IsArithmetic] (f : ModularFormOver R Γ k) (m : ℕ) :
    Reduce r (f.pow m) = (Reduce r f).pow m := by
  apply ModularFormMod.ext
  simp

/-- Reduction commutes with transport along an equality of weights. -/
@[simp] theorem Reduce_cast {a b : ℤ} (h : a = b) (f : ModularFormOver R Γ a) :
    Reduce r (f.cast h) = (Reduce r f).cast h := by
  cases h
  rfl

@[simp] theorem Reduce_natCast [Γ.HasDetPlusMinusOne] (n : ℕ) :
    Reduce r (n : ModularFormOver R Γ 0) = (n : ModularFormMod r Γ 0) := by
  apply ModularFormMod.ext
  simp

@[simp] theorem Reduce_intCast [Γ.HasDetPlusMinusOne] (z : ℤ) :
    Reduce r (z : ModularFormOver R Γ 0) = (z : ModularFormMod r Γ 0) := by
  apply ModularFormMod.ext
  simp

@[simp] theorem Reduce_smulℝ {α : Type*} [SMul α ℝ] [CommSemiring α] [Algebra α R]
    [Algebra α ℂ] [IsScalarTower α R ℂ] [IsScalarTower α ℝ ℂ] [Γ.IsArithmetic]
    (a : α) (f : ModularFormOver R Γ k) :
    Reduce r (a • f) = a • Reduce r f := by
  apply ModularFormMod.ext
  rw [Reduce_fourier, fourier_smul, ModularFormMod.smul_fourierℝ,
    Reduce_fourier, ← algebraMap_smul R a]
  simp only [PowerSeries.smul_eq_C_mul, map_mul, map_C]

/-- Reduction commutes with compatible scalar multiplication. -/
@[simp] theorem Reduce_smul {α : Type*} [CommSemiring α] [Algebra α R]
    [Algebra α ℂ] [IsScalarTower α R ℂ] [Γ.IsArithmetic] [Γ.HasDetOne]
    (a : α) (f : ModularFormOver R Γ k) :
    Reduce r (a • f) = a • Reduce r f := by
  apply ModularFormMod.ext
  rw [Reduce_fourier, fourier_smul, ModularFormMod.smul_fourier,
    Reduce_fourier, ← algebraMap_smul R a]
  simp only [PowerSeries.smul_eq_C_mul, map_mul, map_C]

/-- Coefficient reduction as an `R`-linear map on forms of a fixed weight. -/
@[simps]
noncomputable def ReduceLinearMap [Γ.IsArithmetic] [Γ.HasDetOne] :
    ModularFormOver R Γ k →ₗ[R] ModularFormMod r Γ k where
  toFun := Reduce r
  map_add' := Reduce_add r
  map_smul' := Reduce_smul r


end ModularFormOver
