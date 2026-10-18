import ModularFormsMod.ModularFormMod.Basic

/-!
# Composition of coefficient reductions

`ModularFormMod.map s` maps coefficients along `s`, keeping the original lifting ring.
It is always surjective, and is an equivalence when `s` is injective.
-/

open PowerSeries MatrixGroups

noncomputable section

namespace ModularFormMod

variable {R S T U : Type} [CommRing R] [Algebra R ℂ] [FaithfulSMul R ℂ]
  [CommRing S] [CommRing T] [CommRing U] {r : R →+* S}
  {Γ : Subgroup (GL (Fin 2) ℝ)} {k j : ℤ}

/-- Map the coefficients of a reduced form along a further ring homomorphism. -/
@[simps]
def map (s : S →+* T) (f : ModularFormMod r Γ k) :
    ModularFormMod (s.comp r) Γ k where
  fourier := PowerSeries.map s f.fourier
  modular := by
    obtain ⟨g, hg⟩ := f.modular
    exact ⟨g, by rw [hg]; rfl⟩

@[simp] theorem coeff_map (s : S →+* T) (n : ℕ) (f : ModularFormMod r Γ k) :
    coeff n (map s f) = s (coeff n f) := rfl

@[simp] theorem map_Reduce (s : S →+* T) (f : ModularFormOver R Γ k) :
    map s (f.Reduce r) = f.Reduce (s.comp r) := rfl

@[simp] theorem map_id (f : ModularFormMod r Γ k) : map (RingHom.id S) f = f := by
  apply ext
  rfl

@[simp] theorem map_map (s : S →+* T) (t : T →+* U) (f : ModularFormMod r Γ k) :
    map t (map s f) = map (t.comp s) f := by
  apply ext
  rfl

@[simp] theorem map_zero (s : S →+* T) : map s (0 : ModularFormMod r Γ k) = 0 := by
  apply ext
  exact _root_.map_zero (PowerSeries.map s)

@[simp] theorem map_add [Γ.IsArithmetic] (s : S →+* T) (f g : ModularFormMod r Γ k) :
    map s (f + g) = map s f + map s g := by
  apply ext
  exact _root_.map_add (PowerSeries.map s) _ _

@[simp] theorem map_neg [Γ.IsArithmetic] (s : S →+* T) (f : ModularFormMod r Γ k) :
    map s (-f) = -map s f := by
  apply ext
  exact _root_.map_neg (PowerSeries.map s) _

@[simp] theorem map_mul [Γ.IsArithmetic] (s : S →+* T)
    (f : ModularFormMod r Γ k) (g : ModularFormMod r Γ j) :
    map s (f.mul g) = (map s f).mul (map s g) := by
  apply ext
  exact _root_.map_mul (PowerSeries.map s) _ _

@[simp] theorem map_pow [Γ.IsArithmetic] (s : S →+* T)
    (f : ModularFormMod r Γ k) (n : ℕ) :
    map s (f.pow n) = (map s f).pow n := by
  apply ext
  exact _root_.map_pow (PowerSeries.map s) _ _

/-- Further coefficient reduction is onto because both spaces use lifts over `R`. -/
theorem map_surjective (s : S →+* T) :
    Function.Surjective (map (r := r) (Γ := Γ) (k := k) s) := by
  intro f
  obtain ⟨g, rfl⟩ := f.existsReduce
  exact ⟨g.Reduce r, rfl⟩

/-- Injective maps on target coefficients induce injective maps on reduced forms. -/
theorem map_injective (s : S →+* T) (hs : Function.Injective s) :
    Function.Injective (map (r := r) (Γ := Γ) (k := k) s) := by
  intro f g h
  exact ext (PowerSeries.map_injective s hs (congrArg ModularFormMod.fourier h))

/-- An embedding of target rings preserves the space of reductions up to equivalence. -/
def mapEquiv (s : S →+* T) (hs : Function.Injective s) :
    ModularFormMod r Γ k ≃ ModularFormMod (s.comp r) Γ k :=
  Equiv.ofBijective (map s) ⟨map_injective s hs, map_surjective s⟩

/-- Further coefficient reduction as a linear map over the original coefficient ring. -/
@[simps]
def mapLinearMap [Γ.IsArithmetic] [Γ.HasDetOne] (s : S →+* T) :
    ModularFormMod r Γ k →ₗ[R] ModularFormMod (s.comp r) Γ k where
  toFun := map s
  map_add' := map_add s
  map_smul' a f := by
    apply ext
    simp [PowerSeries.smul_eq_C_mul]

end ModularFormMod
