import ModularFormsMod.ModularFormMod.Map
import ModularFormsMod.ModularFormOver.Derivative

set_option linter.style.header false

/-!
# The normalized Serre derivative after coefficient reduction

The integral formula `12 X F' - k h E₂(X^h) F` descends along arbitrary coefficient maps.
It is independent of a lift and commutes with further coefficient reduction.
-/

open PowerSeries MatrixGroups

noncomputable section

namespace ModularFormMod

variable {R S T : Type} [CommRing R] [Algebra R ℂ] [FaithfulSMul R ℂ]
  [CommRing S] [CommRing T] {r : R →+* S}
  {Γ : Subgroup (GL (Fin 2) ℝ)} [Γ.le_SL2Z] [Γ.IsArithmetic] {k : ℤ}

/-- Coefficient mapping commutes with formal differentiation. -/
theorem map_derivative (s : S →+* T) (F : S⟦X⟧) :
    PowerSeries.map s F.derivative = (PowerSeries.map s F).derivative := by
  ext n
  simp [PowerSeries.coeff_derivative]

/-- The integral `E₂` series is compatible with every ring homomorphism. -/
theorem map_e2Fourier (s : S →+* T) :
    PowerSeries.map s (ModularFormOver.e2Fourier S) = ModularFormOver.e2Fourier T := by
  ext n
  simp only [ModularFormOver.e2Fourier, PowerSeries.coeff_map, PowerSeries.coeff_mk]
  split_ifs <;> simp [map_ofNat]

theorem map_e2FourierAt (s : S →+* T) :
    PowerSeries.map s (ModularFormOver.e2FourierAt Γ S) =
      ModularFormOver.e2FourierAt Γ T := by
  simp only [ModularFormOver.e2FourierAt, PowerSeries.map_expand, map_e2Fourier]

/-- The scaled Serre derivative formula on formal series over an arbitrary target ring. -/
def normalizedSerreFourier (Γ : Subgroup (GL (Fin 2) ℝ)) [Γ.le_SL2Z] [Γ.IsArithmetic]
    (k : ℤ) (F : S⟦X⟧) : S⟦X⟧ :=
  (12 : S) • (X * F.derivative) -
    ((k : S) * ModularFormOver.cuspWidth Γ) • (ModularFormOver.e2FourierAt Γ S * F)

theorem map_normalizedSerreFourier (s : S →+* T) (F : S⟦X⟧) :
    PowerSeries.map s (normalizedSerreFourier Γ k F) =
      normalizedSerreFourier Γ k (PowerSeries.map s F) := by
  simp [normalizedSerreFourier, PowerSeries.smul_eq_C_mul, map_derivative,
    map_e2FourierAt, map_ofNat]

/-- The normalized Serre derivative of a reduced form, defined directly on its Fourier series. -/
@[simps]
def normalizedSerreDerivative (f : ModularFormMod r Γ k) : ModularFormMod r Γ (k + 2) where
  fourier := normalizedSerreFourier Γ k f.fourier
  modular := by
    obtain ⟨g, hg⟩ := f.modular
    refine ⟨ModularFormOver.normalizedSerreDerivative R g, ?_⟩
    rw [ModularFormOver.fourier_normalizedSerreDerivative]
    change normalizedSerreFourier Γ k f.fourier =
      PowerSeries.map r (normalizedSerreFourier Γ k (ModularFormOver.fourier R g))
    rw [map_normalizedSerreFourier, hg]

@[simp] theorem normalizedSerreDerivative_Reduce (f : ModularFormOver R Γ k) :
    normalizedSerreDerivative (f.Reduce r) =
      (ModularFormOver.normalizedSerreDerivative R f).Reduce r := by
  apply ext
  simp only [normalizedSerreDerivative_fourier, ModularFormOver.Reduce_fourier,
    ModularFormOver.fourier_normalizedSerreDerivative]
  exact (map_normalizedSerreFourier r (ModularFormOver.fourier R f)).symm

@[simp] theorem normalizedSerreDerivative_map (s : S →+* T) (f : ModularFormMod r Γ k) :
    normalizedSerreDerivative (map s f) = map s (normalizedSerreDerivative f) := by
  apply ext
  exact (map_normalizedSerreFourier s f.fourier).symm

@[simp] theorem normalizedSerreDerivative_zero :
    normalizedSerreDerivative (0 : ModularFormMod r Γ k) = 0 := by
  apply ext
  simp [normalizedSerreFourier]

@[simp] theorem normalizedSerreDerivative_add (f g : ModularFormMod r Γ k) :
    normalizedSerreDerivative (f + g) =
      normalizedSerreDerivative f + normalizedSerreDerivative g := by
  apply ext
  simp only [normalizedSerreDerivative_fourier, add_fourier, normalizedSerreFourier,
    _root_.map_add, mul_add, smul_add]
  abel

/-- The descended derivative as an additive homomorphism. -/
@[simps]
def normalizedSerreDerivativeAddHom : ModularFormMod r Γ k →+ ModularFormMod r Γ (k + 2) where
  toFun := normalizedSerreDerivative
  map_zero' := normalizedSerreDerivative_zero
  map_add' := normalizedSerreDerivative_add

/-- The coefficient formula for the descended normalized Serre derivative. -/
theorem coeff_normalizedSerreDerivative_explicit (f : ModularFormMod r Γ k) (n : ℕ) :
    coeff n (normalizedSerreDerivative f) =
      (12 : S) * (n : S) * coeff n f -
        ((k : S) * ModularFormOver.cuspWidth Γ) *
          PowerSeries.coeff n (ModularFormOver.e2FourierAt Γ S * f.fourier) := by
  simp only [coeff, normalizedSerreDerivative_fourier, normalizedSerreFourier]
  cases n with
  | zero => simp
  | succ n =>
    simp only [_root_.map_sub, PowerSeries.coeff_smul, PowerSeries.coeff_succ_X_mul,
      PowerSeries.coeff_derivative, smul_eq_mul, Nat.cast_add, Nat.cast_one]
    ring

/-- For surjective coefficient maps the descended derivative is linear over the target ring. -/
@[simps]
def normalizedSerreDerivativeLinearMap [RingHomSurjective r] :
    ModularFormMod r Γ k →ₗ[S] ModularFormMod r Γ (k + 2) where
  toFun := normalizedSerreDerivative
  map_add' := normalizedSerreDerivative_add
  map_smul' a f := by
    apply ext
    simp only [normalizedSerreDerivative_fourier, smul_fourier_of_surjective,
      normalizedSerreFourier, mul_smul_comm, smul_sub, smul_smul]
    simp [smul_smul, mul_comm]

end ModularFormMod
