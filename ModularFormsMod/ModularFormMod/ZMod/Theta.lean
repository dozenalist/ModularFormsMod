/-
Copyright (c) 2026 Carter Hastings. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carter Hastings
-/

module

public import ModularFormsMod.ModularFormMod.ZMod.Basic
public import ModularFormsMod.ModularFormMod.Derivative

/-!
# The theta operator on modular forms modulo a large prime

The Fourier-series operator `X d/dX` raises weight by `p + 1` in characteristic `p`.
-/

@[expose] public section

open PowerSeries MatrixGroups ModularFormOver PInteger

namespace ModularFormMod

open scoped ModularFormMod.ZMod

variable {p : ℕ} [isLargePrime p] {k : ℤ}

/-- The theta operator on reduced level-one modular forms. -/
noncomputable def Theta (f : 𝓜 p k) : 𝓜 p (k + (p + 1)) where
  fourier := X * f.fourier.derivative
  modular := by
    have hp : 5 ≤ p := isLargePrime.AtLeastFive
    have h12 : (12 : ZMod p) ≠ 0 := by
      intro h
      have hdiv := (ZMod.natCast_eq_zero_iff 12 p).mp h
      have hprime : p.Prime := Fact.out
      rcases hprime.dvd_mul.mp (show p ∣ 4 * 3 from hdiv) with h4 | h3
      · have h2 := hprime.dvd_of_dvd_pow (show p ∣ 2 ^ 2 from h4)
        have := Nat.le_of_dvd (by decide : 0 < 2) h2
        omega
      · have := Nat.le_of_dvd (by decide : 0 < 3) h3
        omega
    have : Invertible (12 : ZMod p) := invertibleOfNonzero h12
    -- Both summands have weight `k + p + 1`, and their Fourier sum is `12 θf`.
    let g : 𝓜 p (k + (p + 1)) := (12 : ZMod p)⁻¹ •
      ((k : ZMod p) • (((Eaddone p).Reduce reduce).mul f).cast (by omega) +
        (((Esubone p).Reduce reduce).mul (normalizedSerreDerivative f)).cast (by omega))
    have hg : g.fourier = X * f.fourier.derivative := by
      simp only [g, smul_fourier_of_surjective, add_fourier, cast_fourier,
        mul_fourier, Reduce_Eaddone p (by omega), Reduce_Esubone,
        normalizedSerreDerivative_fourier, normalizedSerreFourier,
        cuspWidth_SL2Z, Nat.cast_one, mul_one, e2FourierAt_SL2Z, one_mul]
      simp [smul_smul]
    exact hg ▸ g.modular


@[simp] theorem Theta_fourier (f : 𝓜 p k) :
    f.Theta.fourier = X * f.fourier.derivative := rfl

/-- The theta operator multiplies the degree-`n` Fourier coefficient by `n`. -/
@[simp] theorem coeff_Theta (f : 𝓜 p k) (n : ℕ) :
    coeff n f.Theta = (n : ZMod p) * coeff n f := by
  cases n with
  | zero => simp [coeff]
  | succ n =>
    simp only [coeff, Theta_fourier, PowerSeries.coeff_succ_X_mul,
      PowerSeries.coeff_derivative, Nat.cast_add, Nat.cast_one]
    ring


@[simp] theorem Theta_zero : Theta (0 : 𝓜 p k) = 0 := by
  apply ext_coeff
  intro n
  simp

@[simp] theorem Theta_add (f g : 𝓜 p k) : (f + g).Theta = f.Theta + g.Theta := by
  apply ext_coeff
  intro n
  simp [mul_add]

@[simp] theorem Theta_neg (f : 𝓜 p k) : (-f).Theta = -f.Theta := by
  apply ext_coeff
  intro n
  simp

@[simp] theorem Theta_sub (f g : 𝓜 p k) : (f - g).Theta = f.Theta - g.Theta := by
  apply ext_coeff
  intro n
  simp [mul_sub]

@[simp] theorem Theta_smul (a : ZMod p) (f : 𝓜 p k) :
    (a • f).Theta = a • f.Theta := by
  apply ext_coeff
  intro n
  simp only [coeff_Theta, coeff_smul_of_surjective]
  ring

/-- Theta is linear over the residue field. -/
@[simps]
noncomputable def ThetaLinearMap : 𝓜 p k →ₗ[ZMod p] 𝓜 p (k + (p + 1)) where
  toFun := Theta
  map_add' := Theta_add
  map_smul' := Theta_smul

@[simp] theorem Theta_sum {ι : Type*} (s : Finset ι) (f : ι → 𝓜 p k) :
    (∑ i ∈ s, f i).Theta = ∑ i ∈ s, (f i).Theta :=
  map_sum ThetaLinearMap f s

@[simp] theorem Theta_cast {j : ℤ} (h : k = j) (f : 𝓜 p k) :
    (f.cast h).Theta = f.Theta.cast (by omega) := by
  apply ext
  rfl

@[simp] theorem Theta_const (a : ZMod p) : Theta (const a : 𝓜 p 0) = 0 := by
  apply ext
  simp

@[simp] theorem Theta_one : Theta (1 : 𝓜 p 0) = 0 := by
  apply ext
  simp

/-- Theta satisfies the product rule, with both terms transported to the same weight. -/
theorem Theta_mul {j : ℤ} (f : 𝓜 p k) (g : 𝓜 p j) :
    (f.mul g).Theta = (f.Theta.mul g).cast (by omega) +
      (f.mul g.Theta).cast (by omega) := by
  apply ext
  simp only [Theta_fourier, mul_fourier, cast_fourier, add_fourier,
    Derivation.leibniz, smul_eq_mul]
  ring


/-- Iterate theta, raising the weight by `m * (p + 1)`. -/
noncomputable def Theta_pow (f : 𝓜 p k) :
    (m : ℕ) → 𝓜 p (k + m * (p + 1))
  | 0 => f.cast (by group)
  | m + 1 => (f.Theta_pow m).Theta.cast (by group)


/-- Iterating theta `m` times multiplies the degree-`n` coefficient by `n^m`. -/
@[simp] theorem coeff_Theta_pow (f : 𝓜 p k) (m n : ℕ) :
    coeff n (f.Theta_pow m) = (n : ZMod p) ^ m * coeff n f := by
  induction m with
  | zero => simp [Theta_pow, coeff]
  | succ m ih =>
    change coeff n (f.Theta_pow m).Theta = _
    rw [coeff_Theta, ih, pow_succ]
    ring

@[simp] theorem Theta_pow_succ (f : 𝓜 p k) (m : ℕ) :
    f.Theta_pow (m + 1) = (f.Theta_pow m).Theta.cast (by group) := rfl


@[simp] theorem Theta_pow_zero (m : ℕ) : (0 : 𝓜 p k).Theta_pow m = 0 := by
  apply ext_coeff
  intro n
  simp

@[simp] theorem Theta_pow_add (f g : 𝓜 p k) (m : ℕ) :
    (f + g).Theta_pow m = f.Theta_pow m + g.Theta_pow m := by
  apply ext_coeff
  intro n
  simp [mul_add]

@[simp] theorem Theta_pow_neg (f : 𝓜 p k) (m : ℕ) :
    (-f).Theta_pow m = -(f.Theta_pow m) := by
  apply ext_coeff
  intro n
  simp

@[simp] theorem Theta_pow_sub (f g : 𝓜 p k) (m : ℕ) :
    (f - g).Theta_pow m = f.Theta_pow m - g.Theta_pow m := by
  apply ext_coeff
  intro n
  simp [mul_sub]

@[simp] theorem Theta_pow_smul (a : ZMod p) (f : 𝓜 p k) (m : ℕ) :
    (a • f).Theta_pow m = a • f.Theta_pow m := by
  apply ext_coeff
  intro n
  simp only [coeff_Theta_pow, coeff_smul_of_surjective]
  ring

/-- Each iterate of theta is linear over the residue field. -/
@[simps]
noncomputable def Theta_powLinearMap (m : ℕ) :
    𝓜 p k →ₗ[ZMod p] 𝓜 p (k + m * (p + 1)) where
  toFun f := f.Theta_pow m
  map_add' f g := Theta_pow_add f g m
  map_smul' a f := Theta_pow_smul a f m

@[simp] theorem Theta_pow_sum {ι : Type*} (s : Finset ι) (f : ι → 𝓜 p k) (m : ℕ) :
    (∑ i ∈ s, f i).Theta_pow m = ∑ i ∈ s, (f i).Theta_pow m :=
  map_sum (Theta_powLinearMap m) f s


@[simp] theorem Theta_pow_card (f : 𝓜 p k) :
    (f.Theta_pow p).fourier = f.Theta.fourier := by
  ext n
  change coeff n (f.Theta_pow p) = coeff n f.Theta
  rw [coeff_Theta_pow, coeff_Theta, ZMod.pow_card]


end ModularFormMod
