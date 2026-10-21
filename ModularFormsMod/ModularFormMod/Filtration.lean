/-
Copyright (c) 2026 Carter Hastings. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carter Hastings
-/

module

public import ModularFormsMod.ModularFormMod.Basic
public import ModularFormsMod.ModularFormMod.Basis
public import Mathlib.NumberTheory.ModularForms.NormTrace

/-!
# Weights and filtration of reduced modular forms

`hasWeight j f` means that the Fourier expansion of `f` lifts to weight `j`, regardless
of its bundled weight. The filtration is the least such weight for a nonzero form.
The zero form has every weight, and its filtration is zero by the convention for `sInf`
on unbounded subsets of `ℤ`.
-/

@[expose] public section

variable {R S : Type} [CommRing R] [Algebra R ℂ] [FaithfulSMul R ℂ] [CommRing S]
  {Γ : Subgroup (GL (Fin 2) ℝ)} {k j : ℤ} {r : R →+* S}

open ModularFormOver PowerSeries MatrixGroups

namespace ModularFormMod

/-- A reduced form has weight `j` if its Fourier expansion lifts to a form of weight `j`. -/
def hasWeight (j : ℤ) (f : ModularFormMod r Γ k) : Prop :=
  ∃ g : ModularFormOver R Γ j, f.fourier = PowerSeries.map r (fourier R g)

theorem hasWeight.exists_reduce {f : ModularFormMod r Γ k} (h : f.hasWeight j) :
    ∃ g : ModularFormOver R Γ j, f.fourier = (g.Reduce r).fourier := h

theorem hasWeight.exists {f : ModularFormMod r Γ k} (h : f.hasWeight j) :
    ∃ g : ModularFormMod r Γ j, ∀ n, coeff n f = coeff n g := by
  obtain ⟨g, hg⟩ := h
  exact ⟨g.Reduce r, fun n => congrArg (PowerSeries.coeff n) hg⟩

/-- Every reduced form has its bundled weight. -/
@[simp] theorem hasWeight_self (f : ModularFormMod r Γ k) : f.hasWeight k := f.modular

@[simp] theorem hasWeight_zero (j : ℤ) : (0 : ModularFormMod r Γ k).hasWeight j :=
  ⟨0, by simp⟩

theorem hasWeight_ext {f : ModularFormMod r Γ k} {g : ModularFormMod r Γ j}
    (h : f.fourier = g.fourier) (m : ℤ) : f.hasWeight m ↔ g.hasWeight m := by
  simp only [hasWeight, h]

@[simp] theorem hasWeight_cast (f : ModularFormMod r Γ k) (h : k = j) (m : ℤ) :
    (f.cast h).hasWeight m ↔ f.hasWeight m := Iff.rfl

theorem exists_hasWeight (f : ModularFormMod r Γ k) :
    {j : ℤ | f.hasWeight j}.Nonempty := ⟨k, f.hasWeight_self⟩

section Arithmetic

variable [Γ.IsArithmetic]

theorem hasWeight_neg {f : ModularFormMod r Γ k} (h : f.hasWeight j) :
    (-f).hasWeight j := by
  obtain ⟨g, hg⟩ := h
  exact ⟨-g, by simp [hg]⟩

@[simp] theorem hasWeight_neg_iff (f : ModularFormMod r Γ k) :
    (-f).hasWeight j ↔ f.hasWeight j :=
  ⟨fun h => by simpa using hasWeight_neg h, hasWeight_neg⟩

theorem hasWeight_add {f g : ModularFormMod r Γ k}
    (hf : f.hasWeight j) (hg : g.hasWeight j) : (f + g).hasWeight j := by
  obtain ⟨f', hf'⟩ := hf
  obtain ⟨g', hg'⟩ := hg
  exact ⟨f' + g', by simp [hf', hg']⟩

theorem hasWeight_sub {f g : ModularFormMod r Γ k}
    (hf : f.hasWeight j) (hg : g.hasWeight j) : (f - g).hasWeight j := by
  simpa only [sub_eq_add_neg] using hasWeight_add hf (hasWeight_neg hg)

theorem hasWeight_mul {m n : ℤ} {f : ModularFormMod r Γ k} {g : ModularFormMod r Γ j}
    (hf : f.hasWeight m) (hg : g.hasWeight n) : (f.mul g).hasWeight (m + n) := by
  obtain ⟨f', hf'⟩ := hf
  obtain ⟨g', hg'⟩ := hg
  exact ⟨f'.mul g', by simp [hf', hg']⟩

theorem hasWeight_pow {f : ModularFormMod r Γ k} (hf : f.hasWeight j) (n : ℕ) :
    (f.pow n).hasWeight (n * j) := by
  obtain ⟨g, hg⟩ := hf
  exact ⟨g.pow n, by simp [hg]⟩

/-- Only the zero reduced form can have negative weight. -/
theorem hasWeight_iff_eq_zero_of_neg (hj : j < 0) (f : ModularFormMod r Γ k) :
    f.hasWeight j ↔ f = 0 := by
  refine ⟨fun ⟨g, hg⟩ => ?_, fun h => h ▸ hasWeight_zero j⟩
  have hg0 : g = 0 := ModularFormOver.ext₂ fun z =>
    DFunLike.congr_fun (ModularForm.isZero_of_neg_weight hj g.toModularForm) z
  exact ext (by simpa [hg0] using hg)

theorem hasWeight.nonneg {f : ModularFormMod r Γ k} (h : f.hasWeight j) (hf : f ≠ 0) :
    0 ≤ j := by
  by_contra hj
  exact hf ((hasWeight_iff_eq_zero_of_neg (lt_of_not_ge hj) f).mp h)

theorem BddBelow_hasWeight_set (f : ModularFormMod r Γ k) [NeZero f] :
    BddBelow {j : ℤ | f.hasWeight j} :=
  ⟨0, fun _ h => h.nonneg (NeZero.ne f)⟩

end Arithmetic

/-- The least weight lifting a nonzero reduced form, with value zero at the zero form. -/
noncomputable def Filtration (f : ModularFormMod r Γ k) : ℤ :=
  sInf {j : ℤ | f.hasWeight j}

@[simp] theorem Filtration_zero : Filtration (0 : ModularFormMod r Γ k) = 0 :=
  Int.csInf_of_not_bddBelow <| not_bddBelow_iff.2 fun j =>
    ⟨j - 1, hasWeight_zero _, sub_lt_self j zero_lt_one⟩

@[simp] theorem Filtration_cast (f : ModularFormMod r Γ k) (h : k = j) :
    (f.cast h).Filtration = f.Filtration := rfl

theorem Filtration_ext' {f : ModularFormMod r Γ k} {g : ModularFormMod r Γ j}
    (h : ∀ m, f.hasWeight m ↔ g.hasWeight m) : f.Filtration = g.Filtration := by
  unfold Filtration
  congr 1
  exact Set.ext h

theorem Filtration_eq_of_fourier_eq {f : ModularFormMod r Γ k} {g : ModularFormMod r Γ j}
    (h : f.fourier = g.fourier) : f.Filtration = g.Filtration :=
  Filtration_ext' (hasWeight_ext h)

theorem Filtration_ext {f : ModularFormMod r Γ k} {g : ModularFormMod r Γ j}
    (h : ∀ n, coeff n f = coeff n g) : f.Filtration = g.Filtration :=
  Filtration_eq_of_fourier_eq (PowerSeries.ext h)

section Arithmetic

variable [Γ.IsArithmetic]

/-- The infimum is attained, including at the zero form. -/
theorem Filtration_spec (f : ModularFormMod r Γ k) : f.hasWeight f.Filtration := by
  by_cases hf : f = 0
  · simp [hf]
  · let : NeZero f := ⟨hf⟩
    exact Int.csInf_mem f.exists_hasWeight f.BddBelow_hasWeight_set

theorem Filtration_le {f : ModularFormMod r Γ k} [NeZero f] (hf : f.hasWeight j) :
    f.Filtration ≤ j := csInf_le f.BddBelow_hasWeight_set hf

theorem Filtration_nonneg (f : ModularFormMod r Γ k) : 0 ≤ f.Filtration := by
  by_cases hf : f = 0
  · simp [hf]
  · exact f.Filtration_spec.nonneg hf

/-- A nonnegative lifting weight bounds the filtration even when the form vanishes. -/
theorem Filtration_le_of_nonneg {f : ModularFormMod r Γ k} (hf : f.hasWeight j)
    (hj : 0 ≤ j) : f.Filtration ≤ j := by
  by_cases h : f = 0
  · simpa [h] using hj
  · let : NeZero f := ⟨h⟩
    exact Filtration_le hf

theorem Filtration_le_Nat {j : ℕ} {f : ModularFormMod r Γ k} (hf : f.hasWeight j) :
    f.Filtration ≤ j := Filtration_le_of_nonneg hf (Int.natCast_nonneg j)

theorem Filtration_le_weight (f : ModularFormMod r Γ k) [NeZero f] :
    f.Filtration ≤ k := Filtration_le f.hasWeight_self

/-- A lift in the minimal weight. -/
noncomputable def Filtration_choose (f : ModularFormMod r Γ k) :
    ModularFormOver R Γ f.Filtration := f.Filtration_spec.choose

theorem Filtration_choose_spec (f : ModularFormMod r Γ k) :
    f.fourier = PowerSeries.map r (fourier R f.Filtration_choose) :=
  f.Filtration_spec.choose_spec

theorem coeff_eq_Filtration_choose (f : ModularFormMod r Γ k) (n : ℕ) :
    coeff n f = r (ModularFormOver.coeff R n f.Filtration_choose) :=
  congrArg (PowerSeries.coeff n) f.Filtration_choose_spec

@[simp] theorem Filtration_neg (f : ModularFormMod r Γ k) :
    (-f).Filtration = f.Filtration := Filtration_ext' fun _ => hasWeight_neg_iff f

theorem Filtration_mul_le (f : ModularFormMod r Γ k) (g : ModularFormMod r Γ j) :
    (f.mul g).Filtration ≤ f.Filtration + g.Filtration :=
  Filtration_le_of_nonneg (hasWeight_mul f.Filtration_spec g.Filtration_spec)
    (add_nonneg f.Filtration_nonneg g.Filtration_nonneg)

theorem Filtration_pow_le (f : ModularFormMod r Γ k) (n : ℕ) :
    (f.pow n).Filtration ≤ n * f.Filtration :=
  Filtration_le_of_nonneg (hasWeight_pow f.Filtration_spec n)
    (mul_nonneg (Int.natCast_nonneg n) f.Filtration_nonneg)

section TargetScalars

variable [Γ.HasDetOne] [RingHomSurjective r]

theorem hasWeight_smul {f : ModularFormMod r Γ k} (a : S) (hf : f.hasWeight j) :
    (a • f).hasWeight j := by
  obtain ⟨b, hb⟩ := r.surjective a
  obtain ⟨g, hg⟩ := hf
  refine ⟨b • g, ?_⟩
  simp only [smul_fourier_of_surjective, fourier_smul, PowerSeries.smul_eq_C_mul,
    _root_.map_mul, map_C, hb, hg]

theorem hasWeight_smul_iff {f : ModularFormMod r Γ k} {a : S} (ha : IsUnit a) :
    (a • f).hasWeight j ↔ f.hasWeight j := by
  obtain ⟨u, rfl⟩ := ha
  refine ⟨fun h => ?_, hasWeight_smul _⟩
  simpa only [smul_smul, Units.inv_mul, one_smul] using
    hasWeight_smul (↑(u⁻¹) : S) h

theorem Filtration_smul_le (a : S) (f : ModularFormMod r Γ k) :
    (a • f).Filtration ≤ f.Filtration :=
  Filtration_le_of_nonneg (hasWeight_smul a f.Filtration_spec) f.Filtration_nonneg

theorem Filtration_smul_eq {a : S} (ha : IsUnit a) (f : ModularFormMod r Γ k) :
    (a • f).Filtration = f.Filtration :=
  Filtration_ext' fun _ => hasWeight_smul_iff ha

end TargetScalars

end Arithmetic

section LevelOne

theorem le_Filtration {m : ℕ} (f : ModularFormMod r 𝒮ℒ k) (fn0 : f ≠ 0)
    (hk : ∀ n < m, f.coeff n = 0) : 12 * m ≤ f.Filtration := by
  by_contra h
  have hdim : Basis.dim f.Filtration ≤ m := by
    have := Basis.dim_le_div_twelve f.Filtration
    have := f.Filtration_nonneg
    omega
  obtain ⟨g, hg⟩ := f.Filtration_spec.exists
  have hg0 : g = 0 := sturm_bound fun n hn => by
    rw [← hg n, hk n (lt_of_lt_of_le hn hdim), coeff_zero]
  apply fn0
  apply ext_coeff
  intro n
  simpa [hg0] using hg n

end LevelOne
end ModularFormMod
