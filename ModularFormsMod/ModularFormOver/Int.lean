import ModularFormsMod.ModularFormOver.Basic
import Mathlib.NumberTheory.ModularForms.EisensteinSeries.QExpansion
import Mathlib.NumberTheory.ModularForms.EisensteinSeries.E2.Summable
import Mathlib.NumberTheory.ModularForms.EisensteinSeries.E2.MDifferentiable
import Mathlib.NumberTheory.ModularForms.EisensteinSeries.E2.Transform
import Mathlib.NumberTheory.ModularForms.NormTrace
import Mathlib.NumberTheory.ModularForms.LevelOne.GradedRing
import ModularFormsMod.qExp_discriminant



/-!
-/

#check ModularForm.restrict

open ModularForm hiding E₄ E₆
open ModularFormOver UpperHalfPlane CongruenceSubgroup MatrixGroups ArithmeticFunction.sigma



variable {F : Type*} [FunLike F ℍ ℂ] {f : F} {Γ : Subgroup (GL (Fin 2) ℝ)} {k : ℤ}

@[coe]
instance ModularFormOverClass.towerℤ [hF : ModularFormOverClass F ℤ Γ k]
    (R : Type) [CommRing R] [Algebra R ℂ] : ModularFormOverClass F R Γ k :=
  hF.tower ℤ R

@[coe] instance (R : Type) [CommRing R] [Algebra R ℂ] :
    Coe (ModularFormOver ℤ Γ k) (ModularFormOver R Γ k) :=
  ⟨ModularFormOver.tower R⟩


namespace ModularFormOver


section LevelOne


theorem qExp_SL2Z {F : Type*} [FunLike F ℍ ℂ] [ModularFormClass F 𝒮ℒ k]
    (f : F) : qExp f = qExpansion 1 f := by
  rw [qExp, Subgroup.strictWidthInfty_SL2Z]

section bernoulli

private lemma bernoulli_four : bernoulli 4 = -(1 / 30) := by
  decide +kernel

private lemma bernoulli_six : bernoulli 6 = 1 / 42 := by
  decide +kernel

private lemma bernoulli'_six : bernoulli' 6 = 1 / 42 := by
  decide +kernel

private lemma bernoulli_eight : bernoulli 8 = -(1 / 30) := by
  have h := sum_bernoulli' 9
  simp only [Finset.sum_range_succ] at h
  norm_num [bernoulli'_eq_zero_of_odd, bernoulli'_two, bernoulli'_four,
    bernoulli'_six] at h
  norm_num [Nat.choose] at h
  rw [bernoulli_eq_bernoulli'_of_ne_one (by decide : 8 ≠ 1)]
  linarith

private lemma bernoulli'_eight : bernoulli' 8 = -(1 / 30) := by
  rw [← bernoulli_eq_bernoulli'_of_ne_one (by decide : 8 ≠ 1), bernoulli_eight]

private lemma bernoulli_ten : bernoulli 10 = 5 / 66 := by
  have h := sum_bernoulli' 11
  simp only [Finset.sum_range_succ] at h
  norm_num [bernoulli'_eq_zero_of_odd, bernoulli'_two, bernoulli'_four,
    bernoulli'_six, bernoulli'_eight] at h
  norm_num [Nat.choose] at h
  rw [bernoulli_eq_bernoulli'_of_ne_one (by decide : 10 ≠ 1)]
  linarith

private lemma bernoulli'_ten : bernoulli' 10 = 5 / 66 := by
  rw [← bernoulli_eq_bernoulli'_of_ne_one (by decide : 10 ≠ 1), bernoulli_ten]

private lemma bernoulli_twelve' : bernoulli' 12 = -(691 / 2730) := by
  have h := sum_bernoulli' 13
  simp only [Finset.sum_range_succ] at h
  norm_num [bernoulli'_eq_zero_of_odd, bernoulli'_two, bernoulli'_four,
    bernoulli'_six, bernoulli'_eight, bernoulli'_ten] at h
  norm_num [Nat.choose] at h
  linarith

private lemma bernoulli_fourteen : bernoulli 14 = 7 / 6 := by
  have h := sum_bernoulli' 15
  simp only [Finset.sum_range_succ] at h
  norm_num [bernoulli'_eq_zero_of_odd, bernoulli'_two, bernoulli'_four,
    bernoulli'_six, bernoulli'_eight, bernoulli'_ten, bernoulli_twelve'] at h
  norm_num [Nat.choose] at h
  rw [bernoulli_eq_bernoulli'_of_ne_one (by decide : 14 ≠ 1)]
  linarith

end bernoulli


noncomputable def E₄ : ModularFormOver ℤ 𝒮ℒ 4 where
  toModularForm := ModularForm.E₄
  isOver' := by
    rw [isOver_iff, qExp_SL2Z, ModularForm.E₄]
    intro n
    rw [EisensteinSeries.E_qExpansion_coeff (by decide) (by decide)]
    rw [bernoulli_four]
    use if n = 0 then 1 else 240 * σ 3 n
    norm_num

noncomputable def E₆ : ModularFormOver ℤ 𝒮ℒ 6 where
  toModularForm := ModularForm.E₆
  isOver' := by
    rw [isOver_iff, qExp_SL2Z, ModularForm.E₆]
    intro n
    rw [EisensteinSeries.E_qExpansion_coeff (by decide) (by decide)]
    rw [bernoulli_six]
    use if n = 0 then 1 else -504 * σ 5 n
    norm_num

noncomputable def discriminant : ModularFormOver ℤ 𝒮ℒ 12 where
  toModularForm := CuspForm.discriminant
  isOver' := by
    rw [isOver, qExp_SL2Z, qExpansion_discriminant]
    exact RingHom.mem_range_self _ _

scoped notation "Δ" => discriminant


theorem E₄_qExp_coeff (n : ℕ) : (qExp E₄).coeff n =
    if n = 0 then (1 : ℂ) else 240 * σ 3 n := by
  simp only [qExp_SL2Z, ← toModularForm_coe, E₄, ModularForm.E₄]
  rw [EisensteinSeries.E_qExpansion_coeff (by decide) (by decide), bernoulli_four]
  norm_num

theorem E₆_qExp_coeff (n : ℕ) : (qExp E₆).coeff n =
    if n = 0 then (1 : ℂ) else -504 * σ 5 n := by
  simp only [qExp_SL2Z, ← toModularForm_coe, E₆, ModularForm.E₆]
  rw [EisensteinSeries.E_qExpansion_coeff (by decide) (by decide), bernoulli_six]
  norm_num

theorem discriminant_qExp_coeff (n : ℕ) :
    (qExp discriminant).coeff n = (discProduct n).coeff n := by
  simp only [qExp_SL2Z, ← toModularForm_coe, discriminant, qExpansion_discriminant,
    PowerSeries.coeff_map, PowerSeries.coeff_mk, map_coeff_discProduct]

variable {R S} [CommRing R] [Algebra R ℂ] [CommRing S]
  [Algebra S ℂ] [FaithfulSMul S ℂ] [Algebra R S] [IsScalarTower R S ℂ]

theorem coeff_E₄ (n : ℕ) : coeff R n E₄ S = if n = 0 then (1 : S)
    else 240 * σ 3 n := by
  rw [coeff_eq_iff, E₄_qExp_coeff]
  split_ifs with h
  · exact algebraMap.coe_one.symm
  · rw [map_mul, map_natCast, ← Nat.cast_ofNat (R := S),
      map_natCast, Nat.cast_ofNat]


theorem coeff_E₆ (n : ℕ) : coeff R n E₆ S =
    if n = 0 then (1 : S) else -504 * σ 5 n := by
  rw [coeff_eq_iff, E₆_qExp_coeff]
  split_ifs with h
  · exact algebraMap.coe_one.symm
  · rw [map_mul, map_natCast, ← Nat.cast_ofNat (R := S),
      map_neg, map_natCast, Nat.cast_ofNat]

@[simp] theorem coeff_zero_E₄ : coeff R 0 E₄ S = 1 := by
  simp only [coeff_E₄, reduceIte]

@[simp] theorem coeff_one_E₄ : coeff R 1 E₄ S = 240 := by
  simp [coeff_E₄]

@[simp] theorem coeff_zero_E₆ : coeff R 0 E₆ S = 1 := by
  simp only [coeff_E₆, reduceIte]

@[simp] theorem coeff_one_E₆ : coeff R 1 E₆ S = -504 := by
  simp [coeff_E₆]

theorem coeff_discriminant (n : ℕ) : coeff R n Δ S = (discProduct n).coeff n := by
  rw [coeff_eq_iff, discriminant_qExp_coeff, map_coeff_discProduct]

@[simp] theorem coeff_zero_discriminant : coeff R 0 Δ S = 0 := by
  simp [coeff_discriminant, discProduct]

@[simp] theorem coeff_one_discriminant : coeff R 1 Δ S = 1 := by
  simp [coeff_discriminant, discProduct]

@[simp] theorem coeff_two_discriminant : coeff R 2 Δ S = -24 := by
  simp only [coeff_discriminant, discProduct, Finset.prod_range, Fin.prod_univ_two, Fin.isValue,
    Fin.coe_ofNat_eq_mod, Nat.zero_mod, zero_add, pow_one, Nat.mod_succ, Nat.reduceAdd,
    PowerSeries.coeff_succ_X_mul]
  ring_nf
  simpa only [map_add, map_sub, PowerSeries.coeff_one, one_ne_zero, ↓reduceIte,
    PowerSeries.coeff_one_mul, PowerSeries.coeff_one_X, one_mul,
    PowerSeries.constantCoeff_X, MulZeroClass.mul_zero, add_zero, zero_sub,
    PowerSeries.coeff_X_pow_mul', Nat.not_ofNat_le_one, sub_zero,
    PowerSeries.coeff_X_pow, OfNat.one_ne_ofNat,Int.reduceNeg, neg_inj, Nat.cast_ofNat]
      using (map_natCast _ _ : PowerSeries.constantCoeff 24 = (24 : S))



noncomputable def E2fourier (R : Type := ℤ) [CommRing R] [Algebra R ℂ] : PowerSeries R :=
  .mk fun n => if n = 0 then 1 else -24 * σ 1 n

@[simp] theorem coeff_E2fourier (R : Type) [CommRing R] [Algebra R ℂ] (n : ℕ) :
    (E2fourier R).coeff n = if n = 0 then 1 else (-24 : R) * σ 1 n := by
  rw [E2fourier, PowerSeries.coeff_mk]


theorem smul_discriminant_eq_E₄E₆ :
    1728 • Δ = (E₄.pow 3).cast (by rfl) - (E₆.pow 2).cast (by rfl) :=
  ext₂ fun z => by
    simp only [smul_apply, show Δ z = ModularForm.discriminant z by rfl,
      discriminant_eq_E₄_cube_sub_E₆_sq, nsmul_eq_mul, Nat.cast_ofNat,
        Int.reduceMul, sub_apply, cast_apply, pow_apply E₄, pow_apply E₆]
    field_simp
    rfl






end LevelOne
end ModularFormOver
open ModularFormOver
