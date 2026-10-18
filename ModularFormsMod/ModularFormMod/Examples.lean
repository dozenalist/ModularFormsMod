import ModularFormsMod.ModularFormMod.GradedRing
import ModularFormsMod.ModularFormMod.Derivative
import ModularFormsMod.ModularFormMod.Operators
import ModularFormsMod.ModularFormMod.ZMod.Basic

set_option linter.style.header false

/-!
# Examples of coefficient reduction and relations between weights

The congruence bound and basis apply to nonreduced target rings such as `ZMod 4`.
Modulo five, `E₄` has Fourier expansion one, giving a nonzero element of the Hasse ideal.
-/

open PowerSeries MatrixGroups ModularFormOver.Basis
open scoped DirectSum

noncomputable section

namespace ModularFormMod

/-- The weight-twelve reduced module over `ZMod 4` is free on two basis vectors. -/
example : Module.Basis (Fin 2) (ZMod 4)
    (ModularFormMod (Int.castRingHom (ZMod 4)) 𝒮ℒ 12) :=
  GBasis (Int.castRingHom (ZMod 4)) 12

/-- The constant and linear coefficients detect equality in weight twelve modulo four. -/
example {f g : ModularFormMod (Int.castRingHom (ZMod 4)) 𝒮ℒ 12}
    (h0 : coeff 0 f = coeff 0 g) (h1 : coeff 1 f = coeff 1 g) : f = g := by
  apply sturm_bound
  intro n hn
  have hn' : n < 2 := hn
  interval_cases n <;> assumption

/-- The integral weight-four Eisenstein series has constant Fourier expansion modulo five. -/
theorem E₄_mod_five_fourier :
    (ModularFormOver.E₄.Reduce (Int.castRingHom (ZMod 5))).fourier = 1 := by
  ext n
  change (Int.castRingHom (ZMod 5)) (ModularFormOver.coeff ℤ n ModularFormOver.E₄) =
    PowerSeries.coeff n 1
  rw [ModularFormOver.coeff_E₄]
  by_cases hn : n = 0
  · subst n
    simp
  · simp only [hn, ite_false, _root_.map_mul, PowerSeries.coeff_one]
    change (240 : ZMod 5) * _ = 0
    rw [show (240 : ZMod 5) = 0 from by decide, zero_mul]

/-- The relation between `E₄` and one is an element of the Hasse ideal modulo five. -/
theorem E₄_sub_one_mem_hasseIdeal :
    DirectSum.of (ModularFormMod (Int.castRingHom (ZMod 5)) 𝒮ℒ) 4
        (ModularFormOver.E₄.Reduce (Int.castRingHom (ZMod 5))) -
      DirectSum.of (ModularFormMod (Int.castRingHom (ZMod 5)) 𝒮ℒ) 0 1 ∈
        hasseIdeal (Γ := 𝒮ℒ) (Int.castRingHom (ZMod 5)) := by
  rw [of_sub_of_mem_hasseIdeal_iff, one_fourier, E₄_mod_five_fourier]

/-- The Hasse ideal modulo five is nonzero, although each fixed-weight Fourier map is injective. -/
theorem hasseIdeal_mod_five_ne_bot :
    hasseIdeal (Γ := 𝒮ℒ) (Int.castRingHom (ZMod 5)) ≠ ⊥ := by
  intro h
  have hz := E₄_sub_one_mem_hasseIdeal
  rw [h, Ideal.mem_bot] at hz
  have h0 := congrArg
    (fun f : ⨁ k : ℤ, ModularFormMod (Int.castRingHom (ZMod 5)) 𝒮ℒ k => f 0) hz
  have hone : (1 : ModularFormMod (Int.castRingHom (ZMod 5)) 𝒮ℒ 0) = 0 := by
    simpa only [DirectSum.sub_apply, DirectSum.zero_apply, DirectSum.of_eq_same,
      DirectSum.of_eq_of_ne _ _ _ (by decide : (0 : ℤ) ≠ 4), zero_sub, neg_eq_zero] using h0
  have hc := congrArg (fun f : ModularFormMod (Int.castRingHom (ZMod 5)) 𝒮ℒ 0 =>
    f.fourier.coeff 0) hone
  exact (by decide : (1 : ZMod 5) ≠ 0) (by simpa using hc)

end ModularFormMod
