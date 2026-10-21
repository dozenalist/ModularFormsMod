/-
Copyright (c) 2026 Carter Hastings. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carter Hastings
-/

module

public import ModularFormsMod.RamanujanCongruence.KOl.ThetaRelation

/-!
# The shift of a Ramanujan congruence

Kiming--Olsson's argument, specialized throughout to the standard partition
function. The theta relation for a nonzero residue contradicts the strictly
increasing initial part of the theta cycle of `fl p`. Thus every partition
congruence has parameter congruent to `δ p` modulo `p`.

As in the paper, the prime is at least five.
-/

@[expose] public section

noncomputable section

open ModularFormMod ModularFormMod.ZMod

namespace RamanujanCongruence.KOl

variable {p : ℕ} [isLargePrime p]

/-- The standard-partition case of Kiming--Olsson's necessary condition
`24a ≡ 1 (mod p)`, with this project's progression written as `p*n - β`. -/
theorem parameter_eq_delta {β : ℤ} (hβ : RamanujanCongruenceWith p β) :
    (β : ZMod p) = (δ p : ZMod p) := by
  by_contra hne
  have ha : (δ p : ZMod p) - (β : ZMod p) ≠ 0 := sub_ne_zero.mpr (Ne.symm hne)
  have hw := filtration_theta_half (fl p) ha (simpleCongruence_fl hβ)
  have hhalf := prime_half (p := p)
  have hp : 5 ≤ p := isLargePrime.AtLeastFive
  have hfirst : (fl p).Theta.Filtration = 12 * (δ p : ℤ) + (p + 1) := by
    simpa only [show (fl p).Theta_pow 1 = (fl p).Theta.cast (by ring) from rfl,
      Filtration_cast, Nat.cast_one, one_mul] using
      (Filtration_Theta_pow_initial (p := p) (m := 1) (by omega))
  rw [hfirst, Filtration_Theta_pow_initial (le_refl _)] at hw
  have hpos : (1 : ℤ) < ((p + 1) / 2 : ℕ) := by omega
  nlinarith

/-- Every partition congruence modulo a prime at least five is the congruence
at the discriminant shift, up to changing the integer parameter by a multiple of `p`. -/
theorem RamanujanCongruence_iff_delta :
    RamanujanCongruence p ↔ RamanujanCongruenceWith p (δ p) := by
  constructor
  · rintro ⟨β, hβ⟩
    exact congruenceWith_of_cast_eq (by simpa using parameter_eq_delta hβ) hβ
  · exact fun h => ⟨δ p, h⟩

end RamanujanCongruence.KOl
