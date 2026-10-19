/-
Copyright (c) 2026 Carter Hastings. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carter Hastings
-/

import ModularFormsMod.ModularFormMod.ZMod.SquarefreeAbar

/-!
# Relative primality of the Eisenstein polynomials

The second part of Lemma 1.40: `Abar p` and `Bbar p` have no common
irreducible factor. The appropriate notion in this multivariate polynomial
ring is `IsRelPrime`.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

noncomputable section

open PInteger MvPolynomial

namespace ModularFormMod.ZMod

variable (p : ℕ) [isLargePrime p]

/-- Lemma 1.40 (ii): `Abar` and `Bbar` have no common nonunit factor. -/
theorem isRelPrime_Abar_Bbar : IsRelPrime (Abar p) (Bbar p) := by
  apply (UniqueFactorizationMonoid.isRelPrime_iff_no_prime_factors (Abar_ne_zero p)).mpr
  intro q hA hB hq
  obtain ⟨a, ha⟩ := hA
  have hqa : ¬q ∣ a := by
    intro h
    exact hq.not_isUnit (squarefree_Abar p q (by
      rw [ha]
      exact mul_dvd_mul_left q h))
  have hD : q ∣ Del (Abar p) := by simpa only [Del_Abar] using hB
  rw [ha, Del.leibniz, smul_eq_mul] at hD
  have h : q ∣ a * Del q := by
    simpa using hD.sub (dvd_mul_right q (Del a))
  exact irreducible_not_dvd_Del_of_dvd_Abar p hq.irreducible ⟨a, ha⟩
    ((hq.dvd_mul.mp h).resolve_left hqa)

end ModularFormMod.ZMod
