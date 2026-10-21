/-
Copyright (c) 2026 Carter Hastings. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carter Hastings
-/

module

public import ModularFormsMod.EventuallyEq
public import Mathlib.RingTheory.PowerSeries.Order

/-!
# Finite products for the modular discriminant

`discProduct m` is the finite product `X * ∏ i < m, (1 - X^(i + 1))^24`.
Its coefficients commute with ring homomorphisms and stabilize as `m` grows.
The final theorem expresses this stabilization using `PowerSeries.eventuallyEq`.
-/

@[expose] public section


noncomputable section ProductDefs

open Finset PowerSeries


variable {α : Type*} [CommRing α]

/-- The finite product `X * ∏ i < m, (1 - X^(i + 1))^24` approximating the Fourier
expansion of `Δ`, defined over any commutative ring. -/
def discProduct (m : ℕ) : α ⟦X⟧ :=
  X * ∏ i ∈ range m, (1 - X ^ (i + 1)) ^ 24


lemma discProduct_apply (m : ℕ) :
  discProduct m = (X : α⟦X⟧) * ∏ i ∈ range m, (1 - X ^ (i + 1)) ^ 24 := rfl


/-- Finite discriminant products commute with coefficientwise ring homomorphisms. -/
@[simp] lemma map_discProduct {R S : Type*} [CommRing R] [CommRing S] (g : R →+* S) (n : ℕ) :
    map g (discProduct (α := R) n) = discProduct (α := S) n := by
  simp only [discProduct, map_mul, map_X, map_prod, map_pow, map_sub, map_one]

/-- A ring homomorphism sends each finite discriminant-product coefficient to the corresponding
coefficient over the target. -/
@[simp] lemma map_coeff_discProduct {R S : Type*} [CommRing R] [CommRing S]
    (g : R →+* S) (k j : ℕ) :
    g ((coeff (R := R) k) (discProduct j)) = (coeff (R := S) k) (discProduct j) := by
  trans (coeff (R := S) k) (map g (discProduct j))
  · rfl
  · rw [map_discProduct]

/-- The coefficients of a finite discriminant product over any commutative ring are casts of its
integer coefficients. -/
@[simp, norm_cast] lemma Int.cast_coeff_discProduct {S : Type*} [CommRing S] (k j : ℕ) :
    ((↑) : ℤ → S) ((coeff k) (discProduct j)) = (coeff (R := S) k) (discProduct j) := by
  trans (Int.castRingHom S) ((coeff k) (discProduct j))
  · rfl
  · rw [map_coeff_discProduct]


section Delta_coeff_le

open Nat PowerSeries Finset

variable {α : Type*}

/-- Increasing the product cutoff beyond degree `n` leaves its degree-`n` coefficient unchanged. -/
lemma discProduct_coeff_le' [CommRing α] {n m j : ℕ} (nlm : n ≤ m) (mlj : m ≤ j) :
    coeff (R := α) n (discProduct m) = coeff (R := α) n (discProduct j) := by
  nontriviality α
  induction j, mlj using Nat.le_induction with
  | base => rfl
  | succ j hj ih =>
    have hc := PowerSeries.coeff_mul_prod_one_sub_of_lt_order n (range 24)
      (discProduct (α := α) j) (fun _ : ℕ => X ^ (j + 1)) (by
        intro i hi
        rw [PowerSeries.order_X_pow]
        exact_mod_cast (show n < j + 1 by omega))
    rw [prod_const, card_range] at hc
    simpa only [discProduct, prod_range_succ, mul_assoc] using ih.trans hc.symm

/-- The coefficient of degree `n` is independent of the cutoff once both cutoffs are at least
`n`. -/
theorem discProduct_coeff_le [CommRing α] {n m j : ℕ} (nlm : n ≤ m) (nlj : n ≤ j) :
    coeff (R := α) n (discProduct m) = coeff (R := α) n (discProduct j) :=
  (m.le_total j).casesOn
    (discProduct_coeff_le' nlm · )
    (.symm <| discProduct_coeff_le' nlj ·)

/-- A truncated power series with prescribed coefficients has coefficient `a n` below the
truncation bound. -/
lemma coeff_sum_X_pow [Semiring α] {n N : ℕ} {a : ℕ → α} (h : n < N) :
    coeff n (∑ i ∈ range N, C (a i) * (X : α⟦X⟧) ^ i ) = a n := by
  simpa using (not_lt_of_ge · h |>.elim)


/-- The finite discriminant products eventually agree coefficientwise with the partial sums of
their stabilized coefficients. -/
theorem discProduct_eventually_sum [CommRing α] :
    (discProduct ·) ⟶ (∑ i ∈ range ·, (discProduct (α := α) i).coeff i • (X : α⟦X⟧) ^ i) := by
  intro n
  use n + 1; intro k kle j jg
  have : j > k := Nat.lt_of_le_of_lt kle jg
  trans (PowerSeries.coeff (R := α) k) (∑ x ∈ range j,
    C ((PowerSeries.coeff (R := α) x) (discProduct x)) * X ^ x)
  · set f : ℕ → α := fun n ↦ (PowerSeries.coeff (R := α) n) (discProduct n) with feq
    rw [coeff_sum_X_pow (a := f) this, feq]; symm
    exact discProduct_coeff_le k.le_refl this.le
  · congr! 2 with x -; simp only [map_coeff_discProduct, smul_eq_C_mul]
