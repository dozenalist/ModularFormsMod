import ModularFormsMod.EventuallyEq

set_option linter.style.header false


noncomputable section ProductDefs

open Finset PowerSeries




variable {α : Type*} [CommRing α]

/-- The power series generating function for `Δ`. Can be instantiated over any commutative ring -/
def discProduct (m : ℕ) : α ⟦X⟧ :=
  X * ∏ i ∈ range m, (1 - X ^ (i + 1)) ^ 24


lemma discProduct_apply (m : ℕ) :
  discProduct m = (X : α⟦X⟧) * ∏ i ∈ range m, (1 - X ^ (i + 1)) ^ 24 := rfl


@[simp] lemma map_discProduct {R S : Type*} [CommRing R] [CommRing S] (g : R →+* S) (n : ℕ) :
    map g (discProduct (α := R) n) = discProduct (α := S) n := by
  simp only [discProduct, map_mul, map_X, map_prod, map_pow, map_sub, map_one]

@[simp] lemma map_coeff_discProduct {R S : Type*} [CommRing R] [CommRing S] (g : R →+* S) (k j : ℕ) :
    g ((coeff (R := R) k) (discProduct j)) = (coeff (R := S) k) (discProduct j) := by
  trans (coeff (R := S) k) (map g (discProduct j))
  · rfl
  · rw [map_discProduct]

@[simp, norm_cast] lemma Int.cast_coeff_discProduct {S : Type*} [CommRing S] (k j : ℕ) :
    ((↑) : ℤ → S) ((coeff k) (discProduct j)) = (coeff (R := S) k) (discProduct j) := by
  trans (Int.castRingHom S) ((coeff k) (discProduct j))
  · rfl
  · rw [map_coeff_discProduct]



section Delta_coeff_le

open Nat PowerSeries Finset

variable {α : Type*}

lemma discProduct_coeff_le' [CommRing α] {n m j : ℕ} (nlm : n ≤ m) (mlj : m ≤ j) :
    coeff (R := α) n (discProduct m) = coeff (R := α) n (discProduct j) := by

  by_cases n0 : n = 0
  · simp [discProduct, n0]

  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero n0

  simp only [discProduct, coeff_succ_X_mul]
  symm; calc
    _ = coeff (R := α) n ((∏ i ∈ Ico 0 m, (1 - X ^ (i + 1)) ^ 24) *
        (∏ i ∈ Ico m j, (1 - X ^ (i + 1)) ^ 24)) := by
      rw [prod_Ico_consecutive, Ico_zero_eq_range]
      exact Nat.zero_le m; exact mlj
    _ = _ := by
      rw [Ico_zero_eq_range, coeff_mul]

      have coeff_eq_ite {k : ℕ} (klt : k < m) :
          coeff (R := α) k (∏ i ∈ Ico m j, (1 - X ^ (i + 1)) ^ 24) = if k = 0 then 1 else 0 := by
        split_ifs with k0
        rw [k0]; simp

        rw [coeff_prod]; apply sum_eq_zero;
        intro x xin; rw [mem_finsuppAntidiag] at xin

        have exy : ∃ y ∈ Ico m j, x y ≠ 0 ∧ x y < m := by
          contrapose! xin

          intro sum_eq
          contrapose! sum_eq
          have fozer {k} (hk : x k ≠ 0) : k ∈ Ico m j := by
            have : k ∈ x.support := Finsupp.mem_support_iff.mpr hk
            exact sum_eq this

          by_cases ex : ∃ y, x y ≠ 0
          obtain ⟨y, yn0⟩ := ex
          have : y ≥ m := List.left_le_of_mem_range' (fozer yn0)
          apply Nat.ne_of_gt; calc
            _ < m := klt
            _ ≤ x y := xin y (fozer yn0) yn0
            _ ≤ (Ico m j).sum ⇑x := single_le_sum_of_canonicallyOrdered <| fozer yn0



          push Not at ex
          suffices (Ico m j).sum ⇑x = 0 by symm; rwa[this]
          exact sum_eq_zero (λ y _ ↦ ex y)

        obtain ⟨y, yin, xyn0, xylm⟩ := exy
        rw [prod_eq_zero]; use yin
        rw [coeff_pow]
        set f : ℕ → α := fun n ↦ (coeff (R := α) n) (1 - X ^ (y + 1)) with hf
        trans ∑ l ∈ (range 24).finsuppAntidiag (x y), ∏ i ∈ range 24, f (l i); rfl


        rw [hf]; dsimp; apply sum_eq_zero; intro z zin
        obtain ⟨zin, supp⟩ := by simpa using zin

        have exb : ∃ b ∈ range 24, z b > 0 := by
          contrapose! zin
          have : (range 24).sum z = 0 := sum_eq_zero λ x h ↦ eq_zero_of_le_zero (zin x h)
          symm; rwa [this]
        obtain ⟨b, bin, bn0⟩ := exb

        rw [prod_eq_zero bin]

        have ble : z b < y := by
          have : z b ≤ (range 24).sum z := single_le_sum_of_canonicallyOrdered bin
          have : m ≤ y := by rw [mem_Ico] at yin; exact yin.1
          omega

        simp only [map_sub, coeff_one]; rw [ite_eq_right (Nat.ne_of_gt bn0)]
        simp only [zero_sub, neg_eq_zero, coeff_pow]

        apply sum_eq_zero; intro x xsum
        have exc : ∃ c ∈ range (y + 1), x c < 1 := by
          contrapose! xsum; simp only [mem_finsuppAntidiag, And.comm, not_and]
          intro xin; apply Nat.ne_of_gt
          have : (range (y + 1) ).sum 1 ≤ (range (y + 1)).sum x := sum_le_sum <| by simpa using xsum
          simp only [Pi.one_apply, sum_const, card_range, smul_eq_mul, mul_one, Order.add_one_le_iff] at this
          omega

        obtain ⟨c, cin, c0⟩ := exc; rw [lt_one_iff] at c0
        rw [prod_eq_zero cin]
        rw [c0, coeff_zero_X]


      calc
        _ = ∑ p ∈ antidiagonal n, (coeff (R := α) p.1) (∏ i ∈ range m, (1 - X ^ (i + 1)) ^ 24) *
            if p.2 = 0 then 1 else 0 := by
          congr! with p pin
          have plt : p.2 < m := by
            have : p.2 ≤ n := HasAntidiagonal.antidiagonal.snd_le pin
            omega
          rw [coeff_eq_ite plt]

        _ =  ∑ x ∈ {(n,0)}, (coeff (R := α) x.1) (∏ i ∈ range m, (1 - X ^ (i + 1)) ^ 24) := by
          simp only [mul_ite, mul_one, mul_zero, sum_ite, sum_const_zero, add_zero]
          congr with x; simp only [mem_filter, mem_antidiagonal, mem_singleton]
          grind

        _ = _ := by simp only [sum_singleton]


theorem discProduct_coeff_le [CommRing α] {n m j : ℕ} (nlm : n ≤ m) (nlj : n ≤ j) :
    coeff (R := α) n (discProduct m) = coeff (R := α) n (discProduct j) :=
  (m.le_total j).casesOn
    (discProduct_coeff_le' nlm · )
    (.symm <| discProduct_coeff_le' nlj ·)

lemma coeff_sum_X_pow [Semiring α] {n N : ℕ} {a : ℕ → α} (h : n < N) :
    coeff n (∑ i ∈ range N, C (a i) * (X : α⟦X⟧) ^ i ) = a n := by
  simpa using (not_lt_of_ge · h |>.elim)


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
