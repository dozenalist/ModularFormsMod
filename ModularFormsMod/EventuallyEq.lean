import Mathlib.RingTheory.PowerSeries.Basic

/-!
# Eventual agreement of power-series coefficients

`PowerSeries.eventuallyEq` compares sequences whose coefficients agree eventually
in every bounded degree. The relation is an equivalence and is preserved by
addition, multiplication, and natural powers.
-/

open PowerSeries Finset Finset.HasAntidiagonal

variable {α : Type*}

namespace PowerSeries

/-- Two sequences of power series eventually agree if, for every degree bound `n`,
there is an index beyond which all their coefficients in degrees at most `n` agree. -/
def eventuallyEq [Semiring α] (f h : ℕ → α⟦X⟧) : Prop :=
  ∀ n, ∃ m, ∀ k ≤ n, ∀ j ≥ m, coeff k (f j) = coeff k (h j)

@[inherit_doc]
scoped infixl : 25 (priority := high) " ⟶ " => eventuallyEq

/-- Coefficientwise eventual agreement is reflexive. -/
@[refl]
theorem eventuallyEq.refl [Semiring α] (f : ℕ → α⟦X⟧) : f ⟶ f :=
  fun _ => ⟨0, fun _ _ _ _ => rfl⟩

/-- Coefficientwise eventual agreement is symmetric. -/
@[symm]
theorem eventuallyEq.symm [Semiring α] (f h : ℕ → α⟦X⟧) : (f ⟶ h) → (h ⟶ f) := by
  intro eq n
  obtain ⟨m, fo⟩ := eq n
  use m, fun n ngm j jgm => fo n ngm j jgm |>.symm

/-- Coefficientwise eventual agreement is transitive. -/
@[trans]
theorem eventuallyEq.trans [Semiring α] (f h g : ℕ → α⟦X⟧) :
    (f ⟶ h) → (h ⟶ g) → (f ⟶ g) := by
  intro feq heq n
  obtain ⟨M, fo⟩ := feq n
  obtain ⟨N, ho⟩ := heq n
  use max M N; intro k klen j jgMax
  rw [fo k klen j <| le_of_max_le_left jgMax, ho k klen j <| le_of_max_le_right jgMax]


instance [Semiring α] : IsEquiv (ℕ → α⟦X⟧) eventuallyEq where
  refl := eventuallyEq.refl
  symm := eventuallyEq.symm
  trans := eventuallyEq.trans

/-- Adding eventually agreeing sequences preserves eventual agreement in every bounded degree. -/
@[gcongr]
theorem eventuallyEq_add [Semiring α] {a b c d : ℕ → α⟦X⟧} (hab : a ⟶ b) (hcd : c ⟶ d) :
    a + c ⟶ b + d := by
  intro k
  obtain ⟨M, fo⟩ := hab k
  obtain ⟨N, go⟩ := hcd k
  use max M N; intro n nle j jg
  simp only [Pi.add_apply, map_add]
  rw [fo n nle j <| le_of_max_le_left jg, go n nle j <| le_of_max_le_right jg]

/-- Multiplying eventually agreeing sequences preserves eventual agreement in every bounded
degree. -/
@[gcongr]
theorem eventuallyEq_mul [Semiring α] {a b c d : ℕ → α⟦X⟧} (hab : a ⟶ b) (hcd : c ⟶ d) :
    a * c ⟶ b * d := by
  intro k
  simp only [Pi.mul_apply, coeff_mul]
  obtain ⟨M, fo⟩ := hab k
  obtain ⟨N, go⟩ := hcd k
  use max M N; intro n nle j jg
  apply sum_congr rfl; intro x xin; congr 1
  · apply fo
    · exact antidiagonal.fst_le xin |> trans <| nle -- cool
    · exact le_of_max_le_left jg
  · apply go
    · exact antidiagonal.snd_le xin |> trans <| nle
    · exact le_of_max_le_right jg

/-- Natural powers preserve coefficientwise eventual agreement. -/
@[gcongr]
theorem eventuallyEq_pow [Semiring α] {a b : ℕ → α⟦X⟧} (hab : a ⟶ b) (n : ℕ) :
    a ^ n ⟶ b ^ n := by
  induction n with
  | zero => simp only [pow_zero]; rfl
  | succ => simp only [pow_succ]; gcongr


/-- View a sequence of polynomials as a sequence of formal power series. -/
def lift [Semiring α] (a : ℕ → Polynomial α) : ℕ → α ⟦X⟧ :=
  fun n ↦ ↑(a n)

@[simp] lemma lift_apply [Semiring α] (a : ℕ → Polynomial α) (n : ℕ) :
  lift a n = ↑(a n) := rfl


/-- A sequence eventually agrees with zero exactly when its coefficients in each bounded degree
eventually vanish. -/
theorem eventuallyEq_zero_iff [Semiring α] {a : ℕ → α⟦X⟧} :
    (a ⟶ 0) ↔ ∀ n, ∃ m, ∀ k ≤ n, ∀ j ≥ m, coeff k (a j) = 0 := by
  unfold eventuallyEq; simp only [Pi.zero_apply, map_zero]


-- lemma sum_X_pow_eventually_zero_iff [Semiring α] (f : ℕ → α) :
--     ( (∑ i ∈ range ·, C (f i) * (X : α ⟦X⟧) ^ i) ⟶ 0 ) ↔ f = 0 := by
--   constructor <;> intro h
--   ext n
--   obtain ⟨m, fo⟩ := h n
--   specialize fo n (le_refl n) (max (n + 1) m) (le_max_of_le_right <| le_refl m)
--   have nlt : n < max (n + 1) m := lt_max_of_lt_left <| lt_add_one n
--   simp_all only [Pi.zero_apply, map_zero, coeff_sum_X_pow]
--   intro n
--   simp only [h, map_zero, zero_mul, sum_const_zero, Pi.zero_apply, implies_true, exists_const]


end PowerSeries
