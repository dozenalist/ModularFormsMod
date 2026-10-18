import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.Ideal.NatInt
import Mathlib.RingTheory.Int.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.GroupWithZero.Invertible
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.Algebra.Algebra.Rat
import Mathlib.Algebra.CharP.Algebra

/-!
# Localizations of the integers and reduction modulo a prime

`PInteger p`, written `ℤ(p)`, is the localization of `ℤ` at the prime ideal `pℤ`.
It represents rational numbers whose denominators are prime to `p`. This file
constructs embeddings into characteristic-zero fields, reduction to `ZMod p`,
and fraction constructors. It also provides the notation `ℤ[1/z]`, its canonical
maps, and invertibility instances used for modular forms over coefficient rings.
-/



variable (p : ℕ) [Fact p.Prime]

noncomputable section


/-- For prime `p`, the principal ideal `pℤ` is prime. -/
instance primeIdeal_isPrime : (Ideal.span {(p : ℤ)}).IsPrime :=
  Ideal.isPrime_span_singleton_of_prime <|
    Nat.prime_iff_prime_int.mp Fact.out


/-- The valuation ring of `ℚ` at the prime ideal `p`. -/
abbrev PInteger := Localization.AtPrime (Ideal.span {(p : ℤ)})

namespace PInteger

scoped notation "ℤ(" p:max ")"  => PInteger p

/-- The localization at a prime ideal inherits a commutative ring structure. -/
@[instance_reducible] def commRing : CommRing (ℤ(p)) := inferInstance

variable {p : ℕ} [Fact p.Prime]

/-- The canonical embedding of the p-local integers into `ℂ`, obtained by first mapping into `ℚ`.
-/
noncomputable def toComplex : ℤ(p) →+* ℂ :=
  (Rat.castHom ℂ).comp (IsLocalization.map (M := ((Ideal.span {(p : ℤ)})).primeCompl)
    (T := nonZeroDivisors ℚ) (S := Localization.AtPrime (Ideal.span {(p : ℤ)})) (Q := ℚ)
    (Int.castRingHom ℚ) (by
      intro x hx
      apply mem_nonZeroDivisors_iff_ne_zero.mpr
      intro hzero
      apply hx
      have hxzero : (x : ℤ) = 0 := by
        change (x : ℚ) = 0 at hzero
        exact_mod_cast hzero
      simp [hxzero]))

/-! The natural maps out of the localization. -/

/-- The canonical embedding of the local integers `ℤ(p)` into `ℚ`. -/
noncomputable def toRat : ℤ(p) →+* ℚ :=
  IsLocalization.map (M := (Ideal.span {(p : ℤ)}).primeCompl)
    (T := nonZeroDivisors ℚ) (S := Localization.AtPrime (Ideal.span {(p : ℤ)}))
    (Q := ℚ) (Int.castRingHom ℚ) (by
      intro x hx
      apply mem_nonZeroDivisors_iff_ne_zero.mpr
      intro hzero
      apply hx
      have hq : (x : ℚ) = 0 := by simpa using hzero
      have hxzero : (x : ℤ) = 0 := by exact_mod_cast hq
      simp [hxzero])

/-- The map from p-local integers into `ℚ` is injective. -/
theorem toRat_injective : Function.Injective (toRat (p := p)) := by
  exact IsLocalization.map_injective_of_injective' (M := (Ideal.span {(p : ℤ)}).primeCompl)
    (Rₘ := Localization.AtPrime (Ideal.span {(p : ℤ)})) (Sₘ := ℚ)
    (hf := by
      intro x hx
      apply mem_nonZeroDivisors_iff_ne_zero.mpr
      intro hzero
      apply hx
      have hxzero : (x : ℤ) = 0 := by
        change (x : ℚ) = 0 at hzero
        exact_mod_cast hzero
      simp [hxzero])
    (hN := by simp)
    (hf' := Int.cast_injective)

/-- The canonical map from the local integers to `ℂ` is injective. -/
theorem toComplex_injective : Function.Injective (toComplex (p := p)) := by
  intro x y h
  apply toRat_injective
  exact (Rat.castHom ℂ).injective h


instance : CharZero ℤ(p) where
  cast_injective m n h := by
    have hq : (m : ℚ) = n := by
      have h' := congrArg (toRat (p := p)) h
      simpa [toRat] using h'
    exact Nat.cast_injective hq

instance : Algebra (ℤ(p)) ℚ := toRat.toAlgebra

instance (R) [DivisionRing R] [CharZero R] : Algebra ℤ(p) R :=
  Algebra.compHom R toRat

instance (R) [Field R] [CharZero R] [Algebra R ℂ] :
    IsScalarTower (ℤ(p)) R ℂ := by
  apply IsScalarTower.of_algebraMap_eq
  intro x
  change algebraMap ℚ ℂ (toRat (p := p) x) =
    algebraMap R ℂ (algebraMap ℚ R (toRat (p := p) x))
  exact IsScalarTower.algebraMap_apply ℚ R ℂ (toRat (p := p) x)

instance : IsScalarTower ℤ ℤ(p) ℂ := inferInstance

/-- Compatibility for the scalar actions supplied by the algebra structures. -/
instance intAlgebraScalarTower :
    @IsScalarTower ℤ ℤ(p) ℂ
      (inferInstance : Algebra ℤ ℤ(p)).toSMul
      (inferInstance : Algebra ℤ(p) ℂ).toSMul
      (inferInstance : Algebra ℤ ℂ).toSMul := by
  apply IsScalarTower.of_algebraMap_eq
  intro n
  simp

instance (R) [Field R] [CharZero R] : FaithfulSMul ℤ(p) R :=
  (faithfulSMul_iff_algebraMap_injective _ _).2
    (show Function.Injective (Rat.cast ∘ ⇑(toRat (p := p))) from
      fun _ _ => by simpa using fun h => toRat_injective h)


/-! Reduction modulo `p`; denominators in the localization are units modulo `p`. -/

/-- Reduce a local integer modulo `p` by inverting its denominator in `ZMod p`. -/
noncomputable def reduce : ℤ(p) →+* ZMod p :=
  IsLocalization.lift (M := (Ideal.span {(p : ℤ)}).primeCompl)
    (g := Int.castRingHom (ZMod p)) (fun s => by
      refine (isUnit_iff_ne_zero (G₀ := ZMod p)).2 ?_
      intro hs
      have hdvd : (p : ℤ) ∣ (s : ℤ) :=
        (ZMod.intCast_zmod_eq_zero_iff_dvd (s : ℤ) p).1 hs
      have hs' : (s : ℤ) ∈ Ideal.span {(p : ℤ)} := by
        simpa [Ideal.mem_span_singleton] using hdvd
      exact s.2 hs')

instance : Coe (PInteger p) (ZMod p) where
  coe := reduce

@[simp] theorem reduce_intCast (z : ℤ) :
    reduce (algebraMap ℤ ℤ(p) z) = (z : ZMod p) := by
  simp [reduce]

@[simp] theorem reduce_natCast (n : ℕ) :
    reduce (n : ℤ(p)) = (n : ZMod p) := by
  simp

@[simp] theorem reduce_zero : reduce (0 : ℤ(p)) = 0 := map_zero _

@[simp] theorem reduce_one : reduce (1 : ℤ(p)) = 1 := map_one _

theorem reduce_add (x y : ℤ(p)) :
    reduce (x + y) = reduce x + reduce y := map_add _ _ _

theorem reduce_mul (x y : ℤ(p)) :
    reduce (x * y) = reduce x * reduce y := map_mul _ _ _

/-- Every residue class modulo `p` is the reduction of a local integer. -/
theorem reduce_surjective : Function.Surjective (reduce (p := p)) := by
  intro x
  obtain ⟨z, rfl⟩ := ZMod.intCast_surjective x
  exact ⟨algebraMap ℤ ℤ(p) z, reduce_intCast z⟩

/-- Construct a `p`-integer as a fraction with denominator coprime to `p`. -/
def mk (a b : ℤ) (hb : ¬ ↑p ∣ b) : PInteger p :=
  IsLocalization.mk' (M := (Ideal.span {(p : ℤ)}).primeCompl)
    _ a ⟨b, fun h => hb <| Ideal.mem_span_singleton.mp h⟩

/-- Construct a local integer from a rational number with nonnegative p-adic valuation. -/
def mk' (q : ℚ) (hq : padicValRat p q ≥ 0) : PInteger p :=
  mk q.num (q.den : ℤ) (by
    intro hden
    have hden' : p ∣ q.den := by exact_mod_cast hden
    have hnum : ¬ (p : ℤ) ∣ q.num := by
      intro hnum
      have hnum' : p ∣ q.num.natAbs := Int.natCast_dvd.mp hnum
      have hpd : p ∣ Nat.gcd q.num.natAbs q.den := Nat.dvd_gcd hnum' hden'
      rw [Nat.Coprime.gcd_eq_one q.reduced] at hpd
      exact (Fact.out : Nat.Prime p).ne_one (Nat.dvd_one.mp hpd)
    have hval : padicValInt p q.num = 0 := padicValInt.eq_zero_of_not_dvd hnum
    have hq' : (0 : ℤ) - (padicValNat p q.den : ℤ) ≥ 0 := by
      simpa [padicValRat_def, hval] using hq
    have hdenval : (1 : ℤ) ≤ (padicValNat p q.den : ℤ) := by
      have h := one_le_padicValNat_of_dvd q.den_ne_zero hden'
      exact_mod_cast h
    omega)


open Rat


/-- The fraction constructor `mk a b hb` maps to the rational fraction `a /. b`. -/
theorem toRat_mk (a b : ℤ) (hb : ¬ ↑p ∣ b) : toRat (mk a b hb) = a /. b := by
  let hmap : (Ideal.span {(p : ℤ)}).primeCompl ≤
      (nonZeroDivisors ℚ).comap (Int.castRingHom ℚ) := by
    intro x hx
    apply mem_nonZeroDivisors_iff_ne_zero.mpr
    intro hzero
    apply hx
    have hq : (x : ℚ) = 0 := by simpa using hzero
    have hxzero : (x : ℤ) = 0 := by exact_mod_cast hq
    simp [hxzero]
  change IsLocalization.map (M := (Ideal.span {(p : ℤ)}).primeCompl)
      (T := nonZeroDivisors ℚ) (S := Localization.AtPrime (Ideal.span {(p : ℤ)}))
      (Q := ℚ) (Int.castRingHom ℚ) hmap
      (IsLocalization.mk' _ a ⟨b, by
        intro h
        exact hb <| Ideal.mem_span_singleton.mp h⟩) = _
  rw [IsLocalization.map_mk']
  rw [IsFractionRing.mk'_eq_div]
  rw [Rat.divInt_eq_div]
  simp

/-- The rational image of `mk' q hq` is the original number `q`. -/
theorem toRat_mk' (q : ℚ) (hq : padicValRat p q ≥ 0) : toRat (mk' q hq) = q := by
  rw [mk']
  rw [toRat_mk (p := p)]
  exact Rat.num_divInt_den q

/-- The image of a local fraction in a characteristic-zero division ring is the corresponding
fraction. -/
@[simp] theorem algebraMap_mk (a b : ℤ) (hb : ¬ ↑p ∣ b)
  {R} [DivisionRing R] [CharZero R] :
    algebraMap ℤ(p) R (mk a b hb) = a /. b := by
  change algebraMap ℚ R (toRat (mk a b hb)) = _
  rw [toRat_mk]
  simp

/-- The image of `mk' q hq` in a characteristic-zero division ring is the cast of `q`. -/
@[simp] theorem algebraMap_mk' (q : ℚ) (hq : padicValRat p q ≥ 0)
  {R} [DivisionRing R] [CharZero R] :
    algebraMap ℤ(p) R (mk' q hq) = q := by
  change algebraMap ℚ R (toRat (mk' q hq)) = _
  rw [toRat_mk']
  rfl


end PInteger

section Localization.Away

open PInteger

private abbrev LocalℤAway (z : ℤ) : Type := Localization.Away z

scoped[PInteger] notation "ℤ[1/" z:max "]" => LocalℤAway z


variable (R) [CommRing R] {z : ℤ} [Invertible (z : R)]

/-- The canonical map `ℤ[1/z] →+* R` when the image of `z` is invertible in `R`. -/
noncomputable def IsLocalization.Away.Intlift : ℤ[1/z] →+* R :=
  IsLocalization.Away.lift z (g := Int.castRingHom R)
    (by rw [eq_intCast]; exact isUnit_of_invertible (z : R))

/-- The canonical map out of `ℤ[1/z]` is injective in characteristic zero. -/
theorem IsLocalization.Away.Intlift_injective [CharZero R] :
    Function.Injective (IsLocalization.Away.Intlift (R := R) (z := z)) := by
  have hzR : (z : R) ≠ 0 := (isUnit_of_invertible (z : R)).ne_zero
  have hz : z ≠ 0 := by
    intro hz
    exact hzR (by simp [hz])
  have hlocal : Function.Injective
      (algebraMap ℤ (Localization.Away (z : ℤ))) :=
    IsLocalization.injective (Localization.Away (z : ℤ))
      (powers_le_nonZeroDivisors_of_noZeroDivisors hz)
  rw [IsLocalization.Away.Intlift, IsLocalization.Away.lift,
    IsLocalization.lift_injective_iff]
  intro a b
  constructor
  · intro hab
    have hab' : a = b := hlocal hab
    simp [hab']
  · intro hab
    have hab' : a = b := Int.cast_injective hab
    simp [hab']

instance : Algebra ℤ[1/z] R :=
  (IsLocalization.Away.Intlift R).toAlgebra

instance [CharZero R] : FaithfulSMul ℤ[1/z] R :=
  (faithfulSMul_iff_algebraMap_injective _ _).2
    (IsLocalization.Away.Intlift_injective R)

instance (R) [DivisionRing R] (z : ℤ) [h : NeZero (z : R)] :
    Invertible (z : R) :=
  invertibleOfNonzero h.out

instance (R) [DivisionRing R] [CharZero R] (z : ℤ) [h : NeZero z] :
    Invertible (z : R) :=
  invertibleOfNonzero (by simpa only [ne_eq, Int.cast_eq_zero] using h.out)


instance (R) [CommRing R] [CharZero R] [Algebra R ℂ] {z : ℤ}
    [Invertible (z : R)] [NeZero z] : IsScalarTower ℤ[1/z] R ℂ := by
  apply IsScalarTower.of_algebraMap_eq'
  apply IsLocalization.ringHom_ext (M := Submonoid.powers (z : ℤ))
  ext n
  simp only [eq_intCast]


instance {z : ℤ} [NeZero z] : IsScalarTower ℤ ℤ[1/z] ℂ := inferInstance

/-- Compatibility for the scalar actions supplied by the algebra structures. -/
instance IsLocalization.Away.intAlgebraScalarTower {z : ℤ} [NeZero z] :
    @IsScalarTower ℤ ℤ[1/z] ℂ
      (inferInstance : Algebra ℤ ℤ[1/z]).toSMul
      (inferInstance : Algebra ℤ[1/z] ℂ).toSMul
      (inferInstance : Algebra ℤ ℂ).toSMul := by
  apply IsScalarTower.of_algebraMap_eq
  intro n
  simp

instance [h : NeZero z] : CharZero ℤ[1/z] :=
  charZero_of_injective_ringHom (IsLocalization.injective _ <|
    powers_le_nonZeroDivisors_of_noZeroDivisors h.out)


instance {z : ℤ} [NeZero z] : Invertible (z : ℤ[1/z]) := by
  refine invertibleOfRightInverse
    (a := (z : ℤ[1/z]))
    (b := IsLocalization.Away.invSelf (S := ℤ[1/z]) z) ?_
  simpa only [eq_intCast] using
    (IsLocalization.Away.mul_invSelf (S := ℤ[1/z]) z)

/-- The numeral form of the inverse of the localized integer `6`. -/
instance : Invertible (6 : ℤ[1/6]) := by
  convert (inferInstance : Invertible ((6 : ℤ) : ℤ[1/6])) using 1
  norm_num

instance (R) [CommRing R] [Invertible (6 : R)] : Invertible (1728 : R) := by
  refine invertibleOfRightInverse (a := (1728 : R))
    (b := (27 : R) * (⅟ (6 : R)) ^ 6) ?_
  calc
    (1728 : R) * (27 * (⅟ (6 : R)) ^ 6) = (6 : R) ^ 6 * (⅟ (6 : R)) ^ 6 := by ring
    _ = (6 * ⅟ (6 : R)) ^ 6 := (mul_pow _ _ _).symm
    _ = 1 := by rw [mul_invOf_self, one_pow]

/-- A prime at least five, packaged for typeclass inference. -/
class isLargePrime (ℓ : ℕ) where [Prime : ℓ.Prime] [AtLeastFive : ℓ ≥ 5]

/-- A prime at least thirteen, packaged for typeclass inference. -/
class isLargerPrime (ℓ : ℕ) where [Prime : ℓ.Prime] [AtLeastThirteen : ℓ ≥ 13]

instance (ℓ) [h : isLargePrime ℓ] : Fact (ℓ.Prime) := ⟨h.Prime⟩
instance (ℓ) [h : isLargePrime ℓ] : Fact (ℓ ≥ 5) := ⟨h.AtLeastFive⟩
instance (ℓ) [h : isLargePrime ℓ] : ℓ.AtLeastTwo := ⟨by grind [h.AtLeastFive]⟩
instance (ℓ) [h : isLargerPrime ℓ] : Fact (ℓ.Prime) := ⟨h.Prime⟩
instance (ℓ) [h : isLargerPrime ℓ] : Fact (ℓ ≥ 13) := ⟨h.AtLeastThirteen⟩
instance (ℓ) [h : isLargerPrime ℓ] : isLargePrime ℓ :=
  {Prime := h.Prime, AtLeastFive := by grind [h.AtLeastThirteen]}
instance (ℓ) [h : isLargerPrime ℓ] : ℓ.AtLeastTwo := ⟨by grind [h.AtLeastThirteen]⟩
instance (ℓ) [Fact (ℓ.Prime)] [Fact (ℓ ≥ 5)] : isLargePrime ℓ :=
  {Prime := Fact.out, AtLeastFive := Fact.out}


namespace PInteger

instance [isLargePrime p] : Invertible (6 : ℤ(p)) := by
  have hnot : ¬ (p : ℤ) ∣ (6 : ℤ) := by
    intro h
    have hnat : p ∣ 6 := by exact_mod_cast h
    have hp : p.Prime := Fact.out
    have hprod : p ∣ 2 * 3 := by simpa using hnat
    rcases hp.dvd_mul.mp hprod with h2 | h3
    · have hp_le : p ≤ 2 := Nat.le_of_dvd (by decide) h2
      have hp_ge : 5 ≤ p := isLargePrime.AtLeastFive
      omega
    · have hp_le : p ≤ 3 := Nat.le_of_dvd (by decide) h3
      have hp_ge : 5 ≤ p := isLargePrime.AtLeastFive
      omega
  have hden : (6 : ℤ) ∈ (Ideal.span {(p : ℤ)}).primeCompl := by
    change (6 : ℤ) ∉ Ideal.span {(p : ℤ)}
    simpa [Ideal.mem_span_singleton] using hnot
  refine invertibleOfRightInverse (a := (6 : ℤ(p)))
    (b := IsLocalization.mk' ℤ(p) (1 : ℤ)
      (⟨6, hden⟩ : (Ideal.span {(p : ℤ)}).primeCompl)) ?_
  simpa only [eq_intCast, map_one, Int.cast_ofNat, Nat.cast_ofNat] using
    (IsLocalization.mk'_spec' ℤ(p) (1 : ℤ)
      (⟨6, hden⟩ : (Ideal.span {(p : ℤ)}).primeCompl))



end PInteger
