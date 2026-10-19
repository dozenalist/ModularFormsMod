# ModularFormsMod

A Lean 4 formalization of modular forms over coefficient rings, their coefficientwise reductions, and Ramanujan congruences for the partition function. The development proceeds from modular forms over subrings of `ℂ`, through the algebra and filtration of modular forms modulo a prime, to the classification of Ramanujan partition congruences for primes at least five.

## Modular forms over coefficient rings

[`ModularFormOver`](ModularFormsMod/ModularFormOver) develops modular forms whose Fourier coefficients lie in a chosen ring `R` embedded in `ℂ`.

- **Definitions and Fourier expansions.** `ModularForm.isOver R f` expresses the coefficient condition, and `ModularFormOver R Γ k` bundles a form of weight `k` with that condition. The theory includes arithmetic, extension of coefficient rings, graded ring operations, and determination of forms by their Fourier coefficients. See [Defs](ModularFormsMod/ModularFormOver/Defs.lean) and [Basic](ModularFormsMod/ModularFormOver/Basic.lean).
- **Eisenstein series and the discriminant.** The forms `E₄`, `E₆`, and `Δ` are constructed over `ℤ`, with `1728 Δ = E₄³ - E₆²`. The development also treats rational Eisenstein series and the series of weights `p - 1` and `p + 1` over the local integers `ℤ(p)`. See [Int](ModularFormsMod/ModularFormOver/Int.lean), [Rat](ModularFormsMod/ModularFormOver/Rat.lean), and [PInteger](ModularFormsMod/ModularFormOver/PInteger.lean).
- **Level-one structure.** Monomials in `E₄`, `E₆`, and `Δ` give bases, dimension formulas, and a Sturm bound. When `6` is invertible in `R`, the graded algebra is the polynomial algebra `R[E₄, E₆]`, with generator weights four and six. See [Basis](ModularFormsMod/ModularFormOver/Basis.lean) and [GradedRing](ModularFormsMod/ModularFormOver/GradedRing.lean).
- **Operators.** A normalized Serre derivative preserves coefficient rings without inverting `12` or the cusp width. The Hecke theory treats operators on `Γ₁(N)` preserving the trivial-character forms and their coefficient rings. See [Derivative](ModularFormsMod/ModularFormOver/Derivative.lean) and [Hecke](ModularFormsMod/ModularFormOver/Hecke.lean).

## Reduced modular forms

[`ModularFormMod`](ModularFormsMod/ModularFormMod) works with an arbitrary coefficient homomorphism `r : R →+* S`. A term of `ModularFormMod r Γ k` is a power series over `S` that lifts to the Fourier expansion of a weight-`k` form over `R`.

- **Reduction and base change.** The reduction map, coefficientwise congruences, composition of reductions, and congruence kernels are developed for general coefficient maps. At level one, integral bases give congruence Sturm bounds; surjective reductions give bases over `S` and a tensor-product description by base change. Reduced forms also carry scalars from the effective coefficient ring `R / ker r`. See [Defs](ModularFormsMod/ModularFormMod/Defs.lean), [Kernel](ModularFormsMod/ModularFormMod/Kernel.lean), [Basis](ModularFormsMod/ModularFormMod/Basis.lean), [BaseChange](ModularFormsMod/ModularFormMod/BaseChange.lean), and [Quotient](ModularFormsMod/ModularFormMod/Quotient.lean).
- **Graded and Fourier algebras.** For surjective `r` with `6` invertible in `R`, the level-one graded algebra is polynomial in the reduced `E₄` and `E₆`. Summing Fourier expansions across weights gives `rAlgebra`; the kernel is the Hasse ideal, which records relations between different weights. See [GradedRing](ModularFormsMod/ModularFormMod/GradedRing.lean), [RAlgebra](ModularFormsMod/ModularFormMod/RAlgebra.lean), and [HasseIdeal](ModularFormsMod/ModularFormMod/HasseIdeal.lean).
- **Filtration and operators.** `hasWeight` records the weights in which an expansion admits a lift; filtration is the least such weight for a nonzero form. The normalized Serre derivative descends through reduction, and a general criterion for descending linear operators is applied to Hecke operators. See [Filtration](ModularFormsMod/ModularFormMod/Filtration.lean), [Derivative](ModularFormsMod/ModularFormMod/Derivative.lean), [Operators](ModularFormsMod/ModularFormMod/Operators.lean), and [Hecke](ModularFormsMod/ModularFormMod/Hecke.lean).

### Modulo a prime

[`ModularFormMod/ZMod`](ModularFormsMod/ModularFormMod/ZMod) specializes the theory to finite coefficient rings. At level one modulo a prime `p ≥ 5`, it proves:

- The Eisenstein series `E_{p-1}` and `E_{p+1}` reduce to the constant series `1` and the formal `E₂` series, respectively.
- Their polynomial representatives `Abar` and `Bbar` satisfy differential identities; `Abar` is squarefree, and `Abar` and `Bbar` are relatively prime.
- The kernel of polynomial evaluation at the Fourier expansions of `E₄` and `E₆` is the principal ideal `(Abar - 1)`.
- Divisibility by `Abar` detects a drop in filtration. For nonzero forms, filtration is congruent to the weight modulo `p - 1`, and natural powers multiply filtration by their exponent.
- The theta operator `Θ = q d/dq` raises weight by `p + 1`. Its filtration satisfies `w(Θf) ≤ w(f) + p + 1`, with equality exactly when `p` does not divide `w(f)`.
- The operator `U` extracts coefficients whose indices are divisible by `p`, agrees with the reduction of `T_p` in weights at least two, and satisfies `w(Uf) ≤ p + ⌊(w(f) - 1) / p⌋`.

The main structural results are in [HasseIdeal](ModularFormsMod/ModularFormMod/ZMod/HasseIdeal.lean), [Theta](ModularFormsMod/ModularFormMod/ZMod/Theta.lean), [UOperator](ModularFormsMod/ModularFormMod/ZMod/UOperator.lean), and [Filtration](ModularFormsMod/ModularFormMod/ZMod/Filtration.lean). Here `w` denotes filtration; the convention is `w(0) = 0`.

## Ramanujan partition congruences

[`RamanujanCongruence`](ModularFormsMod/RamanujanCongruence) applies this theory to the partition function `P(n)`. The Lean definition `RamanujanCongruenceWith p β` means that `P(p n - β) ≡ 0 (mod p)` for every integer `n`, with `P(n) = 0` for negative `n`.

The proof uses the reduced discriminant power `fl p = Δ^δ`, where `δ = (p² - 1) / 24`, and its theta cycle:

- [Partition](ModularFormsMod/RamanujanCongruence/Partition.lean) establishes the partition generating function, and [Basic](ModularFormsMod/RamanujanCongruence/Basic.lean) relates it to the discriminant power.
- [KOl](ModularFormsMod/RamanujanCongruence/KOl) formalizes the standard-partition case of the Kiming–Olsson argument: any congruence modulo a prime `p ≥ 5` has `β ≡ δ (mod p)`.
- [AhBo](ModularFormsMod/RamanujanCongruence/AhBo) relates the congruence at this shift to `U(fl p) = 0` and carries out the Ahlgren–Boylan descent argument, excluding primes `p ≥ 13`.

[MainResults](ModularFormsMod/RamanujanCongruence/MainResults.lean) proves the classical congruences

$$
P(5n + 4) \equiv 0 \pmod{5}, \qquad
P(7n + 5) \equiv 0 \pmod{7}, \qquad
P(11n + 6) \equiv 0 \pmod{11},
$$

and proves that no Ramanujan congruence exists for any prime at least thirteen. Together, these results classify the primes `p ≥ 5` admitting a Ramanujan congruence as exactly `5`, `7`, and `11`.

| Result | Lean declaration |
| --- | --- |
| Congruences modulo 5, 7, and 11 | `RamanujanCongruence_5`, `RamanujanCongruence_7`, `RamanujanCongruence_11` |
| Exclusion of primes at least 13 | `not_RamanujanCongruence`, `not_RamanujanCongruence_verbose` |
| Necessary shift modulo a prime at least 5 | `RamanujanCongruence.KOl.parameter_eq_delta` |

## Building and using the library

The project uses the Lean version pinned in [lean-toolchain](lean-toolchain), with mathlib and LeanModularForms as declared in [lakefile.toml](lakefile.toml). With Lean's `elan` toolchain manager installed, run from the repository root:

```sh
lake exe cache get
lake build
```

Import the full library with:

```lean
import ModularFormsMod
```

For the partition congruence results alone, use:

```lean
import ModularFormsMod.RamanujanCongruence.MainResults
```

The project is released under the [Apache 2.0 license](LICENSE).
