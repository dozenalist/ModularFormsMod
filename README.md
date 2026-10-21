# ModularFormsMod

A Lean 4 formalization of modular forms with coefficients over subrings of `ℂ`, their coefficientwise reductions modulo ring homomorphisms, and a proof classifying the Ramanujan congruences for the partition function following [this paper](https://people.math.sc.edu/boylan/reprints/nomoreramafinal.pdf) [Ah-Bo] by Ahlgren and Boylan. This project also formalizes "Congruences like Ramanujan's for powers of the partition function" [K-Ol] by Kimming and Olson, with results specialized to the standard partition function, as well as Swinnerton-Dyer's original treatment of modular forms modulo a prime in "Modular Functions of One Variable III" [SwD].

## Modular forms over coefficient rings

[`ModularFormOver`](ModularFormsMod/ModularFormOver) provides definitions for modular forms whose q-expansion coefficients lie in a commutative ring `R` embedded in `ℂ`, and provides nice lifts between such modular forms. It defines the Eisenstein series `E₄` and `E₆` as well as the modular discriminant `Δ` as modular forms over `ℤ`. It defines general Eisenstein series `Eis k` as modular forms over `ℚ`. For a prime `ℓ ≥ 5`, it defines `E_{ℓ-1}` and `E_{ℓ+1}` as modular forms over `ℤ(ℓ)`, the localization of `ℤ` at `ℓ`. It proves facts about bases for the space of modular forms over `SL(2, ℤ)`, and provides infrastructure for lifting operators on modular forms (such as hecke operators and the serrre derivative) to modular forms over coefficient rings.

| Lean declaration | Statement |
| --- | --- |
| `ModularForm.isOver R f` | A predicate asserting that the q-expansion of the modular form `f` lies in the image of the algebra map from `R` to `ℂ` |
| `ModularFormOver R Γ k` | Modular forms of level `Γ` and weight `k` that lie over `R` |
| `Basis.G` | The normalized, upper triangular collection `{E₄ ^ a * E₆ ^ b * Δ ^ c }` indexed by the power of `Δ`, which forms a basis for the space of modular forms for    the full modular group over any subring of `ℂ` |
| `Basis.P` | The collection `{E₄ ^ a * E₆ ^ b}`, which forms a basis for the space of modular forms for the full modular group over any ring in which `6` is invertible |


- **Definitions.** `ModularForm.isOver R f` expresses the coefficient condition, and `ModularFormOver R Γ k` bundles a form of weight `k` with that condition. The theory includes arithmetic, extension of coefficient rings, graded ring operations, and determination of forms by their Fourier coefficients. See [Defs](ModularFormsMod/ModularFormOver/Defs.lean) and [Basic](ModularFormsMod/ModularFormOver/Basic.lean).
- **Eisenstein series and the discriminant.** The forms `E₄`, `E₆`, and `Δ` are constructed over `ℤ`, with `1728 Δ = E₄³ - E₆²`. The development also treats rational Eisenstein series and the series of weights `ℓ - 1` and `ℓ + 1` over the local integers `ℤ(ℓ)`. See [Int](ModularFormsMod/ModularFormOver/Int.lean), [Rat](ModularFormsMod/ModularFormOver/Rat.lean), and [PInteger](ModularFormsMod/ModularFormOver/PInteger.lean).
- **Level-one structure.** Monomials in `E₄`, `E₆`, and `Δ` give bases, dimension formulas, and a Sturm bound. When `6` is invertible in `R`, the graded algebra is the polynomial algebra `R[E₄, E₆]`, with generator weights four and six. See [Basis](ModularFormsMod/ModularFormOver/Basis.lean) and [GradedRing](ModularFormsMod/ModularFormOver/GradedRing.lean).
- **Operators.** A normalized Serre derivative preserves coefficient rings without inverting `12` or the cusp width. The Hecke theory treats operators on `Γ₁(N)` preserving the trivial-character forms and their coefficient rings. See [Derivative](ModularFormsMod/ModularFormOver/Derivative.lean) and [Hecke](ModularFormsMod/ModularFormOver/Hecke.lean).

## Reductions modulo ring homomorphisms

[`ModularFormMod`](ModularFormsMod/ModularFormMod) works with an arbitrary coefficient homomorphism `r : R →+* S`. A term of `ModularFormMod r Γ k` is a power series over `S` that lifts to the Fourier expansion of a weight-`k` form over `R`.

- **Reduction and base change.** The reduction map, coefficientwise congruences, composition of reductions, and congruence kernels are developed for general coefficient maps. At level one, integral bases give congruence Sturm bounds; surjective reductions give bases over `S` and a tensor-product description by base change. Reduced forms also carry scalars from the effective coefficient ring `R / ker r`. See [Defs](ModularFormsMod/ModularFormMod/Defs.lean), [Kernel](ModularFormsMod/ModularFormMod/Kernel.lean), [Basis](ModularFormsMod/ModularFormMod/Basis.lean), [BaseChange](ModularFormsMod/ModularFormMod/BaseChange.lean), and [Quotient](ModularFormsMod/ModularFormMod/Quotient.lean).
- **Graded and Fourier algebras.** For surjective `r` with `6` invertible in `R`, the level-one graded algebra is polynomial in the reduced `E₄` and `E₆`. Summing Fourier expansions across weights gives `rAlgebra`; the kernel is the Hasse ideal, which records relations between different weights. See [GradedRing](ModularFormsMod/ModularFormMod/GradedRing.lean), [RAlgebra](ModularFormsMod/ModularFormMod/RAlgebra.lean), and [HasseIdeal](ModularFormsMod/ModularFormMod/HasseIdeal.lean).
- **Filtration and operators.** `hasWeight` records the weights in which an expansion admits a lift; filtration is the least such weight for a nonzero form. The normalized Serre derivative descends through reduction, and a general criterion for descending linear operators is applied to Hecke operators. See [Filtration](ModularFormsMod/ModularFormMod/Filtration.lean), [Derivative](ModularFormsMod/ModularFormMod/Derivative.lean), [Operators](ModularFormsMod/ModularFormMod/Operators.lean), and [Hecke](ModularFormsMod/ModularFormMod/Hecke.lean).

### Reductions modulo a prime

[`ModularFormMod/ZMod`](ModularFormsMod/ModularFormMod/ZMod) specializes the theory to the reduction from mod a prime `ℓ`  `ℤ(ℓ) → ZMod ℓ`. Following [SwD], it proves that at level one modulo a prime `ℓ ≥ 5`:

- The Eisenstein series `E_{ℓ-1}` and `E_{ℓ+1}` reduce to the constant series `1` and the formal `E₂` series, respectively.
- Their polynomial representatives `Abar` and `Bbar` satisfy differential identities; `Abar` is squarefree, and `Abar` and `Bbar` are relatively prime.
- The kernel of polynomial evaluation at the Fourier expansions of `E₄` and `E₆` is the principal ideal `(Abar - 1)`.
- Divisibility by `Abar` detects a drop in filtration. For nonzero forms, filtration is congruent to the weight modulo `p - 1`, and natural powers multiply filtration by their exponent.
- The theta operator `Θ = q d/dq` raises weight by `ℓ + 1`. Its filtration satisfies `w(Θf) ≤ w(f) + ℓ + 1`, with equality exactly when `p` does not divide `w(f)`.
- The operator `U` extracts coefficients whose indices are divisible by `ℓ`, agrees with the reduction of `T_ℓ` in weights at least two, and satisfies `w(Uf) ≤ p + ⌊(w(f) - 1) / p⌋`.

The main structural results are in [HasseIdeal](ModularFormsMod/ModularFormMod/ZMod/HasseIdeal.lean), [Theta](ModularFormsMod/ModularFormMod/ZMod/Theta.lean), [UOperator](ModularFormsMod/ModularFormMod/ZMod/UOperator.lean), and [Filtration](ModularFormsMod/ModularFormMod/ZMod/Filtration.lean). Here `w` denotes filtration; the convention is `w(0) = 0`.

## Ramanujan's partition congruences

Here, [Ah-Bo] refers to [Arithmetic Properties of the Partition function](https://people.math.sc.edu/boylan/reprints/nomoreramafinal.pdf), [K-Ol] refers to "Congruences like Ramanujan's for powers of the partition function", and [SwD] refers to Swinnerton-Dyer's work in "Modular Functions of One Variable III".

[Ah-Bo] is formalized in [AhBo](ModularFormsMod/RamanujanCongruence/AhBo) and [K-Ol] is formalized in [KOl](ModularFormsMod/RamanujanCongruence/KOl), with results common to both of them in [Basic](ModularFormsMod/RamanujanCongruence/Basic). Together, these results combine to give a complete classification for complete classification for congruences like Ramanujan's for the partition function, contained in [MainResults](ModularFormsMod/RamanujanCongruence/MainResults)

[`RamanujanCongruence`](ModularFormsMod/RamanujanCongruence) applies the theory of modular forms mod `\ell` to the partition function `p(n)`. The Lean definition `RamanujanCongruenceWith p β` means that `p(ℓn - β) ≡ 0 (mod p)` for every integer `n`, with `p(n) = 0` for negative `n`.

The proof uses the reduced discriminant power `fl p = Δ^δ`, where `δ = (ℓ² - 1) / 24`, and its theta cycle:

- [Partition](ModularFormsMod/RamanujanCongruence/Partition.lean) establishes the partition generating function, and [Basic](ModularFormsMod/RamanujanCongruence/Basic.lean) relates it to the discriminant power.
- [KOl](ModularFormsMod/RamanujanCongruence/KOl) formalizes the standard-partition case of the Kiming–Olsson argument: any congruence modulo a prime `p ≥ 5` has `β ≡ δ (mod p)`.
- [AhBo](ModularFormsMod/RamanujanCongruence/AhBo) relates the congruence at this shift to `U(fl ℓ) = 0` and carries out the Ahlgren–Boylan descent argument, excluding primes `p ≥ 13`.

[MainResults](ModularFormsMod/RamanujanCongruence/MainResults.lean) proves the classical congruences

$$
p(5n + 4) \equiv 0 \pmod{5}, \qquad
p(7n + 5) \equiv 0 \pmod{7}, \qquad
p(11n + 6) \equiv 0 \pmod{11},
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

## Attribution
This repository was adapted from a [previous formalization project](https://github.com/dozenalist/Partitions-mod-p) of mine, which formalized the arguments of [Ah-Bo], as well as much of the structure surrounding the reduction of modular forms modulo a prime by hand -- without the use of AI. In the process of connecting those results to Mathlib using AI assistance, I was motivated to re-formalize my work from the ground up and in more generality. The files [Defs](ModularFormsMod/ModularFormOver/Defs.lean) and [Basic](ModularFormsMod/ModularFormOver/Basic.lean) were written entirely by me, without AI assistance. Most of everything else in this project was written by first formalizing the main definitions and statements, and then prompting Codex to fill in the gaps, making use of code from my previous project. Codex was used also to generate documentation for many files and declarations.

## Dependencies
This project depends on Mathlib as well as Chris Birbeck's repository [LeanModularForms](https://github.com/CBirkbeck/LeanModularForms) for the definitions of Hecke Operators and facts about their q-expansions.
