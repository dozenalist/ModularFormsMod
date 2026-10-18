import ModularFormsMod.ModularFormOver.Basic
import Mathlib.NumberTheory.Padics.PadicNumbers

/-!
# Preparatory imports for p-adic coefficients

This exploratory file imports modular forms over coefficient rings and p-adic
numbers, and checks the coercion from `ℚ` to `Padic 2`. It currently defines
no modular forms with p-adic coefficients.
-/

set_option linter.style.header false



variable (q : ℚ) (p : Padic 2)
#check (q : Padic 2)
