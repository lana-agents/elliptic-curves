/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import EllipticCurves.Torsion.DivisionPolynomialEval

/-!
# The `y`-coordinate division-polynomial numerators `Ωₙ` and their factorisation

Mathlib's `Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Basic.lean` develops the
`x`-coordinate division polynomials (`ψ₂, Ψ₂Sq, Ψ₃, preΨ₄, ΨSq, Ψ, Φ, ψ, φ`) but explicitly leaves
the *`y`-coordinate* division polynomials `ωₙ` as a `TODO`. The sibling files
`EllipticCurves/Torsion/OmegaTwo.lean` and `EllipticCurves/Torsion/OmegaThree.lean` supply the
*point-evaluated* on-curve identity for the duplication (`n = 2`) and tripling (`n = 3`) maps.

This file builds the **general-`n` substrate** those low-index files use implicitly, in a form
reusable by the multiplication-by-`n` function-field pullback `[n]∗ : F(W) → F(W)`.

The `y`-coordinate of `[n]P` is governed by the bracket appearing in the index-doubling formula
`ψ₂ₙ = ψₙ · (ψₙ₊₂ψₙ₋₁² − ψₙ₋₂ψₙ₊₁²) / ψ₂` (Silverman AEC, Exercise 3.7). We name

* `WeierstrassCurve.preΩ n`, the **univariate** numerator
  `preΩₙ = preΨₙ₊₂·preΨₙ₋₁² − preΨₙ₋₂·preΨₙ₊₁² ∈ R[X]`, and
* `WeierstrassCurve.Ω n`, the **bivariate** numerator
  `Ωₙ = ψₙ₊₂·ψₙ₋₁² − ψₙ₋₂·ψₙ₊₁² ∈ R[X][Y]`,

and establish:

* `preΩ_two`/`preΩ_three` : `preΩ₂ = preΨ₄` and `preΩ₃ = preΨ₅ − preΨ₄²`, reconciling with the exact
  univariate factors `Kᵥ` used in `OmegaTwo`/`OmegaThree` (validating the general definition against
  the two independently-proved low-index cases).
* `preΩ_neg` : `preΩ` is an even function of the index.
* `ψ_mul_Ω` : the index-doubling bridge `ψ₂ₙ · ψ₂ = ψₙ · Ωₙ`, a repackaging of Mathlib's `ψ_even`.
* `Ω_factor` : the parity factorisation, at the level of the honest bivariate polynomials `Ψ`,
  `Ψₙ₊₂·Ψₙ₋₁² − Ψₙ₋₂·Ψₙ₊₁² = (if Even n then ψ₂ else ψ₂²)·C(preΩₙ)`, exhibiting the bivariate
  numerator as a power of `ψ₂` times the univariate `preΩₙ` — the parity split that makes the
  `y`-coordinate of `[n]P` computable from univariate data.

The remaining crux for the full general-`n` on-curve identity `W.Equation (Φₙ/ΨSqₙ) (ωₙ/ψₙ³)` is the
identification of the division-polynomial coordinates with the group-law multiple `n • P`
(equivalently the univariate identity `ΨSqₙ`-weighted analogue of `preΨ₄_sq`/`hstar` for general
`n`), which the
`OmegaTwo`/`OmegaThree` docstrings note is a separate, harder step; this file supplies the numerator
infrastructure it consumes.

## References

* [J. Silverman, *The arithmetic of elliptic curves*][silverman2009], Exercise 3.7, III.6.
-/

open Polynomial
open scoped Polynomial.Bivariate

local macro "C_simp" : tactic =>
  `(tactic| simp only [map_ofNat, C_0, C_1, C_neg, C_add, C_sub, C_mul, C_pow])

namespace WeierstrassCurve

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R)

/-- The **univariate** `y`-coordinate division-polynomial numerator
`preΩₙ = preΨₙ₊₂·preΨₙ₋₁² − preΨₙ₋₂·preΨₙ₊₁² ∈ R[X]`. It is the univariate factor of the bracket in
the index-doubling formula `ψ₂ₙ = ψₙ·(ψₙ₊₂ψₙ₋₁² − ψₙ₋₂ψₙ₊₁²)/ψ₂` (see `Ω_factor`). -/
noncomputable def preΩ (n : ℤ) : R[X] :=
  W.preΨ (n + 2) * W.preΨ (n - 1) ^ 2 - W.preΨ (n - 2) * W.preΨ (n + 1) ^ 2

/-- The **bivariate** `y`-coordinate division-polynomial numerator
`Ωₙ = ψₙ₊₂·ψₙ₋₁² − ψₙ₋₂·ψₙ₊₁² ∈ R[X][Y]`, i.e. `ψₙ · Ωₙ = ψ₂ₙ · ψ₂` (see `ψ_mul_Ω`). -/
noncomputable def Ω (n : ℤ) : R[X][Y] :=
  W.ψ (n + 2) * W.ψ (n - 1) ^ 2 - W.ψ (n - 2) * W.ψ (n + 1) ^ 2

/-- `preΩ₂ = preΨ₄`: the univariate `y`-numerator at `n = 2` is exactly the factor `preΨ₄` used in
`OmegaTwo.doubling_equation`. -/
@[simp]
lemma preΩ_two : W.preΩ 2 = W.preΨ₄ := by
  rw [preΩ, show (2 : ℤ) + 2 = 4 by norm_num, show (2 : ℤ) - 1 = 1 by norm_num,
    show (2 : ℤ) - 2 = 0 by norm_num, show (2 : ℤ) + 1 = 3 by norm_num, preΨ_four, preΨ_one,
    preΨ_zero]
  ring

/-- `preΩ₃ = preΨ₅ − preΨ₄²`: the univariate `y`-numerator at `n = 3` is exactly the factor
`Kᵥ = preΨ₅ − preΨ₄²` used in `OmegaThree.tripling_equation`. -/
@[simp]
lemma preΩ_three : W.preΩ 3 = W.preΨ 5 - W.preΨ₄ ^ 2 := by
  rw [preΩ, show (3 : ℤ) + 2 = 5 by norm_num, show (3 : ℤ) - 1 = 2 by norm_num,
    show (3 : ℤ) - 2 = 1 by norm_num, show (3 : ℤ) + 1 = 4 by norm_num, preΨ_two, preΨ_one,
    preΨ_four]
  ring

/-- `preΩ` is an even function of the index: `preΩ₋ₙ = preΩₙ`. -/
@[simp]
lemma preΩ_neg (n : ℤ) : W.preΩ (-n) = W.preΩ n := by
  rw [preΩ, preΩ, show -n + 2 = -(n - 2) by ring, show -n - 1 = -(n + 1) by ring,
    show -n - 2 = -(n + 2) by ring, show -n + 1 = -(n - 1) by ring, preΨ_neg, preΨ_neg, preΨ_neg,
    preΨ_neg]
  ring

/-- **The index-doubling bridge.** `ψ₂ₙ · ψ₂ = ψₙ · Ωₙ`, a repackaging of Mathlib's `ψ_even` with
the bivariate `y`-numerator `Ωₙ` factored out. -/
lemma ψ_mul_Ω (n : ℤ) : W.ψ (2 * n) * W.ψ₂ = W.ψ n * W.Ω n := by
  rw [Ω]
  linear_combination W.ψ_even n

/-- **The parity factorisation of the bivariate `y`-numerator.** At the level of the honest
bivariate polynomials `Ψ`,
`Ψₙ₊₂·Ψₙ₋₁² − Ψₙ₋₂·Ψₙ₊₁² = (if Even n then ψ₂ else ψ₂²)·C(preΩₙ)`. Since `Ψₙ` carries a factor of
`ψ₂` exactly for even `n`, the bivariate numerator is `ψ₂` (for even `n`) or `ψ₂²` (for odd `n`)
times the univariate `preΩₙ`. -/
lemma Ω_factor (n : ℤ) :
    W.Ψ (n + 2) * W.Ψ (n - 1) ^ 2 - W.Ψ (n - 2) * W.Ψ (n + 1) ^ 2 =
      (if Even n then W.ψ₂ else W.ψ₂ ^ 2) * C (W.preΩ n) := by
  simp only [WeierstrassCurve.Ψ, preΩ, C_sub, C_mul, C_pow]
  rcases Int.even_or_odd n with hn | hn
  · have h2 : Even (n + 2) := hn.add even_two
    have h2' : Even (n - 2) := hn.sub even_two
    have h1 : ¬Even (n - 1) := by simp [parity_simps, hn]
    have h1' : ¬Even (n + 1) := by simp [parity_simps, hn]
    rw [if_pos hn, if_pos h2, if_pos h2', if_neg h1, if_neg h1']
    ring
  · have hne : ¬Even n := by simp [parity_simps, hn]
    have h2 : ¬Even (n + 2) := by simp [parity_simps, hn]
    have h2' : ¬Even (n - 2) := by simp [parity_simps, hn]
    have h1 : Even (n - 1) := by simp [parity_simps, hn]
    have h1' : Even (n + 1) := by simp [parity_simps, hn]
    rw [if_neg hne, if_neg h2, if_neg h2', if_pos h1, if_pos h1']
    ring

end WeierstrassCurve
