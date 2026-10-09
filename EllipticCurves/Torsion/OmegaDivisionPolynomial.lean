/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import EllipticCurves.Torsion.DivisionPolynomialEval

/-!
# The `y`-coordinate division-polynomial numerators `Ωₙ` and their factorisation

Mathlib's `Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Basic.lean` develops the
`x`-coordinate division polynomials (`ψ₂, Ψ₂Sq, Ψ₃, preΨ₄, ΨSq, Ψ, Φ, ψ, φ`) but explicitly leaves
the *`y`-coordinate* division polynomials `ωₙ` as a `TODO`. The downstream files
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

* `preΨ_five` : the closed form `preΨ₅ = preΨ₄·Ψ₂Sq² − Ψ₃³`, from the odd `preΨ'` recurrence.
* `preΨ₄_sq` : the univariate identity `preΨ₄² = 4Φ₂³ + b₂Φ₂²Ψ₂Sq + 2b₄Φ₂Ψ₂Sq² + b₆Ψ₂Sq³` relating
  `preΨ₄`, `Φ₂` and `Ψ₂Sq`.
* `preΩ_two`/`preΩ_three` : `preΩ₂ = preΨ₄` and `preΩ₃ = preΨ₅ − preΨ₄²`, reconciling with the exact
  univariate factors `Kᵥ` used in `OmegaTwo`/`OmegaThree` (validating the general definition against
  the two independently-proved low-index cases).
* `preΩ_neg` : `preΩ` is an even function of the index.
* `map_preΩ` : `preΩ` commutes with base change, the `preΩ` member of Mathlib's
  `map_preΨ` / `map_ΨSq` / `map_Φ` family.
* `ψ_mul_Ω` : the index-doubling bridge `ψ₂ₙ · ψ₂ = ψₙ · Ωₙ`, a repackaging of Mathlib's `ψ_even`.
* `Ω_factor` : the parity factorisation, at the level of the honest bivariate polynomials `Ψ`,
  `Ψₙ₊₂·Ψₙ₋₁² − Ψₙ₋₂·Ψₙ₊₁² = (if Even n then ψ₂ else ψ₂²)·C(preΩₙ)`, exhibiting the bivariate
  numerator as a power of `ψ₂` times the univariate `preΩₙ` — the parity split that makes the
  `y`-coordinate of `[n]P` computable from univariate data.
* `preΨ_two_mul` : the same index doubling **univariately and with no hypotheses**,
  `preΨ₂ₙ = preΨₙ·preΩₙ`, which is Mathlib's `preΨ_even` with the common `preΨₙ` pulled out.
* `ΨSq_two_mul` : its squared form `ΨSq₂ₙ = ΨSqₙ·(preΩₙ²·(if Even n then 1 else Ψ₂Sq))`, whose
  parity factor is the one in `EllipticCurves.Torsion.OmegaOnCurve`'s `HasPreΩSq` — this is the
  lemma that removes `preΩ` from that predicate.
* `ω₃` : the **`2`-free** `3`-division `y`-coordinate polynomial `ω₃ = preΩ₃·Y + preω₃`, an
  honest polynomial over every `CommRing`, with `2·ω₃ = ψ₂·preΩ₃ − ψ₃·(a₁Φ₃ + a₃ΨSq₃)` — so the
  `2` in the `ωₙ/(2ψₙ³)` of `EllipticCurves.Torsion.OmegaCrux` is presentational **at `n = 3`**.
  Its halving witness is `ω₃Aux`, the one explicitly written polynomial of that section.
* `Affine.ψ_two_mul_evalEval` : the two preceding lemmas combined and the common factor of `ψ₂`
  cancelled, at a point `(x, y)` of `W` where `ψ₂` does not vanish:
  `ψ₂ₙ(x, y) = ψₙ(x, y)·(if Even n then 1 else ψ₂(x, y))·preΩₙ(x)`.  Equivalently
  `(if Even n then 1 else ψ₂)·preΩₙ = ψ₂ₙ/ψₙ`, which is the quantity Silverman's `ωₙ` is built
  from, and it is what identifies the parity factor of
  `EllipticCurves.Torsion.OmegaOnCurve`'s `HasPreΩSq` as this factorisation rather than a bare
  degree count.  ⚠️ Pointwise only, and the restriction is a property of the **bivariate** pair:
  `Ω_factor` is about `Ψ` and `Ω` is defined from `ψ`, and the two agree only after evaluation at a
  point of `W`.  Univariately there is no such restriction — that is `preΨ_two_mul` above.
* `Affine.ψ_four_evalEval` : the `n = 2` specialisation, landing on Mathlib's `ψ_four`; a
  non-vacuity check on the general statement rather than new content.

`preΨ_five` and `preΨ₄_sq` are pure `CommRing` statements about `preΨ` — no point, no field, no
characteristic hypothesis — and they feed the `n = 2` and `n = 3` instances of the general-`n`
on-curve engine in `EllipticCurves.Torsion.OmegaOnCurve`, which is why they live here rather than
in the point-level files that used to hold them.

The remaining crux for the full general-`n` on-curve identity `W.Equation (Φₙ/ΨSqₙ) (ωₙ/ψₙ³)` is the
**univariate** identity `WeierstrassCurve.HasPreΩSq` of `EllipticCurves.Torsion.OmegaOnCurve` — the
`ΨSqₙ`-weighted, parity-corrected analogue of `preΨ₄_sq` at general `n`, established there for
`n ∈ {0, ±1, ±2}`, and at `n = 3` in the evaluated form `HasPreΩSqAt` there and in the polynomial
form in `EllipticCurves.Torsion.OmegaCharZero`. It is the *only*
index-dependent input: the uniform half `WeierstrassCurve.Affine.equation_of_hasPreΩSqAt` derives
the Weierstrass equation at the division-polynomial coordinates from it alone, over any field of
characteristic `≠ 2` at a point with `ψₙ(x, y) ≠ 0`. This file supplies the numerator infrastructure
both consume.

⚠️ `ΨSq_two_mul` above is what lets that crux be restated **without `preΩ`**, as
`WeierstrassCurve.HasΨSqDoubling` in `EllipticCurves.Torsion.OmegaOnCurve`; the two are equivalent
and neither is easier. So `preΩ` is the vocabulary the crux was *first written in*, not a
constituent of it — which is worth knowing before extending this file with further `preΩ` lemmas
aimed at the crux.

⚠️ Identifying `(Φₙ/ΨSqₙ, ωₙ/ψₙ³)` with the group-law multiple `n • P` is a **separate** statement
(`#251`), not an equivalent of the above and not a gate on it — `equation_of_hasPreΩSqAt` takes no
group-law input. `EllipticCurves.Torsion.DoublingCoords` and `EllipticCurves.Torsion.TriplingCoords`
supply it at `n = 2` and `n = 3`. The `OmegaTwo`/`OmegaThree` docstrings make the same disclaimer,
`OmegaTwo` calling the `2 • P` identification "a separate, harder statement not proved here" and
`OmegaThree` calling the `3 • P` one "a separate statement" that `TriplingCoords` does prove.
⚠️ That separate statement is now available at **every** index and not only at `2` and `3`:
`WeierstrassCurve.Affine.nsmul_eq_some_omegaY_of_ΨSq_ne_zero`
(`EllipticCurves.Torsion.NsmulYPeriodic`, `#1500`), whose `x`-half is
`hasXCoordFormula_of_two_ne_zero` (`EllipticCurves.Torsion.NsmulOrder`, `#251`) — each at every
index over a field with `(2 : F) ≠ 0`, and the `y`-half under `ΨSqₙ(x) ≠ 0` besides.  Both are
downstream of this file and neither is consumed here.

## References

* [J. Silverman, *The arithmetic of elliptic curves*][silverman2009], Exercise 3.7, III.6.
-/

open Polynomial
open scoped Polynomial.Bivariate

local macro "C_simp" : tactic =>
  `(tactic| simp only [map_ofNat, C_0, C_1, C_neg, C_add, C_sub, C_mul, C_pow])

namespace WeierstrassCurve

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R)

/-- The closed form of the auxiliary `5`-division polynomial `preΨ₅ = preΨ₄·Ψ₂Sq² − Ψ₃³`, obtained
from the odd recurrence for `preΨ'`. -/
lemma preΨ_five : W.preΨ 5 = W.preΨ₄ * W.Ψ₂Sq ^ 2 - W.Ψ₃ ^ 3 := by
  have H := W.preΨ'_odd 0
  norm_num [preΨ'_four, preΨ'_two, preΨ'_one, preΨ'_three] at H
  rw [show (5 : ℤ) = ((5 : ℕ) : ℤ) by norm_num, preΨ_ofNat]; exact H

/-- The key univariate division-polynomial identity underlying the duplication formula: the square
of `preΨ₄` is the cubic in `Φ₂` and `Ψ₂Sq` with the `bᵢ` as coefficients. Equivalently, this is the
statement that `(Φ₂/Ψ₂Sq, preΨ₄/(2 ψ₂³))` — up to the linear correction absorbed into `ω₂` — solves
the Weierstrass equation after clearing the `ψ₂²`-denominators. -/
lemma preΨ₄_sq : W.preΨ₄ ^ 2 =
    4 * W.Φ 2 ^ 3 + C W.b₂ * W.Φ 2 ^ 2 * W.Ψ₂Sq + 2 * C W.b₄ * W.Φ 2 * W.Ψ₂Sq ^ 2 +
      C W.b₆ * W.Ψ₂Sq ^ 3 := by
  rw [Φ_two, preΨ₄, Ψ₂Sq, b₂, b₄, b₆, b₈]
  C_simp
  ring1

/-- **`Ψ₂Sq` split off its square part**: `Ψ₂Sq = (a₁X + a₃)² + 4(X³ + a₂X² + a₄X + a₆)`.

This is the univariate shadow of Mathlib's `C_Ψ₂Sq` (`C Ψ₂Sq = ψ₂² − 4·W.polynomial`): `(a₁X + a₃)`
is the `Y`-free part of `ψ₂` and `X³ + a₂X² + a₄X + a₆` is the `Y`-free part of `−W.polynomial`.

⚠️ **Index-free, and it lives here rather than beside its consumer for that reason**: it mentions no
`ωₙ` and no index, so it belongs with `preΨ_five` and `preΨ₄_sq` among the plain `CommRing` facts
about the division polynomials.  The `n = 3` section below is what uses it, in
`two_mul_ω₃Factor`. -/
lemma Ψ₂Sq_eq_sq_add_four_mul : W.Ψ₂Sq =
    (C W.a₁ * X + C W.a₃) ^ 2 + 4 * (X ^ 3 + C W.a₂ * X ^ 2 + C W.a₄ * X + C W.a₆) := by
  rw [Ψ₂Sq, b₂, b₄, b₆]
  C_simp
  ring1

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

/-- **`preΩ` commutes with base change**: `(W.map f).preΩ n = (W.preΩ n).map f`.  This is the
`preΩ` member of Mathlib's `map_preΨ` / `map_ΨSq` / `map_Φ` family, and it is what lets a
statement about `preΩ` be proved once over the universal curve and specialised — see
`EllipticCurves.Torsion.OmegaUniversal`. -/
lemma map_preΩ {S : Type*} [CommRing S] (f : R →+* S) (n : ℤ) :
    (W.map f).preΩ n = (W.preΩ n).map f := by
  simp only [preΩ, map_preΨ, Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_pow]

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

/-- **The index-doubling bridge, at the univariate level and with no hypotheses at all**:
`preΨ₂ₙ = preΨₙ · preΩₙ`.

This is Mathlib's `preΨ_even` with the common factor of `preΨₙ` pulled out, and the bracket that
remains is `preΩₙ` on the nose.  ⚠️ It is the univariate counterpart of `ψ_mul_Ω`, but it is
**strictly stronger in shape than that lemma is**: `ψ_mul_Ω` carries a spurious factor of `ψ₂` on
each side, which `Affine.ψ_two_mul_evalEval` below can only cancel at a point where `ψ₂` does not
vanish, and only after `ψ_evalEval` has reconciled `ψ` with `Ψ`.  Here there is nothing to cancel
and nothing to reconcile: `preΨ` and `preΩ` are both univariate, the identity is an equation in
`R[X]` over an arbitrary `CommRing`, and it holds at the `2`-torsion points too.

⚠️ `Affine.ψ_two_mul_evalEval`'s docstring says that it is *"a pointwise statement and there is no
polynomial-level version"*.  That remark is about the **bivariate** pair `Ψ`/`Ω` — `Ω_factor` is
stated for `Ψ` while `Ω` is defined from `ψ`, and those agree only on the curve.  It is not a claim
that index doubling has no polynomial-level form, and this lemma is that form. -/
lemma preΨ_two_mul (n : ℤ) : W.preΨ (2 * n) = W.preΨ n * W.preΩ n := by
  rw [preΨ_even, preΩ]
  ring

/-- **Index doubling for the squared division polynomial**:
`ΨSq₂ₙ = ΨSqₙ · (preΩₙ² · (if Even n then 1 else Ψ₂Sq))`.

The parity factor on the right is exactly the one in `EllipticCurves.Torsion.OmegaOnCurve`'s
`WeierstrassCurve.HasPreΩSq`, and that is not a coincidence: this lemma is what turns that
predicate into a statement with no `preΩ` in it — see
`WeierstrassCurve.hasPreΩSq_iff_hasΨSqDoubling` there.

⚠️ The two branches meet: `ΨSqₙ` carries `Ψ₂Sq` exactly when `n` is even and the parity factor
carries it exactly when `n` is odd, so the product carries it in both cases, which is what makes
the left-hand side — with `2n` always even — come out uniformly. -/
lemma ΨSq_two_mul (n : ℤ) :
    W.ΨSq (2 * n) = W.ΨSq n * (W.preΩ n ^ 2 * if Even n then 1 else W.Ψ₂Sq) := by
  rw [ΨSq, ΨSq, preΨ_two_mul, if_pos (even_two_mul n)]
  rcases Int.even_or_odd n with hn | hn
  · simp only [if_pos hn]
    ring
  · simp only [if_neg (Int.not_even_iff_odd.mpr hn)]
    ring

/-! ### The `2`-free form of the `y`-coordinate numerator at `n = 3`

The `y`-coordinate of `[n]P` is written `ωₙ/ψₙ³` with
`ωₙ = ((if Even n then 1 else ψ₂)·preΩₙ − ψₙ·(a₁Φₙ + a₃ΨSqₙ))/2`
(`EllipticCurves.Torsion.OmegaCrux`, `EllipticCurves.Torsion.OmegaOnCurve`).  ⚠️ **At `n = 3` the
`2` in that denominator is PRESENTATIONAL and this section proves it**: the bracket is divisible by
`2` in `ℤ[a₁,…,a₆][X][Y]` identically — no use of the Weierstrass relation, no reduction of `Y²`,
no localisation — so `ω₃` below is an honest polynomial over **every** commutative ring and the
tripling `y`-coordinate is `ω₃/ψ₃³` with no `2` in it at all.

⚠️ **The general-`n` statement is OPEN and is deliberately not claimed here.**  The divisibility
holds at other indices too — verified in exact `ℤ[a₁,…,a₆][X]` arithmetic at `n = 2` and `n = 4`
(the even shape, whose parity factor is `1`) as well as at `n = 3`, and reported at `n = 2…9` in
`𝔽₂` in `#2243` — but **that is evidence at finitely many indices and not an induction**: the
witness below is computed at `n = 3` only, and a general `ωₙ` needs an induction over the `preΨ`
recurrence that nobody has attempted.  **Read nothing here as a theorem about general `n`.**

⚠️ **The divisibility is a fact about the `aᵢ` and not about the `bᵢ`.**  Modulo `2` one has
`b₂ ≡ a₁²`, `b₄ ≡ a₁a₃`, `b₆ ≡ a₃²`, hence `Ψ₂Sq ≡ (a₁X + a₃)²` and
`preΨ₄ ≡ (a₁X + a₃)⁴ + a₁(a₁X + a₃)Ψ₃`; no identity in the `bᵢ` alone sees it, which is why
`ω₃Aux` below is written in the `aᵢ` and is the one explicit object here.

⚠️ **The obvious attack fails.**  The `Y`-free part of the `n = 3` bracket is
`a₁(X·preΩ₃ − Φ₃Ψ₃) + a₃(preΩ₃ − Ψ₃³)`, and **neither** bracket is divisible by `2` — each has
exactly `34` monomials of odd coefficient.  Only the `a₁`/`a₃` combination is, because modulo `2`
the two satisfy `a₁·P ≡ a₃·Q` rather than `P ≡ Q ≡ 0`.
-/

/-- The **halving witness** for the `n = 3` `y`-coordinate numerator: the polynomial with
`2·ω₃Aux = a₁·(a₁X + a₃)·Ψ₃ − (a₁X + a₃)⁴ − preΨ₄` (`two_mul_ω₃Aux`).

⚠️ This is the **only** explicitly written polynomial of this section and everything below is
assembly: `30` monomials, `deg_X = 6`.  Its existence — that is, the divisibility of that
right-hand side by `2` over `ℤ[a₁,…,a₆]` — is the whole content of the `2`-free form. -/
noncomputable def ω₃Aux : R[X] :=
  -X ^ 6 + C (W.a₁ ^ 2 - 2 * W.a₂) * X ^ 5
    + C (2 * W.a₁ ^ 2 * W.a₂ - W.a₁ * W.a₃ - 5 * W.a₄) * X ^ 4
    + C (3 * W.a₁ ^ 2 * W.a₄ + 2 * W.a₁ * W.a₂ * W.a₃ - 5 * W.a₃ ^ 2 - 20 * W.a₆) * X ^ 3
    + C (W.a₁ ^ 2 * W.a₆ + 8 * W.a₁ * W.a₃ * W.a₄ - 5 * W.a₂ * W.a₃ ^ 2 - 20 * W.a₂ * W.a₆ +
        5 * W.a₄ ^ 2) * X ^ 2
    + C (-(2 * W.a₁ ^ 2 * W.a₂ * W.a₆) + 2 * W.a₁ * W.a₂ * W.a₃ * W.a₄ + 8 * W.a₁ * W.a₃ * W.a₆ -
        2 * W.a₂ ^ 2 * W.a₃ ^ 2 - 8 * W.a₂ ^ 2 * W.a₆ + 2 * W.a₂ * W.a₄ ^ 2 + W.a₃ ^ 2 * W.a₄ +
        4 * W.a₄ * W.a₆) * X
    + C (-(W.a₁ ^ 2 * W.a₄ * W.a₆) + W.a₁ * W.a₃ * W.a₄ ^ 2 - W.a₂ * W.a₃ ^ 2 * W.a₄ -
        4 * W.a₂ * W.a₄ * W.a₆ + 4 * W.a₃ ^ 2 * W.a₆ + W.a₄ ^ 3 + 8 * W.a₆ ^ 2)

/-- **The defining identity of the halving witness**:
`2·ω₃Aux = a₁·(a₁X + a₃)·Ψ₃ − (a₁X + a₃)⁴ − preΨ₄`, over an arbitrary `CommRing`.

⚠️ No `Field`, no characteristic hypothesis, no `IsElliptic`: this is an identity in the
`a`-invariants, closed by `ring1` after `C_simp`. -/
lemma two_mul_ω₃Aux : 2 * W.ω₃Aux =
    C W.a₁ * (C W.a₁ * X + C W.a₃) * W.Ψ₃ - (C W.a₁ * X + C W.a₃) ^ 4 - W.preΨ₄ := by
  rw [ω₃Aux, Ψ₃, preΨ₄, b₂, b₄, b₆, b₈]
  C_simp
  ring1

/-- The **assembled factor** of the `2`-free `n = 3` numerator: the polynomial with
`2·ω₃Factor = (a₁X + a₃)·(Ψ₂Sq² − preΨ₄) + a₁·Ψ₂Sq·Ψ₃` (`two_mul_ω₃Factor`).

`60` monomials, `deg_X = 7`, and it is built from `ω₃Aux` rather than written out. -/
noncomputable def ω₃Factor : R[X] :=
  (C W.a₁ * X + C W.a₃) ^ 5 + (C W.a₁ * X + C W.a₃) * W.ω₃Aux
    + 4 * (C W.a₁ * X + C W.a₃) ^ 3 * (X ^ 3 + C W.a₂ * X ^ 2 + C W.a₄ * X + C W.a₆)
    + 8 * (C W.a₁ * X + C W.a₃) * (X ^ 3 + C W.a₂ * X ^ 2 + C W.a₄ * X + C W.a₆) ^ 2
    + 2 * C W.a₁ * (X ^ 3 + C W.a₂ * X ^ 2 + C W.a₄ * X + C W.a₆) * W.Ψ₃

/-- **The halved factor identity**: `2·ω₃Factor = (a₁X + a₃)·(Ψ₂Sq² − preΨ₄) + a₁·Ψ₂Sq·Ψ₃`,
over an arbitrary `CommRing`.

⚠️ The proof is `Ψ₂Sq_eq_sq_add_four_mul` followed by **one** use of `two_mul_ω₃Aux`: after the
`Ψ₂Sq` split, every term of the difference cancels except `(a₁X + a₃)` times that identity. -/
lemma two_mul_ω₃Factor : 2 * W.ω₃Factor =
    (C W.a₁ * X + C W.a₃) * (W.Ψ₂Sq ^ 2 - W.preΨ₄) + C W.a₁ * W.Ψ₂Sq * W.Ψ₃ := by
  rw [ω₃Factor, Ψ₂Sq_eq_sq_add_four_mul]
  linear_combination (C W.a₁ * X + C W.a₃) * W.two_mul_ω₃Aux

/-- The **univariate part of the `2`-free `3`-division `y`-coordinate polynomial**: the `Y`-free
half of `ω₃`, with `2·preω₃ = (a₁X + a₃)·preΩ₃ − a₁·Φ₃·Ψ₃ − a₃·Ψ₃³` (`two_mul_preω₃`).

⚠️ **Not to be confused with `W.preΩ 3`, which stands beside it in that very identity.**
`preΩ 3 = preΨ₅ − preΨ₄²` is the univariate index-doubling factor; `preω₃` is
`preΨ₄·ω₃Factor − (a₁X + a₃)·Ψ₃³`.  **They differ by the case of one omega and are different
polynomials** — `ω₃` below carries the parallel warning against `W.Ω 3`. -/
noncomputable def preω₃ : R[X] :=
  W.preΨ₄ * W.ω₃Factor - (C W.a₁ * X + C W.a₃) * W.Ψ₃ ^ 3

/-- **The `Y`-free half of the `n = 3` numerator is divisible by `2`**:
`2·preω₃ = (a₁X + a₃)·preΩ₃ − a₁·Φ₃·Ψ₃ − a₃·Ψ₃³`, over an arbitrary `CommRing`.

⚠️ This is where `Φ₃ = X·Ψ₃² − preΨ₄·Ψ₂Sq` (Mathlib's `Φ_three`) and `preΨ₅ = preΨ₄·Ψ₂Sq² − Ψ₃³`
(`preΨ_five`) enter, and after them the difference is `preΨ₄` times `two_mul_ω₃Factor`. -/
lemma two_mul_preω₃ : 2 * W.preω₃ =
    (C W.a₁ * X + C W.a₃) * W.preΩ 3 - C W.a₁ * W.Φ 3 * W.Ψ₃ - C W.a₃ * W.Ψ₃ ^ 3 := by
  rw [preω₃, preΩ_three, preΨ_five, Φ_three]
  linear_combination W.preΨ₄ * W.two_mul_ω₃Factor

/-- **The `2`-free `3`-division `y`-coordinate polynomial** `ω₃ = preΩ₃·Y + preω₃ ∈ R[X][Y]`,
an honest polynomial over **every** commutative ring, with
`2·ω₃ = ψ₂·preΩ₃ − ψ₃·(a₁Φ₃ + a₃ΨSq₃)` — the bracket whose half the tripling `y`-coordinate is
(`two_mul_ω₃`).

⚠️ Not to be confused with `W.Ω 3`, which is the *index-doubling* bracket
`ψ₅ψ₂² − ψ₁ψ₄²` and a different polynomial. -/
noncomputable def ω₃ : R[X][Y] :=
  C (W.preΩ 3) * Y + C W.preω₃

/-- **The `n = 3` numerator is twice an honest polynomial**:
`2·ω₃ = ψ₂·preΩ₃ − ψ₃·(a₁Φ₃ + a₃ΨSq₃)`, over an arbitrary `CommRing`.

The right-hand side is the bracket of `WeierstrassCurve.Affine.equation_div_of_ψ_ne_zero` at
`n = 3` (odd, so its parity factor is `ψ₂`), written bivariately.  ⚠️ **So the `2` in that
theorem's `ωₙ/(2ψₙ³)` is presentational at `n = 3`: the quotient is `ω₃/ψ₃³`.** -/
lemma two_mul_ω₃ : 2 * W.ω₃ =
    W.ψ 2 * C (W.preΩ 3) - W.ψ 3 * C (C W.a₁ * W.Φ 3 + C W.a₃ * W.ΨSq 3) := by
  have h := congrArg (C : R[X] → R[X][Y]) W.two_mul_preω₃
  rw [ω₃, ψ_two, ψ₂, Affine.polynomialY, ψ_three, ΨSq_three]
  simp only [map_ofNat, C_add, C_sub, C_mul, C_pow] at h ⊢
  linear_combination h

/-- **`ω₃` at a point**: `ω₃(x, y) = y·preΩ₃(x) + preω₃(x)`.

⚠️ No point of `W` and no hypothesis of any kind: `ω₃` is `Y`-linear by construction, so its
evaluation is this for **every** pair `(x, y)` of the base ring. -/
lemma evalEval_ω₃ (x y : R) :
    W.ω₃.evalEval x y = y * (W.preΩ 3).eval x + W.preω₃.eval x := by
  simp only [ω₃, evalEval, eval_add, eval_mul, eval_C, Polynomial.eval_C, eval_X]
  ring

/-! ### Base change

The four members of Mathlib's `map_preΨ` / `map_ΨSq` / `map_Φ` family that this section's own
polynomials owe.  ⚠️ **They are what makes the `n = 3` `y`-coordinate usable over the universal
curve**, which is the only route to a statement about `ω₃` that holds where `2 = 0`: the `2`-free
identities above are proved by `ring1` over an arbitrary `CommRing`, but any identity whose
derivation cancels a `2` has to be proved over `MvPolynomial (Fin 5) ℤ` and carried down, and that
carrying is exactly these lemmas (`EllipticCurves.Torsion.OmegaThreeCharFree`).
-/

/-- **`ω₃Aux` commutes with base change.** -/
lemma map_ω₃Aux {S : Type*} [CommRing S] (f : R →+* S) :
    (W.map f).ω₃Aux = W.ω₃Aux.map f := by
  simp only [ω₃Aux, WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂, WeierstrassCurve.map_a₃,
    WeierstrassCurve.map_a₄, WeierstrassCurve.map_a₆, Polynomial.map_add, Polynomial.map_sub,
    Polynomial.map_neg, Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_C,
    Polynomial.map_X, Polynomial.map_ofNat, map_add, map_sub, map_neg, map_mul, map_pow,
    map_ofNat]

/-- **`ω₃Factor` commutes with base change.** -/
lemma map_ω₃Factor {S : Type*} [CommRing S] (f : R →+* S) :
    (W.map f).ω₃Factor = W.ω₃Factor.map f := by
  simp only [ω₃Factor, map_ω₃Aux, map_Ψ₃, WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂,
    WeierstrassCurve.map_a₄, WeierstrassCurve.map_a₆, WeierstrassCurve.map_a₃,
    Polynomial.map_add, Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_C,
    Polynomial.map_X, Polynomial.map_ofNat]

/-- **`preω₃` commutes with base change.** -/
lemma map_preω₃ {S : Type*} [CommRing S] (f : R →+* S) :
    (W.map f).preω₃ = W.preω₃.map f := by
  simp only [preω₃, map_ω₃Factor, map_preΨ₄, map_Ψ₃, WeierstrassCurve.map_a₁,
    WeierstrassCurve.map_a₃, Polynomial.map_sub, Polynomial.map_add, Polynomial.map_mul,
    Polynomial.map_pow, Polynomial.map_C, Polynomial.map_X]

/-- **`ω₃` commutes with base change.** -/
lemma map_ω₃ {S : Type*} [CommRing S] (f : R →+* S) :
    (W.map f).ω₃ = W.ω₃.map (mapRingHom f) := by
  simp only [ω₃, map_preΩ, map_preω₃, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C,
    Polynomial.map_X, coe_mapRingHom]

namespace Affine

variable {F : Type*} [Field F] {W : Affine F} {x y : F}

/-- **The index-doubling formula at a point, with the parity factor made explicit.**  For a point
`(x, y)` of `W` at which `ψ₂` does not vanish,

```
ψ₂ₙ(x, y) = ψₙ(x, y) · (if Even n then 1 else ψ₂(x, y)) · preΩₙ(x).
```

This is `ψ_mul_Ω` (`ψ₂ₙ·ψ₂ = ψₙ·Ωₙ`) combined with `Ω_factor` (`Ωₙ = ψ₂^(1 or 2)·preΩₙ` after
`ψ_evalEval`), with the one common factor of `ψ₂` cancelled.  Equivalently
`(if Even n then 1 else ψ₂)·preΩₙ = ψ₂ₙ/ψₙ`, which is the quantity Silverman's `ωₙ` is built from:
`2ωₙ = ψ₂ₙ/ψₙ − ψₙ·(a₁Φₙ + a₃ΨSqₙ)` (AEC, Exercise 3.7).

⚠️ **`hψ₂` is not decoration.**  The proof cancels a common factor of `ψ₂` at the point, and
`ψ₂(x, y) = 2y + a₁x + a₃` vanishes exactly at the `2`-torsion points of `W`; there the identity
carries no information, since `ψ_mul_Ω` reads `0 = ψₙ·Ωₙ` after evaluation.

⚠️ This is a **pointwise** statement and there is no polynomial-level version *of it*: `Ω_factor`
is stated for the honest bivariate `Ψ`, while `Ω` is defined from `ψ`, and `ψₙ` is only *congruent*
to `Ψₙ` modulo `W.polynomial`.  They agree only after evaluation at a point of `W`, via
`ψ_evalEval`, which is what `h` supplies.

⚠️ **That restriction is a fact about the bivariate polynomials, not about index doubling.**  The
univariate identity `preΨ_two_mul`, `preΨ₂ₙ = preΨₙ·preΩₙ`, holds in `R[X]` over an arbitrary
`CommRing` with no point, no `Equation` and no `ψ₂ ≠ 0` — including at the `2`-torsion points where
this lemma carries no information.  Read the sentence above as *"`ψ` and `Ψ` do not agree off the
curve"*, not as *"index doubling is available only pointwise"*. -/
lemma ψ_two_mul_evalEval (h : W.Equation x y) (hψ₂ : (W.ψ 2).evalEval x y ≠ 0) (n : ℤ) :
    (W.ψ (2 * n)).evalEval x y =
      (W.ψ n).evalEval x y * (if Even n then 1 else (W.ψ 2).evalEval x y) *
        (W.preΩ n).eval x := by
  have hΩ : (W.Ω n).evalEval x y =
      (if Even n then (W.ψ 2).evalEval x y else (W.ψ 2).evalEval x y ^ 2) *
        (W.preΩ n).eval x := by
    have hf := congrArg (Polynomial.evalEval x y) (W.Ω_factor n)
    simp only [WeierstrassCurve.Ω, evalEval, eval_mul, eval_sub, eval_pow, apply_ite,
      ψ_evalEval h, ψ_two, evalEval_C] at hf ⊢
    convert hf using 2
  have hbridge := congrArg (Polynomial.evalEval x y) (W.ψ_mul_Ω n)
  rw [← ψ_two] at hbridge
  simp only [evalEval, eval_mul] at hbridge
  refine mul_right_cancel₀ hψ₂ ?_
  simp only [evalEval] at hΩ ⊢
  rw [hbridge, hΩ]
  rcases Int.even_or_odd n with hn | hn
  · rw [if_pos hn, if_pos hn]; ring
  · have hne : ¬Even n := Int.not_even_iff_odd.mpr hn
    rw [if_neg hne, if_neg hne]; ring

/-- **Non-vacuity at `n = 2`: the general index-doubling formula lands on Mathlib's `ψ_four`.**
Specialising `ψ_two_mul_evalEval` at `n = 2` uses `preΩ₂ = preΨ₄` and the even branch of the parity
factor, and produces `ψ₄(x, y) = ψ₂(x, y)·preΨ₄(x)` — which is exactly Mathlib's
`ψ_four : ψ₄ = C preΨ₄ · ψ₂` evaluated at `(x, y)`.

⚠️ This is a **check on the general statement, not new content**: the same identity holds at every
`(x, y)` with no hypotheses at all, straight from `ψ_four`.  It is proved here through the engine
precisely so that a general statement which failed to specialise to the known `n = 2` factorisation
would break the build. -/
lemma ψ_four_evalEval (h : W.Equation x y) (hψ₂ : (W.ψ 2).evalEval x y ≠ 0) :
    (W.ψ 4).evalEval x y = (W.ψ 2).evalEval x y * W.preΨ₄.eval x := by
  have H := ψ_two_mul_evalEval h hψ₂ 2
  rwa [show (2 : ℤ) * 2 = 4 by norm_num, if_pos even_two, mul_one, preΩ_two] at H

end Affine

end WeierstrassCurve
