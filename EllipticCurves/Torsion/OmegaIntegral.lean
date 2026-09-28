/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import EllipticCurves.Torsion.NsmulYCoord
import EllipticCurves.Torsion.NsmulYPeriodic
import EllipticCurves.UniversalCurve

/-!
# The `y`-coordinate numerator `ωₙ` is an honest polynomial — the `2` in `ωₙ/(2ψₙ³)` is
presentational at EVERY index

`EllipticCurves.Torsion.NsmulYCoord`'s `Affine.omegaY` is the `y`-coordinate of `n • P`, and it is
**defined with a `2` in its denominator**:

```
ωₙ/(2ψₙ³) = ((if Even n then 1 else ψ₂)·preΩₙ − ψₙ·(a₁Φₙ + a₃ΨSqₙ)) / (2ψₙ³).
```

Every statement about it therefore carries `(2 : F) ≠ 0`.  ⚠️ **But the numerator is divisible by
`2` as a polynomial**, so that `2` is an artefact of the normalisation and not of the mathematics.
Writing `ωBracketₙ` for the numerator, this file produces `ωNumₙ` with

```
2 · ωNumₙ = ωBracketₙ            over EVERY commutative ring, at EVERY index (`two_mul_ωNum`).
```

⚠️ **`ωBracketₙ` is the classical `2ωₙ`, and the warrant is the POINT level rather than a pair of
polynomial identities.**  Silverman's relation `2ωₙ = ψ₂ₙ/ψₙ − ψₙ(a₁Φₙ + a₃ΨSqₙ)` is an equation in
the function field, and what earns it here is `evalEval_ωBracket`: `ωBracketₙ(x, y)` is **verbatim**
the numerator of `Affine.omegaY` (`EllipticCurves.Torsion.NsmulYCoord`), which that file proves is
the `y`-coordinate of `n • P` (`nsmul_eq_some_omegaY`).  `omegaY_eq` and `nsmul_eq_some_ωNum` below
close it.

⚠️ **Do NOT read that identification off `ψ_mul_Ω` and `Ω_factor`: those two do not compose.**
`Ω` is defined from `ψ` while `Ω_factor` is stated for `Ψ`, and `WeierstrassCurve.ψ` and
`WeierstrassCurve.Ψ` are **different polynomials** — `ψ` is `normEDS ψ₂ (C Ψ₃) (C preΨ₄) n`, whose
auxiliary sequence runs on `ψ₂⁴`, where `Ψ` is `C (preΨ n) · (if Even n then ψ₂ else 1)` and `preΨ`
runs on `Ψ₂Sq²`.  They agree only after the quotient, which is why Mathlib carries
`Affine.CoordinateRing.mk_ψ` and why `ψ_eq_C` below needs the characteristic for exactly that step.
`preΨ_two_mul : preΨ₂ₙ = preΨₙ·preΩₙ` (`EllipticCurves.Torsion.OmegaDivisionPolynomial`) is the
index-doubling bridge that **does** hold as a polynomial identity over an arbitrary `CommRing`, and
its docstring records both halves of this.

**The classical sentence *"`ωₙ` has integral coefficients"* is precisely `2 ∣ ωBracketₙ`, and
that is what `two_mul_ωNum` formalises at a general index.**

## ⚠️ The route, and why it is NOT an induction along the EDS recurrence

`2 ∣ ωBracketₙ` in `ℤ[a₁,…,a₆][X][Y]` is decided by computing mod `2`, and mod `2` the whole family
collapses: `ψ₂ ≡ L := a₁X + a₃` — ⚠️ **the `Y` disappears** — and `Ψ₂Sq ≡ L²`
(`Ψ₂Sq_eq_linForm_sq`), so `ψₙ` becomes `C` of a univariate polynomial (`ψ_eq_C`) and the whole
bracket becomes `C` of a univariate one (`ωBracket_eq_C`).

⚠️ **The one identity this then needs is ALREADY IN THE TREE.**  What has to be proved mod `2` is

```
preΩₙ·(if Even n then 1 else L) = preΨₙ·(if Even n then L else 1)·(a₁Φₙ + a₃ΨSqₙ),
```

and ⚠️ **the SQUARES of the two sides are equal by `WeierstrassCurve.hasPreΩSq`**
(`EllipticCurves.Torsion.OmegaCrux`, `#404`'s crux), which says over every commutative ring

```
preΩₙ² · (if Even n then 1 else Ψ₂Sq) = 4Φₙ³ + b₂Φₙ²ΨSqₙ + 2b₄ΦₙΨSqₙ² + b₆ΨSqₙ³
```

— and mod `2` the right-hand side is `ΨSqₙ·(a₁Φₙ + a₃ΨSqₙ)²`, a square, because `4` and `2b₄` die
and `b₂ ≡ a₁²`, `b₆ ≡ a₃²`.  ⚠️ **So the two sides have equal squares, and in a REDUCED ring of
characteristic `2` squaring is injective** (`x² = y² ⟹ (x−y)² = x² + y² = 0`).  That is
`preΩ_mul_eq_of_char_two`, and it is the whole content of this file.

⚠️ **This is why no induction along `preΨ'_even`/`preΨ'_odd` is needed.**  A direct induction has no
obvious invariant — the identity relates `preΨ` at five consecutive indices — and the Frobenius step
replaces it with a landed lemma plus `IsReduced`.  **The cost is that the argument runs over a
reduced ring, which the universal curve mod `2` supplies and a general `CommRing` does not**; hence
the descent below.

## The descent

`WeierstrassCurve.univ` over `S = MvPolynomial (Fin 5) ℤ` specialises onto every curve over every
commutative ring (`univ_map_specialize`), and `ωBracket` commutes with base change
(`map_ωBracket`).  `MvPolynomial (Fin 5) (ZMod 2)` is an integral domain of characteristic `2`, so
`ωBracket_eq_zero_of_char_two` applies to `univ` reduced mod `2`; and
`MvPolynomial.C_dvd_iff_map_hom_eq_zero` lifted through the two `Polynomial` layers turns that
vanishing into `2 ∣ univ.ωBracketₙ` (`two_dvd_ωBracket_univ`).  `ωNum` is the witness, mapped down.

## Main statements

**In the source: 20** public declarations — **3** definitions (`linForm`, `ωBracket`, `ωNum`) and
**17** theorems — beside **2** `private` lemmas.  ⚠️ **Do not read those off a regex**, which errs
in both directions: a prose line opening `theorem` counts as one, and an anonymous
`private instance :` counts as none.

⚠️ **And do not expect the elaborated environment to report those two numbers — BOTH halves carry
a second population, and the figures below are stated in one unit for both.**
`env.getModuleIdxFor?` puts **28** constants in this module, **24** of them non-`private` against
the **20** in source, and **4** `private` against the **2**.  **The six extras are generated code
on both sides**: `linForm.eq_1`, `ωBracket.eq_1` and `ωNum.eq_1`, the equation lemmas of the three
`def`s; `ωNum._proof_1`, the proof term of its `Exists.choose`; and the two constants the
`local macro "C_simp"` below emits.

⚠️ **`Name.isInternal` is not the filter that reconciles them either**: it is true of
`ωNum._proof_1` and of all **4** private constants — the `_private.` prefix makes every private name
internal — so filtering by it leaves **23** public and **0** private.  **The 23 are the 20 source
declarations plus the three `.eq_1`s**, and no source line declares any of the six extras.

`#print axioms` over all **20** public source declarations, name by name, returns exactly
`[propext, Classical.choice, Quot.sound]` at every one, with **0** `sorryAx`.

⚠️ The naturality `specialize_map : (W.map f).specialize = f ∘ W.specialize`, which `map_ωNum`
cannot be proved without, is **not** here: it mentions no division polynomial, so it sits with
`univ` and `specialize` in `EllipticCurves.UniversalCurve`.

* `WeierstrassCurve.linForm` — `a₁X + a₃`, the univariate shadow of `ψ₂`, with `map_linForm`.
* `WeierstrassCurve.Ψ₂Sq_eq_linForm_sq` — `Ψ₂Sq = (a₁X + a₃)²` when `2 = 0`.
* `WeierstrassCurve.ψ₂_eq_C_linForm` / `ψ_eq_C` — in characteristic `2` the bivariate `ψ₂` and `ψₙ`
  lose their `Y` entirely.  ⚠️ **`ψ_eq_C` is where `linForm⁴ = Ψ₂Sq²` is used** — univariate, both
  sides in `R[X]` — which is false away from characteristic `2` and is what makes the two
  `preNormEDS` sequences agree.
* `WeierstrassCurve.preΩ_mul_eq_of_char_two` — ⚠️ **the crux**, over any `[IsDomain R]` with
  `(2 : R) = 0`.  Proved from `hasPreΩSq` by squaring-injectivity, not by induction.
* `WeierstrassCurve.ωBracket` — the numerator `2ωₙ`, with `map_ωBracket` and `ωBracket_eq_C`.
* `WeierstrassCurve.ωBracket_eq_zero_of_char_two` — it vanishes identically in characteristic `2`.
* `WeierstrassCurve.two_dvd_ωBracket_univ` — `2 ∣ univ.ωBracketₙ`, the descent's payload.
* `WeierstrassCurve.ωNum` — ⚠️ **`ωₙ` itself, over EVERY commutative ring**, with
  `two_mul_ωNum : 2·ωNumₙ = ωBracketₙ` and `map_ωNum`, the `map` member of the
  `map_preΨ` / `map_ΨSq` / `map_Φ` / `map_preΩ` family.
* `WeierstrassCurve.ωNum_one` — ⚠️ **`ω₁ = Y`**, the classical normalisation, recovered here as a
  non-vacuity check on the whole chain: `ωBracket₁ = 2Y` by `ωBracket_one`, and the `2` cancels over
  the universal ring because it is a characteristic-`0` domain.
* `WeierstrassCurve.Affine.omegaY_eq` — ⚠️ **the point-level bridge**,
  `omegaY x y n = ωNumₙ(x, y)/ψₙ(x, y)³`.
* `WeierstrassCurve.Affine.nsmul_eq_some_ωNum` — the `y`-coordinate of `n • P` with **no `2`**,
  the companion of the **ladder** form `nsmul_eq_some_omegaY`; and
  `WeierstrassCurve.Affine.nsmul_eq_some_ωNum_of_ΨSq_ne_zero`, ⚠️ **the sharp one**, the companion
  of `nsmul_eq_some_omegaY_of_ΨSq_ne_zero` at **every** index under `ΨSqₙ(x) ≠ 0` alone.

## ⚠️ On the `(2 : F) ≠ 0` that remains, and what it does and does not pay for

`omegaY_eq` binds `h2`, and ⚠️ **it must**: it pays for the **left**-hand side, whose *definition*
divides by `2`.  Where `2 = 0` the left side is `0/0 = 0` and the right side is not.  **It does not
pay for `ωNum`**, which is a polynomial over every ring including those.

⚠️ **`nsmul_eq_some_ωNum` and `nsmul_eq_some_ωNum_of_ΨSq_ne_zero` both bind `h2`, for one and
the same reason, and this is a CORRECTION to the issue that asked for neither.**  `#2248`
item 3 asked for a companion *"which binds no `h2` at all"*.  ⚠️ **That is out of
reach from here — not because it is false, but because the obstruction is not the `y`-coordinate.**
Measured: `nsmul_eq_some_omegaY` (`EllipticCurves.Torsion.NsmulYCoord`) spends `h2` in **two**
places, and only one of them is the halving —

* `divY_eq_omegaY h2`, which undoes the `2` in `divY`.  ⚠️ **This one is now removable**, and
  removing it is what this file is for; and
* `nsmulEqDiv_of_forall_ψ_ne_zero h2` (`EllipticCurves.Torsion.NsmulLadder`), the
  **`x`-coordinate / group-law** half, which binds `(2 : F) ≠ 0` as a hypothesis of its own
  statement.

⚠️ **So the residue after this file is the `x`-half's, not the `y`-half's**, and it is exactly the
`hasXCoordFormula_of_two_ne_zero` route that `#2248`'s own *"NOT in scope"* section rules out
(*"No `(2 : F) ≠ 0` sweep"*).  **The `y`-coordinate's `2` is gone; the group law's is not, and it is
a different issue.**  ⚠️ **That residue is a BINDER and not a conclusion** — the conclusion of
`nsmulEqDiv_of_forall_ψ_ne_zero` is `NsmulEqDiv hns n` and mentions no `2` — so it is removable in
principle, unlike `#2245`'s terminus where `h2` occurs *inside* the statement it binds.  **The
claim here is out of scope, not unattainable.**

## ⚠️ What is *not* here

* **No change to `omegaY`, to `nsmul_eq_some_omegaY`, or to any landed statement.**  Everything here
  is **additive**: `equation_divX_omegaY`, `divY_eq_omegaY` and `nsmul_eq_some_omegaY` are about
  `omegaY`, whose definition divides by `2`, and they are correct as they stand.
* **No `x`-coordinate work.**  `Φₙ/ΨSqₙ` has never had a `2` in it.
* **Nothing about `mulByThreeEndo`, `tripling_equation` or `two_ne_zero_functionField`.**  ⚠️ **The
  function-field layer is the rung above this one**; this file is a precondition for attacking it
  and is not an attack on it.
* **Nothing at a fixed low index that `#2243` covers.**  `EllipticCurves.Torsion.OmegaThree` and
  `Torsion/OmegaDivisionPolynomial.lean` are untouched.  ⚠️ **`#2243`'s `ω₃` stays the sharp `n = 3`
  statement**: it is a **closed form**, `ω₃ = C preΩ₃·Y + C preω₃`, where `ωNum 3` here is an opaque
  `Exists.choose` with none.  ⚠️ **And the two are the SAME polynomial, not merely compatible** —
  `#2243`'s `two_mul_ω₃` has right-hand side `ψ₂·C preΩ₃ − ψ₃·C (a₁Φ₃ + a₃ΨSq₃)`, which is
  `ωBracket 3` on the nose (`3` is odd, so the parity factor is `ψ₂`), so `2·ω₃ = 2·ωNum 3` and the
  two agree over the universal ring, hence by `map_ωNum` over every ring.  **Stating that
  identification is a rung for the `#2243` / `#2246` lane and is deliberately NOT done here: this
  file must not reach into another branch's files.**
* ⚠️ **No claim beyond `2 ∣ ωBracketₙ`.**  A figure measured mod `2` is a divisibility claim and
  nothing else: nothing here says `4 ∣ ωBracketₙ`, nothing here bounds the size of `ωₙ`, and nothing
  here touches any `(3 : F) ≠ 0`.

## References

* [J. H. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.4 and Exercise 3.7 —
  `2ωₙ = ψ₂ₙ/ψₙ − ψₙ·(a₁Φₙ + a₃ΨSqₙ)`.
-/

open Polynomial Polynomial.Bivariate

local macro "C_simp" : tactic =>
  `(tactic| simp only [map_ofNat, C_0, C_1, C_neg, C_add, C_sub, C_mul, C_pow])

namespace WeierstrassCurve

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R)

/-- **The univariate shadow of `ψ₂`**, `a₁X + a₃`.

⚠️ It is `ψ₂` with its `2Y` dropped, so it agrees with `ψ₂` exactly in characteristic `2`
(`ψ₂_eq_C_linForm`) and is a strictly smaller object everywhere else.  It is named because in
characteristic `2` it is also a square root of `Ψ₂Sq` (`Ψ₂Sq_eq_linForm_sq`), and that square root
is what the whole file turns on. -/
noncomputable def linForm : R[X] := C W.a₁ * X + C W.a₃

variable {W}

/-- **`linForm` commutes with base change.** -/
@[simp]
lemma map_linForm {S : Type*} [CommRing S] (f : R →+* S) :
    (W.map f).linForm = W.linForm.map f := by
  simp [linForm, Polynomial.map_add, Polynomial.map_mul]

/-- **`Ψ₂Sq = (a₁X + a₃)²` in characteristic `2`.**

`4X³` and `2b₄X` die, `b₂ = a₁² + 4a₂` becomes `a₁²` and `b₆ = a₃² + 4a₆` becomes `a₃²`, and the
cross term `2a₁a₃X` of the square dies too.  ⚠️ **The `b`-invariants are unfolded twice in this
file and this is the smaller of the two**: `rw [b₂, b₄, b₆]` occurs here and once in each parity
branch of `preΩ_mul_eq_of_char_two` below — three sites.  The two unfoldings do the same work one
layer apart: this one exposes the square root of `Ψ₂Sq`, and those two are what make the
right-hand side of `hasPreΩSq` a square. -/
lemma Ψ₂Sq_eq_linForm_sq (h2 : (2 : R) = 0) : W.Ψ₂Sq = W.linForm ^ 2 := by
  have h2' : (2 : R[X]) = 0 := by
    have := congrArg (C : R →+* R[X]) h2; rwa [map_ofNat, map_zero] at this
  rw [Ψ₂Sq, linForm, b₂, b₄, b₆]
  C_simp
  linear_combination (2 * X ^ 3 + 2 * C W.a₂ * X ^ 2 + 2 * C W.a₄ * X + 2 * C W.a₆) * h2'

/-- In characteristic `2` the `2`-division polynomial loses its `Y`. -/
lemma ψ₂_eq_C_linForm (h2 : (2 : R) = 0) : W.ψ₂ = C W.linForm := by
  have h2' : (2 : R[X]) = 0 := by
    have := congrArg (C : R →+* R[X]) h2; rwa [map_ofNat, map_zero] at this
  have hz : (C (C (2 : R)) : R[X][Y]) = 0 := by rw [h2, map_zero, map_zero]
  rw [ψ₂, Affine.polynomialY, hz, zero_mul, zero_add, linForm]

/-- **In characteristic `2` the bivariate `ψₙ` is `C` of a univariate polynomial** — it has no `Y`
at all, at any index.

⚠️ **The step that needs the characteristic is `linForm⁴ = Ψ₂Sq²`**, which is
`Ψ₂Sq_eq_linForm_sq` squared and is an identity in `R[X]`: `ψ₂ : R[X][Y]` and `Ψ₂Sq : R[X]` are one
layer apart and `ψ₂⁴ = Ψ₂Sq²` is not an equation in either ring — the bivariate reading is
`ψ₂⁴ = C (Ψ₂Sq²)`, through `ψ₂_eq_C_linForm`.  `ψₙ` is `normEDS ψ₂ (C Ψ₃) (C preΨ₄) n`, whose
auxiliary sequence runs on `ψ₂⁴`, while
`preΨₙ` runs on `Ψ₂Sq²`; away from characteristic `2` those two differ by a multiple of the
Weierstrass polynomial and the conclusion is false. -/
lemma ψ_eq_C (h2 : (2 : R) = 0) (n : ℤ) :
    W.ψ n = C (W.preΨ n * if Even n then W.linForm else 1) := by
  have h4 : W.linForm ^ 4 = W.Ψ₂Sq ^ 2 := by
    rw [Ψ₂Sq_eq_linForm_sq h2, ← pow_mul]
  rw [WeierstrassCurve.ψ, ψ₂_eq_C_linForm h2, ← map_normEDS (C : R[X] →+* R[X][Y]), normEDS,
    h4, ← preΨ]

/-- In a reduced ring of characteristic `2`, squaring is injective. -/
private lemma eq_of_sq_eq_of_char_two {S : Type*} [CommRing S] [IsReduced S] (h2 : (2 : S) = 0)
    {a b : S} (h : a ^ 2 = b ^ 2) : a = b := by
  have hz : (a - b) ^ 2 = 0 := by linear_combination h + (b ^ 2 - a * b) * h2
  exact sub_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp hz)

/-- ⚠️ **THE CRUX.**  In characteristic `2`, over a domain,

```
preΩₙ·(if Even n then 1 else a₁X + a₃) = preΨₙ·(if Even n then a₁X + a₃ else 1)·(a₁Φₙ + a₃ΨSqₙ).
```

⚠️ **Proved by squaring-injectivity and NOT by induction on `n`.**  `WeierstrassCurve.hasPreΩSq`
(`EllipticCurves.Torsion.OmegaCrux`, `#404`) says `preΩₙ²·(if Even n then 1 else Ψ₂Sq)` is the cubic
`4Φₙ³ + b₂Φₙ²ΨSqₙ + 2b₄ΦₙΨSqₙ² + b₆ΨSqₙ³`; in characteristic `2` that cubic is
`ΨSqₙ·(a₁Φₙ + a₃ΨSqₙ)²`, so **both sides above have the same square**, and Frobenius is injective on
a reduced ring.

⚠️ **`[IsDomain R]` is the hypothesis and `IsReduced` is what the proof uses** — the weaker one is
not stated because Mathlib has no `IsReduced R[X]` instance and the only consumer is
`MvPolynomial (Fin 5) (ZMod 2)`, which is a domain. -/
theorem preΩ_mul_eq_of_char_two [IsDomain R] (h2 : (2 : R) = 0) (n : ℤ) :
    W.preΩ n * (if Even n then 1 else W.linForm) =
      W.preΨ n * (if Even n then W.linForm else 1) *
        (C W.a₁ * W.Φ n + C W.a₃ * W.ΨSq n) := by
  have h2' : (2 : R[X]) = 0 := by
    have := congrArg (C : R →+* R[X]) h2; rwa [map_ofNat, map_zero] at this
  have hL : W.Ψ₂Sq = W.linForm ^ 2 := Ψ₂Sq_eq_linForm_sq h2
  have key := W.hasPreΩSq n
  rw [HasPreΩSq] at key
  have hΨ : W.ΨSq n = W.preΨ n ^ 2 * (if Even n then W.Ψ₂Sq else 1) := rfl
  refine eq_of_sq_eq_of_char_two h2' ?_
  rcases Int.even_or_odd n with hn | hn
  · simp only [if_pos hn] at key hΨ ⊢
    rw [hΨ] at key ⊢
    rw [hL] at key ⊢
    rw [b₂, b₄, b₆] at key
    simp only [map_ofNat, C_add, C_mul, C_pow] at key ⊢
    linear_combination key + (2 * W.Φ n ^ 3
      + 2 * C W.a₂ * W.Φ n ^ 2 * (W.preΨ n ^ 2 * W.linForm ^ 2)
      + 2 * C W.a₄ * W.Φ n * (W.preΨ n ^ 2 * W.linForm ^ 2) ^ 2
      + 2 * C W.a₆ * (W.preΨ n ^ 2 * W.linForm ^ 2) ^ 3) * h2'
  · simp only [if_neg (Int.not_even_iff_odd.mpr hn)] at key hΨ ⊢
    rw [hΨ] at key ⊢
    rw [hL] at key
    rw [b₂, b₄, b₆] at key
    simp only [map_ofNat, C_add, C_mul, C_pow] at key ⊢
    linear_combination key + (2 * W.Φ n ^ 3
      + 2 * C W.a₂ * W.Φ n ^ 2 * (W.preΨ n ^ 2 * 1)
      + 2 * C W.a₄ * W.Φ n * (W.preΨ n ^ 2 * 1) ^ 2
      + 2 * C W.a₆ * (W.preΨ n ^ 2 * 1) ^ 3) * h2'

/-! ### The bracket and its vanishing in characteristic `2` -/

variable (W) in
/-- **The numerator `2ωₙ`**, before the `2` is removed:

```
ωBracketₙ = (if Even n then 1 else ψ₂)·preΩₙ − ψₙ·(a₁Φₙ + a₃ΨSqₙ)   ∈ R[X][Y].
```

⚠️ **Its `evalEval` is verbatim the numerator of `Affine.omegaY`**
(`EllipticCurves.Torsion.NsmulYCoord`) — that is `evalEval_ωBracket`, and it is the warrant for
calling this Silverman's `2ωₙ`.  The whole file is the statement that `2` divides it. -/
noncomputable def ωBracket (n : ℤ) : R[X][Y] :=
  (if Even n then 1 else W.ψ₂) * C (W.preΩ n) -
    W.ψ n * C (C W.a₁ * W.Φ n + C W.a₃ * W.ΨSq n)

/-- **`ωBracket` commutes with base change**, which is what lets the divisibility be proved once
over the universal curve. -/
@[simp]
lemma map_ωBracket {S : Type*} [CommRing S] (f : R →+* S) (n : ℤ) :
    (W.map f).ωBracket n = (W.ωBracket n).map (mapRingHom f) := by
  simp only [ωBracket, Polynomial.map_sub, Polynomial.map_mul,
    apply_ite (Polynomial.map (mapRingHom f)), Polynomial.map_one, Polynomial.map_C,
    map_ψ₂, map_ψ, map_preΩ, map_Φ, map_ΨSq, WeierstrassCurve.map_a₁,
    WeierstrassCurve.map_a₃, coe_mapRingHom, Polynomial.map_add, Polynomial.map_C]

/-- **In characteristic `2` the bracket is `C` of a univariate polynomial**, and that polynomial is
the difference of the two sides of `preΩ_mul_eq_of_char_two`. -/
lemma ωBracket_eq_C (h2 : (2 : R) = 0) (n : ℤ) : W.ωBracket n =
    C (W.preΩ n * (if Even n then 1 else W.linForm) -
      W.preΨ n * (if Even n then W.linForm else 1) *
        (C W.a₁ * W.Φ n + C W.a₃ * W.ΨSq n)) := by
  simp only [ωBracket, ψ₂_eq_C_linForm h2, ψ_eq_C h2, map_sub, map_mul, map_one,
    apply_ite (C : R[X] →+* R[X][Y])]
  split_ifs <;> ring

/-- **The bracket vanishes identically in characteristic `2`**, over a domain — the crux packaged
bivariately.  ⚠️ **This is the mod-`2` half of the divisibility and nothing more**: it says
`ωBracketₙ ≡ 0`, not that any particular quotient is distinguished. -/
theorem ωBracket_eq_zero_of_char_two [IsDomain R] (h2 : (2 : R) = 0) (n : ℤ) :
    W.ωBracket n = 0 := by
  rw [ωBracket_eq_C h2, preΩ_mul_eq_of_char_two h2 n, sub_self, map_zero]

/-! ### The descent along the universal curve -/

/-- Divisibility by a constant is detected coefficientwise by a quotient map, one `Polynomial`
layer at a time — the `Polynomial` analogue of `MvPolynomial.C_dvd_iff_map_hom_eq_zero`. -/
private lemma C_dvd_iff_map_eq_zero {A B : Type*} [CommRing A] [CommRing B]
    (q : A →+* B) (r : A) (hr : ∀ a : A, q a = 0 ↔ r ∣ a) (φ : A[X]) :
    C r ∣ φ ↔ φ.map q = 0 := by
  rw [Polynomial.C_dvd_iff_dvd_coeff, Polynomial.ext_iff]
  simp only [coeff_map, coeff_zero, hr]

/-- ⚠️ **`2 ∣ ωBracketₙ` for the universal curve**, at every index — the payload of the descent.

`MvPolynomial (Fin 5) (ZMod 2)` is an integral domain of characteristic `2`, so
`ωBracket_eq_zero_of_char_two` kills the reduction of `univ.ωBracketₙ` mod `2`; and
`MvPolynomial.C_dvd_iff_map_hom_eq_zero`, lifted through the two `Polynomial` layers by
`C_dvd_iff_map_eq_zero`, turns that vanishing back into divisibility over `ℤ`. -/
theorem two_dvd_ωBracket_univ (n : ℤ) :
    (2 : (MvPolynomial (Fin 5) ℤ)[X][Y]) ∣ univ.ωBracket n := by
  have hZ : ∀ a : ℤ, (Int.castRingHom (ZMod 2)) a = 0 ↔ (2 : ℤ) ∣ a := fun a => by
    simpa using ZMod.intCast_zmod_eq_zero_iff_dvd a 2
  have h0 : ∀ a : MvPolynomial (Fin 5) ℤ,
      MvPolynomial.map (Int.castRingHom (ZMod 2)) a = 0 ↔ (2 : MvPolynomial (Fin 5) ℤ) ∣ a := by
    intro a
    rw [← MvPolynomial.C_dvd_iff_map_hom_eq_zero (Int.castRingHom (ZMod 2)) (2 : ℤ) hZ a,
      map_ofNat]
  have h1 : ∀ p : (MvPolynomial (Fin 5) ℤ)[X],
      mapRingHom (MvPolynomial.map (Int.castRingHom (ZMod 2))) p = 0 ↔
        (2 : (MvPolynomial (Fin 5) ℤ)[X]) ∣ p := by
    intro p
    rw [← map_ofNat (C : MvPolynomial (Fin 5) ℤ →+* _) 2,
      C_dvd_iff_map_eq_zero _ _ h0 p]
    rfl
  have h2z : (2 : MvPolynomial (Fin 5) (ZMod 2)) = 0 := by
    have := congrArg (MvPolynomial.C : ZMod 2 →+* MvPolynomial (Fin 5) (ZMod 2))
      (show (2 : ZMod 2) = 0 by decide)
    rwa [map_ofNat, map_zero] at this
  rw [← map_ofNat (C : (MvPolynomial (Fin 5) ℤ)[X] →+* _) 2,
    C_dvd_iff_map_eq_zero _ _ h1]
  have hz := ωBracket_eq_zero_of_char_two
    (W := univ.map (MvPolynomial.map (Int.castRingHom (ZMod 2)))) h2z n
  rwa [map_ωBracket] at hz

/-! ### `ωₙ` itself -/

variable (W) in
/-- **The `y`-coordinate division-polynomial numerator `ωₙ`**, an honest polynomial over every
commutative ring. -/
noncomputable def ωNum (n : ℤ) : R[X][Y] :=
  (two_dvd_ωBracket_univ n).choose.map (mapRingHom W.specialize)

/-- ⚠️ **THE HEADLINE: `2·ωNumₙ = ωBracketₙ`, over EVERY commutative ring and at EVERY index.**

Equivalently, *"`ωₙ` has integral coefficients"* — Silverman AEC III.4 / Exercise 3.7 — as a
theorem about the division polynomials rather than a remark.  ⚠️ **No characteristic hypothesis, no
field, no `IsElliptic`, no index restriction.** -/
theorem two_mul_ωNum (n : ℤ) : 2 * W.ωNum n = W.ωBracket n := by
  have h := (two_dvd_ωBracket_univ n).choose_spec
  calc 2 * W.ωNum n
      = ((2 : (MvPolynomial (Fin 5) ℤ)[X][Y]) * (two_dvd_ωBracket_univ n).choose).map
          (mapRingHom W.specialize) := by
        rw [Polynomial.map_mul, Polynomial.map_ofNat]
        rfl
    _ = (univ.ωBracket n).map (mapRingHom W.specialize) := by rw [← h]
    _ = W.ωBracket n := by rw [← map_ωBracket, univ_map_specialize]

/-- **`ωNum` commutes with base change** — the `ωNum` member of Mathlib's
`map_preΨ` / `map_ΨSq` / `map_Φ` family and of the tree's `map_preΩ`.  ⚠️ **Without it the
definition is inert**, because `ωNum` is built from an `Exists.choose` over the universal ring and
has no other handle. -/
@[simp]
lemma map_ωNum {S : Type*} [CommRing S] (f : R →+* S) (n : ℤ) :
    (W.map f).ωNum n = (W.ωNum n).map (mapRingHom f) := by
  rw [ωNum, ωNum, Polynomial.map_map, specialize_map]
  congr 1
  exact (Polynomial.mapRingHom_comp _ _).symm

/-- **`ωBracket₁ = 2Y`.**  `preΩ₁ = 1`, `ψ₁ = 1`, `Φ₁ = X` and `ΨSq₁ = 1`, so the bracket is
`ψ₂ − (a₁X + a₃)`, which is the `2Y` of `ψ₂`. -/
lemma ωBracket_one : W.ωBracket 1 = 2 * Y := by
  have hpreΩ : W.preΩ 1 = 1 := by
    rw [preΩ, show (1 : ℤ) + 2 = 3 by norm_num, show (1 : ℤ) - 1 = 0 by norm_num,
      show (1 : ℤ) - 2 = -1 by norm_num, show (1 : ℤ) + 1 = 2 by norm_num, preΨ_zero,
      show ((-1 : ℤ)) = -(1 : ℤ) by norm_num, preΨ_neg, preΨ_one, preΨ_two]
    ring
  rw [ωBracket, hpreΩ, if_neg (by decide : ¬Even (1 : ℤ)), ψ_one, Φ_one, ΨSq_one, ψ₂,
    Affine.polynomialY]
  C_simp
  ring

/-- ⚠️ **`ω₁ = Y`** — the classical normalisation, over every commutative ring, and the non-vacuity
check on the whole chain: `ωNum` is an `Exists.choose` and this is the one index at which it is
pinned to a named polynomial.

The `2` is cancelled over `MvPolynomial (Fin 5) ℤ`, a characteristic-`0` domain, and the value is
carried down by `map_ωNum`. -/
@[simp]
theorem ωNum_one : W.ωNum 1 = Y := by
  have huniv : univ.ωNum 1 = Y := by
    have h := two_mul_ωNum (W := univ) 1
    rw [ωBracket_one] at h
    exact mul_left_cancel₀ (a := (2 : (MvPolynomial (Fin 5) ℤ)[X][Y])) (by norm_num) h
  have := map_ωNum (W := univ) W.specialize 1
  rw [univ_map_specialize, huniv, Polynomial.map_X] at this
  exact this

/-! ### The point-level bridge and the `nsmul` payoff -/

namespace Affine

variable {F : Type*} [Field F] {W : Affine F} {x y : F}

/-- **The bracket at a point**, in the shape `Affine.omegaY`'s numerator is written in. -/
lemma evalEval_ωBracket (n : ℤ) :
    (W.ωBracket n).evalEval x y =
      (if Even n then 1 else 2 * y + W.a₁ * x + W.a₃) * (W.preΩ n).eval x -
        (W.ψ n).evalEval x y * (W.a₁ * (W.Φ n).eval x + W.a₃ * (W.ΨSq n).eval x) := by
  simp only [ωBracket, evalEval_sub, evalEval_mul, evalEval_C, eval_add, eval_mul, eval_C,
    apply_ite (Polynomial.evalEval x y), evalEval_one, WeierstrassCurve.ψ₂,
    evalEval_polynomialY]

/-- ⚠️ **THE POINT-LEVEL BRIDGE: `omegaY x y n = ωNumₙ(x, y)/ψₙ(x, y)³`** — the `y`-coordinate the
division polynomials predict, with **no `2`** in it.

⚠️ **`h2` is here and it pays for the LEFT-hand side, not the right.**  `omegaY`'s *definition*
divides by `2`; where `2 = 0` that side is `0/0 = 0` while `ωNumₙ/ψₙ³` is not.  **It does not pay
for `ωNum`**, which is a polynomial over every ring including those.

⚠️ **No `W.Equation x y` and no `ψₙ(x, y) ≠ 0`**, neither of which the identity needs: at a point
where `ψₙ` vanishes both sides are `0` by `div_zero`.  This is strictly stronger than the form
`#2248` item 2 asked for. -/
theorem omegaY_eq (h2 : (2 : F) ≠ 0) (n : ℤ) :
    W.omegaY x y n = (W.ωNum n).evalEval x y / (W.ψ n).evalEval x y ^ 3 := by
  have h := congrArg (Polynomial.evalEval x y) (two_mul_ωNum (W := W) n)
  rw [evalEval_ωBracket] at h
  rw [omegaY, ← h]
  have h2c : Polynomial.evalEval x y (2 : F[X][Y]) = 2 := by
    rw [← map_ofNat (C : F[X] →+* F[X][Y]) 2, evalEval_C, eval_ofNat]
  rw [evalEval_mul, h2c]
  exact mul_div_mul_left _ _ h2

/-- ⚠️ **THE PAYOFF: `n • (x, y) = (Φₙ(x)/ΨSqₙ(x), ωNumₙ(x, y)/ψₙ(x, y)³)`**, the `y`-coordinate
carrying **no `2`** — `nsmul_eq_some_omegaY` with its `ω`-quotient de-halved.

⚠️ **`h2` remains, and this is a correction to `#2248` item 3, which asked for a companion
*"which binds no `h2` at all"*.**  Measured: `nsmul_eq_some_omegaY` spends `h2` at **two** sites and
only one is the halving.  `divY_eq_omegaY`'s is, and `omegaY_eq` removes it.  The other is
`nsmulEqDiv_of_forall_ψ_ne_zero` (`EllipticCurves.Torsion.NsmulLadder`), the **`x`-coordinate /
group-law** half, which no amount of work on `ωₙ` can reach.  ⚠️ **So the residue is the `x`-half's
`h2`, not the `y`-half's**, and removing it is the `hasXCoordFormula_of_two_ne_zero` route that
`#2248` itself rules out of scope — **out of scope from here, not unattainable**: that `h2` is a
binder and not part of the conclusion.

⚠️ **This is the companion of the LADDER form, and the ladder form is not the sharpest
hypothesis the tree has.**  `nsmul_eq_some_ωNum_of_ΨSq_ne_zero` below de-halves
`nsmul_eq_some_omegaY_of_ΨSq_ne_zero` instead — the theorem
`EllipticCurves.Torsion.NsmulYPeriodic`'s own `## Main statements` calls **the headline** — which
reaches the same conclusion at **every** index under `ΨSqₙ(x) ≠ 0` alone, with no ladder and no
`2 ≤ n`.  Both are here because this one is the companion of the statement `#2248` named. -/
theorem nsmul_eq_some_ωNum [DecidableEq F] (h2 : (2 : F) ≠ 0) (hns : W.Nonsingular x y) {n : ℕ}
    (hn : 2 ≤ n) (hψ : ∀ k : ℤ, 1 ≤ k → k ≤ (n : ℤ) → (W.ψ k).evalEval x y ≠ 0) :
    ∃ h' : W.Nonsingular ((W.Φ (n : ℤ)).eval x / (W.ΨSq (n : ℤ)).eval x)
        ((W.ωNum (n : ℤ)).evalEval x y / (W.ψ (n : ℤ)).evalEval x y ^ 3),
      (n • Point.some x y hns : W.Point) = .some _ _ h' := by
  simpa only [omegaY_eq h2] using nsmul_eq_some_omegaY h2 hns hn hψ

/-- ⚠️ **THE PAYOFF UNDER THE SHARPEST HYPOTHESIS THE TREE HAS: the same conclusion at EVERY
index, under `ΨSqₙ(x) ≠ 0` alone** — `nsmul_eq_some_omegaY_of_ΨSq_ne_zero`
(`EllipticCurves.Torsion.NsmulYPeriodic`, **the headline** of that module) with its `ω`-quotient
de-halved.  No ladder hypothesis and no `2 ≤ n`: what it asks here is what
`WeierstrassCurve.Affine.hasXCoordFormula_of_two_ne_zero` asks of the `x`-half.

⚠️ **`h2` remains here for exactly the reason it remains in `nsmul_eq_some_ωNum`** — it is the
`x`-coordinate / group-law half's, not the halving, and the route that would remove it is the one
`#2248` rules out of scope.

⚠️ **Importing `NsmulYPeriodic` for this is what costs this file `+2` modules** (it adds
`EllipticCurves.Torsion.NsmulYPeriodic` and `EllipticCurves.Torsion.NsmulOrder`, and nothing else);
⚠️ **measured at `e4345ae`** by a transitive walk over the
`^(public |private |meta )*import EllipticCurves` lines,
`EllipticCurves.Torsion.NsmulYCoord`'s own closure is untouched at **31** modules **not counting
itself** — the convention `README.md`'s `## Import-closure figures` states — and **32** counting it.
⚠️ **The gap between those two numerals is that convention alone and NOT
`EllipticCurves.UniversalCurve`**, which is already inside the closure either way. -/
theorem nsmul_eq_some_ωNum_of_ΨSq_ne_zero [DecidableEq F] (h2 : (2 : F) ≠ 0)
    (hns : W.Nonsingular x y) {n : ℕ} (hΨ : (W.ΨSq (n : ℤ)).eval x ≠ 0) :
    ∃ h' : W.Nonsingular ((W.Φ (n : ℤ)).eval x / (W.ΨSq (n : ℤ)).eval x)
        ((W.ωNum (n : ℤ)).evalEval x y / (W.ψ (n : ℤ)).evalEval x y ^ 3),
      (n • Point.some x y hns : W.Point) = .some _ _ h' := by
  simpa only [omegaY_eq h2] using nsmul_eq_some_omegaY_of_ΨSq_ne_zero h2 hns hΨ

end Affine

end WeierstrassCurve
