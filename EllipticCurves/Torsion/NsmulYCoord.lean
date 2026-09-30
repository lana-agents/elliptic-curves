/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import EllipticCurves.Torsion.NsmulLadder
import EllipticCurves.Torsion.OmegaCrux
import EllipticCurves.Torsion.TriplingCoords

/-!
# `y(n • P) = ωₙ/(2ψₙ³)` along the ladder: the `y`-half of the coordinate formula

Issue `#1500`.  `EllipticCurves.Torsion.OmegaCrux` proves that the pair `(Φₙ/ΨSqₙ, ωₙ/(2ψₙ³))`
**lies on the curve** at every index over a field with `(2 : F) ≠ 0` and under `ψₙ(x, y) ≠ 0`, and
says in terms that this is *not* a statement about `n • P`.  `EllipticCurves.Torsion.DoublingCoords`
and `EllipticCurves.Torsion.TriplingCoords` identify the second coordinate with `y(n • P)` at
`n = 2` and `n = 3`.  **This file closes the gap between them at every index for which the ladder of
`EllipticCurves.Torsion.NsmulLadder` does not pass through a zero.**

## What was already there, and why this is short

⚠️ **The `y`-coordinate of `n • P` is already on `main`** — the ladder carries one, because it has
to.  `WeierstrassCurve.Affine.nsmulEqDiv_of_forall_ψ_ne_zero` proves
`n • (x, y) = (divX x n, divY x y n)` with

```
divT x y n = ψ₂ₙ(x, y)/ψₙ(x, y)⁴,    divY x y n = (divT x y n − a₁·divX x n − a₃)/2,
```

and `EllipticCurves.Torsion.NsmulLadder`'s own docstring explains that carrying an `x`-coordinate
alone does not close the induction: the *sign* of `ψ₂(n • P)` is what distinguishes `n • P` from
`−n • P`.  So what `#1500` asks for is not a new induction.  **It is the identification of `divY`
with the `ω`-quotient**, and that is one substitution:

```
ψ₂ₙ = ψₙ · (if Even n then 1 else ψ₂) · preΩₙ        (`ψ_two_mul_evalEval`)
```

divided by `ψₙ⁴` and rearranged.  ⚠️ Read this as *"the board priced a rung that was already
built"*, not as *"the `y`-half was easy"*: the content is in `ψ_mul_Ω`, `Ω_factor` and the ladder,
all merged.

## Main definitions and statements

Every public declaration of this file is listed; `some_eq_some_of_eq_snd` is `private`.

* `WeierstrassCurve.Affine.omegaY` : `ωₙ/(2ψₙ³)`, verbatim the second coordinate of
  `WeierstrassCurve.Affine.equation_div_of_ψ_ne_zero`.
* `WeierstrassCurve.Affine.equation_divX_omegaY` : that theorem with both coordinates named —
  `W.Equation (W.divX x n) (W.omegaY x y n)`, with nothing to unfold.  ⚠️ No new content.
* `WeierstrassCurve.Affine.divY_eq_omegaY` : the identification, at any point of `W` with
  `ψ₂(x, y) ≠ 0` and `ψₙ(x, y) ≠ 0`, over a field of characteristic `≠ 2`.
* `WeierstrassCurve.Affine.nsmul_eq_some_omegaY` : **the headline** — under the ladder hypothesis,
  `n • (x, y) = (Φₙ(x)/ΨSqₙ(x), ωₙ/(2ψₙ³))` as a point of `W.Point`.
* `WeierstrassCurve.Affine.omegaY_three_eq` : at `n = 3` the quotient is `ω₃(x, y)/ψ₃(x, y)³`,
  with **no `2`**, over any field with `(2 : F) ≠ 0` and ⚠️ **under no other hypothesis at all**.
* `WeierstrassCurve.Affine.nsmul_three_eq_some_ω₃` : the headline at `n = 3` in that form —
  `3 • (x, y) = (Φ₃(x)/ΨSq₃(x), ω₃(x, y)/ψ₃(x, y)³)`, no `2` in either coordinate.

## ⚠️ What this does *not* prove — ⚠️ **the first item is DISCHARGED downstream, read it**

* **Not the coordinate formula at every index — but that is no longer open.**  The hypothesis here
  is the *ladder* one — `ψ_k(x, y) ≠ 0` for every `1 ≤ k ≤ n` — exactly as in
  `nsmul_eq_some_Φ_div_ΨSq`, and it is strictly stronger than `ψₙ(x, y) ≠ 0`.  The `x`-half was
  lifted off the ladder to every index with `(2 : F) ≠ 0` by
  `WeierstrassCurve.Affine.hasXCoordFormula_of_two_ne_zero` (`EllipticCurves.Torsion.NsmulOrder`)
  through a **third** branch that reduces `n` to `j = n mod d` at the least vanishing index `d` and
  transports along `divX_add_mul_of_not_dvd` — the `d`-periodicity of the `x`-prediction.

  ⚠️ **`WeierstrassCurve.Affine.divY_add_mul_of_not_dvd` and
  `WeierstrassCurve.Affine.nsmul_eq_some_omegaY_of_ΨSq_ne_zero` now exist**
  (`EllipticCurves.Torsion.NsmulYPeriodic`, downstream of this file, issue `#1500`), the latter
  under `ΨSqₙ(x) ≠ 0` alone.  **Nothing in this bullet is open.**  Neither module is imported here
  and neither name is consumed; this file remains the ladder statement.

  ⚠️ **The measurement below is still correct and is why that file does not imitate the `x`-half.**
  Write `r_n = ψ_{n+d}/ψₙ` at a point of order `d`, and `c = ψ_{d+1}·ψ_{d−1}`.  The engine the
  `x`-half consumes — `ψ_mul_ψ_sub_of_ψ_eq_zero`, `ψ_{n+d}·ψ_{n−d} = −c·ψₙ²` — says exactly
  `r_n = −c·r_{n−d}`, a recursion **along the progression `n + dℤ` only**.  Periodicity of the
  `y`-prediction is `T_{n+d} = Tₙ` with `Tₙ = ψ₂ₙ/ψₙ⁴`, which unwinds to
  `r_{2n+d}·r_{2n} = r_n⁴`, i.e. to `−c·r_{2n}² = r_n⁴` — a relation between `r` at `n` and at
  `2n` that the shift engine does not supply.  ⚠️ What *does* supply it is a **different** Ward
  instance, `(p, q, r) = (m + d, k, m)`, whose third term is killed by `ψ_{−d} = 0` and which gives
  `r_{m+k}·r_{m−k} = rₘ²` at every `k`; see `EllipticCurves.Torsion.NsmulYPeriodic`.  ⚠️ The
  addition-law route sketched here previously was **not** the one taken, and at `d = 3` the
  statement is not a consequence of Ward at all.

  The numerical check recorded here — over `𝔽₁₀₁₉`, `T_{n+d} = Tₙ` and `Tₙ = 2·y(n • P)` at every
  `n` with `d ∤ n`, with negative controls that fire — is now redundant but was not wrong.
* **Nothing about `2`-torsion.**  `ψ₂(x, y) ≠ 0` is not decoration: `ψ_two_mul_evalEval` cancels a
  common factor of `ψ₂` and carries no information where it vanishes.  For `2 ≤ n` the ladder
  hypothesis supplies it; at `n = 1` the statement is `one_smul` and needs nothing.
* **Nothing about the function field.**  The ~40 `#251` bullets under `FunctionField/WeilPairing*`
  that mean the `y`-half are untouched by *this* file.  ⚠️ They are swept in `#1504`, and — since
  `EllipticCurves.Torsion.NsmulYPeriodic` closed the `y`-half at every index — that sweep
  **retires** them rather than relettering them; do not go looking for a reletter.

## Import position, measured rather than guessed

⚠️ **The convention, because the `22` below counts the module it is named for while the `31` does
not count this file, and `README.md` `## Import-closure figures` says it *"belongs beside the
figure and must not be assumed"*.**  A count named for *another* module is that module **and**
everything it reaches; a count of what *this* file costs **excludes this file**.  **Measured at
`e4345ae`**, over `EllipticCurves.` only, with the root aggregator `EllipticCurves` dropped, on two
instruments that agree on every cell: the elaborator's `(← Lean.getEnv).header.moduleNames`, read
from a probe module that *imports* the module being measured — ⚠️ **the placement is part of that
instrument and is what fixes its convention: read from an importer the answer carries the measured
module, read from inside that module it does not** — and a transitive walk of the
`^(public |private |meta )*import (\S+)` lines, which needs no build.  Control, as that section
publishes it: `EllipticCurves.TateModule.MatrixRepMod` is **40** excluding itself and **41**
including it.  ⚠️ `EllipticCurves.Torsion.NsmulYPeriodic` reads its figures the same way.

`EllipticCurves.Torsion.NsmulLadder` has a transitive closure of 22 modules in this library and
`EllipticCurves.Torsion.TriplingCoords` of 18; ⚠️ **their union is 25, and that 25 does not count
this file** — neither reaches the other and they share 15 modules, `22 + 18 - 15 = 25`.
Adding `EllipticCurves.Torsion.OmegaCrux` takes it to **31** — six modules (`Collinearity`,
`NetVieta`, `OmegaCharZero`, `OmegaUniversal`, `UniversalCurve`, `OmegaCrux`) — and **31** is this
file's own closure with this file excluded, **32** counting it.  ⚠️ That cost is paid
deliberately: without it `omegaY` would be a fresh definition with no stated relation to the
on-curve identity, and the whole point of this file is that the two coordinates are the same one.

## References

* [J. H. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.4 and Exercise 3.7 —
  `2ωₙ = ψ₂ₙ/ψₙ − ψₙ·(a₁Φₙ + a₃ΨSqₙ)`, which is `omegaY` cleared of its denominator.
-/

open Polynomial Polynomial.Bivariate

namespace WeierstrassCurve.Affine

variable {F : Type*} [Field F] {W : Affine F} {x y : F}

/-- **The `y`-coordinate the division polynomials predict for `n • (x, y)`, in `ω`-form**:

```
ωₙ/(2ψₙ³) = ((if Even n then 1 else ψ₂)·preΩₙ(x) − ψₙ(x,y)·(a₁Φₙ(x) + a₃ΨSqₙ(x))) / (2ψₙ(x,y)³).
```

This is verbatim the second coordinate of `WeierstrassCurve.Affine.equation_div_of_ψ_ne_zero`, so
that theorem reads `W.Equation (W.divX x n) (W.omegaY x y n)` — see `equation_divX_omegaY`.

⚠️ It is *not* `WeierstrassCurve.Affine.divY`, which is defined from `divT = ψ₂ₙ/ψₙ⁴`.  The two
agree at a point where `ψ₂` and `ψₙ` do not vanish (`divY_eq_omegaY`), and that agreement is the
content of this file. -/
noncomputable def omegaY (W : Affine F) (x y : F) (n : ℤ) : F :=
  ((if Even n then 1 else 2 * y + W.a₁ * x + W.a₃) * (W.preΩ n).eval x -
      (W.ψ n).evalEval x y * (W.a₁ * (W.Φ n).eval x + W.a₃ * (W.ΨSq n).eval x)) /
    (2 * (W.ψ n).evalEval x y ^ 3)

/-- **The on-curve identity, in the vocabulary of this file.**  ⚠️ No new content: this is
`WeierstrassCurve.Affine.equation_div_of_ψ_ne_zero` (`EllipticCurves.Torsion.OmegaCrux`, issue
`#404`) with both coordinates named.  It says the predicted pair lies on `W`; it says nothing
about `n • P`, and the gap is what `nsmul_eq_some_omegaY` closes. -/
theorem equation_divX_omegaY (h : W.Equation x y) (h2 : (2 : F) ≠ 0) {n : ℤ}
    (hψ : (W.ψ n).evalEval x y ≠ 0) : W.Equation (W.divX x n) (W.omegaY x y n) :=
  equation_div_of_ψ_ne_zero h h2 hψ

/-- **The two predicted `y`-coordinates agree.**  `divY` is built from `divT = ψ₂ₙ/ψₙ⁴`, which is
what makes the ladder induction close; `omegaY` is built from `preΩₙ`, which is what the on-curve
identity is stated with.  The bridge is the index-doubling formula
`WeierstrassCurve.Affine.ψ_two_mul_evalEval`, `ψ₂ₙ = ψₙ·(if Even n then 1 else ψ₂)·preΩₙ`.

⚠️ `hψ₂` is where the hypothesis is spent, not `h2`: `ψ_two_mul_evalEval` cancels a factor of `ψ₂`
at the point and is vacuous at the `2`-torsion points.  `h2` only undoes the halving in `divY`. -/
theorem divY_eq_omegaY (h : W.Equation x y) (h2 : (2 : F) ≠ 0)
    (hψ₂ : (W.ψ 2).evalEval x y ≠ 0) {n : ℤ} (hψ : (W.ψ n).evalEval x y ≠ 0) :
    W.divY x y n = W.omegaY x y n := by
  have hsq : (W.ΨSq n).eval x = (W.ψ n).evalEval x y ^ 2 := (ψ_sq_evalEval h n).symm
  have hdbl := ψ_two_mul_evalEval h hψ₂ n
  rw [divY, divT, divX, omegaY, hdbl, hsq, ψ_two_evalEval]
  field_simp
  ring

/-- **At `n = 3` the predicted `y`-coordinate is `ω₃/ψ₃³`, with no `2` in the quotient.**
`omegaY`'s numerator at an odd index is `ψ₂·preΩₙ − ψₙ·(a₁Φₙ + a₃ΨSqₙ)`, and at `n = 3` that
bracket is `2·ω₃` on the nose — `WeierstrassCurve.two_mul_ω₃`, an identity of polynomials over
**every** commutative ring — so the two `2`s cancel and `ω₃` is what is left.  ⚠️ **That lemma names
the content but is not what the proof below cites.**  The proof rebuilds the evaluated form from
`WeierstrassCurve.two_mul_preω₃` — which is what `two_mul_ω₃` is itself proved from — through
`congrArg (Polynomial.eval x)` and `WeierstrassCurve.evalEval_ω₃`.  **Grep the proof for
`two_mul_ω₃` and it is not there; the citation is to the identity, not to the tactic.**

⚠️ **`h2` pays for `omegaY`'s own definition and for nothing else.**  The left-hand side divides by
`2ψ₃³`; the right-hand side's `ω₃` is an honest polynomial of
`EllipticCurves.Torsion.OmegaDivisionPolynomial` and its quotient by `ψ₃³` asks nothing of the
characteristic.  This is that file's *"the `2` is presentational at `n = 3`"* carried up to the
`y`-coordinate the ladder actually predicts, and `WeierstrassCurve.Affine.tripling_equation_ω₃`
(`EllipticCurves.Torsion.OmegaThree`) is the same `y`-value one layer down, in `Equation` form.

⚠️ **Neither `W.Equation x y` nor `ψ₃(x, y) ≠ 0` is needed, and issue `#2246` predicted both.**
No point hypothesis, and ⚠️ **the reason is special to `n = 3` — neither *shape* nor *parity*.**
`WeierstrassCurve.ψ_three` (`W.ψ 3 = C W.Ψ₃`) makes `ψ₃` the image of a polynomial in `x` alone, so
with `WeierstrassCurve.ΨSq_three` (`ΨSq₃ = Ψ₃²`) the identity `ψ₃(x, y)² = ΨSq₃(x)` holds at
**every** pair `(x, y)` over **every** commutative ring, on `W` or off it.  That is why
`ψ_sq_evalEval` — the same identity at a general `n`, which binds `W.Equation x y` — never runs.

⚠️⚠️ **Do NOT generalise that along the odd indices: `ψ₃` is `ψ₂`-free and `ψ₅` is not.**
`WeierstrassCurve.ψ_odd` at `m = 2` gives only the RECURRENCE
`W.ψ 5 = ψ 4 * ψ 2 ^ 3 - ψ 1 * ψ 3 ^ 3`; unfolding its four `ψ`-terms by `ψ_four`, `ψ_two`,
`ψ_one` and `ψ_three`, then `map_pow` for `(C Ψ₃)³`, gives
`W.ψ 5 = C preΨ₄ * ψ₂ ^ 4 - C (Ψ₃ ^ 3)`, carrying
`ψ₂ = 2Y + a₁X + a₃` to the fourth power, and `ψ₂²` is `Ψ₂Sq` only modulo the curve equation — so
the `n = 5` instance really does need the point.  ⚠️ **Witness, at a pair the `n = 3` instance
goes through anyway**: on `y² = x³ + 1` over `ZMod 7` the pair `(0, 0)` is off the curve, and there
`ψ₅(0, 0)² = 0` while `ΨSq₅(0) = 2`, whereas `ψ₃(0, 0)² = ΨSq₃(0)` still holds.  **An `n = 5` rung
inherits nothing from this proof, and there is no `ψ_five` to inherit it with — `ψ_odd` is the
recurrence, not a `C`-form.**

⚠️ **And the proof below DOES convert `ΨSq₃`, at `ΨSq_three` and `hs`: what it avoids is
`ψ_sq_evalEval`, not the conversion.**
⚠️ Routing through `tripling_equation` instead *would* want a point, that being a statement about
one, and that is the only reason the predicted signature carried it.  No non-vanishing hypothesis,
because `mul_div_mul_left` cancels the `2` whatever `ψ₃(x, y)` is: where it vanishes both sides are
`0`.  ⚠️ Contrast `divY_eq_omegaY` directly above, which needs a point **and** `ψ₂(x, y) ≠ 0` —
`divY` is built from `divT = ψ₂ₙ/ψₙ⁴` and the bridge to it cancels a `ψ₂`, which is information only
away from `2`-torsion. -/
theorem omegaY_three_eq (h2 : (2 : F) ≠ 0) :
    W.omegaY x y 3 = W.ω₃.evalEval x y / (W.ψ 3).evalEval x y ^ 3 := by
  have hs : (W.ψ 3).evalEval x y = W.Ψ₃.eval x := by rw [ψ_three]; simp [evalEval]
  have hpre : 2 * W.preω₃.eval x = (W.a₁ * x + W.a₃) * (W.preΩ 3).eval x -
      W.a₁ * (W.Φ 3).eval x * W.Ψ₃.eval x - W.a₃ * W.Ψ₃.eval x ^ 3 := by
    have h' := congrArg (Polynomial.eval x) W.two_mul_preω₃
    simpa only [eval_mul, eval_sub, eval_add, eval_pow, eval_ofNat, eval_C, eval_X] using h'
  have hnum : (2 * y + W.a₁ * x + W.a₃) * (W.preΩ 3).eval x -
      (W.ψ 3).evalEval x y * (W.a₁ * (W.Φ 3).eval x + W.a₃ * (W.ΨSq 3).eval x) =
      2 * W.ω₃.evalEval x y := by
    rw [evalEval_ω₃, ΨSq_three, eval_pow, hs]
    linear_combination -hpre
  rw [omegaY, if_neg (by decide : ¬Even (3 : ℤ)), hnum, mul_div_mul_left _ _ h2]

section Point

variable [DecidableEq F]

omit [DecidableEq F] in
/-- `Point.some` is insensitive to a proved equality between its `y`-arguments. -/
private lemma some_eq_some_of_eq_snd {y₁ y₂ : F} (h₁ : W.Nonsingular x y₁)
    (h₂ : W.Nonsingular x y₂) (h : y₁ = y₂) :
    (Point.some x y₁ h₁ : W.Point) = .some x y₂ h₂ := by
  subst h; rfl

/-- **`n • (x, y) = (Φₙ(x)/ΨSqₙ(x), ωₙ/(2ψₙ³))`** — the `y`-half of the coordinate formula, with
`(2 : F) ≠ 0`, at every index `n ≥ 2` whose ladder `ψ₁, …, ψₙ` has no zero.

This is `WeierstrassCurve.Affine.nsmul_eq_some_Φ_div_ΨSq` with its anonymous `y'` identified: that
theorem produces `divY x y n`, and `divY_eq_omegaY` says it is the `ω`-quotient.

⚠️ The hypothesis is the **ladder** one and is strictly stronger than `ψₙ(x, y) ≠ 0`.  ⚠️ It is
**not** the sharp statement: `WeierstrassCurve.Affine.nsmul_eq_some_omegaY_of_ΨSq_ne_zero`
(`EllipticCurves.Torsion.NsmulYPeriodic`, `#1500`) proves the same conclusion at every index under
`ΨSqₙ(x) ≠ 0` alone, and consumes this theorem as its ladder branch.

⚠️ `2 ≤ n` is not a restriction of the mathematics but of the bookkeeping: it is how
`ψ₂(x, y) ≠ 0` is obtained from `hψ`, and at `n = 1` the statement is `one_smul` with
`divY_one`. -/
theorem nsmul_eq_some_omegaY (h2 : (2 : F) ≠ 0) (hns : W.Nonsingular x y) {n : ℕ} (hn : 2 ≤ n)
    (hψ : ∀ k : ℤ, 1 ≤ k → k ≤ (n : ℤ) → (W.ψ k).evalEval x y ≠ 0) :
    ∃ h' : W.Nonsingular ((W.Φ (n : ℤ)).eval x / (W.ΨSq (n : ℤ)).eval x) (W.omegaY x y (n : ℤ)),
      (n • Point.some x y hns : W.Point) = .some _ _ h' := by
  have hn2 : (2 : ℤ) ≤ (n : ℤ) := by exact_mod_cast hn
  have hψ₂ : (W.ψ 2).evalEval x y ≠ 0 := hψ 2 one_le_two hn2
  have hψn : (W.ψ (n : ℤ)).evalEval x y ≠ 0 := hψ (n : ℤ) (by omega) le_rfl
  have hY : W.divY x y (n : ℤ) = W.omegaY x y (n : ℤ) :=
    divY_eq_omegaY hns.left h2 hψ₂ hψn
  obtain ⟨h', heq⟩ := nsmulEqDiv_of_forall_ψ_ne_zero h2 hns (by omega) hψ
  have h'' : W.Nonsingular ((W.Φ (n : ℤ)).eval x / (W.ΨSq (n : ℤ)).eval x)
      (W.omegaY x y (n : ℤ)) := by
    rw [← hY]; exact h'
  refine ⟨h'', ?_⟩
  rw [← natCast_zsmul, heq]
  exact some_eq_some_of_eq_snd h' h'' hY

/-- **`3 • (x, y) = (Φ₃(x)/ΨSq₃(x), ω₃(x, y)/ψ₃(x, y)³)`** — the headline at `n = 3` with no `2` in
either coordinate, as a point of `W.Point`.  This is `nsmul_eq_some_omegaY` at `n = 3` with its
`y`-coordinate rewritten by `omegaY_three_eq`; the hypotheses are `nsmul_eq_some_omegaY`'s at
`n = 3`, with its `hn : 2 ≤ n` discharged by `norm_num`.  ⚠️ **Named rather than left as *that
theorem's*, whose nearest antecedent is `omegaY_three_eq` — which binds `h2` alone, while this
corollary binds three.**

⚠️ **The `h2` is INHERITED and the `2` this removes is the STATEMENT's, not a hypothesis.**  It is
spent by the ladder inside `nsmulEqDiv_of_forall_ψ_ne_zero` and again by `omegaY`'s halving, and
neither spend is presentational: what a `2`-free numerator buys is that the expression being
divided is defined in characteristic `2`, never that the field may have characteristic `2`.  ⚠️ So
do **not** read this as a step toward dropping `h2` from `nsmul_eq_some_omegaY` — that would be a
different statement, and issue `#2246` rules it out of scope in terms.

⚠️ The hypothesis is the **ladder** one and is strictly stronger than `ψ₃(x, y) ≠ 0`, exactly as in
`nsmul_eq_some_omegaY`; ⚠️ `omegaY_three_eq` itself needs neither. -/
theorem nsmul_three_eq_some_ω₃ (h2 : (2 : F) ≠ 0) (hns : W.Nonsingular x y)
    (hψ : ∀ k : ℤ, 1 ≤ k → k ≤ 3 → (W.ψ k).evalEval x y ≠ 0) :
    ∃ h' : W.Nonsingular ((W.Φ 3).eval x / (W.ΨSq 3).eval x)
        (W.ω₃.evalEval x y / (W.ψ 3).evalEval x y ^ 3),
      (3 • Point.some x y hns : W.Point) = .some _ _ h' := by
  have hY : W.omegaY x y 3 = W.ω₃.evalEval x y / (W.ψ 3).evalEval x y ^ 3 := omegaY_three_eq h2
  obtain ⟨h', heq⟩ := nsmul_eq_some_omegaY (n := 3) h2 hns (by norm_num) (by simpa using hψ)
  have h'' : W.Nonsingular ((W.Φ (3 : ℤ)).eval x / (W.ΨSq (3 : ℤ)).eval x)
      (W.ω₃.evalEval x y / (W.ψ 3).evalEval x y ^ 3) := by rw [← hY]; exact h'
  refine ⟨h'', ?_⟩
  rw [heq]
  exact some_eq_some_of_eq_snd h' h'' hY

end Point

/-! ## ⚠️ Non-vacuity: the general `y`-formula against the two merged hand computations

None of the three `example`s is new content.  `WeierstrassCurve.Affine.addY_self_eq_div`
(`EllipticCurves.Torsion.DoublingCoords`) and `WeierstrassCurve.Affine.addY_add_self_eq_div`
(`EllipticCurves.Torsion.TriplingCoords`) compute `y(2 • P)` and `y(3 • P)` by hand from the group
law.  ⚠️ They are **stronger** than the instances below in one respect — neither needs the ladder —
and they are the check that `omegaY` evaluates to the right thing where an independent computation
exists.  A general formula that failed to specialise to them would break the build here.

⚠️ **The third one is why `omegaY_three_eq`'s `y`-coordinate is a fact about `y(3 • P)` and not
merely a name for a quotient**, and it is the only one of the three whose **conclusion** is stated
in the `2`-free quotient rather than in `omegaY`.  ⚠️ **Say it that way, and not *whose statement
contains no `2` anywhere*, which is false of all three**: each binds `h2 : (2 : F) ≠ 0`, the third
one included, and that `example`'s own docstring says so.  ⚠️ **Nor does
*conclusion* alone separate them** — the second `example`'s conclusion writes `omegaY x y 3`, which
carries no `2` in the source text either, and only unfolding `omegaY` exposes the one it divides by.
**The unit is the conclusion with `omegaY` unfolded, and a claim about a `2` has to name it.**  The
third one's tactic chain is the second one's, re-run after `omegaY_three_eq` folds the `2` away;
that repetition is deliberate, since the second `example` has no name to cite.
-/

section Nonvacuity

variable [DecidableEq F]

/-- `ωₙ/(2ψₙ³)` at `n = 2` is `y(2 • P)` as `addY_self_eq_div` computes it: the parity factor is
the even branch, `preΩ₂ = preΨ₄` and `ΨSq₂ = Ψ₂Sq`, and nothing else moves. -/
example (h : W.Equation x y) (h2 : (2 : F) ≠ 0) (hy : y ≠ W.negY x y) :
    W.omegaY x y 2 = W.addY x x y (W.slope x x y y) := by
  rw [addY_self_eq_div h h2 hy, omegaY, if_pos even_two, one_mul, preΩ_two, ΨSq_two]

/-- `ωₙ/(2ψₙ³)` at `n = 3` is `y(3 • P)` as `addY_add_self_eq_div` computes it: the parity factor
is the odd branch `ψ₂ = 2y + a₁x + a₃`, `preΩ₃ = preΨ₅ − preΨ₄²`, and `ΨSq₃ = ψ₃²` turns
`ψ₃·a₃·ΨSq₃` into that computation's `a₃·ψ₃³`. -/
example (h : W.Equation x y) (h2 : (2 : F) ≠ 0) (hy : y ≠ W.negY x y)
    (hT : W.Ψ₃.eval x ≠ 0) :
    W.omegaY x y 3
      = W.addY (W.addX x x (W.slope x x y y)) x (W.addY x x y (W.slope x x y y))
          (W.slope (W.addX x x (W.slope x x y y)) x (W.addY x x y (W.slope x x y y)) y) := by
  rw [addY_add_self_eq_div h2 h hy hT, omegaY, if_neg (by decide : ¬ Even (3 : ℤ)), preΩ_three,
    ← ψ_sq_evalEval h 3]
  simp only [eval_sub, eval_pow]
  ring

/-- ⚠️ **The `2`-free `n = 3` quotient is that same hand computation**: `ω₃(x, y)/ψ₃(x, y)³` is
`y(3 • P)` as `addY_add_self_eq_div` computes it from the group law.  ⚠️ **`h2` survives here and
that is not an oversight** — it is `addY_add_self_eq_div`'s own, and this `example` pins a
`y`-value rather than widening a characteristic. -/
example (h : W.Equation x y) (h2 : (2 : F) ≠ 0) (hy : y ≠ W.negY x y)
    (hT : W.Ψ₃.eval x ≠ 0) :
    W.ω₃.evalEval x y / (W.ψ 3).evalEval x y ^ 3
      = W.addY (W.addX x x (W.slope x x y y)) x (W.addY x x y (W.slope x x y y))
          (W.slope (W.addX x x (W.slope x x y y)) x (W.addY x x y (W.slope x x y y)) y) := by
  rw [← omegaY_three_eq h2, addY_add_self_eq_div h2 h hy hT, omegaY,
    if_neg (by decide : ¬ Even (3 : ℤ)), preΩ_three, ← ψ_sq_evalEval h 3]
  simp only [eval_sub, eval_pow]
  ring

end Nonvacuity

end WeierstrassCurve.Affine
