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

Issue `#1500`.  `EllipticCurves.Torsion.OmegaCrux` proves that the pair
`(Φₙ/ΨSqₙ, ωₙ/(2ψₙ³))` **lies on the curve** at every index over every commutative ring, and says
in terms that this is *not* a statement about `n • P`.  `EllipticCurves.Torsion.DoublingCoords` and
`EllipticCurves.Torsion.TriplingCoords` identify the second coordinate with `y(n • P)` at `n = 2`
and `n = 3`.  **This file closes the gap between them at every index for which the ladder of
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

`EllipticCurves.Torsion.NsmulLadder` has a transitive closure of 22 modules in this library and
`EllipticCurves.Torsion.TriplingCoords` of 18; their union with this file is 25.  Adding
`EllipticCurves.Torsion.OmegaCrux` takes it to **31** — six modules (`Collinearity`, `NetVieta`,
`OmegaCharZero`, `OmegaUniversal`, `UniversalCurve`, `OmegaCrux`).  ⚠️ That cost is paid
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

end Point

/-! ## ⚠️ Non-vacuity: the general `y`-formula against the two merged hand computations

Neither `example` is new content.  `WeierstrassCurve.Affine.addY_self_eq_div`
(`EllipticCurves.Torsion.DoublingCoords`) and `WeierstrassCurve.Affine.addY_add_self_eq_div`
(`EllipticCurves.Torsion.TriplingCoords`) compute `y(2 • P)` and `y(3 • P)` by hand from the group
law.  ⚠️ They are **stronger** than the instances below in one respect — neither needs the ladder —
and they are the check that `omegaY` evaluates to the right thing where an independent computation
exists.  A general formula that failed to specialise to them would break the build here.
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

end Nonvacuity

end WeierstrassCurve.Affine
