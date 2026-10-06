/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import EllipticCurves.Torsion.NsmulLadderOmegaStepNum

/-!
# `W.polynomial ∣ W.stepNum n` over every commutative ring, and the ladder with no `(2 : F) ≠ 0`

`EllipticCurves.Torsion.NsmulLadderOmegaStepNum` reduced the characteristic-`2` ladder step to one
polynomial divisibility and proved the reduction in both directions, leaving the divisibility itself
**unproved at every index past `n = 1`**: every theorem there takes `W.polynomial ∣ W.stepNum n` as
a hypothesis.  **This file proves it, at every integer index and over every commutative ring, and
instantiates those theorems.**

```
theorem polynomial_dvd_stepNum (W : WeierstrassCurve R) (n : ℤ) :
    W.toAffine.polynomial ∣ W.stepNum n
```

⚠️ **No field, no characteristic hypothesis, no `IsElliptic`, no genericity, no index restriction.**
With it, `nsmulEqDivω_of_forall_ψ_ne_zero`, `nsmul_eq_some_divX_divYω` and
`exists_ψ_evalEval_eq_zero_of_nsmul_eq_zero'` below are the `ω`-flavoured ladder, the coordinate
formula `n • P = (Φₙ/ΨSqₙ, ωNumₙ/ψₙ³)` and the `n • P = 0 ⇒ some ψₖ(P) = 0` half of the
division-polynomial dictionary **with `(2 : F) ≠ 0` deleted and nothing put in its place** — and
`nsmulEqDivω_three_curveCharTwoOne` is the rung at `n = 3` over `ZMod 2`, which was the landed
module's `example` conditional on exactly this hypothesis and is now a theorem.

## Which route this takes, and why

`#2347` recorded two routes and costed neither.  **This file takes route (ii), the generic point**,
and route (i) — `2·stepNum·ψ₂ᵏ = polynomial·G` over an arbitrary ring with both factors cancelled
over `MvPolynomial (Fin 5) ℤ` — is **not** attempted here.  The reason is that route (i) needs an
explicit cofactor `G` written down, in the shape
`EllipticCurves.Torsion.OmegaOnCurveCharFree`'s `exists_four_mul_divPairNum` has, and route (ii)
needs **no cofactor at all**: the divisibility is transported as a divisibility and never as an
equation.

The argument is three steps, and only the middle one is about the step:

1. **The generic point.** Over a field `F` of characteristic `0`, the class of `p ∈ F[X][Y]` in the
   function field `F(W)` vanishes iff `W.polynomial ∣ p`, because `F[W] = F[X][Y]/⟨W.polynomial⟩`
   is a domain and embeds in its fraction field.  So the divisibility becomes **one vanishing at one
   point of one curve**.
2. **The landed `h2`-bound ladder, run at that point.** `F(W)` has characteristic `0`, so
   `(2 : F(W)) ≠ 0` and `EllipticCurves.Torsion.NsmulLadder`'s `nsmulEqDiv_of_forall_ψ_ne_zero`
   applies to the generic point — `ψₖ` does not vanish there at any `k ≠ 0` — which supplies the
   `x`-half `hX` that `addX_divYω_eq` needs, and then
   `evalEval_stepNum_eq_zero_of_two_ne_zero` is the vanishing.
   ⚠️ **So the characteristic-free statement is proved BY the characteristic-restricted one**, at a
   point where the restriction is free; nothing is re-proved in characteristic `2`.
3. **Descent, with no cofactor.** `W.polynomial` is **monic** in `Y`
   (Mathlib's `Affine.monic_polynomial`), so `Polynomial.map_dvd_map` reverses the divisibility
   along the injection `MvPolynomial (Fin 5) ℤ ↪ FractionRing (MvPolynomial (Fin 5) ℤ)`, giving it
   over the universal ring; `map_stepNum` and `Affine.map_polynomial` then carry it to every
   commutative ring along `WeierstrassCurve.specialize`.

⚠️ **Three indices are not reachable by step 2 and are computed instead**: `n = 1` is the landed
`stepNum_one`, and `n = 0` and `n = -1` are `stepNum_zero_of_charZero` and
`stepNum_neg_one_of_charZero` below — the ladder needs `ψₖ ≠ 0` at `k = n - 1, n, n + 1` and `ψ₀`
is `0`.  Both are genuinely `0`, and the second is the only one that is not immediate: it is
`ψ₂·(Φ₀ − ωNum₀)` with `Φ₀ = 1` (Mathlib) and `ωNum₀ = 1`, so it cancels.  ⚠️ **Had `ωNum₀` been
`0`, `stepNum (-1)` would have been `ψ₂`, which `W.polynomial` does not divide, and the landed
`∀ k : ℤ` hypothesis would have been unsatisfiable rather than merely unproved.**  `ωNum₀ = 1`
because `preΩ₀ = preΨ₂·preΨ₋₁² − preΨ₋₂·preΨ₁² = 1 + 1 = 2` (`preΩ_zero`).

## The parity of the index, which step 2 needs and the tree did not have

`nsmulEqDiv_of_forall_ψ_ne_zero` is indexed by `ℕ`, and step 2 needs the rungs at `n - 1` and `n`
for **every** nonzero `n : ℤ`, negative ones included.  `nsmulEqDivω_neg` supplies them from the
positive ones, and its content is `divYω_neg`:

```
divYω x y (-n) = negY (divX x n) (divYω x y n),
```

the `y`-coordinate of `-(n • P)`, which rests on the parity of `ωNum`:

```
2·ωNumₙ₋ = 2·(ωNumₙ + ψₙ·(a₁Φₙ + a₃ΨSqₙ))     (two_mul_ωNum_neg, every commutative ring)
```

⚠️ **The doubled form is the honest one over an arbitrary ring**, because `ωNum` is pinned only
through `2·ωNumₙ = ωBracketₙ`; the undoubled `ωNum_neg_of_charZero` is stated over a field of
characteristic `0`, which is where this file consumes it.  The general-ring form would follow by
the same descent as `polynomial_dvd_stepNum` and is not needed here.

## ⚠️ Overlap with PR #941, measured rather than assumed

⚠️⚠️ **PR #941 (`#2250` round 6, `EllipticCurves/Torsion/NsmulLadderOmegaY.lean`) is open and
unmerged at this file's base, and it reaches the `h2`-free `ω`-ladder by a DIFFERENT route.**  It is
cited here as a pull request and not as a module of this tree: nothing below imports it or depends
on it, exactly as `NsmulLadderOmegaStepNum` cites PR #931.

Its route is a different cleared numerator — `stepNumω`, which leaves the group law's `addX`
unexpanded and so needs **one** identity where `stepNum` needs the `x`-half `hX` as well — descended
from an algebraically closed field of characteristic `0` through *"vanishes at every point above
infinitely many `x`"*.  ⚠️ **It deliberately does NOT prove `W.polynomial ∣ W.stepNum n`**, which is
`#2347`'s deliverable 1 and is what this file proves; and it leaves every `_of_dvd` theorem of
`EllipticCurves.Torsion.NsmulLadderOmegaStepNum` with its hypothesis live, which is what the
corollaries below discharge.

⚠️ **Where the two rounds do meet is exactly two propositions, and the names are measured**: over
all **48** open pull requests, the declaration names added by any of them intersect the names
declared here in exactly **two** members, both PR #941's — `nsmulEqDivω_of_forall_ψ_ne_zero` and
`nsmulEqDivω_three_curveCharTwoOne`, both of whose statements are character-for-character the ones
proved below.  **Both are primed here**, so the tree builds whichever lands first and neither
shadows the other.  ⚠️ **If both land, a later round should retire one of each pair** — and until
then the pair is a cross-check and not a redundancy: two independent numerators, two independent
descents, one conclusion.  ⚠️ **This file does not attempt to pre-empt that choice**, and it does
not touch `#2250` or its row.

## Placement

⚠️ **Everything the generic point needs is built inside this file from Mathlib alone, and nothing
from `EllipticCurves.FunctionField` is imported.**  That layer already has
`CoordinateRing.genX`, `genY`, `equation_gen` and `ψ_gen_ne_zero`
(`EllipticCurves.FunctionField.TranslationPullback` / `MulByNXCoordFormula` /
`MulByNYCoordFormula`), and they are **above** `Torsion` in the import order — **no file under
`EllipticCurves/Torsion/` imports `EllipticCurves/FunctionField/`** — while the divisibility is
consumed **below** it, by the ladder and its consumers.  So the five generic-point facts here are
`private`, are never exported, and carry no public name that could collide with that layer's: the
duplication is one proof's worth of plumbing and it buys the layering.  ⚠️ **`preΩ_zero`,
`ωBracket_zero` and `two_mul_ωNum_neg` would sit more naturally in
`EllipticCurves.Torsion.OmegaDivisionPolynomial` and `EllipticCurves.Torsion.OmegaIntegral`
beside `preΩ_two` / `preΩ_three` / `ωBracket_one`**; they are here because this round's unit is one
new file and no edit to a landed one.

## What is **not** here

* ⚠️ **No landed statement is weakened, restated or deprecated, and no signature changes.**  The
  `_of_dvd` theorems keep their hypothesis and their proofs; the corollaries below **instantiate**
  them.
* ⚠️ **No claim about `n • P = 0 ↔ ψₙ(P) = 0`.**  `exists_ψ_evalEval_eq_zero_of_nsmul_eq_zero'` is
  one direction with the vanishing index not pinned to `n`; re-proving
  `EllipticCurves.Torsion.NsmulOrder` free of `h2` is `#2340` item 3 and is downstream of this file.
* ⚠️ **Nothing about the Tate module** (`#2340` items 4 and 5), and nothing about the Weil pairing
  in characteristic `2` (`#2342`).
* ⚠️ **`(ℓ : F) ≠ 0` is nowhere removed and `ℓ = 2` in characteristic `2` is still false** rather
  than unproved; this file reaches the ladder and not that headline.

## References

* [J. Silverman, *The arithmetic of elliptic curves*][silverman2009], Exercise 3.7.
-/

open Polynomial

open scoped Polynomial.Bivariate

namespace WeierstrassCurve

local macro "C_simp" : tactic =>
  `(tactic| simp only [map_ofNat, C_0, C_1, C_neg, C_add, C_sub, C_mul, C_pow])

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R)

/-! ### The index-`0` and index-reflection values of `preΩ`, `ωBracket` and `ωNum` -/

/-- **`preΩ₀ = 2`.**  `preΩ₀ = preΨ₂·preΨ₋₁² − preΨ₋₂·preΨ₁²`, and `preΨ₂ = preΨ₁ = 1` with
`preΨ₋ₙ = −preΨₙ`, so it is `1 − (−1) = 2`.

⚠️ **This `2` is the whole reason `stepNum (-1)` vanishes** — see the module docstring — and it is
why `ωNum₀` is `1` rather than `0`. -/
lemma preΩ_zero : W.preΩ 0 = 2 := by
  rw [preΩ, show (0 : ℤ) + 2 = 2 by norm_num, show (0 : ℤ) - 1 = -1 by norm_num,
    show (0 : ℤ) - 2 = -2 by norm_num, show (0 : ℤ) + 1 = 1 by norm_num,
    show (-1 : ℤ) = -(1 : ℤ) by norm_num, show (-2 : ℤ) = -(2 : ℤ) by norm_num,
    preΨ_neg, preΨ_neg, preΨ_one, preΨ_two]
  ring

/-- **`ωBracket₀ = 2`.**  `0` is even so the parity factor is `1`, `ψ₀ = 0` kills the second term,
and what is left is `C (preΩ₀) = C 2`. -/
lemma ωBracket_zero : W.ωBracket 0 = 2 := by
  rw [ωBracket, preΩ_zero, if_pos (by decide : Even (0 : ℤ)), ψ_zero, zero_mul, sub_zero, one_mul]
  exact map_ofNat C 2

/-- **`ωNum` is `ψ`-twisted-even in the index, doubled**:

```
2·ωNum₋ₙ = 2·(ωNumₙ + ψₙ·(a₁Φₙ + a₃ΨSqₙ))     over every commutative ring.
```

⚠️ **The doubled form is the honest one over an arbitrary ring**: `ωNum` is pinned only through
`2·ωNumₙ = ωBracketₙ` (`EllipticCurves.Torsion.OmegaIntegral`'s `two_mul_ωNum`), and the `2` is not
cancellable there.  `ωNum_neg_of_charZero` cancels it over a field of characteristic `0`.

The bracket's two factors have opposite parities in the index — `preΩ₋ₙ = preΩₙ` and
`Even (-n) ↔ Even n`, against `ψ₋ₙ = −ψₙ` with `Φ₋ₙ = Φₙ` and `ΨSq₋ₙ = ΨSqₙ` — so the difference of
the two brackets is twice the `ψ` term, which is the statement. -/
lemma two_mul_ωNum_neg (n : ℤ) :
    2 * W.ωNum (-n) = 2 * (W.ωNum n + W.ψ n * C (C W.a₁ * W.Φ n + C W.a₃ * W.ΨSq n)) := by
  rw [two_mul_ωNum, mul_add, two_mul_ωNum, ωBracket, ωBracket, preΩ_neg, ψ_neg, Φ_neg, ΨSq_neg]
  rcases Int.even_or_odd n with he | ho
  · rw [if_pos he, if_pos he.neg]
    ring
  · have hno : ¬ Even n := Int.not_even_iff_odd.mpr ho
    rw [if_neg hno, if_neg (by simpa using hno)]
    ring

namespace Affine

variable {F : Type*} [Field F] [CharZero F] {W : Affine F} {x y : F}

private lemma two_ne_zero_bipoly : (2 : F[X][Y]) ≠ 0 := two_ne_zero

/-! ### The three indices the ladder cannot reach -/

/-- **`ωNum₀ = 1`** over a field of characteristic `0`, from `ωBracket₀ = 2`. -/
lemma ωNum_zero_of_charZero : W.ωNum 0 = 1 := by
  refine mul_left_cancel₀ two_ne_zero_bipoly ?_
  rw [two_mul_ωNum, ωBracket_zero, mul_one]

/-- **`ωNum₋ₙ = ωNumₙ + ψₙ·(a₁Φₙ + a₃ΨSqₙ)`** over a field of characteristic `0`: `two_mul_ωNum_neg`
with the `2` cancelled.  ⚠️ The same statement holds over every commutative ring, by the descent
`polynomial_dvd_stepNum` runs; it is not needed in that generality here. -/
lemma ωNum_neg_of_charZero (n : ℤ) :
    W.ωNum (-n) = W.ωNum n + W.ψ n * C (C W.a₁ * W.Φ n + C W.a₃ * W.ΨSq n) :=
  mul_left_cancel₀ two_ne_zero_bipoly (W.two_mul_ωNum_neg n)

/-- **`stepNum 0 = 0`.**  `ψ₀ = 0` kills the three terms carrying `ψₙ³`, and what survives is
`ωNum₀·(−Φ₀·ψ₁²) − ωNum₀·ψ₁³·ψ₋₁ = −ωNum₀ + ωNum₀`. -/
lemma stepNum_zero_of_charZero : W.stepNum 0 = 0 := by
  rw [stepNum, show (0 : ℤ) + 1 = 1 by norm_num, show (0 : ℤ) - 1 = -1 by norm_num,
    show (-1 : ℤ) = -(1 : ℤ) by norm_num, ψ_neg, ψ_zero, ψ_one, Φ_zero, ωNum_zero_of_charZero]
  C_simp
  ring

/-- **`stepNum (-1) = 0`**, and ⚠️ **this is the one exceptional index where the vanishing is not
forced by `ψ₀ = 0` alone.**  The surviving terms are `(ωNum₋₁ + Y)·Φ₀` and `−ωNum₀·ψ₋₁³·ψ₋₂`, i.e.

```
stepNum (-1) = ψ₂·Φ₀ − ωNum₀·ψ₂ = ψ₂·(Φ₀ − ωNum₀),
```

using `ωNum₋₁ = Y + a₁X + a₃` (`ωNum_neg_of_charZero` at `n = 1`), and it vanishes **because
`Φ₀ = 1` and `ωNum₀ = 1` agree**.  ⚠️ **With `ωNum₀ = 0` this would have been `ψ₂`, which
`W.polynomial` does not divide** — `ψ₂` is nonzero of degree `1` in `Y` against a monic divisor of
degree `2` — and `NsmulLadderOmegaStepNum`'s `∀ k : ℤ` hypothesis would have been *unsatisfiable*.
It is not, and `preΩ_zero` is why. -/
lemma stepNum_neg_one_of_charZero : W.stepNum (-1) = 0 := by
  rw [stepNum, show (-1 : ℤ) + 1 = 0 by norm_num, show (-1 : ℤ) - 1 = -2 by norm_num,
    show (-1 : ℤ) = -(1 : ℤ) by norm_num, show (-2 : ℤ) = -(2 : ℤ) by norm_num,
    ψ_neg, ψ_neg, ψ_zero, ψ_one, Φ_zero, ωNum_zero_of_charZero,
    ωNum_neg_of_charZero, ωNum_one, ψ_one, Φ_one, ΨSq_one, ψ_two, ψ₂, Affine.polynomialY,
    show W.toAffine.a₁ = W.a₁ from rfl, show W.toAffine.a₃ = W.a₃ from rfl]
  C_simp
  ring

/-! ### The ladder at a negative index -/

omit [CharZero F] in
/-- **`ψ₂(x, y) ≠ 0` upgrades an equation point to a nonsingular one**, with no hypothesis on `2`
and no `IsElliptic`: `polynomialY.evalEval x y = 2y + a₁x + a₃ = ψ₂(x, y)`, which is the second
disjunct of `Nonsingular`.

⚠️ In characteristic `2` this reads `a₁x + a₃ ≠ 0`, which is exactly where the `ω`-flavoured ladder
spends smoothness. -/
lemma nonsingular_of_ψ_two_ne_zero (h : W.Equation x y) (ht : (W.ψ 2).evalEval x y ≠ 0) :
    W.Nonsingular x y := by
  refine ⟨h, Or.inr ?_⟩
  rw [evalEval_polynomialY]
  rwa [ψ_two_evalEval] at ht

omit [CharZero F] in
/-- **`divX` is even in the index**, from `Φ₋ₙ = Φₙ` and `ΨSq₋ₙ = ΨSqₙ`. -/
lemma divX_neg (n : ℤ) : W.divX x (-n) = W.divX x n := by
  rw [divX, divX, Φ_neg, ΨSq_neg]

/-- **`divYω` at `-n` is the `y`-coordinate of `-(n • P)`**:
`divYω x y (-n) = negY (divX x n) (divYω x y n)`.

The numerator is `ωNum_neg_of_charZero` and the denominator is `ψ₋ₙ³ = −ψₙ³`; the `a₃ΨSqₙ` of the
numerator becomes the `a₃` of `negY` through `ΨSqₙ = ψₙ²` at a point of the curve
(`ψ_sq_evalEval`), which is the only place the equation is used. -/
lemma divYω_neg (h : W.Equation x y) {n : ℤ} (hψ : (W.ψ n).evalEval x y ≠ 0) :
    W.divYω x y (-n) = W.negY (W.divX x n) (W.divYω x y n) := by
  have hsq : (W.ψ n).evalEval x y ^ 2 = (W.ΨSq n).eval x := ψ_sq_evalEval h n
  have hnum : (W.ωNum (-n)).evalEval x y = (W.ωNum n).evalEval x y
      + (W.ψ n).evalEval x y * (W.a₁ * (W.Φ n).eval x + W.a₃ * (W.ΨSq n).eval x) := by
    rw [ωNum_neg_of_charZero]
    simp only [evalEval_add, evalEval_mul, evalEval_C, eval_add, eval_mul, eval_C]
  have hψ' : (W.ψ (-n)).evalEval x y = -(W.ψ n).evalEval x y := by
    rw [ψ_neg, evalEval_neg]
  rw [divYω, divYω, negY, divX, hnum, hψ', ← hsq]
  field_simp
  ring

variable [DecidableEq F]

/-- **The `ω`-flavoured ladder rung at `-n` from the rung at `n`**, over a field of characteristic
`0`: `(-n) • P = -(n • P)`, whose coordinates are `divX x (-n)` and `divYω x y (-n)` by `divX_neg`
and `divYω_neg`.

⚠️ **This is what makes the divisibility an `∀ n : ℤ` statement rather than an `∀ n : ℕ` one**:
`EllipticCurves.Torsion.NsmulLadder`'s `nsmulEqDiv_of_forall_ψ_ne_zero` is indexed by `ℕ`, and the
generic-point argument needs the rungs at `n - 1` and `n` at every nonzero integer `n`. -/
theorem nsmulEqDivω_neg (hns : W.Nonsingular x y) {n : ℤ}
    (hψ : (W.ψ n).evalEval x y ≠ 0) (h : NsmulEqDivω hns n) : NsmulEqDivω hns (-n) := by
  obtain ⟨h', heq⟩ := h
  have hX : W.divX x (-n) = W.divX x n := divX_neg n
  have hY : W.divYω x y (-n) = W.negY (W.divX x n) (W.divYω x y n) := divYω_neg hns.left hψ
  have hns' : W.Nonsingular (W.divX x (-n)) (W.divYω x y (-n)) := by
    rw [hX, hY]
    exact (nonsingular_neg ..).mpr h'
  refine ⟨hns', ?_⟩
  rw [neg_zsmul, heq, Point.neg_some, Point.some.injEq]
  exact ⟨hX.symm, hY.symm⟩

end Affine

end WeierstrassCurve

namespace WeierstrassCurve

/-! ### The generic point, built from Mathlib alone -/

namespace Affine.CoordinateRing

variable {F : Type*} [Field F] {W : Affine F}

local notation "WF" => W.map (algebraMap F W.FunctionField)

/-- The generic `x`-coordinate: the class of `X` in `F[W]`, pushed into `F(W)`.  ⚠️ `private`, and
deliberately: `EllipticCurves.FunctionField.TranslationPullback`'s `genX` is the same element, and
that file is above this one in the import order. -/
private noncomputable def gX (W : Affine F) : W.FunctionField :=
  algebraMap W.CoordinateRing W.FunctionField (mk W (C X))

/-- The generic `y`-coordinate: the root of `W.polynomial`, pushed into `F(W)`. -/
private noncomputable def gY (W : Affine F) : W.FunctionField :=
  algebraMap W.CoordinateRing W.FunctionField (AdjoinRoot.root W.polynomial)

/-- **Evaluating at the generic point is taking the class in `F[W]`.**  For every `p ∈ F[X][Y]`, the
base-changed `p` evaluated at `(gX, gY)` is the image of `mk W p` in `F(W)`.

⚠️ **This is the whole bridge**, and the next lemma is the only thing it is used for: both
directions of *"vanishes at the generic point"* and *"is divisible by `W.polynomial`"* are this one
equation plus injectivity. -/
private lemma evalEval_gen (p : F[X][Y]) :
    (p.map (mapRingHom (algebraMap F W.FunctionField))).evalEval (gX W) (gY W)
      = algebraMap W.CoordinateRing W.FunctionField (mk W p) := by
  set φ := algebraMap F W.FunctionField with hφ
  set ρ := algebraMap W.CoordinateRing W.FunctionField with hρ
  have hcomp : (ρ.comp (AdjoinRoot.of W.polynomial)) = eval₂RingHom φ (gX W) := by
    apply Polynomial.ringHom_ext
    · intro a
      rw [RingHom.comp_apply, coe_eval₂RingHom, eval₂_C, hφ, hρ,
        ← AdjoinRoot.algebraMap_eq, ← IsScalarTower.algebraMap_apply,
        Polynomial.C_eq_algebraMap, ← IsScalarTower.algebraMap_apply]
    · rw [RingHom.comp_apply, coe_eval₂RingHom, eval₂_X, gX, hρ]
      rfl
  have hmk : mk W p = p.eval₂ (AdjoinRoot.of W.polynomial) (AdjoinRoot.root W.polynomial) := by
    rw [← AdjoinRoot.aeval_eq, aeval_def, AdjoinRoot.algebraMap_eq]
  rw [hmk, hom_eval₂, hcomp, ← eval₂_eval₂RingHom_apply]
  rfl

/-- **A vanishing at the generic point is a divisibility by `W.polynomial`.**  `F[W]` is a domain
(Mathlib, for every domain base) so it embeds in `F(W)`, and `AdjoinRoot.mk_eq_zero` is the
divisibility.  ⚠️ No characteristic hypothesis and no `IsElliptic`. -/
private theorem polynomial_dvd_of_evalEval_gen_eq_zero {p : F[X][Y]}
    (h : (p.map (mapRingHom (algebraMap F W.FunctionField))).evalEval (gX W) (gY W) = 0) :
    W.polynomial ∣ p := by
  rw [← AdjoinRoot.mk_eq_zero]
  refine (injective_iff_map_eq_zero _).mp
    (IsFractionRing.injective W.CoordinateRing W.FunctionField) _ ?_
  rw [← evalEval_gen, h]

/-- **The generic point lies on the curve**: `evalEval_gen` at `p = W.polynomial`, where
`mk W W.polynomial = 0`. -/
private lemma equation_gen : (WF).Equation (gX W) (gY W) := by
  have h : ((W.polynomial).map (mapRingHom (algebraMap F W.FunctionField))).evalEval
      (gX W) (gY W) = 0 := by
    rw [evalEval_gen, AdjoinRoot.mk_self, map_zero]
  rwa [Equation, map_polynomial]

/-- **No nonzero univariate polynomial vanishes at `gX`** — the genericity of the `x`-coordinate,
here as the statement that `mk W (C p) ≠ 0`, which is `AdjoinRoot.mk_ne_zero_of_natDegree_lt`
against `natDegree (C p) = 0 < 2 = natDegree W.polynomial`. -/
private lemma eval_map_gen_ne_zero {p : F[X]} (hp : p ≠ 0) :
    (p.map (algebraMap F W.FunctionField)).eval (gX W) ≠ 0 := by
  have hC : ((C p).map (mapRingHom (algebraMap F W.FunctionField))).evalEval (gX W) (gY W)
      = (p.map (algebraMap F W.FunctionField)).eval (gX W) := by
    rw [Polynomial.map_C, evalEval_C, coe_mapRingHom]
  rw [← hC, evalEval_gen]
  refine fun hz => AdjoinRoot.mk_ne_zero_of_natDegree_lt monic_polynomial
    (C_ne_zero.mpr hp) ?_ ((injective_iff_map_eq_zero _).mp
      (IsFractionRing.injective W.CoordinateRing W.FunctionField) _ hz)
  rw [natDegree_polynomial, natDegree_C]
  norm_num

variable [CharZero F]

instance : CharZero W.FunctionField :=
  charZero_of_injective_algebraMap (algebraMap F W.FunctionField).injective

/-- **`ψₖ` does not vanish at the generic point at any `k ≠ 0`**, over a field of characteristic
`0`.  Through the square: `ψₖ(gX, gY)² = ΨSqₖ(gX)` (`ψ_sq_evalEval` at `equation_gen`) and
`ΨSqₖ ≠ 0` whenever `(k : F) ≠ 0` (Mathlib's `ΨSq_ne_zero`), which characteristic `0` supplies for
every `k ≠ 0`. -/
private lemma ψ_gen_ne_zero {n : ℤ} (hn : n ≠ 0) :
    ((WF).ψ n).evalEval (gX W) (gY W) ≠ 0 := by
  intro h
  refine eval_map_gen_ne_zero (W := W) (W.ΨSq_ne_zero (n := n) (by exact_mod_cast hn)) ?_
  have hsq := ψ_sq_evalEval (W := WF) equation_gen n
  rw [h, zero_pow (by norm_num)] at hsq
  rw [WeierstrassCurve.map_ΨSq] at hsq
  exact hsq.symm

/-- The generic point is nonsingular, from `ψ₂(gX, gY) ≠ 0` and `nonsingular_of_ψ_two_ne_zero`.
⚠️ **`[W.IsElliptic]` is not assumed** — it is not needed, here or anywhere below. -/
private lemma nonsingular_gen : (WF).Nonsingular (gX W) (gY W) :=
  nonsingular_of_ψ_two_ne_zero equation_gen (ψ_gen_ne_zero (by norm_num))

open Classical in
/-- **The rung at a positive index at the generic point**, from the landed `h2`-bound ladder:
`F(W)` has characteristic `0`, so `nsmulEqDiv_of_forall_ψ_ne_zero` applies and
`nsmulEqDiv_iff_nsmulEqDivω` converts the halved datum to the `ω`-flavoured one. -/
private theorem nsmulEqDivω_gen_natCast {m : ℕ} (hm : 1 ≤ m) :
    NsmulEqDivω (nonsingular_gen (W := W)) (m : ℤ) := by
  have hψ : ∀ j : ℤ, 1 ≤ j → j ≤ (m : ℤ) → ((WF).ψ j).evalEval (gX W) (gY W) ≠ 0 :=
    fun j hj _ => ψ_gen_ne_zero (by omega)
  have hm' : (1 : ℤ) ≤ (m : ℤ) := by exact_mod_cast hm
  exact (nsmulEqDiv_iff_nsmulEqDivω (W := WF) (x := gX W) (y := gY W) two_ne_zero
      (nonsingular_gen (W := W)) (ψ_gen_ne_zero (by norm_num))
      (hψ (m : ℤ) hm' le_rfl)).mp
    (nsmulEqDiv_of_forall_ψ_ne_zero (W := WF) (x := gX W) (y := gY W) two_ne_zero
      (nonsingular_gen (W := W)) hm hψ)

open Classical in
/-- **The rung at every nonzero index at the generic point**, the negative ones by
`nsmulEqDivω_neg`. -/
private theorem nsmulEqDivω_gen {k : ℤ} (hk : k ≠ 0) :
    NsmulEqDivω (nonsingular_gen (W := W)) k := by
  rcases lt_or_gt_of_ne hk with hneg | hpos
  · obtain ⟨m, rfl⟩ : ∃ m : ℕ, k = -(m : ℤ) := ⟨(-k).toNat, by omega⟩
    exact nsmulEqDivω_neg (W := WF) (x := gX W) (y := gY W) (nonsingular_gen (W := W))
      (ψ_gen_ne_zero (by omega)) (nsmulEqDivω_gen_natCast (by omega))
  · obtain ⟨m, rfl⟩ : ∃ m : ℕ, k = (m : ℤ) := ⟨k.toNat, by omega⟩
    exact nsmulEqDivω_gen_natCast (by omega)

open Classical in
/-- **`stepNumₙ` vanishes at the generic point at every index with `n - 1`, `n` and `n + 1` all
nonzero.**  The two rungs give the step's `x`-half (`addX_divYω_eq`), and
`evalEval_stepNum_eq_zero_of_two_ne_zero` is then the vanishing — the landed pricing of the gap,
applied where `(2 : F(W)) ≠ 0` is free. -/
private theorem evalEval_stepNum_gen_eq_zero {n : ℤ} (h0 : n ≠ 0) (h1 : n ≠ 1) (hm1 : n ≠ -1) :
    ((WF).stepNum n).evalEval (gX W) (gY W) = 0 := by
  obtain ⟨hmns, IHm⟩ := nsmulEqDivω_gen (W := W) (k := n - 1) (by omega)
  obtain ⟨h0ns, IH0⟩ := nsmulEqDivω_gen (W := W) (k := n) h0
  exact evalEval_stepNum_eq_zero_of_two_ne_zero (W := WF) (x := gX W) (y := gY W)
    two_ne_zero equation_gen
    (ψ_gen_ne_zero (by omega)) (ψ_gen_ne_zero h0) (ψ_gen_ne_zero (by omega))
    (ψ_gen_ne_zero (by norm_num))
    (addX_divYω_eq (W := WF) (x := gX W) (y := gY W) (nonsingular_gen (W := W))
      (ψ_gen_ne_zero (by omega)) (ψ_gen_ne_zero h0) (ψ_gen_ne_zero (by omega))
      (ψ_gen_ne_zero (by norm_num)) hmns h0ns IHm IH0)

/-- **`W.polynomial ∣ W.stepNum n` over a field of characteristic `0`, at every index.**  The three
indices the ladder cannot reach are the computations above; every other index is
`evalEval_stepNum_gen_eq_zero` read through `polynomial_dvd_of_evalEval_gen_eq_zero`.

⚠️ **No `IsElliptic` and no genericity of the curve**: the generic point is generic, the curve is
arbitrary. -/
theorem polynomial_dvd_stepNum_of_charZero (n : ℤ) : W.polynomial ∣ W.stepNum n := by
  rcases eq_or_ne n 0 with rfl | h0
  · rw [stepNum_zero_of_charZero]; exact dvd_zero _
  rcases eq_or_ne n 1 with rfl | h1
  · rw [stepNum_one]; exact dvd_zero _
  rcases eq_or_ne n (-1) with rfl | hm1
  · rw [stepNum_neg_one_of_charZero]; exact dvd_zero _
  refine polynomial_dvd_of_evalEval_gen_eq_zero ?_
  rw [← map_stepNum]
  exact evalEval_stepNum_gen_eq_zero h0 h1 hm1

end Affine.CoordinateRing

/-! ### The descent to every commutative ring -/

variable {R : Type*} [CommRing R]

/-- ⚠️⚠️ **`W.polynomial ∣ W.stepNumₙ` over EVERY commutative ring at EVERY integer index.**  No
field, no characteristic hypothesis, no `IsElliptic`, no genericity, no index restriction.

**This is `#2347`'s deliverable 1 and the hypothesis of every `_of_dvd` theorem of
`EllipticCurves.Torsion.NsmulLadderOmegaStepNum`**, so the ladder step, the two-step induction,
`n • P = (Φₙ/ΨSqₙ, ωNumₙ/ψₙ³)` and the `n • P = 0 ⇒ some ψₖ(P) = 0` half of the dictionary all hold
**with `(2 : F) ≠ 0` deleted** — see the three corollaries below.

⚠️ **The descent produces no cofactor and names none.**  `W.polynomial` is monic in `Y`, so
`Polynomial.map_dvd_map` reverses the divisibility along the injection of
`MvPolynomial (Fin 5) ℤ` into its fraction field — a field of characteristic `0`, where
`polynomial_dvd_stepNum_of_charZero` is available — and `map_stepNum` with `Affine.map_polynomial`
then carry it down along `WeierstrassCurve.specialize`.  ⚠️ **This is the same two-stage shape as
`EllipticCurves.Torsion.OmegaOnCurveCharFree`'s `polynomial_dvd_divPairNum` with the first stage
replaced**: that one cancels a `4` in an explicit identity, this one transports a bare
divisibility. -/
theorem polynomial_dvd_stepNum (W : WeierstrassCurve R) (n : ℤ) :
    W.toAffine.polynomial ∣ W.stepNum n := by
  have hinj : Function.Injective
      (algebraMap (MvPolynomial (Fin 5) ℤ) (FractionRing (MvPolynomial (Fin 5) ℤ))) :=
    IsFractionRing.injective _ _
  have hF := Affine.CoordinateRing.polynomial_dvd_stepNum_of_charZero
    (W := (univ.map (algebraMap (MvPolynomial (Fin 5) ℤ)
      (FractionRing (MvPolynomial (Fin 5) ℤ)))).toAffine) n
  rw [show ((univ.map (algebraMap (MvPolynomial (Fin 5) ℤ)
      (FractionRing (MvPolynomial (Fin 5) ℤ)))).toAffine) = (univ.toAffine.map
      (algebraMap (MvPolynomial (Fin 5) ℤ) (FractionRing (MvPolynomial (Fin 5) ℤ)))) from rfl,
    Affine.map_polynomial] at hF
  rw [map_stepNum] at hF
  obtain ⟨G, hG⟩ :=
    (Polynomial.map_dvd_map _ (Polynomial.map_injective _ hinj) Affine.monic_polynomial).mp hF
  have he : univ.toAffine.map W.specialize = W.toAffine := univ_map_specialize W
  have H := congrArg (Polynomial.map (mapRingHom W.specialize)) hG
  rw [← map_stepNum, Polynomial.map_mul, ← Affine.map_polynomial, he, univ_map_specialize] at H
  exact ⟨_, H⟩

/-! ### The `ω`-flavoured ladder with `(2 : F) ≠ 0` deleted -/

namespace Affine

variable {F : Type*} [Field F] [DecidableEq F] {W : Affine F} {x y : F}

/-- ⚠️⚠️ **THE LADDER ALONG A NONVANISHING `ψ`, UNCONDITIONALLY.**
`EllipticCurves.Torsion.NsmulLadderOmegaStepNum`'s `nsmulEqDivω_of_forall_ψ_ne_zero_of_dvd` with its
divisibility hypothesis discharged by `polynomial_dvd_stepNum`.

⚠️ **The prime is not decoration**: PR #941 declares a theorem of this exact statement under the
unprimed name, by a different route — see `## ⚠️ Overlap with PR #941` in the module docstring.

⚠️ **The hypotheses are the landed ones minus `(2 : F) ≠ 0` and nothing is put in its place.**  The
`ψₖ ≠ 0` for `1 ≤ k ≤ n` are unchanged and are not weakened; in characteristic `2` the `k = 2` one
reads `a₁x + a₃ ≠ 0`. -/
theorem nsmulEqDivω_of_forall_ψ_ne_zero' (hns : W.Nonsingular x y) {n : ℕ} (hn : 1 ≤ n)
    (hψ : ∀ k : ℤ, 1 ≤ k → k ≤ (n : ℤ) → (W.ψ k).evalEval x y ≠ 0) :
    NsmulEqDivω hns (n : ℤ) :=
  nsmulEqDivω_of_forall_ψ_ne_zero_of_dvd hns (fun k => polynomial_dvd_stepNum W k) hn hψ

/-- ⚠️⚠️ **`n • P = (Φₙ(x)/ΨSqₙ(x), ωNumₙ(x, y)/ψₙ(x, y)³)` WITH NO HYPOTHESIS ON `2`**, at every
index `n ≥ 1` whose ladder has no zero.

**This is `#2340`'s route (b) as an unconditional statement.**
`EllipticCurves.Torsion.NsmulLadder`'s `nsmul_eq_some_Φ_div_ΨSq` gives only the `x`-coordinate and
binds `(2 : F) ≠ 0`; this names both coordinates and binds none.  ⚠️ The `y`-coordinate is
`EllipticCurves.Torsion.OmegaIntegral`'s unhalved `ωNumₙ` and **not** `divY` — in characteristic `2`
the halved form is not merely unproved but false. -/
theorem nsmul_eq_some_divX_divYω (hns : W.Nonsingular x y) {n : ℕ} (hn : 1 ≤ n)
    (hψ : ∀ k : ℤ, 1 ≤ k → k ≤ (n : ℤ) → (W.ψ k).evalEval x y ≠ 0) :
    ∃ h' : W.Nonsingular ((W.Φ (n : ℤ)).eval x / (W.ΨSq (n : ℤ)).eval x)
        ((W.ωNum (n : ℤ)).evalEval x y / (W.ψ (n : ℤ)).evalEval x y ^ 3),
      (n • Point.some x y hns : W.Point) = .some _ _ h' :=
  nsmul_eq_some_divX_divYω_of_dvd hns (fun k => polynomial_dvd_stepNum W k) hn hψ

/-- ⚠️⚠️ **`n • P = 0` forces one of `ψ₁(P), …, ψₙ(P)` to vanish, with no hypothesis on `2`.**

The `h2`-free counterpart of `EllipticCurves.Torsion.NsmulLadder`'s
`exists_ψ_evalEval_eq_zero_of_nsmul_eq_zero`, which it subsumes; the primed name is there because
that one is landed and this round changes no landed signature.  ⚠️ **The converse
(`ψₙ(P) = 0 → n • P = 0`) is not proved here**, and neither is the sharpening that the vanishing
index may be taken to be `n` itself — that is `EllipticCurves.Torsion.NsmulOrder`'s and is `#2340`
item 3. -/
theorem exists_ψ_evalEval_eq_zero_of_nsmul_eq_zero' (hns : W.Nonsingular x y) {n : ℕ} (hn : 1 ≤ n)
    (hzero : (n • Point.some x y hns : W.Point) = 0) :
    ∃ k : ℤ, 1 ≤ k ∧ k ≤ (n : ℤ) ∧ (W.ψ k).evalEval x y = 0 :=
  exists_ψ_evalEval_eq_zero_of_nsmul_eq_zero_of_dvd hns (fun k => polynomial_dvd_stepNum W k) hn
    hzero

/-! ### ⚠️ The characteristic-`2` payoff, exhibited and not asserted -/

section CharTwo

open EllipticCurves.Fixture

/-- ⚠️⚠️ **THE RUNG AT `n = 3` OVER `ZMod 2`**, where `2 = 0` — a statement no `h2`-bound theorem of
this tree can produce, and the landed module's `example` with its hypothesis discharged.

`curveCharTwoOne = ⟨1, 0, 0, 0, 1⟩` over `ZMod 2` at `(1, 0)`, where `ψ₂(1, 0) = 1 ≠ 0`
(`EllipticCurves.Torsion.DoublingOmega`'s `evalEval_ψ_two_curveCharTwoOne`) and `ψ₃(1, 0) ≠ 0`
(`EllipticCurves.Torsion.OmegaOnCurveCharFree`'s `ψ_three_evalEval_ne_zero_curveCharTwoOne`).

⚠️ **`NsmulEqDiv` is FALSE at this point** (`EllipticCurves.Torsion.NsmulLadderOmega`'s
`not_nsmulEqDiv_two_curveCharTwoOne`), so it is the `ω`-flavoured predicate doing the work and not
the halved one, and this is not a restatement of anything landed.

⚠️ **The prime is not decoration**: PR #941 declares a theorem of this exact statement under the
unprimed name — see `## ⚠️ Overlap with PR #941` in the module docstring. -/
theorem nsmulEqDivω_three_curveCharTwoOne' :
    NsmulEqDivω nonsingular_curveCharTwoOne 3 := by
  refine nsmulEqDivω_of_forall_ψ_ne_zero' nonsingular_curveCharTwoOne (n := 3) (by norm_num) ?_
  intro k hk hk2
  interval_cases k
  · rw [ψ_one_evalEval]; exact one_ne_zero
  · rw [evalEval_ψ_two_curveCharTwoOne]; exact one_ne_zero
  · exact ψ_three_evalEval_ne_zero_curveCharTwoOne

/-- ⚠️ **A concrete consequence a reader can check by hand**: the point `(1, 0)` of
`curveCharTwoOne` over `ZMod 2` is not `3`-torsion.

It falls out of the rung above — `3 • P` is an *affine* point, and `Point.some_ne_zero` — and it is
here because it is checkable independently of everything in this file: `y² + xy = x³ + 1` over
`ZMod 2` has the four points `O`, `(0, 1)`, `(1, 0)`, `(1, 1)`, and `-(1, 0) = (1, 1) ≠ (1, 0)`, so
`P` has order `4` and `3 • P = -P ≠ 0`. -/
theorem nsmul_three_curveCharTwoOne_ne_zero :
    ((3 : ℤ) • Point.some 1 0 nonsingular_curveCharTwoOne : curveCharTwoOne.Point) ≠ 0 := by
  obtain ⟨h', heq⟩ := nsmulEqDivω_three_curveCharTwoOne'
  rw [heq]
  exact Point.some_ne_zero h'

end CharTwo

end Affine

end WeierstrassCurve
