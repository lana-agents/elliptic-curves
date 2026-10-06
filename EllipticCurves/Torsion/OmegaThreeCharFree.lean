/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import EllipticCurves.Torsion.OmegaCharZero
import EllipticCurves.Torsion.OmegaDivisionPolynomial
import Mathlib.Algebra.Field.ZMod

/-!
# The tripling map lies on the curve, with no characteristic hypothesis at all

`EllipticCurves.Torsion.OmegaThree` proves that the division-polynomial tripling point
`[3](x, y) = (Φ₃(x)/ΨSq₃(x), ω₃(x, y)/ψ₃(x, y)³)` lies on `W`, over a field with `(2 : F) ≠ 0`,
and its module docstring enumerates the **four** sites at which that hypothesis is consumed.  Two
of the four are the `2` in the `y`-coordinate's own denominator, and `ω₃`
(`EllipticCurves.Torsion.OmegaDivisionPolynomial`) already removed it from the *statement*.  The
other two are the `b`-relation `4b₈ = b₂b₆ − b₄²` divided by `4`, and that file says of the second
of them — the closing `mul_left_cancel₀` by `4` that passes from the completed-square form
`(2Y + a₁X + a₃)² = 4X³ + b₂X² + 2b₄X + b₆` to `Equation` — that *"no normalisation of `ωₙ` reaches
it"*.

⚠️ **That is true of the route and not of the statement, and this file proves the statement.**
`tripling_equation_ω₃_general` below is `tripling_equation_ω₃` with **every** characteristic
hypothesis gone: an arbitrary field, no `(2 : F) ≠ 0`, no `(3 : F) ≠ 0`, and only
`ψ₃(x, y) ≠ 0` — the genericity that says `(x, y)` is not `3`-torsion.

## The mechanism, and why the `4` is not an obstruction

Clearing the `ψ₃`-denominators of `Equation (Φ₃/ΨSq₃) (ω₃/ψ₃³)` gives the single polynomial

```
triplingNum = ω₃² + a₁Φ₃ψ₃ω₃ + a₃ψ₃³ω₃ − Φ₃³ − a₂Φ₃²ΨSq₃ − a₄Φ₃ΨSq₃² − a₆ΨSq₃³  ∈ R[X][Y],
```

and the on-curve statement is that `W.polynomial` divides it.  ⚠️ **The quotient is exact and it is
a square**: `triplingNum = W.polynomial · preΩ₃²`, which is `triplingNum_eq`, and which holds over
**every** commutative ring.

The proof is in two steps, and the split is the whole point.

1. `four_mul_triplingNum`: `4·triplingNum = 4·(W.polynomial·preΩ₃²)` over an arbitrary
   `CommRing`, by **one** `linear_combination` of three inputs — `two_mul_ω₃`
   (`2·ω₃ = ψ₂·preΩ₃ − ψ₃·(a₁Φ₃ + a₃ΨSq₃)`, quadratically), Mathlib's
   `ψ₂_sq` (`ψ₂² = C Ψ₂Sq + 4·W.polynomial`, once) and `hasPreΩSq_three`
   (`preΩ₃²·Ψ₂Sq = 4Φ₃³ + b₂Φ₃²ΨSq₃ + 2b₄Φ₃ΨSq₃² + b₆ΨSq₃³`, once).  ⚠️ `hasPreΩSq_three` is
   itself characteristic-free — `EllipticCurves.Torsion.OmegaCharZero` proved it over every
   commutative ring, including where `2 = 0` — so no step here asks anything of the base.
2. `triplingNum_eq`: cancel the `4`.  ⚠️ **It cannot be cancelled over `R`, and it does not have to
   be**: `triplingNum` and `W.polynomial·preΩ₃²` both commute with base change, so it is enough to
   cancel it **once**, over `MvPolynomial (Fin 5) ℤ`, a characteristic-`0` domain, and carry the
   identity down along `W.specialize`.  That is `triplingNum_univ` followed by `map_triplingNum`,
   the pattern `EllipticCurves.Torsion.OmegaUniversal` fixes and
   `EllipticCurves.Torsion.OmegaIntegral`'s `two_dvd_ωBracket_univ` already uses for the
   divisibility of the bracket by `2`.

⚠️ **So the `4` of the completed-square route is paid in a ring where `4` is a nonzerodivisor, and
nothing is paid in `R` at all.**  The quoted *"no normalisation of `ωₙ` reaches it"* is correct:
what reaches it is not a normalisation of `ωₙ` but a change of base.

## What this does and does not settle

* ✅ The on-curve identity at `n = 3` over every field, in every characteristic, and the
  polynomial divisibility over every commutative ring.
* ⚠️ **`n = 2` is NOT settled and must not be attempted the same way.**
  `EllipticCurves.FunctionField.MulByTwoPullback`'s side condition is `psiTwo_gen_ne h2`, and
  `ψ₂ = 2Y + a₁X + a₃` vanishes identically in characteristic `2` on a curve with `a₁ = a₃ = 0`.
  That is a genuine obstruction and no `ω`-normalisation and no base change reaches it.
* ⚠️ **Nothing here is about `E[3]` or about the group law.**  This is the algebraic on-curve
  identity for the classical tripling coordinates; identifying them with `3 • P` is
  `EllipticCurves.Torsion.TriplingCoords` and is a separate statement.

## Main statements

* `WeierstrassCurve.triplingNum` : the cleared-denominator numerator, in `R[X][Y]`.
* `WeierstrassCurve.four_mul_triplingNum` : `4·triplingNum = 4·(W.polynomial·preΩ₃²)`, every ring.
* `WeierstrassCurve.triplingNum_eq` : `triplingNum = W.polynomial·preΩ₃²`, every ring.
* `WeierstrassCurve.Affine.tripling_equation_ω₃_general` : the on-curve identity with no
  characteristic hypothesis.
* `WeierstrassCurve.Affine.ω₃_div_eq_div_two_mul` : the `2`-free `y`-coordinate agrees with the
  `2`-bearing one wherever the latter is defined.

## References

* [J. Silverman, *The arithmetic of elliptic curves*][silverman2009], Exercise 3.7, III.6.
-/

open Polynomial
open scoped Polynomial.Bivariate

namespace WeierstrassCurve

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R)

/-- **The cleared-denominator tripling numerator at `n = 3`**:

```
triplingNumₙ₌₃ = ω₃² + a₁Φ₃ψ₃ω₃ + a₃ψ₃³ω₃ − Φ₃³ − a₂Φ₃²ΨSq₃ − a₄Φ₃ΨSq₃² − a₆ΨSq₃³ ∈ R[X][Y].
```

This is `Equation (Φ₃/ΨSq₃) (ω₃/ψ₃³)` multiplied through by `ψ₃⁶`, written with no division
anywhere, so that it makes sense over a ring in which `ψ₃` is not invertible and in which `2 = 0`.
⚠️ **`ΨSq₃` and not `ψ₃²`**: the two agree at a point of the curve (Mathlib's `ψ_sq_evalEval`) and
at `n = 3` they agree as polynomials as well (`ψ 3 = C Ψ₃` and `ΨSq 3 = Ψ₃²`), but the univariate
`ΨSq₃` is the form every `Φ`/`ΨSq` lemma is stated in. -/
noncomputable def triplingNum : R[X][Y] :=
  W.ω₃ ^ 2 + C (C W.a₁) * C (W.Φ 3) * W.ψ 3 * W.ω₃ + C (C W.a₃) * W.ψ 3 ^ 3 * W.ω₃
    - C (W.Φ 3) ^ 3 - C (C W.a₂) * C (W.Φ 3) ^ 2 * C (W.ΨSq 3)
    - C (C W.a₄) * C (W.Φ 3) * C (W.ΨSq 3) ^ 2 - C (C W.a₆) * C (W.ΨSq 3) ^ 3

/-- **`triplingNum` commutes with base change** — the hinge of `triplingNum_eq`.  ⚠️ **Without it
the universal cancellation of the `4` is unusable**, and it is what the four `map_ω₃*` lemmas of
`EllipticCurves.Torsion.OmegaDivisionPolynomial` were added for. -/
lemma map_triplingNum {S : Type*} [CommRing S] (f : R →+* S) :
    (W.map f).triplingNum = W.triplingNum.map (mapRingHom f) := by
  simp only [triplingNum, map_ω₃, map_ψ, map_Φ, map_ΨSq, WeierstrassCurve.map_a₁,
    WeierstrassCurve.map_a₂, WeierstrassCurve.map_a₃, WeierstrassCurve.map_a₄,
    WeierstrassCurve.map_a₆, Polynomial.map_add, Polynomial.map_sub, Polynomial.map_mul,
    Polynomial.map_pow, Polynomial.map_C, coe_mapRingHom]

/-- **Four times the on-curve divisibility, over an arbitrary commutative ring.**
`4·triplingNum = 4·(W.polynomial · preΩ₃²)`.

One `linear_combination` of `two_mul_ω₃` (coefficient `2ω₃ + ψ₂·preΩ₃ + ψ₃·(a₁Φ₃ + a₃Ψ₃²)`),
`ψ₂_sq` (coefficient `preΩ₃²`) and `hasPreΩSq_three` (coefficient `1`), after which the residue is
`Φ₃²Ψ₃²(b₂ − a₁² − 4a₂) + Φ₃Ψ₃⁴(2b₄ − 2a₁a₃ − 4a₄) + Ψ₃⁶(b₆ − a₃² − 4a₆)`, which `ring` closes once
`b₂`, `b₄` and `b₆` are unfolded.

⚠️ **`Ψ₂Sq` and `W.polynomial` stay `ring` atoms**: the `Ψ₂Sq` of `ψ₂_sq` cancels against the
`Ψ₂Sq` of `hasPreΩSq_three`, so nothing here has to be expanded into the `aᵢ` except the three
`bᵢ`. -/
theorem four_mul_triplingNum :
    4 * W.triplingNum = 4 * (W.toAffine.polynomial * C (W.preΩ 3) ^ 2) := by
  have hΩ : W.preΩ 3 ^ 2 * W.Ψ₂Sq =
      4 * W.Φ 3 ^ 3 + C W.b₂ * W.Φ 3 ^ 2 * W.ΨSq 3 + 2 * C W.b₄ * W.Φ 3 * W.ΨSq 3 ^ 2 +
        C W.b₆ * W.ΨSq 3 ^ 3 := by
    have h := W.hasPreΩSq_three
    rwa [HasPreΩSq, if_neg (by decide : ¬Even (3 : ℤ))] at h
  rw [b₂, b₄, b₆, ΨSq_three] at hΩ
  have h1 := W.two_mul_ω₃
  have h2 := congrArg (C : R[X] → R[X][Y]) hΩ
  have h3 := W.ψ₂_sq
  rw [ψ_two, ψ_three, ΨSq_three] at h1
  rw [triplingNum, ψ_three, ΨSq_three]
  simp only [map_ofNat, C_add, C_mul, C_pow] at h1 h2 ⊢
  linear_combination (2 * W.ω₃ + W.ψ₂ * C (W.preΩ 3)
      + C W.Ψ₃ * (C (C W.a₁) * C (W.Φ 3) + C (C W.a₃) * C W.Ψ₃ ^ 2)) * h1
    + C (W.preΩ 3) ^ 2 * h3 + h2

/-- **The on-curve divisibility for the universal curve**, where the `4` can be cancelled:
`MvPolynomial (Fin 5) ℤ` is an integral domain of characteristic `0`, so `(4 : _[X][Y]) ≠ 0`.

⚠️ **This is the only step of the file that uses a property of the base ring at all**, and it uses
it about `MvPolynomial (Fin 5) ℤ` rather than about `R`. -/
theorem triplingNum_univ :
    univ.triplingNum = univ.toAffine.polynomial * C (univ.preΩ 3) ^ 2 := by
  have h4 : (4 : (MvPolynomial (Fin 5) ℤ)[X][Y]) ≠ 0 := by norm_num
  exact mul_left_cancel₀ h4 (four_mul_triplingNum univ)

/-- ⚠️⚠️ **THE HEADLINE, polynomial form: `triplingNum = W.polynomial · preΩ₃²` over EVERY
commutative ring.**  No field, no characteristic hypothesis, no `IsElliptic`, no genericity — the
`4` of the completed-square route is cancelled once over the universal curve and the identity is
carried down along `W.specialize`.

⚠️ **The cofactor is a square and that is not an accident**: at odd `n` the parity factor of `ωₙ`
is `ψ₂`, whose square is `C Ψ₂Sq + 4·W.polynomial`, and the `4·W.polynomial` of that splitting is
the only place `W.polynomial` enters the computation.  `preΩ₃²` is exactly its coefficient. -/
theorem triplingNum_eq :
    W.triplingNum = W.toAffine.polynomial * C (W.preΩ 3) ^ 2 := by
  have he : univ.toAffine.map W.specialize = W.toAffine := univ_map_specialize W
  have H := congrArg (Polynomial.map (mapRingHom W.specialize)) triplingNum_univ
  rw [← map_triplingNum, Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_C,
    coe_mapRingHom, ← Affine.map_polynomial, ← map_preΩ, he, univ_map_specialize] at H
  exact H

namespace Affine

variable {F : Type*} [Field F] {W : Affine F} {x y : F}

/-- ⚠️⚠️ **THE HEADLINE: the tripling point lies on the curve, over an arbitrary field, in EVERY
characteristic.**  For a point `(x, y)` on `W` with `ψ₃(x, y) ≠ 0` — i.e. `(x, y)` not
`3`-torsion — the point

```
[3](x, y) = (Φ₃(x)/ΨSq₃(x), ω₃(x, y)/ψ₃(x, y)³)
```

satisfies the Weierstrass equation, where `ω₃ = preΩ₃·Y + preω₃` is the honest `3`-division
`y`-coordinate polynomial (`WeierstrassCurve.evalEval_ω₃` unfolds the value to
`y·preΩ₃(x) + preω₃(x)`).

⚠️ **This is `WeierstrassCurve.Affine.tripling_equation_ω₃` with `(2 : F) ≠ 0` DELETED**, and the
`Nonvacuity` section below instantiates it over `ZMod 2`, where that hypothesis is false.  ⚠️ **No
`(3 : F) ≠ 0` either**, and none was ever needed: `EllipticCurves.Torsion.OmegaThree` already
records that the degree input is `deg Φ₃ = 9` against `deg ΨSq₃ ≤ 8`, both unconditional.

⚠️ **`tripling_equation` and `tripling_equation_ω₃` are NOT superseded** for a caller that already
holds `h2`: they are merged public API with consumers in `FunctionField/`, their statements are
unchanged, and `ω₃_div_eq_div_two_mul` below is the bridge between the two `y`-coordinates. -/
theorem tripling_equation_ω₃_general (h : W.Equation x y) (hψ : (W.ψ 3).evalEval x y ≠ 0) :
    W.Equation ((W.Φ 3).eval x / (W.ΨSq 3).eval x)
      (W.ω₃.evalEval x y / (W.ψ 3).evalEval x y ^ 3) := by
  have hpoly : W.polynomial.evalEval x y = 0 := h
  have h0 : W.triplingNum.evalEval x y = 0 := by
    rw [triplingNum_eq, evalEval_mul, hpoly, zero_mul]
  rw [triplingNum] at h0
  simp only [evalEval_add, evalEval_sub, evalEval_mul, evalEval_pow, evalEval_C, eval_C] at h0
  have hs : (W.ΨSq 3).eval x = (W.ψ 3).evalEval x y ^ 2 := (ψ_sq_evalEval h 3).symm
  have hS : (W.ΨSq 3).eval x ≠ 0 := by rw [hs]; exact pow_ne_zero 2 hψ
  rw [equation_iff]
  rw [hs] at h0 ⊢
  field_simp
  linear_combination h0

/-- **The `2`-free `y`-coordinate is the `2`-bearing one, wherever the latter is defined.**  Over a
field with `(2 : F) ≠ 0` and at a point with `ψ₃(x, y) ≠ 0`,

```
ω₃(x, y)/ψ₃(x, y)³  =  (bracket)/(2·ψ₃(x, y)³).
```

⚠️ **No `W.Equation x y`**: the identity is `two_mul_preω₃` divided by `2·ψ₃³` and uses nothing
about the point beyond the non-vanishing.  This is the bridge that lets a consumer holding `h2`
move between the landed `tripling_equation` and the `2`-free form, and it is the one statement on
this route that still *needs* `h2` — in characteristic `2` the right-hand side is `0/0`. -/
theorem ω₃_div_eq_div_two_mul (h2 : (2 : F) ≠ 0) (hψ : (W.ψ 3).evalEval x y ≠ 0) :
    W.ω₃.evalEval x y / (W.ψ 3).evalEval x y ^ 3 =
      ((2 * y + W.a₁ * x + W.a₃) * ((W.preΨ 5).eval x - W.preΨ₄.eval x ^ 2) -
          W.a₁ * (W.Φ 3).eval x * (W.ψ 3).evalEval x y -
          W.a₃ * (W.ψ 3).evalEval x y ^ 3) / (2 * (W.ψ 3).evalEval x y ^ 3) := by
  have hs : (W.ψ 3).evalEval x y = W.Ψ₃.eval x := by rw [ψ_three]; simp [evalEval]
  have hA : (W.preΩ 3).eval x = (W.preΨ 5).eval x - W.preΨ₄.eval x ^ 2 := by
    rw [preΩ_three, eval_sub, eval_pow]
  have key : 2 * W.preω₃.eval x = (W.a₁ * x + W.a₃) * (W.preΩ 3).eval x -
      W.a₁ * (W.Φ 3).eval x * W.Ψ₃.eval x - W.a₃ * W.Ψ₃.eval x ^ 3 := by
    have h' := congrArg (Polynomial.eval x) W.two_mul_preω₃
    simpa only [eval_mul, eval_sub, eval_add, eval_pow, eval_ofNat, eval_C, eval_X] using h'
  have hc : (W.ψ 3).evalEval x y ^ 3 ≠ 0 := pow_ne_zero 3 hψ
  rw [evalEval_ω₃, div_eq_div_iff hc (mul_ne_zero h2 hc), ← hA, hs]
  linear_combination (W.Ψ₃.eval x ^ 3) * key

/-! ### Non-vacuity in characteristic `2` -/

section Nonvacuity

/-- **`y² + xy = x³ + 1` over `ZMod 2`** — the tuple `⟨1, 0, 0, 0, 1⟩`, with `b₂ = 1`, `b₄ = 0`,
`b₆ = 0`, `b₈ = 1` and `Ψ₃ = X⁴ + X³ + 1`.  `a₁ ≠ 0` is what a characteristic-`2` fixture needs:
at `a₁ = a₃ = 0` the linear form `a₁x + a₃` vanishes and with it `ψ₂`.

⚠️ **The same tuple already appears twice in the tree and this is a third declaration, not a
reuse**: `EllipticCurves.Torsion.DoublingOmega`'s `curveCharTwoOne` (public) and
`EllipticCurves.Torsion.TriplingSurjective`'s `curveChar2` (private).  **Reusing the public one was
measured and declined**: `import EllipticCurves.Torsion.DoublingOmega` takes this file's
`EllipticCurves` import closure from **7** modules to **38**, and
`EllipticCurves.FunctionField.MulByThreeCharFree`'s from **15** to **44** — the same trade
`EllipticCurves.Torsion.OmegaThree` declines at `3 → 22` for `OmegaCrux`.  ⚠️ This one is **not**
`private`, precisely so that `MulByThreeCharFree` reuses it rather than making a fourth copy.
**Consolidating the three into `EllipticCurves.Fixtures` is a separate job and is out of scope
here** — that file carries no `⟨1, 0, 0, 0, 1⟩` and its own docstring keeps a census of the
fixtures that would have to move.

Nothing about its reduction type, its `j`-invariant or its group order is asserted or used. -/
def curveCharTwo : Affine (ZMod 2) := ⟨1, 0, 0, 0, 1⟩

/-- **The base field really is of characteristic `2`** — the refuter of the hypothesis the theorem
below does not have. -/
lemma two_eq_zero_zmod_two : (2 : ZMod 2) = 0 := by decide

/-- `(1, 0)` lies on `curveCharTwo`: over `ZMod 2`, `0 + 1·1·0 + 0·0 = 0` and `1 + 0 + 0 + 1 = 0`.

⚠️ The same point as `TriplingSurjective`'s own characteristic-`2` cell; its `(0, 1)` sibling is
**not** interchangeable, and that round's §5 banks why. -/
lemma equation_curveCharTwo : curveCharTwo.Equation 1 0 := by
  rw [equation_iff]; decide +kernel

/-- `ψ₃ = C Ψ₃` with `Ψ₃ = X⁴ + X³ + 1`, so `ψ₃(1, 0) = 1 ≠ 0`: the point is **not** `3`-torsion,
which is the one hypothesis the theorem below still carries.

⚠️ `Ψ₃ = 3X⁴ + b₂X³ + 3b₄X² + 3b₆X + b₈` degenerates to `X⁴ + X³ + 1` here because `3 = 1` and
`b₄ = b₆ = 0` in `ZMod 2` — **not** because the characteristic kills the leading term. -/
lemma psi_three_ne_zero_curveCharTwo : (curveCharTwo.ψ 3).evalEval 1 0 ≠ 0 := by
  rw [ψ_three, evalEval_C]
  simp only [WeierstrassCurve.Ψ₃, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆,
    WeierstrassCurve.b₈, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
    Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_ofNat, curveCharTwo]
  decide +kernel

/-- **The tripling on-curve identity, instantiated over a field of characteristic `2`.**

⚠️ **This is the whole content of dropping `h2`: the statement below could not be *written* with
`tripling_equation_ω₃`**, whose `(2 : F) ≠ 0` is refuted here by `two_eq_zero_zmod_two`. -/
theorem tripling_equation_ω₃_curveCharTwo :
    curveCharTwo.Equation ((curveCharTwo.Φ 3).eval 1 / (curveCharTwo.ΨSq 3).eval 1)
      (curveCharTwo.ω₃.evalEval 1 0 / (curveCharTwo.ψ 3).evalEval 1 0 ^ 3) :=
  tripling_equation_ω₃_general equation_curveCharTwo psi_three_ne_zero_curveCharTwo

end Nonvacuity

end Affine

end WeierstrassCurve
