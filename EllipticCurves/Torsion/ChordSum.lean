/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import EllipticCurves.Torsion.NsmulOrder
import EllipticCurves.Torsion.OmegaCrux
import EllipticCurves.Torsion.OmegaUniversal
import EllipticCurves.Torsion.ThreeTorsionStructure
import Mathlib.Algebra.CharP.Algebra
import Mathlib.Algebra.CharZero.Infinite
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-!
# The ADDITIVE recurrence for the division-polynomial `x`-coordinate

`EllipticCurves.Torsion.OmegaOnCurve` carries the **multiplicative** recurrence for the pair
`(Φₙ, ΨSqₙ)` — `WeierstrassCurve.HasΨSqDoubling`, `ΨSq₂ₙ` in terms of `Φₙ` and `ΨSqₙ`, discharged
unconditionally in `EllipticCurves.Torsion.OmegaCrux`.  This file proves the additive one:

```
Φ_{n+1}·ΨSq_{n−1} + Φ_{n−1}·ΨSq_{n+1}
  = 2X·Φₙ² + (2X² + b₂X + b₄)·Φₙ·ΨSqₙ + (b₄X + b₆)·ΨSqₙ² ,
```

over an **arbitrary commutative ring**, at **every** `n : ℤ`, with no hypotheses at all
(`WeierstrassCurve.hasChordSum`).

Divided by `ΨSq_{n+1}·ΨSq_{n−1}` — which is `(X·ΨSqₙ − Φₙ)²`, the merged
`WeierstrassCurve.Affine.ψ_add_mul_ψ_sub` squared — it reads

```
x_{n+1} + x_{n−1} = Σ(xₙ, X) ,    Σ(u, X) = (Ψ₂Sq(u) + Ψ₂Sq(X))/(2(u − X)²) − b₂/2 − 2(u + X) ,
```

the classical statement that `x(Q + P) + x(Q − P)` depends only on `x(Q)` and `x(P)`, at
`Q = n • P`.  ⚠️ Read `Φₙ/ΨSqₙ` as *the division-polynomial `x`-coordinate at `n`*: the identity
above is a statement about polynomials and is proved here over every commutative ring, including
those with no points at all.

## Why the statement is in this form and not the other one

`#1506`'s route to `[n]∗ω = nω` names its additive input in the cleared form

```
2·ΨSqₙ²·(Φ_{n+1}ΨSq_{n−1} + Φ_{n−1}ΨSq_{n+1})
    = ΨSq₂ₙ + ΨSqₙ⁴·Ψ₂Sq − b₂·ΨSqₙ²·Gₙ² − 4·ΨSqₙ·(Φₙ + X·ΨSqₙ)·Gₙ² ,   Gₙ := X·ΨSqₙ − Φₙ .
```

Substituting the merged `HasΨSqDoubling` for `ΨSq₂ₙ` and `Gₙ = X·ΨSqₙ − Φₙ`, every `Gₙ²` term
cancels and the right-hand side collapses to `2·ΨSqₙ²` times the bracket of the display at the top.
So the two differ by exactly that factor, and the one proved here is the stronger:

* it carries **no factor of `2`**, so it says something in characteristic `2`;
* it carries **no factor of `ΨSqₙ²`**, so it says something at `n = 0`, where `ΨSq₀ = 0` makes the
  other display `0 = 0`;
* it does not mention `ΨSq₂ₙ`, so it is independent of `#404`'s crux.

`WeierstrassCurve.hasChordSum_cleared` below is the other display, derived from this one, for a
consumer that wants it in `#1506`'s vocabulary.

## The proof, and what each hypothesis is spent on

Three reductions, none of them new; the content is in the second bullet.

* **Descent.** `HasChordSum` transports along any ring map and descends along an injective one, so
  it is enough to prove it for the single curve `WeierstrassCurve.univQ` over
  `MvPolynomial (Fin 5) ℚ` (`EllipticCurves.Torsion.OmegaUniversal`).  That base is a domain in
  which `univQ.Δ ≠ 0` (`WeierstrassCurve.univQ_Δ_ne_zero`), so base changing along the injection
  into `K := AlgebraicClosure (FractionRing (MvPolynomial (Fin 5) ℚ))` produces an **elliptic**
  curve over an algebraically closed field of characteristic `0`, and `hasChordSum_of_map` brings
  the identity back.  ⚠️ This is *not* `EllipticCurves.Torsion.OmegaCharZero`'s reduction: that one
  quantifies over **every** curve over such a field, including singular ones, where there is no
  group law.  Only one curve over one field is ever needed here.
* **The chord sum.**  `WeierstrassCurve.Affine.addX_add_addX_negY`: for two points of `W` with
  distinct `x`-coordinates,
  `2·(x(Q+P) + x(Q−P))·(x_Q − x_P)² = Ψ₂Sq(x_Q) + Ψ₂Sq(x_P) − (b₂ + 4(x_Q + x_P))·(x_Q − x_P)²`.
  ⚠️ Mathlib has the **difference** of the two chord intersections
  (`WeierstrassCurve.Affine.addX_eq_addX_negY_sub`) and not their sum, so this has to be proved;
  four lines, `field_simp` and `linear_combination` against the two curve equations.
* **Points to polynomials.**  Over `K`, at every `x` off the roots of `ΨSq_{n−1}·ΨSqₙ·ΨSq_{n+1}`,
  take a point `P = (x, y)` (`WeierstrassCurve.Affine.exists_equation`), put `Q := n • P`, and read
  `x(Q) = Φₙ(x)/ΨSqₙ(x)` off the merged `hasXCoordFormula_of_two_ne_zero`
  (`EllipticCurves.Torsion.NsmulOrder`, `#251`, every index).  `(n±1) • P = Q ± P`, so the chord
  sum applies; clearing denominators gives the evaluated identity.  The bad `x` are the roots of
  three nonzero polynomials, hence finitely many, and both sides are polynomials, so multiplying
  through by `ΨSq_{n−1}·ΨSqₙ·ΨSq_{n+1}` makes the two sides agree at **every** point of the
  infinite field `K` and `Polynomial.funext` finishes.

`ΨSqₖ ≠ 0` needs `(k : K) ≠ 0`, which in characteristic `0` is `k ≠ 0`; so that argument runs at
`n ≥ 2` only, and `n = 0`, `n = 1` are the two hand computations `hasChordSum_zero` and
`hasChordSum_one`.  Negative indices are `hasChordSum_neg`, since `Φ` and `ΨSq` are even in the
index.

## Main statements

⚠️ Every public declaration of this file is listed: **16 public, 3 private, 16 listed.**  The three
`private` ones are the point-theoretic core — `chordSum_eval_of_chord` (the algebra that clears the
denominators, stated at three *independent* indices because it needs no relation between them),
`chordSum_eval` (the evaluated identity at a good `x`) and `hasChordSum_succ` (the polynomial
identity at `n ≥ 2` over an algebraically closed characteristic-`0` field).  None of them is worth
a consumer's attention: `hasChordSum` subsumes all three.

* `WeierstrassCurve.HasChordSum` : the identity, as a `Prop` that can be transported between rings.
* `WeierstrassCurve.HasChordSum.map`, `…hasChordSum_of_map`, `…hasChordSum_of_univ`,
  `…forall_hasChordSum_iff_univ`, `…hasChordSum_of_univQ` : the universal-curve descent, the merged
  pattern of `EllipticCurves.Torsion.OmegaUniversal` run once more.
* `WeierstrassCurve.hasChordSum_neg`, `…hasChordSum_zero`, `…hasChordSum_one` : the symmetry in `n`
  and the two base indices.
* `WeierstrassCurve.univ_Δ_ne_zero` and `WeierstrassCurve.univQ_Δ_ne_zero` : the universal
  discriminant is not the zero polynomial — what makes the base change to `K` elliptic.
* `WeierstrassCurve.Affine.addX_add_addX_negY` : **the chord sum**, the one genuinely new input.
* `WeierstrassCurve.Affine.hasChordSum_of_isAlgClosed` : the identity for an elliptic curve over an
  algebraically closed field of characteristic `0`, at every index.
* `WeierstrassCurve.hasChordSum` : **the identity, for every curve over every commutative ring, at
  every `n : ℤ`.**
* `WeierstrassCurve.hasChordSum_cleared` : the same in `#1506`'s display, through the merged
  `WeierstrassCurve.hasΨSqDoubling`.
* `WeierstrassCurve.hasChordSum_two_of_b_relation` : **the independent cross-check at `n = 2`** —
  the identity re-derived from Mathlib's closed forms for `Φ₂`, `Φ₃`, `ΨSq₂`, `ΨSq₃` by polynomial
  algebra alone, with no group law, no descent and no point anywhere.  ⚠️ It is *not* free: it
  needs `WeierstrassCurve.b_relation` (`4b₈ = b₂b₆ − b₄²`) with the coefficient `X²·Ψ₂Sq`, and with
  the `bᵢ` as independent atoms the identity is **false** — which is what makes it a check rather
  than a restatement.

## ⚠️ What this does NOT do

* **It says nothing about `[n]∗ω = nω`,** which is `#1506` scope item 1 and has a derivative in it.
  This is one of that route's four inputs (its "S1"); the other three are `ψ_add_mul_ψ_sub`
  (merged), `HasΨSqDoubling` (merged) and the chain rule for `Σ ∘ xₙ`, which wants a derivation on
  a fraction field and is where PR #582's review puts the remaining cost.  **That one is
  untouched.**
* **It says nothing about `#E[n] = n²`.**  `PrimaryTower`, `#1490` and `#293` are unmoved.
* `#1184`'s arbitrary-ring coprimality, `#962` and `#639` are untouched, and nothing here is
  imported by any pre-existing module.

## References

* [J. H. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.2 and Exercise 3.7.
-/

open Polynomial

namespace WeierstrassCurve

variable {R S : Type*} [CommRing R] [CommRing S]

/-- **The additive recurrence for the division-polynomial `x`-coordinate**, at index `n`:

```
Φ_{n+1}·ΨSq_{n−1} + Φ_{n−1}·ΨSq_{n+1}
  = 2X·Φₙ² + (2X² + b₂X + b₄)·Φₙ·ΨSqₙ + (b₄X + b₆)·ΨSqₙ² .
```

Packaged as a `Prop` so that it can be transported between rings; `WeierstrassCurve.hasChordSum`
proves it over every commutative ring at every index, so a consumer wants that and not this.

⚠️ Every symbol is Mathlib's: `Φ`, `ΨSq` are
`Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic`\'s, `b₂`, `b₄`, `b₆` are
`Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass`\'s.  Nothing of this project appears in the
statement. -/
def HasChordSum (W : WeierstrassCurve R) (n : ℤ) : Prop :=
  W.Φ (n + 1) * W.ΨSq (n - 1) + W.Φ (n - 1) * W.ΨSq (n + 1) =
    2 * X * W.Φ n ^ 2 + (2 * X ^ 2 + C W.b₂ * X + C W.b₄) * W.Φ n * W.ΨSq n +
      (C W.b₄ * X + C W.b₆) * W.ΨSq n ^ 2

/-- **The identity transports along any ring homomorphism.**  Every ingredient commutes with base
change — `map_Φ` / `map_ΨSq` and `map_b₂` / `map_b₄` / `map_b₆` in Mathlib — so applying
`Polynomial.map f` to both sides is the whole proof. -/
theorem HasChordSum.map {W : WeierstrassCurve R} {n : ℤ} (h : W.HasChordSum n) (f : R →+* S) :
    (W.map f).HasChordSum n := by
  have H := congrArg (Polynomial.map f) h
  simpa only [HasChordSum, map_Φ, map_ΨSq, WeierstrassCurve.map_b₂, WeierstrassCurve.map_b₄,
    WeierstrassCurve.map_b₆, Polynomial.map_mul, Polynomial.map_add, Polynomial.map_pow,
    Polynomial.map_ofNat, Polynomial.map_C, Polynomial.map_X] using H

/-- **The identity descends along an injective ring homomorphism.**  `Polynomial.map f` is
injective when `f` is, so an identity that holds after base change already held before it.  This is
what lets the identity be proved over a field — where there are points, and a group law — and then
pulled back to the universal polynomial ring. -/
theorem hasChordSum_of_map {W : WeierstrassCurve R} {f : R →+* S} (hf : Function.Injective f)
    {n : ℤ} (h : (W.map f).HasChordSum n) : W.HasChordSum n := by
  refine Polynomial.map_injective f hf ?_
  simpa only [HasChordSum, map_Φ, map_ΨSq, WeierstrassCurve.map_b₂, WeierstrassCurve.map_b₄,
    WeierstrassCurve.map_b₆, Polynomial.map_mul, Polynomial.map_add, Polynomial.map_pow,
    Polynomial.map_ofNat, Polynomial.map_C, Polynomial.map_X] using h

/-- **The reduction.**  `HasChordSum n` for the universal curve gives it for every Weierstrass
curve over every commutative ring, by base change along `W.specialize`. -/
theorem hasChordSum_of_univ {n : ℤ} (h : univ.HasChordSum n) (W : WeierstrassCurve R) :
    W.HasChordSum n := by
  have H := h.map W.specialize
  rwa [univ_map_specialize] at H

/-- **The reduction is lossless**: the universal instance is *equivalent* to the universally
quantified statement, since `univ` is itself one of the curves quantified over.  Stated at `Type`
because that is where `univ` lives; `hasChordSum_of_univ` is the universe-polymorphic form and is
what consumers should use. -/
theorem forall_hasChordSum_iff_univ {n : ℤ} :
    (∀ (R : Type) [CommRing R] (W : WeierstrassCurve R), W.HasChordSum n) ↔ univ.HasChordSum n :=
  ⟨fun h => h _ univ, fun h _ _ W => hasChordSum_of_univ h W⟩

/-- **The reduction, over a characteristic-`0` base.**  `HasChordSum n` for `univQ` gives it for
every Weierstrass curve over every commutative ring: descend along the injective
`MvPolynomial.map (Int.castRingHom ℚ)` to `univ`, then specialise.  Characteristic `0` is what the
proof below spends — on `2 ≠ 0` for the chord formula, and on `ΨSqₖ ≠ 0` at `k ≠ 0`. -/
theorem hasChordSum_of_univQ {n : ℤ} (h : univQ.HasChordSum n) (W : WeierstrassCurve R) :
    W.HasChordSum n :=
  hasChordSum_of_univ (hasChordSum_of_map (MvPolynomial.map_injective _ Int.cast_injective) h) W

/-- **The identity at `-n` is the identity at `n`.**  `Φ` and `ΨSq` are both even in the index
(`Φ_neg`, `ΨSq_neg`), and `-n ± 1 = -(n ∓ 1)`, so the two sides are the two sides at `n` with the
summands of the left-hand side exchanged.  An induction on `n` may therefore assume `0 ≤ n`. -/
theorem hasChordSum_neg {W : WeierstrassCurve R} {n : ℤ} (h : W.HasChordSum n) :
    W.HasChordSum (-n) := by
  have e₁ : -n + 1 = -(n - 1) := by ring
  have e₂ : -n - 1 = -(n + 1) := by ring
  rw [HasChordSum, e₁, e₂, Φ_neg, Φ_neg, ΨSq_neg, ΨSq_neg, Φ_neg, ΨSq_neg]
  rw [HasChordSum] at h
  linear_combination h

/-- **The identity at `n = 0`.**  `ΨSq₀ = 0` and `Φ₀ = 1` kill both terms of the right-hand side
after the first, and the left-hand side is `Φ₁·ΨSq₋₁ + Φ₋₁·ΨSq₁ = X + X`.  ⚠️ This index is
outside the reach of the point-theoretic argument below — `ΨSq₀ = 0` has every `x` as a root — and
is also where the cleared display of `#1506` degenerates to `0 = 0`. -/
theorem hasChordSum_zero (W : WeierstrassCurve R) : W.HasChordSum 0 := by
  rw [HasChordSum]
  norm_num [Φ_zero, Φ_one, ΨSq_zero, ΨSq_one, show (0 : ℤ) - 1 = -1 from rfl, Φ_neg, ΨSq_neg]
  ring

/-- **The identity at `n = 1`.**  Both sides are `Ψ₂Sq = 4X³ + b₂X² + 2b₄X + b₆`: on the left
`Φ₂·ΨSq₀ + Φ₀·ΨSq₂ = ΨSq₂`, on the right `2X·X² + (2X² + b₂X + b₄)·X + (b₄X + b₆)`.  ⚠️ Like
`hasChordSum_zero` this is outside the point-theoretic argument\'s range, which needs
`ΨSq_{n−1} ≠ 0`. -/
theorem hasChordSum_one (W : WeierstrassCurve R) : W.HasChordSum 1 := by
  rw [HasChordSum]
  norm_num [Φ_zero, Φ_one, Φ_two, ΨSq_zero, ΨSq_one, ΨSq_two, Ψ₂Sq, b₈, map_ofNat]
  ring

/-! ### The universal curve is nonsingular over a field -/

/-- **The universal discriminant is not the zero polynomial.**

If it were, then specialising along `W.specialize` would make `W.Δ = 0` for *every* Weierstrass
curve over every commutative ring (`univ_map_specialize` and `map_Δ`).  It does not: the curve
`Y² = X³ + 1` over `ℤ` has `b₂ = b₄ = b₈ = 0`, `b₆ = 4` and `Δ = -27·4² = -432`.

⚠️ This is what makes the base change of `univQ` to a field **elliptic**, and it is the only reason
this file can use the group law at all. -/
theorem univ_Δ_ne_zero : univ.Δ ≠ 0 := by
  intro h
  have h1 : (univ.map (WeierstrassCurve.specialize
      (⟨0, 0, 0, 0, 1⟩ : WeierstrassCurve ℤ))).Δ = 0 := by rw [map_Δ, h, map_zero]
  rw [univ_map_specialize] at h1
  norm_num [WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆,
    WeierstrassCurve.b₈] at h1

/-- **The rational universal discriminant is not the zero polynomial**, by `univ_Δ_ne_zero` and
the injectivity of `MvPolynomial.map (Int.castRingHom ℚ)`. -/
theorem univQ_Δ_ne_zero : univQ.Δ ≠ 0 := by
  rw [univQ, map_Δ]
  exact fun h => univ_Δ_ne_zero
    (MvPolynomial.map_injective _ Int.cast_injective (by rw [h, map_zero]))

namespace Affine

variable {F : Type*} [Field F] {W : Affine F}

/-- **The chord sum**: for two points `(x₁, y₁)`, `(x₂, y₂)` of `W` with `x₁ ≠ x₂`,

```
2·(x(P₁ + P₂) + x(P₁ − P₂))·(x₁ − x₂)² = Ψ₂Sq(x₁) + Ψ₂Sq(x₂) − (b₂ + 4(x₁ + x₂))·(x₁ − x₂)² .
```

The two `addX`s are the two chord intersections, `P₁ + P₂` using `(x₂, y₂)` and `P₁ − P₂` using its
negation `(x₂, negY x₂ y₂)`.  What the identity says is that their **sum** depends only on the two
`x`-coordinates — the `yᵢ` cancel, which is why `Ψ₂Sq` (a polynomial in `X` alone) can appear on
the right.

⚠️ **Mathlib has the difference and not the sum.**  `WeierstrassCurve.Affine.addX_eq_addX_negY_sub`
gives `x(P₁ + P₂) − x(P₁ − P₂) = −ψ(P₁)ψ(P₂)/(x₂ − x₁)²`, which still mentions the `yᵢ` through
`ψ(x, y) = 2y + a₁x + a₃`.  This is the other combination, and it is the one the division
polynomials see.

⚠️ The `linear_combination` coefficient really is `4` on each curve equation, not `4·(x₁ − x₂)²`;
`field_simp` has already cleared the denominators by then, and the second guess fails. -/
theorem addX_add_addX_negY [DecidableEq F] {x₁ x₂ y₁ y₂ : F} (h₁ : W.Equation x₁ y₁)
    (h₂ : W.Equation x₂ y₂) (hx : x₁ ≠ x₂) :
    2 * (W.addX x₁ x₂ (W.slope x₁ x₂ y₁ y₂)
          + W.addX x₁ x₂ (W.slope x₁ x₂ y₁ (W.negY x₂ y₂))) * (x₁ - x₂) ^ 2
      = W.Ψ₂Sq.eval x₁ + W.Ψ₂Sq.eval x₂ - (W.b₂ + 4 * (x₁ + x₂)) * (x₁ - x₂) ^ 2 := by
  rw [equation_iff] at h₁ h₂
  rw [slope_of_X_ne hx, slope_of_X_ne hx]
  have hd : x₁ - x₂ ≠ 0 := sub_ne_zero.mpr hx
  simp only [addX, negY, WeierstrassCurve.Ψ₂Sq, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, eval_add, eval_mul, eval_pow, eval_C, eval_X, eval_ofNat, map_ofNat]
  field_simp
  linear_combination (4 : F) * h₁ + (4 : F) * h₂

private theorem chordSum_eval_of_chord {x u a b : F} (h2 : (2 : F) ≠ 0) {m p n : ℤ}
    (hm : (W.ΨSq m).eval x ≠ 0) (hp : (W.ΨSq p).eval x ≠ 0)
    (hn : (W.ΨSq n).eval x ≠ 0)
    (hu : u = (W.Φ m).eval x / (W.ΨSq m).eval x)
    (ha : a = (W.Φ p).eval x / (W.ΨSq p).eval x)
    (hb : b = (W.Φ n).eval x / (W.ΨSq n).eval x)
    (hG : (x * (W.ΨSq m).eval x - (W.Φ m).eval x) ^ 2
        = (W.ΨSq p).eval x * (W.ΨSq n).eval x)
    (hchord : 2 * (a + b) * (u - x) ^ 2
        = W.Ψ₂Sq.eval u + W.Ψ₂Sq.eval x - (W.b₂ + 4 * (u + x)) * (u - x) ^ 2) :
    (W.Φ p).eval x * (W.ΨSq n).eval x + (W.Φ n).eval x * (W.ΨSq p).eval x
      = 2 * x * (W.Φ m).eval x ^ 2
        + (2 * x ^ 2 + W.b₂ * x + W.b₄) * (W.Φ m).eval x * (W.ΨSq m).eval x
        + (W.b₄ * x + W.b₆) * (W.ΨSq m).eval x ^ 2 := by
  subst hu ha hb
  simp only [WeierstrassCurve.Ψ₂Sq, eval_add, eval_mul, eval_pow, eval_C, eval_X, eval_ofNat,
    map_ofNat] at hchord
  field_simp at hchord
  rw [← hG] at hchord
  have hG2 : (x * (W.ΨSq m).eval x - (W.Φ m).eval x) ^ 2 ≠ 0 := by
    rw [hG]; exact mul_ne_zero hp hn
  have key : (x * (W.ΨSq m).eval x - (W.Φ m).eval x) ^ 2 *
      (2 * (W.ΨSq m).eval x *
        ((W.Φ p).eval x * (W.ΨSq n).eval x + (W.Φ n).eval x * (W.ΨSq p).eval x))
      = (x * (W.ΨSq m).eval x - (W.Φ m).eval x) ^ 2 *
      (2 * (W.ΨSq m).eval x *
        (2 * x * (W.Φ m).eval x ^ 2
          + (2 * x ^ 2 + W.b₂ * x + W.b₄) * (W.Φ m).eval x * (W.ΨSq m).eval x
          + (W.b₄ * x + W.b₆) * (W.ΨSq m).eval x ^ 2)) := by
    linear_combination hchord
  exact mul_left_cancel₀ (mul_ne_zero h2 hm) (mul_left_cancel₀ hG2 key)

variable [IsAlgClosed F] [W.IsElliptic]

private theorem chordSum_eval (h2 : (2 : F) ≠ 0) (k : ℕ) {x : F}
    (h0 : (W.ΨSq ((k : ℕ) : ℤ)).eval x ≠ 0)
    (h1 : (W.ΨSq (((k + 1 : ℕ)) : ℤ)).eval x ≠ 0)
    (h2' : (W.ΨSq (((k + 2 : ℕ)) : ℤ)).eval x ≠ 0) :
    (W.Φ (((k + 2 : ℕ)) : ℤ)).eval x * (W.ΨSq ((k : ℕ) : ℤ)).eval x
        + (W.Φ ((k : ℕ) : ℤ)).eval x * (W.ΨSq (((k + 2 : ℕ)) : ℤ)).eval x
      = 2 * x * (W.Φ (((k + 1 : ℕ)) : ℤ)).eval x ^ 2
        + (2 * x ^ 2 + W.b₂ * x + W.b₄) * (W.Φ (((k + 1 : ℕ)) : ℤ)).eval x
            * (W.ΨSq (((k + 1 : ℕ)) : ℤ)).eval x
        + (W.b₄ * x + W.b₆) * (W.ΨSq (((k + 1 : ℕ)) : ℤ)).eval x ^ 2 := by
  classical
  have e0 : ((k : ℕ) : ℤ) = ((k : ℤ) + 1) - 1 := by ring
  have e2 : ((k + 2 : ℕ) : ℤ) = ((k : ℤ) + 1) + 1 := by push_cast; ring
  have e1 : ((k + 1 : ℕ) : ℤ) = (k : ℤ) + 1 := by exact_mod_cast rfl
  obtain ⟨y, hy⟩ := exists_equation (W := W) h2 x
  have hns : W.Nonsingular x y := (equation_iff_nonsingular ..).mp hy
  obtain ⟨ym, hnsm, hQ⟩ := hasXCoordFormula_of_two_ne_zero (W := W) h2 (k + 1) hns h1
  obtain ⟨ya, hnsa, hA⟩ := hasXCoordFormula_of_two_ne_zero (W := W) h2 (k + 2) hns h2'
  obtain ⟨yb, hnsb, hB⟩ := hasXCoordFormula_of_two_ne_zero (W := W) h2 k hns h0
  set u := (W.Φ (((k + 1 : ℕ)) : ℤ)).eval x / (W.ΨSq (((k + 1 : ℕ)) : ℤ)).eval x with hu
  have hψ1 : (W.ψ (((k : ℤ) + 1) + 1)).evalEval x y ≠ 0 := fun hz =>
    h2' (by rw [e2, ← ψ_sq_evalEval hy, hz]; ring)
  have hψ2 : (W.ψ (((k : ℤ) + 1) - 1)).evalEval x y ≠ 0 := fun hz =>
    h0 (by rw [e0, ← ψ_sq_evalEval hy, hz]; ring)
  have hux : u ≠ x := by
    intro h
    rcases (Φ_div_ΨSq_eq_iff hy (p := (k : ℤ) + 1) (q := 1) (by rwa [e1] at h1)
      (by simp [ΨSq_one])).mp
      (by rw [Φ_one, ΨSq_one, eval_X, eval_one, div_one]
          rw [hu, e1] at h
          exact h.symm) with h' | h'
    · exact hψ1 h'
    · exact hψ2 h'
  have hstep : (k + 1) • Point.some x y hns + Point.some x y hns
      = (k + 2) • Point.some x y hns := by
    conv_rhs => rw [show k + 2 = (k + 1) + 1 from rfl, succ_nsmul]
  have hstep' : k • Point.some x y hns + Point.some x y hns
      = (k + 1) • Point.some x y hns := by conv_rhs => rw [succ_nsmul]
  have hsum : Point.some u ym hnsm + Point.some x y hns
      = Point.some (W.addX u x (W.slope u x ym y)) _
        (nonsingular_add hnsm hns fun hxy => hux hxy.left) := Point.add_of_X_ne hux
  have hdif : Point.some u ym hnsm + -Point.some x y hns
      = Point.some (W.addX u x (W.slope u x ym (W.negY x y))) _
        (nonsingular_add hnsm ((nonsingular_neg ..).mpr hns) fun hxy => hux hxy.left) :=
    Point.add_of_X_ne hux
  have ha : W.addX u x (W.slope u x ym y)
      = (W.Φ (((k + 2 : ℕ)) : ℤ)).eval x / (W.ΨSq (((k + 2 : ℕ)) : ℤ)).eval x := by
    rw [hQ, hA, hsum] at hstep
    simp only [Point.some.injEq] at hstep
    exact hstep.1
  have hb : W.addX u x (W.slope u x ym (W.negY x y))
      = (W.Φ ((k : ℕ) : ℤ)).eval x / (W.ΨSq ((k : ℕ) : ℤ)).eval x := by
    have hk : k • Point.some x y hns = Point.some u ym hnsm + -Point.some x y hns := by
      rw [← hQ, ← hstep']; abel
    rw [hB, hdif] at hk
    simp only [Point.some.injEq] at hk
    exact hk.1.symm
  refine chordSum_eval_of_chord h2 h1 h2' h0 hu rfl rfl ?_ ?_
  · have hid := ψ_add_mul_ψ_sub_evalEval hy ((k : ℤ) + 1) 1
    rw [Φ_one, ΨSq_one, eval_X, eval_one, mul_one, ← e2, ← e0, ← e1] at hid
    rw [← hid, mul_pow, ψ_sq_evalEval hy, ψ_sq_evalEval hy]
  · rw [← ha, ← hb]
    exact addX_add_addX_negY hnsm.left hy hux

private theorem hasChordSum_succ [CharZero F] (k : ℕ) (hk : k ≠ 0) :
    W.HasChordSum ((k : ℤ) + 1) := by
  have h2 : (2 : F) ≠ 0 := two_ne_zero
  have e0 : ((k : ℕ) : ℤ) = ((k : ℤ) + 1) - 1 := by ring
  have e2 : ((k + 2 : ℕ) : ℤ) = ((k : ℤ) + 1) + 1 := by push_cast; ring
  have e1 : ((k + 1 : ℕ) : ℤ) = (k : ℤ) + 1 := by exact_mod_cast rfl
  have c0 : ((k : ℕ) : F) ≠ 0 := Nat.cast_ne_zero.mpr hk
  have c1 : ((k + 1 : ℕ) : F) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero k)
  have c2 : ((k + 2 : ℕ) : F) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero (k + 1))
  have n0 : W.ΨSq ((k : ℕ) : ℤ) ≠ 0 := W.ΨSq_ne_zero (by exact_mod_cast c0)
  have n1 : W.ΨSq ((k + 1 : ℕ) : ℤ) ≠ 0 := W.ΨSq_ne_zero (by exact_mod_cast c1)
  have n2 : W.ΨSq ((k + 2 : ℕ) : ℤ) ≠ 0 := W.ΨSq_ne_zero (by exact_mod_cast c2)
  rw [HasChordSum, ← e2, ← e0, ← e1]
  refine mul_left_cancel₀ (a := W.ΨSq ((k : ℕ) : ℤ) * W.ΨSq ((k + 1 : ℕ) : ℤ)
    * W.ΨSq ((k + 2 : ℕ) : ℤ)) (mul_ne_zero (mul_ne_zero n0 n1) n2) ?_
  refine Polynomial.funext fun x => ?_
  simp only [eval_mul, eval_add, eval_pow, eval_X, eval_C, eval_ofNat]
  by_cases h0 : (W.ΨSq ((k : ℕ) : ℤ)).eval x = 0
  · rw [h0]; ring
  by_cases h1 : (W.ΨSq ((k + 1 : ℕ) : ℤ)).eval x = 0
  · rw [h1]; ring
  by_cases h2' : (W.ΨSq ((k + 2 : ℕ) : ℤ)).eval x = 0
  · rw [h2']; ring
  rw [chordSum_eval h2 k h0 h1 h2']

/-- **The identity for an elliptic curve over an algebraically closed field of characteristic
`0`**, at every `n : ℤ`.  `hasChordSum_succ` at `n ≥ 2`, the two hand computations at `n = 0, 1`,
and `hasChordSum_neg` for the negative indices. -/
theorem hasChordSum_of_isAlgClosed [CharZero F] (n : ℤ) : W.HasChordSum n := by
  suffices h : ∀ m : ℕ, W.HasChordSum (m : ℤ) by
    by_cases hn : 0 ≤ n
    · lift n to ℕ using hn; exact h n
    · obtain ⟨m, hm⟩ : ∃ m : ℕ, n = -(m : ℤ) := ⟨(-n).toNat, by omega⟩
      rw [hm]
      exact hasChordSum_neg (h m)
  intro m
  match m with
  | 0 => exact_mod_cast hasChordSum_zero W
  | 1 => exact_mod_cast hasChordSum_one W
  | (k + 2) =>
      rw [show ((k + 2 : ℕ) : ℤ) = ((k + 1 : ℕ) : ℤ) + 1 by push_cast; ring]
      exact hasChordSum_succ (k + 1) (Nat.succ_ne_zero k)

end Affine

/-! ### The identity, over every commutative ring -/

/-- **The additive recurrence, for every Weierstrass curve over every commutative ring, at every
`n : ℤ`**, with no hypotheses:

```
Φ_{n+1}·ΨSq_{n−1} + Φ_{n−1}·ΨSq_{n+1}
  = 2X·Φₙ² + (2X² + b₂X + b₄)·Φₙ·ΨSqₙ + (b₄X + b₆)·ΨSqₙ² .
```

`hasChordSum_of_univQ` reduces this to the single curve `univQ`; base changing along the injection
of `MvPolynomial (Fin 5) ℚ` into `K := AlgebraicClosure (FractionRing (MvPolynomial (Fin 5) ℚ))`
makes it an elliptic curve over an algebraically closed field of characteristic `0`
(`univQ_Δ_ne_zero`), where `hasChordSum_of_isAlgClosed` applies, and `hasChordSum_of_map` brings it
back.

⚠️ Characteristic `2` and singular curves are covered by the conclusion even though the proof runs
nowhere near them — that is what the universal reduction buys, and it is the same trade
`WeierstrassCurve.hasPreΩSq` makes in `EllipticCurves.Torsion.OmegaCrux`. -/
theorem hasChordSum (W : WeierstrassCurve R) (n : ℤ) : W.HasChordSum n := by
  classical
  refine hasChordSum_of_univQ ?_ W
  set B := MvPolynomial (Fin 5) ℚ with hB
  set K := AlgebraicClosure (FractionRing B) with hK
  set f : B →+* K := (algebraMap (FractionRing B) K).comp (algebraMap B (FractionRing B)) with hf
  have hfinj : Function.Injective f :=
    (algebraMap (FractionRing B) K).injective.comp (IsFractionRing.injective B (FractionRing B))
  refine hasChordSum_of_map (f := f) hfinj ?_
  haveI : (univQ.map f).IsElliptic := by
    refine ⟨?_⟩
    rw [map_Δ]
    exact isUnit_iff_ne_zero.mpr fun h => univQ_Δ_ne_zero ((map_eq_zero_iff f hfinj).mp h)
  exact Affine.hasChordSum_of_isAlgClosed n


/-- **The same identity in `#1506`\'s display**, for a consumer that wants it in the vocabulary of
that issue\'s route:

```
2·ΨSqₙ²·(Φ_{n+1}ΨSq_{n−1} + Φ_{n−1}ΨSq_{n+1})
    = ΨSq₂ₙ + ΨSqₙ⁴·Ψ₂Sq − b₂·ΨSqₙ²·Gₙ² − 4·ΨSqₙ·(Φₙ + X·ΨSqₙ)·Gₙ² ,   Gₙ = X·ΨSqₙ − Φₙ .
```

⚠️ **This is strictly weaker than `hasChordSum`, not equivalent to it**: it carries the factor
`2·ΨSqₙ²`, so it says nothing in characteristic `2` and nothing at `n = 0`.  It is derived from
`hasChordSum` and the merged `WeierstrassCurve.hasΨSqDoubling`
(`EllipticCurves.Torsion.OmegaCrux`), which is what supplies `ΨSq₂ₙ`; every `Gₙ²` term then
cancels.  ⚠️ It is **not** an independent statement and must not be cited as evidence for
`hasChordSum`. -/
theorem hasChordSum_cleared (W : WeierstrassCurve R) (n : ℤ) :
    2 * W.ΨSq n ^ 2 * (W.Φ (n + 1) * W.ΨSq (n - 1) + W.Φ (n - 1) * W.ΨSq (n + 1))
      = W.ΨSq (2 * n) + W.ΨSq n ^ 4 * W.Ψ₂Sq
        - C W.b₂ * W.ΨSq n ^ 2 * (X * W.ΨSq n - W.Φ n) ^ 2
        - 4 * W.ΨSq n * (W.Φ n + X * W.ΨSq n) * (X * W.ΨSq n - W.Φ n) ^ 2 := by
  have h : W.Φ (n + 1) * W.ΨSq (n - 1) + W.Φ (n - 1) * W.ΨSq (n + 1) =
      2 * X * W.Φ n ^ 2 + (2 * X ^ 2 + C W.b₂ * X + C W.b₄) * W.Φ n * W.ΨSq n +
        (C W.b₄ * X + C W.b₆) * W.ΨSq n ^ 2 := W.hasChordSum n
  rw [W.hasΨSqDoubling n, WeierstrassCurve.Ψ₂Sq]
  simp only [map_ofNat, map_mul]
  linear_combination (2 * W.ΨSq n ^ 2) * h

/-- **The independent cross-check at `n = 2`.**

`hasChordSum` at `n = 2` reads `Φ₃·ΨSq₁ + Φ₁·ΨSq₃ = 2X·Φ₂² + (2X² + b₂X + b₄)·Φ₂·ΨSq₂ +
(b₄X + b₆)·ΨSq₂²`.  This proves that *same equation* from Mathlib\'s closed forms for `Φ₂`, `Φ₃`,
`ΨSq₂ = Ψ₂Sq` and `ΨSq₃ = Ψ₃²` by polynomial algebra alone — **no group law, no point, no descent,
no universal curve** — so a sign or coefficient error in `HasChordSum` would break it.

⚠️ It is not a `ring` call.  With `b₂`, `b₄`, `b₆`, `b₈` as independent atoms the identity is
**false**; it needs `WeierstrassCurve.b_relation` (`4b₈ = b₂b₆ − b₄²`), with the coefficient
`−X²·Ψ₂Sq`.  That the discrepancy is exactly a multiple of the `b`-relation is the content of the
check.

⚠️ It is stated in the unfolded form rather than as `W.HasChordSum 2` so that it is visibly
independent of the definition; `W.hasChordSum 2` proves the same thing the other way. -/
theorem hasChordSum_two_of_b_relation (W : WeierstrassCurve R) :
    W.Φ 3 * W.ΨSq 1 + W.Φ 1 * W.ΨSq 3
      = 2 * X * W.Φ 2 ^ 2 + (2 * X ^ 2 + C W.b₂ * X + C W.b₄) * W.Φ 2 * W.ΨSq 2
        + (C W.b₄ * X + C W.b₆) * W.ΨSq 2 ^ 2 := by
  have hb : (4 : R[X]) * C W.b₈ = C W.b₂ * C W.b₆ - C W.b₄ ^ 2 := by
    simpa only [map_mul, map_sub, map_pow, map_ofNat] using congrArg (C : R →+* R[X]) W.b_relation
  simp only [Φ_three, ΨSq_three, Φ_one, ΨSq_one, Φ_two, ΨSq_two, WeierstrassCurve.Ψ₃,
    WeierstrassCurve.preΨ₄, WeierstrassCurve.Ψ₂Sq, map_mul, map_sub, map_pow, map_ofNat]
  linear_combination (-(X ^ 2) * (4 * X ^ 3 + C W.b₂ * X ^ 2 + 2 * C W.b₄ * X + C W.b₆)) * hb

end WeierstrassCurve
