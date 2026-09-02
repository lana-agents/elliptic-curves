/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import EllipticCurves.Torsion.ChordSum
import EllipticCurves.Torsion.WronskianRecurrence

/-!
# The `y`-half of the chord recurrence, and `#E[n] = n²` at odd `n`

`EllipticCurves.Torsion.WronskianRecurrence` reduced `#1506` scope item 1 — the Wronskian identity
`Φₙ′·ΨSqₙ − Φₙ·ΨSqₙ′ = n·preΨₙ·preΩₙ`, the last gate on `#E[n] = n²` at odd `n` — to **three**
derivative-free polynomial identities: `S1` (`WronskianRec.ChordSum`, discharged by
`EllipticCurves.Torsion.ChordSum`'s `WeierstrassCurve.hasChordSum`) and the pair `C1`, `C2`
(`WronskianRec.OmegaSum`, `WronskianRec.OmegaDiff`), which were open.

**This file proves `C1` and `C2`, and therefore the Wronskian identity and `#E[n] = n²` at odd
`n`,** unconditionally: `WeierstrassCurve.hasWronskianId` and
`WeierstrassCurve.Affine.card_torsion_eq_sq_of_odd`.

## `C1` and `C2` are one identity, not two

The content is a single statement, `WeierstrassCurve.HasOmegaChord`, over an **arbitrary commutative
ring** at an **arbitrary** `m : ℤ` with no hypotheses:

```
2 · preΨ_{2(m+1)} · ΨSq_{m−1}²  =  Gₘ · (Lₘ · preΨ_{2m} − Rₘ) ,
```

with `Gₘ`, `Lₘ`, `Rₘ` the polynomials `WronskianRec.G`, `.L`, `.Rem` of
`EllipticCurves.Torsion.WronskianRecurrence`.  ⚠️ **`C1` and `C2` are its `m` and `−m` instances.**
`preΨ` is *odd* in the index (`preΨ_neg`) while `Φ` and `ΨSq` — hence `G`, `L`, `Rem` — are *even*
(`Φ_neg`, `ΨSq_neg`), so the identity at `−m` reads
`2·preΨ_{2(m−1)}·ΨSqₘ₊₁² = Gₘ·(Lₘ·preΨ₂ₘ + Rₘ)`; adding and subtracting gives `2·C1` and `2·C2`.
The factor `2` is cancelled once and for all over `univQ`, whose base `MvPolynomial (Fin 5) ℚ` is a
characteristic-`0` domain, and the universal descent then carries `C1` and `C2` back to **every**
commutative ring (`WeierstrassCurve.omegaSum`, `WeierstrassCurve.omegaDiff`).

## The proof

The shape is `EllipticCurves.Torsion.ChordSum`'s, with the `y`-coordinate formula in place of the
`x`-coordinate one; that file is the template and this one follows it step for step.

* **The one genuinely new input** is `WeierstrassCurve.Affine.psi2_addY`: for two points of `W` with
  distinct `x`-coordinates,
  ```
  2·(x₂ − x₁)³·ψ₂(P₁ + P₂)
      = ((6x₂² + b₂x₂ + b₄)x₁ + 2x₂³ + b₂x₂² + 3b₄x₂ + 2b₆)·ψ₂(P₁)
        − (2x₁³ + (6x₂ + b₂)x₁² + (b₂x₂ + 3b₄)x₁ + b₄x₂ + 2b₆)·ψ₂(P₂) ,
  ```
  where `ψ₂(x, y) = 2y + a₁x + a₃`.  It is the `y`-analogue of the merged
  `WeierstrassCurve.Affine.addX_add_addX_negY`, and like it, it is one `linear_combination` against
  the two curve equations — here with the slope kept as a variable satisfying
  `L·(x₁ − x₂) = y₁ − y₂`
  rather than divided out, so that no `field_simp` is needed.
* **`ψ₂` at `n • P` is the division-polynomial ratio** (`WeierstrassCurve.Affine.psi2_omegaY`):
  `ψ₂(n • P) = ψ₂(P)·preΨ_{2n}(x)/ΨSqₙ(x)²`.  This is `preΨ_two_mul` (`preΨ₂ₙ = preΨₙ·preΩₙ`)
  together with the definition of `WeierstrassCurve.Affine.omegaY`; the `a₁`, `a₃` terms of `omegaY`
  are exactly what `2y + a₁x + a₃` cancels.  `WeierstrassCurve.Affine.exists_zsmul_eq_some_psi2`
  extends it from `ℕ` to `ℤ` — `(−n) • P = −(n • P)` negates `ψ₂`, and `preΨ` is odd in the
  index, so
  the two sides negate together and the statement is index-symmetric.
* **Points to polynomials.**  Over an algebraically closed field of characteristic `0` carrying an
  elliptic `W`, at every `x` off the roots of `ΨSq_{m−1}·ΨSqₘ·ΨSq_{m+1}·Ψ₂Sq`, take `P = (x, y)`,
  put `Q := m • P`, read the coordinates of `Q` and `Q + P` off the merged
  `nsmul_eq_some_omegaY_of_ΨSq_ne_zero` and `Point.add_of_X_ne`, and feed them to `psi2_addY`.  The
  bad `x` are finitely many and the field is infinite, so `Polynomial.funext` finishes after
  multiplying by the four polynomials.  ⚠️ `Ψ₂Sq(x) ≠ 0` is needed as well as the three `ΨSq`: it is
  `ψ₂(P) ≠ 0`, and the identity is divided by it.
* **Descent.** ⚠️ Not `OmegaCharZero`'s `hasPreΩSq_of_forall_algClosed`, which quantifies over
  singular curves too.  As in `EllipticCurves.Torsion.ChordSum`: `univQ_Δ_ne_zero` makes the base
  change of `univQ` to `AlgebraicClosure (FractionRing (MvPolynomial (Fin 5) ℚ))` elliptic, and one
  curve over one field is all that is used.  The three indices `m = 0, ±1` are outside that argument
  (`ΨSq₀ = 0`) and are proved by hand over an arbitrary commutative ring; at `m = ±1` both sides
  vanish because `G_{±1} = X·ΨSq₁ − Φ₁ = 0`.

## Main statements

⚠️ Every public declaration of this file is listed: **24 public, 3 private, 24 listed.**  The three
`private` ones are `omegaChord_clear` (the denominator clearing, stated at abstract field elements),
`omegaChord_eval` (the evaluated identity at a good `x`) and `hasOmegaPair_of_charZero` (the
`m`/`−m` combination, which needs `2` to be cancellable); `hasOmegaChord` and `hasOmegaPair` subsume
all three.

* `WeierstrassCurve.HasOmegaChord` : the identity, as a `Prop` transportable between rings.
* `WeierstrassCurve.HasOmegaChord.map`, `…hasOmegaChord_of_map`, `…hasOmegaChord_of_univ`,
  `…forall_hasOmegaChord_iff_univ`, `…hasOmegaChord_of_univQ` : the universal-curve descent.
* `WeierstrassCurve.hasOmegaChord_zero`, `…hasOmegaChord_one`, `…hasOmegaChord_neg_one` : the three
  indices the point-theoretic argument cannot reach.
* `WeierstrassCurve.Affine.psi2_addY` : **the chord identity for `ψ₂`**, the one new input.
* `WeierstrassCurve.Affine.psi2_omegaY`, `…exists_zsmul_eq_some_psi2` : `ψ₂` at `n • P`, at `ℤ`.
* `WeierstrassCurve.Affine.hasOmegaChord_of_isAlgClosed` : the identity away from `m = 0, ±1`, over
  an algebraically closed field of characteristic `0`.
* `WeierstrassCurve.hasOmegaChord` : **the identity, for every curve over every commutative ring, at
  every `m : ℤ`.**
* `WeierstrassCurve.HasOmegaPair`, `…HasOmegaPair.map`, `…hasOmegaPair_of_map`,
  `…hasOmegaPair_of_univ`, `…hasOmegaPair_of_univQ`, `…hasOmegaPair` : the pair `C1 ∧ C2` and its
  descent, which is where the factor `2` is spent.
* `WeierstrassCurve.omegaSum`, `WeierstrassCurve.omegaDiff` : **`C1` and `C2`**, over every
  commutative ring at every index — the two open hypotheses of
  `WeierstrassCurve.hasWronskianId_of_univQ_recurrence`.
* `WeierstrassCurve.hasWronskianId` : **`#1506` scope item 1**, `Φₙ′ΨSqₙ − ΦₙΨSqₙ′ = n·preΨₙ·preΩₙ`,
  over every commutative ring at every index, with no hypotheses.
* `WeierstrassCurve.Affine.card_torsion_eq_sq_of_odd` : **`#E[n] = n²` at odd `n`**, over an
  algebraically closed field, with no hypothesis beyond `2 ≠ 0` and `(n : F) ≠ 0`.

## ⚠️ What this does NOT do

* It does not touch `EllipticCurves.Torsion.PrimaryTower`'s gate list, `#1490` item 3 or `#293`.
  Those record `#E[n] = n²` as owed; `card_torsion_eq_sq_of_odd` now supplies it at odd `n`, so they
  are dischargeable, but that is a separate sweep and none of their statements is changed here.
  ⚠️ That sweep has since happened: `EllipticCurves.Torsion.PrimaryTowerOdd` discharges the gate
  list and `#1490` item 3 at every odd `p`, and settles `E[n] ≃+ (ℤ/nℤ)²` at every odd `n`.  `#293`
  is **not** closed by it — the even indices are untouched.
* It says nothing at even `n`: `card_torsion_eq_sq_of_wronskian_identity`'s route is the odd one.
* `#1184`, `#962` and `#639` are untouched.

## References

* [J. H. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.2 and Exercise 3.7.
-/

open Polynomial

namespace WeierstrassCurve

variable {R S : Type*} [CommRing R] [CommRing S]

/-- **The `y`-half of the chord recurrence for the division polynomials**, at index `m`:

```
2 · preΨ_{2(m+1)} · ΨSq_{m−1}²  =  Gₘ · (Lₘ · preΨ_{2m} − Rₘ) ,
```

with `Gₘ`, `Lₘ`, `Rₘ` the polynomials `WronskianRec.G`, `.L`, `.Rem` of
`EllipticCurves.Torsion.WronskianRecurrence`.  Packaged as a `Prop` so that it can be transported
between rings; `WeierstrassCurve.hasOmegaChord` proves it over every commutative ring at every
index, so a consumer wants that and not this.

⚠️ The identity at `−m` is **not** the identity at `m`: `preΨ` is odd in the index while `Φ` and
`ΨSq` are even, so the two are the two halves — `C1` and `C2` of `#1518` — of what
`WronskianRec.OmegaSum` and `WronskianRec.OmegaDiff` state.  That is the whole reason this file
proves one identity rather than two. -/
def HasOmegaChord (W : WeierstrassCurve R) (m : ℤ) : Prop :=
  2 * W.preΨ (2 * (m + 1)) * W.ΨSq (m - 1) ^ 2 =
    WronskianRec.G W m * (WronskianRec.L W m * W.preΨ (2 * m) - WronskianRec.Rem W m)

/-- **The identity transports along any ring homomorphism.**  Every ingredient commutes with base
change — `map_preΨ` / `map_Φ` / `map_ΨSq` and `map_b₂` / `map_b₄` / `map_b₆` in Mathlib — so
applying `Polynomial.map f` to both sides is the whole proof. -/
theorem HasOmegaChord.map {W : WeierstrassCurve R} {m : ℤ} (h : W.HasOmegaChord m) (f : R →+* S) :
    (W.map f).HasOmegaChord m := by
  have H := congrArg (Polynomial.map f) h
  simpa only [HasOmegaChord, WronskianRec.G, WronskianRec.L, WronskianRec.Rem, map_preΨ, map_Φ,
    map_ΨSq, WeierstrassCurve.map_b₂, WeierstrassCurve.map_b₄, WeierstrassCurve.map_b₆,
    Polynomial.map_mul, Polynomial.map_add, Polynomial.map_sub, Polynomial.map_pow,
    Polynomial.map_ofNat, Polynomial.map_C, Polynomial.map_X] using H

/-- **The identity descends along an injective ring homomorphism.**  `Polynomial.map f` is injective
when `f` is, so an identity that holds after base change already held before it.  This is what lets
the identity be proved over a field — where there are points, and a group law — and then pulled back
to the universal polynomial ring. -/
theorem hasOmegaChord_of_map {W : WeierstrassCurve R} {f : R →+* S} (hf : Function.Injective f)
    {m : ℤ} (h : (W.map f).HasOmegaChord m) : W.HasOmegaChord m := by
  refine Polynomial.map_injective f hf ?_
  simpa only [HasOmegaChord, WronskianRec.G, WronskianRec.L, WronskianRec.Rem, map_preΨ, map_Φ,
    map_ΨSq, WeierstrassCurve.map_b₂, WeierstrassCurve.map_b₄, WeierstrassCurve.map_b₆,
    Polynomial.map_mul, Polynomial.map_add, Polynomial.map_sub, Polynomial.map_pow,
    Polynomial.map_ofNat, Polynomial.map_C, Polynomial.map_X] using h

/-- **The reduction.**  `HasOmegaChord m` for the universal curve gives it for every Weierstrass
curve over every commutative ring, by base change along `W.specialize`. -/
theorem hasOmegaChord_of_univ {m : ℤ} (h : univ.HasOmegaChord m) (W : WeierstrassCurve R) :
    W.HasOmegaChord m := by
  have H := h.map W.specialize
  rwa [univ_map_specialize] at H

/-- **The reduction is lossless**: the universal instance is *equivalent* to the universally
quantified statement, since `univ` is itself one of the curves quantified over.  Stated at `Type`
because that is where `univ` lives; `hasOmegaChord_of_univ` is the universe-polymorphic form and is
what consumers should use. -/
theorem forall_hasOmegaChord_iff_univ {m : ℤ} :
    (∀ (R : Type) [CommRing R] (W : WeierstrassCurve R), W.HasOmegaChord m) ↔
      univ.HasOmegaChord m :=
  ⟨fun h => h _ univ, fun h _ _ W => hasOmegaChord_of_univ h W⟩

/-- **The reduction, over a characteristic-`0` base.**  `HasOmegaChord m` for `univQ` gives it for
every Weierstrass curve over every commutative ring: descend along the injective
`MvPolynomial.map (Int.castRingHom ℚ)` to `univ`, then specialise. -/
theorem hasOmegaChord_of_univQ {m : ℤ} (h : univQ.HasOmegaChord m) (W : WeierstrassCurve R) :
    W.HasOmegaChord m :=
  hasOmegaChord_of_univ (hasOmegaChord_of_map (MvPolynomial.map_injective _ Int.cast_injective) h) W

/-- **The identity at `m = 0`.**  `ΨSq₀ = 0` and `Φ₀ = 1` reduce it to `2·preΨ₂·ΨSq₋₁² = G₀·(−R₀)`
with `preΨ₂ = ΨSq₋₁ = 1`, `G₀ = −1` and `R₀ = 2`: both sides are `2`.  ⚠️ This is the index at which
the sign and the factor `G₀` of `WronskianRec.OmegaDiff` are pinned, and it is outside the reach of
the point-theoretic argument below, which needs `ΨSqₘ ≠ 0`. -/
theorem hasOmegaChord_zero (W : WeierstrassCurve R) : W.HasOmegaChord 0 := by
  rw [HasOmegaChord, WronskianRec.G, WronskianRec.L, WronskianRec.Rem,
    show 2 * ((0 : ℤ) + 1) = 2 by norm_num, show (0 : ℤ) - 1 = -1 by norm_num,
    show 2 * (0 : ℤ) = 0 by norm_num, preΨ_two, preΨ_zero, ΨSq_neg, ΨSq_one, ΨSq_zero, Φ_zero]
  ring

/-- **The identity at `m = 1`.**  Both sides vanish: on the left `ΨSq₀ = 0`, and on the right
`G₁ = X·ΨSq₁ − Φ₁ = X − X = 0`. -/
theorem hasOmegaChord_one (W : WeierstrassCurve R) : W.HasOmegaChord 1 := by
  rw [HasOmegaChord, WronskianRec.G, show (1 : ℤ) - 1 = 0 by norm_num, ΨSq_zero, ΨSq_one, Φ_one]
  ring

/-- **The identity at `m = −1`.**  Both sides vanish: on the left `preΨ₀ = 0`, and on the right
`G₋₁ = G₁ = 0` since `Φ` and `ΨSq` are even in the index. -/
theorem hasOmegaChord_neg_one (W : WeierstrassCurve R) : W.HasOmegaChord (-1) := by
  rw [HasOmegaChord, WronskianRec.G, show 2 * ((-1 : ℤ) + 1) = 0 by norm_num, preΨ_zero,
    show (-1 : ℤ) = -(1 : ℤ) from rfl, ΨSq_neg, Φ_neg, ΨSq_one, Φ_one]
  ring

namespace Affine

variable {F : Type*} [Field F] {W : Affine F} {x y : F}

/-- **The chord identity for `ψ₂`**: for two points `(x₁, y₁)`, `(x₂, y₂)` of `W` joined by a line
of slope `L` — i.e. `L·(x₁ − x₂) = y₁ − y₂`, which at `x₁ ≠ x₂` is `WeierstrassCurve.Affine.slope` —

```
2·(x₂ − x₁)³·ψ₂(P₁ + P₂)
    = ((6x₂² + b₂x₂ + b₄)x₁ + 2x₂³ + b₂x₂² + 3b₄x₂ + 2b₆)·ψ₂(P₁)
      − (2x₁³ + (6x₂ + b₂)x₁² + (b₂x₂ + 3b₄)x₁ + b₄x₂ + 2b₆)·ψ₂(P₂) ,
```

where `ψ₂(x, y) = 2y + a₁x + a₃` is `WeierstrassCurve.ψ₂` at a point.  What it says is that the
`ψ₂`-value of the chord intersection is a **bilinear** expression in the `ψ₂`-values of the two
points with coefficients depending only on the `x`-coordinates — which is why an identity between
univariate polynomials can come out of it.

⚠️ This is the `y`-analogue of the merged `WeierstrassCurve.Affine.addX_add_addX_negY`, and Mathlib
has neither.  ⚠️ The slope is a hypothesis rather than `W.slope x₁ x₂ y₁ y₂` so that the proof is a
single `linear_combination` in a polynomial ring, with no `field_simp` and no `x₁ ≠ x₂`; a caller
supplies `hL` from `slope_of_X_ne` by `div_mul_cancel₀`. -/
theorem psi2_addY {x₁ x₂ y₁ y₂ L : F} (h₁ : W.Equation x₁ y₁) (h₂ : W.Equation x₂ y₂)
    (hL : L * (x₁ - x₂) = y₁ - y₂) :
    2 * (x₂ - x₁) ^ 3 * (2 * W.addY x₁ x₂ y₁ L + W.a₁ * W.addX x₁ x₂ L + W.a₃)
      = ((6 * x₂ ^ 2 + W.b₂ * x₂ + W.b₄) * x₁ +
          (2 * x₂ ^ 3 + W.b₂ * x₂ ^ 2 + 3 * W.b₄ * x₂ + 2 * W.b₆)) * (2 * y₁ + W.a₁ * x₁ + W.a₃)
        - (2 * x₁ ^ 3 + (6 * x₂ + W.b₂) * x₁ ^ 2 + (W.b₂ * x₂ + 3 * W.b₄) * x₁ +
            (W.b₄ * x₂ + 2 * W.b₆)) * (2 * y₂ + W.a₁ * x₂ + W.a₃) := by
  rw [equation_iff] at h₁ h₂
  simp only [addY, addX, negY, negAddY, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆]
  linear_combination
    (-4 * W.a₃ - 12 * y₂ + 4 * y₁ - 6 * x₂ * W.a₁ + 2 * x₁ * W.a₁) * h₁ +
    (4 * W.a₃ - 4 * y₂ + 12 * y₁ - 2 * x₂ * W.a₁ + 6 * x₁ * W.a₁) * h₂ +
    (4 * y₂ ^ 2 - 8 * y₁ * y₂ + 4 * y₁ ^ 2 + 6 * x₂ * y₂ * W.a₁ + 4 * x₂ * y₂ * L
      - 6 * x₂ * y₁ * W.a₁ - 4 * x₂ * y₁ * L - 4 * x₂ ^ 2 * W.a₂ + 2 * x₂ ^ 2 * W.a₁ ^ 2
      + 6 * x₂ ^ 2 * L * W.a₁ + 4 * x₂ ^ 2 * L ^ 2 - 4 * x₂ ^ 3 - 6 * x₁ * y₂ * W.a₁
      - 4 * x₁ * y₂ * L + 6 * x₁ * y₁ * W.a₁ + 4 * x₁ * y₁ * L + 8 * x₁ * x₂ * W.a₂
      - 4 * x₁ * x₂ * W.a₁ ^ 2 - 12 * x₁ * x₂ * L * W.a₁ - 8 * x₁ * x₂ * L ^ 2
      - 4 * x₁ ^ 2 * W.a₂ + 2 * x₁ ^ 2 * W.a₁ ^ 2 + 6 * x₁ ^ 2 * L * W.a₁ + 4 * x₁ ^ 2 * L ^ 2
      + 12 * x₁ ^ 2 * x₂ - 8 * x₁ ^ 3) * hL

/-- **`ψ₂` at the predicted `n`-fold multiple**: with `x` the `x`-coordinate `Φₙ(x)/ΨSqₙ(x)` and
`WeierstrassCurve.Affine.omegaY` the `y`-coordinate,

```
2·ωₙ + a₁·(Φₙ/ΨSqₙ) + a₃  =  (2y + a₁x + a₃) · preΨ_{2n}(x) / ΨSqₙ(x)² .
```

The `a₁Φₙ + a₃ΨSqₙ` term of `omegaY` is exactly what the left-hand side's `a₁·(Φₙ/ΨSqₙ) + a₃`
cancels, leaving `preΩₙ/ψₙ³`; `preΨ_two_mul` (`preΨ_{2n} = preΨₙ·preΩₙ`) and `ψₙ = preΨₙ·ψ₂^{[2∣n]}`
turn that into the display.  Both parities are needed and the case split is on `Even n`. -/
theorem psi2_omegaY (h : W.Equation x y) (h2 : (2 : F) ≠ 0) {n : ℤ}
    (hΨ : (W.ΨSq n).eval x ≠ 0) :
    2 * W.omegaY x y n + W.a₁ * ((W.Φ n).eval x / (W.ΨSq n).eval x) + W.a₃
      = (2 * y + W.a₁ * x + W.a₃) * (W.preΨ (2 * n)).eval x / (W.ΨSq n).eval x ^ 2 := by
  have hψ : (W.ψ n).evalEval x y ^ 2 = (W.ΨSq n).eval x := ψ_sq_evalEval h n
  have he : (W.ψ n).evalEval x y ≠ 0 := fun hz => hΨ (by rw [← hψ, hz]; ring)
  have hev : (W.ψ n).evalEval x y
      = (W.preΨ n).eval x * (if Even n then 2 * y + W.a₁ * x + W.a₃ else 1) := by
    rw [ψ_evalEval h, WeierstrassCurve.Ψ]
    have h2' : (W.ψ₂).evalEval x y = 2 * y + W.a₁ * x + W.a₃ := by rw [← ψ_two, ψ_two_evalEval]
    split_ifs with hn <;> simp [h2', evalEval]
  have hΩ : W.preΨ (2 * n) = W.preΨ n * W.preΩ n := W.preΨ_two_mul n
  rw [omegaY, hΩ, ← hψ]
  split_ifs with hn
  · have hf : (W.preΨ n).eval x ≠ 0 := fun hz => he (by rw [hev, hz]; ring)
    have ht : 2 * y + W.a₁ * x + W.a₃ ≠ 0 := fun hz => he (by rw [hev, if_pos hn, hz]; ring)
    rw [if_pos hn] at hev
    field_simp
    simp only [eval_mul]
    rw [hev]
    ring
  · rw [if_neg hn, mul_one] at hev
    field_simp
    simp only [eval_mul]
    rw [hev]
    ring

/-- **Clearing the denominators.**  Stated at abstract field elements — `S = ΨSqₘ(x)`,
`Φ = Φₘ(x)`, `A = ΨSq_{m+1}(x)`, `B = ΨSq_{m−1}(x)`, `G = Gₘ(x)`, `p2 = preΨ_{2(m+1)}(x)`,
`p0 = preΨ_{2m}(x)`, `t = ψ₂(P)` — so that no index arithmetic happens inside.

⚠️ `hG2` is `S0`, `Gₘ² = ΨSq_{m+1}·ΨSq_{m−1}`.  It is used twice: once through `field_simp`, which
turns the chord identity into `2G³·p2 = A²·(L·p0 − R)`, and once to replace `A²B²` by `G⁴`, which is
what makes the two sides agree after multiplying by `A²`. -/
private theorem omegaChord_clear {t S Φ A B G p2 p0 b2 b4 b6 : F}
    (ht : t ≠ 0) (hS : S ≠ 0) (hA : A ≠ 0) (hG : G = x * S - Φ) (hG2 : G ^ 2 = A * B)
    (hchord : 2 * (x - Φ / S) ^ 3 * (t * p2 / A ^ 2)
        = ((6 * x ^ 2 + b2 * x + b4) * (Φ / S) + (2 * x ^ 3 + b2 * x ^ 2 + 3 * b4 * x + 2 * b6))
            * (t * p0 / S ^ 2)
          - (2 * (Φ / S) ^ 3 + (6 * x + b2) * (Φ / S) ^ 2 + (b2 * x + 3 * b4) * (Φ / S)
              + (b4 * x + 2 * b6)) * t) :
    2 * p2 * B ^ 2 = G * (((6 * x ^ 2 + b2 * x + b4) * Φ
        + (2 * x ^ 3 + b2 * x ^ 2 + 3 * b4 * x + 2 * b6) * S) * p0
      - (2 * Φ ^ 3 + (6 * x + b2) * Φ ^ 2 * S + (b2 * x + 3 * b4) * Φ * S ^ 2
          + (b4 * x + 2 * b6) * S ^ 3)) := by
  field_simp at hchord
  rw [← hG] at hchord
  refine mul_left_cancel₀ (pow_ne_zero 2 hA) ?_
  linear_combination G * hchord - (2 * p2 * (A * B + G ^ 2)) * hG2

section DecidableEqField

variable [DecidableEq F]

/-- **The coordinates of `n • P` at every `n : ℤ`, with `ψ₂` in division-polynomial form.**

The merged `WeierstrassCurve.Affine.nsmul_eq_some_omegaY_of_ΨSq_ne_zero` is stated at `n : ℕ`; this
extends it to `ℤ` and bundles `WeierstrassCurve.Affine.psi2_omegaY` with it, which is the exact
package the chord argument consumes.  ⚠️ The extension is free: `(−n) • P = −(n • P)` leaves the
`x`-coordinate alone (`Φ_neg`, `ΨSq_neg`) and negates `ψ₂`, and `preΨ` is odd in the index
(`preΨ_neg`), so both sides of the `ψ₂`-formula negate together. -/
theorem exists_zsmul_eq_some_psi2 (h2 : (2 : F) ≠ 0) (hns : W.Nonsingular x y) {n : ℤ}
    (hΨ : (W.ΨSq n).eval x ≠ 0) :
    ∃ (yv : F) (h' : W.Nonsingular ((W.Φ n).eval x / (W.ΨSq n).eval x) yv),
      (n • Point.some x y hns : W.Point)
          = .some ((W.Φ n).eval x / (W.ΨSq n).eval x) yv h' ∧
        2 * yv + W.a₁ * ((W.Φ n).eval x / (W.ΨSq n).eval x) + W.a₃
          = (2 * y + W.a₁ * x + W.a₃) * (W.preΨ (2 * n)).eval x / (W.ΨSq n).eval x ^ 2 := by
  classical
  rcases le_or_gt 0 n with hn | hn
  · lift n to ℕ using hn
    obtain ⟨h', heq⟩ := nsmul_eq_some_omegaY_of_ΨSq_ne_zero (W := W) h2 hns hΨ
    exact ⟨_, h', by rw [← heq, natCast_zsmul], psi2_omegaY hns.left h2 hΨ⟩
  · obtain ⟨j, rfl⟩ : ∃ j : ℕ, n = -(j : ℤ) := ⟨(-n).toNat, by omega⟩
    have hΨj : (W.ΨSq (j : ℤ)).eval x ≠ 0 := by rwa [ΨSq_neg] at hΨ
    obtain ⟨h', heq⟩ := nsmul_eq_some_omegaY_of_ΨSq_ne_zero (W := W) h2 hns hΨj
    have hpre : (W.preΨ (2 * -(j : ℤ))).eval x = -(W.preΨ (2 * (j : ℤ))).eval x := by
      rw [show 2 * -(j : ℤ) = -(2 * (j : ℤ)) by ring, preΨ_neg, eval_neg]
    simp only [Φ_neg, ΨSq_neg]
    refine ⟨W.negY ((W.Φ (j : ℤ)).eval x / (W.ΨSq (j : ℤ)).eval x) (W.omegaY x y (j : ℤ)),
      (nonsingular_neg ..).mpr h', ?_, ?_⟩
    · rw [neg_zsmul, natCast_zsmul, heq, Point.neg_some]
    · have hp := psi2_omegaY (W := W) hns.left h2 hΨj
      rw [negY, hpre]
      linear_combination -hp

end DecidableEqField

variable [IsAlgClosed F] [W.IsElliptic]

/-- **The identity evaluated at a good `x`.**  `P := (x, y)` is a point above `x`, `Q := m • P`,
and `Q + P = (m + 1) • P`; `psi2_addY` relates the `ψ₂`-values of the three, `psi2_omegaY` turns
each into a division-polynomial ratio, and `omegaChord_clear` clears the denominators.

⚠️ `Ψ₂Sq(x) ≠ 0` is `ψ₂(P) ≠ 0`, and it is a genuine hypothesis: every term of the chord identity
carries a factor `ψ₂(P)`, and it is divided out. -/
private theorem omegaChord_eval (h2 : (2 : F) ≠ 0) (m : ℤ) {x : F}
    (h0 : (W.ΨSq (m - 1)).eval x ≠ 0) (hS : (W.ΨSq m).eval x ≠ 0)
    (hA : (W.ΨSq (m + 1)).eval x ≠ 0) (htt : W.Ψ₂Sq.eval x ≠ 0) :
    2 * (W.preΨ (2 * (m + 1))).eval x * (W.ΨSq (m - 1)).eval x ^ 2
      = (x * (W.ΨSq m).eval x - (W.Φ m).eval x) *
        (((6 * x ^ 2 + W.b₂ * x + W.b₄) * (W.Φ m).eval x
            + (2 * x ^ 3 + W.b₂ * x ^ 2 + 3 * W.b₄ * x + 2 * W.b₆) * (W.ΨSq m).eval x)
              * (W.preΨ (2 * m)).eval x
          - (2 * (W.Φ m).eval x ^ 3 + (6 * x + W.b₂) * (W.Φ m).eval x ^ 2 * (W.ΨSq m).eval x
            + (W.b₂ * x + 3 * W.b₄) * (W.Φ m).eval x * (W.ΨSq m).eval x ^ 2
            + (W.b₄ * x + 2 * W.b₆) * (W.ΨSq m).eval x ^ 3)) := by
  classical
  obtain ⟨y, hy⟩ := exists_equation (W := W) h2 x
  have hns : W.Nonsingular x y := (equation_iff_nonsingular ..).mp hy
  have ht : 2 * y + W.a₁ * x + W.a₃ ≠ 0 := by
    intro hz
    refine htt ?_
    have hsq : (W.ψ 2).evalEval x y ^ 2 = (W.ΨSq 2).eval x := ψ_sq_evalEval hy 2
    rw [ψ_two_evalEval, hz, ΨSq_two] at hsq
    rw [← hsq]; ring
  have hG2 : (x * (W.ΨSq m).eval x - (W.Φ m).eval x) ^ 2
      = (W.ΨSq (m + 1)).eval x * (W.ΨSq (m - 1)).eval x := by
    have hpoly : W.ΨSq (m + 1) * W.ΨSq (m - 1) = (X * W.ΨSq m - W.Φ m) ^ 2 := by
      rw [ΨSq_succ_mul_ΨSq_pred, Φ_eq_neg_adjacent_add]
      ring
    have H := congrArg (Polynomial.eval x) hpoly
    simpa only [eval_mul, eval_sub, eval_pow, eval_X] using H.symm
  have hGne : x * (W.ΨSq m).eval x - (W.Φ m).eval x ≠ 0 := by
    intro hz
    rw [hz] at hG2
    exact mul_ne_zero hA h0 (by linear_combination -hG2)
  obtain ⟨v, hnsm, hQ, hpv⟩ := exists_zsmul_eq_some_psi2 (W := W) h2 hns hS
  obtain ⟨w, hnsa, hAeq, hpw⟩ := exists_zsmul_eq_some_psi2 (W := W) h2 hns hA
  have hux : (W.Φ m).eval x / (W.ΨSq m).eval x ≠ x := by
    intro hz
    rw [div_eq_iff hS] at hz
    exact hGne (by rw [hz]; ring)
  have hstep : m • Point.some x y hns + Point.some x y hns
      = (m + 1) • Point.some x y hns := by
    rw [add_zsmul, one_zsmul]
  have hsum : Point.some ((W.Φ m).eval x / (W.ΨSq m).eval x) v hnsm + Point.some x y hns
      = Point.some (W.addX ((W.Φ m).eval x / (W.ΨSq m).eval x) x
          (W.slope ((W.Φ m).eval x / (W.ΨSq m).eval x) x v y)) _
        (nonsingular_add hnsm hns fun hxy => hux hxy.left) := Point.add_of_X_ne hux
  rw [hQ, hAeq, hsum] at hstep
  simp only [Point.some.injEq] at hstep
  have hL : W.slope ((W.Φ m).eval x / (W.ΨSq m).eval x) x v y
      * ((W.Φ m).eval x / (W.ΨSq m).eval x - x) = v - y := by
    rw [slope_of_X_ne hux]
    exact div_mul_cancel₀ _ (sub_ne_zero.mpr hux)
  have hchord := psi2_addY hnsm.left hy hL
  rw [hstep.1, hstep.2, hpw, hpv] at hchord
  exact omegaChord_clear ht hS hA rfl hG2 hchord

/-- **The identity over an algebraically closed field of characteristic `0`**, at every index other
than `0` and `±1`.  Multiplying by `ΨSq_{m−1}·ΨSqₘ·ΨSq_{m+1}·Ψ₂Sq` makes both sides vanish wherever
any of those four does, so `omegaChord_eval` plus `Polynomial.funext` proves the product identity,
and the four factors are nonzero polynomials — the `ΨSq` by `ΨSq_ne_zero`, which is what needs
`m − 1`, `m`, `m + 1` all nonzero in characteristic `0`. -/
theorem hasOmegaChord_of_isAlgClosed [CharZero F] {m : ℤ} (h0 : m - 1 ≠ 0) (hm : m ≠ 0)
    (h1 : m + 1 ≠ 0) : W.HasOmegaChord m := by
  classical
  have h2 : (2 : F) ≠ 0 := two_ne_zero
  have n0 : W.ΨSq (m - 1) ≠ 0 := W.ΨSq_ne_zero (Int.cast_ne_zero.mpr h0)
  have n1 : W.ΨSq m ≠ 0 := W.ΨSq_ne_zero (Int.cast_ne_zero.mpr hm)
  have n2 : W.ΨSq (m + 1) ≠ 0 := W.ΨSq_ne_zero (Int.cast_ne_zero.mpr h1)
  have nt : W.Ψ₂Sq ≠ 0 := by
    have h := W.ΨSq_ne_zero (n := 2) (by norm_num)
    rwa [ΨSq_two] at h
  rw [HasOmegaChord, WronskianRec.G, WronskianRec.L, WronskianRec.Rem]
  refine mul_left_cancel₀ (a := W.ΨSq (m - 1) * W.ΨSq m * W.ΨSq (m + 1) * W.Ψ₂Sq)
    (mul_ne_zero (mul_ne_zero (mul_ne_zero n0 n1) n2) nt) ?_
  refine Polynomial.funext fun x => ?_
  simp only [eval_mul, eval_add, eval_sub, eval_pow, eval_X, eval_C, eval_ofNat]
  by_cases c0 : (W.ΨSq (m - 1)).eval x = 0
  · rw [c0]; ring
  by_cases c1 : (W.ΨSq m).eval x = 0
  · rw [c1]; ring
  by_cases c2 : (W.ΨSq (m + 1)).eval x = 0
  · rw [c2]; ring
  by_cases ct : W.Ψ₂Sq.eval x = 0
  · rw [ct]; ring
  linear_combination ((W.ΨSq (m - 1)).eval x * (W.ΨSq m).eval x * (W.ΨSq (m + 1)).eval x
    * W.Ψ₂Sq.eval x) * omegaChord_eval h2 m c0 c1 c2 ct

end Affine

/-- **The `y`-half of the chord recurrence, for every Weierstrass curve over every commutative ring,
at every `m : ℤ`**, with no hypotheses:

```
2 · preΨ_{2(m+1)} · ΨSq_{m−1}²  =  Gₘ · (Lₘ · preΨ_{2m} − Rₘ) .
```

`hasOmegaChord_of_univQ` reduces this to the single curve `univQ`; base changing along the injection
of `MvPolynomial (Fin 5) ℚ` into `AlgebraicClosure (FractionRing (MvPolynomial (Fin 5) ℚ))` makes it
an elliptic curve over an algebraically closed field of characteristic `0`
(`univQ_Δ_ne_zero`), where
`Affine.hasOmegaChord_of_isAlgClosed` applies away from `m = 0, ±1`, and `hasOmegaChord_of_map`
brings it back.  The three exceptional indices are `hasOmegaChord_zero`, `hasOmegaChord_one` and
`hasOmegaChord_neg_one`, and they hold over every commutative ring already.

⚠️ Characteristic `2` and singular curves are covered by the conclusion even though the proof runs
nowhere near them — the same trade `WeierstrassCurve.hasChordSum` and `WeierstrassCurve.hasPreΩSq`
make. -/
theorem hasOmegaChord (W : WeierstrassCurve R) (m : ℤ) : W.HasOmegaChord m := by
  classical
  rcases eq_or_ne m 0 with rfl | hm0
  · exact hasOmegaChord_zero W
  rcases eq_or_ne m 1 with rfl | hm1
  · exact hasOmegaChord_one W
  rcases eq_or_ne m (-1) with rfl | hmm1
  · exact hasOmegaChord_neg_one W
  refine hasOmegaChord_of_univQ ?_ W
  set B := MvPolynomial (Fin 5) ℚ with hB
  set K := AlgebraicClosure (FractionRing B) with hK
  set f : B →+* K := (algebraMap (FractionRing B) K).comp (algebraMap B (FractionRing B)) with hf
  have hfinj : Function.Injective f :=
    (algebraMap (FractionRing B) K).injective.comp (IsFractionRing.injective B (FractionRing B))
  refine hasOmegaChord_of_map (f := f) hfinj ?_
  haveI : (univQ.map f).IsElliptic := by
    refine ⟨?_⟩
    rw [map_Δ]
    exact isUnit_iff_ne_zero.mpr fun h => univQ_Δ_ne_zero ((map_eq_zero_iff f hfinj).mp h)
  exact Affine.hasOmegaChord_of_isAlgClosed (sub_ne_zero.mpr hm1) hm0 (fun h => hmm1 (by omega))

/-! ### `C1` and `C2`, the two open hypotheses of `#1518` -/

/-- **The pair `C1 ∧ C2`** — `WronskianRec.OmegaSum` and `WronskianRec.OmegaDiff` — bundled so that
the universal descent is run once rather than twice.  The bundling is the only reason this exists;
`WeierstrassCurve.omegaSum` and `WeierstrassCurve.omegaDiff` are the projections a consumer
wants. -/
def HasOmegaPair (W : WeierstrassCurve R) (m : ℤ) : Prop :=
  WronskianRec.OmegaSum W m ∧ WronskianRec.OmegaDiff W m

/-- **The pair transports along any ring homomorphism**, componentwise and for the same reason
`HasOmegaChord.map` does. -/
theorem HasOmegaPair.map {W : WeierstrassCurve R} {m : ℤ} (h : W.HasOmegaPair m) (f : R →+* S) :
    (W.map f).HasOmegaPair m := by
  obtain ⟨h1, h2⟩ := h
  constructor
  · have H := congrArg (Polynomial.map f) h1
    simpa only [WronskianRec.OmegaSum, WronskianRec.G, WronskianRec.L, map_preΨ, map_Φ, map_ΨSq,
      WeierstrassCurve.map_b₂, WeierstrassCurve.map_b₄, WeierstrassCurve.map_b₆,
      Polynomial.map_mul, Polynomial.map_add, Polynomial.map_sub, Polynomial.map_pow,
      Polynomial.map_ofNat, Polynomial.map_C, Polynomial.map_X] using H
  · have H := congrArg (Polynomial.map f) h2
    simpa only [WronskianRec.OmegaDiff, WronskianRec.G, WronskianRec.Rem, map_preΨ, map_Φ, map_ΨSq,
      WeierstrassCurve.map_b₂, WeierstrassCurve.map_b₄, WeierstrassCurve.map_b₆,
      Polynomial.map_mul, Polynomial.map_add, Polynomial.map_sub, Polynomial.map_neg,
      Polynomial.map_pow, Polynomial.map_ofNat, Polynomial.map_C, Polynomial.map_X] using H

/-- **The pair descends along an injective ring homomorphism**, componentwise. -/
theorem hasOmegaPair_of_map {W : WeierstrassCurve R} {f : R →+* S} (hf : Function.Injective f)
    {m : ℤ} (h : (W.map f).HasOmegaPair m) : W.HasOmegaPair m := by
  obtain ⟨h1, h2⟩ := h
  constructor
  · refine Polynomial.map_injective f hf ?_
    simpa only [WronskianRec.OmegaSum, WronskianRec.G, WronskianRec.L, map_preΨ, map_Φ, map_ΨSq,
      WeierstrassCurve.map_b₂, WeierstrassCurve.map_b₄, WeierstrassCurve.map_b₆,
      Polynomial.map_mul, Polynomial.map_add, Polynomial.map_sub, Polynomial.map_pow,
      Polynomial.map_ofNat, Polynomial.map_C, Polynomial.map_X] using h1
  · refine Polynomial.map_injective f hf ?_
    simpa only [WronskianRec.OmegaDiff, WronskianRec.G, WronskianRec.Rem, map_preΨ, map_Φ, map_ΨSq,
      WeierstrassCurve.map_b₂, WeierstrassCurve.map_b₄, WeierstrassCurve.map_b₆,
      Polynomial.map_mul, Polynomial.map_add, Polynomial.map_sub, Polynomial.map_neg,
      Polynomial.map_pow, Polynomial.map_ofNat, Polynomial.map_C, Polynomial.map_X] using h2

/-- **The reduction to the universal curve**, by base change along `W.specialize`. -/
theorem hasOmegaPair_of_univ {m : ℤ} (h : univ.HasOmegaPair m) (W : WeierstrassCurve R) :
    W.HasOmegaPair m := by
  have H := h.map W.specialize
  rwa [univ_map_specialize] at H

/-- **The reduction over a characteristic-`0` base.**  ⚠️ This is where the whole construction pays
for the factor `2`: the pair is deduced from `hasOmegaChord` at `m` and at `−m` by cancelling `2`,
which is legitimate over `univQ` and nowhere else, and this descent is what carries the result to an
arbitrary commutative ring — including one of characteristic `2`. -/
theorem hasOmegaPair_of_univQ {m : ℤ} (h : univQ.HasOmegaPair m) (W : WeierstrassCurve R) :
    W.HasOmegaPair m :=
  hasOmegaPair_of_univ (hasOmegaPair_of_map (MvPolynomial.map_injective _ Int.cast_injective) h) W

/-- **The `m`/`−m` combination.**  `Φ` and `ΨSq` are even in the index and `preΨ` is odd, so
`hasOmegaChord` at `−m` reads `2·preΨ_{2(m−1)}·ΨSqₘ₊₁² = Gₘ·(Lₘ·preΨ₂ₘ + Rₘ)`; the sum of the two
instances is `2·C1` and the difference is `2·C2`.  Over a characteristic-`0` domain `2` cancels in
`R[X]`, which is all this needs. -/
private theorem hasOmegaPair_of_charZero [IsDomain R] [CharZero R] (W : WeierstrassCurve R)
    (m : ℤ) : W.HasOmegaPair m := by
  have h2 : (2 : R[X]) ≠ 0 := fun h =>
    (two_ne_zero (α := R)) (by simpa using congrArg (fun p => Polynomial.coeff p 0) h)
  have hm := W.hasOmegaChord m
  have hn := W.hasOmegaChord (-m)
  have hG : WronskianRec.G W (-m) = WronskianRec.G W m := by
    simp only [WronskianRec.G, ΨSq_neg, Φ_neg]
  have hL : WronskianRec.L W (-m) = WronskianRec.L W m := by
    simp only [WronskianRec.L, ΨSq_neg, Φ_neg]
  have hR : WronskianRec.Rem W (-m) = WronskianRec.Rem W m := by
    simp only [WronskianRec.Rem, ΨSq_neg, Φ_neg]
  rw [HasOmegaChord, hG, hL, hR, show 2 * (-m + 1) = -(2 * (m - 1)) by ring,
    show -m - 1 = -(m + 1) by ring, show 2 * -m = -(2 * m) by ring, preΨ_neg, preΨ_neg,
    ΨSq_neg] at hn
  rw [HasOmegaChord] at hm
  refine ⟨?_, ?_⟩
  · rw [WronskianRec.OmegaSum]
    refine mul_left_cancel₀ h2 ?_
    linear_combination hm - hn
  · rw [WronskianRec.OmegaDiff]
    refine mul_left_cancel₀ h2 ?_
    linear_combination hm + hn

/-- **`C1` and `C2` together, for every curve over every commutative ring at every index.** -/
theorem hasOmegaPair (W : WeierstrassCurve R) (m : ℤ) : W.HasOmegaPair m :=
  hasOmegaPair_of_univQ (hasOmegaPair_of_charZero univQ m) W

/-- **`C1`**, `WronskianRec.OmegaSum`, unconditionally:
`preΨ_{2(m+1)}·ΨSq_{m−1}² + preΨ_{2(m−1)}·ΨSq_{m+1}² = Gₘ·Lₘ·preΨ_{2m}`.  This is one of the two
hypotheses `WeierstrassCurve.hasWronskianId_of_univQ_recurrence` was left carrying. -/
theorem omegaSum (W : WeierstrassCurve R) (m : ℤ) : WronskianRec.OmegaSum W m :=
  (W.hasOmegaPair m).1

/-- **`C2`**, `WronskianRec.OmegaDiff`, unconditionally:
`preΨ_{2(m+1)}·ΨSq_{m−1}² − preΨ_{2(m−1)}·ΨSq_{m+1}² = −Gₘ·Rₘ`.  The other hypothesis. -/
theorem omegaDiff (W : WeierstrassCurve R) (m : ℤ) : WronskianRec.OmegaDiff W m :=
  (W.hasOmegaPair m).2

/-! ### `#1506` item 1 -/

/-- **The Wronskian identity, unconditionally**:

```
Φₙ′ · ΨSqₙ  −  Φₙ · ΨSqₙ′  =  n · preΨₙ · preΩₙ            in R[X],
```

for every Weierstrass curve over every commutative ring at every `n : ℤ`.  This is `#1506` scope
item 1, and it is `WeierstrassCurve.hasWronskianId_of_univQ_recurrence` with all three of its
hypotheses discharged — `WronskianRec.ChordSum` by the merged `WeierstrassCurve.hasChordSum`, and
`WronskianRec.OmegaSum` / `WronskianRec.OmegaDiff` by `omegaSum` / `omegaDiff` above.

⚠️ The two `Prop`s `WeierstrassCurve.HasChordSum` and `WronskianRec.ChordSum` have the same body;
they exist separately because `EllipticCurves.Torsion.ChordSum` and
`EllipticCurves.Torsion.WronskianRecurrence` were written in parallel.  They are interchangeable by
definitional unfolding, which is why `univQ.hasChordSum` typechecks in the first argument. -/
theorem hasWronskianId (W : WeierstrassCurve R) (n : ℤ) : W.HasWronskianId n :=
  W.hasWronskianId_of_univQ_recurrence (fun m => univQ.hasChordSum m) (fun m => univQ.omegaSum m)
    (fun m => univQ.omegaDiff m) n

end WeierstrassCurve

/-! ### The payoff -/

namespace WeierstrassCurve.Affine

variable {F : Type*} [Field F] {W : Affine F}

/-- **`#E[n] = n²` at odd `n`**, for an elliptic curve over an algebraically closed field, with no
hypothesis beyond `2 ≠ 0` and `(n : F) ≠ 0`.

This is `WeierstrassCurve.Affine.card_torsion_eq_sq_of_recurrence` with its three hypotheses
supplied: the whole chain is `hasChordSum` (`#1516`), `wronskian_recurrence` (`#1518`), `omegaSum`
and `omegaDiff` (this file), the merged `hpair` of `EllipticCurves.Torsion.OmegaPairCoprime`, and
`EllipticCurves.Torsion.OddTorsionCount`'s reduction of the count to `Separable (preΨₙ)`.

⚠️ It is stated at **odd** `n` because that is the régime
`WeierstrassCurve.Affine.card_torsion_eq_sq_of_wronskian_identity` covers; nothing here says
anything at even `n`.  ⚠️ `EllipticCurves.Torsion.PrimaryTower`'s gate list, `#1490` item 3 and
`#293` are **not** updated by this file even though they are now dischargeable. -/
theorem card_torsion_eq_sq_of_odd [DecidableEq F] [IsAlgClosed F] [W.IsElliptic]
    (h2 : (2 : F) ≠ 0) {n : ℕ} (hodd : Odd n) (hn : (n : F) ≠ 0) :
    Nat.card (W.torsion n) = n ^ 2 :=
  card_torsion_eq_sq_of_recurrence h2 hodd hn (fun m => univQ.hasChordSum m)
    (fun m => univQ.omegaSum m) (fun m => univQ.omegaDiff m)

end WeierstrassCurve.Affine
