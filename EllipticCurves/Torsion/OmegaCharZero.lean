/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import EllipticCurves.Torsion.OmegaUniversal
import Mathlib.Algebra.CharP.Algebra
import Mathlib.Algebra.CharZero.Infinite
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-!
# `HasPreΩSq` reduces to its EVALUATED form over an ALGEBRAICALLY CLOSED characteristic-`0` field

`EllipticCurves.Torsion.OmegaUniversal` reduces the univariate identity
`WeierstrassCurve.HasPreΩSq n`, quantified over every commutative ring and every curve, to the
single instance at `WeierstrassCurve.univQ` over `MvPolynomial (Fin 5) ℚ`.  This file takes the
reduction one step further, in the direction that matters for actually proving it.

`EllipticCurves.Torsion.OmegaOnCurve` carries **two** forms of the identity: the polynomial
`HasPreΩSq n`, an equation in `R[X]`, and the evaluated `HasPreΩSqAt n x`, the same equation at one
`x : R`.  The polynomial form implies the evaluated one at every point (`HasPreΩSq.at`); at a
single `x` there is no way back.  Over an **infinite integral domain** there is:
two polynomials agreeing at every point of such a ring are equal (`Polynomial.funext`).  Composed
with the universal reduction, that gives

**`HasPreΩSq n` for every curve over every commutative ring, from the EVALUATED identity at every
point of every characteristic-`0` field** — and, one embedding further, from the evaluated identity
over every **algebraically closed** such field.

## Why that is the useful direction

The two forms are not equally expensive, and `OmegaOnCurve`'s module docstring already measured the
gap at `n = 3`.  The polynomial identity there is true over `ℤ`, but `4b₈ = b₂b₆ − b₄²` is not a
legal substitution over an arbitrary ring, so `ring1` must run with the `aᵢ` as atoms — **9903
monomials in six atoms**, which closed only outside the build and was killed by `lake build` with
exit `137`, out of memory.  With `2` invertible, `b₈` is eliminated by division by `4` and the same
identity has **545 monomials** and closes in seconds.  That is exactly what
`WeierstrassCurve.Affine.hasPreΩSqAt_three` does, and it is why that lemma is stated over a field
of characteristic `≠ 2` and in the evaluated form only.

So the characteristic hypothesis was never a restriction on the *statement*; it was a restriction
on the *proof*, and the universal reduction removes it.  `hasPreΩSq_three` below is the first
cash-out: the polynomial identity at `n = 3`, over **every** commutative ring, including where
`2 = 0`, with no new algebra at all.

## Main results

* `WeierstrassCurve.hasPreΩSq_of_forall_hasPreΩSqAt` : over an infinite integral domain, the
  evaluated identity at every point gives the polynomial identity.
* `WeierstrassCurve.hasPreΩSq_of_forall_charZero` : if the polynomial identity holds for every
  curve over every characteristic-`0` field, it holds for every curve over every commutative ring.
* `WeierstrassCurve.hasPreΩSq_of_forall_hasPreΩSqAt_charZero` : the two composed.
* `WeierstrassCurve.hasPreΩSq_of_forall_algClosed` and
  `WeierstrassCurve.hasPreΩSq_of_forall_hasPreΩSqAt_algClosed` : the same with the base
  additionally **algebraically closed**, by descending along `F → AlgebraicClosure F`.
* `WeierstrassCurve.hasPreΩSq_of_forall_hasΨSqDoubling_algClosed` : **the form in which `#404`'s
  crux was attacked and closed** — the `preΩ`-free identity `HasΨSqDoubling` of
  `EllipticCurves.Torsion.OmegaOnCurve`, over every curve over every algebraically closed field of
  characteristic `0`.  `EllipticCurves.Torsion.OmegaCrux` discharges its hypothesis.
* `WeierstrassCurve.hasPreΩSq_three` : `HasPreΩSq 3`, for every curve over every commutative ring.

## ⚠️ What this settles and what it does not

**This file does not close `#404`; it re-poses it, and the re-posing is what closed it.**  The crux
is `HasPreΩSq` at *general* `n`.  This file closes `n = 3` and re-poses the general question in a
strictly weaker form: it is enough to prove the **evaluated** identity at every point of an
**algebraically closed** characteristic-`0` field, where `2`, `3` and `4` are units, the
545-monomial route is legal, and `Ψ₂Sq` splits.
`hasPreΩSq_of_forall_hasΨSqDoubling_algClosed` is the strongest such statement here and is the
durable content; `hasPreΩSq_three` is one instance of it, and
`EllipticCurves.Torsion.OmegaCrux`'s `WeierstrassCurve.hasPreΩSq` is the general one.

⚠️ **What the closing proof actually used of the algebraically closed base was only that every `x`
is the abscissa of a point** (`WeierstrassCurve.Affine.exists_equation`) — *not* the splitting of
`Ψ₂Sq` that the bullet below nominates.  The `2`-torsion factorisation is a route that was
available and was not the one taken.

⚠️ **Every hypothesis these reductions drop is a hypothesis on the *base*, never on the
*conclusion*.**  All five conclude `W.HasPreΩSq n` for an arbitrary `W` over an arbitrary
`CommRing`, and they differ only in what a prover is allowed to assume while discharging the
hypothesis.  A reduction is worth nothing if its hypothesis is unsatisfiable, which is what the
certificates at the end of this file are for: `hasPreΩSq_three_algClosed` re-derives `n = 3`
through the algebraically closed route and `hasPreΩSq_three_roundTrip` through `HasΨSqDoubling` and
back.

⚠️ **This is not the circular route, and the distinction is easy to lose.**
`EllipticCurves.Torsion.OmegaUniversal`'s docstring warns that a generic-point argument is where
the entanglement with `#251` lives, because the classical proof identifies `(Φₙ/ΨSqₙ, ωₙ/ψₙ³)` with
the group-law multiple `n • P`.  That warning is about how one *proves* the evaluated identity at a
new index.  It does not touch the *upgrade* from evaluated to polynomial, which is what this file
is: base change and `Polynomial.funext`, with **no group law, no `n • P` and no `#251` input**.
Read literally the warning would say this route is blocked; it is not.

## References

* [J. Silverman, *The arithmetic of elliptic curves*][silverman2009], Exercise 3.7, III.6.
-/

open Polynomial

namespace WeierstrassCurve

variable {R : Type*} [CommRing R]

/-! ### From the evaluated identity to the polynomial one -/

/-- **The converse of `HasPreΩSq.at`, over an infinite integral domain.**  The two sides of
`HasPreΩSq n` are polynomials in `R[X]`; if they agree at every `x : R` and `R` is an infinite
domain, they are equal.  ⚠️ Infiniteness is essential and is not a technicality — over a finite
ring the evaluated identity at every point says nothing about the polynomials.

⚠️ It lives here rather than beside `HasPreΩSq.at` in `EllipticCurves.Torsion.OmegaOnCurve`, even
though it elaborates against that file alone, because it is the first half of this file's
reduction and is used only by `hasPreΩSq_of_forall_hasPreΩSqAt_charZero` below.  **That is
settled; do not move it.** -/
theorem hasPreΩSq_of_forall_hasPreΩSqAt [IsDomain R] [Infinite R] {W : WeierstrassCurve R} {n : ℤ}
    (h : ∀ x : R, W.HasPreΩSqAt n x) : W.HasPreΩSq n := by
  rw [HasPreΩSq]
  refine Polynomial.funext fun x => ?_
  have hx := h x
  rw [HasPreΩSqAt] at hx
  simpa only [eval_mul, eval_pow, eval_add, eval_ofNat, eval_C, apply_ite (Polynomial.eval x),
    eval_one] using hx

/-! ### The reduction to characteristic `0` -/

/-- The universal base of `WeierstrassCurve.univQ`. -/
private abbrev UnivBase : Type := MvPolynomial (Fin 5) ℚ

/-- Its fraction field: a characteristic-`0` field, hence an infinite domain, into which the
universal base injects.  It is `private` because no consumer should ever need to name it — the
reduction below quantifies over all characteristic-`0` fields.

⚠️ **`CharZero UnivFrac` is found by instance search and must not be supplied by hand.**  Mathlib's
`IsFractionRing.charZero` is an instance and covers it; a `private instance` here proving the same
thing by `charZero_of_injective_algebraMap` is dead weight.  ⚠️ That instance lives in the closure
of `Mathlib.Algebra.CharP.Algebra`, which is why that import stays even though **no identifier from
it appears in this file** — an import-pruner going by identifiers alone will delete it, and the
file then fails at `hasPreΩSq_of_forall_charZero` with `failed to synthesize CharZero UnivFrac`. -/
private abbrev UnivFrac : Type := FractionRing UnivBase

/-- **`HasPreΩSq n` over every characteristic-`0` field gives it over every commutative ring.**
Instantiate the hypothesis at the fraction field of `MvPolynomial (Fin 5) ℚ`, descend along the
injection to `univQ`, then specialise with `hasPreΩSq_of_univQ`.

The hypothesis is stated at `Type` because that is where `univQ` and its fraction field live; the
conclusion is universe-polymorphic. -/
theorem hasPreΩSq_of_forall_charZero {n : ℤ}
    (h : ∀ (F : Type) [Field F] [CharZero F] (V : WeierstrassCurve F), V.HasPreΩSq n)
    (W : WeierstrassCurve R) : W.HasPreΩSq n :=
  hasPreΩSq_of_univQ
    (hasPreΩSq_of_map (f := algebraMap UnivBase UnivFrac)
      (IsFractionRing.injective UnivBase UnivFrac) (h UnivFrac _)) W

/-- **`hasPreΩSq_of_forall_charZero` and `hasPreΩSq_of_forall_hasPreΩSqAt`, composed.**  To prove
the polynomial identity `HasPreΩSq n` for every Weierstrass curve over every commutative ring it is
enough to prove the **evaluated** identity `HasPreΩSqAt n x` at every point of every
characteristic-`0` field — where `2`, `3` and `4` are units, `b₈ = (b₂b₆ − b₄²)/4` is a legal
substitution, and `field_simp` is available.  See the module docstring for the measured size of the
difference.  This is the route `hasPreΩSq_three` below takes.

⚠️ **`#404`'s crux was not attacked here, although this docstring nominated it until `#1402`.**
The designation was `hasPreΩSq_of_forall_hasΨSqDoubling_algClosed`'s: its base is additionally
algebraically closed, so `Ψ₂Sq` splits, and its hypothesis is stated with no `preΩ` in it at all.
That is the lemma `EllipticCurves.Torsion.OmegaCrux` discharged, so the designation was correct and
is now spent. -/
theorem hasPreΩSq_of_forall_hasPreΩSqAt_charZero {n : ℤ}
    (h : ∀ (F : Type) [Field F] [CharZero F] (V : WeierstrassCurve F) (x : F),
      V.HasPreΩSqAt n x)
    (W : WeierstrassCurve R) : W.HasPreΩSq n :=
  hasPreΩSq_of_forall_charZero
    (fun F _ _ V => hasPreΩSq_of_forall_hasPreΩSqAt (h F V)) W

/-! ### The reduction to an ALGEBRAICALLY CLOSED characteristic-`0` field -/

/-- **`HasPreΩSq n` over every algebraically closed characteristic-`0` field gives it over every
commutative ring.**  One more step than `hasPreΩSq_of_forall_charZero`, and it costs one line: a
field embeds in its algebraic closure, that closure is still of characteristic `0`, and
`hasPreΩSq_of_map` descends the identity back along the embedding.

⚠️ **This is not free strength for its own sake — it is the hypothesis the classical proof wants.**
Over an algebraically closed field `Ψ₂Sq = 4X³ + b₂X² + 2b₄X + b₆` splits, so the three nontrivial
`2`-torsion points are rational and the bracket of `HasΨSqDoubling` factors as
`4·∏ᵢ (Φₙ − eᵢ·ΨSqₙ)`; the classical argument for the crux is that each of those three factors is a
square.  None of that is available over a general characteristic-`0` field, and every earlier note
on `#404` posed the crux over one.

⚠️ **The proof that closed the crux does not use the splitting.**  It uses algebraic closure only
to produce **some** `y` with `W.Equation x y` above a given `x`
(`WeierstrassCurve.Affine.exists_equation` of
`EllipticCurves.Torsion.ThreeTorsionStructure`), which is a strictly weaker use.  The `2`-torsion
factorisation above is a route that was available and was not taken; it is not what this hypothesis
turned out to be for. -/
theorem hasPreΩSq_of_forall_algClosed {n : ℤ}
    (h : ∀ (F : Type) [Field F] [CharZero F] [IsAlgClosed F] (V : WeierstrassCurve F),
      V.HasPreΩSq n) (W : WeierstrassCurve R) : W.HasPreΩSq n :=
  hasPreΩSq_of_forall_charZero (fun F _ _ V =>
    hasPreΩSq_of_map (f := algebraMap F (AlgebraicClosure F))
      (algebraMap F (AlgebraicClosure F)).injective
      (h (AlgebraicClosure F) (V.map (algebraMap F (AlgebraicClosure F))))) W

/-- **The evaluated identity at every point of every algebraically closed characteristic-`0` field
suffices.**  `hasPreΩSq_of_forall_hasPreΩSqAt_charZero` with the base additionally algebraically
closed, so its hypothesis is weaker than that one's.

⚠️ **It is not weaker than `hasPreΩSq_of_forall_hasΨSqDoubling_algClosed`'s; the two tie, and this
docstring asserted a superlative over a miscount until `#1402`.**  An algebraically closed field of
characteristic `0` is an infinite domain, so at `n ≠ 0` the two hypotheses imply each other:
`HasΨSqDoubling n` gives `HasPreΩSq n` by `hasPreΩSq_of_hasΨSqDoubling` and hence
`∀ x, HasPreΩSqAt n x` by `HasPreΩSq.at`, and back by `hasPreΩSq_of_forall_hasPreΩSqAt` and
`HasPreΩSq.hasΨSqDoubling`.  What separates them is vocabulary rather than strength — the other is
written in Mathlib's `Φ`, `ΨSq` and `b₂/b₄/b₆` alone — and that is why it, not this, carries the
designation. -/
theorem hasPreΩSq_of_forall_hasPreΩSqAt_algClosed {n : ℤ}
    (h : ∀ (F : Type) [Field F] [CharZero F] [IsAlgClosed F] (V : WeierstrassCurve F) (x : F),
      V.HasPreΩSqAt n x)
    (W : WeierstrassCurve R) : W.HasPreΩSq n :=
  hasPreΩSq_of_forall_algClosed
    (fun F _ _ _ V => hasPreΩSq_of_forall_hasPreΩSqAt (h F V)) W

/-- **⚠️ THE FORM `#404`'s CRUX WAS ATTACKED IN — and its hypothesis is now discharged**, by
`WeierstrassCurve.hasΨSqDoubling_of_algClosed` of `EllipticCurves.Torsion.OmegaCrux`; the
composition is `WeierstrassCurve.hasPreΩSq_of_one_le` there.  To prove `HasPreΩSq n` for every
Weierstrass curve over every commutative ring — hence, through
`WeierstrassCurve.Affine.equation_of_hasPreΩSq`, the on-curve identity for `(Φₙ/ΨSqₙ, ωₙ/ψₙ³)` — it
is enough to prove

```
ΨSq₂ₙ = ΨSqₙ · (4Φₙ³ + b₂Φₙ²ΨSqₙ + 2b₄ΦₙΨSqₙ² + b₆ΨSqₙ³)
```

for every curve over every **algebraically closed field of characteristic `0`**.

Three things have been given up along the way and none of them was ever part of the statement:
`preΩ` (this project's own construction — the target above is written in Mathlib's `Φ`, `ΨSq` and
`b₂/b₄/b₆` alone), an arbitrary base ring (now a field where `2`, `3` and `4` are units), and an
arbitrary field (now one where `Ψ₂Sq` splits).

⚠️ `hn : n ≠ 0` is not a restriction: `hasPreΩSq_zero` is unconditional. -/
theorem hasPreΩSq_of_forall_hasΨSqDoubling_algClosed {n : ℤ} (hn : n ≠ 0)
    (h : ∀ (F : Type) [Field F] [CharZero F] [IsAlgClosed F] (V : WeierstrassCurve F),
      V.HasΨSqDoubling n)
    (W : WeierstrassCurve R) : W.HasPreΩSq n :=
  hasPreΩSq_of_forall_algClosed
    (fun F _ _ _ V => hasPreΩSq_of_hasΨSqDoubling V (Int.cast_ne_zero.mpr hn) (h F V)) W

/-! ### The polynomial identity at `n = 3` -/

/-- **`HasPreΩSq 3`, for every Weierstrass curve over every commutative ring.**  The input is
`WeierstrassCurve.Affine.hasPreΩSqAt_three`, which is the evaluated identity over a field of
characteristic `≠ 2`; the conclusion needs no hypothesis on the base at all.

⚠️ This adds **no algebra**.  Every monomial of the identity was already checked by
`hasPreΩSqAt_three`; what the reduction supplies is the right to have checked it with `4`
invertible.  `EllipticCurves.Torsion.OmegaOnCurve`'s module docstring measures the alternative at
9903 monomials and records that `lake build` killed it with exit `137`. -/
theorem hasPreΩSq_three (W : WeierstrassCurve R) : W.HasPreΩSq 3 :=
  hasPreΩSq_of_forall_hasPreΩSqAt_charZero
    (fun _ _ _ V x => Affine.hasPreΩSqAt_three (W := V.toAffine) two_ne_zero x) W

/-! ### Non-vacuity

⚠️ **Certificates, not content.**  Both are instances of `hasPreΩSq_three` and neither may be
cited; they exist so that a reduction which silently failed to escape its input's hypotheses would
break the build. -/

/-- **The certificate that matters: characteristic `2`.**  The input
`WeierstrassCurve.Affine.hasPreΩSqAt_three` requires `(2 : F) ≠ 0`, and `hasPreΩSq_three` holds
over `ZMod 2`, where `2 = 0`.  ⚠️ Do not cite this; use `hasPreΩSq_three`. -/
theorem hasPreΩSq_three_zmod_two (W : WeierstrassCurve (ZMod 2)) : W.HasPreΩSq 3 :=
  hasPreΩSq_three W

/-- **The certificate over `ℤ`**, the base for which `EllipticCurves.Torsion.OmegaOnCurve`'s
docstring states the identity is true but out of reach by `ring1`.  ⚠️ Do not cite this; use
`hasPreΩSq_three`. -/
theorem hasPreΩSq_three_int (W : WeierstrassCurve ℤ) : W.HasPreΩSq 3 :=
  hasPreΩSq_three W

/-- **The certificate that `HasΨSqDoubling` is a faithful restatement and not a weaker one**: the
`n = 3` identity is pushed through `HasPreΩSq.hasΨSqDoubling` into the `x`-coordinate form and
pulled back through `hasPreΩSq_of_hasΨSqDoubling`, over `ℚ`, arriving at the statement it started
from.  A reformulation that had quietly lost content would not survive the round trip.  ⚠️ Do not
cite this; use `hasPreΩSq_three`. -/
theorem hasPreΩSq_three_roundTrip (W : WeierstrassCurve ℚ) : W.HasPreΩSq 3 :=
  hasPreΩSq_of_hasΨSqDoubling W (by norm_num) ((hasPreΩSq_three W).hasΨSqDoubling W)

/-- **The certificate that the algebraically closed reduction is usable**: `hasPreΩSq_three` is
re-derived through `hasPreΩSq_of_forall_hasPreΩSqAt_algClosed` rather than through
`hasPreΩSq_of_forall_hasPreΩSqAt_charZero`, so a reduction whose extra `[IsAlgClosed F]` had made
its hypothesis unsatisfiable would break the build here.  ⚠️ Do not cite this; use
`hasPreΩSq_three`. -/
theorem hasPreΩSq_three_algClosed (W : WeierstrassCurve R) : W.HasPreΩSq 3 :=
  hasPreΩSq_of_forall_hasPreΩSqAt_algClosed
    (fun _ _ _ _ V x => Affine.hasPreΩSqAt_three (W := V.toAffine) two_ne_zero x) W

end WeierstrassCurve
