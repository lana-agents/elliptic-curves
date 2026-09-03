/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import EllipticCurves.Fixtures
import EllipticCurves.FunctionField.MulByNComposition
import EllipticCurves.FunctionField.MulByNPlacePullback
import EllipticCurves.FunctionField.MulByNXCoordFormula
import EllipticCurves.FunctionField.MulByThreePlacePullback

/-!
# `[n]` fixes the point at infinity: by composition, and by the pole order

Two routes to the same conclusion, both over a field with `(2 : F) ≠ 0` — one at every `3`-smooth
`n ≠ 0`, which also asks `(3 : F) ≠ 0`, and one at every `n` with `((n : ℤ) : F) ≠ 0`.

`EllipticCurves.FunctionField.MulByNPlacePullback` contracts a place of the projective curve along
`[n]∗` (`comapProjPointN`) for every `n` at which `[n]` is non-constant, and closes its *"rungs that
do not survive"* section with

> Consequently `comapProjPointN … none = none` (*"`[n]` fixes the point at infinity"*) is **also**
> absent: `comapProjPointTwo_none` is proved from the pole order.

That is right about the *merged route*, which runs `divisorProj_mulByTwoEndo_apply` backwards
against `ordInfty ([2]∗ genX) = -2`.  ⚠️ **This paragraph used to add that
`ordInfty ([n]∗ genX) < 0` is therefore "genuinely unavailable at general `n`, because
`mulByNEndo_genX` rewrites to
`x(n • 𝒫)`, about which the group law says only that it satisfies the Weierstrass equation" — and
that reason is incomplete.**  The group law says only that; the **coordinate formula** says
`x(n • 𝒫) = Φₙ(genX)/ΨSqₙ(genX)` (`xCoord_nsmul_genericPoint'`,
`EllipticCurves.FunctionField.MulByNXCoordFormula`, `#251`), which pins the pole order outright at
every `n` with `(2 : F) ≠ 0` and `((n : ℤ) : F) ≠ 0` against Mathlib's `natDegree_Φ` and
`natDegree_ΨSq`.  That is the `§ The same four statements, by the pole order` section below, and it
is why this file now imports `MulByNXCoordFormula`.  ⚠️ **The conclusion survives where it was
aimed**: at an `n` divisible by the characteristic the pole order really is not `-2`, and there the
observation about `x(𝒫 + T)` — which satisfies the same equation with no pole at infinity — is
still the right way to see that the equation alone pins nothing.

**It is available at every `3`-smooth `n`, and by composition rather than by a pole order.**
`EllipticCurves.FunctionField.MulByNComposition` proves `[m · n]∗ = [m]∗ ∘ [n]∗` from the group law;
`comapProjPoint` is contravariant, so that transports to a composition law for the contraction, and
`none ↦ none` at `n = 2` and `n = 3` — both merged — composes up.  This is `#1213`'s finding one
rung over, and `#1165`'s two rungs over: *a dead end inside a route is not a dead end for the
deliverable*.

## ⚠️ The order of composition, which is the reviewable content

`comapProjPointN` is a **contravariant** functor of the endomorphism, and it is stacked on the
contravariance of `[m · n]∗ = [m]∗ ∘ [n]∗` itself.  The two reversals compose to

```
comapProjPointN (m · n) = comapProjPointN n ∘ comapProjPointN m,
```

which is the *covariant* order — as it must be, since on points `comapProjPointN n` is the forward
map `[n]` and `[m · n] = [n] ∘ [m]`.  Getting either reversal wrong gives a statement that is still
true at `m = n` and false in general.  It is derived here from `ValuationSubring.comap_comap`
through the general `comapProjPoint_comp` (`EllipticCurves.FunctionField.PlacePullback`), which is
stated for an arbitrary pair of `F`-fixing endomorphisms over which `F(W)` is integral, and not
guessed.

## ⚠️ The index is unramified at infinity too, and that is *not* rung 4 at general `n`

The ramification index is multiplicative along the composition — same uniformizer argument as
`ramificationIdxN_two` — so `e_∞ = 1` at every `3`-smooth `n ≠ 0` with `(2 : F) ≠ 0` and
`(3 : F) ≠ 0`, and hence `ordInfty ([n]∗ f) = ordInfty f`, in particular
`ordInfty ([n]∗ genX) = -2`.  That is `#670`'s statement at those `n`.

⚠️ **`MulByNPlacePullback`'s argument that it is false at an `n` divisible by the characteristic
is untouched.**  Over `F̄` of characteristic `p > 2` the transcendence hypothesis holds at `n = p`,
`[p]` is inseparable, and `ordInfty ([p]∗ genX)` is `-2p` or `-2p²`.  So `(n : F) ≠ 0` in some form
is not optional.

⚠️ **What does not extend is the *route*, not the statement, and this paragraph used to conflate
them.**  It said *"nothing here says `e_∞ = 1` at any `n` with a prime factor other than `2` or `3`,
and the argument gives no route to one: the composition law manufactures no new prime"*.  The second
half is exactly right and is why the `_of_smooth` layer stops where it does — a ladder built from
`{2, 3}` reaches the `{2,3}`-generated indices at any hypotheses whatsoever.  The first half is
**false as of the section below**, which says `e_∞ = 1` at every `n` with `(2 : F) ≠ 0` and
`((n : ℤ) : F) ≠ 0` by a different argument: the pole order, which manufactures no primes because
it counts degrees rather than composing maps.

## ⚠️ The transcendence parameter, and why no reach clause below names it

Every general-`n` declaration below whose statement mentions the `[n]∗` layer — `mulByNEndo n h`,
`comapProjPointN n h`, or anything built on them — takes
`h : Transcendental F (n • genericPoint).xCoord` as an explicit argument, and no reach clause names
it.  That is the `README.md` exemption
(`## Docstring conventions` → `### Reach clauses`) — a hypothesis derivable from the ones the clause
*does* name adds no reach — and this is the citation it asks for:

* `transcendental_xCoord_nsmul_genericPoint_of_intCast_ne_zero`
  (`EllipticCurves.FunctionField.MulByNXCoordFormula`) proves `h` from `(2 : F) ≠ 0` and
  `((n : ℤ) : F) ≠ 0` — the `_of_ne_zero` clauses' own hypotheses, the two cast forms being
  interderivable by `Int.cast_natCast`;
* `transcendental_xCoord_nsmul_of_smooth` (`EllipticCurves.FunctionField.MulByNComposition`) proves
  it from `(2 : F) ≠ 0`, `(3 : F) ≠ 0`, `n ≠ 0` and `3`-smoothness — the `_of_smooth` clauses' own.

⚠️ **`(2 : F) ≠ 0` fails that same test, and so stays bound.**  Nothing any reach clause in this
file names derives it — not `3`-smoothness, not `(n : F) ≠ 0` — so omitting it is not an instance of
the exemption but the defect class `#1137` is named after.

⚠️ **The general-`n` half of that sentence is a restriction, not filler.**  Several fixed-index
statements below are about that same layer and take no `h` at all: they **discharge** it inline
from their own hypotheses — the `n = 5` ones by the first lemma cited above — so the derivation is
exhibited in this file rather than only asserted about it.

## Main statements

⚠️ Every public declaration of this file is listed.

* `WeierstrassCurve.Affine.CoordinateRing.comapProjPointN_mul` and `…comapProjPointN_of_mul_eq` —
  the composition law for the contraction, and its `m * n = k` form;
* `…comapProjPointN_one`, `…comapProjPointN_three`, `…ramificationIdxN_one` and
  `…ramificationIdxN_three` — the contraction and the index at `n = 1` and at `n = 3`, the latter
  pair being the `n = 3` companions of the merged `comapProjPointN_two` / `ramificationIdxN_two`;
* `…ramificationIdxN_mul` and `…ramificationIdxN_of_mul_eq` — `e_p([m · n]) = e_p([m]) ·
  e_{[m]⁻¹p}([n])`, the multiplicativity of the ramification index along the composition;
* **`…comapProjPointN_two_pow_mul_three_pow_none`** and **`…comapProjPointN_none_of_smooth`** —
  `[n]` fixes the point at infinity at every `3`-smooth `n ≠ 0` with `(2 : F) ≠ 0` and
  `(3 : F) ≠ 0`;
* `…ramificationIdxN_two_pow_mul_three_pow_none` and `…ramificationIdxN_none_of_smooth` — and it is
  unramified there;
* `…ordInfty_mulByNEndo_of_comapProjPointN_none` — `ordInfty ([n]∗ f) = e_∞ · ordInfty f`, from
  `none ↦ none` alone and with no smoothness hypothesis;
* `…ordInfty_mulByNEndo_of_smooth` and `…ordInfty_mulByNEndo_genX_of_smooth` — the same with
  `e_∞ = 1` supplied, and `ordInfty ([n]∗ genX) = -2`, at every `3`-smooth `n ≠ 0` with
  `(2 : F) ≠ 0` and `(3 : F) ≠ 0`.
* ⚠️ **`…ordInfty_mulByNEndo_genX_of_ne_zero`, `…comapProjPointN_none_of_ne_zero`,
  `…ramificationIdxN_none_of_ne_zero` and `…ordInfty_mulByNEndo_of_ne_zero`** — **the same four
  conclusions at every `n` with `(2 : F) ≠ 0` and `((n : ℤ) : F) ≠ 0`**, by the pole order rather
  than by composition.  ⚠️ The cast is the **`ℤ`** one, as all four binders are.
  ⚠️ **The second layer subsumes the first as a statement, and the `example`s beside it prove
  that rather than assert it**: `(2 : F) ≠ 0` and `(3 : F) ≠ 0` force `((2^a · 3^b : ℕ) : F) ≠ 0`,
  so every `_of_smooth` conclusion above is a corollary of its `_of_ne_zero` counterpart.  What
  does **not** transfer is the *route*: the `3`-smooth proofs consume no division polynomial and
  the general ones consume `Φₙ`/`ΨSqₙ`, which is why nothing above is deleted.  `n = 14` is in the
  second statement and not in the first; that is a fact about ranges, not about content.
* `…ordInfty_mulByNEndo_genX_five`, `…comapProjPointN_none_five` and `…ramificationIdxN_none_five` —
  the first index outside `{2, 3}`, named rather than left as `example`s.

## What is *not* here

* **No new theorem about places.**  Every statement is the merged general-`φ` place machinery
  (`EllipticCurves.FunctionField.PlacePullback`) applied to `mulByNEndo`, exactly as
  `MulByNPlacePullback` says of itself; the content is the composition law and the two merged prime
  inputs.
* ⚠️ **`n = 5` IS here now, and characteristic `3` is too — this bullet is what changed.**  It read
  *"Nothing at `n = 5`, and nothing in characteristic `2` or `3`"*.  The `_of_ne_zero` layer needs
  `(2 : F) ≠ 0` and `((n : ℤ) : F) ≠ 0` and nothing else, so it reaches `n = 5` (named), `n = 14`
  (committed, and the index that shows the layer is not `{2,3,5}`-parametrised) and every index
  prime to the characteristic **in characteristic `3`**.  ⚠️ Characteristic `2` is still empty, and
  that half of the bullet stands: `(2 : F) ≠ 0` is a hypothesis of every statement in the file.
* **Still nothing at an `n` divisible by the characteristic**, where `e_∞ = 1` is false rather than
  open.  See the second warning above.
* **No residue degree — *here*.**  ⚠️ This bullet used to say that `#701` and `#1046`, *"the
  residue-degree companions at the point at infinity"*, **are absent**.  Both clauses were loose.
  `#701` and `#1046` are the *fibre sums* `∑_{p ↦ q} e_p · f_p = deg`, not the value of `f` at one
  place; ⚠️ **their general-`n` form was recorded here as still open, and is not**: it is
  `EllipticCurves.FunctionField.MulByNInertia` (`#1221`).  The value at one place — `f_∞ = 1` —
  is `EllipticCurves.FunctionField.MulByNResidueDegree` (`#1225`), and ⚠️ it holds at **every** `n`
  and does not consume this file: it needs no fibre statement, no `3`-smoothness and no hypothesis
  on `F`.  What is true of *this* file is only that it proves nothing about residue degrees.
* **No `ωₙ`, no coprimality, no elliptic net.**  `#404` (closed), `#1184` (⚠️ closed over a field
  of characteristic `≠ 2` by `EllipticCurves.Torsion.CoprimeAdjacent`; open over an arbitrary ring)
  and Ward (`#260`, closed) are unused.

⚠️ **Both of the things that sentence names are now closed, and it is an independence claim
rather than a gate.**  `#404`'s on-curve identity is
`WeierstrassCurve.Affine.equation_div_of_ψ_ne_zero` (`EllipticCurves.Torsion.OmegaCrux`, PR #557, at
every index over every commutative ring) and Ward's theorem (`#260`) is
`WeierstrassCurve.Affine.ψ_isEllipticNet` (`EllipticCurves.Torsion.WardHalving`), unconditional.
The claim below is unchanged in force: this file uses neither.  ⚠️ **Nor is the third thing this
paragraph used to call open**: the identification of `(Φₙ/ΨSqₙ, ωₙ/(2ψₙ³))` with `n • P` is `#251`
on its `x`-half and `#1500` on its `y`-half, and both are closed at every index
(`hasXCoordFormula_of_two_ne_zero`, `EllipticCurves.Torsion.NsmulOrder`;
`nsmul_eq_some_omegaY_of_ΨSq_ne_zero`, `EllipticCurves.Torsion.NsmulYPeriodic`, PR #579); see
`EllipticCurves.FunctionField.MulByNPullback`.

## References

* [J. H. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], II.2, II.3.6.
-/

open IsDedekindDomain

namespace WeierstrassCurve.Affine

namespace CoordinateRing

variable {F : Type*} [Field F] {W : Affine F} [IsDedekindDomain W.CoordinateRing] [W.IsElliptic]

/-! ### The contraction along `[m · n]∗` -/

/-- **`comapProjPointN (m · n) = comapProjPointN n ∘ comapProjPointN m`.**

⚠️ The order is the content.  `[m · n]∗ = [m]∗ ∘ [n]∗` (`mulByNEndo_mul`) and `comapProjPoint` is
contravariant, so the two reversals cancel and the contraction composes in the *covariant* order —
which is right, since on points `comapProjPointN n` is the forward map `[n]`.  Everything is forced
by `ValuationSubring.comap_comap`; see `comapProjPoint_comp`. -/
theorem comapProjPointN_mul {m n : ℕ}
    (hm : Transcendental F (m • genericPoint (W := W)).xCoord)
    (hn : Transcendental F (n • genericPoint (W := W)).xCoord)
    (hmn : Transcendental F ((m * n) • genericPoint (W := W)).xCoord) (p : ProjPoint W) :
    comapProjPointN (m * n) hmn p = comapProjPointN n hn (comapProjPointN m hm p) := by
  refine placeOf_injective ?_
  rw [placeOf_comapProjPointN, placeOf_comapProjPointN, placeOf_comapProjPointN,
    mulByNEndo_mul hm hn hmn, ValuationSubring.comap_comap]

/-- **The composition law at a stated product.**  The `m * n = k` form of `comapProjPointN_mul`, so
that a caller holding `k` as `2 ^ (a + 1) * 3 ^ b` never transports the non-constancy hypothesis
along an arithmetic identity — the friction `#1213` records, resolved the same way, by `subst`. -/
theorem comapProjPointN_of_mul_eq {m n k : ℕ} (hk : m * n = k)
    (hm : Transcendental F (m • genericPoint (W := W)).xCoord)
    (hn : Transcendental F (n • genericPoint (W := W)).xCoord)
    (h : Transcendental F (k • genericPoint (W := W)).xCoord) (p : ProjPoint W) :
    comapProjPointN k h p = comapProjPointN n hn (comapProjPointN m hm p) := by
  subst hk
  exact comapProjPointN_mul hm hn h p

/-! ### The base and the second prime

`comapProjPointN_two` and `ramificationIdxN_two` are merged
(`EllipticCurves.FunctionField.MulByNPlacePullback`).  These are the `n = 1` and `n = 3` companions,
which the double induction below needs and which that file does not carry. -/

/-- **`[1]∗` contracts every place to itself**: `[1]∗` is the identity (`mulByNEndo_one`), and a
place contracted along the identity is itself. -/
theorem comapProjPointN_one (h : Transcendental F ((1 : ℕ) • genericPoint (W := W)).xCoord)
    (p : ProjPoint W) : comapProjPointN 1 h p = p := by
  refine placeOf_injective ?_
  rw [placeOf_comapProjPointN, mulByNEndo_one]
  rfl

/-- **The `[n]∗` contraction at `n = 3` is the merged `[3]∗` contraction** — the `n = 3` companion
of `comapProjPointN_two`, proved the same way, through `mulByNEndo_three`. -/
theorem comapProjPointN_three (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) (p : ProjPoint W) :
    comapProjPointN 3 (transcendental_xCoord_three_nsmul (W := W) h2 h3) p
      = comapProjPointThree h2 h3 p := by
  refine placeOf_injective ?_
  rw [placeOf_comapProjPointN, comapProjPointThree, placeOf_comapProjPoint,
    mulByNEndo_three h2 h3]

/-- **`[1]∗` is unramified everywhere.**  Read off the order transport at a uniformizer at `p`,
which `comapProjPointN_one` says is its own contraction. -/
theorem ramificationIdxN_one (h : Transcendental F ((1 : ℕ) • genericPoint (W := W)).xCoord)
    (p : ProjPoint W) : ramificationIdxN 1 h p = 1 := by
  obtain ⟨π, hπ0, hπ⟩ := exists_divisorProj_eq_one p
  have hN := divisorProj_mulByNEndo_apply 1 h hπ0 p
  have hid : mulByNEndo 1 h π = π := by rw [mulByNEndo_one]; rfl
  rw [comapProjPointN_one h p, hπ, mul_one, hid, hπ] at hN
  exact hN.symm

/-- **The `[n]∗` ramification index at `n = 3` is the merged `[3]∗` index** — the `n = 3` companion
of `ramificationIdxN_two`.  Both are read off the transported order at a uniformizer at the
contracted place, and `comapProjPointN_three` says the contracted place is the same one. -/
theorem ramificationIdxN_three (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) (p : ProjPoint W) :
    ramificationIdxN 3 (transcendental_xCoord_three_nsmul (W := W) h2 h3) p
      = ramificationIdxThree h2 h3 p := by
  obtain ⟨π, hπ0, hπ⟩ := exists_divisorProj_eq_one (comapProjPointThree h2 h3 p)
  have hN := divisorProj_mulByNEndo_apply 3 (transcendental_xCoord_three_nsmul (W := W) h2 h3) hπ0 p
  have hT := divisorProj_mulByThreeEndo_apply h2 h3 hπ0 p
  rw [comapProjPointN_three h2 h3 p, hπ, mul_one] at hN
  rw [hπ, mul_one] at hT
  rw [← hN, ← hT, mulByNEndo_three h2 h3]

/-! ### The ramification index along `[m · n]∗` -/

/-- **`e_p([m · n]) = e_p([m]) · e_{[m]⁻¹p}([n])`** — the ramification index is multiplicative along
the composition.

The proof is `ramificationIdxN_two`'s, once: take a uniformizer `π` at the contracted place
`comapProjPointN (m · n) p`, transport its order in two ways — once along `[m · n]∗` and once along
`[m]∗` after `[n]∗` — and use `comapProjPointN_mul` to see that the two contracted places are the
same, so that the two right-hand sides differ only by the index. -/
theorem ramificationIdxN_mul {m n : ℕ}
    (hm : Transcendental F (m • genericPoint (W := W)).xCoord)
    (hn : Transcendental F (n • genericPoint (W := W)).xCoord)
    (hmn : Transcendental F ((m * n) • genericPoint (W := W)).xCoord) (p : ProjPoint W) :
    ramificationIdxN (m * n) hmn p
      = ramificationIdxN m hm p * ramificationIdxN n hn (comapProjPointN m hm p) := by
  obtain ⟨π, hπ0, hπ⟩ := exists_divisorProj_eq_one (comapProjPointN (m * n) hmn p)
  have hπ' : mulByNEndo n hn π ≠ 0 := fun h =>
    hπ0 ((mulByNEndo n hn).injective (by rw [h, map_zero]))
  have h1 := divisorProj_mulByNEndo_apply (m * n) hmn hπ0 p
  have h2 := divisorProj_mulByNEndo_apply m hm hπ' p
  have h3 := divisorProj_mulByNEndo_apply n hn hπ0 (comapProjPointN m hm p)
  rw [hπ, mul_one] at h1
  rw [← comapProjPointN_mul hm hn hmn p, hπ, mul_one] at h3
  have hcomp : mulByNEndo (m * n) hmn π = mulByNEndo m hm (mulByNEndo n hn π) := by
    rw [mulByNEndo_mul hm hn hmn]; rfl
  rw [← h1, hcomp, h2, h3]

/-- **The multiplicativity at a stated product.**  The `m * n = k` form of
`ramificationIdxN_mul`. -/
theorem ramificationIdxN_of_mul_eq {m n k : ℕ} (hk : m * n = k)
    (hm : Transcendental F (m • genericPoint (W := W)).xCoord)
    (hn : Transcendental F (n • genericPoint (W := W)).xCoord)
    (h : Transcendental F (k • genericPoint (W := W)).xCoord) (p : ProjPoint W) :
    ramificationIdxN k h p
      = ramificationIdxN m hm p * ramificationIdxN n hn (comapProjPointN m hm p) := by
  subst hk
  exact ramificationIdxN_mul hm hn h p

/-! ### `[n]` fixes the point at infinity, at every `3`-smooth `n` -/

/-- **`[2^a · 3^b]` fixes the point at infinity.**

Induction on `a` and then on `b`.  The base is `comapProjPointN_one`; each step peels one prime off
the index with `comapProjPointN_of_mul_eq` and sends `none` to `none` by the merged
`comapProjPointTwo_none` / `comapProjPointThree_none`, reached through `comapProjPointN_two` /
`comapProjPointN_three`.  ⚠️ The two prime steps are the only place a hypothesis on `F` enters. -/
theorem comapProjPointN_two_pow_mul_three_pow_none (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) (a b : ℕ)
    (h : Transcendental F ((2 ^ a * 3 ^ b) • genericPoint (W := W)).xCoord) :
    comapProjPointN (2 ^ a * 3 ^ b) h (none : ProjPoint W) = none := by
  induction a with
  | zero =>
    induction b with
    | zero => exact comapProjPointN_one h none
    | succ b ih =>
      have hb := transcendental_xCoord_two_pow_mul_three_pow_nsmul (W := W) h2 h3 0 b
      rw [comapProjPointN_of_mul_eq (m := 3) (n := 2 ^ 0 * 3 ^ b) (by ring)
        (transcendental_xCoord_three_nsmul h2 h3) hb h, comapProjPointN_three h2 h3,
        comapProjPointThree_none h2 h3, ih hb]
  | succ a ih =>
    have ha := transcendental_xCoord_two_pow_mul_three_pow_nsmul (W := W) h2 h3 a b
    rw [comapProjPointN_of_mul_eq (m := 2) (n := 2 ^ a * 3 ^ b) (by ring)
      (transcendental_xCoord_two_nsmul h2) ha h, comapProjPointN_two h2,
      comapProjPointTwo_none h2, ih ha]

/-- **`[n]` fixes the point at infinity at every `3`-smooth `n ≠ 0` with `(2 : F) ≠ 0` and
`(3 : F) ≠ 0`**: `comapProjPointN n h none = none`.

Classically, that `[n]` extends to a morphism of the projective curve carrying `O` to `O`.  The
hypotheses are those of `finrank_mulByNFieldRange_of_smooth`
(`EllipticCurves.FunctionField.MulByNComposition`), and `n = 5` is the first index not covered. -/
theorem comapProjPointN_none_of_smooth (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) {n : ℕ} (hn : n ≠ 0)
    (hfac : ∀ p ∈ n.primeFactors, p = 2 ∨ p = 3)
    (h : Transcendental F (n • genericPoint (W := W)).xCoord) :
    comapProjPointN n h (none : ProjPoint W) = none := by
  obtain ⟨a, b, rfl⟩ := Nat.exists_eq_two_pow_mul_three_pow n hn hfac
  exact comapProjPointN_two_pow_mul_three_pow_none h2 h3 a b h

/-- **`[2^a · 3^b]` is unramified at the point at infinity.**  The same double induction, against
`ramificationIdxN_mul` and the merged `ramificationIdxTwo_none` / `ramificationIdxThree_none`; the
fibre computation of `comapProjPointN_two_pow_mul_three_pow_none` is what keeps the second factor at
`none` rather than at some affine place. -/
theorem ramificationIdxN_two_pow_mul_three_pow_none (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) (a b : ℕ)
    (h : Transcendental F ((2 ^ a * 3 ^ b) • genericPoint (W := W)).xCoord) :
    ramificationIdxN (2 ^ a * 3 ^ b) h (none : ProjPoint W) = 1 := by
  induction a with
  | zero =>
    induction b with
    | zero => exact ramificationIdxN_one h none
    | succ b ih =>
      have hb := transcendental_xCoord_two_pow_mul_three_pow_nsmul (W := W) h2 h3 0 b
      rw [ramificationIdxN_of_mul_eq (m := 3) (n := 2 ^ 0 * 3 ^ b) (by ring)
        (transcendental_xCoord_three_nsmul h2 h3) hb h, ramificationIdxN_three h2 h3,
        ramificationIdxThree_none h2 h3, comapProjPointN_three h2 h3,
        comapProjPointThree_none h2 h3, ih hb, mul_one]
  | succ a ih =>
    have ha := transcendental_xCoord_two_pow_mul_three_pow_nsmul (W := W) h2 h3 a b
    rw [ramificationIdxN_of_mul_eq (m := 2) (n := 2 ^ a * 3 ^ b) (by ring)
      (transcendental_xCoord_two_nsmul h2) ha h, ramificationIdxN_two h2,
      ramificationIdxTwo_none h2, comapProjPointN_two h2, comapProjPointTwo_none h2, ih ha, mul_one]

/-- **`[n]` is unramified at the point at infinity at every `3`-smooth `n ≠ 0` with
`(2 : F) ≠ 0` and `(3 : F) ≠ 0`.**

⚠️ Both hypotheses on `F` are load-bearing here in a way they are not for the fibre statement above:
they and the `3`-smoothness of `n` are together what forces `char F ∤ n`, hence `[n]` separable.  At
a general `n` this is **false** — see the module docstring. -/
theorem ramificationIdxN_none_of_smooth (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) {n : ℕ} (hn : n ≠ 0)
    (hfac : ∀ p ∈ n.primeFactors, p = 2 ∨ p = 3)
    (h : Transcendental F (n • genericPoint (W := W)).xCoord) :
    ramificationIdxN n h (none : ProjPoint W) = 1 := by
  obtain ⟨a, b, rfl⟩ := Nat.exists_eq_two_pow_mul_three_pow n hn hfac
  exact ramificationIdxN_two_pow_mul_three_pow_none h2 h3 a b h

/-! ### The order at infinity, transported -/

/-- **`ordInfty ([n]∗ f) = e_∞ · ordInfty f`**, at every `n` whose contraction fixes the point at
infinity.

This is `divisorProj_mulByNEndo_apply` read at `p = none`, and it needs *only* the fibre statement:
no smoothness, no hypothesis on `F` beyond what `[n]∗` already carries, and no computation of
`e_∞`.  It is stated separately from the `3`-smooth corollary because the two halves are
independent — the fibre statement is a fact about the group law, `e_∞ = 1` is a fact about
separability, and only the second is genuinely restricted to `3`-smooth `n`. -/
theorem ordInfty_mulByNEndo_of_comapProjPointN_none {n : ℕ}
    (h : Transcendental F (n • genericPoint (W := W)).xCoord)
    (hnone : comapProjPointN n h (none : ProjPoint W) = none) {f : W.FunctionField} (hf : f ≠ 0) :
    ordInfty W (mulByNEndo n h f)
      = ramificationIdxN n h (none : ProjPoint W) * ordInfty W f := by
  have hkey := divisorProj_mulByNEndo_apply n h hf (none : ProjPoint W)
  rw [hnone, divisorProj_apply_none, divisorProj_apply_none] at hkey
  exact hkey

/-- **`ordInfty ([n]∗ f) = ordInfty f` at every `3`-smooth `n ≠ 0` with `(2 : F) ≠ 0` and
`(3 : F) ≠ 0`** — the order at infinity is preserved outright, both factors of the transport
being trivial. -/
theorem ordInfty_mulByNEndo_of_smooth (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) {n : ℕ} (hn : n ≠ 0)
    (hfac : ∀ p ∈ n.primeFactors, p = 2 ∨ p = 3)
    (h : Transcendental F (n • genericPoint (W := W)).xCoord) {f : W.FunctionField} (hf : f ≠ 0) :
    ordInfty W (mulByNEndo n h f) = ordInfty W f := by
  rw [ordInfty_mulByNEndo_of_comapProjPointN_none h
    (comapProjPointN_none_of_smooth h2 h3 hn hfac h) hf,
    ramificationIdxN_none_of_smooth h2 h3 hn hfac h, one_mul]

/-- **`ordInfty ([n]∗ genX) = -2` at every `3`-smooth `n ≠ 0`** — `#670`'s statement, whose merged
`n = 2` proof (`ordInfty_mulByTwoEndo_genX`) counts the degrees of `Φ₂` and `Ψ₂Sq` and has no
general-`n` analogue.  Here it is a corollary of the transport and needs no division polynomial.

⚠️ **This is the one statement in the file a reader is most likely to over-generalise.**  It is
*false* at general `n`: in characteristic `p > 2` the value at `n = p` is `-2p` or `-2p²`.  What
rules that out below is `3`-smoothness together with `(2 : F) ≠ 0` and `(3 : F) ≠ 0`, not the
composition law. -/
theorem ordInfty_mulByNEndo_genX_of_smooth (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) {n : ℕ}
    (hn : n ≠ 0) (hfac : ∀ p ∈ n.primeFactors, p = 2 ∨ p = 3)
    (h : Transcendental F (n • genericPoint (W := W)).xCoord) :
    ordInfty W (mulByNEndo n h (genX W)) = -2 := by
  rw [ordInfty_mulByNEndo_of_smooth h2 h3 hn hfac h genX_ne_zero, ordInfty_genX]

/-! ### The same four statements, by the pole order

⚠️ **Every statement in this section takes `(2 : F) ≠ 0` and `((n : ℤ) : F) ≠ 0`** — the **`ℤ`**
cast, which is what `natDegree_ΨSq` asks for and what all four binders carry.  `(n : F) ≠ 0` is a
different clause, and this section used to name it in place of the pair.

⚠️ **The route this file's opening paragraph declares unavailable is available, and it was a
citation that had never been consumed.**  That paragraph says `ordInfty ([n]∗ genX) < 0` cannot be
had at general `n` *"because `mulByNEndo_genX` rewrites to `x(n • 𝒫)`, about which the group law
says only that it satisfies the Weierstrass equation"*.  The group law says only that — but the
**coordinate formula** says much more, and it is merged:

* `xCoord_nsmul_genericPoint'` (`EllipticCurves.FunctionField.MulByNXCoordFormula`, `#251`) is
  `x(n • 𝒫) = Φₙ(genX)/ΨSqₙ(genX)` at every `n` with `(2 : F) ≠ 0` and `((n : ℤ) : F) ≠ 0`;
* `natDegree_Φ` and `natDegree_ΨSq` are **Mathlib's**, at `n²` and `n² - 1`.  ⚠️ `natDegree_Φ`
  takes **no** side condition at all; `natDegree_ΨSq` takes `((n : ℤ) : F) ≠ 0` and nothing else —
  in particular not `(2 : F) ≠ 0`, which enters this section through `mulByNEndo` and not here;
* `ordInfty_eval_map_genX` (`EllipticCurves.FunctionField.MulByTwoPlaceAtInfinity`) turns a degree
  into a pole order and mentions no doubling.

So `ordInfty_mulByTwoEndo_genX`'s proof — *"rewrite, then count the degrees of `Φ` and `ΨSq`"* —
transposes verbatim from `n = 2` to every `n` with `(2 : F) ≠ 0` and `((n : ℤ) : F) ≠ 0`, and the
three place statements fall out of it exactly as at `n = 2`.  ⚠️ `MulByNPlacePullback`'s account of
why the pole-order route stops is corrected there in the same PR.

## ⚠️ This inverts the dependency order of the `3`-smooth layer, and that is the point

Above, `ordInfty_mulByNEndo_genX_of_smooth` is a **corollary** of the contraction, reached by
composition and needing no division polynomial.  Here it is the **input**: the pole order is proved
first, from the degrees, and the contraction is read off it.  The two layers are therefore
independent proofs of the same conclusion, which is why the `_of_smooth` forms are kept rather than
deprecated — the `3`-smooth route remains the only one here that consumes no division polynomial at
all.

⚠️ **Independent proofs, not independent statements, and the difference is committed below.**  At
the level of what is *proved*, this layer contains the one above outright:
`Nat.intCast_ne_zero_of_smooth` (`EllipticCurves.Torsion.ThreePrimary`) turns `(2 : F) ≠ 0`,
`(3 : F) ≠ 0` and `3`-smoothness into `((n : ℤ) : F) ≠ 0` in four lines, and the three `example`s at
the end of this file derive each `_of_smooth` statement verbatim from its `_of_ne_zero`
counterpart.  ⚠️ **Proved rather than asserted, deliberately** — this file's sibling
`EllipticCurves.TateModule.OpenKernel` commits the same subsumption the same way, and a docstring
sentence claiming an implication does or does not hold is exactly the kind of claim that this front
has repeatedly had to correct.

## ⚠️ `((n : ℤ) : F) ≠ 0` is sharp, and this file's warning about it stands unchanged

At `n = char F > 2` the transcendence hypothesis is still met, `[n]` is inseparable, and
`ordInfty ([n]∗ genX)` is `-2n` or `-2n²` rather than `-2` — so `e_∞ = 1` is **false** there, not
merely unproved.  What changed is the *shape* of the sufficient condition on the **index**: it is
`((n : ℤ) : F) ≠ 0`, not `3`-smoothness together with `n ≠ 0` and `(3 : F) ≠ 0`.  ⚠️ **`(2 : F) ≠ 0`
is common to both layers and is not what changed** — this sentence used to contrast the general
layer against *"`3`-smoothness together with `(2 : F) ≠ 0` and `(3 : F) ≠ 0`"*, which reads as if
the general layer dropped `h2`, and it does not.  ⚠️ Those two index conditions are not the
same, and the implication runs one way only: the second implies the first
(`Nat.intCast_ne_zero_of_smooth`, `EllipticCurves.Torsion.ThreePrimary`), and the first does not
imply the second — `n = 14` satisfies it and is not `3`-smooth.
-/

omit [IsDedekindDomain W.CoordinateRing] in
/-- **`ordInfty ([n]∗ genX) = -2` at every `n` with `(2 : F) ≠ 0` and `((n : ℤ) : F) ≠ 0`** —
`#670`'s statement, by the degree count rather than by composition.

`x(n • 𝒫) = Φₙ(genX)/ΨSqₙ(genX)` has a pole of order `2 · n²` over one of order `2 · (n² - 1)`, so
the quotient has a double pole: the same order as `genX` itself.  ⚠️ The exact degree of `ΨSqₙ`
needs its leading coefficient `n` to be nonzero, which is the whole of what `hn` does here — the
same place `h2` starts doing work in `ordInfty_mulByTwoEndo_genX`.

⚠️ **No `[IsDedekindDomain W.CoordinateRing]`**: this is a statement about the order at infinity of
an element of `F(W)` and nothing about places is needed for it.  The three statements below do need
it.  ⚠️ Measured rather than preferred — `unusedSectionVars` is what says the instance is idle
here, and it fires on this declaration without the `omit`. -/
theorem ordInfty_mulByNEndo_genX_of_ne_zero (h2 : (2 : F) ≠ 0) {n : ℕ} (hn : ((n : ℤ) : F) ≠ 0)
    (h : Transcendental F (n • genericPoint (W := W)).xCoord) :
    ordInfty W (mulByNEndo n h (genX W)) = -2 := by
  have hn0 : n ≠ 0 := by rintro rfl; simp at hn
  have hΦ : ((W.map (algebraMap F W.FunctionField)).Φ (n : ℤ))
      = (W.Φ (n : ℤ)).map (algebraMap F W.FunctionField) := WeierstrassCurve.map_Φ ..
  have hΨ : ((W.map (algebraMap F W.FunctionField)).ΨSq (n : ℤ))
      = (W.ΨSq (n : ℤ)).map (algebraMap F W.FunctionField) := WeierstrassCurve.map_ΨSq ..
  rw [mulByNEndo_genX, xCoord_nsmul_genericPoint' h2 hn, hΦ, hΨ,
    ordInfty_div (eval_map_genX_ne_zero (W.Φ_ne_zero (n : ℤ)))
      (eval_map_genX_ne_zero (W.ΨSq_ne_zero hn)),
    ordInfty_eval_map_genX (W.Φ_ne_zero (n : ℤ)), ordInfty_eval_map_genX (W.ΨSq_ne_zero hn),
    W.natDegree_Φ (n : ℤ), W.natDegree_ΨSq hn]
  have h1 : 1 ≤ ((n : ℤ)).natAbs ^ 2 := Nat.one_le_pow _ _ (by simpa using Nat.pos_of_ne_zero hn0)
  push_cast [h1]
  ring

/-- **`[n]` fixes the point at infinity at every `n` with `(2 : F) ≠ 0` and
`((n : ℤ) : F) ≠ 0`**: `comapProjPointN n h none = none`.

The general-`n` form of `comapProjPointTwo_none` (`#670`) with its proof transposed verbatim:
`divisorProj_mulByNEndo_apply` run backwards at the generic `x`-coordinate.  An affine contraction
would make the right-hand side a nonnegative multiple of a nonnegative order, but the left-hand side
is `-2`.

⚠️ **Wider than `comapProjPointN_none_of_smooth`, and strictly so**: `n = 12` in characteristic `0`
is in both, the containment holds because the `3`-smooth hypotheses imply `hn`, and the converse
fails because `n = 14` does not satisfy them — see `Nat.intCast_ne_zero_of_smooth`
(`EllipticCurves.Torsion.ThreePrimary`) and the `example` at the end of this file, which derive that
statement from this one rather than claiming they are unrelated.  ⚠️ **The two halves used to be
welded to the wrong connective here** — *"the converse containment fails because the `3`-smooth
hypotheses imply `hn`"* — which is the reason the containment **holds**, not the reason its converse
fails (`#1540`, review of PR #599).  ⚠️ The `_of_smooth` form is nevertheless kept: its proof
composes `[2]∗` and `[3]∗` and touches no division polynomial, so it is an independent route and not
dead weight. -/
theorem comapProjPointN_none_of_ne_zero (h2 : (2 : F) ≠ 0) {n : ℕ} (hn : ((n : ℤ) : F) ≠ 0)
    (h : Transcendental F (n • genericPoint (W := W)).xCoord) :
    comapProjPointN n h (none : ProjPoint W) = none := by
  have hkey : (-2 : ℤ) = ramificationIdxN n h (none : ProjPoint W)
      * divisorProj W (genX W) (comapProjPointN n h (none : ProjPoint W)) := by
    rw [← divisorProj_mulByNEndo_apply n h genX_ne_zero none, divisorProj_apply_none,
      ordInfty_mulByNEndo_genX_of_ne_zero h2 hn]
  cases hq : comapProjPointN n h (none : ProjPoint W) with
  | none => rfl
  | some v =>
    exfalso
    rw [hq, divisorProj_apply_some] at hkey
    have hge : (0 : ℤ) ≤ ord v (genX W) := by
      rw [genX, genPsi]
      exact ord_algebraMap_nonneg v _
    have hnn : (0 : ℤ) ≤ ramificationIdxN n h (none : ProjPoint W) * ord v (genX W) :=
      mul_nonneg (ramificationIdxN_pos n h none).le hge
    linarith

/-- **`[n]` is unramified at the point at infinity at every `n` with `(2 : F) ≠ 0` and
`((n : ℤ) : F) ≠ 0`.**

⚠️ `hn` is load-bearing and not inherited: at `n = char F` this is **false**, `e_∞` being `n` or
`n²` there.  It is the general-`n` form of `ramificationIdxTwo_none` and of
`ramificationIdxN_none_of_smooth`, proved from the pole order rather than by composition. -/
theorem ramificationIdxN_none_of_ne_zero (h2 : (2 : F) ≠ 0) {n : ℕ} (hn : ((n : ℤ) : F) ≠ 0)
    (h : Transcendental F (n • genericPoint (W := W)).xCoord) :
    ramificationIdxN n h (none : ProjPoint W) = 1 := by
  have hkey := divisorProj_mulByNEndo_apply n h (f := genX W) genX_ne_zero none
  rw [comapProjPointN_none_of_ne_zero h2 hn h, divisorProj_apply_none, divisorProj_apply_none,
    ordInfty_mulByNEndo_genX_of_ne_zero h2 hn, ordInfty_genX] at hkey
  omega

/-- **`ordInfty ([n]∗ f) = ordInfty f` at every `n` with `(2 : F) ≠ 0` and `((n : ℤ) : F) ≠ 0`** —
the order at infinity is an `[n]∗`-invariant, both factors of the transport being trivial.  The
general-`n` form of `ordInfty_mulByTwoEndo`
(`EllipticCurves.FunctionField.MulByTwoPlaceAtInfinity`). -/
theorem ordInfty_mulByNEndo_of_ne_zero (h2 : (2 : F) ≠ 0) {n : ℕ} (hn : ((n : ℤ) : F) ≠ 0)
    (h : Transcendental F (n • genericPoint (W := W)).xCoord) {f : W.FunctionField} (hf : f ≠ 0) :
    ordInfty W (mulByNEndo n h f) = ordInfty W f := by
  rw [ordInfty_mulByNEndo_of_comapProjPointN_none h (comapProjPointN_none_of_ne_zero h2 hn h) hf,
    ramificationIdxN_none_of_ne_zero h2 hn h, one_mul]

/-! ### The subsumption of the `3`-smooth layer, machine-checked

⚠️ **The containment between the two layers is committed here rather than asserted in a
docstring.**  The `_of_smooth` statements carry `(2 : F) ≠ 0`, `(3 : F) ≠ 0`, `n ≠ 0` and
`3`-smoothness of `n`; in a field those force `((n : ℤ) : F) ≠ 0`, so each of them is a corollary
of its `_of_ne_zero` counterpart above.  The three `example`s below are the `_of_smooth`
statements *verbatim*, proved that way.

⚠️ **Nothing above is deleted, and the reason is not compatibility.**  The `_of_smooth` proofs run
`[m · n]∗ = [m]∗ ∘ [n]∗` against the merged `n = 2` and `n = 3` layers and consume no division
polynomial at all; the `_of_ne_zero` proofs go through `Φₙ`/`ΨSqₙ`.  Two independent routes to one
conclusion are the cheapest cross-check available on this front — the containment is of
*statements*, not of *proofs*.

⚠️ The same subsumption is committed the same way on the sibling front, by the `example` in
`EllipticCurves.TateModule.OpenKernel`'s `§ Every level prime to the characteristic`.  ⚠️ Both
`example`s now spend the **shared** cast lemmas `Nat.intCast_ne_zero_of_smooth` and
`Nat.natCast_ne_zero_of_smooth` (`EllipticCurves.Torsion.ThreePrimary`); this sentence used to cite
a `private` lemma of that name *inside* `OpenKernel`, which was the last of eight copies of the same
four-line argument and is gone (`#1552`). -/

/-- **`comapProjPointN_none_of_smooth` is a corollary of `comapProjPointN_none_of_ne_zero`** — its
statement verbatim, proved from the general layer. -/
example (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) {n : ℕ} (hn : n ≠ 0)
    (hfac : ∀ p ∈ n.primeFactors, p = 2 ∨ p = 3)
    (h : Transcendental F (n • genericPoint (W := W)).xCoord) :
    comapProjPointN n h (none : ProjPoint W) = none :=
  comapProjPointN_none_of_ne_zero h2 (Nat.intCast_ne_zero_of_smooth h2 h3 hn hfac) h

/-- **`ramificationIdxN_none_of_smooth` is a corollary of `ramificationIdxN_none_of_ne_zero`.** -/
example (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) {n : ℕ} (hn : n ≠ 0)
    (hfac : ∀ p ∈ n.primeFactors, p = 2 ∨ p = 3)
    (h : Transcendental F (n • genericPoint (W := W)).xCoord) :
    ramificationIdxN n h (none : ProjPoint W) = 1 :=
  ramificationIdxN_none_of_ne_zero h2 (Nat.intCast_ne_zero_of_smooth h2 h3 hn hfac) h

/-- **`ordInfty_mulByNEndo_genX_of_smooth` is a corollary of
`ordInfty_mulByNEndo_genX_of_ne_zero`** — so the pole order `-2` at every `3`-smooth `n`, which
above is read off the composition, is also read off the degrees of `Φₙ` and `ΨSqₙ`. -/
example (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) {n : ℕ} (hn : n ≠ 0)
    (hfac : ∀ p ∈ n.primeFactors, p = 2 ∨ p = 3)
    (h : Transcendental F (n • genericPoint (W := W)).xCoord) :
    ordInfty W (mulByNEndo n h (genX W)) = -2 :=
  ordInfty_mulByNEndo_genX_of_ne_zero h2 (Nat.intCast_ne_zero_of_smooth h2 h3 hn hfac) h

/-! ### `n = 5`, as named theorems

⚠️ This file's *"Nothing at `n = 5`"* bullet is what the section above makes false.  The three
statements here are the machine-checked consequence, named rather than left as `example`s so that a
reader can grep for them and a consumer can cite them, following
`EllipticCurves.FunctionField.MulByNGalois`.

`5` is the smallest index reachable by no composition of the merged `n = 2` and `n = 3` layers.
⚠️ It is *not* the index that shows the statements above are general rather than
`{2, 3, 5}`-parametrised; that is `n = 14`, and it is in the non-vacuity section below. -/

omit [IsDedekindDomain W.CoordinateRing] in
/-- **`ordInfty ([5]∗ genX) = -2`** — the pole order at the first index outside `{2, 3}`. -/
theorem ordInfty_mulByNEndo_genX_five (h2 : (2 : F) ≠ 0) (h5 : (5 : F) ≠ 0) :
    ordInfty W (mulByNEndo 5
      (transcendental_xCoord_nsmul_genericPoint_of_intCast_ne_zero h2 (by simpa using h5))
      (genX W)) = -2 :=
  ordInfty_mulByNEndo_genX_of_ne_zero h2 (by simpa using h5) _

/-- **`[5]` fixes the point at infinity.** -/
theorem comapProjPointN_none_five (h2 : (2 : F) ≠ 0) (h5 : (5 : F) ≠ 0) :
    comapProjPointN 5
      (transcendental_xCoord_nsmul_genericPoint_of_intCast_ne_zero (W := W) h2 (by simpa using h5))
      (none : ProjPoint W) = none :=
  comapProjPointN_none_of_ne_zero h2 (by simpa using h5) _

/-- **`[5]` is unramified at the point at infinity.** -/
theorem ramificationIdxN_none_five (h2 : (2 : F) ≠ 0) (h5 : (5 : F) ≠ 0) :
    ramificationIdxN 5
      (transcendental_xCoord_nsmul_genericPoint_of_intCast_ne_zero (W := W) h2 (by simpa using h5))
      (none : ProjPoint W) = 1 :=
  ramificationIdxN_none_of_ne_zero h2 (by simpa using h5) _

/-! ### Non-vacuity: the statements have content on a real curve

Every theorem above carries `[IsDedekindDomain W.CoordinateRing]` and `comapProjPointN` is built
from a choice principle, so the chain is exhibited on `y² = x³ - x` over `ℚ` — the curve
`MulByTwoPlaceAtInfinity`, `MulByThreePlacePullback` and `MulByNComposition` all use — at `n = 12`,
an index at which none of the merged statements says anything.  ⚠️ The non-constancy hypothesis is
**produced** by `transcendental_xCoord_nsmul_of_smooth` rather than assumed: a statement whose
hypothesis could not be met would be vacuous. -/

section Nonvacuity

/-! The certificate curve `y² = x³ − x` is the shared `EllipticCurves.Fixture.y2EqX3SubX`, whose
single `[CharZero F]` instance also supplies `IsElliptic` here. -/

open EllipticCurves.Fixture

/-- ⚠️ `decide` does **not** close this: `Nat.primeFactors` goes through `Nat.primeFactorsList`,
whose `Decidable` instance gets stuck on `Nat.minFac`'s well-founded recursion. -/
private lemma exampleSmoothTwelvePlace : ∀ p ∈ Nat.primeFactors 12, p = 2 ∨ p = 3 := by
  intro p hp
  obtain ⟨hp1, hp2, -⟩ := Nat.mem_primeFactors.mp hp
  have hle : p ≤ 12 := Nat.le_of_dvd (by norm_num) hp2
  interval_cases p <;> revert hp1 hp2 <;> decide

example : IsDedekindDomain (y2EqX3SubX ℚ).CoordinateRing := inferInstance

example : comapProjPointN (W := y2EqX3SubX ℚ) 12
      (transcendental_xCoord_nsmul_of_smooth (by norm_num) (by norm_num) (by norm_num)
        exampleSmoothTwelvePlace) (none : ProjPoint (y2EqX3SubX ℚ)) = none :=
  comapProjPointN_none_of_smooth (W := y2EqX3SubX ℚ) (by norm_num) (by norm_num)
    (by norm_num) exampleSmoothTwelvePlace _

example : ramificationIdxN (W := y2EqX3SubX ℚ) 12
      (transcendental_xCoord_nsmul_of_smooth (by norm_num) (by norm_num) (by norm_num)
        exampleSmoothTwelvePlace) (none : ProjPoint (y2EqX3SubX ℚ)) = 1 :=
  ramificationIdxN_none_of_smooth (W := y2EqX3SubX ℚ) (by norm_num) (by norm_num)
    (by norm_num) exampleSmoothTwelvePlace _

example : ordInfty (y2EqX3SubX ℚ) (mulByNEndo 12
      (transcendental_xCoord_nsmul_of_smooth (W := y2EqX3SubX ℚ) (by norm_num) (by norm_num)
        (by norm_num) exampleSmoothTwelvePlace) (genX _)) = -2 :=
  ordInfty_mulByNEndo_genX_of_smooth (W := y2EqX3SubX ℚ) (by norm_num) (by norm_num)
    (by norm_num) exampleSmoothTwelvePlace _

/-! ⚠️ **The certificates for the general layer, and the load-bearing one is `n = 14`.**

`n = 5` shows only that `{2, 3}` was left; it is consistent with a `{2, 3, 5}`-parametrised package
and with an odd-`n` one.  `14 = 2 · 7` is **even and not `3`-smooth**, so it is reachable by no
`_of_smooth` statement in this file and by no odd-`n` statement anywhere, and these certificates can
come only from the `_of_ne_zero` layer by name.  ⚠️ Over `ℚ`, which is **not** algebraically closed
and where the whole `3`-smooth layer above is also stated — so the two layers are being compared on
the same base, not on bases chosen to flatter each one. -/

private lemma exampleFourteenPlace : (((14 : ℕ) : ℤ) : ℚ) ≠ 0 := by norm_num

private lemma exampleTranscendentalFourteenPlace :
    Transcendental ℚ ((14 : ℕ) • genericPoint (W := y2EqX3SubX ℚ)).xCoord :=
  transcendental_xCoord_nsmul_genericPoint_of_intCast_ne_zero (by norm_num) exampleFourteenPlace

/-- **`ordInfty ([14]∗ genX) = -2` on a genuine curve over `ℚ`**, at an index that is even and not
`3`-smooth. -/
example : ordInfty (y2EqX3SubX ℚ)
    (mulByNEndo 14 exampleTranscendentalFourteenPlace (genX _)) = -2 :=
  ordInfty_mulByNEndo_genX_of_ne_zero (by norm_num) exampleFourteenPlace _

/-- **`[14]` fixes the point at infinity, committed.**  ⚠️ The statement the module docstring's
opening paragraph declares unreachable by the pole order at general `n`; the paragraph is corrected
above and here is the index that falsifies its scope. -/
example : comapProjPointN (W := y2EqX3SubX ℚ) 14 exampleTranscendentalFourteenPlace
    (none : ProjPoint (y2EqX3SubX ℚ)) = none :=
  comapProjPointN_none_of_ne_zero (by norm_num) exampleFourteenPlace _

/-- **`[14]` is unramified at the point at infinity, committed.** -/
example : ramificationIdxN (W := y2EqX3SubX ℚ) 14 exampleTranscendentalFourteenPlace
    (none : ProjPoint (y2EqX3SubX ℚ)) = 1 :=
  ramificationIdxN_none_of_ne_zero (by norm_num) exampleFourteenPlace _

/-- **The order at infinity is a `[14]∗`-invariant, committed** — at `genY`, so that the statement
is exercised at an element other than the one its proof goes through. -/
example : ordInfty (y2EqX3SubX ℚ)
      (mulByNEndo 14 exampleTranscendentalFourteenPlace (genY _))
    = ordInfty (y2EqX3SubX ℚ) (genY (y2EqX3SubX ℚ)) :=
  ordInfty_mulByNEndo_of_ne_zero (by norm_num) exampleFourteenPlace _ genY_ne_zero

/-- **`n = 5` on the same curve**, through the named theorem rather than the general one. -/
example : comapProjPointN (W := y2EqX3SubX ℚ) 5
    (transcendental_xCoord_nsmul_genericPoint_of_intCast_ne_zero (by norm_num) (by norm_num))
    (none : ProjPoint (y2EqX3SubX ℚ)) = none :=
  comapProjPointN_none_five (by norm_num) (by norm_num)

end Nonvacuity

end CoordinateRing

end WeierstrassCurve.Affine
