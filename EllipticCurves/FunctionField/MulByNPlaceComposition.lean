/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import EllipticCurves.Fixtures
import EllipticCurves.FunctionField.MulByNComposition
import EllipticCurves.FunctionField.MulByNPlacePullback
import EllipticCurves.FunctionField.MulByThreePlacePullback

/-!
# `[n]` fixes the point at infinity, at every `3`-smooth `n`

`EllipticCurves.FunctionField.MulByNPlacePullback` contracts a place of the projective curve along
`[n]∗` (`comapProjPointN`) for every `n` at which `[n]` is non-constant, and closes its *"rungs that
do not survive"* section with

> Consequently `comapProjPointN … none = none` (*"`[n]` fixes the point at infinity"*) is **also**
> absent: `comapProjPointTwo_none` is proved from the pole order.

That is right about the *merged route*, which runs `divisorProj_mulByTwoEndo_apply` backwards
against `ordInfty ([2]∗ genX) = -2` — and `ordInfty ([n]∗ genX) < 0` is genuinely unavailable at
general `n`, because `mulByNEndo_genX` rewrites to `x(n • 𝒫)`, about which the group law says only
that it satisfies the Weierstrass equation, and `x(𝒫 + T)` for a constant `T ≠ O` satisfies the same
equation with no pole at infinity.

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
`ramificationIdxN_two` — so `e_∞ = 1` at every `3`-smooth `n` and hence
`ordInfty ([n]∗ f) = ordInfty f`, in particular `ordInfty ([n]∗ genX) = -2`.  That is `#670`'s
statement at every `3`-smooth `n`.

⚠️ **It does not extend, and `MulByNPlacePullback`'s argument that it is false at general `n` is
untouched.**  Over `F̄` of characteristic `p > 2` the transcendence hypothesis holds at `n = p`,
`[p]` is inseparable, and `ordInfty ([p]∗ genX)` is `-2p` or `-2p²`.  Everything below carries
`(2 : F) ≠ 0` **and** `(3 : F) ≠ 0` together with `3`-smoothness of `n`, which is exactly the
hypothesis that keeps `p ∤ n`.  Nothing here says `e_∞ = 1` at any `n` with a prime factor other
than `2` or `3`, and the argument gives no route to one: the composition law manufactures no new
prime.

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
  `[n]` fixes the point at infinity at every `3`-smooth `n`;
* `…ramificationIdxN_two_pow_mul_three_pow_none` and `…ramificationIdxN_none_of_smooth` — and it is
  unramified there;
* `…ordInfty_mulByNEndo_of_comapProjPointN_none` — `ordInfty ([n]∗ f) = e_∞ · ordInfty f`, from
  `none ↦ none` alone and with no smoothness hypothesis;
* `…ordInfty_mulByNEndo_of_smooth` and `…ordInfty_mulByNEndo_genX_of_smooth` — the same with
  `e_∞ = 1` supplied, and `ordInfty ([n]∗ genX) = -2` at every `3`-smooth `n`.

## What is *not* here

* **No new theorem about places.**  Every statement is the merged general-`φ` place machinery
  (`EllipticCurves.FunctionField.PlacePullback`) applied to `mulByNEndo`, exactly as
  `MulByNPlacePullback` says of itself; the content is the composition law and the two merged prime
  inputs.
* **Nothing at `n = 5`, and nothing in characteristic `2` or `3`.**  See the second warning above.
* **No residue degree — *here*.**  ⚠️ This bullet used to say that `#701` and `#1046`, *"the
  residue-degree companions at the point at infinity"*, **are absent**.  Both clauses were loose.
  `#701` and `#1046` are the *fibre sums* `∑_{p ↦ q} e_p · f_p = deg`, not the value of `f` at one
  place; ⚠️ **their general-`n` form was recorded here as still open, and is not**: it is
  `EllipticCurves.FunctionField.MulByNInertia` (`#1221`).  The value at one place — `f_∞ = 1` —
  is `EllipticCurves.FunctionField.MulByNResidueDegree` (`#1225`), and ⚠️ it holds at **every** `n`
  and does not consume this file: it needs no fibre statement, no `3`-smoothness and no hypothesis
  on `F`.  What is true of *this* file is only that it proves nothing about residue degrees.
* **No `ωₙ`, no coprimality, no elliptic net.**  `#404` (closed), `#1184` (open) and Ward
  (`#260`, closed) are unused.

⚠️ **Both of the things that sentence names are now closed, and it is an independence claim
rather than a gate.**  `#404`'s on-curve identity is
`WeierstrassCurve.Affine.equation_div_of_ψ_ne_zero` (`EllipticCurves.Torsion.OmegaCrux`, PR #557, at
every index over every commutative ring) and Ward's theorem (`#260`) is
`WeierstrassCurve.Affine.ψ_isEllipticNet` (`EllipticCurves.Torsion.WardHalving`), unconditional.
The claim below is unchanged in force: this file uses neither.  ⚠️ What is still open in this
neighbourhood is `#251`, the identification of `(Φₙ/ΨSqₙ, ωₙ/ψₙ³)` with `n • P`; see
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

/-- **`[n]` fixes the point at infinity at every `3`-smooth `n ≠ 0`**: `comapProjPointN n h
none = none`.

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

/-- **`[n]` is unramified at the point at infinity at every `3`-smooth `n ≠ 0`.**

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

/-- **`ordInfty ([n]∗ f) = ordInfty f` at every `3`-smooth `n ≠ 0`** — the order at infinity is
preserved outright, both factors of the transport being trivial. -/
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

end Nonvacuity

end CoordinateRing

end WeierstrassCurve.Affine
