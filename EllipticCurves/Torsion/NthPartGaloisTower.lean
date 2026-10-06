/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import EllipticCurves.Torsion.CoprimeAdjacent
import EllipticCurves.Torsion.HalvingExtension
import EllipticCurves.Torsion.NDivisionField
import EllipticCurves.Torsion.NsmulOrder
import EllipticCurves.Torsion.NthPartSeparable

/-!
# A finite Galois extension carrying both `E[n]` and an `n`-th part of a point, at EVERY index

Let `W` be an elliptic curve over a field `F` with `(2 : F) ≠ 0`, let `n` be an index with
`(n : F) ≠ 0`, and let `S = (x₀, y₀)` be an affine point of `W` with `Ψ₂Sq(x₀) ≠ 0` — that is, a
point which is **not** `2`-torsion.  The Galois-descent argument `#962` runs at a general index
needs **one** extension of `F` that is finite Galois and over which two things hold at once:
`#E[n] = n²`, and `S` is `n` times another point.  **This file builds it at every such `n`.**

It is the general-index analogue of `EllipticCurves.Torsion.HalvingGaloisTower` (`n = 2`) and
`EllipticCurves.Torsion.TriplingGaloisTower` (`n = 3`), and it is rung 4 of `#962`'s ladder:
`EllipticCurves.FunctionField.PullbackPrincipalityNGeneral` (rung 3) says of itself *"Constructing
the field over which the two hypotheses become theorems … is rung 4, and so is the unconditional
`…_general` headline it unlocks"*, and
`EllipticCurves.FunctionField.PullbackPrincipalityNTower` is that headline, spending exactly the
three statements this file's last three sections prove.

## The tower

```
F  ⊆  L₁ := nDivisionField W n                   -- #E[n] = n² here; separable and finite over F
   ⊆  M  := (W⁄L₁).nthPartField hn r₀            -- S is n-divisible here; separable, finite over L₁
   ⊆  N  := normalClosure F M (AlgebraicClosure M)
```

with `r₀ := algebraMap F L₁ x₀`, and `nthPartX W n x₀ := Φₙ − C x₀ · ΨSqₙ` the polynomial whose
roots are the `x`-coordinates of the points `P` with `x(n • P) = x₀`.

⚠️ **Three named floors are FIVE field extensions, and the count is BOUNDED — it is `5` at every
`n`.**  The diagram hides two of them: `nDivisionField W n`
(`EllipticCurves.Torsion.NDivisionField`) is itself a two-layer tower, a splitting field of
`Ψ₂SqRootPolyN` over a splitting field of `preΨₙ · Ψ₂Sq`, and `nthPartField` below is another
two-layer tower, the `y`-quadratic over the `n`-th-part polynomial's splitting field.  The full
chain is

```
F ⊆ (W.preΨ n * W.Ψ₂Sq).SplittingField ⊆ L₁ ⊆ (W⁄L₁).nthPartXField n r₀ ⊆ M ⊆ N.
```

⚠️⚠️ **That answers `#2296`'s acceptance question in the direction it did not expect.**  That row
predicted *"at a general `n` the layer count is not bounded, so the `n = 2` and `n = 3`
constructions cannot be transcribed … the general form has to be a construction by recursion or a
single splitting field of an explicitly described polynomial, not a chain."*  It **is** a chain, it
**is** a transcription of the `n = 3` file section for section, and the count is **five at every
index** — the same five `TriplingGaloisTower` reports at `n = 3` — because every floor of that
chain was already a splitting field of a polynomial that exists at every index.  The recursion the
row priced is not needed.

⚠️ **The depth cost the row priced did appear, once, and structuring the proof removed it rather
than a `set_option` absorbing it.**  `exists_nsmul_eq_nthPartField` written as a term applying
`exists_nsmul_eq_of_roots_baseChange` exceeds the **default** limit —
`(deterministic) timeout at 'whnf', maximum number of heartbeats (200000)` — and the same statement
with the two root hypotheses named in `have`s of their stated types elaborates in a few seconds.
⚠️ **Neither this file nor `PullbackPrincipalityNTower` carries any `set_option`**, which is the
course `PullbackPrincipalityThreeGeneral`'s own docstring recommends in terms (*"structuring the
proof removes the bump entirely"*), and the whole module elaborates in a few seconds.

## ⚠️⚠️ The hypothesis `Ψ₂Sq(x₀) ≠ 0`, which is a GENUINE exception and not an oversight

`Ψ₂Sq(x₀) ≠ 0` says exactly that `S` is not `2`-torsion, and it cannot be dropped.
`EllipticCurves.Torsion.NthPartSeparable`'s `separable_Φ_two_sub_C_mul_Ψ₂Sq_iff` is an **iff** at
`n = 2`: at a `2`-torsion `x₀` the `n`-th-part polynomial is `halvingX²`, a square of a degree-`2`
polynomial, hence not squarefree — so the first floor is not separable and the Galois closure has
nothing to close.  ⚠️ **A tower over a `2`-torsion `S` has to be built from that factorisation
instead, which is what `HalvingGaloisTower` does at `n = 2` and which nothing here attempts.**

⚠️ **At ODD `n` the hypothesis is FREE and is discharged rather than assumed**, by
`eval_Ψ₂Sq_ne_zero_of_eval_preΨ_eq_zero_of_odd` (`NthPartSeparable`): an `n`-torsion
`x`-coordinate at odd `n` is never a `2`-torsion one.  That is where
`PullbackPrincipalityNTower`'s `…_of_odd` pair comes from, and it is why this file states the
hypothesis rather than a parity one.

## ⚠️ What transposes from `n = 3` for free, and the ONE step that does not

**The `y`-quadratic transposes verbatim.**  `WeierstrassCurve.Affine.halvingY` is **index-free** —
the quadratic cut out by the Weierstrass equation at a given `x`, with discriminant `Ψ₂Sq.eval x` —
so `halvingY`, `degree_halvingY`, `separable_halvingY`, `equation_of_eval_halvingY_eq_zero` and
`eval_halvingY_baseChange` (`EllipticCurves.Torsion.HalvingExtension`) are consumed here unchanged,
exactly as at `n = 3`.  The separability of the first floor transposes too, being
`NthPartSeparable`'s general-index headline.

⚠️⚠️ **The step that does not transpose is `eval_Ψ₂Sq_ne_zero_of_root_nthPartX`**, and it is the
only new argument in the file.  At `n = 3` the corresponding
`Ψ₂Sq_eval_ne_zero_of_root_triplingX` is a **polynomial identity** — Mathlib's
`Φ₃ = X·Ψ₃² − preΨ₄·Ψ₂Sq`, so at a root `r` of `Ψ₂Sq` the tripling equation collapses to
`(r − x₀)·Ψ₃(r)² = 0` — and there is no such factorisation of `Φₙ` at a general index.  The general
route is a **point** argument with a parity split, and no step of it is the `n = 3` one:

* `ΨSqₙ(r) ≠ 0` first (`eval_ΨSq_ne_zero_of_root_nthPartX`), from `isCoprime_Φ_ΨSq`
  (`EllipticCurves.Torsion.CoprimeAdjacent`, at every `n : ℤ` over an elliptic `W` with
  `(2 : F) ≠ 0`) through `eval_Φ_ne_zero_of_isCoprime`.  ⚠️ So `x₀ = Φₙ(r)/ΨSqₙ(r)` is an honest
  quotient.
* If `Ψ₂Sq(r) = 0` then `Ψ₂Sq.eval r` is a square, so `exists_equation_of_isSquare`
  (`EllipticCurves.Torsion.ThreeTorsionStructure`, `(2 : F) ≠ 0` only) produces a point `P = (r, y)`
  of `W` **over `F`**; `Ψ₂Sq_eval_eq_sq` then gives `ψ₂(r, y) = 0` and
  `two_nsmul_eq_zero_of_ψ_two_evalEval_eq_zero` gives `2 • P = 0`.
* `hasXCoordFormula_of_two_ne_zero` (`EllipticCurves.Torsion.NsmulOrder`, at every `n` over a
  field with `[DecidableEq F]` and `(2 : F) ≠ 0`) makes `n • P` **affine** with `x`-coordinate
  `x₀`, so `n • P ≠ 0`.
* At **even** `n`, `2 • P = 0` forces `n • P = 0` — contradiction.  At **odd** `n` it forces
  `n • P = P`, so `x₀ = r` and `Ψ₂Sq(x₀) = 0` — contradiction with the hypothesis.

⚠️ **The parity split is in the proof and in no statement**: nothing in this file binds `Even n`,
`Odd n` or a parity of any kind, which a reader can check against the signatures.

## ⚠️ The divisibility half binds no root hypothesis, as at `n = 3` and unlike `n = 2`

`exists_nsmul_eq_nthPartField` and `exists_nsmul_eq_nthPartGaloisField` hold at **every** affine
point `(x₀, y₀)` of `W`, torsion or not; the roots of `nthPartX n x₀` solve `x(n • P) = x₀`
whatever `x₀` is.  ⚠️ **What `Ψ₂Sq(x₀) ≠ 0` buys is not the `n`-th part but the Galois property** —
`isGalois_nthPartXField`, `isGalois_nthPartField`, `isSeparable_nthPartField`,
`isSeparable_nthPartTower` and `isGalois_nthPartGaloisField` all bind it, and neither `Point`
statement does.  ⚠️ **It is NOT the case that the two halves have disjoint registers**, the tower
carrying the `n`-th part being the one built from the `Ψ₂Sq(x₀) ≠ 0` floors, so a caller wanting
both at once binds it anyway.  ⚠️ **That is a correction of the `n = 3` prose and not a
difference between the files**: `TriplingGaloisTower` reads `0` of `4` on the same two cells and
concludes *"disjoint"*, which over-reads it there as well.

## Main definitions

* `WeierstrassCurve.Affine.nthPartX` : `Φₙ − C x₀ · ΨSqₙ`, of degree `n²` at every `n ≠ 0`.
* `WeierstrassCurve.Affine.nthPartXField`, `nthPartYPoly`, `nthPartField` : the two sub-layers of
  the second floor, taken over an arbitrary base.
* `WeierstrassCurve.Affine.nthPartTower` : the second floor `M`, over the `n`-division field.
* `WeierstrassCurve.Affine.nthPartGaloisField` : the third floor `N`, the Galois extension a
  descent argument consumes.

## Main statements

**The three facts rung 3 consumes**, each over `N = W.nthPartGaloisField hn x₀` and each with every
hypothesis of its own statement named:

* `WeierstrassCurve.Affine.isGalois_nthPartGaloisField` and `finiteDimensional_nthPartGaloisField` :
  `N / F` is finite Galois, the first over an elliptic `W` with `(2 : F) ≠ 0`, `(n : F) ≠ 0`,
  `n ≠ 0` and `Ψ₂Sq(x₀) ≠ 0`, the second over **any** `W` over **any** field with no hypothesis
  at all beyond the `n ≠ 0` the type itself carries.
* `WeierstrassCurve.Affine.card_torsion_eq_sq_nthPartGaloisField` : `#E[n] = n²` over `N`, over an
  elliptic `W` with `(2 : F) ≠ 0`, `(n : F) ≠ 0` and `n ≠ 0`, and with `[DecidableEq N]` —
  ⚠️ **and no `Ψ₂Sq(x₀) ≠ 0`**, this being `NDivisionField`'s count transported along an
  `F`-algebra map.
* `WeierstrassCurve.Affine.exists_nsmul_eq_nthPartGaloisField` : `S` is `n` times a point of
  `W⁄N`, over an elliptic `W` with `(2 : F) ≠ 0`, `n ≠ 0`, `[DecidableEq N]` and `S = (x₀, y₀)` a
  nonsingular point of `W` — ⚠️ **and no `(n : F) ≠ 0` and no torsion, parity or `Ψ₂Sq` hypothesis
  on `x₀`**.

and two further public results:

* `WeierstrassCurve.Affine.eval_Ψ₂Sq_ne_zero_of_root_nthPartX` : at every `n`, over an elliptic `W`
  with `(2 : F) ≠ 0`, a root of `Φₙ − C x₀ · ΨSqₙ` is not a `2`-torsion `x`-coordinate as soon as
  `x₀` is not one.  **The file's one new argument.**
* `WeierstrassCurve.Affine.exists_root_nthPartX_of_nsmul_eq` : the converse — if `S` is already
  `n` times a point of `W` over `F`, then `Φₙ − C x₀ · ΨSqₙ` already has a root over `F`.  At every
  `n`, over an elliptic `W` with `(2 : F) ≠ 0`, `[DecidableEq F]` and `S = (x₀, y₀)` a nonsingular
  point of `W`, and **with no `(n : F) ≠ 0`, no `n ≠ 0` and no torsion, parity or `Ψ₂Sq` hypothesis
  on `x₀`**.

⚠️ **The census, source-declared and not read off the environment**: **42** public and **23** named
`private` declarations plus **2** anonymous `private` instances, of which **14** of the 42 bind
`[W.IsElliptic]` in the elaborated type and **5** bind a `DecidableEq`.  ⚠️ **The other 28 do not
bind `[W.IsElliptic]`**, including every `finiteDimensional_*` row, all four floors as types, all
four root-and-eval rows of the tower and `natDegree_nthPartX`.

## ⚠️ The `private` one-liners, and why they are copies

`algebraMap_ofNat_ne_zero'`, `algebraMap_natCast_ne_zero'` and `baseChange_baseChange_tower` are
restatements.  The first two are `private` in `EllipticCurves.Torsion.NDivisionField` and the
base-change identity is `private` in `EllipticCurves.Torsion.HalvingExtension`, both of which this
file imports, so promoting any of them would remove a copy.  ⚠️ **It would also re-key published
figures in files this round does not own** — `HalvingExtension`'s own docstring publishes **36**
public declarations, `HalvingGaloisTower`'s **17**, and `TriplingGaloisTower`'s **42** written by
hand, and those three figures are quoted from those docstrings rather than re-measured here — so it
is left as a separate change rather than folded in here.  ⚠️ `TriplingGaloisTower` makes exactly
the same copy and gives exactly this reason.

## ⚠️ What is *not* here

* **Nothing at a `2`-torsion `S`.**  See the hypothesis section above: it is an exception with a
  proof, not a gap.  **What happens there at even `n > 2` is not decided here.**
* **No claim that this supersedes `n = 2`.**  `PullbackPrincipalityTwoGeneral`'s headline is about
  a `2`-torsion `S` at `n = 2`, which this file's hypothesis excludes, and
  `HalvingGaloisTower` is not recovered below for that reason.  ⚠️ **Only the `n = 3` pair of
  `#2296`'s four numeral recoveries is reachable from here, and it is recovered in
  `PullbackPrincipalityNTower`; the `n = 2` pair is NOT, and is not claimed.**
* **No degree, irreducibility or Galois-group claim about any floor.**  `natDegree_nthPartX = n²`
  is a statement about the polynomial; nothing below says the first floor has degree `n²` over `F`,
  or that `nthPartX` is irreducible, or anything about `Gal(N/F)`.
* **No `README.md` retirement.**  `### What is formalised`'s *"four files … two at each of `n = 2`
  and `n = 3`"* and `PullbackPrincipalityThreeGeneral`'s *"`n = 3` only"* are both falsified by
  `PullbackPrincipalityNTower`; ⚠️ **retiring them is `#2296`'s own acceptance item and is
  deliberately left there** rather than widened into this unit.
* **Nothing is re-proved and no landed file is edited.**  The only change outside these two new
  modules is the two `import` lines `EllipticCurves.lean` needs.

## Non-vacuity

⚠️ **Both instantiations are at an EVEN index, and they are chosen to say opposite things.**  The
curve is `EllipticCurves.Fixture.y2AddYEqX3` at `R = ℚ` — `y² + y = x³`, with
`b₂ = b₄ = b₈ = 0` and `b₆ = 1`, so `Ψ₂Sq = 4X³ + 1` and `Ψ₂Sq(0) = 1 ≠ 0` — and the point is
`(0, 0)`, which is `3`-torsion.  It is `NthPartSeparable`'s own fixture and `x₀`, one rung up.

* **At `n = 4` the three facts hold and the tower provably buys NOTHING.**  `(0, 0)` is
  `3`-torsion, so `4 • (0, 0) = (0, 0)` over `ℚ` itself — `exists_nsmul_four_eq_y2AddYEqX3`.
  ⚠️ **This is published rather than omitted**: `HalvingGaloisTower` records that it could not
  certify its own fixture informative, and here the negative is not merely uncertified but
  **proved**, which is a stronger disclosure and a cheaper one.
* **At `n = 6` the tower is INFORMATIVE**: `not_exists_nsmul_six_eq_y2AddYEqX3` shows **no rational
  point of `y² + y = x³` is a sixth part of `(0, 0)`**, while
  `exists_nsmul_six_eq_fixtureNSix` produces one over `N`.  ⚠️ **And the route is this file's own
  general converse rather than the `n = 3` file's private lemma**: a sixth part is a third part of
  a doubling, `exists_root_nthPartX_of_nsmul_eq` at `n = 3` sends that to a rational root of
  `nthPartX 3 0 = Φ₃ = X⁹ − 24X⁶ + 3X³ + 1`, and that polynomial is monic over `ℤ` with constant
  coefficient `1`, so `IsIntegrallyClosed.isIntegral_iff` leaves only `±1`, which give `−19` and
  `−27`.
* ⚠️ **What the `n = 6` pair certifies is the CONCLUSION and not the type.**  No clause here says
  `ℚ ⊊ N`; descending a point along a surjective `algebraMap` is a different argument and is not
  made.  What is shown is that the statement this file delivers over `N` is **false over `ℚ`** on
  this curve, so the tower is not decoration.
* ⚠️ **The count half is inhabited and NOT certified informative**, at either index: this file does
  not show `#E[4] ≠ 16` or `#E[6] ≠ 36` over `ℚ` for this curve, the tree having no route from
  *`preΨₙ` does not split* to an upper bound on the count.

## References

* [J. H. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.8.
-/

open Polynomial IntermediateField

namespace WeierstrassCurve.Affine

variable {F : Type*} [Field F] {W : Affine F}

/-! ## The `n`-th-part polynomial -/

variable (W) in
/-- The `n`-th-part polynomial of `x₀`. -/
noncomputable def nthPartX (n : ℕ) (x₀ : F) : F[X] := W.Φ (n : ℤ) - C x₀ * W.ΨSq (n : ℤ)

/-- **The `n`-th-part polynomial has degree `n²`.**  `natDegree_Φ_sub_C_mul_ΨSq`
(`EllipticCurves.Torsion.NsmulSurjective`) with no hypothesis on `(n : F)`. -/
theorem natDegree_nthPartX {n : ℕ} (hn : n ≠ 0) (x₀ : F) :
    (W.nthPartX n x₀).natDegree = n ^ 2 :=
  natDegree_Φ_sub_C_mul_ΨSq hn x₀

/-- The `n`-th-part polynomial is nonzero at every `n ≠ 0`. -/
theorem nthPartX_ne_zero {n : ℕ} (hn : n ≠ 0) (x₀ : F) : W.nthPartX n x₀ ≠ 0 := by
  intro h
  have hd := natDegree_nthPartX (W := W) hn x₀
  rw [h, natDegree_zero] at hd
  exact pow_ne_zero 2 hn hd.symm

/-- The `n`-th-part polynomial has `degree` `n²`, in `WithBot ℕ`. -/
theorem degree_nthPartX {n : ℕ} (hn : n ≠ 0) (x₀ : F) :
    (W.nthPartX n x₀).degree = (n ^ 2 : ℕ) := by
  rw [degree_eq_natDegree (nthPartX_ne_zero hn x₀), natDegree_nthPartX hn]

/-- The `n`-th-part polynomial is not constant — the form `rootOfSplits` consumes. -/
theorem degree_nthPartX_ne_zero {n : ℕ} (hn : n ≠ 0) (x₀ : F) :
    (W.nthPartX n x₀).degree ≠ 0 := by
  intro h
  have h0 : (W.nthPartX n x₀).natDegree = 0 :=
    natDegree_eq_zero_iff_degree_le_zero.mpr (le_of_eq h)
  rw [natDegree_nthPartX hn] at h0
  exact pow_ne_zero 2 hn h0

/-- The `n`-th-part polynomial evaluated, with the `C` stripped. -/
theorem eval_nthPartX (n : ℕ) (x₀ x : F) :
    (W.nthPartX n x₀).eval x = (W.Φ (n : ℤ)).eval x - x₀ * (W.ΨSq (n : ℤ)).eval x := by
  rw [nthPartX, eval_sub, eval_mul, eval_C]

/-- **The `n`-th-part polynomial is separable**, at every `n` over an elliptic `W` with
`(2 : F) ≠ 0`, `(n : F) ≠ 0` and `Ψ₂Sq(x₀) ≠ 0`.  This is
`EllipticCurves.Torsion.NthPartSeparable`'s headline
`separable_Φ_sub_C_mul_ΨSq_of_eval_Ψ₂Sq_ne_zero`, which is why this file can exist at a general
index at all; ⚠️ **no parity and no torsion hypothesis on `x₀`**. -/
theorem separable_nthPartX [W.IsElliptic] (h2 : (2 : F) ≠ 0) {n : ℕ} (hnF : (n : F) ≠ 0)
    {x₀ : F} (hx₀ : W.Ψ₂Sq.eval x₀ ≠ 0) : (W.nthPartX n x₀).Separable :=
  separable_Φ_sub_C_mul_ΨSq_of_eval_Ψ₂Sq_ne_zero h2 hnF hx₀

/-- The `n`-th-part polynomial commutes with base change. -/
theorem map_nthPartX {K : Type*} [Field K] (f : F →+* K) (n : ℕ) (x₀ : F) :
    (W.map f).nthPartX n (f x₀) = (W.nthPartX n x₀).map f := by
  rw [nthPartX, nthPartX, Polynomial.map_sub, Polynomial.map_mul, map_C,
    show (W.map f).Φ (n : ℤ) = (W.Φ (n : ℤ)).map f from WeierstrassCurve.map_Φ ..,
    show (W.map f).ΨSq (n : ℤ) = (W.ΨSq (n : ℤ)).map f from WeierstrassCurve.map_ΨSq ..]

/-! ## A root of the `n`-th-part polynomial is neither `n`-torsion nor `2`-torsion -/

theorem eval_ΨSq_ne_zero_of_root_nthPartX [W.IsElliptic] (h2 : (2 : F) ≠ 0) {n : ℕ} {x₀ r : F}
    (hr : (W.nthPartX n x₀).eval r = 0) : (W.ΨSq (n : ℤ)).eval r ≠ 0 := by
  intro h0
  refine eval_Φ_ne_zero_of_isCoprime (isCoprime_Φ_ΨSq h2 (n : ℤ)) h0 ?_
  rw [eval_nthPartX, h0, mul_zero, sub_zero] at hr
  exact hr

/-- **A root of the `n`-th-part polynomial of a non-`2`-torsion `x₀` is itself not a `2`-torsion
`x`-coordinate**, at every `n` over an elliptic `W` with `(2 : F) ≠ 0`.

⚠️⚠️ **This is the file's one new argument and it is NOT the `n = 3` one transposed.**  At `n = 3`,
`Ψ₂Sq_eval_ne_zero_of_root_triplingX` (`EllipticCurves.Torsion.TriplingGaloisTower`) is a
polynomial identity read off `Φ₃ = X·Ψ₃² − preΨ₄·Ψ₂Sq`, and `Φₙ` has no such factorisation at a
general index.  The route here is a point argument: a root of `Ψ₂Sq` carries a `2`-torsion point
`P = (r, y)` **over `F`** (the discriminant being `0`, hence a square), `ΨSqₙ(r) ≠ 0` makes `n • P`
affine with `x`-coordinate `x₀`, and then `2 • P = 0` contradicts that at even `n` by killing
`n • P` and at odd `n` by forcing `x₀ = r`.

⚠️ **The parity split is here and in no statement of this file.** -/
theorem eval_Ψ₂Sq_ne_zero_of_root_nthPartX [W.IsElliptic] (h2 : (2 : F) ≠ 0) {n : ℕ} {x₀ : F}
    (hx₀ : W.Ψ₂Sq.eval x₀ ≠ 0) {r : F} (hr : (W.nthPartX n x₀).eval r = 0) :
    W.Ψ₂Sq.eval r ≠ 0 := by
  classical
  intro h0
  -- A point `P = (r, y)` of `W` above `r` exists, because `Ψ₂Sq.eval r = 0` is a square.
  obtain ⟨y, hy⟩ := exists_equation_of_isSquare (W := W) h2 (x := r) ⟨0, by rw [h0, mul_zero]⟩
  have hns : W.Nonsingular r y := equation_iff_nonsingular.mp hy
  -- `P` is `2`-torsion.
  have htwo : ((2 : ℕ) • Point.some r y hns : W.Point) = 0 := by
    refine two_nsmul_eq_zero_of_ψ_two_evalEval_eq_zero hns ?_
    rw [ψ_two_evalEval]
    have hsq : (2 * y + W.a₁ * r + W.a₃) ^ 2 = 0 := by rw [← Ψ₂Sq_eval_eq_sq hy]; exact h0
    exact pow_eq_zero_iff two_ne_zero |>.mp hsq
  -- `n • P` is affine with `x`-coordinate `x₀`.
  have hΨ : (W.ΨSq (n : ℤ)).eval r ≠ 0 := eval_ΨSq_ne_zero_of_root_nthPartX h2 hr
  obtain ⟨y', h', hP⟩ := hasXCoordFormula_of_two_ne_zero h2 n hns hΨ
  have hx : (W.Φ (n : ℤ)).eval r / (W.ΨSq (n : ℤ)).eval r = x₀ := by
    rw [eval_nthPartX, sub_eq_zero] at hr
    rw [hr, mul_div_assoc, div_self hΨ, mul_one]
  -- Either `n` is even and `n • P = 0`, or `n` is odd and `n • P = P`, and both are absurd.
  rcases Nat.even_or_odd n with ⟨m, hm⟩ | ⟨m, hm⟩
  · refine Point.some_ne_zero h' ?_
    rw [← hP, hm, ← two_mul, mul_comm, ← smul_smul, htwo, smul_zero]
  · have hself : (n • Point.some r y hns : W.Point) = Point.some r y hns := by
      rw [hm, add_nsmul, mul_comm, ← smul_smul, htwo, smul_zero, one_nsmul, zero_add]
    have heq := hself.symm.trans hP
    rw [Point.some.injEq] at heq
    exact hx₀ (by rw [← hx, ← heq.1]; exact h0)

/-! ## Base change of the root hypothesis -/

private lemma algebraMap_ofNat_ne_zero' {L : Type*} [Field L] [Algebra F L] (n : ℕ)
    [n.AtLeastTwo] (h : (OfNat.ofNat n : F) ≠ 0) : (OfNat.ofNat n : L) ≠ 0 := by
  rw [← map_ofNat (algebraMap F L) n, ne_eq, map_eq_zero]
  exact h

private lemma algebraMap_natCast_ne_zero' {L : Type*} [Field L] [Algebra F L] {n : ℕ}
    (h : (n : F) ≠ 0) : (n : L) ≠ 0 := by
  rw [← map_natCast (algebraMap F L) n, ne_eq, map_eq_zero]
  exact h

/-- **`Ψ₂Sq(x₀) ≠ 0` goes up any field extension**, `algebraMap` being injective. -/
theorem eval_Ψ₂Sq_ne_zero_baseChange {L : Type*} [Field L] [Algebra F L] {x₀ : F}
    (hx₀ : W.Ψ₂Sq.eval x₀ ≠ 0) : (W⁄L).Ψ₂Sq.eval (algebraMap F L x₀) ≠ 0 := by
  rw [show (W⁄L).Ψ₂Sq = W.Ψ₂Sq.map (algebraMap F L) from map_Ψ₂Sq .., eval_map, eval₂_at_apply,
    ne_eq, map_eq_zero]
  exact hx₀

/-! ## The first floor: adjoining the `n`-th-part `x`-coordinate -/

/-- A splitting field of the `n`-th-part polynomial. -/
noncomputable abbrev nthPartXField (W : Affine F) (n : ℕ) (x₀ : F) : Type _ :=
  (W.nthPartX n x₀).SplittingField

/-- A root of the `n`-th-part polynomial in its splitting field. -/
noncomputable def nthPartXRoot (W : Affine F) {n : ℕ} (hn : n ≠ 0) (x₀ : F) :
    W.nthPartXField n x₀ :=
  rootOfSplits (IsSplittingField.splits (W.nthPartXField n x₀) (W.nthPartX n x₀))
    (by rw [Polynomial.degree_map]; exact degree_nthPartX_ne_zero hn x₀)

/-- **The adjoined element is a root of the `n`-th-part polynomial over the first floor.** -/
theorem eval_nthPartXRoot {W : Affine F} {n : ℕ} (hn : n ≠ 0) (x₀ : F) :
    ((W⁄(W.nthPartXField n x₀)).nthPartX n
      (algebraMap F (W.nthPartXField n x₀) x₀)).eval (W.nthPartXRoot hn x₀) = 0 := by
  rw [show (W⁄(W.nthPartXField n x₀)) = W.map (algebraMap F (W.nthPartXField n x₀)) from rfl,
    map_nthPartX]
  exact eval_rootOfSplits _ _

section FirstFloor

variable {W : Affine F} {n : ℕ} {x₀ : F}

/-- **The `x`-layer is Galois over `F`**, being a splitting field of a separable polynomial. -/
theorem isGalois_nthPartXField [W.IsElliptic] (h2 : (2 : F) ≠ 0) (hnF : (n : F) ≠ 0)
    (hx₀ : W.Ψ₂Sq.eval x₀ ≠ 0) : IsGalois F (W.nthPartXField n x₀) :=
  IsGalois.of_separable_splitting_field (p := W.nthPartX n x₀) (separable_nthPartX h2 hnF hx₀)

/-- **The `x`-layer is finite over `F`**, with no hypothesis at all. -/
theorem finiteDimensional_nthPartXField : FiniteDimensional F (W.nthPartXField n x₀) :=
  IsSplittingField.finiteDimensional _ (W.nthPartX n x₀)

/-- **`Ψ₂Sq` does not vanish at the adjoined root**, which is what makes the `y`-quadratic above it
separable.  The previous section's new argument, read over the first floor. -/
theorem Ψ₂Sq_eval_nthPartXRoot_ne_zero [W.IsElliptic] (h2 : (2 : F) ≠ 0) (hn : n ≠ 0)
    (hx₀ : W.Ψ₂Sq.eval x₀ ≠ 0) :
    (W⁄(W.nthPartXField n x₀)).Ψ₂Sq.eval (W.nthPartXRoot hn x₀) ≠ 0 := by
  haveI : (W⁄(W.nthPartXField n x₀)).IsElliptic :=
    inferInstanceAs (W.map (algebraMap F (W.nthPartXField n x₀))).IsElliptic
  exact eval_Ψ₂Sq_ne_zero_of_root_nthPartX (algebraMap_ofNat_ne_zero' 2 h2)
    (eval_Ψ₂Sq_ne_zero_baseChange hx₀) (eval_nthPartXRoot hn x₀)

end FirstFloor

/-! ## The second floor: adjoining the `y`-coordinate above it -/

/-- The `y`-quadratic above the chosen `n`-th-part `x`-coordinate, over the first floor. -/
noncomputable def nthPartYPoly (W : Affine F) {n : ℕ} (hn : n ≠ 0) (x₀ : F) :
    (W.nthPartXField n x₀)[X] :=
  (W⁄(W.nthPartXField n x₀)).halvingY (W.nthPartXRoot hn x₀)

/-- **The `n`-th-part field** of the point at `x₀`. -/
noncomputable abbrev nthPartField (W : Affine F) {n : ℕ} (hn : n ≠ 0) (x₀ : F) : Type _ :=
  (W.nthPartYPoly hn x₀).SplittingField

/-- A root of the `y`-quadratic in the `n`-th-part field. -/
noncomputable def nthPartYRoot (W : Affine F) {n : ℕ} (hn : n ≠ 0) (x₀ : F) :
    W.nthPartField hn x₀ :=
  rootOfSplits (IsSplittingField.splits (W.nthPartField hn x₀) (W.nthPartYPoly hn x₀))
    (by rw [Polynomial.degree_map, nthPartYPoly, degree_halvingY]; exact two_ne_zero)

/-- **The adjoined element is a root of the `y`-quadratic over the first floor.** -/
theorem eval_nthPartYRoot (W : Affine F) {n : ℕ} (hn : n ≠ 0) (x₀ : F) :
    ((W.nthPartYPoly hn x₀).map
      (algebraMap (W.nthPartXField n x₀) (W.nthPartField hn x₀))).eval
      (W.nthPartYRoot hn x₀) = 0 :=
  eval_rootOfSplits _ _

section SecondFloor

variable {W : Affine F} {n : ℕ} {x₀ : F}

/-- **The `y`-layer is Galois over the `x`-layer**, the `y`-quadratic being separable there. -/
theorem isGalois_nthPartField [W.IsElliptic] (h2 : (2 : F) ≠ 0) {hn : n ≠ 0}
    (hx₀ : W.Ψ₂Sq.eval x₀ ≠ 0) :
    IsGalois (W.nthPartXField n x₀) (W.nthPartField hn x₀) :=
  IsGalois.of_separable_splitting_field (p := W.nthPartYPoly hn x₀)
    (separable_halvingY (Ψ₂Sq_eval_nthPartXRoot_ne_zero h2 hn hx₀))

/-- **The `n`-th-part field is separable over `F`**, separability being transitive where
normality is not — which is why there is a third floor at all. -/
theorem isSeparable_nthPartField [W.IsElliptic] (h2 : (2 : F) ≠ 0) (hnF : (n : F) ≠ 0)
    {hn : n ≠ 0} (hx₀ : W.Ψ₂Sq.eval x₀ ≠ 0) :
    Algebra.IsSeparable F (W.nthPartField hn x₀) := by
  haveI := isGalois_nthPartXField h2 hnF hx₀
  haveI := isGalois_nthPartField (W := W) (hn := hn) h2 hx₀
  exact Algebra.IsSeparable.trans F (W.nthPartXField n x₀) (W.nthPartField hn x₀)

/-- **The `n`-th-part field is finite over `F`**, each layer being a splitting field. -/
theorem finiteDimensional_nthPartField {hn : n ≠ 0} :
    FiniteDimensional F (W.nthPartField hn x₀) := by
  haveI : FiniteDimensional F (W.nthPartXField n x₀) := finiteDimensional_nthPartXField
  haveI : FiniteDimensional (W.nthPartXField n x₀) (W.nthPartField hn x₀) :=
    IsSplittingField.finiteDimensional _ (W.nthPartYPoly hn x₀)
  exact FiniteDimensional.trans F (W.nthPartXField n x₀) (W.nthPartField hn x₀)

end SecondFloor

/-! ## The `n`-th part, over the `n`-th-part field -/

section NthPart

variable {W : Affine F} {n : ℕ} {x₀ : F}

private lemma baseChange_baseChange_tower (W : Affine F) (L₁ : Type*) [Field L₁] [Algebra F L₁]
    (L : Type*) [Field L] [Algebra F L] [Algebra L₁ L] [IsScalarTower F L₁ L] :
    ((W⁄L₁)⁄L) = (W⁄L) :=
  WeierstrassCurve.map_baseChange (R := F) W (IsScalarTower.toAlgHom F L₁ L)

section Bridge

variable {L₁ L : Type*} [Field L₁] [Field L] [Algebra F L₁] [Algebra F L] [Algebra L₁ L]
  [IsScalarTower F L₁ L]

/-- A root of the `n`-th-part polynomial over `L₁` is one over any extension of `L₁`. -/
theorem eval_nthPartX_baseChange {r : L₁}
    (hr : ((W⁄L₁).nthPartX n (algebraMap F L₁ x₀)).eval r = 0) :
    ((W⁄L).nthPartX n (algebraMap F L x₀)).eval (algebraMap L₁ L r) = 0 := by
  rw [← baseChange_baseChange_tower W L₁ L,
    show ((W⁄L₁)⁄L) = (W⁄L₁).map (algebraMap L₁ L) from rfl,
    IsScalarTower.algebraMap_apply F L₁ L x₀, map_nthPartX, eval_map, ← Polynomial.aeval_def,
    Polynomial.aeval_algebraMap_apply, Polynomial.aeval_def, ← eval_map, ← map_nthPartX]
  simp [Algebra.algebraMap_self, hr]

end Bridge

/-- **A point is `n` times another point over any extension reached from a field carrying both
roots.** -/
theorem exists_nsmul_eq_of_roots_baseChange {M L : Type*} [Field M] [Field L] [Algebra F M]
    [Algebra F L] [Algebra M L] [IsScalarTower F M L] [DecidableEq L] [W.IsElliptic]
    (h2 : (2 : F) ≠ 0) {y₀ : F} (hQ : W.Nonsingular x₀ y₀)
    {r s : M} (hr : ((W⁄M).nthPartX n (algebraMap F M x₀)).eval r = 0)
    (hs : ((W⁄M).halvingY r).eval s = 0) :
    ∃ P : (W⁄L).Point, n • P = Point.some (algebraMap F L x₀) (algebraMap F L y₀)
      ((W.map_nonsingular (algebraMap F L).injective x₀ y₀).mpr hQ) := by
  haveI : (W⁄L).IsElliptic := inferInstanceAs (W.map (algebraMap F L)).IsElliptic
  have h2' : (2 : L) ≠ 0 := algebraMap_ofNat_ne_zero' 2 h2
  have hrL : ((W⁄L).nthPartX n (algebraMap F L x₀)).eval (algebraMap M L r) = 0 :=
    eval_nthPartX_baseChange hr
  have hsL : ((W⁄L).halvingY (algebraMap M L r)).eval (algebraMap M L s) = 0 := by
    refine eval_halvingY_baseChange ?_
    rw [Polynomial.eval_map, Polynomial.eval₂_at_apply, hs, map_zero]
  refine exists_nsmul_eq_some_of_hasXCoordFormula_of_root
    (fun x hx => eval_Φ_ne_zero_of_isCoprime (isCoprime_Φ_ΨSq h2' (n : ℤ)) hx)
    (hasXCoordFormula_of_two_ne_zero h2' n) _
    (equation_of_eval_halvingY_eq_zero hsL) ?_
  rw [eval_nthPartX, sub_eq_zero] at hrL
  exact hrL

/-- **A point is `n` times another point over its `n`-th-part field.** -/
theorem exists_nsmul_eq_nthPartField {hn : n ≠ 0} [DecidableEq (W.nthPartField hn x₀)]
    [W.IsElliptic] (h2 : (2 : F) ≠ 0) {y₀ : F} (hQ : W.Nonsingular x₀ y₀) :
    ∃ P : (W⁄(W.nthPartField hn x₀)).Point,
      n • P = Point.some (algebraMap F (W.nthPartField hn x₀) x₀)
        (algebraMap F (W.nthPartField hn x₀) y₀)
        ((W.map_nonsingular (algebraMap F (W.nthPartField hn x₀)).injective x₀ y₀).mpr hQ) := by
  haveI : (W⁄(W.nthPartField hn x₀)).IsElliptic :=
    inferInstanceAs (W.map (algebraMap F (W.nthPartField hn x₀))).IsElliptic
  have h2' : (2 : W.nthPartField hn x₀) ≠ 0 := algebraMap_ofNat_ne_zero' 2 h2
  have hr : ((W⁄(W.nthPartField hn x₀)).nthPartX n
      (algebraMap F (W.nthPartField hn x₀) x₀)).eval
      (algebraMap (W.nthPartXField n x₀) (W.nthPartField hn x₀) (W.nthPartXRoot hn x₀)) = 0 :=
    eval_nthPartX_baseChange (eval_nthPartXRoot hn x₀)
  have hy : ((W⁄(W.nthPartField hn x₀)).halvingY
      (algebraMap (W.nthPartXField n x₀) (W.nthPartField hn x₀) (W.nthPartXRoot hn x₀))).eval
      (W.nthPartYRoot hn x₀) = 0 :=
    eval_halvingY_baseChange (eval_nthPartYRoot W hn x₀)
  refine exists_nsmul_eq_some_of_hasXCoordFormula_of_root
    (fun x hx => eval_Φ_ne_zero_of_isCoprime (isCoprime_Φ_ΨSq h2' (n : ℤ)) hx)
    (hasXCoordFormula_of_two_ne_zero h2' n) _
    (equation_of_eval_halvingY_eq_zero hy) ?_
  rw [eval_nthPartX, sub_eq_zero] at hr
  exact hr

end NthPart

/-! ## The three-floor tower -/

variable (W) in
/-- **The second floor `M`**: the `n`-th-part field of `x₀`, taken over the `n`-division field. -/
noncomputable abbrev nthPartTower {n : ℕ} (hn : n ≠ 0) (x₀ : F) : Type _ :=
  (W⁄(nDivisionField W n)).nthPartField hn (algebraMap F (nDivisionField W n) x₀)

/-- `F ⊆ L₁ ⊆ M` is a tower. -/
instance instIsScalarTowerNthPartTower {n : ℕ} (hn : n ≠ 0) (x₀ : F) :
    IsScalarTower F (nDivisionField W n) (W.nthPartTower hn x₀) := by
  refine IsScalarTower.of_algebraMap_eq fun a => ?_
  rw [IsScalarTower.algebraMap_apply F
      ((W⁄(nDivisionField W n)).nthPartXField n (algebraMap F (nDivisionField W n) x₀))
      (W.nthPartTower hn x₀),
    IsScalarTower.algebraMap_apply F (nDivisionField W n)
      ((W⁄(nDivisionField W n)).nthPartXField n (algebraMap F (nDivisionField W n) x₀)),
    ← IsScalarTower.algebraMap_apply (nDivisionField W n)
      ((W⁄(nDivisionField W n)).nthPartXField n (algebraMap F (nDivisionField W n) x₀))
      (W.nthPartTower hn x₀)]

/-- The `n`-th-part `x`-coordinate, as an element of the second floor `M`. -/
noncomputable def nthPartTowerXRoot (W : Affine F) {n : ℕ} (hn : n ≠ 0) (x₀ : F) :
    W.nthPartTower hn x₀ :=
  algebraMap
    ((W⁄(nDivisionField W n)).nthPartXField n (algebraMap F (nDivisionField W n) x₀))
    (W.nthPartTower hn x₀)
    ((W⁄(nDivisionField W n)).nthPartXRoot hn (algebraMap F (nDivisionField W n) x₀))

/-- The `y`-coordinate above it, which is where the second floor is adjoined. -/
noncomputable def nthPartTowerYRoot (W : Affine F) {n : ℕ} (hn : n ≠ 0) (x₀ : F) :
    W.nthPartTower hn x₀ :=
  (W⁄(nDivisionField W n)).nthPartYRoot hn (algebraMap F (nDivisionField W n) x₀)

/-- **The `n`-th-part polynomial of `x₀` has a root over `M`**, stated over `(W⁄M)`. -/
theorem eval_nthPartTowerXRoot {n : ℕ} (hn : n ≠ 0) (x₀ : F) :
    ((W⁄(W.nthPartTower hn x₀)).nthPartX n
      (algebraMap F (W.nthPartTower hn x₀) x₀)).eval (W.nthPartTowerXRoot hn x₀) = 0 := by
  have h : (((W⁄(nDivisionField W n))⁄(W.nthPartTower hn x₀)).nthPartX n
      (algebraMap (nDivisionField W n) (W.nthPartTower hn x₀)
        (algebraMap F (nDivisionField W n) x₀))).eval (W.nthPartTowerXRoot hn x₀) = 0 :=
    eval_nthPartX_baseChange (eval_nthPartXRoot _ _)
  rwa [baseChange_baseChange_tower W (nDivisionField W n) (W.nthPartTower hn x₀),
    ← IsScalarTower.algebraMap_apply F (nDivisionField W n) (W.nthPartTower hn x₀) x₀] at h

/-- **The `y`-quadratic above that root has a root over `M`**, in the same form. -/
theorem eval_nthPartTowerYRoot {n : ℕ} (hn : n ≠ 0) (x₀ : F) :
    ((W⁄(W.nthPartTower hn x₀)).halvingY (W.nthPartTowerXRoot hn x₀)).eval
      (W.nthPartTowerYRoot hn x₀) = 0 := by
  have h : (((W⁄(nDivisionField W n))⁄(W.nthPartTower hn x₀)).halvingY
      (W.nthPartTowerXRoot hn x₀)).eval (W.nthPartTowerYRoot hn x₀) = 0 :=
    eval_halvingY_baseChange (eval_nthPartYRoot _ _ _)
  rwa [baseChange_baseChange_tower W (nDivisionField W n) (W.nthPartTower hn x₀)] at h

/-! ## The second floor is finite and separable over `F` -/

variable [W.IsElliptic]

/-- **`M / F` is separable.** -/
theorem isSeparable_nthPartTower (h2 : (2 : F) ≠ 0) {n : ℕ} (hnF : (n : F) ≠ 0) {hn : n ≠ 0}
    {x₀ : F} (hx₀ : W.Ψ₂Sq.eval x₀ ≠ 0) :
    Algebra.IsSeparable F (W.nthPartTower hn x₀) := by
  haveI : (W⁄(nDivisionField W n)).IsElliptic :=
    inferInstanceAs (W.map (algebraMap F (nDivisionField W n))).IsElliptic
  haveI := isSeparable_nDivisionField W n h2 hnF
  haveI : Algebra.IsSeparable (nDivisionField W n) (W.nthPartTower hn x₀) :=
    isSeparable_nthPartField (algebraMap_ofNat_ne_zero' 2 h2) (algebraMap_natCast_ne_zero' hnF)
      (hn := hn) (eval_Ψ₂Sq_ne_zero_baseChange hx₀)
  exact Algebra.IsSeparable.trans F (nDivisionField W n) (W.nthPartTower hn x₀)

omit [W.IsElliptic] in
/-- **`M / F` is finite**, each floor being a splitting field of a polynomial. -/
theorem finiteDimensional_nthPartTower {n : ℕ} {hn : n ≠ 0} {x₀ : F} :
    FiniteDimensional F (W.nthPartTower hn x₀) := by
  haveI : FiniteDimensional F (nDivisionField W n) := finiteDimensional_nDivisionField W n
  haveI : FiniteDimensional (nDivisionField W n) (W.nthPartTower hn x₀) :=
    finiteDimensional_nthPartField
  exact FiniteDimensional.trans F (nDivisionField W n) (W.nthPartTower hn x₀)

/-! ## The third floor: the Galois closure -/

variable (W) in
/-- **The third floor `N`**: the Galois closure of the tower over `F`. -/
noncomputable abbrev nthPartGaloisField {n : ℕ} (hn : n ≠ 0) (x₀ : F) : Type _ :=
  normalClosure F (W.nthPartTower hn x₀) (AlgebraicClosure (W.nthPartTower hn x₀))

/-- **`N / F` is Galois.** -/
theorem isGalois_nthPartGaloisField (h2 : (2 : F) ≠ 0) {n : ℕ} (hnF : (n : F) ≠ 0) {hn : n ≠ 0}
    {x₀ : F} (hx₀ : W.Ψ₂Sq.eval x₀ ≠ 0) : IsGalois F (W.nthPartGaloisField hn x₀) := by
  haveI := isSeparable_nthPartTower h2 hnF (hn := hn) hx₀
  exact _root_.isGalois_normalClosure_of_isSeparable F (W.nthPartTower hn x₀)

omit [W.IsElliptic] in
/-- **`N / F` is finite.** -/
theorem finiteDimensional_nthPartGaloisField {n : ℕ} {hn : n ≠ 0} {x₀ : F} :
    FiniteDimensional F (W.nthPartGaloisField hn x₀) := by
  haveI : FiniteDimensional F (W.nthPartTower hn x₀) := finiteDimensional_nthPartTower
  infer_instance

/-! ## `#E[n] = n²` over the third floor -/

variable (W) in
/-- The composite `F`-algebra hom `L₁ → N`. -/
noncomputable def nDivisionFieldToNthPartGalois {n : ℕ} (hn : n ≠ 0) (x₀ : F) :
    nDivisionField W n →ₐ[F] W.nthPartGaloisField hn x₀ :=
  (IsScalarTower.toAlgHom F (W.nthPartTower hn x₀) (W.nthPartGaloisField hn x₀)).comp
    (IsScalarTower.toAlgHom F (nDivisionField W n) (W.nthPartTower hn x₀))

/-- **`#E[n] = n²` over `N`.** -/
theorem card_torsion_eq_sq_nthPartGaloisField (h2 : (2 : F) ≠ 0) {n : ℕ} (hnF : (n : F) ≠ 0)
    {hn : n ≠ 0} (x₀ : F) [DecidableEq (W.nthPartGaloisField hn x₀)] :
    Nat.card ((W⁄(W.nthPartGaloisField hn x₀)).torsion n) = n ^ 2 :=
  card_torsion_eq_sq_of_algHom h2 hnF (nDivisionFieldToNthPartGalois W hn x₀)
    (splits_preΨ_tower (W := W) (n := n) (L₂ := nDivisionField W n)
      (W.preΨ (n : ℤ) * W.Ψ₂Sq).SplittingField hnF h2)
    (splits_Ψ₂Sq_tower (W := W) (n := n) (L₂ := nDivisionField W n)
      (W.preΨ (n : ℤ) * W.Ψ₂Sq).SplittingField hnF h2)
    fun _ hz =>
      isSquare_Ψ₂Sq_eval_tower_n (W := W) (n := n) (L₂ := nDivisionField W n)
        (W.preΨ (n : ℤ) * W.Ψ₂Sq).SplittingField hnF h2 hz

/-! ## The `n`-th part over the third floor -/

/-- **`S` is `n` times another point over `N`.** -/
theorem exists_nsmul_eq_nthPartGaloisField (h2 : (2 : F) ≠ 0) {n : ℕ} {hn : n ≠ 0} {x₀ y₀ : F}
    (hQ : W.Nonsingular x₀ y₀) [DecidableEq (W.nthPartGaloisField hn x₀)] :
    ∃ P : (W⁄(W.nthPartGaloisField hn x₀)).Point,
      n • P = Point.some (algebraMap F (W.nthPartGaloisField hn x₀) x₀)
        (algebraMap F (W.nthPartGaloisField hn x₀) y₀)
        ((W.map_nonsingular (algebraMap F (W.nthPartGaloisField hn x₀)).injective x₀ y₀).mpr hQ) :=
  exists_nsmul_eq_of_roots_baseChange h2 hQ (eval_nthPartTowerXRoot hn x₀)
    (eval_nthPartTowerYRoot hn x₀)

/-! ## The converse: when the tower buys nothing -/

section Converse

variable {W : Affine F}

/-- **If `S` is already `n` times a point of `W` over `F`, the `n`-th-part polynomial already has a
root over `F`.** -/
theorem exists_root_nthPartX_of_nsmul_eq [DecidableEq F] [W.IsElliptic] (h2 : (2 : F) ≠ 0)
    {n : ℕ} {x₀ y₀ : F} (hQ : W.Nonsingular x₀ y₀) {P : W.Point}
    (hP : n • P = Point.some x₀ y₀ hQ) : ∃ r : F, (W.nthPartX n x₀).eval r = 0 := by
  match P with
  | .zero =>
    rw [show (Point.zero : W.Point) = 0 from rfl, smul_zero] at hP
    exact absurd hP (by simp)
  | .some r s h =>
    by_cases hΨ : (W.ΨSq (n : ℤ)).eval r = 0
    · have hzero : (n • Point.some r s h : W.Point) = 0 :=
        (nsmul_eq_zero_iff_ψ_evalEval_eq_zero_of_isElliptic h2 h n).mpr
          (pow_eq_zero_iff two_ne_zero |>.mp (by rw [ψ_sq_evalEval h.left]; exact hΨ))
      rw [hzero] at hP
      simp at hP
    · obtain ⟨y', h', hform⟩ := hasXCoordFormula_of_two_ne_zero h2 n h hΨ
      rw [hform, Point.some.injEq] at hP
      refine ⟨r, ?_⟩
      rw [eval_nthPartX, ← hP.1]
      field_simp
      ring

end Converse

/-! ## Non-vacuity, at two EVEN indices -/

section Nonvacuity

open EllipticCurves.Fixture

private lemma four_ne_zero' : (4 : ℕ) ≠ 0 := by decide

private lemma six_ne_zero' : (6 : ℕ) ≠ 0 := by decide

/-- **`(0, 0)` lies on `y² + y = x³`.** -/
private lemma nonsingular_zero_y2AddYEqX3 : (y2AddYEqX3 ℚ).Nonsingular 0 0 := by
  refine equation_iff_nonsingular.mp ?_
  rw [Affine.equation_iff]; norm_num [y2AddYEqX3]

/-- **`Ψ₂Sq = 4X³ + 1` on `y² + y = x³`**, from `b₂ = b₄ = 0` and `b₆ = 1`. -/
private lemma Ψ₂Sq_y2AddYEqX3 : (y2AddYEqX3 ℚ).Ψ₂Sq = C 4 * X ^ 3 + 1 := by
  simp only [WeierstrassCurve.Ψ₂Sq, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, y2AddYEqX3]
  norm_num

/-- `Ψ₂Sq(0) = 1 ≠ 0`, so `(0, 0)` is not a `2`-torsion point. -/
private lemma eval_Ψ₂Sq_zero_ne_y2AddYEqX3 : (y2AddYEqX3 ℚ).Ψ₂Sq.eval 0 ≠ 0 := by
  rw [Ψ₂Sq_y2AddYEqX3]; norm_num

/-- The third floor `N` at `n = 4` on the fixture. -/
private noncomputable abbrev fixtureNFour : Type :=
  (y2AddYEqX3 ℚ).nthPartGaloisField four_ne_zero' 0

/-- The third floor `N` at `n = 6` on the fixture. -/
private noncomputable abbrev fixtureNSix : Type :=
  (y2AddYEqX3 ℚ).nthPartGaloisField six_ne_zero' 0

private noncomputable instance : DecidableEq fixtureNFour := Classical.decEq _

private noncomputable instance : DecidableEq fixtureNSix := Classical.decEq _

/-! ### `n = 4`, where the tower is inhabited and provably buys NOTHING -/

/-- **`N / ℚ` is finite Galois** at `n = 4` on the fixture. -/
private theorem isGalois_fixtureNFour : IsGalois ℚ fixtureNFour :=
  isGalois_nthPartGaloisField (by norm_num) (by norm_num) eval_Ψ₂Sq_zero_ne_y2AddYEqX3

private theorem finiteDimensional_fixtureNFour : FiniteDimensional ℚ fixtureNFour :=
  finiteDimensional_nthPartGaloisField

/-- **`#E[4] = 16` over `N`** at `n = 4` on the fixture. -/
private theorem card_torsion_four_fixtureNFour :
    Nat.card (((y2AddYEqX3 ℚ)⁄fixtureNFour).torsion 4) = 16 :=
  card_torsion_eq_sq_nthPartGaloisField (by norm_num) (by norm_num) 0

/-- **`(0, 0)` is four times a point of the curve over `N`** on the fixture. -/
private theorem exists_nsmul_four_eq_fixtureNFour :
    ∃ P : ((y2AddYEqX3 ℚ)⁄fixtureNFour).Point,
      (4 : ℕ) • P = Point.some (algebraMap ℚ fixtureNFour 0) (algebraMap ℚ fixtureNFour 0)
        (((y2AddYEqX3 ℚ).map_nonsingular
          (algebraMap ℚ fixtureNFour).injective 0 0).mpr nonsingular_zero_y2AddYEqX3) :=
  exists_nsmul_eq_nthPartGaloisField (by norm_num) nonsingular_zero_y2AddYEqX3

/-- `3 • (0, 0) = 0` on `y² + y = x³`: the fixture point is `3`-torsion. -/
private lemma nsmul_three_zero_y2AddYEqX3 :
    ((3 : ℕ) • Point.some 0 0 nonsingular_zero_y2AddYEqX3 : (y2AddYEqX3 ℚ).Point) = 0 := by
  refine (nsmul_eq_zero_iff_eval_preΨ_eq_zero (by norm_num) (by decide)
    nonsingular_zero_y2AddYEqX3).mpr ?_
  rw [show ((3 : ℕ) : ℤ) = (3 : ℤ) by norm_num, WeierstrassCurve.preΨ_three]
  simp only [WeierstrassCurve.Ψ₃, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆,
    WeierstrassCurve.b₈, y2AddYEqX3]
  norm_num

/-- ⚠️ **At `n = 4` the tower buys nothing, and that is PROVED rather than left open**: `(0, 0)` is
`3`-torsion, so `4 • (0, 0) = (0, 0)` over `ℚ` itself. -/
private theorem exists_nsmul_four_eq_y2AddYEqX3 :
    ∃ P : (y2AddYEqX3 ℚ).Point,
      (4 : ℕ) • P = Point.some 0 0 nonsingular_zero_y2AddYEqX3 :=
  ⟨Point.some 0 0 nonsingular_zero_y2AddYEqX3, by
    rw [show (4 : ℕ) = 3 + 1 from rfl, add_nsmul, nsmul_three_zero_y2AddYEqX3, one_nsmul,
      zero_add]⟩

/-! ### `n = 6`, where the tower is INFORMATIVE -/

/-- **`N / ℚ` is finite Galois** at `n = 6` on the fixture. -/
private theorem isGalois_fixtureNSix : IsGalois ℚ fixtureNSix :=
  isGalois_nthPartGaloisField (by norm_num) (by norm_num) eval_Ψ₂Sq_zero_ne_y2AddYEqX3

private theorem finiteDimensional_fixtureNSix : FiniteDimensional ℚ fixtureNSix :=
  finiteDimensional_nthPartGaloisField

/-- **`#E[6] = 36` over `N`** at `n = 6` on the fixture. -/
private theorem card_torsion_six_fixtureNSix :
    Nat.card (((y2AddYEqX3 ℚ)⁄fixtureNSix).torsion 6) = 36 :=
  card_torsion_eq_sq_nthPartGaloisField (by norm_num) (by norm_num) 0

/-- **`(0, 0)` is six times a point of the curve over `N`** on the fixture. -/
private theorem exists_nsmul_six_eq_fixtureNSix :
    ∃ P : ((y2AddYEqX3 ℚ)⁄fixtureNSix).Point,
      (6 : ℕ) • P = Point.some (algebraMap ℚ fixtureNSix 0) (algebraMap ℚ fixtureNSix 0)
        (((y2AddYEqX3 ℚ).map_nonsingular
          (algebraMap ℚ fixtureNSix).injective 0 0).mpr nonsingular_zero_y2AddYEqX3) :=
  exists_nsmul_eq_nthPartGaloisField (by norm_num) nonsingular_zero_y2AddYEqX3

/-- **The `3`-rd-part polynomial of `(0, 0)` on `y² + y = x³` is `X⁹ − 24X⁶ + 3X³ + 1`.** -/
private lemma eval_nthPartX_three_zero_y2AddYEqX3 (x : ℚ) :
    ((y2AddYEqX3 ℚ).nthPartX 3 0).eval x = x ^ 9 - 24 * x ^ 6 + 3 * x ^ 3 + 1 := by
  rw [eval_nthPartX, show ((3 : ℕ) : ℤ) = (3 : ℤ) by norm_num, Φ_three_eval]
  simp only [preΨ₄_eval, WeierstrassCurve.Ψ₃, WeierstrassCurve.Ψ₂Sq, WeierstrassCurve.b₂,
    WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈, y2AddYEqX3]
  simp only [eval_add, eval_mul, eval_pow, eval_X, eval_C, eval_ofNat]
  ring

/-- **The `3`-rd-part polynomial of `(0, 0)` on `y² + y = x³` has no rational root.** -/
private theorem eval_nthPartX_three_zero_y2AddYEqX3_ne_zero (x : ℚ) :
    ((y2AddYEqX3 ℚ).nthPartX 3 0).eval x ≠ 0 := by
  rw [eval_nthPartX_three_zero_y2AddYEqX3]
  intro h
  have hmonic : (X ^ 9 - 24 * X ^ 6 + 3 * X ^ 3 + 1 : ℤ[X]).Monic := by monicity!
  have hint : IsIntegral ℤ x := by
    refine ⟨X ^ 9 - 24 * X ^ 6 + 3 * X ^ 3 + 1, hmonic, ?_⟩
    simp only [eval₂_add, eval₂_sub, eval₂_mul, eval₂_pow, eval₂_X, eval₂_ofNat, eval₂_one]
    linear_combination h
  obtain ⟨d, hd⟩ := IsIntegrallyClosed.isIntegral_iff.mp hint
  subst hd
  have hdz : d ^ 9 - 24 * d ^ 6 + 3 * d ^ 3 + 1 = 0 := by
    exact_mod_cast (by simpa using h : (d : ℚ) ^ 9 - 24 * (d : ℚ) ^ 6 + 3 * (d : ℚ) ^ 3 + 1 = 0)
  have hdvd : d ∣ 1 := ⟨-(d ^ 8 - 24 * d ^ 5 + 3 * d ^ 2), by linarith [hdz]⟩
  rcases Int.isUnit_iff.mp (isUnit_of_dvd_one hdvd) with rfl | rfl <;> norm_num at hdz

/-- ⚠️⚠️ **No rational point of `y² + y = x³` is a SIXTH part of `(0, 0)`**, while
`exists_nsmul_six_eq_fixtureNSix` produces one over `N`: a sixth part is a third part of a doubling,
and this file's own general converse at `n = 3` sends that to a rational root of
`X⁹ − 24X⁶ + 3X³ + 1`. -/
private theorem not_exists_nsmul_six_eq_y2AddYEqX3 :
    ¬ ∃ P : (y2AddYEqX3 ℚ).Point,
      (6 : ℕ) • P = Point.some 0 0 nonsingular_zero_y2AddYEqX3 := by
  rintro ⟨P, hP⟩
  obtain ⟨r, hr⟩ := exists_root_nthPartX_of_nsmul_eq (W := y2AddYEqX3 ℚ) (n := 3) (by norm_num)
    nonsingular_zero_y2AddYEqX3 (P := (2 : ℕ) • P)
    (by rw [smul_smul, show (3 : ℕ) * 2 = 6 from rfl]; exact hP)
  exact eval_nthPartX_three_zero_y2AddYEqX3_ne_zero r hr

end Nonvacuity

end WeierstrassCurve.Affine
