/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import EllipticCurves.Fixtures
import EllipticCurves.FunctionField.MulByNIntegral
import EllipticCurves.FunctionField.PullbackDivisor

/-!
# The contraction of places and the divisor pullback along `[n]∗`, for every `n`

`EllipticCurves.FunctionField.PlacePullback` and
`EllipticCurves.FunctionField.PullbackDivisor` build the contraction `comapProjPoint`, the
ramification index `ramificationIdx`, the order transport `divisorProj_comp_apply` and the divisor
pullback `pullbackDivisor` **for an arbitrary `F`-fixing endomorphism `φ` of `F(W)` over which
`F(W)` is integral**.  Only the `[2]∗` and `[3]∗` instantiations were available, because only there
were the two hypotheses

```
hφF   : ∀ c : F, φ (algebraMap F F(W) c) = algebraMap F F(W) c
hφint : ∀ z : F(W), φ.IsIntegralElem z
```

discharged.  `EllipticCurves.FunctionField.MulByNIntegral` discharges the second one at every `n` at
which `[n]` is non-constant, and the first is the merged `mulByNEndo_algebraMap_base`.  This file is
the resulting instantiation: **`[n]∗` on places and on divisors, for every `n`.**

⚠️ **Nothing here is a new theorem about places.**  Every statement below is a merged general-`φ`
theorem applied to `mulByNEndo n hn`; the content is entirely in the hypothesis discharge, and the
route was `#1169`'s question — *which of the `#639` rungs survive at general `n` on `mulByNEndo`
alone*.  The two that do are these.

## The two rungs that do not survive, and are therefore absent

⚠️ **`[F(W) : [n]∗F(W)] = n²` is not here** (`#682` at `n = 2`, `#775` at `n = 3`).  What does
survive is that the degree is **finite** — `module_finite_mulByNEndoFieldRange`,
`EllipticCurves.FunctionField.MulByNIntegral`, from non-constancy alone.

⚠️ **The *value* is gated at a general `n`, but not at every `n`.**  `#1213`
(`EllipticCurves.FunctionField.MulByNComposition`) proves `[m · n]∗ = [m]∗ ∘ [n]∗` from the group
law and multiplies the two merged degrees up:
`[F(W) : [n]∗F(W)] = n²` holds for every **`3`-smooth** `n`, with none of the three gates below and
no division polynomial in the argument.  What the three gates stand between is `3`-smooth and
*general* `n` — the first index they are needed at is `n = 5`.  Everything in the rest of this
paragraph is about that general-`n` statement and is unaffected.

`finrank_mulByTwoFieldRange` reads the value off the tower `F(W) ⊇ F(x) ⊇ F(x ∘ [2])`, and that
tower needs
(i) `x ∘ [n] ∈ F(x)`, which at `n = 2` is `doublingRatFunc`, an element of `RatFunc F` written down
from `Φ₂/Ψ₂Sq`, and (ii) the reduced degrees of `Φ n` and `ΨSq n` with the coprimality that makes
*reduced* legitimate.

⚠️ **(i) is discharged.**  `x(-P) = x(P)`, so `x(n • 𝒫)` is fixed by the hyperelliptic involution
`negYAlgEquiv`, and `F(x)` **is** the fixed field of that involution:
`ratFuncRange_eq_fixedField_negYGroup`, `EllipticCurves.FunctionField.NegYGalois`, over an arbitrary
field and in every characteristic.  The consequence `(n • 𝒫).xCoord ∈ F(x)` for every `n`, with its
`RatFunc F` name `nMulRatFunc`, is `EllipticCurves.FunctionField.MulByNXCoordRatFunc`.  ⚠️ **This
paragraph originally called (i) *"the cheapest visible follow-up"* and said the fixed field did not
exist**; it had checked `NegYInvolution`, where it indeed is not, and missed `NegYGalois`, where it
was already merged.

⚠️ **And the tower itself is no longer index-specific.**
`EllipticCurves.FunctionField.MulByNDegreeTower` proves

```
[F(W) : [n]∗F(W)] = [F(x) : F(nMulRatFunc W n)]        for every n,
```

with no coprimality, no `(n : F) ≠ 0`, no written-down fraction and no `[IsAlgClosed F]`.  The
index-free tower it instantiates is `finrank_fieldRange_eq_finrank_adjoin`
(`EllipticCurves.FunctionField.MulByTwoDegree`), and the `finrank_mulByTwoFieldRange` and
`finrank_mulByThreeFieldRange` this paragraph names are **proved by** it — two lines each — rather
than merely being instances of it.  ⚠️ So what is gated is **not the tower**: it is the *number on
the right-hand side*, and that is exactly the three items below.  Nothing in this paragraph's list
has been discharged by that file, and it proves no degree at any `n` outside `{2, 3}`.

⚠️ **What (ii) still needs is *not* the degrees.**  `natDegree_Φ` and `natDegree_ΨSq` are
**Mathlib**'s at general `n` (`Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Degree`,
the first over any nontrivial ring, the second under `(n : F) ≠ 0`), and `MulByThreePlacePullback`
and `MulByThreeDegree` already close their degree computations with both of them at general index.
Three other things were missing.  **First**, the identification of `nMulRatFunc W n` *as* the
fraction `Φₙ/ΨSqₙ`, which is `#251`: `nMulRatFunc` is produced by an inverse isomorphism,
so `RatFunc.finrank_eq_max_natDegree` has no numerator and no denominator to read off it — being an
element of `F(x)` is not being a *written-down* rational function.  ⚠️ **This one is discharged**:
`nMulRatFunc_eq_ΦDivΨSq` (`EllipticCurves.FunctionField.MulByNXCoordFormula`) proves it at every `n`
with `((n : ℤ) : F) ≠ 0` over a field of characteristic `≠ 2`, from
`WeierstrassCurve.Affine.hasXCoordFormula_of_two_ne_zero` applied to the generic point.  **Second**,
`IsCoprime (W.Φ n) (W.ΨSq n)` at general `n`, which is `#1184`:
`EllipticCurves.DivisionPolynomial.Coprime` has it at `n = 2` (`isCoprime_Φ_two_Ψ₂Sq`, `#681`,
merged) by a Bézout certificate against `Δ²`, and at `n = 3` by the congruence
`preΨ₄² ≡ Ψ₂Sq⁴ (mod Ψ₃)` reducing to that same `n = 2` certificate rather than to a new one — that
file computes no second `Δ²` identity — and its own `## What is *not* here` **used to call** the
general case *"a much larger induction"*.  ⚠️ **`#1184` narrowed that bullet and this citation of
it was not refreshed**; the bullet's current form is the next sentence here.  ⚠️ After PR #446 the
statement that induction is owed on is
`IsCoprime (W.ΨSq (n + 1) * W.ΨSq (n - 1)) (W.ΨSq n)` and no longer mentions `Φ`:
`isCoprime_Φ_ΨSq_of_isCoprime_ΨSq_adjacent` reduces this **Second** item to that one
unconditionally, over an arbitrary commutative ring.  **Third**, `natDegree_ΨSq`'s `(n : F) ≠ 0`,
the same side condition the rung-4 paragraph below shows `mulByNEndo` does not carry.

⚠️ **The first and second are no longer missing**, though not here: all three modules named below
are **import-incomparable** with this file — none is in its import closure and none has it in
theirs — so nothing here can consume them.  The fraction is `nMulRatFunc_eq_ΦDivΨSq`
(`EllipticCurves.FunctionField.MulByNXCoordFormula`); the coprimality is
`WeierstrassCurve.Affine.isCoprime_ΨSq_adjacent` (`EllipticCurves.Torsion.CoprimeAdjacent`), at
every `n : ℤ` for an elliptic curve over a field of characteristic `≠ 2` — the root route this
paragraph's second item had no proof of.  `EllipticCurves.FunctionField.MulByNDegreeGeneral`
composes them, so `[F(W) : [n]∗F(W)] = n²` at general `n` is owed the **third** item alone,
`(n : F) ≠ 0`, and nothing else.  ⚠️ The three-item list above is kept as the record of what this
file's own rung 3 does not do; it is no longer a list of open problems.

⚠️ **That pair is paid on both halves, and `(n : F) ≠ 0` is what is left.**  PR #557 proved the
on-curve identity for `(Φₙ/ΨSqₙ, ωₙ/ψₙ³)` at every index over every commutative ring
(`WeierstrassCurve.Affine.equation_div_of_ψ_ne_zero`, `EllipticCurves.Torsion.OmegaCrux`) — that was
`#404`, and it says only that those coordinates lie on the curve.  Identifying the `x`-coordinate
with the group-law multiple `n • P` is `#251`, and it is **closed**:
`WeierstrassCurve.Affine.hasXCoordFormula_of_two_ne_zero`
(`EllipticCurves.Torsion.NsmulOrder`) at every index over any field with `(2 : F) ≠ 0`, and in
function-field form `nMulRatFunc_eq_ΦDivΨSq`
(`EllipticCurves.FunctionField.MulByNXCoordFormula`) at every `n` with `((n : ℤ) : F) ≠ 0`.  ⚠️
**`#1184` has since been discharged over a field** —
`WeierstrassCurve.Affine.isCoprime_ΨSq_adjacent` (`EllipticCurves.Torsion.CoprimeAdjacent`) at every
`n : ℤ` for an elliptic curve of characteristic `≠ 2` — so `[F(W) : [n]∗F(W)] = n²` at general `n`
(`EllipticCurves.FunctionField.MulByNDegreeGeneral`) is owed `((n : ℤ) : F) ≠ 0` and nothing else
beyond the `(2 : F) ≠ 0` and `[W.IsElliptic]` that this whole paragraph already carries.  ⚠️ The
arbitrary-**ring** form that `EllipticCurves.DivisionPolynomial.Coprime` states is still open.
⚠️ And the `y`-half — `ωₙ/(2ψₙ³)` as `y(n • P)` — **is closed too, at every index**:
`nsmul_eq_some_omegaY_of_ΨSq_ne_zero` (`EllipticCurves.Torsion.NsmulYPeriodic`, PR #579), under the
same `ΨSqₙ(x) ≠ 0` and `(2 : F) ≠ 0` the `x`-half asks.  ⚠️ So the whole *pair* is available at
every index, and the `#251` bullets on the Weil-pairing front no longer name an open gate.  ⚠️ None
of `EllipticCurves.Torsion.NsmulOrder`, `EllipticCurves.FunctionField.MulByNXCoordFormula`,
`EllipticCurves.Torsion.CoprimeAdjacent` or `EllipticCurves.FunctionField.MulByNDegreeGeneral` is in
this file's import closure and none is added: all four names are cited, not consumed.  The
two-reading account is `EllipticCurves.FunctionField.MulByNPullback`.

⚠️ **`ordInfty ([n]∗ genX) = -2` is not here** (`#670` at `n = 2`), and it is available in two
places outside this file: at every `3`-smooth `n` as
`EllipticCurves.FunctionField.MulByNPlaceComposition.ordInfty_mulByNEndo_genX_of_smooth`, reached by
composition; and — ⚠️ **this is what corrects the paragraph below** — at every `n` with
`((n : ℤ) : F) ≠ 0` as that file's `ordInfty_mulByNEndo_genX_of_ne_zero`, reached by **exactly the
degree count this paragraph is about**.

⚠️ **This paragraph used to call that a "negative result, not a gap" at general `n`, and to give the
reason as follows.**  `ordInfty_mulByTwoEndo_genX`
(`EllipticCurves.FunctionField.MulByTwoPlaceAtInfinity`) and `ord_mulByTwoEndo_genX_neg`
(`EllipticCurves.FunctionField.MulByTwoFibreInfinity`) both open with `rw [mulByTwoEndo_genX h2, …]`
and then count degrees of `Φ₂` and `Ψ₂Sq`; `mulByNEndo_genX` rewrites instead to `x(n • 𝒫)`, about
which *the group law* says only that it satisfies the Weierstrass equation, and ⚠️ **that alone does
pin nothing at infinity** — `x(𝒫 + T)` for a fixed `T ≠ O` satisfies the same equation and has *no*
pole there.  ⚠️ **Every sentence of that is true and the conclusion drawn from it was not**: the
group law is not the only input available.  `xCoord_nsmul_genericPoint'`
(`EllipticCurves.FunctionField.MulByNXCoordFormula`, `#251`) is
`x(n • 𝒫) = Φₙ(genX)/ΨSqₙ(genX)` at every `n` with `((n : ℤ) : F) ≠ 0`, and against Mathlib's
`natDegree_Φ = n²` and `natDegree_ΨSq = n² - 1` it makes the `n = 2` proof transpose
**verbatim**.
⚠️ Note where that name appears in this very file: four paragraphs above, in the list of names that
are *"cited, not consumed"*.  It is now consumed, one file over.

⚠️ **What survives, and it is the part with the mathematics in it**: `k` really is unpinned by the
equation alone, and at an `n` divisible by the characteristic it is genuinely not `1` — the next
paragraph, which this one used to introduce, is unchanged and is what makes `(n : F) ≠ 0`
necessary rather than merely convenient.

⚠️ **`k = 1` is false at general `n`.**  `mulByNEndo n hn` carries no hypothesis on `(n : F)`, and
none is available *to it*: over `F̄` of characteristic `p > 2` the transcendence hypothesis at
`n = p` is discharged by `exists_nsmul_ne_zero_of_isAlgClosed`, which asks only for `(2 : F) ≠ 0`.
There `[p]` is inseparable, hence ramified over the point at infinity — `e = p` in the ordinary
case and `p²` in the supersingular one, the fibre having `p` points and `1` point respectively
against `∑ e_P = deg [p] = p²` — so `ordInfty ([p]∗ genX)` is `-2p` or `-2p²`.

⚠️ **A general-`n` rung 4 needs `(n : F) ≠ 0`, and this sentence used to add "on top of the missing
degree count" — the degree count was never missing.**  `natDegree_Φ` and `natDegree_ΨSq` are
Mathlib's at every index (the latter under the same `(n : F) ≠ 0`), and
`EllipticCurves.FunctionField.MulByNDegreeTower` has consumed both since `#1213`.  `(n : F) ≠ 0` is
the *whole* of what was needed, and with it the count is done — see
`EllipticCurves.FunctionField.MulByNPlaceComposition.ordInfty_mulByNEndo_genX_of_ne_zero`.  ⚠️ The
argument for `k ≠ 1` in characteristic `p` is Silverman *AEC* II.2.12, III.4.10 and V.3.1 read
together; it is stated here as the reason nothing is landed **at `p ∣ n`** and it is **not
formalised** in this tree.

Consequently `comapProjPointN … none = none` (*"`[n]` fixes the point at infinity"*) is **also**
absent *from this file*: `comapProjPointTwo_none` is proved from the pole order, and so are the
fibre-sum identities `#701` and `#1046`.  ⚠️ **Absent from this file, and present in the tree at
every `n` with `(2 : F) ≠ 0` and `((n : ℤ) : F) ≠ 0`** — `comapProjPointN_none_of_ne_zero` and
`ramificationIdxN_none_of_ne_zero` (`EllipticCurves.FunctionField.MulByNPlaceComposition`), by the
pole order and with the `n = 2` proof transposed unchanged.

⚠️ **This paragraph used to conclude that the statement is absent from the tree, and that is now
false at every `3`-smooth `n`.**  `EllipticCurves.FunctionField.MulByNPlaceComposition` (`#1214`)
proves it — and the index `e_∞ = 1`, and `ordInfty ([n]∗ genX) = -2` — with **no pole order**:
`[m · n]∗ = [m]∗ ∘ [n]∗` (`EllipticCurves.FunctionField.MulByNComposition`, `#1213`) transports
through the contravariant `comapProjPoint` to a composition law for the contraction, and the merged
`comapProjPointTwo_none` / `comapProjPointThree_none` compose up.  The reasoning above is not
refuted: it is a correct account of why the *pole-order* route stops at `{2, 3}`, and it is why the
statement at general `n` — and everything in the `k = 1` paragraph, which is about characteristic
`p` and so about an `n` divisible by `p` — still stands.  ⚠️ `#701` and `#1046` are **not**
delivered at `3`-smooth `n` by that file.  ⚠️ **The clause that followed said they are not
delivered at any `n` either, and that is now false of the tree**: the fibre sum
`∑_{p ↦ q} e_p · f_p = [F(W) : [n]∗F(W)]` at general `n` is
`EllipticCurves.FunctionField.MulByNInertia` (`#1221`) — at every `n` in characteristic zero, and
with the right-hand side evaluated to `n²` at every `3`-smooth `n`.  ⚠️ What is delivered at
**every** `n` with no hypothesis on `F` at all is the relative residue degree at the point at
infinity: `f_∞ = 1`, `EllipticCurves.FunctionField.MulByNResidueDegree` (`#1225`), by an argument
uniform in the endomorphism that needs neither the pole order nor the fibre statement.  The two
local invariants at infinity are not alike — `e_∞ = 1` is `3`-smooth-only and false in general,
`f_∞ = 1` is free.

⚠️ **`comapProjPointN_none_of_ne_zero`, `ramificationIdxN_none_of_ne_zero` and
`ramificationIdxN_none_of_smooth` (`EllipticCurves.FunctionField.MulByNPlaceComposition`) each take
`h : Transcendental F (n • genericPoint).xCoord` as an explicit argument, and the clauses citing
them in this file do not name it.**  That is the `README.md` exemption (`## Docstring conventions`
→ `### Reach clauses`) — a hypothesis derivable from the ones the clause *does* name adds no reach
— and this is the citation it asks for:

* `transcendental_xCoord_nsmul_genericPoint_of_intCast_ne_zero`
  (`EllipticCurves.FunctionField.MulByNXCoordFormula`) proves `h` from `(2 : F) ≠ 0` and
  `((n : ℤ) : F) ≠ 0`, which is what the two `_of_ne_zero` clauses name;
* `transcendental_xCoord_nsmul_of_smooth` (`EllipticCurves.FunctionField.MulByNComposition`) proves
  it from `(2 : F) ≠ 0`, `(3 : F) ≠ 0`, `n ≠ 0` and `3`-smoothness, which is what the `_of_smooth`
  clause names.

⚠️ **Neither derivation runs from the index condition alone**, which is all those three clauses
named until `#1659`: `(2 : F) ≠ 0` is derivable from nothing any reach clause here names, so it is
reach and had to be added rather than left to the exemption.

## Main definitions and statements

* `WeierstrassCurve.Affine.CoordinateRing.comapProjPointN` and `…ramificationIdxN` — the contraction
  of a place along `[n]∗` and its ramification index, with `…placeOf_comapProjPointN` identifying
  the contracted place as the comap of the place and `…ramificationIdxN_pos` giving `0 < e_p`;
* `…divisorProj_mulByNEndo_apply` — `ord_p (f ∘ [n]) = e_p · ord_{[n]⁻¹ p} (f)`;
* `…dvd_divisorProj_mulByNEndo` — the divisibility corollary `#422` states;
* `…finite_comapProjPointN_preimage_singleton` — finitely many places lie above a place;
* `…pullbackDivisorN`, its defining `…pullbackDivisorN_apply` and `…divisorProj_mulByNEndo` —
  `div (f ∘ [n]) = [n]∗ (div f)`;
* `…comapProjPointNOfAlgClosed`, `…ramificationIdxNOfAlgClosed`, `…pullbackDivisorNOfAlgClosed`,
  `…divisorProj_mulByNEndoOfAlgClosed_apply`, `…divisorProj_mulByNEndoOfAlgClosed` and
  `…finite_comapProjPointNOfAlgClosed_preimage_singleton` — the same statements over `F̄`, where the
  transcendence hypothesis is automatic and only `n ≠ 0` and `(2 : F) ≠ 0` remain.  ⚠️ This list is
  shorter than the one above it: `…dvd_divisorProj_mulByNEndo` is the general-`n` result with no
  `OfAlgClosed` twin;
* `…comapProjPointN_two` and `…ramificationIdxN_two` — at `n = 2` this layer **is** the merged one.
  The `n = 1` and `n = 3` companions are in
  `EllipticCurves.FunctionField.MulByNPlaceComposition`, which needs them for its induction.

## References

* [J. H. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], II.2, II.3.6.
-/

namespace WeierstrassCurve.Affine

namespace CoordinateRing

variable {F : Type*} [Field F] {W : Affine F} [IsDedekindDomain W.CoordinateRing] [W.IsElliptic]

/-! ### The contraction and the ramification index -/

/-- **The contraction of a place of the projective curve along `[n]∗`.**  The general-`n` form of
the merged `comapProjPointTwo`. -/
noncomputable def comapProjPointN (n : ℕ)
    (hn : Transcendental F (n • genericPoint (W := W)).xCoord) : ProjPoint W → ProjPoint W :=
  comapProjPoint (mulByNEndo_algebraMap_base n hn) (mulByNEndo_isIntegralElem n hn)

@[simp] theorem placeOf_comapProjPointN (n : ℕ)
    (hn : Transcendental F (n • genericPoint (W := W)).xCoord) (p : ProjPoint W) :
    placeOf W (comapProjPointN n hn p) = (placeOf W p).comap (mulByNEndo n hn) :=
  placeOf_comapProjPoint _ _ p

/-- **The ramification index of `[n]∗`.**  The general-`n` form of the merged `ramificationIdxTwo`.

⚠️ It is *defined* as the value of the transported order at a uniformizer, exactly as at `n = 2`.
Nothing below computes it at any particular place, and in particular nothing here says it is `1` at
the place at infinity — that is `#670`'s statement, and at an `n` divisible by the characteristic it
is **false** (see the module docstring).  ⚠️ At every `3`-smooth `n ≠ 0` with `(2 : F) ≠ 0` and
`(3 : F) ≠ 0` it is `1`:
`EllipticCurves.FunctionField.MulByNPlaceComposition.ramificationIdxN_none_of_smooth`, by
multiplicativity of this index along `[m · n]∗ = [m]∗ ∘ [n]∗` rather than by any computation here;
⚠️ and at every `n` with `(2 : F) ≠ 0` and `((n : ℤ) : F) ≠ 0`, `…ramificationIdxN_none_of_ne_zero`,
by the pole count.  ⚠️ *"At general `n`"* in the sentence above meant *"with no hypothesis on
`(n : F)`"*, which is the only range in which it is false. -/
noncomputable def ramificationIdxN (n : ℕ)
    (hn : Transcendental F (n • genericPoint (W := W)).xCoord) (p : ProjPoint W) : ℤ :=
  ramificationIdx (mulByNEndo_algebraMap_base n hn) (mulByNEndo_isIntegralElem n hn) p

theorem ramificationIdxN_pos (n : ℕ)
    (hn : Transcendental F (n • genericPoint (W := W)).xCoord) (p : ProjPoint W) :
    0 < ramificationIdxN n hn p :=
  ramificationIdx_pos _ _ p

/-- **`ord_p (f ∘ [n]) = e_p · ord_{[n]⁻¹ p} (f)`** — the order transport under `[n]∗`, on the
*projective* point set, for every `n` at which `[n]` is non-constant.

`#422`'s 2026-08-16 correction showed the affine AKLB route is false because `[n]∗F[W] ⊄ F[W]`; the
obstruction is projective and this is the statement that dissolves it, now at general `n`. -/
theorem divisorProj_mulByNEndo_apply (n : ℕ)
    (hn : Transcendental F (n • genericPoint (W := W)).xCoord) {f : W.FunctionField} (hf : f ≠ 0)
    (p : ProjPoint W) :
    divisorProj W (mulByNEndo n hn f) p
      = ramificationIdxN n hn p * divisorProj W f (comapProjPointN n hn p) :=
  divisorProj_comp_apply _ _ hf p

/-- **`n`-divisibility of the divisor of `f ∘ [n]`.** -/
theorem dvd_divisorProj_mulByNEndo (n : ℕ)
    (hn : Transcendental F (n • genericPoint (W := W)).xCoord) {m : ℤ} {f : W.FunctionField}
    (hf : f ≠ 0) (hm : ∀ q : ProjPoint W, m ∣ divisorProj W f q) (p : ProjPoint W) :
    m ∣ divisorProj W (mulByNEndo n hn f) p :=
  dvd_divisorProj_comp (mulByNEndo_algebraMap_base n hn) (mulByNEndo_isIntegralElem n hn) hf hm p

/-! ### The divisor pullback -/

/-- **Finitely many places lie above a place, for `[n]∗`.** -/
theorem finite_comapProjPointN_preimage_singleton (n : ℕ)
    (hn : Transcendental F (n • genericPoint (W := W)).xCoord) (q : ProjPoint W) :
    ((comapProjPointN n hn) ⁻¹' {q}).Finite :=
  finite_comapProjPoint_preimage_singleton _ _ q

/-- **The pullback of divisors along `[n]∗`.**  The general-`n` form of the merged
`pullbackDivisorTwo`. -/
noncomputable def pullbackDivisorN (n : ℕ)
    (hn : Transcendental F (n • genericPoint (W := W)).xCoord) :
    (ProjPoint W →₀ ℤ) →+ (ProjPoint W →₀ ℤ) :=
  pullbackDivisor (mulByNEndo_algebraMap_base n hn) (mulByNEndo_isIntegralElem n hn)

@[simp] theorem pullbackDivisorN_apply (n : ℕ)
    (hn : Transcendental F (n • genericPoint (W := W)).xCoord) (D : ProjPoint W →₀ ℤ)
    (p : ProjPoint W) :
    pullbackDivisorN n hn D p = ramificationIdxN n hn p * D (comapProjPointN n hn p) :=
  rfl

/-- **`div (f ∘ [n]) = [n]∗ (div f)`** — the divisor-level functoriality of the
multiplication-by-`n` pullback, as an equation in the projective divisor group, for every `n` at
which `[n]` is non-constant.

This is `#414` / `#422` deliverable 1 at general `n`.  Silverman *AEC* II.3.6. -/
theorem divisorProj_mulByNEndo (n : ℕ)
    (hn : Transcendental F (n • genericPoint (W := W)).xCoord) {f : W.FunctionField} (hf : f ≠ 0) :
    divisorProj W (mulByNEndo n hn f) = pullbackDivisorN n hn (divisorProj W f) :=
  divisorProj_comp _ _ hf

/-! ### The `[IsAlgClosed F]` corollaries

Over an algebraically closed field of characteristic `≠ 2` the transcendence hypothesis is
automatic for every `n ≠ 0` (`transcendental_xCoord_nsmul_of_isAlgClosed`), so each statement above
has an unconditional-in-`n` form.  `mulByNEndoOfAlgClosed h2 hn` **is** `mulByNEndo n` at that
proof, so these are instantiations and not new content. -/

section IsAlgClosed

variable [IsAlgClosed F] (h2 : (2 : F) ≠ 0) {n : ℕ} (hn : n ≠ 0)

open Classical in
/-- **The contraction of a place along `[n]∗` over `F̄`**, for every `n ≠ 0` with
`(2 : F) ≠ 0`. -/
noncomputable def comapProjPointNOfAlgClosed : ProjPoint W → ProjPoint W :=
  comapProjPointN n (transcendental_xCoord_nsmul_of_isAlgClosed h2 hn)

open Classical in
/-- **The ramification index of `[n]∗` over `F̄`**, for every `n ≠ 0` with `(2 : F) ≠ 0`. -/
noncomputable def ramificationIdxNOfAlgClosed (p : ProjPoint W) : ℤ :=
  ramificationIdxN n (transcendental_xCoord_nsmul_of_isAlgClosed h2 hn) p

open Classical in
/-- **The pullback of divisors along `[n]∗` over `F̄`**, for every `n ≠ 0` with `(2 : F) ≠ 0`. -/
noncomputable def pullbackDivisorNOfAlgClosed : (ProjPoint W →₀ ℤ) →+ (ProjPoint W →₀ ℤ) :=
  pullbackDivisorN n (transcendental_xCoord_nsmul_of_isAlgClosed h2 hn)

open Classical in
/-- **`ord_p (f ∘ [n]) = e_p · ord_{[n]⁻¹ p} (f)` over `F̄`**, for every `n ≠ 0` with
`(2 : F) ≠ 0`. -/
theorem divisorProj_mulByNEndoOfAlgClosed_apply {f : W.FunctionField} (hf : f ≠ 0)
    (p : ProjPoint W) :
    divisorProj W (mulByNEndoOfAlgClosed h2 hn f) p
      = ramificationIdxNOfAlgClosed h2 hn p
        * divisorProj W f (comapProjPointNOfAlgClosed h2 hn p) :=
  divisorProj_mulByNEndo_apply n _ hf p

open Classical in
/-- **`div (f ∘ [n]) = [n]∗ (div f)` over `F̄`**, for every `n ≠ 0` with `(2 : F) ≠ 0`.  This is
the general-`n` form of `#414` / `#422` deliverable 1, with no hypothesis left beyond those two. -/
theorem divisorProj_mulByNEndoOfAlgClosed {f : W.FunctionField} (hf : f ≠ 0) :
    divisorProj W (mulByNEndoOfAlgClosed h2 hn f)
      = pullbackDivisorNOfAlgClosed h2 hn (divisorProj W f) :=
  divisorProj_mulByNEndo n _ hf

open Classical in
/-- **Finitely many places lie above a place, for `[n]∗` over `F̄`**, for every `n ≠ 0` with
`(2 : F) ≠ 0`. -/
theorem finite_comapProjPointNOfAlgClosed_preimage_singleton (q : ProjPoint W) :
    ((comapProjPointNOfAlgClosed (W := W) h2 hn) ⁻¹' {q}).Finite :=
  finite_comapProjPointN_preimage_singleton n _ q

end IsAlgClosed

/-! ### Consistency with the merged `n = 2` layer

⚠️ These are not restatements: `comapProjPoint` and `ramificationIdx` are `choose`s, so *"the two
constructions agree"* is a theorem and not a definitional unfolding.  Together with
`mulByNEndo_two` they say the general-`n` place layer really is the merged one at `n = 2`, which is
what makes it the same rung rather than a parallel one. -/

section Consistency

variable (h2 : (2 : F) ≠ 0)

include h2 in
/-- **The `[n]∗` contraction at `n = 2` is the merged `[2]∗` contraction.** -/
theorem comapProjPointN_two (p : ProjPoint W) :
    comapProjPointN 2 (transcendental_xCoord_two_nsmul (W := W) h2) p = comapProjPointTwo h2 p := by
  refine placeOf_injective ?_
  rw [placeOf_comapProjPointN, comapProjPointTwo, placeOf_comapProjPoint, mulByNEndo_two h2]

include h2 in
/-- **The `[n]∗` ramification index at `n = 2` is the merged `[2]∗` index.**  Both are read off the
transported order at a uniformizer at the contracted place, and `comapProjPointN_two` says the
contracted place is the same one. -/
theorem ramificationIdxN_two (p : ProjPoint W) :
    ramificationIdxN 2 (transcendental_xCoord_two_nsmul (W := W) h2) p
      = ramificationIdxTwo h2 p := by
  obtain ⟨π, hπ0, hπ⟩ := exists_divisorProj_eq_one (comapProjPointTwo h2 p)
  have hN := divisorProj_mulByNEndo_apply 2 (transcendental_xCoord_two_nsmul (W := W) h2) hπ0 p
  have hT := divisorProj_mulByTwoEndo_apply h2 hπ0 p
  rw [comapProjPointN_two h2 p, hπ, mul_one] at hN
  rw [hπ, mul_one] at hT
  rw [← hN, ← hT, mulByNEndo_two h2]

end Consistency

/-! ### Non-vacuity

⚠️ Every statement above carries `[IsDedekindDomain W.CoordinateRing]` and `[W.IsElliptic]` on top
of a transcendence hypothesis, and `comapProjPointN` is a `choose`, so a curve on which the whole
chain elaborates with every instance discharged is worth committing rather than quoting.  ⚠️ The
certificate has to be at an index **beyond** `n = 2, 3`, or it certifies the merged instantiations
instead of these; it is at `n = 5`, matching the certificate of
`EllipticCurves.FunctionField.MulByNTranscendence`, on the same curve `y² + y = x³` over an
algebraic closure of `ℚ`. -/

section Nonvacuity

/-! The certificate curve `y² + y = x³` is the shared `EllipticCurves.Fixture.y2AddYEqX3`, and the
base — algebraically closed, and of characteristic `0` so that `2 ≠ 0` and `3 ≠ 0` — is
`EllipticCurves.Fixture.AlgClosedQ`, whose single `[CharZero F]` instance supplies
`(y2AddYEqX3 ℚ).IsElliptic`. The **base-changed** `((y2AddYEqX3 ℚ)⁄AlgClosedQ).IsElliptic` comes
from the same module, via `EllipticCurves.Fixture.instIsEllipticBaseChange`; this block declares no
fixture of its own (`#1408`). -/

open EllipticCurves.Fixture

private lemma exampleTwoN : (2 : AlgClosedQ) ≠ 0 := two_ne_zero

open Classical in
private lemma exampleFiveN :
    Transcendental AlgClosedQ
      ((5 : ℕ) • genericPoint (W := (y2AddYEqX3 ℚ)⁄AlgClosedQ)).xCoord :=
  transcendental_xCoord_nsmul_of_isAlgClosed exampleTwoN (by norm_num)

example : IsDedekindDomain ((y2AddYEqX3 ℚ)⁄AlgClosedQ).CoordinateRing := inferInstance

open Classical in
/-- **⚠️ THE CERTIFICATE, part one.**  At `n = 5` on a curve that exists, the order transport is a
genuine equation with a positive index. -/
example {f : ((y2AddYEqX3 ℚ)⁄AlgClosedQ).FunctionField} (hf : f ≠ 0)
    (p : ProjPoint ((y2AddYEqX3 ℚ)⁄AlgClosedQ)) :
    divisorProj ((y2AddYEqX3 ℚ)⁄AlgClosedQ) (mulByNEndo 5 exampleFiveN f) p
      = ramificationIdxN 5 exampleFiveN p
        * divisorProj ((y2AddYEqX3 ℚ)⁄AlgClosedQ) f (comapProjPointN 5 exampleFiveN p) :=
  divisorProj_mulByNEndo_apply 5 exampleFiveN hf p

open Classical in
/-- **⚠️ THE CERTIFICATE, part two.**  And the divisor-level form, at the same index. -/
example {f : ((y2AddYEqX3 ℚ)⁄AlgClosedQ).FunctionField} (hf : f ≠ 0) :
    divisorProj ((y2AddYEqX3 ℚ)⁄AlgClosedQ) (mulByNEndo 5 exampleFiveN f)
      = pullbackDivisorN 5 exampleFiveN (divisorProj ((y2AddYEqX3 ℚ)⁄AlgClosedQ) f) :=
  divisorProj_mulByNEndo 5 exampleFiveN hf

end Nonvacuity

end CoordinateRing

end WeierstrassCurve.Affine
