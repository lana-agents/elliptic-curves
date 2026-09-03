/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import EllipticCurves.Fixtures
import EllipticCurves.FunctionField.MulByNDegreeGeneral
import EllipticCurves.FunctionField.MulByNSeparable
import EllipticCurves.FunctionField.TranslationActionN
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.FieldTheory.IntermediateField.Algebraic

/-!
# `F(W)` is Galois over `[n]∗F(W)` at every `n` prime to the characteristic, with group `E[n]`

`EllipticCurves.FunctionField.TranslationActionN` (`#1232`) builds the group `G = E[n]` of
translations by `n`-torsion points, acting faithfully on `F(W)` by `F`-algebra automorphisms, with
`Nat.card G = n²` over an algebraically closed base field of characteristic `≠ 2, 3` at every
`3`-smooth `n`, and proves the inclusion `[n]∗F(W) ⊆ Fixed(G)`.  This file closes the sandwich:

```
[n]∗F(W)  ⊆  Fixed(G)  ⊆  F(W),     [F(W) : [n]∗F(W)] = n² = |G| = [F(W) : Fixed(G)]
```

so `Fixed(G) = [n]∗F(W)` exactly, whence `F(W) / [n]∗F(W)` is **Galois** — and in particular
**normal, in every characteristic `≠ 2, 3`**, with no `CharZero` anywhere.

## ⚠️ Two ranges of `n` live in this file, and they must not be conflated

The file is in two halves, and the second one is strictly wider:

* the **`3`-smooth package** (`…_of_smooth`, and the unsuffixed `finrank_fixedFieldN` /
  `fixedFieldN_eq_mulByNFieldRange`) carries `(2 : F) ≠ 0`, `(3 : F) ≠ 0`, `n ≠ 0` and
  `∀ p ∈ n.primeFactors, p = 2 ∨ p = 3`.  It is what the merged consumers cite and it is **kept**;
* the **general package** (`…_of_ne_zero`) carries `(2 : F) ≠ 0` and `(n : F) ≠ 0` and nothing else
  — no `(3 : F) ≠ 0`, no smoothness, no parity.  `#1523`.

⚠️ The general half is not a new argument.  It is the `3`-smooth proof with **one** input replaced:
Artin's theorem needs `|E[n]|`, and `card_torsion_eq_sq` (`EllipticCurves.Torsion.StructureGeneral`,
`#293`) supplies it at every `n` with `(2 : F) ≠ 0` and `(n : F) ≠ 0` where
`card_torsion_eq_sq_of_smooth` supplied it only at `3`-smooth `n`.  ⚠️ **`(2 : F) ≠ 0` is the
count's second hypothesis and this sentence used to name only the index one** (`#1137`).  The
other outer degree, `finrank_mulByNFieldRange_eq_sq_of_two_ne_zero`
(`EllipticCurves.FunctionField.MulByNDegreeGeneral`), never carried smoothness at all and was
sitting unconsumed.

⚠️ `(n : F) ≠ 0` is **sharp**, not a relaxed smoothness: at `p = char F` the count `#E[p] = p²` is
*false* — `E[p]` is `0` or `ℤ/pℤ`, never `(ℤ/pℤ)²` — so no route reaches an index the characteristic
divides.

It is the general-`n` mirror of `EllipticCurves.FunctionField.MulByTwoGalois` (`#759`) and
`EllipticCurves.FunctionField.MulByThreeGalois` (`#775`), whose argument it runs verbatim.  Nothing
mathematical is invented here; what is new is that both outer degrees now exist at every `3`-smooth
`n`: `finrank_mulByNFieldRange_of_smooth` (`EllipticCurves.FunctionField.MulByNComposition`,
`#1213`) on the left and `card_torsionNMul` on the right.

## ⚠️ `Normal` is the deliverable; the separability is a by-product of a statement already merged

`EllipticCurves.FunctionField.MulByNSeparable` (`#1219`) already proves
`Algebra.IsSeparable ([n]∗F(W)) F(W)` at every `3`-smooth `n`, by a tower along
`[m · n]∗ = [m]∗ ∘ [n]∗`.  That argument **provably cannot reach `Normal`**, normality not being
transitive, and that file says so and names this one as the method.  So the deliverable here is
`Normal` and `IsGalois`; separability comes along for free but is not new.

⚠️ **At `3`-smooth `n` it is not new in the weaker sense either: the hypotheses are identical.**
Checked rather than assumed — `isSeparable_mulByNFieldRange_of_smooth` carries exactly
`[IsAlgClosed F]`, `(2 : F) ≠ 0`, `(3 : F) ≠ 0`, `n ≠ 0`, `3`-smoothness and the transcendence of
`x([n]𝒫)`, and so does the `3`-smooth half below.  Neither statement subsumes the other there; they
are **equal in range**, and the two proofs are genuinely independent (a tower of merged
`n = 2`/`n = 3` extensions there, Artin's theorem against a translation action here).
`isGalois_mulByNFieldRange_of_smooth` therefore consumes `#1219`'s separability rather than minting
one, and a consumer at a `3`-smooth index should keep using `#1219`'s name.

⚠️ **The general half does mint its own separability, and the reason is the whole point of
`#1523` item 3.**  `MulByNSeparable` manufactures separability by *multiplying up* from `n = 2` and
`n = 3`, so a composition ladder can only ever reach `3`-smooth indices — the smoothness there is
created by the method, not inherited from an input.  Once the sandwich closes at general `n`,
separability is instead read off the **same** fixed field the normality comes from
(`FixedPoints.isSeparable`, an instance for any finite group), which knows no primes:
`isSeparable_mulByNFieldRange_of_ne_zero` below is one line and reaches `n = 5`.  ⚠️ The tower route
is **kept and not superseded in scope** — it is the only separability proof in this development that
does not need `#E[n] = n²`, hence the only one that survives if the count is ever weakened.  What it
is no longer is *load-bearing*.

⚠️ `isSeparable_mulByNEndoFieldRange_of_charZero` (`EllipticCurves.FunctionField.MulByNInertia`,
`#1221`) is `CharZero` and carries **no** `3`-smoothness, so it reached `n = 5` before anything here
did.  It gives separability only, and it is now no longer the only statement in the tree that does
so at `n = 5`; it is still the only one that does so without `[IsAlgClosed F]`.

## The presentations of `[n]∗F(W)`, and which one carries what

The subset `[n]∗F(W) ⊆ F(W)` appears in this tree as three objects — the `IntermediateField`
`(mulByNEndoAlgHom n h).fieldRange`, the `Subfield` `(mulByNEndo n h).fieldRange` and the `Subring`
`(mulByNEndo n h).range` — with membership in any two `Iff.rfl`.  `MulByThreeGalois`'s module
docstring explains the trade-off in full and it is `n`-independent; the short form is:

* **the headline is stated for the `IntermediateField`**, because the sandwich lemma
  `IntermediateField.eq_of_le_of_finrank_eq'` is stated there.  `FixedPoints.subfield G F(W)` is a
  `Subfield`, promoted with `Subfield.toIntermediateField` — legitimate because `E[n]` acts by
  *`F`-algebra* automorphisms, so `AlgEquiv.commutes` puts every constant in the fixed field;
* **the `Subfield` forms are exported too**, since the place machinery needs a `Field` type;
* **there is no `Subring` form**, because `↥(mulByNEndo n h).range` carries no `Field` instance and
  nothing transportable exists.  `#759` established this at `n = 2` and none of it is `n`-dependent.

⚠️ **The `Subfield` degree crossing is not needed and is deliberately not consumed.**  `#1221`'s
`finrank_mulByNEndoFieldRange_of_smooth` (`EllipticCurves.FunctionField.MulByNInertia`) does cross
the degree, but the sandwich runs entirely in the `IntermediateField` lattice and the `Subfield`
form of the equality is `SetLike.ext` off the headline — no second degree computation, and hence no
import of `MulByNInertia` with its `[IsDedekindDomain W.CoordinateRing]` variable block.  The
`Normal` and `IsGalois` crossings go along `mulByNFieldRangeEquivSubfield` (`#1219`) instead.

## ⚠️ The `Subfield` `Normal`/`IsGalois` are new relative to `n = 2` and `n = 3`

`MulByTwoGalois` and `MulByThreeGalois` cross **only separability** into the `Subfield`
presentation, and their docstrings give a reason that applies to the `Subring` — not to the
`Subfield`.  Mathlib has `Normal.of_equiv_equiv` and `IsGalois.of_equiv_equiv` with exactly the
`hcomp` shape `Algebra.IsSeparable.of_equiv_equiv` takes, so the crossing costs one line each.  They
are shipped here.  ⚠️ This is a genuine addition, not a mirror: at `n = 2` and `n = 3` the
corresponding `Subfield` statements are still absent from the tree, and closing that gap is a
separate (small) `#699`-style question, not this file's business.

## Main results

Every public declaration of this file is listed, and all are in namespace
`WeierstrassCurve.Affine.CoordinateRing`.

* `fixedFieldN` — `Fixed(E[n])` as an `IntermediateField F F(W)`, with `mem_fixedFieldN_iff`, and
  `finrank_fixedFieldN`: it has index `n²`, by Artin;
* `fixedFieldN_eq_mulByNFieldRange` — **the sandwich**, `Fixed(E[n]) = [n]∗F(W)`, and
  `fixedPoints_subfield_eq_mulByNEndoFieldRange` at the `Subfield` level;
* `normal_mulByNFieldRange_of_smooth` and `isGalois_mulByNFieldRange_of_smooth` — the Galois
  package in the `IntermediateField` presentation, with **no hypothesis on the characteristic
  beyond `(2 : F) ≠ 0` and `(3 : F) ≠ 0`**;
* `normal_mulByNEndoFieldRange_of_smooth` and `isGalois_mulByNEndoFieldRange_of_smooth` — the same
  in the `Subfield` presentation;
* `finrank_fixedFieldN_of_ne_zero`, `fixedFieldN_eq_mulByNFieldRange_of_ne_zero` and
  `fixedPoints_subfield_eq_mulByNEndoFieldRange_of_ne_zero` — **Artin and the sandwich at every `n`
  with `(2 : F) ≠ 0` and `(n : F) ≠ 0`**, with no `(3 : F) ≠ 0` and no smoothness;
* `normal_mulByNFieldRange_of_ne_zero`, `isSeparable_mulByNFieldRange_of_ne_zero` and
  `isGalois_mulByNFieldRange_of_ne_zero` — **the general Galois package**, and
  `normal_mulByNEndoFieldRange_of_ne_zero`, `isSeparable_mulByNEndoFieldRange_of_ne_zero`,
  `isGalois_mulByNEndoFieldRange_of_ne_zero` in the `Subfield` presentation;
* `fixedFieldN_eq_mulByNFieldRange_five`, `isSeparable_mulByNFieldRange_five`,
  `isGalois_mulByNFieldRange_five` and `isGalois_mulByNEndoFieldRange_five` — **the sandwich, the
  separability and the Galois property at `n = 5`**, the index at which every earlier statement on
  this front stopped;
* `isGalois_mulByNFieldRange_two` and `isGalois_mulByNFieldRange_three` — consistency certificates
  against the merged `n = 2` and `n = 3` packages.  ⚠️ **Both are strictly weaker than the merged
  statements they reproduce** and are certificates, not new API; see their docstrings.
  `isGalois_mulByNFieldRange_two_of_ne_zero` is the same certificate off the general package, and it
  is **not** weaker — the general route does not carry `(3 : F) ≠ 0`.

## How to fire these

`(2 : F) ≠ 0` and `(3 : F) ≠ 0` are hypotheses rather than typeclasses, so none of the results below
can be an `instance`; a consumer writes

```lean
haveI := isGalois_mulByNEndoFieldRange_of_smooth (W := W) h2 h3 hn hfac h
```

and then applies whatever wanted `[IsGalois ↥(mulByNEndo n h).fieldRange F(W)]`.  Same shape as
`finite_torsionNMul` in `TranslationActionN`, and for the same reason.  Off the general package it
is one hypothesis shorter:

```lean
haveI := isGalois_mulByNEndoFieldRange_of_ne_zero (W := W) h2 hn h
```

with `hn : (n : F) ≠ 0`.

## What is *not* here

* ⚠️ **`Gal(F(W) / [n]∗F(W)) ≃* E[n]` as a group — RETIRED, it landed.**  This bullet used to read
  *"`IsGalois` is delivered; the Galois *group* is not identified with `E[n]`.  Both merged Galois
  files decline the same identification and name their own sandwich as what it would start from;
  `fixedFieldN_eq_mulByNFieldRange` is that starting point here."*  The identification is
  `torsionNMulGaloisEquiv` in `EllipticCurves.FunctionField.MulByNGaloisGroup`, and it starts from
  `fixedPoints_subfield_eq_mulByNEndoFieldRange` below — the `Subfield` form of the sandwich, not
  the `IntermediateField` one this bullet nominated, because `FixedPoints.toAlgAutMulEquiv` has a
  `Subfield` base.  ⚠️ **The warning the bullet ended with stands and is worth keeping**: the
  equality of subfields is *not* the group isomorphism.  What turns one into the other is Mathlib's
  `FixedPoints.toAlgAutMulEquiv` — Artin's theorem in its bijective form — and the equality only
  says which field the resulting group is over.
* ⚠️ **`n = 5` — RETIRED, it landed.**  This bullet used to read *"Both outer degrees are
  `3`-smooth — `card_torsion_eq_sq_of_smooth` and `#1213`'s degree — so the sandwich has no side
  there."*  Neither clause is true any more: the count is `card_torsion_eq_sq` at every `n` with
  `(2 : F) ≠ 0` and `(n : F) ≠ 0` (`#293`), and `#1213`'s degree had a smoothness-free form
  (`finrank_mulByNFieldRange_eq_sq_of_two_ne_zero`) all along.  `isGalois_mulByNFieldRange_five` and
  its three companions are named theorems below.  ⚠️ What is still true is the *shape* of the old
  bullet's reason: nothing here manufactures a prime, and the general statements reach `n = 5`
  because an **input** does, not because `IsGalois` does.
* **No `#E[n] = n²` from a degree.**  `card_torsion_eq_sq_of_smooth` is an **input** here, proved by
  the torsion route in `EllipticCurves.Torsion.ThreePrimary`.  The step *"a separable isogeny has as
  many points in its kernel as its degree"* is recorded as absent by `PlaceRamificationInertia`,
  `PlacePullback`, `MulByTwoFibreInfinity`, `MulByTwoDegree`, `MulByNInertia` and
  `PlaceDegreeComparison`, and **all six are still right**.  Widening `IsGalois` adds none of it,
  and now that the count and the degree sit in one file the temptation to read one off the other is
  real; do not.
* **Nothing about the Weil pairing** (`#418`/`#419`), `hprin` (`#962`), places or divisors.

## References

* [J. H. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.4.
* Artin's theorem on fixed fields, [stacks 09I3].
-/

open Module Polynomial

namespace WeierstrassCurve.Affine

namespace CoordinateRing

variable {F : Type*} [Field F] {W : Affine F} [W.IsElliptic]

/-! ### The fixed field as an intermediate field -/

open Classical in
/-- **The fixed field of `E[n]`, as an intermediate field of `F(W) / F`.**

`FixedPoints.subfield` produces a `Subfield F(W)`; the promotion to an `IntermediateField F F(W)`
is legitimate because `E[n]` acts by *`F`-algebra* automorphisms, so `AlgEquiv.commutes` puts every
constant in the fixed field.  The promotion is what makes
`IntermediateField.eq_of_le_of_finrank_eq'` — the sandwich lemma — applicable.

⚠️ No hypothesis on `n` and none on `F`: this is the general-`n` form of `fixedFieldThree`, and the
`3`-smoothness enters only at `finrank_fixedFieldN` below. -/
noncomputable def fixedFieldN (W : Affine F) [W.IsElliptic] (n : ℕ) :
    IntermediateField F W.FunctionField :=
  (FixedPoints.subfield (TorsionNMul W n) W.FunctionField).toIntermediateField
    fun c T => (translateAut (T.toAdd : W.Point)).commutes c

open Classical in
@[simp] lemma mem_fixedFieldN_iff {n : ℕ} {g : W.FunctionField} :
    g ∈ fixedFieldN W n ↔ ∀ T : TorsionNMul W n, T • g = g := Iff.rfl

open Classical in
/-- **Artin's theorem for the translation action**: `[F(W) : Fixed(E[n])] = |E[n]| = n²`.

`FixedPoints.finrank_eq_card` wants `[Fintype G]` and `[FaithfulSMul G F(W)]`.  The second is an
unconditional instance from `TranslationActionN`; the first is not, because finiteness of `E[n]`
rests on the *hypotheses* `(2 : F) ≠ 0`, `(3 : F) ≠ 0`, `n ≠ 0` and `3`-smoothness — so it is
manufactured here inside the proof, as `Fintype.ofFinite` of `finite_torsionNMul`, and never appears
in a statement.  That is the discipline `finite_torsionNMul`'s own docstring asks for. -/
theorem finrank_fixedFieldN [IsAlgClosed F] (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) {n : ℕ}
    (hn : n ≠ 0) (hfac : ∀ p ∈ n.primeFactors, p = 2 ∨ p = 3) :
    finrank ↥(fixedFieldN W n) W.FunctionField = n ^ 2 := by
  haveI := finite_torsionNMul (W := W) h2 h3 hn hfac
  haveI : Fintype (TorsionNMul W n) := Fintype.ofFinite _
  have h : finrank ↥(FixedPoints.subfield (TorsionNMul W n) W.FunctionField) W.FunctionField
      = n ^ 2 := by
    rw [FixedPoints.finrank_eq_card (TorsionNMul W n) W.FunctionField,
      ← Nat.card_eq_fintype_card, card_torsionNMul h2 h3 hn hfac]
  exact h

/-! ### The sandwich -/

open Classical in
/-- **`Fixed(E[n]) = [n]∗F(W)` at every `3`-smooth `n ≠ 0`.**

Both outer degrees are `n²` — `finrank_fixedFieldN` by Artin, `finrank_mulByNFieldRange_of_smooth`
by `#1213` — and `[n]∗F(W) ⊆ Fixed(E[n])` by `TranslationActionN`, so the middle inclusion has index
one and `IntermediateField.eq_of_le_of_finrank_eq'` closes it.

⚠️ The **prime** on `eq_of_le_of_finrank_eq'` is load-bearing: that variant assumes
finite-dimensionality of the top field over the smaller one and compares the two *outer* degrees
`finrank F L` and `finrank E L`, which is what a sandwich of outer degrees supplies.  The unprimed
`eq_of_le_of_finrank_eq` compares degrees over the *base* and does not close this goal.

This is the whole mathematical content of the file; everything after it is transport. -/
theorem fixedFieldN_eq_mulByNFieldRange [IsAlgClosed F] (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0)
    {n : ℕ} (hn : n ≠ 0) (hfac : ∀ p ∈ n.primeFactors, p = 2 ∨ p = 3)
    (h : Transcendental F (n • genericPoint (W := W)).xCoord) :
    (mulByNEndoAlgHom n h).fieldRange = fixedFieldN W n := by
  have hdeg : finrank ↥(mulByNEndoAlgHom (W := W) n h).fieldRange W.FunctionField = n ^ 2 :=
    finrank_mulByNFieldRange_of_smooth h2 h3 hn hfac h
  haveI : FiniteDimensional ↥(mulByNEndoAlgHom (W := W) n h).fieldRange W.FunctionField :=
    Module.finite_of_finrank_pos (by rw [hdeg]; exact pow_pos (Nat.pos_of_ne_zero hn) 2)
  refine IntermediateField.eq_of_le_of_finrank_eq' ?_
    (by rw [hdeg, finrank_fixedFieldN h2 h3 hn hfac])
  rintro _ ⟨f, rfl⟩
  exact mulByNEndo_mem_fixedPoints n h f

open Classical in
/-- The `Subfield`-level form of the sandwich: `Fixed(E[n])` and `[n]∗F(W)` are the same subfield of
`F(W)`.  Membership on both sides is unchanged, so this is `SetLike.ext` off the headline — in
particular it needs **no** second degree computation and hence not `#1221`'s
`finrank_mulByNEndoFieldRange_of_smooth`. -/
theorem fixedPoints_subfield_eq_mulByNEndoFieldRange [IsAlgClosed F] (h2 : (2 : F) ≠ 0)
    (h3 : (3 : F) ≠ 0) {n : ℕ} (hn : n ≠ 0) (hfac : ∀ p ∈ n.primeFactors, p = 2 ∨ p = 3)
    (h : Transcendental F (n • genericPoint (W := W)).xCoord) :
    FixedPoints.subfield (TorsionNMul W n) W.FunctionField = (mulByNEndo (W := W) n h).fieldRange :=
  by
  refine SetLike.ext fun g => ?_
  have hg : g ∈ fixedFieldN W n ↔ g ∈ (mulByNEndo (W := W) n h).fieldRange := by
    rw [← fixedFieldN_eq_mulByNFieldRange h2 h3 hn hfac h]
    exact Iff.rfl
  exact hg

/-! ### Normality and the Galois package

⚠️ There is deliberately **no** separability declaration here: `#1219`'s
`isSeparable_mulByNFieldRange_of_smooth` has exactly these hypotheses and is consumed below.  See
the module docstring. -/

open Classical in
/-- **`F(W)` is normal over `[n]∗F(W)`** at every `3`-smooth `n ≠ 0`, over an algebraically closed
base field of characteristic `≠ 2, 3` — with **no** `CharZero`.

`FixedPoints.normal` is an instance for the fixed field of any finite group, and the sandwich
identifies that fixed field with `[n]∗F(W)`.

⚠️ This is what the tower of `#1219` provably cannot give, normality not being transitive; it is the
reason the file exists.  It is a `theorem` and not an `instance` because `(2 : F) ≠ 0` and
`(3 : F) ≠ 0` are hypotheses; fire it with `haveI`. -/
theorem normal_mulByNFieldRange_of_smooth [IsAlgClosed F] (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0)
    {n : ℕ} (hn : n ≠ 0) (hfac : ∀ p ∈ n.primeFactors, p = 2 ∨ p = 3)
    (h : Transcendental F (n • genericPoint (W := W)).xCoord) :
    Normal ↥(mulByNEndoAlgHom (W := W) n h).fieldRange W.FunctionField := by
  haveI := finite_torsionNMul (W := W) h2 h3 hn hfac
  haveI : Normal ↥(fixedFieldN W n) W.FunctionField := inferInstanceAs
    (Normal ↥(FixedPoints.subfield (TorsionNMul W n) W.FunctionField) W.FunctionField)
  rw [fixedFieldN_eq_mulByNFieldRange h2 h3 hn hfac]
  infer_instance

/-- **`F(W) / [n]∗F(W)` is Galois** at every `3`-smooth `n ≠ 0`.  `IsGalois` is separable plus
normal: the separable half is `#1219`'s `isSeparable_mulByNFieldRange_of_smooth`, at the same
hypotheses, and the normal half is above. -/
theorem isGalois_mulByNFieldRange_of_smooth [IsAlgClosed F] (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0)
    {n : ℕ} (hn : n ≠ 0) (hfac : ∀ p ∈ n.primeFactors, p = 2 ∨ p = 3)
    (h : Transcendental F (n • genericPoint (W := W)).xCoord) :
    IsGalois ↥(mulByNEndoAlgHom (W := W) n h).fieldRange W.FunctionField :=
  haveI := isSeparable_mulByNFieldRange_of_smooth (W := W) h2 h3 hn hfac h
  haveI := normal_mulByNFieldRange_of_smooth (W := W) h2 h3 hn hfac h
  ⟨⟩

/-! ### The `Subfield` presentation -/

/-- **Normality in the `Subfield` presentation** — the form a consumer that has to write
`ValuationSubring ↥L` wants, since `ValuationSubring` needs `L` to be a `Field` type and the
`Subfield` coercion is one.  Carried across `mulByNFieldRangeEquivSubfield` (`#1219`), which is the
identity on elements.

⚠️ New relative to `n = 2` and `n = 3`, which cross only separability; see the module docstring.
There is deliberately no `Subring` version, for the reason `#759` established. -/
theorem normal_mulByNEndoFieldRange_of_smooth [IsAlgClosed F] (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0)
    {n : ℕ} (hn : n ≠ 0) (hfac : ∀ p ∈ n.primeFactors, p = 2 ∨ p = 3)
    (h : Transcendental F (n • genericPoint (W := W)).xCoord) :
    Normal ↥(mulByNEndo (W := W) n h).fieldRange W.FunctionField := by
  haveI := normal_mulByNFieldRange_of_smooth (W := W) h2 h3 hn hfac h
  exact Normal.of_equiv_equiv (f := mulByNFieldRangeEquivSubfield n h)
    (g := RingEquiv.refl W.FunctionField) (by ext a; rfl)

/-- **`F(W) / [n]∗F(W)` is Galois, in the `Subfield` presentation.**  Separability is `#1219`'s
`isSeparable_mulByNEndoFieldRange_of_smooth`, already crossed there; normality is above. -/
theorem isGalois_mulByNEndoFieldRange_of_smooth [IsAlgClosed F] (h2 : (2 : F) ≠ 0)
    (h3 : (3 : F) ≠ 0) {n : ℕ} (hn : n ≠ 0) (hfac : ∀ p ∈ n.primeFactors, p = 2 ∨ p = 3)
    (h : Transcendental F (n • genericPoint (W := W)).xCoord) :
    IsGalois ↥(mulByNEndo (W := W) n h).fieldRange W.FunctionField :=
  haveI := isSeparable_mulByNEndoFieldRange_of_smooth (W := W) h2 h3 hn hfac h
  haveI := normal_mulByNEndoFieldRange_of_smooth (W := W) h2 h3 hn hfac h
  ⟨⟩

/-! ### The general-`n` package: the same seven statements with the `3`-smoothness removed

⚠️ Everything above is the `3`-smooth package and it is **kept**, unchanged and un-deprecated: its
hypotheses are what the merged `TwoPrimary` / `ThreePrimary` consumers carry, and rewriting the
`3`-smooth front onto the names below is a separate, mechanical job (`#1523` items 3–4).

What changed is the **input**, not the argument.  Artin's theorem needs `|E[n]|`, and
`card_torsion_eq_sq` (`EllipticCurves.Torsion.StructureGeneral`, `#293`) supplies it at every `n`
with `(2 : F) ≠ 0` and `(n : F) ≠ 0`; the other outer degree is
`finrank_mulByNFieldRange_eq_sq_of_two_ne_zero`
(`EllipticCurves.FunctionField.MulByNDegreeGeneral`, `#1213`'s general-`n` form), which never
carried `3`-smoothness at all.  The proofs below are the ones above with those two substitutions
and nothing else.

⚠️ **`(3 : F) ≠ 0` disappears entirely**, which is not cosmetic: the consistency certificates at the
end of this file record that the `3`-smooth route is *strictly weaker* at `n = 2` than the merged
`n = 2` package precisely because `card_torsion_eq_sq_of_smooth` carries `h3`.  That defect is
repaired here — see `isGalois_mulByNFieldRange_two_of_ne_zero`.

⚠️ **`(n : F) ≠ 0` is sharp and is not a weakened `3`-smoothness.**  At `p = char F` the count
`#E[p] = p²` is **false**, not unproved, so no route of any kind reaches `n` divisible by the
characteristic. -/

open Classical in
/-- **Artin's theorem for the translation action at every `n` with `(2 : F) ≠ 0` and
`(n : F) ≠ 0`**: `[F(W) : Fixed(E[n])] = |E[n]| = n²`.

`finrank_fixedFieldN` with `finite_torsionNMul_of_ne_zero` and `card_torsionNMul_of_ne_zero`
(`EllipticCurves.FunctionField.TranslationActionN`) in place of their `3`-smooth forms.  The
`Fintype` is manufactured inside the proof and never appears in a statement, as there. -/
theorem finrank_fixedFieldN_of_ne_zero [IsAlgClosed F] (h2 : (2 : F) ≠ 0) {n : ℕ}
    (hn : (n : F) ≠ 0) :
    finrank ↥(fixedFieldN W n) W.FunctionField = n ^ 2 := by
  haveI := finite_torsionNMul_of_ne_zero (W := W) h2 hn
  haveI : Fintype (TorsionNMul W n) := Fintype.ofFinite _
  have h : finrank ↥(FixedPoints.subfield (TorsionNMul W n) W.FunctionField) W.FunctionField
      = n ^ 2 := by
    rw [FixedPoints.finrank_eq_card (TorsionNMul W n) W.FunctionField,
      ← Nat.card_eq_fintype_card, card_torsionNMul_of_ne_zero h2 hn]
  exact h

open Classical in
/-- **`Fixed(E[n]) = [n]∗F(W)` at every `n` with `(2 : F) ≠ 0` and `(n : F) ≠ 0`** — the sandwich,
with no `3`-smoothness on either side.

⚠️ The transcendence proof `h` is a *parameter of the statement*, because the subfield whose degree
is measured depends on it, while `finrank_mulByNFieldRange_eq_sq_of_two_ne_zero` **fixes** its own
(`transcendental_xCoord_nsmul_genericPoint_of_intCast_ne_zero`).  The two agree because
`Transcendental` is a `Prop` and proof irrelevance is definitional — `hdeg` below typechecks against
`h` for that reason and no other.  `EllipticCurves.FunctionField.MulByNDegreeGeneral` records the
same trap. -/
theorem fixedFieldN_eq_mulByNFieldRange_of_ne_zero [IsAlgClosed F] (h2 : (2 : F) ≠ 0) {n : ℕ}
    (hn : (n : F) ≠ 0) (h : Transcendental F (n • genericPoint (W := W)).xCoord) :
    (mulByNEndoAlgHom n h).fieldRange = fixedFieldN W n := by
  have hn0 : n ≠ 0 := by rintro rfl; simp at hn
  have hdeg : finrank ↥(mulByNEndoAlgHom (W := W) n h).fieldRange W.FunctionField = n ^ 2 :=
    finrank_mulByNFieldRange_eq_sq_of_two_ne_zero h2 (by exact_mod_cast hn)
  haveI : FiniteDimensional ↥(mulByNEndoAlgHom (W := W) n h).fieldRange W.FunctionField :=
    Module.finite_of_finrank_pos (by rw [hdeg]; exact pow_pos (Nat.pos_of_ne_zero hn0) 2)
  refine IntermediateField.eq_of_le_of_finrank_eq' ?_
    (by rw [hdeg, finrank_fixedFieldN_of_ne_zero h2 hn])
  rintro _ ⟨f, rfl⟩
  exact mulByNEndo_mem_fixedPoints n h f

open Classical in
/-- The `Subfield`-level sandwich at every `n` with `(2 : F) ≠ 0` and `(n : F) ≠ 0`; `SetLike.ext`
off the headline, exactly as in the `3`-smooth case. -/
theorem fixedPoints_subfield_eq_mulByNEndoFieldRange_of_ne_zero [IsAlgClosed F] (h2 : (2 : F) ≠ 0)
    {n : ℕ} (hn : (n : F) ≠ 0)
    (h : Transcendental F (n • genericPoint (W := W)).xCoord) :
    FixedPoints.subfield (TorsionNMul W n) W.FunctionField = (mulByNEndo (W := W) n h).fieldRange :=
  by
  refine SetLike.ext fun g => ?_
  have hg : g ∈ fixedFieldN W n ↔ g ∈ (mulByNEndo (W := W) n h).fieldRange := by
    rw [← fixedFieldN_eq_mulByNFieldRange_of_ne_zero h2 hn h]
    exact Iff.rfl
  exact hg

open Classical in
/-- **`F(W)` is normal over `[n]∗F(W)` at every `n` with `(2 : F) ≠ 0` and `(n : F) ≠ 0`** — over
an algebraically closed base field, with **no** hypothesis on `(3 : F)` and no `CharZero`.

`FixedPoints.normal` against the general sandwich. -/
theorem normal_mulByNFieldRange_of_ne_zero [IsAlgClosed F] (h2 : (2 : F) ≠ 0) {n : ℕ}
    (hn : (n : F) ≠ 0) (h : Transcendental F (n • genericPoint (W := W)).xCoord) :
    Normal ↥(mulByNEndoAlgHom (W := W) n h).fieldRange W.FunctionField := by
  haveI := finite_torsionNMul_of_ne_zero (W := W) h2 hn
  haveI : Normal ↥(fixedFieldN W n) W.FunctionField := inferInstanceAs
    (Normal ↥(FixedPoints.subfield (TorsionNMul W n) W.FunctionField) W.FunctionField)
  rw [fixedFieldN_eq_mulByNFieldRange_of_ne_zero h2 hn]
  infer_instance

open Classical in
/-- **`F(W)` is separable over `[n]∗F(W)` at every `n` with `(2 : F) ≠ 0` and `(n : F) ≠ 0`.**

⚠️ This is the one place where the general package is not merely the `3`-smooth proof with a
substituted input, and it is worth saying why.  `EllipticCurves.FunctionField.MulByNSeparable`
manufactures separability by *multiplying up* from `n = 2` and `n = 3`
(`isSeparable_mulByNFieldRange_two_pow_mul_three_pow`), which is exactly where the `3`-smoothness of
that file is created — a composition ladder can only reach the primes it starts from.  Here
separability is instead read off the **same** fixed field the normality comes from
(`FixedPoints.isSeparable`, an instance for any finite group), so it costs one line and knows no
primes at all.

⚠️ The tower route is **kept and is not superseded in scope**: it is the only proof of separability
in this development that does not need `#E[n] = n²`, hence the only one that survives if the count
is ever weakened.  What it is no longer is *load-bearing* — see `MulByNSeparable`'s module
docstring. -/
theorem isSeparable_mulByNFieldRange_of_ne_zero [IsAlgClosed F] (h2 : (2 : F) ≠ 0) {n : ℕ}
    (hn : (n : F) ≠ 0) (h : Transcendental F (n • genericPoint (W := W)).xCoord) :
    Algebra.IsSeparable ↥(mulByNEndoAlgHom (W := W) n h).fieldRange W.FunctionField := by
  haveI := finite_torsionNMul_of_ne_zero (W := W) h2 hn
  haveI : Algebra.IsSeparable ↥(fixedFieldN W n) W.FunctionField := inferInstanceAs
    (Algebra.IsSeparable ↥(FixedPoints.subfield (TorsionNMul W n) W.FunctionField)
      W.FunctionField)
  rw [fixedFieldN_eq_mulByNFieldRange_of_ne_zero h2 hn]
  infer_instance

/-- **`F(W) / [n]∗F(W)` is Galois at every `n` with `(2 : F) ≠ 0` and `(n : F) ≠ 0`.**  Both halves
now come from the same fixed field. -/
theorem isGalois_mulByNFieldRange_of_ne_zero [IsAlgClosed F] (h2 : (2 : F) ≠ 0) {n : ℕ}
    (hn : (n : F) ≠ 0) (h : Transcendental F (n • genericPoint (W := W)).xCoord) :
    IsGalois ↥(mulByNEndoAlgHom (W := W) n h).fieldRange W.FunctionField :=
  haveI := isSeparable_mulByNFieldRange_of_ne_zero (W := W) h2 hn h
  haveI := normal_mulByNFieldRange_of_ne_zero (W := W) h2 hn h
  ⟨⟩

/-- **Normality in the `Subfield` presentation** at every `n` with `(2 : F) ≠ 0` and
`(n : F) ≠ 0`, carried across `mulByNFieldRangeEquivSubfield`. -/
theorem normal_mulByNEndoFieldRange_of_ne_zero [IsAlgClosed F] (h2 : (2 : F) ≠ 0) {n : ℕ}
    (hn : (n : F) ≠ 0) (h : Transcendental F (n • genericPoint (W := W)).xCoord) :
    Normal ↥(mulByNEndo (W := W) n h).fieldRange W.FunctionField := by
  haveI := normal_mulByNFieldRange_of_ne_zero (W := W) h2 hn h
  exact Normal.of_equiv_equiv (f := mulByNFieldRangeEquivSubfield n h)
    (g := RingEquiv.refl W.FunctionField) (by ext a; rfl)

/-- **Separability in the `Subfield` presentation** at every `n` with `(2 : F) ≠ 0` and
`(n : F) ≠ 0` — the form a consumer that has to write `ValuationSubring ↥L` wants, and the entry
`IsIntegralClosure.finite` asks for by name. -/
theorem isSeparable_mulByNEndoFieldRange_of_ne_zero [IsAlgClosed F] (h2 : (2 : F) ≠ 0) {n : ℕ}
    (hn : (n : F) ≠ 0) (h : Transcendental F (n • genericPoint (W := W)).xCoord) :
    Algebra.IsSeparable ↥(mulByNEndo (W := W) n h).fieldRange W.FunctionField := by
  haveI := isSeparable_mulByNFieldRange_of_ne_zero (W := W) h2 hn h
  exact Algebra.IsSeparable.of_equiv_equiv (mulByNFieldRangeEquivSubfield n h)
    (RingEquiv.refl W.FunctionField) (by ext a; rfl)

/-- **`F(W) / [n]∗F(W)` is Galois, in the `Subfield` presentation**, at every `n` with
`(2 : F) ≠ 0` and `(n : F) ≠ 0`. -/
theorem isGalois_mulByNEndoFieldRange_of_ne_zero [IsAlgClosed F] (h2 : (2 : F) ≠ 0) {n : ℕ}
    (hn : (n : F) ≠ 0) (h : Transcendental F (n • genericPoint (W := W)).xCoord) :
    IsGalois ↥(mulByNEndo (W := W) n h).fieldRange W.FunctionField :=
  haveI := isSeparable_mulByNEndoFieldRange_of_ne_zero (W := W) h2 hn h
  haveI := normal_mulByNEndoFieldRange_of_ne_zero (W := W) h2 hn h
  ⟨⟩

/-! ### `n = 5`, the index the whole front stopped at

⚠️ `MulByNSeparable`'s scope section, `ThreePrimary` and this file all say in terms that *"the first
index this does not cover is `n = 5`"*.  That sentence is false on the function-field front as of
this section, and the statements below are the machine-checked reason — named rather than left as
`example`s so that a reader can grep for them and a consumer can cite them.

`5` is the smallest index that is neither `3`-smooth nor covered by the merged `n = 2` / `n = 3`
packages, and `EllipticCurves.FunctionField.MulByNDegreeGeneral` already carries the degree there.
⚠️ These are stated over an arbitrary algebraically closed `F` with `(5 : F) ≠ 0`; the concrete
instantiation on a committed curve is in the non-vacuity section below. -/

/-- **`[F(W) : [5]∗F(W)] = 25` and `Fixed(E[5]) = [5]∗F(W)`** — the sandwich at `n = 5`. -/
theorem fixedFieldN_eq_mulByNFieldRange_five [IsAlgClosed F] (h2 : (2 : F) ≠ 0) (h5 : (5 : F) ≠ 0) :
    (mulByNEndoAlgHom (W := W) 5
        (transcendental_xCoord_nsmul_genericPoint_of_intCast_ne_zero h2
          (by simpa using h5))).fieldRange = fixedFieldN W 5 :=
  fixedFieldN_eq_mulByNFieldRange_of_ne_zero h2 (by exact_mod_cast h5) _

/-- **`F(W)` is separable over `[5]∗F(W)`** — the statement `MulByNSeparable`'s composition ladder
provably cannot reach, since `5` is not a product of `2`s and `3`s. -/
theorem isSeparable_mulByNFieldRange_five [IsAlgClosed F] (h2 : (2 : F) ≠ 0) (h5 : (5 : F) ≠ 0) :
    Algebra.IsSeparable ↥(mulByNEndoAlgHom (W := W) 5
      (transcendental_xCoord_nsmul_genericPoint_of_intCast_ne_zero h2
        (by simpa using h5))).fieldRange W.FunctionField :=
  isSeparable_mulByNFieldRange_of_ne_zero h2 (by exact_mod_cast h5) _

/-- **`F(W) / [5]∗F(W)` is Galois.** -/
theorem isGalois_mulByNFieldRange_five [IsAlgClosed F] (h2 : (2 : F) ≠ 0) (h5 : (5 : F) ≠ 0) :
    IsGalois ↥(mulByNEndoAlgHom (W := W) 5
      (transcendental_xCoord_nsmul_genericPoint_of_intCast_ne_zero h2
        (by simpa using h5))).fieldRange W.FunctionField :=
  isGalois_mulByNFieldRange_of_ne_zero h2 (by exact_mod_cast h5) _

/-- **`F(W) / [5]∗F(W)` is Galois, in the `Subfield` presentation** — the form the place machinery
consumes, and therefore the one that matters for `MulByNInertia` and `MulByNFibre`. -/
theorem isGalois_mulByNEndoFieldRange_five [IsAlgClosed F] (h2 : (2 : F) ≠ 0) (h5 : (5 : F) ≠ 0) :
    IsGalois ↥(mulByNEndo (W := W) 5
      (transcendental_xCoord_nsmul_genericPoint_of_intCast_ne_zero h2
        (by simpa using h5))).fieldRange W.FunctionField :=
  isGalois_mulByNEndoFieldRange_of_ne_zero h2 (by exact_mod_cast h5) _

/-! ### Consistency with the merged `n = 2` and `n = 3` packages

⚠️ **The two `3`-smooth certificates below are strictly weaker than the merged statements they
reproduce**, and that was the reportable finding when they were written:
`isGalois_mulByTwoFieldRange_of_isAlgClosed` needs only `(2 : F) ≠ 0`, whereas the `3`-smooth route
needs `(3 : F) ≠ 0` as well, because `card_torsionNMul` — the right-hand side of Artin's theorem —
runs through `card_torsion_eq_sq_of_smooth`, which carries both.

⚠️ **That gap is closed by the general package, and `isGalois_mulByNFieldRange_two_of_ne_zero` is
the proof.**  `card_torsionNMul_of_ne_zero` carries no `(3 : F) ≠ 0`, so the general route at
`n = 2` needs exactly `(2 : F) ≠ 0` — the merged statement's own hypothesis set, reproduced with
nothing to spare.  The two `3`-smooth certificates are kept unchanged as the record of what the
`3`-smooth route can and cannot do; callers should prefer the merged names at `n = 2` and `n = 3`
regardless, since these exist to check that the constructions agree where both are defined, in the
same spirit as `mulByNEndoAlgHom_two`/`_three`. -/

/-- **The general-`n` Galois package at `n = 2` reproduces the merged `n = 2` package.**  A
certificate, not new API: strictly weaker than `isGalois_mulByTwoFieldRange_of_isAlgClosed`, which
does not need `(3 : F) ≠ 0`. -/
theorem isGalois_mulByNFieldRange_two [IsAlgClosed F] (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) :
    IsGalois ↥(mulByTwoEndoAlgHom (W := W) h2).fieldRange W.FunctionField := by
  have hfac : ∀ p ∈ Nat.primeFactors 2, p = 2 ∨ p = 3 := by
    intro p hp
    obtain ⟨hp1, hp2, -⟩ := Nat.mem_primeFactors.mp hp
    exact Or.inl ((Nat.prime_dvd_prime_iff_eq hp1 Nat.prime_two).mp hp2)
  have hg := isGalois_mulByNFieldRange_of_smooth (W := W) h2 h3 (n := 2) (by norm_num) hfac
    (transcendental_xCoord_two_nsmul h2)
  rwa [mulByNEndoAlgHom_two h2] at hg

/-- **The general-`n` Galois package at `n = 3` reproduces the merged `n = 3` package.**  A
certificate, not new API; here the hypotheses of the two do coincide, unlike at `n = 2`. -/
theorem isGalois_mulByNFieldRange_three [IsAlgClosed F] (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) :
    IsGalois ↥(mulByThreeEndoAlgHom (W := W) h2 h3).fieldRange W.FunctionField := by
  have hfac : ∀ p ∈ Nat.primeFactors 3, p = 2 ∨ p = 3 := by
    intro p hp
    obtain ⟨hp1, hp2, -⟩ := Nat.mem_primeFactors.mp hp
    exact Or.inr ((Nat.prime_dvd_prime_iff_eq hp1 Nat.prime_three).mp hp2)
  have hg := isGalois_mulByNFieldRange_of_smooth (W := W) h2 h3 (n := 3) (by norm_num) hfac
    (transcendental_xCoord_three_nsmul h2 h3)
  rwa [mulByNEndoAlgHom_three h2 h3] at hg

/-- **The general-`n` Galois package at `n = 2` reproduces the merged `n = 2` package with no
hypothesis to spare.**  Unlike `isGalois_mulByNFieldRange_two`, this needs only `(2 : F) ≠ 0` —
`card_torsionNMul_of_ne_zero` does not carry `(3 : F) ≠ 0` — so the general route is **not** weaker
than `isGalois_mulByTwoFieldRange_of_isAlgClosed`.  Still a certificate rather than new API: a
caller at `n = 2` should use the merged name. -/
theorem isGalois_mulByNFieldRange_two_of_ne_zero [IsAlgClosed F] (h2 : (2 : F) ≠ 0) :
    IsGalois ↥(mulByTwoEndoAlgHom (W := W) h2).fieldRange W.FunctionField := by
  have hg := isGalois_mulByNFieldRange_of_ne_zero (W := W) h2 (n := 2) (by exact_mod_cast h2)
    (transcendental_xCoord_two_nsmul h2)
  rwa [mulByNEndoAlgHom_two h2] at hg

/-! ### Non-vacuity

The headline needs `[IsAlgClosed F]`, `[W.IsElliptic]`, `(2 : F) ≠ 0`, `(3 : F) ≠ 0`, `n ≠ 0`,
`3`-smoothness **and** the transcendence of `x([n]𝒫)` at once, and rests on a group whose order is
computed rather than assumed — so a curve on which the whole chain elaborates is committed rather
than quoted.

The curve is `y² + y = x³` over `AlgebraicClosure ℚ` and the index is `n = 12`, following
`TranslationActionN`, `#1219` and `#1221`: the `ℚ` curve of `MulByNComposition` cannot witness a
statement needing an algebraically closed base, and a certificate at `n = 2` or `n = 3` would prove
nothing about a general-`n` file.  ⚠️ Every hypothesis is **produced**, not assumed — in particular
the transcendence, by `transcendental_xCoord_nsmul_of_isAlgClosed`. -/

section Nonvacuity

/-! The certificate curve `y² + y = x³` is the shared `EllipticCurves.Fixture.y2AddYEqX3`, and the
base — algebraically closed, and of characteristic `0` so that `2 ≠ 0` and `3 ≠ 0` — is
`EllipticCurves.Fixture.AlgClosedQ`, whose single `[CharZero F]` instance also supplies
`IsElliptic` here. -/

open EllipticCurves.Fixture

private lemma exampleTwo : (2 : AlgClosedQ) ≠ 0 := two_ne_zero

private lemma exampleThree : (3 : AlgClosedQ) ≠ 0 := three_ne_zero_of_charZero _

/-- ⚠️ `decide` does **not** close this: `Nat.primeFactors` goes through `Nat.primeFactorsList`,
whose `Decidable` instance gets stuck on `Nat.minFac`'s well-founded recursion. -/
private lemma exampleSmoothTwelve : ∀ p ∈ Nat.primeFactors 12, p = 2 ∨ p = 3 := by
  intro p hp
  obtain ⟨hp1, hp2, -⟩ := Nat.mem_primeFactors.mp hp
  have hle : p ≤ 12 := Nat.le_of_dvd (by norm_num) hp2
  interval_cases p <;> revert hp1 hp2 <;> decide

private lemma exampleTranscendentalTwelve :
    Transcendental AlgClosedQ ((12 : ℕ) • genericPoint (W := y2AddYEqX3 AlgClosedQ)).xCoord :=
  transcendental_xCoord_nsmul_of_isAlgClosed exampleTwo (by norm_num)

open Classical in
/-- **`[F(W) : Fixed(E[12])] = 144` on a genuine curve**, by Artin. -/
example : finrank ↥(fixedFieldN (y2AddYEqX3 AlgClosedQ) 12)
    (y2AddYEqX3 AlgClosedQ).FunctionField = 144 :=
  finrank_fixedFieldN exampleTwo exampleThree (by norm_num) exampleSmoothTwelve

open Classical in
/-- **The sandwich, committed: `Fixed(E[12]) = [12]∗F(W)`.** -/
example : (mulByNEndoAlgHom (W := y2AddYEqX3 AlgClosedQ) 12 exampleTranscendentalTwelve).fieldRange
    = fixedFieldN (y2AddYEqX3 AlgClosedQ) 12 :=
  fixedFieldN_eq_mulByNFieldRange exampleTwo exampleThree (by norm_num) exampleSmoothTwelve
    exampleTranscendentalTwelve

open Classical in
/-- **`F(W)` is normal over `[12]∗F(W)`** — the deliverable, at an index no tower reaches. -/
example : Normal ↥(mulByNEndoAlgHom (W := y2AddYEqX3 AlgClosedQ) 12
    exampleTranscendentalTwelve).fieldRange (y2AddYEqX3 AlgClosedQ).FunctionField :=
  normal_mulByNFieldRange_of_smooth exampleTwo exampleThree (by norm_num) exampleSmoothTwelve
    exampleTranscendentalTwelve

open Classical in
example : IsGalois ↥(mulByNEndoAlgHom (W := y2AddYEqX3 AlgClosedQ) 12
    exampleTranscendentalTwelve).fieldRange (y2AddYEqX3 AlgClosedQ).FunctionField :=
  isGalois_mulByNFieldRange_of_smooth exampleTwo exampleThree (by norm_num) exampleSmoothTwelve
    exampleTranscendentalTwelve

open Classical in
/-- The same in the `Subfield` presentation, which is the one the place machinery consumes. -/
example : IsGalois ↥(mulByNEndo (W := y2AddYEqX3 AlgClosedQ) 12
    exampleTranscendentalTwelve).fieldRange
    (y2AddYEqX3 AlgClosedQ).FunctionField :=
  isGalois_mulByNEndoFieldRange_of_smooth exampleTwo exampleThree (by norm_num) exampleSmoothTwelve
    exampleTranscendentalTwelve

/-! ⚠️ **And the same certificates at `n = 5` on the same committed curve.**  `12` is `3`-smooth, so
a certificate there tests only the `3`-smooth package; `5` is the index at which the whole
function-field front stopped, so it is the one that shows the general package is not the `3`-smooth
one re-parametrised.  Every hypothesis is **produced** here too — in particular there is no `hfac`
to produce, which is the point. -/

private lemma exampleFive : (5 : AlgClosedQ) ≠ 0 :=
  Nat.cast_ofNat (R := AlgClosedQ) (n := 5) ▸ Nat.cast_ne_zero.mpr (by norm_num)

private lemma exampleTranscendentalFive :
    Transcendental AlgClosedQ ((5 : ℕ) • genericPoint (W := y2AddYEqX3 AlgClosedQ)).xCoord :=
  transcendental_xCoord_nsmul_of_isAlgClosed exampleTwo (by norm_num)

open Classical in
/-- **`[F(W) : Fixed(E[5])] = 25` on a genuine curve**, by Artin — at an index no `3`-smooth
statement reaches. -/
example : finrank ↥(fixedFieldN (y2AddYEqX3 AlgClosedQ) 5)
    (y2AddYEqX3 AlgClosedQ).FunctionField = 25 := by
  have h := finrank_fixedFieldN_of_ne_zero (W := y2AddYEqX3 AlgClosedQ) exampleTwo
    (n := 5) (by exact_mod_cast exampleFive)
  norm_num at h
  exact h

open Classical in
/-- **The sandwich at `n = 5`, committed: `Fixed(E[5]) = [5]∗F(W)`.** -/
example : (mulByNEndoAlgHom (W := y2AddYEqX3 AlgClosedQ) 5 exampleTranscendentalFive).fieldRange
    = fixedFieldN (y2AddYEqX3 AlgClosedQ) 5 :=
  fixedFieldN_eq_mulByNFieldRange_of_ne_zero exampleTwo (by exact_mod_cast exampleFive)
    exampleTranscendentalFive

open Classical in
/-- **`F(W)` is separable over `[5]∗F(W)`** — what `MulByNSeparable`'s composition ladder cannot
reach on any hypotheses, since `5` is not a product of `2`s and `3`s. -/
example : Algebra.IsSeparable ↥(mulByNEndoAlgHom (W := y2AddYEqX3 AlgClosedQ) 5
    exampleTranscendentalFive).fieldRange (y2AddYEqX3 AlgClosedQ).FunctionField :=
  isSeparable_mulByNFieldRange_of_ne_zero exampleTwo (by exact_mod_cast exampleFive)
    exampleTranscendentalFive

open Classical in
/-- **`F(W)` is normal over `[5]∗F(W)`** — the deliverable, at the index the front stopped at. -/
example : Normal ↥(mulByNEndoAlgHom (W := y2AddYEqX3 AlgClosedQ) 5
    exampleTranscendentalFive).fieldRange (y2AddYEqX3 AlgClosedQ).FunctionField :=
  normal_mulByNFieldRange_of_ne_zero exampleTwo (by exact_mod_cast exampleFive)
    exampleTranscendentalFive

open Classical in
/-- **`F(W) / [5]∗F(W)` is Galois, in the `Subfield` presentation** — the form the place machinery
consumes. -/
example : IsGalois ↥(mulByNEndo (W := y2AddYEqX3 AlgClosedQ) 5
    exampleTranscendentalFive).fieldRange (y2AddYEqX3 AlgClosedQ).FunctionField :=
  isGalois_mulByNEndoFieldRange_of_ne_zero exampleTwo (by exact_mod_cast exampleFive)
    exampleTranscendentalFive

end Nonvacuity

end CoordinateRing

end WeierstrassCurve.Affine
