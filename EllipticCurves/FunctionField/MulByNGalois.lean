/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import EllipticCurves.Fixtures
import EllipticCurves.FunctionField.MulByNSeparable
import EllipticCurves.FunctionField.TranslationActionN
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.FieldTheory.IntermediateField.Algebraic

/-!
# `F(W)` is Galois over `[n]∗F(W)` at every `3`-smooth `n`, with group `E[n]`

`EllipticCurves.FunctionField.TranslationActionN` (`#1232`) builds the group `G = E[n]` of
translations by `n`-torsion points, acting faithfully on `F(W)` by `F`-algebra automorphisms, with
`Nat.card G = n²` over an algebraically closed base field of characteristic `≠ 2, 3` at every
`3`-smooth `n`, and proves the inclusion `[n]∗F(W) ⊆ Fixed(G)`.  This file closes the sandwich:

```
[n]∗F(W)  ⊆  Fixed(G)  ⊆  F(W),     [F(W) : [n]∗F(W)] = n² = |G| = [F(W) : Fixed(G)]
```

so `Fixed(G) = [n]∗F(W)` exactly, whence `F(W) / [n]∗F(W)` is **Galois** — and in particular
**normal, in every characteristic `≠ 2, 3`**, with no `CharZero` anywhere.

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

⚠️ **It is not new in the weaker sense either: the hypotheses are identical.**  Checked rather than
assumed — `isSeparable_mulByNFieldRange_of_smooth` carries exactly `[IsAlgClosed F]`, `(2 : F) ≠ 0`,
`(3 : F) ≠ 0`, `n ≠ 0`, `3`-smoothness and the transcendence of `x([n]𝒫)`, and so does everything
below.  Neither statement subsumes the other; they are **equal in range**, and the two proofs are
genuinely independent (a tower of merged `n = 2`/`n = 3` extensions there, Artin's theorem against a
translation action here).  This file therefore mints **no** separability declaration of its own —
`isGalois_mulByNFieldRange_of_smooth` consumes `#1219`'s, and a consumer that wants only
separability should keep using `#1219`'s name.

⚠️ The one place the ranges do *not* match is `isSeparable_mulByNEndoFieldRange_of_charZero`
(`EllipticCurves.FunctionField.MulByNInertia`, `#1221`), which is `CharZero` and carries **no**
`3`-smoothness, so it reaches `n = 5` where nothing here does.  It gives separability only.

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
* `isGalois_mulByNFieldRange_two` and `isGalois_mulByNFieldRange_three` — consistency certificates
  against the merged `n = 2` and `n = 3` packages.  ⚠️ **Both are strictly weaker than the merged
  statements they reproduce** and are certificates, not new API; see their docstrings.

## How to fire these

`(2 : F) ≠ 0` and `(3 : F) ≠ 0` are hypotheses rather than typeclasses, so none of the results below
can be an `instance`; a consumer writes

```lean
haveI := isGalois_mulByNEndoFieldRange_of_smooth (W := W) h2 h3 hn hfac h
```

and then applies whatever wanted `[IsGalois ↥(mulByNEndo n h).fieldRange F(W)]`.  Same shape as
`finite_torsionNMul` in `TranslationActionN`, and for the same reason.

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
* **Nothing at `n = 5`.**  Both outer degrees are `3`-smooth — `card_torsion_eq_sq_of_smooth` and
  `#1213`'s degree — so the sandwich has no side there.  The composition law manufactures no new
  prime and `IsGalois` does not either.
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

/-! ### Consistency with the merged `n = 2` and `n = 3` packages

⚠️ **Both certificates below are strictly weaker than the merged statements they reproduce**, and
that is the reportable finding, not a defect: `isGalois_mulByTwoFieldRange_of_isAlgClosed` needs
only `(2 : F) ≠ 0`, whereas the general-`n` route needs `(3 : F) ≠ 0` as well, because
`card_torsionNMul` — the right-hand side of Artin's theorem — runs through
`card_torsion_eq_sq_of_smooth`, which carries both.  So the general theorem does **not** subsume
either merged one; callers at `n = 2` and `n = 3` should keep using the merged names.  These exist
to check that the two constructions agree where both are defined, in the same spirit as
`mulByNEndoAlgHom_two`/`_three`. -/

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

end Nonvacuity

end CoordinateRing

end WeierstrassCurve.Affine
