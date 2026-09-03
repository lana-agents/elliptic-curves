/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import EllipticCurves.Fixtures
import EllipticCurves.TateModule.DeterminantModSmooth
import EllipticCurves.Torsion.StructureGeneral

/-!
# `E[n]` is free of rank `2` over `ZMod n` at EVERY `n` with `(n : F) ≠ 0`

`EllipticCurves.TateModule.DeterminantModSmooth` proves that `E[n]` is a finite free `ZMod n`-module
of rank `2` — so that `galoisDetMod n` is an honest determinant and not `LinearEquiv.det`'s junk
value — at every **`3`-smooth** `n > 1`.  This file removes the smoothness, and nothing else: the
five statements below are that file's five with `_of_smooth` replaced by `_of_natCast_ne_zero` and
`hfac` replaced by `(n : F) ≠ 0`.

The mathematics is entirely in `EllipticCurves.Torsion.StructureGeneral`, whose
`nonempty_torsion_addEquiv` is `E[n] ≃+ ℤ/nℤ × ℤ/nℤ` at every `n` with `(2 : F) ≠ 0` and
`(n : F) ≠ 0`.  Every proof here is `DeterminantModSmooth`'s proof with that theorem substituted for
`nonempty_torsion_addEquiv_zmod_sq_of_smooth`, and **no argument of any kind is made below**.

⚠️ **`(n : F) ≠ 0` is sharp and is not a relaxed smoothness.**  At `n = char F` the conclusion is
*false*: `E[p]` over a field of characteristic `p` is `0` or `ℤ/pℤ`, never `(ℤ/pℤ)²`, so its rank
over `ZMod p` is `0` or `1`.  What the hypothesis buys is `n = 10, 14, 35, 91, …` — every index
`DeterminantModSmooth` cannot state at any hypotheses — and the *Non-vacuity* block certifies the
first of those on a curve that exists.

## Why this is a new file and not four new theorems in `DeterminantModSmooth`

⚠️ **`#1549` left the placement open and it is the only real cost on this front, so it is measured
rather than argued.**  `EllipticCurves.Torsion.StructureGeneral` is not in
`DeterminantModSmooth`'s import closure and pulling it in there costs **+34 modules** (37 → 71),
nearly doubling that file, and **+34** again in `EllipticCurves.TateModule.MatrixRepMod` (40 → 74),
which imports it.  As a leaf the same edge costs **0** to every existing file and the general forms
are still available to every future consumer by one import.

This is the shape `EllipticCurves.TateModule.OpenKernelGeneral`,
`EllipticCurves.TateModule.FreeGeneral` and `EllipticCurves.TateModule.MatrixRepGeneral` already
use for exactly this situation, and the `_of_natCast_ne_zero` suffix is theirs.

## What is NOT here

* **`n = 2`.**  `finite_torsion_two_zmod`, `finrank_torsion_two` and `basisTorsionTwo` stay in
  `DeterminantModSmooth`.  They are proved from `card_torsion_two` on `h2` **alone**, and routing
  them through this file would charge them `(2 : F) ≠ 0` twice over — once as `h2` and once as
  `((2 : ℕ) : F) ≠ 0` — for a count that needs neither.  Nothing here subsumes them.
* **Deletions.**  Every `_of_smooth` statement is kept.  They are an independent route: a consumer
  holding `hfac` reaches them without `EllipticCurves.Torsion.StructureGeneral` in its closure, and
  that is the whole reason the split above is worth having.  The *Subsumption* block below compiles
  the containment rather than asserting it.
* **`det ρ_{E,n} = χ_n`.**  Unchanged from `DeterminantModSmooth`: this file widens the indices at
  which the left-hand side is well defined and says nothing about the identification, which needs
  the Weil pairing.
* **The trace and the characteristic polynomial mod `n`.**  Still no consumer, at any `n`.

## Main statements

* `WeierstrassCurve.Affine.nonempty_torsionLinearEquiv_of_natCast_ne_zero` —
  `E[n] ≃ₗ[ZMod n] ZMod n × ZMod n`.  The reusable brick; everything else is a projection of it,
  except the finiteness.
* `WeierstrassCurve.Affine.finite_torsion_zmod_of_natCast_ne_zero` — `E[n]` is a finite
  `ZMod n`-module.  ⚠️ **Wider than its `_of_smooth` twin in a second direction**, see below.
* `WeierstrassCurve.Affine.free_torsion_zmod_of_natCast_ne_zero` — and a free one.
* `WeierstrassCurve.Affine.finrank_torsion_of_natCast_ne_zero` — of rank `2`, for `1 < n`.

## Main definitions

* `WeierstrassCurve.Affine.basisTorsionOfNatCastNeZero` — a `Fin 2`-indexed `ZMod n`-basis.
  ⚠️ Not canonical, and `basisTorsionThree`'s warning applies verbatim: any statement proved with it
  must be one whose truth does not depend on which basis is chosen.  `galoisDetMod` uses none of
  them, deliberately — `LinearEquiv.det` is basis-free.

## Hypotheses, and the one place this file is wider than a re-indexing

⚠️ `finite_torsion_zmod_of_natCast_ne_zero` `omit`s **both** `[IsAlgClosed F]` and `[W.IsElliptic]`,
where `finite_torsion_zmod_of_smooth` can only omit the first.  That is not bookkeeping: its input
is `finite_torsion_of_intCast_ne_zero` (`EllipticCurves.Torsion.XSupport`), which counts the
`x`-support of `ΨSqₙ` and needs no elliptic structure at all, whereas `finite_torsion_of_smooth`
sits in a `section Smooth` carrying `[W.IsElliptic]`.  So the finiteness half of this file holds
over **any** field with `(2 : F) ≠ 0` and `(n : F) ≠ 0`, algebraically closed or not.  The other
three genuinely need both instances, through `nonempty_torsion_addEquiv`.

⚠️ `1 < n` is inherited unchanged from `finrank_torsion_of_smooth` and is still not bookkeeping: at
`n = 1` the hypothesis `(1 : F) ≠ 0` holds, `ZMod 1` is the trivial ring, and the rank is `1`.
`DeterminantModSmooth`'s *Non-vacuity* block states that as a theorem; it is not restated here.

⚠️ `[NeZero n]` is redundant given `(n : F) ≠ 0` and is kept because it is not derivable *in the
statement*: `torsionZModModule` takes it as an instance argument, so without it the `ZMod n`-module
structure on `E[n]` — and hence `≃ₗ[ZMod n]`, `Module.Finite`, `Module.Free` and `Module.finrank` —
does not elaborate.  The same binder for the same reason is on every statement of
`DeterminantModSmooth`'s `section Smooth`.

## References

* [J. H. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.7.
-/

namespace WeierstrassCurve.Affine

open scoped AddSubgroup

variable {F : Type*} [Field F] [DecidableEq F] {W : Affine F} [W.IsElliptic] [IsAlgClosed F]

/-! ### Every `n` with `(n : F) ≠ 0` -/

section General

variable {n : ℕ} [NeZero n]

open Classical in
/-- **`E[n] ≅ (ℤ/nℤ)²` as `ZMod n`-modules, at every `n` with `(n : F) ≠ 0`.**

`nonempty_torsion_addEquiv` (`EllipticCurves.Torsion.StructureGeneral`, `#242`) produces an `≃+`,
and `AddEquiv.toZModLinearEquiv` (`EllipticCurves.TateModule.DeterminantMod`) upgrades it for free:
the `ZMod n`-action on a group killed by `n` is determined by the additive structure, so there is
nothing to check.

⚠️ The general-`n` form of `nonempty_torsionLinearEquiv_of_smooth`, and this is the only place the
smoothness is spent — the four declarations after it consume this one, or `Torsion.XSupport`, and
never `hfac`.

⚠️ A `Nonempty` rather than a chosen isomorphism, because there is no canonical one.  Consumers that
want a *number* should take it from `finrank_torsion_of_natCast_ne_zero` below rather than
destructing this. -/
theorem nonempty_torsionLinearEquiv_of_natCast_ne_zero (h2 : (2 : F) ≠ 0) (hn : (n : F) ≠ 0) :
    Nonempty (W.torsion n ≃ₗ[ZMod n] ZMod n × ZMod n) :=
  (nonempty_torsion_addEquiv h2 hn).map AddEquiv.toZModLinearEquiv

omit [W.IsElliptic] [IsAlgClosed F] in
open Classical in
/-- **`E[n]` is a finite `ZMod n`-module, at every `n` with `(n : F) ≠ 0`.**

⚠️ **The one statement in this file that is wider than a re-indexing of its `_of_smooth` twin.**
`finite_torsion_zmod_of_smooth` omits `[IsAlgClosed F]` and keeps `[W.IsElliptic]`, because
`finite_torsion_of_smooth` sits in a `section Smooth` that carries it.  The input here is
`finite_torsion_of_intCast_ne_zero` (`EllipticCurves.Torsion.XSupport`), which bounds `E[n]` by the
`x`-support of `ΨSqₙ` and asks for no elliptic structure and no algebraic closure, so **both**
instances come off.

⚠️ Taken from that theorem and not from `nonempty_torsionLinearEquiv_of_natCast_ne_zero`, which
would have supplied it in one line and dragged both instances back in — the same economy
`finite_torsion_zmod_of_smooth` and `finite_torsion_three_zmod` practise.

⚠️ It cannot be an `instance`: it carries `(2 : F) ≠ 0` and `(n : F) ≠ 0`. -/
theorem finite_torsion_zmod_of_natCast_ne_zero (h2 : (2 : F) ≠ 0) (hn : (n : F) ≠ 0) :
    Module.Finite (ZMod n) (W.torsion n) :=
  haveI := W.finite_torsion_of_intCast_ne_zero h2 hn
  Module.Finite.of_finite

open Classical in
/-- **`E[n]` is a free `ZMod n`-module, at every `n` with `(n : F) ≠ 0`.**

⚠️ A theorem and not a certificate, for the reason `free_torsion_zmod_of_smooth` gives: `ZMod n` is
a field only at prime `n`, `Module.Free (ZMod 10) E[10]` is not found by instance search, and the
transported basis is the only source of freeness there is.

⚠️ It cannot be an `instance`: it carries `(2 : F) ≠ 0` and `(n : F) ≠ 0`. -/
theorem free_torsion_zmod_of_natCast_ne_zero (h2 : (2 : F) ≠ 0) (hn : (n : F) ≠ 0) :
    Module.Free (ZMod n) (W.torsion n) := by
  obtain ⟨e⟩ := nonempty_torsionLinearEquiv_of_natCast_ne_zero (W := W) h2 hn
  exact Module.Free.of_equiv e.symm

open Classical in
/-- **`E[n]` has rank `2` over `ZMod n`, at every `n > 1` with `(n : F) ≠ 0`.**

The discriminating statement of the file, exactly as `finrank_torsion_of_smooth` is of its own:
`Module.finrank` is `1` over a trivial ring and `0` on a module that is not free and finite, so this
is simultaneously the rank computation *and* the certificate that `galoisDetMod n` is not returning
`LinearEquiv.det`'s junk value.

⚠️ **`1 < n` still excludes a genuine counterexample.**  At `n = 1` the hypothesis `(1 : F) ≠ 0`
holds, `ZMod 1` is the trivial ring, and `Module.finrank_subsingleton` puts the rank at `1`;
`EllipticCurves.TateModule.DeterminantModSmooth`'s *Non-vacuity* block states that as a theorem and
it is not restated here.  Mechanically, `1 < n` is what produces `Fact (1 < n)`, hence
`Nontrivial (ZMod n)`, hence the `StrongRankCondition (ZMod n)` that `Module.finrank_prod` requires.

⚠️ Proved from a chosen isomorphism, unlike `finrank_torsion_three`, which goes through
`Module.card_eq_pow_finrank` precisely to avoid one.  Neither replaces the other; see
`DeterminantModSmooth`'s module docstring, whose argument is unaffected by the widening. -/
theorem finrank_torsion_of_natCast_ne_zero (h2 : (2 : F) ≠ 0) (hn1 : 1 < n) (hn : (n : F) ≠ 0) :
    Module.finrank (ZMod n) (W.torsion n) = 2 := by
  haveI : Fact (1 < n) := ⟨hn1⟩
  obtain ⟨e⟩ := nonempty_torsionLinearEquiv_of_natCast_ne_zero (W := W) h2 hn
  rw [e.finrank_eq, Module.finrank_prod, Module.finrank_self]

open Classical in
/-- **A `ZMod n`-basis of `E[n]` indexed by `Fin 2`, at every `n > 1` with `(n : F) ≠ 0`.**

`Module.finBasisOfFinrankEq` against `finrank_torsion_of_natCast_ne_zero`, the general-`n` mirror of
`basisTorsionOfSmooth`.  ⚠️ Not canonical — it is the interface a coordinate computation needs, and
any statement proved with it must be one whose truth does not depend on which basis is chosen.
`galoisDetMod` does **not** use it, deliberately: `LinearEquiv.det` is basis-free. -/
noncomputable def basisTorsionOfNatCastNeZero (h2 : (2 : F) ≠ 0) (hn1 : 1 < n) (hn : (n : F) ≠ 0) :
    Module.Basis (Fin 2) (ZMod n) (W.torsion n) :=
  haveI : Fact (1 < n) := ⟨hn1⟩
  haveI := finite_torsion_zmod_of_natCast_ne_zero (W := W) h2 hn
  haveI := free_torsion_zmod_of_natCast_ne_zero (W := W) h2 hn
  Module.finBasisOfFinrankEq _ _ (finrank_torsion_of_natCast_ne_zero h2 hn1 hn)

end General

/-! ### Subsumption

⚠️ **Compiled, not asserted.**  The claim *"`3`-smooth `n ≠ 0` with `(2 : F) ≠ 0` and `(3 : F) ≠ 0`
forces `(n : F) ≠ 0`"* is a short argument about `Nat.primeFactors` and not a restatement, and this
board's standing rule is that a containment of that kind is stated as an `example` that restates the
subsumed theorem *verbatim* and proves it from the general layer.

The bridge is `Nat.intCast_ne_zero_of_smooth` (`EllipticCurves.Torsion.ThreePrimary`), which gives
`((n : ℤ) : F) ≠ 0`; the `Nat` form the statements above take is one `exact_mod_cast` away.

⚠️ The four `example`s below restate `DeterminantModSmooth`'s four `_of_smooth` statements binder
for binder.  ⚠️ The `def` `basisTorsionOfSmooth` has no `example` — a definition cannot be restated
as a proposition, and what would be checked of it (that a basis exists) is
`nonempty_torsionLinearEquiv_of_natCast_ne_zero` and is certified below at `n = 10` instead. -/

section Subsumption

variable {n : ℕ} [NeZero n]

open Classical in
/-- `nonempty_torsionLinearEquiv_of_smooth`, restated verbatim and proved from the general layer. -/
example (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0)
    (hfac : ∀ p ∈ n.primeFactors, p = 2 ∨ p = 3) :
    Nonempty (W.torsion n ≃ₗ[ZMod n] ZMod n × ZMod n) :=
  nonempty_torsionLinearEquiv_of_natCast_ne_zero h2
    (by exact_mod_cast Nat.intCast_ne_zero_of_smooth h2 h3 (NeZero.ne n) hfac)

omit [W.IsElliptic] [IsAlgClosed F] in
open Classical in
/-- `finite_torsion_zmod_of_smooth`, restated verbatim and proved from the general layer. -/
example (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0)
    (hfac : ∀ p ∈ n.primeFactors, p = 2 ∨ p = 3) : Module.Finite (ZMod n) (W.torsion n) :=
  finite_torsion_zmod_of_natCast_ne_zero h2
    (by exact_mod_cast Nat.intCast_ne_zero_of_smooth h2 h3 (NeZero.ne n) hfac)

open Classical in
/-- `free_torsion_zmod_of_smooth`, restated verbatim and proved from the general layer. -/
example (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0)
    (hfac : ∀ p ∈ n.primeFactors, p = 2 ∨ p = 3) : Module.Free (ZMod n) (W.torsion n) :=
  free_torsion_zmod_of_natCast_ne_zero h2
    (by exact_mod_cast Nat.intCast_ne_zero_of_smooth h2 h3 (NeZero.ne n) hfac)

open Classical in
/-- `finrank_torsion_of_smooth`, restated verbatim and proved from the general layer. -/
example (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) (hn : 1 < n)
    (hfac : ∀ p ∈ n.primeFactors, p = 2 ∨ p = 3) :
    Module.finrank (ZMod n) (W.torsion n) = 2 :=
  finrank_torsion_of_natCast_ne_zero h2 hn
    (by exact_mod_cast Nat.intCast_ne_zero_of_smooth h2 h3 (NeZero.ne n) hfac)

end Subsumption

/-! ### Non-vacuity

⚠️ **The index is `10`, and the choice is the whole point of this block.**  `12` — what
`DeterminantModSmooth` certifies at — is `3`-smooth, so a certificate there would be consistent with
this file proving nothing new.  `10 = 2 · 5` is composite, divisible by two distinct primes, and
**not `3`-smooth**, so *no* `_of_smooth` statement can state any of the four facts below at any
hypotheses.  `Nat.ten_not_smooth` (`EllipticCurves.Torsion.ThreePrimary`) is the compiled form of
that sentence and is asserted here rather than left to the reader.

The certificate curve is this front's standard one, `y² + y = x³` over `ℚ` base-changed to
`AlgebraicClosure ℚ`, as `EllipticCurves.TateModule.DeterminantModSmooth` and
`EllipticCurves.TateModule.MatrixRepMod` use.  This block declares no fixture of its own (`#1408`).
-/

section Nonvacuity

open EllipticCurves.Fixture

private lemma exampleTwo : (2 : AlgClosedQ) ≠ 0 := two_ne_zero

private lemma exampleTen : ((10 : ℕ) : AlgClosedQ) ≠ 0 := by norm_num

/-- **⚠️ `10` is NOT `3`-smooth**, so every statement in this block is out of reach of
`EllipticCurves.TateModule.DeterminantModSmooth` at any hypotheses.  This is the assertion that
makes the certificates below evidence of a widening rather than of a re-indexing. -/
example : ¬ (∀ p ∈ (10 : ℕ).primeFactors, p = 2 ∨ p = 3) := Nat.ten_not_smooth

open Classical in
/-- **⚠️ THE LOAD-BEARING CERTIFICATE**: on a curve that exists and at an index that is *not*
`3`-smooth, `E[10]` really has rank `2` over `ZMod 10`, so `LinearEquiv.det` is not returning its
junk value there. -/
example : Module.finrank (ZMod 10) (((y2AddYEqX3 ℚ)⁄AlgClosedQ).torsion 10) = 2 :=
  finrank_torsion_of_natCast_ne_zero exampleTwo (by norm_num) exampleTen

open Classical in
/-- Freeness at `10`, where `inferInstance` fails — `ZMod 10` is not a field. -/
example : Module.Free (ZMod 10) (((y2AddYEqX3 ℚ)⁄AlgClosedQ).torsion 10) :=
  free_torsion_zmod_of_natCast_ne_zero exampleTwo exampleTen

open Classical in
/-- Finiteness at `10`. -/
example : Module.Finite (ZMod 10) (((y2AddYEqX3 ℚ)⁄AlgClosedQ).torsion 10) :=
  finite_torsion_zmod_of_natCast_ne_zero exampleTwo exampleTen

open Classical in
/-- A `ZMod 10`-basis on the same curve — the interface a coordinate computation would consume, and
the input `EllipticCurves.TateModule.MatrixRepModGeneral` takes. -/
example : Nonempty (Module.Basis (Fin 2) (ZMod 10) (((y2AddYEqX3 ℚ)⁄AlgClosedQ).torsion 10)) :=
  ⟨basisTorsionOfNatCastNeZero exampleTwo (by norm_num) exampleTen⟩

end Nonvacuity

end WeierstrassCurve.Affine
