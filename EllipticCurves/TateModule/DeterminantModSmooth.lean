/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import EllipticCurves.Fixtures
import EllipticCurves.TateModule.DeterminantMod
import EllipticCurves.Torsion.ThreePrimary

/-!
# `E[n]` is free of rank `2` over `ZMod n` at every `3`-smooth `n`

`EllipticCurves.TateModule.DeterminantMod` defines the mod-`n` determinant character
`galoisDetMod n : (F ≃ₐ[S] F) →* (ZMod n)ˣ` at **every** `n` with `[NeZero n]` and no other
hypothesis, and says of it, correctly, that it is

> ⚠️ Definable with no hypotheses at all, and *worthless* without freeness: `LinearMap.det` is `1`
> on a module that is not free and finite.

The statement that rules the junk value out was available at `n = 3` and nowhere else.  This file
supplies it at **every `3`-smooth `n`**: `E[n]` is a finite free `ZMod n`-module of rank `2`, so
`galoisDetMod n` is an honest determinant at `n = 2, 3, 4, 6, 8, 9, 12, …`.

⚠️ **`3`-smooth is no longer the ceiling of the development, only of this file.**
`EllipticCurves.TateModule.DeterminantModGeneral` proves the same four statements at every `n` with
`(n : F) ≠ 0` — so also at `n = 10, 14, 35, 91, …` — from
`EllipticCurves.Torsion.StructureGeneral`.  It is a **leaf** and not an edit of this file because
that import costs **+34 modules** here and +34 again in
`EllipticCurves.TateModule.MatrixRepMod`; the statements below are the route that pays neither, and
nothing here is deprecated by it.  See the `n = 5` bullet under *Explicitly out of scope*.

## Where this comes from, and why it was not done before

`EllipticCurves.TateModule.DeterminantMod`'s `## Explicitly out of scope` section priced it:

> **Finiteness and rank at general `n`.**  Only `n = 3` is done, because only `n = 3` has
> `card_torsion_three` available.  ⚠️ `n = 2` has `exists_closure_pair_eq_torsion_two` and could be
> done the same way; it is not done here because nothing consumes it.  ⚠️ And at composite `n`,
> `ZMod n` is not a field, so even freeness stops being automatic.

⚠️ **The first sentence went stale and the third is why this file is not a copy of the `n = 3`
block.**  `nonempty_torsion_addEquiv_zmod_sq_of_smooth` (`EllipticCurves.Torsion.ThreePrimary`) and
`card_torsion_eq_sq_of_smooth` landed after that text was written, and the second ingredient — that
an `≃+` between `ZMod n`-modules is automatically `ZMod n`-linear — is `AddEquiv.toZModLinearEquiv`,
which lives in the very file that prices this as out of reach.  So the whole of the mathematics is
one `Nonempty.map`:

```lean
(nonempty_torsion_addEquiv_zmod_sq_of_smooth h2 h3 (NeZero.ne n) hfac).map
  AddEquiv.toZModLinearEquiv
```

⚠️ **The third sentence, by contrast, is true and load-bearing.**  At `n = 2` and `n = 3` the ring
`ZMod n` is a field, so `Module.Free` is `inferInstance` and `DeterminantMod` deliberately states no
`free_torsion_three` on the ground that *"a theorem whose proof is `inferInstance` is noise"*.  That
reasoning does not survive to composite `n`, where the equivalence above is the only source of
freeness; the Non-vacuity section below measures the failure rather than asserting it.

## Main statements

* `WeierstrassCurve.Affine.nonempty_torsionLinearEquiv_of_smooth` —
  `E[n] ≃ₗ[ZMod n] ZMod n × ZMod n`, the `ZMod n`-linear upgrade of the merged additive structure
  theorem.  Everything else here is a projection of it, except the finiteness and the `n = 2` block.
* `WeierstrassCurve.Affine.finite_torsion_zmod_of_smooth` — `E[n]` is a finite `ZMod n`-module.
* `WeierstrassCurve.Affine.free_torsion_zmod_of_smooth` — and a free one.
* `WeierstrassCurve.Affine.finrank_torsion_of_smooth` — of rank `2`, for `1 < n`.
* `WeierstrassCurve.Affine.finite_torsion_two_zmod`, `WeierstrassCurve.Affine.finrank_torsion_two` —
  the `n = 2` named instances, on `h2` alone.  ⚠️ Their input `#E[2] = 4` is `card_torsion_two`
  (`EllipticCurves.Torsion.TwoTorsion`); it is consumed here and not reproved.

## Main definitions

* `WeierstrassCurve.Affine.basisTorsionOfSmooth`, `WeierstrassCurve.Affine.basisTorsionTwo` —
  `Fin 2`-indexed `ZMod n`-bases.  ⚠️ Neither is canonical, and `DeterminantMod`'s warning on
  `basisTorsionThree` applies verbatim: any statement proved with one must be a statement whose
  truth does not depend on which basis is chosen.  `galoisDetMod` uses none of them, deliberately —
  `LinearEquiv.det` is basis-free.

## Hypotheses, and where they are genuinely spent

⚠️ The four statements do **not** carry the same hypotheses, and the differences are not incidental.

* **Finiteness needs no algebraic closure.**  `finite_torsion_of_smooth`
  (`EllipticCurves.Torsion.Multiplicative`) proves `Finite (E[n])` from `h2`, `h3` and
  `[W.IsElliptic]` alone, so `finite_torsion_zmod_of_smooth` `omit`s `[IsAlgClosed F]`.  Deriving it
  from `nonempty_torsionLinearEquiv_of_smooth` instead would have been one line shorter and would
  have silently widened the hypotheses of the cheap half.  ⚠️ It does need `[W.IsElliptic]`, which
  sits in that file's `section Smooth` variable block (`:186`) and is invisible in its signature;
  the first draft of this file asserted otherwise and the elaborator refuted it.
* **The rank needs `1 < n`, and that is not bookkeeping.**  At `n = 1` the hypothesis `hfac` holds
  vacuously, `ZMod 1` is the trivial ring, and `Module.finrank_subsingleton` gives the rank as `1`.
  The statement is *false* at `n = 1`, not merely unproved; see the Non-vacuity section.  `1 < n` is
  what produces `Fact (1 < n)`, hence `Nontrivial (ZMod n)`, hence `StrongRankCondition (ZMod n)`,
  which is what `Module.finrank_prod` and `Module.finBasisOfFinrankEq` ask for.
* **`n = 2` is proved from `n = 2` inputs and carries no `h3`.**  Routing it through
  `finrank_torsion_of_smooth` would have cost a spurious `(3 : F) ≠ 0`, since the smooth structure
  theorem needs both characteristics even at an index divisible by neither `3` nor anything else.
  `finrank_torsion_two` is instead the exact mirror of the merged `finrank_torsion_three`:
  `Module.card_eq_pow_finrank` against `card_torsion_two`.

## ⚠️ `finrank_torsion_three` is subsumed in range and not in kind, and stays where it is

`finrank_torsion_of_smooth h2 h3 (n := 3)` has the same hypotheses as the merged
`finrank_torsion_three` and the same conclusion.  It is nevertheless **not** a replacement, for the
reason that declaration's own docstring gives: it is proved from the cardinality *specifically to
avoid* `.some`-ing an isomorphism, *"putting an arbitrary choice into the proof of a
choice-independent number"*, and `nonempty_torsionLinearEquiv_of_smooth` makes exactly that choice.
Nothing is deleted here; the de-duplication question is a separate one.

## Explicitly out of scope

* **`det ρ_{E,n} = χ_n`.**  This file supplies the *well-definedness* of the left-hand side at more
  indices and nothing else.  The identification needs the Weil pairing, which this development has
  at `n = 2` and `n = 3` only, and it is
  `galoisDetMod_three_eq_galoisModularCyclotomicChar` in
  `EllipticCurves.FunctionField.WeilPairingDeterminantCharacter`.
* **Anything at `n = 5`** — ⚠️ **out of scope of *this file*, and no longer out of reach.**  This
  bullet used to end *"i.e. the general multiplication-by-`n` coordinate formula"*, naming the two
  things behind `nonempty_torsion_addEquiv_zmod_sq_of_smooth` as missing: `[5]`-surjectivity and
  `#E[5]`.  Both landed.  `nsmul_surjective_of_two_ne_zero` is `[n]`-surjectivity at every `n ≠ 0`,
  `card_torsion_eq_sq` is `#E[n] = n²` at every `n` with `(n : F) ≠ 0`, and
  `EllipticCurves.Torsion.StructureGeneral`'s `nonempty_torsion_addEquiv` is the structure theorem
  itself there.  ⚠️ So `hfac` **is** removable, and it is removed — in
  `EllipticCurves.TateModule.DeterminantModGeneral`, which restates all four statements below with
  `hfac` replaced by `(n : F) ≠ 0` and compiles the subsumption.  What keeps it out of *this* file
  is a measured import cost and not a gate: `Torsion.StructureGeneral` is **+34 modules** here
  (37 → 71) and **+34** again in `EllipticCurves.TateModule.MatrixRepMod`, so the general layer is a
  leaf and the statements below are kept as the route that pays neither.
* **A mod-`n` matrix representation** `G →* GL (Fin 2) (ZMod n)` through `basisTorsionOfSmooth`.
  ⚠️ **Spent, and it is the only bullet in this list that was.**  It used to continue *"it is the
  finite-level analogue of `EllipticCurves.TateModule.MatrixRep`, it is basis-dependent, and it
  needs the `MatrixRepBasisChange` treatment to be worth having"*, and all three clauses were
  right: `EllipticCurves.TateModule.MatrixRepMod` (`#1242`) defines `galoisRepModMatrix` on a basis
  this file supplies, ships the conjugation law `galoisRepModMatrix_conj` the third clause asked
  for, and identifies `det ∘ ρ_{E,n}` with `galoisDetMod n`.  ⚠️ What remains out of scope of *this
  file* is only the location — that file is a consumer of `basisTorsionOfSmooth`, and nothing below
  changed when it landed.
* **The trace and the characteristic polynomial mod `n`.**  ⚠️ `DeterminantMod` records that
  `galoisTraceTwo`'s finite-level analogue *"would need the same freeness input and has no
  consumer"*.  Only the first half of that is retired here: the freeness input now exists, and the
  consumer still does not.

## References

* [J. H. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.7.
-/

namespace WeierstrassCurve.Affine

open scoped AddSubgroup

variable {F : Type*} [Field F] [DecidableEq F] {W : Affine F} [W.IsElliptic] [IsAlgClosed F]

/-! ### Every `3`-smooth `n` -/

section Smooth

variable {n : ℕ} [NeZero n]

open Classical in
/-- **`E[n] ≅ (ℤ/nℤ)²` as `ZMod n`-modules, for every `3`-smooth `n`.**

The merged structure theorem `nonempty_torsion_addEquiv_zmod_sq_of_smooth` produces an `≃+`, and
`AddEquiv.toZModLinearEquiv` (`EllipticCurves.TateModule.DeterminantMod`) upgrades it for free: the
`ZMod n`-action on a group killed by `n` is determined by the additive structure, so there is
nothing to check.

⚠️ This is the reusable brick, and it is a `Nonempty` rather than a chosen isomorphism because there
is no canonical one.  Consumers that want a *number* should take it from `finrank_torsion_of_smooth`
below rather than destructing this. -/
theorem nonempty_torsionLinearEquiv_of_smooth (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0)
    (hfac : ∀ p ∈ n.primeFactors, p = 2 ∨ p = 3) :
    Nonempty (W.torsion n ≃ₗ[ZMod n] ZMod n × ZMod n) :=
  (nonempty_torsion_addEquiv_zmod_sq_of_smooth h2 h3 (NeZero.ne n) hfac).map
    AddEquiv.toZModLinearEquiv

omit [IsAlgClosed F] in
open Classical in
/-- **`E[n]` is a finite `ZMod n`-module, for every `3`-smooth `n`.**

⚠️ The half of `LinearEquiv.det`'s hypothesis that needs no algebraic closure, and it is taken from
`finite_torsion_of_smooth` for exactly that reason rather than from
`nonempty_torsionLinearEquiv_of_smooth`, which would have supplied it in one line and carried
`[IsAlgClosed F]` along with it.  The same economy is why `finite_torsion_three_zmod` `omit`s both
`[IsAlgClosed F]` and `[W.IsElliptic]`.

⚠️ Unlike that one this statement does keep `[W.IsElliptic]`, because `finite_torsion_of_smooth`
carries it in its file's `section Smooth` variable block; `finite_torsion_three` does not.

⚠️ It cannot be an `instance`: it carries `(2 : F) ≠ 0` and `(3 : F) ≠ 0`. -/
theorem finite_torsion_zmod_of_smooth (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0)
    (hfac : ∀ p ∈ n.primeFactors, p = 2 ∨ p = 3) : Module.Finite (ZMod n) (W.torsion n) :=
  haveI := W.finite_torsion_of_smooth h2 h3 (NeZero.ne n) hfac
  Module.Finite.of_finite

open Classical in
/-- **`E[n]` is a free `ZMod n`-module, for every `3`-smooth `n`.**

⚠️ **This is a theorem and not a certificate, and the difference from `n = 3` is the point.**
`ZMod 2` and `ZMod 3` are fields, so at those two indices every module is free and
`EllipticCurves.TateModule.DeterminantMod` states no freeness lemma at all, on the ground that a
theorem proved by `inferInstance` is noise.  `ZMod 12` is not a field, `Module.Free (ZMod 12) E[12]`
is **not** found by instance search (measured in the Non-vacuity section), and the transported
basis is the only source of freeness there is.

⚠️ It cannot be an `instance`: it carries `(2 : F) ≠ 0` and `(3 : F) ≠ 0`. -/
theorem free_torsion_zmod_of_smooth (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0)
    (hfac : ∀ p ∈ n.primeFactors, p = 2 ∨ p = 3) : Module.Free (ZMod n) (W.torsion n) := by
  obtain ⟨e⟩ := nonempty_torsionLinearEquiv_of_smooth (W := W) h2 h3 hfac
  exact Module.Free.of_equiv e.symm

open Classical in
/-- **`E[n]` has rank `2` over `ZMod n`, for every `3`-smooth `n > 1`.**

The discriminating statement of the file: `Module.finrank` is `1` over a trivial ring and `0` on a
module that is not free and finite, so this is simultaneously the rank computation *and* the
certificate that `galoisDetMod n` is not returning `LinearEquiv.det`'s junk value — the double duty
`finrank_torsion_three` performs at `n = 3` and `galoisTraceTwo_one` performs `2`-adically.

⚠️ **`1 < n` excludes a genuine counterexample and is not bookkeeping.**  `n = 1` is `3`-smooth
vacuously, `ZMod 1` is the trivial ring, and the rank there is `1`; see the Non-vacuity section,
which states that as a theorem rather than leaving it to the reader.  Mechanically, `1 < n` is what
produces `Fact (1 < n)`, hence `Nontrivial (ZMod n)`, hence the `StrongRankCondition (ZMod n)` that
`Module.finrank_prod` requires — deleting the hypothesis leaves exactly that instance unsynthesised.

⚠️ **Proved from a chosen isomorphism, unlike `finrank_torsion_three`**, which goes through
`Module.card_eq_pow_finrank` precisely to avoid one.  See this file's module docstring: the two are
not interchangeable and neither replaces the other. -/
theorem finrank_torsion_of_smooth (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) (hn : 1 < n)
    (hfac : ∀ p ∈ n.primeFactors, p = 2 ∨ p = 3) :
    Module.finrank (ZMod n) (W.torsion n) = 2 := by
  haveI : Fact (1 < n) := ⟨hn⟩
  obtain ⟨e⟩ := nonempty_torsionLinearEquiv_of_smooth (W := W) h2 h3 hfac
  rw [e.finrank_eq, Module.finrank_prod, Module.finrank_self]

open Classical in
/-- **A `ZMod n`-basis of `E[n]` indexed by `Fin 2`, for every `3`-smooth `n > 1`.**

`Module.finBasisOfFinrankEq` against `finrank_torsion_of_smooth`, the general-`n` mirror of
`basisTorsionThree`.  ⚠️ Not canonical — it is the interface a coordinate computation needs, and any
statement proved with it must be one whose truth does not depend on which basis is chosen.
`galoisDetMod` does **not** use it, deliberately: `LinearEquiv.det` is basis-free. -/
noncomputable def basisTorsionOfSmooth (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) (hn : 1 < n)
    (hfac : ∀ p ∈ n.primeFactors, p = 2 ∨ p = 3) :
    Module.Basis (Fin 2) (ZMod n) (W.torsion n) :=
  haveI : Fact (1 < n) := ⟨hn⟩
  haveI := finite_torsion_zmod_of_smooth (W := W) h2 h3 hfac
  haveI := free_torsion_zmod_of_smooth (W := W) h2 h3 hfac
  Module.finBasisOfFinrankEq _ _ (finrank_torsion_of_smooth h2 h3 hn hfac)

end Smooth

/-! ### The `n = 2` named instances

⚠️ The three declarations below are proved from the `n = 2` inputs and **not** from the `3`-smooth
statements above, which would have charged them a spurious `(3 : F) ≠ 0`.  They are the exact
mirrors of `finite_torsion_three_zmod`, `finrank_torsion_three` and `basisTorsionThree`, and they
are stated because `EllipticCurves.FunctionField.WeilPairingDeterminantLinear` records a tree-wide
grep for three of these four names finding nothing.

⚠️ There is no `free_torsion_two_zmod`, and the reason is the one
`EllipticCurves.TateModule.DeterminantMod` gives for stating no `free_torsion_three`: `ZMod 2` is a
field, so freeness is `inferInstance` with no hypotheses at all.  It is certified in the Non-vacuity
section instead. -/

section TwoTorsion

omit [IsAlgClosed F] in
open Classical in
/-- **`E[2]` is a finite `ZMod 2`-module**, the `n = 2` mirror of `finite_torsion_three_zmod`.

`finite_torsion_two` (`EllipticCurves.Torsion.TwoTorsion`) supplies `Finite (E[2])` from `h2`, and
`Module.Finite.of_finite` upgrades it.  ⚠️ No algebraic closure, exactly as at `n = 3`.

⚠️ It cannot be an `instance`: it carries the hypothesis `(2 : F) ≠ 0`. -/
theorem finite_torsion_two_zmod (h2 : (2 : F) ≠ 0) : Module.Finite (ZMod 2) (W.torsion 2) :=
  haveI := W.finite_torsion_two h2
  Module.Finite.of_finite

open Classical in
/-- **`E[2]` has rank `2` over `ZMod 2`**, the `n = 2` mirror of `finrank_torsion_three`, proved the
same way: `Module.card_eq_pow_finrank` against the sharp count, here `card_torsion_two`.

⚠️ **On `h2` alone.**  The `3`-smooth route would have proved this too and would have charged it
`(3 : F) ≠ 0`, which `#E[2] = 4` does not need.  The load-bearing input is `card_torsion_two`, and
that is what carries `[IsAlgClosed F]`.

⚠️ Content-bearing despite `(ZMod 2)ˣ` being trivial: what this rules out is `LinearEquiv.det`'s
junk value on `E[2]`, which is a statement about the module and not about the unit group. -/
theorem finrank_torsion_two (h2 : (2 : F) ≠ 0) : Module.finrank (ZMod 2) (W.torsion 2) = 2 := by
  haveI := W.finite_torsion_two h2
  haveI := finite_torsion_two_zmod (W := W) h2
  haveI : Fintype (W.torsion 2) := Fintype.ofFinite _
  have hpow : Fintype.card (W.torsion 2)
      = Fintype.card (ZMod 2) ^ Module.finrank (ZMod 2) (W.torsion 2) :=
    Module.card_eq_pow_finrank
  rw [ZMod.card, ← Nat.card_eq_fintype_card, card_torsion_two h2] at hpow
  exact (Nat.pow_right_injective (by norm_num) (show (2 : ℕ) ^ 2 = 2 ^ _ by omega)).symm

open Classical in
/-- **A `ZMod 2`-basis of `E[2]` indexed by `Fin 2`**, the `n = 2` mirror of `basisTorsionThree`.

⚠️ Not canonical, and the warning on `basisTorsionThree` applies verbatim. -/
noncomputable def basisTorsionTwo (h2 : (2 : F) ≠ 0) :
    Module.Basis (Fin 2) (ZMod 2) (W.torsion 2) :=
  haveI := finite_torsion_two_zmod (W := W) h2
  Module.finBasisOfFinrankEq _ _ (finrank_torsion_two h2)

end TwoTorsion

/-! ### Non-vacuity

⚠️ **The load-bearing certificates are the ones at a composite index**, because a certificate at
`n = 2` or `n = 3` elaborates through `Field (ZMod n)` and exercises none of what is new here.  The
index used below is `12`, which is `3`-smooth, composite, and divisible by both primes.

The certificate curve is this front's standard one, `y² + y = x³` over `ℚ` base-changed to
`AlgebraicClosure ℚ`, as `EllipticCurves.TateModule.DeterminantMod` uses.  ⚠️ Its `S = ℚ` rather
than `S = F` matters for `galoisDetMod` and not for anything below, since every statement here is
about the module and not about the Galois group.

**Three measured runs, quoted from `lake env lean` on this file.**  ⚠️ That command reports errors
in the `<file>:<line>:<col>: error(<tag>):` form quoted below, and it does **not** apply the
`leanOptions` of `lakefile.toml`, so a file can be silent under it and still warn under
`lake build`.

* **Freeness at a composite index is not automatic.**  Replacing the body of the freeness
  certificate below by `inferInstance` gives
  ```
  error(lean.synthInstanceFailed): failed to synthesize instance of type class
    Module.Free (ZMod 12) ↥(((y2AddYEqX3 ℚ)⁄AlgClosedQ).torsion 12)
  ```
  ⚠️ This is the run that separates this file from the `n = 3` block, where the same request
  succeeds — and the corresponding success at `n = 2` is certified below rather than described.
* **Finiteness is not automatic either**, at `12` as at `3`:
  ```
  error(lean.synthInstanceFailed): failed to synthesize instance of type class
    Module.Finite (ZMod 12) ↥(((y2AddYEqX3 ℚ)⁄AlgClosedQ).torsion 12)
  ```
* **Deleting `1 < n` from `finrank_torsion_of_smooth` leaves the rank statement unprovable**, and it
  is worth reading *which* instance dies, because it names the mathematics:
  ```
  error(lean.synthInstanceFailed): failed to synthesize instance of type class
    StrongRankCondition (ZMod n)
  ```
  ⚠️ And a deleted hypothesis whose absence merely stalls a proof would prove nothing about whether
  it is needed.  This one is needed: the last certificate below shows the conclusion is **false** at
  `n = 1`. -/

section Nonvacuity

/-! The certificate curve `y² + y = x³` over `ℚ` and its base, an algebraic closure of `ℚ` — of
characteristic `0`, so that `2 ≠ 0` and `3 ≠ 0` — are the shared
`EllipticCurves.Fixture.y2AddYEqX3` and `EllipticCurves.Fixture.AlgClosedQ`, which also supply
`(y2AddYEqX3 ℚ).IsElliptic` from a single `[CharZero F]` instance. The **base-changed**
`((y2AddYEqX3 ℚ)⁄AlgClosedQ).IsElliptic` comes from the same module, via
`EllipticCurves.Fixture.instIsEllipticBaseChange`; this block declares no fixture of its own
(`#1408`). -/

open EllipticCurves.Fixture

private lemma exampleTwo : (2 : AlgClosedQ) ≠ 0 := two_ne_zero

private lemma exampleThree : (3 : AlgClosedQ) ≠ 0 := three_ne_zero_of_charZero _

/-- `12 = 2² · 3` is `3`-smooth.  ⚠️ `decide` does not close this: `Nat.primeFactors` is the support
of a factorisation defined by well-founded recursion. -/
private lemma smoothTwelve : ∀ p ∈ (12 : ℕ).primeFactors, p = 2 ∨ p = 3 := by
  have h : (12 : ℕ) = 2 ^ 2 * 3 ^ 1 := by norm_num
  rw [h, Nat.primeFactors_mul (by norm_num) (by norm_num),
    Nat.primeFactors_prime_pow two_ne_zero Nat.prime_two,
    Nat.primeFactors_prime_pow one_ne_zero Nat.prime_three]
  simp

open Classical in
/-- **⚠️ THE LOAD-BEARING CERTIFICATE**: on a curve that exists and at a *composite* index, `E[12]`
really has rank `2` over `ZMod 12`, so `LinearEquiv.det` is not returning its junk value there. -/
example : Module.finrank (ZMod 12) (((y2AddYEqX3 ℚ)⁄AlgClosedQ).torsion 12) = 2 :=
  finrank_torsion_of_smooth exampleTwo exampleThree (by norm_num) smoothTwelve

open Classical in
/-- Freeness at a composite index, where `inferInstance` fails; see the first measured run. -/
example : Module.Free (ZMod 12) (((y2AddYEqX3 ℚ)⁄AlgClosedQ).torsion 12) :=
  free_torsion_zmod_of_smooth exampleTwo exampleThree smoothTwelve

open Classical in
/-- Finiteness at a composite index, where `inferInstance` also fails. -/
example : Module.Finite (ZMod 12) (((y2AddYEqX3 ℚ)⁄AlgClosedQ).torsion 12) :=
  finite_torsion_zmod_of_smooth exampleTwo exampleThree smoothTwelve

open Classical in
/-- A `ZMod 12`-basis on the same curve — the interface a coordinate computation would consume. -/
example : Nonempty (Module.Basis (Fin 2) (ZMod 12) (((y2AddYEqX3 ℚ)⁄AlgClosedQ).torsion 12)) :=
  ⟨basisTorsionOfSmooth exampleTwo exampleThree (by norm_num) smoothTwelve⟩

open Classical in
/-- **Freeness at `n = 2` IS automatic**, and this is the certificate that says so: no hypothesis,
no lemma of this development, just `inferInstance`, because `Field (ZMod 2)` is an instance.  ⚠️ It
is why this file states no `free_torsion_two_zmod`, following `DeterminantMod` at `n = 3`. -/
example : Module.Free (ZMod 2) (((y2AddYEqX3 ℚ)⁄AlgClosedQ).torsion 2) := inferInstance

open Classical in
/-- The `n = 2` rank on the same curve, restated in full rather than obtained-and-projected. -/
example : Module.finrank (ZMod 2) (((y2AddYEqX3 ℚ)⁄AlgClosedQ).torsion 2) = 2 :=
  finrank_torsion_two exampleTwo

open Classical in
/-- **⚠️ `1 < n` is not bookkeeping.**  At `n = 1` the hypothesis `hfac` holds vacuously — `1` has
no prime factors — and the conclusion of `finrank_torsion_of_smooth` is **false**: `ZMod 1` is the
trivial ring and `Module.finrank_subsingleton` puts the rank at `1`.  This is the certificate that
the hypothesis excludes a counterexample rather than merely unblocking a tactic. -/
example : Module.finrank (ZMod 1) (((y2AddYEqX3 ℚ)⁄AlgClosedQ).torsion 1) ≠ 2 := by
  rw [Module.finrank_subsingleton]
  norm_num

end Nonvacuity

end WeierstrassCurve.Affine
