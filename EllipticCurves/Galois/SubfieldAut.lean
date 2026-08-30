/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import Mathlib.Algebra.Algebra.Equiv
import Mathlib.Algebra.Field.Subfield.Basic

/-!
# Transport of the automorphism group along an equality of base subfields

For a field `K` and two subfields `S T : Subfield K` with `S = T`, the two automorphism groups
`K ≃ₐ[↥S] K` and `K ≃ₐ[↥T] K` are isomorphic, by the identity on underlying functions.

⚠️ **Nothing about elliptic curves enters this file.**  It is stated for an arbitrary field and an
arbitrary pair of equal subfields, and it imports nothing from this development — the
`EllipticCurves`-import closure of this module is empty.

## Why this file exists

An Artin-sandwich argument produces a fixed field as `FixedPoints.subfield G K`, and
`FixedPoints.toAlgAutMulEquiv` identifies `G` with `K ≃ₐ[↥(FixedPoints.subfield G K)] K` — the
automorphism group over *that* presentation of the base.  What a consumer holds is a theorem saying
the fixed field **is** some subfield it cares about, and the two automorphism groups are then
different types with the same elements.  This file is the one-declaration bridge, and it is the only
brick its two consumers — `EllipticCurves.FunctionField.MulByNGaloisGroup` for `[n]∗F(W)` and
`EllipticCurves.FunctionField.NegYGaloisGroup` for `F(x)` — had to build.

## What this file costs its consumers, and ⚠️ how to measure it without getting it wrong

This file was cut out of `FunctionField/NegYGaloisGroup.lean` (`#1266`) to shrink that module's
import weight, and the numbers are the argument for having done it.  Measured at `6e5245c`:

| module | project closure | total closure | `lake build` jobs |
|---|---|---|---|
| `Galois.SubfieldAut` (this file) | 1 — itself, nothing more | 968 | 983 |
| `FunctionField.NegYGaloisGroup` | 20, down from 72 | 2665 | 2680 |
| `FunctionField.MulByNGaloisGroup` | 72 | 2799 | 2814 |

*Project closure* counts modules under `EllipticCurves/`, the module itself included — so the `1`
in the first row is the claim at the top of this docstring, measured.  *Total closure* adds
everything reachable under `.lake/packages/`; the core `Init` / `Lean` / `Std` modules live in the
toolchain rather than there, and the 178–185 of them that are reached are ⚠️ **stopped at but not
counted** — neither expanded nor added to the total, so a reader who does count them gets 1146 for
the first row instead of 968.  The last column is the independent check: `lake build <module>`
exceeds the total closure by exactly 15 on every row, that being lake's fixed set of non-module
jobs.

⚠️ **A second check costs nothing and needs no script.**  A docstring-only edit to this file
rebuilds exactly four jobs — this module, its two consumers, and the `mk_all` root
`EllipticCurves`.  *Which* modules `lake` recompiles is the "two consumers" claim restated from
the build side, so every build of a change to this file re-verifies the fan-out for free.

### ⚠️ `^import` is the wrong pattern, and it fails quietly

Mathlib at this pin uses the Lean module system: its files open with `module` and then
`public import …`.  Census at `6e5245c`:

| tree | `.lean` files | with a `^public import ` line | with a plain `^import ` line |
|---|---|---|---|
| `.lake/packages/mathlib/Mathlib` | 8264 | 8246 | 381 |
| `EllipticCurves/` | 360 | **0** | **360** |

So a script matching `^import\s+(\S+)` finds no import whatever in the **7883** Mathlib files that
have no plain `import ` line — `8264 − 381`.  ⚠️ **Not 8246, and the two columns do not partition
the tree**: `372` of those `381` files carry *both* spellings, so `^import` sees imports in them
and merely under-reads them.  (`#1292`'s description and PR #471 before it both name 8246 as the
blind spot; that is the `public import ` column, and this table refutes it.)
⚠️ **The second row is why the whole thing fails quietly**: every file in *this* project uses the
plain spelling, so the project column of any closure comes out exactly right and only the total is
wrong.  Re-running the three totals above with `^import` gives 3, 42 and 111 under a walker that
skips header lines it cannot parse, and 3, 39 and 108 under one that stops at the first — low
either way, but not absurdly so, and in the same shape as the correct answer.  ⚠️ **That the broken
totals depend on that choice and the correct ones do not is itself diagnostic**: under the pattern
below the two walkers agree to the module, because then nothing in either tree's header is
unparseable.  The pattern that works:

```
^(?:public |private |meta |protected )*import\s+(?:all\s+)?([A-Za-z_][A-Za-z0-9_.']*)\s*(?:--.*)?$
```

⚠️ The prefix group **repeats** deliberately: Mathlib has 501 `public meta import` lines and 6
`meta import` lines, and a pattern spelling only `(?:public )?` drops every one of them.

⚠️ Three further traps, all hit while producing the table above rather than guessed at, and all
three silent:

* **Scan the file header only.**  `Mathlib/Tactic/Rify.lean:68` is a line reading `import Mathlib`
  inside a docstring; a whole-file scan follows it and pulls the whole library into every closure
  that reaches that file.  It inflates this file's own total from 968 to 1601.
* **Allow a trailing `-- comment` on an import.**  `Mathlib/Init.lean` — the root file of Mathlib,
  imported by virtually every file in it — has 32 imports, and the **first** of them is line 3,
  `public import Lean.Linter.Sets -- for the definition of linter sets`.  ⚠️ **A header scanner
  that treats a line it cannot parse as the end of the header therefore stops *before* that first
  import and reads Mathlib's root file as importing nothing at all** — 0 of 32, and no variation on
  where such a scanner is allowed to continue (blank lines, the `module` line, `--` lines) changes
  that, because the very first import is the unparseable line.  A scanner that skips unparseable
  lines rather than stopping collects 28 of the 32.  Both silently *under*-count, which is the
  direction that looks right.
* **Allow `import all M`.**  Mathlib writes it 23 times in 21 files (`Mathlib/Tactic/ToDual.lean`,
  `Mathlib/Data/Nat/Bitwise.lean`, …), 5 of the 21 inside this file's own closure and 9 inside
  each consumer's.  Drop the `(?:all\s+)?` group and the pattern captures `all`, then fails on the
  module name after it — so the line matches nothing at all and the edge is lost, under-counting
  again.  ⚠️ **The `+15` column is what catches this**: without that group the table reads
  966 / 2662 / 2796 and the offsets become 17 / 18 / 18, a check that was constant ceasing to be.
  The edges lost are `Mathlib.Tactic.Translate.ToDual`,
  `Mathlib.Tactic.Translate.TagUnfoldBoundary` and, for the two consumers,
  `Mathlib.Util.DischargerAsTactic`.

⚠️ **The two errors this section has had to correct were both of one kind, and it is not the kind
this file was written to catch.**  Neither the `8246` above nor an earlier *"stops after two of its
thirty-odd imports"* in the middle bullet came from a bad measurement: in both cases the census and
the scanner runs were re-done correctly, and an inherited *sentence about* them was carried across
unchecked.  Re-running a number is not enough — the prose around it has to be re-derived from the
new number too.  Every figure in this section is written so that one command checks it; that is the
only defence, and it is the reason for the `+15` column, the `360 / 0 / 360` control row and the
two-walker agreement above.

⚠️ **The factor is not a constant to quote.**  On the skip-variant totals it is 25.2 for
`MulByNGaloisGroup` and 63.5 for `NegYGaloisGroup` (25.9 and 68.3 on the other walker's), because
the wrong pattern sees little beyond the project half: cutting that half from 72 modules to 20,
while the total fell only from 2799 to 2665, roughly doubles the discrepancy.  Before the move both
consumers sat at about 26.

## Mathlib has no name for this

⚠️ Re-grepped at Lean `v4.32.0` / Mathlib `v4.32.0` before this file was cut, and the position is
unchanged from when the declaration was first written:

* `AlgEquiv.autCongr` (`Mathlib/Algebra/Algebra/Equiv.lean`) moves the **top** algebra over a fixed
  base — `(A₁ ≃ₐ[R] A₂) → ((A₁ ≃ₐ[R] A₁) ≃* (A₂ ≃ₐ[R] A₂))` — and is not this;
* `IntermediateField.equivOfEq` (`Mathlib/FieldTheory/IntermediateField/Basic.lean`) is an
  `AlgEquiv` between the two intermediate fields **themselves**, not between their automorphism
  groups;
* `autCongr` is *declared* in exactly one place in Mathlib — the file above.  The three other
  Mathlib files that mention it (`FieldTheory/AbelRuffini.lean`, `FieldTheory/KummerExtension.lean`,
  `NumberTheory/Cyclotomic/Gal.lean`) are consumers of that one, not a second, base-changing
  version.

So `Subfield.autMulEquivOfEq` is an upstream candidate.  ⚠️ It is a candidate and not a plan: no
Mathlib pull request exists, and nothing in this development is waiting on one.

## ⚠️ The imports are minimal, and `Subfield.Basic` cannot be weakened to `Subfield.Defs`

Both imports were tested by deletion and both are needed.  `Mathlib.Algebra.Field.Subfield.Defs`
does make this file *elaborate* — but it makes it elaborate against a **different** `Algebra ↥S K`
instance.  Measured with `set_option pp.explicit true in #synth Algebra (↥S) K` under each import
set:

* with `Mathlib.Algebra.Field.Subfield.Basic` — `Subfield.toAlgebra`;
* with `Mathlib.Algebra.Field.Subfield.Defs` — `Algebra.ofSubsemiring …`, found through
  `SubsemiringClass`.

`Subfield.toAlgebra` (`Mathlib/Algebra/Field/Subfield/Basic.lean`) is the instance every consumer of
this file resolves, so weakening the import would put a different instance into the *statement* of
`autMulEquivOfEq` and leave consumers to unfold the difference.  ⚠️ **The narrower import is not the
better one here**; do not "optimise" it without re-running that `#synth`.

## Main definitions

Every public declaration of this file is listed, here and under `## Main statements`.  Everything is
in namespace `Subfield`.

* `Subfield.autMulEquivOfEq` — transport of `Aut K` along an equality of base subfields.

## Main statements

* `Subfield.autMulEquivOfEq_apply` and `Subfield.autMulEquivOfEq_symm_apply` — the transport is the
  identity on underlying functions, by `rfl` in both directions.

## What is *not* here

* **No `IntermediateField` twin.**  A consumer whose equality is an `IntermediateField` equality
  drops it to the `Subfield` level first — `SetLike.ext` off the equality it already has — and then
  applies these names.  `EllipticCurves.FunctionField.NegYGaloisGroup` is the worked example, in
  `fixedPoints_subfield_eq_ratFuncRange`; the `≃ₐ` types over the two carriers are definitionally
  equal, which that file commits as an `example`, so a second name here would be noise.
* **Nothing about fixed points.**  `FixedPoints.toAlgAutMulEquiv` is Mathlib's and is what this
  transports *against*; it is not restated, and this file does not import it.
* **No `Normal`, no `IsGalois`, no degree.**  An equality of base subfields carries all three across
  on its own, and no consumer needs a lemma here to say so.
-/

namespace Subfield

variable {K : Type*} [Field K] {S T : Subfield K}

/-- **Equal base subfields give isomorphic automorphism groups**, by the identity on underlying
functions.

An `S`-algebra automorphism of `K` is a ring automorphism that fixes `S` pointwise, and `S = T` says
the two subsets are the same, so nothing is transported except the proof obligation.  The
`MulEquiv` is therefore built out of `AlgEquiv.ofRingEquiv` in both directions and all three
coherence fields are `rfl`. -/
def autMulEquivOfEq (hST : S = T) : (K ≃ₐ[↥S] K) ≃* (K ≃ₐ[↥T] K) where
  toFun e := AlgEquiv.ofRingEquiv (f := (e : K ≃+* K)) fun r => e.commutes ⟨r, hST.ge r.2⟩
  invFun e := AlgEquiv.ofRingEquiv (f := (e : K ≃+* K)) fun r => e.commutes ⟨r, hST.le r.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

@[simp] lemma autMulEquivOfEq_apply (hST : S = T) (e : K ≃ₐ[↥S] K) (x : K) :
    autMulEquivOfEq hST e x = e x := rfl

@[simp] lemma autMulEquivOfEq_symm_apply (hST : S = T) (e : K ≃ₐ[↥T] K) (x : K) :
    (autMulEquivOfEq hST).symm e x = e x := rfl

end Subfield
