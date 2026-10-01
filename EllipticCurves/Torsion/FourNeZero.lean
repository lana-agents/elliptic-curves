/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import Mathlib.Algebra.GroupWithZero.Basic
import Mathlib.Tactic.NormNum.Basic

/-!
# `(4 : R) ≠ 0` from `(2 : R) ≠ 0`

Mathlib's `WeierstrassCurve.Ψ₂Sq_ne_zero` asks for `(4 : F) ≠ 0` — that scalar is `Ψ₂Sq`'s leading
coefficient (`WeierstrassCurve.leadingCoeff_Ψ₂Sq`) — while every layer of this development that
reaches it carries the textbook hypothesis `(2 : F) ≠ 0` instead. The one line that bridges the two
is the whole content of this file.

This module exists for a reason that is not mathematical. ⚠️ **The bridge was `private` in seven
files under three different names**, measured at `5710234` by
`git grep -ln "private lemma four_ne_zero\|private theorem four_ne_zero" -- '*.lean'` (which at
this commit returns one file, this one, for the occurrence inside that quoted command):
`four_ne_zero_of_two_ne_zero` in `FunctionField.MulByTwoDegree`,
`FunctionField.MulByTwoFibreInfinity`, `FunctionField.MulByTwoPlaceAtInfinity`,
`Torsion.TwoTorsion` and `Torsion.TwoTorsionSplittingField`;
`four_ne_zero_of_two_ne_zero'` in `Torsion.HalvingExtension`; and `four_ne_zero` in
`Torsion.XSupport`. ⚠️ **`7` files under `3` names is the figure at `5710234`, and a fourth name
arrives with the eighth copy**: `four_ne_zero'` in `Torsion.EvenTorsionCountSplits`, unmerged at
PR #895 and not retired here — so `8` files under `4` names is the figure once that lands, and `7`
under `4` is neither. ⚠️ **Three spellings is why nobody noticed**: a `git grep` for any one of them
misses at least one of the others, so the author of each new copy looked, found nothing importable,
and wrote another one — and `Torsion.TwoTorsionSplittingField`'s copy carried a docstring saying so
(*"Duplicated on purpose: every other copy in the tree … is itself `private`, so none of them can
be cited from here"*). The repair is a public declaration, not a better grep.

## Main results

* `four_ne_zero_of_two_ne_zero` : in a semiring with no zero divisors, `(2 : R) ≠ 0` implies
  `(4 : R) ≠ 0`.

## The name, and the one it is not

⚠️ **`four_ne_zero` is taken: Mathlib has `four_ne_zero [OfNat α 4] [NeZero (4 : α)]`**
(`Mathlib/Algebra/NeZero.lean`), which reads its conclusion off an instance and cannot be applied
to a hypothesis. That is why `Torsion.XSupport`'s copy had to be `private` to compile under the
short name at all, and why the public declaration here takes the `_of_two_ne_zero` suffix — the
majority spelling among the seven, and the one that says which hypothesis is being spent.

⚠️ **The statement is over `[Semiring R] [NoZeroDivisors R]` and not over a field**, which every
call site in the tree actually has: the proof uses only `4 = 2 * 2` and `mul_ne_zero`, and pinning
it to `Field` would have been a hypothesis this file does not spend. Nothing downstream relies on
the generality; it is here because the narrower statement would have been the arbitrary one.

## Position in the import closure

This module imports **nothing** from `EllipticCurves` — it is a leaf — and its two Mathlib imports
are already in the closure of all seven files a copy was retired from. ⚠️ **So adding it to those
seven import lists grows each of their closures by exactly one module, itself**, and the whole-tree
`lake build` job count moves by exactly `+1`. ⚠️ **The stronger form of that claim, and the one
actually checked: this module's ENTIRE import closure — 1764 modules counting itself, over a walk
of the project and the pinned dependency tree — is a SUBSET of each of those seven closures, set
difference `0` for `7` of `7`.** So *"exactly one module, itself"* is exact rather than approximate.

It lives under `Torsion/` rather than `FunctionField/` because the dependency between the two
directories runs one way: **35** `FunctionField/` files import an `EllipticCurves.Torsion.*` module
at this commit and **no** `Torsion/` file imports an `EllipticCurves.FunctionField.*` one, so a home
here is reachable from both sides without inverting a layer. ⚠️ **Both halves are the DIRECT
`^import` reading, and the first was `32` before this commit**: the three arrivals are
`MulByTwoDegree`, `MulByTwoFibreInfinity` and `MulByTwoPlaceAtInfinity`, i.e. exactly the three
files this commit adds the import to, so the figure is one this module's own existence moved.
The transitive reading is `187` at both refs and the `no` half is `0` under both readings at both.
-/

/-- **`(4 : R) ≠ 0` when `(2 : R) ≠ 0`**, in any semiring without zero divisors: `4` is `2 * 2`.

This is the hypothesis bridge for Mathlib's `WeierstrassCurve.Ψ₂Sq_ne_zero`, whose `(4 : F) ≠ 0` is
the leading coefficient of `Ψ₂Sq`, from the `(2 : F) ≠ 0` that the characteristic-`≠ 2` layers of
this development carry. -/
theorem four_ne_zero_of_two_ne_zero {R : Type*} [Semiring R] [NoZeroDivisors R]
    (h2 : (2 : R) ≠ 0) : (4 : R) ≠ 0 := by
  rw [show (4 : R) = 2 * 2 by norm_num]
  exact mul_ne_zero h2 h2
