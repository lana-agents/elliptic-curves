/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
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
`Torsion.XSupport`. ⚠️ **`7` files under `3` names is the figure at `5710234` and it is keyed
there because it has not been the figure since**: what this paragraph used to carry beside it was a
forecast of the next reading, and `## The eighth copy` below is where that went and why.
⚠️ **Three spellings is why nobody noticed**: a `git grep` for any one of them
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

## The eighth copy, and the forecast retired with it

⚠️ **An eighth copy of the bridge did reach `main` after this module landed, and it is gone again**
(`#2314`).  *four_ne_zero'* in `Torsion.EvenTorsionCountSplits` arrived with PR #895 (`74f065cd`)
and was deleted by this row's commit, which cites `four_ne_zero_of_two_ne_zero` at both of that
file's call sites instead.  ⚠️ **The name is in italics and not backticks** because it no longer
resolves: `### Retired claims`' own reason is that a retired name in backticks is indistinguishable
from a dangling one to every name-resolution check on this board.  That file's own docstring
carries the other half of the retirement — the sentence that commissioned the follow-up — because
its subject is that file's own copy.

⚠️ **What retires here is this module's forecast of the arithmetic, which the landing order
falsified.**  Under a ⚠️ marker — paragraph structure, so named out here rather than reproduced
inside — the paragraph above used to close

*"**`7` files under `3` names is the figure at `5710234`, and a fourth name arrives with the eighth
copy**: `four_ne_zero'` in `Torsion.EvenTorsionCountSplits`, unmerged at PR #895 and not retired
here — so `8` files under `4` names is the figure once that lands, and `7` under `4` is neither."*

⚠️⚠️ **`8` files under `4` names is a population `main` never carried.**  This module landed first
(`0e13ff0`, `2026-10-01`) and retired the seven; the eighth arrived second (`74f065cd`,
`2026-10-03`), so what `main` held between that landing and this commit was `1` file under `1` name,
and the `8 ↔ 4` reading was conditional on the other landing order, which never happened.  The
*"unmerged at PR #895"* half is a state claim and that pull request has merged.  ⚠️ **`7 ↔ 3` at
`5710234` is the one cell of the sentence that survives, and it survives because it is keyed** —
which is the whole argument for keying a census rather than publishing it live.

⚠️ **The recogniser the surviving cell is measured by now returns this file alone, for the
occurrence inside its own quoted command**, exactly as the note beside that command says it does.
The marked quotation above does not add a match: it carries the retired name and not the
`private lemma` or `private theorem` that the command keys on.

## Position in the import closure

This module imports **nothing** from `EllipticCurves` — it is a leaf — and its two Mathlib imports
are already in the closure of all seven files a copy was retired from. ⚠️ **So adding it to those
seven import lists grows each of their closures by exactly one module, itself**, and the whole-tree
`lake build` job count moves by exactly `+1`. ⚠️ **The stronger form of that claim, and the one
actually checked: this module's ENTIRE import closure — 1764 modules counting itself, over a walk
of the project and the pinned dependency tree — is a SUBSET of each of those seven closures, set
difference `0` for `7` of `7`.** So *"exactly one module, itself"* is exact rather than approximate.

⚠️ **The eighth import line is FREE, and that is a different figure from the `+1` above**
(`#2314`).  `Torsion.EvenTorsionCountSplits` already reached this module at distance **2** before
its import line was written, and ⚠️ **by exactly ONE route at that distance**: through
`Torsion.XSupport`, which it imports directly and which imports this one — the only predecessor of
this module on any shortest path.  ⚠️ **`Torsion.TwoTorsion` also imports this module but is itself
at distance 2, so that route is length 3** and is not a second distance-`2` witness.  Either way the
line grows that file's closure by **0** modules and the whole-tree job count by **0**.
⚠️ **It is written anyway, and that is a convention choice rather than a necessity**: a file that
cites `four_ne_zero_of_two_ne_zero` should name the module supplying it rather than rest on another
file keeping an import it does not own.
**So the `+1` sentence above is a claim about the seven and does not generalise.**

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
