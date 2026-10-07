/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import EllipticCurves.Torsion.NsmulLadder
import EllipticCurves.Torsion.ThreeTorsionStructure
import Mathlib.Algebra.Field.ZMod

/-!
# Why `#E[n] = n²` at odd `n` does not reach characteristic `2`: the ladder halves `y`

`#2340` asks for `E[n] ≃+ (ℤ/nℤ)²` at odd `n` with `(n : F) ≠ 0` and **no** `(2 : F) ≠ 0`, and it
asks the question in the only order that can be answered: *finish the `h2` walk first, then decide
which route to take, and if one of the routes is impossible at some step then say which step and
why.*  This file is that answer.  It delivers the walk, the route decision and **the obstruction as
a theorem rather than as a remark** — and it does not deliver the structure theorem, for the reason
the obstruction states.

⚠️ **Nothing here is a defect report.**  Every statement in the walk below is true as stated and
every one of them carries its `(2 : F) ≠ 0` in its own headline.  What this file adds is that the
hypothesis is **not** an artefact of four of those routes and **is** an artefact of a fifth.

## The walk, measured and not read off docstrings

The population is the `h2`-cone of `WeierstrassCurve.Affine.nonempty_torsion_addEquiv_of_odd`
(`EllipticCurves.Torsion.PrimaryTowerOdd`): the declarations reachable from it by the relation
*"binds `(2 : F) ≠ 0` and mentions, in its proof, another declaration that binds `(2 : F) ≠ 0`"*.
⚠️ **Every `file:line` below is keyed to `a10ead64`**, where it was measured, and ⚠️ a coordinate
has three ways to go false against a name's one — re-resolve each by its declaration NAME.

⚠️ **The cone has 49 members and exactly FOUR leaves.**  A *leaf* is a member that binds `h2` and
mentions no other `h2`-binder in its proof, so it is a member that spends the hypothesis rather
than forwarding it.  `#2340` asks for every leaf and not the first one; here they are, with the
whole cone partitioned by **which** leaves each member reaches, because that partition is what
decides the route and a flat list of 49 names does not.

### The four leaves

| leaf | file:line | what the `2` is spent on |
|---|---|---|
| `divY_one` | `Torsion/NsmulLadder.lean`:`273` | undoing the halving in `divY` at `n = 1` |
| `nsmul_step` | `Torsion/NsmulLadder.lean`:`347` | the `field_simp` over `divY` in the step |
| `addY_self_eq_div` | `Torsion/DoublingCoords.lean`:`152` | the `2 ψ₂³` denominator of `y(2P)` |
| `equation_iff_sq` | `Torsion/ThreeTorsionStructure.lean`:`244` | completing the square in `y` |

⚠️⚠️ **Three of the four are ONE defect, not three**, and that is the finding: `divY` is *defined*
as `(Tₙ − a₁·divX − a₃)/2`, and `addY_self_eq_div` is the same halving written out at `n = 2`.  The
fourth is a different mechanism and is the only one the tree already knows how to avoid.

### Cone members reaching only the repairable leaf — 3 of 49

| declaration | file:line |
|---|---|
| `equation_iff_sq` | `Torsion/ThreeTorsionStructure.lean`:`244` |
| `exists_equation_of_isSquare` | `Torsion/ThreeTorsionStructure.lean`:`339` |
| `exists_equation` | `Torsion/ThreeTorsionStructure.lean`:`377` |

⚠️ **This branch is already bypassable at live `main` and this file does not bypass it**, because
doing so alone buys one binder: `exists_equation'`
(`EllipticCurves.Torsion.ThreeTorsionStructure`:`413`) is the same conclusion with no `h2` at all,
proved by `IsAlgClosed.exists_root` on a monic quadratic in `Y` instead of by completing the
square, and `#2253` has already rewired five call sites onto it.  ⚠️⚠️ **Inside the branch the
bypass reaches exactly ONE of the three**: `exists_equation` could shed its binder by taking that
route, while `exists_equation_of_isSquare` and `equation_iff_sq` keep theirs for reasons that file
states in terms — the first **names** its witness `(s − a₁x − a₃)/2`, and the second's left-hand
side `(2y + a₁x + a₃)²` does not mention `y` at `2 = 0`, so it cannot express the equation it
restates.  ⚠️⚠️ **And it reaches NO member above the branch**: the only two cone members that call
`exists_equation` are `eval_ΨSq_adjacent_ne_zero_of_eval_ΨSq_eq_zero` and
`eval_preΩ_ne_zero_of_eval_preΨ_eq_zero`, and both reach a ladder leaf as well, so neither sheds
its binder.  **That is the measurement that stops a round from mistaking the cheap half for
progress.**

### Cone members reaching only a ladder leaf — 8 of 49

| declaration | file:line | leaf |
|---|---|---|
| `divY_one` | `Torsion/NsmulLadder.lean`:`273` | `divY_one` |
| `nsmul_one_eq_div` | `Torsion/NsmulLadder.lean`:`395` | `divY_one` |
| `nsmulEqDiv_one` | `Torsion/NsmulLadder.lean`:`441` | `divY_one` |
| `nsmul_step` | `Torsion/NsmulLadder.lean`:`347` | `nsmul_step` |
| `nsmulEqDiv_step` | `Torsion/NsmulLadder.lean`:`449` | `nsmul_step` |
| `addY_self_eq_div` | `Torsion/DoublingCoords.lean`:`152` | `addY_self_eq_div` |
| `nsmul_two_eq_div` | `Torsion/NsmulLadder.lean`:`409` | `addY_self_eq_div` |
| `nsmulEqDiv_two` | `Torsion/NsmulLadder.lean`:`445` | `addY_self_eq_div` |

### Cone members reaching all three ladder leaves — 28 of 49

| declaration | file:line |
|---|---|
| `nsmul_eq_zero_of_minimal_ψ_evalEval_eq_zero` | `Torsion/NsmulOrder.lean`:`185` |
| `ψ_add_four_evalEval_ne_zero_of_minimal` | `Torsion/NsmulOrder.lean`:`237` |
| `ψ_evalEval_ne_zero_of_not_dvd` | `Torsion/NsmulOrder.lean`:`284` |
| `ψ_evalEval_eq_zero_of_dvd` | `Torsion/NsmulOrder.lean`:`314` |
| `exists_order_of_exists_ψ_evalEval_eq_zero` | `Torsion/NsmulOrder.lean`:`525` |
| `nsmul_eq_zero_iff_ψ_evalEval_eq_zero` | `Torsion/NsmulOrder.lean`:`563` |
| `ψ_evalEval_eq_zero_of_nsmul_eq_zero` | `Torsion/NsmulOrder.lean`:`582` |
| `nsmulEqDiv_pair` | `Torsion/NsmulLadder.lean`:`461` |
| `nsmulEqDiv_of_forall_ψ_ne_zero` | `Torsion/NsmulLadder.lean`:`492` |
| `nsmul_eq_some_Φ_div_ΨSq` | `Torsion/NsmulLadder.lean`:`510` |
| `exists_ψ_evalEval_eq_zero_of_nsmul_eq_zero` | `Torsion/NsmulLadder.lean`:`523` |
| `ψ_add_three_evalEval_of_ψ_three_eq_zero` | `Torsion/NsmulYPeriodic.lean`:`316` |
| `nsmul_eq_zero_iff_ψ_evalEval_eq_zero_of_isElliptic` | `Torsion/TwoTorsionOrder.lean`:`226` |
| `ψ_add_one_evalEval_ne_zero_of_nsmul_eq_zero` | `Torsion/TwoTorsionOrder.lean`:`239` |
| `ψ_sub_one_evalEval_ne_zero_of_nsmul_eq_zero` | `Torsion/TwoTorsionOrder.lean`:`251` |
| `mem_torsionXSupport_of_mem_torsion` | `Torsion/XSupport.lean`:`164` |
| `finite_torsion_of_intCast_ne_zero` | `Torsion/XSupport.lean`:`191` |
| `ψ_cube_of_ψ_three_eq_zero` | `Torsion/OmegaPairCoprime.lean`:`179` |
| `ψ_pair_of_ψ_three_eq_zero` | `Torsion/OmegaPairCoprime.lean`:`197` |
| `ψ_pair_of_ψ_eq_zero` | `Torsion/OmegaPairCoprime.lean`:`221` |
| `ψ_pair_of_equation` | `Torsion/OmegaPairCoprime.lean`:`262` |
| `nsmul_eq_zero_iff_eval_preΨ_eq_zero` | `Torsion/OddTorsionCount.lean`:`234` |
| `torsionOddOfRoot` | `Torsion/OddTorsionCount.lean`:`318` |
| `torsionOddOfRoot_bijective` | `Torsion/OddTorsionCount.lean`:`325` |
| `torsionOddEquiv` | `Torsion/OddTorsionCount.lean`:`357` |
| `card_torsion_odd` | `Torsion/OddTorsionCount.lean`:`368` |
| `card_torsion_eq_sq_iff_separable_preΨ` | `Torsion/OddTorsionCount.lean`:`399` |
| `card_torsion_eq_sq_of_wronskian` | `Torsion/WronskianSeparable.lean`:`199` |

### Cone members reaching all four leaves — 10 of 49

| declaration | file:line |
|---|---|
| `nonempty_torsion_addEquiv_of_odd` | `Torsion/PrimaryTowerOdd.lean`:`256` |
| `card_nsmul_eq_zero_torsion_le_of_odd` | `Torsion/PrimaryTowerOdd.lean`:`201` |
| `card_torsion_eq_sq_of_odd` | `Torsion/OmegaChordSum.lean`:`643` |
| `card_torsion_eq_sq_of_recurrence` | `Torsion/WronskianRecurrence.lean`:`374` |
| `card_torsion_eq_sq_of_wronskian_identity` | `Torsion/OmegaPairCoprime.lean`:`325` |
| `isCoprime_preΨ_preΩ_of_odd` | `Torsion/OmegaPairCoprime.lean`:`281` |
| `isCoprime_preΨ_preΩ` | `Torsion/WronskianSeparable.lean`:`286` |
| `eval_preΩ_ne_zero_of_eval_preΨ_eq_zero` | `Torsion/WronskianSeparable.lean`:`249` |
| `eval_Φ_ne_zero_of_eval_ΨSq_eq_zero` | `Torsion/TwoTorsionOrder.lean`:`305` |
| `eval_ΨSq_adjacent_ne_zero_of_eval_ΨSq_eq_zero` | `Torsion/TwoTorsionOrder.lean`:`279` |

⚠️ **`3 + 8 + 28 + 10 = 49`, so the four blocks are a PARTITION and no member is counted twice or
dropped.**  ⚠️ **46 of the 49 reach a ladder leaf**, which is the whole cone except the three-member
`exists_equation` branch, so the `y`-halving is not one route among several — it is the route.

⚠️ **The instrument is textual and its two failure directions are named rather than hidden.**  It
reads binders of the shape `(h : (2 : _) ≠ 0)` with `(`, `{` or `⦃` and any name, and it tokenises
proof bodies as Unicode words, so a name beginning with a Greek letter (`ψ_…`, `preΨ…`) is a token
and not a suffix.  ⚠️ **That second point is a correction of this file's own first instrument**: an
ASCII-initial identifier class silently read the cone at **38** members with **5** leaves, dropping
every `ψ`-initial edge, and the leaf `mem_torsionXSupport_of_mem_torsion` it then reported is not a
leaf at all — it forwards `h2` to `ψ_evalEval_eq_zero_of_nsmul_eq_zero`.  ⚠️ **A `2 ≠ 0` reaching a
proof as `(by norm_num)` or through a `NeZero`/`Fact` instance is invisible to it**; the cone is
therefore a lower bound on the population and the four leaves are leaves *of the relation measured*.
**The partition and the leaf set were stable under both widenings of the binder pattern.**

## The route decision: `#2340`'s route (b), and route (a) is impossible at `divY`

`#2340` item 2 asks the round to choose between **(a)** weakening the odd chain so that each
consumed step holds at `2 = 0`, and **(b)** a characteristic-`2`-specific route glued to the
existing statements.  ⚠️⚠️ **Route (a) is impossible, and the step it is impossible at is
`WeierstrassCurve.Affine.divY` — a DEFINITION and not a proof.**

`divY W x y n` is `(W.divT x y n − a₁·W.divX x n − a₃)/2`, the `y`-coordinate recovered from
`Tₙ = 2y(nP) + a₁x(nP) + a₃` by halving.  ⚠️ **At `2 = 0` that recovery is not merely lossy, it is
total loss twice over.**  First, `y ↦ 2y + a₁x + a₃` does not mention `y` at `2 = 0`, so `Tₙ`
carries no information to recover from.  Second — and this is the part a Lean statement can be held
to — `divY` is division by `2`, and in a field of characteristic `2` that is division by zero:
`divY_eq_zero_of_two_eq_zero` below proves `W.divY x y n = 0` **for every curve, every point and
every index**, and `divY_eq_divY_of_two_eq_zero` proves it does not depend on `y`.

So the ladder's conclusion `n • (x, y) = Point.some (divX x n) (divY x y n)` says, at `2 = 0`,
*`y(n • P) = 0`*.  ⚠️ **That is false and refuted here, not merely unproved**: at `n = 1` it says
`y = 0`, and `not_nsmul_one_eq_div_of_two_eq_zero` refutes it at every point with `y ≠ 0`.  The
same reading kills `addY_self_eq_div` one index up, where the denominator `2 ψ₂³` is itself `0`
(`addY_self_div_eq_zero_of_two_eq_zero`), while the left-hand side `y(2P)` is not.

⚠️ **This is the same shape as the tree's own ruling on `exists_equation`**, which that file states
in terms: completing the square *"does not merely prove the characteristic-`2` case less cleanly —
it cannot express it."*  ⚠️ **The two cases are not of equal cost, and that is the point of the
partition above.**  For `exists_equation` the statement mentions no `2` and a different route
reaches it; for the ladder, the statement names `divY`, and `divY` is where the `2` lives.  ⚠️ **A
route (b) must therefore replace the REPRESENTATION of the `y`-coordinate and not a proof.**

## What a route (b) owes, named so the next round does not re-derive it

What route (b) owes is the `ψ₂(P) ≠ 0` branch of `nsmul_eq_zero_iff_ψ_evalEval_eq_zero`
(`Torsion/NsmulOrder.lean`:`563`), `n • P = 0 ↔ ψₙ(P) = 0`.  ⚠️ **It is not reached through one
funnel.**  `nsmul_eq_zero_iff_ψ_evalEval_eq_zero_of_isElliptic`
(`Torsion/TwoTorsionOrder.lean`:`226`) is a WRAPPER whose only `h2`-forwarding out-edge is that
statement, and ⚠️ **no cone member at or below `NsmulOrder` can mention the wrapper at all**:
`TwoTorsionOrder` imports `NsmulOrder` imports `NsmulLadder`, so those members — the ladder leaves
among them — consume the ladder DIRECTLY.  ⚠️ **The wrapper's `2`-torsion branch is already free**
— the `ψ₂(P) = 0` case is `nsmul_eq_zero_iff_two_dvd_of_ψ_two_evalEval_eq_zero`, which binds no
`h2` — so what is owed is the other branch, at a point with `ψ₂(P) ≠ 0`, which in characteristic
`2` reads `a₁x + a₃ ≠ 0`.
⚠️ **That is the guess `#2340` flagged as one, and it is confirmed here as the live branch**: it is
`nsmul_eq_zero_iff_ψ_evalEval_eq_zero`'s own hypothesis `ht`, and the ladder is what discharges it
today.  ⚠️ **It is NOT confirmed as the `2`-to-`1` fibre count the row guessed at** — that count is
`fibreY_injective` (`Torsion/OddTorsionCount.lean`:`272`), which binds no `h2` at all and is
already characteristic-free, arguing from `Ψ₂Sq(x) ≠ 0` through
`eval_Ψ₂Sq_ne_zero_of_eval_preΨ_eq_zero`, itself `h2`-free since `#2253`.  **So the fibre count is
not where the parity sits, and a round that starts there starts in the wrong place.**

## ⚠️ What this file does NOT deliver, and why

⚠️⚠️ **`#2340` items 3, 4 and 5 are NOT delivered**: there is no new `E[n] ≃+ (ℤ/nℤ)²` at odd `n`
in characteristic `2`, no new Tate-module statement and no non-vacuity certificate for either.
**They are blocked on the route (b) named above**, which is a new point-level dictionary and not an
edit to an existing proof, and this file does not open it.  ⚠️ **No existing statement is weakened,
restated or deprecated, and no signature changes**: the unit is one new module, every declaration
in it is new, and the `215` files that bind `h2` are untouched.

⚠️ **Item 6 is delivered, and the answer is that nothing further is owed there.**
`continuous_galoisRepMatrix` (`EllipticCurves.TateModule.PrimaryMatrixContinuity`:`324`) is
parametric in a basis `b` and binds **neither** `(2 : F) ≠ 0` **nor** `(ℓ : F) ≠ 0`; the same holds
of `continuous_galoisRepMatrix_coe` at `:310`.  The hypotheses enter one level down, in whatever
produces the basis — `exists_galoisRepMatrix_of_natCast_ne_zero`
(`EllipticCurves.TateModule.MatrixRepGeneral`:`234`), which binds both.  ⚠️ **So item 4 would
discharge the matrix form in characteristic `2` as soon as it produces a basis, and no step beyond
the basis is owed**; the continuity half is already general.

⚠️ **The `(ℓ : F) ≠ 0` hypothesis is untouched here and is sharp**, and `ℓ = 2` in characteristic
`2` is `ℓ = char F`, where the conclusion is false rather than unproved.  Nothing below mentions
either.
-/

open Polynomial
open scoped Polynomial.Bivariate
open EllipticCurves.Fixture

namespace WeierstrassCurve.Affine

variable {F : Type*} [Field F] {W : Affine F} {x y : F}

/-! ## The obstruction, index-free and curve-free -/

/-- **In characteristic `2` the ladder's predicted `y`-coordinate is identically `0`** — at every
index, on every curve, above every point.

⚠️ This is one `rw` and it is the whole obstruction.  `WeierstrassCurve.Affine.divY` is
`(Tₙ − a₁·divX − a₃)/2`; in a field of characteristic `2` the denominator is `0`, and Lean's
`div_zero` makes the quotient `0` rather than undefined.  ⚠️ **So the failure is not that a proof
of the ladder breaks at `2 = 0` — it is that the object the ladder's conclusion names is the wrong
object there**, and no weakening of a hypothesis can repair a definition. -/
theorem divY_eq_zero_of_two_eq_zero (h2 : (2 : F) = 0) (n : ℤ) : W.divY x y n = 0 := by
  rw [divY, h2, div_zero]

/-- **In characteristic `2` the ladder's predicted `y`-coordinate does not depend on the point it
is predicted above.**

⚠️ The sharper reading of `divY_eq_zero_of_two_eq_zero`, and the one that says why route (a) of
`#2340` cannot be run: `Tₙ = 2y(nP) + a₁x(nP) + a₃` is the quantity the induction carries, and at
`2 = 0` the map `y ↦ 2y + a₁x + a₃` is constant in `y`.  **The ladder's `y`-half is not a lossy
representation of `y(n • P)` in characteristic `2`; it is a representation of nothing.** -/
theorem divY_eq_divY_of_two_eq_zero (h2 : (2 : F) = 0) (y' : F) (n : ℤ) :
    W.divY x y n = W.divY x y' n := by
  rw [divY_eq_zero_of_two_eq_zero h2, divY_eq_zero_of_two_eq_zero h2]

/-- **`divY_one` is false at `2 = 0` at every point with `y ≠ 0`** — so its `(2 : F) ≠ 0` is not a
convenience of the route but a hypothesis without which the statement does not hold.

⚠️ `WeierstrassCurve.Affine.divY_one` (`EllipticCurves.Torsion.NsmulLadder`) reads
`divY x y 1 = y`; delete its hypothesis and it asserts `0 = y`. -/
theorem divY_ne_of_two_eq_zero (h2 : (2 : F) = 0) (hy : y ≠ 0) (n : ℤ) : W.divY x y n ≠ y := by
  rw [divY_eq_zero_of_two_eq_zero h2]
  exact fun h => hy h.symm

/-- **The right-hand side of `addY_self_eq_div` is `0` at `2 = 0`**, for the same reason one index
down: its denominator is `2 ψ₂³`.

⚠️ Stated as the bare quotient rather than through `addY_self_eq_div` itself, because that theorem
binds `(2 : F) ≠ 0` and so cannot be instantiated at `2 = 0` to be contradicted — the refutation
has to be assembled from the two sides separately.  The matching left-hand side is computed at a
concrete characteristic-`2` point in the certificate section below. -/
theorem addY_self_div_eq_zero_of_two_eq_zero (h2 : (2 : F) = 0) :
    (W.preΨ₄.eval x -
        (W.ψ 2).evalEval x y * (W.a₁ * (W.Φ 2).eval x + W.a₃ * W.Ψ₂Sq.eval x)) /
      (2 * (W.ψ 2).evalEval x y ^ 3) = 0 := by
  rw [h2, zero_mul, div_zero]

/-! ## The obstruction at the level of points -/

section Point

variable [DecidableEq F]

/-- **The base case of the ladder is FALSE at `2 = 0`**: at a point with `y ≠ 0` there is no proof
that `1 • (x, y)` is the point the division polynomials predict, because that point has
`y`-coordinate `0` and `1 • (x, y)` is `(x, y)`.

⚠️ This is `WeierstrassCurve.Affine.nsmul_one_eq_div`'s conclusion with its `(2 : F) ≠ 0` deleted,
negated.  ⚠️ **It refutes the base case and not only the step**, which matters for scoping a route
(b): there is no induction to repair, because the rung the induction starts from is already wrong.
`nsmul_step` and `addY_self_eq_div` fail by the same reading, through `divY` and through the `2 ψ₂³`
respectively, and `divY_eq_divY_of_two_eq_zero` is why no choice of `Tₙ` repairs either. -/
theorem not_nsmul_one_eq_div_of_two_eq_zero (h2 : (2 : F) = 0) (hns : W.Nonsingular x y)
    (hy : y ≠ 0) :
    ¬ ∃ h' : W.Nonsingular (W.divX x 1) (W.divY x y 1),
      ((1 : ℤ) • Point.some x y hns : W.Point) = .some _ _ h' := by
  rintro ⟨h', hP⟩
  rw [one_zsmul, Point.some.injEq] at hP
  exact divY_ne_of_two_eq_zero h2 hy 1 hP.2.symm

end Point

/-! ## Non-vacuity: the obstruction at a concrete curve in characteristic `2`

⚠️ Everything above is a conditional on `(2 : F) = 0` together with a point having `y ≠ 0`, so it
is the vacuity-prone kind and a certificate is owed.  `EllipticCurves.Fixture.y2AddYEqX3` at
`R = ZMod 2` — `y² + y = x³`, `⟨0, 0, 1, 0, 0⟩`, `Δ = −27·b₆² = 1` — is the curve
`EllipticCurves.Torsion.TwoTorsionCharTwo` already certifies in characteristic `2`, and its
`IsElliptic` instance there is `private`, so the one-line recipe is repeated rather than imported.

⚠️ **`(0, 1)` and `(0, 0)` are the only two affine points of this curve over `ZMod 2`** — at `x = 1`
the equation reads `y² + y = 1`, and `y² + y = 0` for both elements — so the group is `ℤ/3` and the
certificates below are not a choice among many.  That is also why the `addY` certificate is taken
at `(0, 0)` and not at `(0, 1)`: `2 • (0, 1) = −(0, 1) = (0, 0)`, whose `y`-coordinate is `0`, and
the false formula would happen to hold there.  ⚠️ **A certificate that passes for the wrong reason
certifies nothing**, which is what makes the choice of point a measurement here.
-/

section Certificate

/-- `IsElliptic` for `y² + y = x³` over `ZMod 2`: `Δ = −27·b₆² = −27 = 1`, and `1 ≠ 0` there.

⚠️ The recipe is `EllipticCurves.Torsion.TwoTorsionCharTwo`'s own — `isElliptic_iff`,
`isUnit_iff_ne_zero`, `decide +kernel` — repeated because that file's instance is `private` and
`private` hides a name only downstream of the declaring module.  `EllipticCurves.Fixtures`' own
instance for this curve does not reach here either: it is stated where `−27 ≠ 0` is a `norm_num`
fact, and `ZMod 2` is not such a field. -/
private instance : (y2AddYEqX3 (ZMod 2)).IsElliptic := by
  rw [WeierstrassCurve.isElliptic_iff, isUnit_iff_ne_zero]
  decide +kernel

/-- `(0, 1)` is a nonsingular point of `y² + y = x³` over `ZMod 2`, and its `y`-coordinate is
nonzero — which is the hypothesis every statement above needs a witness for. -/
private theorem nonsingular_zero_one : (y2AddYEqX3 (ZMod 2)).Nonsingular 0 1 :=
  equation_iff_nonsingular.mp (by rw [equation_iff']; decide)

/-- `(0, 0)` is a nonsingular point of the same curve; it is where the `addY` certificate is read,
because `2 • (0, 0) = (0, 1)` has nonzero `y` while `2 • (0, 1) = (0, 0)` does not. -/
private theorem nonsingular_zero_zero : (y2AddYEqX3 (ZMod 2)).Nonsingular 0 0 :=
  equation_iff_nonsingular.mp (by rw [equation_iff']; decide)

/-- **The ladder's `n = 1` prediction is wrong at `(0, 1)` over `ZMod 2`** — `divY 0 1 1 = 0` while
`y = 1`.  This is `divY_ne_of_two_eq_zero` with every hypothesis discharged, so `divY_one`'s
`(2 : F) ≠ 0` is **sharp**. -/
private theorem divY_one_ne_zero_one : (y2AddYEqX3 (ZMod 2)).divY 0 1 1 ≠ 1 :=
  divY_ne_of_two_eq_zero (by decide) (by decide) 1

/-- **The ladder's base case is refuted at a concrete curve and point in characteristic `2`** —
`nsmul_one_eq_div` with its hypothesis deleted is false on `y² + y = x³` over `ZMod 2` at `(0, 1)`.
⚠️ **This is the non-vacuity of `not_nsmul_one_eq_div_of_two_eq_zero` and of the whole obstruction
section**: without it every statement above would be a conditional nobody had satisfied. -/
private theorem not_nsmul_one_eq_div_zero_one :
    ¬ ∃ h' : (y2AddYEqX3 (ZMod 2)).Nonsingular ((y2AddYEqX3 (ZMod 2)).divX 0 1)
        ((y2AddYEqX3 (ZMod 2)).divY 0 1 1),
      ((1 : ℤ) • Point.some 0 1 nonsingular_zero_one : (y2AddYEqX3 (ZMod 2)).Point)
        = .some _ _ h' :=
  not_nsmul_one_eq_div_of_two_eq_zero (by decide) nonsingular_zero_one (by decide)

/-- **`y(2 • (0, 0)) = 1` on `y² + y = x³` over `ZMod 2`**, computed through Mathlib's group law and
not through any division polynomial.

⚠️ Paired with `addY_self_div_eq_zero_of_two_eq_zero`, whose right-hand side is `0` here, this
refutes `addY_self_eq_div` at `2 = 0`: its two sides are `1` and `0`.  ⚠️ The hypothesis
`y ≠ negY x y` that theorem also binds is satisfied — `negY 0 0 = 1` on this curve, since `a₃ = 1`
— so the refutation is not a reading of a vacuous instance. -/
private theorem addY_self_zero_zero : (y2AddYEqX3 (ZMod 2)).addY 0 0 0
    ((y2AddYEqX3 (ZMod 2)).slope 0 0 0 0) = 1 := by
  rw [slope_of_Y_ne rfl (by decide)]
  simp only [addY, negAddY, addX, negY, y2AddYEqX3]
  norm_num
  decide

/-- **`equation_iff_sq` is false at `2 = 0`**, at `x = 1` on the same curve: no point of that
curve over `ZMod 2` lies above `x = 1`, while the squared `2`-division value there is
`(a₁·1 + a₃)² = 1 = Ψ₂Sq.eval 1`.

⚠️ This is the fourth leaf and the only one whose consumers already have an `h2`-free bypass in the
tree (`exists_equation'`), so it is certified here for completeness of the leaf set and not because
anything waits on it.  ⚠️ The mechanism is the one that file names: at `2 = 0` the left-hand side
`(2y + a₁x + a₃)²` does not mention `y`, so it cannot express the equation it claims to restate. -/
private theorem not_equation_iff_sq_one_zero :
    ¬ ((y2AddYEqX3 (ZMod 2)).Equation 1 0 ↔
      (2 * 0 + (y2AddYEqX3 (ZMod 2)).a₁ * 1 + (y2AddYEqX3 (ZMod 2)).a₃) ^ 2 =
        (y2AddYEqX3 (ZMod 2)).Ψ₂Sq.eval 1) := by
  have hL : ¬ (y2AddYEqX3 (ZMod 2)).Equation 1 0 := by rw [equation_iff']; decide
  have hR : (2 * 0 + (y2AddYEqX3 (ZMod 2)).a₁ * 1 + (y2AddYEqX3 (ZMod 2)).a₃) ^ 2 =
      (y2AddYEqX3 (ZMod 2)).Ψ₂Sq.eval 1 := by
    simp only [WeierstrassCurve.Ψ₂Sq, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
      WeierstrassCurve.b₆, y2AddYEqX3, eval_add, eval_mul, eval_pow, eval_X, eval_C]
    decide
  exact fun h => hL (h.mpr hR)

end Certificate

end WeierstrassCurve.Affine
