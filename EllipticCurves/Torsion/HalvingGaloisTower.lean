/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import EllipticCurves.Torsion.HalvingExtension
import EllipticCurves.Torsion.TwoTorsionSplittingField

/-!
# A finite Galois extension carrying both `E[2]` and a halving of a `2`-torsion point

Let `W` be an elliptic curve over a field `F` of characteristic `≠ 2` and let `S = (x, y)` be an
affine `2`-torsion point of `W`.  A Galois-descent argument at `n = 2` needs **one** extension of
`F` that is finite Galois and over which two things hold at once: `#E[2] = 4`, and `S` is twice
another point.  This file builds it.

## The tower, and why it has three floors rather than two

```
F  ⊆  L₁ := W.Ψ₂Sq.SplittingField           -- #E[2] = 4 here; Galois and finite over F
   ⊆  M  := (W⁄L₁).halvingField x₀          -- S is 2-divisible here; separable and finite over L₁
   ⊆  N  := normalClosure F M (AlgebraicClosure M)
```

with `x₀ := algebraMap F L₁ x`.

**`L₁` is the field `EllipticCurves.Torsion.TwoTorsionSplittingField`'s theorems are about** — that
module defines none, quantifying instead over an arbitrary `[W.Ψ₂Sq.IsSplittingField F L]`, and
`twoTorsionField` below is Mathlib's `SplittingField`.  `M` is
`EllipticCurves.Torsion.HalvingExtension`'s field, taken at base `L₁` rather than at base `F`.

⚠️ **Neither floor can be dropped, and the reason is not symmetric.**  The halving field of `x`
over `F` carries a halving of `S` and says nothing whatever about the *other* `2`-torsion: for a
`Ψ₂Sq` with one rational root and an irreducible quadratic factor, `E[2]` is not rational over it.
So `#E[2] = 4` is why the tower starts at `L₁`.  Conversely `Ψ₂Sq` splitting says nothing about
halvings, so the halving is why the tower does not stop there.  ⚠️ **The curve that shows this is
not the curve this file certifies on.**  `EllipticCurves.Torsion.HalvingExtension` records, of
`EllipticCurves.Fixture.y2EqX3SubX` over `ℚ`, both `Ψ₂Sq = 4X³ - 4X` — which splits there — and
`halvingX 0 = X² + 1`, which has no rational root; so that curve's `2`-torsion point `(0, 0)` is
not `2`-divisible over `ℚ` although `Ψ₂Sq` already splits.  The `Nonvacuity` section below runs on
`EllipticCurves.Fixture.y2EqX3Add4X` instead, which is the mirror: there `L₁ ⊋ ℚ` and the halving
floor is trivial.  ⚠️ **Neither fixture makes both floors proper**, which that section prices.

⚠️ **And `M / F` is separable and finite but need not be normal**, normality not being transitive,
which is why there is a third floor at all.  `N` is the normal closure, and
`EllipticCurves.Galois.NormalClosureSeparable` is where the field theory of that step lives; it is
curve-free and is shared with `EllipticCurves.Torsion.HalvingExtension`.

## ⚠️ Two things are transported to `N`, and NEITHER of them is a point or a cardinal

The obvious route to `#E[2] = 4` over `N` is to push the four points of `E[2](L₁)` up along
`Point.map` and count them with an injectivity argument.  **That is not the route taken.**
`Ψ₂Sq` splits over `L₁`, there is an `F`-algebra hom `L₁ →ₐ[F] N` (`twoTorsionFieldToGalois`),
and `Polynomial.Splits.of_algHom` carries the splitting to `N`; `card_torsion_two_of_splits` is
then the whole of it.  **No counting and no injection.**

The same holds of the halving.  What is transported is the pair of *root equations*
`halvingX`-at-`x` and `halvingY`-at-that-root, through `HalvingExtension`'s two `_baseChange`
bridges, and `exists_nsmul_two_eq_some_of_roots` is re-applied over `N`.

⚠️ **The reason both are done at the level of a `Prop` is that the type-level identity costs
more**: `((W⁄L₁)⁄L) = (W⁄L)` is `WeierstrassCurve.map_baseChange` and is **not** `rfl` — it is a
propositional equation between two `Affine L`, so a `Point`-level route has to transport a term
along it, while a statement about `Polynomial.eval` is rewritten by it in one step.  That equation
is paid exactly twice below, in `eval_halvingTowerXRoot` and `eval_halvingTowerYRoot`.

## Main statements

**The hypotheses the bullets omit**, scored from the elaborated types of this module's **17**
public declarations at the head that adds it (`Environment.const2ModIdx` returns **42** constants
for the module, **16** of them `private` — 14 written below and 2 generated).  Every statement
carries `{F : Type*} [Field F]` and `{W : Affine F}`, and then:

* `[W.IsElliptic]` occurs in the type of **5**: `isSeparable_halvingTower`,
  `isGalois_halvingGaloisField`, `card_torsion_two_halvingGaloisField`,
  `exists_nsmul_two_eq_of_roots_baseChange` and `exists_nsmul_two_eq_halvingGaloisField`.
  ⚠️ **The other 12 do not**, including `splits_Ψ₂Sq_halvingGaloisField`, which is a statement
  about a polynomial and not about a curve's torsion, and both `finiteDimensional_*` rows.
* `DecidableEq` occurs in the type of **3**, the three that mention a `Point` or a torsion count:
  `card_torsion_two_halvingGaloisField`, `exists_nsmul_two_eq_of_roots_baseChange` and
  `exists_nsmul_two_eq_halvingGaloisField`.
* `(2 : F) ≠ 0` is bound by exactly those same **5** — the two registers coincide here, which is
  a coincidence of this file and not a rule.
* *A root hypothesis* — meaning `W.Ψ₂Sq.eval x = 0`, which
  `Ψ₂Sq_eval_eq_zero_of_mem_torsion_two` (`EllipticCurves.Torsion.TwoTorsion`) supplies from
  membership of `W.torsion 2` — is bound by **4** of those 5:
  `isSeparable_halvingTower`, `isGalois_halvingGaloisField`,
  `exists_nsmul_two_eq_of_roots_baseChange` and `exists_nsmul_two_eq_halvingGaloisField`.
  ⚠️ **`card_torsion_two_halvingGaloisField` is the one that does not**, and it is not an
  oversight: `#E[2] = 4` over `N` holds at **every** `x : F`, the tower being built over a
  splitting field of `Ψ₂Sq` whether or not `x` is a root of it.

⚠️ `#print axioms` over all 42 constants of this module reaches **0** `sorryAx` and nothing outside
`{propext, Classical.choice, Quot.sound}`; **40** of the 42 return all three, and the two that
return `{propext, Quot.sound}` alone are `baseChange_baseChange'` and the `Nonvacuity` section's
`card_torsion_two_ne_halvingGaloisField_y2EqX3Add4X._proof_1_1`.

* the three floors: `twoTorsionField`, `halvingTower`, `halvingGaloisField`, and the instance
  `instIsScalarTowerHalvingTower` that makes `F ⊆ L₁ ⊆ M` a tower;
* the two roots over the middle floor: `halvingTowerXRoot`, `halvingTowerYRoot` and their
  equations `eval_halvingTowerXRoot`, `eval_halvingTowerYRoot`;
* `isSeparable_halvingTower` and `finiteDimensional_halvingTower`: `M / F` is finite separable —
  the first takes `(2 : F) ≠ 0` and a root hypothesis, the second takes neither;
* `isGalois_halvingGaloisField` and `finiteDimensional_halvingGaloisField`: `N / F` is finite
  Galois — the first takes `(2 : F) ≠ 0` and a root hypothesis, the second takes neither;
* `splits_Ψ₂Sq_halvingGaloisField` and `card_torsion_two_halvingGaloisField`: `Ψ₂Sq` splits over
  `N`, so `#E[2] = 4` there;
* `exists_nsmul_two_eq_of_roots_baseChange`: `S` is `2`-divisible over **any** extension reached
  from a field carrying both halving roots — the general form, stated once;
* `exists_nsmul_two_eq_halvingGaloisField`: `S` is `2`-divisible over `N`, that form at `M` and
  `N`.

⚠️ `card_torsion_two_halvingGaloisField` and `exists_nsmul_two_eq_halvingGaloisField` take a
`[DecidableEq _]`, which the `Point` group structure and the `2`-torsion count need.  **Its binder
must come after the `(x : F)` it mentions**: written before it, `x` is auto-bound to a fresh
variable and the statement's elaboration does not terminate (*"(deterministic) timeout at
`isDefEq`"*, measured).  It reads as a heartbeat problem and is a binder-order problem.

## What is *not* here

* **A discharge of `hprin`, and nothing about divisors.**  `#962` records that gate and this file
  supplies two rows of `#2029`'s ledger for it.  No statement below mentions a divisor, a place, a
  function field, `mulByTwoEndo` or Hilbert 90, and none of them is in this module's import
  closure.
* **`n = 3`.**  Every statement below is at `n = 2`: `Ψ₂Sq`, `torsion 2`, `halvingX`, `halvingY`.
  `EllipticCurves.Torsion.ThreeTorsionStructure` is untouched and nothing here applies to it.
* **A `Point`-level base-change API.**  `Point.map` is not used below and `pointBaseChange` is not
  imported; the `((W⁄L₁)⁄M) = (W⁄M)` identity is never taken at the level of a type.
* **Any statement about `Ψ₂Sq` over the middle floor.**  Nothing below says `Ψ₂Sq` splits over `M`;
  it says so over `N`, and only because `L₁ ⊆ N`.
* **A degree, or a Galois group.**  `[N : F]` is not computed and `Gal(N/F)` is not identified with
  a subgroup of anything.  ⚠️ The extension `N` is *some* finite Galois extension with the two
  properties, and nothing below says it is the smallest one.
* **Characteristic `2`.**  Every statement that uses the halving quadratics non-trivially carries
  `(2 : F) ≠ 0`, inherited from `HalvingExtension`.

## Non-vacuity

The `Nonvacuity` section runs on the shared `EllipticCurves.Fixture.y2EqX3Add4X` at `R = ℚ` —
`y² = x³ + 4x`, whose cubic is `4X(X² + 4)` and whose affine `2`-torsion point over `ℚ` is
`(0, 0)`.  ⚠️ **The tower is shown proper by a pair of counts rather than by a statement about a
field**: `#E[2] = 2` over `ℚ` against `#E[2] = 4` over `N`, so the base change is not an
isomorphism and no property of `L₁`, `M` or `N` as types is ever needed.

⚠️ **One of the two main statements is certified inhabited and NOT certified informative, and the
limit is stated rather than papered over.**  `(0, 0) = 2 • (2, 4)` already over `ℚ` on this
curve — its `halvingX 0` is `X² - 4`, which `EllipticCurves.Torsion.HalvingExtension` records — so
the halving statement is true over `ℚ` itself here.  The curve on which it is non-trivial is
`EllipticCurves.Fixture.y2EqX3SubX`, whose `halvingX 0 = X² + 1` has no rational root; **it cannot
serve here** because its `2`-torsion is already split over `ℚ`, which would make the count half
vacuous instead.  ⚠️ **Neither fixture makes both floors proper**, and the reason is visible in the
family: for `y² = x³ + ax` one has `Ψ₂Sq = 4X(X² + a)` and `halvingX 0 = X² - C a`, so `L₁ ⊋ ℚ`
exactly when `-a` is not a rational square and the halving floor is proper exactly when `a` is not
one.  The two fixtures are `a = -1` and `a = 4` and each fails one condition; **`a = 2` satisfies
both**, its two floors being `ℚ(√-2)` and `ℚ(√2)`, and `¬ IsSquare (2 : ℚ)` is `by norm_num` at
this pin through `Mathlib.Tactic.NormNum.IsSquare`, so the obstruction is not the arithmetic.  It
is not added because a characteristic-zero certificate curve belongs in `EllipticCurves.Fixtures`,
whose `## The design` section states *"One `IsElliptic` instance per curve"* over a named list of
**five** discriminants; extending that list, or adding a `private` local fixture and a row to the
census of locally-defined fixtures the same module keeps, is a different branch's edit either way.
-/

open Polynomial IntermediateField

namespace WeierstrassCurve.Affine

variable {F : Type*} [Field F] {W : Affine F}

/-! ## The tower -/

/-- `((W⁄L₁)⁄L) = (W⁄L)` in a tower, which is `WeierstrassCurve.map_baseChange` at the
`IsScalarTower` map.

⚠️ `EllipticCurves.Torsion.HalvingExtension` proves the same one-liner and keeps it `private`, so
it is restated rather than imported.  It is **not** `rfl`: the two sides are different terms of
`Affine L` and only the `IsScalarTower` axiom identifies their coefficients. -/
private lemma baseChange_baseChange' (W : Affine F) (L₁ : Type*) [Field L₁] [Algebra F L₁]
    (L : Type*) [Field L] [Algebra F L] [Algebra L₁ L] [IsScalarTower F L₁ L] :
    ((W⁄L₁)⁄L) = (W⁄L) :=
  WeierstrassCurve.map_baseChange (R := F) W (IsScalarTower.toAlgHom F L₁ L)

/-- A numeral that is nonzero in `F` stays nonzero in a field extension.

⚠️ Both `EllipticCurves.Torsion.HalvingExtension` and
`EllipticCurves.Torsion.TwoTorsionSplittingField` keep a `private` copy of this, and the
general-numeral form `algebraMap_ofNat_ne_zero` is in `EllipticCurves.FunctionField`, downstream of
`Torsion/`. -/
private lemma algebraMap_two_ne_zero'' {L : Type*} [Field L] [Algebra F L] (h2 : (2 : F) ≠ 0) :
    (2 : L) ≠ 0 := by
  rw [← map_ofNat (algebraMap F L) 2, ne_eq, map_eq_zero]
  exact h2

variable (W) in
/-- **The first floor `L₁`**: a splitting field of the `2`-torsion cubic over `F`, over which
`#E[2] = 4`. -/
noncomputable abbrev twoTorsionField : Type _ := W.Ψ₂Sq.SplittingField

variable (W) in
/-- **The second floor `M`**: the halving field of `x`, taken over `L₁` rather than over `F`. -/
noncomputable abbrev halvingTower (x : F) : Type _ :=
  (W⁄(W.twoTorsionField)).halvingField (algebraMap F W.twoTorsionField x)

/-- `F ⊆ L₁ ⊆ M` is a tower.

⚠️ **This is the one instance the file turns on and instance search does not find it.**
`Algebra F M` and `Algebra L₁ M` are both found — Mathlib's `SplittingField` derives an
`Algebra R _` and an
`IsScalarTower R K _` for every `[Algebra R K]` — which gives `IsScalarTower F L₁ K₂`,
`IsScalarTower L₁ K₂ M` and `IsScalarTower F K₂ M` for the intervening `K₂ := halvingXField`, but
not the composite of the outer two. -/
instance instIsScalarTowerHalvingTower (x : F) :
    IsScalarTower F W.twoTorsionField (W.halvingTower x) := by
  refine IsScalarTower.of_algebraMap_eq fun a => ?_
  rw [IsScalarTower.algebraMap_apply F
      ((W⁄(W.twoTorsionField)).halvingXField (algebraMap F W.twoTorsionField x))
      (W.halvingTower x),
    IsScalarTower.algebraMap_apply F W.twoTorsionField
      ((W⁄(W.twoTorsionField)).halvingXField (algebraMap F W.twoTorsionField x)),
    ← IsScalarTower.algebraMap_apply W.twoTorsionField
      ((W⁄(W.twoTorsionField)).halvingXField (algebraMap F W.twoTorsionField x))
      (W.halvingTower x)]

/-! ## The two halving roots, read over the second floor -/

/-- The halving `x`-coordinate, as an element of the second floor `M`. -/
noncomputable def halvingTowerXRoot (W : Affine F) (x : F) : W.halvingTower x :=
  algebraMap ((W⁄(W.twoTorsionField)).halvingXField (algebraMap F W.twoTorsionField x))
    (W.halvingTower x)
    ((W⁄(W.twoTorsionField)).halvingXRoot (algebraMap F W.twoTorsionField x))

/-- The halving `y`-coordinate above it, which is where the second floor is adjoined. -/
noncomputable def halvingTowerYRoot (W : Affine F) (x : F) : W.halvingTower x :=
  (W⁄(W.twoTorsionField)).halvingYRoot (algebraMap F W.twoTorsionField x)

/-- **The halving quadratic of `x` has a root over `M`**, stated over `(W⁄M)` and not over
`((W⁄L₁)⁄M)`.

⚠️ The whole content is the change of curve: `eval_halvingXRoot` and `eval_halvingX_baseChange`
give the equation over `((W⁄L₁)⁄M)` at `algebraMap L₁ M (algebraMap F L₁ x)`, and
`baseChange_baseChange'` together with `IsScalarTower.algebraMap_apply` is what turns it into the
form a consumer over `F` can use. -/
theorem eval_halvingTowerXRoot (x : F) :
    ((W⁄(W.halvingTower x)).halvingX (algebraMap F (W.halvingTower x) x)).eval
      (W.halvingTowerXRoot x) = 0 := by
  have h : (((W⁄(W.twoTorsionField))⁄(W.halvingTower x)).halvingX
      (algebraMap (W.twoTorsionField) (W.halvingTower x)
        (algebraMap F W.twoTorsionField x))).eval (W.halvingTowerXRoot x) = 0 :=
    eval_halvingX_baseChange (eval_halvingXRoot _)
  rwa [baseChange_baseChange' W W.twoTorsionField (W.halvingTower x),
    ← IsScalarTower.algebraMap_apply F W.twoTorsionField (W.halvingTower x) x] at h

/-- **The `y`-quadratic above that root has a root over `M`**, in the same form. -/
theorem eval_halvingTowerYRoot (x : F) :
    ((W⁄(W.halvingTower x)).halvingY (W.halvingTowerXRoot x)).eval
      (W.halvingTowerYRoot x) = 0 := by
  have h : (((W⁄(W.twoTorsionField))⁄(W.halvingTower x)).halvingY
      (W.halvingTowerXRoot x)).eval (W.halvingTowerYRoot x) = 0 :=
    eval_halvingY_baseChange (eval_halvingYRoot _ _)
  rwa [baseChange_baseChange' W W.twoTorsionField (W.halvingTower x)] at h

/-! ## The second floor is finite and separable over `F` -/

variable [W.IsElliptic]

/-- **`M / F` is separable.**  Separability is transitive, `L₁ / F` is Galois by `#1985` and
`M / L₁` is separable by `#1986` — the latter applied at the base-changed curve over `L₁`, whose
`Ψ₂Sq` is separable by `separable_Ψ₂Sq` there rather than by mapping `F`'s up. -/
theorem isSeparable_halvingTower (h2 : (2 : F) ≠ 0) {x : F} (hx : W.Ψ₂Sq.eval x = 0) :
    Algebra.IsSeparable F (W.halvingTower x) := by
  haveI : (W⁄(W.twoTorsionField)).IsElliptic :=
    inferInstanceAs (W.map (algebraMap F W.twoTorsionField)).IsElliptic
  haveI := isGalois_of_isSplittingField_Ψ₂Sq (W := W) (L := W.twoTorsionField) h2
  haveI : Algebra.IsSeparable W.twoTorsionField (W.halvingTower x) :=
    isSeparable_halvingField (algebraMap_two_ne_zero'' h2)
      (separable_Ψ₂Sq (algebraMap_two_ne_zero'' h2)) (eval_Ψ₂Sq_baseChange hx)
  exact Algebra.IsSeparable.trans F W.twoTorsionField (W.halvingTower x)

omit [W.IsElliptic] in
/-- **`M / F` is finite**, each floor being a splitting field of a polynomial.  ⚠️ It takes no
hypothesis on the characteristic and does not need `[W.IsElliptic]`. -/
theorem finiteDimensional_halvingTower {x : F} : FiniteDimensional F (W.halvingTower x) := by
  haveI : FiniteDimensional F W.twoTorsionField :=
    finiteDimensional_of_isSplittingField_Ψ₂Sq W W.twoTorsionField
  haveI : FiniteDimensional W.twoTorsionField (W.halvingTower x) := finiteDimensional_halvingField
  exact FiniteDimensional.trans F W.twoTorsionField (W.halvingTower x)

/-! ## The third floor: the Galois closure -/

variable (W) in
/-- **The third floor `N`**: the Galois closure of the tower over `F`. -/
noncomputable abbrev halvingGaloisField (x : F) : Type _ :=
  normalClosure F (W.halvingTower x) (AlgebraicClosure (W.halvingTower x))

/-- **`N / F` is Galois.**  `EllipticCurves.Galois.NormalClosureSeparable`'s curve-free lemma at
`isSeparable_halvingTower`.  ⚠️ **Finiteness is not used for this half** — `IsGalois` asks only for
normal and separable, and `finiteDimensional_halvingGaloisField` below is a separate statement with
a separate proof. -/
theorem isGalois_halvingGaloisField (h2 : (2 : F) ≠ 0) {x : F} (hx : W.Ψ₂Sq.eval x = 0) :
    IsGalois F (W.halvingGaloisField x) := by
  haveI := isSeparable_halvingTower h2 hx
  exact _root_.isGalois_normalClosure_of_isSeparable F (W.halvingTower x)

omit [W.IsElliptic] in
/-- **`N / F` is finite**, which is the half of *"finite Galois"* that Mathlib's Hilbert 90
(`groupCohomology.isMulCoboundary₁_of_isMulCocycle₁_of_aut_to_units`) takes as a hypothesis.  ⚠️ It
takes no hypothesis on the characteristic and does not need `[W.IsElliptic]`. -/
theorem finiteDimensional_halvingGaloisField {x : F} :
    FiniteDimensional F (W.halvingGaloisField x) := by
  haveI : FiniteDimensional F (W.halvingTower x) := finiteDimensional_halvingTower
  infer_instance

/-! ## `#E[2] = 4` over the third floor -/

variable (W) in
/-- The composite `F`-algebra hom `L₁ → N`, which exists because `L₁ ⊆ M ⊆ N` are all `F`-algebras
in a tower. -/
noncomputable def twoTorsionFieldToGalois (x : F) :
    W.twoTorsionField →ₐ[F] W.halvingGaloisField x :=
  (IsScalarTower.toAlgHom F (W.halvingTower x) (W.halvingGaloisField x)).comp
    (IsScalarTower.toAlgHom F W.twoTorsionField (W.halvingTower x))

omit [W.IsElliptic] in
/-- **The `2`-torsion cubic splits over `N`.**

⚠️ **This is where the `#E[2] = 4` row is actually paid, and it costs no count and no injection.**
`Ψ₂Sq` splits over `L₁` by construction, `twoTorsionFieldToGalois` is an `F`-algebra hom into `N`,
and `Polynomial.Splits.of_algHom` carries a split polynomial along one. -/
theorem splits_Ψ₂Sq_halvingGaloisField (x : F) : (W⁄(W.halvingGaloisField x)).Ψ₂Sq.Splits := by
  have hL₁ : Splits (W.Ψ₂Sq.map (algebraMap F W.twoTorsionField)) := by
    have h := splits_Ψ₂Sq_baseChange W W.twoTorsionField
    rwa [show (W⁄(W.twoTorsionField)) = W.map (algebraMap F W.twoTorsionField) from rfl,
      WeierstrassCurve.map_Ψ₂Sq] at h
  have hN := Polynomial.Splits.of_algHom hL₁ (twoTorsionFieldToGalois W x)
  rwa [show (W⁄(W.halvingGaloisField x)) = W.map (algebraMap F (W.halvingGaloisField x)) from rfl,
    WeierstrassCurve.map_Ψ₂Sq]

/-- **`#E[2] = 4` over `N`.**  `card_torsion_two_of_splits` at the splitting above.

⚠️ The `[DecidableEq _]` binder comes **after** `(x : F)` deliberately; before it, `x` auto-binds
to a fresh variable and the statement does not elaborate. -/
theorem card_torsion_two_halvingGaloisField (h2 : (2 : F) ≠ 0) (x : F)
    [DecidableEq (W.halvingGaloisField x)] :
    Nat.card ((W⁄(W.halvingGaloisField x)).torsion 2) = 4 := by
  haveI : (W⁄(W.halvingGaloisField x)).IsElliptic :=
    inferInstanceAs (W.map (algebraMap F (W.halvingGaloisField x))).IsElliptic
  exact card_torsion_two_of_splits (algebraMap_two_ne_zero'' h2) (splits_Ψ₂Sq_halvingGaloisField x)

/-! ## The halving over the third floor -/

/-- **`S` is twice another point over any extension reached from a field carrying both halving
roots.**

The general form, stated once and used at `M ⊆ N`: the two root equations are pushed up by
`HalvingExtension`'s `_baseChange` bridges and `exists_nsmul_two_eq_some_of_roots` is re-applied
over the top field.  ⚠️ **No `Point` is transported** — the hypothesis and the conclusion are about
different curves, and only `Polynomial.eval` equations cross between them. -/
theorem exists_nsmul_two_eq_of_roots_baseChange {M L : Type*} [Field M] [Field L] [Algebra F M]
    [Algebra F L] [Algebra M L] [IsScalarTower F M L] [DecidableEq L]
    (h2 : (2 : F) ≠ 0) {x y : F} (hQ : W.Nonsingular x y) (hx : W.Ψ₂Sq.eval x = 0)
    {r s : M} (hr : ((W⁄M).halvingX (algebraMap F M x)).eval r = 0)
    (hs : ((W⁄M).halvingY r).eval s = 0) :
    ∃ P : (W⁄L).Point, 2 • P = Point.some (algebraMap F L x) (algebraMap F L y)
      ((W.map_nonsingular (algebraMap F L).injective x y).mpr hQ) := by
  haveI : (W⁄L).IsElliptic := inferInstanceAs (W.map (algebraMap F L)).IsElliptic
  have hrL : ((W⁄L).halvingX (algebraMap F L x)).eval (algebraMap M L r) = 0 :=
    eval_halvingX_baseChange hr
  have hsL : ((W⁄L).halvingY (algebraMap M L r)).eval (algebraMap M L s) = 0 := by
    refine eval_halvingY_baseChange ?_
    rw [Polynomial.eval_map, Polynomial.eval₂_at_apply, hs, map_zero]
  exact exists_nsmul_two_eq_some_of_roots (algebraMap_two_ne_zero'' h2) _
    (eval_Ψ₂Sq_baseChange hx) hrL hsL

/-- **`S` is twice another point over `N`.**

The conclusion `#2029`'s step 4 needs, together with `card_torsion_two_halvingGaloisField` and the
two Galois statements above. -/
theorem exists_nsmul_two_eq_halvingGaloisField (h2 : (2 : F) ≠ 0) {x y : F}
    (hQ : W.Nonsingular x y) (hx : W.Ψ₂Sq.eval x = 0)
    [DecidableEq (W.halvingGaloisField x)] :
    ∃ P : (W⁄(W.halvingGaloisField x)).Point,
      2 • P = Point.some (algebraMap F (W.halvingGaloisField x) x)
        (algebraMap F (W.halvingGaloisField x) y)
        ((W.map_nonsingular (algebraMap F (W.halvingGaloisField x)).injective x y).mpr hQ) :=
  exists_nsmul_two_eq_of_roots_baseChange h2 hQ hx (eval_halvingTowerXRoot x)
    (eval_halvingTowerYRoot x)

/-! ## Non-vacuity

The certificate curve is the shared `EllipticCurves.Fixture.y2EqX3Add4X` at `R = ℚ`:
`y² = x³ + 4x`, whose `2`-torsion cubic is `4X³ + 16X = 4 · X · (X² + 4)` and whose affine
`2`-torsion point over `ℚ` is `(0, 0)`.

⚠️ **What makes the block below say something is the pair of counts, not either one of them.**
`#E[2] = 2` over `ℚ` (`card_torsion_two_y2EqX3Add4X_base`) against `#E[2] = 4` over `N`
(`card_torsion_two_halvingGaloisField_y2EqX3Add4X`): `2 ≠ 4`, so the base change is not an
isomorphism and **the tower this file builds is a proper extension of `ℚ`** — with no statement
about `L₁`, `M` or `N` as types anywhere in the argument.

⚠️ **What this certificate does NOT make non-trivial, said rather than skipped.**
`exists_nsmul_two_eq_halvingGaloisField_y2EqX3Add4X` below is *inhabited* but not *informative* on
this curve: `(0, 0) = 2 • (2, 4)` already over `ℚ` — `halvingX 0` is `X² - 4` here, which
`EllipticCurves.Torsion.HalvingExtension` records — so that statement is true over `ℚ` itself and
the tower buys nothing for it.  The curve on which the halving half is genuinely non-trivial is
`EllipticCurves.Fixture.y2EqX3SubX`, whose `halvingX 0 = X² + 1` has no rational root; ⚠️ **it
cannot serve here**, because its `2`-torsion is already split over `ℚ`, which would make the count
half vacuous instead.  The module docstring's `## Non-vacuity` section names the single curve that
would carry both and says why it is not added.

⚠️ **The `#E[2] = 2` count is restated rather than cited.**
`EllipticCurves.Torsion.TwoTorsionSplittingField` proves it on the same curve and keeps it
`private`, as it keeps the factorisation and the root count it rests on.
-/

section Nonvacuity

open EllipticCurves.Fixture

/-- The `2`-torsion cubic of the certificate curve, factored: `4X³ + 16X = 4 · X · (X² + 4)`. -/
private lemma Ψ₂Sq_y2EqX3Add4X' :
    (y2EqX3Add4X ℚ).Ψ₂Sq = C 4 * X * (X ^ 2 + C 4) := by
  simp only [WeierstrassCurve.Ψ₂Sq, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, y2EqX3Add4X]
  norm_num only
  simp only [map_ofNat, Polynomial.C_0]
  ring

/-- **The only rational root of the cubic is `0`**, because `x² + 4` is positive. -/
private lemma eval_Ψ₂Sq_y2EqX3Add4X_eq_zero_iff' {x : ℚ} :
    (y2EqX3Add4X ℚ).Ψ₂Sq.eval x = 0 ↔ x = 0 := by
  rw [Ψ₂Sq_y2EqX3Add4X']
  simp only [eval_mul, eval_add, eval_pow, eval_C, eval_X]
  constructor
  · intro h
    rcases mul_eq_zero.mp h with h' | h'
    · rcases mul_eq_zero.mp h' with h'' | h''
      · norm_num at h''
      · exact h''
    · nlinarith [sq_nonneg x]
  · rintro rfl
    ring

private lemma eval_Ψ₂Sq_y2EqX3Add4X_zero : (y2EqX3Add4X ℚ).Ψ₂Sq.eval 0 = 0 :=
  eval_Ψ₂Sq_y2EqX3Add4X_eq_zero_iff'.mpr rfl

private lemma card_roots_Ψ₂Sq_y2EqX3Add4X' :
    Nat.card {x : ℚ // (y2EqX3Add4X ℚ).Ψ₂Sq.eval x = 0} = 1 := by
  rw [Nat.card_eq_one_iff_unique]
  exact ⟨⟨fun a b => Subtype.ext ((eval_Ψ₂Sq_y2EqX3Add4X_eq_zero_iff'.mp a.2).trans
    (eval_Ψ₂Sq_y2EqX3Add4X_eq_zero_iff'.mp b.2).symm)⟩,
    ⟨⟨0, eval_Ψ₂Sq_y2EqX3Add4X_eq_zero_iff'.mpr rfl⟩⟩⟩

/-- **`#E[2] = 2` over `ℚ`** for `y² = x³ + 4x`: the point at infinity and the single rational root
`0` of the cubic.  ⚠️ This is the half of the certificate that makes the base change below say
something. -/
private theorem card_torsion_two_y2EqX3Add4X_base :
    Nat.card ((y2EqX3Add4X ℚ).torsion 2) = 2 := by
  haveI := (y2EqX3Add4X ℚ).finite_roots_Ψ₂Sq (by norm_num)
  rw [Nat.card_congr (torsionTwoEquiv (W := y2EqX3Add4X ℚ) (by norm_num)), Finite.card_option,
    card_roots_Ψ₂Sq_y2EqX3Add4X']

private lemma nonsingular_zero_y2EqX3Add4X : (y2EqX3Add4X ℚ).Nonsingular 0 0 := by
  refine equation_iff_nonsingular.mp ?_
  simp [equation_iff', y2EqX3Add4X]

private noncomputable instance :
    DecidableEq ((y2EqX3Add4X ℚ).halvingGaloisField (0 : ℚ)) := Classical.decEq _

/-- **The tower's top floor is a finite Galois extension of `ℚ`**, with no hypothesis at all. -/
private theorem isGalois_halvingGaloisField_y2EqX3Add4X :
    IsGalois ℚ ((y2EqX3Add4X ℚ).halvingGaloisField (0 : ℚ)) :=
  isGalois_halvingGaloisField (by norm_num) eval_Ψ₂Sq_y2EqX3Add4X_zero

private theorem finiteDimensional_halvingGaloisField_y2EqX3Add4X :
    FiniteDimensional ℚ ((y2EqX3Add4X ℚ).halvingGaloisField (0 : ℚ)) :=
  finiteDimensional_halvingGaloisField

/-- **`#E[2] = 4` over the top floor**, with no hypothesis at all — where
`card_torsion_two_y2EqX3Add4X_base` gives `2` over `ℚ`. -/
private theorem card_torsion_two_halvingGaloisField_y2EqX3Add4X :
    Nat.card (((y2EqX3Add4X ℚ)⁄((y2EqX3Add4X ℚ).halvingGaloisField (0 : ℚ))).torsion 2) = 4 :=
  card_torsion_two_halvingGaloisField (by norm_num) 0

/-- **The tower is a proper extension of `ℚ`**, read off the two counts and nothing else. -/
private theorem card_torsion_two_ne_halvingGaloisField_y2EqX3Add4X :
    Nat.card ((y2EqX3Add4X ℚ).torsion 2)
      ≠ Nat.card (((y2EqX3Add4X ℚ)⁄((y2EqX3Add4X ℚ).halvingGaloisField (0 : ℚ))).torsion 2) := by
  rw [card_torsion_two_y2EqX3Add4X_base, card_torsion_two_halvingGaloisField_y2EqX3Add4X]
  omega

/-- **`(0, 0)` is twice a point over the top floor.**  ⚠️ Inhabited but not informative on this
curve — see this section's opening note. -/
private theorem exists_nsmul_two_eq_halvingGaloisField_y2EqX3Add4X :
    ∃ P : ((y2EqX3Add4X ℚ)⁄((y2EqX3Add4X ℚ).halvingGaloisField (0 : ℚ))).Point,
      2 • P = Point.some (algebraMap ℚ ((y2EqX3Add4X ℚ).halvingGaloisField (0 : ℚ)) 0)
        (algebraMap ℚ ((y2EqX3Add4X ℚ).halvingGaloisField (0 : ℚ)) 0)
        (((y2EqX3Add4X ℚ).map_nonsingular
          (algebraMap ℚ ((y2EqX3Add4X ℚ).halvingGaloisField (0 : ℚ))).injective 0 0).mpr
            nonsingular_zero_y2EqX3Add4X) :=
  exists_nsmul_two_eq_halvingGaloisField (by norm_num) nonsingular_zero_y2EqX3Add4X
    eval_Ψ₂Sq_y2EqX3Add4X_zero

end Nonvacuity

end WeierstrassCurve.Affine
