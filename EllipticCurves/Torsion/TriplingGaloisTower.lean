/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import EllipticCurves.Torsion.HalvingExtension
import EllipticCurves.Torsion.ThreeDivisionField
import EllipticCurves.Torsion.TriplingSeparable

/-!
# A finite Galois extension carrying both `E[3]` and a tripling of a `3`-torsion point

Let `W` be an elliptic curve over a field `F` of characteristic `≠ 2, 3` and let `S = (x₀, y₀)` be
an affine `3`-torsion point of `W`.  The Galois-descent argument `#962` runs at `n = 3` needs
**one** extension of `F` that is finite Galois and over which two things hold at once:
`#E[3] = 9`, and `S` is three times another point.  This file builds it.  It is the `n = 3`
analogue of `EllipticCurves.Torsion.HalvingGaloisTower`, and the places where the analogy breaks
are the content.

## The tower

```
F  ⊆  L₁ := threeDivisionField W            -- #E[3] = 9 here; separable and finite over F
   ⊆  M  := (W⁄L₁).triplingField r₀         -- S is 3-divisible here; separable and finite over L₁
   ⊆  N  := normalClosure F M (AlgebraicClosure M)
```

with `r₀ := algebraMap F L₁ x₀`.

⚠️ **Three named floors are five field extensions**, and the diagram above hides two of them.
`threeDivisionField W` is itself the two-layer tower of
`EllipticCurves.Torsion.ThreeDivisionField` — a splitting field of `Ψ₂SqRootPoly` over a splitting
field of `Ψ₃` — and `triplingField` below is another two-layer tower, the `y`-quadratic over the
tripling polynomial's splitting field.  The full chain is

```
F ⊆ W.Ψ₃.SplittingField ⊆ L₁ ⊆ (W⁄L₁).triplingXField r₀ ⊆ M ⊆ N.
```

⚠️ **Neither named floor can be dropped, for the same asymmetric reason as at `n = 2`.**  The
tripling field of `x₀` over `F` carries a tripling of `S` and says nothing about the *other*
`3`-torsion, so `#E[3] = 9` is why the tower starts at `L₁`; and `Ψ₃` splitting says nothing about
triplings, so the tripling is why it does not stop there.  ⚠️ **And `M / F` is separable and finite
but need not be normal** — normality is not transitive — which is why there is a third floor at
all.  `EllipticCurves.Galois.NormalClosureSeparable` is where the field theory of that step lives;
it is curve-free and is shared with `HalvingExtension`, `ThreeDivisionField` and
`HalvingGaloisTower`.

## ⚠️ What the `n = 2` file's construction does NOT transpose, and what transposes for free

**The middle floor is a degree-`9` splitting field and not a quadratic.**  At `n = 2` the quartic
`Φ₂ − C x₀·ΨSq₂` is a perfect square when `x₀` is `2`-torsion
(`Φ_two_sub_C_mul_Ψ₂Sq_eq_halvingX_sq`), and `halvingX` is its square root — a *quadratic*, whose
separability is a discriminant computation.  ⚠️ **There is no such degeneration at `n = 3`**:
`triplingX x₀ := Φ₃ − C x₀·ΨSq₃` is monic of degree `9` (`natDegree_triplingX`, from
`natDegree_Φ_sub_C_mul_ΨSq`), and under this file's hypotheses it is squarefree rather than a
power (`separable_triplingX`).  Its separability is
`separable_Φ_three_sub_C_mul_ΨSq` (`EllipticCurves.Torsion.TriplingSeparable`) — the theorem
`#2216` was blocked on and which landed in `88a0ed6`.

⚠️ **The `y`-quadratic transposes verbatim, and `#2216`'s own item 2 predicted that half exactly.**
`WeierstrassCurve.Affine.halvingY` is **index-free** — it is the quadratic cut out by the
Weierstrass equation at a given `x`, with discriminant `Ψ₂Sq.eval x` — so **five** declarations of
`EllipticCurves.Torsion.HalvingExtension`'s `y`-layer are consumed here unchanged: `halvingY`,
`degree_halvingY`, `separable_halvingY`, `equation_of_eval_halvingY_eq_zero` and
`eval_halvingY_baseChange`.  ⚠️ **But item 2 also predicted that *both* `_baseChange` bridges would
have to be rewritten, and only one did.**  `eval_triplingX_baseChange` below is the rewrite;
`eval_halvingY_baseChange` is consumed as it stands, at **three** sites.

## ⚠️ The step that is genuinely different: why the tripling root is not `2`-torsion

The `y`-quadratic over the middle floor is separable exactly when `Ψ₂Sq` does not vanish at the
root adjoined below it, and at `n = 2` that is a statement about points:
`Ψ₂Sq_eval_ne_zero_of_root_halvingX` argues that a halving of a `2`-torsion point cannot itself be
`2`-torsion, since `2P = S` and `2P = O` would give `S = O`.

⚠️ **`Ψ₂Sq_eval_ne_zero_of_root_triplingX` is not that argument transposed — it is a polynomial
identity, and no point and no group law enters it.**  Mathlib's `Φ_three` is
`Φ₃ = X·Ψ₃² − preΨ₄·Ψ₂Sq`, so at a root `r` of `Ψ₂Sq` the tripling equation
`Φ₃(r) = x₀·Ψ₃(r)²` collapses to `(r − x₀)·Ψ₃(r)² = 0`.  And `Ψ₃(r) ≠ 0`
(`Ψ₃_eval_ne_zero_of_root_triplingX`, from `eval_Φ_three_ne_zero_of_root_ΨSq`), so `r = x₀` — which
contradicts `Ψ₃(x₀) = 0`.  ⚠️ **That contradiction is where the root hypothesis is spent**, and it
is the only place in the separability half where being `3`-torsion rather than arbitrary is used
for anything but `separable_Φ_three_sub_C_mul_ΨSq`.

## ⚠️ The divisibility half binds NO root hypothesis, and at `n = 2` it does

Measured over the elaborated types below: of the **4** statements that mention a `Point`,
**0** bind `W.Ψ₃.eval x₀ = 0` and **0** bind `(3 : F) ≠ 0`.
`exists_nsmul_three_eq_triplingField` and `exists_nsmul_three_eq_triplingGaloisField` hold at
**every** affine point `(x₀, y₀)` of `W`, `3`-torsion or not: the roots of `triplingX x₀` solve
`x(3P) = x₀` whatever `x₀` is, and `exists_nsmul_three_eq_some_of_root`
(`EllipticCurves.Torsion.TriplingSurjective`) asks only for a root with a point above it.

⚠️ **This is the opposite of `n = 2`**, where `exists_nsmul_two_eq_halvingField` binds
`W.Ψ₂Sq.eval x₀ = 0` because `halvingX` only *exists* as a square root of the quartic when `x₀` is
`2`-torsion.  ⚠️ **What the root hypothesis buys here is not the tripling but the Galois property**:
`isGalois_triplingXField`, `isSeparable_triplingField`, `isSeparable_triplingTower` and
`isGalois_triplingGaloisField` all bind it, and none of the four `Point` statements does.  So the
two halves of this file have *disjoint* hypothesis registers and are true of different `x₀`.

## Main statements

**The hypotheses the bullets omit**, scored from the elaborated types of this module's written
public declarations.  ⚠️ **Publish the construction with the count**: the rule
*non-`private`, not `Name.isInternal`* — the one that returns `HalvingGaloisTower`'s published
**17** — returns **45** here, of which **3** are compiler-generated (`triplingX.eq_1`,
`triplingYPoly.eq_1` and `exists_root_triplingX_of_nsmul_three_eq.match_1_1`), leaving **42**
written by hand: **30** `theorem`, **7** `noncomputable def`, **4** `noncomputable abbrev` and
**1** `instance`.  `Environment.const2ModIdx` returns **71** constants for the module, **12** of
them `private` and all **12** written below.  Every statement carries `{F : Type*} [Field F]` and
`{W : Affine F}`, and then, over the **42**:

* `[W.IsElliptic]` occurs in the type of **15**.  ⚠️ **The other 27 do not**, including every
  `finiteDimensional_*` row, `natDegree_triplingX`, `degree_triplingX`, `map_triplingX`,
  `eval_Ψ₃_baseChange` and all four floors as types.
* `(2 : F) ≠ 0` is bound by **11** and `(3 : F) ≠ 0` by **7**; the seven are a subset of the
  eleven, and the four that carry `h2` without `h3` are exactly the four `Point` statements.
* `[DecidableEq _]` is bound by **6**, and they are exactly the statements that mention a `Point`
  or a torsion count: the four `Point` rows,
  `card_torsion_three_triplingGaloisField` and
  `nonempty_torsionThree_addEquiv_triplingGaloisField`.
* *The root hypothesis* `W.Ψ₃.eval x₀ = 0` is bound by **9**.  ⚠️ **`card_torsion_three_*` is not
  among them, and that is not an oversight**: `#E[3] = 9` over `N` holds at **every** `x₀ : F`,
  the tower being built over the `3`-division field whether or not `x₀` is a root of `Ψ₃`.  This is
  the same non-oversight `HalvingGaloisTower` records at `n = 2`, for the same reason.

⚠️ `#print axioms` over all **71** constants of this module reaches **0** `sorryAx` and nothing
outside `{propext, Classical.choice, Quot.sound}`; **70** of the 71 return all three, and the one
that returns `{propext, Quot.sound}` alone is `baseChange_baseChange''` — ⚠️ **the same
declaration, by the same argument, as the one `HalvingGaloisTower` singles out of its own 42.**

**Three direct imports** — `HalvingExtension`, `ThreeDivisionField`, `TriplingSeparable` — and an
import closure of **57** modules with this one excluded.  ⚠️ **Two files this module names are
reached transitively and cost no edge**: `EllipticCurves.Torsion.TriplingSurjective`, which
supplies `Φ_three_eval`, `ΨSq_three_eval`, `preΨ₄_eval`, `hasXCoordFormula_three`,
`eval_Φ_three_ne_zero_of_root_ΨSq` and `exists_nsmul_three_eq_some_of_root`, and
`EllipticCurves.Fixtures`, which supplies the certificate curve — both already inside
`TriplingSeparable`'s closure, which is **53** on its own.

The declarations, by layer:

* the polynomial: `triplingX` with `natDegree_triplingX` (`= 9`), `degree_triplingX`,
  `triplingX_ne_zero`, `eval_triplingX`, `map_triplingX` and `separable_triplingX`;
* the two root facts: `Ψ₃_eval_ne_zero_of_root_triplingX` and
  `Ψ₂Sq_eval_ne_zero_of_root_triplingX`;
* the first floor over a general base: `triplingXField`, `triplingXRoot`, `eval_triplingXRoot`,
  `isGalois_triplingXField`, `finiteDimensional_triplingXField`,
  `Ψ₂Sq_eval_triplingXRoot_ne_zero`;
* the second floor over a general base: `triplingYPoly`, `triplingField`, `triplingYRoot`,
  `eval_triplingYRoot`, `isGalois_triplingField`, `isSeparable_triplingField`,
  `finiteDimensional_triplingField`, and `exists_nsmul_three_eq_triplingField`;
* the three floors of the tower proper: `triplingTower`, `triplingGaloisField` and the instance
  `instIsScalarTowerTriplingTower` that makes `F ⊆ L₁ ⊆ M` a tower, with the two roots
  `triplingTowerXRoot`, `triplingTowerYRoot` and their equations `eval_triplingTowerXRoot`,
  `eval_triplingTowerYRoot`;
* `isSeparable_triplingTower`, `finiteDimensional_triplingTower`: `M / F` is finite separable;
* `isGalois_triplingGaloisField`, `finiteDimensional_triplingGaloisField`: `N / F` is finite
  Galois;
* `threeDivisionFieldToGalois`, `card_torsion_three_triplingGaloisField` and
  `nonempty_torsionThree_addEquiv_triplingGaloisField`: `#E[3] = 9` and
  `E[3] ≃+ ZMod 3 × ZMod 3` over `N`;
* `exists_nsmul_three_eq_of_roots_baseChange` and `exists_nsmul_three_eq_triplingGaloisField`:
  `S` is `3`-divisible over any extension reached from a field carrying both roots, and over `N`;
* `exists_root_triplingX_of_nsmul_three_eq`: the converse, below.

## ⚠️ Two things are transported to `N`, and NEITHER of them is a point or a cardinal

As at `n = 2`.  `Ψ₃` splits over `L₁` and the `Ψ₂Sq` values at its roots are squares there;
`threeDivisionFieldToGalois` is an `F`-algebra hom `L₁ →ₐ[F] N`, and
`card_torsion_three_of_algHom` (`EllipticCurves.Torsion.ThreeDivisionField`) carries both
conditions along it.  **No counting and no injection.**  The tripling is transported the same way:
what crosses is the pair of *root equations*, and
`exists_nsmul_three_eq_some_of_root` is re-applied over the top field.

⚠️ **The reason both are done at the level of a `Prop`** is that `((W⁄L₁)⁄L) = (W⁄L)` is
`WeierstrassCurve.map_baseChange` and is **not** `rfl`, so a `Point`-level route would have to
transport a term along a propositional equation between two `Affine L`, while a statement about
`Polynomial.eval` is rewritten by it in one step.  That equation is paid exactly twice below, in
`eval_triplingTowerXRoot` and `eval_triplingTowerYRoot`.

## The converse, and what it is for

`exists_root_triplingX_of_nsmul_three_eq` says that if `S` is *already* three times a point of `W`
over `F`, then `triplingX x₀` already has a root in `F`.  ⚠️ **It is not the converse of
`exists_nsmul_three_eq_of_roots_baseChange`** — that one needs a root *and* a point above it, and
this one returns only the root.  Its two branches are the two ways the hypothesis can be satisfied
without the coordinate formula applying: `P = O`, which `3 • O = O ≠ S` kills, and `Ψ₃(r) = 0`,
where `nsmul_eq_zero_iff_eval_preΨ_eq_zero` (`EllipticCurves.Torsion.OddTorsionCount`) makes
`3 • P = O ≠ S`.  It is what makes the `Nonvacuity` section below a statement about the *tower*
and not only about a polynomial.

## What is *not* here

* **A discharge of `hprin`, and nothing about divisors.**  `#962` records that gate and this file
  supplies the `n = 3` analogue of the two rows `HalvingGaloisTower` supplies at `n = 2`.  No
  statement below mentions a divisor, a place, a function field or Hilbert 90, and none of those
  modules is in this module's import closure.
* **The assembly.**  `PullbackPrincipalityThreeGeneral` is `#2216`'s item 4 and is not here; this
  file is item 2 and says so.
* **A degree, or a Galois group.**  `[N : F]` is not computed and `Gal(N/F)` is not identified
  with a subgroup of `GL₂(𝔽₃)` or of anything else.  ⚠️ `N` is *some* finite Galois extension with
  the two properties and nothing below says it is the smallest one.  In particular nothing below
  says `N ⊋ F`, as a statement about types; see `## Non-vacuity`.
* **`ΨSq₃` over the middle floor.**  Nothing below says `Ψ₃` splits over `M`; it says `#E[3] = 9`
  over `N`, and only because `L₁ ⊆ N`.
* **A `Point`-level base-change API.**  `Point.map` is not used below.
* **Characteristic `2` or `3`.**  Every statement that uses the tripling polynomial's separability
  carries both `(2 : F) ≠ 0` and `(3 : F) ≠ 0`, inherited from `TriplingSeparable`.
* **An index other than `3`.**  `TriplingSeparable`'s `separable_Φ_sub_C_mul_ΨSq_of_odd` is
  general in the odd index, so the middle floor of this tower generalises; ⚠️ **the counting floor
  does not**, `threeDivisionField` and `card_torsion_three_of_algHom` being `n = 3` objects, and a
  general-`n` tower would have to replace `L₁` first.  Nothing below is stated at a general `n`.

## The two `private` one-liners, and why they are copies

`algebraMap_ofNat_ne_zero'` and `baseChange_baseChange''` are restatements.  The general-numeral
form is `private` in `EllipticCurves.Torsion.ThreeDivisionField` and the base-change identity is
`private` in `EllipticCurves.Torsion.HalvingExtension` — both of which this file imports, so
promoting either would remove a copy.  ⚠️ **It would also re-key a published figure in a file this
round does not own**: `HalvingExtension`'s docstring publishes **36** public declarations and
`HalvingGaloisTower`'s publishes **17** public over **42** constants with **16** `private`, all
three of which reproduce at this head under the rule stated above.  Promoting a `private` lemma
moves them, so it is left as a separate change rather than folded in here.

## Non-vacuity

The `Nonvacuity` section runs on the shared `EllipticCurves.Fixture.y2AddYEqX3` at `R = ℚ` —
`y² + y = x³`, whose `Ψ₃ = 3X⁴ + 3X` has the rational root `0`, so `(0, 0)` is a rational
`3`-torsion point and `x₀ = 0` is the index this file's hypotheses want.

⚠️ **The tripling half is certified INFORMATIVE here and not merely inhabited**, which is the half
`HalvingGaloisTower`'s own `Nonvacuity` section records that it could *not* certify at `n = 2` on
its fixture.  The tripling polynomial is

```
triplingX 0 = Φ₃ = X⁹ − 24X⁶ + 3X³ + 1        on  y² + y = x³,
```

read off `Φ₃ = X·Ψ₃² − preΨ₄·Ψ₂Sq` at `b₂ = b₄ = b₈ = 0`, `b₆ = 1`, and it has **no rational
root**: it is monic over `ℤ`, so `IsIntegrallyClosed.isIntegral_iff` puts any rational root in `ℤ`,
where it divides the constant coefficient `1` and is therefore `±1`, and the two values are `−19`
and `−27`.  With the converse above that gives `not_exists_nsmul_three_eq_y2AddYEqX3`: **no
rational point of `y² + y = x³` triples to `(0, 0)`**, while
`exists_nsmul_three_eq_triplingGaloisField_y2AddYEqX3` produces one over `N`.

⚠️ **What that pair certifies is the CONCLUSION and not the type.**  No clause here says `ℚ ⊊ N`;
descending a point along a surjective `algebraMap` is a different argument and is not made.  What
is shown is that the statement this file delivers over `N` is **false over `ℚ`** on this curve, so
the tower is not decoration.

⚠️ **The count half is inhabited and NOT certified informative, and that is stated rather than
papered over.**  `card_torsion_three_triplingGaloisField_y2AddYEqX3` gives `#E[3] = 9` over `N`;
this file does **not** show `#E[3] ≠ 9` over `ℚ` for this curve, because the tree has no route
from *`Ψ₃` does not split* to an upper bound on the count — `card_torsion_three_of_splits`
(`EllipticCurves.Torsion.ThreeTorsionStructure`) is stated in one direction only.  So the
pair-of-counts argument `HalvingGaloisTower` uses for its properness figure is **not** reproduced
here, and the informativeness figure above is a different one about a different half.
-/

open Polynomial IntermediateField

namespace WeierstrassCurve.Affine

variable {F : Type*} [Field F] {W : Affine F}

/-! ## The tripling polynomial -/

variable (W) in
/-- The tripling polynomial of `x₀`. -/
noncomputable def triplingX (x₀ : F) : F[X] := W.Φ 3 - C x₀ * W.ΨSq 3

theorem natDegree_triplingX (x₀ : F) : (W.triplingX x₀).natDegree = 9 := by
  have h := natDegree_Φ_sub_C_mul_ΨSq (W := W) (n := 3) (by norm_num) x₀
  simpa [triplingX] using h

theorem triplingX_ne_zero (x₀ : F) : W.triplingX x₀ ≠ 0 := by
  intro h
  have h9 := natDegree_triplingX (W := W) x₀
  rw [h, natDegree_zero] at h9
  exact absurd h9 (by norm_num)

theorem degree_triplingX (x₀ : F) : (W.triplingX x₀).degree = 9 := by
  rw [degree_eq_natDegree (triplingX_ne_zero x₀), natDegree_triplingX]
  rfl

theorem eval_triplingX (x₀ x : F) :
    (W.triplingX x₀).eval x = (W.Φ 3).eval x - x₀ * W.Ψ₃.eval x ^ 2 := by
  rw [triplingX, eval_sub, eval_mul, eval_C, ΨSq_three_eval]

theorem separable_triplingX [W.IsElliptic] (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) {x₀ : F}
    (hx₀ : W.Ψ₃.eval x₀ = 0) : (W.triplingX x₀).Separable :=
  separable_Φ_three_sub_C_mul_ΨSq h2 h3 hx₀

theorem map_triplingX {K : Type*} [Field K] (f : F →+* K) (x₀ : F) :
    (W.map f).triplingX (f x₀) = (W.triplingX x₀).map f := by
  simp [triplingX, Polynomial.map_sub, Polynomial.map_mul]

/-! ## A root of the tripling polynomial is neither `3`-torsion nor `2`-torsion -/

theorem Ψ₃_eval_ne_zero_of_root_triplingX [W.IsElliptic] {x₀ r : F}
    (hr : (W.triplingX x₀).eval r = 0) : W.Ψ₃.eval r ≠ 0 := by
  intro hT
  refine eval_Φ_three_ne_zero_of_root_ΨSq r (by rw [ΨSq_three_eval, hT]; ring) ?_
  rw [eval_triplingX, hT] at hr
  linear_combination hr

theorem Ψ₂Sq_eval_ne_zero_of_root_triplingX [W.IsElliptic] {x₀ : F} (hx₀ : W.Ψ₃.eval x₀ = 0)
    {r : F} (hr : (W.triplingX x₀).eval r = 0) : W.Ψ₂Sq.eval r ≠ 0 := by
  intro hp
  have hT : W.Ψ₃.eval r ≠ 0 := Ψ₃_eval_ne_zero_of_root_triplingX hr
  rw [eval_triplingX] at hr
  have hsplit : (r - x₀) * W.Ψ₃.eval r ^ 2 = 0 := by
    rw [Φ_three_eval, hp] at hr
    linear_combination hr
  rcases mul_eq_zero.mp hsplit with h1 | h2
  · exact hT (sub_eq_zero.mp h1 ▸ hx₀)
  · exact hT (pow_eq_zero_iff two_ne_zero |>.mp h2)

/-! ## Base change of the two root hypotheses -/

private lemma algebraMap_ofNat_ne_zero' {L : Type*} [Field L] [Algebra F L] (n : ℕ)
    [n.AtLeastTwo] (h : (OfNat.ofNat n : F) ≠ 0) : (OfNat.ofNat n : L) ≠ 0 := by
  rw [← map_ofNat (algebraMap F L) n, ne_eq, map_eq_zero]
  exact h

theorem eval_Ψ₃_baseChange {L : Type*} [Field L] [Algebra F L] {x₀ : F}
    (hx₀ : W.Ψ₃.eval x₀ = 0) : (W⁄L).Ψ₃.eval (algebraMap F L x₀) = 0 := by
  rw [show (W⁄L) = W.map (algebraMap F L) from rfl, WeierstrassCurve.map_Ψ₃, eval_map,
    ← Polynomial.aeval_def, Polynomial.aeval_algebraMap_apply]
  simp [hx₀]

/-! ## The first floor: adjoining the tripling `x`-coordinate -/

/-- A splitting field of the tripling polynomial. -/
noncomputable abbrev triplingXField (W : Affine F) (x₀ : F) : Type _ :=
  (W.triplingX x₀).SplittingField

/-- A root of the tripling polynomial in its splitting field. -/
noncomputable def triplingXRoot (W : Affine F) (x₀ : F) : W.triplingXField x₀ :=
  rootOfSplits (IsSplittingField.splits (W.triplingXField x₀) (W.triplingX x₀))
    (by rw [Polynomial.degree_map, degree_triplingX]; norm_num)

theorem eval_triplingXRoot {W : Affine F} (x₀ : F) :
    ((W⁄(W.triplingXField x₀)).triplingX (algebraMap F (W.triplingXField x₀) x₀)).eval
      (W.triplingXRoot x₀) = 0 := by
  rw [show (W⁄(W.triplingXField x₀)) = W.map (algebraMap F (W.triplingXField x₀)) from rfl,
    map_triplingX]
  exact eval_rootOfSplits _ _

section Tower

variable {W : Affine F} {x₀ : F}

theorem isGalois_triplingXField [W.IsElliptic] (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0)
    (hx₀ : W.Ψ₃.eval x₀ = 0) : IsGalois F (W.triplingXField x₀) :=
  IsGalois.of_separable_splitting_field (p := W.triplingX x₀) (separable_triplingX h2 h3 hx₀)

theorem finiteDimensional_triplingXField : FiniteDimensional F (W.triplingXField x₀) :=
  IsSplittingField.finiteDimensional _ (W.triplingX x₀)

theorem Ψ₂Sq_eval_triplingXRoot_ne_zero [W.IsElliptic] (hx₀ : W.Ψ₃.eval x₀ = 0) :
    (W⁄(W.triplingXField x₀)).Ψ₂Sq.eval (W.triplingXRoot x₀) ≠ 0 := by
  haveI : (W⁄(W.triplingXField x₀)).IsElliptic :=
    inferInstanceAs (W.map (algebraMap F (W.triplingXField x₀))).IsElliptic
  exact Ψ₂Sq_eval_ne_zero_of_root_triplingX (eval_Ψ₃_baseChange hx₀) (eval_triplingXRoot x₀)

end Tower

/-! ## The second floor: adjoining the `y`-coordinate above it -/

/-- The `y`-quadratic above the chosen tripling `x`-coordinate, over the first floor. -/
noncomputable def triplingYPoly (W : Affine F) (x₀ : F) : (W.triplingXField x₀)[X] :=
  (W⁄(W.triplingXField x₀)).halvingY (W.triplingXRoot x₀)

/-- **The tripling field** of the `3`-torsion point at `x₀`. -/
noncomputable abbrev triplingField (W : Affine F) (x₀ : F) : Type _ :=
  (W.triplingYPoly x₀).SplittingField

/-- A root of the `y`-quadratic in the tripling field. -/
noncomputable def triplingYRoot (W : Affine F) (x₀ : F) : W.triplingField x₀ :=
  rootOfSplits (IsSplittingField.splits (W.triplingField x₀) (W.triplingYPoly x₀))
    (by rw [Polynomial.degree_map, triplingYPoly, degree_halvingY]; exact two_ne_zero)

theorem eval_triplingYRoot (W : Affine F) (x₀ : F) :
    ((W.triplingYPoly x₀).map
      (algebraMap (W.triplingXField x₀) (W.triplingField x₀))).eval (W.triplingYRoot x₀) = 0 :=
  eval_rootOfSplits _ _

section Separability

variable {W : Affine F} {x₀ : F}

theorem isGalois_triplingField [W.IsElliptic] (hx₀ : W.Ψ₃.eval x₀ = 0) :
    IsGalois (W.triplingXField x₀) (W.triplingField x₀) :=
  IsGalois.of_separable_splitting_field (p := W.triplingYPoly x₀)
    (separable_halvingY (Ψ₂Sq_eval_triplingXRoot_ne_zero hx₀))

theorem isSeparable_triplingField [W.IsElliptic] (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0)
    (hx₀ : W.Ψ₃.eval x₀ = 0) : Algebra.IsSeparable F (W.triplingField x₀) := by
  haveI := isGalois_triplingXField h2 h3 hx₀
  haveI := isGalois_triplingField (W := W) hx₀
  exact Algebra.IsSeparable.trans F (W.triplingXField x₀) (W.triplingField x₀)

theorem finiteDimensional_triplingField : FiniteDimensional F (W.triplingField x₀) := by
  haveI : FiniteDimensional F (W.triplingXField x₀) := finiteDimensional_triplingXField
  haveI : FiniteDimensional (W.triplingXField x₀) (W.triplingField x₀) :=
    IsSplittingField.finiteDimensional _ (W.triplingYPoly x₀)
  exact FiniteDimensional.trans F (W.triplingXField x₀) (W.triplingField x₀)

end Separability

/-! ## The tripling, over the tripling field -/

section Tripling

variable {W : Affine F} {x₀ : F}

private lemma baseChange_baseChange'' (W : Affine F) (L₁ : Type*) [Field L₁] [Algebra F L₁]
    (L : Type*) [Field L] [Algebra F L] [Algebra L₁ L] [IsScalarTower F L₁ L] :
    ((W⁄L₁)⁄L) = (W⁄L) :=
  WeierstrassCurve.map_baseChange (R := F) W (IsScalarTower.toAlgHom F L₁ L)

section Bridge

variable {L₁ L : Type*} [Field L₁] [Field L] [Algebra F L₁] [Algebra F L] [Algebra L₁ L]
  [IsScalarTower F L₁ L]

/-- A root of the tripling polynomial over `L₁` is one over any extension of `L₁`. -/
theorem eval_triplingX_baseChange {r : L₁}
    (hr : ((W⁄L₁).triplingX (algebraMap F L₁ x₀)).eval r = 0) :
    ((W⁄L).triplingX (algebraMap F L x₀)).eval (algebraMap L₁ L r) = 0 := by
  rw [← baseChange_baseChange'' W L₁ L,
    show ((W⁄L₁)⁄L) = (W⁄L₁).map (algebraMap L₁ L) from rfl,
    IsScalarTower.algebraMap_apply F L₁ L x₀, map_triplingX, eval_map, ← Polynomial.aeval_def,
    Polynomial.aeval_algebraMap_apply, Polynomial.aeval_def, ← eval_map, ← map_triplingX]
  simp [Algebra.algebraMap_self, hr]

end Bridge

/-- **A `3`-torsion point is three times another point over its tripling field.** -/
theorem exists_nsmul_three_eq_triplingField [DecidableEq (W.triplingField x₀)] [W.IsElliptic]
    (h2 : (2 : F) ≠ 0) {y₀ : F} (hQ : W.Nonsingular x₀ y₀) :
    ∃ P : (W⁄(W.triplingField x₀)).Point,
      (3 : ℕ) • P = Point.some (algebraMap F (W.triplingField x₀) x₀)
        (algebraMap F (W.triplingField x₀) y₀)
        ((W.map_nonsingular (algebraMap F (W.triplingField x₀)).injective x₀ y₀).mpr hQ) := by
  haveI : (W⁄(W.triplingField x₀)).IsElliptic :=
    inferInstanceAs (W.map (algebraMap F (W.triplingField x₀))).IsElliptic
  have hr : ((W⁄(W.triplingField x₀)).triplingX
      (algebraMap F (W.triplingField x₀) x₀)).eval
      (algebraMap (W.triplingXField x₀) (W.triplingField x₀) (W.triplingXRoot x₀)) = 0 :=
    eval_triplingX_baseChange (eval_triplingXRoot x₀)
  have hy : ((W⁄(W.triplingField x₀)).halvingY
      (algebraMap (W.triplingXField x₀) (W.triplingField x₀) (W.triplingXRoot x₀))).eval
      (W.triplingYRoot x₀) = 0 :=
    eval_halvingY_baseChange (eval_triplingYRoot W x₀)
  refine exists_nsmul_three_eq_some_of_root (algebraMap_ofNat_ne_zero' 2 h2) _
    (equation_of_eval_halvingY_eq_zero hy) ?_
  rw [eval_triplingX] at hr
  linear_combination hr

end Tripling

/-! ## The three-floor tower -/

variable (W) in
/-- **The second floor `M`**: the tripling field of `x₀`, taken over the `3`-division field. -/
noncomputable abbrev triplingTower (x₀ : F) : Type _ :=
  (W⁄(threeDivisionField W)).triplingField (algebraMap F (threeDivisionField W) x₀)

/-- `F ⊆ L₁ ⊆ M` is a tower. -/
instance instIsScalarTowerTriplingTower (x₀ : F) :
    IsScalarTower F (threeDivisionField W) (W.triplingTower x₀) := by
  refine IsScalarTower.of_algebraMap_eq fun a => ?_
  rw [IsScalarTower.algebraMap_apply F
      ((W⁄(threeDivisionField W)).triplingXField (algebraMap F (threeDivisionField W) x₀))
      (W.triplingTower x₀),
    IsScalarTower.algebraMap_apply F (threeDivisionField W)
      ((W⁄(threeDivisionField W)).triplingXField (algebraMap F (threeDivisionField W) x₀)),
    ← IsScalarTower.algebraMap_apply (threeDivisionField W)
      ((W⁄(threeDivisionField W)).triplingXField (algebraMap F (threeDivisionField W) x₀))
      (W.triplingTower x₀)]

/-- The tripling `x`-coordinate, as an element of the second floor `M`. -/
noncomputable def triplingTowerXRoot (W : Affine F) (x₀ : F) : W.triplingTower x₀ :=
  algebraMap ((W⁄(threeDivisionField W)).triplingXField (algebraMap F (threeDivisionField W) x₀))
    (W.triplingTower x₀)
    ((W⁄(threeDivisionField W)).triplingXRoot (algebraMap F (threeDivisionField W) x₀))

/-- The `y`-coordinate above it, which is where the second floor is adjoined. -/
noncomputable def triplingTowerYRoot (W : Affine F) (x₀ : F) : W.triplingTower x₀ :=
  (W⁄(threeDivisionField W)).triplingYRoot (algebraMap F (threeDivisionField W) x₀)

/-- **The tripling polynomial of `x₀` has a root over `M`**, stated over `(W⁄M)`. -/
theorem eval_triplingTowerXRoot (x₀ : F) :
    ((W⁄(W.triplingTower x₀)).triplingX (algebraMap F (W.triplingTower x₀) x₀)).eval
      (W.triplingTowerXRoot x₀) = 0 := by
  have h : (((W⁄(threeDivisionField W))⁄(W.triplingTower x₀)).triplingX
      (algebraMap (threeDivisionField W) (W.triplingTower x₀)
        (algebraMap F (threeDivisionField W) x₀))).eval (W.triplingTowerXRoot x₀) = 0 :=
    eval_triplingX_baseChange (eval_triplingXRoot _)
  rwa [baseChange_baseChange'' W (threeDivisionField W) (W.triplingTower x₀),
    ← IsScalarTower.algebraMap_apply F (threeDivisionField W) (W.triplingTower x₀) x₀] at h

/-- **The `y`-quadratic above that root has a root over `M`**, in the same form. -/
theorem eval_triplingTowerYRoot (x₀ : F) :
    ((W⁄(W.triplingTower x₀)).halvingY (W.triplingTowerXRoot x₀)).eval
      (W.triplingTowerYRoot x₀) = 0 := by
  have h : (((W⁄(threeDivisionField W))⁄(W.triplingTower x₀)).halvingY
      (W.triplingTowerXRoot x₀)).eval (W.triplingTowerYRoot x₀) = 0 :=
    eval_halvingY_baseChange (eval_triplingYRoot _ _)
  rwa [baseChange_baseChange'' W (threeDivisionField W) (W.triplingTower x₀)] at h

/-! ## The second floor is finite and separable over `F` -/

variable [W.IsElliptic]

/-- **`M / F` is separable.** -/
theorem isSeparable_triplingTower (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) {x₀ : F}
    (hx₀ : W.Ψ₃.eval x₀ = 0) : Algebra.IsSeparable F (W.triplingTower x₀) := by
  haveI : (W⁄(threeDivisionField W)).IsElliptic :=
    inferInstanceAs (W.map (algebraMap F (threeDivisionField W))).IsElliptic
  haveI := isSeparable_threeDivisionField W h2 h3
  haveI : Algebra.IsSeparable (threeDivisionField W) (W.triplingTower x₀) :=
    isSeparable_triplingField (algebraMap_ofNat_ne_zero' 2 h2) (algebraMap_ofNat_ne_zero' 3 h3)
      (eval_Ψ₃_baseChange hx₀)
  exact Algebra.IsSeparable.trans F (threeDivisionField W) (W.triplingTower x₀)

omit [W.IsElliptic] in
/-- **`M / F` is finite**, each floor being a splitting field of a polynomial. -/
theorem finiteDimensional_triplingTower {x₀ : F} : FiniteDimensional F (W.triplingTower x₀) := by
  haveI : FiniteDimensional F (threeDivisionField W) := finiteDimensional_threeDivisionField W
  haveI : FiniteDimensional (threeDivisionField W) (W.triplingTower x₀) :=
    finiteDimensional_triplingField
  exact FiniteDimensional.trans F (threeDivisionField W) (W.triplingTower x₀)

/-! ## The third floor: the Galois closure -/

variable (W) in
/-- **The third floor `N`**: the Galois closure of the tower over `F`. -/
noncomputable abbrev triplingGaloisField (x₀ : F) : Type _ :=
  normalClosure F (W.triplingTower x₀) (AlgebraicClosure (W.triplingTower x₀))

/-- **`N / F` is Galois.** -/
theorem isGalois_triplingGaloisField (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) {x₀ : F}
    (hx₀ : W.Ψ₃.eval x₀ = 0) : IsGalois F (W.triplingGaloisField x₀) := by
  haveI := isSeparable_triplingTower h2 h3 hx₀
  exact _root_.isGalois_normalClosure_of_isSeparable F (W.triplingTower x₀)

omit [W.IsElliptic] in
/-- **`N / F` is finite.** -/
theorem finiteDimensional_triplingGaloisField {x₀ : F} :
    FiniteDimensional F (W.triplingGaloisField x₀) := by
  haveI : FiniteDimensional F (W.triplingTower x₀) := finiteDimensional_triplingTower
  infer_instance

/-! ## `#E[3] = 9` over the third floor -/

variable (W) in
/-- The composite `F`-algebra hom `L₁ → N`. -/
noncomputable def threeDivisionFieldToGalois (x₀ : F) :
    threeDivisionField W →ₐ[F] W.triplingGaloisField x₀ :=
  (IsScalarTower.toAlgHom F (W.triplingTower x₀) (W.triplingGaloisField x₀)).comp
    (IsScalarTower.toAlgHom F (threeDivisionField W) (W.triplingTower x₀))

/-- **`#E[3] = 9` over `N`.** -/
theorem card_torsion_three_triplingGaloisField (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) (x₀ : F)
    [DecidableEq (W.triplingGaloisField x₀)] :
    Nat.card ((W⁄(W.triplingGaloisField x₀)).torsion 3) = 9 :=
  card_torsion_three_of_algHom h2 h3 (threeDivisionFieldToGalois W x₀)
    (splits_Ψ₃_tower (W := W) W.Ψ₃.SplittingField)
    fun _ hz => isSquare_Ψ₂Sq_eval_tower (W := W) W.Ψ₃.SplittingField h3 hz

/-- **`E[3] ≃+ ZMod 3 × ZMod 3` over `N`.** -/
theorem nonempty_torsionThree_addEquiv_triplingGaloisField (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0)
    (x₀ : F) [DecidableEq (W.triplingGaloisField x₀)] :
    Nonempty ((W⁄(W.triplingGaloisField x₀)).torsion 3 ≃+ ZMod 3 × ZMod 3) :=
  nonempty_torsionThree_addEquiv_of_algHom h2 h3 (threeDivisionFieldToGalois W x₀)
    (splits_Ψ₃_tower (W := W) W.Ψ₃.SplittingField)
    fun _ hz => isSquare_Ψ₂Sq_eval_tower (W := W) W.Ψ₃.SplittingField h3 hz

/-! ## The tripling over the third floor -/

/-- **`S` is three times another point over any extension reached from a field carrying both
roots.** -/
theorem exists_nsmul_three_eq_of_roots_baseChange {M L : Type*} [Field M] [Field L] [Algebra F M]
    [Algebra F L] [Algebra M L] [IsScalarTower F M L] [DecidableEq L]
    (h2 : (2 : F) ≠ 0) {x₀ y₀ : F} (hQ : W.Nonsingular x₀ y₀)
    {r s : M} (hr : ((W⁄M).triplingX (algebraMap F M x₀)).eval r = 0)
    (hs : ((W⁄M).halvingY r).eval s = 0) :
    ∃ P : (W⁄L).Point, (3 : ℕ) • P = Point.some (algebraMap F L x₀) (algebraMap F L y₀)
      ((W.map_nonsingular (algebraMap F L).injective x₀ y₀).mpr hQ) := by
  haveI : (W⁄L).IsElliptic := inferInstanceAs (W.map (algebraMap F L)).IsElliptic
  have hrL : ((W⁄L).triplingX (algebraMap F L x₀)).eval (algebraMap M L r) = 0 :=
    eval_triplingX_baseChange hr
  have hsL : ((W⁄L).halvingY (algebraMap M L r)).eval (algebraMap M L s) = 0 := by
    refine eval_halvingY_baseChange ?_
    rw [Polynomial.eval_map, Polynomial.eval₂_at_apply, hs, map_zero]
  refine exists_nsmul_three_eq_some_of_root (algebraMap_ofNat_ne_zero' 2 h2) _
    (equation_of_eval_halvingY_eq_zero hsL) ?_
  rw [eval_triplingX] at hrL
  linear_combination hrL

/-- **`S` is three times another point over `N`.** -/
theorem exists_nsmul_three_eq_triplingGaloisField (h2 : (2 : F) ≠ 0) {x₀ y₀ : F}
    (hQ : W.Nonsingular x₀ y₀) [DecidableEq (W.triplingGaloisField x₀)] :
    ∃ P : (W⁄(W.triplingGaloisField x₀)).Point,
      (3 : ℕ) • P = Point.some (algebraMap F (W.triplingGaloisField x₀) x₀)
        (algebraMap F (W.triplingGaloisField x₀) y₀)
        ((W.map_nonsingular (algebraMap F (W.triplingGaloisField x₀)).injective x₀ y₀).mpr hQ) :=
  exists_nsmul_three_eq_of_roots_baseChange h2 hQ (eval_triplingTowerXRoot x₀)
    (eval_triplingTowerYRoot x₀)

/-! ## The converse: when the tower buys nothing -/

section Converse

variable {W : Affine F}

/-- **If `S` is already three times a point of `W` over `F`, the tripling polynomial already has a
root over `F`.** -/
theorem exists_root_triplingX_of_nsmul_three_eq [DecidableEq F] [W.IsElliptic] (h2 : (2 : F) ≠ 0)
    {x₀ y₀ : F} (hQ : W.Nonsingular x₀ y₀) {P : W.Point}
    (hP : (3 : ℕ) • P = Point.some x₀ y₀ hQ) : ∃ r : F, (W.triplingX x₀).eval r = 0 := by
  match P with
  | .zero =>
    rw [show (Point.zero : W.Point) = 0 from rfl, smul_zero] at hP
    exact absurd hP (by simp)
  | .some r s h =>
    by_cases hΨ : W.Ψ₃.eval r = 0
    · have hzero : (3 : ℕ) • Point.some r s h = 0 :=
        (nsmul_eq_zero_iff_eval_preΨ_eq_zero h2 (by decide) h).mpr
          (by rw [show ((3 : ℕ) : ℤ) = (3 : ℤ) by norm_num, preΨ_three]; exact hΨ)
      rw [hzero] at hP
      simp at hP
    · have hΨSq : (W.ΨSq (3 : ℕ)).eval r ≠ 0 := by
        rw [show ((3 : ℕ) : ℤ) = (3 : ℤ) by norm_num, ΨSq_three_eval]
        exact pow_ne_zero 2 hΨ
      obtain ⟨y', h', hform⟩ := hasXCoordFormula_three h2 h hΨSq
      rw [hform, Point.some.injEq] at hP
      refine ⟨r, ?_⟩
      rw [eval_triplingX, ← hP.1, show ((3 : ℕ) : ℤ) = (3 : ℤ) by norm_num, ΨSq_three_eval]
      field_simp
      ring

end Converse

/-! ## Non-vacuity -/

section Nonvacuity

open EllipticCurves.Fixture

/-- **`(0, 0)` lies on `y² + y = x³`.** -/
private lemma nonsingular_zero_y2AddYEqX3 : (y2AddYEqX3 ℚ).Nonsingular 0 0 := by
  refine equation_iff_nonsingular.mp ?_
  rw [Affine.equation_iff]; norm_num [y2AddYEqX3]

/-- **`0` is a root of `Ψ₃` on `y² + y = x³`**, so `(0, 0)` is a `3`-torsion point. -/
private lemma eval_Ψ₃_zero_y2AddYEqX3' : (y2AddYEqX3 ℚ).Ψ₃.eval 0 = 0 := by
  simp only [WeierstrassCurve.Ψ₃, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆,
    WeierstrassCurve.b₈, y2AddYEqX3]
  norm_num

private noncomputable instance :
    DecidableEq ((y2AddYEqX3 ℚ).triplingGaloisField 0) := Classical.decEq _

/-- **`N / ℚ` is finite Galois** on the fixture. -/
private theorem isGalois_triplingGaloisField_y2AddYEqX3 :
    IsGalois ℚ ((y2AddYEqX3 ℚ).triplingGaloisField 0) :=
  isGalois_triplingGaloisField (by norm_num) (by norm_num) eval_Ψ₃_zero_y2AddYEqX3'

private theorem finiteDimensional_triplingGaloisField_y2AddYEqX3 :
    FiniteDimensional ℚ ((y2AddYEqX3 ℚ).triplingGaloisField 0) :=
  finiteDimensional_triplingGaloisField

/-- **`#E[3] = 9` over `N`** on the fixture. -/
private theorem card_torsion_three_triplingGaloisField_y2AddYEqX3 :
    Nat.card (((y2AddYEqX3 ℚ)⁄((y2AddYEqX3 ℚ).triplingGaloisField 0)).torsion 3) = 9 :=
  card_torsion_three_triplingGaloisField (by norm_num) (by norm_num) 0

/-- **`(0, 0)` is three times a point of the curve over `N`** on the fixture. -/
private theorem exists_nsmul_three_eq_triplingGaloisField_y2AddYEqX3 :
    ∃ P : ((y2AddYEqX3 ℚ)⁄((y2AddYEqX3 ℚ).triplingGaloisField 0)).Point,
      (3 : ℕ) • P = Point.some (algebraMap ℚ ((y2AddYEqX3 ℚ).triplingGaloisField 0) 0)
        (algebraMap ℚ ((y2AddYEqX3 ℚ).triplingGaloisField 0) 0)
        (((y2AddYEqX3 ℚ).map_nonsingular
          (algebraMap ℚ ((y2AddYEqX3 ℚ).triplingGaloisField 0)).injective 0 0).mpr
          nonsingular_zero_y2AddYEqX3) :=
  exists_nsmul_three_eq_triplingGaloisField (by norm_num) nonsingular_zero_y2AddYEqX3

/-- **The tripling polynomial of `(0, 0)` on `y² + y = x³` is `X⁹ − 24X⁶ + 3X³ + 1`.** -/
private lemma eval_triplingX_zero_y2AddYEqX3 (x : ℚ) :
    ((y2AddYEqX3 ℚ).triplingX 0).eval x = x ^ 9 - 24 * x ^ 6 + 3 * x ^ 3 + 1 := by
  rw [eval_triplingX, Φ_three_eval]
  simp only [preΨ₄_eval, WeierstrassCurve.Ψ₃, WeierstrassCurve.Ψ₂Sq, WeierstrassCurve.b₂,
    WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈, y2AddYEqX3]
  simp only [eval_add, eval_mul, eval_pow, eval_X, eval_C, eval_ofNat]
  ring

/-- **The tripling polynomial of `(0, 0)` on `y² + y = x³` has no rational root.** -/
private theorem eval_triplingX_zero_y2AddYEqX3_ne_zero (x : ℚ) :
    ((y2AddYEqX3 ℚ).triplingX 0).eval x ≠ 0 := by
  rw [eval_triplingX_zero_y2AddYEqX3]
  intro h
  have hmonic : (X ^ 9 - 24 * X ^ 6 + 3 * X ^ 3 + 1 : ℤ[X]).Monic := by monicity!
  have hint : IsIntegral ℤ x := by
    refine ⟨X ^ 9 - 24 * X ^ 6 + 3 * X ^ 3 + 1, hmonic, ?_⟩
    simp only [eval₂_add, eval₂_sub, eval₂_mul, eval₂_pow, eval₂_X, eval₂_ofNat, eval₂_one]
    linear_combination h
  obtain ⟨d, hd⟩ := IsIntegrallyClosed.isIntegral_iff.mp hint
  subst hd
  have hdz : d ^ 9 - 24 * d ^ 6 + 3 * d ^ 3 + 1 = 0 := by
    exact_mod_cast (by simpa using h : (d : ℚ) ^ 9 - 24 * (d : ℚ) ^ 6 + 3 * (d : ℚ) ^ 3 + 1 = 0)
  have hdvd : d ∣ 1 := ⟨-(d ^ 8 - 24 * d ^ 5 + 3 * d ^ 2), by linarith [hdz]⟩
  rcases Int.isUnit_iff.mp (isUnit_of_dvd_one hdvd) with rfl | rfl <;> norm_num at hdz

/-- **No rational point of `y² + y = x³` triples to `(0, 0)`.** -/
private theorem not_exists_nsmul_three_eq_y2AddYEqX3 :
    ¬ ∃ P : (y2AddYEqX3 ℚ).Point,
      (3 : ℕ) • P = Point.some 0 0 nonsingular_zero_y2AddYEqX3 := by
  rintro ⟨P, hP⟩
  obtain ⟨r, hr⟩ := exists_root_triplingX_of_nsmul_three_eq (by norm_num)
    nonsingular_zero_y2AddYEqX3 hP
  exact eval_triplingX_zero_y2AddYEqX3_ne_zero r hr

end Nonvacuity

end WeierstrassCurve.Affine
