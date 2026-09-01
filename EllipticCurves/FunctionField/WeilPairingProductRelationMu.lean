/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import EllipticCurves.Fixtures
import EllipticCurves.FunctionField.WeilPairingAntisymmetricMu
import EllipticCurves.FunctionField.WeilPairingProductRelation

/-!
# Antisymmetry of the Weil pairing in `μ_n(F)`, unconditionally over `F̄` (rung 6)

`EllipticCurves.FunctionField.WeilPairingProductRelation` (`#845`) proves antisymmetry

```
e_n(S, T) · e_n(T, S) = 1,     e_n(S, T) = (e_n(T, S))⁻¹
```

over an algebraically closed field with **no hypothesis beyond the setting**, at `n = 2` and at
`n = 3` — but as equations in the function field `F(W)`.  The honest value group of the Weil
pairing is `μ_n(F) = rootsOfUnity n F ≤ Fˣ` (Silverman *AEC* III.8), where the inverse in the
second display is the *group* inverse rather than the field division of `F(W)`, and where
`WeilPairingAntisymmetricMu.weilPairingMu_mul_swap_eq_one` states the same relation — for a caller
who can supply the product relation `hprod` and the alternating property at all three of `S`, `T`
and `R = S ⊕ T`.

This file closes the loop: it instantiates the `μ_n(F)` antisymmetry statements against `#845`'s
unconditional `F(W)`-level headlines, so that over `F̄` the group-level relation too carries no
hypothesis beyond the setting.

## The route, which is cheaper than expected

`weilPairingMu h₂ hpow` is indexed by a **proof** `hpow : e_n(g, T) ^ n = 1`, so a statement about
it must bind that proof.  `#845`'s headlines return their two roots existentially, so the two
`hpow` data have to be produced inside the existential envelope and then bound by it; that is the
only reason these statements are longer than their `F(W)`-level originals.

The mathematical content is a single descent, `weilPairingMu_mul_swap_eq_one_of_weilPairingElt`:
`algebraMap_coe_rootsOfUnity_injective` (`#459`) turns any relation between `μ_n(F)` values
into the corresponding relation between their `algebraMap`-images, which are the `weilPairingElt`
values by `algebraMap_coe_weilPairingMu` (`#457`).  ⚠️ That descent needs **no** hypothesis at all
beyond the two `hpow` data and the `F(W)`-level relation — in particular it does not re-enter
`hprod`, the alternating property, or the divisor slot.  `weilPairingMu_mul_swap_eq_one` is
therefore **not** the route here: its carried inputs (`hprod`, `hwR`, `haltS`, `haltT`, `haltR`)
are internal to `#845`'s proofs and are not exposed by its existential statements.

⚠️ **The descent itself no longer lives here.**  It was written into this file because this is
where it was first wanted, but it generalises `weilPairingMu_mul_swap_eq_one` and so duplicated
that theorem's proof body across an import edge; `#868` moved it up to
`EllipticCurves.FunctionField.WeilPairingAntisymmetricMu`, next to the theorem it generalises,
which now applies it in one line.  The headlines below reach it through the import and are
otherwise unchanged.

The two `hpow` data come from the certificates the existential already carries.  If
`u • g_S ^ n = [n]∗ f_S` with `g_S ≠ 0` and `T` is `n`-torsion in the base field, then
`e_n(g_S, T) ^ n = 1` by `weilPairingElt_pow_eq_one_of_gS_two_torsion` (`TranslationTorsion`) at
`n = 2` and `weilPairingElt_pow_eq_one_of_gS_three_baseField` (`TranslationTriplingComm`) at
`n = 3`.  ⚠️ **Both slots are needed, and the second one is the new work.**  `#845` builds only
`e_n(g_S, T) ^ n = 1` — the datum the merged translation-slot bilinearity consumes.  The
symmetric `e_n(g_T, S) ^ n = 1` is what `weilPairingMu hS _` needs in order to be *formed*, and it
is the same lemma applied at `S` with `g_T`'s certificate, which the existential also carries.

## Main results

* ⚠️ the descent `weilPairingMu_mul_swap_eq_one_of_weilPairingElt` is **not** here — it is in
  `EllipticCurves.FunctionField.WeilPairingAntisymmetricMu`, next to the theorem it generalises
  (`#868`).  This file consumes it;
* `exists_weilPairingMu_mul_swap_eq_one_two` / `_three` — antisymmetry in `μ_n(F)`, product form,
  over `F̄`, with no hypothesis beyond the setting;
* `exists_weilPairingMu_eq_inv_two` / `_three` — the same in the quotable inverse form.

## Scope

`[Field F] [IsAlgClosed F] {W : Affine F} [W.IsElliptic]` for the four headlines, exactly the
setting of `#845`; the descent they consume carries neither `[IsAlgClosed F]` nor any torsion
hypothesis.  **No `#418`, no rung 4, no Ward, no normality beyond what `#845` already merged.**

Out of scope: `hprin` over a **general** field, which is open at both `n` and is what confines
these statements to `F̄`; general `n`, which wants `#404`'s `ωₙ`; bundling `e_n` as a `MonoidHom`
into `μ_n(F)` in the divisor slot, which needs a `hpow` datum uniform in the slot variable and is
a different statement (`WeilPairingDivisorSlotHom`); any change to `#845`'s or `#723`'s proofs.

⚠️ Also out of scope here, and **done elsewhere**: the headlines below inherit `#845`'s existential
envelope, so a caller who already holds a root cannot apply them.  The `∀ g` forms at both levels
are in `EllipticCurves.FunctionField.WeilPairingProductRelationRootIndependent` (`#854`), which
imports this file and instantiates the descent against them.

## Non-vacuity

Every headline is instantiated below on `#845`'s own certificate curves, and the two-curve split
is inherited from it rather than chosen here: `y² = x³ − x` over `AlgebraicClosure ℚ` has
`Ψ₃ = 3X⁴ − 6X² − 1`, whose roots are irrational, so it cannot **name** a `3`-torsion point.

⚠️ At `n = 2` the certificate is a genuine antisymmetry instance: `(0, 0)`, `(1, 0)` and `(−1, 0)`
are three **distinct** `2`-torsion points, so `S ≠ T`.  At `n = 3` the only nameable `3`-torsion
points on `y² + y = x³` are `(0, 0)` and its negative `(0, −1)`, so the certificate is taken at
`S = T = (0, 0)`, `R = (0, −1)`.  It certifies that the hypotheses are simultaneously satisfiable,
which is what a non-vacuity certificate is for, but it does **not** exhibit `S ≠ T`, so it is not
a witness that the `n = 3` statement says more than the alternating property does.  Exhibiting
`S ≠ T` at `n = 3` needs a nameable pair of independent `3`-torsion points, hence a genuine
algebraic-number argument on `Ψ₃`; that limitation is inherited from `#845` and is not addressed
here.

## References

* [J. Silverman, *The arithmetic of elliptic curves*][silverman2009], III.8.1(d) and III.8 for the
  value group `μ_n`.
-/

namespace WeierstrassCurve.Affine

variable {F : Type*} [Field F] {W : Affine F} [W.IsElliptic]

open CoordinateRing

section Two

variable [IsAlgClosed F]

open Classical in
/-- **Antisymmetry of the Weil pairing at `n = 2` in `μ_2(F)`, over an algebraically closed field
with no hypothesis beyond the setting.**

```
μ_2(S, T) · μ_2(T, S) = 1   in rootsOfUnity 2 F.
```

The `μ_n(F)`-level form of `exists_weilPairingElt_mul_swap_eq_one_two` (`#845`).  The envelope is
that theorem's, extended by the two `hpow` data: they are bound existentially because
`weilPairingMu` is indexed by the *proof*, and they are produced — not assumed — from the two
rung-5 certificates the envelope already carries, by
`weilPairingElt_pow_eq_one_of_gS_two_torsion` applied at `T` with `g_S` and at `S` with `g_T`.

⚠️ `R = S ⊕ T` is not assumed `2`-torsion here either; `#845` derives it. -/
theorem exists_weilPairingMu_mul_swap_eq_one_two (h2 : (2 : F) ≠ 0)
    {xS yS xT yT xR yR : F}
    (hS : W.Nonsingular xS yS) (hT : W.Nonsingular xT yT) (hR : W.Nonsingular xR yR)
    (hmS : Point.some xS yS hS ∈ W.torsion 2) (hmT : Point.some xT yT hT ∈ W.torsion 2)
    (hadd : Point.some xS yS hS + Point.some xT yT hT = Point.some xR yR hR) :
    ∃ gS gT : W.FunctionField, gS ≠ 0 ∧ gT ≠ 0 ∧
      (∃ f : W.FunctionField, f ≠ 0 ∧
        divisor W f = Finsupp.single (pointClosedPoint hS.left) (2 : ℤ) ∧
        ∃ u : W.CoordinateRingˣ, (u : W.CoordinateRing) • gS ^ 2 = mulByTwoEndo h2 f) ∧
      (∃ f : W.FunctionField, f ≠ 0 ∧
        divisor W f = Finsupp.single (pointClosedPoint hT.left) (2 : ℤ) ∧
        ∃ u : W.CoordinateRingˣ, (u : W.CoordinateRing) • gT ^ 2 = mulByTwoEndo h2 f) ∧
      ∃ hpowST : weilPairingElt hS.left gT ^ 2 = 1,
        ∃ hpowTS : weilPairingElt hT.left gS ^ 2 = 1,
          weilPairingMu hS.left hpowST * weilPairingMu hT.left hpowTS = 1 := by
  obtain ⟨gS, gT, hgS, hgT, ⟨fS, hfS, hdS, uS, huS⟩, ⟨fT, hfT, hdT, uT, huT⟩, hswap⟩ :=
    exists_weilPairingElt_mul_swap_eq_one_two h2 hS hT hR hmS hmT hadd
  have hpowTS : weilPairingElt hT.left gS ^ 2 = 1 :=
    weilPairingElt_pow_eq_one_of_gS_two_torsion hT.left h2
      (add_self_eq_zero_of_mem_torsion_two hmT) hgS huS
  have hpowST : weilPairingElt hS.left gT ^ 2 = 1 :=
    weilPairingElt_pow_eq_one_of_gS_two_torsion hS.left h2
      (add_self_eq_zero_of_mem_torsion_two hmS) hgT huT
  exact ⟨gS, gT, hgS, hgT, ⟨fS, hfS, hdS, uS, huS⟩, ⟨fT, hfT, hdT, uT, huT⟩, hpowST, hpowTS,
    weilPairingMu_mul_swap_eq_one_of_weilPairingElt hS.left hT.left hpowST hpowTS hswap⟩

open Classical in
/-- **Antisymmetry at `n = 2` in `μ_2(F)`, in the quotable inverse form**
`μ_2(S, T) = (μ_2(T, S))⁻¹`, over an algebraically closed field with no hypothesis beyond the
setting.

The inverse is the **group** inverse of `rootsOfUnity 2 F`, obtained by
`eq_inv_of_mul_eq_one_left` in that group — not a transport of the field division of `F(W)`, which
is what makes this the form worth quoting. -/
theorem exists_weilPairingMu_eq_inv_two (h2 : (2 : F) ≠ 0) {xS yS xT yT xR yR : F}
    (hS : W.Nonsingular xS yS) (hT : W.Nonsingular xT yT) (hR : W.Nonsingular xR yR)
    (hmS : Point.some xS yS hS ∈ W.torsion 2) (hmT : Point.some xT yT hT ∈ W.torsion 2)
    (hadd : Point.some xS yS hS + Point.some xT yT hT = Point.some xR yR hR) :
    ∃ gS gT : W.FunctionField, gS ≠ 0 ∧ gT ≠ 0 ∧
      (∃ f : W.FunctionField, f ≠ 0 ∧
        divisor W f = Finsupp.single (pointClosedPoint hS.left) (2 : ℤ) ∧
        ∃ u : W.CoordinateRingˣ, (u : W.CoordinateRing) • gS ^ 2 = mulByTwoEndo h2 f) ∧
      (∃ f : W.FunctionField, f ≠ 0 ∧
        divisor W f = Finsupp.single (pointClosedPoint hT.left) (2 : ℤ) ∧
        ∃ u : W.CoordinateRingˣ, (u : W.CoordinateRing) • gT ^ 2 = mulByTwoEndo h2 f) ∧
      ∃ hpowST : weilPairingElt hS.left gT ^ 2 = 1,
        ∃ hpowTS : weilPairingElt hT.left gS ^ 2 = 1,
          weilPairingMu hS.left hpowST = (weilPairingMu hT.left hpowTS)⁻¹ := by
  obtain ⟨gS, gT, hgS, hgT, hcS, hcT, hpowST, hpowTS, hswap⟩ :=
    exists_weilPairingMu_mul_swap_eq_one_two h2 hS hT hR hmS hmT hadd
  exact ⟨gS, gT, hgS, hgT, hcS, hcT, hpowST, hpowTS, eq_inv_of_mul_eq_one_left hswap⟩

end Two

section Three

variable [IsAlgClosed F]

open Classical in
/-- **Antisymmetry of the Weil pairing at `n = 3` in `μ_3(F)`, over an algebraically closed field
with no hypothesis beyond the setting.**

```
μ_3(S, T) · μ_3(T, S) = 1   in rootsOfUnity 3 F.
```

The `n = 3` mirror of `exists_weilPairingMu_mul_swap_eq_one_two`; only the arity of the `hpow`
producer differs, `weilPairingElt_pow_eq_one_of_gS_three_baseField` in place of
`weilPairingElt_pow_eq_one_of_gS_two_torsion`. -/
theorem exists_weilPairingMu_mul_swap_eq_one_three (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0)
    {xS yS xT yT xR yR : F}
    (hS : W.Nonsingular xS yS) (hT : W.Nonsingular xT yT) (hR : W.Nonsingular xR yR)
    (hmS : Point.some xS yS hS ∈ W.torsion 3) (hmT : Point.some xT yT hT ∈ W.torsion 3)
    (hadd : Point.some xS yS hS + Point.some xT yT hT = Point.some xR yR hR) :
    ∃ gS gT : W.FunctionField, gS ≠ 0 ∧ gT ≠ 0 ∧
      (∃ f : W.FunctionField, f ≠ 0 ∧
        divisor W f = Finsupp.single (pointClosedPoint hS.left) (3 : ℤ) ∧
        ∃ u : W.CoordinateRingˣ, (u : W.CoordinateRing) • gS ^ 3 = mulByThreeEndo h2 h3 f) ∧
      (∃ f : W.FunctionField, f ≠ 0 ∧
        divisor W f = Finsupp.single (pointClosedPoint hT.left) (3 : ℤ) ∧
        ∃ u : W.CoordinateRingˣ, (u : W.CoordinateRing) • gT ^ 3 = mulByThreeEndo h2 h3 f) ∧
      ∃ hpowST : weilPairingElt hS.left gT ^ 3 = 1,
        ∃ hpowTS : weilPairingElt hT.left gS ^ 3 = 1,
          weilPairingMu hS.left hpowST * weilPairingMu hT.left hpowTS = 1 := by
  obtain ⟨gS, gT, hgS, hgT, ⟨fS, hfS, hdS, uS, huS⟩, ⟨fT, hfT, hdT, uT, huT⟩, hswap⟩ :=
    exists_weilPairingElt_mul_swap_eq_one_three h2 h3 hS hT hR hmS hmT hadd
  have hpowTS : weilPairingElt hT.left gS ^ 3 = 1 :=
    weilPairingElt_pow_eq_one_of_gS_three_baseField hT.left h2 h3
      (add_add_self_eq_zero_of_mem_torsion_three hmT) hgS huS
  have hpowST : weilPairingElt hS.left gT ^ 3 = 1 :=
    weilPairingElt_pow_eq_one_of_gS_three_baseField hS.left h2 h3
      (add_add_self_eq_zero_of_mem_torsion_three hmS) hgT huT
  exact ⟨gS, gT, hgS, hgT, ⟨fS, hfS, hdS, uS, huS⟩, ⟨fT, hfT, hdT, uT, huT⟩, hpowST, hpowTS,
    weilPairingMu_mul_swap_eq_one_of_weilPairingElt hS.left hT.left hpowST hpowTS hswap⟩

open Classical in
/-- **Antisymmetry at `n = 3` in `μ_3(F)`, in the quotable inverse form**
`μ_3(S, T) = (μ_3(T, S))⁻¹`, over an algebraically closed field with no hypothesis beyond the
setting. -/
theorem exists_weilPairingMu_eq_inv_three (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0)
    {xS yS xT yT xR yR : F}
    (hS : W.Nonsingular xS yS) (hT : W.Nonsingular xT yT) (hR : W.Nonsingular xR yR)
    (hmS : Point.some xS yS hS ∈ W.torsion 3) (hmT : Point.some xT yT hT ∈ W.torsion 3)
    (hadd : Point.some xS yS hS + Point.some xT yT hT = Point.some xR yR hR) :
    ∃ gS gT : W.FunctionField, gS ≠ 0 ∧ gT ≠ 0 ∧
      (∃ f : W.FunctionField, f ≠ 0 ∧
        divisor W f = Finsupp.single (pointClosedPoint hS.left) (3 : ℤ) ∧
        ∃ u : W.CoordinateRingˣ, (u : W.CoordinateRing) • gS ^ 3 = mulByThreeEndo h2 h3 f) ∧
      (∃ f : W.FunctionField, f ≠ 0 ∧
        divisor W f = Finsupp.single (pointClosedPoint hT.left) (3 : ℤ) ∧
        ∃ u : W.CoordinateRingˣ, (u : W.CoordinateRing) • gT ^ 3 = mulByThreeEndo h2 h3 f) ∧
      ∃ hpowST : weilPairingElt hS.left gT ^ 3 = 1,
        ∃ hpowTS : weilPairingElt hT.left gS ^ 3 = 1,
          weilPairingMu hS.left hpowST = (weilPairingMu hT.left hpowTS)⁻¹ := by
  obtain ⟨gS, gT, hgS, hgT, hcS, hcT, hpowST, hpowTS, hswap⟩ :=
    exists_weilPairingMu_mul_swap_eq_one_three h2 h3 hS hT hR hmS hmT hadd
  exact ⟨gS, gT, hgS, hgT, hcS, hcT, hpowST, hpowTS, eq_inv_of_mul_eq_one_left hswap⟩

end Three

/-! ### Non-vacuity

The four headlines are instantiated on `#845`'s own two certificate curves, with the private
scaffolding copied because `#845`'s is not exported.  See the module docstring for what the
`n = 3` certificate does and does not certify. -/

section Nonvacuity

/-! The certificate curves `y² = x³ − x` and `y² + y = x³` are the shared
`EllipticCurves.Fixture.y2EqX3SubX` and `EllipticCurves.Fixture.y2AddYEqX3`, and the base —
algebraically closed, and of characteristic `0` so that `2 ≠ 0` and `3 ≠ 0` — is
`EllipticCurves.Fixture.AlgClosedQ`, whose single `[CharZero F]` instance also supplies
`IsElliptic` here. -/

open EllipticCurves.Fixture

private lemma exampleTwo : (2 : AlgClosedQ) ≠ 0 := two_ne_zero

private lemma exampleThree : (3 : AlgClosedQ) ≠ 0 := three_ne_zero_of_charZero _

private lemma exampleNsS : (y2EqX3SubX AlgClosedQ).Nonsingular 0 0 :=
  (y2EqX3SubX AlgClosedQ).equation_iff_nonsingular.mp (by
    norm_num [y2EqX3SubX, WeierstrassCurve.Affine.equation_iff])

private lemma exampleNsT : (y2EqX3SubX AlgClosedQ).Nonsingular 1 0 :=
  (y2EqX3SubX AlgClosedQ).equation_iff_nonsingular.mp (by
    norm_num [y2EqX3SubX, WeierstrassCurve.Affine.equation_iff])

private lemma exampleNsR : (y2EqX3SubX AlgClosedQ).Nonsingular (-1) 0 :=
  (y2EqX3SubX AlgClosedQ).equation_iff_nonsingular.mp (by
    norm_num [y2EqX3SubX, WeierstrassCurve.Affine.equation_iff])

open Classical in
private lemma exampleTorS :
    Point.some (0 : AlgClosedQ) 0 exampleNsS ∈ (y2EqX3SubX AlgClosedQ).torsion 2 :=
  (mem_torsion_two_some_iff exampleNsS).mpr (by norm_num [y2EqX3SubX])

open Classical in
private lemma exampleTorT :
    Point.some (1 : AlgClosedQ) 0 exampleNsT ∈ (y2EqX3SubX AlgClosedQ).torsion 2 :=
  (mem_torsion_two_some_iff exampleNsT).mpr (by norm_num [y2EqX3SubX])

open Classical in
/-- `(0, 0) ⊕ (1, 0) = (−1, 0)` on `y² = x³ − x`: the three nonzero `2`-torsion points, and they
are **distinct**. -/
private lemma exampleAdd :
    Point.some (0 : AlgClosedQ) 0 exampleNsS + Point.some (1 : AlgClosedQ) 0 exampleNsT
      = Point.some (-1 : AlgClosedQ) 0 exampleNsR := by
  rw [Point.add_of_X_ne (by norm_num)]
  simp only [Point.some.injEq]
  norm_num [y2EqX3SubX, WeierstrassCurve.Affine.addX, WeierstrassCurve.Affine.addY,
    WeierstrassCurve.Affine.negAddY, WeierstrassCurve.Affine.slope, WeierstrassCurve.Affine.negY]

open Classical in
/-- **Antisymmetry in `μ_2(F̄)` at `n = 2`, on a curve that exists**, at two **distinct** named
`2`-torsion points, in product form. -/
example : ∃ gS gT : (y2EqX3SubX AlgClosedQ).FunctionField, gS ≠ 0 ∧ gT ≠ 0 ∧
    (∃ f : (y2EqX3SubX AlgClosedQ).FunctionField, f ≠ 0 ∧
      (y2EqX3SubX AlgClosedQ).divisor f
        = Finsupp.single (pointClosedPoint exampleNsS.left) (2 : ℤ) ∧
      ∃ u : (y2EqX3SubX AlgClosedQ).CoordinateRingˣ,
        (u : (y2EqX3SubX AlgClosedQ).CoordinateRing) • gS ^ 2 = mulByTwoEndo exampleTwo f) ∧
    (∃ f : (y2EqX3SubX AlgClosedQ).FunctionField, f ≠ 0 ∧
      (y2EqX3SubX AlgClosedQ).divisor f
        = Finsupp.single (pointClosedPoint exampleNsT.left) (2 : ℤ) ∧
      ∃ u : (y2EqX3SubX AlgClosedQ).CoordinateRingˣ,
        (u : (y2EqX3SubX AlgClosedQ).CoordinateRing) • gT ^ 2 = mulByTwoEndo exampleTwo f) ∧
    ∃ hpowST : weilPairingElt exampleNsS.left gT ^ 2 = 1,
      ∃ hpowTS : weilPairingElt exampleNsT.left gS ^ 2 = 1,
        weilPairingMu exampleNsS.left hpowST * weilPairingMu exampleNsT.left hpowTS = 1 :=
  exists_weilPairingMu_mul_swap_eq_one_two exampleTwo exampleNsS exampleNsT exampleNsR
    exampleTorS exampleTorT exampleAdd

open Classical in
/-- **The inverse form at `n = 2`, on a curve that exists**, again at two **distinct** named
`2`-torsion points. -/
example : ∃ gS gT : (y2EqX3SubX AlgClosedQ).FunctionField, gS ≠ 0 ∧ gT ≠ 0 ∧
    (∃ f : (y2EqX3SubX AlgClosedQ).FunctionField, f ≠ 0 ∧
      (y2EqX3SubX AlgClosedQ).divisor f
        = Finsupp.single (pointClosedPoint exampleNsS.left) (2 : ℤ) ∧
      ∃ u : (y2EqX3SubX AlgClosedQ).CoordinateRingˣ,
        (u : (y2EqX3SubX AlgClosedQ).CoordinateRing) • gS ^ 2 = mulByTwoEndo exampleTwo f) ∧
    (∃ f : (y2EqX3SubX AlgClosedQ).FunctionField, f ≠ 0 ∧
      (y2EqX3SubX AlgClosedQ).divisor f
        = Finsupp.single (pointClosedPoint exampleNsT.left) (2 : ℤ) ∧
      ∃ u : (y2EqX3SubX AlgClosedQ).CoordinateRingˣ,
        (u : (y2EqX3SubX AlgClosedQ).CoordinateRing) • gT ^ 2 = mulByTwoEndo exampleTwo f) ∧
    ∃ hpowST : weilPairingElt exampleNsS.left gT ^ 2 = 1,
      ∃ hpowTS : weilPairingElt exampleNsT.left gS ^ 2 = 1,
        weilPairingMu exampleNsS.left hpowST = (weilPairingMu exampleNsT.left hpowTS)⁻¹ :=
  exists_weilPairingMu_eq_inv_two exampleTwo exampleNsS exampleNsT exampleNsR
    exampleTorS exampleTorT exampleAdd

private lemma exampleNsThreeS : (y2AddYEqX3 AlgClosedQ).Nonsingular 0 0 :=
  (y2AddYEqX3 AlgClosedQ).equation_iff_nonsingular.mp (by
    norm_num [y2AddYEqX3, WeierstrassCurve.Affine.equation_iff])

private lemma exampleNsThreeR : (y2AddYEqX3 AlgClosedQ).Nonsingular 0 (-1) :=
  (y2AddYEqX3 AlgClosedQ).equation_iff_nonsingular.mp (by
    norm_num [y2AddYEqX3, WeierstrassCurve.Affine.equation_iff])

open Classical in
private lemma exampleTorThreeS :
    Point.some (0 : AlgClosedQ) 0 exampleNsThreeS ∈ (y2AddYEqX3 AlgClosedQ).torsion 3 :=
  mem_torsion_three_some_iff'.mpr (by
    norm_num [y2AddYEqX3, WeierstrassCurve.Ψ₃, WeierstrassCurve.b₂,
      WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈])

open Classical in
/-- `(0, 0) ⊕ (0, 0) = (0, −1)` on `y² + y = x³`: doubling the named `3`-torsion point gives its
negative, which is the other one. -/
private lemma exampleAddThree :
    Point.some (0 : AlgClosedQ) 0 exampleNsThreeS
        + Point.some (0 : AlgClosedQ) 0 exampleNsThreeS
      = Point.some (0 : AlgClosedQ) (-1) exampleNsThreeR := by
  rw [Point.add_of_Y_ne (by norm_num [y2AddYEqX3, WeierstrassCurve.Affine.negY])]
  simp only [Point.some.injEq]
  norm_num [y2AddYEqX3, WeierstrassCurve.Affine.addX, WeierstrassCurve.Affine.addY,
    WeierstrassCurve.Affine.negAddY, WeierstrassCurve.Affine.slope, WeierstrassCurve.Affine.negY]

open Classical in
/-- **Antisymmetry in `μ_3(F̄)` at `n = 3`, on a curve that exists**, in product form.  ⚠️ Here
`S = T`; see the module docstring. -/
example : ∃ gS gT : (y2AddYEqX3 AlgClosedQ).FunctionField, gS ≠ 0 ∧ gT ≠ 0 ∧
    (∃ f : (y2AddYEqX3 AlgClosedQ).FunctionField, f ≠ 0 ∧
      (y2AddYEqX3 AlgClosedQ).divisor f
        = Finsupp.single (pointClosedPoint exampleNsThreeS.left) (3 : ℤ) ∧
      ∃ u : (y2AddYEqX3 AlgClosedQ).CoordinateRingˣ,
        (u : (y2AddYEqX3 AlgClosedQ).CoordinateRing) • gS ^ 3
          = mulByThreeEndo exampleTwo exampleThree f) ∧
    (∃ f : (y2AddYEqX3 AlgClosedQ).FunctionField, f ≠ 0 ∧
      (y2AddYEqX3 AlgClosedQ).divisor f
        = Finsupp.single (pointClosedPoint exampleNsThreeS.left) (3 : ℤ) ∧
      ∃ u : (y2AddYEqX3 AlgClosedQ).CoordinateRingˣ,
        (u : (y2AddYEqX3 AlgClosedQ).CoordinateRing) • gT ^ 3
          = mulByThreeEndo exampleTwo exampleThree f) ∧
    ∃ hpowST : weilPairingElt exampleNsThreeS.left gT ^ 3 = 1,
      ∃ hpowTS : weilPairingElt exampleNsThreeS.left gS ^ 3 = 1,
        weilPairingMu exampleNsThreeS.left hpowST
          * weilPairingMu exampleNsThreeS.left hpowTS = 1 :=
  exists_weilPairingMu_mul_swap_eq_one_three exampleTwo exampleThree exampleNsThreeS
    exampleNsThreeS exampleNsThreeR exampleTorThreeS exampleTorThreeS exampleAddThree

open Classical in
/-- **The inverse form at `n = 3`, on a curve that exists.**  ⚠️ Here `S = T`; see the module
docstring. -/
example : ∃ gS gT : (y2AddYEqX3 AlgClosedQ).FunctionField, gS ≠ 0 ∧ gT ≠ 0 ∧
    (∃ f : (y2AddYEqX3 AlgClosedQ).FunctionField, f ≠ 0 ∧
      (y2AddYEqX3 AlgClosedQ).divisor f
        = Finsupp.single (pointClosedPoint exampleNsThreeS.left) (3 : ℤ) ∧
      ∃ u : (y2AddYEqX3 AlgClosedQ).CoordinateRingˣ,
        (u : (y2AddYEqX3 AlgClosedQ).CoordinateRing) • gS ^ 3
          = mulByThreeEndo exampleTwo exampleThree f) ∧
    (∃ f : (y2AddYEqX3 AlgClosedQ).FunctionField, f ≠ 0 ∧
      (y2AddYEqX3 AlgClosedQ).divisor f
        = Finsupp.single (pointClosedPoint exampleNsThreeS.left) (3 : ℤ) ∧
      ∃ u : (y2AddYEqX3 AlgClosedQ).CoordinateRingˣ,
        (u : (y2AddYEqX3 AlgClosedQ).CoordinateRing) • gT ^ 3
          = mulByThreeEndo exampleTwo exampleThree f) ∧
    ∃ hpowST : weilPairingElt exampleNsThreeS.left gT ^ 3 = 1,
      ∃ hpowTS : weilPairingElt exampleNsThreeS.left gS ^ 3 = 1,
        weilPairingMu exampleNsThreeS.left hpowST
          = (weilPairingMu exampleNsThreeS.left hpowTS)⁻¹ :=
  exists_weilPairingMu_eq_inv_three exampleTwo exampleThree exampleNsThreeS
    exampleNsThreeS exampleNsThreeR exampleTorThreeS exampleTorThreeS exampleAddThree

end Nonvacuity

end WeierstrassCurve.Affine
