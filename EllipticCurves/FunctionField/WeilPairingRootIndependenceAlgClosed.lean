/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import EllipticCurves.FunctionField.PullbackPrincipalityThree
import EllipticCurves.FunctionField.PullbackPrincipalityTwo
import EllipticCurves.FunctionField.WeilPairingAlternatingMu
import EllipticCurves.FunctionField.WeilPairingRootIndependence

/-!
# The root-independent alternating property over an algebraically closed field, at both `n`

Silverman *AEC* III.8.1(d): the Weil pairing is alternating, `e_n(T, T) = 1`.

`EllipticCurves.FunctionField.WeilPairingRootIndependence` upgrades the two merged alternating
headlines from *some* `n`-th root of `[n]∗ f_T` to **every** `n`-th root, at `n = 2` and at `n = 3`,
and it does so without adding a hypothesis: both of its headline corollaries carry the same `hprin`
— the principality of `[n]∗((T) − (O))` — that the statements they consume carry.  This file
discharges that `hprin`, at both `n`, from
`EllipticCurves.FunctionField.PullbackPrincipalityTwo` (`#791`) and
`EllipticCurves.FunctionField.PullbackPrincipalityThree` (`#825`).  It is the composition and
nothing else: **nothing new is proved here about curves.**

⚠️ **The gap this closes was symmetric, and that is the reason the file hosts both `n`.**
`WeilPairingAlternatingTwoAlgClosed` (`#791`'s consumer) discharged `hprin` only for the
*existential*-root headline, and `WeilPairingAlternatingThreeAlgClosed` (`#829`) mirrored it at
`n = 3`.  Neither touched the `∀ g` form, so the omission was never an `n = 3` asymmetry: it was one
omission appearing twice.  ⚠️ Before pricing an `n = 3` mirror on this front, check whether the
`n = 2` name exists — twice now it has not.

## Why the `∀ g` form is the one a consumer can apply

`weilPairingElt` takes the root `g_T` as an **argument**, so the existential headlines cannot be
applied to a root that arrives from elsewhere — from `exists_gS_two_of_isAlgClosed` /
`exists_gS_three_of_isAlgClosed`, say, or supplied by a caller who already holds one.  The
statements below are the ones that accept such a root.

⚠️ **Non-degeneracy is not an instance of that need, though this file's issue said it was.**
`EllipticCurves.FunctionField.WeilPairingNondegenerateTwo` and
`EllipticCurves.FunctionField.WeilPairingNondegenerateThree` state their cores against an
arbitrary rung-5 root passed as an explicit argument and apply **no** alternating statement in
either form, so they neither consume nor are blocked by anything here.  The justification for the
statements below is the first sentence of this section on its own.

⚠️ **Neither is antisymmetry, and `#854` predicted that it was.**  The `∀ g` antisymmetry headlines
(`EllipticCurves.FunctionField.WeilPairingProductRelationRootIndependent`) reach a root that
arrives from elsewhere by a different mechanism — `weilPairingElt_eq_of_nsmul_divisor_eq`
(`WeilPairingRootIndependence`, `#719`) makes the pairing element depend on its root only through
the root's divisor, so the existential headline's own roots can be exchanged for the caller's after
the fact.  That file uses nothing from this one.  Recorded here rather than only on the issue
thread, since a reader of this file would otherwise reasonably expect it to be a consumer.

## Main statements

* `WeierstrassCurve.Affine.exists_forall_weilPairingElt_self_eq_one_of_isAlgClosed` — at `n = 2`:
  for a nonsingular affine `2`-torsion `T` there is a function `f_T` with projective divisor
  `2(T) − 2(O)` such that **every** nonzero `g` with `u · g ^ 2 = [2]∗ f_T`, for some unit `u` of
  `F[W]`, satisfies `τ_T∗ g = g` and `e_2(T, T) = 1`.
* `WeierstrassCurve.Affine.exists_forall_weilPairingElt_self_eq_one_of_isAlgClosed_three` — the same
  at `n = 3`, with cube roots of `[3]∗ f_T`.
* `WeierstrassCurve.Affine.exists_forall_weilPairingMu_self_eq_one_of_isAlgClosed` and
  `WeierstrassCurve.Affine.exists_forall_weilPairingMu_self_eq_one_of_isAlgClosed_three` — the same
  two in the value group: `weilPairingMu(T, T) = 1` in `μ_n(F)`, for every `n` with `[NeZero n]`.
  The root-of-unity datum `hpow` that `weilPairingMu` is indexed by costs nothing, because the
  statements above already give `e_n(T, T) = 1`.

All four are certified on concrete curves — see the non-vacuity section.

## Scope

⚠️ **The function `f_T` stays existential, and that is not an oversight.**
`WeilPairingRootIndependence`'s own docstring records why: `f_T` is pinned only up to a unit, and
rescaling `f_T` rescales `g` by an `n`-th root of a constant rather than by a constant, so
quantifying over `f_T` is a genuinely different statement needing root extraction.  Nothing here
changes that.

⚠️ **`[IsAlgClosed F]` is load-bearing and enters twice, independently, at each `n`.**  Once through
the discharge (`PullbackPrincipality{Two,Three}`, themselves through the surjectivity of `[n]` on
points and through the fibre description of `[n]∗`), and once through
`exists_equation_nsmul_{two,three}_eq`, which is how `WeilPairingAlternating{Two,Three}` obtains the
point `P` with `[n]P = T` that its second product translates by.  A theorem that discharges a
hypothesis inherits the hypotheses of its *proof*, not those of the statement it discharges, which
is why this file exists rather than an edit to `WeilPairingRootIndependence` — whose conditional
statements are unchanged, so that a future general-field discharge has somewhere to land.
⚠️ `hprin` over a **general** field is open at both `n`, and is a different statement from anything
here.

⚠️ **`[IsDedekindDomain W.CoordinateRing]` is not a hypothesis of anything here.**  It is a global
instance for `[W.IsElliptic]` over an **arbitrary** field
(`EllipticCurves.FunctionField.CoordinateRingNormalGeneral`), so it neither appears in the variable
block nor contributes to the `[IsAlgClosed F]` accounting above.

⚠️ **The statements below are pinned to `Classical.propDecidable`.**  `open Classical in` is
required and not a formality: they mention `W.torsion n`, whose `DecidableEq F` instance has to
agree with the one baked into the statements they consume.  The cost is that a consumer whose own
variable block carries `[DecidableEq F]` cannot apply them directly; the bridge is
`obtain rfl : ‹DecidableEq F› = (fun a b => Classical.propDecidable (a = b)) :=
Subsingleton.elim _ _`.

⚠️ **This is not antisymmetry.**  `weilPairingElt_mul_swap_eq_one` (`WeilPairingAntisymmetric`)
consumes the alternating property at three points, which this file supplies unconditionally over
`F̄` at both `n` and in the applicable form — but it also needs the product relation
`g_{S ⊕ T} = g_S · g_T · w` as the hypothesis `hprod`, which is rung-4/5 gated (`#414`/`#418`) and
which nothing here touches.  Nor is this bilinearity, Galois-equivariance, general `n`, or
non-degeneracy, which at `n = 3` is `EllipticCurves.FunctionField.WeilPairingNondegenerateThree`
(`#831`) and is independent of this file in both directions.

## References

* [J. H. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.8, Prop. 8.1(d).
-/

namespace WeierstrassCurve.Affine

open CoordinateRing

variable {F : Type*} [Field F] {W : Affine F}

section AlgClosed

variable [W.IsElliptic] [IsAlgClosed F] {x₂ y₂ : F}

open Classical in
/-- **`e_2(T, T) = 1` for every square root, over an algebraically closed field, with no hypothesis
beyond the setting.**

For a nonsingular affine `2`-torsion point `T = (x₂, y₂)` there is a nonzero `f_T` whose projective
divisor is `2(T) − 2(O)` such that *every* nonzero `g` with `u · g ^ 2 = [2]∗ f_T`, for a unit `u`
of `F[W]`, is fixed by the translation `τ_T∗` — hence `e_2(T, T) = 1` for every such `g`.

`exists_forall_weilPairingElt_self_eq_one_of_algClosed` (`WeilPairingRootIndependence`) is this
statement with the principality of `[2]∗((T) − (O))` carried as the hypothesis `hprin`, and
`exists_nsmul_divisor_eq_divisor_mulByTwoEndo` (`PullbackPrincipalityTwo`) is exactly that
hypothesis, proved.  The two compose with nothing in between. -/
theorem exists_forall_weilPairingElt_self_eq_one_of_isAlgClosed (h2 : (2 : F) ≠ 0)
    (h : W.Nonsingular x₂ y₂) (htors : Point.some x₂ y₂ h ∈ W.torsion 2) :
    ∃ f : W.FunctionField, f ≠ 0 ∧
      divisorProj W f = Finsupp.single (some (pointClosedPoint h.left)) (2 : ℤ)
          - Finsupp.single (none : ProjPoint W) (2 : ℤ) ∧
        ∀ g : W.FunctionField, g ≠ 0 →
          (∃ u : W.CoordinateRingˣ, (u : W.CoordinateRing) • g ^ 2 = mulByTwoEndo h2 f) →
            translateEndo h.left g = g ∧ weilPairingElt h.left g = 1 :=
  exists_forall_weilPairingElt_self_eq_one_of_algClosed h2 h htors fun _ hf hfdiv =>
    exists_nsmul_divisor_eq_divisor_mulByTwoEndo h2 h htors hf hfdiv

open Classical in
/-- **`e_3(T, T) = 1` for every cube root, over an algebraically closed field, with no hypothesis
beyond the setting.**

The `n = 3` twin of `exists_forall_weilPairingElt_self_eq_one_of_isAlgClosed`, discharged the same
way from `exists_nsmul_divisor_eq_divisor_mulByThreeEndo` (`PullbackPrincipalityThree`, `#825`).

⚠️ `h2` and `h3` are both genuinely needed, and not for symmetric reasons: `h3` enters only through
`mulByThreeEndo`, which the statement mentions, while `h2` enters through the doubling slope that
produces the fibre point `P` with `[3]P = T`. -/
theorem exists_forall_weilPairingElt_self_eq_one_of_isAlgClosed_three (h2 : (2 : F) ≠ 0)
    (h3 : (3 : F) ≠ 0) (h : W.Nonsingular x₂ y₂) (htors : Point.some x₂ y₂ h ∈ W.torsion 3) :
    ∃ f : W.FunctionField, f ≠ 0 ∧
      divisorProj W f = Finsupp.single (some (pointClosedPoint h.left)) (3 : ℤ)
          - Finsupp.single (none : ProjPoint W) (3 : ℤ) ∧
        ∀ g : W.FunctionField, g ≠ 0 →
          (∃ u : W.CoordinateRingˣ, (u : W.CoordinateRing) • g ^ 3 = mulByThreeEndo h2 h3 f) →
            translateEndo h.left g = g ∧ weilPairingElt h.left g = 1 :=
  exists_forall_weilPairingElt_self_eq_one_of_algClosed_three h2 h3 h htors fun _ hf hfdiv =>
    exists_nsmul_divisor_eq_divisor_mulByThreeEndo h2 h3 h htors hf hfdiv

open Classical in
/-- **The root-independent alternating property at `n = 2` in the value group**:
`weilPairingMu(T, T) = 1` in `μ_n(F)` for *every* square root of `[2]∗ f_T`.

`weilPairingMu` is indexed by a proof `hpow` that the pairing element is an `n`-th root of unity, so
the statement produces one for each `g`; it costs nothing, since the theorem above already gives
`e_2(T, T) = 1` and `1 ^ n = 1`.  The `n` is arbitrary for the same reason — this is the group
identity of `μ_n(F)` for whichever `n` the caller has packaged the value in, not a claim that `e_2`
lands in `μ_n` for `n ≠ 2`.

The `μ_n`-level reduction is `weilPairingMu_self_of_translateEndo_fixed`
(`WeilPairingAlternatingMu`), whose own hypothesis is the translation-invariance that the theorem
above supplies for every `g`. -/
theorem exists_forall_weilPairingMu_self_eq_one_of_isAlgClosed (h2 : (2 : F) ≠ 0)
    (h : W.Nonsingular x₂ y₂) (htors : Point.some x₂ y₂ h ∈ W.torsion 2) (n : ℕ) [NeZero n] :
    ∃ f : W.FunctionField, f ≠ 0 ∧
      divisorProj W f = Finsupp.single (some (pointClosedPoint h.left)) (2 : ℤ)
          - Finsupp.single (none : ProjPoint W) (2 : ℤ) ∧
        ∀ g : W.FunctionField, g ≠ 0 →
          (∃ u : W.CoordinateRingˣ, (u : W.CoordinateRing) • g ^ 2 = mulByTwoEndo h2 f) →
            ∃ hpow : weilPairingElt h.left g ^ n = 1, weilPairingMu h.left hpow = 1 := by
  obtain ⟨f, hf, hdivproj, hall⟩ :=
    exists_forall_weilPairingElt_self_eq_one_of_isAlgClosed h2 h htors
  refine ⟨f, hf, hdivproj, fun g hg hgroot => ?_⟩
  obtain ⟨htinv, halt⟩ := hall g hg hgroot
  exact ⟨by rw [halt, one_pow], weilPairingMu_self_of_translateEndo_fixed h.left hg _ htinv⟩

open Classical in
/-- **The root-independent alternating property at `n = 3` in the value group**:
`weilPairingMu(T, T) = 1` in `μ_n(F)` for *every* cube root of `[3]∗ f_T`.  The `n = 3` twin of
`exists_forall_weilPairingMu_self_eq_one_of_isAlgClosed`, proved the same way. -/
theorem exists_forall_weilPairingMu_self_eq_one_of_isAlgClosed_three (h2 : (2 : F) ≠ 0)
    (h3 : (3 : F) ≠ 0) (h : W.Nonsingular x₂ y₂) (htors : Point.some x₂ y₂ h ∈ W.torsion 3)
    (n : ℕ) [NeZero n] :
    ∃ f : W.FunctionField, f ≠ 0 ∧
      divisorProj W f = Finsupp.single (some (pointClosedPoint h.left)) (3 : ℤ)
          - Finsupp.single (none : ProjPoint W) (3 : ℤ) ∧
        ∀ g : W.FunctionField, g ≠ 0 →
          (∃ u : W.CoordinateRingˣ, (u : W.CoordinateRing) • g ^ 3 = mulByThreeEndo h2 h3 f) →
            ∃ hpow : weilPairingElt h.left g ^ n = 1, weilPairingMu h.left hpow = 1 := by
  obtain ⟨f, hf, hdivproj, hall⟩ :=
    exists_forall_weilPairingElt_self_eq_one_of_isAlgClosed_three h2 h3 h htors
  refine ⟨f, hf, hdivproj, fun g hg hgroot => ?_⟩
  obtain ⟨htinv, halt⟩ := hall g hg hgroot
  exact ⟨by rw [halt, one_pow], weilPairingMu_self_of_translateEndo_fixed h.left hg _ htinv⟩

end AlgClosed

/-! ### Non-vacuity

`WeilPairingRootIndependence`'s own non-vacuity section could certify its `CoordinateRing`-namespace
machinery but not its two headline corollaries, because `hprin` was carried there.  It is carried no
longer, so all four statements above are certified outright, each on the curve its `n` admits.

⚠️ **Two base curves are needed, and the split is intrinsic.**  At `n = 2` the certificate is
`y² = x³ − x` at `T = (0, 0)`, the curve `WeilPairingRootIndependence` and
`WeilPairingAlternatingTwoAlgClosed` already use.  It does **not** serve at `n = 3`: its
`Ψ₃ = 3X⁴ − 6X² − 1` has no rational root, so none of its nine `3`-torsion points over
`AlgebraicClosure ℚ` can be named without a genuine algebraic-number argument.  At `n = 3` the
certificate is `y² + y = x³` at `T = (0, 0)`, where `Ψ₃ = 3X⁴ + 3b₆X = 3X(X³ + 1)` vanishes — the
curve `WeilPairingAlternatingThreeAlgClosed` and `PullbackPrincipalityThree` use.

⚠️ What stays unnameable on either curve is a *fibre* witness `P` with `n • P = T`; that is what
`PullbackPrincipalityTwo`'s non-vacuity note is about, and it is produced existentially by
`exists_nsmul_{two,three}_eq` and never exhibited. -/

section Nonvacuity

/-- An algebraically closed field of characteristic zero. -/
private abbrev exampleField : Type := AlgebraicClosure ℚ

private lemma exampleTwo : (2 : exampleField) ≠ 0 := by norm_num

private lemma exampleThree : (3 : exampleField) ≠ 0 := by norm_num

/-- The curve `y² = x³ − x` over `AlgebraicClosure ℚ`, of discriminant `64`. -/
private noncomputable def exampleCurve : Affine exampleField := ⟨0, 0, 0, -1, 0⟩

private instance : exampleCurve.IsElliptic := by
  rw [WeierstrassCurve.isElliptic_iff, isUnit_iff_ne_zero]
  norm_num [exampleCurve, WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈]

/-- `T = (0, 0)` lies on `y² = x³ − x` and is nonsingular. -/
private lemma exampleNonsingular : exampleCurve.Nonsingular 0 0 :=
  exampleCurve.equation_iff_nonsingular.mp (by
    norm_num [exampleCurve, WeierstrassCurve.Affine.equation_iff])

open Classical in
/-- `T = (0, 0)` is `2`-torsion: `2y + a₁x + a₃ = 0` reads `0 = 0`. -/
private lemma exampleTorsion :
    Point.some (0 : exampleField) 0 exampleNonsingular ∈ exampleCurve.torsion 2 :=
  (mem_torsion_two_some_iff exampleNonsingular).mpr (by norm_num [exampleCurve])

/-- The curve `y² + y = x³` over `AlgebraicClosure ℚ`, of discriminant `−27`. -/
private noncomputable def exampleCurveThree : Affine exampleField := ⟨0, 0, 1, 0, 0⟩

private instance : exampleCurveThree.IsElliptic := by
  rw [WeierstrassCurve.isElliptic_iff, isUnit_iff_ne_zero]
  norm_num [exampleCurveThree, WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈]

/-- `T = (0, 0)` lies on `y² + y = x³` and is nonsingular. -/
private lemma exampleNonsingularThree : exampleCurveThree.Nonsingular 0 0 :=
  exampleCurveThree.equation_iff_nonsingular.mp (by
    norm_num [exampleCurveThree, WeierstrassCurve.Affine.equation_iff])

open Classical in
/-- `T = (0, 0)` is `3`-torsion: `Ψ₃ = 3X⁴ + 3b₆X` vanishes at `0`. -/
private lemma exampleTorsionThree :
    Point.some (0 : exampleField) 0 exampleNonsingularThree ∈ exampleCurveThree.torsion 3 :=
  mem_torsion_three_some_iff'.mpr (by
    norm_num [exampleCurveThree, WeierstrassCurve.Ψ₃, WeierstrassCurve.b₂,
      WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈])

open Classical in
/-- **The root-independent alternating property at `n = 2`, on a curve that exists**, with the
torsion point named and every instance discharged. -/
example : ∃ f : exampleCurve.FunctionField, f ≠ 0 ∧
    exampleCurve.divisorProj f
        = Finsupp.single (some (pointClosedPoint exampleNonsingular.left)) (2 : ℤ)
          - Finsupp.single (none : ProjPoint exampleCurve) (2 : ℤ) ∧
      ∀ g : exampleCurve.FunctionField, g ≠ 0 →
        (∃ u : exampleCurve.CoordinateRingˣ,
          (u : exampleCurve.CoordinateRing) • g ^ 2 = mulByTwoEndo exampleTwo f) →
          translateEndo exampleNonsingular.left g = g ∧
            weilPairingElt exampleNonsingular.left g = 1 :=
  exists_forall_weilPairingElt_self_eq_one_of_isAlgClosed exampleTwo exampleNonsingular
    exampleTorsion

open Classical in
/-- **The value-group form at `n = 2`, on the same curve**: `weilPairingMu(T, T) = 1` in `μ₂(F̄)`
for every square root. -/
example : ∃ f : exampleCurve.FunctionField, f ≠ 0 ∧
    exampleCurve.divisorProj f
        = Finsupp.single (some (pointClosedPoint exampleNonsingular.left)) (2 : ℤ)
          - Finsupp.single (none : ProjPoint exampleCurve) (2 : ℤ) ∧
      ∀ g : exampleCurve.FunctionField, g ≠ 0 →
        (∃ u : exampleCurve.CoordinateRingˣ,
          (u : exampleCurve.CoordinateRing) • g ^ 2 = mulByTwoEndo exampleTwo f) →
          ∃ hpow : weilPairingElt exampleNonsingular.left g ^ 2 = 1,
            weilPairingMu exampleNonsingular.left hpow = 1 :=
  exists_forall_weilPairingMu_self_eq_one_of_isAlgClosed exampleTwo exampleNonsingular
    exampleTorsion 2

open Classical in
/-- **The root-independent alternating property at `n = 3`, on a curve that exists**, with the
torsion point named and every instance discharged. -/
example : ∃ f : exampleCurveThree.FunctionField, f ≠ 0 ∧
    exampleCurveThree.divisorProj f
        = Finsupp.single (some (pointClosedPoint exampleNonsingularThree.left)) (3 : ℤ)
          - Finsupp.single (none : ProjPoint exampleCurveThree) (3 : ℤ) ∧
      ∀ g : exampleCurveThree.FunctionField, g ≠ 0 →
        (∃ u : exampleCurveThree.CoordinateRingˣ,
          (u : exampleCurveThree.CoordinateRing) • g ^ 3
            = mulByThreeEndo exampleTwo exampleThree f) →
          translateEndo exampleNonsingularThree.left g = g ∧
            weilPairingElt exampleNonsingularThree.left g = 1 :=
  exists_forall_weilPairingElt_self_eq_one_of_isAlgClosed_three exampleTwo exampleThree
    exampleNonsingularThree exampleTorsionThree

open Classical in
/-- **The value-group form at `n = 3`, on the same curve**: `weilPairingMu(T, T) = 1` in `μ₃(F̄)`
for every cube root. -/
example : ∃ f : exampleCurveThree.FunctionField, f ≠ 0 ∧
    exampleCurveThree.divisorProj f
        = Finsupp.single (some (pointClosedPoint exampleNonsingularThree.left)) (3 : ℤ)
          - Finsupp.single (none : ProjPoint exampleCurveThree) (3 : ℤ) ∧
      ∀ g : exampleCurveThree.FunctionField, g ≠ 0 →
        (∃ u : exampleCurveThree.CoordinateRingˣ,
          (u : exampleCurveThree.CoordinateRing) • g ^ 3
            = mulByThreeEndo exampleTwo exampleThree f) →
          ∃ hpow : weilPairingElt exampleNonsingularThree.left g ^ 3 = 1,
            weilPairingMu exampleNonsingularThree.left hpow = 1 :=
  exists_forall_weilPairingMu_self_eq_one_of_isAlgClosed_three exampleTwo exampleThree
    exampleNonsingularThree exampleTorsionThree 3

end Nonvacuity

end WeierstrassCurve.Affine
