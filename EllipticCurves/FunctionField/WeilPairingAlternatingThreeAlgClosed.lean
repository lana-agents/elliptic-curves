/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import EllipticCurves.FunctionField.PullbackPrincipalityThree
import EllipticCurves.FunctionField.WeilPairingAlternatingMu
import EllipticCurves.FunctionField.WeilPairingAlternatingThree

/-!
# The alternating property at `n = 3` over an algebraically closed field, unconditionally

Silverman *AEC* III.8.1(d): the Weil pairing is alternating, `e_n(T, T) = 1`.

`EllipticCurves.FunctionField.WeilPairingAlternatingThree` proves this at `n = 3` over an
algebraically closed field with exactly one gated hypothesis: `hprin`, the principality of
`[3]∗((T) − (O))`, in the shape `exists_gS_three` takes it.
`EllipticCurves.FunctionField.PullbackPrincipalityThree` discharged that hypothesis.  This file is
the composition, and it is the whole content of the file: **nothing new is proved here about
curves.**  It is the `n = 3` mirror of
`EllipticCurves.FunctionField.WeilPairingAlternatingTwoAlgClosed`.

The two shapes match argument for argument, so the discharge is a single application — the
hypothesis of `exists_weilPairingElt_self_eq_one_of_algClosed_three` is literally the conclusion of
`exists_nsmul_divisor_eq_divisor_mulByThreeEndo`, universally quantified over the same `f`.

## Main statements

* `WeierstrassCurve.Affine.exists_weilPairingElt_self_eq_one_of_isAlgClosed_three` — the alternating
  property in `F(W)`: for a nonsingular affine `3`-torsion `T` there are a function `f_T` with
  projective divisor `3(T) − 3(O)`, a cube root `g_T` of `[3]∗ f_T` up to a unit of `F[W]`, and the
  conclusions `τ_T∗ g_T = g_T` and `e_3(T, T) = 1`.
* `WeierstrassCurve.Affine.exists_weilPairingMu_self_eq_one_of_isAlgClosed_three` — the same in the
  value group: `weilPairingMu(T, T) = 1` in `μ_n(F)`, for every `n` with `[NeZero n]`.

⚠️ **The naming register forces the `is` and forbids reusing the `n = 3` conditional name.**  At
`n = 2` the conditional statement is `exists_weilPairingElt_self_eq_one_of_algClosed_two`
(`WeilPairingAlternatingTwo`) and the unconditional one is
`exists_weilPairingElt_self_eq_one_of_isAlgClosed_two` (`WeilPairingAlternatingTwoAlgClosed`); both
live in the namespace `WeierstrassCurve.Affine`, so the `is` is what separates them.  At `n = 3` the
conditional name is `exists_weilPairingElt_self_eq_one_of_algClosed_three`, already taken in this
same namespace, and the unconditional one is therefore `..._of_isAlgClosed_three`.

Both are certified on `y² + y = x³` over `AlgebraicClosure ℚ` with the `3`-torsion point named as
`(0, 0)` — see the non-vacuity section.

## Scope

⚠️ **The `∀ g` form is not what the two statements below say, and it lives elsewhere.**
`exists_forall_weilPairingElt_self_eq_one_of_algClosed_three`
(`EllipticCurves.FunctionField.WeilPairingRootIndependence`) strengthens the existential root to
*every* cube root of `[3]∗ f_T`, and it carries the same `hprin` in its own signature — as does its
`n = 2` twin `exists_forall_weilPairingElt_self_eq_one_of_algClosed_two`, which
`WeilPairingAlternatingTwoAlgClosed` did **not** discharge either.  ⚠️ That omission was symmetric,
not an `n = 3` asymmetry.  Both are now discharged, at both `n` and in one place, in
`EllipticCurves.FunctionField.WeilPairingRootIndependenceAlgClosed` (`#836`); do not read the two
statements below as covering the `∀ g` form.

⚠️ **`[IsAlgClosed F]` is load-bearing and enters twice, independently.**  Once through the
discharge (`PullbackPrincipalityThree`, itself through the surjectivity of `[3]` on points and
through the fibre description of `[3]∗`), and once through `exists_equation_nsmul_three_eq`, which
is how `WeilPairingAlternatingThree` obtains the point `P` with `[3]P = T` that its second product
translates by.  A theorem that discharges a hypothesis inherits the hypotheses of its *proof*, not
those of the statement it discharges, which is why this file exists rather than an edit to
`WeilPairingAlternatingThree` — whose conditional statement is unchanged, so that a future
general-field discharge has somewhere to land.  `hprin` over a general field is open at both `n`.

⚠️ **`h2` and `h3` are both genuinely needed, and not for symmetric reasons.**  `h3` enters only
through `mulByThreeEndo`, which the statement mentions; `h2` enters through the doubling slope that
produces the fibre point `P`, which is why `exists_nsmul_three_eq` and
`exists_nsmul_divisor_eq_divisor_mulByThreeEndo`'s producer need it.  See
`PullbackPrincipalityThree`'s docstring for the hypothesis accounting.

⚠️ **`[IsDedekindDomain W.CoordinateRing]` is not a hypothesis of anything here.**  It is a global
instance for `[W.IsElliptic]` over an **arbitrary** field
(`EllipticCurves.FunctionField.CoordinateRingNormalGeneral`), so it neither appears in the variable
block nor contributes to the `[IsAlgClosed F]` accounting above.

⚠️ **The statements below are pinned to `Classical.propDecidable`.**  `open Classical in` is
required and not a formality: they mention `W.torsion 3`, whose `DecidableEq F` instance has to
agree with the one baked into `PullbackPrincipalityThree`'s `[DecidableEq F]` variable block and
into the statements they consume.  The cost is that a consumer whose own variable block carries
`[DecidableEq F]` cannot apply them directly; the bridge is
`obtain rfl : ‹DecidableEq F› = (fun a b => Classical.propDecidable (a = b)) :=
Subsingleton.elim _ _`.

⚠️ **This is not antisymmetry.**  `weilPairingElt_mul_swap_eq_one` (`WeilPairingAntisymmetric`)
consumes the alternating property at three points, which this file now supplies unconditionally
over `F̄` at `n = 3` — but it also needs the product relation `g_{S ⊕ T} = g_S · g_T · w` as the
hypothesis `hprod`, which nothing here touches.  ⚠️ `hprod` is **not** rung-4 gated, as this
bullet used to say: it follows from rung-5 data alone, and
`EllipticCurves.FunctionField.WeilPairingProductRelation` (`#845`) composes it with the theorems
below into unconditional antisymmetry over `F̄` at `n = 3`.  Nor is
this bilinearity, Galois-equivariance at `n = 3` (`#830`), general `n`, or non-degeneracy at
`n = 3` (`#831`, now assembled in
`EllipticCurves.FunctionField.WeilPairingNondegenerateThree`).

## References

* [J. H. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.8, Prop. 8.1(d).
-/

namespace WeierstrassCurve.Affine

open CoordinateRing

variable {F : Type*} [Field F] {W : Affine F}

section AlgClosed

variable [W.IsElliptic] [IsAlgClosed F] {x₃ y₃ : F}

open Classical in
/-- **`e_3(T, T) = 1` over an algebraically closed field, with no hypothesis beyond the setting.**

For a nonsingular affine `3`-torsion point `T = (x₃, y₃)` there are a nonzero `f_T` whose projective
divisor is `3(T) − 3(O)` and a nonzero `g_T` with `u · g_T ^ 3 = [3]∗ f_T` for a unit `u` of `F[W]`,
such that the translation `τ_T∗` fixes `g_T` — hence `e_3(T, T) = 1`.

`exists_weilPairingElt_self_eq_one_of_algClosed_three` (`WeilPairingAlternatingThree`) is this
statement with the principality of `[3]∗((T) − (O))` carried as the hypothesis `hprin`, and
`exists_nsmul_divisor_eq_divisor_mulByThreeEndo` (`PullbackPrincipalityThree`) is exactly that
hypothesis, proved.  The two compose with nothing in between. -/
theorem exists_weilPairingElt_self_eq_one_of_isAlgClosed_three (h2 : (2 : F) ≠ 0)
    (h3 : (3 : F) ≠ 0) (h : W.Nonsingular x₃ y₃) (htors : Point.some x₃ y₃ h ∈ W.torsion 3) :
    ∃ f : W.FunctionField, f ≠ 0 ∧
      divisorProj W f = Finsupp.single (some (pointClosedPoint h.left)) (3 : ℤ)
          - Finsupp.single (none : ProjPoint W) (3 : ℤ) ∧
        ∃ g : W.FunctionField, g ≠ 0 ∧
          (∃ u : W.CoordinateRingˣ, (u : W.CoordinateRing) • g ^ 3 = mulByThreeEndo h2 h3 f) ∧
          translateEndo h.left g = g ∧ weilPairingElt h.left g = 1 :=
  exists_weilPairingElt_self_eq_one_of_algClosed_three h2 h3 h htors fun _ hf hfdiv =>
    exists_nsmul_divisor_eq_divisor_mulByThreeEndo h2 h3 h htors hf hfdiv

open Classical in
/-- **The alternating property at `n = 3` in the value group**: `weilPairingMu(T, T) = 1` in
`μ_n(F)`, over an algebraically closed field and with no hypothesis beyond the setting.

`weilPairingMu` is indexed by a proof `hpow` that the pairing element is an `n`-th root of unity, so
the statement produces one; it costs nothing, since the previous theorem already gives
`e_3(T, T) = 1` and `1 ^ n = 1`.  The `n` is arbitrary for the same reason — this is the group
identity of `μ_n(F)` for whichever `n` the caller has packaged the value in, not a claim that `e_3`
lands in `μ_n` for `n ≠ 3`.

The `μ_n`-level reduction is `weilPairingMu_self_of_translateEndo_fixed`
(`WeilPairingAlternatingMu`), whose own hypothesis is the translation-invariance that the previous
theorem supplies. -/
theorem exists_weilPairingMu_self_eq_one_of_isAlgClosed_three (h2 : (2 : F) ≠ 0)
    (h3 : (3 : F) ≠ 0) (h : W.Nonsingular x₃ y₃) (htors : Point.some x₃ y₃ h ∈ W.torsion 3)
    (n : ℕ) [NeZero n] :
    ∃ f : W.FunctionField, f ≠ 0 ∧
      divisorProj W f = Finsupp.single (some (pointClosedPoint h.left)) (3 : ℤ)
          - Finsupp.single (none : ProjPoint W) (3 : ℤ) ∧
        ∃ g : W.FunctionField, g ≠ 0 ∧
          (∃ u : W.CoordinateRingˣ, (u : W.CoordinateRing) • g ^ 3 = mulByThreeEndo h2 h3 f) ∧
          ∃ hpow : weilPairingElt h.left g ^ n = 1, weilPairingMu h.left hpow = 1 := by
  obtain ⟨f, hf, hdivproj, g, hg, hu, htinv, halt⟩ :=
    exists_weilPairingElt_self_eq_one_of_isAlgClosed_three h2 h3 h htors
  exact ⟨f, hf, hdivproj, g, hg, hu, by rw [halt, one_pow],
    weilPairingMu_self_of_translateEndo_fixed h.left hg _ htinv⟩

end AlgClosed

/-! ### Non-vacuity

`WeilPairingAlternatingThree`'s own non-vacuity section could only certify that the hypotheses of
its headline are simultaneously satisfiable, because `hprin` was open.  It is open no longer, so the
statements above are certified outright: `y² + y = x³` over `AlgebraicClosure ℚ` is elliptic, the
base field is algebraically closed of characteristic `≠ 2, 3`, and the `3`-torsion point is
**named** as `(0, 0)`, because `Ψ₃ = 3X⁴ + 3b₆X = 3X(X³ + 1)` vanishes there.

⚠️ The `n = 2` certificate curve `y² = x³ − x` would **not** serve: its `Ψ₃ = 3X⁴ − 6X² − 1` has no
rational root, so none of its nine `3`-torsion points over `AlgebraicClosure ℚ` can be named without
a genuine algebraic-number argument.  What stays unnameable on `y² + y = x³` too is a *fibre*
witness `P` with `3 • P = T`; that is what `PullbackPrincipalityTwo`'s non-vacuity note is about,
and it is produced existentially by `exists_nsmul_three_eq` and never exhibited. -/

section Nonvacuity

/-- An algebraically closed field of characteristic zero. -/
private abbrev exampleField : Type := AlgebraicClosure ℚ

/-- The curve `y² + y = x³` over `AlgebraicClosure ℚ`, of discriminant `−27`. -/
private noncomputable def exampleCurveThreeAlg : Affine exampleField := ⟨0, 0, 1, 0, 0⟩

private instance : exampleCurveThreeAlg.IsElliptic := by
  rw [WeierstrassCurve.isElliptic_iff, isUnit_iff_ne_zero]
  norm_num [exampleCurveThreeAlg, WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈]

private lemma exampleTwo : (2 : exampleField) ≠ 0 := by norm_num

private lemma exampleThree : (3 : exampleField) ≠ 0 := by norm_num

/-- `T = (0, 0)` lies on `y² + y = x³` and is nonsingular. -/
private lemma exampleNonsingularThreeAlg : exampleCurveThreeAlg.Nonsingular 0 0 :=
  exampleCurveThreeAlg.equation_iff_nonsingular.mp (by
    norm_num [exampleCurveThreeAlg, WeierstrassCurve.Affine.equation_iff])

open Classical in
/-- `T = (0, 0)` is `3`-torsion: `Ψ₃ = 3X⁴ + 3b₆X` vanishes at `0`, and the side condition of
`mem_torsion_three_some_iff` is automatic. -/
private lemma exampleTorsionThreeAlg :
    Point.some (0 : exampleField) 0 exampleNonsingularThreeAlg ∈ exampleCurveThreeAlg.torsion 3 :=
  mem_torsion_three_some_iff'.mpr (by
    norm_num [exampleCurveThreeAlg, WeierstrassCurve.Ψ₃, WeierstrassCurve.b₂,
      WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈])

open Classical in
/-- **The alternating property at `n = 3`, on a curve that exists**, with the torsion point named
and every instance discharged. -/
example : ∃ f : exampleCurveThreeAlg.FunctionField, f ≠ 0 ∧
    exampleCurveThreeAlg.divisorProj f
        = Finsupp.single (some (pointClosedPoint exampleNonsingularThreeAlg.left)) (3 : ℤ)
          - Finsupp.single (none : ProjPoint exampleCurveThreeAlg) (3 : ℤ) ∧
      ∃ g : exampleCurveThreeAlg.FunctionField, g ≠ 0 ∧
        (∃ u : exampleCurveThreeAlg.CoordinateRingˣ,
          (u : exampleCurveThreeAlg.CoordinateRing) • g ^ 3
            = mulByThreeEndo exampleTwo exampleThree f) ∧
        translateEndo exampleNonsingularThreeAlg.left g = g ∧
          weilPairingElt exampleNonsingularThreeAlg.left g = 1 :=
  exists_weilPairingElt_self_eq_one_of_isAlgClosed_three exampleTwo exampleThree
    exampleNonsingularThreeAlg exampleTorsionThreeAlg

open Classical in
/-- **The value-group form, on the same curve**: `weilPairingMu(T, T) = 1` in `μ₃(F̄)`. -/
example : ∃ f : exampleCurveThreeAlg.FunctionField, f ≠ 0 ∧
    exampleCurveThreeAlg.divisorProj f
        = Finsupp.single (some (pointClosedPoint exampleNonsingularThreeAlg.left)) (3 : ℤ)
          - Finsupp.single (none : ProjPoint exampleCurveThreeAlg) (3 : ℤ) ∧
      ∃ g : exampleCurveThreeAlg.FunctionField, g ≠ 0 ∧
        (∃ u : exampleCurveThreeAlg.CoordinateRingˣ,
          (u : exampleCurveThreeAlg.CoordinateRing) • g ^ 3
            = mulByThreeEndo exampleTwo exampleThree f) ∧
        ∃ hpow : weilPairingElt exampleNonsingularThreeAlg.left g ^ 3 = 1,
          weilPairingMu exampleNonsingularThreeAlg.left hpow = 1 :=
  exists_weilPairingMu_self_eq_one_of_isAlgClosed_three exampleTwo exampleThree
    exampleNonsingularThreeAlg exampleTorsionThreeAlg 3

end Nonvacuity

end WeierstrassCurve.Affine
