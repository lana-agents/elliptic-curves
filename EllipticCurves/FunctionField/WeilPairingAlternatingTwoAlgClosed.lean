/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import EllipticCurves.FunctionField.PullbackPrincipalityTwo
import EllipticCurves.FunctionField.WeilPairingAlternatingMu
import EllipticCurves.FunctionField.WeilPairingAlternatingTwo

/-!
# The alternating property at `n = 2` over an algebraically closed field, unconditionally

Silverman *AEC* III.8.1(d): the Weil pairing is alternating, `e_n(T, T) = 1`.

`EllipticCurves.FunctionField.WeilPairingAlternatingTwo` proves this at `n = 2` over an
algebraically closed field, and says in its own docstring that it does so with exactly one gated
hypothesis: `hprin`, the principality of `[2]∗((T) − (O))`, in the shape `exists_gS_two` takes it.
`EllipticCurves.FunctionField.PullbackPrincipalityTwo` discharged that hypothesis.  This file is the
composition, and it is the whole content of the file: **nothing new is proved here about curves.**

The two shapes match argument for argument, so the discharge is a single application — the
hypothesis of `exists_weilPairingElt_self_eq_one_of_algClosed` is literally the conclusion of
`exists_nsmul_divisor_eq_divisor_mulByTwoEndo`, universally quantified over the same `f`.

## Main statements

* `WeierstrassCurve.Affine.exists_weilPairingElt_self_eq_one_of_isAlgClosed` — the alternating
  property in `F(W)`: for a nonsingular affine `2`-torsion `T` there are a function `f_T` with
  projective divisor `2(T) − 2(O)`, a square root `g_T` of `[2]∗ f_T` up to a unit of `F[W]`, and
  the conclusions `τ_T∗ g_T = g_T` and `e_2(T, T) = 1`.
* `WeierstrassCurve.Affine.exists_weilPairingMu_self_eq_one_of_isAlgClosed` — the same in the value
  group: `weilPairingMu(T, T) = 1` in `μ_n(F)`, for every `n` with `[NeZero n]`.  The
  root-of-unity datum `hpow` that `weilPairingMu` is indexed by costs nothing here, because the
  statement above already gives `e_2(T, T) = 1`.

Both are certified on `y² = x³ − x` over `AlgebraicClosure ℚ` with the `2`-torsion point named as
`(0, 0)` — see the non-vacuity section, which is the first full instantiation this front's
alternating files have been able to write.

## Scope

⚠️ **`n = 2` only, and the `n = 3` version is no longer gated — only unassembled.**
`WeilPairingAlternatingThree`'s `exists_weilPairingElt_self_eq_one_of_algClosed_three` still
carries `hprin` in its own signature, and nothing *here* helps it, because the discharge consumed
here runs through `PullbackPrincipalityTwo`'s class computation, whose count `4` is the order of
`E[2]`.  But its `n = 3` counterpart exists:
`EllipticCurves.FunctionField.PullbackPrincipalityThree`'s
`exists_nsmul_divisor_eq_divisor_mulByThreeEndo` is exactly that `hprin`, so the `n = 3` analogue
of this file is an instantiation and not a research step.  ⚠️ It is *not* performed anywhere in
this tree; do not read the availability of the input as the existence of the statement.

⚠️ **`[IsAlgClosed F]` is load-bearing and enters twice, independently.**  Once through the
discharge (`PullbackPrincipalityTwo`, itself through the surjectivity of `[2]` on points and
through the fibre description of `[2]∗`), and once through `exists_equation_nsmul_two_eq`, which is
how `WeilPairingAlternatingTwo` obtains the point `P` with `[2]P = T` that its second product
translates by.  Removing either is not a matter of restating anything here.  A theorem that
discharges a hypothesis inherits the hypotheses of its *proof*, not those of the statement it
discharges, which is why this file exists rather than an edit to `WeilPairingAlternatingTwo` —
whose conditional statement is unchanged, so that a future general-field discharge has somewhere to
land.

⚠️ **`[IsDedekindDomain W.CoordinateRing]` is not a hypothesis of anything here.**  It is a global
instance for `[W.IsElliptic]` over an **arbitrary** field
(`EllipticCurves.FunctionField.CoordinateRingNormalGeneral`), so it neither appears in the variable
block nor contributes to the `[IsAlgClosed F]` accounting above.

⚠️ **The statements below are pinned to `Classical.propDecidable`.**  `open Classical in` is
required and not a formality: they mention `W.torsion 2`, whose `DecidableEq F` instance has to
agree with the one baked into `TorsionTwoMul` and into the statements they consume.  The cost is
that a consumer whose own variable block carries `[DecidableEq F]` cannot apply them directly; the
bridge is `obtain rfl : ‹DecidableEq F› = (fun a b => Classical.propDecidable (a = b)) :=
Subsingleton.elim _ _`.

⚠️ **This is not antisymmetry.**  `weilPairingElt_mul_swap_eq_one`
(`WeilPairingAntisymmetric`) consumes the alternating property at three points, which this file now
supplies unconditionally over `F̄` — but it also needs the product relation
`g_{S ⊕ T} = g_S · g_T · w` as the hypothesis `hprod`, which is rung-4/5 gated (`#414`/`#418`) and
which nothing here touches.  Nor is this bilinearity, Galois-equivariance (`#456`), general `n`, or
non-degeneracy (`#796`, merged at `n = 2` over `F̄`).  It says nothing about `#E[n] = n²` at general
`n` (`#242`, Ward).

## References

* [J. H. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.8, Prop. 8.1(d).
-/

namespace WeierstrassCurve.Affine

open CoordinateRing

variable {F : Type*} [Field F] {W : Affine F}

section AlgClosed

variable [W.IsElliptic] [IsAlgClosed F] {x₂ y₂ : F}

open Classical in
/-- **`e_2(T, T) = 1` over an algebraically closed field, with no hypothesis beyond the setting.**

For a nonsingular affine `2`-torsion point `T = (x₂, y₂)` there are a nonzero `f_T` whose projective
divisor is `2(T) − 2(O)` and a nonzero `g_T` with `u · g_T ^ 2 = [2]∗ f_T` for a unit `u` of `F[W]`,
such that the translation `τ_T∗` fixes `g_T` — hence `e_2(T, T) = 1`.

`exists_weilPairingElt_self_eq_one_of_algClosed` (`WeilPairingAlternatingTwo`) is this statement
with the principality of `[2]∗((T) − (O))` carried as the hypothesis `hprin`, and
`exists_nsmul_divisor_eq_divisor_mulByTwoEndo` (`PullbackPrincipalityTwo`) is exactly that
hypothesis, proved.  The two compose with nothing in between. -/
theorem exists_weilPairingElt_self_eq_one_of_isAlgClosed (h2 : (2 : F) ≠ 0)
    (h : W.Nonsingular x₂ y₂) (htors : Point.some x₂ y₂ h ∈ W.torsion 2) :
    ∃ f : W.FunctionField, f ≠ 0 ∧
      divisorProj W f = Finsupp.single (some (pointClosedPoint h.left)) (2 : ℤ)
          - Finsupp.single (none : ProjPoint W) (2 : ℤ) ∧
        ∃ g : W.FunctionField, g ≠ 0 ∧
          (∃ u : W.CoordinateRingˣ, (u : W.CoordinateRing) • g ^ 2 = mulByTwoEndo h2 f) ∧
          translateEndo h.left g = g ∧ weilPairingElt h.left g = 1 :=
  exists_weilPairingElt_self_eq_one_of_algClosed h2 h htors fun _ hf hfdiv =>
    exists_nsmul_divisor_eq_divisor_mulByTwoEndo h2 h htors hf hfdiv

open Classical in
/-- **The alternating property at `n = 2` in the value group**: `weilPairingMu(T, T) = 1` in
`μ_n(F)`, over an algebraically closed field and with no hypothesis beyond the setting.

`weilPairingMu` is indexed by a proof `hpow` that the pairing element is an `n`-th root of unity, so
the statement produces one; it costs nothing, since the previous theorem already gives
`e_2(T, T) = 1` and `1 ^ n = 1`.  The `n` is arbitrary for the same reason — this is the group
identity of `μ_n(F)` for whichever `n` the caller has packaged the value in, not a claim that
`e_2` lands in `μ_n` for `n ≠ 2`.

The `μ_n`-level reduction is `weilPairingMu_self_of_translateEndo_fixed`
(`WeilPairingAlternatingMu`), whose own hypothesis is the translation-invariance that the previous
theorem supplies. -/
theorem exists_weilPairingMu_self_eq_one_of_isAlgClosed (h2 : (2 : F) ≠ 0)
    (h : W.Nonsingular x₂ y₂) (htors : Point.some x₂ y₂ h ∈ W.torsion 2) (n : ℕ) [NeZero n] :
    ∃ f : W.FunctionField, f ≠ 0 ∧
      divisorProj W f = Finsupp.single (some (pointClosedPoint h.left)) (2 : ℤ)
          - Finsupp.single (none : ProjPoint W) (2 : ℤ) ∧
        ∃ g : W.FunctionField, g ≠ 0 ∧
          (∃ u : W.CoordinateRingˣ, (u : W.CoordinateRing) • g ^ 2 = mulByTwoEndo h2 f) ∧
          ∃ hpow : weilPairingElt h.left g ^ n = 1, weilPairingMu h.left hpow = 1 := by
  obtain ⟨f, hf, hdivproj, g, hg, hu, htinv, halt⟩ :=
    exists_weilPairingElt_self_eq_one_of_isAlgClosed h2 h htors
  exact ⟨f, hf, hdivproj, g, hg, hu, by rw [halt, one_pow],
    weilPairingMu_self_of_translateEndo_fixed h.left hg _ htinv⟩

end AlgClosed

/-! ### Non-vacuity

`WeilPairingAlternatingTwo`'s own non-vacuity section could only certify that the hypotheses of its
headline are simultaneously satisfiable, because `hprin` was open.  It is open no longer, so the
statements above are certified outright: `y² = x³ − x` over `AlgebraicClosure ℚ` is elliptic, the
base field is algebraically closed of characteristic `≠ 2`, and the `2`-torsion point is **named**
as `(0, 0)`.  Unlike at `n = 3`, where `[IsAlgClosed F]` makes the count provable and the witness
unnameable, at `n = 2` the witness is nameable over `ℚ` already. -/

section Nonvacuity

/-- An algebraically closed field of characteristic zero. -/
private abbrev exampleField : Type := AlgebraicClosure ℚ

/-- The curve `y² = x³ − x` over `AlgebraicClosure ℚ`, of discriminant `64`. -/
private noncomputable def exampleCurve : Affine exampleField := ⟨0, 0, 0, -1, 0⟩

private instance : exampleCurve.IsElliptic := by
  rw [WeierstrassCurve.isElliptic_iff, isUnit_iff_ne_zero]
  norm_num [exampleCurve, WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈]

private lemma exampleTwo : (2 : exampleField) ≠ 0 := by norm_num

/-- `T = (0, 0)` lies on `y² = x³ − x` and is nonsingular. -/
private lemma exampleNonsingular : exampleCurve.Nonsingular 0 0 :=
  exampleCurve.equation_iff_nonsingular.mp (by
    norm_num [exampleCurve, WeierstrassCurve.Affine.equation_iff])

open Classical in
/-- `T = (0, 0)` is `2`-torsion: `2y + a₁x + a₃ = 0` reads `0 = 0`. -/
private lemma exampleTorsion :
    Point.some (0 : exampleField) 0 exampleNonsingular ∈ exampleCurve.torsion 2 :=
  (mem_torsion_two_some_iff exampleNonsingular).mpr (by norm_num [exampleCurve])

open Classical in
/-- **The alternating property at `n = 2`, on a curve that exists**, with the torsion point named
and every instance discharged. -/
example : ∃ f : exampleCurve.FunctionField, f ≠ 0 ∧
    exampleCurve.divisorProj f
        = Finsupp.single (some (pointClosedPoint exampleNonsingular.left)) (2 : ℤ)
          - Finsupp.single (none : ProjPoint exampleCurve) (2 : ℤ) ∧
      ∃ g : exampleCurve.FunctionField, g ≠ 0 ∧
        (∃ u : exampleCurve.CoordinateRingˣ,
          (u : exampleCurve.CoordinateRing) • g ^ 2 = mulByTwoEndo exampleTwo f) ∧
        translateEndo exampleNonsingular.left g = g ∧
          weilPairingElt exampleNonsingular.left g = 1 :=
  exists_weilPairingElt_self_eq_one_of_isAlgClosed exampleTwo exampleNonsingular exampleTorsion

open Classical in
/-- **The value-group form, on the same curve**: `weilPairingMu(T, T) = 1` in `μ₂(F̄)`. -/
example : ∃ f : exampleCurve.FunctionField, f ≠ 0 ∧
    exampleCurve.divisorProj f
        = Finsupp.single (some (pointClosedPoint exampleNonsingular.left)) (2 : ℤ)
          - Finsupp.single (none : ProjPoint exampleCurve) (2 : ℤ) ∧
      ∃ g : exampleCurve.FunctionField, g ≠ 0 ∧
        (∃ u : exampleCurve.CoordinateRingˣ,
          (u : exampleCurve.CoordinateRing) • g ^ 2 = mulByTwoEndo exampleTwo f) ∧
        ∃ hpow : weilPairingElt exampleNonsingular.left g ^ 2 = 1,
          weilPairingMu exampleNonsingular.left hpow = 1 :=
  exists_weilPairingMu_self_eq_one_of_isAlgClosed exampleTwo exampleNonsingular exampleTorsion 2

end Nonvacuity

end WeierstrassCurve.Affine
