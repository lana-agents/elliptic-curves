/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import EllipticCurves.FunctionField.MulByThreeFibre
import EllipticCurves.FunctionField.PullbackPrincipalityTwo

/-!
# `hprin` at `n = 3`: `[3]∗((S) − (O))` is principal, and rung 5 unconditionally

`EllipticCurves.FunctionField.PullbackPrincipalityTwo` (`#791`) discharged `exists_gS_two`'s
`hprin` over an algebraically closed base field.  `EllipticCurves.FunctionField.MulByThreeFibre`
(`#819`) supplied the `n = 3` fibre description `[3]∗(S) = ∑_{R ∈ E[3]} (P ⊕ R)`.  This file is the
`n = 3` half of the first: the class-group computation on top of that description, and

```
exists_gS_three_of_isAlgClosed
```

— rung 5 at `n = 3` with **no** carried hypothesis, which is the last rung of `#418`.

## The argument, and how little of it is new

`#791` is three steps.  Only the third is `n`-dependent, and only in one place:

1. **The fibre description.**  `pullbackDivisorThree_single_eq_sum_torsion` applied at `S` and at
   `O` — where `P` may be taken to be `O`, since `projPointOfPoint W 0 = none` — and subtracted:
   `[3]∗((S) − (O)) = ∑_{R ∈ E[3]} ((P ⊕ R) − (R))`.
2. **The affine chart.**  `hprin` is about the affine `divisor W` while the formula above lives in
   `ProjPoint W →₀ ℤ`.  `affinePart` is the passage, and the point at infinity simply drops out.
3. **The class computation.**  `toClass` is an `AddMonoidHom`, so every summand of step 1 has class
   `toClass P`; there are `#E[3] = 9` of them (`card_torsion_three`, an *input*); and
   `9 • P = 3 • (3 • P) = 3 • S = 0` because `S` is `3`-torsion:

   ```
   ∑_R toClass (P ⊕ R) − ∑_R toClass R = 9 • toClass P = toClass (9 • P) = toClass (3 • S) = 0.
   ```

⚠️ **Step 2 is not transposed here — it is consumed.**  `affinePart`, `affinePart_single_none`,
`affinePart_divisorProj`, `pointDivisorAff`, `classOfDivisor_pointDivisorAff`, `classOfDivisor_sub`
and `classOfDivisor_sum` all live in `PullbackPrincipalityTwo` and **none of them mentions `[2]`**:
they are facts about the affine chart of a projective divisor, about the class of a rational
point's divisor, and about `classOfDivisor` over an arbitrary Dedekind domain.  That is why this
file imports the `n = 2` one, and why it is a fraction of its length.

> ⚠️ **The reusable observation, since this board has now priced three `n = 3` rungs by analogy
> and been wrong twice about which analogy applies.**  What made this rung cheap is *not* "the `[3]`
> proof mirrors the `[2]` proof".  It is that **most of the `[2]` file was never about `[2]`.**
> Those are different claims and only the second is checkable in advance — by reading signatures for
> `h2`, `mulByTwoEndo` and `E[2]`, which costs minutes.  Do that before pricing the next one.

⚠️ **Moving the seven general lemmas to an earlier module would be tidier and is deliberately not
done**: it edits a merged file for no mathematical gain.  `EllipticCurves.Torsion.TriplingCoords`,
`EllipticCurves.FunctionField.MulByThreePlacePullback` and
`EllipticCurves.FunctionField.MulByThreeFibre` each declined the same trade.

## Main statements

* `WeierstrassCurve.Affine.pullbackDivisorThree_single_sub_single_eq_sum_torsion` — step 1;
* `WeierstrassCurve.Affine.affinePart_pullbackDivisorThree_single_sub_single` — on the chart;
* **`WeierstrassCurve.Affine.classOfDivisor_affinePart_pullbackDivisorThree_eq_one`** — step 3, the
  heart;
* `WeierstrassCurve.Affine.exists_divisor_eq_affinePart_pullbackDivisorThree` — the vanishing class
  turned back into a generator by `#726`'s principality criterion;
* `WeierstrassCurve.Affine.exists_nsmul_divisor_eq_divisor_mulByThreeEndo` — **`hprin`**, in the
  shape `exists_gS_three` consumes it;
* **`WeierstrassCurve.Affine.exists_gS_three_of_isAlgClosed`** — rung 5 at `n = 3`, unconditional.

⚠️ `exists_nsmul_divisor_eq_divisor_mulByThreeEndo` quantifies over **every** nonzero `f` with
`divisor W f = 3·(S)`, not only over the generator `#409` produces, so its proof must first know
that the affine divisor pins the projective one.  It does — `ordInfty_eq_of_divisor_eq` compares `f`
with that generator at infinity and `divisorProj_eq_iff` assembles the two halves — and all three
inputs are `n`-agnostic and merged.

## Scope

⚠️ **`[IsAlgClosed F]` is load-bearing and enters twice, independently**, exactly as at `n = 2`:
through `exists_nsmul_three_eq` (surjectivity of `[3]` on points,
`EllipticCurves.Torsion.TriplingSurjective`) and through `MulByThreeFibre`'s coset description.
Over a general field `hprin` at `n = 3` is still open, and `exists_gS_three`
(`EllipticCurves.FunctionField.NthRootOfPullback`) keeps its general-field form, untouched.

⚠️ **No step divides a divisor by `3`.**  `n · D` principal does **not** imply `D` principal — that
failure *is* the `n`-torsion of the class group the Weil pairing measures — and the argument here
exhibits the class of `D` as trivial directly.  `#791` carries the identical warning at `n = 2`.

⚠️ **Nothing here says `#E[3] = 9`.**  `card_torsion_three`
(`EllipticCurves.Torsion.ThreeTorsionStructure`) is an *input* to step 3, exactly as
`card_torsion_two` is at `n = 2`.  The link from a field degree to a kernel count is still
"a separable isogeny has `#ker = deg`", which no file in this tree contains.

## What is *not* here

* The rung-6 corollaries this unblocks: a nothing-carried `n = 3` Galois-equivariance
  (`EllipticCurves.FunctionField.WeilPairingGaloisRoot`'s `weilPairingElt_galois_of_gS_three` needs
  one corollary, `#456`) and the instantiation of
  `EllipticCurves.FunctionField.WeilPairingAlternatingThree`.  Both are now mechanical and neither
  is done here.
* Non-degeneracy at `n = 3`, and `#465` deliverable 2.  ⚠️ The alternating property's obstruction
  is the **translation** slot, not `hprin`: `translateEndo` is not
  `IsFractionRing.ringEquivOfRingEquiv` for any ring automorphism of `F[W⁄F]`, and nothing here
  touches that.
* General `n`.  `mulByNEndo` does not exist and `#404`'s `ωₙ` is untouched.

## References

* [J. H. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.8 (the function `g_P`
  with `g_P ^ n = f_P ∘ [n]`), III.3.4 (the group law is the class-group map).
-/

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum

namespace WeierstrassCurve.Affine

open CoordinateRing

variable {F : Type*} [Field F] {W : Affine F} [IsDedekindDomain W.CoordinateRing]

section IsAlgClosed

variable [DecidableEq F] [W.IsElliptic] [IsAlgClosed F]

/-- **`[3]∗((S) − (O)) = ∑_{R ∈ E[3]} ((P ⊕ R) − (R))`.** -/
theorem pullbackDivisorThree_single_sub_single_eq_sum_torsion [Fintype (W.torsion 3)]
    (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) {S P : W.Point} (hP : (3 : ℕ) • P = S) :
    pullbackDivisorThree h2 h3 (Finsupp.single (projPointOfPoint W S) (1 : ℤ)
        - Finsupp.single (none : ProjPoint W) (1 : ℤ))
      = ∑ R : W.torsion 3, (Finsupp.single (projPointOfPoint W (P + R)) (1 : ℤ)
          - Finsupp.single (projPointOfPoint W (R : W.Point)) (1 : ℤ)) := by
  have hO : (none : ProjPoint W) = projPointOfPoint W 0 := rfl
  rw [map_sub, pullbackDivisorThree_single_eq_sum_torsion h2 h3 hP, hO,
    pullbackDivisorThree_single_eq_sum_torsion h2 h3 (smul_zero (3 : ℕ)),
    ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun R _ => by rw [zero_add]

/-- The same formula on the affine chart, where `hprin` lives. -/
theorem affinePart_pullbackDivisorThree_single_sub_single [Fintype (W.torsion 3)]
    (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) {S P : W.Point} (hP : (3 : ℕ) • P = S) :
    affinePart W (pullbackDivisorThree h2 h3 (Finsupp.single (projPointOfPoint W S) (1 : ℤ)
        - Finsupp.single (none : ProjPoint W) (1 : ℤ)))
      = ∑ R : W.torsion 3, (pointDivisorAff W (P + R) - pointDivisorAff W (R : W.Point)) := by
  rw [pullbackDivisorThree_single_sub_single_eq_sum_torsion h2 h3 hP, map_sum]
  exact Finset.sum_congr rfl fun R _ => map_sub _ _ _

/-- **The class-group computation.** -/
theorem classOfDivisor_affinePart_pullbackDivisorThree_eq_one (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0)
    {S P : W.Point} (hP : (3 : ℕ) • P = S) (hS : (3 : ℕ) • S = 0) :
    classOfDivisor W.FunctionField (affinePart W (pullbackDivisorThree h2 h3
        (Finsupp.single (projPointOfPoint W S) (1 : ℤ)
          - Finsupp.single (none : ProjPoint W) (1 : ℤ)))) = 1 := by
  classical
  haveI := W.finite_torsion_three h3
  haveI : Fintype (W.torsion 3) := Fintype.ofFinite _
  have hP9 : (9 : ℕ) • P = 0 := by
    rw [show (9 : ℕ) = 3 * 3 by norm_num, mul_smul, hP, hS]
  have hterm : ∀ R ∈ (Finset.univ : Finset (W.torsion 3)),
      classOfDivisor W.FunctionField (pointDivisorAff W (P + R) - pointDivisorAff W (R : W.Point))
        = Additive.toMul (Point.toClass P) := by
    intro R _
    rw [classOfDivisor_sub, classOfDivisor_pointDivisorAff, classOfDivisor_pointDivisorAff,
      map_add, toMul_add, mul_div_cancel_right]
  have hcard : Fintype.card (W.torsion 3) = 9 := by
    rw [← Nat.card_eq_fintype_card, card_torsion_three h2 h3]
  rw [affinePart_pullbackDivisorThree_single_sub_single h2 h3 hP, classOfDivisor_sum,
    Finset.prod_congr rfl hterm, Finset.prod_const, Finset.card_univ, hcard, ← toMul_nsmul,
    ← map_nsmul, hP9, Point.toClass_zero]
  rfl

/-- **`[3]∗((S) − (O))` is principal on the affine chart.** -/
theorem exists_divisor_eq_affinePart_pullbackDivisorThree (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0)
    {S P : W.Point} (hP : (3 : ℕ) • P = S) (hS : (3 : ℕ) • S = 0) :
    ∃ g : W.FunctionField, g ≠ 0 ∧ divisor W g = affinePart W (pullbackDivisorThree h2 h3
      (Finsupp.single (projPointOfPoint W S) (1 : ℤ)
        - Finsupp.single (none : ProjPoint W) (1 : ℤ))) :=
  (exists_divisor_eq_iff_classOfDivisor_eq_one _).2
    (classOfDivisor_affinePart_pullbackDivisorThree_eq_one h2 h3 hP hS)

/-- **`hprin`, in the shape `exists_gS_three` consumes it.** -/
theorem exists_nsmul_divisor_eq_divisor_mulByThreeEndo (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0)
    {x y : F} (h : W.Nonsingular x y) (hS : Point.some x y h ∈ W.torsion 3)
    {f : W.FunctionField} (hf : f ≠ 0)
    (hfdiv : divisor W f = Finsupp.single (pointClosedPoint h.left) (3 : ℤ)) :
    ∃ g₀ : W.FunctionField, g₀ ≠ 0 ∧
      3 • divisor W g₀ = divisor W (mulByThreeEndo h2 h3 f) := by
  classical
  obtain ⟨P, hP⟩ := exists_nsmul_three_eq h2 (Point.some x y h)
  obtain ⟨g, hg, hgdiv⟩ :=
    exists_divisor_eq_affinePart_pullbackDivisorThree h2 h3 hP (mem_torsion_iff.mp hS)
  refine ⟨g, hg, ?_⟩
  obtain ⟨f₀, hf₀, hproj₀⟩ := divisorProj_eq_single_sub_single_of_torsion h hS
  have hd₀ : divisor W f₀ = Finsupp.single (pointClosedPoint h.left) (3 : ℤ) := by
    ext v
    have hv := congrArg (fun D => D (some v)) hproj₀
    simpa [Finsupp.single_apply] using hv
  have hfe : divisor W f = divisor W f₀ := hfdiv.trans hd₀.symm
  have hprojf : divisorProj W f = divisorProj W f₀ :=
    divisorProj_eq_iff.2 ⟨hfe, ordInfty_eq_of_divisor_eq hf hf₀ hfe⟩
  have hkey : divisorProj W (mulByThreeEndo h2 h3 f)
      = (3 : ℤ) • pullbackDivisorThree h2 h3
          (Finsupp.single (projPointOfPoint W (Point.some x y h)) (1 : ℤ)
            - Finsupp.single (none : ProjPoint W) (1 : ℤ)) := by
    rw [divisorProj_mulByThreeEndo h2 h3 hf, hprojf, hproj₀, ← map_zsmul]
    congr 1
    rw [smul_sub, Finsupp.smul_single, Finsupp.smul_single, smul_eq_mul, mul_one,
      projPointOfPoint_some]
    norm_num
  have hdiv3 : divisor W (mulByThreeEndo h2 h3 f) = (3 : ℤ) • affinePart W
      (pullbackDivisorThree h2 h3
        (Finsupp.single (projPointOfPoint W (Point.some x y h)) (1 : ℤ)
          - Finsupp.single (none : ProjPoint W) (1 : ℤ))) := by
    rw [← affinePart_divisorProj, hkey, map_zsmul]
  rw [hdiv3, hgdiv]
  exact (Nat.cast_smul_eq_nsmul ℤ 3 _).symm

/-- **Rung 5 of the Weil pairing at `n = 3`, unconditionally.** -/
theorem exists_gS_three_of_isAlgClosed (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) {x y : F}
    (h : W.Nonsingular x y) (hS : Point.some x y h ∈ W.torsion 3) :
    ∃ f : W.FunctionField, f ≠ 0 ∧
      divisor W f = Finsupp.single (pointClosedPoint h.left) (3 : ℤ) ∧
      ∃ gS : W.FunctionField, gS ≠ 0 ∧
        ∃ u : W.CoordinateRingˣ, (u : W.CoordinateRing) • gS ^ 3 = mulByThreeEndo h2 h3 f :=
  exists_gS_three h2 h3 h hS fun _ hf hfdiv =>
    exists_nsmul_divisor_eq_divisor_mulByThreeEndo h2 h3 h hS hf hfdiv

end IsAlgClosed

section Nonvacuity

/-- An algebraically closed field of characteristic zero. -/
private abbrev exampleField : Type := AlgebraicClosure ℚ

/-- The curve `y² + y = x³` over `AlgebraicClosure ℚ`, of discriminant `-27`. -/
private noncomputable def exampleCurve : Affine exampleField := ⟨0, 0, 1, 0, 0⟩

private instance : exampleCurve.IsElliptic := by
  rw [WeierstrassCurve.isElliptic_iff, isUnit_iff_ne_zero]
  norm_num [exampleCurve, WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈]

private lemma exampleTwo : (2 : exampleField) ≠ 0 := by norm_num

private lemma exampleThree : (3 : exampleField) ≠ 0 := by norm_num

/-- `S = (0, 0)` lies on `y² + y = x³` and is nonsingular. -/
private lemma exampleNonsingular : exampleCurve.Nonsingular 0 0 :=
  exampleCurve.equation_iff_nonsingular.mp (by
    norm_num [exampleCurve, WeierstrassCurve.Affine.equation_iff])

/-- `S = (0, 0)` is not `2`-torsion: `negY 0 0 = -1`. -/
private lemma exampleNegY : (0 : exampleField) ≠ exampleCurve.negY 0 0 := by
  norm_num [exampleCurve, WeierstrassCurve.Affine.negY]

/-- `Ψ₃ = 3X⁴ + 3X` on this curve, so `Ψ₃(0) = 0`. -/
private lemma examplePsiThree : exampleCurve.Ψ₃.eval 0 = 0 := by
  norm_num [exampleCurve, WeierstrassCurve.Ψ₃, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈]

open Classical in
/-- `S = (0, 0)` is `3`-torsion. -/
private lemma exampleTorsion :
    Point.some (0 : exampleField) 0 exampleNonsingular ∈ exampleCurve.torsion 3 :=
  (mem_torsion_three_some_iff exampleNegY).mpr examplePsiThree

open Classical in
/-- **The principality, on a curve that exists.** -/
example (P : exampleCurve.Point)
    (hP : (3 : ℕ) • P = Point.some (0 : exampleField) 0 exampleNonsingular) :
    ∃ g : exampleCurve.FunctionField, g ≠ 0 ∧ exampleCurve.divisor g
      = affinePart exampleCurve (pullbackDivisorThree exampleTwo exampleThree
        (Finsupp.single (projPointOfPoint exampleCurve
            (Point.some (0 : exampleField) 0 exampleNonsingular)) (1 : ℤ)
          - Finsupp.single (none : ProjPoint exampleCurve) (1 : ℤ))) :=
  exists_divisor_eq_affinePart_pullbackDivisorThree exampleTwo exampleThree hP
    (mem_torsion_iff.mp exampleTorsion)

open Classical in
/-- **The headline, committed**: rung 5 at `n = 3` with no `hprin`, on a genuine curve with a named
`3`-torsion point. -/
example : ∃ f : exampleCurve.FunctionField, f ≠ 0 ∧
    exampleCurve.divisor f
      = Finsupp.single (pointClosedPoint exampleNonsingular.left) (3 : ℤ) ∧
    ∃ gS : exampleCurve.FunctionField, gS ≠ 0 ∧
      ∃ u : exampleCurve.CoordinateRingˣ,
        (u : exampleCurve.CoordinateRing) • gS ^ 3
          = mulByThreeEndo exampleTwo exampleThree f :=
  exists_gS_three_of_isAlgClosed exampleTwo exampleThree exampleNonsingular exampleTorsion

end Nonvacuity

end WeierstrassCurve.Affine
