/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import EllipticCurves.Fixtures
import EllipticCurves.FunctionField.MulByThreeFibre
import EllipticCurves.FunctionField.PullbackPrincipalityTwo

/-!
# `[3]∗((S) − (O))` is principal, and rung 5 at `n = 3` loses its hypothesis

Rung 5 of the divisor-theoretic Weil pairing (Silverman AEC III.8) produces, from the principal
function `f_S` of an `n`-torsion point `S`, an `n`-th root `g_S` of `f_S ∘ [n]`.  It is merged
(`EllipticCurves.FunctionField.NthRootOfPullback`, `#418`) but **conditionally**: `exists_gS_three`
carries an explicit hypothesis `hprin` saying that the effective divisor `D` with
`3 · D = div (f_S ∘ [3])` is *principal*.  That hypothesis is not formal — `n · D` principal does
**not** imply `D` principal, and the failure is exactly the `n`-torsion of the class group the Weil
pairing measures.

`EllipticCurves.FunctionField.PullbackPrincipalityTwo` (`#791`) discharged it at `n = 2`.  This
file discharges it at `n = 3`, over an algebraically closed base field, and with it the `n = 3`
half of `#418`.

## The argument, and where each input comes from

Let `S` be a nonsingular affine `3`-torsion point and pick `P` with `3 • P = S`
(`exists_nsmul_three_eq`, `EllipticCurves.Torsion.TriplingSurjective`: `[3]` is surjective on
`E(F̄)`).

1. **The fibre description**, `#819`: `[3]∗(S) = ∑_{R ∈ E[3]} (P ⊕ R)`
   (`pullbackDivisorThree_single_eq_sum_torsion`, `EllipticCurves.FunctionField.MulByThreeFibre`).
   Applying it once at `S` and once at `O` — where `P` may be taken to be `O`, since
   `projPointOfPoint W 0 = none` — and subtracting gives

   ```
   [3]∗((S) − (O)) = ∑_{R ∈ E[3]} ((P ⊕ R) − (R)).
   ```

2. **The affine part.**  `hprin` is a statement about the affine `divisor W`, while the formula
   above lives in `ProjPoint W →₀ ℤ`.  `affinePart` is the passage, and it is `[2]`-free: it and
   `pointDivisorAff` and `classOfDivisor_pointDivisorAff` are consumed from
   `PullbackPrincipalityTwo` unchanged (see below).

3. **The class computation.**  Every summand has class `toClass P`, there are `#E[3] = 9` of them,
   and the product telescopes:

   ```
   ∑_R toClass (P ⊕ R) − ∑_R toClass R = 9 • toClass P = toClass (9 • P) = toClass (3 • S) = 0.
   ```

   `#726`'s `exists_divisor_eq_iff_classOfDivisor_eq_one` turns that vanishing class back into an
   actual generator.  ⚠️ **No step divides a divisor by `3`.**

4. **`hprin`'s `∀`-form.**  `exists_gS_three` quantifies over *every* `f ≠ 0` with
   `divisor W f = 3·(S)`, not only over the generator `#409` produces.  The gap closes because the
   affine divisor pins the projective one: `ordInfty_eq_of_divisor_eq` against
   `divisorProj_eq_single_sub_single_of_torsion` — which is already general in `n` — and then
   `divisorProj_eq_iff`.

## Why this file imports the `n = 2` one

`PullbackPrincipalityTwo` proves `classOfDivisor_sub` and `classOfDivisor_sum` for an arbitrary
Dedekind domain, and defines `affinePart` (with `affinePart_apply`, `affinePart_single_some`,
`affinePart_single_none`, `affinePart_divisorProj`) and `pointDivisorAff` (with
`pointDivisorAff_zero`, `pointDivisorAff_some`, `classOfDivisor_pointDivisorAff`).  All eleven are
**`[2]`-free**: facts about `Finsupp.comapDomain` along `some`, about the class of a rational
point's affine divisor, and about an arbitrary Dedekind domain.  They are consumed unchanged rather
than re-proved.

⚠️ Moving them to an earlier module would be tidier and is **deliberately not done**: it edits a
merged file for no mathematical gain.  `EllipticCurves.Torsion.TriplingCoords`,
`EllipticCurves.FunctionField.MulByThreePlacePullback` and
`EllipticCurves.FunctionField.MulByThreeFibre` each declined the same trade, and the last of those
declined it for `MulByTwoFibreAffine`'s seven lemmas one layer down.

## What the `n = 3` layer actually costs

Deliverables 1–4 below are the `n = 2` proofs with `2 ↦ 3`, and the two places where that is *not*
true are worth naming, because both are hypothesis bookkeeping rather than mathematics:

* `card_torsion_three` needs **both** `(2 : F) ≠ 0` and `(3 : F) ≠ 0`, where `card_torsion_two`
  needs only the former.  So the class computation carries `h3` even though nothing in the divisor
  algebra does.
* `exists_nsmul_three_eq` needs **only** `(2 : F) ≠ 0` — the surjectivity of `[3]` on `E(F̄)` goes
  through the tangent slope of a doubling, not through `3`.  Do not thread an `h3` into it.

And one genuine difference: the `n = 2` proof closes `2 • divisor W g = (2 : ℤ) • divisor W g` with
`two_nsmul` and `two_zsmul`, both of which unfold to `a + a`.  There is no such pair at `3`
(`three'_nsmul` is `a + a + a` and has no `zsmul` twin), so the closer here is `natCast_zsmul`,
which is the general statement and would have served at `n = 2` too.

## Main statements

* `WeierstrassCurve.Affine.pullbackDivisorThree_single_sub_single_eq_sum_torsion` —
  `[3]∗((S) − (O)) = ∑_{R ∈ E[3]} ((P ⊕ R) − (R))`.
* `WeierstrassCurve.Affine.affinePart_pullbackDivisorThree_single_sub_single` — the same on the
  affine chart.
* `WeierstrassCurve.Affine.classOfDivisor_affinePart_pullbackDivisorThree_eq_one` — the class of
  that divisor is trivial.
* `WeierstrassCurve.Affine.exists_divisor_eq_affinePart_pullbackDivisorThree` — **the
  principality**.
* `WeierstrassCurve.Affine.exists_nsmul_divisor_eq_divisor_mulByThreeEndo` — `hprin` itself, in the
  shape `exists_gS_three` consumes.
* **`WeierstrassCurve.Affine.exists_gS_three_of_isAlgClosed`** — rung 5 at `n = 3` with no
  hypothesis left: a nonzero `g_S` with `u · g_S ^ 3 = [3]∗ f_S`.

## Scope

⚠️ **This is not the Weil pairing.**  Rung 6 (`#419`, `#465`, `#456`) and the non-degeneracy of
`e_n` are untouched; `EllipticCurves.FunctionField.WeilPairing` holds the canonical account of what
non-degeneracy consumes and this file does not restate it.  What lands here is the *last* gated
input at `n = 3`, not the pairing.

⚠️ **The hypotheses are strictly stronger than `exists_gS_three`'s.**  Everything below carries
`[IsAlgClosed F]` and `[W.IsElliptic]`, which `exists_gS_three` — stated over an arbitrary field
with `[IsDedekindDomain W.CoordinateRing]` — does not.  Two separate inputs need the algebraically
closed base: the surjectivity of `[3]` on points and `#819`'s fibre description.  **Over a general
field `hprin` is still open at both `n`**, and this file says nothing about it.

⚠️ **Nothing here says `#E[n] = n²` at general `n`.**  `card_torsion_three` is an *input*, it is
`[3]`-specific, and it does not go through Ward.  Nor does anything here say that `∑ e_p = 9` is a
count of points: that passage runs through "a separable isogeny has `#ker = deg`", which no file in
this tree contains.

⚠️ **General `n` is untouched *here*.**  ⚠️ **The clause this paragraph used to carry has been
paid** — it read *"`mulByNEndo` does not exist; `[2]∗` and `[3]∗` are the two concrete
endomorphisms this tree has"*.  `[n]∗` at every `n` is `mulByNEndo`,
`EllipticCurves.FunctionField.MulByNPullback`, built from the **group law**, and its divisor
pullback is `pullbackDivisorN` (`EllipticCurves.FunctionField.MulByNPlacePullback`).  ⚠️ The
principality of `[n]∗((S) − (O))` is a different statement from either of those and is not
approached here, and `#404`'s general `ωₙ` is untouched.

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

/-! ### `[3]∗((S) − (O))` and its class -/

/-- **The `n = 3` form of the formula rung 5 has been quoting in prose since `#765`**:

```
[3]∗((S) − (O)) = ∑_{R ∈ E[3]} ((P ⊕ R) − (R))
```

for any `P` with `3 • P = S`.  `pullbackDivisorThree` is an `AddMonoidHom`, so `map_sub` splits the
left-hand side; `#819`'s `pullbackDivisorThree_single_eq_sum_torsion` handles the `(S)` half, and
the **same theorem at `S = O` with `P = O`** handles the `(O)` half, since `projPointOfPoint W 0` is
`none` by `rfl`.  No new geometry.

The `[Fintype (W.torsion 3)]` is carried in the statement rather than produced inside it, for the
reason `#763` records and `#819` repeats: the sum cannot be written without it, and
`Fintype.ofFinite` in a statement is a noncomputable leak.  `finite_torsion_three` supplies it at
the point of use. -/
theorem pullbackDivisorThree_single_sub_single_eq_sum_torsion [Fintype (W.torsion 3)]
    (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) {S P : W.Point} (hP : (3 : ℕ) • P = S) :
    pullbackDivisorThree h2 h3 (Finsupp.single (projPointOfPoint W S) (1 : ℤ)
        - Finsupp.single (none : ProjPoint W) (1 : ℤ))
      = ∑ R : W.torsion 3, (Finsupp.single (projPointOfPoint W (P + R)) (1 : ℤ)
          - Finsupp.single (projPointOfPoint W (R : W.Point)) (1 : ℤ)) := by
  have hO : (none : ProjPoint W) = projPointOfPoint W 0 := rfl
  rw [map_sub, pullbackDivisorThree_single_eq_sum_torsion h2 h3 hP, hO,
    pullbackDivisorThree_single_eq_sum_torsion h2 h3 (smul_zero 3), ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun R _ => by rw [zero_add]

/-- The same formula on the affine chart, where `hprin` lives.  Each `(O)` in the coset sum simply
drops out (`affinePart_single_none`). -/
theorem affinePart_pullbackDivisorThree_single_sub_single [Fintype (W.torsion 3)]
    (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) {S P : W.Point} (hP : (3 : ℕ) • P = S) :
    affinePart W (pullbackDivisorThree h2 h3 (Finsupp.single (projPointOfPoint W S) (1 : ℤ)
        - Finsupp.single (none : ProjPoint W) (1 : ℤ)))
      = ∑ R : W.torsion 3, (pointDivisorAff W (P + R) - pointDivisorAff W (R : W.Point)) := by
  rw [pullbackDivisorThree_single_sub_single_eq_sum_torsion h2 h3 hP, map_sum]
  exact Finset.sum_congr rfl fun R _ => map_sub _ _ _

/-- **The class-group computation, and the mathematical heart of the file.**

```
∑_R toClass (P ⊕ R) − ∑_R toClass R = 9 • toClass P = toClass (9 • P) = toClass (3 • S) = 0.
```

Each summand of the coset formula has class `toClass P` on the nose — `toClass` is an
`AddMonoidHom`, so `toClass (P ⊕ R)` and `toClass R` differ by exactly `toClass P` — and there are
`#E[3] = 9` of them, which is `card_torsion_three`, an input and not a consequence.  Finally
`9 • P = 3 • (3 • P) = 3 • S = 0` because `S` is `3`-torsion.

⚠️ No step divides a divisor by `3`.  `n · D` principal does **not** imply `D` principal — that
failure is the `n`-torsion of the class group the Weil pairing measures — and the argument here
exhibits the class of `D` as trivial directly. -/
theorem classOfDivisor_affinePart_pullbackDivisorThree_eq_one (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0)
    {S P : W.Point} (hP : (3 : ℕ) • P = S) (hS : (3 : ℕ) • S = 0) :
    classOfDivisor W.FunctionField (affinePart W (pullbackDivisorThree h2 h3
        (Finsupp.single (projPointOfPoint W S) (1 : ℤ)
          - Finsupp.single (none : ProjPoint W) (1 : ℤ)))) = 1 := by
  classical
  haveI := W.finite_torsion_three h3
  haveI : Fintype (W.torsion 3) := Fintype.ofFinite _
  have hP9 : (9 : ℕ) • P = 0 := by
    rw [show (9 : ℕ) = 3 * 3 from rfl, mul_smul, hP, hS]
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

/-- **`[3]∗((S) − (O))` is principal on the affine chart.**  The vanishing class of the previous
theorem, turned back into an actual generator by `#726`'s principality criterion. -/
theorem exists_divisor_eq_affinePart_pullbackDivisorThree (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0)
    {S P : W.Point} (hP : (3 : ℕ) • P = S) (hS : (3 : ℕ) • S = 0) :
    ∃ g : W.FunctionField, g ≠ 0 ∧ divisor W g = affinePart W (pullbackDivisorThree h2 h3
      (Finsupp.single (projPointOfPoint W S) (1 : ℤ)
        - Finsupp.single (none : ProjPoint W) (1 : ℤ))) :=
  (exists_divisor_eq_iff_classOfDivisor_eq_one _).2
    (classOfDivisor_affinePart_pullbackDivisorThree_eq_one h2 h3 hP hS)

/-- **`hprin` at `n = 3`, in the shape `exists_gS_three` consumes it.**

The statement quantifies over *every* nonzero `f` with `divisor W f = 3·(S)`, not only over the
generator `#409` produces, so the proof must first know that the affine divisor pins the projective
one.  It does: `ordInfty_eq_of_divisor_eq` compares `f` with `#409`'s generator at the point at
infinity and `divisorProj_eq_iff` assembles the two halves.  Then `divisorProj_mulByThreeEndo`
moves `[3]∗` across, `map_zsmul` pulls the `3` out, and `affinePart` restricts to the chart.

⚠️ The last step is `natCast_zsmul`, not a `three_nsmul`/`three_zsmul` pair: the `n = 2` proof ends
`two_nsmul, two_zsmul` because both unfold to `a + a`, and `three'_nsmul` has no `zsmul` twin. -/
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
  have hdiv3 : divisor W (mulByThreeEndo h2 h3 f)
      = (3 : ℤ) • affinePart W (pullbackDivisorThree h2 h3
        (Finsupp.single (projPointOfPoint W (Point.some x y h)) (1 : ℤ)
          - Finsupp.single (none : ProjPoint W) (1 : ℤ))) := by
    rw [← affinePart_divisorProj, hkey, map_zsmul]
  rw [hdiv3, hgdiv, ← natCast_zsmul]
  norm_num

/-- **Rung 5 of the Weil pairing at `n = 3`, unconditionally.**  `exists_gS_three` with its `hprin`
discharged: for a nonsingular `3`-torsion point `S` over an algebraically closed field of
characteristic `≠ 2, 3`, there are a principal function `f_S` with `div f_S = 3·(S)` and a nonzero
`g_S ∈ F(W)` with `u · g_S ^ 3 = [3]∗ f_S` for a unit `u` of `F[W]`.

⚠️ Stated with `[IsAlgClosed F]` and `[W.IsElliptic]`, which `exists_gS_three` does not carry — see
the Scope section.  Over a general field the hypothesis stands, at `n = 3` exactly as at `n = 2`. -/
theorem exists_gS_three_of_isAlgClosed (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) {x y : F}
    (h : W.Nonsingular x y) (hS : Point.some x y h ∈ W.torsion 3) :
    ∃ f : W.FunctionField, f ≠ 0 ∧
      divisor W f = Finsupp.single (pointClosedPoint h.left) (3 : ℤ) ∧
      ∃ gS : W.FunctionField, gS ≠ 0 ∧
        ∃ u : W.CoordinateRingˣ, (u : W.CoordinateRing) • gS ^ 3 = mulByThreeEndo h2 h3 f :=
  exists_gS_three h2 h3 h hS fun _ hf hfdiv =>
    exists_nsmul_divisor_eq_divisor_mulByThreeEndo h2 h3 h hS hf hfdiv

end IsAlgClosed

/-! ### Non-vacuity

Everything above carries `[IsAlgClosed F]` and `[W.IsElliptic]`, and the headline additionally
needs a nonsingular affine `3`-torsion point to instantiate.  `y² + y = x³` over
`AlgebraicClosure ℚ` — the `n = 3` certificate curve of this tree — supplies all three, and the
`3`-torsion point can be **named**: it is `(0, 0)`, because `Ψ₃ = 3X⁴ + 3b₆X = 3X(X³ + 1)` here.

⚠️ `PullbackPrincipalityTwo`'s non-vacuity section says the `n = 3` witness is unnameable.  That is
true of a *fibre* witness `P` with `3 • P = S`, which is produced by `exists_nsmul_three_eq` and
never exhibited; it is not true of the torsion point `S` itself. -/

section Nonvacuity

/-! The certificate curve `y² + y = x³` is the shared `EllipticCurves.Fixture.y2AddYEqX3`, and the
base — algebraically closed, and of characteristic `0` so that `2 ≠ 0` and `3 ≠ 0` — is
`EllipticCurves.Fixture.AlgClosedQ`, whose single `[CharZero F]` instance also supplies
`IsElliptic` here. -/

open EllipticCurves.Fixture

private lemma exampleTwo : (2 : AlgClosedQ) ≠ 0 := two_ne_zero

private lemma exampleThree : (3 : AlgClosedQ) ≠ 0 := three_ne_zero_of_charZero _

/-- `S = (0, 0)` lies on `y² + y = x³` and is nonsingular. -/
private lemma exampleNonsingular : (y2AddYEqX3 AlgClosedQ).Nonsingular 0 0 :=
  (y2AddYEqX3 AlgClosedQ).equation_iff_nonsingular.mp (by
    norm_num [y2AddYEqX3, WeierstrassCurve.Affine.equation_iff])

open Classical in
/-- `S = (0, 0)` is `3`-torsion: `Ψ₃ = 3X⁴ + 3b₆X` vanishes at `0`, and the side condition of
`mem_torsion_three_some_iff` is automatic. -/
private lemma exampleTorsionThree :
    Point.some (0 : AlgClosedQ) 0 exampleNonsingular ∈ (y2AddYEqX3 AlgClosedQ).torsion 3 :=
  mem_torsion_three_some_iff'.mpr (by
    norm_num [y2AddYEqX3, WeierstrassCurve.Ψ₃, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
      WeierstrassCurve.b₆, WeierstrassCurve.b₈])

open Classical in
/-- **The principality, on a curve that exists.** -/
example (P : (y2AddYEqX3 AlgClosedQ).Point)
    (hP : (3 : ℕ) • P = Point.some (0 : AlgClosedQ) 0 exampleNonsingular) :
    ∃ g : (y2AddYEqX3 AlgClosedQ).FunctionField, g ≠ 0 ∧ (y2AddYEqX3 AlgClosedQ).divisor g
      = affinePart (y2AddYEqX3 AlgClosedQ) (pullbackDivisorThree exampleTwo exampleThree
        (Finsupp.single (projPointOfPoint (y2AddYEqX3 AlgClosedQ)
            (Point.some (0 : AlgClosedQ) 0 exampleNonsingular)) (1 : ℤ)
          - Finsupp.single (none : ProjPoint (y2AddYEqX3 AlgClosedQ)) (1 : ℤ))) :=
  exists_divisor_eq_affinePart_pullbackDivisorThree exampleTwo exampleThree hP
    (mem_torsion_iff.mp exampleTorsionThree)

open Classical in
/-- **The headline, committed**: rung 5 at `n = 3` with no `hprin`, on a genuine curve with a named
`3`-torsion point. -/
example : ∃ f : (y2AddYEqX3 AlgClosedQ).FunctionField, f ≠ 0 ∧
    (y2AddYEqX3 AlgClosedQ).divisor f
      = Finsupp.single (pointClosedPoint exampleNonsingular.left) (3 : ℤ) ∧
    ∃ gS : (y2AddYEqX3 AlgClosedQ).FunctionField, gS ≠ 0 ∧
      ∃ u : (y2AddYEqX3 AlgClosedQ).CoordinateRingˣ,
        (u : (y2AddYEqX3 AlgClosedQ).CoordinateRing) • gS ^ 3
          = mulByThreeEndo exampleTwo exampleThree f :=
  exists_gS_three_of_isAlgClosed exampleTwo exampleThree exampleNonsingular exampleTorsionThree

end Nonvacuity

end WeierstrassCurve.Affine
