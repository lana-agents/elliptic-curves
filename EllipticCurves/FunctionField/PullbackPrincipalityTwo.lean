/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import EllipticCurves.FunctionField.DivisorPrincipality
import EllipticCurves.FunctionField.MulByTwoFibreAffine
import EllipticCurves.FunctionField.NthRootOfPullback
import EllipticCurves.FunctionField.PullbackTorsionDivisor

/-!
# `[2]∗((S) − (O))` is principal, and rung 5 of the Weil pairing loses its hypothesis

Rung 5 of the divisor-theoretic Weil pairing (Silverman AEC III.8) produces, from the principal
function `f_S` of an `n`-torsion point `S`, an `n`-th root `g_S` of `f_S ∘ [n]`.  It is merged
(`EllipticCurves.FunctionField.NthRootOfPullback`, `#418`) but **conditionally**: both
`exists_gS_two` and `exists_gS_three` carry an explicit hypothesis `hprin` saying that the effective
divisor `D` with `n · D = div (f_S ∘ [n])` is *principal*.  That hypothesis is not formal — `n · D`
principal does **not** imply `D` principal, and the failure is exactly the `n`-torsion of the class
group the Weil pairing measures.

This file discharges it at `n = 2`, over an algebraically closed base field.

## The argument, and where each input comes from

Let `S` be a nonsingular affine `2`-torsion point and pick `P` with `2 • P = S`
(`exists_nsmul_two_eq`, `Torsion.DoublingSurjective`: `[2]` is surjective on `E(F̄)`).

1. **The fibre description**, `#774`: `[2]∗(S) = ∑_{R ∈ E[2]} (P ⊕ R)`
   (`pullbackDivisorTwo_single_eq_sum_torsion`).  Applying it once at `S` and once at `O` — where
   `P` may be taken to be `O`, since `projPointOfPoint W 0 = none` — and subtracting gives the
   formula rung 5 has been quoting in prose since `#765`:

   ```
   [2]∗((S) − (O)) = ∑_{R ∈ E[2]} ((P ⊕ R) − (R)).
   ```

   That is `pullbackDivisorTwo_single_sub_single_eq_sum_torsion`, and it was not a theorem anywhere
   before this file.

2. **The affine part.**  `hprin` is a statement about the affine `divisor W`, while the formula
   above lives in the projective divisor group `ProjPoint W →₀ ℤ`.  `#765` established that the
   passage projective ⟹ affine is free; `affinePart` is that passage, as an `AddMonoidHom`
   (`Finsupp.comapDomain.addMonoidHom` along `some`), with `affinePart_divisorProj` the round trip
   against `divisorProj_apply_some`.  Under it the point at infinity simply disappears
   (`affinePart_single_none`), which is why no degree normalisation appears anywhere below.

3. **The class computation.**  `pointDivisorAff` sends a rational point to the affine part of its
   place, so `O ↦ 0` and an affine point to its closed point; `classOfDivisor_pointDivisorAff` then
   identifies its class with Mathlib's `Point.toClass`, *including at the point at infinity*, where
   both sides are trivial.  With `Point.toClass` an `AddMonoidHom` and `card_torsion_two`, every
   summand of step 1 has class `toClass P` and the product telescopes:

   ```
   ∑_R toClass (P ⊕ R) − ∑_R toClass R = 4 • toClass P = toClass (4 • P) = toClass (2 • S) = 0.
   ```

   `#726`'s `exists_divisor_eq_iff_classOfDivisor_eq_one` turns that vanishing class back into an
   actual generator, and no step divides a divisor by `2`.

4. **`hprin`'s `∀`-form.**  `exists_gS_two` quantifies over *every* `f ≠ 0` with
   `divisor W f = 2·(S)`, not only over the generator `#409` produces.  The gap closes because the
   affine divisor pins the projective one: `ordInfty_eq_of_divisor_eq` against `#409`'s generator,
   then `divisorProj_eq_iff`.

## Main statements

* `WeierstrassCurve.Affine.affinePart` — the affine part of a projective divisor, and
  `affinePart_divisorProj`, its round trip against `divisorProj`.
* `WeierstrassCurve.Affine.classOfDivisor_pointDivisorAff` — the class of a rational point's affine
  divisor is its `Point.toClass`, for *every* point including `O`.  Unconditional.
* `WeierstrassCurve.Affine.pullbackDivisorTwo_single_sub_single_eq_sum_torsion` —
  `[2]∗((S) − (O)) = ∑_{R ∈ E[2]} ((P ⊕ R) − (R))`.
* `WeierstrassCurve.Affine.exists_divisor_eq_affinePart_pullbackDivisorTwo` — **the principality**:
  the affine part of `[2]∗((S) − (O))` is the divisor of a nonzero rational function.
* `WeierstrassCurve.Affine.exists_nsmul_divisor_eq_divisor_mulByTwoEndo` — `hprin` itself, in the
  shape `exists_gS_two` consumes.
* **`WeierstrassCurve.Affine.exists_gS_two_of_isAlgClosed`** — rung 5 at `n = 2` with no hypothesis
  left: a nonzero `g_S` with `u · g_S ^ 2 = [2]∗ f_S`.

## Scope

⚠️ **This is `n = 2` only.**  `exists_gS_three` keeps its `hprin` and nothing here helps it: there
is no `[3]` duplication formula at a closed point (`#404`), so the `n = 3` fibre description does
not exist, and `#763`'s count `4` is `[2]`-specific.

⚠️ **The hypotheses are strictly stronger than `exists_gS_two`'s.**  Everything from
`pullbackDivisorTwo_single_sub_single_eq_sum_torsion` onwards carries `[IsAlgClosed F]` and
`[W.IsElliptic]`, which `exists_gS_two` — stated over an arbitrary field with
`[IsDedekindDomain W.CoordinateRing]` — does not.  Two separate inputs need the algebraically closed
base: the surjectivity of `[2]` on points and `#774`'s fibre description.  Over a general field
`hprin` is still open, and this file says nothing about it.

⚠️ **This is not the Weil pairing.**  Rung 6 (`#419`, `#465`, `#456`) and the non-degeneracy of
`e_n` are untouched; `WeilPairing.lean` holds the canonical account of what non-degeneracy consumes
and this file does not restate it.

⚠️ **Nothing here says `#E[n] = n²` at general `n`.**  `card_torsion_two` is an *input*, it is
`[2]`-specific, and it does not go through Ward (`#765`).

## References

* [J. H. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.8 (the function `g_P`
  with `g_P ^ n = f_P ∘ [n]`), III.3.4 (the group law is the class-group map).
-/

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum

namespace IsDedekindDomain.HeightOneSpectrum

variable {R : Type*} [CommRing R] [IsDedekindDomain R]
  (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K]

/-! ### Two missing homomorphism laws for `classOfDivisor`

`#726` supplies `classOfDivisor_zero`, `classOfDivisor_add` and `classOfDivisor_nsmul`.  The
computation below is a difference of two sums, so it needs the other two laws; both are
`classOfDivisorHom` read through `Multiplicative`. -/

/-- **The class of a difference is the quotient of the classes.** -/
theorem classOfDivisor_sub (D₁ D₂ : HeightOneSpectrum R →₀ ℤ) :
    classOfDivisor K (D₁ - D₂) = classOfDivisor K D₁ / classOfDivisor K D₂ :=
  map_div (classOfDivisorHom K) (Multiplicative.ofAdd D₁) (Multiplicative.ofAdd D₂)

/-- **The class of a finite sum is the product of the classes.**  `classOfDivisor_add` iterated;
this is what lets a divisor supported on a coset of `E[2]` be classed one point at a time. -/
theorem classOfDivisor_sum {ι : Type*} (s : Finset ι) (D : ι → HeightOneSpectrum R →₀ ℤ) :
    classOfDivisor K (∑ i ∈ s, D i) = ∏ i ∈ s, classOfDivisor K (D i) := by
  classical
  induction s using Finset.induction with
  | empty => rw [Finset.sum_empty, Finset.prod_empty, classOfDivisor_zero]
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.prod_insert ha, classOfDivisor_add, ih]

end IsDedekindDomain.HeightOneSpectrum

namespace WeierstrassCurve.Affine

open CoordinateRing

variable {F : Type*} [Field F] {W : Affine F} [IsDedekindDomain W.CoordinateRing]

/-! ### The affine part of a projective divisor

`ProjPoint W` is `Option (HeightOneSpectrum F[W])`, so restricting a projective divisor to the
affine chart is `Finsupp.comapDomain` along `some`.  It is an `AddMonoidHom`, which is the whole
reason this passage costs nothing: it commutes with the sums and the `ℤ`-scaling below. -/

variable (W) in
/-- **The affine part of a projective divisor**: forget the coefficient at the point at infinity.

The inverse-image construction rather than a `Finsupp.filter`, so that `affinePart_divisorProj` is
`divisorProj_apply_some` read at every place and nothing has to be proved about supports. -/
noncomputable def affinePart :
    (ProjPoint W →₀ ℤ) →+ (HeightOneSpectrum W.CoordinateRing →₀ ℤ) :=
  Finsupp.comapDomain.addMonoidHom (some_injective_projPoint W)

/-- The affine part evaluates by evaluating at `some v`; definitionally `Finsupp.comapDomain`. -/
@[simp]
theorem affinePart_apply (D : ProjPoint W →₀ ℤ) (v : HeightOneSpectrum W.CoordinateRing) :
    affinePart W D v = D (some v) := rfl

/-- The affine part of an affine place is that place. -/
@[simp]
theorem affinePart_single_some (v : HeightOneSpectrum W.CoordinateRing) (n : ℤ) :
    affinePart W (Finsupp.single (some v) n) = Finsupp.single v n :=
  Finsupp.comapDomain_single _ _ _ _

/-- **The point at infinity disappears.**  This is why no degree normalisation intervenes anywhere
below: the projective statements of `#774` become affine ones by dropping a term, not by correcting
one. -/
@[simp]
theorem affinePart_single_none (n : ℤ) :
    affinePart W (Finsupp.single (none : ProjPoint W) n) = 0 :=
  Finsupp.comapDomain_single_of_not_mem_range (by simp) _ _

/-- **The round trip against `divisorProj`.**  Unconditional, and the precise content of `#765`'s
"the chart mismatch is not a gate": `divisorProj_apply_some` read at every affine place. -/
@[simp]
theorem affinePart_divisorProj (f : W.FunctionField) :
    affinePart W (divisorProj W f) = divisor W f := by
  ext v
  rw [affinePart_apply, divisorProj_apply_some, divisor_apply]

section Point

variable [DecidableEq F] {x y : F}

/-! ### The affine divisor of a rational point, and its class -/

variable (W) in
/-- **The affine divisor of a rational point.**  The point at infinity contributes nothing and an
affine point contributes its closed point with multiplicity one.  Defined uniformly on all of
`W.Point` so that a sum over a coset of `E[2]` — which may or may not contain `O` — needs no case
split. -/
noncomputable def pointDivisorAff (P : W.Point) : HeightOneSpectrum W.CoordinateRing →₀ ℤ :=
  affinePart W (Finsupp.single (projPointOfPoint W P) (1 : ℤ))

omit [DecidableEq F] in
/-- The point at infinity has empty affine divisor. -/
@[simp]
theorem pointDivisorAff_zero : pointDivisorAff W (0 : W.Point) = 0 := by
  rw [pointDivisorAff, projPointOfPoint_zero, affinePart_single_none]

omit [DecidableEq F] in
/-- An affine point has affine divisor its own closed point. -/
@[simp]
theorem pointDivisorAff_some (h : W.Nonsingular x y) :
    pointDivisorAff W (Point.some x y h) = Finsupp.single (pointClosedPoint h.left) (1 : ℤ) := by
  rw [pointDivisorAff, projPointOfPoint_some, affinePart_single_some]

/-- **The class of a rational point's affine divisor is its `Point.toClass`** — for *every* point,
including the point at infinity, where both sides are trivial.

`#726`'s `classOfDivisor_single_pointClosedPoint` is the affine case; the content added here is that
the uniform statement over `W.Point` is true, which is exactly what makes the sum over `E[2]`
collapse without a case split on whether `P ⊕ R` is `O`. -/
theorem classOfDivisor_pointDivisorAff (P : W.Point) :
    classOfDivisor W.FunctionField (pointDivisorAff W P)
      = Additive.toMul (Point.toClass P) := by
  cases P with
  | zero =>
      rw [← Point.zero_def, pointDivisorAff_zero, classOfDivisor_zero, Point.toClass_zero]
      rfl
  | some h => rw [pointDivisorAff_some, classOfDivisor_single_pointClosedPoint]

end Point

section IsAlgClosed

variable [DecidableEq F] [W.IsElliptic] [IsAlgClosed F]

/-! ### `[2]∗((S) − (O))` and its class -/

/-- **The formula rung 5 has been quoting in prose since `#765`, as a theorem**:

```
[2]∗((S) − (O)) = ∑_{R ∈ E[2]} ((P ⊕ R) − (R))
```

for any `P` with `2 • P = S`.  `pullbackDivisorTwo` is an `AddMonoidHom`, so `map_sub` splits the
left-hand side; `#774`'s `pullbackDivisorTwo_single_eq_sum_torsion` handles the `(S)` half, and the
**same theorem at `S = O` with `P = O`** handles the `(O)` half, since `projPointOfPoint W 0` is
`none` by `rfl`.  No new geometry.

The `[Fintype (W.torsion 2)]` is carried in the statement rather than produced inside it, for the
reason `#763` records: the sum cannot be written without it, and `Fintype.ofFinite` in a statement
is a noncomputable leak.  `finite_torsion_two` supplies it at the point of use. -/
theorem pullbackDivisorTwo_single_sub_single_eq_sum_torsion [Fintype (W.torsion 2)]
    (h2 : (2 : F) ≠ 0) {S P : W.Point} (hP : 2 • P = S) :
    pullbackDivisorTwo h2 (Finsupp.single (projPointOfPoint W S) (1 : ℤ)
        - Finsupp.single (none : ProjPoint W) (1 : ℤ))
      = ∑ R : W.torsion 2, (Finsupp.single (projPointOfPoint W (P + R)) (1 : ℤ)
          - Finsupp.single (projPointOfPoint W (R : W.Point)) (1 : ℤ)) := by
  have hO : (none : ProjPoint W) = projPointOfPoint W 0 := rfl
  rw [map_sub, pullbackDivisorTwo_single_eq_sum_torsion h2 hP, hO,
    pullbackDivisorTwo_single_eq_sum_torsion h2 (smul_zero 2), ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun R _ => by rw [zero_add]

/-- The same formula on the affine chart, where `hprin` lives.  Each `(O)` in the coset sum simply
drops out (`affinePart_single_none`). -/
theorem affinePart_pullbackDivisorTwo_single_sub_single [Fintype (W.torsion 2)]
    (h2 : (2 : F) ≠ 0) {S P : W.Point} (hP : 2 • P = S) :
    affinePart W (pullbackDivisorTwo h2 (Finsupp.single (projPointOfPoint W S) (1 : ℤ)
        - Finsupp.single (none : ProjPoint W) (1 : ℤ)))
      = ∑ R : W.torsion 2, (pointDivisorAff W (P + R) - pointDivisorAff W (R : W.Point)) := by
  rw [pullbackDivisorTwo_single_sub_single_eq_sum_torsion h2 hP, map_sum]
  exact Finset.sum_congr rfl fun R _ => map_sub _ _ _

/-- **The class-group computation, and the mathematical heart of the file.**

```
∑_R toClass (P ⊕ R) − ∑_R toClass R = 4 • toClass P = toClass (4 • P) = toClass (2 • S) = 0.
```

Each summand of the coset formula has class `toClass P` on the nose — `toClass` is an
`AddMonoidHom`, so `toClass (P ⊕ R)` and `toClass R` differ by exactly `toClass P` — and there are
`#E[2] = 4` of them, which is `card_torsion_two`, an input and not a consequence.  Finally
`4 • P = 2 • (2 • P) = 2 • S = 0` because `S` is `2`-torsion.

⚠️ No step divides a divisor by `2`.  `n · D` principal does **not** imply `D` principal — that
failure is the `n`-torsion of the class group the Weil pairing measures — and the argument here
exhibits the class of `D` as trivial directly. -/
theorem classOfDivisor_affinePart_pullbackDivisorTwo_eq_one (h2 : (2 : F) ≠ 0)
    {S P : W.Point} (hP : 2 • P = S) (hS : 2 • S = 0) :
    classOfDivisor W.FunctionField (affinePart W (pullbackDivisorTwo h2
        (Finsupp.single (projPointOfPoint W S) (1 : ℤ)
          - Finsupp.single (none : ProjPoint W) (1 : ℤ)))) = 1 := by
  classical
  haveI := W.finite_torsion_two h2
  haveI : Fintype (W.torsion 2) := Fintype.ofFinite _
  have hP4 : (4 : ℕ) • P = 0 := by
    rw [show (4 : ℕ) = 2 * 2 from rfl, mul_smul, hP, hS]
  have hterm : ∀ R ∈ (Finset.univ : Finset (W.torsion 2)),
      classOfDivisor W.FunctionField (pointDivisorAff W (P + R) - pointDivisorAff W (R : W.Point))
        = Additive.toMul (Point.toClass P) := by
    intro R _
    rw [classOfDivisor_sub, classOfDivisor_pointDivisorAff, classOfDivisor_pointDivisorAff,
      map_add, toMul_add, mul_div_cancel_right]
  have hcard : Fintype.card (W.torsion 2) = 4 := by
    rw [← Nat.card_eq_fintype_card, card_torsion_two h2]
  rw [affinePart_pullbackDivisorTwo_single_sub_single h2 hP, classOfDivisor_sum,
    Finset.prod_congr rfl hterm, Finset.prod_const, Finset.card_univ, hcard, ← toMul_nsmul,
    ← map_nsmul, hP4, Point.toClass_zero]
  rfl

/-- **`[2]∗((S) − (O))` is principal on the affine chart.**  The vanishing class of the previous
theorem, turned back into an actual generator by `#726`'s principality criterion.

This is the sentence `NthRootOfPullback` and `PullbackTorsionDivisor` have both named as all that
was left of `hprin` at `n = 2`. -/
theorem exists_divisor_eq_affinePart_pullbackDivisorTwo (h2 : (2 : F) ≠ 0)
    {S P : W.Point} (hP : 2 • P = S) (hS : 2 • S = 0) :
    ∃ g : W.FunctionField, g ≠ 0 ∧ divisor W g = affinePart W (pullbackDivisorTwo h2
      (Finsupp.single (projPointOfPoint W S) (1 : ℤ)
        - Finsupp.single (none : ProjPoint W) (1 : ℤ))) :=
  (exists_divisor_eq_iff_classOfDivisor_eq_one _).2
    (classOfDivisor_affinePart_pullbackDivisorTwo_eq_one h2 hP hS)

/-- **`hprin`, in the shape `exists_gS_two` consumes it.**

The statement quantifies over *every* nonzero `f` with `divisor W f = 2·(S)`, not only over the
generator `#409` produces, so the proof must first know that the affine divisor pins the projective
one.  It does: `ordInfty_eq_of_divisor_eq` compares `f` with `#409`'s generator at the point at
infinity and `divisorProj_eq_iff` assembles the two halves.  Then `divisorProj_mulByTwoEndo` moves
`[2]∗` across, `pullbackDivisorTwo_zsmul` pulls the `2` out, and `affinePart` restricts to the
chart. -/
theorem exists_nsmul_divisor_eq_divisor_mulByTwoEndo (h2 : (2 : F) ≠ 0) {x y : F}
    (h : W.Nonsingular x y) (hS : Point.some x y h ∈ W.torsion 2)
    {f : W.FunctionField} (hf : f ≠ 0)
    (hfdiv : divisor W f = Finsupp.single (pointClosedPoint h.left) (2 : ℤ)) :
    ∃ g₀ : W.FunctionField, g₀ ≠ 0 ∧ 2 • divisor W g₀ = divisor W (mulByTwoEndo h2 f) := by
  classical
  obtain ⟨P, hP⟩ := exists_nsmul_two_eq h2 (Point.some x y h)
  obtain ⟨g, hg, hgdiv⟩ :=
    exists_divisor_eq_affinePart_pullbackDivisorTwo h2 hP (mem_torsion_iff.mp hS)
  refine ⟨g, hg, ?_⟩
  obtain ⟨f₀, hf₀, hproj₀⟩ := divisorProj_eq_single_sub_single_of_torsion h hS
  have hd₀ : divisor W f₀ = Finsupp.single (pointClosedPoint h.left) (2 : ℤ) := by
    ext v
    have hv := congrArg (fun D => D (some v)) hproj₀
    simpa [Finsupp.single_apply] using hv
  have hfe : divisor W f = divisor W f₀ := hfdiv.trans hd₀.symm
  have hprojf : divisorProj W f = divisorProj W f₀ :=
    divisorProj_eq_iff.2 ⟨hfe, ordInfty_eq_of_divisor_eq hf hf₀ hfe⟩
  have hkey : divisorProj W (mulByTwoEndo h2 f)
      = (2 : ℤ) • pullbackDivisorTwo h2
          (Finsupp.single (projPointOfPoint W (Point.some x y h)) (1 : ℤ)
            - Finsupp.single (none : ProjPoint W) (1 : ℤ)) := by
    rw [divisorProj_mulByTwoEndo h2 hf, hprojf, hproj₀, ← pullbackDivisorTwo_zsmul]
    congr 1
    rw [smul_sub, Finsupp.smul_single, Finsupp.smul_single, smul_eq_mul, mul_one,
      projPointOfPoint_some]
    norm_num
  have hdiv2 : divisor W (mulByTwoEndo h2 f) = (2 : ℤ) • affinePart W (pullbackDivisorTwo h2
      (Finsupp.single (projPointOfPoint W (Point.some x y h)) (1 : ℤ)
        - Finsupp.single (none : ProjPoint W) (1 : ℤ))) := by
    rw [← affinePart_divisorProj, hkey, map_zsmul]
  rw [hdiv2, hgdiv, two_nsmul, two_zsmul]

/-- **Rung 5 of the Weil pairing at `n = 2`, unconditionally.**  `exists_gS_two` with its `hprin`
discharged: for a nonsingular `2`-torsion point `S` over an algebraically closed field of
characteristic `≠ 2`, there are a principal function `f_S` with `div f_S = 2·(S)` and a nonzero
`g_S ∈ F(W)` with `u · g_S ^ 2 = [2]∗ f_S` for a unit `u` of `F[W]`.

⚠️ Stated with `[IsAlgClosed F]` and `[W.IsElliptic]`, which `exists_gS_two` does not carry — see
the Scope section.  At `n = 3` `exists_gS_three` keeps its hypothesis. -/
theorem exists_gS_two_of_isAlgClosed (h2 : (2 : F) ≠ 0) {x y : F} (h : W.Nonsingular x y)
    (hS : Point.some x y h ∈ W.torsion 2) :
    ∃ f : W.FunctionField, f ≠ 0 ∧
      divisor W f = Finsupp.single (pointClosedPoint h.left) (2 : ℤ) ∧
      ∃ gS : W.FunctionField, gS ≠ 0 ∧
        ∃ u : W.CoordinateRingˣ, (u : W.CoordinateRing) • gS ^ 2 = mulByTwoEndo h2 f :=
  exists_gS_two h2 h hS fun _ hf hfdiv =>
    exists_nsmul_divisor_eq_divisor_mulByTwoEndo h2 h hS hf hfdiv

end IsAlgClosed

/-! ### Non-vacuity

Everything above carries `[IsAlgClosed F]` and `[W.IsElliptic]`, and the headline additionally needs
a nonsingular affine `2`-torsion point to instantiate.  `y² = x³ − x` over `AlgebraicClosure ℚ`
supplies all three, and — unlike the `n = 3` files, where `[IsAlgClosed F]` makes the count provable
and the witness unnameable — here the `2`-torsion point can be *named*: it is `(0, 0)`. -/

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

/-- `S = (0, 0)` lies on `y² = x³ − x` and is nonsingular. -/
private lemma exampleNonsingular : exampleCurve.Nonsingular 0 0 :=
  exampleCurve.equation_iff_nonsingular.mp (by
    norm_num [exampleCurve, WeierstrassCurve.Affine.equation_iff])

open Classical in
/-- `S = (0, 0)` is `2`-torsion: `2y + a₁x + a₃ = 0` reads `0 = 0`. -/
private lemma exampleTorsion :
    Point.some (0 : exampleField) 0 exampleNonsingular ∈ exampleCurve.torsion 2 :=
  (mem_torsion_two_some_iff exampleNonsingular).mpr (by norm_num [exampleCurve])

open Classical in
/-- **The principality, on a curve that exists.** -/
example (P : exampleCurve.Point) (hP : 2 • P = Point.some (0 : exampleField) 0 exampleNonsingular) :
    ∃ g : exampleCurve.FunctionField, g ≠ 0 ∧ exampleCurve.divisor g
      = affinePart exampleCurve (pullbackDivisorTwo exampleTwo
        (Finsupp.single (projPointOfPoint exampleCurve
            (Point.some (0 : exampleField) 0 exampleNonsingular)) (1 : ℤ)
          - Finsupp.single (none : ProjPoint exampleCurve) (1 : ℤ))) :=
  exists_divisor_eq_affinePart_pullbackDivisorTwo exampleTwo hP
    (mem_torsion_iff.mp exampleTorsion)

open Classical in
/-- **The headline, committed**: rung 5 at `n = 2` with no `hprin`, on a genuine curve with a named
`2`-torsion point. -/
example : ∃ f : exampleCurve.FunctionField, f ≠ 0 ∧
    exampleCurve.divisor f
      = Finsupp.single (pointClosedPoint exampleNonsingular.left) (2 : ℤ) ∧
    ∃ gS : exampleCurve.FunctionField, gS ≠ 0 ∧
      ∃ u : exampleCurve.CoordinateRingˣ,
        (u : exampleCurve.CoordinateRing) • gS ^ 2 = mulByTwoEndo exampleTwo f :=
  exists_gS_two_of_isAlgClosed exampleTwo exampleNonsingular exampleTorsion

end Nonvacuity

end WeierstrassCurve.Affine
