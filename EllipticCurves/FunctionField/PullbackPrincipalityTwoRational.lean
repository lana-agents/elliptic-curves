/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import EllipticCurves.FunctionField.PlaceInertiaGeneral
import EllipticCurves.FunctionField.PullbackPrincipalityTwo

/-!
# `hprin` at `n = 2` over an arbitrary field, from two rationality hypotheses

`EllipticCurves.FunctionField.PullbackPrincipalityTwo` (`#791`) discharges `hprin` at `n = 2` —
the principality of `[2]∗((S) − (O))` that `exists_gS_two` carries as a hypothesis — over an
**algebraically closed** base field.  `#962` records that this is the last standing gate on rungs
5–6 of the Weil pairing over a general field, and its audit thread reduces the closure hypothesis
to a short list of rationality facts.  This file carries that reduction out.

## The statement

`exists_gS_two_of_card_torsion_two` is `exists_gS_two_of_isAlgClosed` with `[IsAlgClosed F]`
replaced by three explicit hypotheses over an arbitrary field `F`:

* `hcard : Nat.card (W.torsion 2) = 4` — the `2`-torsion is `F`-rational;
* `hP : 2 • P = S` — the point `S` being paired has an `F`-rational halving point;
* `hsep` — `F(W) / [2]∗F(W)` is separable, which `[CharZero F]` supplies for free
  (`exists_gS_two_of_charZero`).

None of the three is an algebraic-closure statement, and each is satisfiable over `ℚ`: the
non-vacuity block at the bottom exhibits `y² = x³ − 41x² + 400x`, whose `2`-torsion is
`{O, (0,0), (16,0), (25,0)}` and on which `P = (40, 120)` halves `S = (25, 0)`.

## What made this reachable, and what it cost

⚠️ The `F̄` proof does **not** descend by a Galois argument: `hprin` produces a *witness*, and
`#899`'s test (*is the obstruction used to prove an equality, or to produce a witness?*) says
witnesses do not descend.  The route here is the other one — do not descend the theorem, weaken
its hypothesis — and `#962`'s audit thread priced it by reading every `[IsAlgClosed F]` in the
transitive proof of `exists_nsmul_divisor_eq_divisor_mulByTwoEndo`.  That audit found three leaves,
and its own correction comment identified which of them was load-bearing:

| leaf | shape | status |
| --- | --- | --- |
| `card_torsion_two` | *the three roots of `Ψ₂Sq` are in `F`* | a hypothesis here (`hcard`) |
| `exists_nsmul_two_eq` | *one root of `Φ₂ − x₀·Ψ₂Sq` is in `F`* | a hypothesis here (`hP`) |
| `sum_ramificationIdxTwo_eq_four` | *every place is `F`-rational* | ⚠️ **no rational form** |

The third has no finite-level shape — over `ℚ`, `x² + 1` gives a closed point of degree `2` — and
it is why the reduction could not be run before `#1167`.  What replaces it is
`sum_ramificationIdxTwo_mul_residueDegreeTwo_of_isSeparable`
(`EllipticCurves.FunctionField.PlaceInertiaGeneral`): the **uncollapsed** identity
`∑_{p ↦ q} e_p · f_p = 4`, which needs no hypothesis on `F` beyond separability.

## The counting argument, which is the whole of the new mathematics

Over `F̄` the fibre of `[2]` is understood by *"every `f_p` is `1`, so `∑ e_p = 4`"*.  Over an
arbitrary field that is false at places away from the rational points, and the replacement is:

* the four points `P ⊕ R`, `R ∈ E[2]`, are `F`-rational and distinct, so they are four places in
  the fibre with `f_p = 1` (`residueDegreeTwo_projPointOfPoint`) and `e_p ≥ 1`;
* every place in the fibre has `e_p · f_p ≥ 1` (`ramificationIdxTwo_pos` and `residueDegreeTwo_pos`
  below), so the fibre has at most `4` elements;
* `4 ≤ #fibre ≤ 4` forces the fibre to be exactly those four points **and** every `e_p · f_p` to be
  `1`, hence every `e_p` to be `1`.

⚠️ **No place away from the four rational ones has to be understood**, which is exactly what makes
the `F̄`-only *"every place is rational"* avoidable.  The count is not *"the extra places are
unramified"*; it is *"there are no extra places"*, and it is forced by the degree, not observed.

`residueDegreeTwo_pos` is the one genuinely missing brick and it is three lines: the tower formula
`f_{[2]∗ p} · f_p = f_p^{proj}` together with `degProjPt_pos` through
`degProjPt_eq_residueDegreeProj`.  ⚠️ It is a theorem and not a convention — `residueDegreeProj` is
a `Module.finrank`, which returns `0` on an infinite-dimensional module.

## Recovery

`exists_nsmul_divisor_eq_divisor_mulByTwoEndo` and `exists_gS_two_of_isAlgClosed`, the merged
`[IsAlgClosed F]` statements, are re-derived from the general forms at the bottom of the
`Recovery` section (`#907`): over `F̄` the three hypotheses are `card_torsion_two`,
`exists_nsmul_two_eq` and `isSeparable_mulByTwoEndoFieldRange_of_isAlgClosed`.  The recoveries are
**verbatim**: same binders, same statement, nothing weakened.

## What this does *not* do

⚠️ **It does not close `#962`.** `#962` asks for `hprin` over a general field with *no* rationality
hypothesis, which needs the two hypotheses above to be discharged over a finite extension `L/F` and
the result descended by Hilbert 90 — Mathlib's finite
`isMulCoboundary₁_of_isMulCocycle₁_of_aut_to_units` suffices for the cohomology, but the descent
statement `L(W⁄L)^{Gal(L/F)} = F(W)` is `#692`'s divisor half and is not built, and separability of
`L/F` in characteristic `p` is unaddressed.
What this file supplies is the *target* of that descent: the statement one would descend **from**,
now available over an arbitrary field rather than only over `F̄`.

⚠️ It says nothing about `n = 3`.  `PullbackPrincipalityThree` was not audited for this, and
`#962` records a concrete reason not to assume the mirror: `#947` rules out full rational
`3`-torsion over `ℚ` for *every* elliptic curve, so the `n = 3` analogue of the non-vacuity block
below needs a different base field.

## References

* [J. H. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.8.
* `EllipticCurves.FunctionField.PullbackPrincipalityTwo` — the `[IsAlgClosed F]` original.
* `EllipticCurves.FunctionField.PlaceInertiaGeneral` (`#1167`) — the uncollapsed `∑ e·f = 4`.
-/

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum

namespace WeierstrassCurve.Affine.CoordinateRing

variable {F : Type*} [Field F] [DecidableEq F] {W : Affine F}
  [IsDedekindDomain W.CoordinateRing] [W.IsElliptic]

/-! ### The missing positivity -/

omit [DecidableEq F] in
/-- **The relative residue degree of `[2]∗` is positive at every place**, over an arbitrary field.

⚠️ This is a theorem, not a convention: `residueDegreeProj` is a `Module.finrank`, which is `0` on
an infinite-dimensional module, so nothing is positive by definition here.  What makes it true is
`degProjPt_pos` — every closed point of the projective curve has positive degree — transported
across `degProjPt_eq_residueDegreeProj` and then cancelled out of the tower formula
`f^{proj}_{[2]⁻¹p} · f_p = f^{proj}_p`.

It is the hypothesis that lets a count inside a fibre of `[2]` bound the *number* of places by the
degree, which is the whole reason the algebraically closed base field can be dropped below. -/
theorem residueDegreeTwo_pos (h2 : (2 : F) ≠ 0) (p : ProjPoint W) :
    0 < residueDegreeTwo h2 p := by
  have h := residueDegreeProj_mul_residueDegreeTwo h2 p
  have hp : 0 < residueDegreeProj W p := by
    rw [← degProjPt_eq_residueDegreeProj]; exact degProjPt_pos p
  rcases Nat.eq_zero_or_pos (residueDegreeTwo h2 p) with h0 | h0
  · rw [h0, Nat.mul_zero] at h; omega
  · exact h0

/-! ### The fibre over a rational point, counted by degree rather than by closure -/

/-- **The fibre of `[2]` over a rational point has exactly four elements**, over an arbitrary
field, given that `E[2]` and one halving point of `S` are `F`-rational.

`≥ 4` is the coset `{ P ⊕ R : R ∈ E[2] }`, four distinct places by `hcard` and
`projPointOfPoint_add_injective_two`.  `≤ 4` is the new half: each place of the fibre contributes
`e_p · f_p ≥ 1` to `∑_{p ↦ q} e_p · f_p = 4`, so there cannot be a fifth.

⚠️ The merged `card_fibre_comapProjPointTwo_projPointOfPoint` gets `≤ 4` from
`card_fibre_comapProjPointTwo_le_four`, which reads `∑ e_p = 4` and is `[IsAlgClosed F]`-only
because it has already collapsed every `f_p` to `1`.  The uncollapsed identity is what survives
over a general field. -/
theorem card_fibre_comapProjPointTwo_projPointOfPoint_of_card_torsion_two (h2 : (2 : F) ≠ 0)
    (hsep : Algebra.IsSeparable ↥(mulByTwoEndo (W := W) h2).fieldRange W.FunctionField)
    (hcard : Nat.card (W.torsion 2) = 4) {S P : W.Point} (hP : 2 • P = S) :
    (finite_comapProjPointTwo_preimage_singleton h2 (projPointOfPoint W S)).toFinset.card = 4 := by
  classical
  haveI := W.finite_torsion_two h2
  haveI : Fintype (W.torsion 2) := Fintype.ofFinite _
  set s := (finite_comapProjPointTwo_preimage_singleton h2 (projPointOfPoint W S)).toFinset with hs
  have hsum : ∑ p ∈ s, (ramificationIdxTwo h2 p).toNat * residueDegreeTwo h2 p = 4 :=
    sum_ramificationIdxTwo_mul_residueDegreeTwo_of_isSeparable h2 hsep _
  have hge : ∀ p ∈ s, 1 ≤ (ramificationIdxTwo h2 p).toNat * residueDegreeTwo h2 p := by
    intro p _
    have h1 := ramificationIdxTwo_pos h2 p
    have h2' := residueDegreeTwo_pos h2 p
    exact Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by omega))
  have hle : s.card ≤ 4 := by
    calc s.card = ∑ _p ∈ s, 1 := by rw [Finset.card_eq_sum_ones]
    _ ≤ ∑ p ∈ s, (ramificationIdxTwo h2 p).toNat * residueDegreeTwo h2 p :=
        Finset.sum_le_sum hge
    _ = 4 := hsum
  have hsub : Finset.image (fun R : W.torsion 2 => projPointOfPoint W (P + R)) Finset.univ ⊆ s := by
    intro p hp
    obtain ⟨R, _, rfl⟩ := Finset.mem_image.1 hp
    exact (Set.Finite.mem_toFinset _).2 (comapProjPointTwo_add_torsion_two h2 hP R)
  have himg : (Finset.image (fun R : W.torsion 2 => projPointOfPoint W (P + R))
      Finset.univ).card = 4 := by
    rw [Finset.card_image_of_injective _ (projPointOfPoint_add_injective_two P),
      Finset.card_univ, ← Nat.card_eq_fintype_card, hcard]
  have hge4 : 4 ≤ s.card := himg ▸ Finset.card_le_card hsub
  omega

/-- **The fibre of `[2]` over a rational point *is* the coset `{ P ⊕ R : R ∈ E[2] }`**, over an
arbitrary field.  `⊇` is `comapProjPointTwo_add_torsion_two`; `⊆` is pure counting against the card
above, with no further geometry — exactly as in the merged `fibre_comapProjPointTwo_eq_range`. -/
theorem fibre_comapProjPointTwo_eq_range_of_card_torsion_two (h2 : (2 : F) ≠ 0)
    (hsep : Algebra.IsSeparable ↥(mulByTwoEndo (W := W) h2).fieldRange W.FunctionField)
    (hcard : Nat.card (W.torsion 2) = 4) {S P : W.Point} (hP : 2 • P = S) :
    comapProjPointTwo h2 ⁻¹' {projPointOfPoint W S}
      = Set.range fun R : W.torsion 2 => projPointOfPoint W (P + R) := by
  classical
  haveI := W.finite_torsion_two h2
  haveI : Fintype (W.torsion 2) := Fintype.ofFinite _
  have hfin := finite_comapProjPointTwo_preimage_singleton h2 (projPointOfPoint W S)
  have hsub : (Set.range fun R : W.torsion 2 => projPointOfPoint W (P + R))
      ⊆ comapProjPointTwo h2 ⁻¹' {projPointOfPoint W S} := by
    rintro p ⟨R, rfl⟩
    exact comapProjPointTwo_add_torsion_two h2 hP R
  refine (Set.eq_of_subset_of_ncard_le hsub ?_ hfin).symm
  have h1 : (comapProjPointTwo h2 ⁻¹' {projPointOfPoint W S}).ncard = 4 := by
    rw [Set.ncard_eq_toFinset_card _ hfin]
    exact card_fibre_comapProjPointTwo_projPointOfPoint_of_card_torsion_two h2 hsep hcard hP
  have h2' : (Set.range fun R : W.torsion 2 => projPointOfPoint W (P + R)).ncard = 4 := by
    rw [← Nat.card_coe_set_eq, Nat.card_range_of_injective (projPointOfPoint_add_injective_two P),
      hcard]
  omega

/-- **`[2]` is unramified over a rational point that has a rational halving point**, over an
arbitrary field.

The merged proof gets this from *four positive `e_p` summing to `4`*.  Here the four terms of
`∑_{p ↦ q} e_p · f_p = 4` are each `≥ 1` and there are `#fibre = 4` of them, so every product is
`1` — which pins `e_p = 1` and, incidentally, `f_p = 1` at every place of the fibre.

⚠️ As in the merged version, this is *not* "`[2]` is unramified": a place over a closed point that
is not the closed point of an `F`-rational point is untouched. -/
theorem ramificationIdxTwo_eq_one_of_card_torsion_two (h2 : (2 : F) ≠ 0)
    (hsep : Algebra.IsSeparable ↥(mulByTwoEndo (W := W) h2).fieldRange W.FunctionField)
    (hcard : Nat.card (W.torsion 2) = 4) {S P : W.Point} (hP : 2 • P = S)
    {p : ProjPoint W} (hp : comapProjPointTwo h2 p = projPointOfPoint W S) :
    ramificationIdxTwo h2 p = 1 := by
  classical
  set s := (finite_comapProjPointTwo_preimage_singleton h2 (projPointOfPoint W S)).toFinset with hs
  have hmem : p ∈ s := (Set.Finite.mem_toFinset _).2 hp
  have hcard4 : s.card = 4 :=
    card_fibre_comapProjPointTwo_projPointOfPoint_of_card_torsion_two h2 hsep hcard hP
  have hsum : ∑ q ∈ s, (ramificationIdxTwo h2 q).toNat * residueDegreeTwo h2 q = 4 :=
    sum_ramificationIdxTwo_mul_residueDegreeTwo_of_isSeparable h2 hsep _
  have hge : ∀ q ∈ s, 1 ≤ (ramificationIdxTwo h2 q).toNat * residueDegreeTwo h2 q := by
    intro q _
    have h1 := ramificationIdxTwo_pos h2 q
    have h2' := residueDegreeTwo_pos h2 q
    exact Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by omega))
  have heq : ∑ _q ∈ s, 1 = ∑ q ∈ s, (ramificationIdxTwo h2 q).toNat * residueDegreeTwo h2 q := by
    rw [hsum, Finset.sum_const, hcard4, smul_eq_mul, mul_one]
  have hall := (Finset.sum_eq_sum_iff_of_le hge).1 heq p hmem
  have h1 := ramificationIdxTwo_pos h2 p
  have hone : (ramificationIdxTwo h2 p).toNat = 1 := Nat.eq_one_of_mul_eq_one_right hall.symm
  omega

/-- **`#774`'s fibre description of `[2]∗` at a rational point, over an arbitrary field**:

```
[2]∗(S) = ∑_{R ∈ E[2]} (P ⊕ R)   for any P with 2 • P = S.
```

Proof body identical to the merged `pullbackDivisorTwo_single_eq_sum_torsion`; only the two inputs
change, from the `[IsAlgClosed F]` fibre lemmas to the hypothesis-carrying ones above. -/
theorem pullbackDivisorTwo_single_eq_sum_torsion_of_card_torsion_two [Fintype (W.torsion 2)]
    (h2 : (2 : F) ≠ 0)
    (hsep : Algebra.IsSeparable ↥(mulByTwoEndo (W := W) h2).fieldRange W.FunctionField)
    (hcard : Nat.card (W.torsion 2) = 4) {S P : W.Point} (hP : 2 • P = S) :
    pullbackDivisorTwo h2 (Finsupp.single (projPointOfPoint W S) (1 : ℤ))
      = ∑ R : W.torsion 2, Finsupp.single (projPointOfPoint W (P + R)) (1 : ℤ) := by
  classical
  ext q
  rw [pullbackDivisorTwo_apply, Finset.sum_apply',
    Finset.sum_congr rfl fun R _ => Finsupp.single_apply]
  by_cases hq : comapProjPointTwo h2 q = projPointOfPoint W S
  · obtain ⟨R₀, hR₀⟩ : q ∈ Set.range fun R : W.torsion 2 => projPointOfPoint W (P + R) := by
      rw [← fibre_comapProjPointTwo_eq_range_of_card_torsion_two h2 hsep hcard hP]; exact hq
    rw [hq, Finsupp.single_eq_same, mul_one,
      ramificationIdxTwo_eq_one_of_card_torsion_two h2 hsep hcard hP hq,
      Finset.sum_eq_single R₀ (fun R _ hRne => if_neg fun hc =>
        hRne (projPointOfPoint_add_injective_two P (hc.trans hR₀.symm)))
      (fun hc => absurd (Finset.mem_univ R₀) hc), if_pos hR₀]
  · rw [Finsupp.single_apply, if_neg fun hc => hq hc.symm, mul_zero, Finset.sum_eq_zero]
    intro R _
    refine if_neg fun hc => hq ?_
    rw [← hc]
    exact comapProjPointTwo_add_torsion_two h2 hP R

end WeierstrassCurve.Affine.CoordinateRing

namespace WeierstrassCurve.Affine

open CoordinateRing

-- ⚠️ Binder ORDER, not just the binder list, is copied from `PullbackPrincipalityTwo` (`:142`,
-- `:232`): the recoveries below elaborate to a permutation of the merged statements otherwise.
variable {F : Type*} [Field F] {W : Affine F} [IsDedekindDomain W.CoordinateRing]

variable [DecidableEq F] [W.IsElliptic]

/-! ### `[2]∗((S) − (O))` and its class, over an arbitrary field -/

/-- **`[2]∗((S) − (O)) = ∑_{R ∈ E[2]} ((P ⊕ R) − (R))`**, over an arbitrary field.  The `(O)` half
is the same theorem at `S = O` with `P = O`, where `projPointOfPoint W 0` is `none` by `rfl`. -/
theorem pullbackDivisorTwo_single_sub_single_eq_sum_torsion_of_card_torsion_two
    [Fintype (W.torsion 2)] (h2 : (2 : F) ≠ 0)
    (hsep : Algebra.IsSeparable ↥(mulByTwoEndo (W := W) h2).fieldRange W.FunctionField)
    (hcard : Nat.card (W.torsion 2) = 4) {S P : W.Point} (hP : 2 • P = S) :
    pullbackDivisorTwo h2 (Finsupp.single (projPointOfPoint W S) (1 : ℤ)
        - Finsupp.single (none : ProjPoint W) (1 : ℤ))
      = ∑ R : W.torsion 2, (Finsupp.single (projPointOfPoint W (P + R)) (1 : ℤ)
          - Finsupp.single (projPointOfPoint W (R : W.Point)) (1 : ℤ)) := by
  have hO : (none : ProjPoint W) = projPointOfPoint W 0 := rfl
  rw [map_sub, pullbackDivisorTwo_single_eq_sum_torsion_of_card_torsion_two h2 hsep hcard hP, hO,
    pullbackDivisorTwo_single_eq_sum_torsion_of_card_torsion_two h2 hsep hcard (smul_zero 2),
    ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun R _ => by rw [zero_add]

/-- The same formula on the affine chart, where `hprin` lives. -/
theorem affinePart_pullbackDivisorTwo_single_sub_single_of_card_torsion_two
    [Fintype (W.torsion 2)] (h2 : (2 : F) ≠ 0)
    (hsep : Algebra.IsSeparable ↥(mulByTwoEndo (W := W) h2).fieldRange W.FunctionField)
    (hcard : Nat.card (W.torsion 2) = 4) {S P : W.Point} (hP : 2 • P = S) :
    affinePart W (pullbackDivisorTwo h2 (Finsupp.single (projPointOfPoint W S) (1 : ℤ)
        - Finsupp.single (none : ProjPoint W) (1 : ℤ)))
      = ∑ R : W.torsion 2, (pointDivisorAff W (P + R) - pointDivisorAff W (R : W.Point)) := by
  rw [pullbackDivisorTwo_single_sub_single_eq_sum_torsion_of_card_torsion_two h2 hsep hcard hP,
    map_sum]
  exact Finset.sum_congr rfl fun R _ => map_sub _ _ _

/-- **The class-group computation, over an arbitrary field.**

```
∑_R toClass (P ⊕ R) − ∑_R toClass R = 4 • toClass P = toClass (4 • P) = toClass (2 • S) = 0.
```

`#E[2] = 4` enters only as the number of summands, and it is now `hcard` rather than
`card_torsion_two`.  ⚠️ No step divides a divisor by `2`: the class of `D` is exhibited as trivial
directly, since `n · D` principal does not imply `D` principal. -/
theorem classOfDivisor_affinePart_pullbackDivisorTwo_eq_one_of_card_torsion_two (h2 : (2 : F) ≠ 0)
    (hsep : Algebra.IsSeparable ↥(mulByTwoEndo (W := W) h2).fieldRange W.FunctionField)
    (hcard : Nat.card (W.torsion 2) = 4) {S P : W.Point} (hP : 2 • P = S) (hS : 2 • S = 0) :
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
  have hcard' : Fintype.card (W.torsion 2) = 4 := by
    rw [← Nat.card_eq_fintype_card, hcard]
  rw [affinePart_pullbackDivisorTwo_single_sub_single_of_card_torsion_two h2 hsep hcard hP,
    classOfDivisor_sum, Finset.prod_congr rfl hterm, Finset.prod_const, Finset.card_univ, hcard',
    ← toMul_nsmul, ← map_nsmul, hP4, Point.toClass_zero]
  rfl

/-- **`[2]∗((S) − (O))` is principal on the affine chart**, over an arbitrary field.  The vanishing
class above, turned back into a generator by `#726`'s principality criterion — which never needed a
hypothesis on `F` at all. -/
theorem exists_divisor_eq_affinePart_pullbackDivisorTwo_of_card_torsion_two (h2 : (2 : F) ≠ 0)
    (hsep : Algebra.IsSeparable ↥(mulByTwoEndo (W := W) h2).fieldRange W.FunctionField)
    (hcard : Nat.card (W.torsion 2) = 4) {S P : W.Point} (hP : 2 • P = S) (hS : 2 • S = 0) :
    ∃ g : W.FunctionField, g ≠ 0 ∧ divisor W g = affinePart W (pullbackDivisorTwo h2
      (Finsupp.single (projPointOfPoint W S) (1 : ℤ)
        - Finsupp.single (none : ProjPoint W) (1 : ℤ))) :=
  (exists_divisor_eq_iff_classOfDivisor_eq_one _).2
    (classOfDivisor_affinePart_pullbackDivisorTwo_eq_one_of_card_torsion_two h2 hsep hcard hP hS)

/-- **`hprin` at `n = 2` over an arbitrary field**, in the shape `exists_gS_two` consumes it.

⚠️ The halving point is a hypothesis here and a *conclusion* in the merged
`exists_nsmul_divisor_eq_divisor_mulByTwoEndo`, where `exists_nsmul_two_eq` produces it from
`[IsAlgClosed F]`.  That is not a formalisation artefact: `[2]` is genuinely not surjective on
`E(F)` for a general `F`.

The rest of the proof is the merged one unchanged — `ordInfty_eq_of_divisor_eq` and
`divisorProj_eq_iff` pin the projective divisor from the affine one, `divisorProj_mulByTwoEndo`
moves `[2]∗` across, and `affinePart` restricts to the chart. -/
theorem exists_nsmul_divisor_eq_divisor_mulByTwoEndo_of_card_torsion_two (h2 : (2 : F) ≠ 0)
    (hsep : Algebra.IsSeparable ↥(mulByTwoEndo (W := W) h2).fieldRange W.FunctionField)
    (hcard : Nat.card (W.torsion 2) = 4) {x y : F}
    (h : W.Nonsingular x y) (hS : Point.some x y h ∈ W.torsion 2)
    {P : W.Point} (hP : 2 • P = Point.some x y h)
    {f : W.FunctionField} (hf : f ≠ 0)
    (hfdiv : divisor W f = Finsupp.single (pointClosedPoint h.left) (2 : ℤ)) :
    ∃ g₀ : W.FunctionField, g₀ ≠ 0 ∧ 2 • divisor W g₀ = divisor W (mulByTwoEndo h2 f) := by
  classical
  obtain ⟨g, hg, hgdiv⟩ :=
    exists_divisor_eq_affinePart_pullbackDivisorTwo_of_card_torsion_two h2 hsep hcard hP
      (mem_torsion_iff.mp hS)
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

/-! ### Rung 5 at `n = 2` over an arbitrary field -/

/-- **Rung 5 of the Weil pairing at `n = 2`, over an arbitrary field.**  `exists_gS_two` with its
`hprin` discharged from three hypotheses none of which is an algebraic closure: the `2`-torsion is
rational (`hcard`), `S` has a rational halving point (`hP`), and `F(W) / [2]∗F(W)` is separable
(`hsep`, free in characteristic zero — see `exists_gS_two_of_charZero`). -/
theorem exists_gS_two_of_card_torsion_two (h2 : (2 : F) ≠ 0)
    (hsep : Algebra.IsSeparable ↥(mulByTwoEndo (W := W) h2).fieldRange W.FunctionField)
    (hcard : Nat.card (W.torsion 2) = 4) {x y : F} (h : W.Nonsingular x y)
    (hS : Point.some x y h ∈ W.torsion 2) {P : W.Point} (hP : 2 • P = Point.some x y h) :
    ∃ f : W.FunctionField, f ≠ 0 ∧
      divisor W f = Finsupp.single (pointClosedPoint h.left) (2 : ℤ) ∧
      ∃ gS : W.FunctionField, gS ≠ 0 ∧
        ∃ u : W.CoordinateRingˣ, (u : W.CoordinateRing) • gS ^ 2 = mulByTwoEndo h2 f :=
  exists_gS_two h2 h hS fun _ hf hfdiv =>
    exists_nsmul_divisor_eq_divisor_mulByTwoEndo_of_card_torsion_two h2 hsep hcard h hS hP hf hfdiv

/-- **Rung 5 at `n = 2` in characteristic zero**, with the separability discharged by
`isSeparable_mulByTwoEndoFieldRange`.  Two hypotheses remain, and both are rationality statements
about finitely many points: `#E[2] = 4` and a halving point for `S`.

This is the form the non-vacuity block below instantiates over `ℚ`. -/
theorem exists_gS_two_of_charZero [CharZero F] (h2 : (2 : F) ≠ 0)
    (hcard : Nat.card (W.torsion 2) = 4) {x y : F} (h : W.Nonsingular x y)
    (hS : Point.some x y h ∈ W.torsion 2) {P : W.Point} (hP : 2 • P = Point.some x y h) :
    ∃ f : W.FunctionField, f ≠ 0 ∧
      divisor W f = Finsupp.single (pointClosedPoint h.left) (2 : ℤ) ∧
      ∃ gS : W.FunctionField, gS ≠ 0 ∧
        ∃ u : W.CoordinateRingˣ, (u : W.CoordinateRing) • gS ^ 2 = mulByTwoEndo h2 f :=
  exists_gS_two_of_card_torsion_two h2 (isSeparable_mulByTwoEndoFieldRange h2) hcard h hS hP

/-! ### Recovery

`#907`: a general form must reach the statements it generalises.  Both merged `[IsAlgClosed F]`
theorems come back **verbatim** — same binders, same conclusion — with the three hypotheses
supplied by `card_torsion_two`, `exists_nsmul_two_eq` and
`isSeparable_mulByTwoEndoFieldRange_of_isAlgClosed`. -/

section Recovery

variable [IsAlgClosed F]

/-- Recovery of `exists_nsmul_divisor_eq_divisor_mulByTwoEndo`
(`EllipticCurves.FunctionField.PullbackPrincipalityTwo`). -/
private theorem exists_nsmul_divisor_eq_divisor_mulByTwoEndo_of_general (h2 : (2 : F) ≠ 0)
    {x y : F} (h : W.Nonsingular x y) (hS : Point.some x y h ∈ W.torsion 2)
    {f : W.FunctionField} (hf : f ≠ 0)
    (hfdiv : divisor W f = Finsupp.single (pointClosedPoint h.left) (2 : ℤ)) :
    ∃ g₀ : W.FunctionField, g₀ ≠ 0 ∧ 2 • divisor W g₀ = divisor W (mulByTwoEndo h2 f) :=
  let ⟨_, hP⟩ := exists_nsmul_two_eq h2 (Point.some x y h)
  exists_nsmul_divisor_eq_divisor_mulByTwoEndo_of_card_torsion_two h2
    (isSeparable_mulByTwoEndoFieldRange_of_isAlgClosed h2) (card_torsion_two h2) h hS hP hf hfdiv

/-- Recovery of `exists_gS_two_of_isAlgClosed`
(`EllipticCurves.FunctionField.PullbackPrincipalityTwo`). -/
private theorem exists_gS_two_of_isAlgClosed_of_general (h2 : (2 : F) ≠ 0) {x y : F}
    (h : W.Nonsingular x y) (hS : Point.some x y h ∈ W.torsion 2) :
    ∃ f : W.FunctionField, f ≠ 0 ∧
      divisor W f = Finsupp.single (pointClosedPoint h.left) (2 : ℤ) ∧
      ∃ gS : W.FunctionField, gS ≠ 0 ∧
        ∃ u : W.CoordinateRingˣ, (u : W.CoordinateRing) • gS ^ 2 = mulByTwoEndo h2 f :=
  let ⟨_, hP⟩ := exists_nsmul_two_eq h2 (Point.some x y h)
  exists_gS_two_of_card_torsion_two h2 (isSeparable_mulByTwoEndoFieldRange_of_isAlgClosed h2)
    (card_torsion_two h2) h hS hP

end Recovery

/-! ### Non-vacuity

`#916`: the hypotheses above have to be exhibited on a curve over a field that is **not**
algebraically closed, or the certificate certifies the merged `F̄` theorem instead of this one.

`y² = x³ − 41x² + 400x = x(x − 16)(x − 25)` over `ℚ` does it.  Its `2`-torsion is
`{O, (0, 0), (16, 0), (25, 0)}` — all three roots of the cubic are rational — and
`P = (40, 120)` has `[2]P = (25, 0)`, so `P` has order `4` and supplies the halving point.
`[CharZero ℚ]` supplies the separability.

⚠️ **The merged file's own fixture cannot be reused here, and the reason is the interesting part.**
`PullbackPrincipalityTwo`'s non-vacuity block runs on `y² = x³ − x` over `AlgebraicClosure ℚ` and
leaves the halving point as a hypothesis of an `example`.  Over `ℚ` that curve satisfies `hcard`
perfectly well — its `2`-torsion `{O, (0,0), (1,0), (−1,0)}` is rational — and still cannot be used,
because no nonzero `2`-torsion point of it is `2`-divisible in `E(ℚ)`: the curve has rank zero and
torsion `(ℤ/2)²`, which is Fermat's descent and is *not* proved in this development.  ⚠️ **The two
hypotheses are genuinely independent**, and a fixture with full rational `2`-torsion is not
automatically a fixture with a rational halving point.  `y² = x³ − x` is now known on this board to
be the wrong fixture at every index past `2` (`#1325`, `#1328`, `#1334`); this is the first index at
which it is the wrong fixture *and* the `2`-torsion count is not what fails.

The order arithmetic that picks the curve: a halving `[2]P = S` with `S` of order `2` forces
`ord P = 4`, so the fixture needs `E(ℚ)_tors ⊇ ℤ/2 × ℤ/4`.  For `y² = x(x − e₂)(x − e₃)` the
`2`-torsion point `(e₁, 0)` is `2`-divisible exactly when `e₁ − e₂` and `e₁ − e₃` are both rational
squares; at `(e₁, e₂, e₃) = (25, 0, 16)` they are `25` and `9`, and the halving point comes out at
`x = e₁ + √((e₁ − e₂)(e₁ − e₃)) = 25 + 15 = 40`. -/

section Nonvacuity

open Polynomial in
/-- `ℚ` is not algebraically closed, from `X² + X + 1` having no rational root.  Without this the
block below would certify the merged `[IsAlgClosed F]` theorem rather than this file's. -/
private lemma rat_not_isAlgClosed : ¬ IsAlgClosed ℚ := by
  intro hcl
  obtain ⟨q, hq⟩ := hcl.exists_root (X ^ 2 + X + 1 : ℚ[X]) (by
    rw [show (X ^ 2 + X + 1 : ℚ[X]) = C 1 * X ^ 2 + C 1 * X + C 1 by simp,
      degree_quadratic one_ne_zero]
    exact two_ne_zero)
  rw [IsRoot, eval_add, eval_add, eval_pow, eval_X, eval_one] at hq
  nlinarith [sq_nonneg (2 * q + 1)]

/-- The curve `y² = x³ − 41x² + 400x = x(x − 16)(x − 25)` over `ℚ`, of discriminant `207360000`. -/
private def exampleCurveQ : Affine ℚ := ⟨0, -41, 0, 400, 0⟩

private instance : exampleCurveQ.IsElliptic := by
  rw [WeierstrassCurve.isElliptic_iff, isUnit_iff_ne_zero]
  norm_num [exampleCurveQ, WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈]

private lemma exampleTwoQ : (2 : ℚ) ≠ 0 := by norm_num

/-- The `2`-torsion point `(0, 0)`. -/
private lemma exampleNs0 : exampleCurveQ.Nonsingular 0 0 :=
  exampleCurveQ.equation_iff_nonsingular.mp (by
    norm_num [exampleCurveQ, WeierstrassCurve.Affine.equation_iff])

/-- The `2`-torsion point `(16, 0)`. -/
private lemma exampleNs16 : exampleCurveQ.Nonsingular 16 0 :=
  exampleCurveQ.equation_iff_nonsingular.mp (by
    norm_num [exampleCurveQ, WeierstrassCurve.Affine.equation_iff])

/-- `S = (25, 0)`, the `2`-torsion point that gets halved. -/
private lemma exampleNs25 : exampleCurveQ.Nonsingular 25 0 :=
  exampleCurveQ.equation_iff_nonsingular.mp (by
    norm_num [exampleCurveQ, WeierstrassCurve.Affine.equation_iff])

/-- `P = (40, 120)`, of order `4`. -/
private lemma exampleNsP : exampleCurveQ.Nonsingular 40 120 :=
  exampleCurveQ.equation_iff_nonsingular.mp (by
    norm_num [exampleCurveQ, WeierstrassCurve.Affine.equation_iff])

open Classical in
private lemma exampleTors0 :
    Point.some (0 : ℚ) 0 exampleNs0 ∈ exampleCurveQ.torsion 2 :=
  (mem_torsion_two_some_iff exampleNs0).mpr (by norm_num [exampleCurveQ])

open Classical in
private lemma exampleTors16 :
    Point.some (16 : ℚ) 0 exampleNs16 ∈ exampleCurveQ.torsion 2 :=
  (mem_torsion_two_some_iff exampleNs16).mpr (by norm_num [exampleCurveQ])

open Classical in
private lemma exampleTors25 :
    Point.some (25 : ℚ) 0 exampleNs25 ∈ exampleCurveQ.torsion 2 :=
  (mem_torsion_two_some_iff exampleNs25).mpr (by norm_num [exampleCurveQ])

open Classical in
/-- **`[2](40, 120) = (25, 0)`, discharged rather than assumed.**  The tangent at `(40, 120)` has
slope `(3·40² − 82·40 + 400) / 240 = 8`, so `x([2]P) = 8² + 41 − 80 = 25` and the `y`-coordinate
comes out `0`. -/
private lemma exampleDouble :
    (2 : ℕ) • Point.some (40 : ℚ) 120 exampleNsP = Point.some (25 : ℚ) 0 exampleNs25 := by
  have hy : (120 : ℚ) ≠ exampleCurveQ.negY 40 120 := by
    norm_num [exampleCurveQ, WeierstrassCurve.Affine.negY]
  rw [two_nsmul, Point.add_self_of_Y_ne hy, Point.some.injEq]
  refine ⟨?_, ?_⟩ <;>
    norm_num [exampleCurveQ, WeierstrassCurve.Affine.addX, WeierstrassCurve.Affine.addY,
      WeierstrassCurve.Affine.negAddY, WeierstrassCurve.Affine.negY,
      WeierstrassCurve.Affine.slope]

open Classical in
/-- **`#E[2] = 4` over `ℚ`, proved rather than assumed.**  `card_torsion_two_le` is unconditional,
and the four named points give the reverse inequality — so the algebraically closed base field is
not smuggled back in through the count. -/
private lemma exampleCard : Nat.card (exampleCurveQ.torsion 2) = 4 := by
  haveI := exampleCurveQ.finite_torsion_two exampleTwoQ
  refine le_antisymm (card_torsion_two_le exampleTwoQ) ?_
  have hinj : Function.Injective (fun i : Fin 4 =>
      (![(0 : exampleCurveQ.torsion 2), ⟨_, exampleTors0⟩, ⟨_, exampleTors16⟩,
        ⟨_, exampleTors25⟩] i)) := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [Subtype.ext_iff, Point.zero_def]
  simpa using Nat.card_le_card_of_injective _ hinj

open Classical in
/-- **The headline, committed over a field that is not algebraically closed**: rung 5 at `n = 2`
with `hprin` discharged, on `y² = x³ − 41x² + 400x` over `ℚ` at `S = (25, 0)`.

Every hypothesis is proved: `#E[2] = 4` is `exampleCard`, the halving is `exampleDouble`, the
separability comes from `[CharZero ℚ]`, and `ℚ` is not algebraically closed
(`rat_not_isAlgClosed`), so `exists_gS_two_of_isAlgClosed` does not apply here. -/
example : ∃ f : exampleCurveQ.FunctionField, f ≠ 0 ∧
    exampleCurveQ.divisor f
      = Finsupp.single (pointClosedPoint exampleNs25.left) (2 : ℤ) ∧
    ∃ gS : exampleCurveQ.FunctionField, gS ≠ 0 ∧
      ∃ u : exampleCurveQ.CoordinateRingˣ,
        (u : exampleCurveQ.CoordinateRing) • gS ^ 2 = mulByTwoEndo exampleTwoQ f :=
  exists_gS_two_of_charZero exampleTwoQ exampleCard exampleNs25 exampleTors25 exampleDouble

end Nonvacuity

end WeierstrassCurve.Affine
