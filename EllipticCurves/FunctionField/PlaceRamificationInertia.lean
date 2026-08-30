/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import EllipticCurves.FunctionField.MulByTwoGalois
import EllipticCurves.FunctionField.PlacePrimesOverFibre
import EllipticCurves.FunctionField.PlaceResidueDegree

/-!
# The ramification and inertia compatibilities, and the fundamental identity for `[2]`

`EllipticCurves.FunctionField.PlacePrimesOverFibre` (`#755`) matches the primes of
`B = integralClosure (placeBelow φ q) F(W)` lying over the maximal ideal of `A = placeBelow φ q`
with the points of the fibre of the contraction `comapProjPoint φ` over `q`.  That is the index-set
half of

```lean
-- Mathlib/RingTheory/RamificationInertia/Basic.lean
theorem Ideal.sum_ramification_inertia_eq_finrank
    [IsDomain R] [Module.Finite R S] [Module.Flat R S] [Fintype (p.primesOver S)] :
    ∑ q : p.primesOver S, q.1.ramificationIdx R * q.1.inertiaDeg R = Module.finrank R S
```

What was still missing is the *summands*: nothing related Mathlib's `Ideal.ramificationIdx` and
`Ideal.inertiaDeg` to this development's `ramificationIdx` (`#668`) and `residueDegreeComap`
(`#744`).  This file supplies both and fires the theorem.

## The two compatibilities

Both are theorems rather than transports of a definition, and they are proved by completely
different means.

* **`WeierstrassCurve.Affine.ideal_ramificationIdx_eq_toNat`** — for a height-one prime `v` of `B`
  lying over the maximal ideal of `A`,

  ```
  v.asIdeal.ramificationIdx A = (ramificationIdx hφF hφint (projPointOfHeightOne φ hφF q v)).toNat.
  ```

  Mathlib's index is a length, reduced by `Ideal.ramificationIdx'_eq_ramificationIdx` to the `sSup`
  of the `n` with `𝔪_A B ⊆ P ^ n`; this development's is extracted by choice from
  `exists_ramificationIdx` and characterised only through `divisorProj_comp_apply`.  The bridge is
  the *order function*: `count_eq_divisorProj` identifies the `v`-adic order on `F(W)` with
  `divisorProj W · p`, because the two are `ℤ`-valued, additive, attain `1`, and have the same
  nonnegativity locus — `placeOf W p` *is* the localisation `B_v`, by `#755`'s
  `placeOf_projPointOfHeightOne`.  With that, `𝔪_A B ⊆ P ^ n` unwinds to `n ≤ e_p` and
  `Ideal.ramificationIdx'_spec` reads off the index.  This is the step `#755` predicted would be
  expensive, and it is.
* **`WeierstrassCurve.Affine.ideal_inertiaDeg_eq_one`** — over `[IsAlgClosed F]`,
  `v.asIdeal.inertiaDeg A = 1`.  The residue field of `A` is `F` (`#743`/`#749`), and every element
  of `B` is congruent modulo `P` to a constant: reduce it in `κ(p)`, which is `F` by
  `algebraMap_residueFieldProj_bijective`, and subtract.  No identification of `B ⧸ P` with a
  residue field of a localisation is needed, which is what makes this cheap.

## Main results

* `WeierstrassCurve.Affine.count_eq_divisorProj` — the order bridge;
* **`WeierstrassCurve.Affine.residueDegreeComap_none_eq_one`** — `f_∞ = 1` for an arbitrary `φ`,
  with no `Module.Finite`, no separability and no hypothesis on `F`, together with its companion
  `residueDegreeProj_comapProjPoint_none_eq_one`.  ⚠️ Unlike the ramification index, this one is
  free at every `φ`; see its docstring;
* **`WeierstrassCurve.Affine.ideal_ramificationIdx_eq_toNat`** and
  **`WeierstrassCurve.Affine.ideal_inertiaDeg_eq_one`** — the two compatibilities;
* `WeierstrassCurve.Affine.sum_ramificationIdx_mul_inertiaDeg_placeBelow` — the fundamental
  identity in Mathlib's own indexing, with `Module.Finite` and `Module.Flat` discharged and the
  `Fintype` on the index set carried as an instance argument, since the sum cannot be stated
  without it.  **No hypothesis on `F` beyond the separability `#754` carries**, so this is the form
  to use over `ℚ`;
* **`WeierstrassCurve.Affine.sum_toNat_ramificationIdx_fibre`** — over `[IsAlgClosed F]`, the
  identity in *this* development's indexing:
  `∑_{p ↦ q} e_p = finrank A B`;
* **`WeierstrassCurve.Affine.CoordinateRing.sum_ramificationIdxTwo_eq_four`** and
  `sum_ramificationIdxTwo_mul_residueDegreeTwo` — the `[2]∗` instantiation, `∑_{p ↦ q} e_p = 4` and
  `∑_{p ↦ q} e_p · f_p = 4`;
* `WeierstrassCurve.Affine.CoordinateRing.card_fibre_comapProjPointTwo_le_four` — the fibre has at
  most four elements.  (Nonemptiness is `#755`'s `nonempty_fibre_comapProjPointTwo`.)  These two are
  what the Weil-pairing front consumes;
* `WeierstrassCurve.Affine.CoordinateRing.sum_ramificationIdxTwo_erase_none_eq_three` — at
  `q = none`: `[2]` fixes the point at infinity and is unramified there (`#670`), so the identity
  predicts **three further places above infinity**.

## What is *not* here

* **The general form of the inertia compatibility is not in *this file*.**
  `ideal_inertiaDeg_eq_one` is the `[IsAlgClosed F]` form that `#763`'s deliverable 1 calls "cheap
  partial credit", and `sum_ramificationIdxTwo_mul_residueDegreeTwo` below is stated over
  `[IsAlgClosed F]`, where `residueDegreeTwo h2 p = 1` at every place and the statement collapses
  to the previous one.
  ⚠️ **The clauses this bullet used to carry have been paid** — it read *"the unconditional
  `Ideal.inertiaDeg 𝔪 P = residueDegreeTwo h2 p` is **not** proved, and would need `B ⧸ P` to be
  identified with the residue field of the localisation `B_v = placeOf W p` and `A ⧸ 𝔪_A` with
  `κ(q)`, compatibly with the two algebra maps … Over `ℚ` what is available is
  `sum_ramificationIdx_mul_inertiaDeg_placeBelow`, in Mathlib's indexing."*  Both identifications
  are made and the compatibility is proved over an arbitrary field in
  `EllipticCurves.FunctionField.PlaceInertiaGeneral`, which imports this file:
  `placeComapEquivPlaceBelow`, `valuationSubringAtPrimeEquivPlace` and
  `ideal_inertiaDeg_eq_residueDegreeComap`.  The fibre-indexed identity follows there as
  `sum_toNat_ramificationIdx_mul_residueDegreeComap_fibre`, and over `ℚ` the `[2]∗` form in *this*
  file's own indexing is `sum_ramificationIdxTwo_mul_residueDegreeTwo_of_charZero`.
* **`#E[2] = 4`.**  The identity says the fibre of `[2]` over a place has total ramification `4`;
  it says nothing about the number of `2`-torsion *points*.  The classical link runs through
  "a separable isogeny has `#ker = deg`", which is **not** in this tree — separability of the field
  extension `F(W) / [2]∗F(W)` is (`#759`), but the counting step is a different statement.  **Do not
  read `#E[2] = 4` off this file.**
* `[3]∗` and general `[n]∗`: everything before the `[2]∗` section is stated for an arbitrary `φ` and
  serves them unchanged, but the right-hand side `4` is `[2]`-specific (`#682`'s tower rests on
  `max (deg Φ₂) (deg Ψ₂Sq) = 4`).  The `[3]∗` instantiation, with `9` in place of the `4`, is
  `EllipticCurves.FunctionField.MulByThreeRamification`; general `[n]∗` has no case here.
  ⚠️ **The reason clause this bullet used to give has been paid** — it read *"`mulByNEndo` not
  existing"*.  `[n]∗` at every `n` is `mulByNEndo`,
  `EllipticCurves.FunctionField.MulByNPullback`, with its place layer in
  `EllipticCurves.FunctionField.MulByNPlacePullback`; what is `[2]`-specific is the `4`, as this
  bullet already says.
* Any comparison with `degPt` (`DivisorDegree.lean`), which is a relative ideal norm to `F[X]` and
  so not *definitionally* a residue-field degree.  ⚠️ **This bullet used to end** *"and not a
  residue-field degree"*, with no qualifier, and that is the one reading of it that is now wrong:
  the two constructions really do differ, but their **values agree over an arbitrary base field** —
  `degPt_eq_residueDegreeProj` at an affine place and `degProjPt_eq_residueDegreeProj` at every
  `p : ProjPoint W` (`EllipticCurves.FunctionField.PlaceDegreeComparison`).  ⚠️ Only the gloss
  changes: that file is **downstream** of this one, so no comparison is made here and nothing below
  assumes any relation between the two.

## The `_of_isAlgClosed` companions live here, not in `PlaceBelowIntegralClosure`

`#754` ships `module_finite_integralClosure_placeBelowTwo` (separability hypothesised) and
`…_of_charZero`; `#759` supplies separability over `[IsAlgClosed F]` in every characteristic `≠ 2`.
The matching `…_of_isAlgClosed` companions are below rather than next to their `…_of_charZero`
siblings because `EllipticCurves.FunctionField.PlaceBelowIntegralClosure` does not import
`EllipticCurves.FunctionField.MulByTwoGalois`, and adding that import would pull the translation
action and Mathlib's Galois theory into the cone of every consumer of the place-below layer.  The
two hypotheses remain **incomparable**: `[CharZero F]` needs no algebraic closure and is the one to
use over `ℚ` or a number field.

## References

* [J. H. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], II.2.
* Stichtenoth, *Algebraic Function Fields and Codes*, III.1.11.
-/

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum FractionalIdeal Module

open scoped nonZeroDivisors

namespace IsDedekindDomain.HeightOneSpectrum

/-! ### The `count` order function of a height-one prime, on the fraction field

`FractionalIdeal.count K v ⟨x⟩` is the exponent of `v` in the principal fractional ideal generated
by `x` — the additive `v`-adic order, with the junk value `0` at `0`.  This development's `ord`
(`Divisors.lean`) is this function at `R = F[W]`; the three lemmas here are the general forms of
what `PlaceOrder.lean` proves there, and they are what identify the order at a prime of the
integral closure with `divisorProj` below.  Nothing here mentions curves. -/

variable {R : Type*} [CommRing R] [IsDedekindDomain R]
  {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K] (v : HeightOneSpectrum R)

/-- **The localisation of `R` at `v` is the nonnegativity locus of the `v`-adic order.**  The
general form of `mem_valuationSubringAtPrime_iff_ord_nonneg` (`PlaceOrder.lean`). -/
theorem mem_valuationSubringAtPrime_iff_count_nonneg {f : K} (hf : f ≠ 0) :
    f ∈ valuationSubringAtPrime K v ↔ 0 ≤ count K v (spanSingleton R⁰ f) := by
  rw [valuationSubringAtPrime_eq_valuationSubring, Valuation.mem_valuationSubring_iff,
    valuation_eq_exp_neg_count v hf, ← WithZero.exp_zero, WithZero.exp_le_exp, neg_nonpos]

/-- **The `v`-adic order is additive on nonzero products.**  The general form of `ord_mul`. -/
theorem count_spanSingleton_mul {f g : K} (hf : f ≠ 0) (hg : g ≠ 0) :
    count K v (spanSingleton R⁰ (f * g))
      = count K v (spanSingleton R⁰ f) + count K v (spanSingleton R⁰ g) := by
  have hf' : spanSingleton R⁰ f ≠ 0 := by rwa [ne_eq, spanSingleton_eq_zero_iff]
  have hg' : spanSingleton R⁰ g ≠ 0 := by rwa [ne_eq, spanSingleton_eq_zero_iff]
  rw [← spanSingleton_mul_spanSingleton, count_mul _ _ hf' hg']

/-- **The `v`-adic order attains the value `1`**, on a uniformizer.  This is what pins it down: an
order function is determined by its nonnegativity locus only once it is known to be surjective. -/
theorem exists_count_spanSingleton_eq_one :
    ∃ π : K, π ≠ 0 ∧ count K v (spanSingleton R⁰ π) = 1 := by
  obtain ⟨π, hπ⟩ := valuation_exists_uniformizer K v
  have h0 : π ≠ 0 := by
    intro h
    rw [h, map_zero] at hπ
    exact WithZero.exp_ne_zero hπ.symm
  exact ⟨π, h0, by rw [count_eq_neg_log_valuation v h0, hπ, WithZero.log_exp, neg_neg]⟩

end IsDedekindDomain.HeightOneSpectrum

namespace WeierstrassCurve.Affine

variable {F : Type*} [Field F] {W : Affine F} [IsDedekindDomain W.CoordinateRing]
  {φ : W.FunctionField →+* W.FunctionField} {q : ProjPoint W}
  (hφF : ∀ c : F, φ (algebraMap F W.FunctionField c) = algebraMap F W.FunctionField c)
  (hφint : ∀ z : W.FunctionField, φ.IsIntegralElem z)

/-! ### A uniformizer of the place below

`Ideal.ramificationIdx'` compares `𝔪_A B` with the powers of `P`, so the first thing needed is a
generator of `𝔪_A`.  A place below is a discrete valuation ring (`#753`, `#754`), and its
uniformizers are the images under `placeBelowEquiv` of the uniformizers of `placeOf W q`, which
`#753`'s `irreducible_placeOf_iff` characterises by `divisorProj … = 1`.  Carrying the preimage
along is what lets `divisorProj_comp_apply` be applied to it. -/

/-- **A uniformizer of the place below, with its preimage in `F(W)`.**  The maximal ideal of
`placeBelow φ q` is generated by `πA`, and `πA` is `φ` applied to a function of order `1` at `q`. -/
theorem exists_uniformizer_placeBelow (q : ProjPoint W) :
    ∃ πA : ↥(placeBelow φ q), IsLocalRing.maximalIdeal ↥(placeBelow φ q) = Ideal.span {πA} ∧
      ∃ π₀ : W.FunctionField, π₀ ≠ 0 ∧ divisorProj W π₀ q = 1 ∧
        ((πA : ↥φ.fieldRange) : W.FunctionField) = φ π₀ := by
  obtain ⟨π₀, hπ₀0, hπ₀⟩ := exists_divisorProj_eq_one (W := W) q
  have hmem : π₀ ∈ placeOf W q :=
    (mem_placeOf_iff_divisorProj_nonneg q hπ₀0).2 (by rw [hπ₀]; norm_num)
  refine ⟨placeBelowEquiv φ q ⟨π₀, hmem⟩, ?_, π₀, hπ₀0, hπ₀, ?_⟩
  · refine (IsDiscreteValuationRing.irreducible_iff_uniformizer _).1 ?_
    change Irreducible ((placeBelowEquiv φ q).toMulEquiv ⟨π₀, hmem⟩)
    rw [MulEquiv.irreducible_iff]
    exact (irreducible_placeOf_iff ⟨π₀, hmem⟩).2 hπ₀
  · rw [coe_placeBelowEquiv, RingHom.rangeRestrictFieldEquiv_apply_coe]

section Dedekind

variable [Module.Finite ↥φ.fieldRange W.FunctionField]
  [Algebra.IsSeparable ↥φ.fieldRange W.FunctionField]
  (v : HeightOneSpectrum ↥(integralClosure ↥(placeBelow φ q) W.FunctionField))

/-! ### The order bridge

`#755`'s `placeOf_projPointOfHeightOne` says the place of the point attached to `v` **is** the
localisation `B_v`.  Two `ℤ`-valued order functions on `F(W)` with the same nonnegativity locus,
each attaining `1`, are equal (`PlaceOrder.lean`'s `eq_of_nonneg_iff_of_exists_eq_one`), so the
`v`-adic order and `divisorProj W · p` are the same function.  Everything about ramification below
runs on this one lemma. -/

/-- **The `v`-adic order on `F(W)` is `divisorProj` at the point `v` names.** -/
theorem count_eq_divisorProj {g : W.FunctionField} (hg : g ≠ 0) :
    count W.FunctionField v
        (spanSingleton (integralClosure ↥(placeBelow φ q) W.FunctionField)⁰ g)
      = divisorProj W g (projPointOfHeightOne φ hφF q v) := by
  refine eq_of_nonneg_iff_of_exists_eq_one
    (φ := fun x => count W.FunctionField v
      (spanSingleton (integralClosure ↥(placeBelow φ q) W.FunctionField)⁰ x))
    (ψ := fun x => divisorProj W x (projPointOfHeightOne φ hφF q v))
    (fun x y hx hy => count_spanSingleton_mul v hx hy)
    (fun x y hx hy => by rw [divisorProj_mul hx hy, Finsupp.add_apply])
    (fun x hx => ?_) (exists_count_spanSingleton_eq_one v) (exists_divisorProj_eq_one _) hg
  rw [← mem_valuationSubringAtPrime_iff_count_nonneg v hx,
    ← mem_placeOf_iff_divisorProj_nonneg _ hx, placeOf_projPointOfHeightOne hφF v]

/-! ### The ramification compatibility -/

/-- **`𝔪_A B ⊆ P ^ n` exactly when `n ≤ e_p`.**  `𝔪_A` is generated by a uniformizer `πA`, whose
image in `F(W)` is `φ` of a function of order `1` at `q`, so `ord_p (πA) = e_p · 1` by
`divisorProj_comp_apply`; and membership of `P ^ n` is a bound on the `v`-adic order, which is that
same `ord_p` by `count_eq_divisorProj`. -/
theorem map_maximalIdeal_le_pow_iff
    (hp : comapProjPoint hφF hφint (projPointOfHeightOne φ hφF q v) = q) (n : ℕ) :
    Ideal.map (algebraMap ↥(placeBelow φ q)
        ↥(integralClosure ↥(placeBelow φ q) W.FunctionField))
        (IsLocalRing.maximalIdeal ↥(placeBelow φ q)) ≤ v.asIdeal ^ n
      ↔ (n : ℤ) ≤ ramificationIdx hφF hφint (projPointOfHeightOne φ hφF q v) := by
  obtain ⟨πA, hspan, π₀, h00, h01, hcoe⟩ := exists_uniformizer_placeBelow (φ := φ) q
  have hne : ((πA : ↥φ.fieldRange) : W.FunctionField) ≠ 0 := by
    rw [hcoe]
    exact fun h => h00 (φ.injective (by rw [h, map_zero]))
  have hord : divisorProj W ((πA : ↥φ.fieldRange) : W.FunctionField)
      (projPointOfHeightOne φ hφF q v)
      = ramificationIdx hφF hφint (projPointOfHeightOne φ hφF q v) := by
    rw [hcoe, divisorProj_comp_apply hφF hφint h00 _, hp, h01, mul_one]
  rw [hspan, Ideal.map_span, Set.image_singleton, Ideal.span_singleton_le_iff_mem,
    ← intValuation_le_pow_iff_mem, ← valuation_of_algebraMap (K := W.FunctionField)]
  change valuation W.FunctionField v ((πA : ↥φ.fieldRange) : W.FunctionField)
    ≤ WithZero.exp (-(n : ℤ)) ↔ _
  rw [valuation_eq_exp_neg_count v hne, count_eq_divisorProj hφF v hne, hord,
    WithZero.exp_le_exp, neg_le_neg_iff]

/-- **The ramification compatibility.**  Mathlib's ramification index of `v` over the place below
is this development's ramification index of `φ` at the point `v` names.

`toNat` is safe because `ramificationIdx_pos` makes the `ℤ`-valued index strictly positive. -/
theorem ideal_ramificationIdx_eq_toNat
    [hlies : v.asIdeal.LiesOver (IsLocalRing.maximalIdeal ↥(placeBelow φ q))] :
    v.asIdeal.ramificationIdx ↥(placeBelow φ q)
      = (ramificationIdx hφF hφint (projPointOfHeightOne φ hφF q v)).toNat := by
  have hp : comapProjPoint hφF hφint (projPointOfHeightOne φ hφF q v) = q :=
    (comapProjPoint_projPointOfHeightOne_eq_iff hφF hφint v).2 hlies.over.symm
  have hpos := ramificationIdx_pos hφF hφint (projPointOfHeightOne φ hφF q v)
  rw [← Ideal.ramificationIdx'_eq_ramificationIdx _ _ (maximalIdeal_placeBelow_ne_bot q)]
  refine Ideal.ramificationIdx'_spec ?_ ?_
  · rw [map_maximalIdeal_le_pow_iff hφF hφint v hp]
    omega
  · rw [map_maximalIdeal_le_pow_iff hφF hφint v hp]
    push_cast
    omega

/-! ### The inertia compatibility, over an algebraically closed base field

`#763`'s deliverable 1 allows the `[IsAlgClosed F]` form, and it is genuinely cheaper: it needs no
identification of `B ⧸ P` with the residue field of the localisation.  Every element of `B` is
regular at `p`, its residue lies in `κ(p) = F` (`#743`/`#749`), and the difference with the
corresponding constant — which lies in `A`, because `φ` fixes `F` — is a nonunit of `B_v`, hence in
`P`. -/

include hφF hφint in
/-- **Every element of `B` is congruent to a constant modulo `P`**, over an algebraically closed
base field.  This is the inertia compatibility in its working form. -/
theorem algebraMap_quotient_asIdeal_surjective [IsAlgClosed F]
    [hlies : v.asIdeal.LiesOver (IsLocalRing.maximalIdeal ↥(placeBelow φ q))] :
    Function.Surjective (algebraMap
      (↥(placeBelow φ q) ⧸ IsLocalRing.maximalIdeal ↥(placeBelow φ q))
      (↥(integralClosure ↥(placeBelow φ q) W.FunctionField) ⧸ v.asIdeal)) := by
  have hp : comapProjPoint hφF hφint (projPointOfHeightOne φ hφF q v) = q :=
    (comapProjPoint_projPointOfHeightOne_eq_iff hφF hφint v).2 hlies.over.symm
  intro x
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective x
  have hb : (b : W.FunctionField) ∈ placeOf W (projPointOfHeightOne φ hφF q v) :=
    mem_placeOf_of_mem_integralClosure hφF hφint hp b.2
  obtain ⟨c, hc⟩ := (algebraMap_residueFieldProj_bijective
    (projPointOfHeightOne φ hφF q v)).surjective
    (IsLocalRing.residue _ (⟨(b : W.FunctionField), hb⟩ :
      ↥(placeOf W (projPointOfHeightOne φ hφF q v))))
  have hcA : (⟨algebraMap F W.FunctionField c, ⟨algebraMap F W.FunctionField c, hφF c⟩⟩ :
      ↥φ.fieldRange) ∈ placeBelow φ q :=
    mem_placeBelow_of_coe_eq_algebraMap hφF c _ rfl
  refine ⟨Ideal.Quotient.mk _ ⟨_, hcA⟩, ?_⟩
  rw [Ideal.Quotient.algebraMap_mk_of_liesOver]
  refine (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).2 ?_
  rw [HeightOneSpectrum.mem_asIdeal_iff_mem_nonunits (K := W.FunctionField),
    ← placeOf_projPointOfHeightOne hφF v]
  have hmem : ((algebraMap F ↥(placeOf W (projPointOfHeightOne φ hφF q v)) c
        - ⟨(b : W.FunctionField), hb⟩ :
        ↥(placeOf W (projPointOfHeightOne φ hφF q v)))) ∈ IsLocalRing.maximalIdeal _ := by
    have h1 : algebraMap F (residueFieldProj W (projPointOfHeightOne φ hφF q v)) c
        = Ideal.Quotient.mk (IsLocalRing.maximalIdeal _)
          (algebraMap F ↥(placeOf W (projPointOfHeightOne φ hφF q v)) c) :=
      IsScalarTower.algebraMap_apply F _ _ c
    exact (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).1 (h1.symm.trans hc)
  exact ValuationSubring.coe_mem_nonunits_iff.2 hmem

include hφF hφint in
/-- **The inertia compatibility over an algebraically closed base field**: every place is
residually trivial, so Mathlib's inertia degree is `1`.

This is the numerical input that collapses `∑ e_p · f_p = deg` to `∑ e_p = deg`. -/
theorem ideal_inertiaDeg_eq_one [IsAlgClosed F]
    [v.asIdeal.LiesOver (IsLocalRing.maximalIdeal ↥(placeBelow φ q))] :
    v.asIdeal.inertiaDeg ↥(placeBelow φ q) = 1 := by
  haveI : v.asIdeal.IsMaximal := v.isPrime.isMaximal v.ne_bot
  haveI : (IsLocalRing.maximalIdeal ↥(placeBelow φ q)).IsMaximal :=
    IsLocalRing.maximalIdeal.isMaximal _
  haveI : Nontrivial (↥(placeBelow φ q) ⧸ IsLocalRing.maximalIdeal ↥(placeBelow φ q)) :=
    Ideal.Quotient.nontrivial_iff.2 (IsLocalRing.maximalIdeal.isMaximal _).ne_top
  have hbij : Function.Bijective (algebraMap
      (↥(placeBelow φ q) ⧸ IsLocalRing.maximalIdeal ↥(placeBelow φ q))
      (↥(integralClosure ↥(placeBelow φ q) W.FunctionField) ⧸ v.asIdeal)) :=
    ⟨(faithfulSMul_iff_algebraMap_injective _ _).1 inferInstance,
      algebraMap_quotient_asIdeal_surjective hφF hφint v⟩
  rw [Ideal.inertiaDeg_eq_of_isMaximal (IsLocalRing.maximalIdeal ↥(placeBelow φ q)) v.asIdeal,
    ← Module.finrank_self (↥(placeBelow φ q) ⧸ IsLocalRing.maximalIdeal ↥(placeBelow φ q))]
  exact ((AlgEquiv.ofBijective (Algebra.ofId _ _) hbij).toLinearEquiv.finrank_eq).symm

/-! ### The fundamental identity

`#754` supplies `Module.Finite` and `Module.Flat`, `#755` supplies the finiteness of the index set,
and `#754`'s `finrank_integralClosure_placeBelow` supplies the right-hand side.  The first statement
is Mathlib's, with the first two of those discharged and nothing assumed about `F`; the second
transports it along `#755`'s dictionary, turns the `Finite` into a `Fintype` in its proof, and uses
both compatibilities, so it needs `[IsAlgClosed F]`. -/

/-- **The fundamental identity, in Mathlib's indexing.**  Two of the three hypotheses of
`Ideal.sum_ramification_inertia_eq_finrank` — `Module.Finite` and `Module.Flat` — are discharged
here from `#754`.  The third, `Fintype` of the index set, is **not**: the sum cannot be written
without it, so it stays an instance argument.  Supply it with `Fintype.ofFinite` of `#755`'s
`finite_primesOver_maximalIdeal_placeBelow`, in a `haveI` at the use site, as
`sum_toNat_ramificationIdx_fibre` below does — that keeps the noncomputable choice out of every
statement.

No hypothesis on `F` beyond the separability `#754` already carries — in particular this is the form
available over `ℚ`. -/
theorem sum_ramificationIdx_mul_inertiaDeg_placeBelow
    [Fintype ↥((IsLocalRing.maximalIdeal ↥(placeBelow φ q)).primesOver
      ↥(integralClosure ↥(placeBelow φ q) W.FunctionField))] :
    ∑ P : ↥((IsLocalRing.maximalIdeal ↥(placeBelow φ q)).primesOver
        ↥(integralClosure ↥(placeBelow φ q) W.FunctionField)),
        P.1.ramificationIdx ↥(placeBelow φ q) * P.1.inertiaDeg ↥(placeBelow φ q)
      = finrank ↥(placeBelow φ q) ↥(integralClosure ↥(placeBelow φ q) W.FunctionField) := by
  haveI : Module.Finite ↥(placeBelow φ q)
      ↥(integralClosure ↥(placeBelow φ q) W.FunctionField) :=
    module_finite_integralClosure_placeBelow q
  haveI : Module.Flat ↥(placeBelow φ q)
      ↥(integralClosure ↥(placeBelow φ q) W.FunctionField) :=
    module_flat_integralClosure_placeBelow q
  exact Ideal.sum_ramification_inertia_eq_finrank _ _

include hφF hφint in
/-- **The fundamental identity in this development's indexing**, over an algebraically closed base
field: the ramification indices of the places above `q` sum to the rank of the integral closure.

The transport is `#755`'s `primesOverEquivFibre`; the two compatibilities turn each summand
`e_P · f_P` into `e_p`. -/
theorem sum_toNat_ramificationIdx_fibre [IsAlgClosed F] :
    ∑ p ∈ (finite_comapProjPoint_preimage_singleton hφF hφint q).toFinset,
        (ramificationIdx hφF hφint p).toNat
      = finrank ↥(placeBelow φ q) ↥(integralClosure ↥(placeBelow φ q) W.FunctionField) := by
  haveI : Finite ↥((IsLocalRing.maximalIdeal ↥(placeBelow φ q)).primesOver
      ↥(integralClosure ↥(placeBelow φ q) W.FunctionField)) :=
    finite_primesOver_maximalIdeal_placeBelow hφF hφint
  haveI := Fintype.ofFinite ↥((IsLocalRing.maximalIdeal ↥(placeBelow φ q)).primesOver
    ↥(integralClosure ↥(placeBelow φ q) W.FunctionField))
  rw [← sum_ramificationIdx_mul_inertiaDeg_placeBelow (φ := φ) (q := q), ← Finset.sum_coe_sort]
  refine Eq.symm (Fintype.sum_equiv ((primesOverEquivFibre hφF hφint).trans
    (Equiv.subtypeEquivRight fun x => (Set.Finite.mem_toFinset _).symm)) _ _ fun P => ?_)
  haveI : (heightOneOfPrimesOver P).asIdeal.LiesOver
      (IsLocalRing.maximalIdeal ↥(placeBelow φ q)) := P.2.2
  change (heightOneOfPrimesOver P).asIdeal.ramificationIdx ↥(placeBelow φ q)
      * (heightOneOfPrimesOver P).asIdeal.inertiaDeg ↥(placeBelow φ q) = _
  rw [ideal_inertiaDeg_eq_one hφF hφint (heightOneOfPrimesOver P), mul_one,
    ideal_ramificationIdx_eq_toNat hφF hφint (heightOneOfPrimesOver P)]
  rfl

end Dedekind

/-! ### The relative residue degree at the point at infinity, for an arbitrary `φ`

Unlike everything above, this needs neither `Module.Finite` nor separability — nor, for that
matter, anything about `φ` beyond the two standing hypotheses.  It is stated here because this is
the first module downstream of both halves it consumes: the collapse lemma
`residueDegreeComap_eq_one_of_residueDegreeProj_eq_one`
(`EllipticCurves.FunctionField.PlaceResidueComap`) and the unconditional
`residueDegreeProj_none_eq_one` (`EllipticCurves.FunctionField.PlaceResidueDegree`). -/

/-- **Every `F`-fixing endomorphism over which `F(W)` is integral is residually trivial at the
point at infinity**: `f_∞ = 1`, with no hypothesis on `F` and none on `φ` beyond the standing two.

The reason has nothing to do with ramification, or with the fibre, or with `φ`: `[0 : 1 : 0]` is a
rational point of *every* Weierstrass curve, so `residueDegreeProj W none = 1` unconditionally, and
the tower formula `[κ(q) : F] · f_∞ = [κ(∞) : F]` then reads `d · f_∞ = 1` in `ℕ`, which forces
both factors to be `1`.

⚠️ **Contrast the ramification index**, which is *not* like this: `ramificationIdxTwo_none` and
`ramificationIdxThree_none` are proved from a pole order, and the general-`n` statement
(`EllipticCurves.FunctionField.MulByNPlaceComposition`, `#1214`) holds only at `3`-smooth `n` and
is false in general.  The two local invariants at infinity have genuinely different hypothesis
sets, and that is the interesting thing about them. -/
theorem residueDegreeComap_none_eq_one :
    residueDegreeComap hφF hφint (none : ProjPoint W) = 1 :=
  (residueDegreeComap_eq_one_of_residueDegreeProj_eq_one hφF hφint
    (residueDegreeProj_none_eq_one W)).2

/-- **The place below the point at infinity is rational too**, the other half of the same
collapse: `[κ(comapProjPoint φ ∞) : F] = 1`.  A degree-one extension of `F` sits under nothing but
`F`. -/
theorem residueDegreeProj_comapProjPoint_none_eq_one :
    residueDegreeProj W (comapProjPoint hφF hφint (none : ProjPoint W)) = 1 :=
  (residueDegreeComap_eq_one_of_residueDegreeProj_eq_one hφF hφint
    (residueDegreeProj_none_eq_one W)).1

/-! ### The `[2]∗` instantiation

Everything above is stated for an arbitrary `φ` fixing `F` with `F(W)` integral over its image, so
`[3]∗` and general `[n]∗` will use it unchanged.  Here it is specialised to `[2]∗`, over an
algebraically closed base field of characteristic `≠ 2` — where `#759` makes the separability
hypothesis of `#754` and `#755` free, so none of the statements below carries it. -/

namespace CoordinateRing

variable [W.IsElliptic] (h2 : (2 : F) ≠ 0) (q : ProjPoint W)

/-! #### The `_of_isAlgClosed` companions

`#754` and `#755` state their `[2]∗` results either with `Algebra.IsSeparable` as an explicit
hypothesis or over `[CharZero F]`.  `#759` closes the third case; these are the resulting
unconditional forms over `[IsAlgClosed F]`, which is the hypothesis the `#418`/`#465` front carries.
See the module docstring for why they are here rather than beside their `…_of_charZero` siblings. -/

section IsAlgClosed

variable [IsAlgClosed F]

/-- **The integral closure of a place of `[2]∗F(W)` is module-finite over it**, over an
algebraically closed base field, in every characteristic `≠ 2`. -/
theorem module_finite_integralClosure_placeBelowTwo_of_isAlgClosed :
    Module.Finite ↥(placeBelowTwo W h2 q)
      ↥(integralClosure ↥(placeBelowTwo W h2 q) W.FunctionField) :=
  module_finite_integralClosure_placeBelowTwo h2
    (isSeparable_mulByTwoEndoFieldRange_of_isAlgClosed h2) q

/-- **The rank is `4`**, over an algebraically closed base field. -/
theorem finrank_integralClosure_placeBelowTwo_of_isAlgClosed :
    finrank ↥(placeBelowTwo W h2 q)
      ↥(integralClosure ↥(placeBelowTwo W h2 q) W.FunctionField) = 4 :=
  finrank_integralClosure_placeBelowTwo h2
    (isSeparable_mulByTwoEndoFieldRange_of_isAlgClosed h2) q

/-- **The `primesOver` ↔ fibre dictionary**, over an algebraically closed base field.

⚠️ `nolint defsWithUnderscore` (`#1277`): `_of_isAlgClosed` matches
`finrank_integralClosure_placeBelowTwo_of_isAlgClosed` directly above, which is the theorem this
`def` is the dictionary for. -/
@[nolint defsWithUnderscore]
noncomputable def primesOverEquivFibreTwo_of_isAlgClosed :
    ↥((IsLocalRing.maximalIdeal ↥(placeBelowTwo W h2 q)).primesOver
        ↥(integralClosure ↥(placeBelowTwo W h2 q) W.FunctionField))
      ≃ ↥(comapProjPointTwo h2 ⁻¹' {q}) :=
  primesOverEquivFibreTwo h2 (isSeparable_mulByTwoEndoFieldRange_of_isAlgClosed h2) q

/-- **The fibre of `[2]` over a place is nonempty**, over an algebraically closed base field. -/
theorem nonempty_fibre_comapProjPointTwo_of_isAlgClosed :
    ((comapProjPointTwo (W := W) h2) ⁻¹' {q}).Nonempty :=
  nonempty_fibre_comapProjPointTwo h2 (isSeparable_mulByTwoEndoFieldRange_of_isAlgClosed h2) q

/-- **Finitely many primes lie over the maximal ideal of a place of `[2]∗F(W)`**, over an
algebraically closed base field. -/
theorem finite_primesOver_maximalIdeal_placeBelowTwo_of_isAlgClosed :
    Finite ↥((IsLocalRing.maximalIdeal ↥(placeBelowTwo W h2 q)).primesOver
      ↥(integralClosure ↥(placeBelowTwo W h2 q) W.FunctionField)) :=
  finite_primesOver_maximalIdeal_placeBelowTwo h2
    (isSeparable_mulByTwoEndoFieldRange_of_isAlgClosed h2) q

end IsAlgClosed

/-! #### The identity -/

omit [W.IsElliptic] in
/-- **`[2]∗` is residually trivial at the point at infinity**, unconditionally.

⚠️ This is now the `φ = [2]∗` instance of `residueDegreeComap_none_eq_one` above, and nothing
`[2]`-specific is used.  It used to run through the hypothesis-taking
`residueDegreeTwo_none_eq_one_of_ne_zero` (`#744`, `EllipticCurves.FunctionField.PlaceResidueComap`)
and discharge its hypothesis from `#749`'s `residueDegreeProj_none_eq_one` — a two-step that existed
only because `#744` was written before `#749`.
`EllipticCurves.FunctionField.MulByThreeResidueDegree` named that two-step *"a second fossil of the
same ordering"* and declined to mirror it at `n = 3`;
the general lemma retires it rather than copying it a third time.  The `_of_ne_zero` form stays: its
hypothesis is genuinely weaker than `residueDegreeProj W none = 1`. -/
theorem residueDegreeTwo_none_eq_one :
    residueDegreeTwo h2 (none : ProjPoint W) = 1 :=
  residueDegreeComap_none_eq_one _ _

variable [IsAlgClosed F]

/-- **The fundamental identity for `[2]`**: over an algebraically closed base field of
characteristic `≠ 2`, the ramification indices of the places above a place of `[2]∗F(W)` sum to
`4`.

This is `∑_{p ↦ q} e_p = deg [2]` for the *projective* curve, and it is what `#701` was filed for.

⚠️ It does **not** say `#E[2] = 4`: the link from the degree of the extension to a count of
`2`-torsion points runs through "a separable isogeny has `#ker = deg`", which is nowhere in this
tree.  See the module docstring. -/
theorem sum_ramificationIdxTwo_eq_four :
    ∑ p ∈ (finite_comapProjPointTwo_preimage_singleton h2 q).toFinset,
      (ramificationIdxTwo h2 p).toNat = 4 := by
  haveI := module_finite_mulByTwoEndoFieldRange (W := W) h2
  haveI := isSeparable_mulByTwoEndoFieldRange_of_isAlgClosed (W := W) h2
  rw [show (4 : ℕ) = finrank ↥(placeBelowTwo W h2 q)
      ↥(integralClosure ↥(placeBelowTwo W h2 q) W.FunctionField) from
    (finrank_integralClosure_placeBelowTwo_of_isAlgClosed h2 q).symm]
  exact sum_toNat_ramificationIdx_fibre (mulByTwoEndo_algebraMap_base h2)
    (mulByTwoEndo_isIntegralElem h2)

/-- **The fundamental identity with the residue degrees**, `∑_{p ↦ q} e_p · f_p = 4`.

Over an algebraically closed base field `f_p = 1` at every place (`#744`'s
`residueDegreeTwo_eq_one_of_residueDegreeProj_eq_one` fed by `#749`'s `residueDegreeProj_eq_one`),
so this is the previous statement.  It is stated separately because it is the shape Silverman II.2
and Stichtenoth III.1.11 record, and because the general version needs the inertia compatibility
unconditionally.

⚠️ **The clause this docstring used to end with has been paid** — it read *"is what a later issue
owes"*.  The general version is
`EllipticCurves.FunctionField.PlaceInertiaGeneral`'s
`sum_ramificationIdxTwo_mul_residueDegreeTwo_of_isSeparable` and `…_of_charZero`, in a file that
imports this one. -/
theorem sum_ramificationIdxTwo_mul_residueDegreeTwo :
    ∑ p ∈ (finite_comapProjPointTwo_preimage_singleton h2 q).toFinset,
      (ramificationIdxTwo h2 p).toNat * residueDegreeTwo h2 p = 4 := by
  rw [← sum_ramificationIdxTwo_eq_four h2 q]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [residueDegreeTwo_eq_one_of_residueDegreeProj_eq_one h2 (residueDegreeProj_eq_one p), mul_one]

/-- **A place of `[2]∗F(W)` has at most four places above it.**  Each ramification index is at least
`1` and they sum to `4`.

With `#755`'s `nonempty_fibre_comapProjPointTwo` this pins the fibre between `1` and `4` elements,
which is what the Weil-pairing front consumes. -/
theorem card_fibre_comapProjPointTwo_le_four :
    (finite_comapProjPointTwo_preimage_singleton h2 q).toFinset.card ≤ 4 := by
  rw [Finset.card_eq_sum_ones, ← sum_ramificationIdxTwo_eq_four h2 q]
  exact Finset.sum_le_sum fun p _ => by have := ramificationIdxTwo_pos h2 p; omega

open scoped Classical in
/-- **Three further places lie above infinity.**  `[2]` fixes the point at infinity and is
unramified there (`#670`), so its contribution to the identity at `q = none` is `1` and the
remaining places contribute `3`.

This is `#E[2] = 4` seen from the function-field side — and it is **not** a proof of it: what is
counted here is places of `F(W)`, and the passage to points needs the separable-isogeny count that
this tree does not have. -/
theorem sum_ramificationIdxTwo_erase_none_eq_three :
    ∑ p ∈ (finite_comapProjPointTwo_preimage_singleton h2 (none : ProjPoint W)).toFinset.erase
      none, (ramificationIdxTwo h2 p).toNat = 3 := by
  have hmem : (none : ProjPoint W)
      ∈ (finite_comapProjPointTwo_preimage_singleton h2 (none : ProjPoint W)).toFinset :=
    (Set.Finite.mem_toFinset _).2 (comapProjPointTwo_none h2)
  have hone : (ramificationIdxTwo h2 (none : ProjPoint W)).toNat = 1 := by
    rw [ramificationIdxTwo_none h2]
    rfl
  have hsum : 1 + ∑ p ∈ (finite_comapProjPointTwo_preimage_singleton h2
      (none : ProjPoint W)).toFinset.erase none, (ramificationIdxTwo h2 p).toNat = 4 := by
    rw [← hone, Finset.add_sum_erase _ (fun p => (ramificationIdxTwo h2 p).toNat) hmem]
    exact sum_ramificationIdxTwo_eq_four h2 none
  omega

/-! ### Non-vacuity

The headline needs `[IsAlgClosed F]`, `[W.IsElliptic]` and `(2 : F) ≠ 0` at once, and every step
runs through instance searches on the `ValuationSubring`-of-a-`Subfield` stack that `#754` found
delicate.  A curve on which the whole chain elaborates with nothing supplied by hand is therefore
committed rather than quoted.

`y² = x³ − x` over `AlgebraicClosure ℚ` is the curve `#758`/`#759` use, for the same reason: the `ℚ`
curve of the rest of `FunctionField/` cannot witness a statement that needs an algebraically closed
base field, and weakening the statement to fit it would defeat the point. -/

section Nonvacuity

/-- An algebraically closed field of characteristic zero. -/
private abbrev exampleField : Type := AlgebraicClosure ℚ

/-- The curve `y² = x³ - x` over `AlgebraicClosure ℚ`, of discriminant `64`. -/
private noncomputable def exampleCurve : Affine exampleField := ⟨0, 0, 0, -1, 0⟩

private instance : exampleCurve.IsElliptic := by
  rw [WeierstrassCurve.isElliptic_iff, isUnit_iff_ne_zero]
  norm_num [exampleCurve, WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈]

private lemma exampleTwo : (2 : exampleField) ≠ 0 := by norm_num

/-- **The fundamental identity on a curve that exists.** -/
example (q : ProjPoint exampleCurve) :
    ∑ p ∈ (finite_comapProjPointTwo_preimage_singleton exampleTwo q).toFinset,
      (ramificationIdxTwo exampleTwo p).toNat = 4 :=
  sum_ramificationIdxTwo_eq_four exampleTwo q

/-- The residue-degree form, on the same curve. -/
example (q : ProjPoint exampleCurve) :
    ∑ p ∈ (finite_comapProjPointTwo_preimage_singleton exampleTwo q).toFinset,
      (ramificationIdxTwo exampleTwo p).toNat * residueDegreeTwo exampleTwo p = 4 :=
  sum_ramificationIdxTwo_mul_residueDegreeTwo exampleTwo q

/-- The fibre is nonempty and has at most four elements, on the same curve. -/
example (q : ProjPoint exampleCurve) :
    ((comapProjPointTwo (W := exampleCurve) exampleTwo) ⁻¹' {q}).Nonempty
      ∧ (finite_comapProjPointTwo_preimage_singleton exampleTwo q).toFinset.card ≤ 4 :=
  ⟨nonempty_fibre_comapProjPointTwo_of_isAlgClosed exampleTwo q,
    card_fibre_comapProjPointTwo_le_four exampleTwo q⟩

open scoped Classical in
/-- Three further places above infinity, on the same curve. -/
example :
    ∑ p ∈ (finite_comapProjPointTwo_preimage_singleton exampleTwo
      (none : ProjPoint exampleCurve)).toFinset.erase none,
      (ramificationIdxTwo exampleTwo p).toNat = 3 :=
  sum_ramificationIdxTwo_erase_none_eq_three exampleTwo

end Nonvacuity

end CoordinateRing

end WeierstrassCurve.Affine
