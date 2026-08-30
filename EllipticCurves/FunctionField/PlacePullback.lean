/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import EllipticCurves.FunctionField.MulByTwoExtensionFinite
import EllipticCurves.FunctionField.PlaceOrder
import Mathlib.RingTheory.Valuation.Integral

/-!
# The pullback of places along a non-invertible `F`-embedding of `F(W)`

`EllipticCurves.FunctionField.PlaceOrder` transports the projective divisor along an
**automorphism** `σ` of `F(W)`:

```
divisorProj_algEquiv_apply : divisorProj W (σ f) (mapProjPoint W σ p) = divisorProj W f p.
```

`[n]∗` is not an automorphism, and that is the whole difficulty.  `mulByTwoEndo h2` is an injective
`F`-algebra endomorphism of `F(W)` with *proper* image, so `mapProjPoint` — whose construction pulls
back along `σ.symm` — does not apply, and the transported order is not equal to the original: it is
multiplied by a ramification index.  This file supplies both halves.

## Main results

* `ValuationSubring.mem_of_isIntegralElem` — a valuation subring of `K` is integrally closed **in
  `K`**;
* `RingHom.isIntegralElem_of_isIntegral_range` — the converse of the merged
  `isIntegral_range_of_isIntegralElem`, for a ring endomorphism of a field;
* `WeierstrassCurve.Affine.exists_pos_forall_eq_mul_of_nonneg_iff` — a `ℤ`-valued order function is
  determined by its nonnegativity locus *up to a positive factor*;
* `WeierstrassCurve.Affine.comapProjPoint` — the contraction of a place of the target along `φ`,
  a map `ProjPoint W → ProjPoint W`, with `comapProjPoint_eq_iff` its characterisation and
  `WeierstrassCurve.Affine.comapProjPoint_comp` the **contravariant** composition law
  `comapProjPoint (φ ∘ ψ) = comapProjPoint ψ ∘ comapProjPoint φ`;
* `WeierstrassCurve.Affine.ramificationIdx` and
  **`WeierstrassCurve.Affine.divisorProj_comp_apply`**:
  `divisorProj W (φ f) p = e_p * divisorProj W f (comapProjPoint … p)` with `0 < e_p`;
* `WeierstrassCurve.Affine.dvd_divisorProj_comp` — the `n`-divisibility corollary;
* `WeierstrassCurve.Affine.comapProjPoint_algEquiv` and
  `WeierstrassCurve.Affine.ramificationIdx_algEquiv` — the construction restricted to an
  automorphism is `(mapProjPoint σ).symm`, with index `1`: this file's transport degenerates to the
  merged `divisorProj_algEquiv_apply`;
* `WeierstrassCurve.Affine.CoordinateRing.mulByTwoEndo_isIntegralElem`,
  `divisorProj_mulByTwoEndo_apply` and `dvd_divisorProj_mulByTwoEndo_of_torsion` — the `[2]∗`
  instantiation, and the `n`-divisibility statement `#422` asks for.

## The two standing hypotheses on `φ`

```
hφF   : ∀ c : F, φ (algebraMap F F(W) c) = algebraMap F F(W) c
hφint : ∀ z : F(W), φ.IsIntegralElem z
```

`hφF` is what keeps the contracted place a place *over `F`*, so that rung 4's classification
applies to it.  `hφint` says `F(W)` is integral over the image `φ F(W)`, and it is **load-bearing,
not decoration**: it is what forces the contracted valuation subring to be proper.  Without it the
construction is false — a self-embedding of `F(W)` whose image is, say, a rational subfield over
which `F(W)` is transcendental has places of the target that contract to all of `F(W)`.

Both hypotheses hold for `mulByTwoEndo h2`; see the last section, which is the certificate that
nothing here is a statement about automorphisms in disguise.

## Why the merged uniqueness engine generalises rather than being replaced

`PlaceOrder.lean`'s `eq_of_nonneg_iff_of_exists_eq_one` says a `ℤ`-valued order function is
determined outright by its nonnegativity locus *provided it attains the value `1`*.  Here
`f ↦ divisorProj W (φ f) p` need not attain `1` — that is exactly the ramification — and the correct
statement is that it is a positive integer multiple of the order at the contracted place.  The proof
is *shorter* than the merged one: the `e ∣ 1` step, which is where surjectivity was consumed, simply
disappears.  The two are siblings, and neither implies the other in one line: the merged one has the
stronger conclusion, this one the weaker hypothesis.

The four arithmetic helpers the merged proof uses (`map_one_of_mul`, `map_inv_of_mul`,
`map_zpow_of_mul`, `eq_mul_of_zero_imp_zero`) are `private` there, hence not importable; the two
that are needed here are re-proved below rather than by editing a merged file.

## What is *not* here

* **`pullbackDivisor : (ProjPoint W →₀ ℤ) →+ (ProjPoint W →₀ ℤ)`.**  Not *here*: everything below
  is pointwise.  ⚠️ **This bullet used to continue** *"Defining `[n]∗` on divisors needs each fibre
  `(comapProjPoint φ) ⁻¹' {q}` to be finite — the "finitely many places above a place of a finite
  extension" theorem — which is not in this tree."*  It is
  `EllipticCurves.FunctionField.PullbackDivisor`, which imports this file.
  ⚠️ **And the theorem named is not the one that was used.**  That file's own docstring records
  that the classical route — the integral closure of a valuation ring, and Mathlib's
  `IsDedekindDomain.primesOverFinset` — *"is not available here"*, because `[2]∗F[W] ⊄ F[W]` puts
  the AKLB picture on the wrong spectrum.  What it does instead is take a uniformizer `π` at `q`
  and observe that the whole fibre sits inside the support of the single divisor
  `divisorProj W (φ π)`, since `divisorProj W (φ π) p = e_p ≠ 0` there by `ramificationIdx_pos`
  below: *"the finiteness of the fibre is the finiteness of a `Finsupp`, read backwards"*.  The
  obstruction this bullet named was real and was dissolved rather than met.
  In particular `Finsupp.mapDomain (comapProjPoint …)` is **not** the divisor
  pullback: it pushes forward along the contraction, which is the wrong direction and gives a
  different divisor.
* **Any computation of `ramificationIdx`.**  It is *defined* as the value of the transported order
  at a uniformizer at the contracted place.  Nothing here says it is `1` at any particular place for
  `[2]∗`, and nothing here proves `∑_{p ↦ q} e_p · f_p = deg φ`.
* **The degree formula.**  Nothing *here* proves `∑_{p ↦ q} e_p · f_p = deg φ`; it is proved for
  `[2]∗` over an algebraically closed base field in
  `EllipticCurves.FunctionField.PlaceRamificationInertia` (`#763`), which matches the
  `ramificationIdx` of this file with Mathlib's `Ideal.ramificationIdx` and fires
  `Ideal.sum_ramification_inertia_eq_finrank`.  The *arithmetic* half of it is available here — see
  the note below on `[2]∗`.
* `[3]∗`.  The general section applies to it verbatim once the same two hypotheses are supplied for
  `mulByThreeEndo`, and is deliberately not instantiated *here*; it is instantiated in
  `EllipticCurves.FunctionField.MulByThreePlacePullback`, which also computes the index at
  infinity.
* `div g_S = [n]∗(S)` (`#418`), Riemann–Roch, and anything Ward-gated.

## References

* [J. H. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], II.3 (Prop. II.3.6, the
  pullback of divisors under a finite morphism).
* Stichtenoth, *Algebraic Function Fields and Codes*, III.1 (the ramification index `e(P'|P) ≥ 1`).
-/

open Polynomial IsDedekindDomain

/-! ### Valuation subrings are integrally closed in the ambient field

Mathlib has `IsIntegrallyClosed ↥A` for a valuation subring `A` of `K`
(`Mathlib/RingTheory/Valuation/LocalSubring.lean`), which is a statement about `A` and *its*
fraction field.  `EllipticCurves.FunctionField.Places` records that the glue to membership in
`A ⊆ K` was missing and works around it with a Newton-polygon argument.  Here it cannot be worked
around, so the glue is supplied once, in a form with no curve in it. -/

namespace ValuationSubring

/-- **A valuation subring is integrally closed in the ambient field.**  If every coefficient of a
monic witness lies in `A` — packaged as "the witness is monic over some `R` mapping into `A`" — then
the root lies in `A`.

Stated through `RingHom.IsIntegralElem` rather than `IsIntegral` so that it applies directly to a
ring endomorphism `f : K →+* K`, which is how it is used below; `f` need not be injective. -/
theorem mem_of_isIntegralElem {K R : Type*} [Field K] [CommRing R] (A : ValuationSubring K)
    (f : R →+* K) (hf : ∀ r, f r ∈ A) {x : K} (hx : f.IsIntegralElem x) : x ∈ A := by
  have hcomp : A.subtype.comp (f.codRestrict A.toSubring hf) = f := rfl
  obtain ⟨p, hpm, hpe⟩ := hx
  have hint : IsIntegral A x := by
    refine ⟨p.map (f.codRestrict A.toSubring hf), hpm.map _, ?_⟩
    rw [eval₂_map]
    change eval₂ (A.subtype.comp (f.codRestrict A.toSubring hf)) x p = 0
    rw [hcomp]
    exact hpe
  have hI : Valuation.Integers A.valuation A := by
    have h := Valuation.valuationSubring.integers A.valuation
    rwa [A.valuationSubring_valuation] at h
  have h := hI.mem_of_integral hint
  rwa [A.integer_valuation] at h

end ValuationSubring

namespace RingHom

/-- **The converse of `isIntegral_range_of_isIntegralElem`** (`MulByTwoModuleFinite.lean`) for an
endomorphism of a *field*: being integral over the range subring is the same as being integral with
respect to the endomorphism itself.

The two directions are not symmetric.  The merged direction pushes a monic witness forward along
`f.rangeRestrict` and needs nothing; this one pulls it back along the *inverse* of
`f.rangeRestrict`, which exists only because `f` is injective — and `f` is injective precisely
because its source is a field. -/
theorem isIntegralElem_of_isIntegral_range {K : Type*} [Field K] (f : K →+* K) {z : K}
    (hz : _root_.IsIntegral ↥f.range z) : f.IsIntegralElem z := by
  have hinj : Function.Injective f.rangeRestrict :=
    fun _ _ hab => f.injective (congrArg Subtype.val hab)
  let e : K ≃+* ↥f.range :=
    RingEquiv.ofBijective f.rangeRestrict ⟨hinj, f.rangeRestrict_surjective⟩
  have hce : f.comp (e.symm : ↥f.range →+* K) = f.range.subtype :=
    RingHom.ext fun a => congrArg Subtype.val (e.apply_symm_apply a)
  obtain ⟨p, hpm, hpe⟩ := hz
  refine ⟨p.map (e.symm : ↥f.range →+* K), hpm.map _, ?_⟩
  rw [eval₂_map, hce]
  exact hpe

end RingHom

namespace WeierstrassCurve.Affine

open CoordinateRing

/-! ### An order function is determined by its nonnegativity locus up to a positive factor

The sibling of `PlaceOrder.lean`'s `Uniqueness` section.  As there, `φ` and `ψ` are `ℤ`-valued
functions on a bare field that are additive on products of nonzero elements — the shape both `ord v`
and `ordInfty` have, with the junk value `0` at `0`.  Nothing about curves, and nothing about
valuations; an upstream candidate, as that section is. -/

section Uniqueness

variable {K : Type*} [Field K] {φ ψ : K → ℤ}

/-- Additivity on nonzero products forces `φ 1 = 0`.  (`PlaceOrder.lean` proves the same statement
as a `private` lemma, so it cannot be imported.) -/
private lemma map_one_of_mul' (hφ : ∀ x y : K, x ≠ 0 → y ≠ 0 → φ (x * y) = φ x + φ y) :
    φ 1 = 0 := by
  have h := hφ 1 1 one_ne_zero one_ne_zero
  rw [one_mul] at h
  omega

/-- Additivity on nonzero products forces `φ x⁻¹ = -φ x`. -/
private lemma map_inv_of_mul' (hφ : ∀ x y : K, x ≠ 0 → y ≠ 0 → φ (x * y) = φ x + φ y)
    {x : K} (hx : x ≠ 0) : φ x⁻¹ = -φ x := by
  have h := hφ x x⁻¹ hx (inv_ne_zero hx)
  rw [mul_inv_cancel₀ hx, map_one_of_mul' hφ] at h
  omega

/-- Additivity on nonzero products forces `φ (x ^ n) = n * φ x` for `n : ℤ`. -/
private lemma map_zpow_of_mul' (hφ : ∀ x y : K, x ≠ 0 → y ≠ 0 → φ (x * y) = φ x + φ y)
    {x : K} (hx : x ≠ 0) (n : ℤ) : φ (x ^ n) = n * φ x := by
  induction n using Int.induction_on with
  | zero => simpa using map_one_of_mul' hφ
  | succ k ih =>
      rw [zpow_add_one₀ hx, hφ _ _ (zpow_ne_zero _ hx) hx, ih]
      ring
  | pred k ih =>
      rw [zpow_sub_one₀ hx, hφ _ _ (zpow_ne_zero _ hx) (inv_ne_zero hx),
        map_inv_of_mul' hφ hx, ih]
      ring

/-- **A `ℤ`-valued order function is determined by its nonnegativity locus up to a positive
factor.**

If `φ` and `ψ` are additive on products of nonzero elements, have the same nonnegativity locus, `ψ`
attains the value `1`, and `φ` is not identically zero on the nonzero elements, then `φ = e • ψ`
for a unique `e > 0`.

This is `PlaceOrder.lean`'s `eq_of_nonneg_iff_of_exists_eq_one` with the surjectivity of `φ`
dropped from the hypotheses and moved, as a positive factor, into the conclusion.  It is what makes
the pullback of places along a *non-invertible* embedding possible at all: there `φ` is the order at
a place of the target read through the embedding, and its image is the subgroup `e·ℤ ⊆ ℤ`. -/
theorem exists_pos_forall_eq_mul_of_nonneg_iff
    (hφ : ∀ x y : K, x ≠ 0 → y ≠ 0 → φ (x * y) = φ x + φ y)
    (hψ : ∀ x y : K, x ≠ 0 → y ≠ 0 → ψ (x * y) = ψ x + ψ y)
    (hiff : ∀ x : K, x ≠ 0 → (0 ≤ φ x ↔ 0 ≤ ψ x))
    (hψ1 : ∃ x : K, x ≠ 0 ∧ ψ x = 1) (hφ0 : ∃ x : K, x ≠ 0 ∧ φ x ≠ 0) :
    ∃ e : ℤ, 0 < e ∧ ∀ x : K, x ≠ 0 → φ x = e * ψ x := by
  obtain ⟨π, hπ0, hπ⟩ := hψ1
  -- The two kernels agree: `ψ y = 0` iff both `ψ y` and `ψ y⁻¹` are nonnegative.
  have hzero : ∀ y : K, y ≠ 0 → ψ y = 0 → φ y = 0 := by
    intro y hy h
    have h1 : 0 ≤ φ y := (hiff y hy).2 h.ge
    have h2 : 0 ≤ φ y⁻¹ :=
      (hiff y⁻¹ (inv_ne_zero hy)).2 (by rw [map_inv_of_mul' hψ hy, h, neg_zero])
    rw [map_inv_of_mul' hφ hy] at h2
    omega
  -- Write `x` as `π ^ (ψ x)` times an element of the common kernel.
  have key : ∀ x : K, x ≠ 0 → φ x = φ π * ψ x := by
    intro x hx
    have hz0 : π ^ (-ψ x) ≠ 0 := zpow_ne_zero _ hπ0
    have h0 : ψ (x * π ^ (-ψ x)) = 0 := by
      rw [hψ _ _ hx hz0, map_zpow_of_mul' hψ hπ0, hπ]
      ring
    have h := hzero _ (mul_ne_zero hx hz0) h0
    rw [hφ _ _ hx hz0, map_zpow_of_mul' hφ hπ0] at h
    linear_combination h
  refine ⟨φ π, ?_, key⟩
  obtain ⟨x, hx, hxne⟩ := hφ0
  rcases ((hiff π hπ0).2 (by rw [hπ]; norm_num)).lt_or_eq with h | h
  · exact h
  · exact absurd (by rw [key x hx, ← h, zero_mul]) hxne

end Uniqueness

/-! ### The contraction of a place along `φ`

`φ` is a ring endomorphism of `F(W)` fixing `F` pointwise and making `F(W)` integral over its image.
Pulling a place of the target back along `φ` gives a valuation subring of the source; the two
hypotheses say exactly that it is again a place *over `F`*, so rung 4's classification names it as
`placeOf W q` for a unique `q`. -/

section Contraction

variable {F : Type*} [Field F] {W : Affine F} [IsDedekindDomain W.CoordinateRing]
  {φ : W.FunctionField →+* W.FunctionField}
  (hφF : ∀ c : F, φ (algebraMap F W.FunctionField c) = algebraMap F W.FunctionField c)
  (hφint : ∀ z : W.FunctionField, φ.IsIntegralElem z)

include hφF in
/-- `φ` fixes `F`, so the contracted valuation subring still contains `F`. -/
lemma algebraMap_mem_comap_of_algebraMap_eq (p : ProjPoint W) (c : F) :
    algebraMap F W.FunctionField c ∈ (placeOf W p).comap φ := by
  rw [ValuationSubring.mem_comap, hφF c]
  exact algebraMap_mem_placeOf p c

include hφint in
/-- **The contracted place is proper.**  If it were all of `F(W)` then the whole image `φ F(W)`
would lie in `placeOf W p`; every element of `F(W)` is integral over that image, and a valuation
subring is integrally closed in the ambient field, so `placeOf W p` would be all of `F(W)`,
contradicting `placeOf_ne_top`.

This is the only use of `hφint` in the file, and it is where the construction would fail for an
embedding with a transcendental cokernel. -/
lemma comap_ne_top_of_isIntegralElem (p : ProjPoint W) :
    (placeOf W p).comap φ ≠ ⊤ := by
  intro h
  refine placeOf_ne_top p (SetLike.ext fun z => iff_of_true ?_ (ValuationSubring.mem_top z))
  exact (placeOf W p).mem_of_isIntegralElem φ
    (fun r => (h ▸ ValuationSubring.mem_top r : r ∈ (placeOf W p).comap φ)) (hφint z)

/-- **The contraction of a point of the projective curve along `φ`.**  The point whose place is
`(placeOf W p).comap φ`; it exists and is unique by `exists_placeOf_eq` and `placeOf_injective`.

Unlike `mapProjPoint` this is only a *map*, not an equivalence: `φ` need not be surjective, and the
contraction of the places above a point is generally many-to-one. -/
noncomputable def comapProjPoint (p : ProjPoint W) : ProjPoint W :=
  (exists_placeOf_eq ((placeOf W p).comap φ) (algebraMap_mem_comap_of_algebraMap_eq hφF p)
    (comap_ne_top_of_isIntegralElem hφint p)).choose

@[simp] lemma placeOf_comapProjPoint (p : ProjPoint W) :
    placeOf W (comapProjPoint hφF hφint p) = (placeOf W p).comap φ :=
  (exists_placeOf_eq ((placeOf W p).comap φ) (algebraMap_mem_comap_of_algebraMap_eq hφF p)
    (comap_ne_top_of_isIntegralElem hφint p)).choose_spec

/-- The pointwise form: `g` is regular at the contracted point iff `φ g` is regular at `p`. -/
lemma mem_placeOf_comapProjPoint (p : ProjPoint W) (g : W.FunctionField) :
    g ∈ placeOf W (comapProjPoint hφF hφint p) ↔ φ g ∈ placeOf W p := by
  rw [placeOf_comapProjPoint]
  exact Iff.rfl

/-- `comapProjPoint` is determined by its characterising property. -/
theorem comapProjPoint_eq_iff {p q : ProjPoint W} :
    comapProjPoint hφF hφint p = q ↔ placeOf W q = (placeOf W p).comap φ :=
  ⟨fun h => h ▸ placeOf_comapProjPoint hφF hφint p,
    fun h => placeOf_injective ((placeOf_comapProjPoint hφF hφint p).trans h.symm)⟩

/-- **The contraction along a composite is the composite of the contractions, in the opposite
order**: `comapProjPoint (φ ∘ ψ) = comapProjPoint ψ ∘ comapProjPoint φ`.

⚠️ **The order is the content of this lemma.**  `comapProjPoint` is contravariant, so it reverses
the composition; on points it is the *forward* map, and reading it as covariant gives a statement
that is still true at `φ = ψ` and false in general.  Everything is forced by
`ValuationSubring.comap_comap`, which pulls a place of the target back through `ψ` first and then
through `φ`.

The composite's own two hypotheses are taken as arguments rather than assembled from `hφF`/`hψF`
and `hφint`/`hψint`.  For `hcF` that would be routine, but `hcint` — integrality of `F(W)` over
the image of a composite — does **not** follow from the two componentwise integrality statements in
one step, and a caller that has it (as `[m · n]∗` does, from
`EllipticCurves.FunctionField.MulByNIntegral`) should supply it directly. -/
theorem comapProjPoint_comp {ψ : W.FunctionField →+* W.FunctionField}
    (hψF : ∀ c : F, ψ (algebraMap F W.FunctionField c) = algebraMap F W.FunctionField c)
    (hψint : ∀ z : W.FunctionField, ψ.IsIntegralElem z)
    (hcF : ∀ c : F, (φ.comp ψ) (algebraMap F W.FunctionField c) = algebraMap F W.FunctionField c)
    (hcint : ∀ z : W.FunctionField, (φ.comp ψ).IsIntegralElem z) (p : ProjPoint W) :
    comapProjPoint hcF hcint p = comapProjPoint hψF hψint (comapProjPoint hφF hφint p) := by
  refine placeOf_injective ?_
  rw [placeOf_comapProjPoint, placeOf_comapProjPoint, placeOf_comapProjPoint,
    ValuationSubring.comap_comap]

end Contraction

/-! ### The ramification index and the transport of the order

The two order functions `g ↦ divisorProj W (φ g) p` and `g ↦ divisorProj W g (comapProjPoint φ p)`
have the same nonnegativity locus — that is what the previous section says — so they agree up to a
positive factor.  That factor is the ramification index. -/

section Ramification

variable {F : Type*} [Field F] {W : Affine F} [IsDedekindDomain W.CoordinateRing]
  {φ : W.FunctionField →+* W.FunctionField}
  (hφF : ∀ c : F, φ (algebraMap F W.FunctionField c) = algebraMap F W.FunctionField c)
  (hφint : ∀ z : W.FunctionField, φ.IsIntegralElem z)

omit [IsDedekindDomain W.CoordinateRing] in
/-- A ring homomorphism out of a field does not kill nonzero elements. -/
private lemma ringHom_ne_zero {f : W.FunctionField} (hf : f ≠ 0) : φ f ≠ 0 :=
  fun h => hf (φ.injective (by rw [h, map_zero]))

include hφF hφint in
/-- The existential the ramification index is extracted from. -/
private theorem exists_ramificationIdx (p : ProjPoint W) :
    ∃ e : ℤ, 0 < e ∧ ∀ f : W.FunctionField, f ≠ 0 →
      divisorProj W (φ f) p = e * divisorProj W f (comapProjPoint hφF hφint p) := by
  refine exists_pos_forall_eq_mul_of_nonneg_iff
    (φ := fun g => divisorProj W (φ g) p)
    (ψ := fun g => divisorProj W g (comapProjPoint hφF hφint p))
    (fun x y hx hy => ?_) (fun x y hx hy => ?_) (fun x hx => ?_) ?_ ?_
  · rw [map_mul, divisorProj_mul (ringHom_ne_zero hx) (ringHom_ne_zero hy), Finsupp.add_apply]
  · rw [divisorProj_mul hx hy, Finsupp.add_apply]
  · rw [← mem_placeOf_iff_divisorProj_nonneg _ (ringHom_ne_zero hx),
      ← mem_placeOf_iff_divisorProj_nonneg _ hx, mem_placeOf_comapProjPoint]
  · exact exists_divisorProj_eq_one (comapProjPoint hφF hφint p)
  · -- the contracted place is proper, and a function outside it has a pole at `p` after `φ`
    have hex : ∃ z : W.FunctionField, φ z ∉ placeOf W p := by
      by_contra h
      exact comap_ne_top_of_isIntegralElem hφint p
        (SetLike.ext fun z => iff_of_true (not_not.mp fun hz => h ⟨z, hz⟩)
          (ValuationSubring.mem_top z))
    obtain ⟨z, hz⟩ := hex
    have hz0 : z ≠ 0 := fun h => hz (by rw [h, map_zero]; exact zero_mem _)
    refine ⟨z, hz0, fun h => hz ?_⟩
    rw [mem_placeOf_iff_divisorProj_nonneg _ (ringHom_ne_zero hz0), h]

/-- **The ramification index of `φ` at a point `p` of the projective curve.**

By construction it is the factor by which `φ` multiplies the order function: the order of `φ f` at
`p` is `ramificationIdx` times the order of `f` at the contracted point.  Equivalently it is the
order at `p` of `φ` applied to a uniformizer at the contracted point.

**Nothing in this file computes it.**  No claim is made that it is `1` at any particular place for
any particular `φ`, and the conductor-discriminant / degree formula `∑_{p ↦ q} e_p · f_p = deg φ` is
not proved here; it is `EllipticCurves.FunctionField.PlaceRamificationInertia` (`#763`), which
identifies this index with Mathlib's `Ideal.ramificationIdx`.  Individual values are computed for
`[2]` over every `F`-rational point of the curve, and there only, in
`EllipticCurves.FunctionField.MulByTwoFibreAffine` (`#774`), where they are all `1`; the `2`-torsion
places are the sub-case in `MulByTwoFibreInfinity`.  A place lying over a closed point that is *not*
the closed point of a rational point is still untouched. -/
noncomputable def ramificationIdx (p : ProjPoint W) : ℤ :=
  (exists_ramificationIdx hφF hφint p).choose

/-- **The ramification index is positive.**  In particular `φ` never collapses the order function at
a place to zero — the contracted point really does see everything `p` sees. -/
theorem ramificationIdx_pos (p : ProjPoint W) : 0 < ramificationIdx hφF hφint p :=
  (exists_ramificationIdx hφF hφint p).choose_spec.1

/-- **The order transport under a non-invertible embedding.**

```
ord_p (φ f) = e_p · ord_{φ⁻¹ p} (f).
```

This is the `[n]∗` analogue of the merged `divisorProj_algEquiv_apply`, and it degenerates to it:
for an automorphism the index is `1` and the contraction is `(mapProjPoint σ).symm`
(`ramificationIdx_algEquiv` and `comapProjPoint_algEquiv` below). -/
theorem divisorProj_comp_apply {f : W.FunctionField} (hf : f ≠ 0) (p : ProjPoint W) :
    divisorProj W (φ f) p
      = ramificationIdx hφF hφint p * divisorProj W f (comapProjPoint hφF hφint p) :=
  (exists_ramificationIdx hφF hφint p).choose_spec.2 f hf

include hφF hφint in
/-- **The divisibility corollary.**  If every coefficient of `div f` is divisible by `n`, then so is
every coefficient of `div (φ f)`.  This is the shape `#422` consumes: it converts the divisor of the
torsion generator `f_S` into the `n`-divisibility of the divisor of `f_S ∘ [n]`. -/
theorem dvd_divisorProj_comp {n : ℤ} {f : W.FunctionField} (hf : f ≠ 0)
    (hn : ∀ q : ProjPoint W, n ∣ divisorProj W f q) (p : ProjPoint W) :
    n ∣ divisorProj W (φ f) p := by
  rw [divisorProj_comp_apply hφF hφint hf p]
  exact Dvd.dvd.mul_left (hn _) _

end Ramification

/-! ### Consistency with rung 5: an automorphism is the case `e = 1`

The pullback construction and the merged `mapProjPoint` must not disagree, and the risk is real:
`Places.lean` builds `mapProjPoint σ` from `comap σ.symm`, not `comap σ`, and its docstring warns at
length that this is the choice that makes `mapProjPointHom` a homomorphism rather than an
anti-homomorphism.  The two statements below are the check that no convention has drifted. -/

section AlgEquiv

variable {F : Type*} [Field F] {W : Affine F} [IsDedekindDomain W.CoordinateRing]
  (σ : W.FunctionField ≃ₐ[F] W.FunctionField)

omit [IsDedekindDomain W.CoordinateRing] in
/-- An automorphism satisfies the integrality hypothesis for free: `z` is a root of the monic
`X - C (σ.symm z)` read through `σ`. -/
lemma isIntegralElem_algEquiv (z : W.FunctionField) :
    (σ : W.FunctionField →+* W.FunctionField).IsIntegralElem z :=
  ⟨X - C (σ.symm z), monic_X_sub_C _, by simp⟩

/-- **The contraction along an automorphism is the inverse of `mapProjPoint`.**  Both are
characterised by their place: `placeOf (comapProjPoint σ p) = (placeOf p).comap σ` and
`placeOf (mapProjPoint σ.symm p) = (placeOf p).comap σ.symm.symm`. -/
theorem comapProjPoint_algEquiv (p : ProjPoint W) :
    comapProjPoint (φ := (σ : W.FunctionField →+* W.FunctionField)) σ.commutes
        (isIntegralElem_algEquiv σ) p = (mapProjPoint W σ).symm p := by
  refine placeOf_injective ?_
  rw [placeOf_comapProjPoint]
  have h : placeOf W (mapProjPoint W σ.symm p)
      = (placeOf W p).comap ((σ.symm.symm : W.FunctionField ≃ₐ[F] W.FunctionField) :
        W.FunctionField →+* W.FunctionField) := placeOf_mapProjPoint σ.symm p
  rw [AlgEquiv.symm_symm] at h
  exact h.symm

/-- **An automorphism is unramified everywhere**, so this file's transport really does specialise to
the merged `divisorProj_algEquiv_apply`. -/
theorem ramificationIdx_algEquiv (p : ProjPoint W) :
    ramificationIdx (φ := (σ : W.FunctionField →+* W.FunctionField)) σ.commutes
      (isIntegralElem_algEquiv σ) p = 1 := by
  obtain ⟨π, hπ0, hπ⟩ := exists_divisorProj_eq_one ((mapProjPoint W σ).symm p)
  have h1 := divisorProj_comp_apply (φ := (σ : W.FunctionField →+* W.FunctionField)) σ.commutes
    (isIntegralElem_algEquiv σ) hπ0 p
  rw [comapProjPoint_algEquiv σ p, hπ, mul_one] at h1
  have h2 := divisorProj_algEquiv_apply σ hπ0 ((mapProjPoint W σ).symm p)
  rw [Equiv.apply_symm_apply, hπ] at h2
  exact h1.symm.trans h2

end AlgEquiv

/-! ### The `[2]∗` instantiation

Everything above is conditional on `hφint`, so a reviewer is entitled to ask whether any
*non-invertible* `φ` satisfies it.  One does, and it is the one the Weil-pairing front needs.

**And `[2]∗` really is non-invertible.**  When this file was written nothing in the tree computed
`[F(W) : [2]∗F(W)]` — the merged `MulByTwoFinite` / `MulByTwoExtensionFinite` gave only "finite, of
degree `≤ 4`" — so the honest reading of this section was conditional: the two hypotheses are
discharged for `mulByTwoEndo`, and *if* it is not an automorphism then the section is outside rung
5's reach.  That gap is closed.  `EllipticCurves.FunctionField.MulByTwoDegree` proves

* `finrank_mulByTwoRange_functionField (h2 : (2 : F) ≠ 0) :
  Module.finrank ↥(mulByTwoEndo h2).range W.FunctionField = 4`, and
* `not_surjective_mulByTwoEndo (h2 : (2 : F) ≠ 0) : ¬ Function.Surjective (mulByTwoEndo h2)`,

both under `[W.IsElliptic]`.  So this section is unconditionally more than a restatement of rung 5:
`F(W)` is a proper extension of `[2]∗F(W)`, of degree exactly four, and the places transported here
genuinely lie over a strictly smaller function field.

Two things that does **not** give.  It is the *field degree* `[F(W) : [2]∗F(W)] = 4`, not the degree
formula `∑_{p ↦ q} e_p · deg p = 4`, which additionally needs the residue degrees (`#743`, `#749`)
and a fundamental identity (`EllipticCurves.FunctionField.PlaceRamificationInertia`, `#763`) — both
of which now exist, so the degree formula holds over an algebraically closed base field, but it is
not proved from anything in this file.  ⚠️ **And in this spelling it is `degProjPt`, not the
relative residue degree**: `PlaceRamificationInertia` proves the `f_p`-weighted form, and the
`deg p`-weighted form written here is `sum_ramificationIdxTwo_mul_degProjPt`
(`EllipticCurves.FunctionField.PlaceDegreeComparison`).  ⚠️ **That last clause read** *"which needs
the identification `degProjPt = residueDegreeProj` and therefore an algebraically closed base field
for a second, independent reason"* — **the second reason has evaporated**:
`degProjPt_eq_residueDegreeProj` is now proved over an arbitrary base field.  The weighted identity
keeps `[IsAlgClosed F]` for the *first* reason only, namely that it is a reweighting by
`degProjPt_eq_one`.  Over a general field the two weights are different quantities and only the
relative one is expected to survive.  It says nothing about `#E[n] = n²` either, whose connection to
the field degree runs
through a counting argument for separable isogenies that is nowhere in this tree.  (The
*separability* of `F(W) / [2]∗F(W)` itself is available — `MulByTwoGalois`, `#759` — but the step
from it to a count of `E[2]` is not, and must not be assumed.)  In particular no
`ramificationIdx` at an affine place is computed *here*; places lying over an `F`-rational point are
done in `EllipticCurves.FunctionField.MulByTwoFibreAffine` (`#774`) and are unramified, and a place
lying over a closed point with a nontrivial residue extension is still open.

⚠️ The `[W.IsElliptic]` hypothesis on those two results is load-bearing, not bookkeeping.  The
declarations in this section carry no such hypothesis, and they must not: on a *singular*
Weierstrass curve the smooth locus is `𝔾ₘ` or `𝔾ₐ`, where multiplication by two is squaring
(degree two) or doubling (degree one, an isomorphism as soon as `(2 : F) ≠ 0`).  A blanket
"`[2]∗` is never surjective" would be false. -/

namespace CoordinateRing

variable {F : Type*} [Field F] {W : Affine F}

/-- **`F(W)` is integral over `[2]∗F(W)`.**  The merged `module_finite_mulByTwoRange` says `F(W)` is
a finite module over the range subfield; module-finite implies integral, and
`RingHom.isIntegralElem_of_isIntegral_range` converts integrality over the range subring into
integrality with respect to the endomorphism. -/
theorem mulByTwoEndo_isIntegralElem (h2 : (2 : F) ≠ 0) (z : W.FunctionField) :
    (mulByTwoEndo (W := W) h2).IsIntegralElem z := by
  haveI : Module.Finite ↥(mulByTwoEndo (W := W) h2).range W.FunctionField :=
    module_finite_mulByTwoRange h2
  haveI : Algebra.IsIntegral ↥(mulByTwoEndo (W := W) h2).range W.FunctionField :=
    Algebra.IsIntegral.of_finite _ _
  exact RingHom.isIntegralElem_of_isIntegral_range _ (Algebra.IsIntegral.isIntegral z)

variable [IsDedekindDomain W.CoordinateRing]

/-- **The contraction of a place of the projective curve along `[2]∗`.** -/
noncomputable def comapProjPointTwo (h2 : (2 : F) ≠ 0) : ProjPoint W → ProjPoint W :=
  comapProjPoint (mulByTwoEndo_algebraMap_base h2) (mulByTwoEndo_isIntegralElem h2)

/-- **The ramification index of `[2]∗`.** -/
noncomputable def ramificationIdxTwo (h2 : (2 : F) ≠ 0) (p : ProjPoint W) : ℤ :=
  ramificationIdx (mulByTwoEndo_algebraMap_base h2) (mulByTwoEndo_isIntegralElem h2) p

theorem ramificationIdxTwo_pos (h2 : (2 : F) ≠ 0) (p : ProjPoint W) :
    0 < ramificationIdxTwo h2 p :=
  ramificationIdx_pos _ _ p

/-- **`ord_p (f ∘ [2]) = e_p · ord_{[2]⁻¹ p} (f)`** — the divisor-level pullback under
multiplication by `2`, on the *projective* point set.

`#422`'s 2026-08-16 correction showed the affine AKLB route to this statement is false, because
`[2]∗F[W] ⊄ F[W]`; the obstruction is projective, and this is the statement that dissolves it. -/
theorem divisorProj_mulByTwoEndo_apply (h2 : (2 : F) ≠ 0) {f : W.FunctionField} (hf : f ≠ 0)
    (p : ProjPoint W) :
    divisorProj W (mulByTwoEndo h2 f) p
      = ramificationIdxTwo h2 p * divisorProj W f (comapProjPointTwo h2 p) :=
  divisorProj_comp_apply _ _ hf p

/-- **`n`-divisibility of the divisor of `f ∘ [2]`.** -/
theorem dvd_divisorProj_mulByTwoEndo (h2 : (2 : F) ≠ 0) {n : ℤ} {f : W.FunctionField} (hf : f ≠ 0)
    (hn : ∀ q : ProjPoint W, n ∣ divisorProj W f q) (p : ProjPoint W) :
    n ∣ divisorProj W (mulByTwoEndo h2 f) p :=
  dvd_divisorProj_comp (mulByTwoEndo_algebraMap_base h2) (mulByTwoEndo_isIntegralElem h2) hf hn p

/-- **The statement `#422` asks for.**  For an `n`-torsion point `S` there is a function `f_S` with
`div f_S = n·(S) − n·(O)` (the merged `divisorProj_eq_single_sub_single_of_torsion`), and every
coefficient of `div (f_S ∘ [2])` is then divisible by `n`.

`#422`'s 2026-08-16 correction called this "the downstream-sufficient corollary" of the rung-4
pullback and recorded that no elementary bypass of it was known.  This is it, via the projective
route that correction named. -/
theorem dvd_divisorProj_mulByTwoEndo_of_torsion [DecidableEq F] (h2 : (2 : F) ≠ 0) {x y : F}
    (h : W.Nonsingular x y) {n : ℕ} (hP : Point.some x y h ∈ W.torsion n) :
    ∃ f : W.FunctionField, f ≠ 0 ∧
      divisorProj W f = Finsupp.single (some (pointClosedPoint h.left)) (n : ℤ)
        - Finsupp.single none (n : ℤ) ∧
      ∀ p : ProjPoint W, (n : ℤ) ∣ divisorProj W (mulByTwoEndo h2 f) p := by
  classical
  obtain ⟨f, hf, hdiv⟩ := divisorProj_eq_single_sub_single_of_torsion h hP
  refine ⟨f, hf, hdiv, dvd_divisorProj_mulByTwoEndo h2 hf fun q => ?_⟩
  rw [hdiv, Finsupp.sub_apply, Finsupp.single_apply, Finsupp.single_apply]
  exact dvd_sub (by split <;> simp) (by split <;> simp)

/-! ### Non-vacuity

`comapProjPointTwo` and `ramificationIdxTwo` are extracted from an existence statement by choice,
and everything about them is stated under `[IsDedekindDomain W.CoordinateRing]`.  Exhibiting a
curve on which the transport equation elaborates with every instance discharged is what rules out
the degenerate reading in which the hypotheses are unsatisfiable.  `y² = x³ - x` over `ℚ` has
discriminant `64`, and `IsElliptic` alone gives the Dedekind instance. -/

section Nonvacuity

/-- The curve `y² = x³ - x` over `ℚ`, of discriminant `64`. -/
private def exampleCurve : Affine ℚ := ⟨0, 0, 0, -1, 0⟩

private instance : exampleCurve.IsElliptic := by
  rw [WeierstrassCurve.isElliptic_iff, isUnit_iff_ne_zero]
  norm_num [exampleCurve, WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈]

example : IsDedekindDomain exampleCurve.CoordinateRing := inferInstance

example {f : exampleCurve.FunctionField} (hf : f ≠ 0) (p : ProjPoint exampleCurve) :
    divisorProj exampleCurve (mulByTwoEndo (W := exampleCurve) (by norm_num) f) p
      = ramificationIdxTwo (W := exampleCurve) (by norm_num) p
        * divisorProj exampleCurve f (comapProjPointTwo (by norm_num) p) :=
  divisorProj_mulByTwoEndo_apply _ hf p

example (p : ProjPoint exampleCurve) :
    0 < ramificationIdxTwo (W := exampleCurve) (by norm_num) p :=
  ramificationIdxTwo_pos _ p

end Nonvacuity

end CoordinateRing

end WeierstrassCurve.Affine
