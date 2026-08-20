/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import EllipticCurves.FunctionField.ProjectiveDivisor
import EllipticCurves.FunctionField.ValuationAtInfinity
import EllipticCurves.FunctionField.ValuationSubringDedekind

/-!
# The places of `F(W)`, and the permutation action of `Aut_F F(W)` on the projective curve

`EllipticCurves.FunctionField.ProjectiveDivisor` introduces `ProjPoint W`, the points of the
projective curve, as `Option (HeightOneSpectrum F[W])`, and its docstring is explicit that nothing
there *classifies* the places of `F(W)`: `ProjPoint W` is only known to be *a* set of places.  This
file supplies the classification, and with it the reason the type exists.

## The headline

Every valuation subring of `F(W)` that contains `F` and is not all of `F(W)` is the place of exactly
one point of the projective curve:

```
placeEquiv : ProjPoint W ≃ {O : ValuationSubring F(W) // (∀ c : F, algebraMap F _ c ∈ O) ∧ O ≠ ⊤}
```

and therefore an `F`-algebra automorphism `σ` of `F(W)`, which carries such subrings to such
subrings, **permutes `ProjPoint W`**:

```
mapProjPoint σ : ProjPoint W ≃ ProjPoint W,   placeOf (mapProjPoint σ p) = (placeOf p).comap σ.symm
```

packaged as a monoid homomorphism `mapProjPointHom : Aut_F F(W) →* Equiv.Perm (ProjPoint W)`.
`EllipticCurves.FunctionField.GaloisFunctoriality` records why this is the missing piece for the
translation slot: `translateEndo` is *not* `IsFractionRing.ringEquivOfRingEquiv e` for a ring
automorphism `e` of `F[W]`, precisely because *"it moves the points at infinity"*.  Once the points
at infinity are members of a set that every `F`-automorphism permutes, that objection dissolves,
and `τ_T`'s action on divisors becomes definable.

## The case split, and why there is no third case

The proof splits on `genX W ∈ O`, and each branch is a previously-proved theorem applied verbatim:

* **`genX W ∈ O`** forces `F[W] ⊆ O`, and then `O` is `F[W]`-local: this is
  `IsDedekindDomain.exists_valuationSubringAtPrime_eq`
  (`EllipticCurves.FunctionField.ValuationSubringDedekind`).  Containment of `F[W]` needs
  `genY W ∈ O`, which is `WeierstrassCurve.valuation_le_one_of_valuation_le_one`
  (`EllipticCurves.NewtonPolygon`) — see the implementation note below.
* **`genX W ∉ O`** makes `O` the place at infinity: this is `eq_ordInftyValuationSubring`
  (`EllipticCurves.FunctionField.ValuationAtInfinity`).

No restriction along `F(X) ↪ F(W)`, no degree-two extension, no ramification and no second affine
chart appear anywhere.

## Main results

* `WeierstrassCurve.Affine.exists_heightOneSpectrum_of_genX_mem` — the affine branch;
* `WeierstrassCurve.Affine.placeOf` and `placeOf_injective` / `exists_placeOf_eq` — the
  classification, in unbundled form;
* **`WeierstrassCurve.Affine.placeEquiv`** — the bundled bijection;
* **`WeierstrassCurve.Affine.mapProjPoint`** and `mapProjPointHom` — the permutation action;
* `WeierstrassCurve.Affine.nonempty_heightOneSpectrum` and
  `WeierstrassCurve.Affine.placeOf_none_ne_placeOf_some` — the non-vacuity certificates: the
  projective curve has at least two points and `placeOf` separates them.

## Implementation notes

**`genY W ∈ O` is proved by a valuation computation, not by integral closure.**  The classical
argument observes that `genY` is a root of the monic quadratic
`T² + (a₁ genX + a₃) T − (genX³ + a₂ genX² + a₄ genX + a₆)` over `O` and invokes
`IsIntegrallyClosed` for valuation subrings.  That route needs glue between `IsIntegrallyClosed O`
(a statement about `O` and *its* fraction field) and membership in `O ⊆ F(W)`.  The elementary
route is shorter and was taken: if `1 < O.valuation (genY W)` then `(v y)²` strictly dominates every
other term of the Weierstrass equation, contradicting integrality of the right-hand side.  It is the
`v x ≤ 1` companion of the Newton-polygon dichotomy that `#650` already needed for the other branch,
so it is stated once, over an arbitrary value group, in `EllipticCurves.NewtonPolygon`.
**Consequence worth recording: the whole classification of places uses no integral-closure API.**

**The action is `comap σ.symm`, not `comap σ`.**  Mathlib's `ValuationSubring` API has `comap` and
no `map`, and `comap` is contravariant, so `σ ↦ (· .comap σ)` is an *anti*-homomorphism.  Since `σ`
is bijective, `O.comap σ.symm` is the *image* `σ '' O`, which is the covariant choice and makes
`mapProjPointHom` a genuine `MonoidHom` into `Equiv.Perm (ProjPoint W)`.  The pointwise form is
`mem_placeOf_mapProjPoint : f ∈ placeOf (mapProjPoint σ p) ↔ σ.symm f ∈ placeOf p`.

## What is *not* here

* `τ_T` itself, and every divisor pullback (`#465`, `#414`, `#422`).  This file makes the *target*
  of those constructions well-defined; it constructs none of them.
* **A witness `σ ≠ 1` for the automorphism action.**  See `mapProjPointHom`'s docstring: the
  natural candidate is the hyperelliptic involution, and producing it as an `AlgEquiv` is real work
  that is not attempted here.  No claim of non-triviality of the action is made.
* Riemann–Roch, the genus, the divisor class group, and any identification of `O` with a discrete
  valuation ring beyond `exists_zpow_eq` (`#650`).

## References

* Stichtenoth, *Algebraic Function Fields and Codes*, I.1–I.4.
* [J. H. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], II.1–II.3.
-/

open Polynomial IsDedekindDomain
open scoped Polynomial.Bivariate

namespace WeierstrassCurve.Affine

open CoordinateRing

variable {F : Type*} [Field F] {W : Affine F}

/-! ### Curve step B: the branch `genX W ∈ O`

The content is `F[W] ⊆ O`; the classification of the valuation subrings above a Dedekind domain
then applies verbatim at `R = F[W]`, `K = F(W)`.  Nothing in this section needs
`[IsDedekindDomain W.CoordinateRing]` except the final theorem. -/

section AffineBranch

variable {O : ValuationSubring W.FunctionField}
  (hF : ∀ c : F, algebraMap F W.FunctionField c ∈ O) (hx : CoordinateRing.genX W ∈ O)

include hF hx in
/-- **`genY` is integral wherever `genX` is.**  The `v x ≤ 1` branch of the Newton-polygon
dichotomy, applied to the generic point: were `genY W` to have a pole, `(v genY)²` would strictly
dominate every other term of `equation_gen`, while the right-hand side is `v`-integral because
`genX W` is and the coefficients lie in `F`. -/
lemma genY_mem_of_genX_mem : CoordinateRing.genY W ∈ O :=
  (O.valuation_le_one_iff _).1 <|
    WeierstrassCurve.valuation_le_one_of_valuation_le_one O.valuation
      (W.map (algebraMap F W.FunctionField))
      (by simpa using valuation_algebraMap_base_le hF W.a₁)
      (by simpa using valuation_algebraMap_base_le hF W.a₂)
      (by simpa using valuation_algebraMap_base_le hF W.a₃)
      (by simpa using valuation_algebraMap_base_le hF W.a₄)
      (by simpa using valuation_algebraMap_base_le hF W.a₆)
      equation_gen ((O.valuation_le_one_iff _).2 hx)

include hF hx in
/-- A polynomial in `genX` with coefficients in `F` lies in `O`. -/
lemma algebraMap_polynomial_mem (p : F[X]) : algebraMap F[X] W.FunctionField p ∈ O := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => rw [map_add]; exact add_mem hp hq
  | monomial n c =>
      rw [← Polynomial.C_mul_X_pow_eq_monomial, map_mul, map_pow, algebraMap_polynomial_X]
      refine mul_mem ?_ (pow_mem hx n)
      rw [Polynomial.C_eq_algebraMap, ← IsScalarTower.algebraMap_apply]
      exact hF c

include hF hx in
/-- **`F[W] ⊆ O`.**  Every element of the coordinate ring is `p • 1 + q • Y` with `p, q ∈ F[X]`, and
both parts lie in `O` by the two previous lemmas. -/
theorem algebraMap_coordinateRing_mem (a : W.CoordinateRing) :
    algebraMap W.CoordinateRing W.FunctionField a ∈ O := by
  obtain ⟨p, q, rfl⟩ := CoordinateRing.exists_smul_basis_eq a
  rw [map_add, algebraMap_smul_one, algebraMap_smul_Y]
  exact add_mem (algebraMap_polynomial_mem hF hx p)
    (mul_mem (algebraMap_polynomial_mem hF hx q) (genY_mem_of_genX_mem hF hx))

end AffineBranch

/-! ### Transport of valuation subrings along an automorphism

These lemmas are about `ValuationSubring.comap` and know nothing about the curve; they are what
makes the automorphism action of the last section well-defined. -/

section Comap

variable {O : ValuationSubring W.FunctionField} (σ : W.FunctionField ≃ₐ[F] W.FunctionField)

/-- Pulling back along the identity does nothing.  (Mathlib has `ValuationSubring.comap_comap` but
no `comap_id`.) -/
private lemma comap_ringHom_id (A : ValuationSubring W.FunctionField) :
    A.comap (RingHom.id W.FunctionField) = A := rfl

/-- An `F`-algebra automorphism fixes `F`, so pulling back along it preserves "contains `F`". -/
lemma algebraMap_mem_comap_algEquiv (hF : ∀ c : F, algebraMap F W.FunctionField c ∈ O) (c : F) :
    algebraMap F W.FunctionField c ∈ O.comap (σ : W.FunctionField →+* W.FunctionField) := by
  rw [ValuationSubring.mem_comap, show (σ : W.FunctionField →+* W.FunctionField)
    (algebraMap F W.FunctionField c) = algebraMap F W.FunctionField c from σ.commutes c]
  exact hF c

/-- Pulling back along a *surjective* map preserves properness. -/
lemma comap_algEquiv_ne_top (hO : O ≠ ⊤) :
    O.comap (σ : W.FunctionField →+* W.FunctionField) ≠ ⊤ := fun h => hO <| by
  refine SetLike.ext fun x => iff_of_true ?_ (ValuationSubring.mem_top x)
  have hx : σ.symm x ∈ O.comap (σ : W.FunctionField →+* W.FunctionField) :=
    h ▸ ValuationSubring.mem_top _
  simpa using hx

/-- Two automorphisms that undo each other give inverse pullbacks. -/
private lemma comap_comap_of_apply_apply {e f : W.FunctionField ≃ₐ[F] W.FunctionField}
    (h : ∀ x, e (f x) = x) (A : ValuationSubring W.FunctionField) :
    (A.comap (e : W.FunctionField →+* W.FunctionField)).comap
      (f : W.FunctionField →+* W.FunctionField) = A := by
  rw [ValuationSubring.comap_comap,
    show (e : W.FunctionField →+* W.FunctionField).comp
      (f : W.FunctionField →+* W.FunctionField) = RingHom.id _ from RingHom.ext h, comap_ringHom_id]

end Comap

/-! ### Curve step C: the classification -/

section Classification

variable [IsDedekindDomain W.CoordinateRing]

/-- **The affine branch.**  A proper valuation subring of `F(W)` containing `F` and `genX W` is the
localisation of `F[W]` at a height-one prime — i.e. an affine closed point of the curve. -/
theorem exists_heightOneSpectrum_of_genX_mem {O : ValuationSubring W.FunctionField}
    (hF : ∀ c : F, algebraMap F W.FunctionField c ∈ O) (hO : O ≠ ⊤)
    (hx : CoordinateRing.genX W ∈ O) :
    ∃ v : HeightOneSpectrum W.CoordinateRing,
      HeightOneSpectrum.valuationSubringAtPrime W.FunctionField v = O :=
  IsDedekindDomain.exists_valuationSubringAtPrime_eq O (algebraMap_coordinateRing_mem hF hx) hO

variable (W) in
/-- **The place of `F(W)` attached to a point of the projective curve**: the localisation of `F[W]`
at an affine closed point, and the place at infinity at `none`. -/
noncomputable def placeOf : ProjPoint W → ValuationSubring W.FunctionField
  | none => ordInftyValuationSubring W
  | some v => HeightOneSpectrum.valuationSubringAtPrime W.FunctionField v

@[simp] lemma placeOf_none : placeOf W none = ordInftyValuationSubring W := rfl

@[simp] lemma placeOf_some (v : HeightOneSpectrum W.CoordinateRing) :
    placeOf W (some v) = HeightOneSpectrum.valuationSubringAtPrime W.FunctionField v := rfl

/-- Every place of the projective curve is a place *over `F`*. -/
lemma algebraMap_mem_placeOf (p : ProjPoint W) (c : F) :
    algebraMap F W.FunctionField c ∈ placeOf W p := by
  cases p with
  | none => exact algebraMap_mem_ordInftyValuationSubring c
  | some v =>
      rw [placeOf_some, IsScalarTower.algebraMap_apply F W.CoordinateRing W.FunctionField]
      exact HeightOneSpectrum.algebraMap_mem_valuationSubringAtPrime v _

/-- No place of the projective curve is all of `F(W)`. -/
lemma placeOf_ne_top (p : ProjPoint W) : placeOf W p ≠ ⊤ := by
  cases p with
  | none => exact fun h => genX_notMem_ordInftyValuationSubring (h ▸ ValuationSubring.mem_top _)
  | some v => exact HeightOneSpectrum.valuationSubringAtPrime_ne_top v

/-- **Distinct points give distinct places.**  Infinite versus affine is separated by `genX W`
(`#650`'s `ordInftyValuationSubring_ne_valuationSubringAtPrime`), and affine versus affine by the
injectivity of `v ↦ F[W]_v`. -/
theorem placeOf_injective : Function.Injective (placeOf W) := by
  rintro (_ | v) (_ | w) h
  · rfl
  · exact absurd h (ordInftyValuationSubring_ne_valuationSubringAtPrime _)
  · exact absurd h.symm (ordInftyValuationSubring_ne_valuationSubringAtPrime _)
  · exact congrArg some (HeightOneSpectrum.valuationSubringAtPrime_injective h)

/-- **Every place over `F` comes from a point.**  The case split on `genX W ∈ O`. -/
theorem exists_placeOf_eq (O : ValuationSubring W.FunctionField)
    (hF : ∀ c : F, algebraMap F W.FunctionField c ∈ O) (hO : O ≠ ⊤) :
    ∃ p : ProjPoint W, placeOf W p = O := by
  by_cases hx : CoordinateRing.genX W ∈ O
  · obtain ⟨v, hv⟩ := exists_heightOneSpectrum_of_genX_mem hF hO hx
    exact ⟨some v, hv⟩
  · exact ⟨none, (eq_ordInftyValuationSubring hF hx).symm⟩

variable (W) in
/-- **The points of the projective curve are exactly the places of `F(W)` over `F`.** -/
noncomputable def placeEquiv :
    ProjPoint W ≃ {O : ValuationSubring W.FunctionField //
      (∀ c : F, algebraMap F W.FunctionField c ∈ O) ∧ O ≠ ⊤} :=
  Equiv.ofBijective
    (fun p => ⟨placeOf W p, algebraMap_mem_placeOf p, placeOf_ne_top p⟩)
    ⟨fun _ _ h => placeOf_injective (congrArg Subtype.val h),
      fun O => (exists_placeOf_eq O.1 O.2.1 O.2.2).imp fun _ hp => Subtype.ext hp⟩

@[simp] lemma placeEquiv_apply_coe (p : ProjPoint W) :
    ((placeEquiv W p : _) : ValuationSubring W.FunctionField) = placeOf W p := rfl

@[simp] lemma placeOf_placeEquiv_symm
    (O : {O : ValuationSubring W.FunctionField //
      (∀ c : F, algebraMap F W.FunctionField c ∈ O) ∧ O ≠ ⊤}) :
    placeOf W ((placeEquiv W).symm O) = O :=
  congrArg Subtype.val ((placeEquiv W).apply_symm_apply O)

/-! ### Non-vacuity

`placeEquiv` would be an equivalence of two empty types if the projective curve had no points.  It
does not: `none` is always there, and there is always at least one affine closed point, because
`F[W]` is not a field. -/

omit [IsDedekindDomain W.CoordinateRing] in
/-- **There is at least one affine closed point.**  The coordinate function `x`, i.e.
`mk W (C X) : F[W]`, is not a unit — its degree is `2`, and `deg_eq_zero_iff_isUnit` says the units
are exactly the elements of degree `0` — so it lies in a maximal ideal, which is prime and
nonzero. -/
lemma nonempty_heightOneSpectrum : Nonempty (HeightOneSpectrum W.CoordinateRing) := by
  set a : W.CoordinateRing := CoordinateRing.mk W (Polynomial.C (Polynomial.X : F[X])) with ha
  have hne : a ≠ 0 := mk_C_ne_zero Polynomial.X_ne_zero
  have hnu : ¬ IsUnit a := by
    rw [← deg_eq_zero_iff_isUnit hne, ha, deg_mk_C, Polynomial.natDegree_X]
    omega
  obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal (Ideal.span {a})
    fun h => hnu (Ideal.span_singleton_eq_top.1 h)
  exact ⟨⟨m, hm.isPrime, fun h => hne (Ideal.mem_bot.1
    (h ▸ hle (Ideal.mem_span_singleton_self _)))⟩⟩

/-- The point at infinity is not an affine point, and `placeOf` sees the difference. -/
theorem placeOf_none_ne_placeOf_some (v : HeightOneSpectrum W.CoordinateRing) :
    placeOf W none ≠ placeOf W (some v) :=
  ordInftyValuationSubring_ne_valuationSubringAtPrime v

/-- The projective curve has at least two points. -/
instance : Nontrivial (ProjPoint W) :=
  haveI := nonempty_heightOneSpectrum (W := W); inferInstanceAs (Nontrivial (Option _))

end Classification

/-! ### Curve step D: the permutation action of `Aut_F F(W)` -/

section Aut

variable [IsDedekindDomain W.CoordinateRing] (σ τ : W.FunctionField ≃ₐ[F] W.FunctionField)

variable (W) in
/-- The underlying map of `mapProjPoint`: the point whose place is the `σ`-image of the place of
`p`.  It exists, and is unique, by `exists_placeOf_eq` and `placeOf_injective`. -/
noncomputable def mapProjPointFun (p : ProjPoint W) : ProjPoint W :=
  (exists_placeOf_eq ((placeOf W p).comap (σ.symm : W.FunctionField →+* W.FunctionField))
    (algebraMap_mem_comap_algEquiv σ.symm (algebraMap_mem_placeOf p))
    (comap_algEquiv_ne_top σ.symm (placeOf_ne_top p))).choose

/-- The characterising property of `mapProjPointFun`. -/
lemma placeOf_mapProjPointFun (p : ProjPoint W) :
    placeOf W (mapProjPointFun W σ p)
      = (placeOf W p).comap (σ.symm : W.FunctionField →+* W.FunctionField) :=
  (exists_placeOf_eq ((placeOf W p).comap (σ.symm : W.FunctionField →+* W.FunctionField))
    (algebraMap_mem_comap_algEquiv σ.symm (algebraMap_mem_placeOf p))
    (comap_algEquiv_ne_top σ.symm (placeOf_ne_top p))).choose_spec

variable (W) in
/-- **An `F`-automorphism of `F(W)` permutes the points of the projective curve.**  This is the
deliverable rung 4 exists for: it is what makes an action on `ProjPoint W`-indexed divisors
definable even for maps, such as translation by a point, that move the point at infinity. -/
noncomputable def mapProjPoint : ProjPoint W ≃ ProjPoint W where
  toFun := mapProjPointFun W σ
  invFun := mapProjPointFun W σ.symm
  left_inv p := placeOf_injective <| by
    rw [placeOf_mapProjPointFun, placeOf_mapProjPointFun,
      comap_comap_of_apply_apply (fun x => by simp)]
  right_inv p := placeOf_injective <| by
    rw [placeOf_mapProjPointFun, placeOf_mapProjPointFun,
      comap_comap_of_apply_apply (fun x => by simp)]

@[simp] lemma placeOf_mapProjPoint (p : ProjPoint W) :
    placeOf W (mapProjPoint W σ p)
      = (placeOf W p).comap (σ.symm : W.FunctionField →+* W.FunctionField) :=
  placeOf_mapProjPointFun σ p

/-- The pointwise form: the place of `mapProjPoint σ p` is the `σ`-image of the place of `p`. -/
lemma mem_placeOf_mapProjPoint (p : ProjPoint W) (f : W.FunctionField) :
    f ∈ placeOf W (mapProjPoint W σ p) ↔ σ.symm f ∈ placeOf W p := by
  rw [placeOf_mapProjPoint]; exact Iff.rfl

/-- `mapProjPoint` is determined by its characterising property. -/
theorem mapProjPoint_eq_iff {p q : ProjPoint W} :
    mapProjPoint W σ p = q ↔
      placeOf W q = (placeOf W p).comap (σ.symm : W.FunctionField →+* W.FunctionField) :=
  ⟨fun h => h ▸ placeOf_mapProjPoint σ p,
    fun h => placeOf_injective ((placeOf_mapProjPoint σ p).trans h.symm)⟩

@[simp] lemma mapProjPoint_one :
    mapProjPoint W (1 : W.FunctionField ≃ₐ[F] W.FunctionField) = Equiv.refl _ :=
  Equiv.ext fun p => placeOf_injective <| by
    rw [placeOf_mapProjPoint, Equiv.refl_apply,
      show ((1 : W.FunctionField ≃ₐ[F] W.FunctionField).symm :
        W.FunctionField →+* W.FunctionField) = RingHom.id _ from rfl, comap_ringHom_id]

lemma mapProjPoint_mul :
    mapProjPoint W (σ * τ) = (mapProjPoint W τ).trans (mapProjPoint W σ) :=
  Equiv.ext fun p => placeOf_injective <| by
    rw [placeOf_mapProjPoint, Equiv.trans_apply, placeOf_mapProjPoint, placeOf_mapProjPoint,
      ValuationSubring.comap_comap]
    exact congrArg _ (RingHom.ext fun x => rfl)

variable (W) in
/-- **The permutation action, packaged.**  `Aut_F F(W) →* Equiv.Perm (ProjPoint W)`.

The `comap σ.symm` convention (rather than `comap σ`) is what makes this a homomorphism rather than
an anti-homomorphism; see the module docstring.

**No non-triviality is claimed.**  Exhibiting a `σ ≠ 1` would need the hyperelliptic involution
`y ↦ −y − a₁x − a₃` as an `AlgEquiv`, which this file does not construct: `translateEndoAlgHom` is
only an `AlgHom`, and the composition law `translateEndo_comp` cannot produce the identity because
the group identity is not an affine point.  Recorded here rather than asserted. -/
noncomputable def mapProjPointHom :
    (W.FunctionField ≃ₐ[F] W.FunctionField) →* Equiv.Perm (ProjPoint W) where
  toFun := mapProjPoint W
  map_one' := mapProjPoint_one
  map_mul' σ τ := mapProjPoint_mul σ τ

@[simp] lemma mapProjPointHom_apply : mapProjPointHom W σ = mapProjPoint W σ := rfl

end Aut

end WeierstrassCurve.Affine
