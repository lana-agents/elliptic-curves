/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import EllipticCurves.FunctionField.MulByTwoPlaceAtInfinity
import EllipticCurves.FunctionField.PlaceResidueField

/-!
# The relative residue degree of a place along a contraction, and the route to `∑ e_p · f_p = 4`

`EllipticCurves.FunctionField.PlacePullback` contracts a place `p` of `F(W)` along an `F`-embedding
`φ : F(W) → F(W)` with `F(W)` integral over the image: `comapProjPoint φ p` is the point whose
place is `(placeOf W p).comap φ`, and `ramificationIdx φ p` is the positive integer with

```
ord_p (φ f) = e_p · ord_{comapProjPoint φ p} (f).
```

That is the `e_p` of the fundamental identity `∑_{p ↦ q} e_p · f_p = [F(W) : φ F(W)]`.  This file
supplies the `f_p`: the **relative residue degree** `[κ(p) : κ(q)]`, where `q = comapProjPoint φ p`
and the field extension is the one induced by `φ` itself.

## Why `κ(comapProjPoint φ p)` is the residue field of the place *below* `p`

The place below `p` is a place of the subfield `L = φ F(W)`, with valuation ring `L ∩ placeOf W p`,
and `κ(q)` is a residue field of a place of `F(W)`, not of `L`.  The two agree because `φ` is an
isomorphism onto `L`, and it carries `(placeOf W p).comap φ` *onto* `L ∩ placeOf W p`: a point of
the target is `φ x` with `φ x ∈ placeOf W p`, which is exactly membership of `x` in the contraction.
`placeHomComap` below is that isomorphism, read as a ring map into `placeOf W p`, and
`placeHomComap_injective` is the half of the statement that is not definitional.  So
`residueDegreeComap` really is the classical `f_p`, transported along `φ` rather than restated.

## Main results

* `WeierstrassCurve.Affine.isUnit_placeOf_iff` (in `PlaceResidueField`) — a function is a unit of a
  place exactly when it is nonzero of order `0` there;
* **`WeierstrassCurve.Affine.placeHomComap`** — the induced map of local rings
  `placeOf W (comapProjPoint φ p) →+* placeOf W p`, and `instIsLocalHomPlaceHomComap`: it is a
  *local* homomorphism.  The proof is where `ramificationIdx_pos` is consumed: `ord_p (φ x) = 0`
  forces `e_p · ord_q x = 0`, and `e_p > 0`;
* `WeierstrassCurve.Affine.instAlgebraPlaceComap` and `instIsScalarTowerPlaceComap` — the resulting
  `F`-algebra tower `F → placeOf W q → placeOf W p`, from which Mathlib's
  `IsLocalRing.ResidueField` machinery supplies `Algebra κ(q) κ(p)` and `IsScalarTower F κ(q) κ(p)`
  with no further work;
* **`WeierstrassCurve.Affine.residueDegreeComap`** — `f_p = [κ(p) : κ(q)]`;
* **`WeierstrassCurve.Affine.residueDegreeProj_mul_residueDegreeComap`** — the tower formula
  `deg q · f_p = deg p`, i.e. `[κ(q) : F] · [κ(p) : κ(q)] = [κ(p) : F]`;
* `WeierstrassCurve.Affine.residueDegreeComap_eq_one_of_residueDegreeProj_eq_one` — **the corollary
  the Weil-pairing front consumes**: at a place that is rational over `F`, the relative residue
  degree is `1`, so the fundamental identity collapses to `∑_{p ↦ q} e_p = 4`.  Over an
  algebraically closed base field every place is rational, so this applies at every `p`;
* `WeierstrassCurve.Affine.residueDegreeComap_algEquiv` — the consistency check: contracting along
  an *automorphism* gives relative residue degree `1`, matching `ramificationIdx_algEquiv`;
* `WeierstrassCurve.Affine.CoordinateRing.residueDegreeTwo` and
  `residueDegreeProj_mul_residueDegreeTwo` — the `[2]∗` instantiation, plus
  `residueDegreeTwo_none_eq_one_of_ne_zero`, which computes `f_none = 1` at the point at infinity
  from nothing but `residueDegreeProj W none ≠ 0`.  That hypothesis is discharged outright by
  `#749`'s `residueDegreeProj_none_eq_one`, so the unconditional
  `residueDegreeTwo_none_eq_one` in `EllipticCurves.FunctionField.PlaceRamificationInertia` is the
  form to use.

## What is *not* here: the fundamental identity, and the route decision that unblocked it

**Nothing below proves `∑_{p ↦ q} e_p · f_p = 4`.**  The sibling issue asked for a *written route
decision, with evidence, before any theorem*, and the decision was that the identity does not close
in one session — not for want of effort, but because it rested on three named prerequisites that
were, when this was written, absent from this tree.

All three have since been supplied, along the route chosen below: **(c-i)** is `#753`
(`EllipticCurves.FunctionField.PlaceDiscreteValuationRing`), **(c-ii)** is `#754`
(`EllipticCurves.FunctionField.PlaceBelowIntegralClosure`) with separability from `#759`, and
**(c-iii)** is `#755` (`EllipticCurves.FunctionField.PlacePrimesOverFibre`).  The identity itself is
`EllipticCurves.FunctionField.PlaceRamificationInertia` (`#763`).  The record is kept, with each
bullet updated in place, because it is the map of the route that was taken — and because the one
gap it does *not* close is recorded at the end.

The right-hand side is not in doubt: `finrank_mulByTwoRange_functionField`
(`MulByTwoDegree.lean`) gives `[F(W) : [2]∗F(W)] = 4` under `[W.IsElliptic]`.  The three candidate
routes to the sum were:

**(c) Mathlib's `Ideal.sum_ramification_inertia_eq_finrank`** (`RamificationInertia/Basic.lean:72`).
Contrary to the parent issue's premise, this needs no Dedekind hypothesis and no AKLB
identification — only `[IsDomain R] [Module.Finite R S] [Module.Flat R S]` and a finite fibre
`[Fintype (p.primesOver S)]` — so it is the best of the three.  It still does not close, and for
three separate reasons:

* **(c-i) `IsDiscreteValuationRing (placeOf W q)`.**  It was not available when this was written,
  and was explicitly disclaimed in `PlaceResidueField.lean` and in `ValuationAtInfinity.lean`, whose
  docstring said discreteness at infinity is proved only in the doubled form `exists_zpow_eq`.
  Route (c) wants `R` at least Noetherian, and the natural `R` is the valuation ring of `q`.  This
  one was called a *small* issue rather than a research problem, and that was right:
  `exists_divisorProj_eq_one` already gives a uniformizer at every place — i.e. the value group
  surjects onto `ℤ` — and `mem_placeOf_iff_divisorProj_nonneg` turns ideal membership into an order
  inequality, which is the whole of the argument that every ideal is generated by a power of a
  uniformizer.  That is the argument `#753` runs.
* **(c-ii) `Module.Finite` for the integral closure needs separability.**  Still true as a
  statement about what Mathlib's route asks for; `#754` supplies it.  Mathlib reaches
  module-finiteness of an integral closure through `IsIntegralClosure.finite`
  (`DedekindDomain/IntegralClosure.lean`), which wants `[IsIntegrallyClosed R] [IsNoetherianRing R]
  [IsFractionRing R L] [Algebra.IsSeparable L F(W)]`.  The `IsNoetherianRing R` is (c-i) again.

  Separability of `F(W) / [2]∗F(W)` was stated nowhere in this tree when this decision was written;
  there are now **two** routes to it, and which one to use depends on the base field.  In
  characteristic zero it is free from `Algebra.IsSeparable.of_integral`
  (`Mathlib/FieldTheory/Separable.lean`), an instance under `[Algebra.IsIntegral F K] [CharZero F]`,
  with `module_finite_mulByTwoRange` supplying the integrality — that route needs no algebraic
  closure and is the one to use over `ℚ` or a number field.  Over an algebraically closed base field
  of characteristic `≠ 2` it holds with **no** hypothesis on the characteristic beyond that, by
  Artin's theorem against `#682`'s degree `4`: `isSeparable_mulByTwoEndoFieldRange_of_isAlgClosed`
  (`EllipticCurves.FunctionField.MulByTwoGalois`, `#759`), which additionally gives `IsGalois`.
  Flatness, by contrast, is *not* a blocker: over a discrete valuation ring torsion-free implies
  flat, and a subring of `F(W)` is torsion-free.
* **(c-iii) the fibre dictionary.**  `p.primesOver S` has to be matched with
  `(comapProjPointTwo h2) ⁻¹' {q}`.  `finite_comapProjPointTwo_preimage_singleton` (`#675`) makes
  the sum *statable*, but nothing identified the two index sets, and the `none` branch of
  `ProjPoint W = Option (HeightOneSpectrum W.CoordinateRing)` is not a prime of any ring — the
  asymmetry `placeOf` was built to dissolve.  "Expect this to be the largest of the three" was the
  prediction, and it held: `#755` is `primesOverEquivFibre`, and it took a session of its own.

**(a) unblock `#421`** — build `B = integralClosure ([2]∗F[W]) F(W)` and run AKLB.  Strictly worse
than (c).  `#421`'s 2026-08-16 correction records that `B ⊋ F[W]`, and the reason is visible:
`x ∘ [2] = Φ₂/Ψ₂Sq` has its poles exactly on `E[2]`, so `B` is the ring of functions regular off
`E[2]`, strictly larger than `F[W]`, the functions regular off `∞`.  So (a) must *construct* `B` and
then prove it Dedekind — which is (c-ii) and more.

**(b) localise by hand** — (c-i), (c-ii) and (c-iii) again, with no Mathlib assistance.

One near-miss worth recording so it is not rediscovered: `sum_ramification_inertia_eq_finrank_fiber`
(`RamificationInertia/Basic.lean:44`) needs only `[Algebra.QuasiFinite R S]`, which looks like an
escape from (c-ii).  It is not: its right-hand side is `finrank κ(p) (p.Fiber S)`, and the step from
there to `finrank R S` is `finrank_fiber_eq_finrank`, which reinstates `Module.Finite` and
`Module.Flat` exactly.

Also not here: the individual value of `ramificationIdxTwo` at an affine place — `#763` sums them
and computes none, and `#774` (`EllipticCurves.FunctionField.MulByTwoFibreInfinity`, then
`EllipticCurves.FunctionField.MulByTwoFibreAffine`) computes exactly those lying over an
`F`-rational point, where the index is `1`; a place over a closed point with a nontrivial residue
extension is **still not anywhere**.  Also not here: any
comparison of `residueDegreeProj` with `degPt` (`DivisorDegree.lean`), which is a relative ideal
norm to `F[X]` and not a residue-field degree; the unconditional
`Ideal.inertiaDeg 𝔪 P = residueDegreeTwo h2 p` (`#763` proves only the `[IsAlgClosed F]` form
`= 1`); and `#E[n] = n²`, whose link to the field degree runs through the count "a separable isogeny
has `#ker = deg`".  That last one is **not** (c-ii): the separability of `F(W) / [2]∗F(W)` is
available (`#759`), and the counting step is a different statement that this tree does not have.
Do not assume it.

## References

* [J. H. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], II.2.
* Stichtenoth, *Algebraic Function Fields and Codes*, III.1.11 (the fundamental identity).
-/

open IsDedekindDomain

namespace WeierstrassCurve.Affine

variable {F : Type*} [Field F] {W : Affine F} [IsDedekindDomain W.CoordinateRing]
  {φ : W.FunctionField →+* W.FunctionField}
  (hφF : ∀ c : F, φ (algebraMap F W.FunctionField c) = algebraMap F W.FunctionField c)
  (hφint : ∀ z : W.FunctionField, φ.IsIntegralElem z)

/-! ### The induced map of local rings -/

/-- **The map of local rings induced by `φ`**, from the place below `p` to the place at `p`.

An element of `placeOf W (comapProjPoint φ p)` is a function `x` with `φ x ∈ placeOf W p`, by
`mem_placeOf_comapProjPoint`, so `φ` restricts to a ring map between the two places.  It is the
isomorphism of `(placeOf W p).comap φ` with `L ∩ placeOf W p` — the valuation ring of the place of
`L = φ F(W)` below `p` — read as a map into `placeOf W p`; see the module docstring. -/
noncomputable def placeHomComap (p : ProjPoint W) :
    ↥(placeOf W (comapProjPoint hφF hφint p)) →+* ↥(placeOf W p) :=
  (φ.comp (placeOf W (comapProjPoint hφF hφint p)).subtype).codRestrict (placeOf W p)
    fun x => (mem_placeOf_comapProjPoint hφF hφint p (x : W.FunctionField)).1 x.2

@[simp]
lemma coe_placeHomComap (p : ProjPoint W) (x : placeOf W (comapProjPoint hφF hφint p)) :
    ((placeHomComap hφF hφint p x : placeOf W p) : W.FunctionField) = φ (x : W.FunctionField) :=
  rfl

/-- `φ` is injective, being a ring map out of a field, so the place below `p` embeds in the place at
`p`. -/
theorem placeHomComap_injective (p : ProjPoint W) :
    Function.Injective (placeHomComap hφF hφint p) := fun x y h =>
  Subtype.ext (φ.injective (by simpa using congrArg Subtype.val h))

instance instIsLocalHomPlaceHomComap (p : ProjPoint W) :
    IsLocalHom (placeHomComap hφF hφint p) := by
  constructor
  intro x hx
  rw [isUnit_placeOf_iff] at hx ⊢
  obtain ⟨hne, hord⟩ := hx
  rw [coe_placeHomComap] at hne hord
  have hx0 : (x : W.FunctionField) ≠ 0 := fun h => hne (by rw [h, map_zero])
  refine ⟨hx0, ?_⟩
  rw [divisorProj_comp_apply hφF hφint hx0 p] at hord
  have hpos := ramificationIdx_pos hφF hφint p
  rcases mul_eq_zero.1 hord with h | h
  · omega
  · exact h

/-- The place below `p` is an `F`-subalgebra of the place at `p`, through `φ`. -/
noncomputable instance instAlgebraPlaceComap (p : ProjPoint W) :
    Algebra ↥(placeOf W (comapProjPoint hφF hφint p)) ↥(placeOf W p) :=
  (placeHomComap hφF hφint p).toAlgebra

instance instIsLocalHomAlgebraMapPlaceComap (p : ProjPoint W) :
    IsLocalHom (algebraMap ↥(placeOf W (comapProjPoint hφF hφint p)) ↥(placeOf W p)) :=
  instIsLocalHomPlaceHomComap hφF hφint p

/-- `φ` fixes `F`, so the two places sit in a tower over the constant field.  This is what makes the
residue degrees multiplicative below. -/
instance instIsScalarTowerPlaceComap (p : ProjPoint W) :
    IsScalarTower F ↥(placeOf W (comapProjPoint hφF hφint p)) ↥(placeOf W p) := by
  refine IsScalarTower.of_algebraMap_eq fun c => ?_
  apply Subtype.ext
  change algebraMap F W.FunctionField c = φ (algebraMap F W.FunctionField c)
  rw [hφF]

/-! ### The relative residue degree -/

/-- **The relative residue degree of `φ` at a point `p` of the projective curve**, `f_p`.

`[κ(p) : κ(q)]` for `q = comapProjPoint φ p`, the extension being the one induced by `φ` through
`placeHomComap`.  Mathlib's `IsLocalRing.ResidueField` API supplies the `Algebra κ(q) κ(p)`
instance from `instAlgebraPlaceComap` and `instIsLocalHomAlgebraMapPlaceComap`, so no residue map is
built by hand here.

⚠️ As with `residueDegreeProj`, nothing below shows this is nonzero: `Module.finrank` is `0` on an
infinite-dimensional module.  `residueDegreeProj_mul_residueDegreeComap` is the tool for ruling that
out — it is `1` as soon as `κ(p)` is `F`. -/
noncomputable def residueDegreeComap (p : ProjPoint W) : ℕ :=
  Module.finrank (residueFieldProj W (comapProjPoint hφF hφint p)) (residueFieldProj W p)

/-- **The residue degrees are multiplicative**: `[κ(q) : F] · [κ(p) : κ(q)] = [κ(p) : F]` for
`q = comapProjPoint φ p`.

This is `Module.finrank_mul_finrank` on the tower `F → κ(q) → κ(p)`, which is available because
`instIsScalarTowerPlaceComap` puts the two *places* in a tower over `F` and Mathlib propagates that
to the residue fields.  It holds with no finiteness hypothesis, both sides being `0` when `κ(p)` is
infinite over `F`. -/
theorem residueDegreeProj_mul_residueDegreeComap (p : ProjPoint W) :
    residueDegreeProj W (comapProjPoint hφF hφint p) * residueDegreeComap hφF hφint p
      = residueDegreeProj W p :=
  Module.finrank_mul_finrank F _ _

/-- **A rational place has relative residue degree one.**

If `κ(p) = F` then every intermediate field is `F` as well, so `f_p = 1` *and* the place below is
rational too.  Over an algebraically closed base field the hypothesis holds at every place, and this
is what collapses `∑_{p ↦ q} e_p · f_p = 4` to `∑_{p ↦ q} e_p = 4`.

The proof is the tower formula and `Nat.mul_eq_one`; no property of `φ` beyond the standing two is
used. -/
theorem residueDegreeComap_eq_one_of_residueDegreeProj_eq_one {p : ProjPoint W}
    (hp : residueDegreeProj W p = 1) :
    residueDegreeProj W (comapProjPoint hφF hφint p) = 1 ∧ residueDegreeComap hφF hφint p = 1 :=
  mul_eq_one.1 ((residueDegreeProj_mul_residueDegreeComap hφF hφint p).trans hp)

/-- Relative residue degree one is surjectivity of the structure map `κ(q) → κ(p)`, the relative
form of `residueDegreeProj_eq_one_iff_surjective`. -/
theorem residueDegreeComap_eq_one_iff_surjective (p : ProjPoint W) :
    residueDegreeComap hφF hφint p = 1 ↔ Function.Surjective
      (algebraMap (residueFieldProj W (comapProjPoint hφF hφint p)) (residueFieldProj W p)) := by
  rw [residueDegreeComap, ← Subalgebra.bot_eq_top_iff_finrank_eq_one, eq_top_iff]
  exact ⟨fun h x => Algebra.mem_bot.1 (h Algebra.mem_top),
    fun h _ _ => Algebra.mem_bot.2 (h _)⟩

/-- Whenever the map of local rings is onto — which happens exactly when nothing is lost at the
place, as for an automorphism — the relative residue degree is `1`. -/
theorem residueDegreeComap_eq_one_of_surjective {p : ProjPoint W}
    (h : Function.Surjective (placeHomComap hφF hφint p)) :
    residueDegreeComap hφF hφint p = 1 := by
  refine (residueDegreeComap_eq_one_iff_surjective hφF hφint p).2 fun x => ?_
  obtain ⟨y, rfl⟩ := IsLocalRing.residue_surjective x
  obtain ⟨z, rfl⟩ := h y
  exact ⟨IsLocalRing.residue _ z, rfl⟩

/-! ### Consistency with `PlacePullback`: an automorphism has relative residue degree one

`ramificationIdx_algEquiv` checks that the ramification index of an automorphism is `1`.  The same
check is owed for the residue degree, and it is the statement that the two files' conventions have
not drifted apart: `e_p = f_p = 1` says an automorphism is unramified *and* residually trivial. -/

/-- **Contracting along an automorphism has relative residue degree `1`**, the companion of
`ramificationIdx_algEquiv`.  The induced map of local rings is onto: `y` in the place at `p` is the
image of `σ.symm y`, which lies in the contracted place precisely because `σ (σ.symm y) = y`. -/
theorem residueDegreeComap_algEquiv (σ : W.FunctionField ≃ₐ[F] W.FunctionField)
    (p : ProjPoint W) :
    residueDegreeComap (φ := (σ : W.FunctionField →+* W.FunctionField)) σ.commutes
      (isIntegralElem_algEquiv σ) p = 1 := by
  refine residueDegreeComap_eq_one_of_surjective _ _ fun y => ?_
  have hmem : σ.symm (y : W.FunctionField) ∈ placeOf W (comapProjPoint
      (φ := (σ : W.FunctionField →+* W.FunctionField)) σ.commutes
        (isIntegralElem_algEquiv σ) p) := by
    rw [mem_placeOf_comapProjPoint]
    change σ (σ.symm (y : W.FunctionField)) ∈ placeOf W p
    rw [AlgEquiv.apply_symm_apply]
    exact y.2
  refine ⟨⟨σ.symm (y : W.FunctionField), hmem⟩, Subtype.ext ?_⟩
  rw [coe_placeHomComap]
  change σ (σ.symm (y : W.FunctionField)) = (y : W.FunctionField)
  rw [AlgEquiv.apply_symm_apply]

/-! ### The `[2]∗` instantiation -/

namespace CoordinateRing

/-- **The relative residue degree of `[2]∗`**, `f_p = [κ(p) : κ([2]⁻¹ p)]`.

Together with `ramificationIdxTwo` this is the pair of local invariants of the degree-four extension
`F(W) / [2]∗F(W)` at a place.  Their fundamental identity `∑_{p ↦ q} e_p · f_p = 4` is not proved
here; it is `sum_ramificationIdxTwo_mul_residueDegreeTwo`
(`EllipticCurves.FunctionField.PlaceRamificationInertia`, `#763`), over an algebraically closed base
field.  See the module docstring for the route decision it took. -/
noncomputable def residueDegreeTwo (h2 : (2 : F) ≠ 0) (p : ProjPoint W) : ℕ :=
  residueDegreeComap (mulByTwoEndo_algebraMap_base h2) (mulByTwoEndo_isIntegralElem h2) p

/-- The tower formula for `[2]∗`: `[κ([2]⁻¹ p) : F] · f_p = [κ(p) : F]`. -/
theorem residueDegreeProj_mul_residueDegreeTwo (h2 : (2 : F) ≠ 0) (p : ProjPoint W) :
    residueDegreeProj W (comapProjPointTwo h2 p) * residueDegreeTwo h2 p = residueDegreeProj W p :=
  residueDegreeProj_mul_residueDegreeComap _ _ p

/-- **At a place rational over `F`, `[2]∗` is residually trivial.**  This is the input the
Weil-pairing front consumes: over an algebraically closed base field every place is rational, so
`f_p = 1` everywhere and the fundamental identity reads `∑_{p ↦ q} e_p = 4` — which is exactly how
`#763`'s `sum_ramificationIdxTwo_eq_four` is stated. -/
theorem residueDegreeTwo_eq_one_of_residueDegreeProj_eq_one (h2 : (2 : F) ≠ 0) {p : ProjPoint W}
    (hp : residueDegreeProj W p = 1) : residueDegreeTwo h2 p = 1 :=
  (residueDegreeComap_eq_one_of_residueDegreeProj_eq_one _ _ hp).2

/-- **`[2]∗` is residually trivial at the point at infinity**, on nothing but the nondegeneracy of
`κ(∞)` over `F`.

`comapProjPointTwo h2 none = none` (`MulByTwoPlaceAtInfinity`), so the tower formula degenerates to
`d · f_none = d` with `d = residueDegreeProj W none`; cancelling needs only `d ≠ 0`.  That is
strictly weaker than knowing `d = 1`, and it is what makes this the natural non-vacuity target for
the fibre of `comapProjPointTwo` over `none`: `[2]` fixes infinity, is unramified there
(`ramificationIdxTwo_none`) and, by this, residually trivial there. -/
theorem residueDegreeTwo_none_eq_one_of_ne_zero (h2 : (2 : F) ≠ 0)
    (hd : residueDegreeProj W (none : ProjPoint W) ≠ 0) :
    residueDegreeTwo h2 (none : ProjPoint W) = 1 := by
  have h := residueDegreeProj_mul_residueDegreeTwo h2 (none : ProjPoint W)
  rw [comapProjPointTwo_none h2] at h
  exact (Nat.mul_eq_left hd).1 h

end CoordinateRing

/-! ### Non-vacuity

Every statement above carries `[IsDedekindDomain W.CoordinateRing]` and two hypotheses on `φ`, and
the `[2]∗` section adds `(2 : F) ≠ 0`; `comapProjPoint` and `ramificationIdx` are themselves
extracted from existence statements by choice.  A curve on which the whole chain elaborates with
every instance discharged is therefore committed rather than quoted.  `y² = x³ - x` over `ℚ` has
discriminant `64`, so `IsElliptic` alone gives the Dedekind instance; it is the certificate curve of
`PlacePullback.lean`, `PlaceResidueField.lean` and `MulByTwoPlaceAtInfinity.lean`. -/

section Nonvacuity

/-- The curve `y² = x³ - x` over `ℚ`, of discriminant `64`. -/
private def exampleCurve : Affine ℚ := ⟨0, 0, 0, -1, 0⟩

private instance : exampleCurve.IsElliptic := by
  rw [WeierstrassCurve.isElliptic_iff, isUnit_iff_ne_zero]
  norm_num [exampleCurve, WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈]

private lemma exampleTwoNeZero : (2 : ℚ) ≠ 0 := by norm_num

/-- The tower formula for `[2]∗` on a curve that exists. -/
example (p : ProjPoint exampleCurve) :
    residueDegreeProj exampleCurve (CoordinateRing.comapProjPointTwo (W := exampleCurve)
        exampleTwoNeZero p) * CoordinateRing.residueDegreeTwo (W := exampleCurve) exampleTwoNeZero p
      = residueDegreeProj exampleCurve p :=
  CoordinateRing.residueDegreeProj_mul_residueDegreeTwo exampleTwoNeZero p

/-- On a curve that exists, `[2]∗` is residually trivial at infinity as soon as the residue field
there is finite-dimensional over `ℚ`. -/
example (hd : residueDegreeProj exampleCurve (none : ProjPoint exampleCurve) ≠ 0) :
    CoordinateRing.residueDegreeTwo (W := exampleCurve) exampleTwoNeZero none = 1 :=
  CoordinateRing.residueDegreeTwo_none_eq_one_of_ne_zero exampleTwoNeZero hd

private lemma exampleGenXNeZero : CoordinateRing.genX exampleCurve ≠ 0 :=
  fun h => CoordinateRing.genX_ne (W := exampleCurve) 0 (by rw [h, map_zero])

/-- The unit criterion fires on a function one can name: `x⁻¹` has order `+2` at infinity, so it
lies in the place there and is *not* a unit of it.  The order function at a place is computable on a
named function, which is what the fundamental identity of `#763` needs. -/
example : ¬ IsUnit (⟨(CoordinateRing.genX exampleCurve)⁻¹, (mem_placeOf_iff_divisorProj_nonneg
    (W := exampleCurve) none (inv_ne_zero exampleGenXNeZero)).2 (by
      rw [divisorProj_inv, Finsupp.neg_apply, divisorProj_genX_apply_none]; norm_num)⟩ :
    placeOf exampleCurve none) := by
  rw [isUnit_placeOf_iff]
  rintro ⟨-, h⟩
  rw [divisorProj_inv, Finsupp.neg_apply, divisorProj_genX_apply_none] at h
  norm_num at h

/-- Contraction along the identity automorphism is residually trivial — the `e = f = 1` consistency
check, on a curve that exists. -/
example (p : ProjPoint exampleCurve) :
    residueDegreeComap (φ := ((AlgEquiv.refl :
        exampleCurve.FunctionField ≃ₐ[ℚ] exampleCurve.FunctionField) :
          exampleCurve.FunctionField →+* exampleCurve.FunctionField))
      AlgEquiv.refl.commutes (isIntegralElem_algEquiv AlgEquiv.refl) p = 1 :=
  residueDegreeComap_algEquiv AlgEquiv.refl p

end Nonvacuity

end WeierstrassCurve.Affine
