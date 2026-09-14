/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import EllipticCurves.Fixtures
import EllipticCurves.FunctionField.FunctionFieldBaseChange
import EllipticCurves.FunctionField.GaloisFunctoriality
import EllipticCurves.FunctionField.MulByNPullback
import Mathlib.FieldTheory.Finite.GaloisField

/-!
# Galois descent for the function field of a Weierstrass curve

Let `W` be a Weierstrass curve over a field `S` and let `F` be a field extension of `S`.  Two
merged layers meet on `F(W⁄F)` and have never been compared:

* `EllipticCurves.FunctionField.FunctionFieldBaseChange` builds the **injective** base-change ring
  homomorphism `functionFieldMap W F : S(W) →+* F(W⁄F)`;
* `EllipticCurves.FunctionField.GaloisFunctionField` builds, for each `σ : F ≃ₐ[S] F`, the
  σ-semilinear automorphism `galoisFunctionField σ` of `F(W⁄F)`.

This file proves that the second recovers the image of the first when `F / S` is Galois:

```
range (functionFieldMap W F) = { z : F(W⁄F) | ∀ σ : F ≃ₐ[S] F, σ⋆ z = z } ,
```

i.e. `F(W⁄F) ^ Gal(F/S) = S(W)`, and the coordinate-ring statement underneath it.

## Why this is wanted

`#962` — `hprin` over a general field — is the last gate on rungs 5–6 over an arbitrary base
field, and its thread carries a ledger of what discharging it would need.  The row
`L(W⁄L)^{Gal(L/F)} = F(W)` is recorded there as belonging to `#692`, and **this file is that
row**: the descent step is supplied below, and no rationality input and no separability statement
is proved here.

⚠️ **No *k*-of-*n* over that ledger is printed here, and that is deliberate.**  A count of a
tracker thread's rows is a figure the thread's own next comment can falsify, and `README.md`'s
`### Reach clauses` puts a sentence that pins its denominator on the **false** branch rather than
the merely-short one as soon as a row it names is not there.  `### Gate-discharge claims` gives the
compliant alternative for a `#NNNN` citation in terms — *"asserting no range asserts nothing
false"*.  The row **name** is the stable address, and the ledger is one click away.

The shape of the intended use is Hilbert 90 at the finite level (Mathlib's
`groupCohomology.isMulCoboundary₁_of_isMulCocycle₁_of_aut_to_units`, which needs
`[FiniteDimensional K L]` and therefore fits the finite half below): a function constructed over a
finite Galois extension `L / S`, rescaled by a constant until it is `Gal(L/S)`-invariant, is then
`S`-rational — and *that* last implication is what had no statement in this tree.

## The argument, in two steps with different hypotheses

⚠️ **The two halves do not carry the same hypotheses, and the difference is not cosmetic.**

* **On the coordinate ring** (`exists_map_eq_of_forall_galoisCoordEndo_eq`), `F[W⁄F]` is free of
  rank two over `F[X]` on `1` and `Y` — Mathlib's `CoordinateRing.basis`, read through
  `exists_smul_basis_eq` and `smul_basis_eq_zero`.  `galoisCoordEndo σ` fixes both basis vectors
  and acts on the `F[X]`-coefficients coefficientwise, so an invariant element has coefficients in
  the fixed field of `Gal(F/S)`, which is `S`.  **No finiteness is used**: the fixed-field input is
  `InfiniteGalois.mem_range_algebraMap_iff_fixed`, which takes `[IsGalois S F]` alone.
* **On the function field** (`exists_functionFieldMap_eq_of_forall_galoisFunctionField_eq`), the
  denominator trick: write `z = a / b` in `F(W⁄F)` with `a, b ∈ F[W⁄F]`, replace `b` by
  `N = ∏ σ, σ(b)`, which is invariant because left translation permutes the group, and let the
  numerator absorb the extra factor.  Both `N` and the new numerator are then invariant elements of
  the coordinate ring, and the first step applies to each.  **This half takes
  `[FiniteDimensional S F]`**, because the product is over `Finset.univ : Finset (F ≃ₐ[S] F)`.

⚠️ **The finiteness is a limitation of this proof and is not claimed to be necessary.**  The
conclusion is true for an infinite Galois extension as well — every element of `F(W⁄F)` is a
quotient of two elements of `F[W⁄F]`, each with finitely many coefficients, hence defined over a
finite subextension — but that reduction is not carried out here and the infinite statement is not
proved.  What *is* measured is that only the second half needs it: the first is stated at
`[IsGalois S F]` and compiles there.

## ⚠️ What this file does not do

* **It does not discharge `hprin`.**  This file supplies the `L(W⁄L)^{Gal(L/F)} = F(W)` row of
  `#962`'s ledger and no other row of it.  No statement below mentions a divisor, a principal
  divisor or a torsion point.
* **It does not supply the divisor-level base change.**  `FunctionFieldBaseChange`'s
  `## Remaining work` says of `divisor` and `divisorProj` that *"they need the behaviour of
  `functionFieldMap` on the places of `F(W)`"*, and that half is untouched: this file transports no
  place, and the Galois action it uses on closed points (`GaloisFunctoriality`'s `galoisPoint`) is
  not mentioned below at all.

## ⚠️ Two spellings of the same curve, and the private bridge that fixes it

`W⁄F` (`WeierstrassCurve.Affine.baseChange`, which `GaloisFunctionField` uses) and
`W.map (algebraMap S F)` (which `CoordinateRing.map` and `functionFieldMap` produce) are
definitionally equal — `rfl` proves it — but `WeierstrassCurve.baseChange` is a **semireducible
`def`**, so they are not *reducibly* equal, and `rw` / `simp`, which elaborate at `instances`
transparency, refuse to rewrite across the boundary with
*"the target expression is not type-correct under the `instances` transparency level"*.

The fix used here is to fix the spelling **once**, in the two private definitions `bcCoord` and
`bcField`, whose stated codomains are `(W⁄F).CoordinateRing` and `(W⁄F).FunctionField` and whose
bodies are the merged maps.  Every bridging lemma about them is then closed by `exact` on its
merged counterpart — `exact` elaborates at default transparency, where the two spellings *are*
interchangeable — and every proof below stays inside one spelling.  The public statements are in
the merged vocabulary (`CoordinateRing.map`, `functionFieldMap`, `galoisCoordEndo`,
`galoisFunctionField`) and mention neither private definition.

## Main statements

* `WeierstrassCurve.Affine.CoordinateRing.map_of` and `…map_root` — Mathlib's
  `CoordinateRing.map` on the two `AdjoinRoot` generators.  They mention no curve beyond the one
  being mapped and no field, and are upstream candidates alongside `CoordinateRing.map_mk`.
* `…galoisCoordEndo_map` and `…galoisFunctionField_functionFieldMap` — the image of base change is
  pointwise Galois-invariant, on the coordinate ring and on the function field.  This is the easy
  inclusion and neither takes any hypothesis on `F / S`.
* `…exists_map_eq_of_forall_galoisCoordEndo_eq` and
  `…mem_range_map_iff_forall_galoisCoordEndo_eq` — the coordinate-ring descent, over **any** Galois
  extension `F / S` and with no finiteness.
* `…exists_functionFieldMap_eq_of_forall_galoisFunctionField_eq`,
  `…mem_range_functionFieldMap_iff_forall_galoisFunctionField_eq` and
  `…range_functionFieldMap_eq` — the function-field descent, over a **finite** Galois extension
  `F / S`.
* `…exists_ne_zero_functionFieldMap_eq_of_forall_galoisFunctionField_eq` — the same over a finite
  Galois extension `F / S`, with the witness produced nonzero, which is the form a rescaling
  argument consumes.

## References

* [J. H. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], II.2, III.8.
* [H. Stichtenoth, *Algebraic function fields and codes*][stichtenoth2009], III.6 (constant field
  extensions).
-/

open Polynomial
open scoped Polynomial.Bivariate

namespace WeierstrassCurve.Affine

namespace CoordinateRing

/-! ### `CoordinateRing.map` on the two generators

Mathlib records `CoordinateRing.map_mk`; the two special cases below are what an
`AdjoinRoot.ringHom_ext` argument needs, and neither is in Mathlib.
-/

section MapGenerators

variable {R S' : Type*} [CommRing R] [CommRing S'] {V : Affine R}

/-- Base change of the coordinate ring sends `R[X]`-constants to `S'[X]`-constants. -/
lemma map_of (f : R →+* S') (p : R[X]) :
    CoordinateRing.map V f (AdjoinRoot.of V.polynomial p)
      = AdjoinRoot.of (V.map f).polynomial (p.map f) := by
  rw [← AdjoinRoot.mk_C, CoordinateRing.map_mk, ← AdjoinRoot.mk_C]
  congr 1
  simp

/-- Base change of the coordinate ring fixes the adjoined root, i.e. the `Y`-generator. -/
lemma map_root (f : R →+* S') :
    CoordinateRing.map V f (AdjoinRoot.root V.polynomial)
      = AdjoinRoot.root (V.map f).polynomial := by
  rw [← AdjoinRoot.mk_X, CoordinateRing.map_mk, ← AdjoinRoot.mk_X]
  congr 1
  simp

end MapGenerators

variable {S : Type*} [Field S] {W : Affine S} {F : Type*} [Field F] [Algebra S F]

/-! ### The spelling bridge

See the module docstring: these two definitions are the merged base-change maps with their
codomains spelled `W⁄F` rather than `W.map (algebraMap S F)`, so that the `GaloisFunctionField`
rewrites below apply to them.  They are private and appear in no statement of this file's API.
-/

variable (W F) in
/-- `CoordinateRing.map W (algebraMap S F)`, with its codomain spelled `(W⁄F).CoordinateRing`. -/
private noncomputable def bcCoord : W.CoordinateRing →+* (W⁄F).CoordinateRing :=
  CoordinateRing.map W (algebraMap S F)

/-- `map_of` in the `W⁄F` spelling. -/
private lemma bcCoord_of (p : S[X]) :
    bcCoord W F (AdjoinRoot.of W.polynomial p)
      = AdjoinRoot.of (W⁄F).polynomial (p.map (algebraMap S F)) :=
  map_of _ _

/-- `map_root` in the `W⁄F` spelling. -/
private lemma bcCoord_root :
    bcCoord W F (AdjoinRoot.root W.polynomial) = AdjoinRoot.root (W⁄F).polynomial :=
  map_root _

/-- `CoordinateRing.map_smul` in the `W⁄F` spelling. -/
private lemma bcCoord_smul (r : S[X]) (a : W.CoordinateRing) :
    bcCoord W F (r • a) = r.map (algebraMap S F) • bcCoord W F a :=
  CoordinateRing.map_smul _ _ _

/-- Base change fixes the second basis vector `Y` of `F[W⁄F]` over `F[X]`. -/
private lemma bcCoord_mk_Y : bcCoord W F (mk W Y) = mk (W⁄F) Y := by
  rw [AdjoinRoot.mk_X, bcCoord_root, AdjoinRoot.mk_X]

variable (W F) in
/-- `functionFieldMap W F`, with its codomain spelled `(W⁄F).FunctionField`. -/
private noncomputable def bcField : W.FunctionField →+* (W⁄F).FunctionField :=
  functionFieldMap W F

/-- `functionFieldMap_algebraMap` in the `W⁄F` spelling. -/
private lemma bcField_genPsi (a : W.CoordinateRing) :
    bcField W F (genPsi W a) = genPsi (W⁄F) (bcCoord W F a) :=
  functionFieldMap_algebraMap W F a

/-- `functionFieldMap_algebraMap_base` in the `W⁄F` spelling. -/
private lemma bcField_algebraMap_base (c : S) :
    bcField W F (algebraMap S W.FunctionField c)
      = algebraMap F (W⁄F).FunctionField (algebraMap S F c) :=
  functionFieldMap_algebraMap_base W F c

/-- `functionFieldMap_genX` in the `W⁄F` spelling. -/
private lemma bcField_genX : bcField W F (genX W) = genX (W⁄F) :=
  functionFieldMap_genX W F

/-- `functionFieldMap_genY` in the `W⁄F` spelling. -/
private lemma bcField_genY : bcField W F (genY W) = genY (W⁄F) :=
  functionFieldMap_genY W F

/-! ### The image of base change is Galois-invariant

The easy inclusion.  `σ⋆` fixes the two coordinate generators and acts by `σ` on the constants, and
`σ` fixes `algebraMap S F` — so the two ring homomorphisms agree on generators, which is all
`AdjoinRoot.ringHom_ext` and `functionField_ringHom_ext` ask for.
-/

/-- `galoisCoordEndo_map` in the `W⁄F` spelling. -/
private lemma galoisCoordEndo_bcCoord (σ : F ≃ₐ[S] F) (a : W.CoordinateRing) :
    galoisCoordEndo σ (bcCoord W F a) = bcCoord W F a := by
  have key : (galoisCoordEndo (W := W) σ).comp (bcCoord W F) = bcCoord W F := by
    refine AdjoinRoot.ringHom_ext (Polynomial.ringHom_ext (fun c => ?_) ?_) ?_
    · simp only [RingHom.comp_apply, bcCoord_of, Polynomial.map_C,
        ← algebraMap_coordinateRing_eq_of, galoisCoordEndo_algebraMap, AlgEquiv.commutes]
    · have hX : AdjoinRoot.of (W⁄F).polynomial X = mk (W⁄F) (C X) := rfl
      simp only [RingHom.comp_apply, bcCoord_of, Polynomial.map_X, hX, galoisCoordEndo_mk_C_X]
    · simp only [RingHom.comp_apply, bcCoord_root, galoisCoordEndo_root]
  exact RingHom.congr_fun key a

/-- **The image of the coordinate-ring base change is Galois-invariant.**  Every `σ : F ≃ₐ[S] F`
fixes `CoordinateRing.map W (algebraMap S F) a` pointwise, because it fixes both coordinate
generators and fixes `algebraMap S F` on constants. -/
theorem galoisCoordEndo_map (σ : F ≃ₐ[S] F) (a : W.CoordinateRing) :
    galoisCoordEndo σ (CoordinateRing.map W (algebraMap S F) a)
      = CoordinateRing.map W (algebraMap S F) a :=
  galoisCoordEndo_bcCoord σ a

/-- `galoisFunctionField_functionFieldMap` in the `W⁄F` spelling. -/
private lemma galoisFunctionField_bcField (σ : F ≃ₐ[S] F) (z : W.FunctionField) :
    galoisFunctionField σ (bcField W F z) = bcField W F z := by
  have key : ((galoisFunctionField (W := W) σ :
      (W⁄F).FunctionField →+* (W⁄F).FunctionField)).comp (bcField W F) = bcField W F := by
    refine functionField_ringHom_ext (fun c => ?_) ?_ ?_
    · rw [RingHom.comp_apply, bcField_algebraMap_base]
      exact (galoisFunctionField_algebraMap σ _).trans (congrArg _ (σ.commutes c))
    · rw [RingHom.comp_apply, bcField_genX]
      exact galoisFunctionField_genX σ
    · rw [RingHom.comp_apply, bcField_genY]
      exact galoisFunctionField_genY σ
  exact RingHom.congr_fun key z

/-- **The image of the function-field base change is Galois-invariant.**  The function-field form
of `galoisCoordEndo_map`, and the easy half of the descent theorem below. -/
theorem galoisFunctionField_functionFieldMap (σ : F ≃ₐ[S] F) (z : W.FunctionField) :
    galoisFunctionField σ (functionFieldMap W F z) = functionFieldMap W F z :=
  galoisFunctionField_bcField σ z

/-! ### Descent on the coordinate ring -/

/-- `σ⋆` is `F[X]`-semilinear: it twists the scalar by `σ` coefficientwise. -/
private lemma galoisCoordEndo_smul (σ : F ≃ₐ[S] F) (p : F[X]) (a : (W⁄F).CoordinateRing) :
    galoisCoordEndo σ (p • a) = p.map (σ : F →+* F) • galoisCoordEndo σ a := by
  rw [CoordinateRing.smul, map_mul, CoordinateRing.smul, AdjoinRoot.mk_C, AdjoinRoot.mk_C,
    galoisCoordEndo_of]

/-- `σ⋆` acts on `F[W⁄F] = F[X] · 1 ⊕ F[X] · Y` by twisting the two coordinates and fixing the two
basis vectors. -/
private lemma galoisCoordEndo_smul_basis (σ : F ≃ₐ[S] F) (p q : F[X]) :
    galoisCoordEndo σ (p • (1 : (W⁄F).CoordinateRing) + q • mk (W⁄F) Y)
      = p.map (σ : F →+* F) • (1 : (W⁄F).CoordinateRing)
        + q.map (σ : F →+* F) • mk (W⁄F) Y := by
  rw [map_add, galoisCoordEndo_smul, galoisCoordEndo_smul, map_one, AdjoinRoot.mk_X,
    galoisCoordEndo_root]

/-- **Galois descent on the coordinate ring**, over a Galois extension `F / S` with no finiteness
hypothesis: an element of `F[W⁄F]` fixed by every `σ : F ≃ₐ[S] F` comes from `S[W]`.

`F[W⁄F]` is free over `F[X]` on `1` and `Y`, both of which `σ⋆` fixes, so invariance says exactly
that the two `F[X]`-coordinates are coefficientwise `Gal(F/S)`-invariant — and the fixed field is
`S` by `InfiniteGalois.mem_range_algebraMap_iff_fixed`, which is where `[IsGalois S F]` is spent
and the only place any hypothesis on `F / S` is used. -/
theorem exists_map_eq_of_forall_galoisCoordEndo_eq [IsGalois S F]
    {a : (W⁄F).CoordinateRing} (ha : ∀ σ : F ≃ₐ[S] F, galoisCoordEndo σ a = a) :
    ∃ b : W.CoordinateRing, CoordinateRing.map W (algebraMap S F) b = a := by
  obtain ⟨p, q, rfl⟩ := exists_smul_basis_eq a
  have hfix : ∀ σ : F ≃ₐ[S] F, p.map (σ : F →+* F) = p ∧ q.map (σ : F →+* F) = q := fun σ => by
    have hσ := ha σ
    rw [galoisCoordEndo_smul_basis] at hσ
    have h0 : (p.map (σ : F →+* F) - p) • (1 : (W⁄F).CoordinateRing)
        + (q.map (σ : F →+* F) - q) • mk (W⁄F) Y = 0 := by
      rw [sub_smul, sub_smul, sub_add_sub_comm, hσ, sub_self]
    obtain ⟨h1, h2⟩ := smul_basis_eq_zero h0
    exact ⟨sub_eq_zero.mp h1, sub_eq_zero.mp h2⟩
  have hlift : ∀ r : F[X], (∀ σ : F ≃ₐ[S] F, r.map (σ : F →+* F) = r) →
      ∃ r₀ : S[X], r₀.map (algebraMap S F) = r := fun r hr => by
    have hc : ∀ n, r.coeff n ∈ Set.range (algebraMap S F) := fun n => by
      refine (InfiniteGalois.mem_range_algebraMap_iff_fixed (r.coeff n)).mpr fun σ => ?_
      have h : (σ : F →+* F) (r.coeff n) = r.coeff n := by
        conv_rhs => rw [← hr σ]
        rw [Polynomial.coeff_map]
      exact h
    exact Polynomial.lifts_iff_coeff_lifts (f := algebraMap S F) (p := r) |>.mpr hc
  obtain ⟨p₀, hp₀⟩ := hlift p fun σ => (hfix σ).1
  obtain ⟨q₀, hq₀⟩ := hlift q fun σ => (hfix σ).2
  refine ⟨p₀ • (1 : W.CoordinateRing) + q₀ • mk W Y, ?_⟩
  change bcCoord W F _ = _
  rw [map_add, bcCoord_smul, bcCoord_smul, map_one, bcCoord_mk_Y, hp₀, hq₀]

/-- **Galois descent on the coordinate ring, as a range membership**, over a Galois extension
`F / S` with no finiteness hypothesis. -/
theorem mem_range_map_iff_forall_galoisCoordEndo_eq [IsGalois S F] (a : (W⁄F).CoordinateRing) :
    a ∈ Set.range (CoordinateRing.map W (algebraMap S F))
      ↔ ∀ σ : F ≃ₐ[S] F, galoisCoordEndo σ a = a :=
  ⟨fun ⟨b, hb⟩ σ => hb ▸ galoisCoordEndo_map σ b, exists_map_eq_of_forall_galoisCoordEndo_eq⟩

/-! ### Descent on the function field -/

/-- `σ⋆` is injective on `F[W⁄F]`, being the underlying map of the ring automorphism
`galoisCoordRing σ`, so it does not kill a nonzero element. -/
private lemma galoisCoordEndo_ne_zero (σ : F ≃ₐ[S] F) {b : (W⁄F).CoordinateRing} (hb : b ≠ 0) :
    galoisCoordEndo σ b ≠ 0 := by
  rw [← galoisCoordRing_apply]
  exact fun h => hb ((galoisCoordRing σ).injective (by rwa [map_zero]))

/-- Invariance of `genPsi a` in `F(W⁄F)` is invariance of `a` in `F[W⁄F]`: `σ⋆` on the function
field is `σ⋆` on the coordinate ring through `genPsi`, which is injective. -/
private lemma forall_galoisCoordEndo_eq_of_forall_galoisFunctionField_eq
    {a : (W⁄F).CoordinateRing} (ha : ∀ σ : F ≃ₐ[S] F, galoisFunctionField σ (genPsi (W⁄F) a)
      = genPsi (W⁄F) a) (σ : F ≃ₐ[S] F) : galoisCoordEndo σ a = a := by
  refine IsFractionRing.injective (W⁄F).CoordinateRing (W⁄F).FunctionField ?_
  rw [← galoisFunctionField_algebraMap_coordRing]
  exact ha σ

/-- **Galois descent on the function field**, over a finite Galois extension `F / S`: an element of
`F(W⁄F)` fixed by every `σ : F ≃ₐ[S] F` comes from `S(W)`.

The denominator trick.  Write `z = a / b` with `a, b ∈ F[W⁄F]`; the product `N = ∏ σ, σ⋆ b` is
invariant because left translation by `τ` permutes `Gal(F/S)`, and `z = (a · N/b) / N` presents `z`
with an invariant denominator.  The numerator is then invariant too — it is `z · N` and both
factors are — so `exists_map_eq_of_forall_galoisCoordEndo_eq` applies to each of the two, and the
quotient of the two preimages is the required element of `S(W)`.

⚠️ `[FiniteDimensional S F]` is used **only** to form that product over `Finset.univ`, and the
conclusion is not claimed to need it; see the module docstring. -/
theorem exists_functionFieldMap_eq_of_forall_galoisFunctionField_eq
    [FiniteDimensional S F] [IsGalois S F] {z : (W⁄F).FunctionField}
    (hz : ∀ σ : F ≃ₐ[S] F, galoisFunctionField σ z = z) :
    ∃ w : W.FunctionField, functionFieldMap W F w = z := by
  classical
  obtain ⟨a, b, hb, hab⟩ := IsFractionRing.div_surjective (A := (W⁄F).CoordinateRing) z
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  set c : (W⁄F).CoordinateRing := ∏ σ ∈ Finset.univ.erase (1 : F ≃ₐ[S] F),
    galoisCoordEndo σ b with hc
  set N : (W⁄F).CoordinateRing := ∏ σ : F ≃ₐ[S] F, galoisCoordEndo σ b with hN
  have hNbc : N = b * c := by
    rw [hN, hc, ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ (1 : F ≃ₐ[S] F)),
      galoisCoordEndo_one, RingHom.id_apply]
  have hc0 : c ≠ 0 := Finset.prod_ne_zero_iff.mpr fun σ _ => galoisCoordEndo_ne_zero σ hb0
  have hN0 : N ≠ 0 := by rw [hNbc]; exact mul_ne_zero hb0 hc0
  have hNfix : ∀ τ : F ≃ₐ[S] F, galoisCoordEndo τ N = N := by
    intro τ
    rw [hN, map_prod]
    refine Fintype.prod_equiv (Equiv.mulLeft τ) _ _ fun σ => ?_
    change galoisCoordEndo τ (galoisCoordEndo σ b) = galoisCoordEndo (τ * σ) b
    rw [galoisCoordEndo_mul, RingHom.comp_apply]
  have hgen : ∀ {x : (W⁄F).CoordinateRing}, x ≠ 0 → genPsi (W⁄F) x ≠ 0 := fun {x} hx h =>
    hx (IsFractionRing.injective (W⁄F).CoordinateRing (W⁄F).FunctionField (by rwa [map_zero]))
  set A : (W⁄F).CoordinateRing := a * c with hA
  have hz' : genPsi (W⁄F) A / genPsi (W⁄F) N = z := by
    rw [hA, hNbc, map_mul, map_mul, mul_div_mul_right _ _ (hgen hc0), hab]
  have hAN : genPsi (W⁄F) A = z * genPsi (W⁄F) N := by
    rw [← hz', div_mul_cancel₀ _ (hgen hN0)]
  have hAfix : ∀ σ : F ≃ₐ[S] F, galoisCoordEndo σ A = A := by
    refine forall_galoisCoordEndo_eq_of_forall_galoisFunctionField_eq fun σ => ?_
    rw [hAN, map_mul, hz σ, galoisFunctionField_algebraMap_coordRing, hNfix σ]
  obtain ⟨A₀, hA₀⟩ := exists_map_eq_of_forall_galoisCoordEndo_eq hAfix
  obtain ⟨N₀, hN₀⟩ := exists_map_eq_of_forall_galoisCoordEndo_eq hNfix
  have hA₀' : bcCoord W F A₀ = A := hA₀
  have hN₀' : bcCoord W F N₀ = N := hN₀
  refine ⟨genPsi W A₀ / genPsi W N₀, ?_⟩
  change bcField W F _ = z
  rw [map_div₀, bcField_genPsi, bcField_genPsi, hA₀', hN₀', hz']

/-- **Galois descent on the function field, as a range membership**, over a finite Galois extension
`F / S`. -/
theorem mem_range_functionFieldMap_iff_forall_galoisFunctionField_eq
    [FiniteDimensional S F] [IsGalois S F] (z : (W⁄F).FunctionField) :
    z ∈ Set.range (functionFieldMap W F)
      ↔ ∀ σ : F ≃ₐ[S] F, galoisFunctionField σ z = z :=
  ⟨fun ⟨w, hw⟩ σ => hw ▸ galoisFunctionField_functionFieldMap σ w,
    exists_functionFieldMap_eq_of_forall_galoisFunctionField_eq⟩

/-- **`F(W⁄F) ^ Gal(F/S) = S(W)`**, over a finite Galois extension `F / S`: the image of the
base-change map is exactly the set of Galois-invariant elements. -/
theorem range_functionFieldMap_eq [FiniteDimensional S F] [IsGalois S F] :
    Set.range (functionFieldMap W F)
      = {z : (W⁄F).FunctionField | ∀ σ : F ≃ₐ[S] F, galoisFunctionField σ z = z} :=
  Set.ext fun z => mem_range_functionFieldMap_iff_forall_galoisFunctionField_eq z

/-- **A nonzero invariant function descends to a nonzero function**, over a finite Galois extension
`F / S`.  The form a rescaling argument consumes: the witness of
`exists_functionFieldMap_eq_of_forall_galoisFunctionField_eq` is nonzero whenever `z` is, because
base change is a ring homomorphism. -/
theorem exists_ne_zero_functionFieldMap_eq_of_forall_galoisFunctionField_eq
    [FiniteDimensional S F] [IsGalois S F] {z : (W⁄F).FunctionField} (hz0 : z ≠ 0)
    (hz : ∀ σ : F ≃ₐ[S] F, galoisFunctionField σ z = z) :
    ∃ w : W.FunctionField, w ≠ 0 ∧ functionFieldMap W F w = z := by
  obtain ⟨w, hw⟩ := exists_functionFieldMap_eq_of_forall_galoisFunctionField_eq hz
  exact ⟨w, fun h => hz0 (by rw [← hw, h]; exact map_zero _), hw⟩

/-! ### Non-vacuity

⚠️ **No certificate curve and no certificate field is defined here.**  The curve is
`EllipticCurves.Fixture.y2AddYEqX3` at `ZMod 2` and the extension is Mathlib's `GaloisField`, so
this section adds no row to the census of locally-defined fixtures that
`EllipticCurves.Fixtures` keeps.  No statement in this file takes `[W.IsElliptic]`, so none of that
fixture's instances is needed either.

The point of the certificate is that the Galois group is **not** trivial: `𝔽₄ / 𝔽₂` is Galois of
degree `2`, so `∀ σ : Gal(𝔽₄/𝔽₂), σ⋆ z = z` is a condition on two automorphisms rather than on one.
-/

section Nonvacuity

open EllipticCurves.Fixture

/-- The certificate extension `𝔽₄ / 𝔽₂` has a Galois group with **two** elements. -/
example : Nat.card (GaloisField 2 2 ≃ₐ[ZMod 2] GaloisField 2 2) = 2 := by
  rw [IsGalois.card_aut_eq_finrank, GaloisField.finrank 2 two_ne_zero]

/-- `range_functionFieldMap_eq` on a concrete curve over a concrete finite Galois extension. -/
example :
    Set.range (functionFieldMap (y2AddYEqX3 (ZMod 2)) (GaloisField 2 2))
      = {z : ((y2AddYEqX3 (ZMod 2))⁄(GaloisField 2 2)).FunctionField |
          ∀ σ : GaloisField 2 2 ≃ₐ[ZMod 2] GaloisField 2 2, galoisFunctionField σ z = z} :=
  range_functionFieldMap_eq

end Nonvacuity

end CoordinateRing

end WeierstrassCurve.Affine
