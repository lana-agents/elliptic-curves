/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import EllipticCurves.FunctionField.DivisorTransport
import EllipticCurves.FunctionField.HeightOneSpectrumFunctor

/-!
# The Galois action is an action: functoriality in `σ` of the σ-semilinear automorphisms

`EllipticCurves.FunctionField.GaloisFunctionField` (`#455`) attaches, to a **fixed** base-field
automorphism `σ : F ≃ₐ[S] F`, the σ-semilinear ring automorphisms

* `galoisCoordEndo σ` / `galoisCoordRing σ` of the coordinate ring `F[W⁄F]`, and
* `galoisFunctionField σ` of the function field `F(W⁄F)`,

and `EllipticCurves.FunctionField.DivisorTransport` (`#630`) transports `ord` and `divisor` along
them. Every statement in that development is about one `σ` at a time. **Nothing in it says the
constructions fit together as `σ` varies** — there is no `galoisCoordEndo (σ * τ) = …` and no
`galoisCoordEndo 1 = id`, so, strictly, "the Galois action" is so far a family of unrelated
automorphisms indexed by `σ` rather than an action of the group `F ≃ₐ[S] F`.

This file supplies the missing laws, at each of the four levels the development uses:

| level | object | functoriality |
| --- | --- | --- |
| coordinate ring | `galoisCoordAut` | `(F ≃ₐ[S] F) →* RingAut F[W⁄F]` |
| function field | `galoisFunctionFieldAut` | `(F ≃ₐ[S] F) →* RingAut F(W⁄F)` |
| closed points | `galoisPoint` | `(F ≃ₐ[S] F) →* Equiv.Perm (HeightOneSpectrum F[W⁄F])` |
| divisors | `galoisDivisor` | `galoisDivisor (σ * τ) = (galoisDivisor τ).trans (galoisDivisor σ)` |

No new mathematics about curves is proved here; an existing construction is shown to be the
algebraic object it was always meant to be.

## What this buys

* `divisor` and `ord` become **equivariant maps for a group action**, not merely compatible with
  each individual `σ` — `divisor_galoisFunctionField_aut` and `ord_galoisFunctionField_aut`.
* `ord_galoisFunctionField_apply` (`#630`) has to be stated with
  `(mapEquiv (galoisCoordRing σ)).symm` because no inverse operator was available.
  `ord_galoisFunctionField_apply_inv` states it with `galoisPoint σ⁻¹`, which is the same thing by
  `map_inv` and reads as the transport law it is.
* **The divisor transport hypothesis of `#632` chains**: `divisor_transport_trans` composes a
  σ-transport and a τ-transport into a `(τ * σ)`-transport. This is what will make the rung-5
  family of `n`-th roots `{g_{σS}}_σ` coherent rather than a set of unrelated choices, and it is
  not statable at all without `galoisDivisor_mul`.
* `#456` deliverable 2's residual gate includes `[n]∗(σS) = σ_*([n]∗ S)` — a statement about `σ_*`
  as an operator on divisors. Today `σ_*` is spelled inline as
  `Finsupp.equivMapDomain (mapEquiv (galoisCoordRing σ))` with no laws attached; `galoisDivisor`
  names it and gives it the two laws that make it composable.

## Scope

Rung-4/5-independent and Ward-independent. **`#456` deliverable 2 stays open**: its remaining
inputs are `divisor g_S = [n]∗(S)` (rung 5, `#418`, gated on `#421`/`#422`) and the σ-equivariance
of `[n]∗`, which cannot even be written until `[n]∗` on divisors exists (`#414`). **The translation
slot is untouched**: `translateEndo` is not `IsFractionRing.ringEquivOfRingEquiv e` for any ring
automorphism `e` of `F[W⁄F]` — it moves the points at infinity — so neither `#630`'s transport nor
anything here reaches the divisor-pullback-under-translation formula that `#465` needs.

No `MulAction`/`DistribMulAction` instance is registered. A global action instance on a type as
heavily used as `F[W⁄F]` is a diamond risk for no gain; `MonoidHom`s and explicit lemmas keep every
call site's instance search unchanged.

## Implementation notes

* `galoisPoint` is defined **directly by its `MonoidHom` fields**, not as
  `mapAut.comp galoisCoordAut`, so that `galoisPoint_apply` holds by `rfl` and the `#630` lemmas
  can be `exact`ed against it. The composite description is recorded separately as
  `galoisPoint_eq_comp`. Defining it as the composite makes `galoisPoint_apply` fail to be
  definitional, which breaks every downstream `exact`.
* `galoisDivisor` is an `AddEquiv`-valued function with two explicit laws rather than a `MonoidHom`
  into `AddAut`: Mathlib gives `AddAut M` an *additive* group structure, so a `MonoidHom` into
  `AddAut D` does not elaborate.
* `Equiv.Perm`, `RingAut` and `AddAut` all multiply/add by composition (`g * h = h.trans g`), which
  is why the `mul` lemmas below come out with their arguments swapped relative to `trans`.

## References

* [J. H. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], II.3, III.8.
-/

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum Polynomial

namespace WeierstrassCurve.Affine.CoordinateRing

open WeierstrassCurve.Affine

variable {S F : Type*} [Field S] [Field F] [Algebra S F] {W : Affine S}

/-! ### The coordinate ring -/

/-- The identity automorphism of `F` induces the identity of `F[W⁄F]`. -/
lemma galoisCoordEndo_one :
    galoisCoordEndo (W := W) (1 : F ≃ₐ[S] F) = RingHom.id (W⁄F).CoordinateRing := by
  refine AdjoinRoot.ringHom_ext (Polynomial.ringHom_ext (fun c => ?_) ?_) ?_
  · simp only [RingHom.comp_apply, RingHom.id_apply, ← algebraMap_coordinateRing_eq_of,
      galoisCoordEndo_algebraMap, AlgEquiv.one_apply]
  · change galoisCoordEndo (1 : F ≃ₐ[S] F) (AdjoinRoot.of (W⁄F).polynomial X)
      = RingHom.id _ (AdjoinRoot.of (W⁄F).polynomial X)
    have hX : AdjoinRoot.of (W⁄F).polynomial X = mk (W⁄F) (C X) := rfl
    rw [hX, galoisCoordEndo_mk_C_X, RingHom.id_apply]
  · rw [galoisCoordEndo_root, RingHom.id_apply]

/-- **Composition law on the coordinate ring**: `galoisCoordEndo` is multiplicative in `σ`.

Proved exactly as `galoisCoordEndo_comp`, by checking the two generators and the `F`-constants;
the constants are where the composition of `σ` and `τ` actually happens (`AlgEquiv.mul_apply`),
since both generators are fixed. -/
lemma galoisCoordEndo_mul (σ τ : F ≃ₐ[S] F) :
    galoisCoordEndo (W := W) (σ * τ) = (galoisCoordEndo σ).comp (galoisCoordEndo τ) := by
  refine AdjoinRoot.ringHom_ext (Polynomial.ringHom_ext (fun c => ?_) ?_) ?_
  · simp only [RingHom.comp_apply, ← algebraMap_coordinateRing_eq_of,
      galoisCoordEndo_algebraMap, AlgEquiv.mul_apply]
  · change galoisCoordEndo (σ * τ) (AdjoinRoot.of (W⁄F).polynomial X)
      = galoisCoordEndo σ (galoisCoordEndo τ (AdjoinRoot.of (W⁄F).polynomial X))
    have hX : AdjoinRoot.of (W⁄F).polynomial X = mk (W⁄F) (C X) := rfl
    rw [hX, galoisCoordEndo_mk_C_X, galoisCoordEndo_mk_C_X, galoisCoordEndo_mk_C_X]
  · rw [RingHom.comp_apply, galoisCoordEndo_root, galoisCoordEndo_root, galoisCoordEndo_root]

lemma galoisCoordRing_one : galoisCoordRing (W := W) (1 : F ≃ₐ[S] F) = 1 :=
  RingEquiv.ext fun a => by
    rw [galoisCoordRing_apply, galoisCoordEndo_one, RingHom.id_apply]; rfl

lemma galoisCoordRing_mul (σ τ : F ≃ₐ[S] F) :
    galoisCoordRing (W := W) (σ * τ) = galoisCoordRing σ * galoisCoordRing τ :=
  RingEquiv.ext fun a => by
    rw [galoisCoordRing_apply, galoisCoordEndo_mul, RingHom.comp_apply]; rfl

/-- **The Galois group acts on the coordinate ring by ring automorphisms.** -/
noncomputable def galoisCoordAut : (F ≃ₐ[S] F) →* RingAut (W⁄F).CoordinateRing where
  toFun := galoisCoordRing
  map_one' := galoisCoordRing_one
  map_mul' := galoisCoordRing_mul

@[simp]
lemma galoisCoordAut_apply (σ : F ≃ₐ[S] F) (a : (W⁄F).CoordinateRing) :
    galoisCoordAut σ a = galoisCoordEndo σ a := rfl

/-! ### The function field -/

/-- **Composition law on the function field.** Checked on `r / s` with `r, s` in the coordinate
ring, using `IsFractionRing.div_surjective`; the coordinate-ring composition law then does the
work. -/
lemma galoisFunctionField_mul_apply (σ τ : F ≃ₐ[S] F) (f : (W⁄F).FunctionField) :
    galoisFunctionField (σ * τ) f = galoisFunctionField σ (galoisFunctionField τ f) := by
  obtain ⟨r, s, -, rfl⟩ := IsFractionRing.div_surjective (A := (W⁄F).CoordinateRing) f
  simp only [map_div₀, galoisFunctionField_algebraMap_coordRing, galoisCoordEndo_mul,
    RingHom.comp_apply]

lemma galoisFunctionField_one_apply (f : (W⁄F).FunctionField) :
    galoisFunctionField (W := W) (1 : F ≃ₐ[S] F) f = f := by
  obtain ⟨r, s, -, rfl⟩ := IsFractionRing.div_surjective (A := (W⁄F).CoordinateRing) f
  simp only [map_div₀, galoisFunctionField_algebraMap_coordRing, galoisCoordEndo_one,
    RingHom.id_apply]

/-- **The Galois group acts on the function field by ring automorphisms.** -/
noncomputable def galoisFunctionFieldAut : (F ≃ₐ[S] F) →* RingAut (W⁄F).FunctionField where
  toFun := galoisFunctionField
  map_one' := RingEquiv.ext galoisFunctionField_one_apply
  map_mul' σ τ := RingEquiv.ext (galoisFunctionField_mul_apply σ τ)

@[simp]
lemma galoisFunctionFieldAut_apply (σ : F ≃ₐ[S] F) (f : (W⁄F).FunctionField) :
    galoisFunctionFieldAut σ f = galoisFunctionField σ f := rfl

/-! ### Closed points and divisors

Neither the action on closed points nor the action on divisors needs the coordinate ring to be a
Dedekind domain: `HeightOneSpectrum.mapEquiv` is pure ideal theory. Only `ord` and `divisor`, in
the next section, carry `[IsDedekindDomain (W⁄F).CoordinateRing]`.
-/

/-- **The Galois group acts on the affine closed points of `W⁄F`.**

The permutation attached to `σ` is the one `#630` transports `ord` along; the content here is that
these permutations compose, so that the closed points of the affine chart form a genuine
`Gal(F/S)`-set. -/
noncomputable def galoisPoint :
    (F ≃ₐ[S] F) →* Equiv.Perm (HeightOneSpectrum (W⁄F).CoordinateRing) where
  toFun σ := mapEquiv (galoisCoordRing σ)
  map_one' := by rw [galoisCoordRing_one]; exact mapEquiv_refl
  map_mul' σ τ := by rw [galoisCoordRing_mul]; exact mapEquiv_trans _ _

@[simp]
lemma galoisPoint_apply (σ : F ≃ₐ[S] F) (v : HeightOneSpectrum (W⁄F).CoordinateRing) :
    galoisPoint σ v = mapEquiv (galoisCoordRing σ) v := rfl

/-- `galoisPoint` is the composite of the action on the coordinate ring with the action of ring
automorphisms on closed points. It is *defined* by its fields rather than as this composite so that
`galoisPoint_apply` is definitional. -/
lemma galoisPoint_eq_comp :
    galoisPoint (W := W) (S := S) (F := F) = mapAut.comp galoisCoordAut :=
  MonoidHom.ext fun _ => rfl

/-- **The Galois group acts on divisors**, by permuting the closed points in the support.

This is the operator written `σ_*` in the docstrings of `#630` and `#632`, where it appears
unnamed as `Finsupp.equivMapDomain (mapEquiv (galoisCoordRing σ))`. Naming it, together with
`galoisDivisor_one` / `galoisDivisor_mul`, is what allows divisor transports to be composed. -/
noncomputable def galoisDivisor (σ : F ≃ₐ[S] F) :
    (HeightOneSpectrum (W⁄F).CoordinateRing →₀ ℤ)
      ≃+ (HeightOneSpectrum (W⁄F).CoordinateRing →₀ ℤ) :=
  Finsupp.domCongr (galoisPoint σ)

@[simp]
lemma galoisDivisor_apply (σ : F ≃ₐ[S] F)
    (D : HeightOneSpectrum (W⁄F).CoordinateRing →₀ ℤ) :
    galoisDivisor σ D = D.equivMapDomain (galoisPoint σ) := rfl

lemma galoisDivisor_one : galoisDivisor (W := W) (1 : F ≃ₐ[S] F) = AddEquiv.refl _ := by
  have h : galoisPoint (W := W) (1 : F ≃ₐ[S] F) = Equiv.refl _ := map_one _
  rw [galoisDivisor, h]
  exact Finsupp.domCongr_refl

/-- The divisor action is multiplicative in `σ`. The `trans` order is reversed because
`Equiv.Perm` multiplies by composition. -/
lemma galoisDivisor_mul (σ τ : F ≃ₐ[S] F) :
    galoisDivisor (W := W) (σ * τ) = (galoisDivisor τ).trans (galoisDivisor σ) := by
  have h : galoisPoint (W := W) (σ * τ) = (galoisPoint τ).trans (galoisPoint σ) := by
    rw [map_mul]; rfl
  rw [galoisDivisor, galoisDivisor, galoisDivisor, h]
  exact (Finsupp.domCongr_trans (galoisPoint τ) (galoisPoint σ)).symm

/-! ### `ord` and `divisor` as equivariant maps -/

section Dedekind

variable [IsDedekindDomain (W⁄F).CoordinateRing]

/-- **`divisor` is `Gal(F/S)`-equivariant**: `div (σ⋆ f) = σ · div f`, now with `σ ↦ σ ·` a genuine
action (`galoisDivisor_one`, `galoisDivisor_mul`). This is `divisor_galoisFunctionField` (`#630`)
restated in terms of the named operator. -/
theorem divisor_galoisFunctionField_aut (σ : F ≃ₐ[S] F) (f : (W⁄F).FunctionField) :
    divisor (W⁄F) (galoisFunctionField σ f) = galoisDivisor σ (divisor (W⁄F) f) :=
  divisor_galoisFunctionField σ f

/-- **`ord` is `Gal(F/S)`-equivariant**: the order of `σ⋆ f` at `σ · v` is the order of `f` at `v`.
This is `ord_galoisFunctionField` (`#630`) restated in terms of the group action. -/
theorem ord_galoisFunctionField_aut (σ : F ≃ₐ[S] F)
    (v : HeightOneSpectrum (W⁄F).CoordinateRing) (f : (W⁄F).FunctionField) :
    ord (galoisPoint σ v) (galoisFunctionField σ f) = ord v f :=
  ord_galoisFunctionField σ v f

/-- The pointwise form of equivariance, with the inverse group element in place of the inverse
permutation: `ord w (σ⋆ f) = ord (σ⁻¹ · w) f`.

`ord_galoisFunctionField_apply` (`#630`) has to say `(mapEquiv (galoisCoordRing σ)).symm` because
no inverse operator was available; with `galoisPoint` a `MonoidHom`, `map_inv` identifies the two
and the statement reads as the transport law it is. -/
theorem ord_galoisFunctionField_apply_inv (σ : F ≃ₐ[S] F)
    (w : HeightOneSpectrum (W⁄F).CoordinateRing) (f : (W⁄F).FunctionField) :
    ord w (galoisFunctionField σ f) = ord (galoisPoint σ⁻¹ w) f := by
  rw [ord_galoisFunctionField_apply, map_inv]
  rfl

/-- **Divisor transports compose.**

If `g'` carries the σ-transported divisor of `g`, and `g''` the τ-transported divisor of `g'`, then
`g''` carries the `(τ * σ)`-transported divisor of `g`. This is the hypothesis shape of
`#632`'s `exists_unit_galoisFunctionField_of_divisor_eq` and its consumers, so this lemma says the
`#632` hypothesis is closed under composition of Galois elements — which is what makes a family of
`n`-th roots indexed by the Galois group coherent rather than a set of unrelated choices.

It is not statable without `galoisDivisor_mul`. -/
theorem divisor_transport_trans {g g' g'' : (W⁄F).FunctionField} {σ τ : F ≃ₐ[S] F}
    (h₁ : divisor (W⁄F) g' = galoisDivisor σ (divisor (W⁄F) g))
    (h₂ : divisor (W⁄F) g'' = galoisDivisor τ (divisor (W⁄F) g')) :
    divisor (W⁄F) g'' = galoisDivisor (τ * σ) (divisor (W⁄F) g) := by
  rw [h₂, h₁, galoisDivisor_mul]
  rfl

end Dedekind

end WeierstrassCurve.Affine.CoordinateRing
