/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import EllipticCurves.FunctionField.PlacePullback

/-!
# The divisor pullback `[n]∗` and the functoriality `div (f ∘ [n]) = [n]∗ (div f)`

`EllipticCurves.FunctionField.PlacePullback` pulls a *place* back along an `F`-embedding
`φ : F(W) → F(W)` with `F(W)` integral over its image, and transports the order function
**pointwise**:

```lean
divisorProj_comp_apply :
  divisorProj W (φ f) p = ramificationIdx hφF hφint p * divisorProj W f (comapProjPoint hφF hφint p)
```

Its "What is *not* here" section records the one thing that was missing: `[n]∗` as a map of
*divisors*, `pullbackDivisor : (ProjPoint W →₀ ℤ) →+ (ProjPoint W →₀ ℤ)`.  Building it needs each
fibre `(comapProjPoint φ) ⁻¹' {q}` to be finite — otherwise `p ↦ e_p · D (comap p)` has infinite
support and is not a divisor at all.  This file supplies the finiteness, the map, and the
functoriality as a single equation between divisors:

```lean
divisorProj_comp : divisorProj W (φ f) = pullbackDivisor hφF hφint (divisorProj W f)
```

instantiated at `φ = [2]∗` as `divisorProj_mulByTwoEndo`, which is `#414` / `#422` deliverable 1 in
the form those issues state it.

## The fibres are finite, and the proof uses no ring theory

The classical statement is "finitely many places lie above a place of a finite extension", proved
through the integral closure of a valuation ring.  **That route is not available here**: `#422`'s
2026-08-16 correction showed that `[2]∗F[W] ⊄ F[W]`, so the AKLB picture — and with it Mathlib's
`IsDedekindDomain.primesOverFinset` — is about the wrong spectrum.  The obstruction is exactly the
one this rung of the projective divisor theory exists to dissolve.

The argument below sidesteps it, using the pointwise transport itself.  Fix `q : ProjPoint W` and
take a uniformizer there: `exists_divisorProj_eq_one` gives `π ≠ 0` with `divisorProj W π q = 1`.
For any `p` in the fibre over `q` the transport reads

```
divisorProj W (φ π) p = ramificationIdx p * divisorProj W π q = ramificationIdx p ≠ 0
```

by `ramificationIdx_pos`.  So the fibre is contained in the support of the single divisor
`divisorProj W (φ π)`, and a divisor has finite support by construction.  **The finiteness of the
fibre is the finiteness of a `Finsupp`, read backwards.**  Only one function `π` is needed, and it
depends on `q` alone.

## Main results

* `WeierstrassCurve.Affine.finite_comapProjPoint_preimage_singleton` — each fibre is finite;
* `WeierstrassCurve.Affine.finite_comapProjPoint_preimage` — hence the preimage of any finite set;
* **`WeierstrassCurve.Affine.pullbackDivisor`** — `[n]∗` on divisors, as an `AddMonoidHom`, with
  `pullbackDivisor_apply : (pullbackDivisor hφF hφint D) p = e_p * D (comapProjPoint hφF hφint p)`;
* **`WeierstrassCurve.Affine.divisorProj_comp`** — the functoriality, one equation of divisors;
* `WeierstrassCurve.Affine.CoordinateRing.pullbackDivisorTwo` and
  **`WeierstrassCurve.Affine.CoordinateRing.divisorProj_mulByTwoEndo`** — the `[2]` instantiation.

## What is *not* here

* **The degree formula** `∑_{p ↦ q} e_p · deg p = deg φ` (classically `4` for `[2]`).  Fibre
  finiteness makes that sum *statable* for the first time, and nothing more: no lower bound on
  `deg φ` exists in this tree (`PlacePullback` is explicit that `MulByTwoFinite` gives only
  "finite, of degree `≤ 4`"), and no value of `ramificationIdx` is computed anywhere below.
* **Any computation of `ramificationIdx`.**  `pullbackDivisor` is built *from* it and is as abstract
  as it is.  The point at infinity for `[2]` was a separate piece of work and has since been done,
  in `EllipticCurves.FunctionField.MulByTwoPlaceAtInfinity` (`#670`); the resulting computed
  coefficient `pullbackDivisorTwo h2 D none = D none` lives downstream of both files, in
  `EllipticCurves.FunctionField.MulByTwoPullbackDivisor`.  Nothing is computed here at an affine
  place.  ⚠️ Earlier wording added "where `[2]` genuinely ramifies", which is **false** — the
  affine `2`-torsion indices are all `1`
  (`EllipticCurves.FunctionField.MulByTwoFibreInfinity`, `#774`).
* **Surjectivity of `pullbackDivisor`, or injectivity.**  Neither is claimed; `comapProjPoint` is
  not assumed surjective, so `pullbackDivisor` may well kill divisors supported off the image.
* `[3]∗` — the general section applies verbatim once `mulByThreeEndo` is given the two hypotheses of
  `PlacePullback`, and is deliberately not instantiated *here*; `pullbackDivisorThree` and
  `div (f ∘ [3]) = [3]∗ (div f)` are in
  `EllipticCurves.FunctionField.MulByThreePlacePullback`.
* `div g_S = [n]∗(S)` (`#418`), Riemann–Roch, and anything Ward-gated.

## References

* [J. H. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], II.3 (Prop. II.3.6, the
  pullback of divisors under a finite morphism of curves).
* Stichtenoth, *Algebraic Function Fields and Codes*, III.1.
-/

open IsDedekindDomain

namespace WeierstrassCurve.Affine

open CoordinateRing

/-! ### The fibres of the contraction are finite -/

section Fibre

variable {F : Type*} [Field F] {W : Affine F} [IsDedekindDomain W.CoordinateRing]
  {φ : W.FunctionField →+* W.FunctionField}
  (hφF : ∀ c : F, φ (algebraMap F W.FunctionField c) = algebraMap F W.FunctionField c)
  (hφint : ∀ z : W.FunctionField, φ.IsIntegralElem z)

include hφF hφint in
/-- **Each fibre of the contraction is finite** — "finitely many places lie above a place".

The proof is the pointwise transport `divisorProj_comp_apply` run at a uniformizer at `q`: if
`divisorProj W π q = 1` then every `p` above `q` has `divisorProj W (φ π) p = e_p ≠ 0`, so the whole
fibre sits inside the support of the one divisor `divisorProj W (φ π)`. -/
theorem finite_comapProjPoint_preimage_singleton (q : ProjPoint W) :
    ((comapProjPoint hφF hφint) ⁻¹' {q}).Finite := by
  obtain ⟨π, hπ0, hπ⟩ := exists_divisorProj_eq_one q
  have hφπ : φ π ≠ 0 := fun h => hπ0 (φ.injective (by rw [h, map_zero]))
  refine Set.Finite.subset (divisorProj W (φ π)).support.finite_toSet fun p hp => ?_
  have hpq : comapProjPoint hφF hφint p = q := hp
  have h := divisorProj_comp_apply hφF hφint hπ0 p
  rw [hpq, hπ, mul_one] at h
  refine Finsupp.mem_support_iff.2 ?_
  rw [h]
  exact (ramificationIdx_pos hφF hφint p).ne'

include hφF hφint in
/-- The preimage of a finite set of points is finite. -/
theorem finite_comapProjPoint_preimage {s : Set (ProjPoint W)} (hs : s.Finite) :
    ((comapProjPoint hφF hφint) ⁻¹' s).Finite :=
  hs.preimage' fun q _ => finite_comapProjPoint_preimage_singleton hφF hφint q

include hφF hφint in
/-- The support of the pullback formula is finite, for any divisor `D`: it is contained in the
preimage of `D.support`. -/
theorem finite_setOf_ramificationIdx_mul_ne_zero (D : ProjPoint W →₀ ℤ) :
    {p : ProjPoint W |
      ramificationIdx hφF hφint p * D (comapProjPoint hφF hφint p) ≠ 0}.Finite := by
  refine Set.Finite.subset
    (finite_comapProjPoint_preimage hφF hφint D.support.finite_toSet) fun p hp => ?_
  exact Finsupp.mem_support_iff.2 fun h => hp (by rw [h, mul_zero])

end Fibre

/-! ### `[n]∗` on divisors -/

section Pullback

variable {F : Type*} [Field F] {W : Affine F} [IsDedekindDomain W.CoordinateRing]
  {φ : W.FunctionField →+* W.FunctionField}
  (hφF : ∀ c : F, φ (algebraMap F W.FunctionField c) = algebraMap F W.FunctionField c)
  (hφint : ∀ z : W.FunctionField, φ.IsIntegralElem z)

/-- **The pullback of divisors along `φ`.**

```
(φ∗ D) (p) = e_p · D (φ⁻¹ p),
```

an additive homomorphism of the projective divisor group.  It is a genuine `Finsupp` exactly because
the fibres of `comapProjPoint` are finite (`finite_comapProjPoint_preimage`); note that it is *not*
`Finsupp.mapDomain (comapProjPoint …)`, which pushes forward along the contraction — the wrong
direction, and a different divisor. -/
noncomputable def pullbackDivisor : (ProjPoint W →₀ ℤ) →+ (ProjPoint W →₀ ℤ) where
  toFun D := Finsupp.onFinset
    (finite_setOf_ramificationIdx_mul_ne_zero hφF hφint D).toFinset
    (fun p => ramificationIdx hφF hφint p * D (comapProjPoint hφF hφint p))
    fun p hp => Set.Finite.mem_toFinset _ |>.2 hp
  map_zero' := by ext p; simp [Finsupp.onFinset]
  map_add' D E := by ext p; simp [Finsupp.onFinset, mul_add]

@[simp] theorem pullbackDivisor_apply (D : ProjPoint W →₀ ℤ) (p : ProjPoint W) :
    pullbackDivisor hφF hφint D p
      = ramificationIdx hφF hφint p * D (comapProjPoint hφF hφint p) :=
  rfl

include hφF hφint in
/-- **The functoriality of the divisor, as one equation:** `div (f ∘ φ) = φ∗ (div f)`.

This is `PlacePullback`'s pointwise `divisorProj_comp_apply` with both sides read as divisors, and
it is the form `#414` / `#422` state.  Silverman *AEC* II.3, Prop. II.3.6. -/
theorem divisorProj_comp {f : W.FunctionField} (hf : f ≠ 0) :
    divisorProj W (φ f) = pullbackDivisor hφF hφint (divisorProj W f) := by
  ext p
  rw [pullbackDivisor_apply, divisorProj_comp_apply hφF hφint hf p]

end Pullback

/-! ### The `[2]∗` instantiation

`PlacePullback`'s last section discharges both hypotheses for `mulByTwoEndo h2`
(`mulByTwoEndo_algebraMap_base`, `mulByTwoEndo_isIntegralElem`), so everything above applies to it
verbatim.  The naming mirrors the merged `comapProjPointTwo` / `ramificationIdxTwo`. -/

namespace CoordinateRing

variable {F : Type*} [Field F] {W : Affine F} [IsDedekindDomain W.CoordinateRing]

/-- **The pullback of divisors along `[2]∗`.** -/
noncomputable def pullbackDivisorTwo (h2 : (2 : F) ≠ 0) :
    (ProjPoint W →₀ ℤ) →+ (ProjPoint W →₀ ℤ) :=
  pullbackDivisor (mulByTwoEndo_algebraMap_base h2) (mulByTwoEndo_isIntegralElem h2)

@[simp] theorem pullbackDivisorTwo_apply (h2 : (2 : F) ≠ 0) (D : ProjPoint W →₀ ℤ)
    (p : ProjPoint W) :
    pullbackDivisorTwo h2 D p = ramificationIdxTwo h2 p * D (comapProjPointTwo h2 p) :=
  rfl

/-- **`div (f ∘ [2]) = [2]∗ (div f)`** — the divisor-level functoriality of the
multiplication-by-two pullback, as an equation in the projective divisor group.

This is `#414` / `#422` deliverable 1.  `#422`'s 2026-08-16 correction established that the affine
AKLB route to it is false — `[2]∗F[W] ⊄ F[W]` — and named the projective route as the genuine one;
this is that statement, at the end of it. -/
theorem divisorProj_mulByTwoEndo (h2 : (2 : F) ≠ 0) {f : W.FunctionField} (hf : f ≠ 0) :
    divisorProj W (mulByTwoEndo h2 f) = pullbackDivisorTwo h2 (divisorProj W f) :=
  divisorProj_comp _ _ hf

/-- **Finitely many places lie above a place, for `[2]∗`.** -/
theorem finite_comapProjPointTwo_preimage_singleton (h2 : (2 : F) ≠ 0) (q : ProjPoint W) :
    ((comapProjPointTwo (W := W) h2) ⁻¹' {q}).Finite :=
  finite_comapProjPoint_preimage_singleton _ _ q

/-! ### Non-vacuity

Every statement above carries `[IsDedekindDomain W.CoordinateRing]`, and `pullbackDivisor` is built
from `comapProjPoint`, which is a choice.  A curve on which the whole chain elaborates with every
instance discharged is therefore worth committing rather than quoting in a pull-request body.
`y² = x³ - x` over `ℚ` has discriminant `64`, and the Dedekind instance follows from `IsElliptic`
alone — no algebraically closed base field is needed. -/

section Nonvacuity

/-- The curve `y² = x³ - x` over `ℚ`, of discriminant `64`. -/
private def exampleCurve : Affine ℚ := ⟨0, 0, 0, -1, 0⟩

private instance : exampleCurve.IsElliptic := by
  rw [WeierstrassCurve.isElliptic_iff, isUnit_iff_ne_zero]
  norm_num [exampleCurve, WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈]

example : IsDedekindDomain exampleCurve.CoordinateRing := inferInstance

example {f : exampleCurve.FunctionField} (hf : f ≠ 0) :
    divisorProj exampleCurve (mulByTwoEndo (W := exampleCurve) (by norm_num) f)
      = pullbackDivisorTwo (W := exampleCurve) (by norm_num) (divisorProj exampleCurve f) :=
  divisorProj_mulByTwoEndo _ hf

example (q : ProjPoint exampleCurve) :
    ((comapProjPointTwo (W := exampleCurve) (by norm_num)) ⁻¹' {q}).Finite :=
  finite_comapProjPointTwo_preimage_singleton _ q

end Nonvacuity

end CoordinateRing

end WeierstrassCurve.Affine
