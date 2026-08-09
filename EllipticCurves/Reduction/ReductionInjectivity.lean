/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import EllipticCurves.Reduction.ReductionHom
import EllipticCurves.Reduction.Torsion

/-!
# Reduction is injective on prime-to-`p` torsion (issue #346, closes #243)

Let `R` be a **complete** discrete valuation ring with fraction field `K = Frac R`, residue field
`k` and residue characteristic `p`, and let `W : WeierstrassCurve K` be an elliptic curve with good
reduction.  This file assembles the headline statement of Silverman AEC VII.3 Proposition 3.1(a):
for `m` prime to `p` the reduction map on points is **injective on the `m`-torsion** `E(K)[m]`.

The proof combines two facts already on `main`:

* the reduction map is a group homomorphism `redHom : (W⁄K).Point →+ (reduction R W).Point`
  (`WeierstrassCurve.redHom`, issue #360/#383), and
* the kernel of reduction has no nontrivial prime-to-`p` torsion
  (`WeierstrassCurve.eq_zero_of_redPt_eq_zero_of_isUnit_nsmul`, issue #346 partial / `Torsion`).

Given `m • P = 0`, `m • Q = 0` and `redPt P = redPt Q`, the difference `P - Q` is `m`-torsion and
reduces to `0` (`redPt (P - Q) = redPt P - redPt Q = 0`, using additivity), hence `P - Q = 0` by the
torsion-freeness of the kernel; so `P = Q`.

## Main results

* `WeierstrassCurve.reduction_injOn_torsion` — `Set.InjOn (redPt R W) {P | m • P = 0}` for
  `IsUnit (m : R)` (e.g. `m` prime to `p`): the reduction map is injective on `E(K)[m]`.
* `WeierstrassCurve.eq_of_redPt_eq_of_isUnit_nsmul` — the pointwise phrasing: two `m`-torsion points
  with the same reduction are equal.

## References

* [J. H. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], VII.3 Prop 3.1(a), VII.2.
-/

open IsDiscreteValuationRing

namespace WeierstrassCurve

variable (R : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
variable {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
variable [IsAdicComplete (maximalIdeal R).asIdeal R]
variable (W : WeierstrassCurve K) [HasGoodReduction R W] [W.IsElliptic]

open Classical in
/-- **Reduction is injective on the `m`-torsion (Silverman AEC VII.3 Prop 3.1(a)).**  When
`(m : R)` is a unit — in particular for `m` coprime to the residue characteristic `p`, as `R` is
local with maximal ideal `𝔪` — two `m`-torsion points `P, Q` of `E(K)` with the same reduction are
equal.  The difference `P - Q` reduces to `0` (`redPt` is a homomorphism, `redHom`) and is
`m`-torsion, hence lies in `E₁(K)[m] = 0` by
`eq_zero_of_redPt_eq_zero_of_isUnit_nsmul`. -/
theorem eq_of_redPt_eq_of_isUnit_nsmul {m : ℕ} (hm : IsUnit (m : R))
    {P Q : W.toAffine.Point} (hP : m • P = 0) (hQ : m • Q = 0)
    (hPQ : redPt R W P = redPt R W Q) : P = Q := by
  -- `redPt` is additive, so the difference reduces to `0`
  have hd : redPt R W (P - Q) = 0 := by
    rw [← redHom_apply, map_sub, redHom_apply, redHom_apply, hPQ, sub_self]
  -- the difference is `m`-torsion
  have hm0 : m • (P - Q) = 0 := by rw [smul_sub, hP, hQ, sub_self]
  -- so it vanishes by torsion-freeness of the kernel of reduction
  exact sub_eq_zero.mp (eq_zero_of_redPt_eq_zero_of_isUnit_nsmul R W hm hd hm0)

open Classical in
/-- **The reduction map is injective on `E(K)[m]` for `m` prime to `p`.**  Packaged as `Set.InjOn`
over the `m`-torsion subset `{P | m • P = 0}`.  This is the #243 deliverable and the analytic heart
of the Néron–Ogg–Shafarevich criterion. -/
theorem reduction_injOn_torsion {m : ℕ} (hm : IsUnit (m : R)) :
    Set.InjOn (redPt R W) {P : W.toAffine.Point | m • P = 0} := by
  intro P hP Q hQ hPQ
  exact eq_of_redPt_eq_of_isUnit_nsmul R W hm hP hQ hPQ

end WeierstrassCurve
