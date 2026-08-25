/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import EllipticCurves.FunctionField.MulByThreeDegree
import EllipticCurves.FunctionField.MulByTwoPlaceAtInfinity
import EllipticCurves.FunctionField.PullbackDivisor

/-!
# The `[3]∗` place pullback, and the point at infinity

`EllipticCurves.FunctionField.PlacePullback` contracts places of `F(W)` along a non-invertible
`F`-embedding `φ` and produces a ramification index; `EllipticCurves.FunctionField.PullbackDivisor`
assembles the two into `φ∗` on the projective divisor group.  Both are stated for an abstract `φ`
subject to two hypotheses, both instantiate them at `mulByTwoEndo`, and both say in their own
docstrings that `[3]∗` is *available and deliberately deferred*.  This file takes the deferral up:

```
comapProjPointThree h2 h3 : ProjPoint W → ProjPoint W        the contraction of a place along [3]∗
ramificationIdxThree h2 h3 p                                 its ramification index, positive
pullbackDivisorThree h2 h3 : (ProjPoint W →₀ ℤ) →+ (ProjPoint W →₀ ℤ)
divisorProj_mulByThreeEndo :  div (f ∘ [3]) = [3]∗ (div f)
```

and then computes both factors at the one place every consumer needs first:

```
comapProjPointThree h2 h3 none = none            [3] fixes the point at infinity
ramificationIdxThree h2 h3 none = 1              and is unramified there.
```

## The two hypotheses were already discharged

`PlacePullback`'s general sections take

```lean
(hφF   : ∀ c : F, φ (algebraMap F W.FunctionField c) = algebraMap F W.FunctionField c)
(hφint : ∀ z : W.FunctionField, φ.IsIntegralElem z)
```

and for `mulByThreeEndo h2 h3` the first is the merged `mulByThreeEndo_algebraMap_base`
(`MulByThreeFinite`).  The second is `mulByThreeEndo_isIntegralElem` below, four lines off the
merged `module_finite_mulByThreeRange` (`MulByThreeExtensionFinite`): module-finite implies
integral, and `RingHom.isIntegralElem_of_isIntegral_range` converts integrality over the range
subring into integrality with respect to the endomorphism.  That is the whole gap, and it is why
three merged docstrings were right to call the `[3]∗` instantiation *verbatim*.

## Why this file imports the `[2]` one

`MulByTwoPlaceAtInfinity` proves three lemmas — `genPsi_mk_C_eq_eval_map`,
`eval_map_genX_ne_zero` and `ordInfty_eval_map_genX` — which are **`[2]`-free**: they say that a
univariate polynomial evaluated at the generic `x`-coordinate is a coordinate-ring class, that a
nonzero one does not vanish there, and that its order at infinity is `-2 · deg`.  Nothing in any of
them mentions doubling.  They are consumed here unchanged rather than re-proved, which is why the
`[3]` file imports the `[2]` file and not the other way round.

⚠️ Moving them to an earlier module would be tidier and is **deliberately not done**: it edits a
merged file for no mathematical gain.  `EllipticCurves.Torsion.TriplingCoords` and
`EllipticCurves.Torsion.DoublingCoords` each declined the same trade, and the reason is the same
one.

## Where `h3` stops being inherited

`mulByThreeEndo` carries `h3 : (3 : F) ≠ 0` in its signature, so it is tempting to read the `h3` in
`ordInfty_mulByThreeEndo_genX` as bookkeeping.  It is not: that computation needs
`natDegree (W.ΨSq 3) = 8` **exactly**, and Mathlib's `natDegree_ΨSq` is conditional on
`((3 : ℤ) : F) ≠ 0`.  A `≤` bound is not enough, because the answer is the *difference*
`-18 - (-16)` of two pole orders and a slack in either one destroys it.

⚠️ This is the `n = 3` twin of `MulByTwoPlaceAtInfinity`'s load-bearing `h2`, but **not** for the
same reason.  There the obstruction is arithmetic in the coefficients: `Ψ₂Sq = 4X³ + …` has leading
coefficient `4`, and `natDegree_Ψ₂Sq` asks for `(4 : F) ≠ 0`.  Here it is a cast: `natDegree_ΨSq` is
stated for a general `n : ℤ` and asks for the image of `n` in `F`.  The `Φ` side needs nothing at
all — `natDegree_Φ` holds over any nontrivial ring.

## Main results

* `WeierstrassCurve.Affine.CoordinateRing.mulByThreeEndo_isIntegralElem` — the integrality
  hypothesis of `PlacePullback`, for `[3]∗`.
* `WeierstrassCurve.Affine.CoordinateRing.ordInfty_mulByThreeEndo_genX` —
  `ordInfty W ([3]∗ x) = -2`: tripling leaves the generic `x`-coordinate a double pole at infinity.
  This one degree computation carries the second half of the file.
* `WeierstrassCurve.Affine.CoordinateRing.comapProjPointThree`,
  `ramificationIdxThree`, `ramificationIdxThree_pos`, `divisorProj_mulByThreeEndo_apply` — the
  `PlacePullback` instantiation.
* **`WeierstrassCurve.Affine.CoordinateRing.comapProjPointThree_none`** and
  **`ramificationIdxThree_none`** — `[3]` fixes the point at infinity and is unramified there,
  with the payoffs `divisorProj_mulByThreeEndo_apply_none` and `ordInfty_mulByThreeEndo`.
* **`WeierstrassCurve.Affine.CoordinateRing.pullbackDivisorThree`** and
  **`divisorProj_mulByThreeEndo`** — `div (f ∘ [3]) = [3]∗ (div f)`, the `n = 3` form of what
  `#414` / `#422` state at `n = 2`; plus `pullbackDivisorThree_apply_none`, the first computed
  coefficient of a `[3]`-pulled-back divisor.
* `dvd_divisorProj_mulByThreeEndo` and `dvd_divisorProj_mulByThreeEndo_of_torsion` — the
  `n`-divisibility corollary in the shape `#422` asks for.

## Scope

⚠️ **No affine index is computed.**  Nothing below says anything about `ramificationIdxThree` at a
place other than infinity.  At `n = 2` that is the work of
`EllipticCurves.FunctionField.MulByTwoFibreInfinity` and
`EllipticCurves.FunctionField.MulByTwoFibreAffine`; the `n = 3` analogue of both is
`EllipticCurves.FunctionField.MulByThreeFibre`, which consumes this file.

⚠️ **This is not the degree formula.**  `∑_{p ↦ q} e_p · deg p = 9` needs the residue-degree
machinery on top of a fundamental identity, and nothing here approaches either.  The identity is
`EllipticCurves.FunctionField.MulByThreeRamification`, which instantiates
`EllipticCurves.FunctionField.PlaceRamificationInertia` (`#763`) at `[3]∗` on top of this file and
proves the **unweighted** `∑_{p ↦ q} e_p = 9`.  ⚠️ **The sentence that used to end this paragraph
has been paid** — it read *"The weighted form still has no `n = 3` case: `residueDegreeThree` does
not exist, so `sum_ramificationIdxTwo_mul_residueDegreeTwo` has no mirror"*.  The mirror is
`sum_ramificationIdxThree_mul_residueDegreeThree`
(`EllipticCurves.FunctionField.MulByThreeResidueDegree`), which consumes
`EllipticCurves.FunctionField.MulByThreeRamification` and hence this file — so the first sentence of
this paragraph stands unchanged: nothing *here* approaches either.

⚠️ One correction while retiring it: the `deg p` written above is `[κ(p) : F]`
(`residueDegreeProj`), and the weight in the fundamental identity is the **relative** degree
`f_p = [κ(p) : κ([3]⁻¹ p)]` (`residueDegreeThree`).  Over an algebraically closed base field both
are `1` and the distinction is invisible; it is the relative one that survives when the base field
is not closed, and it is the one `sum_ramificationIdxTwo_mul_residueDegreeTwo` already used at
`n = 2`.

⚠️ **A second reading of `deg p` is in the tree and it is not this one.**
`EllipticCurves.FunctionField.MulByTwoPlaceAtInfinity` glosses `deg p` as `degPt`, the *relative
ideal norm to `F[X]`* of `EllipticCurves.FunctionField.DivisorDegree`, where the `One correction
while retiring it` paragraph of this file glosses it as `[κ(p) : F]` (`residueDegreeProj`).
**The two glosses were committed one hour and twenty-six minutes apart** — `b3d79fc` (`#1046`) at
2026-08-24 20:31:47 and `de3483b` (`#1049`) at 21:57:49 — **by two agents each of whom was
correcting the same underanalysed `deg p`, and they name different objects.**  They agree over an
algebraically closed base field — that is `degProjPt_eq_residueDegreeProj`
(`EllipticCurves.FunctionField.PlaceDegreeComparison`), a theorem and not a definitional
coincidence — and over a general field neither the agreement nor either `= 1` claim is available.
So `deg p` in a docstring on this front is ambiguous by two readings and unambiguous by value only
over `F̄`; the `deg p`-weighted identity at `n = 3` is `sum_ramificationIdxThree_mul_degProjPt`, in
`EllipticCurves.FunctionField.PlaceDegreeComparison`, and it takes the `degPt` reading.

⚠️ **`[W.IsElliptic]` is absent from every declaration below, and that is not bookkeeping.**  What
makes this section more than a restatement of the general one is that `[3]∗` is a *proper*
embedding: `finrank_mulByThreeRange_functionField = 9` and `not_surjective_mulByThreeEndo`
(`EllipticCurves.FunctionField.MulByThreeDegree`), both of which carry `[W.IsElliptic]`.  The
declarations here must not, and a blanket "`[3]∗` is never surjective" would be **false**: on a
singular Weierstrass curve the smooth locus is `𝔾ₘ` or `𝔾ₐ`, where multiplication by three is
cubing or tripling, and the latter is an isomorphism as soon as `(3 : F) ≠ 0`.  This is
`PlacePullback`'s own warning at `n = 2`, unchanged.

⚠️ **This does not discharge `hprin` at `n = 3` (`#418`).**  It supplies the place-theoretic rung
above `EllipticCurves.Torsion.TriplingCoords`'s coordinate rung; the fibre description that `#791`
consumed at `n = 2` is `EllipticCurves.FunctionField.MulByThreeFibre`, which computes the affine
indices on top of this file and `EllipticCurves.FunctionField.MulByThreeRamification`'s
`∑_{p ↦ q} e_p = 9`.  The class-group computation above it is
`EllipticCurves.FunctionField.PullbackPrincipalityThree`, which is where `hprin` at `n = 3` is
actually discharged, over an algebraically closed base field.

## References

* [J. H. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], II.3 (Prop. II.3.6, the
  pullback of divisors under a finite morphism of curves), III.4 (multiplication by `n`).
* Stichtenoth, *Algebraic Function Fields and Codes*, III.1 (the ramification index `e(P'|P) ≥ 1`).
-/

open Polynomial IsDedekindDomain

namespace WeierstrassCurve.Affine

namespace CoordinateRing

variable {F : Type*} [Field F] {W : Affine F}

/-! ### The integrality hypothesis -/

/-- **`F(W)` is integral over `[3]∗F(W)`.**  The merged `module_finite_mulByThreeRange` says `F(W)`
is a finite module over the range subfield; module-finite implies integral, and
`RingHom.isIntegralElem_of_isIntegral_range` converts integrality over the range subring into
integrality with respect to the endomorphism.

This is the `n = 3` transcription of `mulByTwoEndo_isIntegralElem` (`PlacePullback`), and it is the
only input `PlacePullback`'s general sections were missing at `n = 3` — the other one,
`mulByThreeEndo_algebraMap_base`, has been merged since `MulByThreeFinite`. -/
theorem mulByThreeEndo_isIntegralElem (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0)
    (z : W.FunctionField) : (mulByThreeEndo (W := W) h2 h3).IsIntegralElem z := by
  haveI : Module.Finite ↥(mulByThreeEndo (W := W) h2 h3).range W.FunctionField :=
    module_finite_mulByThreeRange h2 h3
  haveI : Algebra.IsIntegral ↥(mulByThreeEndo (W := W) h2 h3).range W.FunctionField :=
    Algebra.IsIntegral.of_finite _ _
  exact RingHom.isIntegralElem_of_isIntegral_range _ (Algebra.IsIntegral.isIntegral z)

/-! ### The order at infinity of `x ∘ [3]` -/

/-- **`ordInfty (x ∘ [3]) = -2`.**  The tripling formula writes `x(3P) = Φ₃(x)/ΨSq₃(x)` with
`natDegree (Φ 3) = 3² = 9` and `natDegree (ΨSq 3) = 3² - 1 = 8`, so the pole orders at infinity are
`18` and `16` and the quotient has a double pole — the same order as `x` itself, which is what
"`[3]` fixes `O`" looks like before the place theory is run.

The exact degree of `ΨSq 3` needs `((3 : ℤ) : F) ≠ 0`, which is where `h3` stops being inherited
from `mulByThreeEndo`; see the module docstring for why the `n = 2` obstruction is a different
one. -/
theorem ordInfty_mulByThreeEndo_genX (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) :
    ordInfty W (mulByThreeEndo h2 h3 (genX W)) = -2 := by
  have h3' : ((3 : ℤ) : F) ≠ 0 := by exact_mod_cast h3
  have hΦ : ((W.map (algebraMap F W.FunctionField)).Φ 3)
      = (W.Φ 3).map (algebraMap F W.FunctionField) := WeierstrassCurve.map_Φ ..
  have hΨ : ((W.map (algebraMap F W.FunctionField)).ΨSq 3)
      = (W.ΨSq 3).map (algebraMap F W.FunctionField) := WeierstrassCurve.map_ΨSq ..
  rw [mulByThreeEndo_genX h2 h3, hΦ, hΨ,
    ordInfty_div (eval_map_genX_ne_zero (W.Φ_ne_zero 3))
      (eval_map_genX_ne_zero (W.ΨSq_ne_zero h3')),
    ordInfty_eval_map_genX (W.Φ_ne_zero 3), ordInfty_eval_map_genX (W.ΨSq_ne_zero h3'),
    W.natDegree_Φ 3, W.natDegree_ΨSq h3']
  decide

/-! ### The contraction, the index, and the divisor pullback -/

variable [IsDedekindDomain W.CoordinateRing]

/-- **The contraction of a place of the projective curve along `[3]∗`.** -/
noncomputable def comapProjPointThree (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) :
    ProjPoint W → ProjPoint W :=
  comapProjPoint (mulByThreeEndo_algebraMap_base h2 h3) (mulByThreeEndo_isIntegralElem h2 h3)

/-- **The ramification index of `[3]∗`.** -/
noncomputable def ramificationIdxThree (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) (p : ProjPoint W) :
    ℤ :=
  ramificationIdx (mulByThreeEndo_algebraMap_base h2 h3) (mulByThreeEndo_isIntegralElem h2 h3) p

theorem ramificationIdxThree_pos (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) (p : ProjPoint W) :
    0 < ramificationIdxThree h2 h3 p :=
  ramificationIdx_pos _ _ p

/-- **`ord_p (f ∘ [3]) = e_p · ord_{[3]⁻¹ p} (f)`** — the pointwise divisor-level pullback under
multiplication by `3`, on the *projective* point set.

The projectivity is not decoration: `#422`'s 2026-08-16 correction showed the affine AKLB route is
false at `n = 2` because `[2]∗F[W] ⊄ F[W]`, and the same obstruction is there at `n = 3`. -/
theorem divisorProj_mulByThreeEndo_apply (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0)
    {f : W.FunctionField} (hf : f ≠ 0) (p : ProjPoint W) :
    divisorProj W (mulByThreeEndo h2 h3 f) p
      = ramificationIdxThree h2 h3 p * divisorProj W f (comapProjPointThree h2 h3 p) :=
  divisorProj_comp_apply _ _ hf p

/-- **`n`-divisibility of the divisor of `f ∘ [3]`.** -/
theorem dvd_divisorProj_mulByThreeEndo (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) {n : ℤ}
    {f : W.FunctionField} (hf : f ≠ 0)
    (hn : ∀ q : ProjPoint W, n ∣ divisorProj W f q) (p : ProjPoint W) :
    n ∣ divisorProj W (mulByThreeEndo h2 h3 f) p :=
  dvd_divisorProj_comp (mulByThreeEndo_algebraMap_base h2 h3)
    (mulByThreeEndo_isIntegralElem h2 h3) hf hn p

/-- **The `n = 3` form of the statement `#422` asks for.**  For an `n`-torsion point `S` there is a
function `f_S` with `div f_S = n·(S) − n·(O)` (the merged
`divisorProj_eq_single_sub_single_of_torsion`), and every coefficient of `div (f_S ∘ [3])` is then
divisible by `n`. -/
theorem dvd_divisorProj_mulByThreeEndo_of_torsion [DecidableEq F] (h2 : (2 : F) ≠ 0)
    (h3 : (3 : F) ≠ 0) {x y : F} (h : W.Nonsingular x y) {n : ℕ}
    (hP : Point.some x y h ∈ W.torsion n) :
    ∃ f : W.FunctionField, f ≠ 0 ∧
      divisorProj W f = Finsupp.single (some (pointClosedPoint h.left)) (n : ℤ)
        - Finsupp.single none (n : ℤ) ∧
      ∀ p : ProjPoint W, (n : ℤ) ∣ divisorProj W (mulByThreeEndo h2 h3 f) p := by
  classical
  obtain ⟨f, hf, hdiv⟩ := divisorProj_eq_single_sub_single_of_torsion h hP
  refine ⟨f, hf, hdiv, dvd_divisorProj_mulByThreeEndo h2 h3 hf fun q => ?_⟩
  rw [hdiv, Finsupp.sub_apply, Finsupp.single_apply, Finsupp.single_apply]
  exact dvd_sub (by split <;> simp) (by split <;> simp)

/-- **The pullback of divisors along `[3]∗`.** -/
noncomputable def pullbackDivisorThree (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) :
    (ProjPoint W →₀ ℤ) →+ (ProjPoint W →₀ ℤ) :=
  pullbackDivisor (mulByThreeEndo_algebraMap_base h2 h3) (mulByThreeEndo_isIntegralElem h2 h3)

@[simp] theorem pullbackDivisorThree_apply (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0)
    (D : ProjPoint W →₀ ℤ) (p : ProjPoint W) :
    pullbackDivisorThree h2 h3 D p
      = ramificationIdxThree h2 h3 p * D (comapProjPointThree h2 h3 p) :=
  rfl

/-- **`div (f ∘ [3]) = [3]∗ (div f)`** — the divisor-level functoriality of the
multiplication-by-three pullback, as an equation in the projective divisor group.

This is the `n = 3` form of what `divisorProj_mulByTwoEndo` states at `n = 2`, i.e. of `#414` /
`#422` deliverable 1. -/
theorem divisorProj_mulByThreeEndo (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0)
    {f : W.FunctionField} (hf : f ≠ 0) :
    divisorProj W (mulByThreeEndo h2 h3 f) = pullbackDivisorThree h2 h3 (divisorProj W f) :=
  divisorProj_comp _ _ hf

/-- **Finitely many places lie above a place, for `[3]∗`.** -/
theorem finite_comapProjPointThree_preimage_singleton (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0)
    (q : ProjPoint W) : ((comapProjPointThree (W := W) h2 h3) ⁻¹' {q}).Finite :=
  finite_comapProjPoint_preimage_singleton _ _ q

/-! ### The point at infinity -/

/-- **`[3]` fixes the point at infinity**: `comapProjPointThree h2 h3 none = none`.

Classically this is the statement that multiplication by `3` extends to a morphism of the
projective curve carrying `O` to `O`.  The proof runs `divisorProj_mulByThreeEndo_apply` backwards
at the generic `x`-coordinate: an affine contraction would make the right-hand side a nonnegative
multiple of a nonnegative order, because `genX W` lies in the image of the coordinate ring and the
index is positive — but the left-hand side is `-2`. -/
theorem comapProjPointThree_none (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) :
    comapProjPointThree h2 h3 (none : ProjPoint W) = none := by
  have hkey : (-2 : ℤ) = ramificationIdxThree h2 h3 (none : ProjPoint W)
      * divisorProj W (genX W) (comapProjPointThree h2 h3 (none : ProjPoint W)) := by
    rw [← divisorProj_mulByThreeEndo_apply h2 h3 genX_ne_zero none, divisorProj_apply_none,
      ordInfty_mulByThreeEndo_genX h2 h3]
  cases hq : comapProjPointThree h2 h3 (none : ProjPoint W) with
  | none => rfl
  | some v =>
    exfalso
    rw [hq, divisorProj_apply_some] at hkey
    have hge : (0 : ℤ) ≤ ord v (genX W) := by
      rw [genX, genPsi]
      exact ord_algebraMap_nonneg v _
    have hnn : (0 : ℤ) ≤ ramificationIdxThree h2 h3 (none : ProjPoint W) * ord v (genX W) :=
      mul_nonneg (ramificationIdxThree_pos h2 h3 none).le hge
    linarith

/-- **`[3]` is unramified at the point at infinity**: `ramificationIdxThree h2 h3 none = 1`.

⚠️ This says nothing about any other place.  Reading it as "`[3]` is unramified" would be the
mistake five merged docstrings made at `n = 2` in the opposite direction, and which
`MulByTwoFibreInfinity` (`#774`) had to correct. -/
theorem ramificationIdxThree_none (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) :
    ramificationIdxThree h2 h3 (none : ProjPoint W) = 1 := by
  have hkey := divisorProj_mulByThreeEndo_apply h2 h3 (f := genX W) genX_ne_zero none
  rw [comapProjPointThree_none h2 h3, divisorProj_apply_none, divisorProj_apply_none,
    ordInfty_mulByThreeEndo_genX h2 h3, ordInfty_genX] at hkey
  omega

/-- **The projective payoff.**  Pulling back along `[3]` leaves the coefficient of the divisor of a
function at the point at infinity unchanged. -/
theorem divisorProj_mulByThreeEndo_apply_none (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0)
    {f : W.FunctionField} (hf : f ≠ 0) :
    divisorProj W (mulByThreeEndo h2 h3 f) (none : ProjPoint W) = divisorProj W f none := by
  rw [divisorProj_mulByThreeEndo_apply h2 h3 hf, comapProjPointThree_none h2 h3,
    ramificationIdxThree_none h2 h3, one_mul]

/-- **`ordInfty (f ∘ [3]) = ordInfty f`.**  The same statement in the language of
`EllipticCurves.FunctionField.PlaceAtInfinity`: the order at infinity is a `[3]∗`-invariant.

The Dedekind hypothesis does not appear in the statement but is used in the proof, which goes
through the place-theoretic contraction. -/
theorem ordInfty_mulByThreeEndo (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) {f : W.FunctionField}
    (hf : f ≠ 0) : ordInfty W (mulByThreeEndo h2 h3 f) = ordInfty W f := by
  have h := divisorProj_mulByThreeEndo_apply_none h2 h3 hf
  rwa [divisorProj_apply_none, divisorProj_apply_none] at h

/-- **The first computed coefficient of a `[3]`-pulled-back divisor**:
`pullbackDivisorThree h2 h3 D none = D none`, for an **arbitrary** divisor `D`, whether or not it is
`div f` of anything.

`divisorProj_mulByThreeEndo_apply_none` above is the `D = div f` specialisation; neither is the
primitive fact, which is the pair `comapProjPointThree_none` / `ramificationIdxThree_none`.  At
`n = 2` these two statements live in different files (`MulByTwoPlaceAtInfinity` and
`MulByTwoPullbackDivisor`) for import reasons that do not arise here. -/
theorem pullbackDivisorThree_apply_none (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0)
    (D : ProjPoint W →₀ ℤ) : pullbackDivisorThree h2 h3 D (none : ProjPoint W) = D none := by
  rw [pullbackDivisorThree_apply, comapProjPointThree_none h2 h3, ramificationIdxThree_none h2 h3,
    one_mul]

/-! ### Non-vacuity: the statements have content on a real curve

Every theorem above carries `[IsDedekindDomain W.CoordinateRing]`, and `comapProjPointThree` is
extracted from an existence statement by choice, so it is worth exhibiting a curve on which the
whole chain elaborates with every instance discharged rather than asserting that one exists.
`y² = x³ - x` over `ℚ` — the curve the `[2]` files use — has discriminant `64`, and the Dedekind
instance is reached from `IsElliptic` alone over an arbitrary field
(`EllipticCurves.FunctionField.CoordinateRingNormalGeneral`); no algebraically closed base field is
needed, and `(2 : ℚ) ≠ 0` and `(3 : ℚ) ≠ 0` are both `norm_num`. -/

section Nonvacuity

/-- The curve `y² = x³ - x` over `ℚ`, of discriminant `64`. -/
private def exampleCurve : Affine ℚ := ⟨0, 0, 0, -1, 0⟩

private instance : exampleCurve.IsElliptic := by
  rw [WeierstrassCurve.isElliptic_iff, isUnit_iff_ne_zero]
  norm_num [exampleCurve, WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈]

example : IsDedekindDomain exampleCurve.CoordinateRing := inferInstance

example : ordInfty exampleCurve
    (mulByThreeEndo (W := exampleCurve) (by norm_num) (by norm_num) (genX _)) = -2 :=
  ordInfty_mulByThreeEndo_genX _ _

example : comapProjPointThree (W := exampleCurve) (by norm_num) (by norm_num)
    (none : ProjPoint exampleCurve) = none :=
  comapProjPointThree_none _ _

example : ramificationIdxThree (W := exampleCurve) (by norm_num) (by norm_num)
    (none : ProjPoint exampleCurve) = 1 :=
  ramificationIdxThree_none _ _

example {f : exampleCurve.FunctionField} (hf : f ≠ 0) :
    divisorProj exampleCurve (mulByThreeEndo (W := exampleCurve) (by norm_num) (by norm_num) f)
      = pullbackDivisorThree (W := exampleCurve) (by norm_num) (by norm_num)
          (divisorProj exampleCurve f) :=
  divisorProj_mulByThreeEndo _ _ hf

end Nonvacuity

end CoordinateRing

end WeierstrassCurve.Affine
