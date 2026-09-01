/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import EllipticCurves.Fixtures
import EllipticCurves.FunctionField.FunctionFieldBaseChangeN
import EllipticCurves.FunctionField.MulByNComposition
import EllipticCurves.FunctionField.WeilPairingAlternatingAssemblyN
import EllipticCurves.FunctionField.WeilPairingAlternatingBaseChange

/-!
# The alternating property at general `n` over an arbitrary field: the halving point descends

Silverman *AEC* III.8.1(d).  `EllipticCurves.FunctionField.WeilPairingAlternatingAssemblyN` proves
`e_n(T, T) = 1` at an arbitrary `n` over an arbitrary field, but carrying **two** hypotheses: the
`#418` datum `hprin`, and a halving point `P` with `[n]P = T`.  This file removes the second at
every `3`-smooth `n`, exactly as
`EllipticCurves.FunctionField.WeilPairingAlternatingBaseChange` removes it at `n = 2` and `n = 3`.

`hprin` stays.  ⚠️ It is `#418`, it is an *existence* statement, and existence does not descend —
`WeilPairingAlternatingBaseChange`'s test, which this file does not weaken: **base change carries
conclusions down, not hypotheses up.**  The halving point is used to prove an *equality* in `F(W)`,
and equalities descend.

## What made this reachable, and what it cost

The `n = 2` descent (`translateEndo_eq_self_of_mul_algebraMap_sq_eq_of_baseChange`) needs three
things pushed along `functionFieldMap`: the nonsingularity of `T`, the telescoping relation, and
the `n`-th root relation.  At general `n` two of those had no transporter:

* the `n`-th root relation mentions `[n]∗`, and `FunctionFieldBaseChange` had only
  `functionFieldMap_mulByTwoEndo` and `functionFieldMap_mulByThreeEndo`;
* the telescoping relation is indexed by `i • T` for `T : W.Point`, and
  `functionFieldMap_translateEndo` is indexed by an **affine pair** — the interior factor at
  `i ≡ 0` translates by the point at infinity, which that lemma cannot express.

Both are supplied by `EllipticCurves.FunctionField.FunctionFieldBaseChangeN`
(`functionFieldMap_mulByNEndo` and `functionFieldMap_translatePointEndo`).  ⚠️ The second was
*not* on anyone's list: `#1333` predicted the telescope row would "vanish entirely" because gate A
produces `htel` upstairs.  It does — and that is precisely why `htel` has to be carried *down*,
which needs the `W.Point`-indexed intertwiner.  Producing a datum upstairs does not remove the
need to transport it; it only changes which direction it travels.

## ⚠️ Where the `3`-smoothness enters, and where it does not

`hfac` is consumed in exactly one place: `exists_nsmul_eq_of_smooth`
(`EllipticCurves.Torsion.NsmulSmoothSurjective`), the halving point over `F̄`.  The transcendence
over `F̄` is `transcendental_xCoord_nsmul_of_isAlgClosed`, general in `n ≠ 0`.  So the first index
these statements do not reach is `n = 5` **for the halving point**, and `#251`'s coordinate formula
through `nsmul_surjective_of_hasXCoordFormula` would lift them all to every `n` with nothing else
changing.  This is the observation `WeilPairingAlternatingAssemblyN`'s docstring makes about its
`[IsAlgClosed F]` corollary, and it survives the descent unchanged.

⚠️ In `…_of_smooth` below the transcendence over `F` is discharged too, by
`transcendental_xCoord_nsmul_of_smooth`, and *that* one genuinely needs `3`-smoothness and `h3`.
So the two uses of `hfac` in that statement have different reasons, and only one of them is what
`#251` would remove.

## Main statements

* `WeierstrassCurve.Affine.translatePointEndo_eq_self_of_prod_eq_of_pow_eq_of_baseChange` — gate B
  (`WeilPairingAlternatingWorkhorseN`) with its halving-point hypothesis **removed, not relocated**,
  over an arbitrary field at `3`-smooth `n`.
* `WeierstrassCurve.Affine.exists_weilPairingElt_self_eq_one_of_hprin_n_of_baseChange` —
  `e_n(T, T) = 1` over an arbitrary field with `hprin` the only gate.
* `WeierstrassCurve.Affine.exists_weilPairingElt_self_eq_one_of_smooth_of_baseChange` — the same
  with the transcendence discharged as well, so that `h2`, `h3`, `3`-smoothness and `hprin` are the
  whole hypothesis list.

`Recovery` derives the merged `exists_weilPairingElt_self_eq_one_of_hprin_two` and
`…_of_hprin_three` (`WeilPairingAlternatingBaseChange`) from the general form, verbatim.

## What is *not* here

* `hprin` (`#418`, `#962`).
* The `μ`-valued twins.  ⚠️ Deliberately: they are `#1334`'s re-scoped deliverable, together with
  the `μ` forms of the merged general-`n` assembly, and splitting them across two PRs would put two
  authors in the same three-line neighbourhood again.
* `n = 5` and beyond — see above; the obstruction is the halving point, i.e. `#251`.
* The divisor half of base change (`#692`).  Nothing here wants it: no statement below mentions
  `divisor` on the `F̄` side, and `hprin` is never transported.

## References

* [J. Silverman, *The arithmetic of elliptic curves*][silverman2009], III.8.1(d).
-/

open Polynomial IsDedekindDomain

namespace WeierstrassCurve.Affine

open CoordinateRing

variable {F : Type*} [Field F] {W : Affine F} [W.IsElliptic] {xT yT : F}

local notation3 "K" => AlgebraicClosure F

/-! ### Gate B without the halving point -/

open Classical in
/-- **Translation by `T` fixes the `n`-th root, over an arbitrary field.**

`translatePointEndo_eq_self_of_prod_eq_of_pow_eq` (`WeilPairingAlternatingWorkhorseN`) with the
halving hypothesis `[n]P = T` **removed** — not relocated — at every `3`-smooth `n ≠ 0`.

`htel` and `hpow` are equations in `F(W)`, so they push forward along `functionFieldMap`; over `F̄`
the halving point is `exists_nsmul_eq_of_smooth`; and the conclusion, being an equality, comes back
through `functionFieldMap_injective`.  ⚠️ `T` is an arbitrary `W.Point` and is **not** assumed
affine: `basePointMap` is additive, so `[i]T` transports as `[i]` of the transported `T` whether or
not either is at infinity. -/
theorem translatePointEndo_eq_self_of_prod_eq_of_pow_eq_of_baseChange (h2 : (2 : F) ≠ 0)
    {n : ℕ} (hn0 : n ≠ 0) (hfac : ∀ p ∈ n.primeFactors, p = 2 ∨ p = 3)
    (hn : Transcendental F (n • genericPoint (W := W)).xCoord) {T : W.Point}
    {f g : W.FunctionField} (hg : g ≠ 0) {c c₀ : F} (hc : c ≠ 0) (hc₀ : c₀ ≠ 0)
    (htel : ∏ i ∈ Finset.range n, translatePointEndo (i • T) f = algebraMap F W.FunctionField c)
    (hpow : algebraMap F W.FunctionField c₀ * g ^ n = mulByNEndo n hn f) :
    translatePointEndo T g = g := by
  have h2' : (2 : K) ≠ 0 := algebraMap_ofNat_ne_zero h2
  have hn' : Transcendental K
      (n • genericPoint (W := W.map (algebraMap F K))).xCoord :=
    transcendental_xCoord_nsmul_of_isAlgClosed h2' hn0
  have hgne : functionFieldMap W K g ≠ 0 :=
    (map_ne_zero_iff _ (functionFieldMap_injective W K)).mpr hg
  obtain ⟨P, hP⟩ := exists_nsmul_eq_of_smooth h2' hn0 hfac (basePointMap W K T)
  have htel' : ∏ i ∈ Finset.range n,
      translatePointEndo (i • basePointMap W K T) (functionFieldMap W K f)
        = algebraMap K (W.map (algebraMap F K)).FunctionField (algebraMap F K c) := by
    rw [← functionFieldMap_algebraMap_base, ← htel, map_prod]
    exact Finset.prod_congr rfl fun i _ => by
      rw [functionFieldMap_translatePointEndo, map_nsmul]
  have hpow' : algebraMap K (W.map (algebraMap F K)).FunctionField (algebraMap F K c₀)
      * functionFieldMap W K g ^ n = mulByNEndo n hn' (functionFieldMap W K f) := by
    rw [← functionFieldMap_algebraMap_base, ← map_pow, ← map_mul, hpow,
      functionFieldMap_mulByNEndo hn hn']
  have key : translatePointEndo (basePointMap W K T) (functionFieldMap W K g)
      = functionFieldMap W K g :=
    translatePointEndo_eq_self_of_prod_eq_of_pow_eq hn0 hn' hP hgne
      ((map_ne_zero_iff _ (algebraMap F K).injective).mpr hc)
      ((map_ne_zero_iff _ (algebraMap F K).injective).mpr hc₀) htel' hpow'
  refine functionFieldMap_injective W K ?_
  rw [functionFieldMap_translatePointEndo]
  exact key

/-! ### The assembly over an arbitrary field -/

open Classical in
/-- **`e_n(T, T) = 1` at an arbitrary `n` over an arbitrary field**, with `hprin` (`#418`) the only
gate.

`exists_weilPairingElt_self_eq_one_of_hprin_n` (`WeilPairingAlternatingAssemblyN`) is this statement
with the halving point `[n]P = T` added as a hypothesis; the hypotheses and the conclusion are
otherwise identical, and the proof is that one with gate B replaced by its descended form. -/
theorem exists_weilPairingElt_self_eq_one_of_hprin_n_of_baseChange (h2 : (2 : F) ≠ 0)
    {n : ℕ} (hn0 : n ≠ 0) (hfac : ∀ p ∈ n.primeFactors, p = 2 ∨ p = 3)
    (hn : Transcendental F (n • genericPoint (W := W)).xCoord)
    (h : W.Nonsingular xT yT) (htors : Point.some xT yT h ∈ W.torsion n)
    (hprin : ∀ f : W.FunctionField, f ≠ 0 →
      divisor W f = Finsupp.single (pointClosedPoint h.left) (n : ℤ) →
      ∃ g₀ : W.FunctionField, g₀ ≠ 0 ∧
        n • divisor W g₀ = divisor W (mulByNEndo n hn f)) :
    ∃ f : W.FunctionField, f ≠ 0 ∧
      divisorProj W f = Finsupp.single (some (pointClosedPoint h.left)) (n : ℤ)
          - Finsupp.single (none : ProjPoint W) (n : ℤ) ∧
        ∃ g : W.FunctionField, g ≠ 0 ∧
          (∃ u : W.CoordinateRingˣ, (u : W.CoordinateRing) • g ^ n = mulByNEndo n hn f) ∧
          translateEndo h.left g = g ∧ weilPairingElt h.left g = 1 := by
  obtain ⟨f, hf, hdivproj, c, hc, htel⟩ := exists_prod_translatePointEndo_eq_algebraMap h htors
  obtain ⟨g, hg, hgdiv⟩ :=
    hprin f hf (divisor_eq_single_of_divisorProj_eq_single_sub_single hdivproj)
  have hfne : mulByNEndo n hn f ≠ 0 := fun hz =>
    hf ((mulByNEndo n hn).injective (by rw [hz, map_zero]))
  obtain ⟨u, hu⟩ := exists_smul_pow_eq_of_nsmul_divisor hfne hg hgdiv
  obtain ⟨c₀, hc₀, hueq⟩ := isUnit_iff_exists_eq_algebraMap.mp u.isUnit
  have hpow : algebraMap F W.FunctionField c₀ * g ^ n = mulByNEndo n hn f := by
    rw [← hu, Algebra.smul_def, hueq, ← IsScalarTower.algebraMap_apply]
  have htinv : translateEndo h.left g = g := by
    have key := translatePointEndo_eq_self_of_prod_eq_of_pow_eq_of_baseChange h2 hn0 hfac hn hg
      hc hc₀ htel hpow
    rwa [show Point.some xT yT h = torsionPoint h.left from rfl,
      translatePointEndo_torsionPoint] at key
  exact ⟨f, hf, hdivproj, g, hg, ⟨u, hu⟩, htinv,
    weilPairingElt_self_of_translateEndo_fixed h.left hg htinv⟩

open Classical in
/-- **`e_n(T, T) = 1` over an arbitrary field at every `3`-smooth `n ≠ 0`**, with `hprin` the only
hypothesis that is not about the characteristic.

The transcendence is discharged by `transcendental_xCoord_nsmul_of_smooth`, which is where `h3`
enters — the halving point needs neither `h3` nor, over `F̄`, the transcendence.  See the module
docstring for why `hfac` is doing two different jobs here. -/
theorem exists_weilPairingElt_self_eq_one_of_smooth_of_baseChange (h2 : (2 : F) ≠ 0)
    (h3 : (3 : F) ≠ 0) {n : ℕ} (hn0 : n ≠ 0) (hfac : ∀ p ∈ n.primeFactors, p = 2 ∨ p = 3)
    (h : W.Nonsingular xT yT) (htors : Point.some xT yT h ∈ W.torsion n)
    (hprin : ∀ f : W.FunctionField, f ≠ 0 →
      divisor W f = Finsupp.single (pointClosedPoint h.left) (n : ℤ) →
      ∃ g₀ : W.FunctionField, g₀ ≠ 0 ∧
        n • divisor W g₀
          = divisor W (mulByNEndo n (transcendental_xCoord_nsmul_of_smooth h2 h3 hn0 hfac) f)) :
    ∃ f : W.FunctionField, f ≠ 0 ∧
      divisorProj W f = Finsupp.single (some (pointClosedPoint h.left)) (n : ℤ)
          - Finsupp.single (none : ProjPoint W) (n : ℤ) ∧
        ∃ g : W.FunctionField, g ≠ 0 ∧
          (∃ u : W.CoordinateRingˣ, (u : W.CoordinateRing) • g ^ n
            = mulByNEndo n (transcendental_xCoord_nsmul_of_smooth h2 h3 hn0 hfac) f) ∧
          translateEndo h.left g = g ∧ weilPairingElt h.left g = 1 :=
  exists_weilPairingElt_self_eq_one_of_hprin_n_of_baseChange h2 hn0 hfac _ h htors hprin

/-! ### Recovery of the merged `n = 2` and `n = 3` arbitrary-field assemblies

`#907`'s rule.  Both merged headlines of `WeilPairingAlternatingBaseChange` come back out of the
general form, verbatim, through `mulByNEndo_two` / `mulByNEndo_three`.  Each is `private`: a public
copy would duplicate a merged name.
-/

section Recovery

variable {x₂ y₂ x₃ y₃ : F}

omit [W.IsElliptic] in
/-- `3`-smoothness at a prime index: the only prime factor of a prime `p` is `p` itself. -/
private lemma primeFactors_eq_two_or_three_of_prime {p : ℕ} (hp : p.Prime)
    (h : p = 2 ∨ p = 3) : ∀ q ∈ p.primeFactors, q = 2 ∨ q = 3 := fun q hq => by
  rw [Nat.mem_primeFactors] at hq
  rw [(Nat.prime_dvd_prime_iff_eq hq.1 hp).mp hq.2.1]
  exact h

open Classical in
/-- `exists_weilPairingElt_self_eq_one_of_hprin_two`
(`EllipticCurves.FunctionField.WeilPairingAlternatingBaseChange`), recovered. -/
private theorem exists_weilPairingElt_self_eq_one_of_hprin_two_of_general (h2 : (2 : F) ≠ 0)
    (h : W.Nonsingular x₂ y₂) (htors : Point.some x₂ y₂ h ∈ W.torsion 2)
    (hprin : ∀ f : W.FunctionField, f ≠ 0 →
      divisor W f = Finsupp.single (pointClosedPoint h.left) (2 : ℤ) →
      ∃ g₀ : W.FunctionField, g₀ ≠ 0 ∧
        2 • divisor W g₀ = divisor W (mulByTwoEndo h2 f)) :
    ∃ f : W.FunctionField, f ≠ 0 ∧
      divisorProj W f = Finsupp.single (some (pointClosedPoint h.left)) (2 : ℤ)
          - Finsupp.single (none : ProjPoint W) (2 : ℤ) ∧
        ∃ g : W.FunctionField, g ≠ 0 ∧
          (∃ u : W.CoordinateRingˣ, (u : W.CoordinateRing) • g ^ 2 = mulByTwoEndo h2 f) ∧
          translateEndo h.left g = g ∧ weilPairingElt h.left g = 1 := by
  have key := exists_weilPairingElt_self_eq_one_of_hprin_n_of_baseChange (n := 2) h2
    (by norm_num) (primeFactors_eq_two_or_three_of_prime Nat.prime_two (Or.inl rfl))
    (transcendental_xCoord_two_nsmul (W := W) h2) h htors
    (by simpa only [mulByNEndo_two h2, Nat.cast_ofNat] using hprin)
  simpa only [mulByNEndo_two h2, Nat.cast_ofNat] using key

open Classical in
/-- `exists_weilPairingElt_self_eq_one_of_hprin_three`
(`EllipticCurves.FunctionField.WeilPairingAlternatingBaseChange`), recovered. -/
private theorem exists_weilPairingElt_self_eq_one_of_hprin_three_of_general (h2 : (2 : F) ≠ 0)
    (h3 : (3 : F) ≠ 0) (h : W.Nonsingular x₃ y₃) (htors : Point.some x₃ y₃ h ∈ W.torsion 3)
    (hprin : ∀ f : W.FunctionField, f ≠ 0 →
      divisor W f = Finsupp.single (pointClosedPoint h.left) (3 : ℤ) →
      ∃ g₀ : W.FunctionField, g₀ ≠ 0 ∧
        3 • divisor W g₀ = divisor W (mulByThreeEndo h2 h3 f)) :
    ∃ f : W.FunctionField, f ≠ 0 ∧
      divisorProj W f = Finsupp.single (some (pointClosedPoint h.left)) (3 : ℤ)
          - Finsupp.single (none : ProjPoint W) (3 : ℤ) ∧
        ∃ g : W.FunctionField, g ≠ 0 ∧
          (∃ u : W.CoordinateRingˣ, (u : W.CoordinateRing) • g ^ 3 = mulByThreeEndo h2 h3 f) ∧
          translateEndo h.left g = g ∧ weilPairingElt h.left g = 1 := by
  have key := exists_weilPairingElt_self_eq_one_of_hprin_n_of_baseChange (n := 3) h2
    (by norm_num) (primeFactors_eq_two_or_three_of_prime Nat.prime_three (Or.inr rfl))
    (transcendental_xCoord_three_nsmul (W := W) h2 h3) h htors
    (by simpa only [mulByNEndo_three h2 h3, Nat.cast_ofNat] using hprin)
  simpa only [mulByNEndo_three h2 h3, Nat.cast_ofNat] using key

end Recovery

/-! ### Non-vacuity at `n = 6`, over a field that is not algebraically closed

⚠️ `hprin` is `#418` and cannot be discharged at any index, so it stays bound below.  What is
certified is that **every other hypothesis of the `3`-smooth headline is simultaneously satisfiable
over `ℚ`** at an index no merged statement reaches: the elliptic instance, `(2 : ℚ) ≠ 0`,
`(3 : ℚ) ≠ 0`, `n ≠ 0`, `3`-smoothness, an affine nonsingular `T`, and `T ∈ torsion 6`.  The halving
point is not in that list because the theorem produces it — which is the whole content of this file.

⚠️ `ℚ` is **not** algebraically closed (`rat_not_isAlgClosed'`), so neither the merged
`exists_weilPairingElt_self_eq_one_of_hprin_n_of_algClosed` nor `exists_nsmul_eq_of_smooth` applies
directly here.  That is what makes this a certificate for the descent rather than a restatement of
the algebraically closed corollary.

⚠️ The curve is `y² = x³ + 1`, **not** this subtree's default `y² = x³ − x`: on the default every
affine rational point is `2`-torsion, so there is no point of order `3` on it.  A certificate
resting on a false hypothesis proves nothing (`#916`), so `htors` is proved rather than assumed.
-/

section Nonvacuity

/-- **`ℚ` is not algebraically closed**, from `X² + X + 1` having no rational root.  Re-derived
because `WeilPairingAlternatingBaseChange`'s copy is `private`. -/
private lemma rat_not_isAlgClosed' : ¬ IsAlgClosed ℚ := by
  intro hcl
  obtain ⟨q, hq⟩ := hcl.exists_root (X ^ 2 + X + 1 : ℚ[X]) (by
    rw [show (X ^ 2 + X + 1 : ℚ[X]) = C 1 * X ^ 2 + C 1 * X + C 1 by simp,
      degree_quadratic one_ne_zero]
    exact two_ne_zero)
  rw [IsRoot, eval_add, eval_add, eval_pow, eval_X, eval_one] at hq
  nlinarith [sq_nonneg (2 * q + 1)]

private lemma exampleTwoNeZero : (2 : ℚ) ≠ 0 := by norm_num

private lemma exampleThreeNeZero : (3 : ℚ) ≠ 0 := by norm_num

/-! The certificate curve `y² = x³ + 1` is the shared `EllipticCurves.Fixture.y2EqX3AddOne`, whose
single `[CharZero F]` instance also supplies `IsElliptic` here. -/

open EllipticCurves.Fixture

/-- `T = (0, 1)` is a nonsingular point of `y² = x³ + 1`. -/
private lemma exampleNonsingularT : (y2EqX3AddOne ℚ).Nonsingular 0 1 := by
  rw [nonsingular_iff]
  refine ⟨?_, Or.inr ?_⟩ <;>
    norm_num [y2EqX3AddOne, WeierstrassCurve.Affine.equation_iff, WeierstrassCurve.Affine.negY]

open Classical in
/-- `[2]T = −T`: the tangent at `(0, 1)` is horizontal, and doubling returns `(0, −1)`. -/
private lemma exampleDouble :
    Point.some (0 : ℚ) 1 exampleNonsingularT + Point.some (0 : ℚ) 1 exampleNonsingularT
      = -Point.some (0 : ℚ) 1 exampleNonsingularT := by
  have hy : (1 : ℚ) ≠ (y2EqX3AddOne ℚ).negY 0 1 := by
    norm_num [y2EqX3AddOne, WeierstrassCurve.Affine.negY]
  rw [Point.add_self_of_Y_ne hy, Point.neg_some, Point.some.injEq]
  constructor <;>
    norm_num [y2EqX3AddOne, WeierstrassCurve.Affine.addX, WeierstrassCurve.Affine.addY,
      WeierstrassCurve.Affine.negAddY, WeierstrassCurve.Affine.negY,
      WeierstrassCurve.Affine.slope]

open Classical in
/-- `T` has order `3`. -/
private lemma exampleThreeTorsion :
    ((3 : ℕ) • Point.some (0 : ℚ) 1 exampleNonsingularT : (y2EqX3AddOne ℚ).Point) = 0 := by
  rw [show (3 : ℕ) = 2 + 1 from rfl, succ_nsmul, two_nsmul, exampleDouble, neg_add_cancel]

open Classical in
/-- Hence `T` is `6`-torsion, without having order `6`. -/
private lemma exampleSixTorsion :
    Point.some (0 : ℚ) 1 exampleNonsingularT ∈ (y2EqX3AddOne ℚ).torsion 6 := by
  rw [mem_torsion_iff, show (6 : ℕ) = 3 + 3 from rfl, add_nsmul, exampleThreeTorsion, add_zero]

/-- `6` is `3`-smooth. -/
private lemma exampleSmooth : ∀ p ∈ (6 : ℕ).primeFactors, p = 2 ∨ p = 3 := by
  intro p hp
  rw [show (6 : ℕ) = 2 * 3 from rfl, Nat.primeFactors_mul (by norm_num) (by norm_num),
    Finset.mem_union, Nat.Prime.primeFactors Nat.prime_two,
    Nat.Prime.primeFactors Nat.prime_three, Finset.mem_singleton, Finset.mem_singleton] at hp
  exact hp

open Classical in
/-- **Every hypothesis but `hprin` is simultaneously satisfiable at `n = 6` over `ℚ`.**

⚠️ The `by convert exampleSixTorsion` is not decoration: `ℚ` has a genuine `DecidableEq` instance,
so `exampleSixTorsion`'s `torsion` is indexed by `instDecidableEqRat` while the headline — general
in `F` and elaborated `open Classical in` — is indexed by `Classical.propDecidable`.  `convert`
discharges the difference by `Subsingleton.elim`.  It does not arise in the merged blocks over
`AlgebraicClosure ℚ`, which has no decidable equality. -/
example
    (hprin : ∀ f : (y2EqX3AddOne ℚ).FunctionField, f ≠ 0 →
      divisor (y2EqX3AddOne ℚ) f
          = Finsupp.single (pointClosedPoint exampleNonsingularT.left) ((6 : ℕ) : ℤ) →
        ∃ g₀ : (y2EqX3AddOne ℚ).FunctionField, g₀ ≠ 0 ∧
          (6 : ℕ) • divisor (y2EqX3AddOne ℚ) g₀ = divisor (y2EqX3AddOne ℚ)
            (mulByNEndo 6 (transcendental_xCoord_nsmul_of_smooth exampleTwoNeZero
              exampleThreeNeZero (by norm_num) exampleSmooth) f)) :
    ∃ f : (y2EqX3AddOne ℚ).FunctionField, f ≠ 0 ∧
      divisorProj (y2EqX3AddOne ℚ) f
          = Finsupp.single (some (pointClosedPoint exampleNonsingularT.left)) ((6 : ℕ) : ℤ)
            - Finsupp.single (none : ProjPoint (y2EqX3AddOne ℚ)) ((6 : ℕ) : ℤ) ∧
        ∃ g : (y2EqX3AddOne ℚ).FunctionField, g ≠ 0 ∧
          (∃ u : (y2EqX3AddOne ℚ).CoordinateRingˣ, (u : (y2EqX3AddOne ℚ).CoordinateRing) • g ^
              (6 : ℕ)
            = mulByNEndo 6 (transcendental_xCoord_nsmul_of_smooth exampleTwoNeZero
                exampleThreeNeZero (by norm_num) exampleSmooth) f) ∧
          translateEndo exampleNonsingularT.left g = g ∧
            weilPairingElt exampleNonsingularT.left g = 1 :=
  exists_weilPairingElt_self_eq_one_of_smooth_of_baseChange exampleTwoNeZero exampleThreeNeZero
    (by norm_num) exampleSmooth exampleNonsingularT (by convert exampleSixTorsion) hprin

end Nonvacuity

end WeierstrassCurve.Affine
