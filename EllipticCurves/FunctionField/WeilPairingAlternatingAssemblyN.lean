/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import EllipticCurves.FunctionField.WeilPairingAlternatingWorkhorseN
import EllipticCurves.FunctionField.WeilPairingTelescopeN
import EllipticCurves.Torsion.NsmulSmoothSurjective

/-!
# The alternating property at general `n`: `e_n(T, T) = 1`, assembled

Silverman *AEC* III.8.1(d).  `EllipticCurves.FunctionField.WeilPairingAlternating{Two,Three}` are
the merged numeral cases; this file is the assembly at an arbitrary `n`, and both of them are
recovered from it, verbatim.

`#1327` split the general-`n` alternating argument into two gates that do not depend on each other.
Both are now merged, and this file is the join:

* **gate A, the divisor telescope** — `f` with `div f = n(T) − n(O)` and
  `∏_{i<n} τ_{[i]T}∗ f = c ∈ F∖{0}`, from `exists_prod_translatePointEndo_eq_algebraMap`
  (`EllipticCurves.FunctionField.WeilPairingTelescopeN`);
* **gate B, the workhorse** — `τ_T∗ g = g` from that product and an `n`-th root `g` of `[n]∗ f`,
  from `translatePointEndo_eq_self_of_prod_eq_of_pow_eq`
  (`EllipticCurves.FunctionField.WeilPairingAlternatingWorkhorseN`).

Between them the argument is the merged `n = 2` proof with three names changed: the `#418` datum
`hprin` produces `g`, `exists_smul_pow_eq_of_nsmul_divisor` turns `n • div g = div ([n]∗ f)` into
`u • gⁿ = [n]∗ f`, `isUnit_iff_exists_eq_algebraMap` says the unit `u` is a nonzero constant, gate B
gives `τ_T∗ g = g`, and `weilPairingElt_self_of_translateEndo_fixed` reads off `e_n(T, T) = 1`.
Every one of those five was already general in `n`; only the two gates were missing.

## ⚠️ The core needs no `[IsAlgClosed F]`, and that is not a technicality

`WeilPairingAlternatingBaseChange`'s docstring establishes that `[IsAlgClosed F]` reaches this front
by **two** independent routes: `hprin`, and the halving point `P` with `[n]P = T`.  At `n = 2` and
`n = 3` the halving point is produced *inside* the assembly, which is why both merged headlines
carry `[IsAlgClosed F]`.

Gate B takes `{P T : W.Point} (hPT : n • P = T)` with `P` **not required to be affine** and no
`[IsAlgClosed F]` anywhere.  So `exists_weilPairingElt_self_eq_one_of_hprin_n` below takes the
halving point as a hypothesis and is stated over an **arbitrary field**, and
`…_of_algClosed` discharges it.  That layering matches
`translateEndo_eq_self_of_mul_algebraMap_sq_eq` (core, arbitrary field, halving point explicit)
against its `_of_baseChange` form, and it is what leaves the base-change descent a separate piece of
work rather than a rewrite of this one.

## ⚠️ Where the `n = 5` gate on the algebraically closed corollary actually is

Every other `_of_smooth` corollary on this front stops at `n = 5` because the *transcendence*
`Transcendental F (n • 𝒫).xCoord` is only available at `3`-smooth `n`.  **That is not the reason
here.**  Over `F̄` the transcendence is `transcendental_xCoord_nsmul_of_isAlgClosed`, which is
general in `n ≠ 0` and needs no `3`-smoothness and no `(3 : F) ≠ 0`.  The `3`-smoothness enters in
exactly one place, `exists_nsmul_eq_of_smooth` (`EllipticCurves.Torsion.NsmulSmoothSurjective`),
which is what produces the halving point.  A general-`n` surjectivity of `[n]` on `E(F̄)` — i.e.
`#251`'s coordinate formula through `nsmul_surjective_of_hasXCoordFormula` — would lift this
corollary to every `n` with nothing else changing.

## Main results

* **`WeierstrassCurve.Affine.exists_weilPairingElt_self_eq_one_of_hprin_n`** — over an arbitrary
  field, with `hprin` and the halving point as hypotheses;
* **`WeierstrassCurve.Affine.exists_weilPairingElt_self_eq_one_of_hprin_n_of_algClosed`** — over
  `F̄` at every `3`-smooth `n ≠ 0`, with `hprin` the only hypothesis left.

## ⚠️ `open Classical in`, and why the `[DecidableEq F]` binder is *not* used here

`WeilPairingTelescopeN` found that a general statement mentioning `i • P` should take
`[DecidableEq F]` as an instance **binder** rather than being elaborated `open Classical in`, so
that a certificate over a field with its own `DecidableEq` instance costs no `convert`.  That
finding is right and this file is the first place it does not apply, for two reasons worth stating
so the next author does not re-litigate it:

* gate B is elaborated `open Classical in`, so its `htel` and `hPT` are Classical-fixed.  A binder
  form here would have to transport both across `Subsingleton.elim` at every use — the binder pays
  only once gate B is restated, not before;
* both statements this file must recover are themselves `open Classical in`
  (`WeilPairingAlternatingTwo:276`, `WeilPairingAlternatingThree:311`), and the certificate is over
  `AlgebraicClosure ℚ`, which carries **no** `DecidableEq` instance — so there is no competing
  instance for a binder to be polymorphic over.  The certificate below costs zero `convert`s as it
  stands.

The general lesson is narrower than "prefer the binder": **the binder pays exactly when a consumer
over a field with a competing `DecidableEq` instance exists.**  Over `F̄` it buys nothing.

## What is *not* here

* **`hprin`, the `#418` datum** — carried as a hypothesis at both levels, exactly as the merged
  `n = 2` and `n = 3` headlines carry it.  `EllipticCurves.FunctionField.PullbackPrincipalityTwo`
  discharges it at `n = 2` over `F̄`; at general `n` nothing does, and `#962` records the general
  field case.  ⚠️ This is the last real gate on the alternating front — do not read this file as
  "alternating at general `n` is unconditional".
* **The base-change descent**, i.e. dropping the halving-point hypothesis over an arbitrary field
  the way `translateEndo_eq_self_of_mul_algebraMap_sq_eq_of_baseChange` does at `n = 2`.  It needs
  `functionFieldMap_mulByNEndo`, and `EllipticCurves.FunctionField.FunctionFieldBaseChange` has only
  the two numeral forms `functionFieldMap_mulByTwoEndo` and `functionFieldMap_mulByThreeEndo`.  That
  missing intertwiner is the whole of the remaining work and it is a separate piece.
* `n = 5` on the algebraically closed corollary — see above; the obstruction is the halving point.
* `ωₙ`, `#404`, `#251`, Ward, `μ_n`, bilinearity, non-degeneracy.

## References

* [J. Silverman, *The arithmetic of elliptic curves*][silverman2009], III.8.1(d).
-/

open Polynomial IsDedekindDomain

namespace WeierstrassCurve.Affine

open CoordinateRing

variable {F : Type*} [Field F] {W : Affine F} [W.IsElliptic]
  [IsDedekindDomain W.CoordinateRing] {xT yT : F}

/-! ### The assembly over an arbitrary field -/

open Classical in
/-- **`e_n(T, T) = 1` at general `n`, over an arbitrary field.**

Given the `#418` datum `hprin` — the principality of the `n`-divisible divisor `div ([n]∗ f_T)`, in
the exact shape `exists_gS_n` takes it — and a point `P` with `[n]P = T`, there are a principal
function `f_T` with `div f_T = n(T) − n(O)` and an `n`-th root `g_T` of `[n]∗ f_T` (up to a unit of
`F[W]`) with `τ_T∗ g_T = g_T`, hence `e_n(T, T) = 1`.

This is `exists_weilPairingElt_self_eq_one_of_algClosed_two`
(`EllipticCurves.FunctionField.WeilPairingAlternatingTwo`) at an arbitrary `n`, with
`[IsAlgClosed F]` traded for the explicit halving point.  ⚠️ `P` is **not** required to be affine
and no interior multiple `[i]P` or `[i]T` is either — that is what
`EllipticCurves.FunctionField.TranslationPointEndomorphism` buys, and it is why the `n = 3`
assembly's auxiliary point `Q` has no analogue in this hypothesis list.

⚠️ `hprin` is a hypothesis, not a conclusion.  It is `#418`, it is open at general `n`, and it is
the last real gate on this front. -/
theorem exists_weilPairingElt_self_eq_one_of_hprin_n {n : ℕ} (hnz : n ≠ 0)
    (hn : Transcendental F (n • genericPoint (W := W)).xCoord)
    (h : W.Nonsingular xT yT) (htors : Point.some xT yT h ∈ W.torsion n)
    {P : W.Point} (hPT : n • P = Point.some xT yT h)
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
    have key := translatePointEndo_eq_self_of_prod_eq_of_pow_eq hnz hn hPT hg hc hc₀ htel hpow
    rwa [show Point.some xT yT h = torsionPoint h.left from rfl,
      translatePointEndo_torsionPoint] at key
  exact ⟨f, hf, hdivproj, g, hg, ⟨u, hu⟩, htinv,
    weilPairingElt_self_of_translateEndo_fixed h.left hg htinv⟩

/-! ### The assembly over an algebraically closed field -/

section AlgClosed

open Classical in
/-- **`e_n(T, T) = 1` over `F̄` at every `3`-smooth `n ≠ 0`**, with `hprin` the only hypothesis
left.

Both hypotheses the core takes on top of `hprin` are discharged here:

* the transcendence, by `transcendental_xCoord_nsmul_of_isAlgClosed` — general in `n ≠ 0` over `F̄`,
  needing neither `3`-smoothness nor `(3 : F) ≠ 0`;
* the halving point, by `exists_nsmul_eq_of_smooth`
  (`EllipticCurves.Torsion.NsmulSmoothSurjective`).

⚠️ **`hfac` is consumed in the second of those and nowhere else**, so the first index this does not
reach is `n = 5` *for the halving point*, not for the transcendence — unlike every other
`_of_smooth` corollary on this front.  See the module docstring. -/
theorem exists_weilPairingElt_self_eq_one_of_hprin_n_of_algClosed [IsAlgClosed F]
    (h2 : (2 : F) ≠ 0) {n : ℕ} (hnz : n ≠ 0) (hfac : ∀ p ∈ n.primeFactors, p = 2 ∨ p = 3)
    (h : W.Nonsingular xT yT) (htors : Point.some xT yT h ∈ W.torsion n)
    (hprin : ∀ f : W.FunctionField, f ≠ 0 →
      divisor W f = Finsupp.single (pointClosedPoint h.left) (n : ℤ) →
      ∃ g₀ : W.FunctionField, g₀ ≠ 0 ∧
        n • divisor W g₀
          = divisor W (mulByNEndo n (transcendental_xCoord_nsmul_of_isAlgClosed h2 hnz) f)) :
    ∃ f : W.FunctionField, f ≠ 0 ∧
      divisorProj W f = Finsupp.single (some (pointClosedPoint h.left)) (n : ℤ)
          - Finsupp.single (none : ProjPoint W) (n : ℤ) ∧
        ∃ g : W.FunctionField, g ≠ 0 ∧
          (∃ u : W.CoordinateRingˣ, (u : W.CoordinateRing) • g ^ n
            = mulByNEndo n (transcendental_xCoord_nsmul_of_isAlgClosed h2 hnz) f) ∧
          translateEndo h.left g = g ∧ weilPairingElt h.left g = 1 :=
  let ⟨_, hP⟩ := exists_nsmul_eq_of_smooth h2 hnz hfac (Point.some xT yT h)
  exists_weilPairingElt_self_eq_one_of_hprin_n hnz _ h htors hP hprin

end AlgClosed

/-! ### Recovery of the merged `n = 2` and `n = 3` assemblies

`#907`'s rule: a general form is only worth having if the merged statements it replaces come back
out of it unchanged.  Both do, and the two statements below are their signatures character for
character, ambient `variable` line included, `[IsAlgClosed F]` included.  Each is proved *through*
the algebraically closed corollary rather than re-proved.

⚠️ Both are `private`: public copies would duplicate merged names.  Check them against their twins
by the **elaborated-type** comparison (`pp.explicit`, `pp.universes`, `pp.deepTerms`) inside a copy
of this module, not by a source diff — a source comparator cannot see an auto-bound instance binder,
and printed names differ between modules with different `open` lines.

⚠️ The only real content of either is the numeral bridge `mulByNEndo_two` / `mulByNEndo_three`,
which has to be pushed through `hprin` as well as through the conclusion.  Proof irrelevance makes
the transcendence argument of `mulByNEndo` unify on its own; do not try to match it by hand. -/

section Recovery

variable {x₂ y₂ x₃ y₃ : F}

omit [W.IsElliptic] [IsDedekindDomain W.CoordinateRing] in
/-- `3`-smoothness at a prime index: the only prime factor of a prime `p` is `p` itself. -/
private lemma primeFactors_eq_two_or_three_of_prime {p : ℕ} (hp : p.Prime)
    (h : p = 2 ∨ p = 3) : ∀ q ∈ p.primeFactors, q = 2 ∨ q = 3 := fun q hq => by
  rw [Nat.mem_primeFactors] at hq
  rw [(Nat.prime_dvd_prime_iff_eq hq.1 hp).mp hq.2.1]
  exact h

open Classical in
/-- `exists_weilPairingElt_self_eq_one_of_algClosed_two`
(`EllipticCurves.FunctionField.WeilPairingAlternatingTwo`), recovered. -/
private theorem exists_weilPairingElt_self_eq_one_of_algClosed_two_of_general [IsAlgClosed F]
    (h2 : (2 : F) ≠ 0) (h : W.Nonsingular x₂ y₂) (htors : Point.some x₂ y₂ h ∈ W.torsion 2)
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
  have key := exists_weilPairingElt_self_eq_one_of_hprin_n_of_algClosed (n := 2) h2
    (by norm_num) (primeFactors_eq_two_or_three_of_prime Nat.prime_two (Or.inl rfl)) h htors
    (by simpa only [mulByNEndo_two h2, Nat.cast_ofNat] using hprin)
  simpa only [mulByNEndo_two h2, Nat.cast_ofNat] using key

open Classical in
/-- `exists_weilPairingElt_self_eq_one_of_algClosed_three`
(`EllipticCurves.FunctionField.WeilPairingAlternatingThree`), recovered.

⚠️ `h3` is in the statement only because `mulByThreeEndo` is indexed by it; neither discharge in the
corollary above needs it.  Asking the general form for it would have made this recovery carry a
hypothesis the merged statement does not have. -/
private theorem exists_weilPairingElt_self_eq_one_of_algClosed_three_of_general [IsAlgClosed F]
    (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) (h : W.Nonsingular x₃ y₃)
    (htors : Point.some x₃ y₃ h ∈ W.torsion 3)
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
  have key := exists_weilPairingElt_self_eq_one_of_hprin_n_of_algClosed (n := 3) h2
    (by norm_num) (primeFactors_eq_two_or_three_of_prime Nat.prime_three (Or.inr rfl)) h htors
    (by simpa only [mulByNEndo_three h2 h3, Nat.cast_ofNat] using hprin)
  simpa only [mulByNEndo_three h2 h3, Nat.cast_ofNat] using key

end Recovery

/-! ### Non-vacuity at `n = 6`

⚠️ **`hprin` is a hypothesis and it is `#418`, so the headline cannot be fully instantiated on any
concrete curve.**  What is certified below is that *every other* hypothesis of the algebraically
closed corollary is simultaneously satisfiable at an index no merged assembly reaches: the elliptic
instance, `(2 : K) ≠ 0`, `n ≠ 0`, `3`-smoothness of `n`, an affine nonsingular `T`, and
`T ∈ torsion n`.  The halving point is not in that list because the corollary produces it — which is
itself part of the claim.  What stays hypothetical is `hprin` and nothing else; a certificate
resting on a hypothesis that is *false* proves nothing (`#916`), so each of the others is proved
here rather than assumed.

⚠️ `n = 6` at a `T` of order **3** is chosen for the order, not the index.  `T` of order strictly
dividing `n` is the configuration no `translateEndo`-indexed statement can express — the interior
factor at `i = 3` translates by `O` — and `WeilPairingTelescopeN`'s certificate exercises the same
one for the same reason.

⚠️ The curve is `y² = x³ + 1`, **not** this subtree's default `y² = x³ − x`: on the default every
affine rational point is `2`-torsion, so there is no point of order `3` on it to exhibit.  That has
now made a certificate impossible twice on this front (`#1325`, `#1328`) and the default is simply
wrong for anything past `n = 3`.

The base field is `AlgebraicClosure ℚ`, as `[IsAlgClosed F]` requires.  It carries no `DecidableEq`
instance, so `open Classical in` supplies the same one the theorem's statement fixes and the
certificate costs no `convert` — see the module docstring. -/

section Nonvacuity

/-- An algebraically closed field of characteristic zero. -/
private abbrev exampleField : Type := AlgebraicClosure ℚ

/-- The curve `y² = x³ + 1` over `AlgebraicClosure ℚ`, of discriminant `−432`. -/
private noncomputable def exampleCurve : Affine exampleField := ⟨0, 0, 0, 0, 1⟩

private instance : exampleCurve.IsElliptic := by
  rw [WeierstrassCurve.isElliptic_iff, isUnit_iff_ne_zero]
  norm_num [exampleCurve, WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈]

private lemma exampleTwoNeZero : (2 : exampleField) ≠ 0 := by norm_num

/-- `T = (0, 1)` is a nonsingular point of `y² = x³ + 1`. -/
private lemma exampleNonsingularT : exampleCurve.Nonsingular 0 1 := by
  rw [nonsingular_iff]
  refine ⟨?_, Or.inr ?_⟩ <;>
    norm_num [exampleCurve, WeierstrassCurve.Affine.equation_iff, WeierstrassCurve.Affine.negY]

open Classical in
/-- `[2]T = −T`: the tangent at `(0, 1)` is horizontal, and doubling returns `(0, −1)`. -/
private lemma exampleDouble :
    Point.some (0 : exampleField) 1 exampleNonsingularT
        + Point.some (0 : exampleField) 1 exampleNonsingularT
      = -Point.some (0 : exampleField) 1 exampleNonsingularT := by
  have hy : (1 : exampleField) ≠ exampleCurve.negY 0 1 := by
    norm_num [exampleCurve, WeierstrassCurve.Affine.negY]
  rw [Point.add_self_of_Y_ne hy, Point.neg_some, Point.some.injEq]
  constructor <;>
    norm_num [exampleCurve, WeierstrassCurve.Affine.addX, WeierstrassCurve.Affine.addY,
      WeierstrassCurve.Affine.negAddY, WeierstrassCurve.Affine.negY,
      WeierstrassCurve.Affine.slope]

open Classical in
/-- `T` has order `3`. -/
private lemma exampleThreeTorsion :
    ((3 : ℕ) • Point.some (0 : exampleField) 1 exampleNonsingularT : exampleCurve.Point) = 0 := by
  rw [show (3 : ℕ) = 2 + 1 from rfl, succ_nsmul, two_nsmul, exampleDouble, neg_add_cancel]

open Classical in
/-- Hence `T` is `6`-torsion, without having order `6`. -/
private lemma exampleSixTorsion :
    Point.some (0 : exampleField) 1 exampleNonsingularT ∈ exampleCurve.torsion 6 := by
  rw [mem_torsion_iff, show (6 : ℕ) = 3 + 3 from rfl, add_nsmul, exampleThreeTorsion, add_zero]

/-- `6` is `3`-smooth. -/
private lemma exampleSmooth : ∀ p ∈ (6 : ℕ).primeFactors, p = 2 ∨ p = 3 := by
  intro p hp
  rw [show (6 : ℕ) = 2 * 3 from rfl, Nat.primeFactors_mul (by norm_num) (by norm_num),
    Finset.mem_union, Nat.Prime.primeFactors Nat.prime_two,
    Nat.Prime.primeFactors Nat.prime_three, Finset.mem_singleton, Finset.mem_singleton] at hp
  exact hp

open Classical in
/-- **Every hypothesis but `hprin` is simultaneously satisfiable at `n = 6`.** -/
example
    (hprin : ∀ f : exampleCurve.FunctionField, f ≠ 0 →
      divisor exampleCurve f
          = Finsupp.single (pointClosedPoint exampleNonsingularT.left) ((6 : ℕ) : ℤ) →
        ∃ g₀ : exampleCurve.FunctionField, g₀ ≠ 0 ∧
          (6 : ℕ) • divisor exampleCurve g₀ = divisor exampleCurve
            (mulByNEndo 6
              (transcendental_xCoord_nsmul_of_isAlgClosed exampleTwoNeZero (by norm_num)) f)) :
    ∃ f : exampleCurve.FunctionField, f ≠ 0 ∧
      divisorProj exampleCurve f
          = Finsupp.single (some (pointClosedPoint exampleNonsingularT.left)) ((6 : ℕ) : ℤ)
            - Finsupp.single (none : ProjPoint exampleCurve) ((6 : ℕ) : ℤ) ∧
        ∃ g : exampleCurve.FunctionField, g ≠ 0 ∧
          (∃ u : exampleCurve.CoordinateRingˣ, (u : exampleCurve.CoordinateRing) • g ^ (6 : ℕ)
            = mulByNEndo 6
                (transcendental_xCoord_nsmul_of_isAlgClosed exampleTwoNeZero (by norm_num)) f) ∧
          translateEndo exampleNonsingularT.left g = g ∧
            weilPairingElt exampleNonsingularT.left g = 1 :=
  exists_weilPairingElt_self_eq_one_of_hprin_n_of_algClosed exampleTwoNeZero (by norm_num)
    exampleSmooth exampleNonsingularT exampleSixTorsion hprin

end Nonvacuity

end WeierstrassCurve.Affine
