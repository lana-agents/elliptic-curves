/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import EllipticCurves.FunctionField.CoordinateRingUnits
import EllipticCurves.FunctionField.NthRootOfPullback
import EllipticCurves.FunctionField.TranslationDoublingCommGeneral
import EllipticCurves.FunctionField.WeilPairingAlternating
import EllipticCurves.FunctionField.WeilPairingTelescopeTwo
import EllipticCurves.Torsion.DoublingSurjective

/-!
# The alternating property of the Weil pairing at `n = 2` over an algebraically closed field

Silverman *AEC* III.8.1(d) proves `e_n(T, T) = 1` by running two products.  At `n = 2` the first is
the two-term divisor telescoping of `WeilPairingTelescopeTwo`, and the second is the two-factor
product `h := g_T · (τ_P∗ g_T)` for a point `P` with `[2]P = T`.  This file assembles them.

## The `τ_P` gate is not real at `n = 2`

`WeilPairingAlternating`'s docstring records that the second product "translates by a point `P` with
`[n]P = T`, which is **not `F`-rational in general**", and concludes that closing the alternating
property needs either a base change or a translation endomorphism along a non-rational point.  Over
an algebraically closed field that is simply false: `P` *is* rational, by the merged

```
Torsion/DoublingSurjective.lean
exists_nsmul_two_eq [IsAlgClosed F] [W.IsElliptic] (h2 : (2 : F) ≠ 0) (Q : W.Point) :
    ∃ P : W.Point, 2 • P = Q
```

and `translateEndo` expresses `τ_P` with no generalisation at all.  Neither a base change nor a
non-rational `translateEndo` is used below.

`P` is moreover automatically **affine**: if `P = O` then `T = [2]P = O`, contradicting the standing
hypothesis that `T` is an affine point.  So there is no degenerate case to split on, and
`exists_equation_nsmul_two_eq` hands the `W.Equation`-shaped datum `translateEndo` consumes straight
out of the `Point`-level surjectivity.

⚠️ This is special to `n = 2`.  The `i = 0` factor of the general product is `g_T` itself, so `τ_O`
never appears; for `n > 2` it does, unless the `i = 0` factor is again special-cased, and for some
`n` the point `[i]P` can be `O` for `0 < i < n` as well.  That is what `translatePointEndo`
(`TranslationPointEndomorphism`) is for, and it is not needed here.  The precise position — in
particular that the interior case cannot arise at `n = 3` — is in *Explicitly not here* below.

## The argument

Write `k := τ_P∗`, and let `f_T` be the telescoping function, `c` its telescoping constant and
`g_T` the rung-5 square root, so that

```
f_T · (τ_T∗ f_T) = c        and        c₀ · g_T ^ 2 = [2]∗ f_T.
```

The unit `u` of `F[W]` that `exists_smul_pow_eq_of_nsmul_divisor` produces is a **nonzero constant
`c₀ : F`** — that is `isUnit_iff_exists_eq_algebraMap` (`CoordinateRingUnits`), and it is what keeps
the bookkeeping below inside `F` instead of inside `F[W]`.  Then

```
c₀ ^ 2 · (g_T · k g_T) ^ 2 = (c₀ · g_T ^ 2) · k (c₀ · g_T ^ 2)      -- k fixes constants
                           = ([2]∗ f_T) · ([2]∗ (τ_T∗ f_T))         -- τ_P∗ ∘ [2]∗ = [2]∗ ∘ τ_T∗
                           = [2]∗ (f_T · τ_T∗ f_T) = [2]∗ c = c,
```

the middle step being the general doubling/translation commutation
`translateEndo_mulByTwoEndo_apply_general` (`TranslationDoublingCommGeneral`) — the merged
degenerate case `[2]T = O` is *not* enough, since here the right-hand translation does not collapse.

So `h := g_T · k g_T` has `2 · div h = 0`, hence `div h = 0`, hence `h` is a nonzero constant and is
fixed by `k`.  Expanding `k h = h` with `k ∘ k = τ_{2P}∗ = τ_T∗` gives
`(k g_T) · (τ_T∗ g_T) = g_T · (k g_T)`, and cancelling `k g_T ≠ 0` leaves `τ_T∗ g_T = g_T` — which
is `weilPairingElt_eq_one_iff_translateEndo_fixed`, i.e. `e_2(T, T) = 1`.

## Main results

* `exists_equation_nsmul_two_eq` — the `Point`-level surjectivity repackaged as the affine datum
  `translateEndo` consumes: over `F̄` there are `xP yP` and `hP : W.Equation xP yP` with
  `[2] (torsionPoint hP) = T`;
* **`translateEndo_eq_self_of_mul_algebraMap_sq_eq`** — the core, and the only place any of the
  computation happens.  It is stated over an **arbitrary** field, with the telescoping constant, the
  square root and the doubling relation all as hypotheses, so that the `[3]` analogue can reuse it
  verbatim;
* **`exists_weilPairingElt_self_eq_one_of_algClosed_two`** — `e_2(T, T) = 1` over `F̄`.

## Which hypotheses are load-bearing

* `[IsAlgClosed F]` — in exactly one place, `exists_equation_nsmul_two_eq`, to produce `P`.  The
  core lemma does not have it.
* `(2 : F) ≠ 0` — for `mulByTwoEndo` and for `exists_nsmul_two_eq`.
* `[W.IsElliptic]` — the standing hypothesis of the whole divisor calculus.
* `[IsDedekindDomain W.CoordinateRing]` — a binder in the variable block below, so `#check` does
  show it on the headline, but it is *not* a real hypothesis and is not `#396`: it is a **global
  instance** for `[W.IsElliptic]` over an **arbitrary** field (`CoordinateRingNormalGeneral`), so
  instance search supplies it and no caller ever has to.  Deleting the binder would be a no-op
  tidy-up, not a generalisation.
* `hprin`, the **`#418` datum**: principality of `[2]∗((T) − (O))`, in the exact shape
  `exists_gS_two` (`NthRootOfPullback`) takes it, so that the two compose.  It is *not* discharged
  here — but it is discharged over an algebraically closed base field in
  `EllipticCurves.FunctionField.PullbackPrincipalityTwo`, and
  `EllipticCurves.FunctionField.WeilPairingAlternatingTwoAlgClosed` is the resulting hypothesis-free
  form of the headline below.  The statement here keeps `hprin`, so that a general-field discharge
  has somewhere to land.

Because `P` is produced over `F̄`, the conclusion is a statement about `F̄`; obtaining it over a
general `F` needs the function-field base-change layer, which is deliberately deferred (`#692`) and
is not built here.

## Explicitly not here

* `n = 3` or general `n` — but **not** for the reason this list gave when the file was written.
  The `n = 3` producer exists: `nsmul_three_surjective` (`Torsion/TriplingSurjective.lean`, `#690`)
  supplies a point `P` with `[3]P = T`, and it costs no more hypotheses than the `n = 2` one, since
  `#690` found that `(3 : F) ≠ 0` is not needed — only `h2 : (2 : F) ≠ 0`, exactly as
  `exists_nsmul_two_eq` above.  Step B at `n = 3` is merged as well
  (`WeilPairingTelescopeThree`, `#712`).  What is genuinely left at `n = 3` is step A, the general
  commutation `τ_P∗ ∘ [3]∗ = [3]∗ ∘ τ_T∗` for `[3]P = T` (`#713`), plus `hprin` — the same `#418`
  gate as at `n = 2`, unchanged and blocking both.
* The `τ_O` half of that sentence, stated precisely, because it is easy to over-read.  In the
  second product `∏_i τ_{[i]P}∗ g_T` the `i = 0` factor is `τ_O`, and that alone is what
  `translatePointEndo` (`#689`) is for; whether it is *needed* depends only on whether the product
  is written uniformly over `Finset.range n` or with the `i = 0` factor special-cased as `g_T`, the
  way the ⚠️ above does it at `n = 2`.  An **interior** `[i]P = O` with `0 < i < n` is a different
  matter, and it needs `T` to have order a proper divisor of `n` (`n = 6`, `ord P = 4` is the
  standard example, recorded in `TranslationPointEndomorphism`).  So it **cannot occur at `n = 3`**:
  `T` is affine and `3` is prime, so `ord T = 3`, whence `3 ∣ ord P` and `ord P ≥ 3 > i`.
* Discharging `#418`, or any base change of function fields.
* Antisymmetry `e_n(T, S) = e_n(S, T)⁻¹` — but **not** because divisor-slot bilinearity is
  unavailable.  Both it and the antisymmetry corollary are merged, as `WeilPairingAntisymmetric`
  (`#723`), on `[Field F]` and `[W.IsElliptic]` alone.  What that file still carries is the
  *production* of the product relation `g_{S ⊕ T} = g_S · g_T · w`, as the hypothesis `hprod`
  — ⚠️ which is **rung 5 only, never rung 4**, and is discharged from rung-5 data in
  `EllipticCurves.FunctionField.WeilPairingProductRelation` (`#845`); the correction factor `w` is
  invisible to `e_n(·, T)`, so nothing downstream of `hprod` costs anything.  Note also that
  the derivation consumes `e_n(T, T) = 1` at
  **three** points, `S`, `T` and `S ⊕ T` — i.e. the theorem below, `hprin` and all, applied three
  times.  So end-to-end antisymmetry is neither more nor less gated than this file already is: the
  gate did not move, and `#723` added no new one.

## References

* [J. Silverman, *The arithmetic of elliptic curves*][silverman2009], III.8.1(d).
-/

open Polynomial IsDedekindDomain

namespace WeierstrassCurve.Affine

open CoordinateRing

variable {F : Type*} [Field F] {W : Affine F} [W.IsElliptic]
  [IsDedekindDomain W.CoordinateRing] {x₂ y₂ : F}

/-! ### A rational point `P` with `[2]P = T` -/

omit [IsDedekindDomain W.CoordinateRing] in
open Classical in
/-- **Over `F̄` the halving point of an affine point is affine and rational.**  The merged
`exists_nsmul_two_eq` gives `P : W.Point` with `[2]P = T`; since `T` is affine, `P ≠ O`, so `P` is
`Point.some xP yP _` and carries a `W.Equation` — which is the datum `translateEndo` is indexed by.

This is the whole of the `[IsAlgClosed F]` content of this file. -/
theorem exists_equation_nsmul_two_eq [IsAlgClosed F] (h2 : (2 : F) ≠ 0)
    (h : W.Nonsingular x₂ y₂) :
    ∃ (xP yP : F) (hP : W.Equation xP yP),
      torsionPoint hP + torsionPoint hP = Point.some x₂ y₂ h := by
  obtain ⟨P, hP⟩ := exists_nsmul_two_eq h2 (Point.some x₂ y₂ h)
  rcases P with _ | ⟨xP, yP, hns⟩
  · have hz : (Point.zero : W.Point) = 0 := rfl
    rw [hz, smul_zero] at hP
    exact absurd hP.symm (Point.some_ne_zero _)
  · refine ⟨xP, yP, hns.left, ?_⟩
    rw [← two_nsmul]
    exact hP

/-! ### The core computation -/

open Classical in
/-- **The second product of Silverman III.8.1(d), at `n = 2`.**

Given the telescoping constant `f · (τ_T∗ f) = c` and a square root `c₀ · g ^ 2 = [2]∗ f`, together
with an affine `P` whose double is `T`, the translate `τ_T∗` fixes `g`.

Every hypothesis is explicit and the statement is over an arbitrary field: no `[IsAlgClosed F]`, no
`#418`.  Those enter only in the assembly below, which is what makes this lemma the reusable piece —
the `[3]` version differs only in `mulByTwoEndo`, the exponent, and the number of factors. -/
theorem translateEndo_eq_self_of_mul_algebraMap_sq_eq (h2 : (2 : F) ≠ 0) {xP yP : F}
    (hP : W.Equation xP yP) (h₂ : W.Equation x₂ y₂)
    (hdouble : translatePoint hP + translatePoint hP = translatePoint h₂)
    {f g : W.FunctionField} (hg : g ≠ 0) {c c₀ : F} (hc : c ≠ 0) (hc₀ : c₀ ≠ 0)
    (htel : f * translateEndo h₂ f = algebraMap F W.FunctionField c)
    (hsq : algebraMap F W.FunctionField c₀ * g ^ 2 = mulByTwoEndo h2 f) :
    translateEndo h₂ g = g := by
  have hkg : translateEndo hP g ≠ 0 := fun hz =>
    hg ((translateEndo hP).injective (by rw [hz, map_zero]))
  have hprod : g * translateEndo hP g ≠ 0 := mul_ne_zero hg hkg
  -- The translate of the square-root relation, through the doubling/translation commutation.
  have hsq' : algebraMap F W.FunctionField c₀ * translateEndo hP g ^ 2
      = mulByTwoEndo h2 (translateEndo h₂ f) := by
    have h1 := congrArg (translateEndo hP) hsq
    rwa [map_mul, map_pow, translateEndo_algebraMap_base,
      translateEndo_mulByTwoEndo_apply_general hP h₂ h2 hdouble] at h1
  -- The square of `h := g · τ_P∗ g` is the nonzero constant `c / c₀ ^ 2`.
  have hkey : algebraMap F W.FunctionField (c₀ ^ 2) * (g * translateEndo hP g) ^ 2
      = algebraMap F W.FunctionField c := by
    calc algebraMap F W.FunctionField (c₀ ^ 2) * (g * translateEndo hP g) ^ 2
        = (algebraMap F W.FunctionField c₀ * g ^ 2)
            * (algebraMap F W.FunctionField c₀ * translateEndo hP g ^ 2) := by
          rw [map_pow]; ring
      _ = mulByTwoEndo h2 f * mulByTwoEndo h2 (translateEndo h₂ f) := by rw [hsq, hsq']
      _ = mulByTwoEndo h2 (f * translateEndo h₂ f) := (map_mul _ _ _).symm
      _ = algebraMap F W.FunctionField c := by rw [htel, mulByTwoEndo_algebraMap_base]
  -- Hence its projective divisor is trivial, so it is itself a nonzero constant.
  have hc₀' : algebraMap F W.FunctionField (c₀ ^ 2) ≠ 0 :=
    (map_ne_zero_iff _ (algebraMap F W.FunctionField).injective).mpr (pow_ne_zero 2 hc₀)
  have hdiv : (2 : ℕ) • divisorProj W (g * translateEndo hP g) = 0 := by
    have hcongr := congrArg (divisorProj W) hkey
    rwa [divisorProj_mul hc₀' (pow_ne_zero 2 hprod),
      divisorProj_algebraMap_base (pow_ne_zero 2 hc₀), divisorProj_pow,
      divisorProj_algebraMap_base hc, zero_add] at hcongr
  have hzero : divisorProj W (g * translateEndo hP g) = 0 := by
    ext p
    have hp : (2 : ℤ) * divisorProj W (g * translateEndo hP g) p = 0 := by
      simpa [nsmul_eq_mul] using congrArg (fun D : ProjPoint W →₀ ℤ => D p) hdiv
    simp only [Finsupp.coe_zero, Pi.zero_apply]
    omega
  obtain ⟨c₁, -, hconst⟩ := (divisorProj_eq_zero_iff hprod).mp hzero
  -- A constant is fixed by `τ_P∗`; expanding that with `τ_P∗ ∘ τ_P∗ = τ_T∗` finishes.
  have hfix : translateEndo hP g * translateEndo h₂ g = g * translateEndo hP g := by
    have hcomp : translateEndo hP (translateEndo hP g) = translateEndo h₂ g :=
      congr($(translateEndo_comp hP hP h₂ hdouble) g)
    have h1 : translateEndo hP (g * translateEndo hP g) = g * translateEndo hP g := by
      rw [hconst, translateEndo_algebraMap_base]
    rwa [map_mul, hcomp] at h1
  refine mul_left_cancel₀ hkg ?_
  rw [hfix, mul_comm]

/-! ### The affine divisor of a function with a prescribed projective divisor -/

omit [W.IsElliptic] in
/-- The affine divisor read off a projective one of the shape `n(T) − n(O)`.  `divisorProj` is
`divisor` on the affine chart (`divisorProj_apply_some`), and the point at infinity contributes
nothing there. -/
lemma divisor_eq_single_of_divisorProj_eq_single_sub_single {f : W.FunctionField}
    {v : HeightOneSpectrum W.CoordinateRing} {n : ℤ}
    (hdiv : divisorProj W f
      = Finsupp.single (some v) n - Finsupp.single (none : ProjPoint W) n) :
    divisor W f = Finsupp.single v n := by
  classical
  ext w
  have hw := congrArg (fun D => D (some w)) hdiv
  simp only [Finsupp.coe_sub, Pi.sub_apply, divisorProj_apply_some, Finsupp.single_apply,
    reduceCtorEq, if_false, sub_zero, Option.some.injEq] at hw
  rw [divisor_apply, hw, Finsupp.single_apply]

/-! ### The alternating property -/

open Classical in
/-- **`e_2(T, T) = 1` over an algebraically closed field.**

For an affine `2`-torsion point `T = (x₂, y₂)` on `W ⁄ F̄` and the `#418` datum `hprin` — the
principality of the `2`-divisible divisor `div ([2]∗ f_T)`, in the exact shape `exists_gS_two` takes
it — there are a principal function `f_T` with `div f_T = 2(T) − 2(O)` and a square root `g_T` of
`[2]∗ f_T` (up to a unit of `F[W]`) such that `τ_T∗ g_T = g_T`, hence `e_2(T, T) = 1`.

`hprin` is the only gated hypothesis; everything else is discharged here.  See the module docstring
for why the point `P` with `[2]P = T` costs nothing over `F̄`. -/
theorem exists_weilPairingElt_self_eq_one_of_algClosed_two [IsAlgClosed F] (h2 : (2 : F) ≠ 0)
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
  obtain ⟨f, hf, hdivproj, c, hc, htel⟩ := exists_mul_translateEndo_eq_algebraMap h htors
  -- The `#418` datum, at the telescoping function.
  obtain ⟨g, hg, hgdiv⟩ :=
    hprin f hf (divisor_eq_single_of_divisorProj_eq_single_sub_single hdivproj)
  have hfne : mulByTwoEndo h2 f ≠ 0 := fun hz =>
    hf ((mulByTwoEndo h2).injective (by rw [hz, map_zero]))
  obtain ⟨u, hu⟩ := exists_smul_pow_eq_of_nsmul_divisor hfne hg hgdiv
  -- The unit of `F[W]` is a nonzero constant, so the square-root relation lives over `F`.
  obtain ⟨c₀, hc₀, hueq⟩ := isUnit_iff_exists_eq_algebraMap.mp u.isUnit
  have hsq : algebraMap F W.FunctionField c₀ * g ^ 2 = mulByTwoEndo h2 f := by
    rw [← hu, Algebra.smul_def, hueq, ← IsScalarTower.algebraMap_apply]
  obtain ⟨xP, yP, hP, hdouble⟩ := exists_equation_nsmul_two_eq h2 h
  have htinv : translateEndo h.left g = g :=
    translateEndo_eq_self_of_mul_algebraMap_sq_eq h2 hP h.left
      (translatePoint_add hP hP h.left hdouble) hg hc hc₀ htel hsq
  exact ⟨f, hf, hdivproj, g, hg, ⟨u, hu⟩, htinv,
    weilPairingElt_self_of_translateEndo_fixed h.left hg htinv⟩

/-! ### Non-vacuity

The headline as stated here cannot be fully instantiated on a concrete curve, for one reason and
one only: `hprin` is a hypothesis, and it is `#418`.  What *can* be certified, and is below, is
that every hypothesis this file adds on top of it is simultaneously satisfiable — over an
algebraically closed field, which is the new one.  On `y² = x³ − x` over `AlgebraicClosure ℚ` the
point `T = (0, 0)` is affine, nonsingular and `2`-torsion, `(2 : K) ≠ 0`, and
`exists_equation_nsmul_two_eq` really does produce an **affine** `P` with `[2]P = T`.  In particular
the `[IsAlgClosed F]` step of the argument is not vacuous, which is the claim this file rests on.

For the *fully* instantiated certificate see
`EllipticCurves.FunctionField.WeilPairingAlternatingTwoAlgClosed`, which discharges `hprin` over an
algebraically closed base field and certifies the resulting hypothesis-free headline on this same
curve.  ⚠️ `[IsDedekindDomain W.CoordinateRing]` is not a second obstruction and never was: it is a
global instance for `[W.IsElliptic]` over an arbitrary field (`CoordinateRingNormalGeneral`). -/

section Nonvacuity

/-- An algebraically closed field of characteristic zero. -/
private abbrev exampleField : Type := AlgebraicClosure ℚ

/-- The curve `y² = x³ − x` over `AlgebraicClosure ℚ`, of discriminant `64`. -/
private noncomputable def exampleCurve : Affine exampleField := ⟨0, 0, 0, -1, 0⟩

private instance : exampleCurve.IsElliptic := by
  rw [WeierstrassCurve.isElliptic_iff, isUnit_iff_ne_zero]
  norm_num [exampleCurve, WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈]

/-- `T = (0, 0)` lies on `y² = x³ − x` and is nonsingular. -/
private lemma exampleNonsingular : exampleCurve.Nonsingular 0 0 :=
  exampleCurve.equation_iff_nonsingular.mp (by
    norm_num [exampleCurve, WeierstrassCurve.Affine.equation_iff])

open Classical in
/-- `T = (0, 0)` is `2`-torsion: `2y + a₁x + a₃ = 0` reads `0 = 0`.  So the `htors` hypothesis of
the headline is satisfiable on the same curve. -/
private lemma exampleTorsion :
    Point.some (0 : exampleField) 0 exampleNonsingular ∈ exampleCurve.torsion 2 :=
  (mem_torsion_two_some_iff exampleNonsingular).mpr (by norm_num [exampleCurve])

open Classical in
/-- The halving point exists and is affine. -/
example : ∃ (xP yP : exampleField) (hP : exampleCurve.Equation xP yP),
    torsionPoint hP + torsionPoint hP = Point.some (0 : exampleField) 0 exampleNonsingular :=
  exists_equation_nsmul_two_eq (by norm_num) exampleNonsingular

end Nonvacuity

end WeierstrassCurve.Affine
