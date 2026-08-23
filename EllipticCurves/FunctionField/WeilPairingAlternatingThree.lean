/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import EllipticCurves.FunctionField.CoordinateRingUnits
import EllipticCurves.FunctionField.NthRootOfPullback
import EllipticCurves.FunctionField.TranslationTriplingCommGeneral
import EllipticCurves.FunctionField.WeilPairingAlternatingTwo
import EllipticCurves.FunctionField.WeilPairingBilinearBaseField
import EllipticCurves.FunctionField.WeilPairingTelescopeThree
import EllipticCurves.Torsion.TriplingSurjective

/-!
# The alternating property of the Weil pairing at `n = 3` over an algebraically closed field

Silverman *AEC* III.8.1(d) proves `e_n(T, T) = 1` by running two products.  At `n = 3` the first is
the three-term divisor telescoping of `WeilPairingTelescopeThree`, and the second is the
three-factor product `h := g_T · (τ_P∗ g_T) · (τ_Q∗ g_T)` for a point `P` with `[3]P = T` and
`Q := [2]P`.  This file assembles them, and is the `n = 3` mirror of `WeilPairingAlternatingTwo`.

## Everything except `hprin` is merged

| what | where |
| --- | --- |
| step B, `f · τ_T∗f · τ_{−T}∗f = c` | `exists_mul_translateEndo_mul_translateEndo_eq_algebraMap` |
| | (`WeilPairingTelescopeThree`) |
| step A, `τ_P∗ ∘ [3]∗ = [3]∗ ∘ τ_T∗` | `translateEndo_mulByThreeEndo_apply_general` |
| | (`TranslationTriplingCommGeneral`) |
| projective ⟹ affine divisor | `divisor_eq_single_of_divisorProj_eq_single_sub_single` |
| | (`WeilPairingAlternatingTwo`) |
| the producer over `F̄` | `exists_nsmul_three_eq` (`Torsion/TriplingSurjective`) |
| `n`-th root from the divisor | `exists_smul_pow_eq_of_nsmul_divisor` (`NthRootOfPullback`) |
| unit of `F[W]` ⟹ constant | `isUnit_iff_exists_eq_algebraMap` (`CoordinateRingUnits`) |
| `τ_P ∘ τ_R = τ_{P ⊕ R}` | `translateEndo_comp` (`TranslationComposition`) |
| base-field ⟹ `F(W)` relation | `translatePoint_add` (`WeilPairingBilinearBaseField`) |
| `τ_T∗ g = g ⟹ e_n(T, T) = 1` | `weilPairingElt_self_of_translateEndo_fixed` |
| | (`WeilPairingAlternating`) |

The affine-divisor bridge is reused rather than reproved: it is stated for an arbitrary `n : ℤ`, so
the `n = 2` file's version serves verbatim.  `hprin`, the `#418` datum, is kept in the exact shape
`exists_gS_three` (`NthRootOfPullback`) takes it, so that the two compose.

## The argument

Write `f` for the telescoping function, `c` for its telescoping constant and `g` for the rung-5
cube root, so that

```
f · (τ_T∗ f) · (τ_{−T}∗ f) = c        and        c₀ · g ^ 3 = [3]∗ f,
```

the unit produced by `exists_smul_pow_eq_of_nsmul_divisor` being a **nonzero constant `c₀ : F`**
(`isUnit_iff_exists_eq_algebraMap`), which is what keeps the bookkeeping inside `F`.  Translating
the second relation by `P` and by `Q = [2]P` and using step A at the two group relations
`[3]P = T` and `[3]Q = −T`,

```
c₀ · (τ_P∗ g) ^ 3 = [3]∗ (τ_T∗ f)        and        c₀ · (τ_Q∗ g) ^ 3 = [3]∗ (τ_{−T}∗ f),
```

so with `h := g · (τ_P∗ g) · (τ_Q∗ g)` the product of the three gives
`c₀ ^ 3 · h ^ 3 = [3]∗ (f · τ_T∗f · τ_{−T}∗f) = [3]∗ c = c`.  Hence `3 • div h = 0`, hence
`div h = 0`, hence `h` is a nonzero constant and is fixed by `τ_P∗`.  Expanding that fixedness with
`τ_P∗ ∘ τ_P∗ = τ_Q∗` and `τ_P∗ ∘ τ_Q∗ = τ_T∗`,

```
τ_P∗ h = (τ_P∗ g) · (τ_Q∗ g) · (τ_T∗ g)        and        h = g · (τ_P∗ g) · (τ_Q∗ g),
```

and cancelling the common factor `(τ_P∗ g) · (τ_Q∗ g) ≠ 0` leaves `τ_T∗ g = g`, which
`weilPairingElt_self_of_translateEndo_fixed` turns into `e_3(T, T) = 1`.

## Three ways this differs from `n = 2`, none of them cosmetic

1. **The second translation point is `Q = [2]P`, and the target of step A there is `−T`, not `T`.**
   `[3]Q = [6]P = [2]T = −T`, using `[3]T = O`.  Writing `τ_Q∗ ([3]∗ f) = [3]∗ (τ_T∗ f)` instead
   would be a *false* statement.  Correspondingly the third factor of the telescoping is the
   translate by `−T`, which is exactly the shape `WeilPairingTelescopeThree` produces.
2. **`Q` is affine, and this needs an argument.**  `translateEndo` is indexed by a `W.Equation`, so
   `τ_Q` needs `Q ≠ O`.  If `[2]P = O` then `T = [3]P = P`, so `T + T = O`; with `[3]T = O` that
   gives `T = [3]T − [2]T = O`, contradicting `T` affine.  **`translatePointEndo` (`#689`) is
   *not* used in this file**, and no interior `[i]P = O` can occur at `n = 3`: `T` affine and `3`
   prime give `ord T = 3`, and `[3]P = T` gives `ord T ∣ ord P`, so `ord P ≥ 3 > i` for `0 < i < 3`.
   Interior vanishing needs `ord T` to be a *proper* divisor of `n`; the smallest `n` where it
   happens is `n = 6` with `ord P = 4`, the example recorded in `TranslationPointEndomorphism`.
3. **The cancellation comes off a two-factor product.**  `#688` cancels the single factor `τ_P∗ g`;
   here both `τ_P∗ g` and `τ_Q∗ g` have to go, which is one `mul_left_cancel₀` at the product
   `(τ_P∗ g) · (τ_Q∗ g)` rather than two nested ones.

## Main results

* `exists_equation_nsmul_three_eq` — the `Point`-level surjectivity repackaged as the **pair** of
  affine data `translateEndo` consumes: over `F̄` there are `P` and `Q` with `[2]P = Q` and
  `P ⊕ Q = T`, both carrying a `W.Equation`.  This is the whole `[IsAlgClosed F]` content;
* **`translateEndo_eq_self_of_mul_algebraMap_cube_eq`** — the core, where all the computation
  happens.  It is stated over an **arbitrary** field with the telescoping constant, the cube root
  and the two group relations as explicit hypotheses: no `[IsAlgClosed F]`, no `#418`.  Keeping the
  `n = 2` analogue ungated is what made that file reusable, and the same is done here;
* **`exists_weilPairingElt_self_eq_one_of_algClosed_three`** — `e_3(T, T) = 1` over `F̄`.

## Which hypotheses are load-bearing

* `[IsAlgClosed F]` — in exactly one place, `exists_equation_nsmul_three_eq`, to produce `P`.  The
  core lemma does not have it.
* `(2 : F) ≠ 0` and `(3 : F) ≠ 0` — for `mulByThreeEndo`, whose construction runs through the
  generic-point tripling formula.  Only `h2` is needed for `exists_nsmul_three_eq`, which `#690`
  proved without `h3`.
* `[W.IsElliptic]` — the standing hypothesis of the whole divisor calculus.
* `[IsDedekindDomain W.CoordinateRing]` — a binder in the variable block below, so `#check` does
  show it on the headline, but it is *not* a real hypothesis and is not open: it is a **global
  instance** for `[W.IsElliptic]` over an **arbitrary** field
  (`EllipticCurves.FunctionField.CoordinateRingNormalGeneral`), so instance search supplies it and
  no caller ever has to.
* `hprin`, the **`#418` datum**: principality of `[3]∗((T) − (O))`.  It is *not* discharged here.
  ⚠️ It is discharged **elsewhere**, over an algebraically closed base field:
  `exists_gS_three_of_isAlgClosed`
  (`EllipticCurves.FunctionField.PullbackPrincipalityThree`).  So a caller over `F̄` need not
  supply it, and the headline below is instantiable — see the Non-vacuity section.

Because `P` is produced over `F̄`, the conclusion is a statement about `F̄`; obtaining it over a
general `F` needs the function-field base-change layer, which is deliberately deferred (`#692`).

## Explicitly not here

* General `n`.  The group-theoretic half of the route is uniform in `n`, but the input it consumes
  — `mulByNEndo` and the generic-point correspondence — exists only at `n = 2` (`GenericDoubling`)
  and `n = 3` (`GenericTripling`); a uniform `n` is gated on the `ωₙ` crux (`#403`/`#404`).
* Discharging `#418`, or any base change of function fields (`#692`).
* Antisymmetry `e_n(T, S) = e_n(S, T)⁻¹` — but **not** because divisor-slot bilinearity is
  unavailable.  Both it and the antisymmetry corollary are merged, as `WeilPairingAntisymmetric`
  (`#723`), on `[Field F]` and `[W.IsElliptic]` alone.  What that file still carries is the
  *production* of the product relation `g_{S ⊕ T} = g_S · g_T · w`, as the hypothesis `hprod`
  — ⚠️ **rung 5 only, never rung 4**, and discharged from rung-5 data in
  `EllipticCurves.FunctionField.WeilPairingProductRelation` (`#845`).  Its derivation consumes
  `e_n(T, T) = 1` at **three** points, `S`, `T`
  and `S ⊕ T` — i.e. the theorem below, `hprin` and all, applied three times — so end-to-end
  antisymmetry is neither more nor less gated than this file already is.

## References

* [J. Silverman, *The arithmetic of elliptic curves*][silverman2009], III.8.1(d).
-/

open Polynomial IsDedekindDomain

namespace WeierstrassCurve.Affine

open CoordinateRing

variable {F : Type*} [Field F] {W : Affine F} [W.IsElliptic]
  [IsDedekindDomain W.CoordinateRing] {x₃ y₃ : F}

/-! ### The rational points `P` and `Q = [2]P` with `[3]P = T` -/

omit [W.IsElliptic] [IsDedekindDomain W.CoordinateRing] in
open Classical in
/-- The `∈ W.torsion 3` membership as the three-term group relation `T ⊕ T ⊕ T = O`.  Both the
producer and the assembly need it in that shape; `WeilPairingTelescopeThree` and
`TranslationTorsionMap` unfold `(3 : ℕ) • T = 0` by hand in the same way. -/
private lemma add_add_self_eq_zero_of_mem_torsion_three (h : W.Nonsingular x₃ y₃)
    (htors : Point.some x₃ y₃ h ∈ W.torsion 3) :
    Point.some x₃ y₃ h + Point.some x₃ y₃ h + Point.some x₃ y₃ h = 0 := by
  have hn := mem_torsion_iff.mp htors
  rwa [show (3 : ℕ) = 2 + 1 from rfl, add_smul, two_nsmul, one_nsmul] at hn

omit [IsDedekindDomain W.CoordinateRing] in
open Classical in
/-- **Over `F̄` a third of an affine `3`-torsion point is affine, and so is its double.**  The
merged `exists_nsmul_three_eq` gives `P : W.Point` with `[3]P = T`; the file needs `W.Equation`
data for `P` *and* for `Q := [2]P`, since it translates by both.

Both are nonzero.  `P = O` would force `T = O`.  `Q = O` would force `T = [3]P = P`, hence
`T + T = O`; combined with `[3]T = O` that gives `T = O`, contradicting `T` affine.  So no
`τ_O`-tolerant translation wrapper is needed at `n = 3` — see the module docstring.

This is the whole of the `[IsAlgClosed F]` content of this file. -/
theorem exists_equation_nsmul_three_eq [IsAlgClosed F] (h2 : (2 : F) ≠ 0)
    (h : W.Nonsingular x₃ y₃) (htors : Point.some x₃ y₃ h ∈ W.torsion 3) :
    ∃ (xP yP xQ yQ : F) (hP : W.Equation xP yP) (hQ : W.Equation xQ yQ),
      torsionPoint hP + torsionPoint hP = torsionPoint hQ ∧
        torsionPoint hP + torsionPoint hQ = Point.some x₃ y₃ h := by
  -- Every nonzero point of `W.Point` carries the `W.Equation` datum, with `torsionPoint` as the
  -- inverse of that repackaging.
  have hsome : ∀ R : W.Point, R ≠ 0 →
      ∃ (xR yR : F) (hR : W.Equation xR yR), torsionPoint hR = R := by
    rintro (_ | ⟨x, y, hns⟩) hR
    · exact absurd rfl hR
    · exact ⟨x, y, hns.left, rfl⟩
  obtain ⟨P, hP3⟩ := exists_nsmul_three_eq h2 (Point.some x₃ y₃ h)
  have h3 : P + P + P = Point.some x₃ y₃ h := by
    rwa [show (3 : ℕ) = 2 + 1 from rfl, add_smul, two_nsmul, one_nsmul] at hP3
  have hPne : P ≠ 0 := by
    rintro rfl
    rw [add_zero, add_zero] at h3
    exact (Point.some_ne_zero _) h3.symm
  have hQne : P + P ≠ 0 := by
    intro hz
    have hT : Point.some x₃ y₃ h = P := by rw [← h3, hz, zero_add]
    have h3T := add_add_self_eq_zero_of_mem_torsion_three h htors
    rw [hT, hz, zero_add] at h3T
    exact hPne h3T
  obtain ⟨xP, yP, hP, hPeq⟩ := hsome P hPne
  obtain ⟨xQ, yQ, hQ, hQeq⟩ := hsome (P + P) hQne
  exact ⟨xP, yP, xQ, yQ, hP, hQ, by rw [hPeq, hQeq], by rw [hPeq, hQeq, ← h3]; abel⟩

/-! ### The core computation -/

open Classical in
/-- **The second product of Silverman III.8.1(d), at `n = 3`.**

Given the telescoping constant `f · (τ_T∗ f) · (τ_{−T}∗ f) = c`, a cube root `c₀ · g ^ 3 = [3]∗ f`,
and affine points `P`, `Q` with `[2]P = Q` and `P ⊕ Q = T` (so `[3]P = T`), the translate `τ_T∗`
fixes `g`.

Every hypothesis is explicit and the statement is over an arbitrary field: no `[IsAlgClosed F]`,
no `#418`.  Those enter only in the assembly below, which is what makes this lemma the reusable
piece — exactly as at `n = 2`. -/
theorem translateEndo_eq_self_of_mul_algebraMap_cube_eq (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0)
    {xP yP xQ yQ : F} (hP : W.Equation xP yP) (hQ : W.Equation xQ yQ) (h₃ : W.Equation x₃ y₃)
    (hdouble : translatePoint hP + translatePoint hP = translatePoint hQ)
    (hsum : translatePoint hP + translatePoint hQ = translatePoint h₃)
    (htors : translatePoint h₃ + translatePoint h₃ + translatePoint h₃ = 0)
    {f g : W.FunctionField} (hg : g ≠ 0) {c c₀ : F} (hc : c ≠ 0) (hc₀ : c₀ ≠ 0)
    (htel : f * translateEndo h₃ f * translateEndo ((W.equation_neg x₃ y₃).mpr h₃) f
      = algebraMap F W.FunctionField c)
    (hcube : algebraMap F W.FunctionField c₀ * g ^ 3 = mulByThreeEndo h2 h3 f) :
    translateEndo h₃ g = g := by
  -- The two group relations at which the commutation is invoked.
  have htripleP :
      translatePoint hP + translatePoint hP + translatePoint hP = translatePoint h₃ := by
    rw [hdouble, add_comm]; exact hsum
  have htripleQ : translatePoint hQ + translatePoint hQ + translatePoint hQ
      = translatePoint ((W.equation_neg x₃ y₃).mpr h₃) := by
    -- `[3]Q = [6]P = [2]T`, and `[3]T = O` turns `[2]T` into `−T`.
    have h6 : translatePoint hQ + translatePoint hQ + translatePoint hQ
        = translatePoint h₃ + translatePoint h₃ := by
      rw [← hdouble, ← htripleP]; abel
    rw [h6, add_eq_zero_iff_eq_neg.mp htors, translatePoint_neg h₃]
  have hkgP : translateEndo hP g ≠ 0 := fun hz =>
    hg ((translateEndo hP).injective (by rw [hz, map_zero]))
  have hkgQ : translateEndo hQ g ≠ 0 := fun hz =>
    hg ((translateEndo hQ).injective (by rw [hz, map_zero]))
  have hprod : g * translateEndo hP g * translateEndo hQ g ≠ 0 :=
    mul_ne_zero (mul_ne_zero hg hkgP) hkgQ
  -- The two translates of the cube-root relation, through the tripling/translation commutation.
  have hcubeP : algebraMap F W.FunctionField c₀ * translateEndo hP g ^ 3
      = mulByThreeEndo h2 h3 (translateEndo h₃ f) := by
    have h1 := congrArg (translateEndo hP) hcube
    rwa [map_mul, map_pow, translateEndo_algebraMap_base,
      translateEndo_mulByThreeEndo_apply_general hP h₃ h2 h3 htripleP] at h1
  have hcubeQ : algebraMap F W.FunctionField c₀ * translateEndo hQ g ^ 3
      = mulByThreeEndo h2 h3 (translateEndo ((W.equation_neg x₃ y₃).mpr h₃) f) := by
    have h1 := congrArg (translateEndo hQ) hcube
    rwa [map_mul, map_pow, translateEndo_algebraMap_base,
      translateEndo_mulByThreeEndo_apply_general hQ ((W.equation_neg x₃ y₃).mpr h₃) h2 h3
        htripleQ] at h1
  -- The cube of `h := g · τ_P∗ g · τ_Q∗ g` is the nonzero constant `c / c₀ ^ 3`.
  have hkey : algebraMap F W.FunctionField (c₀ ^ 3)
      * (g * translateEndo hP g * translateEndo hQ g) ^ 3
        = algebraMap F W.FunctionField c := by
    calc algebraMap F W.FunctionField (c₀ ^ 3)
          * (g * translateEndo hP g * translateEndo hQ g) ^ 3
        = (algebraMap F W.FunctionField c₀ * g ^ 3)
            * (algebraMap F W.FunctionField c₀ * translateEndo hP g ^ 3)
            * (algebraMap F W.FunctionField c₀ * translateEndo hQ g ^ 3) := by
          rw [map_pow]; ring
      _ = mulByThreeEndo h2 h3 f * mulByThreeEndo h2 h3 (translateEndo h₃ f)
            * mulByThreeEndo h2 h3
              (translateEndo ((W.equation_neg x₃ y₃).mpr h₃) f) := by
          rw [hcube, hcubeP, hcubeQ]
      _ = mulByThreeEndo h2 h3 (f * translateEndo h₃ f
            * translateEndo ((W.equation_neg x₃ y₃).mpr h₃) f) := by rw [map_mul, map_mul]
      _ = algebraMap F W.FunctionField c := by rw [htel, mulByThreeEndo_algebraMap_base]
  -- Hence its projective divisor is trivial, so it is itself a nonzero constant.
  have hc₀' : algebraMap F W.FunctionField (c₀ ^ 3) ≠ 0 :=
    (map_ne_zero_iff _ (algebraMap F W.FunctionField).injective).mpr (pow_ne_zero 3 hc₀)
  have hdiv : (3 : ℕ) • divisorProj W (g * translateEndo hP g * translateEndo hQ g) = 0 := by
    have hcongr := congrArg (divisorProj W) hkey
    rwa [divisorProj_mul hc₀' (pow_ne_zero 3 hprod),
      divisorProj_algebraMap_base (pow_ne_zero 3 hc₀), divisorProj_pow,
      divisorProj_algebraMap_base hc, zero_add] at hcongr
  have hzero : divisorProj W (g * translateEndo hP g * translateEndo hQ g) = 0 := by
    ext p
    have hp : (3 : ℤ) * divisorProj W (g * translateEndo hP g * translateEndo hQ g) p = 0 := by
      simpa [nsmul_eq_mul] using congrArg (fun D : ProjPoint W →₀ ℤ => D p) hdiv
    simp only [Finsupp.coe_zero, Pi.zero_apply]
    omega
  obtain ⟨c₁, -, hconst⟩ := (divisorProj_eq_zero_iff hprod).mp hzero
  -- A constant is fixed by `τ_P∗`; expanding that with `τ_P∗ ∘ τ_P∗ = τ_Q∗` and
  -- `τ_P∗ ∘ τ_Q∗ = τ_T∗` finishes.
  have hfix : translateEndo hP g * translateEndo hQ g * translateEndo h₃ g
      = g * translateEndo hP g * translateEndo hQ g := by
    have hcompPP : translateEndo hP (translateEndo hP g) = translateEndo hQ g :=
      congr($(translateEndo_comp hP hP hQ hdouble) g)
    have hcompPQ : translateEndo hP (translateEndo hQ g) = translateEndo h₃ g :=
      congr($(translateEndo_comp hP hQ h₃ hsum) g)
    have h1 : translateEndo hP (g * translateEndo hP g * translateEndo hQ g)
        = g * translateEndo hP g * translateEndo hQ g := by
      rw [hconst, translateEndo_algebraMap_base]
    rwa [map_mul, map_mul, hcompPP, hcompPQ] at h1
  refine mul_left_cancel₀ (mul_ne_zero hkgP hkgQ) ?_
  rw [hfix]
  ring

/-! ### The alternating property -/

open Classical in
/-- **`e_3(T, T) = 1` over an algebraically closed field.**

For an affine `3`-torsion point `T = (x₃, y₃)` on `W ⁄ F̄` and the `#418` datum `hprin` — the
principality of the `3`-divisible divisor `div ([3]∗ f_T)`, in the exact shape `exists_gS_three`
takes it — there are a principal function `f_T` with `div f_T = 3(T) − 3(O)` and a cube root `g_T`
of `[3]∗ f_T` (up to a unit of `F[W]`) such that `τ_T∗ g_T = g_T`, hence `e_3(T, T) = 1`.

`hprin` is the only gated hypothesis; everything else is discharged here.  See the module docstring
for why the points `P` and `Q = [2]P` cost nothing over `F̄`. -/
theorem exists_weilPairingElt_self_eq_one_of_algClosed_three [IsAlgClosed F] (h2 : (2 : F) ≠ 0)
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
  obtain ⟨f, hf, hdivproj, c, hc, htel⟩ :=
    exists_mul_translateEndo_mul_translateEndo_eq_algebraMap h htors
  -- The `#418` datum, at the telescoping function.
  obtain ⟨g, hg, hgdiv⟩ :=
    hprin f hf (divisor_eq_single_of_divisorProj_eq_single_sub_single hdivproj)
  have hfne : mulByThreeEndo h2 h3 f ≠ 0 := fun hz =>
    hf ((mulByThreeEndo h2 h3).injective (by rw [hz, map_zero]))
  obtain ⟨u, hu⟩ := exists_smul_pow_eq_of_nsmul_divisor hfne hg hgdiv
  -- The unit of `F[W]` is a nonzero constant, so the cube-root relation lives over `F`.
  obtain ⟨c₀, hc₀, hueq⟩ := isUnit_iff_exists_eq_algebraMap.mp u.isUnit
  have hcube : algebraMap F W.FunctionField c₀ * g ^ 3 = mulByThreeEndo h2 h3 f := by
    rw [← hu, Algebra.smul_def, hueq, ← IsScalarTower.algebraMap_apply]
  obtain ⟨xP, yP, xQ, yQ, hP, hQ, hdouble, hsum⟩ := exists_equation_nsmul_three_eq h2 h htors
  have htors' : torsionPoint h.left + torsionPoint h.left + torsionPoint h.left = 0 :=
    add_add_self_eq_zero_of_mem_torsion_three h htors
  have htinv : translateEndo h.left g = g :=
    translateEndo_eq_self_of_mul_algebraMap_cube_eq h2 h3 hP hQ h.left
      (translatePoint_add hP hP hQ hdouble) (translatePoint_add hP hQ h.left hsum)
      (translatePoint_add_add_self h.left htors') hg hc hc₀ htel hcube
  exact ⟨f, hf, hdivproj, g, hg, ⟨u, hu⟩, htinv,
    weilPairingElt_self_of_translateEndo_fixed h.left hg htinv⟩

/-! ### Non-vacuity

The headline is not instantiated outright **here**, because `hprin` is a hypothesis of the theorem
below.  ⚠️ **That is a fact about this file only, not an obstruction**: `hprin` at `n = 3` is
discharged over `F̄` by `exists_gS_three_of_isAlgClosed`
(`EllipticCurves.FunctionField.PullbackPrincipalityThree`), exactly as `#791` discharges it at
`n = 2` for `EllipticCurves.FunctionField.WeilPairingAlternatingTwoAlgClosed`.  The `n = 3` twin of
that file is `EllipticCurves.FunctionField.WeilPairingAlternatingThreeAlgClosed` (`#829`), where
the headline below is stated with `hprin` discharged and certified on the curve used here.
`[IsDedekindDomain W.CoordinateRing]` is **not** a second reason and never was: it is a global
instance for `[W.IsElliptic]` over an arbitrary field
(`EllipticCurves.FunctionField.CoordinateRingNormalGeneral`).  What is certified below is that
every hypothesis this file *adds* on top of `hprin` is simultaneously satisfiable — in
particular that the `[IsAlgClosed F]` step is not vacuous.

Which curve serves is worth stating, since over `F̄` the choice is not forced the way it is over
`ℚ`.  The `n = 2` certificate `y² = x³ − x` does have `3`-torsion over `AlgebraicClosure ℚ` — it has
nine `3`-torsion points, like every elliptic curve there — but none of them is rational: its
`Ψ₃ = 3X⁴ − 6X² − 1` has no rational root, so exhibiting one costs a genuine algebraic-number
argument.  The curve here is `WeilPairingTelescopeThree`'s `y² + y = x³`, of discriminant `−27`,
whose `Ψ₃ = 3X⁴ + 3X` vanishes at `0`, so the `3`-torsion point `(0, 0)` is rational and
base-changes to `AlgebraicClosure ℚ` for free.  `T` is *not* required to be rational anywhere in
this file; taking one that happens to be simply makes the certificate cheap. -/

section Nonvacuity

/-- An algebraically closed field of characteristic zero. -/
private abbrev exampleFieldThree : Type := AlgebraicClosure ℚ

/-- The curve `y² + y = x³` over `AlgebraicClosure ℚ`, of discriminant `-27`. -/
private noncomputable def exampleCurveAlgThree : Affine exampleFieldThree := ⟨0, 0, 1, 0, 0⟩

private instance : exampleCurveAlgThree.IsElliptic := by
  rw [WeierstrassCurve.isElliptic_iff, isUnit_iff_ne_zero]
  norm_num [exampleCurveAlgThree, WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈]

/-- `T = (0, 0)` is a nonsingular point of `y² + y = x³`. -/
private lemma exampleNonsingularAlgThree : exampleCurveAlgThree.Nonsingular 0 0 := by
  rw [nonsingular_iff]
  refine ⟨?_, Or.inr ?_⟩ <;>
    norm_num [exampleCurveAlgThree, WeierstrassCurve.Affine.negY]

open Classical in
/-- `T = (0, 0)` has order `3`: it is not fixed by negation, and `Ψ₃ = 3X⁴ + 3b₆X` vanishes at
`0`. -/
private lemma exampleTorsionAlgThree :
    Point.some (0 : exampleFieldThree) 0 exampleNonsingularAlgThree
      ∈ exampleCurveAlgThree.torsion 3 := by
  rw [mem_torsion_three_some_iff
    (by norm_num [exampleCurveAlgThree, WeierstrassCurve.Affine.negY])]
  norm_num [exampleCurveAlgThree, WeierstrassCurve.Ψ₃, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈]

open Classical in
/-- The two translation points exist and are both affine. -/
example : ∃ (xP yP xQ yQ : exampleFieldThree) (hP : exampleCurveAlgThree.Equation xP yP)
    (hQ : exampleCurveAlgThree.Equation xQ yQ),
    torsionPoint hP + torsionPoint hP = torsionPoint hQ ∧
      torsionPoint hP + torsionPoint hQ
        = Point.some (0 : exampleFieldThree) 0 exampleNonsingularAlgThree :=
  exists_equation_nsmul_three_eq (by norm_num) exampleNonsingularAlgThree exampleTorsionAlgThree

end Nonvacuity

end WeierstrassCurve.Affine
