/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import EllipticCurves.FunctionField.CoordinateRingNormalGeneral
import EllipticCurves.FunctionField.DivisorConstant
import EllipticCurves.FunctionField.DivisorPrincipality
import EllipticCurves.FunctionField.NthRootOfPullback
import EllipticCurves.FunctionField.WeilPairingAlternatingThreeAlgClosed
import EllipticCurves.FunctionField.WeilPairingAlternatingTwoAlgClosed
import EllipticCurves.FunctionField.WeilPairingAntisymmetric

/-!
# The product relation `g_{S ⊕ T} = g_S · g_T · w`, and antisymmetry over `F̄`

Silverman *AEC* III.8.1(d): the Weil pairing is antisymmetric, `e_n(T, S) = e_n(S, T)⁻¹`.

`EllipticCurves.FunctionField.WeilPairingAntisymmetric` (`#723`) proved that from the product
relation

```
hprod :  g_R = g_S · g_T · w        (for S ⊕ T = R)
```

carried as a hypothesis, and every file on this front defers the *production* of `hprod` in the
same words — *"rung-4/5 gated (`#414`/`#418`)"*.  **This file produces it, and the deferral was
wrong.**

## ⚠️ Why `hprod` was never rung-4 gated

The divisor input the product relation rests on is the Abel–Jacobi statement *`(S) + (T) − (S ⊕ T)`
is principal*, and `EllipticCurves.FunctionField.DivisorPrincipality` (`#726`) has had everything
it needs since it merged: `exists_divisor_eq_iff_classOfDivisor_eq_one` replaces "exhibit a
generator" by "compute a class", `classOfDivisor_add` computes the class termwise, and
`classOfDivisor_single_pointClosedPoint` identifies the class of `(P)` with `Point.toClass P`.
Since `Point.toClass` is a group homomorphism, the statement is immediate.

`DivisorPrincipality`'s own docstring says as much — *"the group law on `E` **is** the class-group
map"* — and the corollary was never drawn.  `exists_divisor_eq_add_sub_single_of_add_eq` below
needs **no `[IsAlgClosed F]`, no rung 4, no `hprin`, no Ward**: only `[W.IsElliptic]` over an
arbitrary field.

⚠️ This is the same failure mode `#465`'s 2026-08-23 comment named — *"a status note that says
'blocked on X' ages badly when the **route** changes, not just when X lands"* — and the same one
`#818` → `#819` → `#825` worked through for `hprin`.  Six files inherited one deferral sentence and
nobody re-read it after `#726` landed the criterion.

## The chain

Write `k` for the Abel–Jacobi function and `f_•`, `g_•`, `u_•` for the rung-5 data.

1. `div (f_S · f_T) = n(S) + n(T) = div (f_R · k ^ n)`, so the quotient has trivial divisor and is
   a constant (`exists_eq_algebraMap_of_divisor_eq_zero`, `#629`): `f_S · f_T = c · f_R · k ^ n`.
2. Apply the pullback `φ`, which fixes constants, and substitute `u_• • g_• ^ n = φ f_•`.  The
   units are constants (`exists_eq_algebraMap_of_isUnit`, `#398`).
3. `z := g_S · g_T · (g_R · φ k)⁻¹` then satisfies `z ^ n = ` a constant, so `n • div z = 0`, so
   `div z = 0`, so `z` is a constant by (1) again.
4. Rearranged: `g_R = g_S · g_T · (c · φ (k⁻¹))` — ⚠️ **exactly the shape the consumer already
   discharges.**  `weilPairingElt_divisorSlot_add_{two,three}` take `w = c · [n]∗f` and prove
   `e_n(w, R) = 1` outright, so the second hypothesis of the antisymmetry headline costs nothing.

⚠️ **Step 2 is generic in `φ`.**  Nothing in the argument is specific to `[2]∗` or `[3]∗`: the
producer `exists_prod_eq_of_pullback` takes an arbitrary ring endomorphism of `F(W)` that fixes the
base field, and the two concrete cases are instantiations.  A future `[n]∗` (`#403`/`#405`) plugs in
unchanged.

## Main statements

* `WeierstrassCurve.Affine.exists_divisor_eq_add_sub_single_of_add_eq` — **the Abel–Jacobi
  statement**, `(S) + (T) − (S ⊕ T)` is principal, over an arbitrary field.  Of interest well
  beyond `hprod`; it is the affine incarnation of Silverman III.3.5.
* `WeierstrassCurve.Affine.exists_prod_eq_of_pullback` — the product relation, generically in the
  pullback.
* **`WeierstrassCurve.Affine.exists_weilPairingElt_mul_swap_eq_one_two`** and **`_three`** —
  antisymmetry in product form, `e_n(S, T) · e_n(T, S) = 1`, over an algebraically closed field
  with **no hypothesis beyond the setting**.
* `WeierstrassCurve.Affine.exists_weilPairingElt_eq_inv_two` and `_three` — the quotable form
  `e_n(T, S) = e_n(S, T)⁻¹`.
* `classOfDivisor_neg`, `exists_mul_eq_algebraMap_mul` — the two steps of the chain.

## Scope

⚠️ **The three points carry their own rung-5 data, and the statements return it.**  `weilPairingElt`
takes the root `g_S` as an *argument*, so an antisymmetry statement has to say *which* roots it is
about; the headlines therefore produce `g_S` and `g_T` together with their rung-5 certificates,
exactly as `exists_gS_two_weilPairingElt_ne_one` does for non-degeneracy.  There is still no
`W.Point`-level pairing in this tree, and inventing one here would be the drift this front keeps
paying for.

⚠️ **A caller who already holds a root cannot apply those headlines**, and the `∀ g` forms that
serve such a caller are in `EllipticCurves.FunctionField.WeilPairingProductRelationRootIndependent`
(`#854`), at both `n` and at both levels.  They are *transfers* of the statements here and prove
nothing new: `weilPairingElt_eq_of_nsmul_divisor_eq` (`WeilPairingRootIndependence`, `#719`) makes
the pairing element depend on its root only through the root's divisor, which the rung-5 relation
pins, so the roots produced below can simply be exchanged for the caller's.  Moving the roots into
the hypotheses is *not* a step towards a `W.Point`-level pairing and that file says so too.

⚠️ **`[IsAlgClosed F]` enters only through the alternating inputs.**  Antisymmetry consumes the
alternating property at **three** points, `S`, `T` and `R = S ⊕ T` (`WeilPairingAntisymmetric`'s
docstring is right about this and it is not a defect — all three are `n`-torsion, so all three come
from one theorem).  Those are `exists_weilPairingElt_self_eq_one_of_isAlgClosed_two{,_three}`
(`#801`, `#829`), which carry `[IsAlgClosed F]`.  ⚠️ The Abel–Jacobi statement and the generic
producer do **not**, and are stated without it.

⚠️ **`hprin` over a general field is untouched and remains the genuine research gate**, at both `n`.
So is general `n` (`#404`'s `ωₙ` crux), and rung 4 itself (`#414`/`#421`/`#422`) — which this file
does not use and does not advance.

⚠️ **The `n = 2` and `n = 3` statements are pinned to `Classical.propDecidable`**, because they
mention `W.torsion n` and the base-field group law.  The generic layer above is not, and carries
`[DecidableEq F]` as an ordinary instance argument.

## References

* [J. H. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.3.5 (the divisor-class
  group law) and III.8, Prop. 8.1(a),(d).
-/

namespace WeierstrassCurve.Affine

open CoordinateRing IsDedekindDomain IsDedekindDomain.HeightOneSpectrum

variable {F : Type*} [Field F] {W : Affine F} [W.IsElliptic]

/-! ### The Abel–Jacobi statement -/

omit [W.IsElliptic] in
/-- **The class of `−D` is the inverse of the class of `D`.**  `classOfDivisor` is a group
homomorphism (`classOfDivisorHom`); `DivisorPrincipality` records `_zero`, `_add` and `_nsmul` but
not this one, which the Abel–Jacobi computation below needs to handle the `− (S ⊕ T)` term. -/
theorem classOfDivisor_neg [IsDedekindDomain W.CoordinateRing]
    (D : HeightOneSpectrum W.CoordinateRing →₀ ℤ) :
    classOfDivisor W.FunctionField (-D) = (classOfDivisor W.FunctionField D)⁻¹ :=
  map_inv (classOfDivisorHom W.FunctionField) (Multiplicative.ofAdd D)

section Generic

variable [DecidableEq F]

/-- **The Abel–Jacobi statement: `(S) + (T) − (S ⊕ T)` is a principal divisor.**

⚠️ **This needs no `[IsAlgClosed F]`, no rung 4, no `hprin` and no Ward** — only `[W.IsElliptic]`
over an arbitrary field, and it has been available since `DivisorPrincipality` (`#726`) merged.
Six files on this front defer the product relation `hprod` as *"rung-4/5 gated"*; that deferral was
about this statement and it was wrong.

The whole proof is that `classOfDivisor_single_pointClosedPoint` identifies the divisor class of a
rational point `(P)` with `Point.toClass P`, together with the fact that `Point.toClass` is a group
homomorphism.  `DivisorPrincipality`'s own docstring puts it as *"the group law on `E` **is** the
class-group map"*; this is that sentence used.

Affine throughout: the classical `− (O)` terms live at the point at infinity, off this chart, and
the three of them cancel in `(S) + (T) − (S ⊕ T) − (O)` anyway. -/
theorem exists_divisor_eq_add_sub_single_of_add_eq {xS yS xT yT xR yR : F}
    (hS : W.Nonsingular xS yS) (hT : W.Nonsingular xT yT) (hR : W.Nonsingular xR yR)
    (hadd : Point.some xS yS hS + Point.some xT yT hT = Point.some xR yR hR) :
    ∃ k : W.FunctionField, k ≠ 0 ∧
      divisor W k = Finsupp.single (pointClosedPoint hS.left) (1 : ℤ)
        + Finsupp.single (pointClosedPoint hT.left) (1 : ℤ)
        - Finsupp.single (pointClosedPoint hR.left) (1 : ℤ) := by
  rw [exists_divisor_eq_iff_classOfDivisor_eq_one, sub_eq_add_neg, classOfDivisor_add,
    classOfDivisor_add, classOfDivisor_neg, classOfDivisor_single_pointClosedPoint hS,
    classOfDivisor_single_pointClosedPoint hT, classOfDivisor_single_pointClosedPoint hR,
    ← hadd, map_add]
  simp

/-! ### The product relation -/

/-- **Step 1 of the chain: `f_S · f_T = c · f_R · k ^ n`.**

`div (f_S · f_T) = n(S) + n(T)`, and `div (f_R · k ^ n) = n(R) + n[(S) + (T) − (R)]` is the same
divisor, so the quotient has trivial divisor and is therefore a nonzero constant
(`exists_eq_algebraMap_of_divisor_eq_zero`, `#629`).

⚠️ `n` is arbitrary here, including `n = 0`, where the statement is a triviality.  The producer
below is the one that needs `n ≠ 0`. -/
theorem exists_mul_eq_algebraMap_mul {n : ℕ} {xS yS xT yT xR yR : F}
    (hS : W.Nonsingular xS yS) (hT : W.Nonsingular xT yT) (hR : W.Nonsingular xR yR)
    (hadd : Point.some xS yS hS + Point.some xT yT hT = Point.some xR yR hR)
    {fS fT fR : W.FunctionField} (hfS : fS ≠ 0) (hfT : fT ≠ 0) (hfR : fR ≠ 0)
    (hdS : divisor W fS = Finsupp.single (pointClosedPoint hS.left) (n : ℤ))
    (hdT : divisor W fT = Finsupp.single (pointClosedPoint hT.left) (n : ℤ))
    (hdR : divisor W fR = Finsupp.single (pointClosedPoint hR.left) (n : ℤ)) :
    ∃ (c : F) (k : W.FunctionField), c ≠ 0 ∧ k ≠ 0 ∧
      fS * fT = algebraMap F W.FunctionField c * (fR * k ^ n) := by
  obtain ⟨k, hk, hkdiv⟩ := exists_divisor_eq_add_sub_single_of_add_eq hS hT hR hadd
  have hpow : fR * k ^ n ≠ 0 := mul_ne_zero hfR (pow_ne_zero n hk)
  have hquot : divisor W (fS * fT * (fR * k ^ n)⁻¹) = 0 := by
    rw [divisor_mul (mul_ne_zero hfS hfT) (inv_ne_zero hpow), divisor_inv,
      divisor_mul hfS hfT, divisor_mul hfR (pow_ne_zero n hk), divisor_pow, hdS, hdT, hdR, hkdiv]
    rw [smul_sub, smul_add, Finsupp.smul_single, Finsupp.smul_single, Finsupp.smul_single]
    simp only [nsmul_eq_mul, mul_one]
    abel
  obtain ⟨c, hc, hceq⟩ :=
    Elliptic.exists_eq_algebraMap_of_divisor_eq_zero (mul_ne_zero (mul_ne_zero hfS hfT)
      (inv_ne_zero hpow)) hquot
  refine ⟨c, k, hc, hk, ?_⟩
  field_simp at hceq
  linear_combination hceq

/-- **The product relation `g_R = g_S · g_T · w`, generically in the pullback.**

Given rung-5 data at `S`, `T` and `R = S ⊕ T` for one and the same endomorphism `φ` of `F(W)` that
fixes the base field, the three roots satisfy `g_R = g_S · g_T · (c · φ (k⁻¹))` for a nonzero
constant `c` and a nonzero `k`.

⚠️ **Nothing in the argument is specific to `[2]∗` or `[3]∗`**, which is why `φ` is a parameter: a
future divisor-level `[n]∗` (`#403`/`#405`) instantiates it unchanged.  `φ` needs no injectivity
hypothesis — a ring homomorphism out of a field is injective.

⚠️ **The shape of `w` is not incidental.**  `c · φ k⁻¹` is exactly what
`weilPairingElt_divisorSlot_add_{two,three}` (`WeilPairingAntisymmetric`) already discharge, so the
`hwR : e_n(w, R) = 1` hypothesis of the antisymmetry headline costs nothing downstream.  Silverman
writes the same factor as `c · (h ∘ [n])`.

The chain, after step 1: pull back along `φ`, substitute the roots and absorb the three units
(constants, by `exists_eq_algebraMap_of_isUnit`, `#398`); then `z := g_S · g_T · (g_R · φ k)⁻¹`
satisfies `z ^ n = ` a constant, so `n • div z = 0`, so `div z = 0` since `n ≠ 0` and the divisor
group is torsion-free, so `z` is itself a constant. -/
theorem exists_prod_eq_of_pullback (φ : W.FunctionField →+* W.FunctionField)
    (hφc : ∀ c : F, φ (algebraMap F W.FunctionField c) = algebraMap F W.FunctionField c)
    {n : ℕ} (hn : n ≠ 0) {xS yS xT yT xR yR : F}
    (hS : W.Nonsingular xS yS) (hT : W.Nonsingular xT yT) (hR : W.Nonsingular xR yR)
    (hadd : Point.some xS yS hS + Point.some xT yT hT = Point.some xR yR hR)
    {fS fT fR gS gT gR : W.FunctionField} (hfS : fS ≠ 0) (hfT : fT ≠ 0) (hfR : fR ≠ 0)
    (hdS : divisor W fS = Finsupp.single (pointClosedPoint hS.left) (n : ℤ))
    (hdT : divisor W fT = Finsupp.single (pointClosedPoint hT.left) (n : ℤ))
    (hdR : divisor W fR = Finsupp.single (pointClosedPoint hR.left) (n : ℤ))
    (hgS : gS ≠ 0) (hgT : gT ≠ 0) (hgR : gR ≠ 0)
    {uS uT uR : W.CoordinateRingˣ}
    (huS : (uS : W.CoordinateRing) • gS ^ n = φ fS)
    (huT : (uT : W.CoordinateRing) • gT ^ n = φ fT)
    (huR : (uR : W.CoordinateRing) • gR ^ n = φ fR) :
    ∃ (c : F) (k : W.FunctionField), c ≠ 0 ∧ k ≠ 0 ∧
      gR = gS * gT * (algebraMap F W.FunctionField c * φ k) := by
  obtain ⟨c₁, k, hc₁, hk, hkeq⟩ :=
    exists_mul_eq_algebraMap_mul hS hT hR hadd hfS hfT hfR hdS hdT hdR
  -- Each unit is a nonzero constant of `F`.
  have hunit : ∀ (u : W.CoordinateRingˣ) (g : W.FunctionField), ∃ d : F, d ≠ 0 ∧
      (u : W.CoordinateRing) • g ^ n = algebraMap F W.FunctionField d * g ^ n := by
    intro u g
    obtain ⟨d, hd⟩ := exists_eq_algebraMap_of_isUnit u.isUnit
    refine ⟨d, ?_, by rw [Algebra.smul_def, hd, ← IsScalarTower.algebraMap_apply]⟩
    rintro rfl
    exact u.ne_zero (by rw [hd, map_zero])
  obtain ⟨dS, hdS0, hdSeq⟩ := hunit uS gS
  obtain ⟨dT, hdT0, hdTeq⟩ := hunit uT gT
  obtain ⟨dR, hdR0, hdReq⟩ := hunit uR gR
  have hφk : φ k ≠ 0 := fun hz => hk (φ.injective (by rw [hz, map_zero]))
  -- Pull back the step-B identity and substitute the roots.
  have hpull : algebraMap F W.FunctionField dS * gS ^ n * (algebraMap F W.FunctionField dT * gT ^ n)
      = algebraMap F W.FunctionField c₁ *
        (algebraMap F W.FunctionField dR * gR ^ n * φ k ^ n) := by
    rw [← hdSeq, ← hdTeq, ← hdReq, huS, huT, huR, ← map_pow, ← hφc c₁, ← map_mul, ← map_mul,
      ← map_mul, hkeq]
  -- `z := g_S · g_T / (g_R · φ k)` is an `n`-th root of a constant, hence a constant.
  set z : W.FunctionField := gS * gT * (gR * φ k)⁻¹ with hz
  have hz0 : z ≠ 0 :=
    mul_ne_zero (mul_ne_zero hgS hgT) (inv_ne_zero (mul_ne_zero hgR hφk))
  have hzpow : z ^ n = algebraMap F W.FunctionField (c₁ * dR * (dS * dT)⁻¹) := by
    have hne : (algebraMap F W.FunctionField dS) ≠ 0 := by simpa using hdS0
    have hne' : (algebraMap F W.FunctionField dT) ≠ 0 := by simpa using hdT0
    rw [hz, mul_pow, mul_pow, inv_pow, mul_pow, map_mul, map_mul, map_inv₀, map_mul]
    field_simp
    linear_combination hpull
  have hzdiv : divisor W z = 0 := by
    have h1 : (n : ℕ) • divisor W z = 0 := by
      rw [← divisor_pow, hzpow, divisor_algebraMap_base]
      exact mul_ne_zero (mul_ne_zero hc₁ hdR0) (inv_ne_zero (mul_ne_zero hdS0 hdT0))
    ext v
    have := DFunLike.congr_fun h1 v
    rw [Finsupp.smul_apply, nsmul_eq_mul] at this
    have hn' : (n : ℤ) ≠ 0 := Int.natCast_ne_zero.mpr hn
    simpa using (mul_eq_zero.mp this).resolve_left hn'
  obtain ⟨c₂, hc₂, hc₂eq⟩ := Elliptic.exists_eq_algebraMap_of_divisor_eq_zero hz0 hzdiv
  refine ⟨c₂⁻¹, k⁻¹, inv_ne_zero hc₂, inv_ne_zero hk, ?_⟩
  have : gS * gT = algebraMap F W.FunctionField c₂ * (gR * φ k) := by
    rw [← hc₂eq, hz]; field_simp
  have hc₂' : (algebraMap F W.FunctionField c₂) ≠ 0 := by simpa using hc₂
  rw [map_inv₀ (algebraMap F W.FunctionField) c₂, map_inv₀ φ k, this]
  field_simp


end Generic

section Two

variable [IsAlgClosed F]

open Classical in
/-- The rung-5 datum at a `2`-torsion point, together with the alternating property for
**that** root: the affine divisor form of `exists_weilPairingElt_self_eq_one_of_isAlgClosed_two`. -/
private lemma rungFiveAlt_two (h2 : (2 : F) ≠ 0) {x y : F} (h : W.Nonsingular x y)
    (htors : Point.some x y h ∈ W.torsion 2) :
    ∃ f g : W.FunctionField, f ≠ 0 ∧ g ≠ 0 ∧
      divisor W f = Finsupp.single (pointClosedPoint h.left) (2 : ℤ) ∧
      (∃ u : W.CoordinateRingˣ, (u : W.CoordinateRing) • g ^ 2 = mulByTwoEndo h2 f) ∧
      weilPairingElt h.left g = 1 := by
  obtain ⟨f, hf, hdivproj, g, hg, hu, _, halt⟩ :=
    exists_weilPairingElt_self_eq_one_of_isAlgClosed_two h2 h htors
  exact ⟨f, g, hf, hg, divisor_eq_single_of_divisorProj_eq_single_sub_single hdivproj, hu, halt⟩

open Classical in
/-- **Antisymmetry of the Weil pairing at `n = 2` over an algebraically closed field, with no
hypothesis beyond the setting.**

⚠️ `R = S ⊕ T` is **not** assumed to be `2`-torsion: `W.torsion 2` is a subgroup, so `hadd ▸
add_mem hmS hmT` derives it.  The alternating property is nevertheless consumed at all three of
`S`, `T` and `R`, as `weilPairingElt_mul_swap_eq_one` requires. -/
theorem exists_weilPairingElt_mul_swap_eq_one_two (h2 : (2 : F) ≠ 0)
    {xS yS xT yT xR yR : F}
    (hS : W.Nonsingular xS yS) (hT : W.Nonsingular xT yT) (hR : W.Nonsingular xR yR)
    (hmS : Point.some xS yS hS ∈ W.torsion 2) (hmT : Point.some xT yT hT ∈ W.torsion 2)
    (hadd : Point.some xS yS hS + Point.some xT yT hT = Point.some xR yR hR) :
    ∃ gS gT : W.FunctionField, gS ≠ 0 ∧ gT ≠ 0 ∧
      (∃ f : W.FunctionField, f ≠ 0 ∧
        divisor W f = Finsupp.single (pointClosedPoint hS.left) (2 : ℤ) ∧
        ∃ u : W.CoordinateRingˣ, (u : W.CoordinateRing) • gS ^ 2 = mulByTwoEndo h2 f) ∧
      (∃ f : W.FunctionField, f ≠ 0 ∧
        divisor W f = Finsupp.single (pointClosedPoint hT.left) (2 : ℤ) ∧
        ∃ u : W.CoordinateRingˣ, (u : W.CoordinateRing) • gT ^ 2 = mulByTwoEndo h2 f) ∧
      weilPairingElt hS.left gT * weilPairingElt hT.left gS = 1 := by
  have hmR : Point.some xR yR hR ∈ W.torsion 2 := hadd ▸ add_mem hmS hmT
  obtain ⟨fS, gS, hfS, hgS, hdS, ⟨uS, huS⟩, haltS⟩ := rungFiveAlt_two h2 hS hmS
  obtain ⟨fT, gT, hfT, hgT, hdT, ⟨uT, huT⟩, haltT⟩ := rungFiveAlt_two h2 hT hmT
  obtain ⟨fR, gR, hfR, hgR, hdR, ⟨uR, huR⟩, haltR⟩ := rungFiveAlt_two h2 hR hmR
  obtain ⟨c, k, hc, hk, hprod⟩ :=
    exists_prod_eq_of_pullback (mulByTwoEndo h2) (mulByTwoEndo_algebraMap_base h2)
      two_ne_zero hS hT hR hadd hfS hfT hfR hdS hdT hdR hgS hgT hgR huS huT huR
  have hwR : weilPairingElt hR.left
      (algebraMap F W.FunctionField c * mulByTwoEndo h2 k) = 1 := by
    rw [weilPairingElt_mul, weilPairingElt_algebraMap hR.left hc,
      weilPairingElt_mulByTwoEndo_of_baseField hR.left h2
        (add_self_eq_zero_of_mem_torsion_two hmR) hk, mul_one]
  refine ⟨gS, gT, hgS, hgT, ⟨fS, hfS, hdS, uS, huS⟩, ⟨fT, hfT, hdT, uT, huT⟩, ?_⟩
  exact weilPairingElt_mul_swap_eq_one hS.left hT.left hR.left hadd hgS hgT hprod hwR
    two_ne_zero
    (weilPairingElt_pow_eq_one_of_gS_two_torsion hT.left h2
      (add_self_eq_zero_of_mem_torsion_two hmT) hgS huS)
    haltS haltT haltR

open Classical in
/-- **Antisymmetry at `n = 2` in the quotable inverse form**: `e_2(T, S) = e_2(S, T)⁻¹`, over an
algebraically closed field with no hypothesis beyond the setting. -/
theorem exists_weilPairingElt_eq_inv_two (h2 : (2 : F) ≠ 0) {xS yS xT yT xR yR : F}
    (hS : W.Nonsingular xS yS) (hT : W.Nonsingular xT yT) (hR : W.Nonsingular xR yR)
    (hmS : Point.some xS yS hS ∈ W.torsion 2) (hmT : Point.some xT yT hT ∈ W.torsion 2)
    (hadd : Point.some xS yS hS + Point.some xT yT hT = Point.some xR yR hR) :
    ∃ gS gT : W.FunctionField, gS ≠ 0 ∧ gT ≠ 0 ∧
      (∃ f : W.FunctionField, f ≠ 0 ∧
        divisor W f = Finsupp.single (pointClosedPoint hS.left) (2 : ℤ) ∧
        ∃ u : W.CoordinateRingˣ, (u : W.CoordinateRing) • gS ^ 2 = mulByTwoEndo h2 f) ∧
      (∃ f : W.FunctionField, f ≠ 0 ∧
        divisor W f = Finsupp.single (pointClosedPoint hT.left) (2 : ℤ) ∧
        ∃ u : W.CoordinateRingˣ, (u : W.CoordinateRing) • gT ^ 2 = mulByTwoEndo h2 f) ∧
      weilPairingElt hS.left gT = (weilPairingElt hT.left gS)⁻¹ := by
  obtain ⟨gS, gT, hgS, hgT, hcS, hcT, hswap⟩ :=
    exists_weilPairingElt_mul_swap_eq_one_two h2 hS hT hR hmS hmT hadd
  exact ⟨gS, gT, hgS, hgT, hcS, hcT, eq_inv_of_mul_eq_one_left hswap⟩

end Two

section Three

variable [IsAlgClosed F]

open Classical in
private lemma rungFiveAlt_three (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) {x y : F}
    (h : W.Nonsingular x y) (htors : Point.some x y h ∈ W.torsion 3) :
    ∃ f g : W.FunctionField, f ≠ 0 ∧ g ≠ 0 ∧
      divisor W f = Finsupp.single (pointClosedPoint h.left) (3 : ℤ) ∧
      (∃ u : W.CoordinateRingˣ, (u : W.CoordinateRing) • g ^ 3 = mulByThreeEndo h2 h3 f) ∧
      weilPairingElt h.left g = 1 := by
  obtain ⟨f, hf, hdivproj, g, hg, hu, _, halt⟩ :=
    exists_weilPairingElt_self_eq_one_of_isAlgClosed_three h2 h3 h htors
  exact ⟨f, g, hf, hg, divisor_eq_single_of_divisorProj_eq_single_sub_single hdivproj, hu, halt⟩

open Classical in
/-- **Antisymmetry of the Weil pairing at `n = 3` over an algebraically closed field, with no
hypothesis beyond the setting.**

⚠️ As at `n = 2`, the `3`-torsion of `R = S ⊕ T` is derived from that of `S` and `T` rather than
assumed. -/
theorem exists_weilPairingElt_mul_swap_eq_one_three (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0)
    {xS yS xT yT xR yR : F}
    (hS : W.Nonsingular xS yS) (hT : W.Nonsingular xT yT) (hR : W.Nonsingular xR yR)
    (hmS : Point.some xS yS hS ∈ W.torsion 3) (hmT : Point.some xT yT hT ∈ W.torsion 3)
    (hadd : Point.some xS yS hS + Point.some xT yT hT = Point.some xR yR hR) :
    ∃ gS gT : W.FunctionField, gS ≠ 0 ∧ gT ≠ 0 ∧
      (∃ f : W.FunctionField, f ≠ 0 ∧
        divisor W f = Finsupp.single (pointClosedPoint hS.left) (3 : ℤ) ∧
        ∃ u : W.CoordinateRingˣ, (u : W.CoordinateRing) • gS ^ 3 = mulByThreeEndo h2 h3 f) ∧
      (∃ f : W.FunctionField, f ≠ 0 ∧
        divisor W f = Finsupp.single (pointClosedPoint hT.left) (3 : ℤ) ∧
        ∃ u : W.CoordinateRingˣ, (u : W.CoordinateRing) • gT ^ 3 = mulByThreeEndo h2 h3 f) ∧
      weilPairingElt hS.left gT * weilPairingElt hT.left gS = 1 := by
  have hmR : Point.some xR yR hR ∈ W.torsion 3 := hadd ▸ add_mem hmS hmT
  obtain ⟨fS, gS, hfS, hgS, hdS, ⟨uS, huS⟩, haltS⟩ := rungFiveAlt_three h2 h3 hS hmS
  obtain ⟨fT, gT, hfT, hgT, hdT, ⟨uT, huT⟩, haltT⟩ := rungFiveAlt_three h2 h3 hT hmT
  obtain ⟨fR, gR, hfR, hgR, hdR, ⟨uR, huR⟩, haltR⟩ := rungFiveAlt_three h2 h3 hR hmR
  obtain ⟨c, k, hc, hk, hprod⟩ :=
    exists_prod_eq_of_pullback (mulByThreeEndo h2 h3) (mulByThreeEndo_algebraMap_base h2 h3)
      three_ne_zero hS hT hR hadd hfS hfT hfR hdS hdT hdR hgS hgT hgR huS huT huR
  have hwR : weilPairingElt hR.left
      (algebraMap F W.FunctionField c * mulByThreeEndo h2 h3 k) = 1 := by
    rw [weilPairingElt_mul, weilPairingElt_algebraMap hR.left hc,
      weilPairingElt_mulByThreeEndo_of_baseField hR.left h2 h3
        (add_add_self_eq_zero_of_mem_torsion_three hmR) hk, mul_one]
  refine ⟨gS, gT, hgS, hgT, ⟨fS, hfS, hdS, uS, huS⟩, ⟨fT, hfT, hdT, uT, huT⟩, ?_⟩
  exact weilPairingElt_mul_swap_eq_one hS.left hT.left hR.left hadd hgS hgT hprod hwR
    three_ne_zero
    (weilPairingElt_pow_eq_one_of_gS_three_baseField hT.left h2 h3
      (add_add_self_eq_zero_of_mem_torsion_three hmT) hgS huS)
    haltS haltT haltR

open Classical in
/-- **Antisymmetry at `n = 3` in the quotable inverse form**: `e_3(T, S) = e_3(S, T)⁻¹`, over an
algebraically closed field with no hypothesis beyond the setting. -/
theorem exists_weilPairingElt_eq_inv_three (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0)
    {xS yS xT yT xR yR : F}
    (hS : W.Nonsingular xS yS) (hT : W.Nonsingular xT yT) (hR : W.Nonsingular xR yR)
    (hmS : Point.some xS yS hS ∈ W.torsion 3) (hmT : Point.some xT yT hT ∈ W.torsion 3)
    (hadd : Point.some xS yS hS + Point.some xT yT hT = Point.some xR yR hR) :
    ∃ gS gT : W.FunctionField, gS ≠ 0 ∧ gT ≠ 0 ∧
      (∃ f : W.FunctionField, f ≠ 0 ∧
        divisor W f = Finsupp.single (pointClosedPoint hS.left) (3 : ℤ) ∧
        ∃ u : W.CoordinateRingˣ, (u : W.CoordinateRing) • gS ^ 3 = mulByThreeEndo h2 h3 f) ∧
      (∃ f : W.FunctionField, f ≠ 0 ∧
        divisor W f = Finsupp.single (pointClosedPoint hT.left) (3 : ℤ) ∧
        ∃ u : W.CoordinateRingˣ, (u : W.CoordinateRing) • gT ^ 3 = mulByThreeEndo h2 h3 f) ∧
      weilPairingElt hS.left gT = (weilPairingElt hT.left gS)⁻¹ := by
  obtain ⟨gS, gT, hgS, hgT, hcS, hcT, hswap⟩ :=
    exists_weilPairingElt_mul_swap_eq_one_three h2 h3 hS hT hR hmS hmT hadd
  exact ⟨gS, gT, hgS, hgT, hcS, hcT, eq_inv_of_mul_eq_one_left hswap⟩

end Three

/-! ### Non-vacuity

Both headlines carry `[IsAlgClosed F]`, `[W.IsElliptic]`, a **pair** of affine torsion points and
an affine point `R` with `S ⊕ T = R` (whose torsion is derived, not assumed).  Two base curves
are needed and the split is intrinsic, not stylistic: `y² = x³ − x` has `Ψ₃ = 3X⁴ − 6X² − 1`,
whose roots are irrational, so it cannot **name** a `3`-torsion point at all.

⚠️ At `n = 2` the certificate is genuinely non-degenerate as an instance of *antisymmetry*: the
three points `(0, 0)`, `(1, 0)` and `(−1, 0)` are **distinct**, so `S ≠ T` and the statement is not
a disguised instance of the alternating property.  At `n = 3` that is not available — the only
nameable `3`-torsion points on `y² + y = x³` are `(0, 0)` and its negative `(0, −1)` — so the
`n = 3` certificate is taken at `S = T = (0, 0)`, `R = (0, −1)`.  **Said plainly rather than
papered over**: the `n = 3` example certifies that the hypotheses are simultaneously satisfiable,
which is what a non-vacuity certificate is for, but it does not exhibit `S ≠ T`. -/

section Nonvacuity

/-- An algebraically closed field of characteristic zero. -/
private abbrev exampleField : Type := AlgebraicClosure ℚ

private lemma exampleTwo : (2 : exampleField) ≠ 0 := by norm_num

private lemma exampleThree : (3 : exampleField) ≠ 0 := by norm_num

/-- The curve `y² = x³ − x` over `AlgebraicClosure ℚ`, of discriminant `64`. -/
private noncomputable def exampleCurve : Affine exampleField := ⟨0, 0, 0, -1, 0⟩

private instance : exampleCurve.IsElliptic := by
  rw [WeierstrassCurve.isElliptic_iff, isUnit_iff_ne_zero]
  norm_num [exampleCurve, WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈]

private lemma exampleNsS : exampleCurve.Nonsingular 0 0 :=
  exampleCurve.equation_iff_nonsingular.mp (by
    norm_num [exampleCurve, WeierstrassCurve.Affine.equation_iff])

private lemma exampleNsT : exampleCurve.Nonsingular 1 0 :=
  exampleCurve.equation_iff_nonsingular.mp (by
    norm_num [exampleCurve, WeierstrassCurve.Affine.equation_iff])

private lemma exampleNsR : exampleCurve.Nonsingular (-1) 0 :=
  exampleCurve.equation_iff_nonsingular.mp (by
    norm_num [exampleCurve, WeierstrassCurve.Affine.equation_iff])

open Classical in
private lemma exampleTorS :
    Point.some (0 : exampleField) 0 exampleNsS ∈ exampleCurve.torsion 2 :=
  (mem_torsion_two_some_iff exampleNsS).mpr (by norm_num [exampleCurve])

open Classical in
private lemma exampleTorT :
    Point.some (1 : exampleField) 0 exampleNsT ∈ exampleCurve.torsion 2 :=
  (mem_torsion_two_some_iff exampleNsT).mpr (by norm_num [exampleCurve])

open Classical in
/-- `(0, 0) ⊕ (1, 0) = (−1, 0)` on `y² = x³ − x`: the three nonzero `2`-torsion points, and they
are **distinct**. -/
private lemma exampleAdd :
    Point.some (0 : exampleField) 0 exampleNsS + Point.some (1 : exampleField) 0 exampleNsT
      = Point.some (-1 : exampleField) 0 exampleNsR := by
  rw [Point.add_of_X_ne (by norm_num)]
  simp only [Point.some.injEq]
  norm_num [exampleCurve, WeierstrassCurve.Affine.addX, WeierstrassCurve.Affine.addY,
    WeierstrassCurve.Affine.negAddY, WeierstrassCurve.Affine.slope, WeierstrassCurve.Affine.negY]

open Classical in
/-- **Antisymmetry at `n = 2`, on a curve that exists**, at two **distinct** named `2`-torsion
points. -/
example : ∃ gS gT : exampleCurve.FunctionField, gS ≠ 0 ∧ gT ≠ 0 ∧
    (∃ f : exampleCurve.FunctionField, f ≠ 0 ∧
      exampleCurve.divisor f
        = Finsupp.single (pointClosedPoint exampleNsS.left) (2 : ℤ) ∧
      ∃ u : exampleCurve.CoordinateRingˣ,
        (u : exampleCurve.CoordinateRing) • gS ^ 2 = mulByTwoEndo exampleTwo f) ∧
    (∃ f : exampleCurve.FunctionField, f ≠ 0 ∧
      exampleCurve.divisor f
        = Finsupp.single (pointClosedPoint exampleNsT.left) (2 : ℤ) ∧
      ∃ u : exampleCurve.CoordinateRingˣ,
        (u : exampleCurve.CoordinateRing) • gT ^ 2 = mulByTwoEndo exampleTwo f) ∧
    weilPairingElt exampleNsS.left gT * weilPairingElt exampleNsT.left gS = 1 :=
  exists_weilPairingElt_mul_swap_eq_one_two exampleTwo exampleNsS exampleNsT exampleNsR
    exampleTorS exampleTorT exampleAdd

/-- The curve `y² + y = x³` over `AlgebraicClosure ℚ`, of discriminant `−27`. -/
private noncomputable def exampleCurveThree : Affine exampleField := ⟨0, 0, 1, 0, 0⟩

private instance : exampleCurveThree.IsElliptic := by
  rw [WeierstrassCurve.isElliptic_iff, isUnit_iff_ne_zero]
  norm_num [exampleCurveThree, WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈]

private lemma exampleNsThreeS : exampleCurveThree.Nonsingular 0 0 :=
  exampleCurveThree.equation_iff_nonsingular.mp (by
    norm_num [exampleCurveThree, WeierstrassCurve.Affine.equation_iff])

private lemma exampleNsThreeR : exampleCurveThree.Nonsingular 0 (-1) :=
  exampleCurveThree.equation_iff_nonsingular.mp (by
    norm_num [exampleCurveThree, WeierstrassCurve.Affine.equation_iff])

open Classical in
private lemma exampleTorThreeS :
    Point.some (0 : exampleField) 0 exampleNsThreeS ∈ exampleCurveThree.torsion 3 :=
  mem_torsion_three_some_iff'.mpr (by
    norm_num [exampleCurveThree, WeierstrassCurve.Ψ₃, WeierstrassCurve.b₂,
      WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈])

open Classical in
/-- `(0, 0) ⊕ (0, 0) = (0, −1)` on `y² + y = x³`: doubling the named `3`-torsion point gives its
negative, which is the other one. -/
private lemma exampleAddThree :
    Point.some (0 : exampleField) 0 exampleNsThreeS
        + Point.some (0 : exampleField) 0 exampleNsThreeS
      = Point.some (0 : exampleField) (-1) exampleNsThreeR := by
  rw [Point.add_of_Y_ne (by norm_num [exampleCurveThree, WeierstrassCurve.Affine.negY])]
  simp only [Point.some.injEq]
  norm_num [exampleCurveThree, WeierstrassCurve.Affine.addX, WeierstrassCurve.Affine.addY,
    WeierstrassCurve.Affine.negAddY, WeierstrassCurve.Affine.slope, WeierstrassCurve.Affine.negY]

open Classical in
/-- **Antisymmetry at `n = 3`, on a curve that exists.**  ⚠️ Here `S = T`; see the section note. -/
example : ∃ gS gT : exampleCurveThree.FunctionField, gS ≠ 0 ∧ gT ≠ 0 ∧
    (∃ f : exampleCurveThree.FunctionField, f ≠ 0 ∧
      exampleCurveThree.divisor f
        = Finsupp.single (pointClosedPoint exampleNsThreeS.left) (3 : ℤ) ∧
      ∃ u : exampleCurveThree.CoordinateRingˣ,
        (u : exampleCurveThree.CoordinateRing) • gS ^ 3
          = mulByThreeEndo exampleTwo exampleThree f) ∧
    (∃ f : exampleCurveThree.FunctionField, f ≠ 0 ∧
      exampleCurveThree.divisor f
        = Finsupp.single (pointClosedPoint exampleNsThreeS.left) (3 : ℤ) ∧
      ∃ u : exampleCurveThree.CoordinateRingˣ,
        (u : exampleCurveThree.CoordinateRing) • gT ^ 3
          = mulByThreeEndo exampleTwo exampleThree f) ∧
    weilPairingElt exampleNsThreeS.left gT * weilPairingElt exampleNsThreeS.left gS = 1 :=
  exists_weilPairingElt_mul_swap_eq_one_three exampleTwo exampleThree exampleNsThreeS
    exampleNsThreeS exampleNsThreeR exampleTorThreeS exampleTorThreeS exampleAddThree

end Nonvacuity

end WeierstrassCurve.Affine
