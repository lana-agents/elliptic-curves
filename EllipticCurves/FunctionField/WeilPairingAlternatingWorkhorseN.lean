/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import EllipticCurves.Fixtures
import EllipticCurves.FunctionField.TranslationMulByNCommGeneral
import EllipticCurves.FunctionField.TranslationPointEndomorphism
import EllipticCurves.FunctionField.WeilPairingAlternatingThree

/-!
# The alternating workhorse at general `n`: `τ_T∗ g = g` from the `⟨T⟩`-telescope

Silverman *AEC* III.8.1(d) proves `e_n(T, T) = 1` from two products.  The **first** is a
telescoping of divisors over `⟨T⟩`, `∏_{i<n} τ_{[i]T}∗ f_T = c`; the **second** takes that constant,
an `n`-th root `g` of `[n]∗ f_T`, and an `n`-division point `P` with `[n]P = T`, and concludes that
`g` is fixed by `τ_T∗`.  This file is the **second** product, at an arbitrary `n`.

`EllipticCurves.FunctionField.WeilPairingAlternating{Two,Three}` prove it at `n = 2` and `n = 3`
(`translateEndo_eq_self_of_mul_algebraMap_{sq,cube}_eq`), each with the numeral hard-wired into the
shape of the telescope hypothesis.  Both are recovered from the general form below, verbatim.

## ⚠️ The two halves are independent, and only this one is here

The first product needs no `[n]∗`, no `hprin` and no division point; the second needs no divisor
telescoping.  Neither is an input to the other — they meet only in the assembly
`exists_weilPairingElt_self_eq_one_of_hprin_n`, which is **not** here and cannot be written until
both exist.  In particular **nothing below produces the hypothesis `htel`**: it is the caller's, and
at general `n` nothing on this tree produces it yet.

## The argument, and why it needs no new mathematics

With `w := ∏_{i<n} τ_{[i]P}∗ g`, where `[n]P = T`:

```
w ^ n = ∏_i τ_{[i]P}∗ (g ^ n)  =  c₀⁻ⁿ ∏_i τ_{[i]P}∗ ([n]∗ f)
      = c₀⁻ⁿ ∏_i [n]∗ (τ_{[i]T}∗ f)                     -- τ_Q∗ ∘ [n]∗ = [n]∗ ∘ τ_{[n]Q}∗
      = c₀⁻ⁿ [n]∗ (∏_i τ_{[i]T}∗ f)  =  c / c₀ⁿ         -- and [n]([i]P) = [i]([n]P) = [i]T
```

so `div w = 0` and `w` is a nonzero constant, hence fixed by `τ_P∗`.  Expanding that fixedness with
the two ways of peeling a `Finset.range (n+1)` product (`Finset.prod_range_succ'` off the bottom,
`Finset.prod_range_succ` off the top) gives `τ_P∗ w · g = w · τ_{[n]P}∗ g`, and cancelling `w`
leaves `τ_T∗ g = g`.

⚠️ **The commutation is the load-bearing input and it is already general in `n`.**  Two merged
statements cover it: `translateEndo_mulByNEndo_apply_of_baseField`
(`EllipticCurves.FunctionField.TranslationMulByNCommGeneral`) when `[n]Q` is affine, and
`translateEndo_mulByNEndo_apply_torsion_of_baseField` when it is `O`.  A blocker list for this seam
that omits them will conclude the file is unreachable; it is not.

## ⚠️ Why `translatePointEndo` and not `translateEndo`

The `i = 0` factor of both products translates by `O`, which is not an affine point, so
`translateEndo` — indexed by a `W.Equation` datum — cannot state either product uniformly.  The
same happens whenever `T` has order strictly dividing `n`.
`EllipticCurves.FunctionField.TranslationPointEndomorphism` was written for exactly this and
supplies `translatePointEndo` together with `_comp`, `_apply_apply`, `_nsmul` and
`_torsionPoint`; `WeilPairingTelescopeTwo`'s module docstring predicted the need.

## Main results

* `translatePointEndo_algebraMap_base` — `τ_P∗` fixes the constants, at every `P` including `O`.
* `translatePointEndo_mulByNEndo_apply` — the commutation `τ_P∗ ∘ [n]∗ = [n]∗ ∘ τ_T∗` for
  `[n]P = T`, with **no affineness assumption on either point**: the three cases (`P = O`;
  `P` affine and `T = O`; both affine) are each one merged lemma.
* `torsionPointMap_injective` — the base-change map `W.Point → (W ⁄ F(W)).Point` is injective.
* **`translatePointEndo_eq_self_of_prod_eq_of_pow_eq`** — the workhorse.

## ⚠️ Placement, stated rather than assumed

`translatePointEndo_algebraMap_base` belongs in `TranslationPointEndomorphism` and
`torsionPointMap_injective` belongs next to `torsionPointMap_eq_zero_iff`
(`EllipticCurves.FunctionField.MulByNTranscendence`); both files sit *below* this one, so moving
them costs no import damage and would be purely mechanical.  They are here because this file is
their only consumer today and a one-file diff is cheaper to review — **not** because this is where
they belong.  Anyone who wants them lower should move them and say so.

The workhorse itself is stated in `WeierstrassCurve.Affine`, not in the `CoordinateRing`
sub-namespace, because that is where its two merged twins live; the bricks are in `CoordinateRing`,
because that is where `translatePointEndo` and `translateEndo_mulByNEndo_apply_general` live.  This
is the placement rule of `#1317`, applied in both directions inside one file.

## Scope

`[Field F] {W : Affine F} [W.IsElliptic]`.  No `[IsAlgClosed F]`, no `hprin`, no `ωₙ` (`#404`), no
Ward, no rung 4.  The transcendence hypothesis `hn` is the standard general-`n` gate of
`mulByNEndo` and is discharged by `transcendental_xCoord_nsmul_of_smooth` or, at a numeral, by
`transcendental_xCoord_{two,three}_nsmul`.

Out of scope: the divisor telescoping (`∏_{i<n} τ_{[i]T}∗ f_T = c`), the assembly, and any edit to
`WeilPairingAlternating{,Two,Three,Mu,BaseChange}`.

## References

* [J. Silverman, *The arithmetic of elliptic curves*][silverman2009], III.8.1(d), second product.
-/

open Polynomial IsDedekindDomain

namespace WeierstrassCurve.Affine

namespace CoordinateRing

variable {F : Type*} [Field F] {W : Affine F} [W.IsElliptic]

/-! ### Translation by an arbitrary point, on constants and past `[n]∗` -/

/-- **`τ_P∗` fixes the base field**, at every `P` — the `O` case is `RingHom.id` and the affine case
is the merged `translateEndo_algebraMap_base`. -/
lemma translatePointEndo_algebraMap_base (P : W.Point) (c : F) :
    translatePointEndo P (algebraMap F W.FunctionField c) = algebraMap F W.FunctionField c := by
  match P with
  | .zero => rfl
  | .some x y h => exact translateEndo_algebraMap_base h.left c

open Classical in
/-- **`τ_P∗ ([n]∗ f) = [n]∗ (τ_T∗ f)` whenever `[n]P = T`**, with neither point assumed affine.

The merged `translateEndo_mulByNEndo_apply_of_baseField` says this for two affine points and
`translateEndo_mulByNEndo_apply_torsion_of_baseField` says it when `[n]P = O`; the remaining case
`P = O` forces `T = O` and both sides are `[n]∗ f`.  Stating it at `translatePointEndo` is what lets
a `Finset.range n`-indexed product use it at every `i`, including `i = 0`. -/
theorem translatePointEndo_mulByNEndo_apply (n : ℕ)
    (hn : Transcendental F (n • genericPoint (W := W)).xCoord)
    (P T : W.Point) (hmul : n • P = T) (f : W.FunctionField) :
    translatePointEndo P (mulByNEndo n hn f) = mulByNEndo n hn (translatePointEndo T f) := by
  have hz : (Point.zero : W.Point) = 0 := rfl
  match P, T, hmul with
  | .zero, T, hmul =>
      rw [hz, smul_zero] at hmul
      rw [hz, ← hmul, translatePointEndo_zero]
      rfl
  | .some xP yP hP, .zero, hmul =>
      rw [translatePointEndo_some, hz, translatePointEndo_zero]
      exact translateEndo_mulByNEndo_apply_torsion_of_baseField hP.left n hn hmul f
  | .some xP yP hP, .some xT yT hT, hmul =>
      rw [translatePointEndo_some, translatePointEndo_some]
      exact translateEndo_mulByNEndo_apply_of_baseField hP.left hT.left n hn hmul f

/-! ### The base-change map on points is injective -/

open Classical in
/-- **`W.Point → (W ⁄ F(W)).Point` is injective.**  The merged `torsionPointMap_eq_zero_iff`
(`EllipticCurves.FunctionField.MulByNTranscendence`) is the kernel statement; this is the standard
promotion of it for a homomorphism of groups.

It is what turns the `translatePoint`-level group relations the merged `n = 2` and `n = 3`
workhorses take — `translatePoint hP + translatePoint hP = translatePoint h₂` and its `n = 3`
analogues — into the `W.Point`-level `n • P = T` the general workhorse takes. -/
lemma torsionPointMap_injective : Function.Injective (torsionPointMap (W := W)) := by
  intro P Q hPQ
  have hsub : torsionPointMap (W := W) (P - Q) = 0 := by rw [map_sub, hPQ, sub_self]
  exact sub_eq_zero.mp (torsionPointMap_eq_zero_iff.mp hsub)

end CoordinateRing

open CoordinateRing

variable {F : Type*} [Field F] {W : Affine F} [W.IsElliptic]

/-! ### The workhorse -/

open Classical in
/-- **Translation by `T` fixes the `n`-th root, at an arbitrary `n`.**

Given an `n`-division point `P` of `T` (`hPT : [n]P = T`), a function `f` whose translates over
`⟨T⟩` multiply to the nonzero constant `c` (`htel`), and a `g` with `c₀ · gⁿ = [n]∗ f` (`hpow`), the
conclusion is `τ_T∗ g = g`.

⚠️ `htel` is **not** produced here; at `n = 2` and `n = 3` it comes from
`EllipticCurves.FunctionField.WeilPairingTelescope{Two,Three}` and at general `n` nothing on this
tree produces it yet.  Nor is `P`: over an algebraically closed field it costs nothing, and over an
arbitrary one it is supplied by base change, as
`translateEndo_eq_self_of_mul_algebraMap_sq_eq_of_baseChange`
(`EllipticCurves.FunctionField.WeilPairingAlternatingBaseChange`) does at `n = 2`.

The whole content is the auxiliary function `w = ∏_{i<n} τ_{[i]P}∗ g`: its `n`-th power is a
constant, so `w` itself is, so `τ_P∗ w = w`, and the two ways of peeling a `range (n+1)` product
turn that into the conclusion. -/
theorem translatePointEndo_eq_self_of_prod_eq_of_pow_eq {n : ℕ} (hn0 : n ≠ 0)
    (hn : Transcendental F (n • genericPoint (W := W)).xCoord)
    {P T : W.Point} (hPT : n • P = T)
    {f g : W.FunctionField} (hg : g ≠ 0) {c c₀ : F} (hc : c ≠ 0) (hc₀ : c₀ ≠ 0)
    (htel : ∏ i ∈ Finset.range n, translatePointEndo (i • T) f = algebraMap F W.FunctionField c)
    (hpow : algebraMap F W.FunctionField c₀ * g ^ n = mulByNEndo n hn f) :
    translatePointEndo T g = g := by
  have hane : ∀ i : ℕ, translatePointEndo (i • P) g ≠ 0 := fun i hzz =>
    hg ((translatePointEndo (i • P)).injective (by rw [hzz, map_zero]))
  set w : W.FunctionField := ∏ i ∈ Finset.range n, translatePointEndo (i • P) g with hw
  have hwne : w ≠ 0 := Finset.prod_ne_zero_iff.mpr fun i _ => hane i
  -- Each factor of `w ^ n` is a `[n]∗`-image, by the commutation at `[n]([i]P) = [i]T`.
  have hstep : ∀ i ∈ Finset.range n,
      algebraMap F W.FunctionField c₀ * translatePointEndo (i • P) g ^ n
        = mulByNEndo n hn (translatePointEndo (i • T) f) := by
    intro i _
    have hcomm : n • (i • P) = i • T := by rw [← hPT, smul_comm]
    rw [← map_pow, ← translatePointEndo_algebraMap_base (i • P) c₀, ← map_mul, hpow,
      translatePointEndo_mulByNEndo_apply n hn (i • P) (i • T) hcomm]
  -- Hence `w ^ n` is the nonzero constant `c / c₀ ^ n`.
  have hkey : algebraMap F W.FunctionField (c₀ ^ n) * w ^ n = algebraMap F W.FunctionField c := by
    calc algebraMap F W.FunctionField (c₀ ^ n) * w ^ n
        = ∏ i ∈ Finset.range n,
            algebraMap F W.FunctionField c₀ * translatePointEndo (i • P) g ^ n := by
          rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range, Finset.prod_pow,
            map_pow, hw]
      _ = ∏ i ∈ Finset.range n, mulByNEndo n hn (translatePointEndo (i • T) f) :=
          Finset.prod_congr rfl hstep
      _ = mulByNEndo n hn (∏ i ∈ Finset.range n, translatePointEndo (i • T) f) :=
          (map_prod _ _ _).symm
      _ = algebraMap F W.FunctionField c := by rw [htel, mulByNEndo_algebraMap_base]
  -- So its projective divisor is `n`-torsion, hence trivial, hence `w` is a constant.
  have hc₀' : algebraMap F W.FunctionField (c₀ ^ n) ≠ 0 :=
    (map_ne_zero_iff _ (algebraMap F W.FunctionField).injective).mpr (pow_ne_zero n hc₀)
  have hdiv : n • divisorProj W w = 0 := by
    have hcongr := congrArg (divisorProj W) hkey
    rwa [divisorProj_mul hc₀' (pow_ne_zero n hwne),
      divisorProj_algebraMap_base (pow_ne_zero n hc₀), divisorProj_pow,
      divisorProj_algebraMap_base hc, zero_add] at hcongr
  have hzero : divisorProj W w = 0 := by
    ext p
    have hp : (n : ℤ) * divisorProj W w p = 0 := by
      simpa [nsmul_eq_mul] using congrArg (fun D : ProjPoint W →₀ ℤ => D p) hdiv
    simp only [Finsupp.coe_zero, Pi.zero_apply]
    exact (mul_eq_zero.mp hp).resolve_left (Int.natCast_ne_zero.mpr hn0)
  obtain ⟨c₁, -, hconst⟩ := (divisorProj_eq_zero_iff hwne).mp hzero
  -- A constant is fixed by `τ_P∗`, and peeling the product from the bottom rather than the top
  -- turns that fixedness into the statement.
  have hfix : translatePointEndo P w = w := by
    rw [hconst, translatePointEndo_algebraMap_base]
  have hshiftl : translatePointEndo P w
      = ∏ i ∈ Finset.range n, translatePointEndo ((i + 1) • P) g := by
    rw [hw, map_prod]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [translatePointEndo_apply_apply]
    congr 1
    rw [succ_nsmul, add_comm]
  have hrange : (∏ i ∈ Finset.range n, translatePointEndo ((i + 1) • P) g)
      * translatePointEndo ((0 : ℕ) • P) g
      = (∏ i ∈ Finset.range n, translatePointEndo (i • P) g) * translatePointEndo (n • P) g := by
    rw [← Finset.prod_range_succ' (fun i => translatePointEndo (i • P) g) n,
      ← Finset.prod_range_succ (fun i => translatePointEndo (i • P) g) n]
  rw [hshiftl] at hfix
  rw [hfix, zero_smul, translatePointEndo_zero, RingHom.id_apply, hPT, ← hw] at hrange
  exact mul_left_cancel₀ hwne hrange.symm

/-! ### Recovery of the merged `n = 2` and `n = 3` workhorses

`#907`'s rule: a general form is only worth having if the merged statements it replaces come back
out of it unchanged.  Both do, and the two statements below are their signatures character for
character, ambient `variable` line included. -/

section Recovery

variable {F : Type*} [Field F] {W : Affine F} [W.IsElliptic]
  [IsDedekindDomain W.CoordinateRing] {x₂ y₂ x₃ y₃ : F}

-- ⚠️ `[IsDedekindDomain W.CoordinateRing]` is deliberately kept even though neither statement below
-- uses it: both merged originals carry it (their proofs go through `divisorProj`), so dropping it
-- would change the elaborated type and the recovery would no longer be a recovery.  The linter is
-- silenced for that reason and no other.
set_option linter.unusedSectionVars false in
open Classical in
/-- `translateEndo_eq_self_of_mul_algebraMap_sq_eq`
(`EllipticCurves.FunctionField.WeilPairingAlternatingTwo`), recovered.

`hdouble` lives in `(W ⁄ F(W)).Point` and the general form wants `[2]P = T` in `W.Point`;
`torsionPointMap_injective` is the bridge.  The two-factor telescope `f · τ_T∗ f` is the
`Finset.range 2` product with the `i = 0` factor `τ_O∗ f = f` written out. -/
private theorem translateEndo_eq_self_of_mul_algebraMap_sq_eq_of_general (h2 : (2 : F) ≠ 0)
    {xP yP : F} (hP : W.Equation xP yP) (h₂ : W.Equation x₂ y₂)
    (hdouble : translatePoint hP + translatePoint hP = translatePoint h₂)
    {f g : W.FunctionField} (hg : g ≠ 0) {c c₀ : F} (hc : c ≠ 0) (hc₀ : c₀ ≠ 0)
    (htel : f * translateEndo h₂ f = algebraMap F W.FunctionField c)
    (hsq : algebraMap F W.FunctionField c₀ * g ^ 2 = mulByTwoEndo h2 f) :
    translateEndo h₂ g = g := by
  have hPT : (2 : ℕ) • torsionPoint hP = torsionPoint h₂ :=
    torsionPointMap_injective <| by
      rw [map_nsmul, torsionPointMap_torsionPoint, torsionPointMap_torsionPoint, two_nsmul,
        hdouble]
  have key := translatePointEndo_eq_self_of_prod_eq_of_pow_eq (n := 2) (P := torsionPoint hP)
    (T := torsionPoint h₂) two_ne_zero (transcendental_xCoord_two_nsmul h2) hPT hg hc hc₀
    (by
      rw [Finset.prod_range_succ, Finset.prod_range_one, zero_smul, translatePointEndo_zero,
        RingHom.id_apply, one_smul, translatePointEndo_torsionPoint]
      exact htel)
    (by rw [mulByNEndo_two h2]; exact hsq)
  rwa [translatePointEndo_torsionPoint] at key

set_option linter.unusedSectionVars false in
open Classical in
/-- `translateEndo_eq_self_of_mul_algebraMap_cube_eq`
(`EllipticCurves.FunctionField.WeilPairingAlternatingThree`), recovered.

⚠️ The merged telescope's third factor translates by `−T` and the uniform product's translates by
`[2]T`.  They agree **because** `[3]T = O`, which is exactly what `htors` says — so the `n = 3`
recovery consumes a hypothesis the `n = 2` one does not, and it consumes it for this reason rather
than for the reason the merged proof does. -/
private theorem translateEndo_eq_self_of_mul_algebraMap_cube_eq_of_general (h2 : (2 : F) ≠ 0)
    (h3 : (3 : F) ≠ 0) {xP yP xQ yQ : F} (hP : W.Equation xP yP) (hQ : W.Equation xQ yQ)
    (h₃ : W.Equation x₃ y₃)
    (hdouble : translatePoint hP + translatePoint hP = translatePoint hQ)
    (hsum : translatePoint hP + translatePoint hQ = translatePoint h₃)
    (htors : translatePoint h₃ + translatePoint h₃ + translatePoint h₃ = 0)
    {f g : W.FunctionField} (hg : g ≠ 0) {c c₀ : F} (hc : c ≠ 0) (hc₀ : c₀ ≠ 0)
    (htel : f * translateEndo h₃ f * translateEndo ((W.equation_neg x₃ y₃).mpr h₃) f
      = algebraMap F W.FunctionField c)
    (hcube : algebraMap F W.FunctionField c₀ * g ^ 3 = mulByThreeEndo h2 h3 f) :
    translateEndo h₃ g = g := by
  have hPT : (3 : ℕ) • torsionPoint hP = torsionPoint h₃ :=
    torsionPointMap_injective <| by
      rw [map_nsmul, torsionPointMap_torsionPoint, torsionPointMap_torsionPoint,
        show (3 : ℕ) • translatePoint hP = translatePoint hP + translatePoint hP
          + translatePoint hP by rw [succ_nsmul, two_nsmul], hdouble, add_comm]
      exact hsum
  have hneg : (2 : ℕ) • torsionPoint h₃ = torsionPoint ((W.equation_neg x₃ y₃).mpr h₃) :=
    torsionPointMap_injective <| by
      rw [map_nsmul, torsionPointMap_torsionPoint, torsionPointMap_torsionPoint,
        translatePoint_neg h₃, two_nsmul, ← add_eq_zero_iff_eq_neg]
      exact htors
  have key := translatePointEndo_eq_self_of_prod_eq_of_pow_eq (n := 3) (P := torsionPoint hP)
    (T := torsionPoint h₃) three_ne_zero (transcendental_xCoord_three_nsmul h2 h3) hPT hg hc hc₀
    (by
      rw [Finset.prod_range_succ, Finset.prod_range_succ, Finset.prod_range_one, zero_smul,
        translatePointEndo_zero, RingHom.id_apply, one_smul, translatePointEndo_torsionPoint,
        hneg, translatePointEndo_torsionPoint]
      exact htel)
    (by rw [mulByNEndo_three h2 h3]; exact hcube)
  rwa [translatePointEndo_torsionPoint] at key

end Recovery

/-! ### Non-vacuity

The certificates run at `n = 4`, an index no merged workhorse reaches, on `y² = x³ + 1` over `ℚ`
with `P = (2, 3)` and `T = [4]P = (0, −1)`.  ⚠️ The arithmetic duplicates the `Nonvacuity` block of
`EllipticCurves.FunctionField.TranslationMulByNCommGeneral`, whose lemmas are `private` and
therefore unavailable; it is re-derived rather than imported.

There are **two** certificates: one instantiated at `f = g = c = c₀ = 1`, which certifies that the
hypothesis list is jointly satisfiable, and one that binds `htel` and `hpow` and so reaches the
conclusion the theorem is actually for.  Instantiating at `1` lets the theorem generate the types
of `htel` and `hpow` itself, leaving one `convert` on `hPT`.

⚠️ **This block used to carry only the first, and the reason it gave was half right** (`#1415`).
It said that a certificate binding `htel` and `hpow` writes their types in `ℚ`'s own `DecidableEq`
instance while the theorem's copies carry `Classical.propDecidable`, so *"every hypothesis then
needs its own `convert … using 9` and the elaboration does not terminate inside the heartbeat
budget"*.

The **mechanism** is right, and so is the timeout, which is now measured rather than inferred:
passing `htel` and `hpow` with no `convert` at all still times out at `maxHeartbeats 4000000`,
twenty times the default, after about 250 s.  What is wrong is the **depth**, and hence the
conclusion.  `9` is the depth that works on `hPT`; on `htel` and `hpow` it leaves `unsolved goals`,
and so does **every** depth from `1` to `11`.  At **`using 12`** both close, as do `13` and `14`,
so `12` is the **minimum**, and the parameterised certificate was affordable all along.  ⚠️ The
scan is exhaustive below `12` only because PR #539's non-author review filled in `1`, `3` and `5`,
which the author's scan had skipped; the shipped list read *"`2`, `4`, `6`, `7`, `8`, `10` and
`11`"* and did not rule out a smaller working depth.  ⚠️ The depth was found by scanning, not
derived — and minimality is one more measurement, not an explanation of it: the
`HSMul → … → AddCommGroup` chain quoted below accounts for `9` at `hPT` and does not predict `12`
here, so do not read one off the other.

At depth `12` this file elaborates in about 3.8 s **on the authoring box**; three warm runs of the
same file on the reviewer's gave 4.4 / 6.7 / 7.1 s.  The figure is pinned to a machine and is kept
only because the contrast it draws is with the 250 s timeout above, not with any other depth.

⚠️ Through the **affine** corollary in
`EllipticCurves.FunctionField.WeilPairingAlternatingConsumerN` the same certificate needs only a
single `convert`, because `htel` is stated with `translateEndo hT` and the point-level `n • ·` then
occurs once, on `hmul`.  That file's diagnosis of the difference is correct and the difference is
real; it is one `convert` against one per hypothesis, not affordable against unaffordable.
`#1328`'s route is cheaper still — stating the theorem with `[DecidableEq F]` as an instance binder
rather than `open Classical in` removes the `convert`s entirely, and its `n = 6` certificate has
none — but retrofitting this theorem to it is a separate call and is deliberately not made here. -/

namespace Nonvacuity

/-! The certificate curve `y² = x³ + 1` is the shared `EllipticCurves.Fixture.y2EqX3AddOne`, whose
single `[CharZero F]` instance also supplies `IsElliptic` here. -/

open EllipticCurves.Fixture

/-- `P = (2, 3)` lies on `y² = x³ + 1`. -/
private lemma exampleEqP : (y2EqX3AddOne ℚ).Equation 2 3 := by
  norm_num [y2EqX3AddOne, WeierstrassCurve.Affine.equation_iff]

/-- `[2]P = (0, 1)`. -/
private lemma exampleEqTwoP : (y2EqX3AddOne ℚ).Equation 0 1 := by
  norm_num [y2EqX3AddOne, WeierstrassCurve.Affine.equation_iff]

/-- `[3]P = (-1, 0)`. -/
private lemma exampleEqThreeP : (y2EqX3AddOne ℚ).Equation (-1) 0 := by
  norm_num [y2EqX3AddOne, WeierstrassCurve.Affine.equation_iff]

/-- `T = [4]P = (0, -1)` lies on `y² = x³ + 1`. -/
private lemma exampleEqT : (y2EqX3AddOne ℚ).Equation 0 (-1) := by
  norm_num [y2EqX3AddOne, WeierstrassCurve.Affine.equation_iff]

open Classical in
/-- `[4](2, 3) = (0, −1)`: the tangent at `P` has slope `2`, giving `[2]P = (0, 1)`; the secant
through `(0, 1)` and `(2, 3)` has slope `1`, giving `[3]P = (−1, 0)`; the secant through `(−1, 0)`
and `(2, 3)` has slope `1`, giving `[4]P = (0, −1)`. -/
private lemma exampleQuadruple :
    (4 : ℕ) • torsionPoint exampleEqP = torsionPoint exampleEqT := by
  have hy : (3 : ℚ) ≠ (y2EqX3AddOne ℚ).negY 2 3 := by
    norm_num [y2EqX3AddOne, WeierstrassCurve.Affine.negY]
  have hdouble : Point.some (2 : ℚ) 3
        ((y2EqX3AddOne ℚ).equation_iff_nonsingular.mp exampleEqP)
      + Point.some (2 : ℚ) 3 ((y2EqX3AddOne ℚ).equation_iff_nonsingular.mp exampleEqP)
      = Point.some (0 : ℚ) 1 ((y2EqX3AddOne ℚ).equation_iff_nonsingular.mp exampleEqTwoP) := by
    rw [Point.add_self_of_Y_ne hy, Point.some.injEq]
    constructor <;>
      norm_num [y2EqX3AddOne, WeierstrassCurve.Affine.addX, WeierstrassCurve.Affine.addY,
        WeierstrassCurve.Affine.negAddY, WeierstrassCurve.Affine.negY,
        WeierstrassCurve.Affine.slope]
  have hx : (0 : ℚ) ≠ 2 := by norm_num
  have hsecant : Point.some (0 : ℚ) 1
        ((y2EqX3AddOne ℚ).equation_iff_nonsingular.mp exampleEqTwoP)
      + Point.some (2 : ℚ) 3 ((y2EqX3AddOne ℚ).equation_iff_nonsingular.mp exampleEqP)
      = Point.some (-1 : ℚ) 0 ((y2EqX3AddOne ℚ).equation_iff_nonsingular.mp exampleEqThreeP) := by
    rw [Point.add_of_X_ne hx, Point.some.injEq]
    constructor <;>
      norm_num [y2EqX3AddOne, WeierstrassCurve.Affine.addX, WeierstrassCurve.Affine.addY,
        WeierstrassCurve.Affine.negAddY, WeierstrassCurve.Affine.negY,
        WeierstrassCurve.Affine.slope]
  have hx' : (-1 : ℚ) ≠ 2 := by norm_num
  have hsecant' : Point.some (-1 : ℚ) 0
        ((y2EqX3AddOne ℚ).equation_iff_nonsingular.mp exampleEqThreeP)
      + Point.some (2 : ℚ) 3 ((y2EqX3AddOne ℚ).equation_iff_nonsingular.mp exampleEqP)
      = Point.some (0 : ℚ) (-1) ((y2EqX3AddOne ℚ).equation_iff_nonsingular.mp exampleEqT) := by
    rw [Point.add_of_X_ne hx', Point.some.injEq]
    constructor <;>
      norm_num [y2EqX3AddOne, WeierstrassCurve.Affine.addX, WeierstrassCurve.Affine.addY,
        WeierstrassCurve.Affine.negAddY, WeierstrassCurve.Affine.negY,
        WeierstrassCurve.Affine.slope]
  change (4 : ℕ) • Point.some (2 : ℚ) 3 _ = Point.some (0 : ℚ) (-1) _
  rw [show (4 : ℕ) = 3 + 1 from rfl, succ_nsmul, show (3 : ℕ) = 2 + 1 from rfl, succ_nsmul,
    two_nsmul, hdouble, hsecant, hsecant']

open Classical in
/-- `P = (2, 3)` is not `4`-torsion, which is what discharges the transcendence hypothesis. -/
private lemma exampleNotFourTorsion : (4 : ℕ) • torsionPoint exampleEqP ≠ 0 := by
  rw [exampleQuadruple, torsionPoint]
  exact fun h => by simp at h

-- ⚠️ The `convert … using 9` below is bookkeeping, not mathematics.  The general statements are
-- elaborated `open Classical in` at an abstract `F`, so `n • ·` on `W.Point` carries
-- `Classical.propDecidable`; the certificates are elaborated at `F = ℚ`, where `instDecidableEqRat`
-- wins on priority.  Depth `9` reaches `Point.instAddCommGroup`'s own `DecidableEq` argument, since
-- `n • x` goes through `HSMul → SMul → NSMul → AddMonoid → SubNegMonoid → AddGroup → AddCommGroup`.
-- This is the same note as `TranslationMulByNCommGeneral`'s Nonvacuity block.
open Classical in
/-- The transcendence hypothesis at `n = 4` over `ℚ`, discharged by `P` itself. -/
private lemma exampleTranscendentalFour :
    Transcendental ℚ ((4 : ℕ) • genericPoint (W := y2EqX3AddOne ℚ)).xCoord :=
  transcendental_xCoord_nsmul_genericPoint 4 (T := torsionPoint exampleEqP)
    (by convert exampleNotFourTorsion using 9)

open Classical in
/-- `T = [4]P = (0, −1)` is not the point at infinity, so the certificate below is not the
degenerate `T = O` instance in which `τ_T∗` is the identity by definition. -/
private lemma exampleTNeZero : torsionPoint exampleEqT ≠ (0 : (y2EqX3AddOne ℚ).Point) := by
  rw [torsionPoint]
  exact fun h => by simp at h

open Classical in
/-- **The workhorse applies at `n = 4` on a curve over `ℚ`**, an index no merged workhorse reaches,
at a `T` that is not the point at infinity and a `P` that is not `4`-torsion — so `hn0`, `hn` and
`hPT` are simultaneously inhabited there, and `mulByNEndo 4` is a genuine `[4]∗`.

⚠️ The instance is taken at `f = g = c = c₀ = 1`, which discharges `htel` and `hpow` outright and so
certifies that the hypothesis set is **jointly satisfiable**, not merely non-contradictory.  Stated
for what it is: with `g = 1` the conclusion `τ_T∗ 1 = 1` is trivially true, so this says nothing
about the case the theorem is *for*.  What it does say is that nothing in the hypothesis list rules
the others out at `n = 4`, which is the failure mode a general-`n` statement actually has. -/
example : translatePointEndo (torsionPoint exampleEqT) (1 : (y2EqX3AddOne ℚ).FunctionField) = 1 :=
  translatePointEndo_eq_self_of_prod_eq_of_pow_eq (n := 4) (P := torsionPoint exampleEqP)
    (T := torsionPoint exampleEqT) (f := 1) (g := 1) (c := 1) (c₀ := 1) (by norm_num)
    exampleTranscendentalFour (by convert exampleQuadruple using 9) one_ne_zero one_ne_zero
    one_ne_zero (by rw [map_one]; exact Finset.prod_eq_one fun i _ => map_one _)
    (by rw [map_one, one_pow, one_mul, map_one])

open Classical in
/-- **The same instance at `n = 4` with `htel` and `hpow` left BOUND**, which is the shape the
theorem is for: the conclusion `τ_T∗ g = g` is not trivially true here, because `g` is an arbitrary
non-zero element rather than `1`.

⚠️ **Still hypothetical**: `htel`, `hpow`, `hg`, `hc` and `hc₀` are assumed, exactly as at the
merged `n = 2` and `n = 3`.  What is **discharged** is `hn0`, the transcendence hypothesis `hn` and
the point relation `hmul`, the last from `exampleQuadruple` on a curve chosen so that `[4]P` is
affine and distinct from `P`.  ⚠️ It does **not** exhibit a real telescope at `n = 4` — nothing on
this tree produces one yet — so it says the hypothesis list is reachable at an index no merged
workhorse covers, not that the theorem fires there.

⚠️ `convert … using 12` is the depth this shape needs; `using 9`, which is right for `hPT` above,
leaves `unsolved goals` on both.  See the block docstring. -/
example (f g : (y2EqX3AddOne ℚ).FunctionField) (hg : g ≠ 0) (c c₀ : ℚ) (hc : c ≠ 0) (hc₀ : c₀ ≠ 0)
    (htel : ∏ i ∈ Finset.range 4,
        translatePointEndo (i • torsionPoint exampleEqT) f =
          algebraMap ℚ (y2EqX3AddOne ℚ).FunctionField c)
    (hpow : algebraMap ℚ (y2EqX3AddOne ℚ).FunctionField c₀ * g ^ 4 =
      mulByNEndo 4 exampleTranscendentalFour f) :
    translatePointEndo (torsionPoint exampleEqT) g = g :=
  translatePointEndo_eq_self_of_prod_eq_of_pow_eq (n := 4) (P := torsionPoint exampleEqP)
    (T := torsionPoint exampleEqT) (by norm_num) exampleTranscendentalFour
    (by convert exampleQuadruple using 9) hg hc hc₀ (by convert htel using 12)
    (by convert hpow using 12)

end Nonvacuity

end WeierstrassCurve.Affine
