/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import EllipticCurves.FunctionField.MulByNComposition
import EllipticCurves.FunctionField.TranslationMulByNCommGeneral
import EllipticCurves.FunctionField.TranslationPointEndomorphism
import EllipticCurves.FunctionField.WeilPairingAlternatingThree

/-!
# The alternating workhorse at an ARBITRARY `n` (Silverman III.8.1(d), the second product)

`EllipticCurves.FunctionField.WeilPairingAlternatingTwo` and
`…AlternatingThree` prove

```
τ_T∗ g = g       from      ∏ᵢ τ_{[i]T}∗ f = c   and   c₀ · g ^ n = [n]∗ f
```

at `n = 2` and `n = 3`.  This file proves it at **every** `n`.

## ⚠️ This is not a numeral strip, and the reason it is reachable anyway is not the obvious one

`#1317` recorded that this family is *"genuinely `n`-dependent, not a numeral"*, and **that is
true**: the product `∏ᵢ τ_{[i]P}∗ g` has `n` factors, so no transcription of the merged proof
produces the general one.  What does not follow is that it is *blocked*.  An `n`-fold product is a
`Finset.prod` over `Finset.range n`.

⚠️ **The real obstruction was never the factor count — it was that `τ` is only defined at affine
points.**  The merged `n = 3` statement has to carry a *second* point `Q` with `[2]P = Q` as an
explicit hypothesis for exactly this reason, and scaling that to general `n` would need an affine
witness for every interior multiple `[i]P`, `0 < i < n`.
`EllipticCurves.FunctionField.TranslationPointEndomorphism`'s module docstring shows that family
**does not exist in general**: `[i]P` can be `O` while `T = [n]P` is a perfectly good affine point,
first at `n = 6`.

⚠️ **And that file was built to remove the obstruction and then never consumed.**
`translatePointEndo : W.Point → (F(W) →+* F(W))` is total, `translatePointEndo_comp` is the
composition law with **no** side condition, and `translatePointEndo_nsmul_apply` is
`τ_{n • P}∗ = (τ_P∗)^[n]`.  Its docstring says outright that the product
`∏_{i=0}^{n-1} g ∘ τ_{[i]P}` *"needs `τ_{n • P}∗` in terms of `τ_P∗`"*.  Stating the workhorse over
`W.Point` rather than over `W.Equation` is the whole content of this file: **nothing below ever
names an affine witness for an interior multiple.**

## The proof

1. `c₀ · ((τ_P∗)^[i] g) ^ n = [n]∗ ((τ_T∗)^[i] f)` for every `i`, by induction — each step is one
   application of the commutation at `P` alone.  ⚠️ This is the step where a family of affine
   witnesses would have been needed, and it is where the iterate replaces it.
2. Multiplying those over `i < n`: `c₀ ^ n · h ^ n = [n]∗ (∏ᵢ (τ_T∗)^[i] f) = [n]∗ c = c`, where
   `h := ∏_{i < n} (τ_P∗)^[i] g`.
3. So `n • divisorProj h = 0`, hence `divisorProj h = 0`, hence `h` is a nonzero constant — the
   merged `n = 2` argument with `2` replaced by `n`.
4. A constant is fixed by `τ_P∗`, and both `h` and `τ_P∗ h` split off the same
   `∏_{1 ≤ i < n} (τ_P∗)^[i] g`, so cancelling it leaves `(τ_P∗)^[n] g = g`.
5. `(τ_P∗)^[n] = τ_{n • P}∗`.

## Main statements

* `WeierstrassCurve.Affine.translatePointEndo_eq_self_of_mul_algebraMap_pow_eq` — the workhorse over
  an arbitrary `P : W.Point`, with the commutation as a hypothesis;
* `WeierstrassCurve.Affine.translateEndo_eq_self_of_mul_algebraMap_pow_eq` — the form a consumer
  wants, indexed by affine `P` and `T` with `n • T_P = T_T` over the base field, the commutation
  discharged by `translateEndo_mulByNEndo_apply_general`;
* `WeierstrassCurve.Affine.translateEndo_eq_self_of_mul_algebraMap_pow_eq_of_smooth` — the same at
  every `3`-smooth `n ≠ 0`, with the non-constancy hypothesis discharged.

## ⚠️ What is NOT here

**The alternating *assembly* at general `n`, and it is not reachable.**  The assembly's input is the
telescope `∏_{i < n} τ_{[i]T}∗ f = c`, and its producer `exists_mul_translateEndo_eq_algebraMap`
exists only in `EllipticCurves.FunctionField.WeilPairingTelescopeTwo` and `…TelescopeThree` — there
is no general-`n` telescope on this tree.  The workhorse takes the telescope as a **hypothesis**,
exactly as both merged workhorses do, which is what makes it shippable today.

⚠️ **This does not touch `#899`.**  That gate is `[IsAlgClosed F]` entering the *assembly*, through
`hprin` and through the rational halving point.  The workhorse never had an `[IsAlgClosed F]` at
`n = 2, 3` and the general form does not either; what is refuted here is only the numeral gate.

Also out: any edit to `WeilPairingAlternatingTwo`, `…Three`, `TranslationPointEndomorphism` or the
telescope files; the antisymmetry family; `ωₙ` (`#404`), Ward (`#260`), `#251`.

## Recovery, and Non-vacuity

`Recovery` derives **both** merged workhorses from the general form, each its merged twin
**verbatim**, binders included; the elaborator performs the check so no reader has to take *"the
merged proof with the numeral removed"* on faith.  `Nonvacuity` instantiates the `3`-smooth
corollary at **`n = 4`**, an index no merged alternating statement reaches.

## References

* [J. H. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.8.1(d).
-/

open Polynomial IsDedekindDomain

namespace WeierstrassCurve.Affine

open CoordinateRing

variable {F : Type*} [Field F] {W : Affine F} [W.IsElliptic]

/-! ### Two facts about `translatePointEndo` that its own file does not state

⚠️ They live here rather than in `EllipticCurves.FunctionField.TranslationPointEndomorphism`: that
file sits well below the whole Weil-pairing front, and moving these down would put its consumers
under it for no gain.  This is `#1317`'s and `#1321`'s placement rule. -/

/-- **`τ_P∗` fixes the constants**, at every point including `O`.  The affine case is the merged
`translateEndo_algebraMap_base`; at the point at infinity `τ_O∗` is the identity by `rfl`. -/
lemma translatePointEndo_algebraMap_base (P : W.Point) (c : F) :
    translatePointEndo P (algebraMap F W.FunctionField c) = algebraMap F W.FunctionField c := by
  cases P with
  | zero => rfl
  | some x y h => exact translateEndo_algebraMap_base h.left c

/-- `τ_P∗` is a ring homomorphism of fields, hence injective, hence so is every iterate. -/
lemma translatePointEndo_ne_zero {P : W.Point} {f : W.FunctionField} (hf : f ≠ 0) :
    translatePointEndo P f ≠ 0 := fun hz =>
  hf ((translatePointEndo P).injective (by rw [hz, map_zero]))

/-- The iterated form of `translatePointEndo_ne_zero`, which is what the `n`-factor product needs
in order to be nonzero. -/
lemma translatePointEndo_iterate_ne_zero (P : W.Point) {f : W.FunctionField} (hf : f ≠ 0) :
    ∀ i : ℕ, (translatePointEndo P)^[i] f ≠ 0
  | 0 => by simpa using hf
  | i + 1 => by
      rw [Function.iterate_succ_apply']
      exact translatePointEndo_ne_zero (translatePointEndo_iterate_ne_zero P hf i)

/-! ### The workhorse at an arbitrary `n` -/

open Classical in
/-- **The second product of Silverman III.8.1(d), at an arbitrary `n`.**

Given the telescoping constant `∏_{i < n} τ_T∗^[i] f = c`, an `n`-th root `c₀ · g ^ n = [n]∗ f`, and
a point `P` — possibly `O`, and with no affine witness demanded of any of its multiples — whose
`n`-th multiple is `T` and at which `[n]∗` commutes with translation, the translate `τ_T∗` fixes
`g`.

Every hypothesis is explicit and the statement is over an arbitrary field: no `[IsAlgClosed F]`, no
`#418`.  That is the merged arrangement at `n = 2, 3`, preserved.

⚠️ `hcomm` is the *only* place `P` interacts with `[n]∗`, and it is used at `P` alone — never at an
interior multiple.  That is what makes the general case no harder than `n = 2`; see the module
docstring. -/
theorem translatePointEndo_eq_self_of_mul_algebraMap_pow_eq
    {n : ℕ} (hnz : n ≠ 0) (hn : Transcendental F (n • genericPoint (W := W)).xCoord)
    (P : W.Point)
    (hcomm : ∀ z : W.FunctionField, translatePointEndo P (mulByNEndo n hn z)
      = mulByNEndo n hn (translatePointEndo (n • P) z))
    {f g : W.FunctionField} (hg : g ≠ 0) {c c₀ : F} (hc : c ≠ 0) (hc₀ : c₀ ≠ 0)
    (htel : ∏ i ∈ Finset.range n, (translatePointEndo (n • P))^[i] f
      = algebraMap F W.FunctionField c)
    (hpow : algebraMap F W.FunctionField c₀ * g ^ n = mulByNEndo n hn f) :
    translatePointEndo (n • P) g = g := by
  -- Step 1: the `n`-th-root relation, translated `i` times.
  have hiter : ∀ i : ℕ, algebraMap F W.FunctionField c₀ * ((translatePointEndo P)^[i] g) ^ n
      = mulByNEndo n hn ((translatePointEndo (n • P))^[i] f) := by
    intro i
    induction i with
    | zero => simpa using hpow
    | succ i ih =>
        have h1 := congrArg (translatePointEndo P) ih
        rw [map_mul, map_pow, translatePointEndo_algebraMap_base, hcomm] at h1
        rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
        exact h1
  -- Step 2: the `n`-factor product, and the constant its `n`-th power is.
  set h : W.FunctionField := ∏ i ∈ Finset.range n, (translatePointEndo P)^[i] g with hh
  have hhne : h ≠ 0 := by
    rw [hh]
    exact Finset.prod_ne_zero_iff.mpr fun i _ => translatePointEndo_iterate_ne_zero P hg i
  have hkey : algebraMap F W.FunctionField (c₀ ^ n) * h ^ n
      = algebraMap F W.FunctionField c := by
    have hsplit : algebraMap F W.FunctionField (c₀ ^ n) * h ^ n
        = ∏ i ∈ Finset.range n,
            (algebraMap F W.FunctionField c₀ * ((translatePointEndo P)^[i] g) ^ n) := by
      rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range, hh, ← Finset.prod_pow,
        map_pow]
    rw [hsplit]
    simp only [hiter]
    rw [← map_prod, htel, mulByNEndo_algebraMap_base]
  -- Step 3: trivial projective divisor, so `h` is a nonzero constant.
  have hc₀' : algebraMap F W.FunctionField (c₀ ^ n) ≠ 0 :=
    (map_ne_zero_iff _ (algebraMap F W.FunctionField).injective).mpr (pow_ne_zero n hc₀)
  have hdiv : n • divisorProj W h = 0 := by
    have hcongr := congrArg (divisorProj W) hkey
    rwa [divisorProj_mul hc₀' (pow_ne_zero n hhne),
      divisorProj_algebraMap_base (pow_ne_zero n hc₀), divisorProj_pow,
      divisorProj_algebraMap_base hc, zero_add] at hcongr
  have hzero : divisorProj W h = 0 := by
    ext p
    have hp : (n : ℤ) * divisorProj W h p = 0 := by
      simpa [nsmul_eq_mul] using congrArg (fun D : ProjPoint W →₀ ℤ => D p) hdiv
    simpa only [Finsupp.coe_zero, Pi.zero_apply] using
      (mul_eq_zero.mp hp).resolve_left (Int.natCast_ne_zero.mpr hnz)
  obtain ⟨c₁, -, hconst⟩ := (divisorProj_eq_zero_iff hhne).mp hzero
  -- Step 4: the constant is fixed by `τ_P∗`, and the product telescopes.
  have hfix : translatePointEndo P h = h := by
    rw [hconst, translatePointEndo_algebraMap_base]
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 :=
    ⟨n - 1, (Nat.succ_pred_eq_of_pos (Nat.pos_of_ne_zero hnz)).symm⟩
  set Q : W.FunctionField := ∏ i ∈ Finset.range m, (translatePointEndo P)^[i + 1] g with hQ
  have hQne : Q ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun i _ => translatePointEndo_iterate_ne_zero P hg (i + 1)
  have hsplit : h = Q * g := by
    rw [hh, Finset.prod_range_succ', hQ]; simp
  have hmapped : translatePointEndo P h = Q * (translatePointEndo P)^[m + 1] g := by
    rw [hh, map_prod, Finset.prod_range_succ, hQ]
    congr 1
    · exact Finset.prod_congr rfl fun i _ => (Function.iterate_succ_apply' _ i g).symm
    · exact (Function.iterate_succ_apply' _ m g).symm
  rw [hmapped, hsplit] at hfix
  -- Step 5: the iterate is translation by `n • P`.
  rw [translatePointEndo_nsmul_apply]
  exact mul_left_cancel₀ hQne hfix

/-! ### The affine form, which is what a consumer holds -/

open Classical in
/-- **The workhorse indexed by affine points**, the direct general-`n` analogue of the two merged
statements: `P` and `T` are affine, `n • P = T` over the base field, and the commutation is
discharged by `translateEndo_mulByNEndo_apply_general` rather than assumed.

⚠️ The relation is asked for at the **base-field** level (`torsionPoint`), not at the `F(W)` level
(`translatePoint`), because that is the form a caller has and because the two are interchangeable
through the injective `torsionPointMap`; the `Recovery` block below converts one merged hypothesis
each way. -/
theorem translateEndo_eq_self_of_mul_algebraMap_pow_eq
    {n : ℕ} (hnz : n ≠ 0) (hn : Transcendental F (n • genericPoint (W := W)).xCoord)
    {xP yP xT yT : F} (hP : W.Equation xP yP) (hT : W.Equation xT yT)
    (hmul : n • torsionPoint hP = torsionPoint hT)
    {f g : W.FunctionField} (hg : g ≠ 0) {c c₀ : F} (hc : c ≠ 0) (hc₀ : c₀ ≠ 0)
    (htel : ∏ i ∈ Finset.range n, (translateEndo hT)^[i] f = algebraMap F W.FunctionField c)
    (hpow : algebraMap F W.FunctionField c₀ * g ^ n = mulByNEndo n hn f) :
    translateEndo hT g = g := by
  have key := translatePointEndo_eq_self_of_mul_algebraMap_pow_eq hnz hn (torsionPoint hP)
    (fun z => by
      rw [hmul, translatePointEndo_torsionPoint, translatePointEndo_torsionPoint]
      exact translateEndo_mulByNEndo_apply_general hP hT n hn (by
        rw [← torsionPointMap_torsionPoint, ← torsionPointMap_torsionPoint, ← map_nsmul,
          hmul]) z)
    hg hc hc₀ (by rw [hmul, translatePointEndo_torsionPoint]; exact htel)
    hpow
  rwa [hmul, translatePointEndo_torsionPoint] at key

open Classical in
/-- **The workhorse at every `3`-smooth `n ≠ 0`**, with the non-constancy hypothesis discharged by
`transcendental_xCoord_nsmul_of_smooth`.

⚠️ The first index this does **not** cover is `n = 5`, for `exists_gS_of_smooth`'s reason and for
the reason every other `_of_smooth` corollary on this front stops there: the argument manufactures
no new prime. -/
theorem translateEndo_eq_self_of_mul_algebraMap_pow_eq_of_smooth
    (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) {n : ℕ} (hnz : n ≠ 0)
    (hfac : ∀ p ∈ n.primeFactors, p = 2 ∨ p = 3)
    {xP yP xT yT : F} (hP : W.Equation xP yP) (hT : W.Equation xT yT)
    (hmul : n • torsionPoint hP = torsionPoint hT)
    {f g : W.FunctionField} (hg : g ≠ 0) {c c₀ : F} (hc : c ≠ 0) (hc₀ : c₀ ≠ 0)
    (htel : ∏ i ∈ Finset.range n, (translateEndo hT)^[i] f = algebraMap F W.FunctionField c)
    (hpow : algebraMap F W.FunctionField c₀ * g ^ n
      = mulByNEndo n (transcendental_xCoord_nsmul_of_smooth h2 h3 hnz hfac) f) :
    translateEndo hT g = g :=
  translateEndo_eq_self_of_mul_algebraMap_pow_eq hnz _ hP hT hmul hg hc hc₀ htel hpow

/-! ### Recovery of the two merged workhorses

⚠️ Each statement below is its merged twin **verbatim** — binders, implicit/explicit split and
conclusion — and each is proved *through* the general form rather than re-proved.  It is the check
that separates a faithful generalisation from a new statement that merely resembles one, and the
elaborator performs it.

⚠️ Both are `private`: public copies would duplicate merged names.

⚠️ `variable [IsDedekindDomain W.CoordinateRing]` is **not** decoration.  The merged files do not
declare it and do not have the instance in their import closure, so it is auto-bound into both
merged signatures as an unnamed instance binder.  This file *does* have the instance, so without
that `variable` line the recovered statements would come out one binder **shorter** than their
twins — strictly stronger, and no longer verbatim.  Declaring it restores the merged signature
character for character, which is the only thing these declarations exist to certify.  Check the
result with `#check @…`, not by reading the source: an ambient instance binder is exactly what a
text comparison cannot see.

⚠️ Because the instance is synthesisable here, the binder is *included but unreferenced*, so
`linter.unusedSectionVars` fires on both recoveries and is disabled on each with this note.  Do not
"fix" that by deleting the `variable` line or by `omit`-ing the binder — that is precisely the edit
that breaks the verbatim property this block certifies. -/

open Classical in
/-- The base-field relation the general form asks for, from the `F(W)`-level relation the merged
statements carry.  ⚠️ `Point.map_injective` here is the **`AlgHom`** form
(`Mathlib/AlgebraicGeometry/EllipticCurve/Affine/Point.lean`), which is unconditional; the `RingHom`
form of the same name takes an injectivity argument and is not the one that applies.  Going through
`torsionPointMap` rather than the bare `Point.map` is what makes `map_nsmul` fire — the bare form is
a function, not an `AddMonoidHom`. -/
private lemma torsionPoint_nsmul_of_translatePoint {xP yP xT yT : F} (hP : W.Equation xP yP)
    (hT : W.Equation xT yT) {n : ℕ} (h : n • translatePoint hP = translatePoint hT) :
    n • torsionPoint hP = torsionPoint hT := by
  have hinj : Function.Injective (torsionPointMap (W := W)) :=
    Point.map_injective (W' := W) (f := (Algebra.ofId F W.FunctionField))
  apply hinj
  rw [map_nsmul, torsionPointMap_torsionPoint, torsionPointMap_torsionPoint]
  exact h

section Recovery

variable [IsDedekindDomain W.CoordinateRing] {x₂ y₂ x₃ y₃ : F}

set_option linter.unusedSectionVars false in
open Classical in
/-- `translateEndo_eq_self_of_mul_algebraMap_sq_eq`, recovered.

⚠️ The two-factor telescope `f · τ_T∗ f` is `∏ i ∈ range 2, (τ_T∗)^[i] f` after
`Finset.prod_range_succ`; the `i = 0` factor is `f` itself, which is why the merged statement does
not look like a product at all. -/
private theorem translateEndo_eq_self_of_mul_algebraMap_sq_eq_of_general
    (h2 : (2 : F) ≠ 0) {xP yP : F}
    (hP : W.Equation xP yP) (h₂ : W.Equation x₂ y₂)
    (hdouble : translatePoint hP + translatePoint hP = translatePoint h₂)
    {f g : W.FunctionField} (hg : g ≠ 0) {c c₀ : F} (hc : c ≠ 0) (hc₀ : c₀ ≠ 0)
    (htel : f * translateEndo h₂ f = algebraMap F W.FunctionField c)
    (hsq : algebraMap F W.FunctionField c₀ * g ^ 2 = mulByTwoEndo h2 f) :
    translateEndo h₂ g = g := by
  have hmul : (2 : ℕ) • torsionPoint hP = torsionPoint h₂ :=
    torsionPoint_nsmul_of_translatePoint (n := 2) hP h₂ (by rw [two_nsmul]; exact hdouble)
  exact translateEndo_eq_self_of_mul_algebraMap_pow_eq (n := 2) (by norm_num)
    (transcendental_xCoord_two_nsmul h2) hP h₂ hmul hg hc hc₀
    (by simpa [Finset.prod_range_succ] using htel)
    (by simpa only [mulByNEndo_two h2] using hsq)

set_option linter.unusedVariables false in
set_option linter.unusedSectionVars false in
open Classical in
/-- `translateEndo_eq_self_of_mul_algebraMap_cube_eq`, recovered.

⚠️ **`hQ`, `hdouble` and `hsum` are used only to produce `3 • T_P = T_T`.**  The auxiliary point `Q`
that the merged `n = 3` proof needs for its interior factor plays no part in the general argument —
it never names an interior multiple.  That is the concrete measure of what `translatePointEndo`
buys, and it says the merged hypothesis list is larger than its content requires.  `hQ` is therefore
genuinely unreferenced, and the `unusedVariables` linter is disabled for this declaration rather
than the binder dropped: dropping it would stop the statement being its merged twin verbatim, which
is the only thing this declaration exists to certify.

⚠️ `htors` is still needed, but for a different job: the merged telescope's third factor is written
as `τ_{−T}∗ f`, and identifying it with the general form's `(τ_T∗)^[2] f` is exactly `[2]T = −T`. -/
private theorem translateEndo_eq_self_of_mul_algebraMap_cube_eq_of_general
    (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0)
    {xP yP xQ yQ : F} (hP : W.Equation xP yP) (hQ : W.Equation xQ yQ) (h₃ : W.Equation x₃ y₃)
    (hdouble : translatePoint hP + translatePoint hP = translatePoint hQ)
    (hsum : translatePoint hP + translatePoint hQ = translatePoint h₃)
    (htors : translatePoint h₃ + translatePoint h₃ + translatePoint h₃ = 0)
    {f g : W.FunctionField} (hg : g ≠ 0) {c c₀ : F} (hc : c ≠ 0) (hc₀ : c₀ ≠ 0)
    (htel : f * translateEndo h₃ f * translateEndo ((W.equation_neg x₃ y₃).mpr h₃) f
      = algebraMap F W.FunctionField c)
    (hcube : algebraMap F W.FunctionField c₀ * g ^ 3 = mulByThreeEndo h2 h3 f) :
    translateEndo h₃ g = g := by
  have hmul : (3 : ℕ) • torsionPoint hP = torsionPoint h₃ :=
    torsionPoint_nsmul_of_translatePoint (n := 3) hP h₃ (by
      rw [show (3 : ℕ) = 2 + 1 from rfl, succ_nsmul, two_nsmul, hdouble, add_comm]; exact hsum)
  have hneg : (2 : ℕ) • torsionPoint h₃ = torsionPoint ((W.equation_neg x₃ y₃).mpr h₃) :=
    torsionPoint_nsmul_of_translatePoint (n := 2) h₃ ((W.equation_neg x₃ y₃).mpr h₃) (by
      rw [two_nsmul, add_eq_zero_iff_eq_neg.mp htors, translatePoint_neg h₃])
  exact translateEndo_eq_self_of_mul_algebraMap_pow_eq (n := 3) (by norm_num)
    (transcendental_xCoord_three_nsmul h2 h3) hP h₃ hmul hg hc hc₀
    (by
      simp only [Finset.prod_range_succ, Finset.prod_range_zero, one_mul,
        Function.iterate_zero_apply, Function.iterate_one]
      rw [show (translateEndo h₃)^[2] f
            = translatePointEndo ((2 : ℕ) • torsionPoint h₃) f from by
          rw [translatePointEndo_nsmul_apply, translatePointEndo_torsionPoint],
        hneg, translatePointEndo_torsionPoint]
      exact htel)
    (by simpa only [mulByNEndo_three h2 h3] using hcube)

end Recovery

/-! ### Non-vacuity at `n = 4`

⚠️ `n = 4` is reached by no merged alternating statement: `WeilPairingAlternatingTwo` and
`…AlternatingThree` are the whole family and both are numeral-indexed.

⚠️ **The curve is `y² = x³ + 1`, not this subtree's usual `y² = x³ − x`, and the reason is that the
usual one makes the certificate vacuous.**  On `y² = x³ − x` over `ℚ` every affine rational point is
`2`-torsion, so the only relation available at `n = 4` would be `4 • T = T` with `T` affine, which
is **false** — and a certificate with a false hypothesis proves nothing, `#916`'s lesson.  On
`y² = x³ + 1` the point `P = (2, 3)` has order `6`, so `[4]P = (0, −1)` is affine and *different*
from `P`: the base-field relation `4 • T_P = T_T` that the corollary takes is **discharged here, not
assumed**, on two distinct named affine points.

What remains hypothetical is exactly the three data every merged workhorse also assumes — the
telescope, the `n`-th root, and the nonzero constants.  Everything else (the elliptic instance,
`3`-smoothness at a composite index, both affine points, and the relation between them) is
inhabited. -/

section Nonvacuity

/-- The curve `y² = x³ + 1` over `ℚ`, of discriminant `−432`.  ⚠️ Deliberately not `y² = x³ − x`;
see the section docstring. -/
private def exampleCurve : Affine ℚ := ⟨0, 0, 0, 0, 1⟩

private instance : exampleCurve.IsElliptic := by
  rw [WeierstrassCurve.isElliptic_iff, isUnit_iff_ne_zero]
  norm_num [exampleCurve, WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈]

private lemma exampleTwo : (2 : ℚ) ≠ 0 := by norm_num

private lemma exampleThree : (3 : ℚ) ≠ 0 := by norm_num

/-- `4` is `3`-smooth.  ⚠️ Not `by decide`: the `Decidable` instance for the bounded quantifier over
`primeFactors` gets stuck (`#1213`).  This is `NthRootOfPullbackN`'s `primeFactors_four` idiom. -/
private lemma primeFactorsFour : ∀ p ∈ (4 : ℕ).primeFactors, p = 2 ∨ p = 3 := by
  intro p hp
  obtain ⟨hpp, hdvd, -⟩ := Nat.mem_primeFactors.mp hp
  rw [show (4 : ℕ) = 2 ^ 2 from rfl] at hdvd
  exact Or.inl ((Nat.prime_dvd_prime_iff_eq hpp Nat.prime_two).mp (hpp.dvd_of_dvd_pow hdvd))

/-- `P = (2, 3)`, a point of order `6`. -/
private lemma exampleEqP : exampleCurve.Equation 2 3 := by
  norm_num [exampleCurve, WeierstrassCurve.Affine.equation_iff]

/-- `[2]P = (0, 1)`. -/
private lemma exampleEqQ : exampleCurve.Equation 0 1 := by
  norm_num [exampleCurve, WeierstrassCurve.Affine.equation_iff]

/-- `T = [4]P = (0, −1)`, affine and distinct from `P`. -/
private lemma exampleEqT : exampleCurve.Equation 0 (-1) := by
  norm_num [exampleCurve, WeierstrassCurve.Affine.equation_iff]

open Classical in
/-- `[2](2, 3) = (0, 1)`: the tangent at `(2, 3)` has slope `2`, so `x([2]P) = 4 − 4 = 0`. -/
private lemma exampleDoubleP :
    torsionPoint exampleEqP + torsionPoint exampleEqP = torsionPoint exampleEqQ := by
  have hy : (3 : ℚ) ≠ exampleCurve.negY 2 3 := by
    norm_num [exampleCurve, WeierstrassCurve.Affine.negY]
  rw [torsionPoint, torsionPoint, Point.add_self_of_Y_ne hy, Point.some.injEq]
  refine ⟨?_, ?_⟩ <;>
    norm_num [exampleCurve, WeierstrassCurve.Affine.addX, WeierstrassCurve.Affine.addY,
      WeierstrassCurve.Affine.negAddY, WeierstrassCurve.Affine.negY,
      WeierstrassCurve.Affine.slope]

open Classical in
/-- `[2](0, 1) = (0, −1)`: the tangent at `(0, 1)` is horizontal, so `x` is unchanged and the
`y`-coordinate is negated. -/
private lemma exampleDoubleQ :
    torsionPoint exampleEqQ + torsionPoint exampleEqQ = torsionPoint exampleEqT := by
  have hy : (1 : ℚ) ≠ exampleCurve.negY 0 1 := by
    norm_num [exampleCurve, WeierstrassCurve.Affine.negY]
  rw [torsionPoint, torsionPoint, Point.add_self_of_Y_ne hy, Point.some.injEq]
  refine ⟨?_, ?_⟩ <;>
    norm_num [exampleCurve, WeierstrassCurve.Affine.addX, WeierstrassCurve.Affine.addY,
      WeierstrassCurve.Affine.negAddY, WeierstrassCurve.Affine.negY,
      WeierstrassCurve.Affine.slope]

open Classical in
/-- **`[4]P = T` on the nose**, from `[4] = [2] ∘ [2]`.  This is the hypothesis the corollary takes
and the reason this block is not vacuous. -/
private lemma exampleQuadruple :
    (4 : ℕ) • torsionPoint exampleEqP = torsionPoint exampleEqT := by
  rw [show (4 : ℕ) = 2 * 2 from rfl, mul_nsmul, two_nsmul (torsionPoint exampleEqP),
    exampleDoubleP, two_nsmul, exampleDoubleQ]

open Classical in
/-- **The `3`-smooth workhorse applies at `n = 4`**, on a named curve over `ℚ`, at two distinct
named affine points whose relation `[4]P = T` is proved rather than assumed.  Only the telescope,
the `4`-th root and the two nonzero constants remain hypothetical, exactly as at `n = 2, 3`.

⚠️ The `by convert` is load-bearing: `ℚ` has a genuine `DecidableEq` instance, so `exampleQuadruple`
is indexed by `instDecidableEqRat`, while the corollary — stated for a general `F` under
`open Classical in` — is indexed by `Classical.propDecidable`.  The two are propositionally but not
syntactically equal and `convert` closes the gap by `Subsingleton.elim`. -/
example
    {f g : exampleCurve.FunctionField} (hg : g ≠ 0) {c c₀ : ℚ} (hc : c ≠ 0) (hc₀ : c₀ ≠ 0)
    (htel : ∏ i ∈ Finset.range 4, (translateEndo exampleEqT)^[i] f
      = algebraMap ℚ exampleCurve.FunctionField c)
    (hpow : algebraMap ℚ exampleCurve.FunctionField c₀ * g ^ 4
      = mulByNEndo 4 (transcendental_xCoord_nsmul_of_smooth exampleTwo exampleThree
          (by norm_num) primeFactorsFour) f) :
    translateEndo exampleEqT g = g :=
  translateEndo_eq_self_of_mul_algebraMap_pow_eq_of_smooth exampleTwo exampleThree
    (n := 4) (by norm_num) primeFactorsFour exampleEqP exampleEqT (by convert exampleQuadruple)
    hg hc hc₀ htel hpow

end Nonvacuity

end WeierstrassCurve.Affine
