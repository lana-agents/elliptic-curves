/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import EllipticCurves.FunctionField.WeilPairingDivisorSlotBilinear
import EllipticCurves.FunctionField.WeilPairingNondegenerateTwo
import EllipticCurves.FunctionField.WeilPairingProductRelationRootIndependent
import EllipticCurves.FunctionField.WeilPairingRootIndependenceAlgClosed
import EllipticCurves.FunctionField.WeilPairingTranslationSlotHom

/-!
# The Weil pairing at `n = 2` as a function of two torsion points

`EllipticCurves.FunctionField.WeilPairingNondegenerateTwo`'s scope section recorded what this file
exists to remove.  ⚠️ **The sentence quoted here is its wording before `da4b169`; that file now says
the opposite and points back at this one**, so do not expect to find the quote there:

> ⚠️ **There is no `W.Point`-level pairing in this tree**, so "non-degeneracy" cannot be stated as a
> property of a bilinear map.

`WeilPairingTranslationSlotBilinear` (`#861`) and `WeilPairingTranslationSlotHom` (`#873`) say the
same and call it separate work.  Every rung-6 property on this board is currently a statement of
the shape

```
∃ g_S g_T g_R, (three rung-5 certificates) ∧ (the property, at those roots)
```

which cannot be composed: `e_2(S ⊕ T, P) = e_2(S, P) · e_2(T, P)` is not writable as an equation,
`e_2` is not a `MonoidHom` in either slot, and non-degeneracy has to quantify over the *data* rung 5
produces rather than over points.  This file replaces the existentials by a genuine function

```
weilPairingTwo : E[2] → E[2] → μ_2(F̄),
```

and then re-reads the merged headlines through it.  ⚠️ **No new mathematics is proved here.**  Every
input is merged; the content is a definition, one well-definedness lemma, and a case analysis.

## Why the choice of root does not matter, which is the whole design

`e_2(S, T) = τ_T∗(g_S) / g_S` depends a priori on `g_S`, hence on the `f_S` whose pullback `g_S` is
a square root of.  It depends on neither, and both halves are merged:

* **Same `f`, different root** — `weilPairingElt_eq_of_smul_pow_eq` (`WeilPairingRootIndependence`,
  `#719`).
* **Different `f` with the same divisor** — `weilPairingElt_eq_of_smul_pow_eq_of_divisor_eq`
  (`WeilPairingProductRelationRootIndependent`, `#910`), which is generic in the pullback `φ` and
  runs the argument *two functions with equal divisors differ by a unit of `F[W]`, a unit is a
  nonzero constant, `φ` fixes constants, a nonzero constant has trivial divisor*.

Only the second is needed here, since the first is a special case of it.  The point at infinity is
free: `weilPairingPointElt_zero` gives `1` for either root.  So
`weilPairingPointElt_eq_of_isWeilRootTwo` below is those inputs plus a two-line case split, and it
is the only lemma the file rests on.

## ⚠️ The divisor condition is stated at a `W.Point`, not at an affine point

`IsWeilRootTwo` pins `f_S` by `divisor W f = (2 : ℤ) • pointDivisorAff W S` — the shape
`eq_zero_of_forall_weilPairingElt_eq_one_two` (`WeilPairingNondegenerateTwo`, `#796`) already uses,
and the only one that covers `O` and the affine points at once (`pointDivisorAff_zero`,
`pointDivisorAff_some`).  Taking it as the definition is what makes non-degeneracy below a
three-line consequence rather than a case split, and it is why `S = O` needs no special treatment
anywhere: `f = g = 1` is a root there, unconditionally and without `[IsAlgClosed F]`.

The merged headlines state their divisor conditions as `Finsupp.single (pointClosedPoint h.left) 2`
instead, and one of them (`exists_weilPairingElt_self_eq_one_of_isAlgClosed_two`) states it
*projectively*.  `isWeilRootTwo_some` and `divisor_eq_of_divisorProj_eq` are the two bridges, and
they are the only places the affine/projective passage appears — free, per `#765`, but not zero.

## Main statements

* `WeierstrassCurve.Affine.IsWeilRootTwo` — the rung-5 datum at a point of `W`, uniform in the
  point, with `isWeilRootTwo_one` and `exists_isWeilRootTwo` its inhabitation.
* `WeierstrassCurve.Affine.weilPairingPointElt_eq_of_isWeilRootTwo` — **well-definedness**: two
  rung-5 roots at the same `S` pair identically with every point of `W`.
* `WeierstrassCurve.Affine.weilPairingEltTwo` / `weilPairingTwo` — the pairing as a function
  `E[2] → E[2] → F(W)`, respectively `E[2] → E[2] → μ_2(F)`.
* `WeierstrassCurve.Affine.weilPairingEltTwo_eq` — **the bridge**: the value at *any* rung-5 root
  the caller holds.  Every merged headline is applied through this and nothing else.  Its two
  specialisations to an affine translation point are `weilPairingEltTwo_eq_weilPairingElt` at the
  `F(W)` level and `weilPairingTwo_eq_weilPairingMu` at the `μ_2(F)` level; the latter is what a
  headline stated against `weilPairingMu` — the Galois ones are — has to be read through.
* `weilPairingTwo_add_right` / `weilPairingTwo_add_left` — bilinearity, in both slots.
* `weilPairingTwo_self` — the alternating property; `weilPairingTwo_swap` — antisymmetry.
* `WeierstrassCurve.Affine.eq_zero_of_forall_weilPairingTwo_eq_one` — non-degeneracy.
* **`WeierstrassCurve.Affine.weilPairingTwoHom`** — the bundled bilinear map
  `Multiplicative E[2] →* Multiplicative E[2] →* μ_2(F)`, with `ker_weilPairingTwoHom` restating
  non-degeneracy as `MonoidHom.ker _ = ⊥`.

## Scope

⚠️ **`[IsAlgClosed F]` is load-bearing and will not lift.**  It enters through
`exists_gS_two_of_isAlgClosed` (`#791`) alone — the file has no second, independent use — but that
use *produces a witness* rather than proving an equality, and `#899`'s test says base change never
reaches an obstruction of that shape.  A general-field version would have to take the whole family
of roots as a hypothesis, which is a different design; the `_of_hprin` twins on this front weaken a
hypothesis, and there is no hypothesis here to weaken.

⚠️ **`n = 2` only.**  The `n = 3` mirror is a separate issue and is **not** a transcription:
`WeilPairingAlternatingThree` records that the cube case takes `htors` at the `translatePoint` level
and needs `map_negY` where `n = 2` uses proof irrelevance.

⚠️ **The pairing is a function of `E[2] × E[2]`, not of `W.Point × W.Point`.**  It has to be: the
rung-5 root exists only at torsion points, and the translation slot's `μ_n`-membership is
`torsion_le_weilPairingPointSubgroup_two`, which is a statement about `W.torsion 2`.

⚠️ This is not Galois-equivariance (`#456`), not `#E[2] = 4` (merged, and not used here), and not
general `n` (which needs `#404`'s `ωₙ` crux).  ⚠️ `#456`'s two forms are re-read *through* the
function of this file by `EllipticCurves.FunctionField.WeilPairingFunctionGalois` (`#936`), which
is where `σ(e_2(S, T)) = e_2(σ • S, σ • T)` exists as an equation rather than an existential.

## References

* [J. H. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.8, Prop. 8.1.
-/

namespace WeierstrassCurve.Affine

open CoordinateRing

variable {F : Type*} [Field F] {W : Affine F} [W.IsElliptic]

/-! ### The rung-5 datum at a point, uniform in the point -/

section Root

open Classical in
/-- **`g` is a rung-5 root at the `2`-torsion point `S`**: there is a nonzero `f` with
`div f = 2 · (S)` — in the affine divisor group, so `O` contributes nothing — of which `g` is a
square root of the pullback, up to a unit of `F[W]`.

⚠️ The divisor is written against `pointDivisorAff`, not against
`Finsupp.single (pointClosedPoint h.left) 2`, so that `S = O` is covered by the same formula; see
the module docstring.  `isWeilRootTwo_some` is the bridge to the shape the merged headlines use. -/
def IsWeilRootTwo (h2 : (2 : F) ≠ 0) (S : W.Point) (g : W.FunctionField) : Prop :=
  g ≠ 0 ∧ ∃ f : W.FunctionField, f ≠ 0 ∧ divisor W f = (2 : ℤ) • pointDivisorAff W S ∧
    ∃ u : W.CoordinateRingˣ, (u : W.CoordinateRing) • g ^ 2 = mulByTwoEndo h2 f

open Classical in
/-- A rung-5 root is nonzero, by definition. -/
theorem IsWeilRootTwo.ne_zero {h2 : (2 : F) ≠ 0} {S : W.Point} {g : W.FunctionField}
    (hg : IsWeilRootTwo h2 S g) : g ≠ 0 := hg.1

open Classical in
/-- **`1` is a rung-5 root at `O`**, with `f = 1` and `u = 1`: the point at infinity has empty
affine divisor (`pointDivisorAff_zero`) and `[2]∗` is a ring homomorphism.

⚠️ Unconditional — no `[IsAlgClosed F]`.  This is why the `O` corner of every statement below is
free, and why `weilPairingEltTwo_zero_left` needs no case split. -/
theorem isWeilRootTwo_one (h2 : (2 : F) ≠ 0) :
    IsWeilRootTwo h2 (0 : W.Point) (1 : W.FunctionField) :=
  ⟨one_ne_zero, 1, one_ne_zero, by rw [divisor_one, pointDivisorAff_zero, smul_zero], 1, by
    rw [Units.val_one, one_smul, one_pow, map_one]⟩

open Classical in
/-- **The bridge from the shape the merged headlines use.**  At an affine point the uniform divisor
condition is `Finsupp.single (pointClosedPoint h.left) 2`, which is what every `exists_gS_two`-style
statement in this tree hands the caller. -/
theorem isWeilRootTwo_some (h2 : (2 : F) ≠ 0) {x y : F} (h : W.Nonsingular x y)
    {g f : W.FunctionField} (hg : g ≠ 0) (hf : f ≠ 0)
    (hd : divisor W f = Finsupp.single (pointClosedPoint h.left) (2 : ℤ))
    {u : W.CoordinateRingˣ} (hu : (u : W.CoordinateRing) • g ^ 2 = mulByTwoEndo h2 f) :
    IsWeilRootTwo h2 (Point.some x y h) g :=
  ⟨hg, f, hf, by rw [pointDivisorAff_some, Finsupp.smul_single, smul_eq_mul, mul_one]; exact hd,
    u, hu⟩

open Classical in
/-- **The projective divisor condition implies the affine one.**  `#765`'s passage, run once: the
point at infinity disappears under `affinePart` rather than being corrected for.  Consumed by the
alternating property, whose headline is the one stated projectively.

⚠️ **General in the multiplicity `m`, which costs nothing**: `affinePart_single_some` and
`affinePart_single_none` are already general in it and the proof never looks at it.  The `n = 3`
mirror (`WeilPairingFunctionThree`, `#925`) consumes it at `m = 3`; the name is deliberately not
`_two`, since nothing here is about the multiplication-by-two isogeny. -/
theorem divisor_eq_of_divisorProj_eq {x y : F} (h : W.Nonsingular x y) {f : W.FunctionField}
    {m : ℤ} (hf : divisorProj W f = Finsupp.single (some (pointClosedPoint h.left)) m
        - Finsupp.single (none : ProjPoint W) m) :
    divisor W f = Finsupp.single (pointClosedPoint h.left) m := by
  rw [← affinePart_divisorProj, hf, map_sub, affinePart_single_some, affinePart_single_none,
    sub_zero]

open Classical in
/-- **Every `2`-torsion point carries a rung-5 root**, over an algebraically closed field.  At `O`
this is `isWeilRootTwo_one`; at an affine point it is `exists_gS_two_of_isAlgClosed` (`#791`), which
is the only place `[IsAlgClosed F]` enters this file. -/
theorem exists_isWeilRootTwo [IsAlgClosed F] (h2 : (2 : F) ≠ 0) {S : W.Point}
    (hS : S ∈ W.torsion 2) : ∃ g : W.FunctionField, IsWeilRootTwo h2 S g := by
  rcases S with _ | ⟨x, y, h⟩
  · exact ⟨1, by rw [← Point.zero_def]; exact isWeilRootTwo_one h2⟩
  · obtain ⟨f, hf, hd, g, hg, u, hu⟩ := exists_gS_two_of_isAlgClosed h2 h hS
    exact ⟨g, isWeilRootTwo_some h2 h hg hf hd hu⟩

open Classical in
/-- **Well-definedness, and the only lemma this file rests on**: two rung-5 roots at the same `S`
give the same pairing value at *every* point of `W`, the point at infinity included.

At `O` both values are `1`.  At an affine point this is
`weilPairingElt_eq_of_smul_pow_eq_of_divisor_eq` (`#910`) instantiated at `φ = [2]∗`, whose `hfdiv`
is the two roots' divisor conditions read transitively — which is exactly why `IsWeilRootTwo` pins
`div f` rather than `f`. -/
theorem weilPairingPointElt_eq_of_isWeilRootTwo (h2 : (2 : F) ≠ 0) {S : W.Point}
    {g₁ g₂ : W.FunctionField} (hg₁ : IsWeilRootTwo h2 S g₁) (hg₂ : IsWeilRootTwo h2 S g₂)
    (P : W.Point) : weilPairingPointElt g₁ P = weilPairingPointElt g₂ P := by
  obtain ⟨hg₁0, f₁, hf₁, hd₁, u₁, hu₁⟩ := hg₁
  obtain ⟨hg₂0, f₂, hf₂, hd₂, u₂, hu₂⟩ := hg₂
  rcases P with _ | ⟨x, y, h⟩
  · rw [← Point.zero_def, weilPairingPointElt_zero hg₁0, weilPairingPointElt_zero hg₂0]
  · exact weilPairingElt_eq_of_smul_pow_eq_of_divisor_eq h.left (mulByTwoEndo h2)
      (mulByTwoEndo_algebraMap_base h2) two_ne_zero hf₁ hf₂ (hd₁.trans hd₂.symm) hg₁0 hg₂0 hu₁ hu₂

end Root

/-! ### The pairing as a function -/

section Pairing

variable [IsAlgClosed F]

open Classical in
/-- **A chosen rung-5 root at `S`.**  Which one is chosen never matters —
`weilPairingPointElt_eq_of_isWeilRootTwo` — and the only way to use this definition is through
`weilPairingEltTwo_eq`, which never unfolds the choice. -/
noncomputable def weilPairingRootTwo (h2 : (2 : F) ≠ 0) (S : W.torsion 2) : W.FunctionField :=
  (exists_isWeilRootTwo h2 S.2).choose

open Classical in
/-- The chosen root is a root. -/
theorem isWeilRootTwo_weilPairingRootTwo (h2 : (2 : F) ≠ 0) (S : W.torsion 2) :
    IsWeilRootTwo h2 (S : W.Point) (weilPairingRootTwo h2 S) :=
  (exists_isWeilRootTwo h2 S.2).choose_spec

open Classical in
theorem weilPairingRootTwo_ne_zero (h2 : (2 : F) ≠ 0) (S : W.torsion 2) :
    weilPairingRootTwo h2 S ≠ 0 :=
  (isWeilRootTwo_weilPairingRootTwo h2 S).ne_zero

open Classical in
/-- **The Weil pairing at `n = 2`, valued in `F(W)`**: `e_2(S, T) = τ_T∗(g_S) / g_S` at a chosen
rung-5 root `g_S`.  A function of two `2`-torsion points, with no existential and no data
argument. -/
noncomputable def weilPairingEltTwo (h2 : (2 : F) ≠ 0) (S T : W.torsion 2) : W.FunctionField :=
  weilPairingPointElt (weilPairingRootTwo h2 S) (T : W.Point)

open Classical in
/-- **The bridge, and the lemma every consumer wants.**  The value is computed by *any* rung-5 root
at `S` the caller happens to hold — in particular by the roots the merged existential headlines
produce, which is how each of them is read through this function below. -/
theorem weilPairingEltTwo_eq (h2 : (2 : F) ≠ 0) {S : W.torsion 2} {g : W.FunctionField}
    (hg : IsWeilRootTwo h2 (S : W.Point) g) (T : W.torsion 2) :
    weilPairingEltTwo h2 S T = weilPairingPointElt g (T : W.Point) :=
  weilPairingPointElt_eq_of_isWeilRootTwo h2 (isWeilRootTwo_weilPairingRootTwo h2 S) hg _

open Classical in
theorem weilPairingEltTwo_ne_zero (h2 : (2 : F) ≠ 0) (S T : W.torsion 2) :
    weilPairingEltTwo h2 S T ≠ 0 :=
  weilPairingPointElt_ne_zero (weilPairingRootTwo_ne_zero h2 S) _

open Classical in
/-- The value is a square root of unity, in the form `weilPairingPointMu` consumes.  Stated against
`weilPairingPointElt` rather than against `weilPairingEltTwo` so that `weilPairingTwo` can be
defined by it without an intervening transport. -/
theorem weilPairingPointElt_weilPairingRootTwo_pow (h2 : (2 : F) ≠ 0) (S T : W.torsion 2) :
    weilPairingPointElt (weilPairingRootTwo h2 S) (T : W.Point) ^ 2 = 1 := by
  obtain ⟨hg0, f, hf, hd, u, hu⟩ := isWeilRootTwo_weilPairingRootTwo h2 S
  exact torsion_le_weilPairingPointSubgroup_two h2 hg0 hu T.2

open Classical in
/-- **`e_2(S, T) ^ 2 = 1`**, for every pair of `2`-torsion points. -/
theorem weilPairingEltTwo_pow_eq_one (h2 : (2 : F) ≠ 0) (S T : W.torsion 2) :
    weilPairingEltTwo h2 S T ^ 2 = 1 :=
  weilPairingPointElt_weilPairingRootTwo_pow h2 S T

open Classical in
/-- **`e_2(S, O) = 1`**: translation by the point at infinity is the identity. -/
@[simp]
theorem weilPairingEltTwo_zero_right (h2 : (2 : F) ≠ 0) (S : W.torsion 2) :
    weilPairingEltTwo h2 S 0 = 1 := by
  rw [weilPairingEltTwo, ZeroMemClass.coe_zero,
    weilPairingPointElt_zero (weilPairingRootTwo_ne_zero h2 S)]

open Classical in
/-- **`e_2(O, T) = 1`**: `1` is a rung-5 root at `O` (`isWeilRootTwo_one`) and pairs trivially with
every point.  ⚠️ Proved through the bridge, not by unfolding the choice — the chosen root at `O`
need not be `1`, and nothing below ever needs to know what it is. -/
@[simp]
theorem weilPairingEltTwo_zero_left (h2 : (2 : F) ≠ 0) (T : W.torsion 2) :
    weilPairingEltTwo h2 0 T = 1 := by
  rw [weilPairingEltTwo_eq h2 (S := 0)
      (by rw [ZeroMemClass.coe_zero]; exact isWeilRootTwo_one h2) T,
    weilPairingPointElt_one]

open Classical in
/-- **The Weil pairing at `n = 2`, valued in `μ_2(F)`.**  The value group form, off
`weilPairingPointMu` (`#873`). -/
noncomputable def weilPairingTwo (h2 : (2 : F) ≠ 0) (S T : W.torsion 2) : rootsOfUnity 2 F :=
  weilPairingPointMu (weilPairingRootTwo_ne_zero h2 S)
    (weilPairingPointElt_weilPairingRootTwo_pow h2 S T)

open Classical in
/-- **Defining property**: pushing the `μ_2(F)` value into `F(W)` recovers the `F(W)` value. -/
@[simp]
theorem algebraMap_coe_weilPairingTwo (h2 : (2 : F) ≠ 0) (S T : W.torsion 2) :
    algebraMap F W.FunctionField ((weilPairingTwo h2 S T : Fˣ) : F) = weilPairingEltTwo h2 S T :=
  algebraMap_coe_weilPairingPointMu _ _

open Classical in
/-- Triviality in `μ_2(F)` is triviality in `F(W)`; the transport used by every `μ`-level statement
below whose `F(W)` form is an equality with `1`. -/
theorem weilPairingTwo_eq_one_iff (h2 : (2 : F) ≠ 0) (S T : W.torsion 2) :
    weilPairingTwo h2 S T = 1 ↔ weilPairingEltTwo h2 S T = 1 :=
  weilPairingPointMu_eq_one_iff _ _

end Pairing

/-! ### The properties, each one merged headline read through the bridge -/

section Properties

variable [IsAlgClosed F]

open Classical in
/-- Specialisation of the bridge to an affine translation point, which is the form the merged
headlines — all stated at `weilPairingElt` — apply in. -/
theorem weilPairingEltTwo_eq_weilPairingElt (h2 : (2 : F) ≠ 0) {S : W.torsion 2}
    {g : W.FunctionField} (hg : IsWeilRootTwo h2 (S : W.Point) g) {T : W.torsion 2} {x y : F}
    (h : W.Nonsingular x y) (hT : (T : W.Point) = Point.some x y h) :
    weilPairingEltTwo h2 S T = weilPairingElt h.left g := by
  rw [weilPairingEltTwo_eq h2 hg, hT, weilPairingPointElt_some]

open Classical in
/-- **The `μ_2(F)` bridge**, the value-group twin of `weilPairingEltTwo_eq_weilPairingElt`.

⚠️ Needed because the merged Galois headlines state their `μ_n(F)` conclusion against
`weilPairingMu`, so a consumer reading them through this function has to compare two elements of
`rootsOfUnity 2 F` rather than two elements of `F(W)`.

The proof is the only thing worth remembering here: two elements of `rootsOfUnity n F` are equal
as soon as their images in `F` agree (`Subtype.ext` then `Units.ext`), and `algebraMap F F(W)` is
injective, so the two `algebraMap_coe_…` defining properties turn the goal into the `F(W)`-level
bridge above.  The `Classical.choose` inside `weilPairingTwo` is never unfolded. -/
theorem weilPairingTwo_eq_weilPairingMu (h2 : (2 : F) ≠ 0) {S : W.torsion 2}
    {g : W.FunctionField} (hg : IsWeilRootTwo h2 (S : W.Point) g) {T : W.torsion 2} {x y : F}
    (h : W.Nonsingular x y) (hT : (T : W.Point) = Point.some x y h)
    (hpow : weilPairingElt h.left g ^ 2 = 1) :
    weilPairingTwo h2 S T = weilPairingMu h.left hpow := by
  refine Subtype.ext (Units.ext ((algebraMap F W.FunctionField).injective ?_))
  rw [algebraMap_coe_weilPairingTwo, algebraMap_coe_weilPairingMu,
    weilPairingEltTwo_eq_weilPairingElt h2 hg h hT]

open Classical in
theorem weilPairingEltTwo_eq_one_of_right_eq_zero (h2 : (2 : F) ≠ 0) (S : W.torsion 2)
    {T : W.torsion 2} (hT : (T : W.Point) = 0) : weilPairingEltTwo h2 S T = 1 := by
  rw [weilPairingEltTwo, hT, weilPairingPointElt_zero (weilPairingRootTwo_ne_zero h2 S)]

open Classical in
theorem weilPairingEltTwo_eq_one_of_left_eq_zero (h2 : (2 : F) ≠ 0) {S : W.torsion 2}
    (hS : (S : W.Point) = 0) (T : W.torsion 2) : weilPairingEltTwo h2 S T = 1 := by
  rw [weilPairingEltTwo_eq h2 (g := 1) (by rw [hS]; exact isWeilRootTwo_one h2) T,
    weilPairingPointElt_one]

/-! #### The translation slot -/

open Classical in
/-- **`e_2(S, T₁ ⊕ T₂) = e_2(S, T₁) · e_2(S, T₂)`**, as an equation between values of a function.
`weilPairingPointElt_add` (`#873`) with its root-of-unity datum supplied by the chosen root. -/
theorem weilPairingEltTwo_add_right (h2 : (2 : F) ≠ 0) (S T₁ T₂ : W.torsion 2) :
    weilPairingEltTwo h2 S (T₁ + T₂)
      = weilPairingEltTwo h2 S T₁ * weilPairingEltTwo h2 S T₂ := by
  rw [weilPairingEltTwo, weilPairingEltTwo, weilPairingEltTwo, AddSubgroup.coe_add]
  exact weilPairingPointElt_add (weilPairingRootTwo_ne_zero h2 S) _ two_ne_zero
    (weilPairingPointElt_weilPairingRootTwo_pow h2 S T₂)

/-! #### The alternating property -/

open Classical in
/-- **`e_2(S, S) = 1`.**  At `O` this is `weilPairingEltTwo_zero_left`; at an affine `S` it is
`exists_weilPairingElt_self_eq_one_of_isAlgClosed_two` (`#836`) read through the bridge, its `f`
converted from the projective divisor condition by `divisor_eq_of_divisorProj_eq`. -/
@[simp]
theorem weilPairingEltTwo_self (h2 : (2 : F) ≠ 0) (S : W.torsion 2) :
    weilPairingEltTwo h2 S S = 1 := by
  cases hS : (S : W.Point) with
  | zero =>
      exact weilPairingEltTwo_eq_one_of_left_eq_zero h2 (hS.trans Point.zero_def.symm) S
  | some x y h =>
      have htors : Point.some x y h ∈ W.torsion 2 := hS ▸ S.2
      obtain ⟨f, hf, hdproj, g, hg, ⟨u, hu⟩, -, hone⟩ :=
        exists_weilPairingElt_self_eq_one_of_isAlgClosed_two h2 h htors
      have hroot : IsWeilRootTwo h2 (S : W.Point) g := by
        rw [hS]
        exact isWeilRootTwo_some h2 h hg hf (divisor_eq_of_divisorProj_eq h hdproj) hu
      rw [weilPairingEltTwo_eq_weilPairingElt h2 hroot h hS]
      exact hone

/-! #### The divisor slot -/

open Classical in
/-- **`e_2(S₁ ⊕ S₂, T) = e_2(S₁, T) · e_2(S₂, T)`.**

`exists_weilPairingElt_divisorSlot_add_two` (`#912`) read through the bridge — but only in the case
where all four points are affine.  ⚠️ **The other three cases are not instances of it and are done
here:** `T = O` (all three values are `1`), `S₁ = O` or `S₂ = O` (the corner lemmas), and
`S₁ ⊕ S₂ = O` with both affine, where a `2`-torsion point being its own negative forces `S₂ = S₁`
and the claim is `1 = e_2(S₁, T) ^ 2`, i.e. `weilPairingEltTwo_pow_eq_one`. -/
theorem weilPairingEltTwo_add_left (h2 : (2 : F) ≠ 0) (S₁ S₂ T : W.torsion 2) :
    weilPairingEltTwo h2 (S₁ + S₂) T
      = weilPairingEltTwo h2 S₁ T * weilPairingEltTwo h2 S₂ T := by
  cases hT : (T : W.Point) with
  | zero =>
      have h0 : (T : W.Point) = 0 := hT.trans Point.zero_def.symm
      rw [weilPairingEltTwo_eq_one_of_right_eq_zero h2 _ h0,
        weilPairingEltTwo_eq_one_of_right_eq_zero h2 _ h0,
        weilPairingEltTwo_eq_one_of_right_eq_zero h2 _ h0, one_mul]
  | some xT yT hTns =>
  have hmT : Point.some xT yT hTns ∈ W.torsion 2 := hT ▸ T.2
  cases hS₁ : (S₁ : W.Point) with
  | zero =>
      have h0 : S₁ = 0 := Subtype.ext hS₁
      rw [h0, zero_add, weilPairingEltTwo_zero_left, one_mul]
  | some x₁ y₁ h₁ =>
  cases hS₂ : (S₂ : W.Point) with
  | zero =>
      have h0 : S₂ = 0 := Subtype.ext hS₂
      rw [h0, add_zero, weilPairingEltTwo_zero_left, mul_one]
  | some x₂ y₂ h₂ =>
  have hmS₁ : Point.some x₁ y₁ h₁ ∈ W.torsion 2 := hS₁ ▸ S₁.2
  have hmS₂ : Point.some x₂ y₂ h₂ ∈ W.torsion 2 := hS₂ ▸ S₂.2
  cases hR : ((S₁ + S₂ : W.torsion 2) : W.Point) with
  | zero =>
      have hswap : S₂ = S₁ := by
        have hsum : S₁ + S₂ = 0 := Subtype.ext hR
        have h2S₂ : S₂ + S₂ = 0 := Subtype.ext (by
          rw [AddSubgroup.coe_add]
          exact add_self_eq_zero_of_mem_torsion_two S₂.2)
        exact (neg_eq_of_add_eq_zero_left h2S₂).symm.trans (neg_eq_of_add_eq_zero_left hsum)
      rw [weilPairingEltTwo_eq_one_of_left_eq_zero h2 hR T, hswap,
        ← pow_two, weilPairingEltTwo_pow_eq_one]
  | some xR yR hRns =>
      have hadd : Point.some x₁ y₁ h₁ + Point.some x₂ y₂ h₂ = Point.some xR yR hRns := by
        rw [← hS₁, ← hS₂, ← AddSubgroup.coe_add, hR]
      obtain ⟨gS, gT, gR, hgS, hgT, hgR, ⟨fS, hfS, hdS, uS, huS⟩, ⟨fT, hfT, hdT, uT, huT⟩,
        ⟨fR, hfR, hdR, uR, huR⟩, hbil⟩ :=
        exists_weilPairingElt_divisorSlot_add_two h2 hTns h₁ h₂ hRns hmT hmS₁ hmS₂ hadd
      rw [weilPairingEltTwo_eq_weilPairingElt h2
          (S := S₁ + S₂) (by rw [hR]; exact isWeilRootTwo_some h2 hRns hgR hfR hdR huR) hTns hT,
        weilPairingEltTwo_eq_weilPairingElt h2
          (S := S₁) (by rw [hS₁]; exact isWeilRootTwo_some h2 h₁ hgS hfS hdS huS) hTns hT,
        weilPairingEltTwo_eq_weilPairingElt h2
          (S := S₂) (by rw [hS₂]; exact isWeilRootTwo_some h2 h₂ hgT hfT hdT huT) hTns hT]
      exact hbil

/-! #### Antisymmetry -/

open Classical in
/-- **`e_2(S, T) · e_2(T, S) = 1`.**  ⚠️ Free from the alternating property and bilinearity, by
expanding `e_2(S ⊕ T, S ⊕ T) = 1` — Silverman's own derivation, and it needs none of the
`WeilPairingProductRelation*` machinery, which the existential packaging did need. -/
theorem weilPairingEltTwo_mul_swap (h2 : (2 : F) ≠ 0) (S T : W.torsion 2) :
    weilPairingEltTwo h2 S T * weilPairingEltTwo h2 T S = 1 := by
  have h := weilPairingEltTwo_self h2 (S + T)
  rwa [weilPairingEltTwo_add_left, weilPairingEltTwo_add_right, weilPairingEltTwo_add_right,
    weilPairingEltTwo_self, weilPairingEltTwo_self, one_mul, mul_one] at h

open Classical in
/-- **`e_2(T, S) = e_2(S, T)⁻¹`**, the quotable form. -/
theorem weilPairingEltTwo_swap (h2 : (2 : F) ≠ 0) (S T : W.torsion 2) :
    weilPairingEltTwo h2 T S = (weilPairingEltTwo h2 S T)⁻¹ :=
  eq_inv_of_mul_eq_one_left ((mul_comm _ _).trans (weilPairingEltTwo_mul_swap h2 S T))

/-! #### Non-degeneracy -/

open Classical in
/-- **Silverman III.8.1(d), as a statement about points**: if `e_2(S, ·)` is trivial on all of
`E[2]` then `S = O`.  `eq_zero_of_forall_weilPairingElt_eq_one_two` (`#796`) applied to the chosen
root — and it applies *directly*, with no divisor bookkeeping, because `IsWeilRootTwo` states its
divisor condition in exactly the shape that theorem takes. -/
theorem eq_zero_of_forall_weilPairingEltTwo_eq_one (h2 : (2 : F) ≠ 0) {S : W.torsion 2}
    (hone : ∀ T : W.torsion 2, weilPairingEltTwo h2 S T = 1) : S = 0 := by
  obtain ⟨hg0, f, hf, hd, u, hu⟩ := isWeilRootTwo_weilPairingRootTwo h2 S
  refine Subtype.ext (eq_zero_of_forall_weilPairingElt_eq_one_two h2 hf hd hg0 hu ?_)
  intro x y h hmem
  have hT := hone ⟨Point.some x y h, hmem⟩
  rwa [weilPairingEltTwo, weilPairingPointElt_some] at hT

/-! #### The same statements in `μ_2(F)` -/

open Classical in
@[simp]
theorem weilPairingTwo_zero_right (h2 : (2 : F) ≠ 0) (S : W.torsion 2) :
    weilPairingTwo h2 S 0 = 1 :=
  (weilPairingTwo_eq_one_iff h2 S 0).mpr (weilPairingEltTwo_zero_right h2 S)

open Classical in
@[simp]
theorem weilPairingTwo_zero_left (h2 : (2 : F) ≠ 0) (T : W.torsion 2) :
    weilPairingTwo h2 0 T = 1 :=
  (weilPairingTwo_eq_one_iff h2 0 T).mpr (weilPairingEltTwo_zero_left h2 T)

open Classical in
/-- **Bilinearity in the translation slot, in `μ_2(F)`.** -/
theorem weilPairingTwo_add_right (h2 : (2 : F) ≠ 0) (S T₁ T₂ : W.torsion 2) :
    weilPairingTwo h2 S (T₁ + T₂) = weilPairingTwo h2 S T₁ * weilPairingTwo h2 S T₂ := by
  refine algebraMap_coe_rootsOfUnity_injective (W := W) ?_
  simp only [Subgroup.coe_mul, Units.val_mul, map_mul, algebraMap_coe_weilPairingTwo]
  exact weilPairingEltTwo_add_right h2 S T₁ T₂

open Classical in
/-- **Bilinearity in the divisor slot, in `μ_2(F)`.** -/
theorem weilPairingTwo_add_left (h2 : (2 : F) ≠ 0) (S₁ S₂ T : W.torsion 2) :
    weilPairingTwo h2 (S₁ + S₂) T = weilPairingTwo h2 S₁ T * weilPairingTwo h2 S₂ T := by
  refine algebraMap_coe_rootsOfUnity_injective (W := W) ?_
  simp only [Subgroup.coe_mul, Units.val_mul, map_mul, algebraMap_coe_weilPairingTwo]
  exact weilPairingEltTwo_add_left h2 S₁ S₂ T

open Classical in
/-- **The alternating property in `μ_2(F)`.** -/
@[simp]
theorem weilPairingTwo_self (h2 : (2 : F) ≠ 0) (S : W.torsion 2) : weilPairingTwo h2 S S = 1 :=
  (weilPairingTwo_eq_one_iff h2 S S).mpr (weilPairingEltTwo_self h2 S)

open Classical in
/-- **Antisymmetry in `μ_2(F)`.** -/
theorem weilPairingTwo_mul_swap (h2 : (2 : F) ≠ 0) (S T : W.torsion 2) :
    weilPairingTwo h2 S T * weilPairingTwo h2 T S = 1 := by
  refine algebraMap_coe_rootsOfUnity_injective (W := W) ?_
  simp only [Subgroup.coe_mul, Units.val_mul, map_mul, algebraMap_coe_weilPairingTwo,
    Subgroup.coe_one, Units.val_one, map_one]
  exact weilPairingEltTwo_mul_swap h2 S T

open Classical in
theorem weilPairingTwo_swap (h2 : (2 : F) ≠ 0) (S T : W.torsion 2) :
    weilPairingTwo h2 T S = (weilPairingTwo h2 S T)⁻¹ :=
  eq_inv_of_mul_eq_one_left ((mul_comm _ _).trans (weilPairingTwo_mul_swap h2 S T))

open Classical in
/-- **Non-degeneracy in `μ_2(F)`.** -/
theorem eq_zero_of_forall_weilPairingTwo_eq_one (h2 : (2 : F) ≠ 0) {S : W.torsion 2}
    (hone : ∀ T : W.torsion 2, weilPairingTwo h2 S T = 1) : S = 0 :=
  eq_zero_of_forall_weilPairingEltTwo_eq_one h2 fun T =>
    (weilPairingTwo_eq_one_iff h2 S T).mp (hone T)

/-! ### The bundled bilinear map

⚠️ This is the object the tree did not have, and the reason for the file.  Each field below is one
of the equations above; the bundling adds nothing mathematically and everything to what a consumer
can say. -/

open Classical in
/-- **The Weil pairing at `n = 2` as a bilinear map**

```
weilPairingTwoHom h2 : Multiplicative E[2] →* Multiplicative E[2] →* μ_2(F),
                       S ↦ T ↦ e_2(S, T).
```

Silverman *AEC* III.8.1(a) with both slots bundled at once.  The inner `map_one'`/`map_mul'` are
`weilPairingTwo_zero_right`/`_add_right`; the outer two are `weilPairingTwo_zero_left`/`_add_left`
under `MonoidHom.ext`. -/
noncomputable def weilPairingTwoHom (h2 : (2 : F) ≠ 0) :
    Multiplicative (W.torsion 2) →* Multiplicative (W.torsion 2) →* rootsOfUnity 2 F where
  toFun S :=
    { toFun := fun T => weilPairingTwo h2 S.toAdd T.toAdd
      map_one' := weilPairingTwo_zero_right h2 S.toAdd
      map_mul' := fun T₁ T₂ => weilPairingTwo_add_right h2 S.toAdd T₁.toAdd T₂.toAdd }
  map_one' := MonoidHom.ext fun T => weilPairingTwo_zero_left h2 T.toAdd
  map_mul' S₁ S₂ := MonoidHom.ext fun T =>
    weilPairingTwo_add_left h2 S₁.toAdd S₂.toAdd T.toAdd

open Classical in
/-- The bundled map's values are the pairing values. -/
@[simp]
theorem weilPairingTwoHom_apply_apply (h2 : (2 : F) ≠ 0)
    (S T : Multiplicative (W.torsion 2)) :
    weilPairingTwoHom h2 S T = weilPairingTwo h2 S.toAdd T.toAdd :=
  rfl

open Classical in
/-- **Non-degeneracy as a property of the bilinear map**: `MonoidHom.ker (e_2) = ⊥`.

⚠️ This is the sentence `WeilPairingNondegenerateTwo`'s scope section says the tree cannot state.
It is one `MonoidHom.ext` away from `eq_zero_of_forall_weilPairingTwo_eq_one`, and the distance
between the two is exactly the packaging this file supplies. -/
theorem ker_weilPairingTwoHom (h2 : (2 : F) ≠ 0) :
    MonoidHom.ker (weilPairingTwoHom (W := W) h2) = ⊥ := by
  refine le_antisymm (fun S hS => ?_) bot_le
  rw [Subgroup.mem_bot]
  rw [MonoidHom.mem_ker] at hS
  have hval : ∀ T : W.torsion 2, weilPairingTwo h2 S.toAdd T = 1 := fun T => by
    have hT := congrArg (fun φ => φ (Multiplicative.ofAdd T)) hS
    simpa using hT
  exact eq_zero_of_forall_weilPairingTwo_eq_one h2 hval

end Properties

/-! ### Non-vacuity

Everything above carries `[IsAlgClosed F]` and `[W.IsElliptic]`, so `ℚ` cannot witness it; the curve
is `y² = x³ − x` over `AlgebraicClosure ℚ`, which is what `#758`/`#759`/`#774`/`#791`/`#796` use,
and the `2`-torsion point is **named**: `S = (0, 0)`.

⚠️ The load-bearing certificate is the **non-degeneracy** one, and it is the last `example` below:
it asserts that some `T ∈ E[2]` pairs non-trivially with a *named* point, which no hypothesis-free
term reaches.  The bilinearity and alternating certificates are equations that hold for all
arguments, so they certify that the construction elaborates on a curve that exists — real, but
weaker, and said here rather than left to be inferred (`#916`). -/

section Nonvacuity

/-- An algebraically closed field of characteristic zero. -/
private abbrev exampleField : Type := AlgebraicClosure ℚ

/-- The curve `y² = x³ − x` over `AlgebraicClosure ℚ`, of discriminant `64`. -/
private noncomputable def exampleCurve : Affine exampleField := ⟨0, 0, 0, -1, 0⟩

private instance : exampleCurve.IsElliptic := by
  rw [WeierstrassCurve.isElliptic_iff, isUnit_iff_ne_zero]
  norm_num [exampleCurve, WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈]

private lemma exampleTwo : (2 : exampleField) ≠ 0 := by norm_num

/-- `S = (0, 0)` lies on `y² = x³ − x` and is nonsingular. -/
private lemma exampleNonsingular : exampleCurve.Nonsingular 0 0 :=
  exampleCurve.equation_iff_nonsingular.mp (by
    norm_num [exampleCurve, WeierstrassCurve.Affine.equation_iff])

open Classical in
/-- `S = (0, 0)` is `2`-torsion: `2y + a₁x + a₃ = 0` reads `0 = 0`. -/
private lemma exampleTorsion :
    Point.some (0 : exampleField) 0 exampleNonsingular ∈ exampleCurve.torsion 2 :=
  (mem_torsion_two_some_iff exampleNonsingular).mpr (by norm_num [exampleCurve])

open Classical in
/-- The named `2`-torsion point, as an element of `E[2]`. -/
private noncomputable def exampleS : exampleCurve.torsion 2 :=
  ⟨Point.some 0 0 exampleNonsingular, exampleTorsion⟩

open Classical in
/-- The pairing is bilinear on a curve that exists. -/
example (S₁ S₂ T₁ T₂ : exampleCurve.torsion 2) :
    weilPairingTwo exampleTwo (S₁ + S₂) (T₁ + T₂)
      = weilPairingTwo exampleTwo S₁ T₁ * weilPairingTwo exampleTwo S₂ T₁
        * (weilPairingTwo exampleTwo S₁ T₂ * weilPairingTwo exampleTwo S₂ T₂) := by
  rw [weilPairingTwo_add_right, weilPairingTwo_add_left, weilPairingTwo_add_left]

open Classical in
/-- It is alternating, and antisymmetric, on that curve. -/
example (S T : exampleCurve.torsion 2) :
    weilPairingTwo exampleTwo S S = 1 ∧
      weilPairingTwo exampleTwo T S = (weilPairingTwo exampleTwo S T)⁻¹ :=
  ⟨weilPairingTwo_self exampleTwo S, weilPairingTwo_swap exampleTwo S T⟩

open Classical in
/-- The bundled map exists there, and its kernel is trivial. -/
example : MonoidHom.ker (weilPairingTwoHom (W := exampleCurve) exampleTwo) = ⊥ :=
  ker_weilPairingTwoHom exampleTwo

open Classical in
/-- **The certificate that cannot hold vacuously**: at the named point `S = (0, 0)` of
`y² = x³ − x`, some `T ∈ E[2]` pairs non-trivially.  ⚠️ Stated as an existence over `E[2]` with the
*divisor* point fixed and named, which is what makes it a statement about this curve and not a
schema. -/
example : ∃ T : exampleCurve.torsion 2, weilPairingTwo exampleTwo exampleS T ≠ 1 := by
  by_contra hcon
  have hall : ∀ T : exampleCurve.torsion 2, weilPairingTwo exampleTwo exampleS T = 1 := fun T =>
    not_not.mp fun hne => hcon ⟨T, hne⟩
  have h0 : exampleS = 0 := eq_zero_of_forall_weilPairingTwo_eq_one exampleTwo hall
  exact Point.some_ne_zero exampleNonsingular (congrArg Subtype.val h0)

end Nonvacuity

end WeierstrassCurve.Affine
