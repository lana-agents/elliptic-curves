/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import EllipticCurves.Fixtures
import EllipticCurves.FunctionField.WeilPairingFunctionTwo
import EllipticCurves.FunctionField.WeilPairingNondegenerateThree
import EllipticCurves.FunctionField.WeilPairingAlternatingThreeAlgClosed

/-!
# The Weil pairing at `n = 3` as a function of two torsion points

`EllipticCurves.FunctionField.WeilPairingFunctionTwo` (`#922`) replaced the existential packaging
of rung 6 at `n = 2` by a genuine function

```
weilPairingTwo : E[2] → E[2] → μ_2(F),
```

bundled as `weilPairingTwoHom` with `MonoidHom.ker _ = ⊥`.  This file is the `n = 3` mirror.  As
there, ⚠️ **no new mathematics is proved**: every input is merged, and the content is a definition,
one well-definedness lemma, and a case analysis.

## What transfers unchanged, and the one thing that does not

Every ingredient exists at `n = 3` in the shape the `n = 2` construction consumes, with `h3`
threaded and `mulByThreeEndo` for `mulByTwoEndo`.  Two of them are worth naming because they are
what make the mirror cheap rather than merely possible:

* `weilPairingElt_eq_of_smul_pow_eq_of_divisor_eq` (`WeilPairingProductRelationRootIndependent`,
  `#854`) is generic in the pullback `φ` **and in the exponent `m`** — the exponent was already a
  variable, so well-definedness needs nothing added.
* `eq_zero_of_forall_weilPairingElt_eq_one_three` (`WeilPairingNondegenerateThree`, `#831`) states
  its divisor hypothesis as `divisor W f = (3 : ℤ) • pointDivisorAff W S`, the same uniform
  `pointDivisorAff` shape the `n = 2` headline uses.  Taking it as `IsWeilRootThree`'s definition is
  why `S = O` needs no special treatment anywhere and why non-degeneracy is three lines.

⚠️ **The exception is the degenerate case of divisor-slot bilinearity, and it is a genuinely
different argument.**  See `weilPairingEltThree_add_left` below.

## ⚠️ What became *cheaper* than the existential packaging, and stays cheaper here

`WeilPairingProductRelation`'s product relation `g_{S ⊕ T} = g_S · g_T · w` is **not** on the path
to antisymmetry once the pairing is a function: `weilPairingEltThree_mul_swap` is four tactic lines
out of `e_3(S ⊕ T, S ⊕ T) = 1`, and this file does not import that module.  That machinery is
still the right thing for the arbitrary-field (`_of_hprin`) statements, where there is no function
to expand.

## Main statements

* `WeierstrassCurve.Affine.IsWeilRootThree` — the rung-5 datum at a point of `W`, uniform in the
  point, with `isWeilRootThree_one` and `exists_isWeilRootThree` its inhabitation.
* `WeierstrassCurve.Affine.weilPairingPointElt_eq_of_isWeilRootThree` — **well-definedness**.
* `WeierstrassCurve.Affine.weilPairingEltThree` / `weilPairingThree` — the pairing as a function
  `E[3] → E[3] → F(W)`, respectively `E[3] → E[3] → μ_3(F)`.
* `WeierstrassCurve.Affine.weilPairingEltThree_eq` — **the bridge**: the value at *any* rung-5 root
  the caller holds.  Every merged headline is applied through this and nothing else.  Its two
  specialisations to an affine translation point are `weilPairingEltThree_eq_weilPairingElt` at the
  `F(W)` level and `weilPairingThree_eq_weilPairingMu` at the `μ_3(F)` level; the latter is what a
  headline stated against `weilPairingMu` — the Galois ones are — has to be read through.
* `weilPairingThree_add_right` / `weilPairingThree_add_left` — bilinearity, in both slots.
* `weilPairingThree_self` — the alternating property; `weilPairingThree_swap` — antisymmetry.
* `WeierstrassCurve.Affine.eq_zero_of_forall_weilPairingThree_eq_one` — non-degeneracy.
* **`WeierstrassCurve.Affine.weilPairingThreeHom`** — the bundled bilinear map
  `Multiplicative E[3] →* Multiplicative E[3] →* μ_3(F)`, with `ker_weilPairingThreeHom` restating
  non-degeneracy as `MonoidHom.ker _ = ⊥`.

## ⚠️ One merged statement is generalised, and it is the only non-additive line in this file

`divisor_eq_of_divisorProj_eq` (`WeilPairingFunctionTwo`) was stated at the exponent `2`.  Its proof
— `affinePart_divisorProj`, `map_sub`, `affinePart_single_some`, `affinePart_single_none` — never
looks at the exponent, and `affinePart_single_{some,none}` are already general in it, so the
statement is generalised **in place** to `{m : ℤ}` rather than copied to a `_three` sibling.  The
existing call site infers `m` and is unchanged; no proof anywhere is touched.

## Scope

⚠️ **`[IsAlgClosed F]` is load-bearing and will not lift**, for exactly the reason recorded in
`WeilPairingFunctionTwo`: it enters through `exists_gS_three_of_isAlgClosed` (`#825`) alone, but
that use *produces a witness*, and `#899`'s test says base change never reaches an obstruction of
that shape.  ⚠️ **A one-gate file is liftable only if the gate is also equality-shaped**; the
single-gate test and `#899`'s test are different tests, and this pair of files is where they
disagree.  There is no hypothesis here to weaken, so there is no `_of_hprin` twin to write.

⚠️ **`h2` is needed at `n = 3` and not for a symmetric reason.**  `h3` enters through
`mulByThreeEndo`, which the statements mention; `h2` enters through the doubling slope that produces
the fibre point `P` with `[3]P = T` (`WeilPairingRootIndependenceAlgClosed` records this).

⚠️ This is not Galois-equivariance (`#456`; the `F(W)`-level and `μ_n`-level forms are merged in
`WeilPairingGaloisRoot` and `WeilPairingGaloisRootHprin`), not general `n` (which needs `#251`; ⚠️
**not** `#404`, see below), and not `#E[3] = 9`.  ⚠️ Those Galois forms are re-read *through* the
function of this file by `EllipticCurves.FunctionField.WeilPairingFunctionGalois` (`#936`), which is
where `σ(e_3(S, T)) = e_3(σ • S, σ • T)` exists as an equation rather than an existential.

⚠️ **`#404` is closed, and the general-`n` entry above named it as the gate.**  PR #557 proved the
on-curve identity for `(Φₙ/ΨSqₙ, ωₙ/ψₙ³)` at every index over every commutative ring —
`WeierstrassCurve.Affine.equation_div_of_ψ_ne_zero`, `EllipticCurves.Torsion.OmegaCrux`.  What still
gates a general index is the *other* statement this tree also called `ωₙ`: the identification of
those coordinates with the **group-law** multiple `n • P`, which is `#251`.  ⚠️ The two-reading
account is `EllipticCurves.FunctionField.MulByNPullback`; the gate is relettered here, not lifted.

## ⚠️ Five issue numbers in this file were wrong while the names beside them were right

Corrected in place rather than retired — a wrong number was wrong when it was typed, so no clause
here *became* false.  Ground truth is the creating commit of the module that declares the name
(`git log --diff-filter=A --format=%s -- <file>`, subject `… (#issue) (#PR)`).

* `weilPairingElt_eq_of_smul_pow_eq_of_divisor_eq` was `#910`, twice — declared in
  `WeilPairingProductRelationRootIndependent` (**`#854`**).  `#910` is that module's `hprin` twin.
* `weilPairingPointMu` and `weilPairingPointElt_add` were `#873` — both declared in
  `WeilPairingTranslationSlotHom` (**`#890`**), the same shift `WeilPairingFunctionTwo` carried.
* `exists_weilPairingElt_self_eq_one_of_isAlgClosed_three` was `#836` — declared in
  `WeilPairingAlternatingThreeAlgClosed` (**`#829`**), which is the module this file imports for
  it.

⚠️ Each wrong number names real adjacent work, so none of them looked wrong; an issue number is a
citation and the only check is against its source.

## References

* [J. H. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.8, Prop. 8.1.
-/

namespace WeierstrassCurve.Affine

open CoordinateRing

variable {F : Type*} [Field F] {W : Affine F} [W.IsElliptic]

/-! ### The rung-5 datum at a point, uniform in the point -/

section Root

open Classical in
/-- **`g` is a rung-5 root at the `3`-torsion point `S`**: there is a nonzero `f` with
`div f = 3 · (S)` — in the affine divisor group, so `O` contributes nothing — of which `g` is a
cube root of the pullback, up to a unit of `F[W]`.

⚠️ The divisor is written against `pointDivisorAff`, not against
`Finsupp.single (pointClosedPoint h.left) (3 : ℤ)`, so that `S = O` is covered by the same formula;
`isWeilRootThree_some` is the bridge to the shape the merged headlines use. -/
def IsWeilRootThree (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) (S : W.Point) (g : W.FunctionField) :
    Prop :=
  g ≠ 0 ∧ ∃ f : W.FunctionField, f ≠ 0 ∧ divisor W f = (3 : ℤ) • pointDivisorAff W S ∧
    ∃ u : W.CoordinateRingˣ, (u : W.CoordinateRing) • g ^ 3 = mulByThreeEndo h2 h3 f

open Classical in
/-- A rung-5 root is nonzero, by definition. -/
theorem IsWeilRootThree.ne_zero {h2 : (2 : F) ≠ 0} {h3 : (3 : F) ≠ 0} {S : W.Point}
    {g : W.FunctionField} (hg : IsWeilRootThree h2 h3 S g) : g ≠ 0 := hg.1

open Classical in
/-- **`1` is a rung-5 root at `O`**, with `f = 1` and `u = 1`: the point at infinity has empty
affine divisor (`pointDivisorAff_zero`) and `[3]∗` is a ring homomorphism.

⚠️ Unconditional — no `[IsAlgClosed F]`.  This is why the `O` corner of every statement below is
free, and why `weilPairingEltThree_zero_left` needs no case split. -/
theorem isWeilRootThree_one (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) :
    IsWeilRootThree h2 h3 (0 : W.Point) (1 : W.FunctionField) :=
  ⟨one_ne_zero, 1, one_ne_zero, by rw [divisor_one, pointDivisorAff_zero, smul_zero], 1, by
    rw [Units.val_one, one_smul, one_pow, map_one]⟩

open Classical in
/-- **The bridge from the shape the merged headlines use.**  At an affine point the uniform divisor
condition is `Finsupp.single (pointClosedPoint h.left) (3 : ℤ)`, which is what every
`exists_gS_three`-style statement in this tree hands the caller. -/
theorem isWeilRootThree_some (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) {x y : F}
    (h : W.Nonsingular x y) {g f : W.FunctionField} (hg : g ≠ 0) (hf : f ≠ 0)
    (hd : divisor W f = Finsupp.single (pointClosedPoint h.left) (3 : ℤ))
    {u : W.CoordinateRingˣ} (hu : (u : W.CoordinateRing) • g ^ 3 = mulByThreeEndo h2 h3 f) :
    IsWeilRootThree h2 h3 (Point.some x y h) g :=
  ⟨hg, f, hf, by rw [pointDivisorAff_some, Finsupp.smul_single, smul_eq_mul, mul_one]; exact hd,
    u, hu⟩

open Classical in
/-- **Every `3`-torsion point carries a rung-5 root**, over an algebraically closed field.  At `O`
this is `isWeilRootThree_one`; at an affine point it is `exists_gS_three_of_isAlgClosed` (`#825`),
which is the only place `[IsAlgClosed F]` enters this file. -/
theorem exists_isWeilRootThree [IsAlgClosed F] (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) {S : W.Point}
    (hS : S ∈ W.torsion 3) : ∃ g : W.FunctionField, IsWeilRootThree h2 h3 S g := by
  rcases S with _ | ⟨x, y, h⟩
  · exact ⟨1, by rw [← Point.zero_def]; exact isWeilRootThree_one h2 h3⟩
  · obtain ⟨f, hf, hd, g, hg, u, hu⟩ := exists_gS_three_of_isAlgClosed h2 h3 h hS
    exact ⟨g, isWeilRootThree_some h2 h3 h hg hf hd hu⟩

open Classical in
/-- **Well-definedness, and the only lemma this file rests on**: two rung-5 roots at the same `S`
give the same pairing value at *every* point of `W`, the point at infinity included.

At `O` both values are `1`.  At an affine point this is
`weilPairingElt_eq_of_smul_pow_eq_of_divisor_eq` (`#854`) instantiated at `φ = [3]∗` and `m = 3` —
both were already variables there — with its `hfdiv` the two roots' divisor conditions read
transitively, which is exactly why `IsWeilRootThree` pins `div f` rather than `f`. -/
theorem weilPairingPointElt_eq_of_isWeilRootThree (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0)
    {S : W.Point} {g₁ g₂ : W.FunctionField} (hg₁ : IsWeilRootThree h2 h3 S g₁)
    (hg₂ : IsWeilRootThree h2 h3 S g₂) (P : W.Point) :
    weilPairingPointElt g₁ P = weilPairingPointElt g₂ P := by
  obtain ⟨hg₁0, f₁, hf₁, hd₁, u₁, hu₁⟩ := hg₁
  obtain ⟨hg₂0, f₂, hf₂, hd₂, u₂, hu₂⟩ := hg₂
  rcases P with _ | ⟨x, y, h⟩
  · rw [← Point.zero_def, weilPairingPointElt_zero hg₁0, weilPairingPointElt_zero hg₂0]
  · exact weilPairingElt_eq_of_smul_pow_eq_of_divisor_eq h.left (mulByThreeEndo h2 h3)
      (mulByThreeEndo_algebraMap_base h2 h3) three_ne_zero hf₁ hf₂ (hd₁.trans hd₂.symm) hg₁0 hg₂0
      hu₁ hu₂

end Root

/-! ### The pairing as a function -/

section Pairing

variable [IsAlgClosed F]

open Classical in
/-- **A chosen rung-5 root at `S`.**  Which one is chosen never matters —
`weilPairingPointElt_eq_of_isWeilRootThree` — and the only way to use this definition is through
`weilPairingEltThree_eq`, which never unfolds the choice. -/
noncomputable def weilPairingRootThree (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) (S : W.torsion 3) :
    W.FunctionField :=
  (exists_isWeilRootThree h2 h3 S.2).choose

open Classical in
/-- The chosen root is a root. -/
theorem isWeilRootThree_weilPairingRootThree (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0)
    (S : W.torsion 3) :
    IsWeilRootThree h2 h3 (S : W.Point) (weilPairingRootThree h2 h3 S) :=
  (exists_isWeilRootThree h2 h3 S.2).choose_spec

open Classical in
theorem weilPairingRootThree_ne_zero (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) (S : W.torsion 3) :
    weilPairingRootThree h2 h3 S ≠ 0 :=
  (isWeilRootThree_weilPairingRootThree h2 h3 S).ne_zero

open Classical in
/-- **The Weil pairing at `n = 3`, valued in `F(W)`**: `e_3(S, T) = τ_T∗(g_S)/g_S` at a chosen
rung-5 root `g_S`.  A function of two `3`-torsion points, with no existential and no data
argument. -/
noncomputable def weilPairingEltThree (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) (S T : W.torsion 3) :
    W.FunctionField :=
  weilPairingPointElt (weilPairingRootThree h2 h3 S) (T : W.Point)

open Classical in
/-- **The bridge, and the lemma every consumer wants.**  The value is computed by *any* rung-5 root
at `S` the caller happens to hold — in particular by the roots the merged existential headlines
produce, which is how each of them is read through this function below. -/
theorem weilPairingEltThree_eq (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) {S : W.torsion 3}
    {g : W.FunctionField} (hg : IsWeilRootThree h2 h3 (S : W.Point) g) (T : W.torsion 3) :
    weilPairingEltThree h2 h3 S T = weilPairingPointElt g (T : W.Point) :=
  weilPairingPointElt_eq_of_isWeilRootThree h2 h3
    (isWeilRootThree_weilPairingRootThree h2 h3 S) hg _

open Classical in
theorem weilPairingEltThree_ne_zero (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) (S T : W.torsion 3) :
    weilPairingEltThree h2 h3 S T ≠ 0 :=
  weilPairingPointElt_ne_zero (weilPairingRootThree_ne_zero h2 h3 S) _

open Classical in
/-- The value is a cube root of unity, in the form `weilPairingPointMu` consumes.  Stated against
`weilPairingPointElt` rather than against `weilPairingEltThree` so that `weilPairingThree` can be
defined by it without an intervening transport. -/
theorem weilPairingPointElt_weilPairingRootThree_pow (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0)
    (S T : W.torsion 3) :
    weilPairingPointElt (weilPairingRootThree h2 h3 S) (T : W.Point) ^ 3 = 1 := by
  obtain ⟨hg0, f, hf, hd, u, hu⟩ := isWeilRootThree_weilPairingRootThree h2 h3 S
  exact torsion_le_weilPairingPointSubgroup_three h2 h3 hg0 hu T.2

open Classical in
/-- **`e_3(S, T) ^ 3 = 1`**, for every pair of `3`-torsion points. -/
theorem weilPairingEltThree_pow_eq_one (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) (S T : W.torsion 3) :
    weilPairingEltThree h2 h3 S T ^ 3 = 1 :=
  weilPairingPointElt_weilPairingRootThree_pow h2 h3 S T

open Classical in
/-- **`e_3(S, O) = 1`**: translation by the point at infinity is the identity. -/
@[simp]
theorem weilPairingEltThree_zero_right (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) (S : W.torsion 3) :
    weilPairingEltThree h2 h3 S 0 = 1 := by
  rw [weilPairingEltThree, ZeroMemClass.coe_zero,
    weilPairingPointElt_zero (weilPairingRootThree_ne_zero h2 h3 S)]

open Classical in
/-- **`e_3(O, T) = 1`**: `1` is a rung-5 root at `O` (`isWeilRootThree_one`) and pairs trivially
with every point.  ⚠️ Proved through the bridge, not by unfolding the choice — the chosen root at
`O` need not be `1`, and nothing below ever needs to know what it is. -/
@[simp]
theorem weilPairingEltThree_zero_left (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) (T : W.torsion 3) :
    weilPairingEltThree h2 h3 0 T = 1 := by
  rw [weilPairingEltThree_eq h2 h3 (S := 0)
      (by rw [ZeroMemClass.coe_zero]; exact isWeilRootThree_one h2 h3) T,
    weilPairingPointElt_one]

open Classical in
/-- **The Weil pairing at `n = 3`, valued in `μ_3(F)`.**  The value group form, off
`weilPairingPointMu` (`#890`). -/
noncomputable def weilPairingThree (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) (S T : W.torsion 3) :
    rootsOfUnity 3 F :=
  weilPairingPointMu (weilPairingRootThree_ne_zero h2 h3 S)
    (weilPairingPointElt_weilPairingRootThree_pow h2 h3 S T)

open Classical in
/-- **Defining property**: pushing the `μ_3(F)` value into `F(W)` recovers the `F(W)` value. -/
@[simp]
theorem algebraMap_coe_weilPairingThree (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0)
    (S T : W.torsion 3) :
    algebraMap F W.FunctionField ((weilPairingThree h2 h3 S T : Fˣ) : F)
      = weilPairingEltThree h2 h3 S T :=
  algebraMap_coe_weilPairingPointMu _ _

open Classical in
/-- Triviality in `μ_3(F)` is triviality in `F(W)`; the transport used by every `μ`-level statement
below whose `F(W)` form is an equality with `1`. -/
theorem weilPairingThree_eq_one_iff (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) (S T : W.torsion 3) :
    weilPairingThree h2 h3 S T = 1 ↔ weilPairingEltThree h2 h3 S T = 1 :=
  weilPairingPointMu_eq_one_iff _ _

end Pairing

/-! ### The properties, each one merged headline read through the bridge -/

section Properties

variable [IsAlgClosed F]

open Classical in
/-- Specialisation of the bridge to an affine translation point, which is the form the merged
headlines — all stated at `weilPairingElt` — apply in. -/
theorem weilPairingEltThree_eq_weilPairingElt (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0)
    {S : W.torsion 3} {g : W.FunctionField} (hg : IsWeilRootThree h2 h3 (S : W.Point) g)
    {T : W.torsion 3} {x y : F} (h : W.Nonsingular x y) (hT : (T : W.Point) = Point.some x y h) :
    weilPairingEltThree h2 h3 S T = weilPairingElt h.left g := by
  rw [weilPairingEltThree_eq h2 h3 hg, hT, weilPairingPointElt_some]

open Classical in
/-- **The `μ_3(F)` bridge**, the value-group twin of `weilPairingEltThree_eq_weilPairingElt` and the
`n = 3` mirror of `weilPairingTwo_eq_weilPairingMu`.

⚠️ Needed because the merged Galois headlines state their `μ_n(F)` conclusion against
`weilPairingMu`, so a consumer reading them through this function has to compare two elements of
`rootsOfUnity 3 F` rather than two elements of `F(W)`.  See the `n = 2` twin for why the proof is
`Subtype.ext`/`Units.ext` and injectivity of `algebraMap` and nothing else. -/
theorem weilPairingThree_eq_weilPairingMu (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0)
    {S : W.torsion 3} {g : W.FunctionField} (hg : IsWeilRootThree h2 h3 (S : W.Point) g)
    {T : W.torsion 3} {x y : F} (h : W.Nonsingular x y) (hT : (T : W.Point) = Point.some x y h)
    (hpow : weilPairingElt h.left g ^ 3 = 1) :
    weilPairingThree h2 h3 S T = weilPairingMu h.left hpow := by
  refine Subtype.ext (Units.ext ((algebraMap F W.FunctionField).injective ?_))
  rw [algebraMap_coe_weilPairingThree, algebraMap_coe_weilPairingMu,
    weilPairingEltThree_eq_weilPairingElt h2 h3 hg h hT]

open Classical in
theorem weilPairingEltThree_eq_one_of_right_eq_zero (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0)
    (S : W.torsion 3) {T : W.torsion 3} (hT : (T : W.Point) = 0) :
    weilPairingEltThree h2 h3 S T = 1 := by
  rw [weilPairingEltThree, hT, weilPairingPointElt_zero (weilPairingRootThree_ne_zero h2 h3 S)]

open Classical in
theorem weilPairingEltThree_eq_one_of_left_eq_zero (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0)
    {S : W.torsion 3} (hS : (S : W.Point) = 0) (T : W.torsion 3) :
    weilPairingEltThree h2 h3 S T = 1 := by
  rw [weilPairingEltThree_eq h2 h3 (g := 1) (by rw [hS]; exact isWeilRootThree_one h2 h3) T,
    weilPairingPointElt_one]

/-! #### The translation slot -/

open Classical in
/-- **`e_3(S, T₁ ⊕ T₂) = e_3(S, T₁) · e_3(S, T₂)`**, as an equation between values of a function.
`weilPairingPointElt_add` (`#890`) with its root-of-unity datum supplied by the chosen root. -/
theorem weilPairingEltThree_add_right (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0)
    (S T₁ T₂ : W.torsion 3) :
    weilPairingEltThree h2 h3 S (T₁ + T₂)
      = weilPairingEltThree h2 h3 S T₁ * weilPairingEltThree h2 h3 S T₂ := by
  rw [weilPairingEltThree, weilPairingEltThree, weilPairingEltThree, AddSubgroup.coe_add]
  exact weilPairingPointElt_add (weilPairingRootThree_ne_zero h2 h3 S) _ three_ne_zero
    (weilPairingPointElt_weilPairingRootThree_pow h2 h3 S T₂)

/-! #### The alternating property -/

open Classical in
/-- **`e_3(S, S) = 1`.**  At `O` this is `weilPairingEltThree_zero_left`; at an affine `S` it is
`exists_weilPairingElt_self_eq_one_of_isAlgClosed_three` (`#829`) read through the bridge, its `f`
converted from the projective divisor condition by `divisor_eq_of_divisorProj_eq`. -/
@[simp]
theorem weilPairingEltThree_self (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) (S : W.torsion 3) :
    weilPairingEltThree h2 h3 S S = 1 := by
  cases hS : (S : W.Point) with
  | zero =>
      exact weilPairingEltThree_eq_one_of_left_eq_zero h2 h3 (hS.trans Point.zero_def.symm) S
  | some x y h =>
      have htors : Point.some x y h ∈ W.torsion 3 := hS ▸ S.2
      obtain ⟨f, hf, hdproj, g, hg, ⟨u, hu⟩, -, hone⟩ :=
        exists_weilPairingElt_self_eq_one_of_isAlgClosed_three h2 h3 h htors
      have hroot : IsWeilRootThree h2 h3 (S : W.Point) g := by
        rw [hS]
        exact isWeilRootThree_some h2 h3 h hg hf (divisor_eq_of_divisorProj_eq h hdproj) hu
      rw [weilPairingEltThree_eq_weilPairingElt h2 h3 hroot h hS]
      exact hone

/-! #### The divisor slot -/

open Classical in
/-- **`e_3(S₁ ⊕ S₂, T) = e_3(S₁, T) · e_3(S₂, T)`.**

`exists_weilPairingElt_divisorSlot_add_three` (`#861`) read through the bridge — but only in the
case where all four points are affine.  ⚠️ **The other three cases are not instances of it and are
done here:** `T = O` (all three values are `1`), `S₁ = O` or `S₂ = O` (the corner lemmas), and
`S₁ ⊕ S₂ = O` with both affine.

⚠️ **That last case is where the `n = 2` proof does not transfer, and it is the only place in this
file where anything has to be thought about.**  At `n = 2` it is settled by *a `2`-torsion point is
its own negative*, which gives `S₂ = S₁` and collapses the goal to `e_2(S₁, T) ^ 2 = 1`.  At `n = 3`
that step is false — `S₁ ⊕ S₂ = O` gives `S₂ = −S₁` — and `e_3(S₁, T) · e_3(−S₁, T) = 1` is the
divisor-slot inverse law, which is what is being proved.  Copying the `n = 2` argument is circular.

What works instead uses the merged headline a second time rather than adding anything: `3 • S₁ = 0`
gives `S₁ ⊕ S₁ = −S₁ = S₂`, and `S₂` is affine in this branch, so the headline applies to the triple
`(S₁, S₁, S₂)` with `hadd : S₁ ⊕ S₁ = S₂` and yields `e_3(S₂, T) = e_3(S₁, T) ^ 2`.  The goal
`1 = e_3(S₁, T) · e_3(S₂, T)` is then `1 = e_3(S₁, T) ^ 3`, which is
`weilPairingEltThree_pow_eq_one`. -/
theorem weilPairingEltThree_add_left (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0)
    (S₁ S₂ T : W.torsion 3) :
    weilPairingEltThree h2 h3 (S₁ + S₂) T
      = weilPairingEltThree h2 h3 S₁ T * weilPairingEltThree h2 h3 S₂ T := by
  cases hT : (T : W.Point) with
  | zero =>
      have h0 : (T : W.Point) = 0 := hT.trans Point.zero_def.symm
      rw [weilPairingEltThree_eq_one_of_right_eq_zero h2 h3 _ h0,
        weilPairingEltThree_eq_one_of_right_eq_zero h2 h3 _ h0,
        weilPairingEltThree_eq_one_of_right_eq_zero h2 h3 _ h0, one_mul]
  | some xT yT hTns =>
  have hmT : Point.some xT yT hTns ∈ W.torsion 3 := hT ▸ T.2
  cases hS₁ : (S₁ : W.Point) with
  | zero =>
      have h0 : S₁ = 0 := Subtype.ext hS₁
      rw [h0, zero_add, weilPairingEltThree_zero_left, one_mul]
  | some x₁ y₁ h₁ =>
  cases hS₂ : (S₂ : W.Point) with
  | zero =>
      have h0 : S₂ = 0 := Subtype.ext hS₂
      rw [h0, add_zero, weilPairingEltThree_zero_left, mul_one]
  | some x₂ y₂ h₂ =>
  have hmS₁ : Point.some x₁ y₁ h₁ ∈ W.torsion 3 := hS₁ ▸ S₁.2
  have hmS₂ : Point.some x₂ y₂ h₂ ∈ W.torsion 3 := hS₂ ▸ S₂.2
  cases hR : ((S₁ + S₂ : W.torsion 3) : W.Point) with
  | zero =>
      have hsum : S₁ + S₂ = 0 := Subtype.ext hR
      have h3S₁ : S₁ + S₁ + S₁ = 0 := Subtype.ext (by
        rw [AddSubgroup.coe_add, AddSubgroup.coe_add]
        exact add_add_self_eq_zero_of_mem_torsion_three S₁.2)
      have hdouble : S₁ + S₁ = S₂ :=
        (neg_eq_of_add_eq_zero_left h3S₁).symm.trans (neg_eq_of_add_eq_zero_right hsum)
      have haff : Point.some x₁ y₁ h₁ + Point.some x₁ y₁ h₁ = Point.some x₂ y₂ h₂ := by
        rw [← hS₁, ← AddSubgroup.coe_add, hdouble, hS₂]
      obtain ⟨gS, gT, gR, hgS, hgT, hgR, ⟨fS, hfS, hdS, uS, huS⟩, ⟨fT, hfT, hdT, uT, huT⟩,
        ⟨fR, hfR, hdR, uR, huR⟩, hbil⟩ :=
        exists_weilPairingElt_divisorSlot_add_three h2 h3 hTns h₁ h₁ h₂ hmT hmS₁ hmS₁ haff
      have hval₁ : weilPairingEltThree h2 h3 S₁ T = weilPairingElt hTns.left gS :=
        weilPairingEltThree_eq_weilPairingElt h2 h3
          (by rw [hS₁]; exact isWeilRootThree_some h2 h3 h₁ hgS hfS hdS huS) hTns hT
      have hval₂ : weilPairingEltThree h2 h3 S₂ T = weilPairingElt hTns.left gR :=
        weilPairingEltThree_eq_weilPairingElt h2 h3
          (by rw [hS₂]; exact isWeilRootThree_some h2 h3 h₂ hgR hfR hdR huR) hTns hT
      have hval₃ : weilPairingEltThree h2 h3 S₁ T = weilPairingElt hTns.left gT :=
        weilPairingEltThree_eq_weilPairingElt h2 h3
          (by rw [hS₁]; exact isWeilRootThree_some h2 h3 h₁ hgT hfT hdT huT) hTns hT
      have hsq : weilPairingEltThree h2 h3 S₂ T = weilPairingEltThree h2 h3 S₁ T ^ 2 := by
        rw [hval₂, hbil, ← hval₁, ← hval₃, sq]
      rw [weilPairingEltThree_eq_one_of_left_eq_zero h2 h3 hR T, hsq, ← pow_succ',
        weilPairingEltThree_pow_eq_one]
  | some xR yR hRns =>
      have hadd : Point.some x₁ y₁ h₁ + Point.some x₂ y₂ h₂ = Point.some xR yR hRns := by
        rw [← hS₁, ← hS₂, ← AddSubgroup.coe_add, hR]
      obtain ⟨gS, gT, gR, hgS, hgT, hgR, ⟨fS, hfS, hdS, uS, huS⟩, ⟨fT, hfT, hdT, uT, huT⟩,
        ⟨fR, hfR, hdR, uR, huR⟩, hbil⟩ :=
        exists_weilPairingElt_divisorSlot_add_three h2 h3 hTns h₁ h₂ hRns hmT hmS₁ hmS₂ hadd
      rw [weilPairingEltThree_eq_weilPairingElt h2 h3
          (S := S₁ + S₂) (by rw [hR]; exact isWeilRootThree_some h2 h3 hRns hgR hfR hdR huR)
          hTns hT,
        weilPairingEltThree_eq_weilPairingElt h2 h3
          (S := S₁) (by rw [hS₁]; exact isWeilRootThree_some h2 h3 h₁ hgS hfS hdS huS) hTns hT,
        weilPairingEltThree_eq_weilPairingElt h2 h3
          (S := S₂) (by rw [hS₂]; exact isWeilRootThree_some h2 h3 h₂ hgT hfT hdT huT) hTns hT]
      exact hbil

/-! #### Antisymmetry -/

open Classical in
/-- **`e_3(S, T) · e_3(T, S) = 1`.**  ⚠️ Free from the alternating property and bilinearity, by
expanding `e_3(S ⊕ T, S ⊕ T) = 1` — Silverman's own derivation, and it needs none of the
`WeilPairingProductRelation*` machinery, which the existential packaging did need. -/
theorem weilPairingEltThree_mul_swap (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) (S T : W.torsion 3) :
    weilPairingEltThree h2 h3 S T * weilPairingEltThree h2 h3 T S = 1 := by
  have h := weilPairingEltThree_self h2 h3 (S + T)
  rwa [weilPairingEltThree_add_left, weilPairingEltThree_add_right,
    weilPairingEltThree_add_right, weilPairingEltThree_self, weilPairingEltThree_self, one_mul,
    mul_one] at h

open Classical in
/-- **`e_3(T, S) = e_3(S, T)⁻¹`**, the quotable form. -/
theorem weilPairingEltThree_swap (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) (S T : W.torsion 3) :
    weilPairingEltThree h2 h3 T S = (weilPairingEltThree h2 h3 S T)⁻¹ :=
  eq_inv_of_mul_eq_one_left ((mul_comm _ _).trans (weilPairingEltThree_mul_swap h2 h3 S T))

/-! #### Non-degeneracy -/

open Classical in
/-- **Silverman III.8.1(c) at `n = 3`, as a statement about points**: if `e_3(S, ·)` is trivial on
all of `E[3]` then `S = O`.  `eq_zero_of_forall_weilPairingElt_eq_one_three` (`#831`) applied to the
chosen root — and it applies *directly*, with no divisor bookkeeping, because `IsWeilRootThree`
states its divisor condition in exactly the shape that theorem takes. -/
theorem eq_zero_of_forall_weilPairingEltThree_eq_one (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0)
    {S : W.torsion 3} (hone : ∀ T : W.torsion 3, weilPairingEltThree h2 h3 S T = 1) : S = 0 := by
  obtain ⟨hg0, f, hf, hd, u, hu⟩ := isWeilRootThree_weilPairingRootThree h2 h3 S
  refine Subtype.ext (eq_zero_of_forall_weilPairingElt_eq_one_three h2 h3 hf hd hg0 hu ?_)
  intro x y h hmem
  have hT := hone ⟨Point.some x y h, hmem⟩
  rwa [weilPairingEltThree, weilPairingPointElt_some] at hT

/-! #### The same statements in `μ_3(F)` -/

open Classical in
@[simp]
theorem weilPairingThree_zero_right (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) (S : W.torsion 3) :
    weilPairingThree h2 h3 S 0 = 1 :=
  (weilPairingThree_eq_one_iff h2 h3 S 0).mpr (weilPairingEltThree_zero_right h2 h3 S)

open Classical in
@[simp]
theorem weilPairingThree_zero_left (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) (T : W.torsion 3) :
    weilPairingThree h2 h3 0 T = 1 :=
  (weilPairingThree_eq_one_iff h2 h3 0 T).mpr (weilPairingEltThree_zero_left h2 h3 T)

open Classical in
/-- **Bilinearity in the translation slot, in `μ_3(F)`.** -/
theorem weilPairingThree_add_right (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) (S T₁ T₂ : W.torsion 3) :
    weilPairingThree h2 h3 S (T₁ + T₂)
      = weilPairingThree h2 h3 S T₁ * weilPairingThree h2 h3 S T₂ := by
  refine algebraMap_coe_rootsOfUnity_injective (W := W) ?_
  simp only [Subgroup.coe_mul, Units.val_mul, map_mul, algebraMap_coe_weilPairingThree]
  exact weilPairingEltThree_add_right h2 h3 S T₁ T₂

open Classical in
/-- **Bilinearity in the divisor slot, in `μ_3(F)`.** -/
theorem weilPairingThree_add_left (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) (S₁ S₂ T : W.torsion 3) :
    weilPairingThree h2 h3 (S₁ + S₂) T
      = weilPairingThree h2 h3 S₁ T * weilPairingThree h2 h3 S₂ T := by
  refine algebraMap_coe_rootsOfUnity_injective (W := W) ?_
  simp only [Subgroup.coe_mul, Units.val_mul, map_mul, algebraMap_coe_weilPairingThree]
  exact weilPairingEltThree_add_left h2 h3 S₁ S₂ T

open Classical in
/-- **The alternating property in `μ_3(F)`.** -/
@[simp]
theorem weilPairingThree_self (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) (S : W.torsion 3) :
    weilPairingThree h2 h3 S S = 1 :=
  (weilPairingThree_eq_one_iff h2 h3 S S).mpr (weilPairingEltThree_self h2 h3 S)

open Classical in
/-- **Antisymmetry in `μ_3(F)`.** -/
theorem weilPairingThree_mul_swap (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) (S T : W.torsion 3) :
    weilPairingThree h2 h3 S T * weilPairingThree h2 h3 T S = 1 := by
  refine algebraMap_coe_rootsOfUnity_injective (W := W) ?_
  simp only [Subgroup.coe_mul, Units.val_mul, map_mul, algebraMap_coe_weilPairingThree,
    Subgroup.coe_one, Units.val_one, map_one]
  exact weilPairingEltThree_mul_swap h2 h3 S T

open Classical in
theorem weilPairingThree_swap (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) (S T : W.torsion 3) :
    weilPairingThree h2 h3 T S = (weilPairingThree h2 h3 S T)⁻¹ :=
  eq_inv_of_mul_eq_one_left ((mul_comm _ _).trans (weilPairingThree_mul_swap h2 h3 S T))

open Classical in
/-- **Non-degeneracy in `μ_3(F)`.** -/
theorem eq_zero_of_forall_weilPairingThree_eq_one (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0)
    {S : W.torsion 3} (hone : ∀ T : W.torsion 3, weilPairingThree h2 h3 S T = 1) : S = 0 :=
  eq_zero_of_forall_weilPairingEltThree_eq_one h2 h3 fun T =>
    (weilPairingThree_eq_one_iff h2 h3 S T).mp (hone T)

/-! ### The bundled bilinear map

⚠️ The `n = 3` mirror of `weilPairingTwoHom`.  Each field below is one of the equations above; the
bundling adds nothing mathematically and everything to what a consumer can say. -/

open Classical in
/-- **The Weil pairing at `n = 3` as a bilinear map**

```
weilPairingThreeHom h2 h3 : Multiplicative E[3] →* Multiplicative E[3] →* μ_3(F),
                            S ↦ T ↦ e_3(S, T).
```

Silverman *AEC* III.8.1(a) at `n = 3` with both slots bundled at once.  The inner
`map_one'`/`map_mul'` are `weilPairingThree_zero_right`/`_add_right`; the outer two are
`weilPairingThree_zero_left`/`_add_left` under `MonoidHom.ext`. -/
noncomputable def weilPairingThreeHom (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) :
    Multiplicative (W.torsion 3) →* Multiplicative (W.torsion 3) →* rootsOfUnity 3 F where
  toFun S :=
    { toFun := fun T => weilPairingThree h2 h3 S.toAdd T.toAdd
      map_one' := weilPairingThree_zero_right h2 h3 S.toAdd
      map_mul' := fun T₁ T₂ => weilPairingThree_add_right h2 h3 S.toAdd T₁.toAdd T₂.toAdd }
  map_one' := MonoidHom.ext fun T => weilPairingThree_zero_left h2 h3 T.toAdd
  map_mul' S₁ S₂ := MonoidHom.ext fun T =>
    weilPairingThree_add_left h2 h3 S₁.toAdd S₂.toAdd T.toAdd

open Classical in
/-- The bundled map's values are the pairing values. -/
@[simp]
theorem weilPairingThreeHom_apply_apply (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0)
    (S T : Multiplicative (W.torsion 3)) :
    weilPairingThreeHom h2 h3 S T = weilPairingThree h2 h3 S.toAdd T.toAdd :=
  rfl

open Classical in
/-- **Non-degeneracy as a property of the bilinear map**: `MonoidHom.ker (e_3) = ⊥`. -/
theorem ker_weilPairingThreeHom (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) :
    MonoidHom.ker (weilPairingThreeHom (W := W) h2 h3) = ⊥ := by
  refine le_antisymm (fun S hS => ?_) bot_le
  rw [Subgroup.mem_bot]
  rw [MonoidHom.mem_ker] at hS
  have hval : ∀ T : W.torsion 3, weilPairingThree h2 h3 S.toAdd T = 1 := fun T => by
    have hT := congrArg (fun φ => φ (Multiplicative.ofAdd T)) hS
    simpa using hT
  exact eq_zero_of_forall_weilPairingThree_eq_one h2 h3 hval

end Properties

/-! ### Non-vacuity

Everything above carries `[IsAlgClosed F]` and `[W.IsElliptic]`, so `ℚ` cannot witness it.  ⚠️ **The
`n = 2` certificate curve `y² = x³ − x` would not serve either**: its `Ψ₃ = 3X⁴ − 6X² − 1` has no
rational root, so none of its nine `3`-torsion points can be *named*.  The curve is `y² + y = x³`
over `AlgebraicClosure ℚ` — this tree's `n = 3` certificate curve, used by `#825`/`#829`/`#831`/
`#836` — and the `3`-torsion point is **named**: `S = (0, 0)`, because
`Ψ₃ = 3X⁴ + 3b₆X = 3X(X³ + 1)` vanishes there.

⚠️ The load-bearing certificate is the **non-degeneracy** one, and it is the last `example` below:
it asserts that some `T ∈ E[3]` pairs non-trivially with a *named* point, which no hypothesis-free
term reaches — substituting `S := 0` makes it false (`weilPairingThree_zero_left`), so its truth
turns on the divisor point being the named non-trivial one.  The bilinearity and alternating
certificates are equations that hold for all arguments, so they certify that the construction
elaborates on a curve that exists — real, but weaker, and said here rather than left to be
inferred (`#916`). -/

section Nonvacuity

/-! The certificate curve `y² + y = x³` is the shared `EllipticCurves.Fixture.y2AddYEqX3`, and the
base — algebraically closed, and of characteristic `0` so that `2 ≠ 0` and `3 ≠ 0` — is
`EllipticCurves.Fixture.AlgClosedQ`, whose single `[CharZero F]` instance also supplies
`IsElliptic` here. -/

open EllipticCurves.Fixture

private lemma exampleTwo : (2 : AlgClosedQ) ≠ 0 := two_ne_zero

private lemma exampleThree : (3 : AlgClosedQ) ≠ 0 := three_ne_zero_of_charZero _

/-- `S = (0, 0)` lies on `y² + y = x³` and is nonsingular. -/
private lemma exampleNonsingular : (y2AddYEqX3 AlgClosedQ).Nonsingular 0 0 :=
  (y2AddYEqX3 AlgClosedQ).equation_iff_nonsingular.mp (by
    norm_num [y2AddYEqX3, WeierstrassCurve.Affine.equation_iff])

open Classical in
/-- `S = (0, 0)` is `3`-torsion: `Ψ₃ = 3X⁴ + 3b₆X` vanishes at `0`. -/
private lemma exampleTorsion :
    Point.some (0 : AlgClosedQ) 0 exampleNonsingular ∈ (y2AddYEqX3 AlgClosedQ).torsion 3 :=
  mem_torsion_three_some_iff'.mpr (by
    norm_num [y2AddYEqX3, WeierstrassCurve.Ψ₃, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
      WeierstrassCurve.b₆, WeierstrassCurve.b₈])

open Classical in
/-- The named `3`-torsion point, as an element of `E[3]`. -/
private noncomputable def exampleS : (y2AddYEqX3 AlgClosedQ).torsion 3 :=
  ⟨Point.some 0 0 exampleNonsingular, exampleTorsion⟩

open Classical in
/-- The pairing is bilinear on a curve that exists. -/
example (S₁ S₂ T₁ T₂ : (y2AddYEqX3 AlgClosedQ).torsion 3) :
    weilPairingThree exampleTwo exampleThree (S₁ + S₂) (T₁ + T₂)
      = weilPairingThree exampleTwo exampleThree S₁ T₁
          * weilPairingThree exampleTwo exampleThree S₂ T₁
        * (weilPairingThree exampleTwo exampleThree S₁ T₂
          * weilPairingThree exampleTwo exampleThree S₂ T₂) := by
  rw [weilPairingThree_add_right, weilPairingThree_add_left, weilPairingThree_add_left]

open Classical in
/-- It is alternating, and antisymmetric, on that curve. -/
example (S T : (y2AddYEqX3 AlgClosedQ).torsion 3) :
    weilPairingThree exampleTwo exampleThree S S = 1 ∧
      weilPairingThree exampleTwo exampleThree T S
        = (weilPairingThree exampleTwo exampleThree S T)⁻¹ :=
  ⟨weilPairingThree_self exampleTwo exampleThree S,
    weilPairingThree_swap exampleTwo exampleThree S T⟩

open Classical in
/-- The bundled map exists there, and its kernel is trivial. -/
example :
    MonoidHom.ker (weilPairingThreeHom (W := y2AddYEqX3 AlgClosedQ) exampleTwo exampleThree) = ⊥ :=
  ker_weilPairingThreeHom exampleTwo exampleThree

open Classical in
/-- **The certificate that cannot hold vacuously**: at the named point `S = (0, 0)` of
`y² + y = x³`, some `T ∈ E[3]` pairs non-trivially.  ⚠️ Stated as an existence over `E[3]` with the
*divisor* point fixed and named, which is what makes it a statement about this curve and not a
schema. -/
example : ∃ T : (y2AddYEqX3 AlgClosedQ).torsion 3,
    weilPairingThree exampleTwo exampleThree exampleS T ≠ 1 := by
  by_contra hcon
  have hall : ∀ T : (y2AddYEqX3 AlgClosedQ).torsion 3,
      weilPairingThree exampleTwo exampleThree exampleS T = 1 := fun T =>
    not_not.mp fun hne => hcon ⟨T, hne⟩
  have h0 : exampleS = 0 :=
    eq_zero_of_forall_weilPairingThree_eq_one exampleTwo exampleThree hall
  exact Point.some_ne_zero exampleNonsingular (congrArg Subtype.val h0)

end Nonvacuity

end WeierstrassCurve.Affine
