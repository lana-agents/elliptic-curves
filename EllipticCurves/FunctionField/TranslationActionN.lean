/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import EllipticCurves.Fixtures
import EllipticCurves.FunctionField.TranslationAction
import EllipticCurves.FunctionField.TranslationMulByNCommGeneral
import EllipticCurves.Torsion.StructureGeneral
import EllipticCurves.Torsion.ThreePrimary

/-!
# The translation action of `E[n]` on the function field, at every `n`

For `G := Multiplicative ↥(W.torsion n)` — the group `E[n]` written multiplicatively — this file
builds a faithful `MulSemiringAction G F(W)` by translation, computes `Nat.card G = n²` over an
algebraically closed base field — at every `3`-smooth `n` in characteristic `≠ 2, 3`, and at
**every** `n` with `(n : F) ≠ 0` in characteristic `≠ 2` — and proves the inclusion

```
[n]∗F(W) ⊆ Fixed(G).
```

It is the general-`n` mirror of `EllipticCurves.FunctionField.TranslationActionThree` (`#784`),
which is the `n = 3` case, and of `EllipticCurves.FunctionField.TranslationAction` (`#758`) at
`n = 2`.  As there, the sandwich that turns the inclusion into an **equality** is a sibling file and
is deliberately **not** here; see `## What is not here` below.

## ⚠️ Two different ranges of `n`, and they must not be conflated

`#1221` has just shown on this board what it costs to bundle a statement with a value of narrower
range, so the split is made explicit here:

* **the action, its faithfulness and the inclusion** hold at **every** `n` at which `[n]` is
  non-constant — no `3`-smoothness, no hypothesis on the characteristic, no `[IsAlgClosed F]`;
* **only the count** `Nat.card (TorsionNMul W n) = n ^ 2` needs `F̄` and a hypothesis on the
  index, because the torsion count does.

Read those hypotheses as belonging to the count lemmas alone.  Everything else in this file is
`n`-agnostic.

⚠️ **The count itself now comes in two ranges, and the wider one is not `3`-smooth**:

* `card_torsionNMul` / `finite_torsionNMul` — `(2 : F) ≠ 0`, `(3 : F) ≠ 0`, `n ≠ 0`, `3`-smooth,
  through `card_torsion_eq_sq_of_smooth` (`EllipticCurves.Torsion.ThreePrimary`);
* `card_torsionNMul_of_ne_zero` / `finite_torsionNMul_of_ne_zero` — `(2 : F) ≠ 0` and `(n : F) ≠ 0`
  and nothing else, through `card_torsion_eq_sq` (`EllipticCurves.Torsion.StructureGeneral`,
  `#293`).  ⚠️ `(n : F) ≠ 0` is **sharp**: at `p = char F` the count is *false*, `E[p]` being `0` or
  `ℤ/pℤ` there.

The `3`-smooth pair is **kept** — it is what the merged consumers cite, and rewriting the front onto
the general pair is `#1523` items 3–4.  This bullet used to end *"would serve `n = 5` unchanged the
day a count exists there"*; that day is `#293`, and `EllipticCurves.FunctionField.MulByNGalois`
serves `n = 5` off the general pair.

## What this file does *not* rebuild, and why it is short

`TranslationAction` builds `translateAut : W.Point → (F(W) ≃ₐ[F] F(W))` — the identity at the point
at infinity, `translateAlgEquiv` at an affine point — together with the homomorphism law
`translateAut_add`, the faithfulness criterion `translateAut_eq_one_iff`, the injectivity
`translateAut_injective` and the bundled `translateAutHom`.  **All of that is stated for an
arbitrary `W.Point` and is `n`-agnostic**, so it is reused here verbatim; the `n = 3` file says the
same of itself and for the same reason.

What is genuinely `n`-dependent is therefore only: the restriction of `translateAutHom` to `E[n]`,
the two instances, the count, and the inclusion.

⚠️ **At general `n` this is shorter than at `n = 3`, not longer.**  Two things that needed
`n = 3`-specific work there are already uniform:

* the torsion datum.  `TranslationActionThree` needs
  `add_add_self_eq_zero_of_mem_torsion_three` to unfold `3 • P = 0` into `P + P + P = 0`, because
  its commutation lemma is stated in that shape.  Here `mem_torsion_iff`
  (`EllipticCurves.Torsion.Defs`) gives `n • P = 0` directly and `translatePoint_nsmul_eq_zero`
  (`EllipticCurves.FunctionField.TranslationTorsionMap`) — which calls itself *"the uniform
  transport"* — carries it to `F(W)` at every `n`;
* the commutation itself, `translateEndo_mulByNEndo_apply_torsion`
  (`EllipticCurves.FunctionField.TranslationMulByNCommGeneral`), which is the general-`n` form of
  the `~250` lines of coordinate work `TranslationTriplingComm` spends on `n = 3` and is proved by
  a group calculation on `(W ⁄ F(W)).Point` instead.

## Why: Artin's theorem at general `n`

`F(W)` is a degree-`n²` extension of `[n]∗F(W)` (`finrank_mulByNFieldRange_of_smooth`, `#1213`; and
`finrank_mulByNFieldRange_eq_sq_of_two_ne_zero` with no smoothness) and `E[n]` has exactly `n²`
elements over an algebraically closed field (`card_torsion_eq_sq_of_smooth`, `#1209`, in
characteristic `≠ 2, 3` at `3`-smooth `n`; `card_torsion_eq_sq`, `#293`, at every `n` with
`(n : F) ≠ 0`).  Translation by an `n`-torsion point fixes `[n]∗f`
pointwise, so `[n]∗F(W) ⊆ Fixed(E[n])`, and `FixedPoints.finrank_eq_card` gives
`[F(W) : Fixed(E[n])] = n²`.  Both outer degrees being `n²`, the sandwich closes and
`Fixed(E[n]) = [n]∗F(W)` exactly — whence separability, **normality** and `IsGalois`.

⚠️ This file is the **first half only**: everything up to and including the inclusion.  The close is
where the value of the whole route is: `#1219` already has the separability by a tower, but
`EllipticCurves.FunctionField.MulByNSeparable` records that a tower **cannot** reach `Normal`,
normality not being transitive, and names this action as the missing method.

⚠️ **The close has landed**, in `EllipticCurves.FunctionField.MulByNGalois` (`#1233`), which
consumes `card_torsionNMul` and `mulByNRange_le_fixedPoints` below.  Everything in the paragraph
above stays true — this file is still the first half, and the split is still what makes each half
short — but *"the close is where the value is"* is now a description of a merged file rather than of
a plan.

## The `DecidableEq F` convention

The group law on `W.Point` is data-dependent on a `DecidableEq F` instance (Mathlib's `Point.add`
branches on `x₁ = x₂`), and this tree uses two conventions: `EllipticCurves/Torsion/` carries
`[DecidableEq F]` as an instance argument, while `EllipticCurves/FunctionField/Translation*.lean`
writes `open Classical in`.  This file follows the `FunctionField/` convention, as
`TranslationActionThree` does.  ⚠️ `card_torsion_eq_sq_of_smooth` is stated with `[DecidableEq F]`
as an instance argument, so it applies verbatim at the classical instance; no
`Subsingleton (Decidable _)` transport is involved, exactly as the `n = 3` file records of
`card_torsion_three`.

## Main results

Every public declaration of this file is listed, and all are in namespace
`WeierstrassCurve.Affine.CoordinateRing`.

* `TorsionNMul` — `E[n]` written multiplicatively, the type the action is keyed on;
* `translateAutNHom` and `translateAutNHom_injective` — the translation homomorphism restricted to
  `E[n]`, and its injectivity;
* the `MulSemiringAction (TorsionNMul W n) F(W)` and `FaithfulSMul` instances, with the `@[simp]`
  unfolding lemmas `translateAutNHom_apply` and `torsionNMul_smul_def`;
* `card_torsionNMul` — `Nat.card (TorsionNMul W n) = n ^ 2` at every `3`-smooth `n ≠ 0` over `F̄`;
* `finite_torsionNMul` — finiteness at the same indices;
* `card_torsionNMul_of_ne_zero` and `finite_torsionNMul_of_ne_zero` — the same two at **every** `n`
  with `(n : F) ≠ 0`, with no `(3 : F) ≠ 0` and no smoothness (`#1523`);
* `translateAut_mulByNEndo` — translation by an `n`-torsion **point of `W`** fixes `[n]∗f`, the
  `O` case included;
* `mulByNEndo_mem_fixedPoints` and `mulByNRange_le_fixedPoints` — `[n]∗F(W) ⊆ Fixed(E[n])`.

## ⚠️ What is *not* here

* **The reverse inclusion, and so no `Normal`, no `IsGalois`, and no `Fixed(E[n]) = [n]∗F(W)`.**
  That is Artin's theorem against `#1213`'s degree, and it is **not in this file**, exactly as
  `TranslationActionThree` splits from `EllipticCurves.FunctionField.MulByThreeGalois` — keeping
  the split is what makes each half short.  ⚠️ **This bullet used to call it "a sibling issue"; it
  is now a sibling *file*** — `EllipticCurves.FunctionField.MulByNGalois` (`#1233`), which imports
  this one and consumes `card_torsionNMul` and `mulByNRange_le_fixedPoints`.  The scope statement is
  unchanged: nothing below proves it.  ⚠️ Note that the inclusion proved here carries **no**
  `[IsAlgClosed F]` while the equality must, since one of its two degrees does.
* ⚠️ **`n = 5` in the count — RETIRED, it landed.**  This bullet used to read
  *"`card_torsion_eq_sq_of_smooth` is `3`-smooth and this file manufactures no new prime."*  The
  second clause is still true and is still why: what changed is the **input**, not this file's
  method.  `card_torsion_eq_sq` (`#293`) is the count at every `n` with `(n : F) ≠ 0`, and
  `card_torsionNMul_of_ne_zero` is it in the multiplicative packaging.  The action, the faithfulness
  and the inclusion remain unaffected either way — they never mention `n²`.
* **Not `#E[n] = n²`.**  That count is an *input* here, merged separately in
  `EllipticCurves.Torsion.ThreePrimary` (`3`-smooth) and `EllipticCurves.Torsion.StructureGeneral`
  (every `n` with `(n : F) ≠ 0`) by the torsion route.  This file supplies no kernel count
  for `[n]` as an isogeny, and the step *"a separable isogeny has `#ker = deg`"* remains nowhere in
  this tree.
* **No coordinate work.**  `ωₙ` (`#404`), the general-`n` on-curve identity, `#251` and Ward
  (`#260`) are all unused: `mulByNEndo` is built from the **group law** on `(W ⁄ F(W)).Point`, and
  as `TranslationMulByNCommGeneral` says of itself, *"the coordinates of `[n]` as rational
  functions remain unavailable and are not needed"*.  ⚠️ **Two of those four are now closed and
  this is an independence claim, not a gate** (`#1460`): `#404`'s on-curve identity is
  `WeierstrassCurve.Affine.equation_div_of_ψ_ne_zero` (`EllipticCurves.Torsion.OmegaCrux`, PR
  #557, every index, every commutative ring) and Ward is
  `WeierstrassCurve.Affine.ψ_isEllipticNet` (`EllipticCurves.Torsion.WardHalving`),
  unconditional.  ⚠️ **And `#251`, which this bullet named as the one of the four still open, is
  closed as well** — `hasXCoordFormula_of_two_ne_zero` (`EllipticCurves.Torsion.NsmulOrder`) with
  its `y`-half `nsmul_eq_some_omegaY_of_ΨSq_ne_zero` (`EllipticCurves.Torsion.NsmulYPeriodic`,
  `#1500`, PR #579), at every index.  So all four are closed, this is an independence claim
  throughout, and none of the four is a gate on anything here.
* **No re-examination of `TranslationTriplingComm`.**  Whether its coordinate work is now redundant
  is a `#699`-style de-duplication question and belongs in its own issue, as that file records.
* `TranslationAction`'s own Scope sentence, that nothing in *that* file is `[2]`- or
  `[3]`-flavoured, is a statement about its contents and stays true; it is deliberately left
  untouched, as the `n = 3` file also left it.

## References

* [J. Silverman, *The arithmetic of elliptic curves*][silverman2009], III.4.
* Artin's theorem on fixed fields, [stacks 09I3].
-/

open Polynomial

namespace WeierstrassCurve.Affine

namespace CoordinateRing

variable {F : Type*} [Field F] {W : Affine F} [W.IsElliptic]

/-! ### The group `E[n]` acting on `F(W)` -/

open Classical in
/-- **The `n`-torsion group `E[n]`, written multiplicatively.**  This is the group that acts on
`F(W)` by translation and whose fixed field is `[n]∗F(W)`; the `Multiplicative` wrapper exists only
because `MulSemiringAction` and `FixedPoints.subfield` are stated for monoids.

The classical `DecidableEq F` instance is baked in here, which is what pins the convention of this
file (see the module docstring) for every statement below. -/
abbrev TorsionNMul (W : Affine F) (n : ℕ) : Type _ := Multiplicative ↥(W.torsion n)

open Classical in
/-- **The translation homomorphism restricted to `E[n]`.**  Injective, being the composite of the
injective `translateAutHom` with the inclusion of a subgroup.  ⚠️ No hypothesis on `n`: this is the
`n`-agnostic `translateAutHom` of `EllipticCurves.FunctionField.TranslationAction` and nothing
more. -/
noncomputable def translateAutNHom (n : ℕ) :
    TorsionNMul W n →* (W.FunctionField ≃ₐ[F] W.FunctionField) :=
  translateAutHom.comp (AddMonoidHom.toMultiplicative (W.torsion n).subtype)

open Classical in
@[simp] lemma translateAutNHom_apply (n : ℕ) (T : TorsionNMul W n) :
    translateAutNHom n T = translateAut (T.toAdd : W.Point) := rfl

open Classical in
theorem translateAutNHom_injective (n : ℕ) :
    Function.Injective (translateAutNHom (F := F) (W := W) n) := by
  intro S T h
  simp only [translateAutNHom_apply] at h
  exact Multiplicative.toAdd.injective (Subtype.ext (translateAut_injective h))

open Classical in
/-- **`E[n]` acts on `F(W)` by ring automorphisms**, through `translateAutNHom` and the tautological
action of `Aut_F F(W)` on `F(W)`.

`MulSemiringAction.compHom` is an `abbrev` and not an instance — it would loop — so the composite is
declared as an instance here, at the head `TorsionNMul W n`.  A global instance keyed on that head
is preferable to a `letI`: downstream files get the action from instance search with nothing to
import but this module, which is the same choice `TranslationActionThree` made at `n = 3`. -/
noncomputable instance (n : ℕ) : MulSemiringAction (TorsionNMul W n) W.FunctionField :=
  MulSemiringAction.compHom _ (translateAutNHom n)

open Classical in
@[simp] lemma torsionNMul_smul_def (n : ℕ) (T : TorsionNMul W n) (g : W.FunctionField) :
    T • g = translateAut (T.toAdd : W.Point) g := rfl

open Classical in
/-- **The action is faithful**, which is the hypothesis Artin's theorem
(`FixedPoints.finrank_eq_card`) carries alongside finiteness. -/
instance (n : ℕ) : FaithfulSMul (TorsionNMul W n) W.FunctionField where
  eq_of_smul_eq_smul h := translateAutNHom_injective n (AlgEquiv.ext h)

/-! ### The order of `E[n]`

⚠️ This is the **only** part of the file that constrains `n` or needs a hypothesis on `F`.
Everything above and everything below is stated at an arbitrary `n` over an arbitrary field.  The
`3`-smooth pair comes first and the general pair after it; neither is deprecated, and `#1523`
records why both are kept. -/

open Classical in
/-- **`|E[n]| = n²` at every `3`-smooth `n ≠ 0`**, in the multiplicative packaging.  This is
`card_torsion_eq_sq_of_smooth` (`EllipticCurves.Torsion.ThreePrimary`, `#1209`) read through the
type synonym; it is the right-hand side of Artin's theorem for the translation action, and the
general-`n` form of `card_torsionThreeMul`.

`card_torsion_eq_sq_of_smooth` is stated with `[DecidableEq F]` as an instance argument, so it
applies verbatim at the classical instance this file works with; no `Subsingleton (Decidable _)`
transport is involved. -/
theorem card_torsionNMul [IsAlgClosed F] (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) {n : ℕ} (hn : n ≠ 0)
    (hfac : ∀ p ∈ n.primeFactors, p = 2 ∨ p = 3) :
    Nat.card (TorsionNMul W n) = n ^ 2 :=
  (Nat.card_congr Multiplicative.toAdd).trans (card_torsion_eq_sq_of_smooth h2 h3 hn hfac)

open Classical in
/-- `E[n]` is finite over an algebraically closed field of characteristic `≠ 2, 3` at every
`3`-smooth `n ≠ 0`, since it has exactly `n²` elements.

This is a `theorem`, not an `instance`, because it rests on the *hypotheses* `h2`, `h3`, `hn` and
`hfac` rather than on typeclasses.  Downstream, fire it as
`haveI := finite_torsionNMul (W := W) h2 h3 hn hfac`; the `Fintype` that
`FixedPoints.finrank_eq_card` asks for is then `Fintype.ofFinite _`, which is noncomputable and
should be kept inside a `haveI` at the use site rather than named in a statement. -/
theorem finite_torsionNMul [IsAlgClosed F] (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) {n : ℕ}
    (hn : n ≠ 0) (hfac : ∀ p ∈ n.primeFactors, p = 2 ∨ p = 3) :
    Finite (TorsionNMul W n) :=
  Nat.finite_of_card_ne_zero (by
    rw [card_torsionNMul h2 h3 hn hfac]; exact pow_ne_zero 2 hn)

open Classical in
/-- **`|E[n]| = n²` at every `n` with `(n : F) ≠ 0`**, in the multiplicative packaging — the
`3`-smoothness of `card_torsionNMul` removed, and the parity restriction with it.

This is `card_torsion_eq_sq` (`EllipticCurves.Torsion.StructureGeneral`, `#293`) read through the
type synonym, exactly as `card_torsionNMul` is `card_torsion_eq_sq_of_smooth` read through it.
⚠️ `(n : F) ≠ 0` is the sharp hypothesis and it is *not* a weakening of `3`-smoothness: at
`p = char F` the conclusion is **false**, `E[p]` being `0` or `ℤ/pℤ` there, never `(ℤ/pℤ)²`.

⚠️ `card_torsionNMul` is **kept**, and not as a deprecation: it is the form whose hypotheses match
the `TwoPrimary` / `ThreePrimary` consumers, and rewriting the `3`-smooth front onto this name is a
separate, mechanical job (`#1523` items 3–4).  Neither statement subsumes the other's *use sites*;
this one does subsume the other's *content* wherever `(n : F) ≠ 0`, which at `3`-smooth `n ≠ 0` with
`(2 : F) ≠ 0` and `(3 : F) ≠ 0` is automatic. -/
theorem card_torsionNMul_of_ne_zero [IsAlgClosed F] (h2 : (2 : F) ≠ 0) {n : ℕ} (hn : (n : F) ≠ 0) :
    Nat.card (TorsionNMul W n) = n ^ 2 :=
  (Nat.card_congr Multiplicative.toAdd).trans (card_torsion_eq_sq h2 hn)

open Classical in
/-- `E[n]` is finite over an algebraically closed field at every `n` with `(n : F) ≠ 0`, since it
has exactly `n²` elements.  The general-`n` form of `finite_torsionNMul`, and the same discipline
applies: fire it as `haveI := finite_torsionNMul_of_ne_zero (W := W) h2 hn` and let
`Fintype.ofFinite` manufacture the `Fintype` inside the proof, never in a statement.

⚠️ `n ≠ 0` is not a separate hypothesis — it follows from `(n : F) ≠ 0`, since `((0 : ℕ) : F) = 0`.
That is the only place the cast is used. -/
theorem finite_torsionNMul_of_ne_zero [IsAlgClosed F] (h2 : (2 : F) ≠ 0) {n : ℕ}
    (hn : (n : F) ≠ 0) : Finite (TorsionNMul W n) :=
  have hn0 : n ≠ 0 := by rintro rfl; simp at hn
  Nat.finite_of_card_ne_zero (by
    rw [card_torsionNMul_of_ne_zero h2 hn]; exact pow_ne_zero 2 hn0)

/-! ### `[n]∗F(W)` is fixed by the action

⚠️ Back to an arbitrary `n` over an arbitrary field: nothing below mentions `n²`, `3`-smoothness,
`(n : F) ≠ 0` or `[IsAlgClosed F]`. -/

open Classical in
/-- **Translation by an `n`-torsion point fixes `[n]∗f`.**  The affine case is
`translateEndo_mulByNEndo_apply_torsion_of_baseField`
(`EllipticCurves.FunctionField.TranslationMulByNCommGeneral`), which says `[n] ∘ τ_T = [n]` when
`n • T = 0`; the point at infinity acts as the identity by construction.

⚠️ Shorter than the `n = 3` mirror `translateAut_mulByThreeEndo`, which needs
`add_add_self_eq_zero_of_mem_torsion_three` to put `3 • P = 0` into the `P + P + P = 0` shape its
commutation lemma is stated in.  Here `mem_torsion_iff` is already the right shape. -/
theorem translateAut_mulByNEndo (n : ℕ)
    (hn : Transcendental F (n • genericPoint (W := W)).xCoord) {P : W.Point}
    (hP : P ∈ W.torsion n) (f : W.FunctionField) :
    translateAut P (mulByNEndo n hn f) = mulByNEndo n hn f := by
  rcases P with _ | ⟨x, y, h⟩
  · rw [← Point.zero_def, translateAut_zero, AlgEquiv.one_apply]
  · rw [translateAut_apply_some]
    exact translateEndo_mulByNEndo_apply_torsion_of_baseField h.left n hn
      (mem_torsion_iff.mp hP) f

open Classical in
/-- **Every `[n]∗f` lies in the fixed field of `E[n]`.** -/
theorem mulByNEndo_mem_fixedPoints (n : ℕ)
    (hn : Transcendental F (n • genericPoint (W := W)).xCoord) (f : W.FunctionField) :
    mulByNEndo n hn f ∈ FixedPoints.subfield (TorsionNMul W n) W.FunctionField := fun T =>
  translateAut_mulByNEndo n hn T.toAdd.2 f

open Classical in
/-- **`[n]∗F(W) ⊆ Fixed(E[n])`**, the inclusion half of the sandwich that identifies the two, at
every `n` at which `[n]` is non-constant and over an arbitrary base field.

The reverse inclusion is a degree count — Artin's theorem against `#1213`'s
`finrank_mulByNFieldRange_of_smooth` — and is **not** proved here; it is
`fixedPoints_subfield_eq_mulByNEndoFieldRange` (`EllipticCurves.FunctionField.MulByNGalois`,
`#1233`), the general-`n` analogue of `fixedPoints_subfield_eq_mulByThreeEndoFieldRange`
(`EllipticCurves.FunctionField.MulByThreeGalois`), and it carries `[IsAlgClosed F]` and
`3`-smoothness.  ⚠️ Neither hypothesis appears in this statement's own signature, and that asymmetry
is the point of splitting the two.

⚠️ **The `Three` name above is a correction**: this docstring shipped citing
`fixedPoints_subfield_eq_mulByThreeFieldRange`, which is not a declaration in this tree — the
`n = 3` statement has `Endo` in the middle, as the `Subfield` presentation always does here. -/
theorem mulByNRange_le_fixedPoints (n : ℕ)
    (hn : Transcendental F (n • genericPoint (W := W)).xCoord) :
    (mulByNEndo (W := W) n hn).range
      ≤ (FixedPoints.subfield (TorsionNMul W n) W.FunctionField).toSubring := by
  rintro _ ⟨f, rfl⟩
  exact mulByNEndo_mem_fixedPoints n hn f

/-! ### Non-vacuity

Every statement above carries `[W.IsElliptic]`, `card_torsionNMul` additionally carries
`[IsAlgClosed F]` and `3`-smoothness, and the action is a `MulSemiringAction` instance found by
search rather than supplied by hand.  A curve on which the whole chain elaborates with nothing
given by hand is therefore committed rather than quoted.

⚠️ **The curve cannot be the `ℚ` curve of most of `FunctionField/`.**  `card_torsionNMul` needs
`[IsAlgClosed F]`, and `y² = x³ − x` — the curve the `n = 2` files certify on — has **no** affine
`3`-torsion point with rational coordinates, so exhibiting a nonidentity element of `E[12]` on it
would mean naming a root of `3X⁴ − 6X² − 1`.  The curve used instead is `y² + y = x³` over
`AlgebraicClosure ℚ`, of discriminant `−27`, on which `T = (0, 0)` has order exactly `3` — the same
curve, under the same construction, that `TranslationActionThree` certifies on and that `#1219` and
`#1221` use for their general-`n` statements.

⚠️ **The index is `12`, not `3`.**  A certificate at `n = 3` would prove nothing about this file:
it would elaborate through statements whose `n` is fixed and would not exercise the point of the
whole exercise, which is that `TorsionNMul W n` is an instance head with `n` a **variable**.  At
`n = 12` the two instances below are genuinely found by search at an index no merged file mentions,
and `T = (0, 0)` is `12`-torsion by `torsion_mono` because `3 ∣ 12`. -/

section Nonvacuity

/-! The certificate curve `y² + y = x³` is the shared `EllipticCurves.Fixture.y2AddYEqX3`, and the
base — algebraically closed, and of characteristic `0` so that `2 ≠ 0` and `3 ≠ 0` — is
`EllipticCurves.Fixture.AlgClosedQ`, whose single `[CharZero F]` instance also supplies
`IsElliptic` here. -/

open EllipticCurves.Fixture

/-- Hoisted rather than written inline: an inline `by norm_num` for `(2 : AlgClosedQ) ≠ 0` is
postponed and leaves the curve a metavariable at the use site. -/
private lemma exampleTwo : (2 : AlgClosedQ) ≠ 0 := two_ne_zero

private lemma exampleThree : (3 : AlgClosedQ) ≠ 0 := three_ne_zero_of_charZero _

/-- ⚠️ `decide` does **not** close this: `Nat.primeFactors` goes through `Nat.primeFactorsList`,
whose `Decidable` instance gets stuck on `Nat.minFac`'s well-founded recursion.  Bounding `p` and
case-splitting is what works — the same note `#1219` and `#1221` record. -/
private lemma smoothTwelve : ∀ p ∈ Nat.primeFactors 12, p = 2 ∨ p = 3 := by
  intro p hp
  obtain ⟨hp1, hp2, -⟩ := Nat.mem_primeFactors.mp hp
  have hle : p ≤ 12 := Nat.le_of_dvd (by norm_num) hp2
  interval_cases p <;> revert hp1 hp2 <;> decide

/-- `T = (0, 0)` lies on `y² + y = x³` and is nonsingular. -/
private lemma exampleNonsingular : (y2AddYEqX3 AlgClosedQ).Nonsingular 0 0 :=
  (y2AddYEqX3 AlgClosedQ).equation_iff_nonsingular.mp (by
    norm_num [y2AddYEqX3, WeierstrassCurve.Affine.equation_iff])

open Classical in
/-- `T = (0, 0)` is `3`-torsion: `Ψ₃ = 3X⁴ + 3b₆X` vanishes at `0`, and the side condition of
`mem_torsion_three_some_iff'` is automatic. -/
private lemma exampleTorsionThree :
    Point.some (0 : AlgClosedQ) 0 exampleNonsingular ∈ (y2AddYEqX3 AlgClosedQ).torsion 3 :=
  mem_torsion_three_some_iff'.mpr (by
    norm_num [y2AddYEqX3, WeierstrassCurve.Ψ₃, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
      WeierstrassCurve.b₆, WeierstrassCurve.b₈])

open Classical in
/-- …and therefore `12`-torsion, by `torsion_mono` at `3 ∣ 12`. -/
private lemma exampleTorsionTwelve :
    Point.some (0 : AlgClosedQ) 0 exampleNonsingular ∈ (y2AddYEqX3 AlgClosedQ).torsion 12 :=
  torsion_mono (by norm_num) exampleTorsionThree

open Classical in
/-- **The action exists at `n = 12`, found by instance search.**  This is the check the sibling
issue depends on: the `MulSemiringAction` instance is keyed on the head `TorsionNMul W n` with `n` a
variable, and it is still found at a concrete index with nothing supplied by hand. -/
noncomputable example :
    MulSemiringAction (TorsionNMul (y2AddYEqX3 AlgClosedQ) 12)
        (y2AddYEqX3 AlgClosedQ).FunctionField :=
  inferInstance

open Classical in
example : FaithfulSMul (TorsionNMul (y2AddYEqX3 AlgClosedQ) 12)
    (y2AddYEqX3 AlgClosedQ).FunctionField :=
  inferInstance

open Classical in
/-- The acting group has more than one element, so the fixed field is not all of `F(W)` for a
trivial reason. -/
example : Nontrivial (TorsionNMul (y2AddYEqX3 AlgClosedQ) 12) :=
  ⟨⟨Multiplicative.ofAdd ⟨_, exampleTorsionTwelve⟩, 1, by
    simp only [ne_eq, ← Multiplicative.toAdd.injective.eq_iff, Subtype.ext_iff]
    exact Point.some_ne_zero exampleNonsingular⟩⟩

open Classical in
/-- **`|E[12]| = 144` on a genuine curve**, at an index no merged file computes. -/
example : Nat.card (TorsionNMul (y2AddYEqX3 AlgClosedQ) 12) = 144 :=
  card_torsionNMul exampleTwo exampleThree (by norm_num) smoothTwelve

open Classical in
example : Finite (TorsionNMul (y2AddYEqX3 AlgClosedQ) 12) :=
  finite_torsionNMul exampleTwo exampleThree (by norm_num) smoothTwelve

open Classical in
/-- The transcendence hypothesis at `n = 12`, discharged rather than assumed:
`transcendental_xCoord_nsmul_of_isAlgClosed` gives it at every `n ≠ 0` over `F̄`. -/
private lemma exampleTranscendentalTwelve :
    Transcendental AlgClosedQ ((12 : ℕ) • genericPoint (W := y2AddYEqX3 AlgClosedQ)).xCoord :=
  transcendental_xCoord_nsmul_of_isAlgClosed exampleTwo (by norm_num)

open Classical in
/-- **`[12]∗F(W) ⊆ Fixed(E[12])`, committed.**  ⚠️ Neither `[IsAlgClosed F]` nor `3`-smoothness is
used by the statement being certified — only by the curve it is certified on, which needs the first
to have a `12`-torsion point to exhibit at all. -/
example : (mulByNEndo (W := y2AddYEqX3 AlgClosedQ) 12 exampleTranscendentalTwelve).range
    ≤ (FixedPoints.subfield (TorsionNMul (y2AddYEqX3 AlgClosedQ) 12)
      (y2AddYEqX3 AlgClosedQ).FunctionField).toSubring :=
  mulByNRange_le_fixedPoints 12 exampleTranscendentalTwelve

open Classical in
example (f : (y2AddYEqX3 AlgClosedQ).FunctionField) :
    translateAut (Point.some (0 : AlgClosedQ) 0 exampleNonsingular)
        (mulByNEndo 12 exampleTranscendentalTwelve f)
      = mulByNEndo 12 exampleTranscendentalTwelve f :=
  translateAut_mulByNEndo 12 exampleTranscendentalTwelve exampleTorsionTwelve f

end Nonvacuity

end CoordinateRing

end WeierstrassCurve.Affine
