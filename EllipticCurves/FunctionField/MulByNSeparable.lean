/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import EllipticCurves.Fixtures
import EllipticCurves.FunctionField.MulByNComposition
import EllipticCurves.FunctionField.MulByThreeGalois
import EllipticCurves.FunctionField.MulByTwoGalois

/-!
# `F(W)` is separable over `[n]∗F(W)` at every `3`-smooth `n`

Let `W` be an elliptic curve over an algebraically closed field `F` of characteristic `≠ 2, 3`.
`EllipticCurves.FunctionField.MulByTwoGalois` (`#759`) and
`EllipticCurves.FunctionField.MulByThreeGalois` prove

```
Algebra.IsSeparable ([2]∗F(W)) F(W)        and        Algebra.IsSeparable ([3]∗F(W)) F(W)
```

by Artin's theorem, each against a translation action by a torsion group whose order is computed.
This file composes them: **separability is transitive in towers**, so
`EllipticCurves.FunctionField.MulByNComposition`'s `[m · n]∗ = [m]∗ ∘ [n]∗` carries the two merged
statements to

```
Algebra.IsSeparable ([n]∗F(W)) F(W)        for every 3-smooth n.
```

Nothing here is new about torsion, about Artin's theorem, or about `[n]` — the whole file is the
tower step plus the induction `MulByNComposition` already ran for the degree.

Where a statement below takes `h : Transcendental F (n • genericPoint).xCoord` as an explicit
argument, no reach clause names it, under `README.md`'s derivability exemption: at a `3`-smooth
`n ≠ 0` with `(2 : F) ≠ 0` and `(3 : F) ≠ 0` it is produced by
`transcendental_xCoord_nsmul_of_smooth` (`EllipticCurves.FunctionField.MulByNComposition`), which
is exactly what those clauses name — and `2 ^ a * 3 ^ b` is such an `n`, so the same lemma covers
`isSeparable_mulByNFieldRange_two_pow_mul_three_pow`.  ⚠️ `isSeparable_fieldRange_comp` takes no
such argument — it is about two arbitrary `F`-algebra endomorphisms and sits above the
`variable [W.IsElliptic]` line — and `isSeparable_mulByNFieldRange_mul`, `…_of_mul_eq` and
`…_one` take transcendence hypotheses as the *data* they are statements about and name no
hypothesis at all.

⚠️ **That universal was read row by row and it HOLDS, which is why it is still here** (`#1696`).
The sentence is a copy — `#1688` and `#1696` measured six files carrying it — and this file's copy
is the one that survived the reading.  The ground is recorded here so that the next sweep does not
repair a true sentence: `#1647`'s standing instruction covers wordings that are false of their own
lists, and pre-emptive editing is the thing it rules out.  Recogniser, run
here: every prose occurrence of *"non-constan…"* or *"transcenden…"* at or below the
`## Main statements` heading, outside backticks and inside a comment, read one by one.  **Two**
occur and neither is a reach clause:

* `### Non-vacuity`'s *"The non-constancy hypothesis is **produced** by
  `transcendental_xCoord_nsmul_of_smooth` rather than assumed"* quantifies over one certificate at
  `n = 12`, not over the declarations below.  ⚠️ Its `…MulByNInertia` twin **does** count, and the
  difference is a phrase and not a file: that one reads *"produced **at every index below**, never
  assumed"*, and `README.md` `### Reach clauses` wants a phrase that says how far something goes;
* the non-surjectivity certificate's *"certified here on the same curve only because that is where
  the non-constancy hypothesis is already built"* says why the witness lives where it does.

None of the `## Main statements` bullets names the parameter either: they name index conditions
(*"at `3`-smooth `n ∉ {0, 1}`"*) and instance hypotheses, which is the register's own subject.
⚠️ Backticked `transcendental_…` names are citations and not clauses (PR #671's exclusion).

## ⚠️ What this refutes

`EllipticCurves.FunctionField.MulByThreeGalois` listed, under *"What is not here"*:

> General `[n]∗`: `#775`'s degree `9` is `[3]`-specific and `card_torsion_three` is the `n = 3`
> count.  **The general case waits on `#E[n] = n²` and on `#403`/`#404`/`#405`.**

The second sentence is **false at every `3`-smooth `n`**.  The `3`-smooth case waits on none of
`#E[n] = n²`, `#403`, `#404`, `#405`; it waits on the composition law, which is merged.  What those
four gate is the *general* `n`, and the first index at which they are needed is `n = 5`.  ⚠️ *"They
are needed"* is about the **division-polynomial** route to `n = 5`, which is what that quotation is
about; it is not a claim that nothing reaches `n = 5`.  Separability, normality and `IsGalois` at
`n = 5` are theorems in `EllipticCurves.FunctionField.MulByNGalois` (`#1523`), by the translation
action and `#293`'s count, and they consume none of `#403`/`#405`.

⚠️ **`#404` has since been paid and is no longer one of them** (`#1460`).  Its on-curve identity is
`WeierstrassCurve.Affine.equation_div_of_ψ_ne_zero` (`EllipticCurves.Torsion.OmegaCrux`, PR #557),
at every index over a field with `(2 : F) ≠ 0` and under `ψₙ(x, y) ≠ 0`.  ⚠️ The quotation above is
left verbatim because it is a quotation.  At `n = 5` the division-polynomial route still waits on
`#E[n] = n²` and on `#403`/`#405` — whose missing input `#404` was.  ⚠️ **`#251` used to be listed
here as a third and is closed**: the identification of the division-polynomial coordinates with the
group-law multiple `n • P`, which `#404` never claimed to supply, is
`hasXCoordFormula_of_two_ne_zero` (`EllipticCurves.Torsion.NsmulOrder`) on its `x`-half and
`nsmul_eq_some_omegaY_of_ΨSq_ne_zero` (`EllipticCurves.Torsion.NsmulYPeriodic`, `#1500`, PR #579) on
its `y`-half, at every index with `(2 : F) ≠ 0`, under `ΨSqₙ(x) ≠ 0`.

This is `#1213`'s finding a second time, and by the same detector: **take a merged sentence of the
form "X is gated on A, B, C" and ask whether A, B, C gate the statement or gate one route to it.**
`#1213` applied it to the degree `[F(W) : [n]∗F(W)] = n²`; here it applies to separability.  The
route those two files were decomposed around — a division-polynomial coordinate formula for `[n]` —
really does need all four, and every session that read the paragraph re-derived the gate *within*
it.

## The tower step

For `F`-algebra endomorphisms `φ`, `ψ` of `F(W)`, the tower is `F(W) ⊇ φF(W) ⊇ φψF(W)`, exactly as
in `MulByNComposition`'s `finrank_fieldRange_comp`:

* the **upper** storey `F(W) / φF(W)` is separable by hypothesis;
* the **lower** storey `φF(W) / φψF(W)` is `F(W) / ψF(W)` transported along `φ`, which is an
  isomorphism onto its range because it is a ring homomorphism out of a field;
* `Algebra.IsSeparable.trans` composes them.

⚠️ Two friction points, both mechanical and both worth knowing in advance.  There is no
`Algebra ↥A ↥B` instance for intermediate fields with `A ≤ B` — `h : A ≤ B` is not a class — so the
tower has to be built by hand out of `IntermediateField.inclusion` and
`IsScalarTower.of_algebraMap_eq'`, which is what Mathlib's own `relrank_mul_rank_top` does.  And
`Algebra.IsSeparable ↥(⊤ : IntermediateField F L) L` is likewise not an instance, so the base case
`[1]∗ = id` is a step rather than an `infer_instance`.

## ⚠️ What is *not* here, and one of them is an obstruction rather than a gap

* **No `Normal`, and so no `IsGalois`, *by the argument in this file*, at any `n ∉ {2, 3}`.**  Both
  Galois files deliver `normal_…` and `isGalois_…` beside separability, so the omission is
  conspicuous; it is not an oversight.  ⚠️ **The emphasis is a correction**: the heading used to
  read *"No `Normal`, and so no `IsGalois`, at any `n ∉ {2, 3}`"* flat, which read as a claim about
  the tree, and as a claim about the tree it is **false** at every `3`-smooth `n` —
  `EllipticCurves.FunctionField.MulByNGalois` (`#1233`) proves both.  As a claim about *this file's
  route* it was and remains exactly right, and the reason is the next sentence.
  **Normality is not transitive** — `ℚ(⁴√2) / ℚ(√2) / ℚ` is the standard counterexample, both
  storeys normal and the composite not — so the argument below, which is nothing but a tower,
  cannot reach it.  ⚠️ The *statement* `IsGalois ([n]∗F(W)) F(W)` is nevertheless **true** at every
  `3`-smooth `n`, with Galois group `E[n]` acting by translation.
  ⚠️ **The clause this bullet used to end with priced that route and the price was wrong** — it
  read *"Reaching it needs the general-`n` analogue of
  `EllipticCurves.FunctionField.TranslationAction` /
  `EllipticCurves.FunctionField.TranslationActionThree` — a `TorsionNMul` action with `FaithfulSMul`
  and `card = n²` — which is a different and much larger build.  **What is missing is the method,
  not the truth.**"*  The action is `EllipticCurves.FunctionField.TranslationActionN` (`#1232`) and
  it is **short**, because every input it needs was already merged when the clause was written:
  `translateAutHom` is `n`-agnostic, `translatePoint_nsmul_eq_zero` is the uniform torsion
  transport at every `n`, and `card_torsion_eq_sq_of_smooth` (`#1209`) supplies `card = n²`.  ⚠️
  **Both halves have since landed.**  `TranslationActionN` gives the action, its faithfulness and
  the inclusion `[n]∗F(W) ⊆ Fixed(E[n])`; `EllipticCurves.FunctionField.MulByNGalois` (`#1233`)
  closes the Artin sandwich against `#1213`'s degree, so `Fixed(E[n]) = [n]∗F(W)` and
  `normal_mulByNFieldRange_of_smooth` / `isGalois_mulByNFieldRange_of_smooth` hold at every
  `3`-smooth `n`.  What was missing was never the truth; it was the method, and it has been paid in
  two files rather than one.
* **No `#E[n] = n²`, and no isogeny counting.**  `EllipticCurves.FunctionField.MulByTwoDegree` and
  `EllipticCurves.FunctionField.MulByTwoFibreInfinity` both record that the step *"a separable
  isogeny has as many points in its kernel as its degree"* is nowhere in this tree.  That stays
  exactly as true as it was: this file supplies one **hypothesis** of that step at more indices, not
  the step.
* ⚠️ **Nothing at `n = 5` *by this file's method*, and that is now a statement about the method
  rather than about the tree.**  The composition law manufactures no new prime, so `…_of_smooth` is
  as wide as the set of indices whose prime factors are `2` and `3` and no wider — that clause is
  unchanged and unchangeable.  What changed is the conclusion that used to be drawn from it:
  `isSeparable_mulByNFieldRange_of_ne_zero` (`EllipticCurves.FunctionField.MulByNGalois`, `#1523`)
  proves separability at **every** `n` with `(n : F) ≠ 0`, `n = 5` included, by reading it off the
  fixed field of the translation action instead of by multiplying up.  ⚠️ **This file's route is
  kept and is not superseded in scope**: it is the only separability proof here that does not need
  `#E[n] = n²`, hence the only one that survives if the count is ever weakened.  What it is no
  longer is *load-bearing*.
* **No fundamental identity at `3`-smooth `n`** — and this is the one worth being precise about,
  because it is *closer* than the rest of this list.
  `EllipticCurves.FunctionField.PlaceInertiaGeneral` proves
  `∑_{p ↦ q} e_p · f_p = [F(W) : φF(W)]` at an **arbitrary** `φ`, under exactly
  `[Module.Finite ↥φ.fieldRange F(W)]` and `[Algebra.IsSeparable ↥φ.fieldRange F(W)]` (plus `φ`
  fixing `F` and integrality).  At a `3`-smooth `n` the first is
  `module_finite_mulByNEndoFieldRange` (`EllipticCurves.FunctionField.MulByNIntegral`, general `n`)
  and the second is `isSeparable_mulByNEndoFieldRange_of_smooth` below, so both instance
  hypotheses are now available.  ⚠️ **The clause this bullet used to carry has been paid** — it
  read *"Instantiating it is nevertheless not done here, and the remaining work is real rather than
  notational: the identity's right-hand side is a `finrank` of an integral closure over
  `placeBelow`, not `n²`, and `[IsDedekindDomain W.CoordinateRing]` has to be carried.  Filed rather
  than reached for."*  It was filed as `#1221` and paid in
  `EllipticCurves.FunctionField.MulByNInertia`, which imports this file; the pricing was right, and
  the `finrank`-versus-`n²` distinction it names turns out to be the *content* rather than an
  obstacle — the identity holds at every `n` in characteristic zero, and only the value `n²` is
  `3`-smooth.

## Main statements

⚠️ Every public declaration of this file is listed.

* `WeierstrassCurve.Affine.CoordinateRing.isSeparable_fieldRange_comp` — the tower step, for
  arbitrary `F`-algebra endomorphisms `φ`, `ψ` of `F(W)`.  No `[W.IsElliptic]`, no
  `[IsAlgClosed F]`, no mention of `[n]`;
* `…isSeparable_mulByNFieldRange_mul` — separability composes in the index, and
  `…isSeparable_mulByNFieldRange_of_mul_eq` is the `m * n = k` form the inductions use;
* `…isSeparable_mulByNFieldRange_one` — the base case, `[1]∗F(W) = F(W)`;
* `…isSeparable_mulByNFieldRange_two_pow_mul_three_pow` and
  `…isSeparable_mulByNFieldRange_of_smooth` — **the headline**, in the `IntermediateField`
  presentation;
* `…mulByNFieldRangeEquivSubfield` and `…isSeparable_mulByNEndoFieldRange_of_smooth` — the same in
  the `Subfield` presentation, which is the one a place-theoretic consumer states its hypotheses in;
* `…not_surjective_mulByNEndo_of_smooth` — `[n]∗` is not surjective at `3`-smooth `n ∉ {0, 1}`.
  ⚠️ A **degree** consequence, on strictly weaker hypotheses than everything above it: no
  `[IsAlgClosed F]`, and no separability.

## References

* [J. Silverman, *The arithmetic of elliptic curves*][silverman2009], II.2, III.4.
-/

open Module Polynomial IntermediateField

namespace WeierstrassCurve.Affine

namespace CoordinateRing

variable {F : Type*} [Field F] {W : Affine F}

/-! ### The tower step: separability of a composite -/

/-- **Separability passes to a composite.**  If `F(W)` is separable over `ψF(W)` and over `φF(W)`,
then it is separable over `(φ ∘ ψ)F(W)`.

The tower is `F(W) ⊇ φF(W) ⊇ φψF(W)`.  Its upper storey is the hypothesis at `φ`; its lower storey
is the hypothesis at `ψ` transported along `φ`, which is an isomorphism onto its range because a
ring homomorphism out of a field is injective.  `Algebra.IsSeparable.trans` composes them.

⚠️ There is no `Algebra ↥A ↥B` instance for intermediate fields `A ≤ B`, because `h : A ≤ B` is not
a class; the two `letI`/`haveI` lines below are Mathlib's own idiom for it, copied from
`IntermediateField.relrank_mul_rank_top`.

⚠️ Nothing about `φ` or `ψ` is used beyond their being `F`-algebra homomorphisms of a field, and no
`[W.IsElliptic]` or `[IsAlgClosed F]` appears — this is the separability counterpart of
`finrank_fieldRange_comp` and sits above the `variable [W.IsElliptic]` line for the same reason. -/
theorem isSeparable_fieldRange_comp (φ ψ : W.FunctionField →ₐ[F] W.FunctionField)
    (hφ : Algebra.IsSeparable ↥φ.fieldRange W.FunctionField)
    (hψ : Algebra.IsSeparable ↥ψ.fieldRange W.FunctionField) :
    Algebra.IsSeparable ↥(φ.comp ψ).fieldRange W.FunctionField := by
  haveI := hφ
  haveI := hψ
  have hrange : (φ.comp ψ).fieldRange = ψ.fieldRange.map φ := fieldRange_comp φ ψ
  have hle : (φ.comp ψ).fieldRange ≤ φ.fieldRange := by
    rw [hrange, AlgHom.fieldRange_eq_map φ]
    exact IntermediateField.map_mono φ le_top
  letI : Algebra ↥(φ.comp ψ).fieldRange ↥φ.fieldRange :=
    (IntermediateField.inclusion hle).toAlgebra
  haveI : IsScalarTower ↥(φ.comp ψ).fieldRange ↥φ.fieldRange W.FunctionField :=
    IsScalarTower.of_algebraMap_eq' rfl
  haveI : Algebra.IsSeparable ↥(φ.comp ψ).fieldRange ↥φ.fieldRange := by
    refine Algebra.IsSeparable.of_equiv_equiv
      ((IntermediateField.equivMap ψ.fieldRange φ).toRingEquiv.trans
        (IntermediateField.equivOfEq hrange.symm).toRingEquiv)
      (AlgEquiv.ofInjectiveField φ).toRingEquiv ?_
    ext x
    rfl
  exact Algebra.IsSeparable.trans ↥(φ.comp ψ).fieldRange ↥φ.fieldRange W.FunctionField

variable [W.IsElliptic]

/-! ### Separability, multiplied up -/

/-- **Separability composes in the index.**  `isSeparable_fieldRange_comp` against
`mulByNEndoAlgHom_mul`, and it is where the `3`-smooth statement below comes from. -/
theorem isSeparable_mulByNFieldRange_mul {m n : ℕ}
    (hm : Transcendental F (m • genericPoint (W := W)).xCoord)
    (hn : Transcendental F (n • genericPoint (W := W)).xCoord)
    (hmn : Transcendental F ((m * n) • genericPoint (W := W)).xCoord)
    (Hm : Algebra.IsSeparable ↥(mulByNEndoAlgHom m hm).fieldRange W.FunctionField)
    (Hn : Algebra.IsSeparable ↥(mulByNEndoAlgHom n hn).fieldRange W.FunctionField) :
    Algebra.IsSeparable ↥(mulByNEndoAlgHom (m * n) hmn).fieldRange W.FunctionField := by
  rw [mulByNEndoAlgHom_mul hm hn]
  exact isSeparable_fieldRange_comp _ _ Hm Hn

/-- **Separability composes, at a stated product.**  The `m * n = k` form, and the one both
inductions below use: `mulByNEndoAlgHom n h` carries `n` inside the *type* of `h`, so a step from
`2 ^ a * 3 ^ b` to `2 ^ (a + 1) * 3 ^ b` cannot transport the hypothesis by `rw`.  `subst` does the
index arithmetic once, here, instead of at each call site — the trade
`EllipticCurves.FunctionField.MulByNComposition` records for the degree, made again. -/
theorem isSeparable_mulByNFieldRange_of_mul_eq {m n k : ℕ} (hk : m * n = k)
    (hm : Transcendental F (m • genericPoint (W := W)).xCoord)
    (hn : Transcendental F (n • genericPoint (W := W)).xCoord)
    (h : Transcendental F (k • genericPoint (W := W)).xCoord)
    (Hm : Algebra.IsSeparable ↥(mulByNEndoAlgHom m hm).fieldRange W.FunctionField)
    (Hn : Algebra.IsSeparable ↥(mulByNEndoAlgHom n hn).fieldRange W.FunctionField) :
    Algebra.IsSeparable ↥(mulByNEndoAlgHom k h).fieldRange W.FunctionField := by
  subst hk
  exact isSeparable_mulByNFieldRange_mul hm hn h Hm Hn

/-- **`F(W)` is separable over `[1]∗F(W)`**, the base of both inductions: `[1]∗` is the identity
(`mulByNEndo_one`), whose range is `⊤`.

⚠️ `Algebra.IsSeparable ↥(⊤ : IntermediateField F L) L` is not an instance, so this is a step and
not `infer_instance`; `IntermediateField.topEquiv` carries it from `Algebra.IsSeparable L L`. -/
theorem isSeparable_mulByNFieldRange_one
    (h : Transcendental F ((1 : ℕ) • genericPoint (W := W)).xCoord) :
    Algebra.IsSeparable ↥(mulByNEndoAlgHom 1 h).fieldRange W.FunctionField := by
  have hid : mulByNEndoAlgHom (W := W) 1 h = AlgHom.id F W.FunctionField :=
    AlgHom.coe_ringHom_injective (mulByNEndo_one (W := W))
  rw [hid, AlgHom.fieldRange_eq_map, IntermediateField.map_id]
  exact Algebra.IsSeparable.of_equiv_equiv
    (IntermediateField.topEquiv (F := F) (E := W.FunctionField)).symm.toRingEquiv
    (RingEquiv.refl W.FunctionField) (by ext a; rfl)

/-- **`F(W)` is separable over `[2^a · 3^b]∗F(W)`**, over an algebraically closed base field of
characteristic `≠ 2, 3`.

Induction on `a` and then on `b`, with `isSeparable_mulByNFieldRange_of_mul_eq` at each step.  ⚠️
The two prime steps are the *only* place Artin's theorem enters, and they are the merged `n = 2`
and `n = 3` statements — `isSeparable_mulByTwoFieldRange_of_isAlgClosed` (`#759`) and
`isSeparable_mulByThreeFieldRange_of_isAlgClosed` — reached through `mulByNEndoAlgHom_two` and
`mulByNEndoAlgHom_three`.  Nothing new about torsion is proved anywhere below.

⚠️ `[IsAlgClosed F]` is inherited from those two inputs and cannot be dropped here: both run on
`FixedPoints.finrank_eq_card` against a torsion group whose order the algebraic closure is what
makes computable.  The characteristic-zero route (`Algebra.IsSeparable.of_integral`) is a
different theorem with a different hypothesis, and composing *it* is a separate question. -/
theorem isSeparable_mulByNFieldRange_two_pow_mul_three_pow [IsAlgClosed F]
    (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) (a b : ℕ)
    (h : Transcendental F ((2 ^ a * 3 ^ b) • genericPoint (W := W)).xCoord) :
    Algebra.IsSeparable ↥(mulByNEndoAlgHom (2 ^ a * 3 ^ b) h).fieldRange W.FunctionField := by
  induction a with
  | zero =>
    induction b with
    | zero => exact isSeparable_mulByNFieldRange_one h
    | succ b ih =>
      have hb := transcendental_xCoord_two_pow_mul_three_pow_nsmul (W := W) h2 h3 0 b
      refine isSeparable_mulByNFieldRange_of_mul_eq (m := 3) (n := 2 ^ 0 * 3 ^ b) (by ring)
        (transcendental_xCoord_three_nsmul h2 h3) hb h ?_ (ih hb)
      rw [mulByNEndoAlgHom_three h2 h3]
      exact isSeparable_mulByThreeFieldRange_of_isAlgClosed h2 h3
  | succ a ih =>
    have ha := transcendental_xCoord_two_pow_mul_three_pow_nsmul (W := W) h2 h3 a b
    refine isSeparable_mulByNFieldRange_of_mul_eq (m := 2) (n := 2 ^ a * 3 ^ b) (by ring)
      (transcendental_xCoord_two_nsmul h2) ha h ?_ (ih ha)
    rw [mulByNEndoAlgHom_two h2]
    exact isSeparable_mulByTwoFieldRange_of_isAlgClosed h2

/-- **`F(W)` is separable over `[n]∗F(W)` at every `3`-smooth `n ≠ 0` with `(2 : F) ≠ 0` and
`(3 : F) ≠ 0`.**

The hypotheses `n ≠ 0` and `∀ p ∈ n.primeFactors, p = 2 ∨ p = 3` are those of
`finrank_mulByNFieldRange_of_smooth`, which is the degree at the same slice of indices, and of
`card_torsion_eq_sq_of_smooth` (`EllipticCurves.Torsion.ThreePrimary`), which is `#E[n] = n²` at it.

⚠️ The first index **this argument** does not cover is `n = 5`; it manufactures no new prime.  ⚠️
That is not a statement about the tree: `isSeparable_mulByNFieldRange_of_ne_zero`
(`EllipticCurves.FunctionField.MulByNGalois`, `#1523`) covers every `n` with `(n : F) ≠ 0`, off the
fixed field of the translation action.  This theorem stays because it is the only separability proof
here that does not consume `#E[n] = n²`.

⚠️ This is separability only, and `Normal` does *not* follow **from it**, because normality is not
transitive.  ⚠️ That sentence used to end *"— `Normal`, and so `IsGalois`, does not follow"* without
the emphasis, which read as a claim about the tree; `Normal` and `IsGalois` are now proved at
exactly these hypotheses by a different route, in
`EllipticCurves.FunctionField.MulByNGalois` (`#1233`).  ⚠️ That file used to consume this theorem as
the separable half of `isGalois_mulByNFieldRange_of_smooth` and mint no separability of its own; it
still does at `3`-smooth `n`, but its general-`n` half mints its own (`#1523`).  See the module
docstring. -/
theorem isSeparable_mulByNFieldRange_of_smooth [IsAlgClosed F]
    (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) {n : ℕ} (hn : n ≠ 0)
    (hfac : ∀ p ∈ n.primeFactors, p = 2 ∨ p = 3)
    (h : Transcendental F (n • genericPoint (W := W)).xCoord) :
    Algebra.IsSeparable ↥(mulByNEndoAlgHom n h).fieldRange W.FunctionField := by
  obtain ⟨a, b, rfl⟩ := Nat.exists_eq_two_pow_mul_three_pow n hn hfac
  exact isSeparable_mulByNFieldRange_two_pow_mul_three_pow h2 h3 a b h

/-! ### The `Subfield` presentation -/

/-- The identity map, read as an isomorphism from the `IntermediateField` presentation of
`[n]∗F(W)` to the `Subfield` one.  Both are the same subset — `mem_fieldRange` twice — but they live
in different subobject lattices, and separability has to be carried across.

The general-`n` form of `mulByTwoFieldRangeEquivSubfield` and `mulByThreeFieldRangeEquivSubfield`.
As there, there is deliberately no `Subring` version. -/
def mulByNFieldRangeEquivSubfield (n : ℕ)
    (h : Transcendental F (n • genericPoint (W := W)).xCoord) :
    ↥(mulByNEndoAlgHom n h).fieldRange ≃+* ↥(mulByNEndo n h).fieldRange where
  toFun a := ⟨a.1, a.2⟩
  invFun a := ⟨a.1, a.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl

/-- **Separability at every `3`-smooth `n ≠ 0` with `(2 : F) ≠ 0` and `(3 : F) ≠ 0`, in the
`Subfield` presentation** — the form a consumer
that has to write `ValuationSubring ↥L` wants, since `ValuationSubring` needs `L` to be a `Field`
type and the `Subfield` coercion is one.

It is also the entry `IsIntegralClosure.finite` asks for by name; see the module docstring on what
that does and does not buy. -/
theorem isSeparable_mulByNEndoFieldRange_of_smooth [IsAlgClosed F]
    (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) {n : ℕ} (hn : n ≠ 0)
    (hfac : ∀ p ∈ n.primeFactors, p = 2 ∨ p = 3)
    (h : Transcendental F (n • genericPoint (W := W)).xCoord) :
    Algebra.IsSeparable ↥(mulByNEndo n h).fieldRange W.FunctionField := by
  haveI := isSeparable_mulByNFieldRange_of_smooth h2 h3 hn hfac h
  exact Algebra.IsSeparable.of_equiv_equiv (mulByNFieldRangeEquivSubfield n h)
    (RingEquiv.refl W.FunctionField) (by ext a; rfl)

/-! ### Non-surjectivity, on strictly weaker hypotheses -/

/-- **`[n]∗` is not surjective at every `3`-smooth `n ∉ {0, 1}` with `(2 : F) ≠ 0` and
`(3 : F) ≠ 0`.**  A surjective endomorphism would
have `fieldRange = ⊤`, hence index one, contradicting index `n²`.

The general form of `not_surjective_mulByTwoEndo` (`EllipticCurves.FunctionField.MulByTwoDegree`)
and `not_surjective_mulByThreeEndo` (`EllipticCurves.FunctionField.MulByThreeDegree`).

⚠️ **This is a degree consequence and its hypotheses are strictly weaker than everything above:
no `[IsAlgClosed F]`, and no separability.**  It runs on
`finrank_mulByNFieldRange_of_smooth` (`EllipticCurves.FunctionField.MulByNComposition`) alone, and
it holds over any field in which `2` and `3` are invertible.  It sits in this file because it is the
other thing the composition law buys at a `3`-smooth index, not because it needs anything here. -/
theorem not_surjective_mulByNEndo_of_smooth (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) {n : ℕ}
    (hn : n ≠ 0) (hn1 : n ≠ 1) (hfac : ∀ p ∈ n.primeFactors, p = 2 ∨ p = 3)
    (h : Transcendental F (n • genericPoint (W := W)).xCoord) :
    ¬ Function.Surjective (mulByNEndo n h) := by
  intro hs
  have htop : (mulByNEndoAlgHom (W := W) n h).fieldRange = ⊤ := AlgHom.fieldRange_eq_top.mpr hs
  have hdeg := finrank_mulByNFieldRange_of_smooth (W := W) h2 h3 hn hfac h
  rw [htop, ← IntermediateField.relfinrank_top_right (⊤ : IntermediateField F W.FunctionField),
    IntermediateField.relfinrank_self] at hdeg
  exact hn1 (by nlinarith [Nat.one_le_iff_ne_zero.mpr hn])

/-! ### Non-vacuity

The headline needs `[IsAlgClosed F]`, `[W.IsElliptic]`, `(2 : F) ≠ 0` and `(3 : F) ≠ 0` at once, and
both prime inputs rest on groups whose orders are computed rather than assumed — so a curve on which
the whole chain elaborates is committed rather than quoted.

⚠️ At a `3`-smooth index **both** prime inputs fire, so the certificate has to be a curve that
witnesses the `n = 3` chain as well as the `n = 2` one; `y² + y = x³` over `AlgebraicClosure ℚ` is
that curve, and it is the one `EllipticCurves.FunctionField.TranslationActionThree` and
`EllipticCurves.FunctionField.MulByThreeGalois` use, for the same reason.  ⚠️ The `ℚ` curve of most
of `FunctionField/` cannot witness a statement that needs an algebraically closed base field, and
weakening the statement to fit it would defeat the point.

The non-constancy hypothesis is **produced** by `transcendental_xCoord_nsmul_of_smooth` rather than
assumed: a separability statement whose hypothesis could not be met would be vacuous.  `n = 12` is
an index at which neither merged input says anything. -/

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
whose `Decidable` instance gets stuck on `Nat.minFac`'s well-founded recursion.  Bounding `p` by
`12` and case-splitting is what works. -/
private lemma exampleSmoothTwelve : ∀ p ∈ Nat.primeFactors 12, p = 2 ∨ p = 3 := by
  intro p hp
  obtain ⟨hp1, hp2, -⟩ := Nat.mem_primeFactors.mp hp
  have hle : p ≤ 12 := Nat.le_of_dvd (by norm_num) hp2
  interval_cases p <;> revert hp1 hp2 <;> decide

/-- **The headline, committed**: `F(W)` is separable over `[12]∗F(W)` on a genuine curve — an index
at which neither `#759` nor its `n = 3` twin says anything. -/
example : Algebra.IsSeparable
    ↥(mulByNEndoAlgHom (W := y2AddYEqX3 AlgClosedQ) 12
      (transcendental_xCoord_nsmul_of_smooth exampleTwo exampleThree (by norm_num)
        exampleSmoothTwelve)).fieldRange (y2AddYEqX3 AlgClosedQ).FunctionField :=
  isSeparable_mulByNFieldRange_of_smooth exampleTwo exampleThree (by norm_num)
    exampleSmoothTwelve _

/-- The same in the `Subfield` presentation, which is the one a place-theoretic consumer states its
hypotheses in. -/
example : Algebra.IsSeparable
    ↥(mulByNEndo (W := y2AddYEqX3 AlgClosedQ) 12
      (transcendental_xCoord_nsmul_of_smooth exampleTwo exampleThree (by norm_num)
        exampleSmoothTwelve)).fieldRange (y2AddYEqX3 AlgClosedQ).FunctionField :=
  isSeparable_mulByNEndoFieldRange_of_smooth exampleTwo exampleThree (by norm_num)
    exampleSmoothTwelve _

/-- **Non-surjectivity at `12`**, whose hypotheses do not include `[IsAlgClosed F]` — certified here
on the same curve only because that is where the non-constancy hypothesis is already built. -/
example : ¬ Function.Surjective (mulByNEndo (W := y2AddYEqX3 AlgClosedQ) 12
    (transcendental_xCoord_nsmul_of_smooth exampleTwo exampleThree (by norm_num)
      exampleSmoothTwelve)) :=
  not_surjective_mulByNEndo_of_smooth exampleTwo exampleThree (by norm_num) (by norm_num)
    exampleSmoothTwelve _

end Nonvacuity

end CoordinateRing

end WeierstrassCurve.Affine
