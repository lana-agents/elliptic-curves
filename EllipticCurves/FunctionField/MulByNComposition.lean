/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import EllipticCurves.Fixtures
import EllipticCurves.FunctionField.MulByNDegreeTower
import EllipticCurves.FunctionField.TranslationMulByNCommGeneral
import EllipticCurves.Torsion.ThreePrimary

/-!
# `[mn]∗ = [m]∗ ∘ [n]∗`, and the degree `n²` at every `3`-smooth `n`

Let `W` be an elliptic curve over a field `F`.  `EllipticCurves.FunctionField.MulByNPullback` builds
`[n]∗ : F(W) → F(W)` for every `n` at which `[n]` is non-constant, out of the group law on
`(W ⁄ F(W)).Point` alone.  This file proves that the construction is **multiplicative in the
index**,

```
[m · n]∗  =  [m]∗ ∘ [n]∗,
```

and reads off the consequence the index-specific files could not reach:

```
[F(W) : [n]∗F(W)] = n²        for every 3-smooth n.
```

## ⚠️ What this refutes, and what it leaves standing

`EllipticCurves.FunctionField.MulByNPlacePullback` records `[F(W) : [n]∗F(W)] = n²` as a rung that
*does not survive* at general `n`, and lists three gates for it: the coordinates of `[n]` as a
written-down fraction `Φₙ/ΨSqₙ` (`#251`), the coprimality `IsCoprime (Φₙ) (ΨSqₙ)` (`#1184`),
and `natDegree_ΨSq`'s `(n : F) ≠ 0`.  **All three are gates on the `Φₙ/ΨSqₙ` route, not on the
degree.**  Degrees multiply in towers, so the two merged values

⚠️ **The `#404` half of that pair has been paid, and only the `#251` half remains.**  PR #557 proved
the on-curve identity for `(Φₙ/ΨSqₙ, ωₙ/ψₙ³)` at every index over every commutative ring
(`WeierstrassCurve.Affine.equation_div_of_ψ_ne_zero`, `EllipticCurves.Torsion.OmegaCrux`).  It says
those coordinates lie on the curve; it does **not** identify them with the group-law multiple
`n • P`, which is what a written-down `Φₙ/ΨSqₙ` for `[n]` needs and is `#251`
(`WeierstrassCurve.Affine.HasXCoordFormula`, `EllipticCurves.Torsion.NsmulSurjective`, available at
`n = 2, 3` only).  ⚠️ The gate is relettered, not lifted, and `#1184` is untouched; the two-reading
account is `EllipticCurves.FunctionField.MulByNPullback`.

```
[F(W) : [2]∗F(W)] = 4       (`finrank_mulByTwoFieldRange`,   #682)
[F(W) : [3]∗F(W)] = 9       (`finrank_mulByThreeFieldRange`, #775)
```

together with the composition law give the value at every index built from `2` and `3`, with none of
the three gates and with no division polynomial anywhere in the argument.

⚠️ **What is not refuted is that the gates gate the *general* `n`.**  Nothing below says anything at
`n = 5`: the composition law manufactures no new *prime*, and `finrank_mulByNFieldRange_of_smooth`
is exactly as wide as the set of indices whose prime factors are `2` and `3`.  What moves is the
boundary — the three gates now stand between `3`-smooth and general `n`, not between `{2, 3}` and
general `n`.  This is `#1165`'s finding one rung over: *a dead end inside a route is not a dead end
for the deliverable*, and the way to tell them apart is to re-read what the consumer requires.

## Where the composition law comes from

`EllipticCurves.FunctionField.TranslationDoublingCommGeneral` packages the action of an `F`-algebra
endomorphism `φ` of `F(W)` on `(W ⁄ F(W)).Point` as an **`AddMonoidHom`** `genPointHom φ`, proves it
functorial (`genPointHom_comp`) and proves that two endomorphisms agreeing on the generic point `𝒫`
are equal (`algHom_ext_of_genPointHom`).  `TranslationMulByNCommGeneral` adds
`genPointHom_genericPoint_mulByN : genPointHom [n]∗ 𝒫 = n • 𝒫`.  Against those, the composition law
is the group calculation

```
genPointHom ([m]∗ ∘ [n]∗) 𝒫 = genPointHom [n]∗ (genPointHom [m]∗ 𝒫)
                            = genPointHom [n]∗ (m • 𝒫)
                            = n • (m • 𝒫) = (m · n) • 𝒫 = genPointHom [m·n]∗ 𝒫,
```

whose only non-formal step is `AddMonoidHom.map_nsmul` — that is, the additivity of `genPointHom`,
which is the whole content of the file that built it.  ⚠️ Note the contravariance: `genPointHom` of
a *composite* is the composite of `genPointHom`s in the **opposite** order, as
`genPointHom_comp`'s own docstring warns.

## Hypotheses, and the one that has to be composed first

`[n]∗` is only defined at indices where `[n]` is non-constant, as
`Transcendental F ((n • 𝒫).xCoord)`.  That hypothesis is *needed to state* the composition law at
`m · n`, so `transcendental_xCoord_mul_nsmul` comes first: `(m·n) • 𝒫` is the image of `n • 𝒫` under
`genPointHom [m]∗`, so its `x`-coordinate is `[m]∗ ((n • 𝒫).xCoord)`, and an injective `F`-algebra
map carries transcendental elements to transcendental elements.

Because `Transcendental F _` is a `Prop`, the value of `mulByNEndoAlgHom n h` does not depend on
which proof `h` is supplied, so every statement below takes the hypothesis as an ordinary argument
rather than fixing a canonical one.

## Main statements

⚠️ Every public declaration of this file is listed.

* `WeierstrassCurve.Affine.CoordinateRing.fieldRange_comp` and `…finrank_fieldRange_comp` — for
  arbitrary `F`-algebra endomorphisms `φ`, `ψ` of `F(W)`, the range of a composite is the image of
  one range under the other, and `[F(W) : (φ ∘ ψ)F(W)] = [F(W) : ψF(W)] · [F(W) : φF(W)]`.  Neither
  carries `[W.IsElliptic]`, neither needs a finiteness hypothesis, and neither mentions `[n]`;
* `…nsmul_mul_genericPoint_eq` and `…xCoord_mul_nsmul_genericPoint` — `(m·n) • 𝒫` as the image of
  `n • 𝒫` under `[m]∗`, and the resulting `x`-coordinate;
* `…transcendental_xCoord_mul_nsmul` — the non-constancy hypothesis composes;
* `…mulByNEndoAlgHom_mul` and `…mulByNEndo_mul` — **the composition law**, as `F`-algebra and as
  ring homomorphisms;
* `…finrank_mulByNFieldRange_mul` — the degree is multiplicative in the index, and
  `…transcendental_xCoord_nsmul_of_mul_eq` / `…finrank_mulByNFieldRange_of_mul_eq` are the two
  `m * n = k` forms, which is what every consumer below uses: the index arithmetic is done once, by
  `subst`, instead of by transporting a hypothesis at each call site;
* `…finrank_mulByNFieldRange_one` — `[F(W) : [1]∗F(W)] = 1`, the base of both inductions;
* `…transcendental_xCoord_two_pow_mul_three_pow_nsmul` and
  `…finrank_mulByNFieldRange_two_pow_mul_three_pow` — `[2^a · 3^b]` is non-constant, and its degree
  is `(2^a · 3^b)^2`;
* `…transcendental_xCoord_nsmul_of_smooth` and `…finrank_mulByNFieldRange_of_smooth` — the same
  under the hypothesis `∀ p ∈ n.primeFactors, p = 2 ∨ p = 3`, which is the shape
  `card_torsion_eq_sq_of_smooth` (`EllipticCurves.Torsion.ThreePrimary`) states `#E[n] = n²` in;
* `…finrank_mulByNFieldRange_four` and `…finrank_mulByNFieldRange_six` — `16` and `36`, the first
  degrees this tree knows at an index outside `{2, 3}`.

## What is *not* here

* **No degree at `n = 5`, and no general `n`.**  See the second section above.
* **Nothing at infinity — *here*.**  `comapProjPointN … none = none` (*"`[n]` fixes the point at
  infinity"*) is not proved below: it needs the corresponding composition law for
  `comapProjPoint`, which is a statement about places and a different argument.  ⚠️ **That argument
  has since been made**, in `EllipticCurves.FunctionField.MulByNPlaceComposition` (`#1214`), which
  consumes this file's `mulByNEndo_mul` and gets `none ↦ none` — and `e_∞ = 1`, and
  `ordInfty ([n]∗ genX) = -2` — at every `3`-smooth `n`.  This bullet is about the contents of this
  file and not about the tree.
* **No `ωₙ`, no coprimality, no elliptic net.**  `#404` (closed), `#1184` (open) and Ward
  (`#260`, closed) are untouched and
  unused; the whole file runs on the group law and four Mathlib `relfinrank` lemmas.

## References

* [J. Silverman, *The arithmetic of elliptic curves*][silverman2009], III.4, III.8.
-/

open Module Polynomial IntermediateField

namespace WeierstrassCurve.Affine

namespace CoordinateRing

variable {F : Type*} [Field F] {W : Affine F}

/-! ### The tower step: the degree of a composite -/

/-- **The range of a composite is the image of one range under the other.** -/
theorem fieldRange_comp (φ ψ : W.FunctionField →ₐ[F] W.FunctionField) :
    (φ.comp ψ).fieldRange = ψ.fieldRange.map φ := by
  rw [AlgHom.fieldRange_eq_map, AlgHom.fieldRange_eq_map, IntermediateField.map_map]

/-- **`[F(W) : (φ ∘ ψ)F(W)] = [F(W) : ψF(W)] · [F(W) : φF(W)]`** for `F`-algebra endomorphisms
`φ`, `ψ` of `F(W)`.

The tower is `F(W) ⊇ φF(W) ⊇ φψF(W)`.  Its upper storey is `finrank φ.fieldRange`; its lower storey
is `relfinrank (ψ.fieldRange.map φ) (⊤.map φ)`, which `IntermediateField.relfinrank_map_map`
transports back down to `relfinrank ψ.fieldRange ⊤ = finrank ψ.fieldRange` — the point being that
`φ` is injective, so it is an isomorphism of `F(W)` onto its range and carries the pair
`(ψF(W), F(W))` to the pair `(φψF(W), φF(W))`.

⚠️ Nothing about `φ` or `ψ` is used beyond their being `F`-algebra homomorphisms of a field, no
`[W.IsElliptic]` appears, and **no finiteness hypothesis is needed**:
`IntermediateField.relfinrank_mul_finrank_top` is unconditional, both sides being `0` when the
degrees are infinite. -/
theorem finrank_fieldRange_comp (φ ψ : W.FunctionField →ₐ[F] W.FunctionField) :
    finrank ↥(φ.comp ψ).fieldRange W.FunctionField
      = finrank ↥ψ.fieldRange W.FunctionField * finrank ↥φ.fieldRange W.FunctionField := by
  have hB : φ.fieldRange = (⊤ : IntermediateField F W.FunctionField).map φ :=
    AlgHom.fieldRange_eq_map φ
  have hle : (φ.comp ψ).fieldRange ≤ φ.fieldRange := by
    rw [fieldRange_comp, hB]
    exact IntermediateField.map_mono φ le_top
  have hrel : relfinrank (φ.comp ψ).fieldRange φ.fieldRange
      = finrank ↥ψ.fieldRange W.FunctionField := by
    rw [fieldRange_comp, hB, IntermediateField.relfinrank_map_map,
      IntermediateField.relfinrank_top_right]
  have htower := IntermediateField.relfinrank_mul_finrank_top hle
  rw [hrel] at htower
  exact htower.symm

variable [W.IsElliptic]

/-! ### The composition law -/

/-- **`(m · n) • 𝒫` is the image of `n • 𝒫` under `[m]∗`.**  This is `n • (m • 𝒫) = (m · n) • 𝒫`
read through the additive `genPointHom`. -/
theorem nsmul_mul_genericPoint_eq {m : ℕ}
    (hm : Transcendental F (m • genericPoint (W := W)).xCoord) (n : ℕ) :
    (m * n) • genericPoint (W := W)
      = genPointHom (mulByNEndoAlgHom m hm) (n • genericPoint (W := W)) := by
  rw [map_nsmul, genPointHom_genericPoint_mulByN, smul_smul, mul_comm]

/-- **`x((m · n) • 𝒫) = [m]∗ (x(n • 𝒫))`.**  The `x`-coordinate form of
`nsmul_mul_genericPoint_eq`; the hypothesis at `n` is used only to know that `n • 𝒫` is affine, so
that `genPointHom` acts on it coordinatewise. -/
theorem xCoord_mul_nsmul_genericPoint {m n : ℕ}
    (hm : Transcendental F (m • genericPoint (W := W)).xCoord)
    (hn : Transcendental F (n • genericPoint (W := W)).xCoord) :
    ((m * n) • genericPoint (W := W)).xCoord
      = mulByNEndoAlgHom m hm ((n • genericPoint (W := W)).xCoord) := by
  rw [nsmul_mul_genericPoint_eq hm n]
  conv_lhs => rw [Point.eq_some_of_ne_zero (ne_zero_of_transcendental_xCoord hn)]
  rw [genPointHom_some]
  rfl

/-- **Non-constancy composes**: if `[m]` and `[n]` are non-constant then so is `[m · n]`.

`x((m·n) • 𝒫)` is `[m]∗` of `x(n • 𝒫)` by `xCoord_mul_nsmul_genericPoint`, and an injective
`F`-algebra map carries a transcendental element to a transcendental one — if `p` kills the image
then `[m]∗` kills `aeval _ p`, so `aeval _ p = 0`. -/
theorem transcendental_xCoord_mul_nsmul {m n : ℕ}
    (hm : Transcendental F (m • genericPoint (W := W)).xCoord)
    (hn : Transcendental F (n • genericPoint (W := W)).xCoord) :
    Transcendental F ((m * n) • genericPoint (W := W)).xCoord := by
  rw [xCoord_mul_nsmul_genericPoint hm hn]
  rintro ⟨p, hp0, hp⟩
  rw [Polynomial.aeval_algHom_apply] at hp
  exact hn ⟨p, hp0, (mulByNEndoAlgHom m hm).toRingHom.injective (by rw [map_zero]; exact hp)⟩

/-- **The composition law `[m · n]∗ = [m]∗ ∘ [n]∗`**, as `F`-algebra endomorphisms of `F(W)`.

Both sides act on `𝒫` as `(m · n) • 𝒫`, and `algHom_ext_of_genPointHom` says that is enough.  ⚠️ The
right-hand side is a composite of *pullbacks*, so as a map of points it is `Q ↦ n • (m • Q)`; the
`mul_comm` at the end of the proof is where that is reconciled with `m · n`.

The hypothesis `hmn` is an arbitrary proof of non-constancy at `m · n` rather than
`transcendental_xCoord_mul_nsmul hm hn`: the two are equal by proof irrelevance, and taking it as an
argument is what lets a consumer rewrite with this at whichever proof it already holds. -/
theorem mulByNEndoAlgHom_mul {m n : ℕ}
    (hm : Transcendental F (m • genericPoint (W := W)).xCoord)
    (hn : Transcendental F (n • genericPoint (W := W)).xCoord)
    (hmn : Transcendental F ((m * n) • genericPoint (W := W)).xCoord) :
    mulByNEndoAlgHom (m * n) hmn = (mulByNEndoAlgHom m hm).comp (mulByNEndoAlgHom n hn) := by
  refine algHom_ext_of_genPointHom ?_
  rw [← genPointHom_comp, genPointHom_genericPoint_mulByN, genPointHom_genericPoint_mulByN,
    map_nsmul, genPointHom_genericPoint_mulByN, smul_smul, mul_comm]

/-- **The composition law as ring homomorphisms.** -/
theorem mulByNEndo_mul {m n : ℕ}
    (hm : Transcendental F (m • genericPoint (W := W)).xCoord)
    (hn : Transcendental F (n • genericPoint (W := W)).xCoord)
    (hmn : Transcendental F ((m * n) • genericPoint (W := W)).xCoord) :
    mulByNEndo (m * n) hmn = (mulByNEndo m hm).comp (mulByNEndo n hn) :=
  RingHom.ext fun z =>
    congrArg (fun φ : W.FunctionField →ₐ[F] W.FunctionField => φ z)
      (mulByNEndoAlgHom_mul hm hn hmn)

/-! ### The degree, multiplied up -/

/-- **Non-constancy composes, at a stated product.**  The `m * n = k` form of
`transcendental_xCoord_mul_nsmul`, so that a caller holding `k` as a literal or as `2 ^ (a + 1)`
never has to transport the hypothesis along an arithmetic identity. -/
theorem transcendental_xCoord_nsmul_of_mul_eq {m n k : ℕ} (hk : m * n = k)
    (hm : Transcendental F (m • genericPoint (W := W)).xCoord)
    (hn : Transcendental F (n • genericPoint (W := W)).xCoord) :
    Transcendental F (k • genericPoint (W := W)).xCoord :=
  hk ▸ transcendental_xCoord_mul_nsmul hm hn

/-- **The degree of `[n]∗` is multiplicative in `n`**, at every pair of indices where both maps are
non-constant.  This is `finrank_fieldRange_comp` against the composition law, and it is where the
`n²` below comes from. -/
theorem finrank_mulByNFieldRange_mul {m n : ℕ}
    (hm : Transcendental F (m • genericPoint (W := W)).xCoord)
    (hn : Transcendental F (n • genericPoint (W := W)).xCoord)
    (hmn : Transcendental F ((m * n) • genericPoint (W := W)).xCoord) :
    finrank ↥(mulByNEndoAlgHom (m * n) hmn).fieldRange W.FunctionField
      = finrank ↥(mulByNEndoAlgHom m hm).fieldRange W.FunctionField
        * finrank ↥(mulByNEndoAlgHom n hn).fieldRange W.FunctionField := by
  rw [mulByNEndoAlgHom_mul hm hn, finrank_fieldRange_comp, mul_comm]

/-- **The multiplicativity at a stated product.**  The `m * n = k` form of
`finrank_mulByNFieldRange_mul`, and the form every consumer below uses: `subst` does the index
arithmetic once, here, instead of at each call site. -/
theorem finrank_mulByNFieldRange_of_mul_eq {m n k : ℕ} (hk : m * n = k)
    (hm : Transcendental F (m • genericPoint (W := W)).xCoord)
    (hn : Transcendental F (n • genericPoint (W := W)).xCoord)
    (h : Transcendental F (k • genericPoint (W := W)).xCoord) :
    finrank ↥(mulByNEndoAlgHom k h).fieldRange W.FunctionField
      = finrank ↥(mulByNEndoAlgHom m hm).fieldRange W.FunctionField
        * finrank ↥(mulByNEndoAlgHom n hn).fieldRange W.FunctionField := by
  subst hk
  exact finrank_mulByNFieldRange_mul hm hn h

/-- **`[F(W) : [1]∗F(W)] = 1`**, the base of every induction below: `[1]∗` is the identity
(`mulByNEndo_one`), whose range is `⊤`. -/
theorem finrank_mulByNFieldRange_one
    (h : Transcendental F ((1 : ℕ) • genericPoint (W := W)).xCoord) :
    finrank ↥(mulByNEndoAlgHom 1 h).fieldRange W.FunctionField = 1 := by
  have hid : mulByNEndoAlgHom (W := W) 1 h = AlgHom.id F W.FunctionField :=
    AlgHom.coe_ringHom_injective (mulByNEndo_one (W := W))
  rw [hid, AlgHom.fieldRange_eq_map, IntermediateField.map_id]
  exact IntermediateField.finrank_top

/-- **`[2^a · 3^b]` is non-constant**, for every `a` and `b`, given `(2 : F) ≠ 0` and
`(3 : F) ≠ 0`.

Induction on `a` and then on `b`, from `transcendental_xCoord_one_nsmul` at the base and
`transcendental_xCoord_nsmul_of_mul_eq` at each step.  ⚠️ The two prime steps are the *only* place a
hypothesis on `F` enters this file, and they are the merged `n = 2` and `n = 3` non-constancy
statements, not new work. -/
theorem transcendental_xCoord_two_pow_mul_three_pow_nsmul (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0)
    (a b : ℕ) :
    Transcendental F ((2 ^ a * 3 ^ b) • genericPoint (W := W)).xCoord := by
  induction a with
  | zero =>
    induction b with
    | zero => exact transcendental_xCoord_one_nsmul (W := W)
    | succ b ih =>
      exact transcendental_xCoord_nsmul_of_mul_eq (by ring)
        (transcendental_xCoord_three_nsmul h2 h3) ih
  | succ a ih =>
    exact transcendental_xCoord_nsmul_of_mul_eq (by ring)
      (transcendental_xCoord_two_nsmul h2) ih

/-- **`[F(W) : [2^a · 3^b]∗F(W)] = (2^a · 3^b)^2`.**

The induction of `transcendental_xCoord_two_pow_mul_three_pow_nsmul`, with
`finrank_mulByNFieldRange_of_mul_eq` at each step and the two merged degrees `4` and `9` as the
prime inputs — `finrank_mulByTwoFieldRange` (`#682`) and `finrank_mulByThreeFieldRange` (`#775`),
reached through `mulByNEndoAlgHom_two` and `mulByNEndoAlgHom_three`.  At the base `[1]∗` is the
identity, whose range is `⊤`.

⚠️ **No coordinate formula, no coprimality, and no `(n : F) ≠ 0` at the composite index.**  The only
hypotheses are `(2 : F) ≠ 0` and `(3 : F) ≠ 0`, which the two prime inputs carry; in particular the
degree at `2 ^ a` alone is available in every odd characteristic, including characteristic `3`. -/
theorem finrank_mulByNFieldRange_two_pow_mul_three_pow (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0)
    (a b : ℕ) (h : Transcendental F ((2 ^ a * 3 ^ b) • genericPoint (W := W)).xCoord) :
    finrank ↥(mulByNEndoAlgHom (2 ^ a * 3 ^ b) h).fieldRange W.FunctionField
      = (2 ^ a * 3 ^ b) ^ 2 := by
  induction a with
  | zero =>
    induction b with
    | zero => exact finrank_mulByNFieldRange_one h
    | succ b ih =>
      have hb := transcendental_xCoord_two_pow_mul_three_pow_nsmul (W := W) h2 h3 0 b
      rw [finrank_mulByNFieldRange_of_mul_eq (m := 3) (n := 2 ^ 0 * 3 ^ b) (by ring)
        (transcendental_xCoord_three_nsmul h2 h3) hb h,
        mulByNEndoAlgHom_three h2 h3, finrank_mulByThreeFieldRange h2 h3, ih hb]
      ring
  | succ a ih =>
    have ha := transcendental_xCoord_two_pow_mul_three_pow_nsmul (W := W) h2 h3 a b
    rw [finrank_mulByNFieldRange_of_mul_eq (m := 2) (n := 2 ^ a * 3 ^ b) (by ring)
      (transcendental_xCoord_two_nsmul h2) ha h,
      mulByNEndoAlgHom_two h2, finrank_mulByTwoFieldRange h2, ih ha]
    ring

/-- **`[n]` is non-constant at every `3`-smooth `n ≠ 0`.** -/
theorem transcendental_xCoord_nsmul_of_smooth (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) {n : ℕ}
    (hn : n ≠ 0) (hfac : ∀ p ∈ n.primeFactors, p = 2 ∨ p = 3) :
    Transcendental F (n • genericPoint (W := W)).xCoord := by
  obtain ⟨a, b, rfl⟩ := Nat.exists_eq_two_pow_mul_three_pow n hn hfac
  exact transcendental_xCoord_two_pow_mul_three_pow_nsmul h2 h3 a b

/-- **`[F(W) : [n]∗F(W)] = n²` for every `3`-smooth `n ≠ 0`.**

The hypotheses are those of `card_torsion_eq_sq_of_smooth` (`EllipticCurves.Torsion.ThreePrimary`),
which is the same slice of indices on the other side of the pairing: `#E[n] = n²` there,
`[F(W) : [n]∗F(W)] = n²` here.

⚠️ The first index this does **not** cover is `n = 5`, exactly as for the torsion structure theorem,
and for the same reason: the argument manufactures no new prime.  What stands between this and
general `n` is `#251`, `#1184` and `(n : F) ≠ 0` — see the module docstring. -/
theorem finrank_mulByNFieldRange_of_smooth (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) {n : ℕ}
    (hn : n ≠ 0) (hfac : ∀ p ∈ n.primeFactors, p = 2 ∨ p = 3)
    (h : Transcendental F (n • genericPoint (W := W)).xCoord) :
    finrank ↥(mulByNEndoAlgHom n h).fieldRange W.FunctionField = n ^ 2 := by
  obtain ⟨a, b, rfl⟩ := Nat.exists_eq_two_pow_mul_three_pow n hn hfac
  exact finrank_mulByNFieldRange_two_pow_mul_three_pow h2 h3 a b h

/-! ### The first two degrees outside `{2, 3}` -/

/-- **`[F(W) : [4]∗F(W)] = 16`.**  The first degree this tree knows at an index other than `2` and
`3`, and it needs only `(2 : F) ≠ 0`: `[4]∗ = [2]∗ ∘ [2]∗`. -/
theorem finrank_mulByNFieldRange_four (h2 : (2 : F) ≠ 0)
    (h : Transcendental F ((4 : ℕ) • genericPoint (W := W)).xCoord) :
    finrank ↥(mulByNEndoAlgHom 4 h).fieldRange W.FunctionField = 16 := by
  rw [finrank_mulByNFieldRange_of_mul_eq (m := 2) (n := 2) (by norm_num)
    (transcendental_xCoord_two_nsmul h2) (transcendental_xCoord_two_nsmul h2) h,
    mulByNEndoAlgHom_two h2, finrank_mulByTwoFieldRange h2]

/-- **`[F(W) : [6]∗F(W)] = 36`.**  `[6]∗ = [2]∗ ∘ [3]∗`, so `36 = 4 · 9`. -/
theorem finrank_mulByNFieldRange_six (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0)
    (h : Transcendental F ((6 : ℕ) • genericPoint (W := W)).xCoord) :
    finrank ↥(mulByNEndoAlgHom 6 h).fieldRange W.FunctionField = 36 := by
  rw [finrank_mulByNFieldRange_of_mul_eq (m := 2) (n := 3) (by norm_num)
    (transcendental_xCoord_two_nsmul h2) (transcendental_xCoord_three_nsmul h2 h3) h,
    mulByNEndoAlgHom_two h2, finrank_mulByTwoFieldRange h2, mulByNEndoAlgHom_three h2 h3,
    finrank_mulByThreeFieldRange h2 h3]

/-! ### Non-vacuity

`y² = x³ - x` over `ℚ`, of discriminant `64` — the curve `#682`, `#675` and `#1200` instantiate on.
Every hypothesis of the section above is discharged on it: it is elliptic, `(2 : ℚ) ≠ 0` and
`(3 : ℚ) ≠ 0`, and the non-constancy of `[4]` and `[12]` is *produced* by
`transcendental_xCoord_nsmul_of_smooth` rather than assumed — which is the point, since a degree
statement whose non-constancy hypothesis could not be met would be vacuous.

⚠️ Base `ℚ` is safe here even though `#1200` recorded that it is **not** safe for
`finrank_mulByNFieldRange_eq_finrank_adjoin`: that statement mentions `IntermediateField ℚ
(RatFunc ℚ)`, where `#synth Algebra ℚ (RatFunc ℚ)` answers `DivisionRing.toRatAlgebra` and the
instances diamond.  Nothing in this file mentions `RatFunc`. -/

section Nonvacuity

/-! The certificate curve `y² = x³ − x` is the shared `EllipticCurves.Fixture.y2EqX3SubX`, whose
single `[CharZero F]` instance also supplies `IsElliptic` here. -/

open EllipticCurves.Fixture

private lemma exampleTwoNeZero : (2 : ℚ) ≠ 0 := by norm_num

private lemma exampleThreeNeZero : (3 : ℚ) ≠ 0 := by norm_num

/-- ⚠️ `decide` does **not** close this: `Nat.primeFactors` goes through
`Nat.primeFactorsList`, whose `Decidable` instance gets stuck on `Nat.minFac`'s well-founded
recursion.  Bounding `p` by `12` and case-splitting is what works. -/
private lemma exampleSmoothTwelve : ∀ p ∈ Nat.primeFactors 12, p = 2 ∨ p = 3 := by
  intro p hp
  obtain ⟨hp1, hp2, -⟩ := Nat.mem_primeFactors.mp hp
  have hle : p ≤ 12 := Nat.le_of_dvd (by norm_num) hp2
  interval_cases p <;> revert hp1 hp2 <;> decide

/-- **`[F(W) : [4]∗F(W)] = 16` on a concrete curve**, with the non-constancy of `[4]` produced from
the merged non-constancy of `[2]` rather than assumed. -/
example :
    finrank ↥(mulByNEndoAlgHom 4 (transcendental_xCoord_nsmul_of_mul_eq
        (W := y2EqX3SubX ℚ) (show 2 * 2 = 4 by norm_num)
        (transcendental_xCoord_two_nsmul exampleTwoNeZero)
        (transcendental_xCoord_two_nsmul exampleTwoNeZero))).fieldRange
      (y2EqX3SubX ℚ).FunctionField = 16 :=
  finrank_mulByNFieldRange_four exampleTwoNeZero _

/-- **`[F(W) : [12]∗F(W)] = 144` on a concrete curve** — an index at which neither the two merged
degrees nor `finrank_mulByNFieldRange_four` says anything, so the `3`-smooth statement is what is
being certified. -/
example :
    finrank ↥(mulByNEndoAlgHom 12 (transcendental_xCoord_nsmul_of_smooth
        (W := y2EqX3SubX ℚ) exampleTwoNeZero exampleThreeNeZero (by norm_num)
        exampleSmoothTwelve)).fieldRange (y2EqX3SubX ℚ).FunctionField = 144 := by
  have h := finrank_mulByNFieldRange_of_smooth (W := y2EqX3SubX ℚ) (n := 12)
    exampleTwoNeZero exampleThreeNeZero (by norm_num) exampleSmoothTwelve
    (transcendental_xCoord_nsmul_of_smooth exampleTwoNeZero exampleThreeNeZero (by norm_num)
      exampleSmoothTwelve)
  rw [h]
  norm_num

end Nonvacuity

end CoordinateRing

end WeierstrassCurve.Affine
