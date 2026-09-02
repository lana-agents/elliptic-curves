/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import EllipticCurves.Fixtures
import EllipticCurves.FunctionField.MulByNXCoordRatFunc

/-!
# The degree tower at general `n`: `[F(W) : σF(W)]` is the degree of one rational function

Let `W` be a Weierstrass curve over a field `F`, with function field `F(W)` and rational function
subfield `F(x) = ratFuncRange W ⊆ F(W)`.  `EllipticCurves.FunctionField.MulByTwoDegree`'s
`finrank_fieldRange_eq_finrank_adjoin` says that for **any** `F`-algebra endomorphism `σ` of `F(W)`
whose value at the generic `x`-coordinate lies in `F(x)`,

```
[F(W) : σF(W)]  =  [F(x) : F(r)],        where  algebraMap (RatFunc F) F(W) r = σ (genX W).
```

This file instantiates that at `σ = [n]∗` for every `n : ℕ`:

```
[F(W) : [n]∗F(W)]  =  [F(x) : F(nMulRatFunc W n)].
```

⚠️ **The second statement carries no coprimality, no `(n : F) ≠ 0`, no written-down fraction, no
`[IsAlgClosed F]` and no hypothesis on `n`** beyond the transcendence of `x(n • 𝒫)` that
`mulByNEndo` needs in order to exist at all.

## What this changes, and what it does not

The degree of `[n]` **is** the degree of the rational function `nMulRatFunc W n`.  Everything this
tree records as gating `[F(W) : [n]∗F(W)] = n²` at general `n` gates only the *evaluation of that
one number*; none of it gates the tower.

⚠️ **It does not prove `[F(W) : [n]∗F(W)] = n²` at any `n` beyond `2` and `3`, and must not be read
as doing so.**  `finrank F⟮nMulRatFunc W n⟯ (RatFunc F)` is a number this development cannot
evaluate at general `n`, because `nMulRatFunc` is produced by an inverse isomorphism and so has no
numerator and no denominator to read off — `EllipticCurves.FunctionField.MulByNXCoordRatFunc`'s
*"being an element of `F(x)` is not being a written-down rational function"*.  The three gates named
there and in `EllipticCurves.FunctionField.MulByNPlacePullback` are unchanged:

1. `nMulRatFunc W n = Φₙ/ΨSqₙ` as a written-down fraction (`#251`);
2. `IsCoprime (W.Φ n) (W.ΨSq n)` at general `n` (`#1184`);
3. `natDegree_ΨSq`'s `(n : F) ≠ 0`.

⚠️ **The `#404` half of that pair has been paid, and only the `#251` half remains.**  PR #557 proved
the on-curve identity for `(Φₙ/ΨSqₙ, ωₙ/ψₙ³)` at every index over every commutative ring
(`WeierstrassCurve.Affine.equation_div_of_ψ_ne_zero`, `EllipticCurves.Torsion.OmegaCrux`).  It says
those coordinates lie on the curve; it does **not** identify them with the group-law multiple
`n • P`, which is what a written-down `Φₙ/ΨSqₙ` for `[n]` needs and is `#251`
(`WeierstrassCurve.Affine.HasXCoordFormula`, `EllipticCurves.Torsion.NsmulSurjective`, available at
`n = 2, 3` only).  ⚠️ The gate is relettered, not lifted, and `#1184` is untouched; the two-reading
account is `EllipticCurves.FunctionField.MulByNPullback`.

`finrank_fieldRange_eq_of_eq_ΦDivΨSq` below is the conditional statement those three gates
discharge, so a future `n` at which they are available needs nothing further from this side.

⚠️ **A reader must not conclude that `n²` is unavailable outside `{2, 3}`.**  It is available at
every `3`-smooth `n`, by a route that goes nowhere near this file:
`EllipticCurves.FunctionField.MulByNComposition` (`#1213`) proves `[m · n]∗ = [m]∗ ∘ [n]∗` from the
group law and multiplies the two merged degrees up in the tower.  That route evaluates no
`finrank F⟮nMulRatFunc W n⟯ (RatFunc F)` and meets none of the three gates; at every `3`-smooth `n`
its conclusion is strictly stronger than `finrank_mulByNFieldRange_of_nMulRatFunc_eq`'s, which
carries three hypotheses.  What the three gates now stand between is `3`-smooth and *general* `n`.

## Where the tower lives, and why not here

`finrank_fieldRange_eq_finrank_adjoin` is **not** in this file.  It needs only `ratFuncRange`,
`ratFuncRange_eq_adjoin`, `finrank_ratFuncRange` and four Mathlib `relfinrank` lemmas, all of which
are in `EllipticCurves.FunctionField.MulByTwoDegree`, so it lives there — immediately after
`finrank_ratFuncRange` and above the two instances that consume it.  Putting it here instead would
have made it inaccessible to `finrank_mulByTwoFieldRange` and `finrank_mulByThreeFieldRange`, which
this file imports rather than the other way round.

⚠️ The argument used to be written out **three** times: once at `finrank_mulByTwoFieldRange`, once
at `finrank_mulByThreeFieldRange`, and once here.  It is now written once, and both merged theorems
are two-line consequences of it — which is a stronger statement than any `example` in this file
could make, because it is the merged proof terms themselves that go through the general lemma.

## Hypotheses, and the ones that turned out not to be needed

`finrank_fieldRange_eq_finrank_adjoin` needs **no `[W.IsElliptic]`**: its only input about `F(W)` is
`finrank_ratFuncRange`, which carries none.  Everything in *this* file does carry it, and for two
unrelated reasons — `nMulRatFunc`, whose construction runs through the hyperelliptic involution's
fixed field, and the coprimality corollary, where `[W.IsElliptic]` is what makes `Δ` a unit.

## Main definitions and statements

⚠️ Every public declaration of this file is listed.  One of them is a `def`, which is why the
heading is not `## Main results`.

* **`WeierstrassCurve.Affine.CoordinateRing.finrank_mulByNFieldRange_eq_finrank_adjoin`** — the
  instance of `MulByTwoDegree`'s `finrank_fieldRange_eq_finrank_adjoin` at `[n]∗`, for every
  `n : ℕ`;
* `WeierstrassCurve.Affine.CoordinateRing.ΦDivΨSq` — the fraction `Φₙ/ΨSqₙ` in `RatFunc F` at
  general `n`, the common generalisation of the merged `doublingRatFunc` and `triplingRatFunc`,
  with `doublingRatFunc_eq_ΦDivΨSq` and `triplingRatFunc_eq_ΦDivΨSq` identifying it at `n = 2, 3`;
* `WeierstrassCurve.Affine.CoordinateRing.finrank_adjoin_ΦDivΨSq` — `[F(x) : F(Φₙ/ΨSqₙ)] = n²`,
  under `(n : F) ≠ 0` and coprimality;
* **`WeierstrassCurve.Affine.CoordinateRing.finrank_fieldRange_eq_of_eq_ΦDivΨSq`** and
  **`WeierstrassCurve.Affine.CoordinateRing.finrank_mulByNFieldRange_of_nMulRatFunc_eq`** — the two
  combined forms: `[F(W) : σF(W)] = n²` once the fraction, the coprimality and `(n : F) ≠ 0` are
  supplied.  These are the statements the three gates discharge.

## What is *not* here

* **No new degree.**  Nothing below evaluates `finrank F⟮nMulRatFunc W n⟯ (RatFunc F)` at any `n`;
  the `example`s do it at `n = 2` and `n = 3` only, and each of those goes through a merged
  identification (`nMulRatFunc_two`, `nMulRatFunc_three`).  ⚠️ New degrees *do* exist in the tree —
  `[F(W) : [n]∗F(W)] = n²` at every `3`-smooth `n`,
  `EllipticCurves.FunctionField.MulByNComposition` — but they are not proved here and not by this
  route; see *"What this changes, and what it does not"* above.
* **No re-derivation of `finrank_mulByTwoFieldRange` / `finrank_mulByThreeFieldRange`.**  This file
  used to carry two `example`s doing that; since those two theorems are now *proved* by
  `finrank_fieldRange_eq_finrank_adjoin`, an `example` re-deriving them would be circular
  decoration.  The `example`s that remain are about `[n]∗`, which neither merged theorem mentions.
* **Nothing about `[n]∗` on divisors or places.**  This is a field degree.  Rung 4 of `#639`
  (`ordInfty ([n]∗ genX) = -2`) is *false* at general `n` and nothing here touches it; see
  `EllipticCurves.FunctionField.MulByNPlacePullback`.
* **No separability, no Galois statement.**  `MulByTwoGalois` / `MulByThreeGalois` consume the two
  merged degrees; nothing here is on that chain.

## References

* [J. H. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], II.2, III.4.10.
-/

open Module Polynomial IntermediateField

namespace WeierstrassCurve.Affine
namespace CoordinateRing

variable {F : Type*} [Field F] {W : Affine F}

/-- **The degree of `[n]` is the degree of `nMulRatFunc W n`**, for every `n : ℕ`.

`algebraMap_nMulRatFunc` and `mulByNEndo_genX` name the *same* element `x(n • 𝒫)` of `F(W)`, which
is exactly the hypothesis `finrank_fieldRange_eq_finrank_adjoin` asks for.

⚠️ This is not a degree computation and gives no number: it says the number on the left is the
number on the right.  See this file's module docstring for the three gates that stand between the
right-hand side and `n²`. -/
theorem finrank_mulByNFieldRange_eq_finrank_adjoin [W.IsElliptic] (n : ℕ)
    (hn : Transcendental F (n • genericPoint (W := W)).xCoord) :
    finrank ↥(mulByNEndoAlgHom n hn).fieldRange W.FunctionField
      = finrank ↥(F⟮nMulRatFunc W n⟯ : IntermediateField F (RatFunc F)) (RatFunc F) :=
  finrank_fieldRange_eq_finrank_adjoin _ _ (by
    rw [algebraMap_nMulRatFunc, mulByNEndoAlgHom_apply, mulByNEndo_genX])

/-! ### The middle degree, when the fraction *is* written down -/

variable (W) in
/-- **`Φₙ/ΨSqₙ` as an element of `RatFunc F`**, at general `n : ℤ`.

This is the common generalisation of the merged `doublingRatFunc` and `triplingRatFunc`, which are
this definition at `n = 2` and `n = 3` (`doublingRatFunc_eq_ΦDivΨSq`, `triplingRatFunc_eq_ΦDivΨSq`).
⚠️ Writing the fraction down is not the same as knowing it presents `x ∘ [n]`: that identification
is `#251` and is *not* available at general `n`. -/
noncomputable def ΦDivΨSq (n : ℤ) : RatFunc F :=
  algebraMap F[X] (RatFunc F) (W.Φ n) / algebraMap F[X] (RatFunc F) (W.ΨSq n)

/-- `doublingRatFunc W = ΦDivΨSq W 2`, the two differing only in that `ΨSq 2` is spelt `Ψ₂Sq`
(`WeierstrassCurve.ΨSq_two`). -/
theorem doublingRatFunc_eq_ΦDivΨSq : doublingRatFunc W = ΦDivΨSq W 2 := by
  rw [doublingRatFunc, ΦDivΨSq, WeierstrassCurve.ΨSq_two]

/-- `triplingRatFunc W = ΦDivΨSq W 3`, which is definitional. -/
theorem triplingRatFunc_eq_ΦDivΨSq : triplingRatFunc W = ΦDivΨSq W 3 := rfl

/-- **`[F(x) : F(Φₙ/ΨSqₙ)] = n²`.**  Mathlib's `RatFunc.finrank_eq_max_natDegree` computes the
degree of `F(X)` over the subfield generated by a rational function as the maximum of the degrees of
its *reduced* numerator and denominator; `hcop` says the presentation `Φₙ/ΨSqₙ` is already reduced,
and the two degrees are Mathlib's `natDegree_Φ n = n²` and `natDegree_ΨSq hn = n² - 1`.

⚠️ `max (n² ) (n² - 1) = n²` needs **no** side condition: the subtraction is truncated, so the
identity survives at `n = 0` as `max 0 0 = 0`.  The hypothesis `hn` is `natDegree_ΨSq`'s, not the
maximum's.

This is `finrank_adjoin_doublingRatFunc` / `finrank_adjoin_triplingRatFunc` with the index erased;
both are recovered below.

⚠️ **This statement used to carry `[W.IsElliptic]` and it was dead** — the instance occurred in
neither the remainder of the type nor the proof term, measured on the elaborated environment at
`2e44940` (`#1272`).  Nothing in the proof knows what an elliptic curve is: it is
`RatFunc.finrank_eq_max_natDegree` together with `RatFunc.natDegree_num_div_of_isCoprime`,
`RatFunc.natDegree_denom_div_of_isCoprime` and Mathlib's `natDegree_Φ` / `natDegree_ΨSq`.  The
number `n²` on the right is a fact about the division polynomials of an arbitrary `Affine F`; what
the three gates in the module docstring stand between is *this* number and
`[F(W) : [n]∗F(W)]`, and dropping the instance does not move any of them. -/
theorem finrank_adjoin_ΦDivΨSq {n : ℤ} (hn : ((n : ℤ) : F) ≠ 0)
    (hcop : IsCoprime (W.Φ n) (W.ΨSq n)) :
    finrank ↥(F⟮ΦDivΨSq W n⟯ : IntermediateField F (RatFunc F)) (RatFunc F) = n.natAbs ^ 2 := by
  have hq : W.ΨSq n ≠ 0 := W.ΨSq_ne_zero hn
  rw [ΦDivΨSq, RatFunc.finrank_eq_max_natDegree,
    RatFunc.natDegree_num_div_of_isCoprime hq hcop,
    RatFunc.natDegree_denom_div_of_isCoprime hq hcop, W.natDegree_Φ n, W.natDegree_ΨSq hn]
  omega

/-! ### The two combined forms: what the three gates discharge -/

/-- **`[F(W) : σF(W)] = n²`** for an endomorphism `σ` presented at `genX` by the written-down
fraction `Φₙ/ΨSqₙ`.  This is the tower and the middle degree composed; it is stated separately
because it is the exact shape a general-`n` rung 3 will consume. -/
theorem finrank_fieldRange_eq_of_eq_ΦDivΨSq {n : ℤ} (hn : ((n : ℤ) : F) ≠ 0)
    (hcop : IsCoprime (W.Φ n) (W.ΨSq n)) (σ : W.FunctionField →ₐ[F] W.FunctionField)
    (hσ : algebraMap (RatFunc F) W.FunctionField (ΦDivΨSq W n) = σ (genX W)) :
    finrank ↥σ.fieldRange W.FunctionField = n.natAbs ^ 2 := by
  rw [finrank_fieldRange_eq_finrank_adjoin σ _ hσ, finrank_adjoin_ΦDivΨSq hn hcop]

/-- **`[F(W) : [n]∗F(W)] = n²`, conditional on the three gates.**  `hfrac` is gate 1 (`#251`),
`hcop` is gate 2 (`#1184`) and `hchar` is gate 3.

⚠️ This theorem is **not** a proof that the degree is `n²`: it is the statement that the three
gates are jointly sufficient, and no `n` outside `{2, 3}` currently satisfies `hfrac`. -/
theorem finrank_mulByNFieldRange_of_nMulRatFunc_eq [W.IsElliptic] (n : ℕ)
    (hn : Transcendental F (n • genericPoint (W := W)).xCoord) (hchar : ((n : ℤ) : F) ≠ 0)
    (hcop : IsCoprime (W.Φ (n : ℤ)) (W.ΨSq (n : ℤ)))
    (hfrac : nMulRatFunc W n = ΦDivΨSq W (n : ℤ)) :
    finrank ↥(mulByNEndoAlgHom n hn).fieldRange W.FunctionField = n ^ 2 := by
  rw [finrank_mulByNFieldRange_eq_finrank_adjoin n hn, hfrac, finrank_adjoin_ΦDivΨSq hchar hcop]
  simp

/-! ### ⚠️ Validation: the `[n]∗` form is not vacuous at the two indices where the answer is known

`finrank_mulByNFieldRange_eq_finrank_adjoin` is an equality of two numbers neither of which it
computes, so nothing above rules out its being useless.  The `example`s below discharge that at the
only two indices at which `nMulRatFunc` has been identified with a written-down fraction, through
the merged `nMulRatFunc_two` / `nMulRatFunc_three`, and the last one drives the fully gated form
with all three of its hypotheses supplied.

That the *tower* is not vacuous is no longer an `example`'s job: `finrank_mulByTwoFieldRange` and
`finrank_mulByThreeFieldRange` are proved by it outright.

⚠️ They are `example`s and not theorems on purpose: naming them would put a second name on a
statement that already has one. -/

/-- **The `[n]∗` form at `n = 2`**, through the merged `nMulRatFunc_two`. -/
example [W.IsElliptic] (h2 : (2 : F) ≠ 0) :
    finrank ↥(mulByNEndoAlgHom 2 (transcendental_xCoord_two_nsmul (W := W) h2)).fieldRange
      W.FunctionField = 4 := by
  rw [finrank_mulByNFieldRange_eq_finrank_adjoin, nMulRatFunc_two h2,
    finrank_adjoin_doublingRatFunc h2]

/-- **The `[n]∗` form at `n = 3`**, through the merged `nMulRatFunc_three`. -/
example [W.IsElliptic] (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) :
    finrank ↥(mulByNEndoAlgHom 3 (transcendental_xCoord_three_nsmul (W := W) h2 h3)).fieldRange
      W.FunctionField = 9 := by
  rw [finrank_mulByNFieldRange_eq_finrank_adjoin, nMulRatFunc_three h2 h3,
    finrank_adjoin_triplingRatFunc h3]

/-- **The fully gated form is not vacuous**: at `n = 2` all three of its hypotheses are available,
`hfrac` from `nMulRatFunc_two` and `doublingRatFunc_eq_ΦDivΨSq`, `hcop` from the merged
`isCoprime_Φ_two_Ψ₂Sq`. -/
example [W.IsElliptic] (h2 : (2 : F) ≠ 0) :
    finrank ↥(mulByNEndoAlgHom 2 (transcendental_xCoord_two_nsmul (W := W) h2)).fieldRange
      W.FunctionField = 2 ^ 2 :=
  finrank_mulByNFieldRange_of_nMulRatFunc_eq 2 _ (by exact_mod_cast h2)
    (by rw [show ((2 : ℕ) : ℤ) = 2 from rfl, WeierstrassCurve.ΨSq_two]
        exact W.isCoprime_Φ_two_Ψ₂Sq)
    (by rw [nMulRatFunc_two h2, doublingRatFunc_eq_ΦDivΨSq, show ((2 : ℕ) : ℤ) = 2 from rfl])

/-! ### Non-vacuity

`y² = x³ - x`, of discriminant `64`, over two bases — and the second one is **not** decoration.

⚠️ **The general-`n` statement cannot be certified over `ℚ`.**  Its right-hand side mentions
`IntermediateField ℚ (RatFunc ℚ)`, and `#synth Algebra ℚ (RatFunc ℚ)` answers
`DivisionRing.toRatAlgebra` — every division ring of characteristic zero is a `ℚ`-algebra — not the
`RatFunc` algebra instance the theorem above is stated with.  The two are **not** definitionally
equal, so the certificate fails to typecheck with the error that prints *"has type X but is expected
to have type X"* with both sides identical.  ⚠️ The diamond is specific to base `ℚ`; it is not a
defect in anything above.  So the every-`n` certificate is over `ZMod 5`, where the base carries no
second algebra structure over itself, and it doubles as this file's evidence that nothing above
needs characteristic zero.  The `ℚ` certificate below is for the gated `n = 2` form, whose statement
mentions no intermediate field and is therefore unaffected.

`ℚ` rather than `AlgebraicClosure ℚ` is deliberate: nothing above needs an algebraically closed
base. -/

section Nonvacuity

/-- ⚠️ Kept **local**: this file has no business adding a global `Fact (Nat.Prime 5)` instance to
the tree, and nothing outside this section needs it. -/
private lemma fact_prime_five : Fact (Nat.Prime 5) := ⟨by decide⟩

attribute [local instance] fact_prime_five

/-- The curve `y² = x³ - x` over `ZMod 5`, of discriminant `64 = 4`. -/
private def exampleCurveFive : Affine (ZMod 5) := ⟨0, 0, 0, -1, 0⟩

private instance : exampleCurveFive.IsElliptic := by
  rw [WeierstrassCurve.isElliptic_iff, isUnit_iff_ne_zero]
  decide +kernel

/-- The general-`n` statement, on a concrete curve, at **every** `n`. -/
example (n : ℕ)
    (hn : Transcendental (ZMod 5) (n • genericPoint (W := exampleCurveFive)).xCoord) :
    finrank ↥(mulByNEndoAlgHom n hn).fieldRange exampleCurveFive.FunctionField
      = finrank ↥(ZMod 5)⟮nMulRatFunc exampleCurveFive n⟯ (RatFunc (ZMod 5)) :=
  finrank_mulByNFieldRange_eq_finrank_adjoin n hn

/-! The certificate curve `y² = x³ − x` is the shared `EllipticCurves.Fixture.y2EqX3SubX`, whose
single `[CharZero F]` instance also supplies `IsElliptic` here. -/

open EllipticCurves.Fixture

/-- The gated form, with all three hypotheses discharged, at `n = 2` over `ℚ`. -/
example :
    finrank ↥(mulByNEndoAlgHom 2 (transcendental_xCoord_two_nsmul
        (W := y2EqX3SubX ℚ) (by norm_num))).fieldRange
      (y2EqX3SubX ℚ).FunctionField = 2 ^ 2 :=
  finrank_mulByNFieldRange_of_nMulRatFunc_eq 2 _ (by norm_num)
    (by rw [show ((2 : ℕ) : ℤ) = 2 from rfl, WeierstrassCurve.ΨSq_two]
        exact (y2EqX3SubX ℚ).isCoprime_Φ_two_Ψ₂Sq)
    (by rw [nMulRatFunc_two (by norm_num), doublingRatFunc_eq_ΦDivΨSq,
        show ((2 : ℕ) : ℤ) = 2 from rfl])

end Nonvacuity

end CoordinateRing
end WeierstrassCurve.Affine
