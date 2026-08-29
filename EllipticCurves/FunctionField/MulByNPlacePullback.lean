/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import EllipticCurves.FunctionField.MulByNIntegral
import EllipticCurves.FunctionField.PullbackDivisor

/-!
# The contraction of places and the divisor pullback along `[n]∗`, for every `n`

`EllipticCurves.FunctionField.PlacePullback` and
`EllipticCurves.FunctionField.PullbackDivisor` build the contraction `comapProjPoint`, the
ramification index `ramificationIdx`, the order transport `divisorProj_comp_apply` and the divisor
pullback `pullbackDivisor` **for an arbitrary `F`-fixing endomorphism `φ` of `F(W)` over which
`F(W)` is integral**.  Only the `[2]∗` and `[3]∗` instantiations were available, because only there
were the two hypotheses

```
hφF   : ∀ c : F, φ (algebraMap F F(W) c) = algebraMap F F(W) c
hφint : ∀ z : F(W), φ.IsIntegralElem z
```

discharged.  `EllipticCurves.FunctionField.MulByNIntegral` discharges the second one at every `n` at
which `[n]` is non-constant, and the first is the merged `mulByNEndo_algebraMap_base`.  This file is
the resulting instantiation: **`[n]∗` on places and on divisors, for every `n`.**

⚠️ **Nothing here is a new theorem about places.**  Every statement below is a merged general-`φ`
theorem applied to `mulByNEndo n hn`; the content is entirely in the hypothesis discharge, and the
route was `#1169`'s question — *which of the `#639` rungs survive at general `n` on `mulByNEndo`
alone*.  The two that do are these.

## The two rungs that do not survive, and are therefore absent

⚠️ **`[F(W) : [n]∗F(W)] = n²` is not here** (`#682` at `n = 2`, `#775` at `n = 3`).  What does
survive is that the degree is **finite** — `module_finite_mulByNEndoFieldRange`,
`EllipticCurves.FunctionField.MulByNIntegral`, from non-constancy alone.  The *value* is gated
twice over.  `finrank_mulByTwoFieldRange` reads it off the tower `F(W) ⊇ F(x) ⊇ F(x ∘ [2])`, and
that tower needs (i) `x ∘ [n] ∈ F(x)`, which at `n = 2` is `doublingRatFunc`, an element of
`RatFunc F` written down from `Φ₂/Ψ₂Sq`, and (ii) the reduced degrees `natDegree (Φ n) = n²` and
`natDegree (ΨSq n) = n² - 1` with the coprimality `#681`.  Both are `#404` / `#251`.  ⚠️ Note that
(i) is *true* at general `n` for a reason the group law does supply — `x(-P) = x(P)`, so
`x(n • 𝒫)` is fixed by the hyperelliptic involution `negYAlgEquiv`
(`EllipticCurves.FunctionField.NegYInvolution`) — but turning that into membership in `F(x)` needs
`F(x)` identified as the fixed field of that involution, which is **not** among that file's
results.  It is the cheapest visible follow-up on this front and it would still leave (ii).

⚠️ **`ordInfty ([n]∗ genX) = -2` is not here** (`#670` at `n = 2`), and this one is a **negative
result, not a gap**.  `ordInfty_mulByTwoEndo_genX`
(`EllipticCurves.FunctionField.MulByTwoPlaceAtInfinity`) and `ord_mulByTwoEndo_genX_neg`
(`EllipticCurves.FunctionField.MulByTwoFibreInfinity`) both open with `rw [mulByTwoEndo_genX h2, …]`
and then count degrees of `Φ₂` and `Ψ₂Sq`; `mulByNEndo_genX` rewrites instead to `x(n • 𝒫)`, about
which the group law says only that it satisfies the Weierstrass equation.  That pins
`ordInfty (x(n • 𝒫)) = -2k` and `ordInfty (y(n • 𝒫)) = -3k` for **some** `k ≥ 1`, and no more.

⚠️ **`k = 1` is false at general `n`.**  `mulByNEndo n hn` carries no hypothesis on `(n : F)`, and
none is available: over `F̄` of characteristic `p > 2` the transcendence hypothesis at `n = p` is
discharged by `exists_nsmul_ne_zero_of_isAlgClosed`, which asks only for `(2 : F) ≠ 0`.  There `[p]`
is inseparable, hence ramified over the point at infinity — `e = p` in the ordinary case and `p²` in
the supersingular one, the fibre having `p` points and `1` point respectively against
`∑ e_P = deg [p] = p²` — so `ordInfty ([p]∗ genX)` is `-2p` or `-2p²`.  A general-`n` rung 4 needs
`(n : F) ≠ 0` **on top of** the missing degree count.  ⚠️ That argument is Silverman *AEC* II.2.12,
III.4.10 and V.3.1 read together; it is stated here as the reason nothing is landed and it is **not
formalised** in this tree.

Consequently `comapProjPointN … none = none` (*"`[n]` fixes the point at infinity"*) is **also**
absent: `comapProjPointTwo_none` is proved from the pole order, and so are the residue-degree
companions `#701` and `#1046`.

## Main definitions and statements

* `WeierstrassCurve.Affine.CoordinateRing.comapProjPointN` and `…ramificationIdxN` — the contraction
  of a place along `[n]∗` and its ramification index;
* `…divisorProj_mulByNEndo_apply` — `ord_p (f ∘ [n]) = e_p · ord_{[n]⁻¹ p} (f)`;
* `…dvd_divisorProj_mulByNEndo` — the divisibility corollary `#422` states;
* `…finite_comapProjPointN_preimage_singleton` — finitely many places lie above a place;
* `…pullbackDivisorN` and `…divisorProj_mulByNEndo` — `div (f ∘ [n]) = [n]∗ (div f)`;
* `…comapProjPointNOfAlgClosed`, `…ramificationIdxNOfAlgClosed`, `…pullbackDivisorNOfAlgClosed`,
  `…divisorProj_mulByNEndoOfAlgClosed_apply`, `…divisorProj_mulByNEndoOfAlgClosed` and
  `…finite_comapProjPointNOfAlgClosed_preimage_singleton` — the same six over `F̄`, where the
  transcendence hypothesis is automatic and only `n ≠ 0` and `(2 : F) ≠ 0` remain;
* `…comapProjPointN_two` and `…ramificationIdxN_two` — at `n = 2` this layer **is** the merged one.

## References

* [J. H. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], II.2, II.3.6.
-/

namespace WeierstrassCurve.Affine

namespace CoordinateRing

variable {F : Type*} [Field F] {W : Affine F} [IsDedekindDomain W.CoordinateRing] [W.IsElliptic]

/-! ### The contraction and the ramification index -/

/-- **The contraction of a place of the projective curve along `[n]∗`.**  The general-`n` form of
the merged `comapProjPointTwo`. -/
noncomputable def comapProjPointN (n : ℕ)
    (hn : Transcendental F (n • genericPoint (W := W)).xCoord) : ProjPoint W → ProjPoint W :=
  comapProjPoint (mulByNEndo_algebraMap_base n hn) (mulByNEndo_isIntegralElem n hn)

@[simp] theorem placeOf_comapProjPointN (n : ℕ)
    (hn : Transcendental F (n • genericPoint (W := W)).xCoord) (p : ProjPoint W) :
    placeOf W (comapProjPointN n hn p) = (placeOf W p).comap (mulByNEndo n hn) :=
  placeOf_comapProjPoint _ _ p

/-- **The ramification index of `[n]∗`.**  The general-`n` form of the merged `ramificationIdxTwo`.

⚠️ It is *defined* as the value of the transported order at a uniformizer, exactly as at `n = 2`.
Nothing below computes it at any particular place, and in particular nothing says it is `1` at the
place at infinity — that is `#670`'s statement and it is not available at general `n`. -/
noncomputable def ramificationIdxN (n : ℕ)
    (hn : Transcendental F (n • genericPoint (W := W)).xCoord) (p : ProjPoint W) : ℤ :=
  ramificationIdx (mulByNEndo_algebraMap_base n hn) (mulByNEndo_isIntegralElem n hn) p

theorem ramificationIdxN_pos (n : ℕ)
    (hn : Transcendental F (n • genericPoint (W := W)).xCoord) (p : ProjPoint W) :
    0 < ramificationIdxN n hn p :=
  ramificationIdx_pos _ _ p

/-- **`ord_p (f ∘ [n]) = e_p · ord_{[n]⁻¹ p} (f)`** — the order transport under `[n]∗`, on the
*projective* point set, for every `n` at which `[n]` is non-constant.

`#422`'s 2026-08-16 correction showed the affine AKLB route is false because `[n]∗F[W] ⊄ F[W]`; the
obstruction is projective and this is the statement that dissolves it, now at general `n`. -/
theorem divisorProj_mulByNEndo_apply (n : ℕ)
    (hn : Transcendental F (n • genericPoint (W := W)).xCoord) {f : W.FunctionField} (hf : f ≠ 0)
    (p : ProjPoint W) :
    divisorProj W (mulByNEndo n hn f) p
      = ramificationIdxN n hn p * divisorProj W f (comapProjPointN n hn p) :=
  divisorProj_comp_apply _ _ hf p

/-- **`n`-divisibility of the divisor of `f ∘ [n]`.** -/
theorem dvd_divisorProj_mulByNEndo (n : ℕ)
    (hn : Transcendental F (n • genericPoint (W := W)).xCoord) {m : ℤ} {f : W.FunctionField}
    (hf : f ≠ 0) (hm : ∀ q : ProjPoint W, m ∣ divisorProj W f q) (p : ProjPoint W) :
    m ∣ divisorProj W (mulByNEndo n hn f) p :=
  dvd_divisorProj_comp (mulByNEndo_algebraMap_base n hn) (mulByNEndo_isIntegralElem n hn) hf hm p

/-! ### The divisor pullback -/

/-- **Finitely many places lie above a place, for `[n]∗`.** -/
theorem finite_comapProjPointN_preimage_singleton (n : ℕ)
    (hn : Transcendental F (n • genericPoint (W := W)).xCoord) (q : ProjPoint W) :
    ((comapProjPointN n hn) ⁻¹' {q}).Finite :=
  finite_comapProjPoint_preimage_singleton _ _ q

/-- **The pullback of divisors along `[n]∗`.**  The general-`n` form of the merged
`pullbackDivisorTwo`. -/
noncomputable def pullbackDivisorN (n : ℕ)
    (hn : Transcendental F (n • genericPoint (W := W)).xCoord) :
    (ProjPoint W →₀ ℤ) →+ (ProjPoint W →₀ ℤ) :=
  pullbackDivisor (mulByNEndo_algebraMap_base n hn) (mulByNEndo_isIntegralElem n hn)

@[simp] theorem pullbackDivisorN_apply (n : ℕ)
    (hn : Transcendental F (n • genericPoint (W := W)).xCoord) (D : ProjPoint W →₀ ℤ)
    (p : ProjPoint W) :
    pullbackDivisorN n hn D p = ramificationIdxN n hn p * D (comapProjPointN n hn p) :=
  rfl

/-- **`div (f ∘ [n]) = [n]∗ (div f)`** — the divisor-level functoriality of the
multiplication-by-`n` pullback, as an equation in the projective divisor group, for every `n` at
which `[n]` is non-constant.

This is `#414` / `#422` deliverable 1 at general `n`.  Silverman *AEC* II.3.6. -/
theorem divisorProj_mulByNEndo (n : ℕ)
    (hn : Transcendental F (n • genericPoint (W := W)).xCoord) {f : W.FunctionField} (hf : f ≠ 0) :
    divisorProj W (mulByNEndo n hn f) = pullbackDivisorN n hn (divisorProj W f) :=
  divisorProj_comp _ _ hf

/-! ### The `[IsAlgClosed F]` corollaries

Over an algebraically closed field of characteristic `≠ 2` the transcendence hypothesis is
automatic for every `n ≠ 0` (`transcendental_xCoord_nsmul_of_isAlgClosed`), so each statement above
has an unconditional-in-`n` form.  `mulByNEndoOfAlgClosed h2 hn` **is** `mulByNEndo n` at that
proof, so these are instantiations and not new content. -/

section IsAlgClosed

variable [IsAlgClosed F] (h2 : (2 : F) ≠ 0) {n : ℕ} (hn : n ≠ 0)

open Classical in
/-- **The contraction of a place along `[n]∗` over `F̄`**, for every `n ≠ 0`. -/
noncomputable def comapProjPointNOfAlgClosed : ProjPoint W → ProjPoint W :=
  comapProjPointN n (transcendental_xCoord_nsmul_of_isAlgClosed h2 hn)

open Classical in
/-- **The ramification index of `[n]∗` over `F̄`**, for every `n ≠ 0`. -/
noncomputable def ramificationIdxNOfAlgClosed (p : ProjPoint W) : ℤ :=
  ramificationIdxN n (transcendental_xCoord_nsmul_of_isAlgClosed h2 hn) p

open Classical in
/-- **The pullback of divisors along `[n]∗` over `F̄`**, for every `n ≠ 0`. -/
noncomputable def pullbackDivisorNOfAlgClosed : (ProjPoint W →₀ ℤ) →+ (ProjPoint W →₀ ℤ) :=
  pullbackDivisorN n (transcendental_xCoord_nsmul_of_isAlgClosed h2 hn)

open Classical in
/-- **`ord_p (f ∘ [n]) = e_p · ord_{[n]⁻¹ p} (f)` over `F̄`**, for every `n ≠ 0`. -/
theorem divisorProj_mulByNEndoOfAlgClosed_apply {f : W.FunctionField} (hf : f ≠ 0)
    (p : ProjPoint W) :
    divisorProj W (mulByNEndoOfAlgClosed h2 hn f) p
      = ramificationIdxNOfAlgClosed h2 hn p
        * divisorProj W f (comapProjPointNOfAlgClosed h2 hn p) :=
  divisorProj_mulByNEndo_apply n _ hf p

open Classical in
/-- **`div (f ∘ [n]) = [n]∗ (div f)` over `F̄`**, for every `n ≠ 0`.  This is the general-`n`
form of `#414` / `#422` deliverable 1, with no hypothesis left but `n ≠ 0` and `(2 : F) ≠ 0`. -/
theorem divisorProj_mulByNEndoOfAlgClosed {f : W.FunctionField} (hf : f ≠ 0) :
    divisorProj W (mulByNEndoOfAlgClosed h2 hn f)
      = pullbackDivisorNOfAlgClosed h2 hn (divisorProj W f) :=
  divisorProj_mulByNEndo n _ hf

open Classical in
/-- **Finitely many places lie above a place, for `[n]∗` over `F̄`**, for every `n ≠ 0`. -/
theorem finite_comapProjPointNOfAlgClosed_preimage_singleton (q : ProjPoint W) :
    ((comapProjPointNOfAlgClosed (W := W) h2 hn) ⁻¹' {q}).Finite :=
  finite_comapProjPointN_preimage_singleton n _ q

end IsAlgClosed

/-! ### Consistency with the merged `n = 2` layer

⚠️ These are not restatements: `comapProjPoint` and `ramificationIdx` are `choose`s, so *"the two
constructions agree"* is a theorem and not a definitional unfolding.  Together with
`mulByNEndo_two` they say the general-`n` place layer really is the merged one at `n = 2`, which is
what makes it the same rung rather than a parallel one. -/

section Consistency

variable (h2 : (2 : F) ≠ 0)

include h2 in
/-- **The `[n]∗` contraction at `n = 2` is the merged `[2]∗` contraction.** -/
theorem comapProjPointN_two (p : ProjPoint W) :
    comapProjPointN 2 (transcendental_xCoord_two_nsmul (W := W) h2) p = comapProjPointTwo h2 p := by
  refine placeOf_injective ?_
  rw [placeOf_comapProjPointN, comapProjPointTwo, placeOf_comapProjPoint, mulByNEndo_two h2]

include h2 in
/-- **The `[n]∗` ramification index at `n = 2` is the merged `[2]∗` index.**  Both are read off the
transported order at a uniformizer at the contracted place, and `comapProjPointN_two` says the
contracted place is the same one. -/
theorem ramificationIdxN_two (p : ProjPoint W) :
    ramificationIdxN 2 (transcendental_xCoord_two_nsmul (W := W) h2) p
      = ramificationIdxTwo h2 p := by
  obtain ⟨π, hπ0, hπ⟩ := exists_divisorProj_eq_one (comapProjPointTwo h2 p)
  have hN := divisorProj_mulByNEndo_apply 2 (transcendental_xCoord_two_nsmul (W := W) h2) hπ0 p
  have hT := divisorProj_mulByTwoEndo_apply h2 hπ0 p
  rw [comapProjPointN_two h2 p, hπ, mul_one] at hN
  rw [hπ, mul_one] at hT
  rw [← hN, ← hT, mulByNEndo_two h2]

end Consistency

/-! ### Non-vacuity

⚠️ Every statement above carries `[IsDedekindDomain W.CoordinateRing]` and `[W.IsElliptic]` on top
of a transcendence hypothesis, and `comapProjPointN` is a `choose`, so a curve on which the whole
chain elaborates with every instance discharged is worth committing rather than quoting.  ⚠️ The
certificate has to be at an index **beyond** `n = 2, 3`, or it certifies the merged instantiations
instead of these; it is at `n = 5`, matching the certificate of
`EllipticCurves.FunctionField.MulByNTranscendence`, on the same curve `y² + y = x³` over an
algebraic closure of `ℚ`. -/

section Nonvacuity

/-- The curve `y² + y = x³` over `ℚ`, this development's standard certificate curve. -/
private noncomputable def exampleCurveN : Affine ℚ := ⟨0, 0, 1, 0, 0⟩

/-- An algebraically closed extension of `ℚ`. -/
private abbrev exampleFieldN : Type := AlgebraicClosure ℚ

private instance : exampleCurveN.IsElliptic := by
  rw [WeierstrassCurve.isElliptic_iff, isUnit_iff_ne_zero]
  norm_num [exampleCurveN, WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈]

/-- ⚠️ `WeierstrassCurve.baseChange` is a plain `def`, so `[(W⁄F).IsElliptic]` is **not** found by
bare `inferInstance` from `[W.IsElliptic]`. -/
private instance : (exampleCurveN⁄exampleFieldN).IsElliptic :=
  inferInstanceAs (exampleCurveN.map (algebraMap ℚ exampleFieldN)).IsElliptic

private lemma exampleTwoN : (2 : exampleFieldN) ≠ 0 := by norm_num

open Classical in
private lemma exampleFiveN :
    Transcendental exampleFieldN
      ((5 : ℕ) • genericPoint (W := exampleCurveN⁄exampleFieldN)).xCoord :=
  transcendental_xCoord_nsmul_of_isAlgClosed exampleTwoN (by norm_num)

example : IsDedekindDomain (exampleCurveN⁄exampleFieldN).CoordinateRing := inferInstance

open Classical in
/-- **⚠️ THE CERTIFICATE, part one.**  At `n = 5` on a curve that exists, the order transport is a
genuine equation with a positive index. -/
example {f : (exampleCurveN⁄exampleFieldN).FunctionField} (hf : f ≠ 0)
    (p : ProjPoint (exampleCurveN⁄exampleFieldN)) :
    divisorProj (exampleCurveN⁄exampleFieldN) (mulByNEndo 5 exampleFiveN f) p
      = ramificationIdxN 5 exampleFiveN p
        * divisorProj (exampleCurveN⁄exampleFieldN) f (comapProjPointN 5 exampleFiveN p) :=
  divisorProj_mulByNEndo_apply 5 exampleFiveN hf p

open Classical in
/-- **⚠️ THE CERTIFICATE, part two.**  And the divisor-level form, at the same index. -/
example {f : (exampleCurveN⁄exampleFieldN).FunctionField} (hf : f ≠ 0) :
    divisorProj (exampleCurveN⁄exampleFieldN) (mulByNEndo 5 exampleFiveN f)
      = pullbackDivisorN 5 exampleFiveN (divisorProj (exampleCurveN⁄exampleFieldN) f) :=
  divisorProj_mulByNEndo 5 exampleFiveN hf

end Nonvacuity

end CoordinateRing

end WeierstrassCurve.Affine
