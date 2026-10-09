/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import EllipticCurves.DivisionPolynomial.PsiModFour
import EllipticCurves.Torsion.NsmulLadderOmega
import EllipticCurves.Torsion.OmegaThreeCharFree

/-!
# The division-polynomial pair lies on the curve at **every** index in **every** characteristic

`EllipticCurves.Torsion.OmegaCrux`'s `WeierstrassCurve.Affine.equation_div_of_ψ_ne_zero` proves
that the pair

```
(Φₙ(x)/ΨSqₙ(x),  ωₙ(x, y)/(2·ψₙ(x, y)³))
```

is a point of `W`, at every index over a field with `(2 : F) ≠ 0` and under `ψₙ(x, y) ≠ 0`, and its
`y`-coordinate is halved in its own statement.  `EllipticCurves.Torsion.OmegaIntegral` removed the
halving from the *datum* — `ωNumₙ` is an honest polynomial over every commutative ring with
`2·ωNumₙ = ωBracketₙ` — but not from the *theorem*: `(2 : F) ≠ 0` is still bound, because
`EllipticCurves.Torsion.OmegaOnCurve`'s `equation_of_hasPreΩSqAt` closes on
`mul_left_cancel₀ h4`, passing from the completed-square form
`(2Y + a₁X + a₃)² = 4X³ + b₂X² + 2b₄X + b₆` to `Equation` by dividing by `4`.

**This file proves the statement with no characteristic hypothesis at all, at every index.**
`WeierstrassCurve.Affine.equation_div_ωNum` is an arbitrary field, no `(2 : F) ≠ 0`, and only
`W.Equation x y` and `ψₙ(x, y) ≠ 0` — the genericity that says `(x, y)` is not `n`-torsion.

⚠️ **`EllipticCurves.Torsion.OmegaThreeCharFree` is the `n = 3` case of this and is where the
method was found**; this file is that argument at a general index, and `divPairNum_three` proves the
two numerators are the *same polynomial* rather than two spellings of one idea.

## The mechanism, and the two places the index costs something

Clearing the `ψₙ`-denominators of `Equation (Φₙ/ΨSqₙ) (ωNumₙ/ψₙ³)` gives the single polynomial

```
divPairNumₙ = ωNumₙ² + a₁Φₙψₙ·ωNumₙ + a₃ψₙ³·ωNumₙ
                − Φₙ³ − a₂Φₙ²ΨSqₙ − a₄ΦₙΨSqₙ² − a₆ΨSqₙ³   ∈ R[X][Y],
```

and the on-curve statement is that `W.polynomial` divides it (`polynomial_dvd_divPairNum`).  The
proof is `OmegaThreeCharFree`'s, in two steps:

1. `exists_four_mul_divPairNum`: `4·divPairNumₙ = 4·(W.polynomial·G)` over an arbitrary
   `CommRing`, by **one** `linear_combination` per parity of three or four inputs —
   `two_mul_ωNum` (used quadratically), `hasPreΩSq` (characteristic-free, every commutative ring),
   `four_mul_polynomial_dvd_ψ_sq_sub_C_ΨSq`, and at odd `n` Mathlib's `ψ₂_sq`.
2. `polynomial_dvd_divPairNum`: cancel the `4` **once**, over `MvPolynomial (Fin 5) ℤ`, a
   characteristic-`0` domain, and carry the divisibility down along `W.specialize`.

⚠️ **Two things are genuinely harder at a general index than at `n = 3`, and both are paid rather
than assumed.**

* **`ψₙ² ≠ ΨSqₙ` as polynomials.**  At `n = 3` they are equal (`ψ 3 = C Ψ₃`,
  `ΨSq 3 = Ψ₃²`), so the `n = 3` proof trades one for the other for free.  At a general index the
  trade leaves a multiple of `W.polynomial` behind, and the multiple has to be divisible by `4` or
  the cancellation in step 2 is illegal.  That is
  `EllipticCurves.DivisionPolynomial.PsiModFour`'s `four_mul_polynomial_dvd_ψ_sq_sub_C_ΨSq`, and it
  is why this file is two files.
* **The parity factor.**  `ωBracketₙ` carries `if Even n then 1 else ψ₂` and `HasPreΩSq n` carries
  its square, so the argument splits on the parity of `n` and the cofactor `G` differs between the
  branches: at odd `n` it is `preΩₙ² + 4a₃Dψₙ·ωNumₙ − D·(a₁Φₙ + a₃ΨSqₙ)²`, with `D` the cofactor of
  the first item (`ψₙ² − ΨSqₙ = 4·W.polynomial·D`), and at even `n` the `preΩₙ²` is absent, because
  the `4·W.polynomial` of `ψ₂² = Ψ₂Sq + 4·W.polynomial` is spent only where `ψ₂` actually occurs.
  ⚠️ **At `n = 3` the first item's contribution vanishes** — `ψ₃² = ΨSq₃` on the nose, so `D` may be
  taken to be `0` — **and `ψ₂²` is then the only source of `W.polynomial` at all, which is why
  `#2252`'s cofactor is the bare square `preΩ₃²` where the general odd one is not a square.**

## Main statements

⚠️ Every public declaration of this file is listed: **11 public, 0 private, 11 listed** in **9**
bullets, the last of which names three.  ⚠️ The elaborated environment carries a **twelfth** public
constant, `divPairNum.eq_1`, which is Lean's own equation lemma for the `def` and no source
declaration.  There are also **2 `example`s**, which assert nothing new: each type-checks a landed
statement as an instance of a theorem here, and they are named in `## What this subsumes` below.

* `WeierstrassCurve.divPairNum` : the cleared-denominator numerator, in `R[X][Y]`.
* `WeierstrassCurve.map_divPairNum` : it commutes with base change — the hinge of the descent.
* `WeierstrassCurve.exists_four_mul_divPairNum` : `4·divPairNumₙ = 4·(W.polynomial·G)` for some
  `G`, at every index over every commutative ring.
* `WeierstrassCurve.polynomial_dvd_divPairNum` : **`W.polynomial ∣ divPairNumₙ`**, at every index
  over every commutative ring, with no hypotheses.
* `WeierstrassCurve.ωNum_three` : `ωNum 3 = ω₃`, so the universal-curve `y`-numerator and
  `OmegaDivisionPolynomial`'s explicit `n = 3` one are one polynomial.
* `WeierstrassCurve.divPairNum_three` : `divPairNum 3 = triplingNum`, the same for the numerators.
* `WeierstrassCurve.Affine.equation_div_ωNum` : ⚠️⚠️ **the headline** — `(Φₙ/ΨSqₙ, ωNumₙ/ψₙ³)` is a
  point of `W`, over an arbitrary field, under `W.Equation x y` and `ψₙ(x, y) ≠ 0` and **nothing
  else**.
* `WeierstrassCurve.Affine.equation_divX_divYω` : the same with both coordinates named as the
  ladder's, `W.Equation (W.divX x n) (W.divYω x y n)`, under the same two hypotheses.
* `WeierstrassCurve.Affine.ψ_three_evalEval_ne_zero_curveCharTwoOne`,
  `…equation_div_ωNum_two_curveCharTwoOne`, `…equation_div_ωNum_three_curveCharTwoOne` :
  non-vacuity in characteristic `2` at an **even** and an **odd** index, exhibited and not asserted.

## What this subsumes

The two `example`s check, by type-checking and not by prose:

* `equation_div_of_ψ_ne_zero`'s conclusion at the named `y`-coordinate `W.omegaY x y n` follows
  from `equation_div_ωNum` and `OmegaIntegral`'s `omegaY_eq`, for a caller that holds
  `(2 : F) ≠ 0`;
* `OmegaThreeCharFree`'s `tripling_equation_ω₃_general` is `equation_div_ωNum` at `n = 3` composed
  with `ωNum_three`.

⚠️ **No landed statement is edited, weakened or deprecated.**  `equation_div_of_ψ_ne_zero`,
`equation_divX_omegaY` and `tripling_equation_ω₃_general` keep their statements and their proofs;
this file sits beside them.

## ⚠️ What this does **not** do

* ⚠️⚠️ **It says nothing about `n • P`.**  This is the algebraic on-curve identity for the
  division-polynomial coordinates; identifying the pair with the group-law multiple is the ladder of
  `EllipticCurves.Torsion.NsmulLadder` and `…NsmulLadderOmegaStep`, whose residual `(2 : F) ≠ 0` is
  a *sign* problem — `divT` carries no sign information where `2 = 0` — and is **not** touched here.
  `OmegaCrux`'s own docstring makes the same distinction for the `h2`-bound form.
* **No `(2 : F) ≠ 0` sweep.**  `equation_div_of_ψ_ne_zero`'s consumers are not re-proved: an
  `h2`-free form does not by itself retire a consumer's own `h2`, and the cascade is its own job.
* **Nothing about `Nonsingular`.**  The conclusion is `Equation`, exactly as the landed forms'.
* **Nothing about `hasXCoordFormula`** (`#2250`) or the Tate module (`#2340`).  Both consume the
  ladder and not this identity.

## References

* [J. Silverman, *The arithmetic of elliptic curves*][silverman2009], Exercise 3.7, III.6.
-/

open Polynomial
open scoped Polynomial.Bivariate

namespace WeierstrassCurve

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R)

/-- **The cleared-denominator numerator of the Weierstrass equation at the division-polynomial
pair of index `n`**:

```
divPairNumₙ = ωNumₙ² + a₁Φₙψₙ·ωNumₙ + a₃ψₙ³·ωNumₙ
                − Φₙ³ − a₂Φₙ²ΨSqₙ − a₄ΦₙΨSqₙ² − a₆ΨSqₙ³   ∈ R[X][Y].
```

This is `Equation (Φₙ/ΨSqₙ) (ωNumₙ/ψₙ³)` multiplied through by `ψₙ⁶`, with no division anywhere, so
that it makes sense over a ring in which `ψₙ` is not invertible and in which `2 = 0`.

⚠️ **`ΨSqₙ` and not `ψₙ²`** in the four `x`-coordinate terms: the two agree at a point of the curve
(`EllipticCurves.Torsion.DivisionPolynomialEval`'s `ψ_sq_evalEval`, this project's lemma and not
Mathlib's) but **not** as polynomials, and `ΨSqₙ` is the form every `Φ`/`ΨSq` lemma is stated in.
The gap is what `four_mul_polynomial_dvd_ψ_sq_sub_C_ΨSq` measures. -/
noncomputable def divPairNum (n : ℤ) : R[X][Y] :=
  W.ωNum n ^ 2 + C (C W.a₁) * C (W.Φ n) * W.ψ n * W.ωNum n + C (C W.a₃) * W.ψ n ^ 3 * W.ωNum n
    - C (W.Φ n) ^ 3 - C (C W.a₂) * C (W.Φ n) ^ 2 * C (W.ΨSq n)
    - C (C W.a₄) * C (W.Φ n) * C (W.ΨSq n) ^ 2 - C (C W.a₆) * C (W.ΨSq n) ^ 3

/-- **`divPairNum` commutes with base change** — the hinge of `polynomial_dvd_divPairNum`.
⚠️ **Without it the universal cancellation of the `4` is unusable**.  Of the base-change family
`map_preΨ` / `map_ΨSq` / `map_Φ` / `map_preΩ` / `map_ωNum`, the first **three** are Mathlib's and
the last **two** are this project's — `map_preΩ` in `EllipticCurves.Torsion.OmegaDivisionPolynomial`
and `map_ωNum` in `EllipticCurves.Torsion.OmegaIntegral`. -/
lemma map_divPairNum {S : Type*} [CommRing S] (f : R →+* S) (n : ℤ) :
    (W.map f).divPairNum n = (W.divPairNum n).map (mapRingHom f) := by
  simp only [divPairNum, map_ωNum, map_ψ, map_Φ, map_ΨSq, WeierstrassCurve.map_a₁,
    WeierstrassCurve.map_a₂, WeierstrassCurve.map_a₃, WeierstrassCurve.map_a₄,
    WeierstrassCurve.map_a₆, Polynomial.map_add, Polynomial.map_sub, Polynomial.map_mul,
    Polynomial.map_pow, Polynomial.map_C, coe_mapRingHom]

/-- **Four times the on-curve divisibility, over an arbitrary commutative ring at an arbitrary
index**: `4·divPairNumₙ = 4·(W.polynomial·G)`.

The witness is `G = (if Even n then 0 else preΩₙ²) + 4a₃Dψₙ·ωNumₙ − D·(a₁Φₙ + a₃ΨSqₙ)²`, where `D`
is the cofactor of `four_mul_polynomial_dvd_ψ_sq_sub_C_ΨSq`:
`ψₙ² − ΨSqₙ = 4·W.polynomial·D`.  Each parity is one `linear_combination`:

* `two_mul_ωNum` with coefficient
  `2ωNumₙ + εₙ·preΩₙ − ψₙ·A + 2a₁Φₙψₙ + 2a₃ψₙ³ − 8a₃·W.polynomial·D·ψₙ`, where
  `εₙ = if Even n then 1 else ψ₂` and `A = a₁Φₙ + a₃ΨSqₙ`; it enters quadratically, which is what
  the leading `2ωNumₙ` is;
* `four_mul_polynomial_dvd_ψ_sq_sub_C_ΨSq` with coefficient `2a₃εₙ·preΩₙψₙ − A·(A + 2a₃ψₙ²)`;
* `hasPreΩSq` with coefficient `1`, after `b₂`, `b₄` and `b₆` are unfolded;
* at odd `n` only, `ψ₂_sq` with coefficient `preΩₙ²`.

⚠️ **`Ψ₂Sq` and `W.polynomial` stay `ring` atoms**: at odd `n` the `Ψ₂Sq` of `ψ₂_sq` cancels against
the `Ψ₂Sq` of `hasPreΩSq`, and at even `n` neither appears.  The residue `ring` closes is
`Φₙ²ΨSqₙ(b₂ − a₁² − 4a₂) + ΦₙΨSqₙ²(2b₄ − 2a₁a₃ − 4a₄) + ΨSqₙ³(b₆ − a₃² − 4a₆)`, the same in both
branches. -/
theorem exists_four_mul_divPairNum (n : ℤ) :
    ∃ G : R[X][Y], 4 * W.divPairNum n = 4 * (W.toAffine.polynomial * G) := by
  obtain ⟨D, hD⟩ := W.four_mul_polynomial_dvd_ψ_sq_sub_C_ΨSq n
  have hN := W.two_mul_ωNum n
  rw [ωBracket] at hN
  set A : R[X][Y] := C (C W.a₁) * C (W.Φ n) + C (C W.a₃) * C (W.ΨSq n) with hA
  rcases Int.even_or_odd n with hev | hod
  · rw [if_pos hev] at hN
    have hΩ : W.preΩ n ^ 2 = 4 * W.Φ n ^ 3 + C W.b₂ * W.Φ n ^ 2 * W.ΨSq n +
        2 * C W.b₄ * W.Φ n * W.ΨSq n ^ 2 + C W.b₆ * W.ΨSq n ^ 3 := by
      have h := W.hasPreΩSq n
      rwa [HasPreΩSq, if_pos hev, mul_one] at h
    rw [b₂, b₄, b₆] at hΩ
    have hΩ' := congrArg (C : R[X] → R[X][Y]) hΩ
    refine ⟨4 * C (C W.a₃) * D * W.ψ n * W.ωNum n - D * A ^ 2, ?_⟩
    rw [divPairNum]
    simp only [map_ofNat, C_add, C_mul, C_pow] at hN hΩ' ⊢
    linear_combination (2 * W.ωNum n + C (W.preΩ n) - W.ψ n * A
        + 2 * C (C W.a₁) * C (W.Φ n) * W.ψ n + 2 * C (C W.a₃) * W.ψ n ^ 3
        - 8 * C (C W.a₃) * W.toAffine.polynomial * D * W.ψ n) * hN
      + (2 * C (C W.a₃) * C (W.preΩ n) * W.ψ n
        - A * (A + 2 * C (C W.a₃) * W.ψ n ^ 2)) * hD + hΩ'
  · have hodd : ¬ Even n := Int.not_even_iff_odd.mpr hod
    rw [if_neg hodd] at hN
    have hΩ : W.preΩ n ^ 2 * W.Ψ₂Sq = 4 * W.Φ n ^ 3 + C W.b₂ * W.Φ n ^ 2 * W.ΨSq n +
        2 * C W.b₄ * W.Φ n * W.ΨSq n ^ 2 + C W.b₆ * W.ΨSq n ^ 3 := by
      have h := W.hasPreΩSq n
      rwa [HasPreΩSq, if_neg hodd] at h
    rw [b₂, b₄, b₆] at hΩ
    have hΩ' := congrArg (C : R[X] → R[X][Y]) hΩ
    refine ⟨C (W.preΩ n) ^ 2 + 4 * C (C W.a₃) * D * W.ψ n * W.ωNum n - D * A ^ 2, ?_⟩
    rw [divPairNum]
    simp only [map_ofNat, C_add, C_mul, C_pow] at hN hΩ' ⊢
    linear_combination (2 * W.ωNum n + W.ψ₂ * C (W.preΩ n) - W.ψ n * A
        + 2 * C (C W.a₁) * C (W.Φ n) * W.ψ n + 2 * C (C W.a₃) * W.ψ n ^ 3
        - 8 * C (C W.a₃) * W.toAffine.polynomial * D * W.ψ n) * hN
      + C (W.preΩ n) ^ 2 * W.ψ₂_sq
      + (2 * C (C W.a₃) * W.ψ₂ * C (W.preΩ n) * W.ψ n
        - A * (A + 2 * C (C W.a₃) * W.ψ n ^ 2)) * hD + hΩ'

/-- ⚠️⚠️ **`W.polynomial ∣ divPairNumₙ` over EVERY commutative ring at EVERY index.**  No field, no
characteristic hypothesis, no `IsElliptic`, no genericity.

⚠️ **The `4` is not cancelled over `R` and does not have to be**: `divPairNum` and `W.polynomial`
both commute with base change, so it is enough to cancel it **once**, over
`MvPolynomial (Fin 5) ℤ`, which is an integral domain of characteristic `0`, and to carry the
divisibility down along `W.specialize`.  This is the only step of the file that uses a property of
any base ring at all, and it uses it about the universal one. -/
theorem polynomial_dvd_divPairNum (n : ℤ) : W.toAffine.polynomial ∣ W.divPairNum n := by
  obtain ⟨G, hG⟩ := exists_four_mul_divPairNum univ n
  have h4 : (4 : (MvPolynomial (Fin 5) ℤ)[X][Y]) ≠ 0 := by norm_num
  have huniv : univ.divPairNum n = univ.toAffine.polynomial * G := mul_left_cancel₀ h4 hG
  have he : univ.toAffine.map W.specialize = W.toAffine := univ_map_specialize W
  have H := congrArg (Polynomial.map (mapRingHom W.specialize)) huniv
  rw [← map_divPairNum, Polynomial.map_mul, ← Affine.map_polynomial, he, univ_map_specialize] at H
  exact ⟨_, H⟩

/-- **`ωNum 3 = ω₃`**: the universal-curve `y`-numerator at `n = 3` is
`EllipticCurves.Torsion.OmegaDivisionPolynomial`'s explicit `preΩ₃·Y + preω₃`, over every
commutative ring.

Both satisfy `2·z = ωBracket 3` (`two_mul_ωNum` and `two_mul_ω₃`, which is that bracket with
`if_neg` and `ψ 2 = ψ₂` applied), so they agree over `MvPolynomial (Fin 5) ℤ`, where `2` may be
cancelled, and `map_ωNum` with `map_ω₃` carries the equality to every ring.  ⚠️ **This is the
pattern `EllipticCurves.Torsion.DoublingOmega`'s `ωNum_two` already runs at `n = 2`**; it is here
because `divPairNum_three` needs it and because without it the tree carries two `n = 3`
`y`-numerators with no stated relation. -/
lemma ωNum_three : W.ωNum 3 = W.ω₃ := by
  have h2 : (2 : (MvPolynomial (Fin 5) ℤ)[X][Y]) ≠ 0 := by norm_num
  have huniv : univ.ωNum 3 = univ.ω₃ := by
    refine mul_left_cancel₀ h2 ?_
    rw [two_mul_ωNum, two_mul_ω₃, ωBracket, if_neg (by decide : ¬Even (3 : ℤ)), ψ_two]
  have H := congrArg (Polynomial.map (mapRingHom W.specialize)) huniv
  rw [← map_ωNum, ← map_ω₃, univ_map_specialize] at H
  exact H

/-- **`divPairNum 3 = triplingNum`**: the general numerator at `n = 3` is
`EllipticCurves.Torsion.OmegaThreeCharFree`'s, on the nose and not merely up to a rearrangement.

⚠️ **So nothing is duplicated**: that file's `triplingNum_eq` is `polynomial_dvd_divPairNum` at
`n = 3` with the cofactor named, and this file does not re-prove it. -/
lemma divPairNum_three : W.divPairNum 3 = W.triplingNum := by
  rw [divPairNum, triplingNum, ωNum_three]

namespace Affine

variable {F : Type*} [Field F] {W : Affine F} {x y : F}

/-- ⚠️⚠️ **THE HEADLINE: the division-polynomial pair of index `n` lies on the curve, over an
arbitrary field, in EVERY characteristic.**  For a point `(x, y)` of `W` with `ψₙ(x, y) ≠ 0` — i.e.
`(x, y)` not `n`-torsion — the pair

```
(Φₙ(x)/ΨSqₙ(x),  ωNumₙ(x, y)/ψₙ(x, y)³)
```

satisfies the Weierstrass equation, where `ωNumₙ` is the `2`-free `n`-division `y`-numerator of
`EllipticCurves.Torsion.OmegaIntegral` (`2·ωNumₙ = ωBracketₙ`).

⚠️ **This is `EllipticCurves.Torsion.OmegaCrux`'s `equation_div_of_ψ_ne_zero` with `(2 : F) ≠ 0`
DELETED and the halving removed from the `y`-coordinate**; the `Nonvacuity` section below
instantiates it over `ZMod 2`, where that hypothesis is false, at an even and at an odd index.

⚠️ **It is not a statement about `n • P`** — see the module docstring. -/
theorem equation_div_ωNum (h : W.Equation x y) {n : ℤ} (hψ : (W.ψ n).evalEval x y ≠ 0) :
    W.Equation ((W.Φ n).eval x / (W.ΨSq n).eval x)
      ((W.ωNum n).evalEval x y / (W.ψ n).evalEval x y ^ 3) := by
  obtain ⟨G, hG⟩ := W.polynomial_dvd_divPairNum n
  have hpoly : W.polynomial.evalEval x y = 0 := h
  have h0 : (W.divPairNum n).evalEval x y = 0 := by
    rw [hG, evalEval_mul, hpoly, zero_mul]
  rw [divPairNum] at h0
  simp only [evalEval_add, evalEval_sub, evalEval_mul, evalEval_pow, evalEval_C, eval_C] at h0
  have hs : (W.ΨSq n).eval x = (W.ψ n).evalEval x y ^ 2 := (ψ_sq_evalEval h n).symm
  have hS : (W.ΨSq n).eval x ≠ 0 := by rw [hs]; exact pow_ne_zero 2 hψ
  rw [equation_iff]
  rw [hs] at h0 ⊢
  field_simp
  linear_combination h0

/-- **The headline with both coordinates named as the ladder's**:
`W.Equation (W.divX x n) (W.divYω x y n)`, over an arbitrary field under `W.Equation x y` and
`ψₙ(x, y) ≠ 0`.

`divX x n = Φₙ(x)/ΨSqₙ(x)` and `divYω x y n = ωNumₙ(x, y)/ψₙ(x, y)³` by definition, so this is
`equation_div_ωNum` with two `rw`s and no content.  ⚠️ **It is the `h2`-free companion of
`EllipticCurves.Torsion.NsmulYCoord`'s `equation_divX_omegaY`**, whose `y`-coordinate is the halved
`omegaY`; ⚠️ **and it is still not a statement about `n • P`** — `NsmulEqDivω` is, and this is not
it. -/
theorem equation_divX_divYω (h : W.Equation x y) {n : ℤ} (hψ : (W.ψ n).evalEval x y ≠ 0) :
    W.Equation (W.divX x n) (W.divYω x y n) := by
  rw [divX, divYω]
  exact equation_div_ωNum h hψ

/-! ### ⚠️ What this subsumes, type-checked rather than claimed -/

-- `equation_div_of_ψ_ne_zero`'s conclusion at the named halved `y`-coordinate, for a caller that
-- holds `(2 : F) ≠ 0`: `omegaY_eq` identifies the two `y`-coordinates and the rest is the headline.
example (h2 : (2 : F) ≠ 0) (h : W.Equation x y) {n : ℤ} (hψ : (W.ψ n).evalEval x y ≠ 0) :
    W.Equation ((W.Φ n).eval x / (W.ΨSq n).eval x) (W.omegaY x y n) := by
  rw [omegaY_eq h2 n]
  exact equation_div_ωNum h hψ

-- `OmegaThreeCharFree`'s `tripling_equation_ω₃_general`, verbatim, as the `n = 3` instance.
example (h : W.Equation x y) (hψ : (W.ψ 3).evalEval x y ≠ 0) :
    W.Equation ((W.Φ 3).eval x / (W.ΨSq 3).eval x)
      (W.ω₃.evalEval x y / (W.ψ 3).evalEval x y ^ 3) := by
  rw [← ωNum_three]
  exact equation_div_ωNum h hψ

/-! ### Non-vacuity in characteristic `2`, at an even and at an odd index -/

section Nonvacuity

/-- `ψ₃ = C Ψ₃` with `Ψ₃ = X⁴ + X³ + 1` on `curveCharTwoOne = ⟨1, 0, 0, 0, 1⟩`, so
`ψ₃(1, 0) = 1 ≠ 0`: the point is **not** `3`-torsion, which is the one hypothesis the odd-index
certificate below still carries.

⚠️ `Ψ₃ = 3X⁴ + b₂X³ + 3b₄X² + 3b₆X + b₈` degenerates to `X⁴ + X³ + 1` here because `3 = 1` and
`b₄ = b₆ = 0` in `ZMod 2`, **not** because the characteristic kills the leading term.

⚠️ **The fixture is `EllipticCurves.Torsion.DoublingOmega`'s and no new one is declared.**  That
tuple is already a fixture elsewhere in the tree — `DoublingOmega`'s `curveCharTwoOne` and
`EllipticCurves.Torsion.OmegaThreeCharFree`'s `curveCharTwo` are **both public**, the second
deliberately so, while `EllipticCurves.Torsion.TriplingSurjective`'s `curveChar2` is private;
all three are over `ZMod 2`, with further copies over `AlgebraicClosure (ZMod 2)` — and this
file declares **none** of its own: `curveCharTwoOne` is in the import closure already and carries
`evalEval_ωNum_two_curveCharTwoOne`, which the even-index certificate needs and the other two do
not.  `curveCharTwo`'s own `ψ₃(1, 0) ≠ 0` is this same computation at a different declaration. -/
lemma ψ_three_evalEval_ne_zero_curveCharTwoOne : (curveCharTwoOne.ψ 3).evalEval 1 0 ≠ 0 := by
  rw [ψ_three, evalEval_C]
  simp only [WeierstrassCurve.Ψ₃, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆,
    WeierstrassCurve.b₈, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
    Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_ofNat, curveCharTwoOne]
  decide +kernel

/-- ⚠️⚠️ **The on-curve identity at the EVEN index `n = 2` over a field of characteristic `2`, with
both coordinates evaluated: `(Φ₂(1), 1)` is a point of `y² + xy = x³ + 1` over `ZMod 2`.**

`ψ₂(1, 0) = 1` (`evalEval_ψ_two_curveCharTwoOne`), so `ΨSq₂(1) = ψ₂(1, 0)² = 1` by
`ψ_sq_evalEval` and `ωNum₂(1, 0) = 1` by `evalEval_ωNum_two_curveCharTwoOne`; both denominators are
`1`.

⚠️ **This statement could not be *written* with `equation_div_of_ψ_ne_zero`**, whose `(2 : F) ≠ 0`
is false here, and `n = 2` is **even**, so it exercises the branch of
`exists_four_mul_divPairNum` in which no `ψ₂` occurs and the cofactor loses its `preΩₙ²`. -/
theorem equation_div_ωNum_two_curveCharTwoOne :
    curveCharTwoOne.Equation ((curveCharTwoOne.Φ 2).eval 1) 1 := by
  have hψ : (curveCharTwoOne.ψ 2).evalEval 1 0 ≠ 0 := by
    rw [evalEval_ψ_two_curveCharTwoOne]; decide
  have hΨSq : (curveCharTwoOne.ΨSq 2).eval 1 = 1 := by
    rw [← ψ_sq_evalEval equation_curveCharTwoOne 2, evalEval_ψ_two_curveCharTwoOne, one_pow]
  have h := equation_div_ωNum (W := curveCharTwoOne) equation_curveCharTwoOne (n := 2) hψ
  rwa [hΨSq, div_one, evalEval_ωNum_two_curveCharTwoOne, evalEval_ψ_two_curveCharTwoOne, one_pow,
    div_one] at h

/-- ⚠️ **The on-curve identity at the ODD index `n = 3` over a field of characteristic `2`.**  The
same curve and the same point; `ψ₃(1, 0) = 1 ≠ 0` is
`ψ_three_evalEval_ne_zero_curveCharTwoOne`.

⚠️ This index is also reachable from `OmegaThreeCharFree`'s `tripling_equation_ω₃_general`, and that
is the point of stating it: with `ωNum_three` the two are the same statement, so the general theorem
**agrees** with the landed `n = 3` one in characteristic `2` rather than merely coexisting with
it. -/
theorem equation_div_ωNum_three_curveCharTwoOne :
    curveCharTwoOne.Equation ((curveCharTwoOne.Φ 3).eval 1 / (curveCharTwoOne.ΨSq 3).eval 1)
      ((curveCharTwoOne.ωNum 3).evalEval 1 0 / (curveCharTwoOne.ψ 3).evalEval 1 0 ^ 3) :=
  equation_div_ωNum equation_curveCharTwoOne ψ_three_evalEval_ne_zero_curveCharTwoOne

end Nonvacuity

end Affine

end WeierstrassCurve
