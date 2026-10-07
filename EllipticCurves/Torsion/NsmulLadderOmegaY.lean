/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import EllipticCurves.Torsion.NsmulLadderOmegaStep
import EllipticCurves.Torsion.ThreeTorsionStructure
import EllipticCurves.Torsion.ChordSum
import EllipticCurves.Torsion.OmegaOnCurveCharFree

/-!
# The `y`-half of the `ω` ladder step, with no `(2 : F) ≠ 0`

`EllipticCurves.Torsion.NsmulLadderOmegaStep` ran the `ω`-flavoured ladder step as far as it goes
without `(2 : F) ≠ 0` and priced what was left down to a single item: the hypothesis `hY` of
`WeierstrassCurve.Affine.nsmul_stepω_of_addY_eq`, which is `#2250`'s route step 3 in its entirety.
Its `## What is *not* here` says what a round that wants `hY` must build — *"a polynomial identity
over an arbitrary commutative ring, in `ωNumₙ`, `ωNumₙ₊₁`, `Φₙ`, `Φₙ₊₁`, `ψₙ₋₁`, `ψₙ`, `ψₙ₊₁` and
`ψ₂`"*, descended from a characteristic-`0` domain.  ⚠️ **What is built below needs neither `Φₙ₊₁`
nor `ψ₂`**, and is two ingredients short of that prediction: the group law's `x`-coordinate stays
`M/P²` in index-`n` data instead of being identified with `Φₙ₊₁/ΨSqₙ₊₁`, and `ψ₂` survives only as
a nonvanishing hypothesis of the ladder step and never as an ingredient of the polynomial.

**This file builds that identity and discharges `hY`.**  The ladder step, the two-step induction
and the `x`-coordinate formula along a nonvanishing ladder all lose their `(2 : F) ≠ 0` here, and
the step is exercised at an odd index on a curve over `ZMod 2`.

## The identity

`hY` is the group law's `y`-coordinate at `(divXₙ, divYωₙ) + (x, y)`.  Writing `A = ψₙ(x, y)`,
`B = ψₙ₊₁(x, y)`, `C = ψₙ₋₁(x, y)`, `N = y·A³ − ωNumₙ(x, y)` and `P = A·B·C`, the chord slope is
`N/P` (because `x − divXₙ = B·C/A²`), the group law's `x`-coordinate is `M/P²` with

```
M = N² + a₁·N·P − a₂·P² − Φₙ·(B·C)² − x·P² ,
```

and multiplying `hY` through by `A³B³C³` turns it into the vanishing of

```
stepNumωₙ = N·(M − Φₙ·(B·C)²) + ωNumₙ·(B·C)³ + a₁·M·P + a₃·P³ + ωNumₙ₊₁·A³·C³ ,
```

an honest element of `R[X][Y]` with **no division anywhere** — `Y·ψₙ³ − ωNumₙ` in place of
`y − divYωₙ` is the whole trick, and it is available because `ωNumₙ` is a polynomial over every
commutative ring (`EllipticCurves.Torsion.OmegaIntegral`).  ⚠️ **`ψₙ²` and not `ΨSqₙ`**: the two
agree at a point of the curve and not as polynomials, and the statement proved here is a
divisibility by `W.polynomial`, so working modulo the curve is exactly right.

`WeierstrassCurve.Affine.evalEval_stepNumω_eq_mul` is that bookkeeping, and it is an equality
rather than an implication: it holds in **both** directions, which is what lets the same polynomial
carry the identity down from characteristic `0` and back out at a point in characteristic `2`.

## The route, and why it is not a `linear_combination`

⚠️ **The `2` is not cancelled by algebra here.**  `EllipticCurves.Torsion.OmegaOnCurveCharFree`
reaches `polynomial_dvd_divPairNum` by proving `4·divPairNumₙ = 4·(W.polynomial·G)` over an
arbitrary ring and cancelling the `4` once over `MvPolynomial (Fin 5) ℤ`; that needs an explicit
cofactor `G`, and for `stepNumω` no cofactor is written down anywhere.  **This file takes the other
route the tree already runs** — `EllipticCurves.Torsion.OmegaChordSum`'s: prove the polynomial
identity over an algebraically closed field of characteristic `0`, where the **landed `h2`-bound
ladder is available at every rung**, and descend.

1. `WeierstrassCurve.Affine.addY_divYω_eq_of_two_ne_zero`: with `(2 : F) ≠ 0`, `hY` is read off the
   two rungs `n` and `n + 1` of `nsmulEqDiv_of_forall_ψ_ne_zero` through
   `Point.add_of_X_ne` and translated into `divYω` by `divY_eq_divYω`.  ⚠️ **Nothing is re-proved**;
   the halved ladder is the source and the only new step is the group-law reading of `(n+1) • P`
   as `n • P + P`.
2. `WeierstrassCurve.Affine.polynomial_dvd_of_evalEval_eq_zero`: a bivariate polynomial that
   vanishes at every point of `W` above infinitely many `x` with `Ψ₂Sq(x) ≠ 0` is divisible by
   `W.polynomial`.  ⚠️ **This is the instrument the tree did not have**, and it is the bivariate
   counterpart of the `Polynomial.funext` step `OmegaChordSum` uses in one variable: reduce modulo
   the monic `W.polynomial`, write the remainder as `u + v·Y`, and kill `u` and `v` by reading the
   remainder at the **two** points above each good `x` — which is where `Ψ₂Sq(x) ≠ 0` is spent.
3. `WeierstrassCurve.Affine.hasStepOmega_of_isAlgClosed`: the good set is the complement of the
   root set of `∏_{k = 1}^{n+1} ΨSqₖ`, a nonzero polynomial in characteristic `0`, and
   `ψ_sq_evalEval` turns `ΨSqₖ(x) ≠ 0` into the ladder hypothesis `ψₖ(x, y) ≠ 0`.
4. `WeierstrassCurve.hasStepOmega`: descend to `univQ`, then along `ℤ → ℚ` to `univ`, then
   specialise.  ⚠️ **Divisibility descends along an injective base change because `W.polynomial` is
   MONIC** (`Polynomial.map_dvd_map`); no cofactor is needed and none is produced.

⚠️ **Characteristic `2` and singular curves are covered by the conclusion even though the proof
runs nowhere near them** — the same trade `WeierstrassCurve.hasChordSum`,
`WeierstrassCurve.hasPreΩSq` and `WeierstrassCurve.hasOmegaChord` make.

## Main results

⚠️ Every public declaration of this file is listed: **36 public, 7 private, 36 listed.**  ⚠️ The
figure is read off the **elaborated environment** and not a regex.  The environment's own totals
are **42** public and **16** private, with `Name.isInternal` dropped on the public side and not on
the private one; a uniform `isPrivateName` split reads **73** / **16** instead, and dropping
`Name.isInternal` on both sides reads **42** / **0**, every `_private.…` name being internal.  The
six extra public names are auto-generated (`ladderGap.eq_1`, `ladderProd.eq_1`,
`ladderAddXNum.eq_1`, `stepNumω.eq_1`, `HasStepOmega.eq_1` and the `NsmulEqDivω.congr_simp` this
file's `simp` calls elaborate), and the nine extra private ones are `_proof_1_*` internals of
`nsmulEqDivω_pair`.  **No source line declares any of the fifteen.**

* `WeierstrassCurve.ladderGap`, `WeierstrassCurve.ladderProd`, `WeierstrassCurve.ladderAddXNum`,
  `WeierstrassCurve.stepNumω` : the four pieces of the numerator above.
* `WeierstrassCurve.HasStepOmega` : `W.polynomial ∣ stepNumωₙ`, packaged for transport.
* `WeierstrassCurve.map_ladderGap`, `…map_ladderProd`, `…map_ladderAddXNum`, `…map_stepNumω`,
  `WeierstrassCurve.HasStepOmega.map`, `WeierstrassCurve.hasStepOmega_of_map`,
  `WeierstrassCurve.hasStepOmega_of_univ`, `WeierstrassCurve.hasStepOmega_of_univQ` : the descent.
* `WeierstrassCurve.stepNumω_one` and `WeierstrassCurve.hasStepOmega_one` : `stepNumω₁ = 0`
  outright, the one index the point-theoretic argument cannot reach (`ψ₀ = 0` makes `divX₀`
  meaningless, so there is no rung below `n = 1`).
* `WeierstrassCurve.Affine.evalEval_ladderGap`, `…evalEval_ladderProd`, `…evalEval_ladderAddXNum`,
  `…evalEval_stepNumω`, `…evalEval_stepNumω_eq_zero` : the point-level unfoldings.
* `WeierstrassCurve.Affine.evalEval_stepNumω_eq_mul` : the pricing identity, both directions.
* `WeierstrassCurve.Affine.polynomial_dvd_of_evalEval_eq_zero` : the divisibility criterion.
* `WeierstrassCurve.Affine.addY_divYω_eq_of_two_ne_zero` : `hY` under `(2 : F) ≠ 0`.
* `WeierstrassCurve.Affine.hasStepOmega_of_isAlgClosed` : the identity over `F̄` of characteristic
  `0`.
* `WeierstrassCurve.hasStepOmega` : ⚠️⚠️ **the identity over EVERY commutative ring at EVERY index
  `n ≥ 1`**, with no hypotheses on the ring and none on the curve.
* `WeierstrassCurve.Affine.addY_divYω_eq` : ⚠️⚠️ **`hY` with `(2 : F) ≠ 0` DROPPED** — `#2250`'s
  route step 3.
* `WeierstrassCurve.Affine.nsmulEqDivω_step_general` : ⚠️⚠️ **the ladder step with no
  `(2 : F) ≠ 0`**, `nsmul_stepω_of_addY_eq` with its last hypothesis discharged.
* `WeierstrassCurve.Affine.nsmulEqDivω_of_forall_ψ_ne_zero` : the whole ladder with no
  `(2 : F) ≠ 0`.
* `WeierstrassCurve.Affine.nsmul_eq_some_Φ_div_ΨSq_of_forall_ψ_ne_zero` and
  `…exists_ψ_evalEval_eq_zero_of_nsmul_eq_zero_general` : the `h2`-free counterparts of
  `nsmul_eq_some_Φ_div_ΨSq` and `exists_ψ_evalEval_eq_zero_of_nsmul_eq_zero`.
* `WeierstrassCurve.Affine.nsmulEqDivω_three_curveCharTwoOne` and
  `…nsmul_three_eq_some_Φ_div_ΨSq_curveCharTwoOne` : non-vacuity at an **odd** index in
  characteristic `2`.
* `WeierstrassCurve.Affine.divX_two_curveCharTwoOne` and `…divX_divYω_three_curveCharTwoOne` : both
  index-`3` coordinates **evaluated** on `y² + xy = x³ + 1` over `ZMod 2`.
* `WeierstrassCurve.Affine.nsmul_three_eq_neg_curveCharTwoOne` : ⚠️⚠️ **`3 • (1, 0) = −(1, 0)` in
  characteristic `2`**, so that point has order `4` — a group-law fact obtained from the `ω` ladder
  and from nothing else in this tree.
* `WeierstrassCurve.Affine.not_nsmulEqDiv_three_curveCharTwoOne` : ⚠️ **the halved ladder is FALSE
  at that index and point**, so the `ω` ladder is not a restatement of it there.

## ⚠️ What this does NOT do

* **It does not touch `divY`, `divT`, `NsmulEqDiv` or any landed statement.**  Everything is
  additive; `nsmulEqDivω_step` (the `h2`-bound step of `NsmulLadderOmegaStep`) keeps its statement
  and its proof, and so does every lemma of `EllipticCurves.Torsion.NsmulLadder`.  ⚠️ **No
  `(2 : F) ≠ 0` sweep of any consumer is attempted**, which `#2250` rules out in terms and which
  `#2245`'s cascade is the precedent against.
* **It does not deliver `#2250`'s route step 4.**  `WeierstrassCurve.Affine.HasXCoordFormula W n`
  quantifies over all points of `W` under the *weaker* hypothesis `ΨSqₙ(x) ≠ 0`, where the ladder
  asks for `ψ₁, …, ψₙ` all nonzero at the point; `hasXCoordFormula_of_two_ne_zero`
  (`EllipticCurves.Torsion.NsmulOrder`) spends `h2` at **six** sites across four lemmas, of which
  the ladder is only one. ⚠️ **The gap between the two hypotheses is real and this file does not
  close it.**
* **It does not deliver `#2340` items 3–5.**  What that row needs is
  `nsmul_eq_zero_iff_ψ_evalEval_eq_zero` (`NsmulOrder`) without `h2`, and the ladder is the half of
  it this file reaches: `exists_ψ_evalEval_eq_zero_of_nsmul_eq_zero_general` says *some* rung
  vanishes, and the sharpening to `ψₙ` itself, together with the converse, is the elliptic
  divisibility half that `NsmulLadder`'s own docstring names as not given by the ladder.
* **It does not claim that `stepNumωₙ` is nonzero at any index**, and nothing below needs it: at
  `n = 1` it is `0` outright (`stepNumω_one`), and at every index what is proved is the
  **divisibility**.  ⚠️ The identity is a congruence modulo `W.polynomial` by construction — its
  derivation substitutes `ψₙ(x, y)²` for `ΨSqₙ(x)` and `x·ψₙ² − ψₙ₊₁ψₙ₋₁` for `Φₙ`, both of which
  hold only on the curve — so an unqualified `stepNumωₙ = 0` is not what this file asserts.
* **Nothing here says anything about `(ℓ : F) ≠ 0`**, which is sharp, or about
  `EllipticCurves.Torsion.OddCharTwoLadderObstruction`'s ruling that route (a) of `#2340` is
  impossible at `divY`.  ⚠️ **That ruling stands and is not contradicted**: `divY` really is
  division by `2`, really is `0` in characteristic `2`, and nothing below weakens a hypothesis of
  any statement that names it.  What this file does is the route (b) that ruling prescribes —
  replace the *representation* of the `y`-coordinate, which `divYω` is.

## References

* [J. H. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], Exercise 3.7
-/

open Polynomial
open scoped Polynomial.Bivariate

namespace WeierstrassCurve

variable {R S : Type*} [CommRing R] [CommRing S] (W : WeierstrassCurve R)

/-- `Y·ψₙ³ − ωNumₙ`, i.e. `(y − divYωₙ)·ψₙ³`. -/
noncomputable def ladderGap (n : ℤ) : R[X][Y] := Y * W.ψ n ^ 3 - W.ωNum n

/-- `ψₙ·ψₙ₊₁·ψₙ₋₁`. -/
noncomputable def ladderProd (n : ℤ) : R[X][Y] := W.ψ n * W.ψ (n + 1) * W.ψ (n - 1)

/-- The group law's `x`-coordinate at `(divXₙ, divYωₙ) + (X, Y)`, cleared of denominators. -/
noncomputable def ladderAddXNum (n : ℤ) : R[X][Y] :=
  W.ladderGap n ^ 2 + C (C W.a₁) * W.ladderGap n * W.ladderProd n
    - C (C W.a₂) * W.ladderProd n ^ 2 - C (W.Φ n) * (W.ψ (n + 1) * W.ψ (n - 1)) ^ 2
    - C X * W.ladderProd n ^ 2

/-- The ladder step's `y`-half, cleared of denominators. -/
noncomputable def stepNumω (n : ℤ) : R[X][Y] :=
  W.ladderGap n * (W.ladderAddXNum n - C (W.Φ n) * (W.ψ (n + 1) * W.ψ (n - 1)) ^ 2)
    + W.ωNum n * (W.ψ (n + 1) * W.ψ (n - 1)) ^ 3
    + C (C W.a₁) * W.ladderAddXNum n * W.ladderProd n
    + C (C W.a₃) * W.ladderProd n ^ 3
    + W.ωNum (n + 1) * W.ψ n ^ 3 * W.ψ (n - 1) ^ 3

/-- The ladder step's `y`-half as a divisibility in `R[X][Y]`. -/
def HasStepOmega (W : WeierstrassCurve R) (n : ℤ) : Prop :=
  W.toAffine.polynomial ∣ W.stepNumω n

variable {W}

/-- `ladderGap` commutes with base change: `map_ωNum` and Mathlib's `map_ψ`. -/
lemma map_ladderGap (f : R →+* S) (n : ℤ) :
    (W.map f).ladderGap n = (W.ladderGap n).map (mapRingHom f) := by
  simp only [ladderGap, map_ωNum, map_ψ, Polynomial.map_sub, Polynomial.map_mul,
    Polynomial.map_pow, Polynomial.map_X]

/-- `ladderProd` commutes with base change. -/
lemma map_ladderProd (f : R →+* S) (n : ℤ) :
    (W.map f).ladderProd n = (W.ladderProd n).map (mapRingHom f) := by
  simp only [ladderProd, map_ψ, Polynomial.map_mul]

/-- `ladderAddXNum` commutes with base change. -/
lemma map_ladderAddXNum (f : R →+* S) (n : ℤ) :
    (W.map f).ladderAddXNum n = (W.ladderAddXNum n).map (mapRingHom f) := by
  simp only [ladderAddXNum, map_ladderGap, map_ladderProd, map_ψ, map_Φ,
    WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂, Polynomial.map_add, Polynomial.map_sub,
    Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_C, coe_mapRingHom, Polynomial.map_X]

/-- **`stepNumω` commutes with base change** — the hinge of the whole descent.  ⚠️ **Without it
the universal argument is unusable**, `ωNum` being built from an `Exists.choose` over the universal
ring and having no other handle (`EllipticCurves.Torsion.OmegaIntegral`'s `map_ωNum`). -/
lemma map_stepNumω (f : R →+* S) (n : ℤ) :
    (W.map f).stepNumω n = (W.stepNumω n).map (mapRingHom f) := by
  simp only [stepNumω, map_ladderGap, map_ladderProd, map_ladderAddXNum, map_ωNum, map_ψ, map_Φ,
    WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₃, Polynomial.map_add, Polynomial.map_sub,
    Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_C, coe_mapRingHom]

/-- **The identity transports along any ring homomorphism.**  Both sides commute with base change
and divisibility is preserved by `Polynomial.map_dvd`, so that is the whole proof. -/
lemma HasStepOmega.map {n : ℤ} (h : W.HasStepOmega n) (f : R →+* S) :
    (W.map f).HasStepOmega n := by
  rw [HasStepOmega, map_stepNumω, Affine.map_polynomial]
  exact Polynomial.map_dvd _ h

/-- **The identity descends along an injective ring homomorphism.**  ⚠️ **This is where
`Affine.monic_polynomial` is load-bearing and the reason the statement is a bare divisibility
rather than an equation with a named cofactor**: `Polynomial.map_dvd_map` reverses a divisibility
along an injective map exactly when the divisor is monic, so no cofactor has to be produced, and
`W.polynomial` is monic of degree `2` in `Y` over every ring. -/
lemma hasStepOmega_of_map {f : R →+* S} (hf : Function.Injective f) {n : ℤ}
    (h : (W.map f).HasStepOmega n) : W.HasStepOmega n := by
  rw [HasStepOmega, map_stepNumω, Affine.map_polynomial] at h
  exact (Polynomial.map_dvd_map _ (Polynomial.map_injective f hf) Affine.monic_polynomial).mp h

/-- **The reduction.**  `HasStepOmega n` for the universal curve gives it for every Weierstrass
curve over every commutative ring, by base change along `W.specialize`. -/
theorem hasStepOmega_of_univ {n : ℤ} (h : univ.HasStepOmega n) (W : WeierstrassCurve R) :
    W.HasStepOmega n := by
  have H := h.map W.specialize
  rwa [univ_map_specialize] at H

/-- **The reduction, over a characteristic-`0` base.**  Descend along the injective
`MvPolynomial.map (Int.castRingHom ℚ)` to `univ`, then specialise. -/
theorem hasStepOmega_of_univQ {n : ℤ} (h : univQ.HasStepOmega n) (W : WeierstrassCurve R) :
    W.HasStepOmega n :=
  hasStepOmega_of_univ
    (hasStepOmega_of_map (MvPolynomial.map_injective _ Int.cast_injective) h) W

/-- `stepNumω 1 = 0`: every factor that is not killed by `ψ₀ = 0` is killed by `ωNum₁ = Y`. -/
theorem stepNumω_one : W.stepNumω 1 = 0 := by
  have hgap : W.ladderGap 1 = 0 := by
    rw [ladderGap, ωNum_one, ψ_one]; ring
  have hzero : W.ψ (1 - 1) = 0 := by
    rw [show (1 : ℤ) - 1 = 0 by ring, ψ_zero]
  have hprod : W.ladderProd 1 = 0 := by rw [ladderProd, hzero]; ring
  have haddX : W.ladderAddXNum 1 = 0 := by
    rw [ladderAddXNum, hgap, hprod, hzero]; ring
  rw [stepNumω, hgap, hprod, haddX, hzero]; ring

/-- `HasStepOmega 1` over every commutative ring, out of `stepNumω_one` and `dvd_zero`. -/
theorem hasStepOmega_one (W : WeierstrassCurve R) : W.HasStepOmega 1 := by
  rw [HasStepOmega, stepNumω_one]
  exact dvd_zero _

namespace Affine

variable {F : Type*} [Field F] {W : Affine F} {x y : F}

/-- `ladderGapₙ(x, y) = y·ψₙ(x, y)³ − ωNumₙ(x, y)`, i.e. `(y − divYωₙ)·ψₙ³`. -/
lemma evalEval_ladderGap (n : ℤ) :
    (W.ladderGap n).evalEval x y
      = y * (W.ψ n).evalEval x y ^ 3 - (W.ωNum n).evalEval x y := by
  simp only [ladderGap, evalEval_sub, evalEval_mul, evalEval_pow, evalEval_X]

/-- `ladderProdₙ(x, y) = ψₙ·ψₙ₊₁·ψₙ₋₁` at the point. -/
lemma evalEval_ladderProd (n : ℤ) :
    (W.ladderProd n).evalEval x y
      = (W.ψ n).evalEval x y * (W.ψ (n + 1)).evalEval x y * (W.ψ (n - 1)).evalEval x y := by
  simp only [ladderProd, evalEval_mul]

/-- `ladderAddXNum` at the point, with `Φₙ` left as a univariate evaluation. -/
lemma evalEval_ladderAddXNum (n : ℤ) :
    (W.ladderAddXNum n).evalEval x y
      = (W.ladderGap n).evalEval x y ^ 2
          + W.a₁ * (W.ladderGap n).evalEval x y * (W.ladderProd n).evalEval x y
        - W.a₂ * (W.ladderProd n).evalEval x y ^ 2
        - (W.Φ n).eval x * ((W.ψ (n + 1)).evalEval x y * (W.ψ (n - 1)).evalEval x y) ^ 2
        - x * (W.ladderProd n).evalEval x y ^ 2 := by
  simp only [ladderAddXNum, evalEval_sub, evalEval_add, evalEval_mul, evalEval_pow, evalEval_C,
    eval_C, eval_X]

/-- `stepNumω` at the point, with its three pieces left folded. -/
lemma evalEval_stepNumω (n : ℤ) :
    (W.stepNumω n).evalEval x y
      = (W.ladderGap n).evalEval x y
          * ((W.ladderAddXNum n).evalEval x y
            - (W.Φ n).eval x * ((W.ψ (n + 1)).evalEval x y * (W.ψ (n - 1)).evalEval x y) ^ 2)
        + (W.ωNum n).evalEval x y
            * ((W.ψ (n + 1)).evalEval x y * (W.ψ (n - 1)).evalEval x y) ^ 3
        + W.a₁ * (W.ladderAddXNum n).evalEval x y * (W.ladderProd n).evalEval x y
        + W.a₃ * (W.ladderProd n).evalEval x y ^ 3
        + (W.ωNum (n + 1)).evalEval x y * (W.ψ n).evalEval x y ^ 3
            * (W.ψ (n - 1)).evalEval x y ^ 3 := by
  simp only [stepNumω, evalEval_sub, evalEval_add, evalEval_mul, evalEval_pow, evalEval_C,
    eval_C]

/-- **`stepNumωₙ` vanishes at every point of the curve**, which is all a consumer wants of the
divisibility: `W.polynomial` evaluates to `0` there by the definition of `Equation`. -/
lemma evalEval_stepNumω_eq_zero {n : ℤ} (hstep : W.HasStepOmega n) (h : W.Equation x y) :
    (W.stepNumω n).evalEval x y = 0 := by
  obtain ⟨g, hg⟩ := hstep
  rw [hg, evalEval_mul, h, zero_mul]

variable [DecidableEq F]

/-- **The pricing identity**: `stepNumω` evaluated at a point of the curve is the ladder step's
`y`-half, cleared of denominators. -/
theorem evalEval_stepNumω_eq_mul (h : W.Equation x y) {n : ℤ}
    (hm : (W.ψ (n - 1)).evalEval x y ≠ 0) (h0 : (W.ψ n).evalEval x y ≠ 0)
    (hp : (W.ψ (n + 1)).evalEval x y ≠ 0) :
    (W.addY (W.divX x n) x (W.divYω x y n)
            (W.slope (W.divX x n) x (W.divYω x y n) y) - W.divYω x y (n + 1))
        * ((W.ψ n).evalEval x y ^ 3 * (W.ψ (n + 1)).evalEval x y ^ 3
            * (W.ψ (n - 1)).evalEval x y ^ 3)
      = -(W.stepNumω n).evalEval x y := by
  have hφ : (W.Φ n).eval x
      = x * (W.ψ n).evalEval x y ^ 2
        - (W.ψ (n + 1)).evalEval x y * (W.ψ (n - 1)).evalEval x y :=
    Φ_eval_eq_of_equation h n
  have hd : x - W.divX x n
      = (W.ψ (n + 1)).evalEval x y * (W.ψ (n - 1)).evalEval x y
          / (W.ψ n).evalEval x y ^ 2 := sub_Φ_div_ΨSq h h0
  have hdne : (W.ψ (n + 1)).evalEval x y * (W.ψ (n - 1)).evalEval x y
      / (W.ψ n).evalEval x y ^ 2 ≠ 0 :=
    div_ne_zero (mul_ne_zero hp hm) (pow_ne_zero 2 h0)
  have hX : W.divX x n = x - (W.ψ (n + 1)).evalEval x y * (W.ψ (n - 1)).evalEval x y
      / (W.ψ n).evalEval x y ^ 2 := by linear_combination -hd
  have hxne : W.divX x n ≠ x := by
    rw [hX]
    intro hc
    exact hdne (by linear_combination -hc)
  rw [addY, negAddY, addX, negY, slope_of_X_ne hxne, hX, divYω, divYω, evalEval_stepNumω,
    evalEval_ladderAddXNum, evalEval_ladderGap, evalEval_ladderProd, hφ]
  field_simp
  ring

/-- ⚠️ **The ladder step's `y`-half with `(2 : F) ≠ 0` DROPPED.** -/
theorem addY_divYω_eq {n : ℤ} (hstep : W.HasStepOmega n) (h : W.Equation x y)
    (hm : (W.ψ (n - 1)).evalEval x y ≠ 0) (h0 : (W.ψ n).evalEval x y ≠ 0)
    (hp : (W.ψ (n + 1)).evalEval x y ≠ 0) :
    W.addY (W.divX x n) x (W.divYω x y n)
        (W.slope (W.divX x n) x (W.divYω x y n) y)
      = W.divYω x y (n + 1) := by
  have key := evalEval_stepNumω_eq_mul h hm h0 hp
  rw [evalEval_stepNumω_eq_zero hstep h, neg_zero] at key
  rcases mul_eq_zero.mp key with hz | hz
  · linear_combination hz
  · exact absurd hz
      (mul_ne_zero (mul_ne_zero (pow_ne_zero 3 h0) (pow_ne_zero 3 hp)) (pow_ne_zero 3 hm))

/-! ### Vanishing on the curve implies divisibility by `W.polynomial` -/

omit [DecidableEq F] in
/-- **A bivariate polynomial vanishing at every point of `W` above infinitely many
`x`-coordinates at which `Ψ₂Sq` does not vanish is divisible by `W.polynomial`.** -/
theorem polynomial_dvd_of_evalEval_eq_zero [IsAlgClosed F] {p : F[X][Y]}
    (hinf : {x : F | W.Ψ₂Sq.eval x ≠ 0 ∧ ∀ y : F, W.Equation x y → p.evalEval x y = 0}.Infinite) :
    W.polynomial ∣ p := by
  classical
  rw [← modByMonic_eq_zero_iff_dvd monic_polynomial]
  have hdeg : (p %ₘ W.polynomial).degree ≤ 1 := by
    have h2 := degree_modByMonic_lt p (monic_polynomial (W := W))
    rw [degree_polynomial] at h2
    exact Order.le_of_lt_succ h2
  have hrEq : p %ₘ W.polynomial
      = C ((p %ₘ W.polynomial).coeff 1) * Y + C ((p %ₘ W.polynomial).coeff 0) :=
    eq_X_add_C_of_degree_le_one hdeg
  have hrv : ∀ x y : F, W.Equation x y → p.evalEval x y = 0 →
      ((p %ₘ W.polynomial).coeff 1).eval x * y
        + ((p %ₘ W.polynomial).coeff 0).eval x = 0 := by
    intro x y hxy hp0
    have hev := congrArg (Polynomial.evalEval x y) (modByMonic_add_div p W.polynomial)
    rw [evalEval_add, evalEval_mul, hxy, zero_mul, add_zero, hp0, hrEq, evalEval_add,
      evalEval_mul, evalEval_C, evalEval_C, evalEval_X] at hev
    linear_combination hev
  have hboth : ∀ x ∈ {x : F | W.Ψ₂Sq.eval x ≠ 0 ∧
      ∀ y : F, W.Equation x y → p.evalEval x y = 0},
      ((p %ₘ W.polynomial).coeff 1).eval x = 0
        ∧ ((p %ₘ W.polynomial).coeff 0).eval x = 0 := by
    rintro x ⟨hΨ, hp0⟩
    obtain ⟨y, hy⟩ := exists_equation' (W := W) x
    have hy' : W.Equation x (W.negY x y) := (equation_neg x y).mpr hy
    have hyne : y - W.negY x y ≠ 0 := by
      intro hc
      refine hΨ ?_
      have hψ : (W.ψ 2).evalEval x y = 0 := by
        rw [ψ_two_evalEval]
        rw [negY] at hc
        linear_combination hc
      have hsq := ψ_sq_evalEval hy 2
      rw [ΨSq_two, hψ] at hsq
      linear_combination -hsq
    have e1 := hrv x y hy (hp0 y hy)
    have e2 := hrv x (W.negY x y) hy' (hp0 _ hy')
    have hc1 : ((p %ₘ W.polynomial).coeff 1).eval x = 0 := by
      rcases mul_eq_zero.mp
        (show ((p %ₘ W.polynomial).coeff 1).eval x * (y - W.negY x y) = 0 by
          linear_combination e1 - e2) with h | h
      · exact h
      · exact absurd h hyne
    exact ⟨hc1, by linear_combination e1 - y * hc1⟩
  have h1 : (p %ₘ W.polynomial).coeff 1 = 0 :=
    eq_zero_of_infinite_isRoot _ (hinf.mono fun x hx => (hboth x hx).1)
  have h0 : (p %ₘ W.polynomial).coeff 0 = 0 :=
    eq_zero_of_infinite_isRoot _ (hinf.mono fun x hx => (hboth x hx).2)
  rw [hrEq, h1, h0, C_0, zero_mul, add_zero]

/-! ### The identity over a characteristic-`0` algebraically closed field -/

/-- The ladder step's `y`-half under `(2 : F) ≠ 0`, read off the two rungs `n` and `n + 1` of the
halved ladder and translated into `divYω`. -/
theorem addY_divYω_eq_of_two_ne_zero (h2 : (2 : F) ≠ 0) (hns : W.Nonsingular x y) {n : ℕ}
    (hn : 2 ≤ n) (hψ : ∀ k : ℤ, 1 ≤ k → k ≤ (n : ℤ) + 1 → (W.ψ k).evalEval x y ≠ 0) :
    W.addY (W.divX x (n : ℤ)) x (W.divYω x y (n : ℤ))
        (W.slope (W.divX x (n : ℤ)) x (W.divYω x y (n : ℤ)) y)
      = W.divYω x y ((n : ℤ) + 1) := by
  have hEq : W.Equation x y := hns.left
  have ht : (W.ψ 2).evalEval x y ≠ 0 := hψ 2 (by norm_num) (by omega)
  have hm : (W.ψ ((n : ℤ) - 1)).evalEval x y ≠ 0 := hψ _ (by omega) (by omega)
  have h0 : (W.ψ (n : ℤ)).evalEval x y ≠ 0 := hψ _ (by omega) (by omega)
  have hp : (W.ψ ((n : ℤ) + 1)).evalEval x y ≠ 0 := hψ _ (by omega) le_rfl
  obtain ⟨h0', IH0⟩ := nsmulEqDiv_of_forall_ψ_ne_zero h2 hns (n := n) (by omega)
    fun k hk hk2 => hψ k hk (by omega)
  have hcast : ((n + 1 : ℕ) : ℤ) = (n : ℤ) + 1 := by push_cast; ring
  have G1 : NsmulEqDiv hns ((n : ℤ) + 1) := by
    rw [← hcast]
    exact nsmulEqDiv_of_forall_ψ_ne_zero h2 hns (n := n + 1) (by omega)
      fun k hk hk2 => hψ k hk (by push_cast at hk2; omega)
  obtain ⟨hp', IH1⟩ := G1
  have hsub0 : x - W.divX x (n : ℤ) ≠ 0 := by
    rw [divX, sub_Φ_div_ΨSq hEq h0]
    exact div_ne_zero (mul_ne_zero hp hm) (pow_ne_zero 2 h0)
  have hxne : W.divX x (n : ℤ) ≠ x := fun hc => hsub0 (sub_eq_zero_of_eq hc.symm)
  have hadd : (((n : ℤ) + 1) • Point.some x y hns : W.Point)
      = (n : ℤ) • Point.some x y hns + Point.some x y hns := by
    rw [add_smul, one_zsmul]
  rw [IH0, Point.add_of_X_ne hxne, IH1, Point.some.injEq] at hadd
  have hY := hadd.2
  rw [divY_eq_divYω hEq h2 ht h0] at hY
  rw [divY_eq_divYω hEq h2 ht hp] at hY
  exact hY.symm

omit [DecidableEq F] in
/-- **The step identity over an algebraically closed field of characteristic `0`.** -/
theorem hasStepOmega_of_isAlgClosed [CharZero F] [IsAlgClosed F] [W.IsElliptic] {n : ℕ}
    (hn : 2 ≤ n) : W.HasStepOmega (n : ℤ) := by
  classical
  have h2 : (2 : F) ≠ 0 := two_ne_zero
  refine polynomial_dvd_of_evalEval_eq_zero ?_
  have hq0 : (∏ k ∈ Finset.Icc (1 : ℤ) ((n : ℤ) + 1), W.ΨSq k) ≠ 0 := by
    refine Finset.prod_ne_zero_iff.mpr fun k hk => W.ΨSq_ne_zero ?_
    simp only [Finset.mem_Icc] at hk
    exact Int.cast_ne_zero.mpr (by omega)
  refine Set.Infinite.mono ?_ (finite_setOf_isRoot hq0).infinite_compl
  intro x hx
  simp only [Set.mem_compl_iff, Set.mem_setOf_eq, IsRoot.def, eval_prod] at hx
  have heach : ∀ k ∈ Finset.Icc (1 : ℤ) ((n : ℤ) + 1), (W.ΨSq k).eval x ≠ 0 :=
    Finset.prod_ne_zero_iff.mp hx
  refine ⟨?_, ?_⟩
  · have h2Sq := heach 2 (by simp only [Finset.mem_Icc]; omega)
    rwa [ΨSq_two] at h2Sq
  · intro y hy
    have hψ : ∀ k : ℤ, 1 ≤ k → k ≤ (n : ℤ) + 1 → (W.ψ k).evalEval x y ≠ 0 := by
      intro k hk hk2 hc
      have hs := ψ_sq_evalEval hy k
      rw [hc] at hs
      exact heach k (by simp only [Finset.mem_Icc]; omega) (by linear_combination -hs)
    have hns : W.Nonsingular x y := equation_iff_nonsingular.mp hy
    have hm : (W.ψ ((n : ℤ) - 1)).evalEval x y ≠ 0 := hψ _ (by omega) (by omega)
    have h0 : (W.ψ (n : ℤ)).evalEval x y ≠ 0 := hψ _ (by omega) (by omega)
    have hp : (W.ψ ((n : ℤ) + 1)).evalEval x y ≠ 0 := hψ _ (by omega) le_rfl
    have key := evalEval_stepNumω_eq_mul hy hm h0 hp
    rw [addY_divYω_eq_of_two_ne_zero h2 hns hn hψ, sub_self, zero_mul] at key
    exact neg_eq_zero.mp key.symm

end Affine

/-! ### The identity over every commutative ring -/

/-- ⚠️⚠️ **The ladder step's `y`-half, over EVERY commutative ring at EVERY index `n ≥ 1`.** -/
theorem hasStepOmega (W : WeierstrassCurve R) {n : ℤ} (hn : 1 ≤ n) : W.HasStepOmega n := by
  classical
  obtain ⟨m, rfl⟩ : ∃ m : ℕ, n = (m : ℤ) := ⟨n.toNat, by omega⟩
  rcases Nat.lt_or_ge m 2 with hlt | hge
  · obtain rfl : m = 1 := by omega
    exact_mod_cast hasStepOmega_one W
  refine hasStepOmega_of_univQ ?_ W
  set B := MvPolynomial (Fin 5) ℚ with hB
  set K := AlgebraicClosure (FractionRing B) with hK
  set f : B →+* K := (algebraMap (FractionRing B) K).comp (algebraMap B (FractionRing B)) with hf
  have hfinj : Function.Injective f :=
    (algebraMap (FractionRing B) K).injective.comp (IsFractionRing.injective B (FractionRing B))
  refine hasStepOmega_of_map (f := f) hfinj ?_
  haveI : (univQ.map f).IsElliptic := by
    refine ⟨?_⟩
    rw [map_Δ]
    exact isUnit_iff_ne_zero.mpr fun h => univQ_Δ_ne_zero ((map_eq_zero_iff f hfinj).mp h)
  exact Affine.hasStepOmega_of_isAlgClosed hge

namespace Affine

variable {F : Type*} [Field F] [DecidableEq F] {W : Affine F} {x y : F}

/-- ⚠️⚠️ **The ladder step on `NsmulEqDivω` with `(2 : F) ≠ 0` DROPPED.** -/
theorem nsmulEqDivω_step_general (hns : W.Nonsingular x y) {n : ℤ} (hn : 1 ≤ n)
    (hm : (W.ψ (n - 1)).evalEval x y ≠ 0) (h0 : (W.ψ n).evalEval x y ≠ 0)
    (hp : (W.ψ (n + 1)).evalEval x y ≠ 0) (ht : (W.ψ 2).evalEval x y ≠ 0)
    (Gm : NsmulEqDivω hns (n - 1)) (G0 : NsmulEqDivω hns n) : NsmulEqDivω hns (n + 1) := by
  obtain ⟨hm', IHm⟩ := Gm
  obtain ⟨h0', IH0⟩ := G0
  exact nsmul_stepω_of_addY_eq hns hm h0 hp ht hm' h0' IHm IH0
    (addY_divYω_eq (hasStepOmega W hn) hns.left hm h0 hp)

/-- The two-step induction, with no `(2 : F) ≠ 0`. -/
private theorem nsmulEqDivω_pair (hns : W.Nonsingular x y) :
    ∀ m : ℕ, (∀ k : ℤ, 1 ≤ k → k ≤ (m : ℤ) + 2 → (W.ψ k).evalEval x y ≠ 0) →
      NsmulEqDivω hns ((m : ℤ) + 1) ∧ NsmulEqDivω hns ((m : ℤ) + 2) := by
  intro m
  induction m with
  | zero =>
    intro hψ
    refine ⟨?_, ?_⟩
    · simpa using nsmulEqDivω_one hns
    · simpa using nsmulEqDivω_two hns (hψ 2 (by norm_num) (by push_cast))
  | succ k IH =>
    intro hψ
    obtain ⟨G1, G2⟩ := IH fun j hj hj2 => hψ j hj (by push_cast at hj2 ⊢; omega)
    have hcast : ((k : ℕ) : ℤ) + 1 + 1 = ((k + 1 : ℕ) : ℤ) + 1 := by push_cast; ring
    refine ⟨by rw [← hcast]; exact G2, ?_⟩
    have hne : ∀ j : ℤ, 1 ≤ j → j ≤ (k : ℤ) + 3 → (W.ψ j).evalEval x y ≠ 0 := by
      intro j hj hj2; exact hψ j hj (by push_cast; omega)
    have hstep := nsmulEqDivω_step_general (n := (k : ℤ) + 2) hns (by omega)
      (by rw [show (k : ℤ) + 2 - 1 = (k : ℤ) + 1 by ring]
          exact hne _ (by omega) (by omega))
      (hne _ (by omega) (by omega))
      (by rw [show (k : ℤ) + 2 + 1 = (k : ℤ) + 3 by ring]
          exact hne _ (by omega) (by omega))
      (hne 2 (by norm_num) (by omega))
      (by rw [show (k : ℤ) + 2 - 1 = (k : ℤ) + 1 by ring]; exact G1) G2
    rw [show ((k + 1 : ℕ) : ℤ) + 2 = (k : ℤ) + 2 + 1 by push_cast; ring]
    exact hstep

/-- ⚠️⚠️ **The multiplication-by-`n` coordinate formula along a nonvanishing ladder, with no
`(2 : F) ≠ 0`.** -/
theorem nsmulEqDivω_of_forall_ψ_ne_zero (hns : W.Nonsingular x y) {n : ℕ}
    (hn : 1 ≤ n) (hψ : ∀ k : ℤ, 1 ≤ k → k ≤ (n : ℤ) → (W.ψ k).evalEval x y ≠ 0) :
    NsmulEqDivω hns (n : ℤ) := by
  rcases Nat.lt_or_ge n 2 with hlt | hge
  · obtain rfl : n = 1 := by omega
    simpa using nsmulEqDivω_one hns
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
    have H := (nsmulEqDivω_pair hns m
      fun k hk hk2 => hψ k hk (by push_cast at hk2 ⊢; omega)).2
    rwa [show ((m : ℕ) : ℤ) + 2 = ((m + 2 : ℕ) : ℤ) by push_cast; ring] at H

/-- ⚠️⚠️ **`x(n • P) = Φₙ(x)/ΨSqₙ(x)` with no `(2 : F) ≠ 0`.** -/
theorem nsmul_eq_some_Φ_div_ΨSq_of_forall_ψ_ne_zero (hns : W.Nonsingular x y) {n : ℕ}
    (hn : 1 ≤ n) (hψ : ∀ k : ℤ, 1 ≤ k → k ≤ (n : ℤ) → (W.ψ k).evalEval x y ≠ 0) :
    ∃ (y' : F) (h' : W.Nonsingular ((W.Φ (n : ℤ)).eval x / (W.ΨSq (n : ℤ)).eval x) y'),
      (n • Point.some x y hns : W.Point) = .some _ y' h' := by
  obtain ⟨h', heq⟩ := nsmulEqDivω_of_forall_ψ_ne_zero hns hn hψ
  exact ⟨W.divYω x y (n : ℤ), h', by rw [← natCast_zsmul]; exact heq⟩

/-- ⚠️⚠️ **`n • P = 0` forces one of `ψ₁(P), …, ψₙ(P)` to vanish, with no `(2 : F) ≠ 0`.** -/
theorem exists_ψ_evalEval_eq_zero_of_nsmul_eq_zero_general (hns : W.Nonsingular x y) {n : ℕ}
    (hn : 1 ≤ n) (hzero : (n • Point.some x y hns : W.Point) = 0) :
    ∃ k : ℤ, 1 ≤ k ∧ k ≤ (n : ℤ) ∧ (W.ψ k).evalEval x y = 0 := by
  by_contra hcon
  push Not at hcon
  obtain ⟨y', h', heq⟩ := nsmul_eq_some_Φ_div_ΨSq_of_forall_ψ_ne_zero hns hn
    fun k hk hk2 => hcon k hk hk2
  rw [heq] at hzero
  exact Point.some_ne_zero h' hzero

/-! ### Non-vacuity: the ladder step runs in characteristic `2` -/

section Nonvacuity

open EllipticCurves.Fixture

/-- `ψ₁(1, 0)`, `ψ₂(1, 0)` and `ψ₃(1, 0)` are all nonzero on `curveCharTwoOne` over `ZMod 2`. -/
private lemma ψ_ne_zero_curveCharTwoOne : ∀ k : ℤ, 1 ≤ k → k ≤ 3 →
    (curveCharTwoOne.ψ k).evalEval 1 0 ≠ 0 := by
  intro k hk hk3
  interval_cases k
  · rw [ψ_one_evalEval]; exact one_ne_zero
  · rw [evalEval_ψ_two_curveCharTwoOne]; decide
  · exact ψ_three_evalEval_ne_zero_curveCharTwoOne

/-- ⚠️⚠️ **The ladder reaches the ODD index `n = 3` on `y² + xy = x³ + 1` over `ZMod 2`.** -/
theorem nsmulEqDivω_three_curveCharTwoOne :
    NsmulEqDivω nonsingular_curveCharTwoOne (3 : ℤ) := by
  have H := nsmulEqDivω_of_forall_ψ_ne_zero nonsingular_curveCharTwoOne (n := 3) (by norm_num)
    fun k hk hk3 => ψ_ne_zero_curveCharTwoOne k hk (by exact_mod_cast hk3)
  exact_mod_cast H

/-- ⚠️ **The `x`-coordinate formula at `n = 3` in characteristic `2`.** -/
theorem nsmul_three_eq_some_Φ_div_ΨSq_curveCharTwoOne :
    ∃ (y' : ZMod 2) (h' : curveCharTwoOne.Nonsingular
        ((curveCharTwoOne.Φ 3).eval 1 / (curveCharTwoOne.ΨSq 3).eval 1) y'),
      ((3 : ℕ) • Point.some 1 0 nonsingular_curveCharTwoOne : curveCharTwoOne.Point)
        = .some _ y' h' := by
  have H := nsmul_eq_some_Φ_div_ΨSq_of_forall_ψ_ne_zero nonsingular_curveCharTwoOne (n := 3)
    (by norm_num) fun k hk hk3 => ψ_ne_zero_curveCharTwoOne k hk (by exact_mod_cast hk3)
  exact_mod_cast H

/-- `a ≠ 0 → a = 1` in `ZMod 2`, by `decide` over the two elements. -/
private lemma eq_one_of_ne_zero_zmod_two {a : ZMod 2} (h : a ≠ 0) : a = 1 := by
  revert h; revert a; decide

/-- **`divX₂(1) = 0` on `curveCharTwoOne`.**  `Φ₂(1) = 1·ψ₂(1, 0)² − ψ₃(1, 0)·ψ₁(1, 0)` by
`Φ_eval_eq_of_equation`, and all three values are `1`, so the numerator is `1 − 1 = 0`;
`ΨSq₂(1) = ψ₂(1, 0)² = 1`.  ⚠️ **No division polynomial is evaluated by `decide` here** — `ψ₃(1, 0)`
comes from `ψ_three_evalEval_ne_zero_curveCharTwoOne`, where `≠ 0` upgrades to `= 1` because the
field has two elements. -/
theorem divX_two_curveCharTwoOne : curveCharTwoOne.divX 1 2 = 0 := by
  have hψ2 : (curveCharTwoOne.ψ 2).evalEval 1 0 = 1 := evalEval_ψ_two_curveCharTwoOne
  have hψ3 : (curveCharTwoOne.ψ 3).evalEval 1 0 = 1 :=
    eq_one_of_ne_zero_zmod_two ψ_three_evalEval_ne_zero_curveCharTwoOne
  have hΨSq : (curveCharTwoOne.ΨSq 2).eval 1 = 1 := by
    rw [← ψ_sq_evalEval equation_curveCharTwoOne 2, hψ2, one_pow]
  have hΦ := Φ_eval_eq_of_equation (W := curveCharTwoOne) equation_curveCharTwoOne 2
  rw [show (2 : ℤ) + 1 = 3 by ring, show (2 : ℤ) - 1 = 1 by ring, ψ_one_evalEval, hψ2,
    hψ3] at hΦ
  rw [divX, hΦ, hΨSq, div_one]
  decide

/-- The chord slope between `2 • (1, 0) = (0, 1)` and `(1, 0)`, in `ZMod 2`. -/
private lemma slope_zero_one_curveCharTwoOne : curveCharTwoOne.slope 0 1 1 0 = 1 := by
  rw [slope_of_X_ne (by decide : (0 : ZMod 2) ≠ 1),
    show ((1 : ZMod 2) - 0) = 1 by decide, show ((0 : ZMod 2) - 1) = 1 by decide, div_one]

/-- The group law's `x`-coordinate at that chord. -/
private lemma addX_zero_one_curveCharTwoOne : curveCharTwoOne.addX 0 1 1 = 1 := by
  simp only [addX, curveCharTwoOne]
  decide

/-- The group law's `y`-coordinate at that chord. -/
private lemma addY_zero_one_curveCharTwoOne : curveCharTwoOne.addY 0 1 1 1 = 1 := by
  simp only [addY, negAddY, negY, addX, curveCharTwoOne]
  decide

/-- ⚠️⚠️ **Both index-`3` coordinates evaluated in characteristic `2`: `divX₃(1) = 1` and
`divYω₃(1, 0) = 1`.**

The route is the group law and not a division-polynomial computation: `2 • (1, 0)` is
`(divX₂(1), divYω₂(1, 0)) = (0, 1)` by `nsmulEqDivω_two_curveCharTwoOne` with
`divX_two_curveCharTwoOne` and `divYω_two_curveCharTwoOne`, `3 • P = 2 • P + P` by `add_zsmul`, and
`Point.add_of_X_ne` then reads both coordinates off `addX`/`addY` at `(0, 1) + (1, 0)` — which
`nsmulEqDivω_three_curveCharTwoOne` identifies with `(divX₃(1), divYω₃(1, 0))`.

⚠️ **`divYω₃(1, 0) = 1 ≠ 0` is the sharp half**, and it is what no `h2`-bound statement of this tree
can produce: `divY₃(1, 0) = 0` identically in characteristic `2`
(`EllipticCurves.Torsion.NsmulLadderOmega`'s `divY_eq_zero_of_two_eq_zero`). -/
theorem divX_divYω_three_curveCharTwoOne :
    curveCharTwoOne.divX 1 3 = 1 ∧ curveCharTwoOne.divYω 1 0 3 = 1 := by
  obtain ⟨h2', e2⟩ := nsmulEqDivω_two_curveCharTwoOne
  obtain ⟨h3', e3⟩ := nsmulEqDivω_three_curveCharTwoOne
  have hxne : curveCharTwoOne.divX 1 2 ≠ 1 := by rw [divX_two_curveCharTwoOne]; decide
  have hadd : ((3 : ℤ) • Point.some 1 0 nonsingular_curveCharTwoOne : curveCharTwoOne.Point)
      = (2 : ℤ) • Point.some 1 0 nonsingular_curveCharTwoOne
        + Point.some 1 0 nonsingular_curveCharTwoOne := by
    rw [show (3 : ℤ) = 2 + 1 by ring, add_zsmul, one_zsmul]
  rw [e3, e2, Point.add_of_X_ne hxne, Point.some.injEq] at hadd
  rw [divX_two_curveCharTwoOne, divYω_two_curveCharTwoOne, slope_zero_one_curveCharTwoOne,
    addX_zero_one_curveCharTwoOne, addY_zero_one_curveCharTwoOne] at hadd
  exact hadd

/-- `negY 1 0 = 1` on `curveCharTwoOne`: `a₁ = 1` and `a₃ = 0`, so `−0 − 1 − 0 = −1 = 1`. -/
private lemma negY_one_zero_curveCharTwoOne : curveCharTwoOne.negY 1 0 = 1 := by
  simp only [negY, curveCharTwoOne]
  decide

/-- ⚠️⚠️ **`3 • (1, 0) = −(1, 0)` on `y² + xy = x³ + 1` over `ZMod 2`, read off the `ω` ladder.**

The point therefore has order `4`, and the whole chain of this file is exercised to produce it:
`hasStepOmega 2`, `addY_divYω_eq` at `n = 2` in a field where `2 = 0`,
`nsmulEqDivω_step_general`, and the two base cases of
`EllipticCurves.Torsion.NsmulLadderOmega`.  ⚠️ **No `(2 : F) ≠ 0`-bound statement of this tree can
state it**, let alone prove it. -/
theorem nsmul_three_eq_neg_curveCharTwoOne :
    ((3 : ℤ) • Point.some 1 0 nonsingular_curveCharTwoOne : curveCharTwoOne.Point)
      = -Point.some 1 0 nonsingular_curveCharTwoOne := by
  obtain ⟨h3', e3⟩ := nsmulEqDivω_three_curveCharTwoOne
  obtain ⟨hX, hY⟩ := divX_divYω_three_curveCharTwoOne
  rw [e3, Point.neg_some, Point.some.injEq]
  exact ⟨hX, by rw [hY, negY_one_zero_curveCharTwoOne]⟩

/-- ⚠️⚠️ **The halved ladder is FALSE at `n = 3` at this point**, so the `ω` ladder is not a
re-statement of it there: the two predicates pin the same `x` and name different `y`, and in
characteristic `2` the halved one names `0` while the true `y`-coordinate is `1`.

⚠️ `EllipticCurves.Torsion.NsmulLadderOmega` already refutes `NsmulEqDiv` at `n = 2` on this curve
(`not_nsmulEqDiv_two_curveCharTwoOne`); what is new here is the **odd** index, which only the step
reaches. -/
theorem not_nsmulEqDiv_three_curveCharTwoOne :
    ¬ NsmulEqDiv nonsingular_curveCharTwoOne (3 : ℤ) := by
  rintro ⟨h', e⟩
  obtain ⟨h3', e3⟩ := nsmulEqDivω_three_curveCharTwoOne
  have hcoord := (Point.some.injEq _ _ _ _ _ _).mp (e3.symm.trans e)
  have hdivY : curveCharTwoOne.divY 1 0 3 = 0 :=
    divY_eq_zero_of_two_eq_zero (by decide) 3
  have hdivYω : curveCharTwoOne.divYω 1 0 3 = 1 := divX_divYω_three_curveCharTwoOne.2
  rw [hdivY, hdivYω] at hcoord
  exact absurd hcoord.2 (by decide)

end Nonvacuity

end Affine
end WeierstrassCurve
