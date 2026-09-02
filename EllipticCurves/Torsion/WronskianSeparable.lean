/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import EllipticCurves.Torsion.OddTorsionCount

/-!
# `#E[n] = n²` at odd `n`, reduced to one Wronskian identity and one coprimality

Issue `#1506`.  `EllipticCurves.Torsion.OddTorsionCount` proves that over an algebraically closed
field of characteristic `≠ 2`, at an odd `n` with `char F ∤ n`,

```
#E[n] = n²   ↔   Separable (preΨₙ),
```

so the last gate on the `p`-primary tower (`EllipticCurves.Torsion.PrimaryTower`, `#1490` item 3)
is the separability of one univariate polynomial.  **This file discharges that gate from two
inputs, neither of which mentions torsion, points, or the group law.**

## The two inputs

* the **Wronskian identity** — this is `[n]∗ω = nω` on the invariant differential, written in
  `F[X]` with no differentials:

  ```
  Φₙ′ · ΨSqₙ  −  Φₙ · ΨSqₙ′  =  n · preΨₙ · preΩₙ ;
  ```

* `IsCoprime (preΨₙ) (preΩₙ)`.

⚠️ **Neither is proved here, and this file is not a proof of `#E[n] = n²`.**  It is the assembly,
in the idiom of `WeierstrassCurve.Affine.nonempty_torsionPow_addEquiv_of_card`
(`EllipticCurves.Torsion.PrimaryTowerAlgClosed`): one signature from which a reader can see the
whole of what is owed.  `#1506` records the route to each input, and the evidence for both.

## Why those two inputs suffice, in three lines

`Separable p` **is** `IsCoprime p p′`.  At odd `n` the parity branch of `ΨSqₙ` is trivial, so
`ΨSqₙ = preΨₙ²` and the identity divides by `preΨₙ` — which is nonzero because `char F ∤ n` — to

```
Φₙ′ · preΨₙ  −  2 · Φₙ · preΨₙ′  =  n · preΩₙ .
```

A Bézout certificate for `(preΨₙ, preΩₙ)` therefore becomes one for `(preΨₙ, preΨₙ′)` after
substituting `preΩₙ = n⁻¹·(Φₙ′·preΨₙ − 2Φₙ·preΨₙ′)`, and `n⁻¹` exists exactly because
`(n : F) ≠ 0`.

⚠️ **`(n : F) ≠ 0` is spent in exactly one place and that is the point.**  It is the only step that
can fail, and it must be able to fail: in characteristic `p` the conclusion `#E[p] = p²` is false.
A route that did not consume the hypothesis there would be proving something untrue.

## Main statements

⚠️ Every public declaration of this file is listed.

* `WeierstrassCurve.Affine.separable_preΨ_of_wronskian` : `Separable (preΨₙ)` from the two inputs.
  Over any field with `char F ∤ n`; **no** algebraic closure, **no** `[W.IsElliptic]`, and
  **nothing about `(2 : F)`**.
* `WeierstrassCurve.Affine.card_torsion_eq_sq_of_wronskian` : `#E[n] = n²`, the same two inputs
  plus what `card_torsion_eq_sq_iff_separable_preΨ` itself asks — `[IsAlgClosed F]`,
  `[W.IsElliptic]` and `(2 : F) ≠ 0`.
* `WeierstrassCurve.Affine.ψ_add_mul_ψ_sub_of_ψ_eq_zero` : `ψ_{n+q}·ψ_{n−q} = −Φₙ(x)·ΨSq_q(x)` at a
  point where `ψₙ` vanishes, at every `q`.  ⚠️ Merged content, repackaged: it is
  `ψ_add_mul_ψ_sub_evalEval` with one term killed.
* `WeierstrassCurve.Affine.eval_preΩ_ne_zero_of_eval_preΨ_eq_zero` and
  `WeierstrassCurve.Affine.isCoprime_preΨ_preΩ` : the **second** input reduced to a single pointwise
  identity `hpair`, spending three merged facts on the way.
* `WeierstrassCurve.Affine.card_torsion_eq_sq_of_wronskian_of_pair` : both reductions composed —
  `#E[n] = n²` from two equations and nothing else.

⚠️ So the gate is **two identities**, not a research programme: the Wronskian one, and `hpair`.

⚠️ The hypothesis gap between the two is real and is worth reading off the signatures: separability
of `preΨₙ` is a statement about one polynomial over any field, while turning it into a point count
needs the curve to be elliptic and the field to be closed.  The Wronskian identity is asked for
only at the single index `n`, not at every index.

## What is *not* here

* **No proof of either input.**  `#1506` scope items 1 and 2.
* **Nothing at even `n`.**  `card_torsion_eq_sq_iff_separable_preΨ` is odd-`n` only, and the
  division by `preΨₙ` above uses `ΨSqₙ = preΨₙ²`, which is the odd branch.
* **Nothing about `#1184`'s arbitrary-ring coprimality**, `#403`/`#405`, or the function field.
  ⚠️ In particular this is **not** the fibre route: `card_fibre_comapProjPointN_projPointOfPoint`
  (`EllipticCurves.FunctionField.MulByNFibre`) computes its `n²` *from* `card_torsion_eq_sq_of_
  smooth`, so it cannot supply this count without circularity.
* **No change to `PrimaryTower`'s gate list or to `#293`.**  Those record `#E[p] = p²` as open, and
  it is open: this file only renames what is owed.

## References

* [J. H. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.4.10, III.5.3 (the
  invariant differential and `[n]∗ω = nω`) and III.6 Cor 6.4.
-/

open Polynomial

namespace WeierstrassCurve.Affine

variable {F : Type*} [Field F] {W : Affine F}

/-- **`preΨₙ` is separable**, at an odd `n` invertible in `F`, given the Wronskian identity and the
coprimality of `preΨₙ` with `preΩₙ`.

⚠️ Read the hypotheses as the statement: the mathematics is `hid` and `hcop`, and everything below
is the Bézout bookkeeping.  See `#1506` for what is known about each.

`hid` is `[n]∗ω = nω` cleared of denominators; `hcop` says `preΨₙ` and `preΩₙ` have no common
factor, equivalently — since `preΨ₂ₙ = preΨₙ·preΩₙ` — that no root of `preΨₙ` is a repeated root of
`preΨ₂ₙ` for that reason. -/
theorem separable_preΨ_of_wronskian {n : ℕ} (hodd : Odd n) (hn : (n : F) ≠ 0)
    (hid : derivative (W.Φ (n : ℤ)) * W.ΨSq (n : ℤ) -
        W.Φ (n : ℤ) * derivative (W.ΨSq (n : ℤ)) =
      (n : F[X]) * W.preΨ (n : ℤ) * W.preΩ (n : ℤ))
    (hcop : IsCoprime (W.preΨ (n : ℤ)) (W.preΩ (n : ℤ))) :
    (W.preΨ (n : ℤ)).Separable := by
  have hcast : (((n : ℤ)) : F) ≠ 0 := by push_cast; exact hn
  have hp0 : W.preΨ (n : ℤ) ≠ 0 := W.preΨ_ne_zero (R := F) hcast
  -- at an odd index the parity branch of `ΨSq` is trivial
  have hoddZ : Odd ((n : ℤ)) := by exact_mod_cast hodd
  have hsq : W.ΨSq (n : ℤ) = W.preΨ (n : ℤ) ^ 2 := by
    rw [WeierstrassCurve.ΨSq, if_neg (Int.not_even_iff_odd.mpr hoddZ), mul_one]
  -- divide the identity by `preΨₙ`
  have hdiv : derivative (W.Φ (n : ℤ)) * W.preΨ (n : ℤ) -
      2 * W.Φ (n : ℤ) * derivative (W.preΨ (n : ℤ)) = (n : F[X]) * W.preΩ (n : ℤ) := by
    refine mul_left_cancel₀ hp0 ?_
    rw [hsq] at hid
    simp only [derivative_pow, Nat.cast_ofNat, map_ofNat] at hid ⊢
    linear_combination hid
  -- turn a Bézout certificate for `(preΨₙ, preΩₙ)` into one for `(preΨₙ, preΨₙ′)`
  obtain ⟨u, v, huv⟩ := hcop
  refine (separable_def' _).2 ⟨u + v * C ((n : F)⁻¹) * derivative (W.Φ (n : ℤ)),
    -(2 * v * C ((n : F)⁻¹) * W.Φ (n : ℤ)), ?_⟩
  have hC : C ((n : F)⁻¹) * (n : F[X]) = 1 := by
    rw [← C_eq_natCast, ← C_mul, inv_mul_cancel₀ hn, C_1]
  linear_combination huv + v * C ((n : F)⁻¹) * hdiv + v * W.preΩ (n : ℤ) * hC

/-- **`#E[n] = n²` at odd `n`** — `#1490`'s remaining gate, reduced to the Wronskian identity and
the `preΨₙ`/`preΩₙ` coprimality.

⚠️ This is not a proof that `#E[n] = n²`; it is the statement that those two polynomial facts are
all that stands between `main` and it.  The `↔` of
`WeierstrassCurve.Affine.card_torsion_eq_sq_iff_separable_preΨ` also says there is no cheaper
substitute: any proof of this conclusion proves `preΨₙ` separable. -/
theorem card_torsion_eq_sq_of_wronskian [DecidableEq F] [IsAlgClosed F] [W.IsElliptic]
    (h2 : (2 : F) ≠ 0) {n : ℕ}
    (hodd : Odd n) (hn : (n : F) ≠ 0)
    (hid : derivative (W.Φ (n : ℤ)) * W.ΨSq (n : ℤ) -
        W.Φ (n : ℤ) * derivative (W.ΨSq (n : ℤ)) =
      (n : F[X]) * W.preΨ (n : ℤ) * W.preΩ (n : ℤ))
    (hcop : IsCoprime (W.preΨ (n : ℤ)) (W.preΩ (n : ℤ))) :
    Nat.card (W.torsion n) = n ^ 2 :=
  (card_torsion_eq_sq_iff_separable_preΨ h2 hodd hn).2
    (separable_preΨ_of_wronskian hodd hn hid hcop)

/-! ## Reducing the second input to one pointwise identity

`IsCoprime (preΨₙ) (preΩₙ)` is not a fresh front: everything it needs is on `main` **except** one
equation.  This section spends the merged facts and leaves that equation exposed.
-/

variable {x y : F}

/-- **`ψ_{n+q}·ψ_{n−q} = −Φₙ(x)·ΨSq_q(x)` at a point where `ψₙ` vanishes**, at every `q`.

`WeierstrassCurve.Affine.ψ_add_mul_ψ_sub_evalEval` (`EllipticCurves.Torsion.XDifference`) reads
`ψ_{p+q}ψ_{p−q} = Φ_q·ΨSq_p − Φ_p·ΨSq_q`; at `p = n` the first term dies because `ΨSqₙ(x)` is
`ψₙ(x, y)²`.  ⚠️ The right-hand side does not involve `y`, so the product `ψ_{n+q}·ψ_{n−q}` is
constant on the `y`-fibre — that is what makes `q = 1` and `q = 2` below into non-vanishing
statements about `x` alone. -/
theorem ψ_add_mul_ψ_sub_of_ψ_eq_zero (h : W.Equation x y) {n : ℤ}
    (hz : (W.ψ n).evalEval x y = 0) (q : ℤ) :
    (W.ψ (n + q)).evalEval x y * (W.ψ (n - q)).evalEval x y =
      -((W.Φ n).eval x * (W.ΨSq q).eval x) := by
  have hsq : (W.ΨSq n).eval x = 0 := by rw [← ψ_sq_evalEval h n, hz]; ring
  rw [ψ_add_mul_ψ_sub_evalEval h n q, hsq]
  ring

/-- **`preΩₙ` does not vanish at a root of `preΨₙ`** — scope item 2 of `#1506`, reduced to `hpair`.

Everything except `hpair` is merged.  ⚠️ Read the proof as a budget: `Φₙ(x) ≠ 0` is
`eval_Φ_ne_zero_of_eval_ΨSq_eq_zero` (`EllipticCurves.Torsion.TwoTorsionOrder`, PR #569) and
`Ψ₂Sq(x) ≠ 0` is `eval_Ψ₂Sq_ne_zero_of_eval_preΨ_eq_zero` (`EllipticCurves.Torsion.OddTorsionCount`,
PR #574); together with `ψ_add_mul_ψ_sub_of_ψ_eq_zero` at `q = 1` and `q = 2` they give
`ψ_{n−1}(x, y) ≠ 0` and `ψ_{n+2}(x, y) ≠ 0`.  `hpair` then collapses `Ωₙ` to `2·ψ_{n+2}·ψ_{n−1}²`,
and `WeierstrassCurve.Ω_factor` divides out the `ψ₂²`.

⚠️ `hpair` is **not** proved and is the whole content.  It says the two summands of `Ωₙ` are
negatives of one another at a point where `ψₙ` vanishes; equivalently, since their product is
`Φₙ³·Ψ₂Sq` by the two instances above, that `(ψ_{n+2}·ψ_{n−1}²)² = Φₙ³·Ψ₂Sq`.  ⚠️ It is **not** a
consequence of `ψ_add_mul_ψ_sub` alone: that relation determines `ψ_{n+k}·ψ_{n−k}` for each `k` and
says nothing relating different `k`, which is exactly what `hpair` needs. -/
theorem eval_preΩ_ne_zero_of_eval_preΨ_eq_zero [IsAlgClosed F] [W.IsElliptic] (h2 : (2 : F) ≠ 0)
    {n : ℕ} (hodd : Odd n) (hn : n ≠ 0)
    (hpair : ∀ x y : F, W.Equation x y → (W.ψ (n : ℤ)).evalEval x y = 0 →
      (W.ψ ((n : ℤ) + 2)).evalEval x y * (W.ψ ((n : ℤ) - 1)).evalEval x y ^ 2 =
        -((W.ψ ((n : ℤ) - 2)).evalEval x y * (W.ψ ((n : ℤ) + 1)).evalEval x y ^ 2))
    {x : F} (hx : (W.preΨ (n : ℤ)).eval x = 0) :
    (W.preΩ (n : ℤ)).eval x ≠ 0 := by
  obtain ⟨y, hxy⟩ := exists_equation (W := W) h2 x
  have hΨSq : (W.ΨSq (n : ℤ)).eval x = 0 := by
    rw [ΨSq_natCast_eq_sq_of_odd hodd, eval_pow, hx, zero_pow (two_ne_zero (α := ℕ))]
  have hψn : (W.ψ (n : ℤ)).evalEval x y = 0 :=
    pow_eq_zero_iff (n := 2) (by norm_num) |>.mp (by rw [ψ_sq_evalEval hxy, hΨSq])
  have hΦ : (W.Φ (n : ℤ)).eval x ≠ 0 := eval_Φ_ne_zero_of_eval_ΨSq_eq_zero h2 hn x hΨSq
  have hΨ₂ : W.Ψ₂Sq.eval x ≠ 0 := eval_Ψ₂Sq_ne_zero_of_eval_preΨ_eq_zero h2 hodd hx
  -- `ψ_{n−1}(x, y) ≠ 0` and `ψ_{n+2}(x, y) ≠ 0`
  have h1 := ψ_add_mul_ψ_sub_of_ψ_eq_zero hxy hψn 1
  rw [WeierstrassCurve.ΨSq_one, eval_one, mul_one] at h1
  have hm1 : (W.ψ ((n : ℤ) - 1)).evalEval x y ≠ 0 := fun hc => hΦ (by
    rw [hc, mul_zero] at h1; simpa using h1.symm)
  have h2' := ψ_add_mul_ψ_sub_of_ψ_eq_zero hxy hψn 2
  rw [WeierstrassCurve.ΨSq_two] at h2'
  have hp2 : (W.ψ ((n : ℤ) + 2)).evalEval x y ≠ 0 := fun hc => (mul_ne_zero hΦ hΨ₂) (by
    rw [hc, zero_mul] at h2'; simpa using h2'.symm)
  -- `Ωₙ` collapses, and `Ω_factor` divides out the `ψ₂²`
  have hfac := congrArg (Polynomial.evalEval x y) (W.Ω_factor (n : ℤ))
  rw [if_neg (Int.not_even_iff_odd.mpr (by exact_mod_cast hodd : Odd ((n : ℤ))))] at hfac
  simp only [evalEval_mul, evalEval_sub, evalEval_pow, evalEval_C, ← ψ_evalEval hxy] at hfac
  intro hΩ
  rw [hΩ, mul_zero] at hfac
  exact mul_ne_zero (mul_ne_zero h2 hp2) (pow_ne_zero 2 hm1) (by
    linear_combination hfac + hpair x y hxy hψn)

/-- **`IsCoprime (preΨₙ) (preΩₙ)`** over an algebraically closed field, from `hpair`.

The descent is the same one PR #576 used for `isCoprime_ΨSq_adjacent` —
`Polynomial.isCoprime_iff_aeval_ne_zero_of_isAlgClosed` — and it is trivial here because the base
field is already closed, so no `AlgebraicClosure F` transport is needed. -/
theorem isCoprime_preΨ_preΩ [IsAlgClosed F] [W.IsElliptic] (h2 : (2 : F) ≠ 0) {n : ℕ}
    (hodd : Odd n) (hn : n ≠ 0)
    (hpair : ∀ x y : F, W.Equation x y → (W.ψ (n : ℤ)).evalEval x y = 0 →
      (W.ψ ((n : ℤ) + 2)).evalEval x y * (W.ψ ((n : ℤ) - 1)).evalEval x y ^ 2 =
        -((W.ψ ((n : ℤ) - 2)).evalEval x y * (W.ψ ((n : ℤ) + 1)).evalEval x y ^ 2)) :
    IsCoprime (W.preΨ (n : ℤ)) (W.preΩ (n : ℤ)) := by
  refine (Polynomial.isCoprime_iff_aeval_ne_zero_of_isAlgClosed (K := F) _ _ _).mpr fun a => ?_
  simp only [aeval_def, eval₂_eq_eval_map, Algebra.algebraMap_self, Polynomial.map_id]
  by_cases hp : (W.preΨ (n : ℤ)).eval a = 0
  · exact Or.inr (eval_preΩ_ne_zero_of_eval_preΨ_eq_zero h2 hodd hn hpair hp)
  · exact Or.inl hp

/-- **`#E[n] = n²` at odd `n` from two equations** — the two reductions of this file composed.

⚠️ This is a statement about what is owed, not a proof of its conclusion.  Read the two hypotheses:
`hid` is `[n]∗ω = nω` in `F[X]`, and `hpair` says the two summands of `Ωₙ` are negatives at a point
where `ψₙ` vanishes.  `#1506` scope items 1 and 2. -/
theorem card_torsion_eq_sq_of_wronskian_of_pair [DecidableEq F] [IsAlgClosed F] [W.IsElliptic]
    (h2 : (2 : F) ≠ 0) {n : ℕ} (hodd : Odd n) (hn : (n : F) ≠ 0) (hn0 : n ≠ 0)
    (hid : derivative (W.Φ (n : ℤ)) * W.ΨSq (n : ℤ) -
        W.Φ (n : ℤ) * derivative (W.ΨSq (n : ℤ)) =
      (n : F[X]) * W.preΨ (n : ℤ) * W.preΩ (n : ℤ))
    (hpair : ∀ x y : F, W.Equation x y → (W.ψ (n : ℤ)).evalEval x y = 0 →
      (W.ψ ((n : ℤ) + 2)).evalEval x y * (W.ψ ((n : ℤ) - 1)).evalEval x y ^ 2 =
        -((W.ψ ((n : ℤ) - 2)).evalEval x y * (W.ψ ((n : ℤ) + 1)).evalEval x y ^ 2)) :
    Nat.card (W.torsion n) = n ^ 2 :=
  card_torsion_eq_sq_of_wronskian h2 hodd hn hid (isCoprime_preΨ_preΩ h2 hodd hn0 hpair)

end WeierstrassCurve.Affine

/-! ## ⚠️ Non-vacuity of the Wronskian hypothesis, and a measurement of what proving it costs

`hid` is an implication's hypothesis, so it is worth knowing that it is **not** vacuous.  It is
proved outright below at `n = 1` and `n = 2`, by expanding both sides.

⚠️ **And the measurement, which is the more useful half.**  The same script at `n = 3` — the first
index where `Φₙ` and `ΨSqₙ` are not small — **exceeds `maxRecDepth` inside the `C`-normalisation,
before `ring` is even reached**, in 20 s.  Raising `maxRecDepth` is a `set_option` and this
development does not use them.  So `#1506` scope item 1 cannot be done index by index and cannot be
done by expansion: it needs the `normEDS` induction or the universal-curve route, and a worker who
starts by trying `n = 5` directly will only rediscover this.
-/

namespace WeierstrassCurve

open Polynomial

local macro "C_simp" : tactic =>
  `(tactic| simp only [map_ofNat, C_0, C_1, C_neg, C_add, C_sub, C_mul, C_pow])

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R)

/-- The Wronskian identity at `n = 1`, over an arbitrary commutative ring.  `Φ₁ = X`, `ΨSq₁ = 1`
and `preΩ₁ = 1`, so both sides are `1`. -/
example : derivative (W.Φ 1) * W.ΨSq 1 - W.Φ 1 * derivative (W.ΨSq 1)
    = (1 : R[X]) * W.preΨ 1 * W.preΩ 1 := by
  have h : W.preΩ 1 = 1 := by
    rw [preΩ, show (1 : ℤ) + 2 = 3 by norm_num, show (1 : ℤ) - 1 = 0 by norm_num,
      show (1 : ℤ) - 2 = -1 by norm_num, show (1 : ℤ) + 1 = 2 by norm_num, preΨ_zero, preΨ_two,
      preΨ_neg, preΨ_one]
    ring
  rw [Φ_one, ΨSq_one, preΨ_one, h]
  simp

/-- The Wronskian identity at `n = 2`, over an arbitrary commutative ring — `Φ₂′·Ψ₂Sq −
Φ₂·Ψ₂Sq′ = 2·preΨ₄`, both sides expanded in the `bᵢ`.  ⚠️ This is the first index that is not
formal, and it is the last one that expands within the default `maxRecDepth`. -/
example : derivative (W.Φ 2) * W.ΨSq 2 - W.Φ 2 * derivative (W.ΨSq 2)
    = (2 : R[X]) * W.preΨ 2 * W.preΩ 2 := by
  rw [Φ_two, ΨSq_two, preΨ_two, preΩ_two, Ψ₂Sq, preΨ₄, b₂, b₄, b₆, b₈]
  simp only [derivative_sub, derivative_add, derivative_mul, derivative_pow, derivative_X,
    derivative_C, Nat.cast_ofNat]
  C_simp
  push_cast
  ring

end WeierstrassCurve
