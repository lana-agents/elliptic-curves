/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import EllipticCurves.Torsion.OmegaUniversal
import EllipticCurves.Torsion.OmegaPairCoprime
import Mathlib.RingTheory.Polynomial.Wronskian

/-!
# The Wronskian identity is a statement about one curve over one characteristic-`0` domain

`EllipticCurves.Torsion.WronskianSeparable` reduces `#E[n] = n²` at odd `n` — `#1490` item 3, the
last gate on the `p`-primary tower — to two inputs, and `EllipticCurves.Torsion.OmegaPairCoprime`
discharges the second, so exactly one is still open (`#1506` scope item 1):

```
derivative (W.Φ n) * W.ΨSq n - W.Φ n * derivative (W.ΨSq n) = n * W.preΨ n * W.preΩ n   in R[X].
```

That is `[n]∗ω = nω` on the invariant differential, cleared of denominators, and as stated it is
quantified over **every** commutative ring and **every** `W : WeierstrassCurve R`.  **This file
shows it does not have to be.**  Every ingredient — `Φ`, `ΨSq`, `preΨ`, `preΩ`, and `derivative` —
commutes with base change, so the identity transports along any ring homomorphism and *descends*
along any injective one; base changing the universal curve `WeierstrassCurve.univ` along
`W.specialize` recovers `W`.  Hence

**`HasWronskianId n` for one explicit curve over one explicit characteristic-`0` domain implies it
for all of them** (`hasWronskianId_of_univQ`).

This is `EllipticCurves.Torsion.OmegaUniversal`'s reduction for `HasPreΩSq`, run again for the one
identity that is still owed; the two files are deliberately parallel and share `univ`, `univQ` and
`specialize`.

⚠️ **Nothing here proves the identity at a general index.**  This file changes where it has to be
proved, not whether it is proved, and `#1506` item 1 is exactly as open as it was.  What the
reduction buys is recorded below.

## What the reduction buys

`WronskianSeparable` measures that the identity **cannot be done index by index**: at `n = 3` the
expansion exceeds `maxRecDepth` inside the `C`-normalisation before `ring` is reached, and this
development uses no `set_option`.  So the identity has to be proved by an argument that is uniform
in `n`, and every such argument known to this tree wants a base with more structure than a bare
`CommRing`:

* `MvPolynomial (Fin 5) ℚ` is an **integral domain**, so an equation `a * b = a * c` with `a ≠ 0`
  may be cancelled — and `preΨ n ≠ 0` is available there for every `n ≠ 0`
  (`WeierstrassCurve.preΨ_ne_zero`, whose hypothesis `(n : R) ≠ 0` is free in characteristic `0`).
  Every route below divides by some `ΨSqₙ`;
* it has **characteristic `0`**, so `2`, `3` and every index `n` are invertible in its fraction
  field.  ⚠️ That is not a way of dodging the characteristic-`p` obstruction to `#E[p] = p²`: the
  identity is *true* in characteristic `p`, and it is `separable_preΨ_of_wronskian` — not this
  identity — that spends `(n : F) ≠ 0`;
* it is an infinite domain with an algebraically closed field above it, so a polynomial identity may
  be proved by evaluating at cofinitely many points and appealing to `Polynomial.funext`.
  `EllipticCurves.Torsion.OmegaCharZero` already runs that pattern on top of `OmegaUniversal`.

## Main results

⚠️ Every public declaration of this file is listed.

* `WeierstrassCurve.HasWronskianId` : the identity at index `n`, as a `Prop` about one curve.
* `WeierstrassCurve.hasWronskianId_iff_wronskian` : it is `Polynomial.wronskian (ΨSqₙ) (Φₙ)`, so
  Mathlib's Wronskian API applies to it verbatim.
* `WeierstrassCurve.HasWronskianId.map` : the identity transports along any `f : R →+* S`.
* `WeierstrassCurve.hasWronskianId_of_map` : it descends along any **injective** `f`.
* `WeierstrassCurve.hasWronskianId_of_univ`, `WeierstrassCurve.hasWronskianId_of_univQ` : the
  reduction, to `univ` and to the characteristic-`0` `univQ`.
* `WeierstrassCurve.forall_hasWronskianId_iff_univ` : the reduction is lossless.
* `WeierstrassCurve.hasWronskianId_neg` : the identity at `-n` **is** the identity at `n`, so a
  proof may assume `0 ≤ n`.
* `WeierstrassCurve.hasWronskianId_zero`, `hasWronskianId_one`, `hasWronskianId_two` : the three
  indices that are known, over an arbitrary commutative ring.  ⚠️ `n = 1` and `n = 2` were
  `example`s in `WronskianSeparable` and so unreachable; they are the base cases any induction on
  the `normEDS` recurrences will need, and they are named here for that reason.
* `WeierstrassCurve.hasWronskianId_two_of_univQ` : a non-vacuity check on the chain, not content.
* `WeierstrassCurve.Affine.separable_preΨ_of_univQ` and
  `WeierstrassCurve.Affine.card_torsion_eq_sq_of_univQ` : the payoff — `Separable (preΨₙ)`, and
  `#E[n] = n²` at odd `n`, from the identity **at `univQ` alone**.  ⚠️ The second has no other
  mathematical hypothesis at all: `EllipticCurves.Torsion.OmegaPairCoprime` discharged the companion
  `hpair`, so what is left between this tree and `#1490` item 3 is **one polynomial identity about
  one curve over one ring**.

⚠️ `hasWronskianId_two_of_univQ` proves the long way round something `hasWronskianId_two` already
gives directly.  It exists so that a reduction which failed to recover a known instance would break
the build, and it must not be cited.

## References

* [J. Silverman, *The arithmetic of elliptic curves*][silverman2009], III.5 and Exercise 3.7.
-/

open Polynomial

namespace WeierstrassCurve

variable {R S : Type*} [CommRing R] [CommRing S]

/-! ### The identity as a `Prop` -/

/-- **The Wronskian identity at index `n`**, `[n]∗ω = nω` written in `R[X]`:

```
Φₙ′ · ΨSqₙ  −  Φₙ · ΨSqₙ′  =  n · preΨₙ · preΩₙ .
```

This is verbatim the hypothesis `hid` of
`WeierstrassCurve.Affine.separable_preΨ_of_wronskian`, packaged so that it can be transported
between rings.  ⚠️ By `WeierstrassCurve.preΨ_two_mul` the right-hand side is `n · preΨ₂ₙ`; the
`preΨₙ · preΩₙ` form is the one the consumer wants, because the Bézout step there divides by
`preΨₙ`. -/
def HasWronskianId (W : WeierstrassCurve R) (n : ℤ) : Prop :=
  derivative (W.Φ n) * W.ΨSq n - W.Φ n * derivative (W.ΨSq n) =
    (n : R[X]) * W.preΨ n * W.preΩ n

/-- **The left-hand side is Mathlib's `Polynomial.wronskian`**, in the order `(ΨSqₙ, Φₙ)`:
`wronskian a b = a·b′ − a′·b`, so `wronskian (ΨSqₙ) (Φₙ) = Φₙ′·ΨSqₙ − Φₙ·ΨSqₙ′`.  ⚠️ The other
order differs by a sign. -/
theorem hasWronskianId_iff_wronskian {W : WeierstrassCurve R} {n : ℤ} :
    W.HasWronskianId n ↔
      wronskian (W.ΨSq n) (W.Φ n) = (n : R[X]) * W.preΨ n * W.preΩ n := by
  unfold HasWronskianId Polynomial.wronskian
  constructor <;> intro h <;> linear_combination h

/-! ### Base change in both directions -/

/-- **The identity transports along any ring homomorphism.**  Every ingredient commutes with base
change — `map_Φ` / `map_ΨSq` / `map_preΨ` in Mathlib, `map_preΩ` in
`EllipticCurves.Torsion.OmegaDivisionPolynomial`, and `Polynomial.derivative_map` for the
derivative — so applying `Polynomial.map f` to both sides is the whole proof. -/
theorem HasWronskianId.map {W : WeierstrassCurve R} {n : ℤ} (h : W.HasWronskianId n) (f : R →+* S) :
    (W.map f).HasWronskianId n := by
  have H := congrArg (Polynomial.map f) h
  simpa only [HasWronskianId, map_Φ, map_ΨSq, map_preΨ, map_preΩ, derivative_map,
    Polynomial.map_mul, Polynomial.map_sub, Polynomial.map_intCast] using H

/-- **The identity descends along an injective ring homomorphism.**  `Polynomial.map f` is
injective when `f` is, so an identity that holds after base change already held before it.  This is
what allows the identity to be proved over a ring with better properties than `R` — over
`MvPolynomial (Fin 5) ℚ` rather than `MvPolynomial (Fin 5) ℤ`, say — and then pulled back. -/
theorem hasWronskianId_of_map {W : WeierstrassCurve R} {f : R →+* S} (hf : Function.Injective f)
    {n : ℤ} (h : (W.map f).HasWronskianId n) : W.HasWronskianId n := by
  refine Polynomial.map_injective f hf ?_
  simpa only [HasWronskianId, map_Φ, map_ΨSq, map_preΨ, map_preΩ, derivative_map,
    Polynomial.map_mul, Polynomial.map_sub, Polynomial.map_intCast] using h

/-! ### The reduction to the universal curve -/

/-- **The reduction.**  `HasWronskianId n` for the universal curve gives it for every Weierstrass
curve over every commutative ring, by base change along `W.specialize`. -/
theorem hasWronskianId_of_univ {n : ℤ} (h : univ.HasWronskianId n) (W : WeierstrassCurve R) :
    W.HasWronskianId n := by
  have H := h.map W.specialize
  rwa [univ_map_specialize] at H

/-- **The reduction is lossless**: the universal instance is *equivalent* to the universally
quantified statement, since `univ` is itself one of the curves quantified over.  Stated at `Type`
because that is where `univ` lives; `hasWronskianId_of_univ` is the universe-polymorphic form and is
what consumers should use. -/
theorem forall_hasWronskianId_iff_univ {n : ℤ} :
    (∀ (R : Type) [CommRing R] (W : WeierstrassCurve R), W.HasWronskianId n) ↔
      univ.HasWronskianId n :=
  ⟨fun h => h _ univ, fun h _ _ W => hasWronskianId_of_univ h W⟩

/-- **The reduction, over a characteristic-`0` base.**  `HasWronskianId n` for `univQ` gives it for
every Weierstrass curve over every commutative ring: descend along the injective
`MvPolynomial.map (Int.castRingHom ℚ)` to `univ`, then specialise.  See the module docstring for
what the characteristic-`0` base is worth. -/
theorem hasWronskianId_of_univQ {n : ℤ} (h : univQ.HasWronskianId n) (W : WeierstrassCurve R) :
    W.HasWronskianId n :=
  hasWronskianId_of_univ (hasWronskianId_of_map (MvPolynomial.map_injective _ Int.cast_injective) h)
    W

/-! ### The symmetry in `n`, and the indices that are known -/

/-- **The identity at `-n` is the identity at `n`.**  `Φ` and `ΨSq` and `preΩ` are even in the
index and `preΨ` is odd, so both sides of the identity change sign an even number of times.  An
induction on `n` may therefore assume `0 ≤ n`. -/
theorem hasWronskianId_neg {W : WeierstrassCurve R} {n : ℤ} :
    W.HasWronskianId (-n) ↔ W.HasWronskianId n := by
  simp only [HasWronskianId, Φ_neg, ΨSq_neg, preΨ_neg, preΩ_neg, Int.cast_neg, neg_mul, mul_neg,
    neg_neg]

variable (W : WeierstrassCurve R)

/-- **The identity at `n = 0`.**  `ΨSq₀ = 0` and `preΨ₀ = 0`, so both sides vanish. -/
theorem hasWronskianId_zero : W.HasWronskianId 0 := by
  simp [HasWronskianId, ΨSq_zero, preΨ_zero]

/-- **The identity at `n = 1`.**  `Φ₁ = X`, `ΨSq₁ = 1` and `preΨ₁ = preΩ₁ = 1`, so both sides
are `1`. -/
theorem hasWronskianId_one : W.HasWronskianId 1 := by
  have h : W.preΩ 1 = 1 := by
    rw [preΩ, show (1 : ℤ) + 2 = 3 by norm_num, show (1 : ℤ) - 1 = 0 by norm_num,
      show (1 : ℤ) - 2 = -1 by norm_num, show (1 : ℤ) + 1 = 2 by norm_num, preΨ_zero, preΨ_two,
      preΨ_neg, preΨ_one]
    ring
  rw [HasWronskianId, Φ_one, ΨSq_one, preΨ_one, h]
  simp

/-- **The identity at `n = 2`** — `Φ₂′·Ψ₂Sq − Φ₂·Ψ₂Sq′ = 2·preΨ₄`, both sides expanded in the `bᵢ`.
⚠️ This is the first index that is not formal, and — see `WronskianSeparable` — the last one that
expands within the default `maxRecDepth`. -/
theorem hasWronskianId_two : W.HasWronskianId 2 := by
  rw [HasWronskianId, Φ_two, ΨSq_two, preΨ_two, preΩ_two, Ψ₂Sq, preΨ₄, b₂, b₄, b₆, b₈]
  simp only [derivative_sub, derivative_add, derivative_mul, derivative_pow, derivative_X,
    derivative_C, Nat.cast_ofNat]
  simp only [map_ofNat, C_add, C_sub, C_mul, C_pow]
  push_cast
  ring

/-- **Non-vacuity check on the whole chain.**  `HasWronskianId 2` for an arbitrary `W` over an
arbitrary `CommRing`, recovered from the *single* instance at `univQ` — which exercises
`hasWronskianId_of_map` (descent along `ℤ → ℚ`), `hasWronskianId_of_univ` (specialisation) and
`HasWronskianId.map` (which the latter uses) in one term.

⚠️ **This is a check, not content, and it must not be cited.**  `hasWronskianId_two` above already
proves this for every `W` directly and is strictly the better lemma; this is proved the long way
round precisely so that a reduction which failed to recover a known instance would break the
build. -/
theorem hasWronskianId_two_of_univQ : W.HasWronskianId 2 :=
  hasWronskianId_of_univQ (univQ.hasWronskianId_two) W

end WeierstrassCurve

/-! ### The payoff: `#E[n] = n²` from one identity over one ring -/

namespace WeierstrassCurve.Affine

variable {F : Type*} [Field F] {W : Affine F}

/-- **`Separable (preΨₙ)` from the identity at `univQ` alone.**  The Wronskian hypothesis of
`separable_preΨ_of_wronskian` is discharged for `W` by
`WeierstrassCurve.hasWronskianId_of_univQ`, so what is owed is one instance over one
characteristic-`0` domain. -/
theorem separable_preΨ_of_univQ {n : ℕ} (hodd : Odd n) (hn : (n : F) ≠ 0)
    (h : univQ.HasWronskianId (n : ℤ))
    (hcop : IsCoprime (W.preΨ (n : ℤ)) (W.preΩ (n : ℤ))) :
    (W.preΨ (n : ℤ)).Separable := by
  refine separable_preΨ_of_wronskian hodd hn ?_ hcop
  have H := hasWronskianId_of_univQ h W
  rw [HasWronskianId] at H
  rw [H]
  push_cast
  ring

/-- **`#E[n] = n²` at odd `n`, from the identity at `univQ` and nothing else.**

⚠️ This is not a proof of its conclusion: `h` is `#1506` scope item 1, and it is open.  What the
statement says is that the whole of what is owed is **one polynomial identity about one curve over
one ring** — no quantifier over rings, no quantifier over curves, and, since
`EllipticCurves.Torsion.OmegaPairCoprime` discharged the companion `hpair`, no second hypothesis.
⚠️ `EllipticCurves.Torsion.PrimaryTower`'s gate list and `#293` are unchanged, and must stay so
until `h` is proved. -/
theorem card_torsion_eq_sq_of_univQ [DecidableEq F] [IsAlgClosed F] [W.IsElliptic]
    (h2 : (2 : F) ≠ 0) {n : ℕ} (hodd : Odd n) (hn : (n : F) ≠ 0)
    (h : univQ.HasWronskianId (n : ℤ)) :
    Nat.card (W.torsion n) = n ^ 2 :=
  card_torsion_eq_sq_of_wronskian_identity h2 hodd hn
    (by
      have H := hasWronskianId_of_univQ h W
      rw [HasWronskianId] at H
      rw [H]; push_cast; ring)

end WeierstrassCurve.Affine
