/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import EllipticCurves.Torsion.OmegaOnCurve
import EllipticCurves.UniversalCurve

/-!
# `HasPreΩSq` is a statement about one curve over one characteristic-`0` domain

`EllipticCurves.Torsion.OmegaOnCurve` reduces the on-curve identity for the division-polynomial
coordinates `(Φₙ/ΨSqₙ, ωₙ/ψₙ³)` at general `n` to the single univariate polynomial identity
`WeierstrassCurve.HasPreΩSq n`,

```
preΩₙ² · (if Even n then 1 else Ψ₂Sq) = 4Φₙ³ + b₂Φₙ²ΨSqₙ + 2b₄ΦₙΨSqₙ² + b₆ΨSqₙ³   in R[X],
```

and proves it at `n ∈ {0, ±1, ±2}`.  Establishing it at general `n` was the crux left in `#404`; it
is proved in `EllipticCurves.Torsion.OmegaCrux`, and **this file's reduction is on that route** —
the closing proof reaches an arbitrary commutative ring through `hasPreΩSq_of_univQ` below.

As stated, `HasPreΩSq n` is quantified over **every** commutative ring `R` and **every**
`W : WeierstrassCurve R`.  This file shows it does not have to be.  Every polynomial in it —
`preΩ`, `Φ`, `ΨSq`, `Ψ₂Sq` — commutes with base change, and so do the `bᵢ`, so the identity
transports along any ring homomorphism and *descends* along any injective one.  Base changing the
universal curve `WeierstrassCurve.univ` along `W.specialize` recovers `W`, so:

**`HasPreΩSq n` for one explicit curve over one explicit ring implies it for all of them.**

## Main results

* `WeierstrassCurve.HasPreΩSq.map` : the identity transports along any `f : R →+* S`.
* `WeierstrassCurve.hasPreΩSq_of_map` : it descends along any **injective** `f`.
* `WeierstrassCurve.hasPreΩSq_of_univ` : `univ.HasPreΩSq n → W.HasPreΩSq n`, for every `W` over
  every `CommRing`.
* `WeierstrassCurve.forall_hasPreΩSq_iff_univ` : the reduction is lossless — the universal
  instance is *equivalent* to the universally quantified statement.
* `WeierstrassCurve.hasPreΩSq_of_univQ` : the same from `univQ`, the universal curve with
  **rational** coefficients.
* `WeierstrassCurve.hasPreΩSq_two_of_univQ` : a non-vacuity check on the chain, not new content.

## Why `univQ` and not just `univ`

`MvPolynomial (Fin 5) ℚ` is a characteristic-`0` integral domain in which `2` and `3` are
invertible and whose fraction field is available.  That matters: the division-polynomial
recurrences `preΨ'_even` / `preΨ'_odd` are what any induction on `n` must run through, and several
of their steps divide by `2`.  Over a general `CommRing` that is unavailable and the identity looks
harder than it is; `hasPreΩSq_of_univQ` says the general case costs nothing extra once the
characteristic-`0` case is done.

⚠️ **Nothing here proves the crux.**  This file changes what has to be proved, not whether it is
proved, and `hasPreΩSq_of_univQ univQ.hasPreΩSq_two` reproving `n = 2` everywhere is a non-vacuity
check on the reduction rather than progress on `#404`.

What the reduction is *for* is cashed out one file later.
`EllipticCurves.Torsion.OmegaCharZero` composes it with `Polynomial.funext` and obtains
`WeierstrassCurve.hasPreΩSq_three`: the polynomial identity at `n = 3` over **every** commutative
ring, including where `2 = 0`, out of an evaluated lemma that assumes `(2 : F) ≠ 0` — and with no
new algebra at all.  ⚠️ That is a new *index*, not a new *proof*: `HasPreΩSq` at **general** `n` is
untouched by either file.

⚠️ **The circularity, and how it was avoided.**  The classical proof of this identity identifies
`(Φₙ/ΨSqₙ, ωₙ/ψₙ³)` with the group-law multiple `n • P` and then observes that a point of the curve
satisfies the curve's equation.  That identification is the *other* open statement (`#251`), and
`#251`'s own analysis records that it runs through `ωₙ`, i.e. through this identity; the two look
like faces of one induction.  **They are not.**  `EllipticCurves.Torsion.OmegaCrux` proves the
identity at every `n` with **no group law, no `n • P` and no `#251` input**: the induction is on
the *Vieta defect* of three division-polynomial points, which Ward's elliptic-net relation controls
directly.  ⚠️ `#251` is untouched by that and remains open — what is refuted is the claim that it
has to come first.

## References

* [J. Silverman, *The arithmetic of elliptic curves*][silverman2009], Exercise 3.7, III.6.
-/

open Polynomial

namespace WeierstrassCurve

variable {R S : Type*} [CommRing R] [CommRing S]

/-! ### Base change in both directions -/

/-- **The identity transports along any ring homomorphism.**  Every ingredient of `HasPreΩSq`
commutes with base change — `map_preΩ` here, `map_Φ` / `map_ΨSq` / `map_Ψ₂Sq` and `map_b₂` /
`map_b₄` / `map_b₆` in Mathlib — so applying `Polynomial.map f` to both sides is the whole proof. -/
theorem HasPreΩSq.map {W : WeierstrassCurve R} {n : ℤ} (h : W.HasPreΩSq n) (f : R →+* S) :
    (W.map f).HasPreΩSq n := by
  have H := congrArg (Polynomial.map f) h
  simpa only [HasPreΩSq, map_preΩ, map_Φ, map_ΨSq, map_Ψ₂Sq, WeierstrassCurve.map_b₂,
    WeierstrassCurve.map_b₄, WeierstrassCurve.map_b₆, Polynomial.map_mul, Polynomial.map_pow,
    Polynomial.map_add, Polynomial.map_ofNat, Polynomial.map_C,
    apply_ite (Polynomial.map f), Polynomial.map_one] using H

/-- **The identity descends along an injective ring homomorphism.**  `Polynomial.map f` is
injective when `f` is, so an identity that holds after base change already held before it.  This is
what allows the identity to be proved over a ring with better properties than `R` — over
`MvPolynomial (Fin 5) ℚ` rather than `MvPolynomial (Fin 5) ℤ`, say — and then pulled back. -/
theorem hasPreΩSq_of_map {W : WeierstrassCurve R} {f : R →+* S} (hf : Function.Injective f)
    {n : ℤ} (h : (W.map f).HasPreΩSq n) : W.HasPreΩSq n := by
  refine Polynomial.map_injective f hf ?_
  simpa only [HasPreΩSq, map_preΩ, map_Φ, map_ΨSq, map_Ψ₂Sq, WeierstrassCurve.map_b₂,
    WeierstrassCurve.map_b₄, WeierstrassCurve.map_b₆, Polynomial.map_mul, Polynomial.map_pow,
    Polynomial.map_add, Polynomial.map_ofNat, Polynomial.map_C,
    apply_ite (Polynomial.map f), Polynomial.map_one] using h

/-! ### The reduction to the universal curve -/

/-- **The reduction.**  `HasPreΩSq n` for the universal curve gives it for every Weierstrass curve
over every commutative ring, by base change along `W.specialize`. -/
theorem hasPreΩSq_of_univ {n : ℤ} (h : univ.HasPreΩSq n) (W : WeierstrassCurve R) :
    W.HasPreΩSq n := by
  have H := h.map W.specialize
  rwa [univ_map_specialize] at H

/-- **The reduction is lossless.**  The universal instance is not merely sufficient but equivalent
to the universally quantified statement, since `univ` is itself one of the curves quantified over.
Stated at `Type` because that is where `univ` lives; `hasPreΩSq_of_univ` is the
universe-polymorphic form and is what consumers should use. -/
theorem forall_hasPreΩSq_iff_univ {n : ℤ} :
    (∀ (R : Type) [CommRing R] (W : WeierstrassCurve R), W.HasPreΩSq n) ↔ univ.HasPreΩSq n :=
  ⟨fun h => h _ univ, fun h _ _ W => hasPreΩSq_of_univ h W⟩

/-- The universal Weierstrass curve with **rational** coefficients, `univ` base changed along
`ℤ → ℚ`.  Its coefficient ring `MvPolynomial (Fin 5) ℚ` is a characteristic-`0` integral domain in
which `2` and `3` are invertible; see the module docstring for why that is the base worth reducing
to. -/
noncomputable def univQ : WeierstrassCurve (MvPolynomial (Fin 5) ℚ) :=
  univ.map (MvPolynomial.map (Int.castRingHom ℚ))

/-- **The reduction, over a characteristic-`0` base.**  `HasPreΩSq n` for `univQ` gives it for
every Weierstrass curve over every commutative ring: descend along the injective
`MvPolynomial.map (Int.castRingHom ℚ)` to `univ`, then specialise. -/
theorem hasPreΩSq_of_univQ {n : ℤ} (h : univQ.HasPreΩSq n) (W : WeierstrassCurve R) :
    W.HasPreΩSq n :=
  hasPreΩSq_of_univ (hasPreΩSq_of_map (MvPolynomial.map_injective _ Int.cast_injective) h) W

/-! ### Non-vacuity -/

/-- **Non-vacuity check on the whole chain.**  `HasPreΩSq 2` for an arbitrary `W` over an arbitrary
`CommRing`, recovered from the *single* instance at `univQ` — which exercises
`hasPreΩSq_of_map` (descent along `ℤ → ℚ`), `hasPreΩSq_of_univ` (specialisation) and
`HasPreΩSq.map` (which the latter uses) in one term.

⚠️ **This is a check, not content, and it must not be cited.**  `WeierstrassCurve.hasPreΩSq_two`
already proves this for every `W` directly and is strictly the better lemma; this is proved the long
way round precisely so that a reduction which failed to recover a known instance would break the
build.  It is a named lemma rather than an anonymous `example` because an `example` cannot be
pinned by `#check`, `#print axioms` or a `#907` comparator. -/
theorem hasPreΩSq_two_of_univQ (W : WeierstrassCurve R) : W.HasPreΩSq 2 :=
  hasPreΩSq_of_univQ univQ.hasPreΩSq_two W

end WeierstrassCurve
