/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import EllipticCurves.FunctionField.DivisorInjective
import EllipticCurves.FunctionField.PrincipalDivisorOfPoint
import EllipticCurves.FunctionField.MulByThreeEndomorphism
import EllipticCurves.FunctionField.MulByTwoEndomorphism

/-!
# The `n`-th root `g_S` of the pulled-back principal function (Weil-pairing construction, rung 5)

Let `W` be a Weierstrass curve over a field `F` whose affine coordinate ring `F[W]` is a Dedekind
domain, and let `f_S ∈ F(W)` be the principal function of a nonzero `n`-torsion point `S` (issue
#409: `divisor W f_S = n·(S)` on the affine chart).  The multiplication-by-`n` endomorphism
`[n]∗ = mulByTwoEndo` (issue #405, concrete `n = 2`) pulls `f_S` back to `mulByTwoEndo f_S`, whose
divisor is `n`-divisible (issue #414, rung 4).  The **second-to-last rung of the divisor-theoretic
Weil pairing** (Silverman AEC III.8) produces a nonzero `n`-th root

```
g_S ∈ F(W)   with   u · g_S ^ n = mulByTwoEndo f_S   (u a unit of F[W]),
```

equivalently `divisor W g_S = [n]∗(S)`, the effective half of `divisor W (mulByTwoEndo f_S)`.

## The mathematical subtlety, and the scope delivered here

`n · D` principal does **not** imply `D` principal — that failure is exactly the `n`-torsion of the
class group the Weil pairing measures.  So the existence of `g_S` is *not* a formal consequence of
`n`-divisibility alone; Silverman III.8 obtains it from the specific group-theoretic structure
(`S = [n]P` for some `P`, and `[n]` a homomorphism).

This file therefore delivers the assembly around that step: the general divisor-theoretic engine
that turns a *principal* `n`-th-root divisor into an `n`-th root of the target function (up to a
unit), together with the uniqueness of that root, and the concrete `n = 2` and `n = 3`
instantiations against the torsion generator of #409.  The one gated input — that the effective
divisor `D` with `n·D = divisor W (mulByTwoEndo f_S)` is principal — is carried as an explicit
hypothesis (`hprin`).

## What gates `hprin`, and what does not (`#765`)

⚠️ Earlier versions of this docstring said `hprin` was **Ward-coupled**, to be discharged "once
`#E[n] = n²` lands".  **That is false at the only two `n` this file is stated at.**  The counts are
merged, and neither goes through Ward — `#E[2]` counts the roots of the `2`-division cubic and
`#E[3]` counts two points over each root of `Ψ₃`:

* `card_torsion_two` (`Torsion/TwoTorsion.lean`), with `nonempty_torsionTwo_addEquiv`;
* `card_torsion_three` (`Torsion/ThreeTorsionStructure.lean`), with
  `nonempty_torsionThree_addEquiv`.

Ward gates `#E[n] = n²` at **general** `n` (`#242`/`#251`), which is not what `exists_gS_two` and
`exists_gS_three` need.  The class-group layer that would turn a vanishing class back into a
generator is merged too: `classOfDivisor` and `exists_divisor_eq_iff_classOfDivisor_eq_one`
(`EllipticCurves.FunctionField.DivisorPrincipality`, `#726`).

⚠️ Earlier wording said "what is actually missing is one geometric fact", namely the fibre
description `[2]∗((S) − (O)) = ∑_{R ∈ E[2]} ((P ⊕ R) − (R))`, and attributed it to `#639` rung 8.
The attribution was wrong (it is rung 9, `#774` — `#701` counts the fibre and does not describe it),
and **the fact is now merged**: `EllipticCurves.FunctionField.MulByTwoFibreAffine`'s
`pullbackDivisorTwo_single_eq_sum_torsion`, with every `ramificationIdxTwo` over a rational point
pinned to `1` in the same file.

⚠️ Those results are **not stated in this file's generality**: `comapProjPointTwo_projPointOfPoint`
carries `[W.IsElliptic]`, and the coset description, the four-element count and the pinned indices
carry `[IsAlgClosed F]` as well, whereas the variable block here is `[Field F]` with
`[IsDedekindDomain W.CoordinateRing]` and `exists_gS_two` adds nothing.  Read the sentence below as
*over an algebraically closed base field*; for a general `F` the fibre description is still not
available.

So at `n = 2`, over such a base field, what remains of `hprin` is the **class-group computation**,
on merged material:
`∑_R toClass (P ⊕ R) − ∑_R toClass R = 4 · toClass P = toClass ([2]S) = 0`, by `card_torsion_two`,
Mathlib's `Point.toClass_eq_zero` and `#726`'s `exists_divisor_eq_iff_classOfDivisor_eq_one`.  That
is bookkeeping between `divisorProj` sums and `toClass`, not a geometric input — but it is **not
done**, and nothing in this file or in `#774` discharges `hprin`.

At `n = 3` the geometric fact is still missing: there is no `[3]` duplication formula at a point
(`#404`) and `#763`'s count `4` is `[2]`-specific.

## Main statements

* `WeierstrassCurve.Affine.divisor_pow` — `divisor W (f ^ m) = m • divisor W f`.
* `WeierstrassCurve.Affine.exists_smul_pow_eq_of_nsmul_divisor` — the engine: if
  `m • divisor W g₀ = divisor W h` (nonzero `g₀`, `h`), then `u · g₀ ^ m = h` for a unit `u`.
* `WeierstrassCurve.Affine.exists_unit_of_nsmul_divisor_eq` — uniqueness: an `n`-th root of a given
  divisor is unique up to a unit of `F[W]` (for `m ≠ 0`).
* `WeierstrassCurve.Affine.exists_gS_two` — the concrete `n = 2` rung: from the torsion generator
  `f_S` of #409 and the principality of `[2]∗(S)`, a nonzero `g_S` with `u · g_S ^ 2 = [2]∗ f_S`.
* `WeierstrassCurve.Affine.exists_gS_three` — the concrete `n = 3` rung, the `mulByThreeEndo`
  analogue of `exists_gS_two`: a nonzero `g_S` with `u · g_S ^ 3 = [3]∗ f_S`.

## References

* [J. H. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.8 (the Weil pairing;
  the function `g_P` with `g_P ^ n = f_P ∘ [n]`).
-/

open scoped nonZeroDivisors

namespace WeierstrassCurve.Affine

variable {F : Type*} [Field F] {W : Affine F} [IsDedekindDomain W.CoordinateRing]

open CoordinateRing

/-- **The divisor of a power.** `divisor W (f ^ m) = m • divisor W f`; the order-of-vanishing
homomorphism law `ord v (f ^ m) = m · ord v f` read at every closed point. Holds unconditionally
(both sides vanish for `f = 0`, `m ≥ 1`). -/
lemma divisor_pow (f : W.FunctionField) (m : ℕ) :
    divisor W (f ^ m) = m • divisor W f := by
  ext v
  simp only [divisor_apply, ord_pow, Finsupp.smul_apply, nsmul_eq_mul]

/-- **The `n`-th-root engine.** If a nonzero `g₀ ∈ F(W)` has divisor `D` with `m • D` equal to the
divisor of a nonzero `h ∈ F(W)`, then `g₀ ^ m` and `h` have the same divisor, so they agree up to a
unit of the coordinate ring: `u · g₀ ^ m = h`.  This is the divisor-theoretic content of the rung-5
`n`-th root: once the effective divisor `D = [n]∗(S)` is known to be principal (`D = divisor W g₀`),
its generator `g₀` is an `n`-th root of the pulled-back function up to a unit. -/
theorem exists_smul_pow_eq_of_nsmul_divisor {h : W.FunctionField} (hh : h ≠ 0)
    {m : ℕ} {g₀ : W.FunctionField} (hg₀ : g₀ ≠ 0)
    (hdiv : m • divisor W g₀ = divisor W h) :
    ∃ u : W.CoordinateRingˣ, (u : W.CoordinateRing) • g₀ ^ m = h :=
  exists_unit_of_divisor_eq (pow_ne_zero m hg₀) hh (by rw [divisor_pow, hdiv])

/-- **Uniqueness of the `n`-th root up to a unit.** For `m ≠ 0`, two nonzero functions whose
`m`-fold divisors agree (`m • divisor W g₁ = m • divisor W g₂`) already have equal divisors, hence
differ by a unit of `F[W]`.  In particular the `g_S` produced by
`exists_smul_pow_eq_of_nsmul_divisor` is pinned uniquely up to a unit. -/
theorem exists_unit_of_nsmul_divisor_eq {m : ℕ} (hm : m ≠ 0)
    {g₁ g₂ : W.FunctionField} (hg₁ : g₁ ≠ 0) (hg₂ : g₂ ≠ 0)
    (h : m • divisor W g₁ = m • divisor W g₂) :
    ∃ u : W.CoordinateRingˣ, (u : W.CoordinateRing) • g₁ = g₂ := by
  refine exists_unit_of_divisor_eq hg₁ hg₂ ?_
  ext v
  have hv := DFunLike.congr_fun h v
  simp only [Finsupp.smul_apply, nsmul_eq_mul] at hv
  exact mul_left_cancel₀ (by exact_mod_cast hm) hv

/-- **The concrete `n = 2` rung of the Weil pairing.** For a nonsingular `2`-torsion point
`S = (x, y)`, take the principal function `f_S` of #409 (`divisor W f_S = 2·(S)` on the affine
chart) and its pullback `[2]∗ f_S = mulByTwoEndo h2 f_S`.  Assuming the effective divisor of the
`n`-th root is principal (`hprin`: `∃ g₀ ≠ 0, 2 • divisor W g₀ = divisor W (mulByTwoEndo h2 f_S)`),
there is a nonzero `g_S ∈ F(W)` with `u · g_S ^ 2 = mulByTwoEndo h2 f_S` for a unit `u` of `F[W]`.

The hypothesis `hprin` is the single gated input (principality of `[2]∗(S)`); everything else is
unconditional.  It is **not** gated on `#E[2] = 4`, which is merged (`card_torsion_two`), and — as
of `#774` — no longer on the fibre description of `[2]∗` either, which is merged as
`pullbackDivisorTwo_single_eq_sum_torsion` (`MulByTwoFibreAffine`) **over `[IsAlgClosed F]` and
`[W.IsElliptic]`, which this statement does not carry**.  What is left is the class-group
computation; see the module docstring. -/
theorem exists_gS_two [DecidableEq F] (h2 : (2 : F) ≠ 0) {x y : F} (h : W.Nonsingular x y)
    (hP : Point.some x y h ∈ W.torsion 2)
    (hprin : ∀ f : W.FunctionField, f ≠ 0 →
      divisor W f = Finsupp.single (CoordinateRing.pointClosedPoint h.1) (2 : ℤ) →
      ∃ g₀ : W.FunctionField, g₀ ≠ 0 ∧
        2 • divisor W g₀ = divisor W (mulByTwoEndo h2 f)) :
    ∃ f : W.FunctionField, f ≠ 0 ∧
      divisor W f = Finsupp.single (CoordinateRing.pointClosedPoint h.1) (2 : ℤ) ∧
      ∃ gS : W.FunctionField, gS ≠ 0 ∧
        ∃ u : W.CoordinateRingˣ, (u : W.CoordinateRing) • gS ^ 2 = mulByTwoEndo h2 f := by
  obtain ⟨f, hf, hfdiv⟩ := exists_generator_divisor_eq_of_torsion h hP
  obtain ⟨g₀, hg₀, hdiv⟩ := hprin f hf hfdiv
  have hne : mulByTwoEndo h2 f ≠ 0 := fun hz =>
    hf ((mulByTwoEndo h2).injective (by rw [hz, map_zero]))
  exact ⟨f, hf, hfdiv, g₀, hg₀, exists_smul_pow_eq_of_nsmul_divisor hne hg₀ hdiv⟩

/-- **The concrete `n = 3` rung of the Weil pairing.** The `mulByThreeEndo` analogue of
`exists_gS_two`: for a nonsingular `3`-torsion point `S = (x, y)`, take the principal function `f_S`
of #409 (`divisor W f_S = 3·(S)` on the affine chart) and its pullback `[3]∗ f_S = mulByThreeEndo`
`h2 h3 f_S`.  Assuming the effective divisor of the `n`-th root is principal (`hprin`:
`∃ g₀ ≠ 0, 3 • divisor W g₀ = divisor W (mulByThreeEndo h2 h3 f_S)`), there is a nonzero
`g_S ∈ F(W)` with `u · g_S ^ 3 = mulByThreeEndo h2 h3 f_S` for a unit `u` of `F[W]`.

As with `exists_gS_two`, the hypothesis `hprin` is the single gated input (principality of
`[3]∗(S)`); everything else is unconditional.  It is **not** gated on `#E[3] = 9`, which is merged
(`card_torsion_three`), but on the fibre description of `[3]∗` — see the module docstring and
`#765`. -/
theorem exists_gS_three [DecidableEq F] (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) {x y : F}
    (h : W.Nonsingular x y) (hP : Point.some x y h ∈ W.torsion 3)
    (hprin : ∀ f : W.FunctionField, f ≠ 0 →
      divisor W f = Finsupp.single (CoordinateRing.pointClosedPoint h.1) (3 : ℤ) →
      ∃ g₀ : W.FunctionField, g₀ ≠ 0 ∧
        3 • divisor W g₀ = divisor W (mulByThreeEndo h2 h3 f)) :
    ∃ f : W.FunctionField, f ≠ 0 ∧
      divisor W f = Finsupp.single (CoordinateRing.pointClosedPoint h.1) (3 : ℤ) ∧
      ∃ gS : W.FunctionField, gS ≠ 0 ∧
        ∃ u : W.CoordinateRingˣ, (u : W.CoordinateRing) • gS ^ 3 = mulByThreeEndo h2 h3 f := by
  obtain ⟨f, hf, hfdiv⟩ := exists_generator_divisor_eq_of_torsion h hP
  obtain ⟨g₀, hg₀, hdiv⟩ := hprin f hf hfdiv
  have hne : mulByThreeEndo h2 h3 f ≠ 0 := fun hz =>
    hf ((mulByThreeEndo h2 h3).injective (by rw [hz, map_zero]))
  exact ⟨f, hf, hfdiv, g₀, hg₀, exists_smul_pow_eq_of_nsmul_divisor hne hg₀ hdiv⟩

end WeierstrassCurve.Affine
