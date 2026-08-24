/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import Mathlib.RingTheory.DiscreteValuationRing.TFAE
import Mathlib.RingTheory.LocalProperties.IntegrallyClosed
import EllipticCurves.FunctionField.LocalRingUniformizer

/-!
# Normality of the coordinate ring from the Jacobian–uniformizer lemma

This file takes the next step of the normality crux of issue #396 Part A after the
Jacobian–uniformizer milestone (`maximalIdeal_isPrincipal_of_nonsingular`, `#469` / PR #188,
`LocalRingUniformizer.lean`): it turns the *principality* of the localised maximal ideal at a
nonsingular point into **integral closedness** of that local ring, and assembles the local
statements into `IsIntegrallyClosed W.CoordinateRing` — hence `IsDedekindDomain W.CoordinateRing`
(`CoordinateRing.isDedekindDomain`, PR #130) — for a Weierstrass curve *whose maximal ideals are all
of the closed-point form* `⟨X - x, Y - y⟩` at nonsingular points.

## The mathematics

Fix a nonsingular affine point `(x, y)` of `W`.  The local ring
`Rₚ := Localization.AtPrime ⟨X - x, Y - y⟩` is a Noetherian local domain, and by the merged
milestone its maximal ideal is principal.  For such a ring the discrete-valuation-ring TFAE
(`tfae_of_isNoetherianRing_of_isLocalRing_of_isDomain`) makes *principal maximal ideal* equivalent
to *integrally closed*, so `Rₚ` is integrally closed (indeed a discrete valuation ring).

To promote this to integral closedness of the whole coordinate ring one uses
`IsIntegrallyClosed.of_localization_maximal`: a domain is integrally closed as soon as its
localization at every maximal ideal is.  Over an algebraically closed base field the weak
Nullstellensatz identifies *every* maximal ideal of `F[W]` with a closed point `⟨X - x, Y - y⟩`,
and `W.IsElliptic` makes every such point nonsingular — discharging the hypothesis.  Formalising
that classification is a separate, substantial piece of work (it is the last genuinely-missing input
of `#396` Part A), so here it is carried as the explicit hypothesis `hcl`, exactly matching how the
rest of this development carries its single genuinely-gated geometric input as a hypothesis.  The
unconditional content — that each nonsingular closed point contributes an integrally closed
localization — is the reusable brick `isIntegrallyClosed_localization_of_nonsingular`.

## Main results

* `isIntegrallyClosed_localization_of_nonsingular` — **unconditional**: at a nonsingular affine
  point, `Localization.AtPrime ⟨X - x, Y - y⟩` is integrally closed (a discrete valuation ring).
  This is the per-closed-point normality input to `IsIntegrallyClosed.of_localization_maximal`.
* `isIntegrallyClosed_of_maximalIdeal_classification` — conditional on the maximal-ideal
  classification `hcl` (every nonzero maximal ideal is `⟨X - x, Y - y⟩` at a nonsingular point):
  `IsIntegrallyClosed W.CoordinateRing`.
* `isDedekindDomain_of_maximalIdeal_classification` — the same hypothesis yields
  `IsDedekindDomain W.CoordinateRing`, composing with `CoordinateRing.isDedekindDomain`.

## The gap this file left, and how it was closed

⚠️ **This section used to be headed `## The remaining gap`** and to say that the maximal-ideal
classification `hcl` *"is the one input still carried as a hypothesis"*.  It still is, in this
file — `isIntegrallyClosed_of_maximalIdeal_classification` below takes it — but it is no longer a
gap in the tree, and the two routes it offered did not fare equally.

* Over an algebraically closed field the classification is
  `exists_equation_and_eq_XYIdeal_of_isMaximal`
  (`EllipticCurves.FunctionField.CoordinateRingNormalAlgClosed`), which is the weak Nullstellensatz
  argument sketched here — Zariski's lemma on `F[W] ⧸ m`, then
  `IsAlgClosed.algebraMap_bijective_of_isIntegral` to read off the point — and that file fires
  `IsIntegrallyClosed.of_localization_maximal` directly rather than through
  `isIntegrallyClosed_of_maximalIdeal_classification`.
* Over a general field, ⚠️ **the "finer classification" was never built and is still nowhere in
  this tree.**  It is the *other* option this paragraph named that was taken:
  `EllipticCurves.FunctionField.CoordinateRingNormalGeneral` descends `IsIntegrallyClosed` along
  `F[W] → F̄[W]` by `IsIntegrallyClosed.of_faithfullyFlat`
  (`EllipticCurves.FunctionField.IntegrallyClosedDescent`), and registers
  `IsIntegrallyClosed W.CoordinateRing` and `IsDedekindDomain W.CoordinateRing` as **global
  instances** for every `[W.IsElliptic]`.  A reader who prices the general case off this paragraph
  will price the wrong one of the two.

⚠️ **The whole `#396` / `#469` ladder was written and closed inside one afternoon, and none of
its five rungs was revisited.**  Pickaxe dating (`git log --format=%ci -S'<clause>' -- <file>`),
all on 2026-08-16: `LocalRingUnit` predicted the Taylor brick and the Nakayama step at 10:40;
`LocalRingTaylor` landed the first at 11:24 and predicted the second; `LocalRingUniformizer` landed
it at 11:48 and predicted the passage to `IsIntegrallyClosed`; `LocalRingNormal` landed that at
12:30 and predicted the maximal-ideal classification; `CoordinateRingNormalAlgClosed` landed it at
12:48 and predicted the general-base-field descent, which `CoordinateRingNormalGeneral` registered
as a **global instance** at 13:59.  Three hours and nineteen minutes, five files, five surviving
predictions.

## References

* [J. Silverman, *The arithmetic of elliptic curves*][silverman2009], II.1–II.3, III.8.
-/

open Polynomial

namespace WeierstrassCurve.Affine

namespace CoordinateRing

variable {F : Type*} [Field F] (W : Affine F) (x y : F)

/-- **Local normality at a nonsingular closed point.**  At a nonsingular affine point `(x, y)` of
`W`, the local ring `Localization.AtPrime ⟨X - x, Y - y⟩` is integrally closed — in fact a discrete
valuation ring.

This follows from the Jacobian–uniformizer milestone `maximalIdeal_isPrincipal_of_nonsingular`
(the maximal ideal is principal) via the discrete-valuation-ring TFAE for a Noetherian local domain
(`tfae_of_isNoetherianRing_of_isLocalRing_of_isDomain`), which makes *principal maximal ideal*
(entry 4) equivalent to *integrally closed with a unique nonzero prime* (entry 3).  It is the
per-closed-point input to `IsIntegrallyClosed.of_localization_maximal`. -/
theorem isIntegrallyClosed_localization_of_nonsingular (h : W.Nonsingular x y)
    [(XYIdeal W x (C y)).IsPrime] :
    IsIntegrallyClosed (Localization.AtPrime (XYIdeal W x (C y))) := by
  have hiff := (tfae_of_isNoetherianRing_of_isLocalRing_of_isDomain
      (Localization.AtPrime (XYIdeal W x (C y)))).out 4 3
  exact (hiff.mp (maximalIdeal_isPrincipal_of_nonsingular W x y h)).1

/-- **Integral closedness of the coordinate ring from the closed-point classification.**  If every
nonzero maximal ideal of `F[W]` is a closed point `⟨X - x, Y - y⟩` at a nonsingular affine point,
then `F[W]` is integrally closed (normal).

The classification hypothesis `hcl` is the single remaining genuinely-gated input of `#396` Part A:
over an algebraically closed base it is the weak Nullstellensatz for `F[W]` together with
`W.IsElliptic ⇒` all points nonsingular.  Given it, `IsIntegrallyClosed.of_localization_maximal`
reduces the statement to local normality at each maximal ideal, which is the unconditional
`isIntegrallyClosed_localization_of_nonsingular`. -/
theorem isIntegrallyClosed_of_maximalIdeal_classification
    (hcl : ∀ p : Ideal W.CoordinateRing, p ≠ ⊥ → p.IsMaximal →
      ∃ x y : F, W.Nonsingular x y ∧ p = XYIdeal W x (C y)) :
    IsIntegrallyClosed W.CoordinateRing := by
  apply IsIntegrallyClosed.of_localization_maximal
  intro p hp hpm
  obtain ⟨x, y, hns, rfl⟩ := hcl p hp hpm
  haveI : (XYIdeal W x (C y)).IsPrime := hpm.isPrime
  exact isIntegrallyClosed_localization_of_nonsingular W x y hns

/-- **The coordinate ring is a Dedekind domain from the closed-point classification.**  Under the
same maximal-ideal classification hypothesis `hcl` as
`isIntegrallyClosed_of_maximalIdeal_classification`, the affine coordinate ring `F[W]` is a Dedekind
domain: the Noetherian and Krull-dimension-`≤ 1` pillars are unconditional
(`CoordinateRing.isDedekindDomain`, PR #130) and `hcl` supplies the third (normality). -/
theorem isDedekindDomain_of_maximalIdeal_classification
    (hcl : ∀ p : Ideal W.CoordinateRing, p ≠ ⊥ → p.IsMaximal →
      ∃ x y : F, W.Nonsingular x y ∧ p = XYIdeal W x (C y)) :
    IsDedekindDomain W.CoordinateRing :=
  letI := isIntegrallyClosed_of_maximalIdeal_classification W hcl
  isDedekindDomain (W := W)

end CoordinateRing

end WeierstrassCurve.Affine
