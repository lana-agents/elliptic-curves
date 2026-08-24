/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import Mathlib.RingTheory.FormalGroup.Basic
import EllipticCurves.FormalGroup.GroupLawAssoc
import EllipticCurves.FormalGroup.GenuineLawComm

/-!
# Packaging the Weierstrass formal group law as a `FormalGroup R`

This file assembles the `Mathlib.RingTheory.FormalGroup.FormalGroup R` structure term for the
Weierstrass formal group law, built **directly on the genuine `(z, w)` series**
`W.formalGroupZW : MvPowerSeries (Fin 2) R`, together with its commutativity witness
`FormalGroup.IsComm`.

Building the bundle on `W.formalGroupZW` (rather than on the Laurent-extracted
`W.formalGroupSeries`) sidesteps the `(z, w)`↔Laurent identification crux (#310/#314) for **both**
structure fields:

* **normalisation** — `constantCoeff_formalGroupZW`, `coeff_single_zero_formalGroupZW`,
  `coeff_single_one_formalGroupZW` (all in `GenuineLaw.lean`);
* **commutativity** — `formalGroupZW_comm : rename (Equiv.swap 0 1) F = F`
  (`GenuineLawComm.lean`, unconditional over a general `CommRing R`);
* **associativity** — `formalGroupZW_assoc hadd` (`GroupLawAssoc.lean`, #319, over a `ℚ`-algebra,
  conditional on the log-additivity hypothesis `hadd` of #315), already in the exact
  `FormalGroup.assoc`-field shape.

⚠️ **The clause this paragraph used to carry has been paid, and by something stronger than it
promised.**  It read *"The only remaining hypothesis is `hadd`; the instant #315 lands it
unconditionally (`W.formalLog_subst_formalGroupZW`), feeding it here yields an unconditional
`FormalGroup R` over any `ℚ`-algebra"*.  `#315` landed
(`EllipticCurves.FormalGroup.LogAdditivityUnconditional`) — but ⚠️ **the unconditional bundle is
not here and is not restricted to `ℚ`-algebras**: `WeierstrassCurve.formalGroup : FormalGroup R`
and `WeierstrassCurve.formalGroup_isComm` live in
`EllipticCurves.FormalGroup.GroupLawBundleGeneral` over an **arbitrary** `CommRing R`, by the
universality transfer described next.  *A promise can be overtaken rather than merely fulfilled,
and a reader sent to the fulfilment gets the weaker theorem.*  The general-`CommRing R` version of
parent #263 follows by
the universality transfer (specialise at `Frac(ℤ[a₁, …, a₆])`, base-change via #318
`map_formalGroupZW`).

## Main results

* `WeierstrassCurve.formalGroupZW_subst_swap` :
  `W.formalGroupZW.subst ![X 1, X 0] = W.formalGroupZW` — the `IsComm.comm`-shaped commutativity
  identity on `formalGroupZW`, unconditional over a general `CommRing R`.
* `WeierstrassCurve.formalGroupOfLogAdditivity` :
  the `FormalGroup R` term over a `ℚ`-algebra, conditional on `hadd`.
* `WeierstrassCurve.formalGroupOfLogAdditivity_isComm` :
  its `FormalGroup.IsComm` witness.

## References

* [J. H. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], IV.1, Theorem 1.1.
-/

open MvPowerSeries

namespace WeierstrassCurve

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R)

/-- **The `IsComm.comm`-shaped commutativity of `W.formalGroupZW`.**
`F(z₁, z₂) = F(z₂, z₁)` rephrased as a substitution `F.subst ![X 1, X 0] = F`, the form the
`FormalGroup.IsComm` class consumes.  Unconditional over a general `CommRing R`, obtained from the
merged `formalGroupZW_comm` (`rename (Equiv.swap 0 1) F = F`) via
`MvPowerSeries.rename_eq_subst`. -/
theorem formalGroupZW_subst_swap :
    W.formalGroupZW.subst ![X (1 : Fin 2), X 0] = W.formalGroupZW := by
  have hfun : (![X (1 : Fin 2), X (0 : Fin 2)] : Fin 2 → MvPowerSeries (Fin 2) R)
      = X ∘ ⇑(Equiv.swap (0 : Fin 2) 1) := by
    funext i
    fin_cases i <;>
      simp [Function.comp, Equiv.swap_apply_left, Equiv.swap_apply_right]
  rw [hfun, ← MvPowerSeries.rename_eq_subst, W.formalGroupZW_comm]

/-- **The Weierstrass formal group law as a `FormalGroup R`**, built on the genuine `(z, w)` series
`W.formalGroupZW`, over a `ℚ`-algebra `R` and conditional on the log-additivity hypothesis `hadd`
of #315.  The `assoc` field is `W.formalGroupZW_assoc hadd` (#319); the normalisation fields come
from `GenuineLaw.lean`.  ⚠️ `#315` has since discharged `hadd` unconditionally
(`WeierstrassCurve.formalLog_subst_formalGroupZW`,
`EllipticCurves.FormalGroup.LogAdditivityUnconditional`), so this definition is no longer the
last-mile packaging of #263: ⚠️ **that is `WeierstrassCurve.formalGroup`
(`EllipticCurves.FormalGroup.GroupLawBundleGeneral`), unconditional over an arbitrary
`CommRing R`.**  This conditional form is kept because it is what the general bundle is built
from. -/
noncomputable def formalGroupOfLogAdditivity [Algebra ℚ R]
    (hadd : W.formalLog.subst W.formalGroupZW
      = W.formalLog.subst (X 0) + W.formalLog.subst (X 1)) :
    FormalGroup R where
  toPowerSeries := W.formalGroupZW
  zero_constantCoeff := W.constantCoeff_formalGroupZW
  lin_coeff_X := W.coeff_single_zero_formalGroupZW
  lin_coeff_Y := W.coeff_single_one_formalGroupZW
  assoc := W.formalGroupZW_assoc hadd

@[simp]
theorem formalGroupOfLogAdditivity_toPowerSeries [Algebra ℚ R]
    (hadd : W.formalLog.subst W.formalGroupZW
      = W.formalLog.subst (X 0) + W.formalLog.subst (X 1)) :
    (W.formalGroupOfLogAdditivity hadd).toPowerSeries = W.formalGroupZW :=
  rfl

/-- **The Weierstrass formal group law is commutative.**  The `FormalGroup.IsComm` witness for
`W.formalGroupOfLogAdditivity hadd`, from the unconditional `formalGroupZW_subst_swap`. -/
theorem formalGroupOfLogAdditivity_isComm [Algebra ℚ R]
    (hadd : W.formalLog.subst W.formalGroupZW
      = W.formalLog.subst (X 0) + W.formalLog.subst (X 1)) :
    (W.formalGroupOfLogAdditivity hadd).IsComm :=
  ⟨(W.formalGroupZW_subst_swap).symm⟩

end WeierstrassCurve
