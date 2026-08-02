/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import EllipticCurves.FormalGroup.GroupLawAssoc
import EllipticCurves.FormalGroup.GroupLawBundle
import EllipticCurves.FormalGroup.LogAdditivityUnconditional

/-!
# Unconditional associativity of `W.formalGroupZW` over a `ℚ`-algebra (issue #319)

The route-2 associativity core `WeierstrassCurve.formalGroupZW_assoc` (`GroupLawAssoc.lean`, #319)
and the `FormalGroup R` bundle `WeierstrassCurve.formalGroupOfLogAdditivity` (`GroupLawBundle.lean`,
#324) both consume the log-additivity hypothesis
```
hadd : W.formalLog.subst W.formalGroupZW = W.formalLog.subst (X 0) + W.formalLog.subst (X 1)
```
of issue #315.  That hypothesis is now an **unconditional, merged theorem**
`WeierstrassCurve.formalLog_subst_formalGroupZW` (`LogAdditivityUnconditional.lean`, #315).

Feeding it in discharges the hypothesis, delivering — over any `ℚ`-algebra `R`, unconditionally:

* `WeierstrassCurve.formalGroupZW_assoc_unconditional` — associativity of the genuine `(z, w)`
  Weierstrass formal group law `W.formalGroupZW` in the exact `FormalGroup.assoc`-field shape
  `F(F(X₀, X₁), X₂) = F(X₀, F(X₁, X₂))` (the deliverable of #319);
* `WeierstrassCurve.formalGroup` — the `FormalGroup R` term itself, and
  `WeierstrassCurve.formalGroup_isComm` — its `FormalGroup.IsComm` commutativity witness.

The general-`CommRing R` version (parent #263, issue #339) follows from `formalGroup` here by the
universality transfer: specialise at `R = Frac(ℤ[a₁, …, a₆])` and base-change to arbitrary `R` via
`map_formalGroupZW` (#318).

## References

* [J. H. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], IV.1 Theorem 1.1,
  IV.5 Proposition 5.2.
-/

open MvPowerSeries

namespace WeierstrassCurve

variable {R : Type*} [CommRing R] [Algebra ℚ R] (W : WeierstrassCurve R)

/-- **Associativity of `W.formalGroupZW`, unconditional over a `ℚ`-algebra.**
`F(F(X₀, X₁), X₂) = F(X₀, F(X₁, X₂))` in `MvPowerSeries (Fin 3) R`, in the exact
`FormalGroup.assoc`-field shape.  This discharges the log-additivity hypothesis of the merged
route-2 core `formalGroupZW_assoc` (#319) using the now-unconditional
`formalLog_subst_formalGroupZW` (#315). -/
theorem formalGroupZW_assoc_unconditional :
    W.formalGroupZW.subst
        ![W.formalGroupZW.subst ![(X 0 : MvPowerSeries (Fin 3) R), X 1], X 2]
      = W.formalGroupZW.subst
        ![(X 0 : MvPowerSeries (Fin 3) R), W.formalGroupZW.subst ![X 1, X 2]] :=
  W.formalGroupZW_assoc W.formalLog_subst_formalGroupZW

/-- **The Weierstrass formal group law as a `FormalGroup R`**, over a `ℚ`-algebra `R`,
unconditional.  Built on the genuine `(z, w)` series `W.formalGroupZW`, with the `assoc` field
discharged by the merged unconditional log-additivity `formalLog_subst_formalGroupZW` (#315).
This is the ℚ-algebra last-mile packaging of #263; the general-`CommRing R` bundle (#339) descends
from it by universality. -/
noncomputable def formalGroup : FormalGroup R :=
  W.formalGroupOfLogAdditivity W.formalLog_subst_formalGroupZW

@[simp]
theorem formalGroup_toPowerSeries : W.formalGroup.toPowerSeries = W.formalGroupZW :=
  rfl

/-- **The Weierstrass formal group law is commutative.**  The `FormalGroup.IsComm` witness for
`W.formalGroup`, from the unconditional `formalGroupZW_subst_swap`. -/
theorem formalGroup_isComm : W.formalGroup.IsComm :=
  W.formalGroupOfLogAdditivity_isComm W.formalLog_subst_formalGroupZW

end WeierstrassCurve
