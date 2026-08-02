/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import EllipticCurves.FormalGroup.GroupLawAssoc
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
  `F(F(X₀, X₁), X₂) = F(X₀, F(X₁, X₂))` (the deliverable of #319).

The `FormalGroup R` bundle itself (`WeierstrassCurve.formalGroup`) and its commutativity witness
(`formalGroup_isComm`) are packaged over an **arbitrary `CommRing R`** in
`GroupLawBundleGeneral.lean` (issue #339, the last-mile of #263), which subsumes the ℚ-algebra case;
the general-`CommRing R` associativity there follows from `formalGroupZW_assoc_unconditional` by the
universality transfer
(specialise at `R = Frac(ℤ[a₁, …, a₆])` and base-change via `map_formalGroupZW`, #318).

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

end WeierstrassCurve
