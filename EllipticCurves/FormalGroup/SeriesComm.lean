/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import EllipticCurves.FormalGroup.GroupLawBundle
import EllipticCurves.FormalGroup.GenuineLawTransfer

/-!
# Commutativity of the extracted Weierstrass formal group series

The substantive commutativity of the Weierstrass formal group law was proved on the genuine
`(z, w)` power-series construction `W.formalGroupZW` in
`EllipticCurves.FormalGroup.GenuineLawComm` (`formalGroupZW_comm`) and rephrased in the
`FormalGroup.IsComm`-shaped substitution form `formalGroupZW_subst_swap` in
`EllipticCurves.FormalGroup.GroupLawBundle`.

This file transports that commutativity to the **extracted** Laurent-coefficient series
`W.formalGroupSeries`, using the now-unconditional round-trip
`formalGroupSeries = formalGroupZW` (`EllipticCurves.FormalGroup.GenuineLawTransfer`, delivered by
the identification `embedDoubleLaurent formalGroupZW = formalGroupLaurent`). The result is the exact
`FormalGroup.IsComm.comm`-shaped identity a `FormalGroup R` bundle built on `formalGroupSeries`
consumes.

## Main results

* `WeierstrassCurve.formalGroupSeries_comm` :
  `W.formalGroupSeries.subst ![X 1, X 0] = W.formalGroupSeries`.

## References

* [J. H. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], IV.1, Theorem 1.1.
-/

open MvPowerSeries

namespace WeierstrassCurve

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R)

/-- **The extracted Weierstrass formal group series is commutative.**
`F_E(z₁, z₂) = F_E(z₂, z₁)` rephrased as a substitution
`W.formalGroupSeries.subst ![X 1, X 0] = W.formalGroupSeries`, the exact `FormalGroup.IsComm.comm`
form a bundle built on `formalGroupSeries` consumes.  Unconditional over a general `CommRing R`:
the round-trip `formalGroupSeries = formalGroupZW` (`formalGroupSeries_eq_formalGroupZW`) reduces it
to the manifest symmetry `formalGroupZW_subst_swap` of the genuine `(z, w)` series. -/
theorem formalGroupSeries_comm :
    W.formalGroupSeries.subst ![X (1 : Fin 2), X 0] = W.formalGroupSeries := by
  rw [W.formalGroupSeries_eq_formalGroupZW, W.formalGroupZW_subst_swap]

end WeierstrassCurve
