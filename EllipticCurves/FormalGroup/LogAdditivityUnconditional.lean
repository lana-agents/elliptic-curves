/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import EllipticCurves.FormalGroup.LogAdditivityStarClose
import EllipticCurves.FormalGroup.VietaDifferential
import EllipticCurves.FormalGroup.GenuineWThreeIdentification

/-!
# Unconditional log-additivity of the Weierstrass formal logarithm (issue #315)

This file discharges the last two hypotheses of the merged consumer
`WeierstrassCurve.formalLog_subst_formalGroupZW_of_hWF_hdiff`
(from `LogAdditivityStarClose.lean`) and thereby delivers, over a `ℚ`-algebra `R`, the
**unconditional** additivity of the formal logarithm on the genuine `(z, w)` Weierstrass
formal group law `F = W.formalGroupZW`:
```
log_E(F(z₁, z₂)) = log_E(z₁) + log_E(z₂)     in  MvPowerSeries (Fin 2) R
```
i.e. `log_E : formalGroupZW ≅ 𝔾ₐ` is a morphism of formal group laws (Silverman AEC IV.5,
Proposition 5.2).

Both remaining inputs are now available as unconditional, merged theorems:

* `hWF` = `WeierstrassCurve.embedDoubleLaurent_formalW_subst_formalGroupZW`
  (`edl (w ∘ F_E) = formalWThree`, issue #333, `GenuineWThreeIdentification.lean`);
* `hdiff` = `WeierstrassCurve.derivative_formalXThree`
  (`∂_{z₂} x₃ = ω̃₂·(2·y₃ + a₁·x₃ + a₃)`, issue #338, `VietaDifferential.lean`).

Feeding them into `formalLog_subst_formalGroupZW_of_hWF_hdiff` closes the entire `(★)`/`hstar`
program that the approved partials #36/#45/#46/#58/#60/#61/#62 assembled.

This unconditional `formalLog_subst_formalGroupZW` is exactly the hypothesis `hadd` that the
route-2 associativity core `WeierstrassCurve.formalGroupZW_assoc` (#319, `GroupLawAssoc.lean`)
consumes, so it unblocks #319 → #263.
-/

namespace WeierstrassCurve

variable {R : Type*} [CommRing R] [Algebra ℚ R] (W : WeierstrassCurve R)

open MvPowerSeries

/-- **Log-additivity of the Weierstrass formal logarithm (issue #315), unconditional.**
Over a `ℚ`-algebra, the formal logarithm of the genuine `(z, w)` formal group law
`F = W.formalGroupZW` is additive:
`log_E(F(z₁, z₂)) = log_E(z₁) + log_E(z₂)`.

This is `formalLog_subst_formalGroupZW_of_hWF_hdiff` with its two hypotheses discharged by the
merged unconditional theorems `embedDoubleLaurent_formalW_subst_formalGroupZW` (`hWF`, #333) and
`derivative_formalXThree` (`hdiff`, #338). -/
theorem formalLog_subst_formalGroupZW :
    W.formalLog.subst W.formalGroupZW = W.formalLog.subst (X 0) + W.formalLog.subst (X 1) :=
  W.formalLog_subst_formalGroupZW_of_hWF_hdiff
    W.embedDoubleLaurent_formalW_subst_formalGroupZW W.derivative_formalXThree

end WeierstrassCurve
