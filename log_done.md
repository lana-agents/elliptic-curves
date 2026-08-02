# VietaDifferential.lean (#338) — DONE

All 10 sorries filled. `lake build EllipticCurves.FormalGroup.VietaDifferential`
succeeds (no errors, no warnings, --wfail clean). No sorry/axiom introduced.
`#print axioms WeierstrassCurve.derivative_formalXThree`
  = [propext, Classical.choice, Quot.sound].

Key techniques:
- derivative_mapRingHom: coeff-wise via LaurentSeries.coeff_derivative + map_zsmul.
- derivative_ofPowerSeries: case split n<0 / n≥0, coe_powerSeries_coeff_of_neg.
- derivative_single_one: hasseDeriv_single + Ring.choose_one_right + simp.
- derivative_formalX (UNIV-X): cancel w^2 (unit) using Eq.Ω coerced via
  HahnSeries.ofPowerSeries + map_* / ofPowerSeries_C/X.
- derivative_formalY (UNIV-Y): differentiate weierstrass, cancel unit (2y+a1x+a3)*w=den
  (den unit via PowerSeries.isUnit_iff_constantCoeff, negTwoUnit).
- derivative_biX1/biY1: LaurentSeries.derivative_C (term mode).
- derivative_biX2/biY2: derivative_mapRingHom + map_* / cLaurentRingHom_C + rfl.
- derivative_formalXThree: double cancellation of unit (biX2-biX1); Vieta certificate
  linear_combination (2λ+C(C a1))*(h1 - h2) after rw biY1_eq/biY2_eq + simp unfolds.
