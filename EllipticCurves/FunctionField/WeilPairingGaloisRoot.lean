/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import EllipticCurves.FunctionField.GaloisPointAction
import EllipticCurves.FunctionField.MulByThreeFinite
import EllipticCurves.FunctionField.MulByTwoFinite
import EllipticCurves.FunctionField.PullbackPrincipalityTwo
import EllipticCurves.FunctionField.WeilPairingGaloisPoint
import EllipticCurves.FunctionField.WeilPairingRootIndependence

/-!
# The Galois transport of a rung-5 root, and `e_n(σS, σT) = σ(e_n(S, T))` unconditionally

`EllipticCurves.FunctionField.WeilPairingGaloisDivisor` reduces the Galois-equivariance of the
Weil-pairing element to one divisor identity: it proves

```
weilPairingElt_galois_of_divisor_eq :
  divisor g' = σ_*(divisor g)  →  σ⋆(e_n(S, T)) = e_n(σS, σT),
```

and then says the residual gate is `divisor g_S = [n]∗(S)` — the rung-5 characterising identity,
which is gated on rung 4 (`#421`/`#422`).  Every file on this front has repeated that reading.

**It is not the gate.**  What the pairing needs is that the divisors of `σ⋆ g_S` and of `g_{σS}`
agree, and *that* follows from the rung-5 datum in the shape it is actually produced in,

```
u · g_S ^ n = [n]∗ f_S,        div f_S = n·(S),
```

without ever computing `divisor g_S`.  The reason is that `[n]∗` and `σ⋆` commute and both fix the
base field, so `[n]∗ f_{σS}` and `σ⋆([n]∗ f_S)` differ by a constant; the two `n`-th powers
`g_{σS} ^ n` and `(σ⋆ g_S) ^ n` therefore have the same divisor, and the divisor group of a curve
is torsion-free, so the `n` cancels.  That last step is the merged `n`-th-root uniqueness engine
`exists_unit_of_nsmul_divisor_eq` (`NthRootOfPullback`, `#418`), used here in the one direction
nobody had pointed it at.

Consequently `#456` deliverable 2 — the *unconditional* Galois-equivariance — holds over an
arbitrary base field as soon as rung-5 data exists at `S` and at `σS`, and holds with no data
supplied at all over an algebraically closed field, where `exists_gS_two_of_isAlgClosed` (`#791`)
produces it.

## The route, in one line each

1. `div f' = σ_*(div f)` (point data, `divisor_eq_equivMapDomain_of_eq_single`, `#635`) gives
   `div (σ⋆ f) = div f'`, hence `f' = c · σ⋆ f` for a constant `c` (`#402` + `#398`).
2. Applying `Φ = [n]∗`, which fixes constants (`mulByTwoEndo_algebraMap_base`) and commutes with
   `σ⋆` (`galoisFunctionField_mulByTwoEndo`, `#461`), gives `Φ f' = c · σ⋆(Φ f)`.
3. Substituting the two rung-5 relations turns that into
   `a' · g' ^ n = (c · σ a) · (σ⋆ g) ^ n`, an equation between `n`-th powers up to constants.
4. Constants have trivial divisor (`divisor_algebraMap_base`), so
   `n • div g' = n • div (σ⋆ g)`, and `n` cancels place by place in `ℤ`.
5. `div g' = div (σ⋆ g) = σ_*(div g)` is exactly the hypothesis of
   `weilPairingElt_galois_of_divisor_eq`.

Step 4 is the whole trick, and it is worth naming: **an `n`-th root is pinned by its `n`-th power
up to a unit, so any identity between the powers transports to the roots.**  Nothing in this file
knows what `divisor g` is, and nothing needs to.

## Main results

* `WeierstrassCurve.Affine.CoordinateRing.divisor_eq_equivMapDomain_of_smul_pow` — the engine,
  stated for an abstract `Φ` that fixes the base field and commutes with `σ⋆`, so that the `n = 2`
  and `n = 3` instances are two applications rather than two proofs.
* `WeierstrassCurve.Affine.CoordinateRing.exists_unit_galoisFunctionField_of_smul_pow` — the
  transport hypothesis `htr` of `weilPairingElt_galois_of_transport` (`#456` deliverable 1),
  discharged from rung-5 data.
* `weilPairingElt_galois_of_gS_two`, `weilPairingMu_galois_of_gS_two` and their `n = 3` twins —
  **`#456` deliverable 2**, over an arbitrary base field, from rung-5 data at `S` and at `σS`.
* `exists_weilPairingElt_galois_two` — the same with nothing carried at all, over an algebraically
  closed base field, `exists_gS_two_of_isAlgClosed` (`#791`) supplying both roots.

## Scope

⚠️ **This is the Galois slot only.**  The translation slot has not moved: `translateEndo` is not
induced by a ring automorphism of `F[W⁄F]`, so `#630`'s divisor transport does not apply to it and
the alternating property (`#465` deliverable 2) is exactly as open as it was.  The asymmetry is
`#630`'s scope note and it survives this file.

⚠️ **`exists_gS_three` still carries its `hprin`,** so the `n = 3` statements below are the
data-carrying ones and there is no `n = 3` analogue of `exists_weilPairingElt_galois_two`.  What is
missing there is the class computation above the `[3]` fibre description — the fibre description
itself is `EllipticCurves.FunctionField.MulByThreeFibre`, merged — and not anything about the
Galois action: the `n = 3` engine instance is proved here and is waiting.

⚠️ **`[IsAlgClosed F]` appears only in the last theorem**, and only through `#791`.  The engine and
the `n = 2`/`n = 3` transport statements need `[Field S] [Field F] [Algebra S F]` and
`[W.IsElliptic]` and nothing else; in particular they are Ward-, rung-4- and normality-independent.

⚠️ **Non-degeneracy is not in scope**, and neither is `#E[n] = n²`.  `WeilPairing`'s scope section
is the canonical account of what non-degeneracy consumes (`#769`); at `n = 2` over `F̄` it is
merged as `WeilPairingNondegenerateTwo` (`#796`).

## References

* [J. H. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.8.
-/

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum

namespace WeierstrassCurve.Affine.CoordinateRing

variable {S F : Type*} [Field S] [Field F] [Algebra S F] {W : Affine S} [W.IsElliptic]

/-! ### The engine: an identity between `n`-th powers transports to the roots -/

/-- **The Galois transport of a rung-5 root is determined by the rung-5 datum alone.**

Let `Φ` be a ring endomorphism of `F(W⁄F)` that fixes the base field and commutes with the Galois
action `σ⋆` — `[2]∗` and `[3]∗` are the two instances.  If `g` and `g'` are `n`-th roots, up to
units of `F[W⁄F]`, of `Φ f` and `Φ f'`, and the divisors of `f` and `f'` are `σ`-transports of one
another, then so are the divisors of `g` and `g'`.

**No hypothesis about `divisor g` is used, and none is available**: the rung-5 root is produced
only through the relation `u · g ^ n = Φ f`, and `divisor g = [n]∗(S)` is rung-4-gated.  The point
is that the relation is enough, because the divisor group of the curve is torsion-free: the two
`n`-th powers are forced to have the same divisor, and `n` then cancels place by place.  This is
the merged `exists_unit_of_nsmul_divisor_eq` argument (`NthRootOfPullback`) applied across `σ`
rather than between two roots over the same point.

`f ≠ 0` and `f' ≠ 0` are not assumed: they follow from `g ≠ 0`, `g' ≠ 0` and the two relations. -/
theorem divisor_eq_equivMapDomain_of_smul_pow (σ : F ≃ₐ[S] F)
    {Φ : (W⁄F).FunctionField →+* (W⁄F).FunctionField}
    (hbase : ∀ c : F, Φ (algebraMap F (W⁄F).FunctionField c)
      = algebraMap F (W⁄F).FunctionField c)
    (hgal : ∀ z, galoisFunctionField σ (Φ z) = Φ (galoisFunctionField σ z))
    {n : ℕ} (hn : n ≠ 0) {f f' g g' : (W⁄F).FunctionField} (hg : g ≠ 0) (hg' : g' ≠ 0)
    {u u' : (W⁄F).CoordinateRingˣ}
    (hu : (u : (W⁄F).CoordinateRing) • g ^ n = Φ f)
    (hu' : (u' : (W⁄F).CoordinateRing) • g' ^ n = Φ f')
    (hff' : divisor (W⁄F) f'
      = (divisor (W⁄F) f).equivMapDomain (mapEquiv (galoisCoordRing σ))) :
    divisor (W⁄F) g' = (divisor (W⁄F) g).equivMapDomain (mapEquiv (galoisCoordRing σ)) := by
  -- Write the two units as nonzero constants of `F`.
  obtain ⟨a, ha⟩ := exists_eq_algebraMap_of_isUnit u.isUnit
  obtain ⟨a', ha'⟩ := exists_eq_algebraMap_of_isUnit u'.isUnit
  have ha0 : a ≠ 0 := fun h => u.ne_zero (by rw [ha, h, map_zero])
  have ha'0 : a' ≠ 0 := fun h => u'.ne_zero (by rw [ha', h, map_zero])
  have hsm : ∀ (b : F) (z : (W⁄F).FunctionField),
      (algebraMap F (W⁄F).CoordinateRing b) • z = algebraMap F (W⁄F).FunctionField b * z :=
    fun b z => by
      rw [Algebra.smul_def, ← IsScalarTower.algebraMap_apply]
  rw [ha, hsm] at hu
  rw [ha', hsm] at hu'
  have hmap : ∀ {b : F}, b ≠ 0 → algebraMap F (W⁄F).FunctionField b ≠ 0 :=
    fun hb => (map_ne_zero_iff _ (algebraMap F (W⁄F).FunctionField).injective).mpr hb
  -- `f` and `f'` are nonzero, since their `Φ`-images are.
  have hf : f ≠ 0 := by
    intro hz
    rw [hz, map_zero] at hu
    exact mul_ne_zero (hmap ha0) (pow_ne_zero n hg) hu
  have hf' : f' ≠ 0 := by
    intro hz
    rw [hz, map_zero] at hu'
    exact mul_ne_zero (hmap ha'0) (pow_ne_zero n hg') hu'
  have hσf : galoisFunctionField σ f ≠ 0 := by
    simpa using (map_ne_zero_iff _ (galoisFunctionField σ).injective).mpr hf
  have hσg : galoisFunctionField σ g ≠ 0 := by
    simpa using (map_ne_zero_iff _ (galoisFunctionField σ).injective).mpr hg
  -- Step 1: `f' = c · σ⋆ f` for a nonzero constant `c`.
  have hdf : divisor (W⁄F) (galoisFunctionField σ f) = divisor (W⁄F) f' := by
    rw [divisor_galoisFunctionField, hff']
  obtain ⟨w, hw⟩ := Elliptic.exists_unit_of_divisor_eq hσf hf' hdf
  obtain ⟨c, hc⟩ := exists_eq_algebraMap_of_isUnit w.isUnit
  have hc0 : c ≠ 0 := fun h => w.ne_zero (by rw [hc, h, map_zero])
  rw [hc, hsm] at hw
  -- Steps 2 and 3: an identity between the two `n`-th powers, up to constants.
  have key : algebraMap F (W⁄F).FunctionField a' * g' ^ n
      = algebraMap F (W⁄F).FunctionField (c * σ a) * (galoisFunctionField σ g) ^ n := by
    rw [map_mul, mul_assoc, hu', ← hw, map_mul, hbase, ← hgal, ← hu, map_mul, map_pow,
      galoisFunctionField_algebraMap]
  -- Step 4: constants have trivial divisor, and `n` cancels place by place.
  have hca : c * σ a ≠ 0 :=
    mul_ne_zero hc0 ((map_ne_zero_iff σ (EquivLike.injective σ)).mpr ha0)
  have hdiv := congrArg (divisor (W⁄F)) key
  rw [divisor_mul (hmap ha'0) (pow_ne_zero n hg'), divisor_mul (hmap hca) (pow_ne_zero n hσg),
    divisor_algebraMap_base ha'0, divisor_algebraMap_base hca, zero_add, zero_add,
    divisor_pow, divisor_pow] at hdiv
  -- Step 5: read the conclusion off `divisor_galoisFunctionField`.
  rw [← divisor_galoisFunctionField]
  ext v
  have hv := DFunLike.congr_fun hdiv v
  simp only [Finsupp.smul_apply, nsmul_eq_mul] at hv
  exact mul_left_cancel₀ (a := (n : ℤ)) (by exact_mod_cast hn) hv

/-- **The transport hypothesis `htr`, discharged from rung-5 data.**

`weilPairingElt_galois_of_transport` (`#456` deliverable 1) assumes
`galoisFunctionField σ g = u • g'`; `exists_unit_galoisFunctionField_of_divisor_eq` derives that
from a divisor hypothesis on `g`.  This derives it from the rung-5 relation instead, which is the
form in which the root is available. -/
theorem exists_unit_galoisFunctionField_of_smul_pow (σ : F ≃ₐ[S] F)
    {Φ : (W⁄F).FunctionField →+* (W⁄F).FunctionField}
    (hbase : ∀ c : F, Φ (algebraMap F (W⁄F).FunctionField c)
      = algebraMap F (W⁄F).FunctionField c)
    (hgal : ∀ z, galoisFunctionField σ (Φ z) = Φ (galoisFunctionField σ z))
    {n : ℕ} (hn : n ≠ 0) {f f' g g' : (W⁄F).FunctionField} (hg : g ≠ 0) (hg' : g' ≠ 0)
    {u u' : (W⁄F).CoordinateRingˣ}
    (hu : (u : (W⁄F).CoordinateRing) • g ^ n = Φ f)
    (hu' : (u' : (W⁄F).CoordinateRing) • g' ^ n = Φ f')
    (hff' : divisor (W⁄F) f'
      = (divisor (W⁄F) f).equivMapDomain (mapEquiv (galoisCoordRing σ))) :
    ∃ w : (W⁄F).CoordinateRingˣ,
      galoisFunctionField σ g = (w : (W⁄F).CoordinateRing) • g' :=
  exists_unit_galoisFunctionField_of_divisor_eq σ hg hg'
    (divisor_eq_equivMapDomain_of_smul_pow σ hbase hgal hn hg hg' hu hu' hff')

/-! ### `#456` deliverable 2 at `n = 2` -/

variable {x₂ y₂ x y : F}

/-- **Galois-equivariance of the Weil-pairing element at `n = 2`, from rung-5 data.**

`σ⋆(e_2(S, T)) = e_2(σS, σT)`, where the divisor-slot roots `g` at `S` and `g'` at `σS` are given
by the rung-5 relations `u · g ^ 2 = [2]∗ f` and `u' · g' ^ 2 = [2]∗ f'` over `div f = 2·(S)` and
`div f' = 2·(σS)`.  This is `#456` deliverable 2: nothing beyond rung 5 is carried, and in
particular the rung-4-gated identity `div g = [2]∗(S)` is not used.

The two inputs specific to `[2]∗` are `mulByTwoEndo_algebraMap_base` (it fixes the base field) and
`galoisFunctionField_mulByTwoEndo` (`#461`, it commutes with `σ⋆`); everything else is the engine
above. -/
theorem weilPairingElt_galois_of_gS_two (σ : F ≃ₐ[S] F) (h2 : (2 : F) ≠ 0)
    (h₂ : (W⁄F).Equation x₂ y₂) (h : (W⁄F).Equation x y)
    {f f' g g' : (W⁄F).FunctionField} (hg : g ≠ 0) (hg' : g' ≠ 0)
    (hf : divisor (W⁄F) f = Finsupp.single (pointClosedPoint h) (2 : ℤ))
    (hf' : divisor (W⁄F) f'
      = Finsupp.single (pointClosedPoint (equation_algEquiv σ h)) (2 : ℤ))
    {u u' : (W⁄F).CoordinateRingˣ}
    (hu : (u : (W⁄F).CoordinateRing) • g ^ 2 = mulByTwoEndo h2 f)
    (hu' : (u' : (W⁄F).CoordinateRing) • g' ^ 2 = mulByTwoEndo h2 f') :
    galoisFunctionField σ (weilPairingElt h₂ g)
      = weilPairingElt (equation_algEquiv σ h₂) g' :=
  weilPairingElt_galois_of_divisor_eq σ h₂ hg hg'
    (divisor_eq_equivMapDomain_of_smul_pow σ (mulByTwoEndo_algebraMap_base h2)
      (galoisFunctionField_mulByTwoEndo σ h2) two_ne_zero hg hg' hu hu'
      (divisor_eq_equivMapDomain_of_eq_single σ h hf hf'))

open Classical in
/-- **Galois-equivariance of the Weil pairing in `μ_n(F)` at `n = 2`, from rung-5 data.**
`weilPairingElt_galois_of_gS_two` in the honest value group of the pairing.

⚠️ The `n` of `μ_n(F)` is the order of the pairing value and is unrelated to the `2` of the
rung-5 relation; it arrives with the two hypotheses `hpow`, `hpow'` and is not constrained here. -/
theorem weilPairingMu_galois_of_gS_two (σ : F ≃ₐ[S] F) (h2 : (2 : F) ≠ 0)
    (h₂ : (W⁄F).Equation x₂ y₂) (h : (W⁄F).Equation x y)
    {f f' g g' : (W⁄F).FunctionField} {n : ℕ} [NeZero n] (hg : g ≠ 0) (hg' : g' ≠ 0)
    (hf : divisor (W⁄F) f = Finsupp.single (pointClosedPoint h) (2 : ℤ))
    (hf' : divisor (W⁄F) f'
      = Finsupp.single (pointClosedPoint (equation_algEquiv σ h)) (2 : ℤ))
    {u u' : (W⁄F).CoordinateRingˣ}
    (hu : (u : (W⁄F).CoordinateRing) • g ^ 2 = mulByTwoEndo h2 f)
    (hu' : (u' : (W⁄F).CoordinateRing) • g' ^ 2 = mulByTwoEndo h2 f')
    (hpow : weilPairingElt h₂ g ^ n = 1)
    (hpow' : weilPairingElt (equation_algEquiv σ h₂) g' ^ n = 1) :
    restrictRootsOfUnity (σ.toRingEquiv.toRingHom) n (weilPairingMu h₂ hpow)
      = weilPairingMu (equation_algEquiv σ h₂) hpow' :=
  weilPairingMu_galois_of_divisor_eq σ h₂ hg hg'
    (divisor_eq_equivMapDomain_of_smul_pow σ (mulByTwoEndo_algebraMap_base h2)
      (galoisFunctionField_mulByTwoEndo σ h2) two_ne_zero hg hg' hu hu'
      (divisor_eq_equivMapDomain_of_eq_single σ h hf hf')) hpow hpow'

/-! ### `#456` deliverable 2 at `n = 3` -/

/-- **Galois-equivariance of the Weil-pairing element at `n = 3`, from rung-5 data.**  The
`mulByThreeEndo` mirror of `weilPairingElt_galois_of_gS_two`, with the same two `[3]∗`-specific
inputs (`mulByThreeEndo_algebraMap_base` and `galoisFunctionField_mulByThreeEndo`, `#461`).

⚠️ Unlike at `n = 2`, there is no unconditional companion: `exists_gS_three` keeps its `hprin`, so
the rung-5 data below has to be supplied.  That gap is the class computation above the `[3]`
fibre description — not `#404`, which is the general `ωₙ`, and not anything Galois-theoretic. -/
theorem weilPairingElt_galois_of_gS_three (σ : F ≃ₐ[S] F) (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0)
    (h₂ : (W⁄F).Equation x₂ y₂) (h : (W⁄F).Equation x y)
    {f f' g g' : (W⁄F).FunctionField} (hg : g ≠ 0) (hg' : g' ≠ 0)
    (hf : divisor (W⁄F) f = Finsupp.single (pointClosedPoint h) (3 : ℤ))
    (hf' : divisor (W⁄F) f'
      = Finsupp.single (pointClosedPoint (equation_algEquiv σ h)) (3 : ℤ))
    {u u' : (W⁄F).CoordinateRingˣ}
    (hu : (u : (W⁄F).CoordinateRing) • g ^ 3 = mulByThreeEndo h2 h3 f)
    (hu' : (u' : (W⁄F).CoordinateRing) • g' ^ 3 = mulByThreeEndo h2 h3 f') :
    galoisFunctionField σ (weilPairingElt h₂ g)
      = weilPairingElt (equation_algEquiv σ h₂) g' :=
  weilPairingElt_galois_of_divisor_eq σ h₂ hg hg'
    (divisor_eq_equivMapDomain_of_smul_pow σ (mulByThreeEndo_algebraMap_base h2 h3)
      (galoisFunctionField_mulByThreeEndo σ h2 h3) three_ne_zero hg hg' hu hu'
      (divisor_eq_equivMapDomain_of_eq_single σ h hf hf'))

open Classical in
/-- **Galois-equivariance of the Weil pairing in `μ_n(F)` at `n = 3`, from rung-5 data.** -/
theorem weilPairingMu_galois_of_gS_three (σ : F ≃ₐ[S] F) (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0)
    (h₂ : (W⁄F).Equation x₂ y₂) (h : (W⁄F).Equation x y)
    {f f' g g' : (W⁄F).FunctionField} {n : ℕ} [NeZero n] (hg : g ≠ 0) (hg' : g' ≠ 0)
    (hf : divisor (W⁄F) f = Finsupp.single (pointClosedPoint h) (3 : ℤ))
    (hf' : divisor (W⁄F) f'
      = Finsupp.single (pointClosedPoint (equation_algEquiv σ h)) (3 : ℤ))
    {u u' : (W⁄F).CoordinateRingˣ}
    (hu : (u : (W⁄F).CoordinateRing) • g ^ 3 = mulByThreeEndo h2 h3 f)
    (hu' : (u' : (W⁄F).CoordinateRing) • g' ^ 3 = mulByThreeEndo h2 h3 f')
    (hpow : weilPairingElt h₂ g ^ n = 1)
    (hpow' : weilPairingElt (equation_algEquiv σ h₂) g' ^ n = 1) :
    restrictRootsOfUnity (σ.toRingEquiv.toRingHom) n (weilPairingMu h₂ hpow)
      = weilPairingMu (equation_algEquiv σ h₂) hpow' :=
  weilPairingMu_galois_of_divisor_eq σ h₂ hg hg'
    (divisor_eq_equivMapDomain_of_smul_pow σ (mulByThreeEndo_algebraMap_base h2 h3)
      (galoisFunctionField_mulByThreeEndo σ h2 h3) three_ne_zero hg hg' hu hu'
      (divisor_eq_equivMapDomain_of_eq_single σ h hf hf')) hpow hpow'

/-! ### Nothing carried, over an algebraically closed base field -/

open Classical in
/-- **`#456` deliverable 2 at `n = 2` with no hypothesis beyond the setting.**

For a nonsingular affine `2`-torsion point `S` of `W⁄F` over an algebraically closed `F` of
characteristic `≠ 2`, there are rung-5 roots `g` at `S` and `g'` at `σS` — produced by
`exists_gS_two_of_isAlgClosed` (`#791`), which is `exists_gS_two` with `hprin` discharged — for
which `σ⋆(e_2(S, T)) = e_2(σS, σT)`.

`σS` is again a nonsingular affine `2`-torsion point (`nonsingular_algEquiv`,
`mem_torsion_galois_smul_some`), which is why the same producer applies at both points; the two
roots are otherwise unrelated, and `g'` is emphatically *not* `σ⋆ g` — the constant relating them
is exactly what the pairing quotient cancels.

⚠️ The rung-5 data is returned rather than discarded, because the pairing element depends on the
root: `weilPairingElt` takes `g` as an argument.  A consumer that has its own root should use
`weilPairingElt_galois_of_gS_two` and feed it in. -/
theorem exists_weilPairingElt_galois_two [IsAlgClosed F] (σ : F ≃ₐ[S] F) (h2 : (2 : F) ≠ 0)
    (h₂ : (W⁄F).Equation x₂ y₂) (h : (W⁄F).Nonsingular x y)
    (hS : Point.some x y h ∈ (W⁄F).torsion 2) :
    ∃ g g' : (W⁄F).FunctionField, g ≠ 0 ∧ g' ≠ 0 ∧
      (∃ f : (W⁄F).FunctionField, f ≠ 0 ∧
        divisor (W⁄F) f = Finsupp.single (pointClosedPoint h.left) (2 : ℤ) ∧
        ∃ u : (W⁄F).CoordinateRingˣ,
          (u : (W⁄F).CoordinateRing) • g ^ 2 = mulByTwoEndo h2 f) ∧
      (∃ f' : (W⁄F).FunctionField, f' ≠ 0 ∧
        divisor (W⁄F) f'
          = Finsupp.single (pointClosedPoint (equation_algEquiv σ h.left)) (2 : ℤ) ∧
        ∃ u' : (W⁄F).CoordinateRingˣ,
          (u' : (W⁄F).CoordinateRing) • g' ^ 2 = mulByTwoEndo h2 f') ∧
      galoisFunctionField σ (weilPairingElt h₂ g)
        = weilPairingElt (equation_algEquiv σ h₂) g' := by
  obtain ⟨f, hf, hfdiv, g, hg, u, hu⟩ := exists_gS_two_of_isAlgClosed h2 h hS
  obtain ⟨f', hf', hf'div, g', hg', u', hu'⟩ :=
    exists_gS_two_of_isAlgClosed h2 (nonsingular_algEquiv σ h)
      (Point.mem_torsion_galois_smul_some σ h hS)
  exact ⟨g, g', hg, hg', ⟨f, hf, hfdiv, u, hu⟩, ⟨f', hf', hf'div, u', hu'⟩,
    weilPairingElt_galois_of_gS_two σ h2 h₂ h.left hg hg' hfdiv hf'div hu hu'⟩

/-! ### Non-vacuity

The theorems above quantify over a base field `S`, an extension `F` and an `S`-automorphism of `F`;
the last one additionally needs `[IsAlgClosed F]` and a nonsingular affine `2`-torsion point of
`W⁄F`.  `y² = x³ − x` over `ℚ`, base-changed to `AlgebraicClosure ℚ`, supplies all of it with the
torsion point **named**: it is `(0, 0)`, and it is already rational, so the certificate exhibits the
statement rather than the action.  This is the curve `#758`/`#759`/`#763`/`#774`/`#791`/`#796` all
use; here it is the *base* curve, since a Galois statement needs two fields and the rest of
`FunctionField/` only needs one. -/

section Nonvacuity

/-- The curve `y² = x³ − x` over `ℚ`, of discriminant `64`. -/
private noncomputable def exampleCurve : Affine ℚ := ⟨0, 0, 0, -1, 0⟩

/-- An algebraically closed extension of `ℚ`. -/
private abbrev exampleField : Type := AlgebraicClosure ℚ

private instance : exampleCurve.IsElliptic := by
  rw [WeierstrassCurve.isElliptic_iff, isUnit_iff_ne_zero]
  norm_num [exampleCurve, WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈]

private lemma exampleTwo : (2 : exampleField) ≠ 0 := by norm_num

/-- `S = (0, 0)` lies on the base-changed curve and is nonsingular. -/
private lemma exampleNonsingular : (exampleCurve⁄exampleField).Nonsingular 0 0 :=
  (exampleCurve⁄exampleField).equation_iff_nonsingular.mp (by
    simp [exampleCurve, WeierstrassCurve.Affine.equation_iff])

open Classical in
/-- `S = (0, 0)` is `2`-torsion: `2y + a₁x + a₃ = 0` reads `0 = 0`. -/
private lemma exampleTorsion :
    Point.some (0 : exampleField) 0 exampleNonsingular ∈ (exampleCurve⁄exampleField).torsion 2 :=
  (mem_torsion_two_some_iff exampleNonsingular).mpr (by simp [exampleCurve])

open Classical in
/-- **Galois-equivariance of the Weil pairing at `n = 2`, on a curve that exists**, with the base
field, the extension and the `2`-torsion point all named. -/
example (σ : exampleField ≃ₐ[ℚ] exampleField) {x₂ y₂ : exampleField}
    (h₂ : (exampleCurve⁄exampleField).Equation x₂ y₂) :
    ∃ g g' : (exampleCurve⁄exampleField).FunctionField, g ≠ 0 ∧ g' ≠ 0 ∧
      (∃ f : (exampleCurve⁄exampleField).FunctionField, f ≠ 0 ∧
        divisor (exampleCurve⁄exampleField) f
          = Finsupp.single (pointClosedPoint exampleNonsingular.left) (2 : ℤ) ∧
        ∃ u : (exampleCurve⁄exampleField).CoordinateRingˣ,
          (u : (exampleCurve⁄exampleField).CoordinateRing) • g ^ 2
            = mulByTwoEndo exampleTwo f) ∧
      (∃ f' : (exampleCurve⁄exampleField).FunctionField, f' ≠ 0 ∧
        divisor (exampleCurve⁄exampleField) f'
          = Finsupp.single
              (pointClosedPoint (equation_algEquiv σ exampleNonsingular.left)) (2 : ℤ) ∧
        ∃ u' : (exampleCurve⁄exampleField).CoordinateRingˣ,
          (u' : (exampleCurve⁄exampleField).CoordinateRing) • g' ^ 2
            = mulByTwoEndo exampleTwo f') ∧
      galoisFunctionField σ (weilPairingElt h₂ g)
        = weilPairingElt (equation_algEquiv σ h₂) g' :=
  exists_weilPairingElt_galois_two σ exampleTwo h₂ exampleNonsingular exampleTorsion

end Nonvacuity

end WeierstrassCurve.Affine.CoordinateRing
