/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import EllipticCurves.FunctionField.WeilPairingConstant

/-!
# The Weil-pairing element as a genuine element of `μ_n(F)` (rung 6)

Let `W` be an elliptic curve over a field `F`.  The Weil-pairing element
(`WeilPairing.lean`, issue #419)

```
e_n(S, T) := weilPairingElt h₂ g = τ_T∗(g) / g,   τ_T∗ = translateEndo h₂ : F(W) →+* F(W),
```

is known to be a base-field **constant** `algebraMap F F(W) c` whose constant `c` is an `n`-th root
of unity, `c ^ n = 1` (`weilPairingElt_isRootOfUnity`, `WeilPairingConstant.lean`, issue #454).
That statement lives at the level of "there is a constant `c : F` with `c ^ n = 1`"; this file
packages it as membership in the *group* of `n`-th roots of unity, `μ_n(F) = rootsOfUnity n F`, a
subgroup of `Fˣ`.  This is the honest codomain of the Weil pairing `E[n] × E[n] → μ_n` (Silverman
AEC III.8): the value is not merely *a* constant satisfying `c ^ n = 1`, it is a bona fide
element of the finite cyclic group `μ_n(F)`.

## Main results

* `weilPairingMu` — the Weil-pairing element packaged as an element of `rootsOfUnity n F`, from
  `e_n(S, T) ^ n = 1` (`n ≠ 0`, as `[NeZero n]`);
* `algebraMap_coe_weilPairingMu` — its defining property: pushing `weilPairingMu` down `Fˣ → F` and
  then up `algebraMap F F(W)` recovers `e_n(S, T)`;
* `weilPairingElt_mem_range_algebraMap_rootsOfUnity` — the plain existential form: `e_n(S, T)` is
  the `algebraMap`-image of some `μ_n(F)` element;
* `weilPairingMu_of_gS'` / `_of_gS_three'` — the concrete `n = 2` / `n = 3` instances over the
  combined data `weilPairingElt_pow_eq_one_of_gS'` / `_three'`, mirroring
  `weilPairingElt_isRootOfUnity_of_gS'` / `_three'`.

## Scope

Ward- and normality-independent: needs only `[Field F] [W.IsElliptic]` and the root-of-unity input
(already delivered).  Non-degeneracy remains out of scope (Ward-gated, #242).

## References

* [J. Silverman, *The arithmetic of elliptic curves*][silverman2009], III.8.
-/

namespace WeierstrassCurve.Affine

namespace CoordinateRing

variable {F : Type*} [Field F] {W : Affine F}

/-- **The Weil-pairing element as an element of `μ_n(F)`.**  From `e_n(S, T) ^ n = 1` (`n ≠ 0`,
carried as `[NeZero n]`), `weilPairingElt_isRootOfUnity` produces a constant `c : F` with
`e_n(S, T) = algebraMap F F(W) c` and `c ^ n = 1`; `rootsOfUnity.mkOfPowEq` packages that `c` as a
genuine element of the group `μ_n(F) = rootsOfUnity n F ≤ Fˣ`.  Its `algebraMap`-image is
`e_n(S, T)` (`algebraMap_coe_weilPairingMu`). -/
noncomputable def weilPairingMu [W.IsElliptic] {x₂ y₂ : F} (h₂ : W.Equation x₂ y₂)
    {g : W.FunctionField} {n : ℕ} [NeZero n] (hpow : weilPairingElt h₂ g ^ n = 1) :
    rootsOfUnity n F :=
  rootsOfUnity.mkOfPowEq
    (Classical.choose (weilPairingElt_isRootOfUnity h₂ (NeZero.ne n) hpow))
    (Classical.choose_spec (weilPairingElt_isRootOfUnity h₂ (NeZero.ne n) hpow)).2

/-- **Defining property of `weilPairingMu`.**  Coercing the `μ_n(F)` element `weilPairingMu` down to
`F` (through `Fˣ`) and applying `algebraMap F F(W)` recovers the pairing value `e_n(S, T)`. -/
@[simp]
theorem algebraMap_coe_weilPairingMu [W.IsElliptic] {x₂ y₂ : F} (h₂ : W.Equation x₂ y₂)
    {g : W.FunctionField} {n : ℕ} [NeZero n] (hpow : weilPairingElt h₂ g ^ n = 1) :
    algebraMap F W.FunctionField ((weilPairingMu h₂ hpow : Fˣ) : F) = weilPairingElt h₂ g := by
  rw [weilPairingMu, rootsOfUnity.coe_mkOfPowEq]
  exact (Classical.choose_spec (weilPairingElt_isRootOfUnity h₂ (NeZero.ne n) hpow)).1.symm

/-- **The Weil-pairing element is the `algebraMap`-image of a `μ_n(F)` element** (plain existential
form of `weilPairingMu`). -/
theorem weilPairingElt_mem_range_algebraMap_rootsOfUnity [W.IsElliptic] {x₂ y₂ : F}
    (h₂ : W.Equation x₂ y₂) {g : W.FunctionField} {n : ℕ} [NeZero n]
    (hpow : weilPairingElt h₂ g ^ n = 1) :
    ∃ ζ : rootsOfUnity n F, algebraMap F W.FunctionField ((ζ : Fˣ) : F) = weilPairingElt h₂ g :=
  ⟨weilPairingMu h₂ hpow, algebraMap_coe_weilPairingMu h₂ hpow⟩

/-- **The `n = 2`-track Weil-pairing element as an element of `μ_n(F)`.**  Feeds the concrete
combined datum `weilPairingElt_pow_eq_one_of_gS'` to `weilPairingMu`, mirroring
`weilPairingElt_isRootOfUnity_of_gS'`. -/
noncomputable def weilPairingMu_of_gS' [W.IsElliptic] {x₂ y₂ : F} (h₂ : W.Equation x₂ y₂)
    (h2 : (2 : F) ≠ 0) {f g : W.FunctionField} {u : W.CoordinateRingˣ} {n : ℕ} [NeZero n]
    (hg : g ≠ 0) (hu : (u : W.CoordinateRing) • g ^ n = mulByTwoEndo h2 f)
    (hcomm : translateEndo h₂ (mulByTwoEndo h2 f) = mulByTwoEndo h2 f) :
    rootsOfUnity n F :=
  weilPairingMu h₂ (weilPairingElt_pow_eq_one_of_gS' h₂ h2 hg hu hcomm)

/-- **The `n = 3`-track Weil-pairing element as an element of `μ_n(F)`.**  The `mulByThreeEndo`
mirror of `weilPairingMu_of_gS'`, over the concrete datum
`weilPairingElt_pow_eq_one_of_gS_three'`. -/
noncomputable def weilPairingMu_of_gS_three' [W.IsElliptic] {x₂ y₂ : F} (h₂ : W.Equation x₂ y₂)
    (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) {f g : W.FunctionField} {u : W.CoordinateRingˣ} {n : ℕ}
    [NeZero n] (hg : g ≠ 0) (hu : (u : W.CoordinateRing) • g ^ n = mulByThreeEndo h2 h3 f)
    (hcomm : translateEndo h₂ (mulByThreeEndo h2 h3 f) = mulByThreeEndo h2 h3 f) :
    rootsOfUnity n F :=
  weilPairingMu h₂ (weilPairingElt_pow_eq_one_of_gS_three' h₂ h2 h3 hg hu hcomm)

end CoordinateRing

end WeierstrassCurve.Affine
