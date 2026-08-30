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
* `weilPairingMu_eq_one_iff` — the `μ_n(F)` value is the group identity exactly when `e_n(S, T)`
  is `1` in `F(W)`, with **no `g ≠ 0` hypothesis** (moved here from `WeilPairingAntisymmetricMu`
  by `#883`);
* `weilPairingMu_ne_one_iff` — its contrapositive, which is what carries a non-degeneracy witness
  from `F(W)` into the group;
* `weilPairingElt_mem_range_algebraMap_rootsOfUnity` — the plain existential form: `e_n(S, T)` is
  the `algebraMap`-image of some `μ_n(F)` element;
* `weilPairingMu_of_gS_two'` / `_of_gS_three'` — the concrete `n = 2` / `n = 3` instances over the
  combined data `weilPairingElt_pow_eq_one_of_gS_two'` / `_three'`, mirroring
  `weilPairingElt_isRootOfUnity_of_gS_two'` / `_three'`.

## Scope

Ward- and normality-independent: needs only `[Field F] [W.IsElliptic]` and the root-of-unity input
(already delivered).  Non-degeneracy itself remains out of scope — the witness `e_n(S, T) ≠ 1` is
built in `WeilPairingNondegenerateTwo` / `...Three` — and it is **not** Ward-gated;
`WeilPairing`'s scope section is the canonical account of what it consumes (#769).  What *is* here
is the transport `weilPairingMu_ne_one_iff`, which is about `weilPairingMu` and not about
non-degeneracy: it says the packaging into `μ_n(F)` loses no information, whatever the value.

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

/-- **`weilPairingMu` is the group identity of `μ_n(F)` exactly when the pairing element is `1` in
`F(W)`.**

```
weilPairingMu h₂ hpow = 1 ↔ weilPairingElt h₂ g = 1.
```

Unlike `weilPairingMu_eq_one_iff_translateEndo_fixed` (`WeilPairingAlternatingMu.lean`) this needs
**no `g ≠ 0` hypothesis**: the comparison is between `weilPairingElt` and `1`, and never between
`τ_T∗ g` and `g`, so the degenerate case `g = 0` — where `e_n(0, T) = 0 / 0 = 0 ≠ 1` — is decided
correctly on both sides rather than excluded.

Both directions are the defining property `algebraMap_coe_weilPairingMu` (`#457`) together with
`algebraMap F F(W) 1 = 1`; the backward one additionally needs that composite to be injective,
which it is because `algebraMap F F(W)` is a ring hom out of a field.

⚠️ This lemma was first written in `WeilPairingAntisymmetricMu` (`#733`), downstream of the
definition it is about, and moved here by `#883` so that non-degeneracy can reach it.  The proof
changed in exactly one way: it no longer routes the backward direction through
`algebraMap_coe_rootsOfUnity_injective` (`WeilPairingBilinearMu`, `#459`), which is itself
downstream, but through `RingHom.injective` directly.  The statement is unchanged, binder for
binder. -/
theorem weilPairingMu_eq_one_iff [W.IsElliptic] {x₂ y₂ : F} (h₂ : W.Equation x₂ y₂)
    {g : W.FunctionField} {n : ℕ} [NeZero n] (hpow : weilPairingElt h₂ g ^ n = 1) :
    weilPairingMu h₂ hpow = 1 ↔ weilPairingElt h₂ g = 1 := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rw [← algebraMap_coe_weilPairingMu h₂ hpow, h]
    simp
  · have := (algebraMap_coe_weilPairingMu h₂ hpow).trans h
    rw [show (1 : W.FunctionField) = algebraMap F W.FunctionField 1 by simp] at this
    exact Subtype.ext (Units.ext ((algebraMap F W.FunctionField).injective this))

/-- **`weilPairingMu` is non-trivial exactly when `e_n(S, T)` is**, the contrapositive form of
`weilPairingMu_eq_one_iff`.  This is the direction non-degeneracy consumes: a witness
`e_n(S, T) ≠ 1` in `F(W)` is a witness in the group `μ_n(F)`. -/
theorem weilPairingMu_ne_one_iff [W.IsElliptic] {x₂ y₂ : F} (h₂ : W.Equation x₂ y₂)
    {g : W.FunctionField} {n : ℕ} [NeZero n] (hpow : weilPairingElt h₂ g ^ n = 1) :
    weilPairingMu h₂ hpow ≠ 1 ↔ weilPairingElt h₂ g ≠ 1 :=
  (weilPairingMu_eq_one_iff h₂ hpow).not

/-- **The Weil-pairing element is the `algebraMap`-image of a `μ_n(F)` element** (plain existential
form of `weilPairingMu`). -/
theorem weilPairingElt_mem_range_algebraMap_rootsOfUnity [W.IsElliptic] {x₂ y₂ : F}
    (h₂ : W.Equation x₂ y₂) {g : W.FunctionField} {n : ℕ} [NeZero n]
    (hpow : weilPairingElt h₂ g ^ n = 1) :
    ∃ ζ : rootsOfUnity n F, algebraMap F W.FunctionField ((ζ : Fˣ) : F) = weilPairingElt h₂ g :=
  ⟨weilPairingMu h₂ hpow, algebraMap_coe_weilPairingMu h₂ hpow⟩

/-- **The `n = 2`-track Weil-pairing element as an element of `μ_n(F)`.**  Feeds the concrete
combined datum `weilPairingElt_pow_eq_one_of_gS_two'` to `weilPairingMu`, mirroring
`weilPairingElt_isRootOfUnity_of_gS_two'`.

⚠️ `nolint defsWithUnderscore` (`#1277`): the `_of_gS_two'` suffix names the concrete rung-5 datum
this is built from, and is shared verbatim with the theorems
`weilPairingElt_pow_eq_one_of_gS_two'` and `weilPairingElt_isRootOfUnity_of_gS_two'` that it
consumes. -/
@[nolint defsWithUnderscore]
noncomputable def weilPairingMu_of_gS_two' [W.IsElliptic] {x₂ y₂ : F} (h₂ : W.Equation x₂ y₂)
    (h2 : (2 : F) ≠ 0) {f g : W.FunctionField} {u : W.CoordinateRingˣ} {n : ℕ} [NeZero n]
    (hg : g ≠ 0) (hu : (u : W.CoordinateRing) • g ^ n = mulByTwoEndo h2 f)
    (hcomm : translateEndo h₂ (mulByTwoEndo h2 f) = mulByTwoEndo h2 f) :
    rootsOfUnity n F :=
  weilPairingMu h₂ (weilPairingElt_pow_eq_one_of_gS_two' h₂ h2 hg hu hcomm)

/-- **The `n = 3`-track Weil-pairing element as an element of `μ_n(F)`.**  The `mulByThreeEndo`
mirror of `weilPairingMu_of_gS_two'`, over the concrete datum
`weilPairingElt_pow_eq_one_of_gS_three'`.

⚠️ `nolint defsWithUnderscore` (`#1277`): as for `weilPairingMu_of_gS_two'` — the suffix is shared
with the theorem supplying the datum. -/
@[nolint defsWithUnderscore]
noncomputable def weilPairingMu_of_gS_three' [W.IsElliptic] {x₂ y₂ : F} (h₂ : W.Equation x₂ y₂)
    (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) {f g : W.FunctionField} {u : W.CoordinateRingˣ} {n : ℕ}
    [NeZero n] (hg : g ≠ 0) (hu : (u : W.CoordinateRing) • g ^ n = mulByThreeEndo h2 h3 f)
    (hcomm : translateEndo h₂ (mulByThreeEndo h2 h3 f) = mulByThreeEndo h2 h3 f) :
    rootsOfUnity n F :=
  weilPairingMu h₂ (weilPairingElt_pow_eq_one_of_gS_three' h₂ h2 h3 hg hu hcomm)

end CoordinateRing

end WeierstrassCurve.Affine
