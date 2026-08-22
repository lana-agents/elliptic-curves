/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import EllipticCurves.FunctionField.WeilPairingAntisymmetricMu

/-!
# The divisor slot of `e_n` as a homomorphism into `μ_n(F)` (rung 6)

Let `W` be an elliptic curve over a field `F`.  Divisor-slot multiplicativity of the Weil-pairing
element (`WeilPairing.lean`, `#419`)

```
e_n(S, T) := weilPairingElt h_T g_S = τ_T∗(g_S) / g_S,   τ_T∗ = translateEndo h_T,
```

is merged at both levels — `weilPairingElt_mul` / `weilPairingElt_one` / `weilPairingElt_inv`
(`#723`) in `F(W)`, and `weilPairingMu_mul` / `weilPairingMu_inv` (`#733`) in the value group
`μ_n(F) = rootsOfUnity n F ≤ Fˣ`.  All of those are *pointwise* equations, one element at a time.

Silverman *AEC* III.8's `e_n` is a **pairing of groups**, and that is a statement about maps.  This
file supplies the map: the divisor slot bundled as a `MonoidHom` into `μ_n(F)`.

## The obstruction, and how it is removed

`weilPairingMu h₂ hpow` takes the root-of-unity datum `hpow : e_n(g, T) ^ n = 1` as an *argument*,
so it is not a function of `g` alone and there is nothing whose `map_mul` field could be filled.
This is why `#723` and `#733` both placed the bundling out of scope.

The fix is to make the datum a **membership** rather than an argument.  The set of `g` carrying one
is a submonoid of `F(W)`, because `#733` already supplies its two closure properties:

```lean
weilPairingElt_one           : e_n(1, T) = 1                          -- one_mem'
weilPairingElt_mul_pow_eq_one : … → … → e_n(g₁ * g₂, T) ^ n = 1        -- mul_mem'
weilPairingElt_inv_pow_eq_one : … → e_n(g⁻¹, T) ^ n = 1                -- inverse-closure
```

`#733` recorded those two `_pow_eq_one` companions precisely so a caller could *manufacture* a
datum instead of assuming it; here they are the structure fields.  Membership in
`weilPairingRootSubmonoid h₂ n` then *is* the `hpow` datum, `weilPairingMuHom` is a genuine
`MonoidHom`, and `map_pow` / `MonoidHom.mker` come for free.

⚠️ `map_mul'` typechecks only because **`weilPairingMu h₂ hpow` is proof-irrelevant in `hpow`**: it
is `Classical.choose` of a `Prop`, so two propositionally equal data give a *definitionally* equal
value.  That is also why `weilPairingMu_mul` can take three independent `hpow` arguments with no
transport lemma.  A reader who does not know this will expect a coherence obligation that is not
there.

## Main results

* `weilPairingEltHom` — the divisor slot as a monoid-with-zero hom `F(W) →*₀ F(W)`, off
  `weilPairingElt_one` / `weilPairingElt_mul` and `e_n(0, T) = 0 / 0 = 0`;
* `weilPairingElt_pow` — its immediate payoff, `e_n(g ^ k, T) = e_n(g, T) ^ k`, which the
  pointwise development did not have;
* `weilPairingRootSubmonoid` — the `g` carrying a root-of-unity datum, as a `Submonoid F(W)`, with
  `ne_zero_of_mem_weilPairingRootSubmonoid` and closure under inverses;
* **`weilPairingMuHom`** — the headline, `weilPairingRootSubmonoid h₂ n →* rootsOfUnity n F`, with
  the computation rules `weilPairingMuHom_apply` and `algebraMap_coe_weilPairingMuHom`;
* `weilPairingMuHom_pow`, `weilPairingMuHom_inv`, `weilPairingMuHom_eq_one_iff` and
  `mem_mker_weilPairingMuHom_iff` — the consequences of being a hom;
* `weilPairingRootSubgroup` and **`weilPairingMuHomUnits`** — the same map on units, as a
  homomorphism *of groups* `weilPairingRootSubgroup h₂ n →* μ_n(F)`, where `map_inv`, `map_zpow`
  and the genuine subgroup kernel `mem_ker_weilPairingMuHomUnits_iff` are free rather than
  hand-stated.

## Scope

`[Field F] {W : Affine F} [W.IsElliptic]` throughout, plus the `[NeZero n]` that `weilPairingMu`
itself carries.  **No `[IsDedekindDomain W.CoordinateRing]`, no `[IsAlgClosed F]`, no `#418`, no
rung 4, no Ward.**  Every input consumed here is merged and unconditional, so this file is ungated
end to end and adds no gate.

Out of scope: the **translation** slot.  `weilPairingMu_translatePoint_add_of_baseField`
(`WeilPairingBilinearMu.lean`, `#459`) is indexed by three `W.Equation` proofs together with
`hadd : torsionPoint hP + torsionPoint hQ = torsionPoint hR`, so bundling *it* needs a map out of
the torsion subgroup of `W.Point` rather than out of a subobject of `F(W)`, and it carries `hg`
and three separate `hpow` data besides.  That is a strictly harder statement and nothing here
implies it.  Also out of scope: producing `hprod`/`hprin` (rung 4/5, `#414`/`#418`), so
`weilPairingMu_divisorSlot_add` and the antisymmetry headlines are untouched and their gates are
neither moved nor restated; Galois-equivariance (`#456`); base change (`#692`); non-degeneracy
(Ward-gated, `#242`).

## Non-vacuity

Every declaration in this file is unconditional given `[W.IsElliptic]`, a `W.Equation` for the
translation point and `[NeZero n]`, so all of them are instantiated below on `y² = x³ − x` over
`AlgebraicClosure ℚ` with `T = (0, 0)` — the certificate curve `WeilPairingAntisymmetricMu`,
`WeilPairingAlternatingTwo` and `WeilPairingRootIndependence` use.  Every instance is closed
outright: no `hpow` datum survives as a hypothesis anywhere, because membership in the submonoid
now *is* that datum and the members exhibited (`1`, a nonzero constant, their powers, inverses and
products) carry theirs by proof.  The only hypothesis left anywhere is `c ≠ 0` on the constant.
The two `_apply` rules are `rfl`, so they are not certified separately.

## References

* [J. Silverman, *The arithmetic of elliptic curves*][silverman2009], III.8.1(a); III.8 for the
  value group `μ_n` and for `e_n` being a pairing of groups.
-/

namespace WeierstrassCurve.Affine

namespace CoordinateRing

variable {F : Type*} [Field F] {W : Affine F} [W.IsElliptic]

/-! ### The divisor slot as a monoid-with-zero hom on `F(W)`

Below the `μ_n` layer, `g ↦ e_n(g, T)` is already a homomorphism of the multiplicative monoid of
`F(W)`: `weilPairingElt_one` and `weilPairingElt_mul` (`#723`) are its two fields, and it sends `0`
to `τ_T∗(0) / 0 = 0 / 0 = 0`.  Bundling it here is what makes `map_pow` available at the `F(W)`
level as well as at the group level. -/

/-- **The divisor slot of the Weil-pairing element, as a monoid-with-zero homomorphism
`F(W) →*₀ F(W)`.**

```
g ↦ e_n(g, T) = τ_T∗(g) / g.
```

`map_one'` is `weilPairingElt_one`, `map_mul'` is `weilPairingElt_mul` and `map_zero'` is
`0 / 0 = 0` in the field `F(W)`; all three are hypothesis-free (`#723`), so this needs nothing
beyond the `W.Equation` for the translation point. -/
noncomputable def weilPairingEltHom {x₂ y₂ : F} (h₂ : W.Equation x₂ y₂) :
    W.FunctionField →*₀ W.FunctionField where
  toFun g := weilPairingElt h₂ g
  map_one' := weilPairingElt_one h₂
  map_mul' := weilPairingElt_mul h₂
  map_zero' := by simp only [weilPairingElt, map_zero, div_zero]

@[simp]
theorem weilPairingEltHom_apply {x₂ y₂ : F} (h₂ : W.Equation x₂ y₂) (g : W.FunctionField) :
    weilPairingEltHom h₂ g = weilPairingElt h₂ g :=
  rfl

/-- **`e_n(g ^ k, T) = e_n(g, T) ^ k`.**  The divisor slot respects powers, immediately from
`weilPairingEltHom` being a monoid hom.  Not available before the bundling: the pointwise
development of `#723` has only the binary `weilPairingElt_mul`.

Not to be confused with `weilPairingElt_pow_eq_one` (`WeilPairingConstant.lean`, `#454`), which is
the statement that `e_n(g, T) ^ n = 1` for the *particular* exponent `n`. -/
@[simp]
theorem weilPairingElt_pow {x₂ y₂ : F} (h₂ : W.Equation x₂ y₂) (g : W.FunctionField) (k : ℕ) :
    weilPairingElt h₂ (g ^ k) = weilPairingElt h₂ g ^ k :=
  map_pow (weilPairingEltHom h₂) g k

/-! ### The `g` carrying a root-of-unity datum, as a submonoid -/

/-- **The functions whose Weil-pairing element is an `n`-th root of unity, as a submonoid of
`F(W)`.**

```
weilPairingRootSubmonoid h₂ n = {g : F(W) | e_n(g, T) ^ n = 1}.
```

`one_mem'` is `weilPairingElt_one` and `mul_mem'` is `weilPairingElt_mul_pow_eq_one` (`#733`).
Membership here *is* the `hpow` datum that `weilPairingMu` consumes, which is exactly what makes
the divisor slot bundle into a `MonoidHom` (`weilPairingMuHom`). -/
def weilPairingRootSubmonoid {x₂ y₂ : F} (h₂ : W.Equation x₂ y₂) (n : ℕ) :
    Submonoid W.FunctionField where
  carrier := {g | weilPairingElt h₂ g ^ n = 1}
  one_mem' := by
    change weilPairingElt h₂ (1 : W.FunctionField) ^ n = 1
    rw [weilPairingElt_one, one_pow]
  mul_mem' hg₁ hg₂ := weilPairingElt_mul_pow_eq_one h₂ hg₁ hg₂

@[simp]
theorem mem_weilPairingRootSubmonoid_iff {x₂ y₂ : F} (h₂ : W.Equation x₂ y₂) {n : ℕ}
    {g : W.FunctionField} :
    g ∈ weilPairingRootSubmonoid h₂ n ↔ weilPairingElt h₂ g ^ n = 1 :=
  Iff.rfl

/-- **No member of `weilPairingRootSubmonoid h₂ n` is `0`.**  `e_n(0, T) = 0 / 0 = 0` and
`0 ^ n = 0 ≠ 1` for `n ≠ 0`, so the submonoid consists of units of `F(W)` — which is what lets the
same carrier be read as a `Subgroup W.FunctionFieldˣ` (`weilPairingRootSubgroup`). -/
theorem ne_zero_of_mem_weilPairingRootSubmonoid {x₂ y₂ : F} (h₂ : W.Equation x₂ y₂) {n : ℕ}
    [NeZero n] {g : W.FunctionField} (hg : g ∈ weilPairingRootSubmonoid h₂ n) : g ≠ 0 := by
  rintro rfl
  rw [mem_weilPairingRootSubmonoid_iff, ← weilPairingEltHom_apply,
    map_zero (weilPairingEltHom h₂), zero_pow (NeZero.ne n)] at hg
  exact zero_ne_one hg

/-- **The submonoid is closed under inverses.**  `weilPairingElt_inv_pow_eq_one` (`#733`).  Stated
as a theorem rather than a structure field because `Submonoid` has no `inv_mem'`; the group form is
`weilPairingRootSubgroup`. -/
theorem inv_mem_weilPairingRootSubmonoid {x₂ y₂ : F} (h₂ : W.Equation x₂ y₂) {n : ℕ}
    {g : W.FunctionField} (hg : g ∈ weilPairingRootSubmonoid h₂ n) :
    g⁻¹ ∈ weilPairingRootSubmonoid h₂ n :=
  weilPairingElt_inv_pow_eq_one h₂ hg

/-! ### The pairing as a homomorphism into `μ_n(F)` -/

open Classical in
/-- **The divisor slot of the Weil pairing, as a homomorphism of monoids into `μ_n(F)`.**

```
weilPairingMuHom h₂ n : {g : F(W) | e_n(g, T) ^ n = 1} →* rootsOfUnity n F,
                    g ↦ e_n(g, T).
```

This is Silverman *AEC* III.8.1(a) in the divisor slot as a statement about a *map* rather than a
family of pointwise equations.  `map_one'` is `weilPairingMu_eq_one_iff` applied to
`weilPairingElt_one`, and `map_mul'` is `weilPairingMu_mul` — both `#733`.

⚠️ `map_mul'` is literally `weilPairingMu_mul` with no transport, because `weilPairingMu h₂ hpow`
is proof-irrelevant in `hpow`: it is `Classical.choose` of a `Prop`, so the datum carried by the
product `g₁ * g₂` and the datum manufactured by `weilPairingElt_mul_pow_eq_one` are definitionally
interchangeable. -/
noncomputable def weilPairingMuHom {x₂ y₂ : F} (h₂ : W.Equation x₂ y₂) (n : ℕ) [NeZero n] :
    weilPairingRootSubmonoid h₂ n →* rootsOfUnity n F where
  toFun g := weilPairingMu h₂ g.2
  map_one' := (weilPairingMu_eq_one_iff h₂ _).mpr (weilPairingElt_one h₂)
  map_mul' _ _ := weilPairingMu_mul h₂ _ _ _

@[simp]
theorem weilPairingMuHom_apply {x₂ y₂ : F} (h₂ : W.Equation x₂ y₂) {n : ℕ} [NeZero n]
    {g : W.FunctionField} (hg : g ∈ weilPairingRootSubmonoid h₂ n) :
    weilPairingMuHom h₂ n ⟨g, hg⟩ = weilPairingMu h₂ hg :=
  rfl

/-- **The defining property of the bundled map**, inherited from `algebraMap_coe_weilPairingMu`
(`#457`): pushing a value down `μ_n(F) → Fˣ → F` and then up `algebraMap F F(W)` recovers the
Weil-pairing element itself. -/
@[simp]
theorem algebraMap_coe_weilPairingMuHom {x₂ y₂ : F} (h₂ : W.Equation x₂ y₂) {n : ℕ} [NeZero n]
    (g : weilPairingRootSubmonoid h₂ n) :
    algebraMap F W.FunctionField (((weilPairingMuHom h₂ n g : Fˣ) : F)) =
      weilPairingElt h₂ (g : W.FunctionField) :=
  algebraMap_coe_weilPairingMu h₂ g.2

/-! ### What being a homomorphism buys -/

/-- **`e_n(g ^ k, T) = e_n(g, T) ^ k` in the group `μ_n(F)`.**  `map_pow` on `weilPairingMuHom`;
the group-level form of `weilPairingElt_pow`, and the first statement of this shape at either
level. -/
theorem weilPairingMuHom_pow {x₂ y₂ : F} (h₂ : W.Equation x₂ y₂) {n : ℕ} [NeZero n]
    (g : weilPairingRootSubmonoid h₂ n) (k : ℕ) :
    weilPairingMuHom h₂ n (g ^ k) = weilPairingMuHom h₂ n g ^ k :=
  map_pow (weilPairingMuHom h₂ n) g k

/-- **The value at an inverse is the group inverse.**  `weilPairingMu_inv` (`#733`) read through
the bundling; the inverse on the left is the field inverse of `F(W)`, the one on the right is the
group inverse of `μ_n(F)`. -/
theorem weilPairingMuHom_inv {x₂ y₂ : F} (h₂ : W.Equation x₂ y₂) {n : ℕ} [NeZero n]
    {g : W.FunctionField} (hg : g ∈ weilPairingRootSubmonoid h₂ n) :
    weilPairingMuHom h₂ n ⟨g⁻¹, inv_mem_weilPairingRootSubmonoid h₂ hg⟩ =
      (weilPairingMuHom h₂ n ⟨g, hg⟩)⁻¹ :=
  weilPairingMu_inv h₂ hg (inv_mem_weilPairingRootSubmonoid h₂ hg)

/-- **A value is the group identity exactly when the pairing element is `1` in `F(W)`.**
`weilPairingMu_eq_one_iff` (`#733`) read through the bundling; no `g ≠ 0` hypothesis, since members
of the submonoid are nonzero anyway (`ne_zero_of_mem_weilPairingRootSubmonoid`). -/
theorem weilPairingMuHom_eq_one_iff {x₂ y₂ : F} (h₂ : W.Equation x₂ y₂) {n : ℕ} [NeZero n]
    (g : weilPairingRootSubmonoid h₂ n) :
    weilPairingMuHom h₂ n g = 1 ↔ weilPairingElt h₂ (g : W.FunctionField) = 1 :=
  weilPairingMu_eq_one_iff h₂ g.2

/-- **The kernel as a subobject.**  "Which functions pair trivially with `T`" becomes a submonoid
question rather than a question asked one element at a time — the form non-degeneracy (`#242`) will
eventually need.  `MonoidHom.mker` and not `MonoidHom.ker`, since the domain is a monoid; the
genuine subgroup kernel is `mem_ker_weilPairingMuHomUnits_iff` below. -/
theorem mem_mker_weilPairingMuHom_iff {x₂ y₂ : F} (h₂ : W.Equation x₂ y₂) {n : ℕ} [NeZero n]
    (g : weilPairingRootSubmonoid h₂ n) :
    g ∈ MonoidHom.mker (weilPairingMuHom h₂ n) ↔ weilPairingElt h₂ (g : W.FunctionField) = 1 :=
  weilPairingMuHom_eq_one_iff h₂ g

/-! ### The group form, on units

Members of `weilPairingRootSubmonoid h₂ n` are nonzero, so the same condition read on `F(W)ˣ` cuts
out a genuine **subgroup**, and the pairing becomes a homomorphism of groups.  This is the honest
form of Silverman III.8.1(a) in the divisor slot, and it is the one for which `map_inv` and
`map_zpow` are free rather than hand-stated. -/

/-- **The units whose Weil-pairing element is an `n`-th root of unity, as a subgroup of `F(W)ˣ`.**
`inv_mem'` is `weilPairingElt_inv` (`#723`) through `Units.val_inv_eq_inv_val`. -/
def weilPairingRootSubgroup {x₂ y₂ : F} (h₂ : W.Equation x₂ y₂) (n : ℕ) :
    Subgroup W.FunctionFieldˣ where
  carrier := {u | weilPairingElt h₂ (u : W.FunctionField) ^ n = 1}
  one_mem' := by
    change weilPairingElt h₂ ((1 : W.FunctionFieldˣ) : W.FunctionField) ^ n = 1
    rw [Units.val_one, weilPairingElt_one, one_pow]
  mul_mem' hu hv := by
    change weilPairingElt h₂ ((_ * _ : W.FunctionFieldˣ) : W.FunctionField) ^ n = 1
    rw [Units.val_mul]
    exact weilPairingElt_mul_pow_eq_one h₂ hu hv
  inv_mem' hu := by
    change weilPairingElt h₂ ((_⁻¹ : W.FunctionFieldˣ) : W.FunctionField) ^ n = 1
    rw [Units.val_inv_eq_inv_val]
    exact weilPairingElt_inv_pow_eq_one h₂ hu

@[simp]
theorem mem_weilPairingRootSubgroup_iff {x₂ y₂ : F} (h₂ : W.Equation x₂ y₂) {n : ℕ}
    {u : W.FunctionFieldˣ} :
    u ∈ weilPairingRootSubgroup h₂ n ↔ weilPairingElt h₂ (u : W.FunctionField) ^ n = 1 :=
  Iff.rfl

open Classical in
/-- **The divisor slot of the Weil pairing, as a homomorphism of groups into `μ_n(F)`.**

```
weilPairingMuHomUnits h₂ n : {u : F(W)ˣ | e_n(u, T) ^ n = 1} →* rootsOfUnity n F.
```

The `Units` form of `weilPairingMuHom`, with the same two fields.  Being a hom of *groups*, it
carries `map_inv` and `map_zpow` with no further work. -/
noncomputable def weilPairingMuHomUnits {x₂ y₂ : F} (h₂ : W.Equation x₂ y₂) (n : ℕ) [NeZero n] :
    weilPairingRootSubgroup h₂ n →* rootsOfUnity n F where
  toFun u := weilPairingMu h₂ u.2
  map_one' := (weilPairingMu_eq_one_iff h₂ _).mpr (by
    simp only [OneMemClass.coe_one, Units.val_one, weilPairingElt_one])
  map_mul' _ _ := weilPairingMu_mul h₂ _ _ _

@[simp]
theorem weilPairingMuHomUnits_apply {x₂ y₂ : F} (h₂ : W.Equation x₂ y₂) {n : ℕ} [NeZero n]
    {u : W.FunctionFieldˣ} (hu : u ∈ weilPairingRootSubgroup h₂ n) :
    weilPairingMuHomUnits h₂ n ⟨u, hu⟩ = weilPairingMu h₂ hu :=
  rfl

/-- The defining property of the group form, as for `algebraMap_coe_weilPairingMuHom`. -/
@[simp]
theorem algebraMap_coe_weilPairingMuHomUnits {x₂ y₂ : F} (h₂ : W.Equation x₂ y₂) {n : ℕ}
    [NeZero n] (u : weilPairingRootSubgroup h₂ n) :
    algebraMap F W.FunctionField (((weilPairingMuHomUnits h₂ n u : Fˣ) : F)) =
      weilPairingElt h₂ ((u : W.FunctionFieldˣ) : W.FunctionField) :=
  algebraMap_coe_weilPairingMu h₂ u.2

/-- **Inverses go to group inverses, for free.**  `map_inv` on the group homomorphism
`weilPairingMuHomUnits` — no descent through `algebraMap_coe_rootsOfUnity_injective` and no
manufactured `hpow` datum, unlike the pointwise `weilPairingMu_inv`. -/
theorem weilPairingMuHomUnits_inv {x₂ y₂ : F} (h₂ : W.Equation x₂ y₂) {n : ℕ} [NeZero n]
    (u : weilPairingRootSubgroup h₂ n) :
    weilPairingMuHomUnits h₂ n u⁻¹ = (weilPairingMuHomUnits h₂ n u)⁻¹ :=
  map_inv (weilPairingMuHomUnits h₂ n) u

/-- **Integer powers, for free.**  `map_zpow` on `weilPairingMuHomUnits`; there is no `F(W)`-level
counterpart, because `weilPairingRootSubmonoid` is only a monoid. -/
theorem weilPairingMuHomUnits_zpow {x₂ y₂ : F} (h₂ : W.Equation x₂ y₂) {n : ℕ} [NeZero n]
    (u : weilPairingRootSubgroup h₂ n) (k : ℤ) :
    weilPairingMuHomUnits h₂ n (u ^ k) = weilPairingMuHomUnits h₂ n u ^ k :=
  map_zpow (weilPairingMuHomUnits h₂ n) u k

/-- **The kernel as a genuine subgroup.**  The units form of `mem_mker_weilPairingMuHom_iff`; here
`MonoidHom.ker` really is available, because the domain is a group. -/
theorem mem_ker_weilPairingMuHomUnits_iff {x₂ y₂ : F} (h₂ : W.Equation x₂ y₂) {n : ℕ} [NeZero n]
    (u : weilPairingRootSubgroup h₂ n) :
    u ∈ (weilPairingMuHomUnits h₂ n).ker ↔
      weilPairingElt h₂ ((u : W.FunctionFieldˣ) : W.FunctionField) = 1 :=
  weilPairingMu_eq_one_iff h₂ u.2

/-! ### Non-vacuity

Every declaration above is unconditional given `[W.IsElliptic]`, a `W.Equation` for the translation
point and `[NeZero n]`, so all of them are instantiated here, on `y² = x³ − x` over
`AlgebraicClosure ℚ` with `T = (0, 0)` — the certificate curve `WeilPairingAntisymmetricMu`,
`WeilPairingAlternatingTwo` and `WeilPairingRootIndependence` use.

Every instance below is closed outright.  No `hpow` datum survives as a hypothesis, because
membership in `weilPairingRootSubmonoid` *is* that datum and each member exhibited carries its own
by proof: `1` by `weilPairingElt_one`, a nonzero constant by `weilPairingElt_algebraMap`, and their
powers and products by the submonoid structure.  The only hypothesis left anywhere below is `c ≠ 0`
on the constant.

The two `_apply` computation rules are `rfl` and are therefore not certified separately; they are
what lets every instance below be written in the `⟨g, hg⟩` form at all. -/

section Nonvacuity

/-- An algebraically closed field of characteristic zero. -/
private abbrev exampleField : Type := AlgebraicClosure ℚ

/-- The curve `y² = x³ − x` over `AlgebraicClosure ℚ`, of discriminant `64`. -/
private noncomputable def exampleCurve : Affine exampleField := ⟨0, 0, 0, -1, 0⟩

private instance : exampleCurve.IsElliptic := by
  rw [WeierstrassCurve.isElliptic_iff, isUnit_iff_ne_zero]
  norm_num [exampleCurve, WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈]

/-- `T = (0, 0)` lies on `y² = x³ − x`. -/
private lemma exampleEquation : exampleCurve.Equation 0 0 := by
  rw [equation_iff]
  norm_num [exampleCurve]

/-- The submonoid at `n = 2` on the curve above.  Every certificate below lives in it. -/
private noncomputable abbrev exampleSubmonoid : Submonoid exampleCurve.FunctionField :=
  weilPairingRootSubmonoid exampleEquation 2

/-- A nonzero constant of the base field lies in the submonoid: `e_2(c, T) = 1` by
`weilPairingElt_algebraMap`, so its square is `1`.  Nothing beyond `c ≠ 0` is assumed. -/
private lemma exampleMemConst {c : exampleField} (hc : c ≠ 0) :
    algebraMap exampleField exampleCurve.FunctionField c ∈ exampleSubmonoid := by
  rw [mem_weilPairingRootSubmonoid_iff, weilPairingElt_algebraMap exampleEquation hc, one_pow]

/-- On a curve that exists, the bundled map really does send the identity of the submonoid to the
identity of the group `μ_2(F̄)` — `map_one`, with no hypothesis left over. -/
example : weilPairingMuHom exampleEquation 2 1 = 1 :=
  map_one (weilPairingMuHom exampleEquation 2)

/-- The value at a nonzero constant is the identity of `μ_2(F̄)`, not merely an element whose
square is `1`.  Only `c ≠ 0` remains. -/
example {c : exampleField} (hc : c ≠ 0) :
    weilPairingMuHom exampleEquation 2
        ⟨algebraMap exampleField exampleCurve.FunctionField c, exampleMemConst hc⟩ = 1 :=
  (weilPairingMuHom_eq_one_iff exampleEquation _).mpr
    (weilPairingElt_algebraMap exampleEquation hc)

/-- **`map_pow` at a concrete exponent, on a curve that exists** — the certificate that the
bundling has content the pointwise development did not.  `e_2(c ^ 3, T) = e_2(c, T) ^ 3` in
`μ_2(F̄)`, with only `c ≠ 0` assumed. -/
example {c : exampleField} (hc : c ≠ 0) :
    weilPairingMuHom exampleEquation 2
        (⟨algebraMap exampleField exampleCurve.FunctionField c, exampleMemConst hc⟩ ^ 3) =
      weilPairingMuHom exampleEquation 2
        ⟨algebraMap exampleField exampleCurve.FunctionField c, exampleMemConst hc⟩ ^ 3 :=
  weilPairingMuHom_pow exampleEquation _ 3

/-- The `F(W)`-level `weilPairingElt_pow` on a curve that exists, at a concrete exponent and with
both sides computed: `e_2(c ^ 3, T) = 1 ^ 3 = 1`.  No hypothesis but `c ≠ 0`. -/
example {c : exampleField} (hc : c ≠ 0) :
    weilPairingElt exampleEquation
      ((algebraMap exampleField exampleCurve.FunctionField c) ^ 3) = 1 := by
  rw [weilPairingElt_pow, weilPairingElt_algebraMap exampleEquation hc, one_pow]

/-- The value at an inverse is the group inverse, on a curve that exists. -/
example {c : exampleField} (hc : c ≠ 0) :
    weilPairingMuHom exampleEquation 2
        ⟨(algebraMap exampleField exampleCurve.FunctionField c)⁻¹,
          inv_mem_weilPairingRootSubmonoid exampleEquation (exampleMemConst hc)⟩ =
      (weilPairingMuHom exampleEquation 2
        ⟨algebraMap exampleField exampleCurve.FunctionField c, exampleMemConst hc⟩)⁻¹ :=
  weilPairingMuHom_inv exampleEquation (exampleMemConst hc)

/-- Members of the submonoid are nonzero, on a curve that exists: the constant `1` is not `0` in
`F̄(W)`.  Discharged outright through `ne_zero_of_mem_weilPairingRootSubmonoid`. -/
example : (1 : exampleCurve.FunctionField) ≠ 0 :=
  ne_zero_of_mem_weilPairingRootSubmonoid exampleEquation (n := 2) (one_mem _)

/-- A nonzero constant, as a unit of `F̄(W)`, lies in the subgroup. -/
private lemma exampleMemConstUnits {c : exampleField} (hc : c ≠ 0) :
    (Units.mk0 (algebraMap exampleField exampleCurve.FunctionField c)
        ((map_ne_zero_iff _ (algebraMap exampleField exampleCurve.FunctionField).injective).mpr
          hc)) ∈ weilPairingRootSubgroup exampleEquation 2 := by
  rw [mem_weilPairingRootSubgroup_iff, Units.val_mk0,
    weilPairingElt_algebraMap exampleEquation hc, one_pow]

/-- **The group form on a curve that exists**, with `map_inv` free: the value at the inverse unit
is the group inverse in `μ_2(F̄)`.  Only `c ≠ 0` remains. -/
example {c : exampleField} (hc : c ≠ 0) :
    weilPairingMuHomUnits exampleEquation 2
        ⟨_, exampleMemConstUnits hc⟩⁻¹ =
      (weilPairingMuHomUnits exampleEquation 2 ⟨_, exampleMemConstUnits hc⟩)⁻¹ :=
  weilPairingMuHomUnits_inv exampleEquation _

/-- `map_zpow` free, at a concrete negative exponent, on a curve that exists. -/
example {c : exampleField} (hc : c ≠ 0) :
    weilPairingMuHomUnits exampleEquation 2 (⟨_, exampleMemConstUnits hc⟩ ^ (-2 : ℤ)) =
      weilPairingMuHomUnits exampleEquation 2 ⟨_, exampleMemConstUnits hc⟩ ^ (-2 : ℤ) :=
  weilPairingMuHomUnits_zpow exampleEquation _ (-2)

/-- The defining property on a curve that exists, with the right-hand side computed outright: the
value at a nonzero constant pushes forward to `e_2(c, T) = 1` in `F̄(W)`. -/
example {c : exampleField} (hc : c ≠ 0) :
    algebraMap exampleField exampleCurve.FunctionField
        (((weilPairingMuHom exampleEquation 2 ⟨_, exampleMemConst hc⟩ : exampleFieldˣ) :
          exampleField)) = 1 := by
  rw [algebraMap_coe_weilPairingMuHom, weilPairingElt_algebraMap exampleEquation hc]

/-- The same for the group form. -/
example {c : exampleField} (hc : c ≠ 0) :
    algebraMap exampleField exampleCurve.FunctionField
        (((weilPairingMuHomUnits exampleEquation 2 ⟨_, exampleMemConstUnits hc⟩ : exampleFieldˣ) :
          exampleField)) = 1 := by
  rw [algebraMap_coe_weilPairingMuHomUnits, Units.val_mk0,
    weilPairingElt_algebraMap exampleEquation hc]

/-- **The kernel is inhabited on a curve that exists**: the nonzero constants pair trivially with
`T`, so they lie in `MonoidHom.mker (weilPairingMuHom …)`.  Only `c ≠ 0` remains. -/
example {c : exampleField} (hc : c ≠ 0) :
    (⟨_, exampleMemConst hc⟩ : exampleSubmonoid) ∈
      MonoidHom.mker (weilPairingMuHom exampleEquation 2) :=
  (mem_mker_weilPairingMuHom_iff exampleEquation _).mpr
    (weilPairingElt_algebraMap exampleEquation hc)

/-- The same in the genuine subgroup kernel. -/
example {c : exampleField} (hc : c ≠ 0) :
    (⟨_, exampleMemConstUnits hc⟩ : weilPairingRootSubgroup exampleEquation 2) ∈
      (weilPairingMuHomUnits exampleEquation 2).ker :=
  (mem_ker_weilPairingMuHomUnits_iff exampleEquation _).mpr (by
    rw [Units.val_mk0, weilPairingElt_algebraMap exampleEquation hc])

end Nonvacuity

end CoordinateRing

end WeierstrassCurve.Affine
