/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import EllipticCurves.Fixtures
import EllipticCurves.FunctionField.PullbackPrincipalityThree
import EllipticCurves.FunctionField.WeilPairingBilinearMu

/-!
# The translation slot of `e_n` as a homomorphism `E[n] → μ_n(F)` (rung 6)

Let `W` be an elliptic curve over a field `F`.  Silverman *AEC* III.8's `e_n` is a **pairing of
groups**, and that is a statement about maps.  The **divisor** slot has been a bundled homomorphism
since `#746`,

```lean
weilPairingMuHom h₂ n : weilPairingRootSubmonoid h₂ n →* rootsOfUnity n F,   g ↦ e_n(g, T),
```

and the **translation** slot has had none.  This file supplies it, and with it the map
`e_n(S, ·) : E[n] → μ_n(F)` that `WeilPairingNondegenerateMu` opens by saying the whole `μ_n` layer
exists for.

## Why the translation slot needs a different construction

`weilPairingElt h₂ g = τ_T∗(g) / g` is indexed by `h₂ : W.Equation x₂ y₂`, so it can only name an
**affine** translation point.  A homomorphism out of `E[n]` has to name the identity, and the
identity of `W.Point` is the point at infinity.  Every merged translation-slot statement — the five
`translatePoint_add` theorems and `#873`'s four instantiations — is therefore a statement about
three *affine* points related by `P ⊕ Q = R`, and none of them can be a `map_mul'` field.

`EllipticCurves.FunctionField.TranslationAction`'s `translateAut : W.Point → (F(W) ≃ₐ[F] F(W))` is
exactly the missing piece, and its own docstring says so:

> the `O` corner is exactly what a *group homomorphism* out of `W.Point` has to name.  That is the
> whole reason this definition exists.

⚠️ **No `weilPairing*` *definition* was indexed by `W.Point`** — and two merged proofs already
reach for `translateAut` for exactly the reason this file does.
`exists_torsion_two_weilPairingElt_ne_one` (`WeilPairingNondegenerateTwo`) and
`exists_torsion_three_weilPairingElt_ne_one` each split `cases P with | zero | some` by hand to get
past `O`; that is the boilerplate abolished here.  Building the pairing element on `translateAut`
instead of `translateEndo` makes `weilPairingPointElt_some` an `rfl`, so every merged
`weilPairingElt` fact transfers to the `Point` layer with no transport lemma, and the `O` corner —
where the value is `g / g = 1` — costs one `div_self`.

## ⚠️ The second half of the obstruction is gone, and the notes that named it are stale

`WeilPairingDivisorSlotHom` (`#746`) and `WeilPairingTranslationSlotBilinear` (`#873`) both put
this bundling out of scope, and both located the difficulty in the `hpow` datum.  That half is
solved here the same way `#746` solved it in the divisor slot — make the datum a **membership**
rather than an argument, so that `weilPairingPointSubgroup` *is* the family of data.

The other half was multiplicativity, which `WeilPairingBilinear` (`#419`) carried as the hypothesis
`hfix`: the value at `Q` has to be fixed by `τ_P`.  **That is no longer a hypothesis.**  `#434`
discharged `algebraicClosure F F(W) = ⊥`, so `weilPairingElt_isRootOfUnity`
(`WeilPairingConstant`) is unconditional given `e ^ n = 1` and `n ≠ 0`; the value is then a constant
of `F`, and `translateAut P` is an `F`-**algebra** equivalence, so `AlgEquiv.commutes` fixes it
outright.

⚠️ **That sentence used to read *"which `#161`/`#450` carried"*, and neither number is an issue of
this project.**  Corrected in place, not retired.  `#161` is the **pull request** that created
`WeilPairingBilinear` (*"bilinearity of the Weil-pairing element in the translation slot (#419)"*),
and `#450` is the same mis-citation of that same module that
`WeilPairingTranslationSlotBilinear`'s own recording section resolves to `#419` — it is issue 450 of
project **9**, and a pull request of this repository.  ⚠️ **The slash-pair is one referent, not
two**: `hfix` *in this sense* — the translation `τ_P` fixing the **pairing value** `e_n(S, T_Q)` —
is the hypothesis of exactly one declaration in this tree, `weilPairingElt_translatePoint_add`
(`WeilPairingBilinear`); `WeilPairingBilinearBaseField` only *compares* to it, and its
`weilPairingElt_translatePoint_add_of_baseField` takes `hpow`.  The sibling file was repaired on
2026-08-28 and this copy was missed because no name precedes either number.

⚠️ **The qualifier is load-bearing: an unqualified `hfix` count is false.**  `grep -rn '(hfix :'`
returns **13 binder sites across seven modules** — 14 once the quotation in this paragraph is
counted, which is why the grep is written out here rather than merely cited — and the name alone
does not separate them.  Six of the seven modules bind a different hypothesis under it:
`weilPairingElt_pow_eq_one` (`WeilPairing`) and
`weilPairingElt_mul_left_of_translateEndo_fixed` (`WeilPairingRootIndependence`) fix a
`translateEndo` point of a *plain function* rather than of a pairing value;
`forall_mem_rootsOfUnity_three_fixed_of_forall_torsion_fixed` (`WeilPairingRationalTorsion`) and
`galoisModularCyclotomicChar_three_eq_one_of_forall_fixed` (`WeilPairingRationalTorsionGalois`) fix
`3`-torsion under a Galois automorphism; `eq_formalW_of_wOp_fixed` (`FormalGroup/Expansion`) and
`eq_formalW_subst_of_wOpSubst_fixed` (`FormalGroup/ExpansionSubst`) fix a `wOp` point.  ⚠️ **So the
collapse above rests on provenance, not on the count**: PR #161 is `WeilPairingBilinear`'s creating
pull request, and that is what fixes the referent.  The count is stated here with its scope because
a citation repair whose own evidence is unscoped is the defect it is repairing.

> The generalisable point: **a scope note that names an obstruction freezes it.**  Both notes were
> accurate beside the statement they were written for, and both were stale about the tree within
> days, because `#434` and `translateAut` landed and nothing re-read them.  This is `#456`'s
> failure mode one level up — there a *dependency* was misattributed, here a *difficulty* was.

## ⚠️ The datum is needed at `Q` only, and that is `#873`'s asymmetry, preserved

`weilPairingPointElt_add` takes the root-of-unity datum at `Q` alone; nothing is assumed about `P`.
`translateAut_add` gives `τ_{P ⊕ Q} = τ_P ∘ τ_Q`, so the only value pushed through `τ_P` is the one
at `Q`.  `#873`'s docstring explains why this is mathematics rather than an artefact of the proof;
it is not symmetrised here for tidiness.  It is also what makes `neg_mem'` free: `e(−P)` is
obtained from `(−P) ⊕ P = O` using the datum at `P`, which is the one already in hand.

## Main results

* `weilPairingPointElt` — `e_n(g, P) := translateAut P g / g`, defined at **every** `P : W.Point`,
  with `weilPairingPointElt_some` an `rfl` onto `weilPairingElt` and
  `weilPairingPointElt_zero` the `O` corner;
* `weilPairingPointElt_add` / `_neg` — translation-slot multiplicativity as a statement about the
  group `W.Point`, the point at infinity included;
* `weilPairingPointSubgroup` — the `P` carrying a root-of-unity datum, as an
  `AddSubgroup W.Point`, with `mem_weilPairingPointSubgroup_iff` an `Iff.rfl`;
* `weilPairingPointMu` and its `algebraMap_coe_weilPairingPointMu` / `_eq_one_iff` / `_add` /
  `_neg`, the `Point`-indexed mirror of `weilPairingMu`;
* **`weilPairingPointMuHom`** — the headline, `Multiplicative (weilPairingPointSubgroup hg n) →*
  rootsOfUnity n F`, with `map_inv`, `map_zpow` and `MonoidHom.ker` free;
* `torsion_le_weilPairingPointSubgroup_{two,three}` — the bridge that makes the domain `E[n]`, and
  **`weilPairingTorsionMuHom_{two,three}` : `Multiplicative (W.torsion n) →* rootsOfUnity n F`**;
* `exists_weilPairingTorsionMuHom_{two,three}` — the same over `F̄` with no hypothesis beyond the
  setting: `e_n(S, ·) : E[n] → μ_n(F)` **is** a group homomorphism at `n = 2` and `n = 3`.

## ⚠️ `map_mul'` has no coherence obligation, and a reader arriving here will expect one

`weilPairingPointMu hg hpow` is `Classical.choose` of a `Prop`, hence **proof-irrelevant in
`hpow`**: two propositionally equal data give a *definitionally* equal value.  So the datum carried
by `P ⊕ Q` and the datum manufactured by `add_mem'` are interchangeable, and `map_mul'` is
`weilPairingPointMu_add` with nothing transported.  `WeilPairingDivisorSlotHom` records the same
fact about `weilPairingMu`; it is repeated here because the surprise is not transferable — a reader
coming from the `W.Point` side has no reason to have read that file.

## Scope

`[Field F] {W : Affine F} [W.IsElliptic]` throughout, plus the `[NeZero n]` that `weilPairingMu`
itself carries.  Everything through `weilPairingPointMuHom` is **ungated end to end**: no
`[IsAlgClosed F]`, no `[IsDedekindDomain W.CoordinateRing]` hypothesis (the instance has been
global for `[W.IsElliptic]` over an arbitrary field since `CoordinateRingNormalGeneral`), no
rung 4, no `#418`, no Ward.

`[IsAlgClosed F]` enters the four `exists_` headlines **only** through `hprin`, i.e. only through
`exists_gS_{two,three}_of_isAlgClosed` (`#791`/`#825`) — the same single source as every other
`[IsAlgClosed F]` on this front.  `weilPairingTorsionMuHom_{two,three}` themselves carry no such
hypothesis: they take the rung-5 datum `u · g ^ n = [n]∗ f` as an argument and are stated over an
arbitrary field.

Out of scope: **combining the two slots** into a pairing on `W.Point × W.Point` — `#873` records
that as a separate design question and it stays one, since the divisor slot is a slot of
`weilPairingElt`, which takes a *function* and not a point.  General `n`
(⚠️ no longer `#251`, which is closed — see below); `hprin`
over a general field, open at both `n`.  Nothing existing is renamed or reproved: this module is
purely additive.

⚠️ **That bullet read *"general `n` (`#404`'s `ωₙ`)"*, then *"general `n` (`#251`)"*, and both of
those are now closed.**  PR #557 proved the on-curve identity for `(Φₙ/ΨSqₙ, ωₙ/ψₙ³)` at every index
over every commutative ring — `WeierstrassCurve.Affine.equation_div_of_ψ_ne_zero`,
`EllipticCurves.Torsion.OmegaCrux`.  The *other* statement this tree also called `ωₙ` — the
identification of those coordinates with the **group-law** multiple `n • P` — is `#251` on its
`x`-half and `#1500` on its `y`-half, and **both are closed**: `hasXCoordFormula_of_two_ne_zero`
(`EllipticCurves.Torsion.NsmulOrder`) and `nsmul_eq_some_omegaY_of_ΨSq_ne_zero`
(`EllipticCurves.Torsion.NsmulYPeriodic`, PR #579), each at every index over a field with
`(2 : F) ≠ 0`.  ⚠️ That was the step `hprin` reaches through
`MulByTwoFibreAffine`/`MulByThreeFibre`, whose own input is `addY_self_eq_div`
(`EllipticCurves.Torsion.DoublingCoords`) and its `n = 3` mirror — and that input now exists at
every index.  ⚠️ **Whether it unblocks those two fibre descriptions is NOT measured**, here or
anywhere in this tree: the bullet is retired because the reason it gave is false, not because a
replacement reason was found.  The two-reading account is
`EllipticCurves.FunctionField.MulByNPullback`.

⚠️ **The out-of-scope list in this `## Scope` section used to open with one more entry, and that
entry was filed and delivered.**  It read *"**Non-degeneracy as a statement about this map**
(`weilPairingTorsionMuHom ≠ 1`), the obvious
next corollary, which wants `WeilPairingNondegenerateMu`'s six headlines as input and its own
issue."*  The issue is `#893`, and it is
`EllipticCurves.FunctionField.WeilPairingTranslationSlotNondegenerate`:
`weilPairingTorsionMuHom_{two,three}_ne_one`, the proper-kernel form
`ker_weilPairingTorsionMuHom_{two,three}_ne_top`, and the Silverman III.8.1(c) converse
`eq_zero_of_weilPairingTorsionMuHom_{two,three}_eq_one`.  ⚠️ The prediction was right about the
input — that file consumes exactly `WeilPairingNondegenerateMu`'s headlines — and right that it
belonged in its own module, which is why nothing here changed when it landed.

⚠️ **Injectivity of the same map is a different statement and is not merely open**: it is false,
and `not_injective_weilPairingTorsionMuHom_{two,three}`
(`EllipticCurves.FunctionField.WeilPairingTranslationSlotNotInjective`) is the refutation, off
`#E[n] = n²` against `#μ_n(F̄) = n`.  Non-degeneracy is `≠ 1`; it is not injectivity, and the two
are not steps of one ladder.

## Placement

The lemma layer — everything about `weilPairingPointElt`, `weilPairingPointMu`,
`weilPairingPointMuHom` and the two `weilPairingTorsionMuHom_{two,three}` bundles — lives in
`WeierstrassCurve.Affine.CoordinateRing`.  The two `exists_` headlines over `F̄` live one level up
in `WeierstrassCurve.Affine`, reached with `open CoordinateRing`.  That is `#903`'s house pattern,
demonstrated in `EllipticCurves.FunctionField.WeilPairingRootIndependence`.

⚠️ **The headlines were moved up by `#918`; they used to be in the sub-namespace with the lemmas.**
Nothing about them changed but the prefix — no statement, no proof, no binder.  The move was worth
making because their arbitrary-field twins in
`EllipticCurves.FunctionField.WeilPairingTranslationSlotHprin` (`#913`) are in `Affine`, and a twin
pair split across two namespaces is invisible to a clean build, to `mk_all`, to a line-by-line read
and to `#print axioms` run on only one of the two names — which is precisely how it survived here.

## Non-vacuity

Every headline is certified below on the curves `#845`/`#861`/`#873` use — `y² = x³ − x` over
`AlgebraicClosure ℚ` at `n = 2`, `y² + y = x³` at `n = 3`.  ⚠️ The two `_apply`-style computation
rules are `rfl` and are not certified separately.  ⚠️ The certificates sit in `Affine` alongside the
headlines rather than in the sub-namespace; they are `example`s and `private` lemmas, so no name
outside this file is affected.

## References

* [J. Silverman, *The arithmetic of elliptic curves*][silverman2009], III.8.1(a); III.8 for the
  value group `μ_n` and for `e_n` being a pairing of groups.
-/

namespace WeierstrassCurve.Affine

namespace CoordinateRing

variable {F : Type*} [Field F] {W : Affine F} [W.IsElliptic]

/-! ### The pairing element at an arbitrary point, the point at infinity included -/

/-- **The Weil-pairing element in the translation slot, indexed by a point of `W`.**

```
e_n(g, P) := translateAut P g / g ∈ F(W).
```

`translateAut` is the identity at `O` and `translateAlgEquiv` at an affine point
(`TranslationAction`), so this agrees with `weilPairingElt` wherever the latter is defined
(`weilPairingPointElt_some`, an `rfl`) and extends it to `P = O`, which is what a homomorphism out
of `W.Point` needs. -/
noncomputable def weilPairingPointElt (g : W.FunctionField) (P : W.Point) : W.FunctionField :=
  translateAut P g / g

/-- **The affine values are the merged ones.**  `translateAut (.some x y h) = translateAlgEquiv
h.left` by definition and `translateAlgEquiv` applies as `translateEndo`, so this is `rfl` — which
is the point of building on `translateAut`: no fact about `weilPairingElt` needs transporting. -/
@[simp]
theorem weilPairingPointElt_some (g : W.FunctionField) {x y : F} (h : W.Nonsingular x y) :
    weilPairingPointElt g (.some x y h) = weilPairingElt h.left g :=
  rfl

/-- **The `O` corner**: translation by the point at infinity is the identity, so the value is
`g / g = 1`.

⚠️ This and `weilPairingPointElt_one` specialise **different slots**, and only the argument order
distinguishes them.  The convention, which is forced rather than chosen: `W.Point` is written
additively and has a `0` but no `1`, so `_zero` is always the translation slot; the divisor slot is
a function of `F(W)` used multiplicatively, so `_one` is always that one. -/
@[simp]
theorem weilPairingPointElt_zero {g : W.FunctionField} (hg : g ≠ 0) :
    weilPairingPointElt g 0 = 1 := by
  rw [weilPairingPointElt, translateAut_zero, AlgEquiv.one_apply, div_self hg]

/-- **Pairing with the trivial function is trivial**, at every point: `e_n(1, P) = 1`.  The
`Point`-indexed form of `weilPairingElt_one`, and the reason `weilPairingPointSubgroup` is never
empty (see the non-vacuity section).  On the naming, see `weilPairingPointElt_zero`. -/
@[simp]
theorem weilPairingPointElt_one (P : W.Point) :
    weilPairingPointElt (1 : W.FunctionField) P = 1 := by
  rw [weilPairingPointElt, map_one, div_one]

/-- The value is nonzero whenever `g` is: `translateAut P` is injective, being an equivalence. -/
theorem weilPairingPointElt_ne_zero {g : W.FunctionField} (hg : g ≠ 0) (P : W.Point) :
    weilPairingPointElt g P ≠ 0 :=
  div_ne_zero ((map_ne_zero_iff _ (AlgEquiv.injective _)).mpr hg) hg

/-- `e_n(g, P) · g = τ_P(g)`, the multiplicative form of the definition.  Used to push the value at
one point through the translation at another. -/
theorem weilPairingPointElt_mul_self {g : W.FunctionField} (hg : g ≠ 0) (P : W.Point) :
    weilPairingPointElt g P * g = translateAut P g :=
  div_mul_cancel₀ _ hg

/-! ### Multiplicativity in the point -/

open Classical in
/-- **Translation-slot multiplicativity, from constancy of the value at `Q`.**

```
e_n(g, P ⊕ Q) = e_n(g, P) · e_n(g, Q).
```

`translateAut_add` gives `τ_{P ⊕ Q} = τ_P ∘ τ_Q`, so `τ_{P ⊕ Q}(g) = τ_P(e_n(g, Q) · g)`; the
constant passes through the `F`-algebra map `τ_P` untouched (`AlgEquiv.commutes`), leaving
`e_n(g, Q) · τ_P(g)`.  Dividing by `g` gives the claim.

⚠️ Nothing is assumed about `P`.  See the module docstring. -/
theorem weilPairingPointElt_add_of_const {g : W.FunctionField} (hg : g ≠ 0) (P : W.Point)
    {Q : W.Point} {c : F} (hc : weilPairingPointElt g Q = algebraMap F W.FunctionField c) :
    weilPairingPointElt g (P + Q) = weilPairingPointElt g P * weilPairingPointElt g Q := by
  have hQ : translateAut Q g = algebraMap F W.FunctionField c * g := by
    rw [← weilPairingPointElt_mul_self hg Q, hc]
  have h1 : translateAut (P + Q) g = algebraMap F W.FunctionField c * translateAut P g := by
    rw [translateAut_add, AlgEquiv.mul_apply, hQ, map_mul, AlgEquiv.commutes]
  simp only [weilPairingPointElt, h1, hQ]
  field_simp

/-- **The value is a base-field constant, and an `n`-th root of unity**, at every point.

At `O` the value is `1 = algebraMap F F(W) 1`.  At an affine point this is
`weilPairingElt_isRootOfUnity` (`WeilPairingConstant`) verbatim — unconditional since `#434`
discharged the constant-field hypothesis. -/
theorem weilPairingPointElt_isRootOfUnity {g : W.FunctionField} (hg : g ≠ 0) {n : ℕ} (hn : n ≠ 0)
    {P : W.Point} (hpow : weilPairingPointElt g P ^ n = 1) :
    ∃ c : F, weilPairingPointElt g P = algebraMap F W.FunctionField c ∧ c ^ n = 1 := by
  rcases P with _ | ⟨x, y, h⟩
  · exact ⟨1, by rw [← Point.zero_def, weilPairingPointElt_zero hg, map_one], one_pow n⟩
  · exact weilPairingElt_isRootOfUnity h.left hn hpow

open Classical in
/-- **Translation-slot multiplicativity, from the root-of-unity datum at `Q` alone.**  Constancy is
produced by `weilPairingPointElt_isRootOfUnity` and fed to `weilPairingPointElt_add_of_const`. -/
theorem weilPairingPointElt_add {g : W.FunctionField} (hg : g ≠ 0) (P : W.Point) {Q : W.Point}
    {n : ℕ} (hn : n ≠ 0) (hpow : weilPairingPointElt g Q ^ n = 1) :
    weilPairingPointElt g (P + Q) = weilPairingPointElt g P * weilPairingPointElt g Q := by
  obtain ⟨c, hc, -⟩ := weilPairingPointElt_isRootOfUnity hg hn hpow
  exact weilPairingPointElt_add_of_const hg P hc

open Classical in
/-- **`e_n(g, −P) = e_n(g, P)⁻¹`**, from multiplicativity at `(−P) ⊕ P = O`.  ⚠️ The datum consumed
is the one at `P`, not at `−P`: multiplicativity needs it at the *right-hand* argument, and that is
`P` here.  This is what makes `neg_mem'` cost nothing below. -/
theorem weilPairingPointElt_neg {g : W.FunctionField} (hg : g ≠ 0) {P : W.Point} {n : ℕ}
    (hn : n ≠ 0) (hpow : weilPairingPointElt g P ^ n = 1) :
    weilPairingPointElt g (-P) = (weilPairingPointElt g P)⁻¹ := by
  have h := weilPairingPointElt_add hg (-P) hn hpow
  rw [neg_add_cancel] at h
  simp only [weilPairingPointElt_zero hg] at h
  have hP := weilPairingPointElt_ne_zero hg P
  field_simp
  exact h.symm

/-! ### The points carrying a root-of-unity datum, as a subgroup -/

open Classical in
/-- **The points whose Weil-pairing value is an `n`-th root of unity, as an `AddSubgroup
W.Point`.**

```
weilPairingPointSubgroup hg n = {P : W.Point | e_n(g, P) ^ n = 1}.
```

The three fields are `weilPairingPointElt_zero`, `_add` and `_neg`.  As in
`weilPairingRootSubmonoid` (`#746`) for the divisor slot, **membership here *is* the `hpow` datum**
that `weilPairingPointMu` consumes, which is what makes the translation slot bundle into a
`MonoidHom` at all. -/
def weilPairingPointSubgroup {g : W.FunctionField} (hg : g ≠ 0) (n : ℕ) [NeZero n] :
    AddSubgroup W.Point where
  carrier := {P | weilPairingPointElt g P ^ n = 1}
  zero_mem' := by
    change weilPairingPointElt g (0 : W.Point) ^ n = 1
    rw [weilPairingPointElt_zero hg, one_pow]
  add_mem' {P Q} hP hQ := by
    change weilPairingPointElt g (P + Q) ^ n = 1
    rw [weilPairingPointElt_add hg P (NeZero.ne n) hQ, mul_pow, hP, hQ, one_mul]
  neg_mem' {P} hP := by
    change weilPairingPointElt g (-P) ^ n = 1
    rw [weilPairingPointElt_neg hg (NeZero.ne n) hP, inv_pow, hP, inv_one]

open Classical in
@[simp]
theorem mem_weilPairingPointSubgroup_iff {g : W.FunctionField} (hg : g ≠ 0) {n : ℕ} [NeZero n]
    {P : W.Point} :
    P ∈ weilPairingPointSubgroup hg n ↔ weilPairingPointElt g P ^ n = 1 :=
  Iff.rfl

/-! ### The value as an element of `μ_n(F)` -/

/-- **The `Point`-indexed pairing value as an element of `μ_n(F)`.**  The mirror of `weilPairingMu`
(`WeilPairingRootsOfUnity`, `#457`): `weilPairingPointElt_isRootOfUnity` produces a constant `c`
with `c ^ n = 1`, and `rootsOfUnity.mkOfPowEq` packages it as a genuine element of
`rootsOfUnity n F ≤ Fˣ`. -/
noncomputable def weilPairingPointMu {g : W.FunctionField} (hg : g ≠ 0) {P : W.Point} {n : ℕ}
    [NeZero n] (hpow : weilPairingPointElt g P ^ n = 1) : rootsOfUnity n F :=
  rootsOfUnity.mkOfPowEq
    (Classical.choose (weilPairingPointElt_isRootOfUnity hg (NeZero.ne n) hpow))
    (Classical.choose_spec (weilPairingPointElt_isRootOfUnity hg (NeZero.ne n) hpow)).2

/-- **Defining property of `weilPairingPointMu`**: pushing it down `μ_n(F) → Fˣ → F` and back up
`algebraMap F F(W)` recovers the pairing value. -/
@[simp]
theorem algebraMap_coe_weilPairingPointMu {g : W.FunctionField} (hg : g ≠ 0) {P : W.Point} {n : ℕ}
    [NeZero n] (hpow : weilPairingPointElt g P ^ n = 1) :
    algebraMap F W.FunctionField ((weilPairingPointMu hg hpow : Fˣ) : F)
      = weilPairingPointElt g P := by
  rw [weilPairingPointMu, rootsOfUnity.coe_mkOfPowEq]
  exact (Classical.choose_spec (weilPairingPointElt_isRootOfUnity hg (NeZero.ne n) hpow)).1.symm

/-- **The `μ_n(F)` value is the group identity exactly when the pairing element is `1`.**  The
mirror of `weilPairingMu_eq_one_iff`; both directions are the defining property together with
injectivity of `algebraMap F F(W)`. -/
theorem weilPairingPointMu_eq_one_iff {g : W.FunctionField} (hg : g ≠ 0) {P : W.Point} {n : ℕ}
    [NeZero n] (hpow : weilPairingPointElt g P ^ n = 1) :
    weilPairingPointMu hg hpow = 1 ↔ weilPairingPointElt g P = 1 := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rw [← algebraMap_coe_weilPairingPointMu hg hpow, h]
    simp
  · have := (algebraMap_coe_weilPairingPointMu hg hpow).trans h
    rw [show (1 : W.FunctionField) = algebraMap F W.FunctionField 1 by simp] at this
    exact Subtype.ext (Units.ext ((algebraMap F W.FunctionField).injective this))

/-- **The `μ_n(F)` value is non-trivial exactly when the pairing element is**, the contrapositive
form.  This is the direction a non-degeneracy witness travels in. -/
theorem weilPairingPointMu_ne_one_iff {g : W.FunctionField} (hg : g ≠ 0) {P : W.Point} {n : ℕ}
    [NeZero n] (hpow : weilPairingPointElt g P ^ n = 1) :
    weilPairingPointMu hg hpow ≠ 1 ↔ weilPairingPointElt g P ≠ 1 :=
  (weilPairingPointMu_eq_one_iff hg hpow).not

open Classical in
/-- **Multiplicativity in `μ_n(F)`.**  Descends through
`algebraMap_coe_rootsOfUnity_injective` (`WeilPairingBilinearMu`, `#459`) to
`weilPairingPointElt_add`, exactly as `weilPairingMu_mul` does in the divisor slot. -/
theorem weilPairingPointMu_add {g : W.FunctionField} (hg : g ≠ 0) {P Q : W.Point} {n : ℕ}
    [NeZero n] (hP : weilPairingPointElt g P ^ n = 1) (hQ : weilPairingPointElt g Q ^ n = 1)
    (hPQ : weilPairingPointElt g (P + Q) ^ n = 1) :
    weilPairingPointMu hg hPQ = weilPairingPointMu hg hP * weilPairingPointMu hg hQ := by
  refine algebraMap_coe_rootsOfUnity_injective (W := W) ?_
  simp only [Subgroup.coe_mul, Units.val_mul, map_mul, algebraMap_coe_weilPairingPointMu]
  exact weilPairingPointElt_add hg P (NeZero.ne n) hQ

open Classical in
/-- **The value at `−P` is the group inverse in `μ_n(F)`.**  The descent of
`weilPairingPointElt_neg`. -/
theorem weilPairingPointMu_neg {g : W.FunctionField} (hg : g ≠ 0) {P : W.Point} {n : ℕ} [NeZero n]
    (hP : weilPairingPointElt g P ^ n = 1) (hnegP : weilPairingPointElt g (-P) ^ n = 1) :
    weilPairingPointMu hg hnegP = (weilPairingPointMu hg hP)⁻¹ := by
  refine algebraMap_coe_rootsOfUnity_injective (W := W) ?_
  simp only [Subgroup.coe_inv, Units.val_inv_eq_inv_val, map_inv₀,
    algebraMap_coe_weilPairingPointMu]
  exact weilPairingPointElt_neg hg (NeZero.ne n) hP

/-! ### The headline: the translation slot as a homomorphism -/

open Classical in
/-- **The translation slot of the Weil pairing, as a homomorphism of groups into `μ_n(F)`.**

```
weilPairingPointMuHom hg n : Multiplicative {P : W.Point | e_n(g, P) ^ n = 1} →* rootsOfUnity n F,
                        P ↦ e_n(g, P).
```

This is Silverman *AEC* III.8.1(a) in the translation slot as a statement about a *map*, and the
statement `WeilPairingDivisorSlotHom` (`#746`) and `WeilPairingTranslationSlotBilinear` (`#873`)
each declared out of scope.  `map_one'` is `weilPairingPointMu_eq_one_iff` applied to the `O`
corner; `map_mul'` is `weilPairingPointMu_add`.

⚠️ `map_mul'` needs no transport, because `weilPairingPointMu` is proof-irrelevant in its datum;
see the module docstring. -/
noncomputable def weilPairingPointMuHom {g : W.FunctionField} (hg : g ≠ 0) (n : ℕ) [NeZero n] :
    Multiplicative (weilPairingPointSubgroup hg n) →* rootsOfUnity n F where
  toFun P := weilPairingPointMu hg P.toAdd.2
  map_one' := (weilPairingPointMu_eq_one_iff hg _).mpr (weilPairingPointElt_zero hg)
  map_mul' _ _ := weilPairingPointMu_add hg _ _ _

open Classical in
@[simp]
theorem weilPairingPointMuHom_apply {g : W.FunctionField} (hg : g ≠ 0) {n : ℕ} [NeZero n]
    {P : W.Point} (hP : P ∈ weilPairingPointSubgroup hg n) :
    weilPairingPointMuHom hg n (Multiplicative.ofAdd (⟨P, hP⟩ : weilPairingPointSubgroup hg n))
      = weilPairingPointMu hg hP :=
  rfl

open Classical in
/-- **The defining property of the bundled map**, inherited from
`algebraMap_coe_weilPairingPointMu`. -/
@[simp]
theorem algebraMap_coe_weilPairingPointMuHom {g : W.FunctionField} (hg : g ≠ 0) {n : ℕ} [NeZero n]
    (P : Multiplicative (weilPairingPointSubgroup hg n)) :
    algebraMap F W.FunctionField ((weilPairingPointMuHom hg n P : Fˣ) : F)
      = weilPairingPointElt g (P.toAdd : W.Point) :=
  algebraMap_coe_weilPairingPointMu hg P.toAdd.2

/-! ### What being a homomorphism buys

⚠️ Each of the three below is a `map_*` field with no proof of its own.  In the pointwise
development each would have been a separate theorem; that is the content of the bundling. -/

open Classical in
/-- `e_n(g, −P) = e_n(g, P)⁻¹` in `μ_n(F)`, free from `map_inv`. -/
theorem weilPairingPointMuHom_inv {g : W.FunctionField} (hg : g ≠ 0) {n : ℕ} [NeZero n]
    (P : Multiplicative (weilPairingPointSubgroup hg n)) :
    weilPairingPointMuHom hg n P⁻¹ = (weilPairingPointMuHom hg n P)⁻¹ :=
  map_inv _ _

open Classical in
/-- `e_n(g, k • P) = e_n(g, P) ^ k` for `k : ℤ`, free from `map_zpow`.  There is no `F(W)`-level
form of this statement at either slot. -/
theorem weilPairingPointMuHom_zpow {g : W.FunctionField} (hg : g ≠ 0) {n : ℕ} [NeZero n]
    (P : Multiplicative (weilPairingPointSubgroup hg n)) (k : ℤ) :
    weilPairingPointMuHom hg n (P ^ k) = weilPairingPointMuHom hg n P ^ k :=
  map_zpow _ _ _

open Classical in
/-- **The kernel as a genuine subgroup**: "which points pair trivially with `g`" is
`MonoidHom.ker`, and membership in it is the `F(W)`-level equation. -/
theorem mem_ker_weilPairingPointMuHom_iff {g : W.FunctionField} (hg : g ≠ 0) {n : ℕ} [NeZero n]
    (P : Multiplicative (weilPairingPointSubgroup hg n)) :
    P ∈ MonoidHom.ker (weilPairingPointMuHom hg n)
      ↔ weilPairingPointElt g (P.toAdd : W.Point) = 1 :=
  weilPairingPointMu_eq_one_iff hg P.toAdd.2

/-! ### The domain is `E[n]`: the bridge at `n = 2` and `n = 3` -/

open Classical in
/-- **Every `2`-torsion point carries the datum**, for a rung-5 root `g` at any divisor point.  The
point at infinity is free; at an affine point this is
`weilPairingElt_pow_eq_one_of_gS_two_torsion` (`TranslationTorsion`) fed
`add_self_eq_zero_of_mem_torsion_two` (`Torsion/Defs`).

⚠️ No `[IsAlgClosed F]`: the rung-5 datum `hu` is an argument here, not something produced. -/
theorem torsion_le_weilPairingPointSubgroup_two (h2 : (2 : F) ≠ 0) {f g : W.FunctionField}
    {u : W.CoordinateRingˣ} (hg : g ≠ 0)
    (hu : (u : W.CoordinateRing) • g ^ 2 = mulByTwoEndo h2 f) :
    W.torsion 2 ≤ weilPairingPointSubgroup hg 2 := by
  rintro (_ | ⟨x, y, h⟩) hP
  · exact (weilPairingPointSubgroup hg 2).zero_mem
  · exact weilPairingElt_pow_eq_one_of_gS_two_torsion h.left h2
      (add_self_eq_zero_of_mem_torsion_two hP) hg hu

open Classical in
/-- **`e_2(S, ·) : E[2] → μ_2(F)` as a homomorphism of groups**, for a rung-5 root `g` at `S` over
an **arbitrary** field.  `weilPairingPointMuHom` restricted along the inclusion of `E[2]`.

⚠️ `nolint defsWithUnderscore` (`#1277`): `_two` is this development's index suffix for the
concrete `n = 2` track — the same suffix every theorem on that track carries — and is not a
compound name. -/
@[nolint defsWithUnderscore]
noncomputable def weilPairingTorsionMuHom_two (h2 : (2 : F) ≠ 0) {f g : W.FunctionField}
    {u : W.CoordinateRingˣ} (hg : g ≠ 0)
    (hu : (u : W.CoordinateRing) • g ^ 2 = mulByTwoEndo h2 f) :
    Multiplicative (W.torsion 2) →* rootsOfUnity 2 F :=
  (weilPairingPointMuHom hg 2).comp
    (AddMonoidHom.toMultiplicative
      (AddSubgroup.inclusion (torsion_le_weilPairingPointSubgroup_two h2 hg hu)))

open Classical in
/-- The values of `weilPairingTorsionMuHom_two` are the pairing values. -/
@[simp]
theorem algebraMap_coe_weilPairingTorsionMuHom_two (h2 : (2 : F) ≠ 0) {f g : W.FunctionField}
    {u : W.CoordinateRingˣ} (hg : g ≠ 0)
    (hu : (u : W.CoordinateRing) • g ^ 2 = mulByTwoEndo h2 f) (P : W.torsion 2) :
    algebraMap F W.FunctionField
        ((weilPairingTorsionMuHom_two h2 hg hu (Multiplicative.ofAdd P) : Fˣ) : F)
      = weilPairingPointElt g (P : W.Point) :=
  algebraMap_coe_weilPairingPointMu hg (torsion_le_weilPairingPointSubgroup_two h2 hg hu P.2)

open Classical in
/-- **Every `3`-torsion point carries the datum**, the `n = 3` mirror of
`torsion_le_weilPairingPointSubgroup_two`, off
`weilPairingElt_pow_eq_one_of_gS_three_baseField` (`TranslationTriplingComm`). -/
theorem torsion_le_weilPairingPointSubgroup_three (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0)
    {f g : W.FunctionField} {u : W.CoordinateRingˣ} (hg : g ≠ 0)
    (hu : (u : W.CoordinateRing) • g ^ 3 = mulByThreeEndo h2 h3 f) :
    W.torsion 3 ≤ weilPairingPointSubgroup hg 3 := by
  rintro (_ | ⟨x, y, h⟩) hP
  · exact (weilPairingPointSubgroup hg 3).zero_mem
  · exact weilPairingElt_pow_eq_one_of_gS_three_baseField h.left h2 h3
      (add_add_self_eq_zero_of_mem_torsion_three hP) hg hu

open Classical in
/-- **`e_3(S, ·) : E[3] → μ_3(F)` as a homomorphism of groups**, over an arbitrary field.

⚠️ `nolint defsWithUnderscore` (`#1277`): the `_three` index suffix, as for
`weilPairingTorsionMuHom_two`. -/
@[nolint defsWithUnderscore]
noncomputable def weilPairingTorsionMuHom_three (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0)
    {f g : W.FunctionField} {u : W.CoordinateRingˣ} (hg : g ≠ 0)
    (hu : (u : W.CoordinateRing) • g ^ 3 = mulByThreeEndo h2 h3 f) :
    Multiplicative (W.torsion 3) →* rootsOfUnity 3 F :=
  (weilPairingPointMuHom hg 3).comp
    (AddMonoidHom.toMultiplicative
      (AddSubgroup.inclusion (torsion_le_weilPairingPointSubgroup_three h2 h3 hg hu)))

open Classical in
/-- The values of `weilPairingTorsionMuHom_three` are the pairing values. -/
@[simp]
theorem algebraMap_coe_weilPairingTorsionMuHom_three (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0)
    {f g : W.FunctionField} {u : W.CoordinateRingˣ} (hg : g ≠ 0)
    (hu : (u : W.CoordinateRing) • g ^ 3 = mulByThreeEndo h2 h3 f) (P : W.torsion 3) :
    algebraMap F W.FunctionField
        ((weilPairingTorsionMuHom_three h2 h3 hg hu (Multiplicative.ofAdd P) : Fˣ) : F)
      = weilPairingPointElt g (P : W.Point) :=
  algebraMap_coe_weilPairingPointMu hg (torsion_le_weilPairingPointSubgroup_three h2 h3 hg hu P.2)

end CoordinateRing

variable {F : Type*} [Field F] {W : Affine F} [W.IsElliptic]

open CoordinateRing

/-! ### Over `F̄`, with no hypothesis beyond the setting -/

section IsAlgClosed

variable [IsAlgClosed F]

open Classical in
/-- **`e_2(S, ·) : E[2] → μ_2(F̄)` is a group homomorphism, unconditionally.**  The root at `S` and
its rung-5 certificate are produced by `exists_gS_two_of_isAlgClosed` (`#791`), which is the only
place `[IsAlgClosed F]` enters. -/
theorem exists_weilPairingTorsionMuHom_two (h2 : (2 : F) ≠ 0) {xS yS : F}
    (hS : W.Nonsingular xS yS) (hmS : Point.some xS yS hS ∈ W.torsion 2) :
    ∃ g : W.FunctionField, g ≠ 0 ∧
      (∃ f : W.FunctionField, f ≠ 0 ∧
        divisor W f = Finsupp.single (pointClosedPoint hS.left) (2 : ℤ) ∧
        ∃ u : W.CoordinateRingˣ, (u : W.CoordinateRing) • g ^ 2 = mulByTwoEndo h2 f) ∧
      ∃ φ : Multiplicative (W.torsion 2) →* rootsOfUnity 2 F, ∀ P : W.torsion 2,
        algebraMap F W.FunctionField ((φ (Multiplicative.ofAdd P) : Fˣ) : F)
          = weilPairingPointElt g (P : W.Point) := by
  obtain ⟨f, hf, hd, g, hg, u, hu⟩ := exists_gS_two_of_isAlgClosed h2 hS hmS
  exact ⟨g, hg, ⟨f, hf, hd, u, hu⟩, weilPairingTorsionMuHom_two h2 hg hu,
    fun P => algebraMap_coe_weilPairingTorsionMuHom_two h2 hg hu P⟩

open Classical in
/-- **`e_3(S, ·) : E[3] → μ_3(F̄)` is a group homomorphism, unconditionally.**  The `n = 3` mirror,
off `exists_gS_three_of_isAlgClosed` (`#825`). -/
theorem exists_weilPairingTorsionMuHom_three (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) {xS yS : F}
    (hS : W.Nonsingular xS yS) (hmS : Point.some xS yS hS ∈ W.torsion 3) :
    ∃ g : W.FunctionField, g ≠ 0 ∧
      (∃ f : W.FunctionField, f ≠ 0 ∧
        divisor W f = Finsupp.single (pointClosedPoint hS.left) (3 : ℤ) ∧
        ∃ u : W.CoordinateRingˣ, (u : W.CoordinateRing) • g ^ 3 = mulByThreeEndo h2 h3 f) ∧
      ∃ φ : Multiplicative (W.torsion 3) →* rootsOfUnity 3 F, ∀ P : W.torsion 3,
        algebraMap F W.FunctionField ((φ (Multiplicative.ofAdd P) : Fˣ) : F)
          = weilPairingPointElt g (P : W.Point) := by
  obtain ⟨f, hf, hd, g, hg, u, hu⟩ := exists_gS_three_of_isAlgClosed h2 h3 hS hmS
  exact ⟨g, hg, ⟨f, hf, hd, u, hu⟩, weilPairingTorsionMuHom_three h2 h3 hg hu,
    fun P => algebraMap_coe_weilPairingTorsionMuHom_three h2 h3 hg hu P⟩

end IsAlgClosed

/-! ### Non-vacuity

Every headline above is instantiated below.  The `g = 1` block certifies the ungated layer —
`weilPairingPointSubgroup`, `weilPairingPointMuHom` and its three free `map_*` consequences — on a
curve that exists, with **no hypothesis left over at all**: `e_n(1, P) = 1` at every point
(`weilPairingPointElt_one`), so the subgroup is the whole of `W.Point` and every membership is
discharged by proof.

The two `exists_` blocks certify the headlines that matter, on the curves `#845`/`#861`/`#873` use:
`y² = x³ − x` over `AlgebraicClosure ℚ` with `S = (0, 0) ∈ E[2]`, and `y² + y = x³` with
`S = (0, 0) ∈ E[3]`.  ⚠️ `#873` records why no second `3`-torsion point of `y² + y = x³` is
nameable; nothing here needs one, because the divisor point `S` is the only point the statement
constrains — the *whole* of `E[3]` is the domain of the map, named as a group rather than
point by point.  That is the one respect in which this file's certificate is stronger than
`#873`'s, and it is a consequence of bundling. -/

section Nonvacuity

/-! The certificate curves `y² = x³ − x` and `y² + y = x³` are the shared
`EllipticCurves.Fixture.y2EqX3SubX` and `EllipticCurves.Fixture.y2AddYEqX3`, and the base —
algebraically closed, and of characteristic `0` so that `2 ≠ 0` and `3 ≠ 0` — is
`EllipticCurves.Fixture.AlgClosedQ`, whose single `[CharZero F]` instance also supplies
`IsElliptic` here. -/

open EllipticCurves.Fixture

private lemma exampleTwo : (2 : AlgClosedQ) ≠ 0 := two_ne_zero

private lemma exampleThree : (3 : AlgClosedQ) ≠ 0 := three_ne_zero_of_charZero _

private lemma exampleOne : (1 : (y2EqX3SubX AlgClosedQ).FunctionField) ≠ 0 := one_ne_zero

/-- Every point of `y² = x³ − x` lies in the subgroup at `g = 1`, by `weilPairingPointElt_one`:
the subgroup is not merely nonempty, it is everything. -/
private lemma exampleMemAll (P : (y2EqX3SubX AlgClosedQ).Point) :
    P ∈ weilPairingPointSubgroup exampleOne 2 := by
  rw [mem_weilPairingPointSubgroup_iff, weilPairingPointElt_one, one_pow]

/-- A point of the curve, read as an element of the domain of `weilPairingPointMuHom`. -/
private noncomputable abbrev exampleElt (P : (y2EqX3SubX AlgClosedQ).Point) :
    Multiplicative (weilPairingPointSubgroup exampleOne 2) :=
  Multiplicative.ofAdd (⟨P, exampleMemAll P⟩ : weilPairingPointSubgroup exampleOne 2)

/-- On a curve that exists, the bundled translation-slot map sends the identity of the group to the
identity of `μ_2(F̄)` — `map_one`, with nothing assumed. -/
example : weilPairingPointMuHom exampleOne 2 1 = 1 :=
  map_one (weilPairingPointMuHom exampleOne 2)

/-- **`map_mul` on a curve that exists**, at two arbitrary points of `y² = x³ − x`: the certificate
that the bundling has the content the pointwise statements did not.  ⚠️ Neither point is assumed
affine — this instance ranges over the point at infinity too, which is exactly what no merged
translation-slot statement can do. -/
example (P Q : (y2EqX3SubX AlgClosedQ).Point) :
    weilPairingPointMuHom exampleOne 2 (exampleElt P * exampleElt Q) =
      weilPairingPointMuHom exampleOne 2 (exampleElt P) *
        weilPairingPointMuHom exampleOne 2 (exampleElt Q) :=
  map_mul (weilPairingPointMuHom exampleOne 2) _ _

/-- `map_inv` on a curve that exists. -/
example (P : (y2EqX3SubX AlgClosedQ).Point) :
    weilPairingPointMuHom exampleOne 2 (exampleElt P)⁻¹ =
      (weilPairingPointMuHom exampleOne 2 (exampleElt P))⁻¹ :=
  weilPairingPointMuHom_inv exampleOne (exampleElt P)

/-- `map_zpow` at a concrete negative exponent, on a curve that exists.  There is no `F(W)`-level
statement of this shape at either slot. -/
example (P : (y2EqX3SubX AlgClosedQ).Point) :
    weilPairingPointMuHom exampleOne 2 (exampleElt P ^ (-3 : ℤ)) =
      weilPairingPointMuHom exampleOne 2 (exampleElt P) ^ (-3 : ℤ) :=
  weilPairingPointMuHom_zpow exampleOne (exampleElt P) (-3)

/-- The kernel is everything at `g = 1`, on a curve that exists: every point pairs trivially with
the trivial function.  Discharged outright. -/
example (P : (y2EqX3SubX AlgClosedQ).Point) :
    exampleElt P ∈ MonoidHom.ker (weilPairingPointMuHom exampleOne 2) :=
  (mem_ker_weilPairingPointMuHom_iff exampleOne (exampleElt P)).mpr (weilPairingPointElt_one P)

private lemma exampleNsS : (y2EqX3SubX AlgClosedQ).Nonsingular 0 0 :=
  (y2EqX3SubX AlgClosedQ).equation_iff_nonsingular.mp (by
    norm_num [y2EqX3SubX, WeierstrassCurve.Affine.equation_iff])

open Classical in
private lemma exampleTorS :
    Point.some (0 : AlgClosedQ) 0 exampleNsS ∈ (y2EqX3SubX AlgClosedQ).torsion 2 :=
  (mem_torsion_two_some_iff exampleNsS).mpr (by norm_num [y2EqX3SubX])

open Classical in
/-- **`e_2(S, ·) : E[2] → μ_2(F̄)` is a group homomorphism computing the pairing, on a curve that
exists.**  `S = (0, 0)` on `y² = x³ − x`; no hypothesis survives. -/
example : ∃ (g : (y2EqX3SubX AlgClosedQ).FunctionField)
    (φ : Multiplicative ((y2EqX3SubX AlgClosedQ).torsion 2) →* rootsOfUnity 2 AlgClosedQ),
    ∀ P : (y2EqX3SubX AlgClosedQ).torsion 2,
      algebraMap AlgClosedQ (y2EqX3SubX AlgClosedQ).FunctionField
          ((φ (Multiplicative.ofAdd P) : AlgClosedQˣ) : AlgClosedQ)
        = weilPairingPointElt g (P : (y2EqX3SubX AlgClosedQ).Point) := by
  obtain ⟨g, -, -, φ, hφ⟩ := exists_weilPairingTorsionMuHom_two exampleTwo exampleNsS exampleTorS
  exact ⟨g, φ, hφ⟩

private lemma exampleNsThreeS : (y2AddYEqX3 AlgClosedQ).Nonsingular 0 0 :=
  (y2AddYEqX3 AlgClosedQ).equation_iff_nonsingular.mp (by
    norm_num [y2AddYEqX3, WeierstrassCurve.Affine.equation_iff])

open Classical in
private lemma exampleTorThreeS :
    Point.some (0 : AlgClosedQ) 0 exampleNsThreeS ∈ (y2AddYEqX3 AlgClosedQ).torsion 3 :=
  mem_torsion_three_some_iff'.mpr (by
    norm_num [y2AddYEqX3, WeierstrassCurve.Ψ₃, WeierstrassCurve.b₂,
      WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈])

open Classical in
/-- **`e_3(S, ·) : E[3] → μ_3(F̄)` is a group homomorphism computing the pairing, on a curve that
exists.**  `S = (0, 0)` on `y² + y = x³`.  ⚠️ Unlike `#873`'s `n = 3` certificate this needs only
the **divisor** point to be nameable: the translation slot is quantified as a group, not as three
named points, so the fact that no second `3`-torsion point of this curve is nameable does not bite.
That is the one respect in which bundling strengthens the certificate. -/
example : ∃ (g : (y2AddYEqX3 AlgClosedQ).FunctionField)
    (φ : Multiplicative ((y2AddYEqX3 AlgClosedQ).torsion 3) →* rootsOfUnity 3 AlgClosedQ),
    ∀ P : (y2AddYEqX3 AlgClosedQ).torsion 3,
      algebraMap AlgClosedQ (y2AddYEqX3 AlgClosedQ).FunctionField
          ((φ (Multiplicative.ofAdd P) : AlgClosedQˣ) : AlgClosedQ)
        = weilPairingPointElt g (P : (y2AddYEqX3 AlgClosedQ).Point) := by
  obtain ⟨g, -, -, φ, hφ⟩ := exists_weilPairingTorsionMuHom_three exampleTwo exampleThree
    exampleNsThreeS exampleTorThreeS
  exact ⟨g, φ, hφ⟩

end Nonvacuity

end WeierstrassCurve.Affine
