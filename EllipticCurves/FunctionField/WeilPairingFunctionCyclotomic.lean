/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import EllipticCurves.FunctionField.WeilPairingFunctionGalois
import EllipticCurves.FunctionField.WeilPairingSurjective
import EllipticCurves.Galois.CyclotomicCharacter

/-!
# `e_n(σS, σT) = e_n(S, T) ^ χ_n(σ)` for the Weil pairing as a function of two points

`EllipticCurves.FunctionField.WeilPairingCyclotomic` (`#867`) put the Galois-equivariance of the
Weil pairing into Silverman's exponent form

```
e_n(σS, σT) = e_n(S, T) ^ χ_n(σ)
```

for `weilPairingMu`, the value attached to *rung-5 and divisor data*.  That form does not compose:
`weilPairingMu` takes the root as an argument, so there is no term `e_n(σS, σT)` in it and the
three merged shapes there each thread their own hypothesis.  `#922`/`#925` replaced the existential
packaging by genuine functions `weilPairingTwo`, `weilPairingThree` of two torsion points, and
`#936` gave those functions their equivariance,

```
restrictRootsOfUnity σ n (e_n(S, T)) = e_n(σ • S, σ • T),
```

with no data threaded and no hypothesis beyond `(n : F) ≠ 0`.  **This file is the exponent form of
that equation**: both sides name themselves, nothing is carried, and the statement composes with
bilinearity, non-degeneracy and perfectness.

## What supplies the character's hypothesis, and why that is the whole cost

`galoisModularCyclotomicChar S F hn` asks for `hn : Nat.card μ_n(F) = n` — that `F` really has `n`
`n`-th roots of unity.  ⚠️ **On this front that hypothesis is free**, and it became free only
recently: `natCard_rootsOfUnity_of_ne_zero` (`EllipticCurves.FunctionField.WeilPairingSurjective`,
`#938`) derives it from `(n : F) ≠ 0` over an algebraically closed `F`, which is exactly the
`h2` / `h3` these functions already carry.  So the exponent form below takes **no hypothesis at all
beyond the ones `#936` already had**, and the character appearing in it is canonical: it is the one
attached to `natCard_rootsOfUnity_of_ne_zero h2`, not to an arbitrary proof supplied by the caller.

## ⚠️ At `n = 2` the twist is trivial, and that is a theorem rather than a coincidence

`(ZMod 2)ˣ` is a subsingleton, so `χ_2` is the trivial character of *every* extension `F / S` —
`galoisModularCyclotomicChar_two_eq_one`, which mentions no curve.  Therefore

```
e_2(σ • S, σ • T) = e_2(S, T)     for every σ, with no hypothesis on S or T,
```

`weilPairingTwo_galois_eq_self`.  ⚠️ **This is strictly stronger than what `#936`'s own
certificate could show**, and the difference is worth stating because it is the first place on this
front where `n = 2` and `n = 3` genuinely part company.  `#936`'s invariance certificate had to
consume the `ℚ`-rationality of both points; this one holds for *any* pair of `2`-torsion points on
*any* elliptic curve over *any* algebraically closed `F` of characteristic `≠ 2`, because the
obstruction was never the points — it was the value group, and `μ_2 = {±1}` sits in the prime
field.  At `n = 3` there is no such theorem, only the conditional
`weilPairingThree_galois_eq_self_of_forall_fixed`, and the Non-vacuity section below compiles the
failure of the unconditional script to show the difference is real and not a gap in effort.

## Main statements

* `galoisModularCyclotomicChar_two_eq_one` — `χ_2` is trivial, for every `F / S`; a statement about
  a field extension, in the root namespace.
* `WeierstrassCurve.Affine.weilPairingTwo_galois_eq_pow`,
  `…weilPairingThree_galois_eq_pow` — **the exponent form**,
  `e_n(σ • S, σ • T) = e_n(S, T) ^ (χ_n σ).val`.
* `WeierstrassCurve.Affine.weilPairingTwo_galois_eq_self` — `e_2` is `Gal(F/S)`-invariant,
  unconditionally.
* `WeierstrassCurve.Affine.weilPairingThree_galois_eq_self_of_forall_fixed` — `e_3` is invariant
  under any `σ` fixing `μ_3(F)` pointwise, which by `galoisModularCyclotomicChar_eq_one_iff` is
  exactly the kernel of `χ_3`.

## Naming and placement

`galoisModularCyclotomicChar_two_eq_one` mentions no curve and sits at the root, above
`namespace WeierstrassCurve.Affine`; `#938` and `#940` placed their curve-free inputs the same way,
and putting a curve namespace on a curve-free statement is `#903`'s defect one level up.
Everything else is in `WeierstrassCurve.Affine` with `open CoordinateRing`, `#903`'s house pattern
as enforced by `#918` and `#927`.  ⚠️ Note that the `weilPairingMu`-level twins in
`EllipticCurves.FunctionField.WeilPairingCyclotomic` live in
`WeierstrassCurve.Affine.CoordinateRing`, one namespace deeper: that is `#936`'s split, not an
inconsistency introduced here — the *function*-level statements have been in `Affine` since `#922`.

## Explicitly out of scope

* **General `n`** — `#404`'s `ωₙ` crux, transitively Ward-blocked, as everywhere on this front.
  ⚠️ Like `#940` and unlike `#938`, the argument here carries **no second obstruction**: it is one
  rewrite of `#936`'s equation by a statement about `μ_n(F)` that is already general in `n`, so it
  transcribes to any `n` at which `weilPairingN` and its equivariance exist.
* **The `p`-adic level.**  `weilPairingMu_galois_of_transport_eq_pow_padic` states the `n = p ^ k`
  form off `galoisCyclotomicChar_toZModPow`, and `n = 2` is the level `k = 1` of `p = 2`.  ⚠️ It is
  absent here **on purpose and the reason is not cost**: at `n = 2` the exponent is `1` by the
  triviality above, so the `p`-adic restatement would carry no information the unconditional
  invariance does not already carry.  It becomes worth writing at `n = 4`, which needs general `n`.
* **`det ρ_{E,ℓ} = χ_ℓ`.**  `EllipticCurves.TateModule.Determinant`'s `galoisDetTwo` and the
  cyclotomic character have had the same type since `EllipticCurves.Galois.CyclotomicCharacter`;
  what is still missing is the pairing on `E[2 ^ k]` for `k > 1`, not this rewrite.  ⚠️ Nothing in
  this file brings that identification closer, and saying so is the point of naming it.
* **The `F(W⁄F)`-level (`weilPairingEltTwo`, `weilPairingEltThree`) forms.**  `χ_n` acts on
  `μ_n(F)`; there is no exponent statement to make at the function-field level, where the action is
  `galoisFunctionField σ` and the value is not a root of unity in `F`.
* **Non-degeneracy of the twist** — that some `σ` really has `χ_3 σ ≠ 1`, and hence that `e_3` is
  *not* `Gal(F/ℚ)`-invariant.  ⚠️ True, and it needs an automorphism of `AlgebraicClosure ℚ`
  moving a primitive cube root of unity; that is a Galois-theoretic existence statement about the
  base field with nothing to do with the curve, and it is not spiked.  The Non-vacuity section
  below makes the weaker, checkable point instead: the unconditional script *fails* at `n = 3`.

## References

* [J. H. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.8, Prop. 8.1(e).
-/

/-- **The mod-`2` cyclotomic character is trivial**, for every extension `F / S`.

`(ZMod 2)ˣ` has one element, so there is nothing for `χ_2` to record: the only square roots of `1`
in a field are `± 1`, both of which lie in the prime field and are therefore fixed by every
`S`-algebra automorphism.  ⚠️ This is what makes `weilPairingTwo_galois_eq_self` unconditional,
and it is the reason `n = 2` and `n = 3` part company on this front.

A statement about a field extension and nothing else; it belongs beside
`galoisModularCyclotomicChar` itself. -/
theorem galoisModularCyclotomicChar_two_eq_one {S F : Type*} [Field S] [Field F] [Algebra S F]
    (hn : Nat.card { x // x ∈ rootsOfUnity 2 F } = 2) (σ : F ≃ₐ[S] F) :
    galoisModularCyclotomicChar S F hn σ = 1 :=
  Subsingleton.elim _ _

namespace WeierstrassCurve.Affine

open CoordinateRing

variable {S F : Type*} [Field S] [Field F] [Algebra S F] {W : Affine S} [W.IsElliptic]
  [IsAlgClosed F]

/-! ### `n = 2` -/

open Classical in
/-- **The Weil pairing at `n = 2` in cyclotomic form**:

```
e_2(σ • S, σ • T) = e_2(S, T) ^ χ_2(σ).
```

`#936`'s equivariance says `σ` acts on the value; this says *how*.  One rewrite of
`weilPairingTwo_galois` by `restrictRootsOfUnity_eq_pow_galoisModularCyclotomicChar`, with the
character's hypothesis `Nat.card μ_2(F) = 2` discharged by `natCard_rootsOfUnity_of_ne_zero`
(`#938`) from the `h2` the pairing already carries — so the character named here is canonical and
the caller supplies nothing.

⚠️ At `n = 2` the exponent is `1`; see `weilPairingTwo_galois_eq_self`, which is the statement
worth quoting.  This one is kept because it is the `n`-uniform shape, and because the `n = 3` twin
is not degenerate. -/
theorem weilPairingTwo_galois_eq_pow (σ : F ≃ₐ[S] F) (h2 : (2 : F) ≠ 0) (P T : (W⁄F).torsion 2) :
    weilPairingTwo h2 (σ • P) (σ • T)
      = weilPairingTwo h2 P T
        ^ ((galoisModularCyclotomicChar S F (natCard_rootsOfUnity_of_ne_zero h2) σ :
            ZMod 2)).val := by
  rw [← weilPairingTwo_galois σ h2 P T, restrictRootsOfUnity_eq_pow_galoisModularCyclotomicChar]

open Classical in
/-- **The Weil pairing at `n = 2` is `Gal(F/S)`-invariant**, with no hypothesis on either point:

```
e_2(σ • S, σ • T) = e_2(S, T)     for every σ.
```

The twist is `χ_2`, which is trivial (`galoisModularCyclotomicChar_two_eq_one`).  ⚠️ Compare
`#936`, whose invariance *certificate* had to take two `ℚ`-rational points on a named curve: the
obstruction there was never the points, it was that the equation as stated says only that `σ`
carries the value to the value at the moved points.  Here the value group settles it, so the
statement is about every pair of `2`-torsion points on every elliptic curve over every
algebraically closed `F` with `2 ≠ 0`.

⚠️ There is no `n = 3` analogue; see `weilPairingThree_galois_eq_self_of_forall_fixed`, which has
to assume what is automatic here. -/
theorem weilPairingTwo_galois_eq_self (σ : F ≃ₐ[S] F) (h2 : (2 : F) ≠ 0)
    (P T : (W⁄F).torsion 2) :
    weilPairingTwo h2 (σ • P) (σ • T) = weilPairingTwo h2 P T := by
  rw [weilPairingTwo_galois_eq_pow σ h2 P T,
    galoisModularCyclotomicChar_two_eq_one (natCard_rootsOfUnity_of_ne_zero h2) σ,
    Units.val_one, show ((1 : ZMod 2)).val = 1 from by decide, pow_one]

/-! ### `n = 3` -/

open Classical in
/-- **The Weil pairing at `n = 3` in cyclotomic form**:

```
e_3(σ • S, σ • T) = e_3(S, T) ^ χ_3(σ),
```

the `n = 3` twin of `weilPairingTwo_galois_eq_pow` and, unlike it, **not** degenerate: `(ZMod 3)ˣ`
has two elements, so `χ_3` records a genuine invariant of `σ`
(`galoisModularCyclotomicChar_eq_one_iff`).

⚠️ Which hypothesis does what, as everywhere on this front: the character and its hypothesis are
gated on `h3` alone — the value group is `μ_3(F)` — and `h2` enters only through
`weilPairingThree_galois`, which needs it to build the pairing at all. -/
theorem weilPairingThree_galois_eq_pow (σ : F ≃ₐ[S] F) (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0)
    (P T : (W⁄F).torsion 3) :
    weilPairingThree h2 h3 (σ • P) (σ • T)
      = weilPairingThree h2 h3 P T
        ^ ((galoisModularCyclotomicChar S F (natCard_rootsOfUnity_of_ne_zero h3) σ :
            ZMod 3)).val := by
  rw [← weilPairingThree_galois σ h2 h3 P T,
    restrictRootsOfUnity_eq_pow_galoisModularCyclotomicChar]

open Classical in
/-- **`e_3` is invariant under any `σ` fixing the cube roots of unity pointwise.**

By `galoisModularCyclotomicChar_eq_one_iff` the hypothesis is exactly `χ_3 σ = 1`, so this is the
sharp conditional form of which `weilPairingTwo_galois_eq_self` is the unconditional `n = 2`
shadow: there the kernel of the character is everything, here it is a proper subgroup in general.
⚠️ The hypothesis is stated as "σ fixes every cube root of unity" rather than as `χ_3 σ = 1`
because that is the form a consumer can check without naming the character. -/
theorem weilPairingThree_galois_eq_self_of_forall_fixed (σ : F ≃ₐ[S] F) (h2 : (2 : F) ≠ 0)
    (h3 : (3 : F) ≠ 0) (hσ : ∀ t ∈ rootsOfUnity 3 F, σ ((t : Fˣ) : F) = ((t : Fˣ) : F))
    (P T : (W⁄F).torsion 3) :
    weilPairingThree h2 h3 (σ • P) (σ • T) = weilPairingThree h2 h3 P T := by
  rw [weilPairingThree_galois_eq_pow σ h2 h3 P T,
    (galoisModularCyclotomicChar_eq_one_iff (natCard_rootsOfUnity_of_ne_zero h3) σ).mpr hσ,
    Units.val_one, show ((1 : ZMod 3)).val = 1 from by decide, pow_one]

/-! ### Non-vacuity

Everything above carries `[IsAlgClosed F]`, so `ℚ` cannot witness it; the certificates are on
`#936`'s own curves base-changed to `AlgebraicClosure ℚ`, with `S = ℚ`, so that `Gal(F/ℚ)` is a
genuine group and not the trivial one.

⚠️ **Which certificates are load-bearing, and the three compiled checks that say so.**  `#940`
recorded that a statement universally quantified in the curve alone has no degenerate argument to
substitute, so its certificate is weightless.  That is not the situation here: both load-bearing
certificates below were checked by `#936`'s technique — delete an input, watch the script stop
closing — and all three failures were compiled and are quoted verbatim, not paraphrased.

* Dropping `weilPairingTwo_galois_eq_self` from the `n = 2` certificate leaves
  `⊢ weilPairingTwo exampleTwo (σ • exampleS) (σ • exampleT) = weilPairingTwo exampleTwo exampleS
  exampleT` under `error: unsolved goals` — so that certificate really is `#936`'s conclusion
  reached without either point's rationality, and not a restatement of the equivariance equation.
* Dropping `exampleSThree_fixed` from the `n = 3` certificate leaves
  `⊢ weilPairingThree … exampleSThree exampleSThree = weilPairingThree … (σ • exampleSThree)
  (σ • exampleSThree)` under `error: unsolved goals`.
* Naming the theorem that does not exist gives
  `` error(lean.unknownIdentifier): Unknown identifier `weilPairingThree_galois_eq_self` ``.
  ⚠️ That is the compiled half of this file's asymmetry: at `n = 2` the invariance is a theorem, at
  `n = 3` there is nothing to apply.

⚠️ **And a trap this block fell into on the way, worth more than the certificates themselves.**  The
`n = 3` certificate was first written as

```
e_3(σ • S, σ • T) = e_3(S, T)      closed by `rw [exampleSThree_fixed]`
```

which **compiles and certifies nothing**: rewriting the *arguments* back makes the two sides
syntactically equal without ever mentioning a theorem of this file.  ⚠️ A non-vacuity certificate
whose conclusion moves the points must be closed by moving the *value*, which is why `#936` states
its own at the `restrictRootsOfUnity` level and why both certificates below do too.  A green build
is not evidence that a certificate consumed anything. -/

section Nonvacuity

/-- The curve `y² = x³ − x` over `ℚ`, `#936`'s `n = 2` certificate curve. -/
private noncomputable def exampleCurve : Affine ℚ := ⟨0, 0, 0, -1, 0⟩

/-- An algebraically closed extension of `ℚ`, so that `Gal(F/ℚ)` is not the trivial group. -/
private abbrev exampleField : Type := AlgebraicClosure ℚ

private instance : exampleCurve.IsElliptic := by
  rw [WeierstrassCurve.isElliptic_iff, isUnit_iff_ne_zero]
  norm_num [exampleCurve, WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈]

private lemma exampleTwo : (2 : exampleField) ≠ 0 := by norm_num

private lemma exampleThree : (3 : exampleField) ≠ 0 := by norm_num

/-- `S = (0, 0)` lies on the base-changed curve and is nonsingular. -/
private lemma exampleNonsingular : (exampleCurve⁄exampleField).Nonsingular 0 0 :=
  (exampleCurve⁄exampleField).equation_iff_nonsingular.mp (by
    simp [exampleCurve, WeierstrassCurve.Affine.equation_iff])

/-- `T = (1, 0)` lies on the base-changed curve and is nonsingular. -/
private lemma exampleNonsingularTranslate : (exampleCurve⁄exampleField).Nonsingular 1 0 :=
  (exampleCurve⁄exampleField).equation_iff_nonsingular.mp (by
    simp [exampleCurve, WeierstrassCurve.Affine.equation_iff])

open Classical in
/-- `S = (0, 0)` is `2`-torsion: `2y + a₁x + a₃ = 0` reads `0 = 0`. -/
private lemma exampleTorsion :
    Point.some (0 : exampleField) 0 exampleNonsingular ∈ (exampleCurve⁄exampleField).torsion 2 :=
  (mem_torsion_two_some_iff exampleNonsingular).mpr (by simp [exampleCurve])

open Classical in
/-- `T = (1, 0)` is `2`-torsion, as at `(0, 0)`. -/
private lemma exampleTorsionTranslate :
    Point.some (1 : exampleField) 0 exampleNonsingularTranslate
      ∈ (exampleCurve⁄exampleField).torsion 2 :=
  (mem_torsion_two_some_iff exampleNonsingularTranslate).mpr (by simp [exampleCurve])

open Classical in
/-- `S = (0, 0)` as an element of `E[2]`. -/
private noncomputable def exampleS : (exampleCurve⁄exampleField).torsion 2 :=
  ⟨Point.some 0 0 exampleNonsingular, exampleTorsion⟩

open Classical in
/-- `T = (1, 0)` as an element of `E[2]`, distinct from `exampleS`. -/
private noncomputable def exampleT : (exampleCurve⁄exampleField).torsion 2 :=
  ⟨Point.some 1 0 exampleNonsingularTranslate, exampleTorsionTranslate⟩

open Classical in
/-- **The exponent form at `n = 2`, on a curve that exists**, at two distinct named `2`-torsion
points.  A schema instance, universally quantified in `σ`. -/
example (σ : exampleField ≃ₐ[ℚ] exampleField) :
    weilPairingTwo exampleTwo (σ • exampleS) (σ • exampleT)
      = weilPairingTwo exampleTwo exampleS exampleT
        ^ ((galoisModularCyclotomicChar ℚ exampleField
            (natCard_rootsOfUnity_of_ne_zero exampleTwo) σ : ZMod 2)).val :=
  weilPairingTwo_galois_eq_pow σ exampleTwo exampleS exampleT

open Classical in
/-- **⚠️ The load-bearing certificate at `n = 2`: `#936`'s own conclusion, with strictly fewer
inputs.**

```
σ · e_2((0,0), (1,0)) = e_2((0,0), (1,0))     in μ_2(F).
```

This is character-for-character the statement `#936`'s file calls *its* load-bearing certificate,
and there it consumes `exampleS_fixed` and `exampleT_fixed` — the `ℚ`-rationality of both points,
false for a general pair.  Here **neither is named**: the value is moved by `#936`'s equivariance
and then moved back by `weilPairingTwo_galois_eq_self`, which knows nothing about these points.
⚠️ Same conclusion, one strictly weaker set of inputs, both compiled — that is the whole claim, and
it is checkable rather than asserted.  ⚠️ It does **not** transfer to `n = 3`: the second rewrite
has no `n = 3` twin to be, and the `n = 3` certificate above names the rationality.

⚠️ **Not overclaimed**: this conclusion is *also* reachable without any pairing theory at all, since
`galoisModularCyclotomicChar_two_eq_one` says `σ` fixes every element of `μ_2(F)` and the value is
one.  What the script below shows is that *this file's* route reaches `#936`'s conclusion without
`#936`'s two inputs — which is the claim being made, and the reason the `n = 3` certificate is the
one that carries the exponent. -/
example (σ : exampleField ≃ₐ[ℚ] exampleField) :
    restrictRootsOfUnity (σ.toRingEquiv.toRingHom) 2 (weilPairingTwo exampleTwo exampleS exampleT)
      = weilPairingTwo exampleTwo exampleS exampleT := by
  rw [weilPairingTwo_galois σ exampleTwo exampleS exampleT,
    weilPairingTwo_galois_eq_self σ exampleTwo exampleS exampleT]

/-- The curve `y² + y = x³` over `ℚ`, `#936`'s `n = 3` certificate curve. -/
private noncomputable def exampleCurveThree : Affine ℚ := ⟨0, 0, 1, 0, 0⟩

private instance : exampleCurveThree.IsElliptic := by
  rw [WeierstrassCurve.isElliptic_iff, isUnit_iff_ne_zero]
  norm_num [exampleCurveThree, WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈]

/-- `S = (0, 0)` lies on the base-changed curve `y² + y = x³` and is nonsingular. -/
private lemma exampleNonsingularThree : (exampleCurveThree⁄exampleField).Nonsingular 0 0 :=
  (exampleCurveThree⁄exampleField).equation_iff_nonsingular.mp (by
    simp [exampleCurveThree, WeierstrassCurve.Affine.equation_iff])

open Classical in
/-- `S = (0, 0)` is `3`-torsion: `Ψ₃ = 3X⁴ + 3b₆X` vanishes at `0`. -/
private lemma exampleTorsionThree :
    Point.some (0 : exampleField) 0 exampleNonsingularThree
      ∈ (exampleCurveThree⁄exampleField).torsion 3 :=
  mem_torsion_three_some_iff'.mpr (by
    simp [exampleCurveThree, WeierstrassCurve.Ψ₃, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
      WeierstrassCurve.b₆, WeierstrassCurve.b₈])

open Classical in
/-- `S = (0, 0)` as an element of `E[3]`. -/
private noncomputable def exampleSThree : (exampleCurveThree⁄exampleField).torsion 3 :=
  ⟨Point.some 0 0 exampleNonsingularThree, exampleTorsionThree⟩

open Classical in
/-- `(0, 0)` is `ℚ`-rational on `y² + y = x³`, so every `σ` fixes it. -/
private lemma exampleSThree_fixed (σ : exampleField ≃ₐ[ℚ] exampleField) :
    σ • exampleSThree = exampleSThree :=
  Subtype.ext ((Point.galois_smul_some_eq_some_iff σ exampleNonsingularThree
    exampleNonsingularThree).mpr ⟨(map_zero σ).symm, (map_zero σ).symm⟩)

open Classical in
/-- **The exponent form at `n = 3`**, on `#936`'s curve.

⚠️ Taken at `S = T = (0, 0)`, a limitation of the curve and not of the statement: the only
nameable `3`-torsion points on `y² + y = x³` are `(0, 0)` and its negative, since the `X = −1`
fibre of `Ψ₃ = 3X(X³ + 1)` is `y² + y + 1 = 0`.  The same limitation is recorded by `#936` and by
`WeilPairingGaloisRoot` about the same curve. -/
example (σ : exampleField ≃ₐ[ℚ] exampleField) :
    weilPairingThree exampleTwo exampleThree (σ • exampleSThree) (σ • exampleSThree)
      = weilPairingThree exampleTwo exampleThree exampleSThree exampleSThree
        ^ ((galoisModularCyclotomicChar ℚ exampleField
            (natCard_rootsOfUnity_of_ne_zero exampleThree) σ : ZMod 3)).val :=
  weilPairingThree_galois_eq_pow σ exampleTwo exampleThree exampleSThree exampleSThree

open Classical in
/-- **⚠️ The load-bearing certificate at `n = 3`: the value at a `ℚ`-rational `3`-torsion point is
its own `χ_3`-power.**

```
e_3((0,0), (0,0)) = e_3((0,0), (0,0)) ^ χ_3(σ).
```

This consumes `weilPairingThree_galois_eq_pow` **and** `exampleSThree_fixed`, and neither can be
dropped: without the rationality the two sides are pairings at different points, and without the
exponent theorem there is nothing that produces the power at all.  ⚠️ It is not `rfl` and it is
not closed by rewriting the arguments — which is the trap the next certificate note describes. -/
example (σ : exampleField ≃ₐ[ℚ] exampleField) :
    weilPairingThree exampleTwo exampleThree exampleSThree exampleSThree
      = weilPairingThree exampleTwo exampleThree exampleSThree exampleSThree
        ^ ((galoisModularCyclotomicChar ℚ exampleField
            (natCard_rootsOfUnity_of_ne_zero exampleThree) σ : ZMod 3)).val := by
  rw [← weilPairingThree_galois_eq_pow σ exampleTwo exampleThree exampleSThree exampleSThree,
    exampleSThree_fixed]

open Classical in
/-- **The conditional `n = 3` invariance, on the same curve**, so that the hypothesis-carrying
statement is certified and not only the exponent form.  A schema instance in `σ` and in the
hypothesis. -/
example (σ : exampleField ≃ₐ[ℚ] exampleField)
    (hσ : ∀ t ∈ rootsOfUnity 3 exampleField, σ ((t : exampleFieldˣ) : exampleField)
      = ((t : exampleFieldˣ) : exampleField)) :
    weilPairingThree exampleTwo exampleThree (σ • exampleSThree) (σ • exampleSThree)
      = weilPairingThree exampleTwo exampleThree exampleSThree exampleSThree :=
  weilPairingThree_galois_eq_self_of_forall_fixed σ exampleTwo exampleThree hσ exampleSThree
    exampleSThree

end Nonvacuity

end WeierstrassCurve.Affine
