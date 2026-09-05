/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import EllipticCurves.Fixtures
import EllipticCurves.FunctionField.WeilPairingGaloisRoot

/-!
# Galois-equivariance of the Weil pairing over an ARBITRARY field, with `hprin` the only gate

`EllipticCurves.FunctionField.WeilPairingGaloisRoot` proves

```
σ⋆(e_n(S, T)) = e_n(σS, σT)          in `F(W⁄F)` and in `μ_n(F)`, at `n = 2` and `n = 3`,
```

with no hypothesis beyond the setting, over an **algebraically closed** base field.  This file
states the same four theorems over an arbitrary base field, with the closure replaced by the
principality hypothesis `hprin` and by nothing else.  Every conclusion is token-identical to its
twin's.

## What is actually going on

The closure is not used by the Galois argument at all.  `WeilPairingGaloisRoot`'s module docstring
says so itself:

> `[IsAlgClosed F]` appears only in the four `exists_` theorems, and only through `#791` and `#825`.

The engine `weilPairingElt_galois_of_gS_*` and every transport statement it consumes are already
stated over an arbitrary field; the four `exists_` headlines are the *assembly*, and their only
call into the closed world is the rung-5 root producer.  So the whole edit is the substitution

```
exists_gS_two_of_isAlgClosed h2 h hS  ↦  exists_gS_two h2 h hS (hprin h hS)
```

`EllipticCurves.FunctionField.NthRootOfPullback` states `exists_gS_two`/`exists_gS_three` with the
`hprin` hypothesis; `EllipticCurves.FunctionField.PullbackPrincipalityTwo` (`#791`) and
`…Three` (`#825`) derive the `F̄` corollaries by discharging it.  Nothing else in either body
changes, and no hypothesis is added or weakened.

⚠️ **The substitution is applied *twice* per headline, and that is what makes this file's `hprin`
different from `#913`'s.**  A Galois statement produces a root at `S` **and** a root at `σS`, so the
producer is called at two points.  `exists_gS_two`'s own `hprin` is *point-specific* — it names
`pointClosedPoint h.1` for the point it is applied at — so a `hprin` bound to a single point, which
is what `EllipticCurves.FunctionField.WeilPairingTranslationSlotHprin` takes, cannot serve both.
The uniform form below, quantified over the point, is `#912`'s
(`EllipticCurves.FunctionField.WeilPairingDivisorSlotBilinearHprin`), and it is forced here rather
than chosen.

⚠️ **`hprin` is not discharged by any of this and cannot be.**  `#899` recorded the test that
decides which obstructions descend: *is the obstruction used to prove an equality, or to produce a
witness?*  `hprin` produces a witness, so it does not descend.  Over `F̄` it is discharged by
`#791`/`#825`, which is exactly what the twins in `WeilPairingGaloisRoot` do.

⚠️ **The `σ`-side data is derived, never assumed a second time.**  `σS` is again a nonsingular
affine `n`-torsion point, by `nonsingular_algEquiv` and `Point.mem_torsion_galois_smul_some`, and
those two lemmas are what `hprin`'s second application is fed.  As in the twins, `g'` is
emphatically *not* `σ⋆ g`: the constant relating them is what the pairing quotient cancels.

## The four theorems, and the shape of the `μ_n(F)` pair

| | from rung-5 data | over `F̄` | over an arbitrary field |
|---|---|---|---|
| `F(W⁄F)` | `weilPairingElt_galois_of_gS_*` | `exists_weilPairingElt_galois_*` | here |
| `μ_n(F)` | `weilPairingMu_galois_of_gS_*` | `exists_weilPairingMu_galois_*` | here |

with `*` ranging over `two` and `three` in every cell.

⚠️ **The two `μ_n(F)` theorems go through the lifted `F(W⁄F)` ones, not through
`weilPairingMu_galois_of_gS_*`.**  That is the route `WeilPairingGaloisRoot` takes and the reason it
gives transfers verbatim: the `_of_gS_` form would re-supply the rung-5 data that the envelope has
already consumed and quantified away, whereas
`weilPairingMu_galois_of_weilPairingElt` (`EllipticCurves.FunctionField.WeilPairingGaloisMu`)
consumes the envelope's public payload and nothing else.  The two `hpow` producers
(`weilPairingElt_pow_eq_one_of_gS_two_torsion`, `weilPairingElt_pow_eq_one_of_gS_three_baseField`)
are already field-agnostic and are used unchanged.

⚠️ **The `μ_n(F)` headlines carry one hypothesis the `F(W⁄F)` ones do not**: the translation point
`T` is asked to be `n`-torsion.  That is inherited from the twins and is not a residue of anything
lifted here — it is what makes the pairing *value* a root of unity, so that `weilPairingMu` can be
formed at all.

## Naming and placement

The names are the twins' with `_of_hprin` appended, so `exists_weilPairingElt_galois_two_of_hprin`.
The review of `#910` settled the rule: **"mirror your twin" wins while every `_of_hprin` file has a
twin**, the qualifier's position varying by design, because the only reader who cares is the one
holding the two statements side by side.

⚠️ **Placement mirrors the twin as well, and both are now `WeierstrassCurve.Affine`.**  When this
module landed (`#923`) it stated its four headlines in `WeierstrassCurve.Affine.CoordinateRing`,
because `WeilPairingGaloisRoot` stated its four there and `#918`'s tree-wide check — that a
declaration and its twin share a namespace — was reporting zero; stating these four in `Affine`
alone would have taken it from 0 to 4.  That was the right call for a feature PR and the wrong
resting place for the tree: it kept the mechanical invariant green by letting `#903`'s house
pattern (lemma layer in `CoordinateRing`, `exists_` headlines one level up) drift further.

`#927` resolved it the way `#918` did, by moving **all eight** headlines up together, so that both
invariants hold at once and the check reads 0 before and 0 after.  ⚠️ **Move them together or not
at all** is the whole content of that decision: moving one file's four is exactly the straddle the
check exists to catch.  Nothing about the eight changed but the prefix — no statement, no proof, no
binder, verified by `#check @f` and fully-qualified `#print axioms` on all eight at both spellings,
before and after.

## Non-vacuity

Certified below over **`ℚ` itself**, with `σ = AlgEquiv.refl`, on the curves `WeilPairingGaloisRoot`
uses — `y² = x³ − x` with `S = (0, 0)` and `T = (1, 0)` at `n = 2`, `y² + y = x³` with `(0, 0)` at
`n = 3`.  ⚠️ **The base field is `ℚ` and not `AlgebraicClosure ℚ` on purpose**: a certificate over
an algebraically closed field would demonstrate nothing about the claim this file makes.  Every
hypothesis but `hprin` is discharged concretely, which is `#912`'s discriminator for when such a
block is worth writing.

⚠️ **Each certificate restates its headline's conclusion in full.**  `#916` had to repair four
blocks that `obtain`ed the headline and dropped the rung-5 conjuncts, leaving statements provable
with a trivial term.  The test before shipping one is: *can I prove this with `⟨1, 1, …, by simp⟩`?*

⚠️ As in `WeilPairingGaloisRoot`, the `n = 3` `μ` certificate is necessarily taken at `S = T`: the
only nameable `3`-torsion points on `y² + y = x³` are `(0, 0)` and `(0, −1)`, the `X = −1` fibre of
`Ψ₃ = 3X(X³ + 1)` being the primitive cube roots of unity.  At `n = 2` there is no such limitation
and the certificate is at two distinct points.

## Scope

Nothing existing is renamed or reproved: this module is purely additive.  Out of scope: discharging
`hprin`; any change to `WeilPairingGaloisRoot`'s statements or to the
`weilPairingElt_galois_of_gS_*` engine, which needs nothing; general `n`; `#E[n] = n²`; Ward.
⚠️ Moving `WeilPairingGaloisRoot`'s headlines up a namespace was out of scope *of `#923`* and was
done afterwards by `#927`, which moved these four with them; see the placement note above.

⚠️ **Non-degeneracy is not in scope and is not a lift of this kind.**
`EllipticCurves.FunctionField.WeilPairingNondegenerateTwo` states a *second*, independent
`[IsAlgClosed F]` dependence, through `card_torsion_two` in `#759`.  Unlike `hprin` that one is not
a gap in the formalisation: non-degeneracy against `E(F)[n]` over a non-closed `F` is false, so
there is nothing there to lift.

## References

* [J. H. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.8.
-/

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum

namespace WeierstrassCurve.Affine

open CoordinateRing

variable {S F : Type*} [Field S] [Field F] [Algebra S F] {W : Affine S} [W.IsElliptic]

variable {x₂ y₂ x y : F}

/-! ### Over an arbitrary field, at the level of `F(W⁄F)` -/

open Classical in
/-- **Galois-equivariance of the Weil pairing at `n = 2` over an arbitrary field with
`(2 : F) ≠ 0`**, with `hprin` the only gate:

```
σ⋆(e_2(S, T)) = e_2(σS, σT).
```

`exists_weilPairingElt_galois_two` (`WeilPairingGaloisRoot`, `#456`) is this statement with
`[IsAlgClosed F]` in place of `hprin`; the conclusion is identical and no other hypothesis is added.
The rung-5 data is returned rather than discarded, for the reason the twin records: `weilPairingElt`
takes the root as an argument, so a consumer holding its own root should use
`weilPairingElt_galois_of_gS_two` and feed it in.

⚠️ **`hprin` is quantified over the point, and it has to be.**  The producer is applied at `S` *and*
at `σS`, and `exists_gS_two`'s own `hprin` names `pointClosedPoint` at the point it is used at, so
the single-point form `WeilPairingTranslationSlotHprin` takes could not serve both.  The bound
point is written `(x₀, y₀)` rather than `(x, y)` because this file's `variable` block already binds
`x` and `y` for the torsion point `S`. -/
theorem exists_weilPairingElt_galois_two_of_hprin (σ : F ≃ₐ[S] F) (h2 : (2 : F) ≠ 0)
    (h₂ : (W⁄F).Equation x₂ y₂) (h : (W⁄F).Nonsingular x y)
    (hS : Point.some x y h ∈ (W⁄F).torsion 2)
    (hprin : ∀ {x₀ y₀ : F} (h₀ : (W⁄F).Nonsingular x₀ y₀),
      Point.some x₀ y₀ h₀ ∈ (W⁄F).torsion 2 →
      ∀ f : (W⁄F).FunctionField, f ≠ 0 →
        divisor (W⁄F) f = Finsupp.single (pointClosedPoint h₀.left) (2 : ℤ) →
        ∃ g₀ : (W⁄F).FunctionField, g₀ ≠ 0 ∧
          2 • divisor (W⁄F) g₀ = divisor (W⁄F) (mulByTwoEndo h2 f)) :
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
  obtain ⟨f, hf, hfdiv, g, hg, u, hu⟩ := exists_gS_two h2 h hS (hprin h hS)
  obtain ⟨f', hf', hf'div, g', hg', u', hu'⟩ :=
    exists_gS_two h2 (nonsingular_algEquiv σ h)
      (Point.mem_torsion_galois_smul_some σ h hS)
      (hprin (nonsingular_algEquiv σ h) (Point.mem_torsion_galois_smul_some σ h hS))
  exact ⟨g, g', hg, hg', ⟨f, hf, hfdiv, u, hu⟩, ⟨f', hf', hf'div, u', hu'⟩,
    weilPairingElt_galois_of_gS_two σ h2 h₂ h.left hg hg' hfdiv hf'div hu hu'⟩

open Classical in
/-- **Galois-equivariance of the Weil pairing at `n = 3` over an arbitrary field with
`(2 : F) ≠ 0` and `(3 : F) ≠ 0`**, with `hprin` the only gate: the `n = 3` mirror of
`exists_weilPairingElt_galois_two_of_hprin`, and `exists_weilPairingElt_galois_three` with `hprin`
in place of `[IsAlgClosed F]`.

Only the producer differs — `exists_gS_three` for `exists_gS_two`, with the extra `h3` — and the
engine `weilPairingElt_galois_of_gS_three` was already stated over an arbitrary field. -/
theorem exists_weilPairingElt_galois_three_of_hprin (σ : F ≃ₐ[S] F) (h2 : (2 : F) ≠ 0)
    (h3 : (3 : F) ≠ 0) (h₂ : (W⁄F).Equation x₂ y₂) (h : (W⁄F).Nonsingular x y)
    (hS : Point.some x y h ∈ (W⁄F).torsion 3)
    (hprin : ∀ {x₀ y₀ : F} (h₀ : (W⁄F).Nonsingular x₀ y₀),
      Point.some x₀ y₀ h₀ ∈ (W⁄F).torsion 3 →
      ∀ f : (W⁄F).FunctionField, f ≠ 0 →
        divisor (W⁄F) f = Finsupp.single (pointClosedPoint h₀.left) (3 : ℤ) →
        ∃ g₀ : (W⁄F).FunctionField, g₀ ≠ 0 ∧
          3 • divisor (W⁄F) g₀ = divisor (W⁄F) (mulByThreeEndo h2 h3 f)) :
    ∃ g g' : (W⁄F).FunctionField, g ≠ 0 ∧ g' ≠ 0 ∧
      (∃ f : (W⁄F).FunctionField, f ≠ 0 ∧
        divisor (W⁄F) f = Finsupp.single (pointClosedPoint h.left) (3 : ℤ) ∧
        ∃ u : (W⁄F).CoordinateRingˣ,
          (u : (W⁄F).CoordinateRing) • g ^ 3 = mulByThreeEndo h2 h3 f) ∧
      (∃ f' : (W⁄F).FunctionField, f' ≠ 0 ∧
        divisor (W⁄F) f'
          = Finsupp.single (pointClosedPoint (equation_algEquiv σ h.left)) (3 : ℤ) ∧
        ∃ u' : (W⁄F).CoordinateRingˣ,
          (u' : (W⁄F).CoordinateRing) • g' ^ 3 = mulByThreeEndo h2 h3 f') ∧
      galoisFunctionField σ (weilPairingElt h₂ g)
        = weilPairingElt (equation_algEquiv σ h₂) g' := by
  obtain ⟨f, hf, hfdiv, g, hg, u, hu⟩ := exists_gS_three h2 h3 h hS (hprin h hS)
  obtain ⟨f', hf', hf'div, g', hg', u', hu'⟩ :=
    exists_gS_three h2 h3 (nonsingular_algEquiv σ h)
      (Point.mem_torsion_galois_smul_some σ h hS)
      (hprin (nonsingular_algEquiv σ h) (Point.mem_torsion_galois_smul_some σ h hS))
  exact ⟨g, g', hg, hg', ⟨f, hf, hfdiv, u, hu⟩, ⟨f', hf', hf'div, u', hu'⟩,
    weilPairingElt_galois_of_gS_three σ h2 h3 h₂ h.left hg hg' hfdiv hf'div hu hu'⟩

/-! ### Over an arbitrary field, at the level of `μ_n(F)` -/

open Classical in
/-- **Galois-equivariance of the Weil pairing in `μ_2(F)` over an arbitrary field with
`(2 : F) ≠ 0`**, with `hprin` the only gate:

```
σ · μ_2(S, T) = μ_2(σS, σT)     in `rootsOfUnity 2 F`.
```

`exists_weilPairingMu_galois_two` (`WeilPairingGaloisRoot`) with `hprin` in place of
`[IsAlgClosed F]`.  The envelope is `exists_weilPairingElt_galois_two_of_hprin`'s, extended by the
two `hpow` data, which are bound existentially because `weilPairingMu` is indexed by the *proof*
that the pairing value is a square root of unity — produced here rather than assumed.

⚠️ **The route is to descend the conclusion, not to apply `weilPairingMu_galois_of_gS_two`.**  That
theorem would do the job only by re-supplying rung-5 data the envelope has already quantified away;
`weilPairingMu_galois_of_weilPairingElt` consumes the envelope's public payload instead.  This is
the twin's route and the lift changes nothing about it.

⚠️ **The exponent `2` is forced by the data, not adopted by convention**: the `hpow` producer
`weilPairingElt_pow_eq_one_of_gS_two_torsion` takes its exponent from the rung-5 relation it
consumes, and `exists_gS_two` produces `u • g ^ 2 = [2]∗ f`. -/
theorem exists_weilPairingMu_galois_two_of_hprin (σ : F ≃ₐ[S] F) (h2 : (2 : F) ≠ 0)
    (h₂ : (W⁄F).Nonsingular x₂ y₂) (hm₂ : Point.some x₂ y₂ h₂ ∈ (W⁄F).torsion 2)
    (h : (W⁄F).Nonsingular x y) (hS : Point.some x y h ∈ (W⁄F).torsion 2)
    (hprin : ∀ {x₀ y₀ : F} (h₀ : (W⁄F).Nonsingular x₀ y₀),
      Point.some x₀ y₀ h₀ ∈ (W⁄F).torsion 2 →
      ∀ f : (W⁄F).FunctionField, f ≠ 0 →
        divisor (W⁄F) f = Finsupp.single (pointClosedPoint h₀.left) (2 : ℤ) →
        ∃ g₀ : (W⁄F).FunctionField, g₀ ≠ 0 ∧
          2 • divisor (W⁄F) g₀ = divisor (W⁄F) (mulByTwoEndo h2 f)) :
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
      ∃ hpow : weilPairingElt h₂.left g ^ 2 = 1,
        ∃ hpow' : weilPairingElt (equation_algEquiv σ h₂.left) g' ^ 2 = 1,
          restrictRootsOfUnity (σ.toRingEquiv.toRingHom) 2 (weilPairingMu h₂.left hpow)
            = weilPairingMu (equation_algEquiv σ h₂.left) hpow' := by
  obtain ⟨g, g', hg, hg', ⟨f, hf, hfdiv, u, hu⟩, ⟨f', hf', hf'div, u', hu'⟩, hgal⟩ :=
    exists_weilPairingElt_galois_two_of_hprin σ h2 h₂.left h hS hprin
  have hpow : weilPairingElt h₂.left g ^ 2 = 1 :=
    weilPairingElt_pow_eq_one_of_gS_two_torsion h₂.left h2
      (add_self_eq_zero_of_mem_torsion_two hm₂) hg hu
  have hpow' : weilPairingElt (equation_algEquiv σ h₂.left) g' ^ 2 = 1 :=
    weilPairingElt_pow_eq_one_of_gS_two_torsion (equation_algEquiv σ h₂.left) h2
      (add_self_eq_zero_of_mem_torsion_two
        (Point.mem_torsion_galois_smul_some σ h₂ hm₂)) hg' hu'
  exact ⟨g, g', hg, hg', ⟨f, hf, hfdiv, u, hu⟩, ⟨f', hf', hf'div, u', hu'⟩, hpow, hpow',
    weilPairingMu_galois_of_weilPairingElt σ h₂.left hgal hpow hpow'⟩

open Classical in
/-- **Galois-equivariance of the Weil pairing in `μ_3(F)` over an arbitrary field with
`(2 : F) ≠ 0` and `(3 : F) ≠ 0`**, with `hprin` the only gate: the `n = 3` mirror of
`exists_weilPairingMu_galois_two_of_hprin`.

Two things differ from the `n = 2` statement and neither is mathematical: the envelope is
`exists_weilPairingElt_galois_three_of_hprin`'s, and the `hpow` producer is
`weilPairingElt_pow_eq_one_of_gS_three_baseField` in place of
`weilPairingElt_pow_eq_one_of_gS_two_torsion`. -/
theorem exists_weilPairingMu_galois_three_of_hprin (σ : F ≃ₐ[S] F) (h2 : (2 : F) ≠ 0)
    (h3 : (3 : F) ≠ 0) (h₂ : (W⁄F).Nonsingular x₂ y₂)
    (hm₂ : Point.some x₂ y₂ h₂ ∈ (W⁄F).torsion 3)
    (h : (W⁄F).Nonsingular x y) (hS : Point.some x y h ∈ (W⁄F).torsion 3)
    (hprin : ∀ {x₀ y₀ : F} (h₀ : (W⁄F).Nonsingular x₀ y₀),
      Point.some x₀ y₀ h₀ ∈ (W⁄F).torsion 3 →
      ∀ f : (W⁄F).FunctionField, f ≠ 0 →
        divisor (W⁄F) f = Finsupp.single (pointClosedPoint h₀.left) (3 : ℤ) →
        ∃ g₀ : (W⁄F).FunctionField, g₀ ≠ 0 ∧
          3 • divisor (W⁄F) g₀ = divisor (W⁄F) (mulByThreeEndo h2 h3 f)) :
    ∃ g g' : (W⁄F).FunctionField, g ≠ 0 ∧ g' ≠ 0 ∧
      (∃ f : (W⁄F).FunctionField, f ≠ 0 ∧
        divisor (W⁄F) f = Finsupp.single (pointClosedPoint h.left) (3 : ℤ) ∧
        ∃ u : (W⁄F).CoordinateRingˣ,
          (u : (W⁄F).CoordinateRing) • g ^ 3 = mulByThreeEndo h2 h3 f) ∧
      (∃ f' : (W⁄F).FunctionField, f' ≠ 0 ∧
        divisor (W⁄F) f'
          = Finsupp.single (pointClosedPoint (equation_algEquiv σ h.left)) (3 : ℤ) ∧
        ∃ u' : (W⁄F).CoordinateRingˣ,
          (u' : (W⁄F).CoordinateRing) • g' ^ 3 = mulByThreeEndo h2 h3 f') ∧
      ∃ hpow : weilPairingElt h₂.left g ^ 3 = 1,
        ∃ hpow' : weilPairingElt (equation_algEquiv σ h₂.left) g' ^ 3 = 1,
          restrictRootsOfUnity (σ.toRingEquiv.toRingHom) 3 (weilPairingMu h₂.left hpow)
            = weilPairingMu (equation_algEquiv σ h₂.left) hpow' := by
  obtain ⟨g, g', hg, hg', ⟨f, hf, hfdiv, u, hu⟩, ⟨f', hf', hf'div, u', hu'⟩, hgal⟩ :=
    exists_weilPairingElt_galois_three_of_hprin σ h2 h3 h₂.left h hS hprin
  have hpow : weilPairingElt h₂.left g ^ 3 = 1 :=
    weilPairingElt_pow_eq_one_of_gS_three_baseField h₂.left h2 h3
      (add_add_self_eq_zero_of_mem_torsion_three hm₂) hg hu
  have hpow' : weilPairingElt (equation_algEquiv σ h₂.left) g' ^ 3 = 1 :=
    weilPairingElt_pow_eq_one_of_gS_three_baseField (equation_algEquiv σ h₂.left) h2 h3
      (add_add_self_eq_zero_of_mem_torsion_three
        (Point.mem_torsion_galois_smul_some σ h₂ hm₂)) hg' hu'
  exact ⟨g, g', hg, hg', ⟨f, hf, hfdiv, u, hu⟩, ⟨f', hf', hf'div, u', hu'⟩, hpow, hpow',
    weilPairingMu_galois_of_weilPairingElt σ h₂.left hgal hpow hpow'⟩

/-! ### Non-vacuity

The theorems above quantify over a base field `S`, an extension `F` and an `S`-automorphism of `F`.
⚠️ **The certificates below take `S = F = ℚ`, which is *not* algebraically closed** — that is the
whole point, and a block over `AlgebraicClosure ℚ` would certify the twins rather than these
statements.  `hprin` is supplied as a hypothesis, because it is the one thing that is not
dischargeable here; everything else is concrete. -/

section Nonvacuity

/-! The certificate curves `y² = x³ − x` and `y² + y = x³` are the shared
`EllipticCurves.Fixture.y2EqX3SubX` and `EllipticCurves.Fixture.y2AddYEqX3`, whose single
`[CharZero F]` instance also supplies `IsElliptic` here. -/

open EllipticCurves.Fixture

/-- ⚠️ The base field is `ℚ` itself, **not** an algebraic closure of it.  The twins in
`EllipticCurves.FunctionField.WeilPairingGaloisRoot` certify the same shapes over
`AlgebraicClosure ℚ`, which is what `[IsAlgClosed F]` forces on them. -/
private abbrev exampleField : Type := ℚ

private lemma exampleTwo : (2 : exampleField) ≠ 0 := by norm_num

/-- `S = (0, 0)` lies on the base-changed curve and is nonsingular. -/
private lemma exampleNonsingular : ((y2EqX3SubX ℚ)⁄exampleField).Nonsingular 0 0 :=
  ((y2EqX3SubX ℚ)⁄exampleField).equation_iff_nonsingular.mp (by
    simp [y2EqX3SubX, WeierstrassCurve.Affine.equation_iff])

open Classical in
/-- `S = (0, 0)` is `2`-torsion: `2y + a₁x + a₃ = 0` reads `0 = 0`. -/
private lemma exampleTorsion :
    Point.some (0 : exampleField) 0 exampleNonsingular ∈ ((y2EqX3SubX ℚ)⁄exampleField).torsion 2 :=
  (mem_torsion_two_some_iff exampleNonsingular).mpr (by simp [y2EqX3SubX])

open Classical in
/-- **Galois-equivariance at `n = 2` over a base field that is not algebraically closed**, with the
field, the extension and the `2`-torsion point all named and `hprin` the only hypothesis left
standing.

⚠️ The conclusion is the headline's, written out in full rather than `obtain`ed and projected —
`#916` had to repair four blocks that dropped the rung-5 conjuncts and so stated something provable
with a trivial term. -/
example (σ : exampleField ≃ₐ[ℚ] exampleField) {x₂ y₂ : exampleField}
    (h₂ : ((y2EqX3SubX ℚ)⁄exampleField).Equation x₂ y₂)
    (hprin : ∀ {x₀ y₀ : exampleField} (h₀ : ((y2EqX3SubX ℚ)⁄exampleField).Nonsingular x₀ y₀),
      Point.some x₀ y₀ h₀ ∈ ((y2EqX3SubX ℚ)⁄exampleField).torsion 2 →
      ∀ f : ((y2EqX3SubX ℚ)⁄exampleField).FunctionField, f ≠ 0 →
        divisor ((y2EqX3SubX ℚ)⁄exampleField) f
            = Finsupp.single (pointClosedPoint h₀.left) (2 : ℤ) →
        ∃ g₀ : ((y2EqX3SubX ℚ)⁄exampleField).FunctionField, g₀ ≠ 0 ∧
          2 • divisor ((y2EqX3SubX ℚ)⁄exampleField) g₀
            = divisor ((y2EqX3SubX ℚ)⁄exampleField) (mulByTwoEndo exampleTwo f)) :
    ∃ g g' : ((y2EqX3SubX ℚ)⁄exampleField).FunctionField, g ≠ 0 ∧ g' ≠ 0 ∧
      (∃ f : ((y2EqX3SubX ℚ)⁄exampleField).FunctionField, f ≠ 0 ∧
        divisor ((y2EqX3SubX ℚ)⁄exampleField) f
          = Finsupp.single (pointClosedPoint exampleNonsingular.left) (2 : ℤ) ∧
        ∃ u : ((y2EqX3SubX ℚ)⁄exampleField).CoordinateRingˣ,
          (u : ((y2EqX3SubX ℚ)⁄exampleField).CoordinateRing) • g ^ 2
            = mulByTwoEndo exampleTwo f) ∧
      (∃ f' : ((y2EqX3SubX ℚ)⁄exampleField).FunctionField, f' ≠ 0 ∧
        divisor ((y2EqX3SubX ℚ)⁄exampleField) f'
          = Finsupp.single
              (pointClosedPoint (equation_algEquiv σ exampleNonsingular.left)) (2 : ℤ) ∧
        ∃ u' : ((y2EqX3SubX ℚ)⁄exampleField).CoordinateRingˣ,
          (u' : ((y2EqX3SubX ℚ)⁄exampleField).CoordinateRing) • g' ^ 2
            = mulByTwoEndo exampleTwo f') ∧
      galoisFunctionField σ (weilPairingElt h₂ g)
        = weilPairingElt (equation_algEquiv σ h₂) g' :=
  exists_weilPairingElt_galois_two_of_hprin σ exampleTwo h₂ exampleNonsingular
    (by convert exampleTorsion) (fun h₀ hm₀ => hprin h₀ (by convert hm₀))

private lemma exampleThree : (3 : exampleField) ≠ 0 := by norm_num

/-- `S = (0, 0)` lies on the base-changed curve `y² + y = x³` and is nonsingular. -/
private lemma exampleNonsingularThree : ((y2AddYEqX3 ℚ)⁄exampleField).Nonsingular 0 0 :=
  ((y2AddYEqX3 ℚ)⁄exampleField).equation_iff_nonsingular.mp (by
    simp [y2AddYEqX3, WeierstrassCurve.Affine.equation_iff])

open Classical in
/-- `S = (0, 0)` is `3`-torsion: `Ψ₃ = 3X⁴ + 3b₆X` vanishes at `0`. -/
private lemma exampleTorsionThree :
    Point.some (0 : exampleField) 0 exampleNonsingularThree
      ∈ ((y2AddYEqX3 ℚ)⁄exampleField).torsion 3 :=
  mem_torsion_three_some_iff'.mpr (by
    simp [y2AddYEqX3, WeierstrassCurve.Ψ₃, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
      WeierstrassCurve.b₆, WeierstrassCurve.b₈])

open Classical in
/-- **Galois-equivariance at `n = 3` over a base field that is not algebraically closed**, with the
field, the extension and the `3`-torsion point all named and `hprin` the only hypothesis left
standing. -/
example (σ : exampleField ≃ₐ[ℚ] exampleField) {x₂ y₂ : exampleField}
    (h₂ : ((y2AddYEqX3 ℚ)⁄exampleField).Equation x₂ y₂)
    (hprin : ∀ {x₀ y₀ : exampleField} (h₀ : ((y2AddYEqX3 ℚ)⁄exampleField).Nonsingular x₀ y₀),
      Point.some x₀ y₀ h₀ ∈ ((y2AddYEqX3 ℚ)⁄exampleField).torsion 3 →
      ∀ f : ((y2AddYEqX3 ℚ)⁄exampleField).FunctionField, f ≠ 0 →
        divisor ((y2AddYEqX3 ℚ)⁄exampleField) f
            = Finsupp.single (pointClosedPoint h₀.left) (3 : ℤ) →
        ∃ g₀ : ((y2AddYEqX3 ℚ)⁄exampleField).FunctionField, g₀ ≠ 0 ∧
          3 • divisor ((y2AddYEqX3 ℚ)⁄exampleField) g₀
            = divisor ((y2AddYEqX3 ℚ)⁄exampleField)
                (mulByThreeEndo exampleTwo exampleThree f)) :
    ∃ g g' : ((y2AddYEqX3 ℚ)⁄exampleField).FunctionField, g ≠ 0 ∧ g' ≠ 0 ∧
      (∃ f : ((y2AddYEqX3 ℚ)⁄exampleField).FunctionField, f ≠ 0 ∧
        divisor ((y2AddYEqX3 ℚ)⁄exampleField) f
          = Finsupp.single (pointClosedPoint exampleNonsingularThree.left) (3 : ℤ) ∧
        ∃ u : ((y2AddYEqX3 ℚ)⁄exampleField).CoordinateRingˣ,
          (u : ((y2AddYEqX3 ℚ)⁄exampleField).CoordinateRing) • g ^ 3
            = mulByThreeEndo exampleTwo exampleThree f) ∧
      (∃ f' : ((y2AddYEqX3 ℚ)⁄exampleField).FunctionField, f' ≠ 0 ∧
        divisor ((y2AddYEqX3 ℚ)⁄exampleField) f'
          = Finsupp.single
              (pointClosedPoint (equation_algEquiv σ exampleNonsingularThree.left)) (3 : ℤ) ∧
        ∃ u' : ((y2AddYEqX3 ℚ)⁄exampleField).CoordinateRingˣ,
          (u' : ((y2AddYEqX3 ℚ)⁄exampleField).CoordinateRing) • g' ^ 3
            = mulByThreeEndo exampleTwo exampleThree f') ∧
      galoisFunctionField σ (weilPairingElt h₂ g)
        = weilPairingElt (equation_algEquiv σ h₂) g' :=
  exists_weilPairingElt_galois_three_of_hprin σ exampleTwo exampleThree h₂
    exampleNonsingularThree (by convert exampleTorsionThree)
    (fun h₀ hm₀ => hprin h₀ (by convert hm₀))

/-- `T = (1, 0)` lies on `y² = x³ − x` and is nonsingular.  ⚠️ A **second** point on the same curve
is needed here and not by the `F(W⁄F)`-level certificates above: those leave the translation point
`T` free, whereas `exists_weilPairingMu_galois_two_of_hprin` asks for it to be `2`-torsion.  Taking
`T = (1, 0)` against `S = (0, 0)` keeps the certificate a genuine two-point instance. -/
private lemma exampleNonsingularTranslate : ((y2EqX3SubX ℚ)⁄exampleField).Nonsingular 1 0 :=
  ((y2EqX3SubX ℚ)⁄exampleField).equation_iff_nonsingular.mp (by
    simp [y2EqX3SubX, WeierstrassCurve.Affine.equation_iff])

open Classical in
/-- `T = (1, 0)` is `2`-torsion: `2y + a₁x + a₃ = 0` reads `0 = 0`, as at `(0, 0)`. -/
private lemma exampleTorsionTranslate :
    Point.some (1 : exampleField) 0 exampleNonsingularTranslate
      ∈ ((y2EqX3SubX ℚ)⁄exampleField).torsion 2 :=
  (mem_torsion_two_some_iff exampleNonsingularTranslate).mpr (by simp [y2EqX3SubX])

open Classical in
/-- **Galois-equivariance in `μ_2(ℚ)` over a base field that is not algebraically closed**, with
**both** `2`-torsion points named — `S = (0, 0)` and `T = (1, 0)`, which are distinct, so the
certificate is not a disguised instance at `S = T`. -/
example (σ : exampleField ≃ₐ[ℚ] exampleField)
    (hprin : ∀ {x₀ y₀ : exampleField} (h₀ : ((y2EqX3SubX ℚ)⁄exampleField).Nonsingular x₀ y₀),
      Point.some x₀ y₀ h₀ ∈ ((y2EqX3SubX ℚ)⁄exampleField).torsion 2 →
      ∀ f : ((y2EqX3SubX ℚ)⁄exampleField).FunctionField, f ≠ 0 →
        divisor ((y2EqX3SubX ℚ)⁄exampleField) f
            = Finsupp.single (pointClosedPoint h₀.left) (2 : ℤ) →
        ∃ g₀ : ((y2EqX3SubX ℚ)⁄exampleField).FunctionField, g₀ ≠ 0 ∧
          2 • divisor ((y2EqX3SubX ℚ)⁄exampleField) g₀
            = divisor ((y2EqX3SubX ℚ)⁄exampleField) (mulByTwoEndo exampleTwo f)) :
    ∃ g g' : ((y2EqX3SubX ℚ)⁄exampleField).FunctionField, g ≠ 0 ∧ g' ≠ 0 ∧
      (∃ f : ((y2EqX3SubX ℚ)⁄exampleField).FunctionField, f ≠ 0 ∧
        divisor ((y2EqX3SubX ℚ)⁄exampleField) f
          = Finsupp.single (pointClosedPoint exampleNonsingular.left) (2 : ℤ) ∧
        ∃ u : ((y2EqX3SubX ℚ)⁄exampleField).CoordinateRingˣ,
          (u : ((y2EqX3SubX ℚ)⁄exampleField).CoordinateRing) • g ^ 2
            = mulByTwoEndo exampleTwo f) ∧
      (∃ f' : ((y2EqX3SubX ℚ)⁄exampleField).FunctionField, f' ≠ 0 ∧
        divisor ((y2EqX3SubX ℚ)⁄exampleField) f'
          = Finsupp.single
              (pointClosedPoint (equation_algEquiv σ exampleNonsingular.left)) (2 : ℤ) ∧
        ∃ u' : ((y2EqX3SubX ℚ)⁄exampleField).CoordinateRingˣ,
          (u' : ((y2EqX3SubX ℚ)⁄exampleField).CoordinateRing) • g' ^ 2
            = mulByTwoEndo exampleTwo f') ∧
      ∃ hpow : weilPairingElt exampleNonsingularTranslate.left g ^ 2 = 1,
        ∃ hpow' : weilPairingElt (equation_algEquiv σ exampleNonsingularTranslate.left) g' ^ 2 = 1,
          restrictRootsOfUnity (σ.toRingEquiv.toRingHom) 2
              (weilPairingMu exampleNonsingularTranslate.left hpow)
            = weilPairingMu (equation_algEquiv σ exampleNonsingularTranslate.left) hpow' :=
  exists_weilPairingMu_galois_two_of_hprin σ exampleTwo exampleNonsingularTranslate
    (by convert exampleTorsionTranslate) exampleNonsingular (by convert exampleTorsion)
    (fun h₀ hm₀ => hprin h₀ (by convert hm₀))

open Classical in
/-- **Galois-equivariance in `μ_3(ℚ)` over a base field that is not algebraically closed.**

⚠️ **This certificate is taken at `S = T = (0, 0)`, and that is a genuine limitation rather than a
convenience.**  The only nameable `3`-torsion points on `y² + y = x³` are `(0, 0)` and its negative
`(0, −1)`: the `X = −1` fibre of `Ψ₃ = 3X(X³ + 1)` is `y² + y + 1 = 0`, the primitive cube roots of
unity, which cannot be named without a genuine algebraic-number argument.  The limitation is
inherited from the twin and from `#829`/`#845`/`#855`, and it is not addressed here.  ⚠️ At `n = 2`
there is no such limitation: the certificate above is at two distinct points. -/
example (σ : exampleField ≃ₐ[ℚ] exampleField)
    (hprin : ∀ {x₀ y₀ : exampleField} (h₀ : ((y2AddYEqX3 ℚ)⁄exampleField).Nonsingular x₀ y₀),
      Point.some x₀ y₀ h₀ ∈ ((y2AddYEqX3 ℚ)⁄exampleField).torsion 3 →
      ∀ f : ((y2AddYEqX3 ℚ)⁄exampleField).FunctionField, f ≠ 0 →
        divisor ((y2AddYEqX3 ℚ)⁄exampleField) f
            = Finsupp.single (pointClosedPoint h₀.left) (3 : ℤ) →
        ∃ g₀ : ((y2AddYEqX3 ℚ)⁄exampleField).FunctionField, g₀ ≠ 0 ∧
          3 • divisor ((y2AddYEqX3 ℚ)⁄exampleField) g₀
            = divisor ((y2AddYEqX3 ℚ)⁄exampleField)
                (mulByThreeEndo exampleTwo exampleThree f)) :
    ∃ g g' : ((y2AddYEqX3 ℚ)⁄exampleField).FunctionField, g ≠ 0 ∧ g' ≠ 0 ∧
      (∃ f : ((y2AddYEqX3 ℚ)⁄exampleField).FunctionField, f ≠ 0 ∧
        divisor ((y2AddYEqX3 ℚ)⁄exampleField) f
          = Finsupp.single (pointClosedPoint exampleNonsingularThree.left) (3 : ℤ) ∧
        ∃ u : ((y2AddYEqX3 ℚ)⁄exampleField).CoordinateRingˣ,
          (u : ((y2AddYEqX3 ℚ)⁄exampleField).CoordinateRing) • g ^ 3
            = mulByThreeEndo exampleTwo exampleThree f) ∧
      (∃ f' : ((y2AddYEqX3 ℚ)⁄exampleField).FunctionField, f' ≠ 0 ∧
        divisor ((y2AddYEqX3 ℚ)⁄exampleField) f'
          = Finsupp.single
              (pointClosedPoint (equation_algEquiv σ exampleNonsingularThree.left)) (3 : ℤ) ∧
        ∃ u' : ((y2AddYEqX3 ℚ)⁄exampleField).CoordinateRingˣ,
          (u' : ((y2AddYEqX3 ℚ)⁄exampleField).CoordinateRing) • g' ^ 3
            = mulByThreeEndo exampleTwo exampleThree f') ∧
      ∃ hpow : weilPairingElt exampleNonsingularThree.left g ^ 3 = 1,
        ∃ hpow' : weilPairingElt (equation_algEquiv σ exampleNonsingularThree.left) g' ^ 3 = 1,
          restrictRootsOfUnity (σ.toRingEquiv.toRingHom) 3
              (weilPairingMu exampleNonsingularThree.left hpow)
            = weilPairingMu (equation_algEquiv σ exampleNonsingularThree.left) hpow' :=
  exists_weilPairingMu_galois_three_of_hprin σ exampleTwo exampleThree exampleNonsingularThree
    (by convert exampleTorsionThree) exampleNonsingularThree (by convert exampleTorsionThree)
    (fun h₀ hm₀ => hprin h₀ (by convert hm₀))

end Nonvacuity

end WeierstrassCurve.Affine
