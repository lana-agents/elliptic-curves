/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import EllipticCurves.FunctionField.WeilPairingTranslationSlotBilinear
import EllipticCurves.FunctionField.WeilPairingTranslationSlotHom

/-!
# The translation slot over an ARBITRARY field, with `hprin` the only gate (rung 6)

Two rung-6 fronts are confined to `F̄` by the same single input, and this file lifts both off it:

* **translation-slot bilinearity**, `e_n(R, g) = e_n(P, g) · e_n(Q, g)` for `P ⊕ Q = R`
  (`EllipticCurves.FunctionField.WeilPairingTranslationSlotBilinear`, `#861`), at the `F(W)` level
  and in `μ_n(F)`;
* the **bundled homomorphism** `e_n(S, ·) : E[n] → μ_n(F)`
  (`EllipticCurves.FunctionField.WeilPairingTranslationSlotHom`, `#873`).

All six headlines lose `[IsAlgClosed F]` and gain the single hypothesis `hprin` — the principality
of `[n]∗(S)` at the divisor point — and nothing else.

## Why it is a substitution and not an argument

⚠️ Both source files name their own gate, in one sentence each, and those sentences are the whole
plan of this file:

> `[IsAlgClosed F]` enters through `exists_gS_two_of_isAlgClosed` (`#791`) alone.
> — `WeilPairingTranslationSlotBilinear:154`

> The root at `S` and its rung-5 certificate are produced by `exists_gS_two_of_isAlgClosed`
> (`#791`), which is the only place `[IsAlgClosed F]` enters.
> — `WeilPairingTranslationSlotHom:504`

`exists_gS_two_of_isAlgClosed` (`PullbackPrincipalityTwo`) is itself `exists_gS_two`
(`NthRootOfPullback`) with `hprin` discharged, and `exists_gS_two` carries **no** `[IsAlgClosed F]`
and **no** `[W.IsElliptic]`.  So the general-field replacement of the one gated input has been in
the tree since `#765`, and putting it in is the entire content here.  Each proof below is its twin's
**verbatim**, with one call swapped:

```lean
obtain ⟨f, hf, hd, g, hg, u, hu⟩ := exists_gS_two_of_isAlgClosed h2 hS hmS   -- twin
obtain ⟨f, hf, hd, g, hg, u, hu⟩ := exists_gS_two h2 hS hmS hprin            -- here
```

⚠️ **Nothing about curves is proved in this file.**  A reader should check it by putting each
declaration beside its twin; the normalised diff — delete the `hprin` binder, delete `_of_hprin`,
rewrite `exists_gS_{two,three}` back to `…_of_isAlgClosed`, drop the threaded argument — is the
intended review, and it is byte-identical on all six.  The elaborator checks the one thing that
diff strips, namely that the threading typechecks.

## ⚠️ `hprin` is POINT-LOCAL here, and deliberately not `#907`'s quantified shape

`EllipticCurves.FunctionField.WeilPairingProductRelationHprin` (`#907`) quantifies its `hprin` over
all `n`-torsion points, because antisymmetry produces roots at **three** points `S`, `T`, `R`.
Every headline below produces a root at **one** point, the divisor point `S`: `P`, `Q` and `R` are
*translation* points and never index a root.  So `hprin` here is `exists_gS_two`'s own hypothesis
taken verbatim, with no quantifier.

⚠️ That is a decision, not an oversight, and copying `#907`'s shape "for consistency" would be
wrong: a quantified hypothesis is strictly stronger and would buy nothing.  `#907`'s own reason for
quantifying — *"no consumer holds `hprin` at three points without holding it at all of them"* — is a
statement about consumers that produce three roots, and does not apply to one that produces one.
**The test is: how many points does the file produce roots at?**  One ⇒ point-local; more ⇒
quantified.  Both shapes now exist on this front, and that is correct rather than an inconsistency.

## ⚠️ What is *not* achieved: `hprin` is not discharged, and cannot be by any of this

`#899` recorded the test that decides which `[IsAlgClosed F]` uses can be removed this way:

> Is the obstruction used to prove an **equality**, or to produce a **witness**?

`hprin` produces a witness, so it does not descend and will not.  Over `F̄` it is discharged by
`exists_nsmul_divisor_eq_divisor_mulByTwoEndo` (`PullbackPrincipalityTwo`) and
`exists_nsmul_divisor_eq_divisor_mulByThreeEndo` (`PullbackPrincipalityThree`); over a general field
it is open, and it is now the **only** thing between this tree and the translation slot over an
arbitrary field — exactly as on the alternating (`#899`) and antisymmetry (`#907`, `#910`) fronts.

## Main statements

At `n = 2` and at `n = 3`:

* `WeierstrassCurve.Affine.exists_weilPairingElt_translatePoint_add_{two,three}_of_hprin` —
  `e_n(R, g) = e_n(P, g) · e_n(Q, g)` for `P ⊕ Q = R`, in `F(W)`;
* `WeierstrassCurve.Affine.exists_weilPairingMu_translatePoint_add_{two,three}_of_hprin` — the same
  in `rootsOfUnity n F`, with the three `hpow` data **produced** rather than assumed;
* `WeierstrassCurve.Affine.exists_weilPairingTorsionMuHom_{two,three}_of_hprin` —
  `e_n(S, ·) : E[n] → μ_n(F)` is a group homomorphism.

On naming: `_two`/`_three` **before** the qualifier, as in the twins, and not `#907`'s
`_of_hprin_{two,three}`.  `#910`'s review settled the split — *"mirror your twin wins while every
`_of_hprin` file has a twin"*, because the only reader who cares where the suffix sits is the one
holding the two statements side by side.  Every declaration here has a merged twin, so the rule
applies and there is no free choice to make.  As in the twins, `_two`/`_three` track the **isogeny**
— `mulByTwoEndo` versus `mulByThreeEndo` — per the `## Naming` section of
`EllipticCurves.FunctionField.WeilPairing`, not the exponent.

On placement: everything is stated in `WeierstrassCurve.Affine`, where the twins live, with
`open CoordinateRing` rather than a nested `namespace`.  ⚠️ `#903`: the build resolves either
spelling from inside a file that opens `CoordinateRing`, so only `#print axioms` on the **fully
qualified** name — and negatively on the `…CoordinateRing.…` one — checks this.

## Scope

`[Field F] {W : Affine F} [W.IsElliptic]` throughout, with **no** `[IsAlgClosed F]` on any headline;
the `AlgClosedRecovery` section adds it back locally and nowhere else.  Every headline needs
`open Classical in`, because `exists_gS_{two,three}` carries `[DecidableEq F]`.

Out of scope: discharging `hprin`; the **divisor**-slot family
(`WeilPairingDivisorSlotBilinear`), which produces roots at three points and so wants `#907`'s
quantified shape; general `n` (`#404`'s `ωₙ`); rung 4; non-degeneracy, where `[IsAlgClosed F]` is
genuinely load-bearing and enters twice (`WeilPairingNondegenerateTwo:81`).  Nothing here edits
`#861`'s or `#873`'s statements or proofs, and the `_of_isAlgClosed` forms are **not** deprecated:
their consumers carry `[IsAlgClosed F]` already and would gain nothing, the judgement `#903`, `#907`
and `#910` all reached.

⚠️ **The two slots are still not combined into a single bilinearity statement.**  That wants a
pairing on `W.Point × W.Point`; there is none in this tree, and `#861` records it as separate work
with its own design question.

## Non-vacuity

Two blocks, and they answer different questions:

* `AlgClosedRecovery` exhibits the discharge of `hprin` over `F̄` and recovers all six merged
  headlines **on the nose**.  ⚠️ This block is what distinguishes a weakened hypothesis from a
  vacuous one: from the outside a hypothesis no existing theorem can discharge looks exactly like
  `hprin`.
* `Nonvacuity` instantiates the `n = 2` headlines over **`ℚ`**, which is *not* algebraically closed,
  so neither the merged headlines nor the recovery block applies to it.  On `y² = x³ − x` the three
  rational `2`-torsion points `(0, 0)`, `(1, 0)`, `(−1, 0)` are pairwise distinct and satisfy
  `(0, 0) ⊕ (1, 0) = (−1, 0)`, so `P`, `Q`, `R` are all named and distinct; the divisor point `S` is
  a free variable of the statement and is taken to be `P`.  `hprin` is the only hypothesis left.

⚠️ No `n = 3` block over `ℚ`, and the reason is a property of the curves rather than of the
statements: on `y² + y = x³` only `(0, 0)` and its negative `(0, −1)` are nameable —
`Ψ₃ = 3X(X³ + 1)`, and the `X = −1` fibre is `y² + y + 1 = 0`, whose roots are primitive cube roots
of unity — so `P = Q = S` is forced, and the certificate would exhibit strictly less than the
`n = 2` one while reading as more.  `#861` records the same limitation for its own `F̄`
certificate; it is stated, not repaired.

## References

* [J. Silverman, *The arithmetic of elliptic curves*][silverman2009], III.8.1(a).
-/

namespace WeierstrassCurve.Affine

open CoordinateRing IsDedekindDomain IsDedekindDomain.HeightOneSpectrum

variable {F : Type*} [Field F] {W : Affine F} [W.IsElliptic]

section Two

open Classical in
/-- **Translation-slot bilinearity at `n = 2` over an arbitrary field, with `hprin` the only gate.**

```
e_2(R, g) = e_2(P, g) · e_2(Q, g),     for  P ⊕ Q = R.
```

`exists_weilPairingElt_translatePoint_add_two` (`#861`) verbatim, with
`exists_gS_two_of_isAlgClosed` replaced by `exists_gS_two` (`NthRootOfPullback`) and `hprin`
threaded.

⚠️ `hprin` is stated at the **divisor** point `S` only, and is `exists_gS_two`'s own hypothesis: the
three translation points `P`, `Q`, `R` do not index a root.  See the module docstring for why this
is not `#907`'s quantified shape.

⚠️ As in the twin, only `Q`'s `2`-torsion is assumed among the translation points —
`weilPairingElt_translatePoint_add_of_baseField` (`WeilPairingBilinearBaseField`) needs the pairing
value to be a constant at the *middle* point only. -/
theorem exists_weilPairingElt_translatePoint_add_two_of_hprin (h2 : (2 : F) ≠ 0)
    {xP yP xQ yQ xR yR xS yS : F} (hP : W.Nonsingular xP yP) (hQ : W.Nonsingular xQ yQ)
    (hR : W.Nonsingular xR yR) (hS : W.Nonsingular xS yS)
    (hmQ : Point.some xQ yQ hQ ∈ W.torsion 2) (hmS : Point.some xS yS hS ∈ W.torsion 2)
    (hadd : Point.some xP yP hP + Point.some xQ yQ hQ = Point.some xR yR hR)
    (hprin : ∀ f : W.FunctionField, f ≠ 0 →
      divisor W f = Finsupp.single (pointClosedPoint hS.left) (2 : ℤ) →
      ∃ g₀ : W.FunctionField, g₀ ≠ 0 ∧
        2 • divisor W g₀ = divisor W (mulByTwoEndo h2 f)) :
    ∃ g : W.FunctionField, g ≠ 0 ∧
      (∃ f : W.FunctionField, f ≠ 0 ∧
        divisor W f = Finsupp.single (pointClosedPoint hS.left) (2 : ℤ) ∧
        ∃ u : W.CoordinateRingˣ, (u : W.CoordinateRing) • g ^ 2 = mulByTwoEndo h2 f) ∧
      weilPairingElt hR.left g = weilPairingElt hP.left g * weilPairingElt hQ.left g := by
  obtain ⟨f, hf, hd, g, hg, u, hu⟩ := exists_gS_two h2 hS hmS hprin
  have hpowQ : weilPairingElt hQ.left g ^ 2 = 1 :=
    weilPairingElt_pow_eq_one_of_gS_two_torsion hQ.left h2
      (add_self_eq_zero_of_mem_torsion_two hmQ) hg hu
  exact ⟨g, hg, ⟨f, hf, hd, u, hu⟩,
    weilPairingElt_translatePoint_add_of_baseField hP.left hQ.left hR.left hadd hg two_ne_zero
      hpowQ⟩

open Classical in
/-- **Translation-slot bilinearity at `n = 2` in `μ_n(F)` over an arbitrary field, with `hprin` the
only gate.**

```
μ_n(R, g) = μ_n(P, g) · μ_n(Q, g)   in rootsOfUnity n F.
```

`exists_weilPairingMu_translatePoint_add_two` (`#861`) verbatim, with the root producer swapped.
The three `hpow` data are bound existentially because `weilPairingMu` is indexed by the *proof*, and
they are **produced** — not assumed — from the single rung-5 certificate the envelope already
carries, by `weilPairingElt_pow_eq_one_of_gS_two_torsion` (`TranslationTorsion`) at each of `P`,
`Q`, `R`.

⚠️ `hmP` is required here and is not in the `F(W)`-level headline; that is a consequence of
`weilPairingMu` being indexed by `hpow`, not of the mathematics changing.  `hmR` is derived from
`hadd`, not assumed. -/
theorem exists_weilPairingMu_translatePoint_add_two_of_hprin (h2 : (2 : F) ≠ 0)
    {xP yP xQ yQ xR yR xS yS : F} (hP : W.Nonsingular xP yP) (hQ : W.Nonsingular xQ yQ)
    (hR : W.Nonsingular xR yR) (hS : W.Nonsingular xS yS)
    (hmP : Point.some xP yP hP ∈ W.torsion 2) (hmQ : Point.some xQ yQ hQ ∈ W.torsion 2)
    (hmS : Point.some xS yS hS ∈ W.torsion 2)
    (hadd : Point.some xP yP hP + Point.some xQ yQ hQ = Point.some xR yR hR)
    (hprin : ∀ f : W.FunctionField, f ≠ 0 →
      divisor W f = Finsupp.single (pointClosedPoint hS.left) (2 : ℤ) →
      ∃ g₀ : W.FunctionField, g₀ ≠ 0 ∧
        2 • divisor W g₀ = divisor W (mulByTwoEndo h2 f)) :
    ∃ g : W.FunctionField, g ≠ 0 ∧
      (∃ f : W.FunctionField, f ≠ 0 ∧
        divisor W f = Finsupp.single (pointClosedPoint hS.left) (2 : ℤ) ∧
        ∃ u : W.CoordinateRingˣ, (u : W.CoordinateRing) • g ^ 2 = mulByTwoEndo h2 f) ∧
      ∃ hpowP : weilPairingElt hP.left g ^ 2 = 1,
        ∃ hpowQ : weilPairingElt hQ.left g ^ 2 = 1,
          ∃ hpowR : weilPairingElt hR.left g ^ 2 = 1,
            weilPairingMu hR.left hpowR
              = weilPairingMu hP.left hpowP * weilPairingMu hQ.left hpowQ := by
  have hmR : Point.some xR yR hR ∈ W.torsion 2 := hadd ▸ add_mem hmP hmQ
  obtain ⟨f, hf, hd, g, hg, u, hu⟩ := exists_gS_two h2 hS hmS hprin
  have hpowP : weilPairingElt hP.left g ^ 2 = 1 :=
    weilPairingElt_pow_eq_one_of_gS_two_torsion hP.left h2
      (add_self_eq_zero_of_mem_torsion_two hmP) hg hu
  have hpowQ : weilPairingElt hQ.left g ^ 2 = 1 :=
    weilPairingElt_pow_eq_one_of_gS_two_torsion hQ.left h2
      (add_self_eq_zero_of_mem_torsion_two hmQ) hg hu
  have hpowR : weilPairingElt hR.left g ^ 2 = 1 :=
    weilPairingElt_pow_eq_one_of_gS_two_torsion hR.left h2
      (add_self_eq_zero_of_mem_torsion_two hmR) hg hu
  exact ⟨g, hg, ⟨f, hf, hd, u, hu⟩, hpowP, hpowQ, hpowR,
    weilPairingMu_translatePoint_add_of_baseField hP.left hQ.left hR.left hadd hg hpowP hpowQ
      hpowR⟩

open Classical in
/-- **`e_2(S, ·) : E[2] → μ_2(F)` is a group homomorphism over an arbitrary field, with `hprin` the
only gate.**

`exists_weilPairingTorsionMuHom_two` (`#873`) verbatim, with the root producer swapped.  ⚠️ The
whole of `E[2]` is the domain, named as a group rather than point by point, so this is the one
headline here whose statement constrains a single point — the divisor point `S`, which is also the
only point `hprin` mentions. -/
theorem exists_weilPairingTorsionMuHom_two_of_hprin (h2 : (2 : F) ≠ 0) {xS yS : F}
    (hS : W.Nonsingular xS yS) (hmS : Point.some xS yS hS ∈ W.torsion 2)
    (hprin : ∀ f : W.FunctionField, f ≠ 0 →
      divisor W f = Finsupp.single (pointClosedPoint hS.left) (2 : ℤ) →
      ∃ g₀ : W.FunctionField, g₀ ≠ 0 ∧
        2 • divisor W g₀ = divisor W (mulByTwoEndo h2 f)) :
    ∃ g : W.FunctionField, g ≠ 0 ∧
      (∃ f : W.FunctionField, f ≠ 0 ∧
        divisor W f = Finsupp.single (pointClosedPoint hS.left) (2 : ℤ) ∧
        ∃ u : W.CoordinateRingˣ, (u : W.CoordinateRing) • g ^ 2 = mulByTwoEndo h2 f) ∧
      ∃ φ : Multiplicative (W.torsion 2) →* rootsOfUnity 2 F, ∀ P : W.torsion 2,
        algebraMap F W.FunctionField ((φ (Multiplicative.ofAdd P) : Fˣ) : F)
          = weilPairingPointElt g (P : W.Point) := by
  obtain ⟨f, hf, hd, g, hg, u, hu⟩ := exists_gS_two h2 hS hmS hprin
  exact ⟨g, hg, ⟨f, hf, hd, u, hu⟩, weilPairingTorsionMuHom_two h2 hg hu,
    fun P => algebraMap_coe_weilPairingTorsionMuHom_two h2 hg hu P⟩

end Two

section Three

open Classical in
/-- **Translation-slot bilinearity at `n = 3` over an arbitrary field, with `hprin` the only gate.**

The `n = 3` mirror of `exists_weilPairingElt_translatePoint_add_two_of_hprin`: only the pullback
differs, `mulByThreeEndo h2 h3` in place of `mulByTwoEndo h2`, and with it the rung-5 producer
(`exists_gS_three`, `NthRootOfPullback`) and the `hpow` producer
(`weilPairingElt_pow_eq_one_of_gS_three_baseField`, `TranslationTriplingComm`). -/
theorem exists_weilPairingElt_translatePoint_add_three_of_hprin (h2 : (2 : F) ≠ 0)
    (h3 : (3 : F) ≠ 0) {xP yP xQ yQ xR yR xS yS : F} (hP : W.Nonsingular xP yP)
    (hQ : W.Nonsingular xQ yQ) (hR : W.Nonsingular xR yR) (hS : W.Nonsingular xS yS)
    (hmQ : Point.some xQ yQ hQ ∈ W.torsion 3) (hmS : Point.some xS yS hS ∈ W.torsion 3)
    (hadd : Point.some xP yP hP + Point.some xQ yQ hQ = Point.some xR yR hR)
    (hprin : ∀ f : W.FunctionField, f ≠ 0 →
      divisor W f = Finsupp.single (pointClosedPoint hS.left) (3 : ℤ) →
      ∃ g₀ : W.FunctionField, g₀ ≠ 0 ∧
        3 • divisor W g₀ = divisor W (mulByThreeEndo h2 h3 f)) :
    ∃ g : W.FunctionField, g ≠ 0 ∧
      (∃ f : W.FunctionField, f ≠ 0 ∧
        divisor W f = Finsupp.single (pointClosedPoint hS.left) (3 : ℤ) ∧
        ∃ u : W.CoordinateRingˣ, (u : W.CoordinateRing) • g ^ 3 = mulByThreeEndo h2 h3 f) ∧
      weilPairingElt hR.left g = weilPairingElt hP.left g * weilPairingElt hQ.left g := by
  obtain ⟨f, hf, hd, g, hg, u, hu⟩ := exists_gS_three h2 h3 hS hmS hprin
  have hpowQ : weilPairingElt hQ.left g ^ 3 = 1 :=
    weilPairingElt_pow_eq_one_of_gS_three_baseField hQ.left h2 h3
      (add_add_self_eq_zero_of_mem_torsion_three hmQ) hg hu
  exact ⟨g, hg, ⟨f, hf, hd, u, hu⟩,
    weilPairingElt_translatePoint_add_of_baseField hP.left hQ.left hR.left hadd hg three_ne_zero
      hpowQ⟩

open Classical in
/-- **Translation-slot bilinearity at `n = 3` in `μ_n(F)` over an arbitrary field, with `hprin` the
only gate.**  The `n = 3` mirror of `exists_weilPairingMu_translatePoint_add_two_of_hprin`; its
three `hpow` data come from `weilPairingElt_pow_eq_one_of_gS_three_baseField`
(`TranslationTriplingComm`) in place of `weilPairingElt_pow_eq_one_of_gS_two_torsion`
(`TranslationTorsion`). -/
theorem exists_weilPairingMu_translatePoint_add_three_of_hprin (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0)
    {xP yP xQ yQ xR yR xS yS : F} (hP : W.Nonsingular xP yP) (hQ : W.Nonsingular xQ yQ)
    (hR : W.Nonsingular xR yR) (hS : W.Nonsingular xS yS)
    (hmP : Point.some xP yP hP ∈ W.torsion 3) (hmQ : Point.some xQ yQ hQ ∈ W.torsion 3)
    (hmS : Point.some xS yS hS ∈ W.torsion 3)
    (hadd : Point.some xP yP hP + Point.some xQ yQ hQ = Point.some xR yR hR)
    (hprin : ∀ f : W.FunctionField, f ≠ 0 →
      divisor W f = Finsupp.single (pointClosedPoint hS.left) (3 : ℤ) →
      ∃ g₀ : W.FunctionField, g₀ ≠ 0 ∧
        3 • divisor W g₀ = divisor W (mulByThreeEndo h2 h3 f)) :
    ∃ g : W.FunctionField, g ≠ 0 ∧
      (∃ f : W.FunctionField, f ≠ 0 ∧
        divisor W f = Finsupp.single (pointClosedPoint hS.left) (3 : ℤ) ∧
        ∃ u : W.CoordinateRingˣ, (u : W.CoordinateRing) • g ^ 3 = mulByThreeEndo h2 h3 f) ∧
      ∃ hpowP : weilPairingElt hP.left g ^ 3 = 1,
        ∃ hpowQ : weilPairingElt hQ.left g ^ 3 = 1,
          ∃ hpowR : weilPairingElt hR.left g ^ 3 = 1,
            weilPairingMu hR.left hpowR
              = weilPairingMu hP.left hpowP * weilPairingMu hQ.left hpowQ := by
  have hmR : Point.some xR yR hR ∈ W.torsion 3 := hadd ▸ add_mem hmP hmQ
  obtain ⟨f, hf, hd, g, hg, u, hu⟩ := exists_gS_three h2 h3 hS hmS hprin
  have hpowP : weilPairingElt hP.left g ^ 3 = 1 :=
    weilPairingElt_pow_eq_one_of_gS_three_baseField hP.left h2 h3
      (add_add_self_eq_zero_of_mem_torsion_three hmP) hg hu
  have hpowQ : weilPairingElt hQ.left g ^ 3 = 1 :=
    weilPairingElt_pow_eq_one_of_gS_three_baseField hQ.left h2 h3
      (add_add_self_eq_zero_of_mem_torsion_three hmQ) hg hu
  have hpowR : weilPairingElt hR.left g ^ 3 = 1 :=
    weilPairingElt_pow_eq_one_of_gS_three_baseField hR.left h2 h3
      (add_add_self_eq_zero_of_mem_torsion_three hmR) hg hu
  exact ⟨g, hg, ⟨f, hf, hd, u, hu⟩, hpowP, hpowQ, hpowR,
    weilPairingMu_translatePoint_add_of_baseField hP.left hQ.left hR.left hadd hg hpowP hpowQ
      hpowR⟩

open Classical in
/-- **`e_3(S, ·) : E[3] → μ_3(F)` is a group homomorphism over an arbitrary field, with `hprin` the
only gate.**  The `n = 3` mirror of `exists_weilPairingTorsionMuHom_two_of_hprin`, off
`exists_gS_three` (`NthRootOfPullback`). -/
theorem exists_weilPairingTorsionMuHom_three_of_hprin (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0)
    {xS yS : F} (hS : W.Nonsingular xS yS) (hmS : Point.some xS yS hS ∈ W.torsion 3)
    (hprin : ∀ f : W.FunctionField, f ≠ 0 →
      divisor W f = Finsupp.single (pointClosedPoint hS.left) (3 : ℤ) →
      ∃ g₀ : W.FunctionField, g₀ ≠ 0 ∧
        3 • divisor W g₀ = divisor W (mulByThreeEndo h2 h3 f)) :
    ∃ g : W.FunctionField, g ≠ 0 ∧
      (∃ f : W.FunctionField, f ≠ 0 ∧
        divisor W f = Finsupp.single (pointClosedPoint hS.left) (3 : ℤ) ∧
        ∃ u : W.CoordinateRingˣ, (u : W.CoordinateRing) • g ^ 3 = mulByThreeEndo h2 h3 f) ∧
      ∃ φ : Multiplicative (W.torsion 3) →* rootsOfUnity 3 F, ∀ P : W.torsion 3,
        algebraMap F W.FunctionField ((φ (Multiplicative.ofAdd P) : Fˣ) : F)
          = weilPairingPointElt g (P : W.Point) := by
  obtain ⟨f, hf, hd, g, hg, u, hu⟩ := exists_gS_three h2 h3 hS hmS hprin
  exact ⟨g, hg, ⟨f, hf, hd, u, hu⟩, weilPairingTorsionMuHom_three h2 h3 hg hu,
    fun P => algebraMap_coe_weilPairingTorsionMuHom_three h2 h3 hg hu P⟩

end Three

/-! ### Recovery of the merged `F̄` headlines

⚠️ These six blocks are the check that the point-local `hprin` above is the **right shape**: over an
algebraically closed field it is discharged by a single term, and what comes out is the merged
headline's conclusion on the nose.  A hypothesis that no existing theorem can discharge would look
exactly like `hprin` from the outside, and this is what distinguishes the two.

⚠️ The discharger takes `hS` and `hmS` from the ambient headline rather than binding them — one
binder shorter than `#907`'s `fun h hm _ hf hd => …`, which is the point-local shape showing
through.

They also show that `#861`'s and `#873`'s headlines are **subsumed** by this file's.  That is not a
reason to deprecate them: their consumers all carry `[IsAlgClosed F]` already and would gain
nothing. -/

section AlgClosedRecovery

variable [IsAlgClosed F]

open Classical in
/-- Over `F̄`, `hprin` is `exists_nsmul_divisor_eq_divisor_mulByTwoEndo` and nothing else, so this
file's `n = 2` headline recovers `exists_weilPairingElt_translatePoint_add_two`. -/
example (h2 : (2 : F) ≠ 0) {xP yP xQ yQ xR yR xS yS : F} (hP : W.Nonsingular xP yP)
    (hQ : W.Nonsingular xQ yQ) (hR : W.Nonsingular xR yR) (hS : W.Nonsingular xS yS)
    (hmQ : Point.some xQ yQ hQ ∈ W.torsion 2) (hmS : Point.some xS yS hS ∈ W.torsion 2)
    (hadd : Point.some xP yP hP + Point.some xQ yQ hQ = Point.some xR yR hR) :
    ∃ g : W.FunctionField, g ≠ 0 ∧
      (∃ f : W.FunctionField, f ≠ 0 ∧
        divisor W f = Finsupp.single (pointClosedPoint hS.left) (2 : ℤ) ∧
        ∃ u : W.CoordinateRingˣ, (u : W.CoordinateRing) • g ^ 2 = mulByTwoEndo h2 f) ∧
      weilPairingElt hR.left g = weilPairingElt hP.left g * weilPairingElt hQ.left g :=
  exists_weilPairingElt_translatePoint_add_two_of_hprin h2 hP hQ hR hS hmQ hmS hadd
    fun _ hf hd => exists_nsmul_divisor_eq_divisor_mulByTwoEndo h2 hS hmS hf hd

open Classical in
/-- The `μ_n(F)` recovery at `n = 2`, giving back
`exists_weilPairingMu_translatePoint_add_two`. -/
example (h2 : (2 : F) ≠ 0) {xP yP xQ yQ xR yR xS yS : F} (hP : W.Nonsingular xP yP)
    (hQ : W.Nonsingular xQ yQ) (hR : W.Nonsingular xR yR) (hS : W.Nonsingular xS yS)
    (hmP : Point.some xP yP hP ∈ W.torsion 2) (hmQ : Point.some xQ yQ hQ ∈ W.torsion 2)
    (hmS : Point.some xS yS hS ∈ W.torsion 2)
    (hadd : Point.some xP yP hP + Point.some xQ yQ hQ = Point.some xR yR hR) :
    ∃ g : W.FunctionField, g ≠ 0 ∧
      (∃ f : W.FunctionField, f ≠ 0 ∧
        divisor W f = Finsupp.single (pointClosedPoint hS.left) (2 : ℤ) ∧
        ∃ u : W.CoordinateRingˣ, (u : W.CoordinateRing) • g ^ 2 = mulByTwoEndo h2 f) ∧
      ∃ hpowP : weilPairingElt hP.left g ^ 2 = 1,
        ∃ hpowQ : weilPairingElt hQ.left g ^ 2 = 1,
          ∃ hpowR : weilPairingElt hR.left g ^ 2 = 1,
            weilPairingMu hR.left hpowR
              = weilPairingMu hP.left hpowP * weilPairingMu hQ.left hpowQ :=
  exists_weilPairingMu_translatePoint_add_two_of_hprin h2 hP hQ hR hS hmP hmQ hmS hadd
    fun _ hf hd => exists_nsmul_divisor_eq_divisor_mulByTwoEndo h2 hS hmS hf hd

open Classical in
/-- The bundled-hom recovery at `n = 2`, giving back `exists_weilPairingTorsionMuHom_two`. -/
example (h2 : (2 : F) ≠ 0) {xS yS : F} (hS : W.Nonsingular xS yS)
    (hmS : Point.some xS yS hS ∈ W.torsion 2) :
    ∃ g : W.FunctionField, g ≠ 0 ∧
      (∃ f : W.FunctionField, f ≠ 0 ∧
        divisor W f = Finsupp.single (pointClosedPoint hS.left) (2 : ℤ) ∧
        ∃ u : W.CoordinateRingˣ, (u : W.CoordinateRing) • g ^ 2 = mulByTwoEndo h2 f) ∧
      ∃ φ : Multiplicative (W.torsion 2) →* rootsOfUnity 2 F, ∀ P : W.torsion 2,
        algebraMap F W.FunctionField ((φ (Multiplicative.ofAdd P) : Fˣ) : F)
          = weilPairingPointElt g (P : W.Point) :=
  exists_weilPairingTorsionMuHom_two_of_hprin h2 hS hmS
    fun _ hf hd => exists_nsmul_divisor_eq_divisor_mulByTwoEndo h2 hS hmS hf hd

open Classical in
/-- The `n = 3` mirror, recovering `exists_weilPairingElt_translatePoint_add_three` from
`exists_nsmul_divisor_eq_divisor_mulByThreeEndo`. -/
example (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) {xP yP xQ yQ xR yR xS yS : F}
    (hP : W.Nonsingular xP yP) (hQ : W.Nonsingular xQ yQ) (hR : W.Nonsingular xR yR)
    (hS : W.Nonsingular xS yS) (hmQ : Point.some xQ yQ hQ ∈ W.torsion 3)
    (hmS : Point.some xS yS hS ∈ W.torsion 3)
    (hadd : Point.some xP yP hP + Point.some xQ yQ hQ = Point.some xR yR hR) :
    ∃ g : W.FunctionField, g ≠ 0 ∧
      (∃ f : W.FunctionField, f ≠ 0 ∧
        divisor W f = Finsupp.single (pointClosedPoint hS.left) (3 : ℤ) ∧
        ∃ u : W.CoordinateRingˣ, (u : W.CoordinateRing) • g ^ 3 = mulByThreeEndo h2 h3 f) ∧
      weilPairingElt hR.left g = weilPairingElt hP.left g * weilPairingElt hQ.left g :=
  exists_weilPairingElt_translatePoint_add_three_of_hprin h2 h3 hP hQ hR hS hmQ hmS hadd
    fun _ hf hd => exists_nsmul_divisor_eq_divisor_mulByThreeEndo h2 h3 hS hmS hf hd

open Classical in
/-- The `μ_n(F)` recovery at `n = 3`, giving back
`exists_weilPairingMu_translatePoint_add_three`. -/
example (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) {xP yP xQ yQ xR yR xS yS : F}
    (hP : W.Nonsingular xP yP) (hQ : W.Nonsingular xQ yQ) (hR : W.Nonsingular xR yR)
    (hS : W.Nonsingular xS yS) (hmP : Point.some xP yP hP ∈ W.torsion 3)
    (hmQ : Point.some xQ yQ hQ ∈ W.torsion 3) (hmS : Point.some xS yS hS ∈ W.torsion 3)
    (hadd : Point.some xP yP hP + Point.some xQ yQ hQ = Point.some xR yR hR) :
    ∃ g : W.FunctionField, g ≠ 0 ∧
      (∃ f : W.FunctionField, f ≠ 0 ∧
        divisor W f = Finsupp.single (pointClosedPoint hS.left) (3 : ℤ) ∧
        ∃ u : W.CoordinateRingˣ, (u : W.CoordinateRing) • g ^ 3 = mulByThreeEndo h2 h3 f) ∧
      ∃ hpowP : weilPairingElt hP.left g ^ 3 = 1,
        ∃ hpowQ : weilPairingElt hQ.left g ^ 3 = 1,
          ∃ hpowR : weilPairingElt hR.left g ^ 3 = 1,
            weilPairingMu hR.left hpowR
              = weilPairingMu hP.left hpowP * weilPairingMu hQ.left hpowQ :=
  exists_weilPairingMu_translatePoint_add_three_of_hprin h2 h3 hP hQ hR hS hmP hmQ hmS hadd
    fun _ hf hd => exists_nsmul_divisor_eq_divisor_mulByThreeEndo h2 h3 hS hmS hf hd

open Classical in
/-- The bundled-hom recovery at `n = 3`, giving back `exists_weilPairingTorsionMuHom_three`. -/
example (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) {xS yS : F} (hS : W.Nonsingular xS yS)
    (hmS : Point.some xS yS hS ∈ W.torsion 3) :
    ∃ g : W.FunctionField, g ≠ 0 ∧
      (∃ f : W.FunctionField, f ≠ 0 ∧
        divisor W f = Finsupp.single (pointClosedPoint hS.left) (3 : ℤ) ∧
        ∃ u : W.CoordinateRingˣ, (u : W.CoordinateRing) • g ^ 3 = mulByThreeEndo h2 h3 f) ∧
      ∃ φ : Multiplicative (W.torsion 3) →* rootsOfUnity 3 F, ∀ P : W.torsion 3,
        algebraMap F W.FunctionField ((φ (Multiplicative.ofAdd P) : Fˣ) : F)
          = weilPairingPointElt g (P : W.Point) :=
  exists_weilPairingTorsionMuHom_three_of_hprin h2 h3 hS hmS
    fun _ hf hd => exists_nsmul_divisor_eq_divisor_mulByThreeEndo h2 h3 hS hmS hf hd

end AlgClosedRecovery

/-! ### Non-vacuity, over a field that is NOT algebraically closed

⚠️ The base field below is **`ℚ`**, so neither `#861`'s nor `#873`'s headline nor the
`AlgClosedRecovery` block above applies to it, and `hprin` is the only hypothesis left over.

`y² = x³ − x` has **three** rational `2`-torsion points, `(0, 0)`, `(1, 0)` and `(−1, 0)`, and
`exampleAdd` verifies `(0, 0) ⊕ (1, 0) = (−1, 0)` by Mathlib's secant formula — so the three
translation points `P`, `Q`, `R` below are pairwise distinct and all rational.  The divisor point
`S` is a free variable of the statement and is taken to be `P`; nothing constrains it to be distinct
from them.  ⚠️ Contrast `#861`'s divisor-slot sibling, which needs three *divisor* points and so has
no fourth point left for the translation slot at all. -/

section Nonvacuity

private lemma exampleTwo : (2 : ℚ) ≠ 0 := by norm_num

/-- The curve `y² = x³ − x` over `ℚ`, of discriminant `64`. -/
private noncomputable def exampleCurve : Affine ℚ := ⟨0, 0, 0, -1, 0⟩

private instance : exampleCurve.IsElliptic := by
  rw [WeierstrassCurve.isElliptic_iff, isUnit_iff_ne_zero]
  norm_num [exampleCurve, WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈]

private lemma exampleNsP : exampleCurve.Nonsingular 0 0 :=
  exampleCurve.equation_iff_nonsingular.mp (by
    norm_num [exampleCurve, WeierstrassCurve.Affine.equation_iff])

private lemma exampleNsQ : exampleCurve.Nonsingular 1 0 :=
  exampleCurve.equation_iff_nonsingular.mp (by
    norm_num [exampleCurve, WeierstrassCurve.Affine.equation_iff])

private lemma exampleNsR : exampleCurve.Nonsingular (-1) 0 :=
  exampleCurve.equation_iff_nonsingular.mp (by
    norm_num [exampleCurve, WeierstrassCurve.Affine.equation_iff])

open Classical in
private lemma exampleTorP : Point.some (0 : ℚ) 0 exampleNsP ∈ exampleCurve.torsion 2 :=
  (mem_torsion_two_some_iff exampleNsP).mpr (by norm_num [exampleCurve])

open Classical in
private lemma exampleTorQ : Point.some (1 : ℚ) 0 exampleNsQ ∈ exampleCurve.torsion 2 :=
  (mem_torsion_two_some_iff exampleNsQ).mpr (by norm_num [exampleCurve])

/-- `(0, 0) ⊕ (1, 0) = (−1, 0)` on `y² = x³ − x` over `ℚ`.  The `x`-coordinates differ, so this is
Mathlib's secant case: the slope is `0`, `addX = −1` and `addY = 0`. -/
private lemma exampleAdd : Point.some (0 : ℚ) 0 exampleNsP + Point.some (1 : ℚ) 0 exampleNsQ
    = Point.some (-1 : ℚ) 0 exampleNsR := by
  rw [Point.add_of_X_ne (by norm_num)]
  norm_num [WeierstrassCurve.Affine.addX, WeierstrassCurve.Affine.addY,
    WeierstrassCurve.Affine.negAddY, WeierstrassCurve.Affine.negY,
    WeierstrassCurve.Affine.slope, exampleCurve]

open Classical in
/-- **The `n = 2` translation-slot bilinearity headline applies on a curve over `ℚ`**, at three
*distinct* rational `2`-torsion translation points, with `hprin` the only hypothesis left.

⚠️ **Every `by convert` below is load-bearing.**  `ℚ` has a genuine `DecidableEq` instance, so
anything stated over `ℚ` is indexed by `instDecidableEqRat`, while the headline — stated for a
general `F` under `open Classical in` — is indexed by `Classical.propDecidable`.  That is a
*low-priority* local instance, so `open Classical in` on the `ℚ` lemmas would not change which one
they pick: the conversion is unavoidable, not a stylistic choice.  The objects are propositionally
but not syntactically equal and `convert` closes each gap by `Subsingleton.elim`.

⚠️ It bites in the `torsion` memberships and in `exampleAdd` (the `Point.instAdd` inside the `hadd`
equation), but **not** inside `hprin` — which is the point-local shape showing through again, since
`hprin` here mentions no `torsion` membership at all.  `#907` needed a fourth `convert` there. -/
example (hprin : ∀ f : exampleCurve.FunctionField, f ≠ 0 →
      divisor exampleCurve f = Finsupp.single (pointClosedPoint exampleNsP.left) (2 : ℤ) →
      ∃ g₀ : exampleCurve.FunctionField, g₀ ≠ 0 ∧
        2 • divisor exampleCurve g₀ = divisor exampleCurve (mulByTwoEndo exampleTwo f)) :
    ∃ g : exampleCurve.FunctionField, g ≠ 0 ∧
      (∃ f : exampleCurve.FunctionField, f ≠ 0 ∧
        divisor exampleCurve f = Finsupp.single (pointClosedPoint exampleNsP.left) (2 : ℤ) ∧
        ∃ u : exampleCurve.CoordinateRingˣ,
          (u : exampleCurve.CoordinateRing) • g ^ 2 = mulByTwoEndo exampleTwo f) ∧
      weilPairingElt exampleNsR.left g
        = weilPairingElt exampleNsP.left g * weilPairingElt exampleNsQ.left g :=
  exists_weilPairingElt_translatePoint_add_two_of_hprin exampleTwo exampleNsP exampleNsQ
    exampleNsR exampleNsP (by convert exampleTorQ) (by convert exampleTorP)
    (by convert exampleAdd) hprin

/-! ⚠️ **The bundled-hom headline needs more than a `by convert`, and the reason is structural.**
Every `DecidableEq` mismatch above sits in a *hypothesis*, where `convert` bridges it by
`Subsingleton.elim`.  `exists_weilPairingTorsionMuHom_two_of_hprin`'s **conclusion** names `E[2]`,
and `W.torsion` takes the `DecidableEq F` instance as an argument — so over `ℚ` the two statements
differ in *the type of a bound variable* (`φ : Multiplicative ↥(E[2]) →* μ_2(ℚ)`), which no
hypothesis-side conversion can reach and which `convert` can only take apart into a `HEq` between
two `φ`s.

The fix is to state the certificate at the **same** instance the headline is elaborated at, by
pinning `Classical.propDecidable` for this section only.  ⚠️ Nothing is assumed away by that:
`DecidableEq ℚ` is a `Subsingleton`, so the pinned instance and `instDecidableEqRat` give the same
subgroup — the certificate is about the curve, and the attribute is about which of two equal terms
the elaborator writes down.  It is scoped to this section so that the blocks above keep the
`convert` form, which is the one that generalises. -/

section HomNonvacuity

attribute [local instance 10000] Classical.propDecidable

/-- **`e_2(S, ·) : E[2] → μ_2(ℚ)` is a group homomorphism on a curve over `ℚ`**, with `hprin` the
only hypothesis left.

⚠️ This is the sharper of the two `ℚ` certificates, because its conclusion names the *whole* of
`E[2]` as a group rather than a finite list of points: the domain is `exampleCurve.torsion 2`, which
over `ℚ` is a proper subgroup of the `F̄`-torsion and is not assumed to be anything in
particular. -/
example (hprin : ∀ f : exampleCurve.FunctionField, f ≠ 0 →
      divisor exampleCurve f = Finsupp.single (pointClosedPoint exampleNsP.left) (2 : ℤ) →
      ∃ g₀ : exampleCurve.FunctionField, g₀ ≠ 0 ∧
        2 • divisor exampleCurve g₀ = divisor exampleCurve (mulByTwoEndo exampleTwo f)) :
    ∃ g : exampleCurve.FunctionField, g ≠ 0 ∧
      (∃ f : exampleCurve.FunctionField, f ≠ 0 ∧
        divisor exampleCurve f = Finsupp.single (pointClosedPoint exampleNsP.left) (2 : ℤ) ∧
        ∃ u : exampleCurve.CoordinateRingˣ,
          (u : exampleCurve.CoordinateRing) • g ^ 2 = mulByTwoEndo exampleTwo f) ∧
      ∃ φ : Multiplicative (exampleCurve.torsion 2) →* rootsOfUnity 2 ℚ,
        ∀ P : exampleCurve.torsion 2,
          algebraMap ℚ exampleCurve.FunctionField ((φ (Multiplicative.ofAdd P) : ℚˣ) : ℚ)
            = weilPairingPointElt g (P : exampleCurve.Point) :=
  exists_weilPairingTorsionMuHom_two_of_hprin exampleTwo exampleNsP (by convert exampleTorP) hprin

end HomNonvacuity

end Nonvacuity

end WeierstrassCurve.Affine
