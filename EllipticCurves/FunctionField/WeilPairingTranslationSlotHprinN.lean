/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import EllipticCurves.FunctionField.CoordinateRingNormalGeneral
import EllipticCurves.FunctionField.NthRootOfPullbackN
import EllipticCurves.FunctionField.TranslationMulByNCommGeneral
import EllipticCurves.FunctionField.WeilPairingTranslationSlotHprin

/-!
# The translation slot at general `n`, with `hprin` the only gate (rung 6)

`EllipticCurves.FunctionField.WeilPairingTranslationSlotHprin` states the rung-6 translation slot
over an arbitrary field — bilinearity in `F(W)`, the same in `μ_n(F)`, and the bundled homomorphism
`e_n(S, ·) : E[n] → μ_n(F)` — at `n = 2` and `n = 3`, with `hprin` the only gate.  This file states
all three at **every** `n`, and discharges the one side condition at every `3`-smooth `n`.

## ⚠️ The `n = 2, 3` restriction was chronological, and its scope bullet blamed the wrong gate

The twin's `## Scope` section listed *"general `n` (`#404`'s `ωₙ`)"* as out of scope.  **`ωₙ` is not
what gated it.**  `#1165` established that `[n]∗` needs no `y`-coordinate division polynomial, and
`EllipticCurves.FunctionField.TranslationMulByNCommGeneral` says so in terms about the very
commutation this file consumes: *"nothing here uses the `y`-coordinate division polynomial `ωₙ`, the
general `n` on-curve identity (`#404`) or the elliptic-net recurrence (Ward, `#260`)"*.

Every input to the six merged headlines is already stated at a general index, and most always were:

| input | generality |
| --- | --- |
| `weilPairingElt_pow_eq_one` (`WeilPairing`) | `{n : ℕ}`, arbitrary |
| `translateEndo_pow_eq_self_of` (`WeilPairing`) | ⚠️ the pulled-back function is arbitrary |
| `translateEndo_algebraMap_unit` (`WeilPairing`) | no index at all |
| `translateEndo_mulByNEndo_apply_torsion_of_baseField` (`TranslationMulByNComm…`) | every `n` |
| `weilPairingElt_translatePoint_add_of_baseField` (`WeilPairingBilinearBaseField`) | `n ≠ 0` |
| `weilPairingMu_translatePoint_add_of_baseField` (`WeilPairingBilinearMu`) | `[NeZero n]` |
| `weilPairingPointMuHom` (`WeilPairingTranslationSlotHom`) | `(n : ℕ)`, `[NeZero n]` |
| `exists_gS_n`, `exists_gS_of_smooth` (`NthRootOfPullbackN`) | arbitrary `n` / `3`-smooth `n` |

⚠️ **The specificity lived in exactly two places, and neither is `ωₙ`**: the root producer
`exists_gS_two` / `exists_gS_three`, generalised by `#1304`; and the single lemma
`weilPairingElt_pow_eq_one_of_gS_two_torsion` (`TranslationTorsion`), whose general form is the
four-line `weilPairingElt_pow_eq_one_of_gS_n_torsion` below.  Everything else is the merged proof
with the numeral removed.

## ⚠️ This DOES subsume the merged six — and they are still not touched

`#1304` could **not** subsume `exists_gS_two` / `exists_gS_three`, because those carry
`[IsDedekindDomain W.CoordinateRing]` and not `[W.IsElliptic]`, so the hypothesis sets are
incomparable.  That is not the situation here: the twin file's own variable line already reads
`[Field F] {W : Affine F} [W.IsElliptic]`, so what is below is strictly more general in `n` **in the
same setting**.

⚠️ **Nothing in `WeilPairingTranslationSlotHprin.lean` is deleted, deprecated, restated or
re-proved.**  The standing judgement of `#903`, `#907`, `#910` and `#1304` is that a merged
statement whose consumers already hold the stronger hypothesis gains nothing from a deprecation,
which would be a diff across every consumer for no mathematical content.  Faithfulness is certified
instead by the `Recovery` block, which derives all six merged statements *through* the general ones.

## Main statements

* `WeierstrassCurve.Affine.CoordinateRing.weilPairingElt_pow_eq_one_of_gS_n_torsion` — the one new
  input: `e(T, g) ^ k = 1` for an `n`-torsion `T` and a rung-5 datum over `[n]∗`;
* `WeierstrassCurve.Affine.exists_weilPairingElt_translatePoint_add_n_of_hprin` —
  `e_n(R, g) = e_n(P, g) · e_n(Q, g)` for `P ⊕ Q = R`, in `F(W)`, at every `n`;
* `WeierstrassCurve.Affine.exists_weilPairingMu_translatePoint_add_n_of_hprin` — the same in
  `rootsOfUnity n F`, with the three `hpow` data **produced** rather than assumed;
* `WeierstrassCurve.Affine.exists_weilPairingTorsionMuHom_n_of_hprin` —
  `e_n(S, ·) : E[n] → μ_n(F)` is a group homomorphism, at every `n`;
* the three `…_of_smooth_of_hprin` corollaries, with the non-constancy hypothesis **discharged** at
  every `3`-smooth `n ≠ 0`.  These are the first rung-6 statements on this board that reach an index
  other than `2` and `3`.

## Naming

⚠️ The index suffix goes **before** the qualifier — `…_n_of_hprin`, not `…_of_hprin_n` — which is
the twin file's rule, settled by `#910`'s review (*"mirror your twin wins while every `_of_hprin`
file has a twin"*).  As there, `_n` tracks the **isogeny** `mulByNEndo n hn`, not the exponent; the
`3`-smooth track takes the index slot too, so the corollaries read `…_of_smooth_of_hprin`.

`weilPairingTorsionMuHom_n` carries `@[nolint defsWithUnderscore]` for the reason its merged twin
`weilPairingTorsionMuHom_two` gives (`#1277`): `_n` is this development's index suffix and not a
compound name.  ⚠️ Spelling it `weilPairingTorsionMuHomN` to dodge the linter would break twin
consistency, which is the invariant `#918`'s namespace check exists to protect.

On placement, each declaration sits in **its own twin's** namespace rather than in one uniform
choice: `weilPairingElt_pow_eq_one_of_gS_n_torsion`, `torsion_le_weilPairingPointSubgroup_n`,
`weilPairingTorsionMuHom_n` and `algebraMap_coe_weilPairingTorsionMuHom_n` in
`WeierstrassCurve.Affine.CoordinateRing`; every `exists_…` headline in `WeierstrassCurve.Affine`.
⚠️ `#903`: the build resolves either spelling from inside a file that opens `CoordinateRing`, so
only `#print axioms` on the fully qualified name — of the new declaration *and of its twin* — checks
this.

## ⚠️ What is NOT here

* **`hprin` is not discharged at any `n`.**  `#899`'s test — is the obstruction used to prove an
  *equality* or to produce a *witness*? — puts it on the witness side.
* ⚠️ **There is deliberately no general-`n` `_of_isAlgClosed` corollary.**  At `n = 2` and `n = 3`
  `hprin` is discharged over `F̄` by `PullbackPrincipalityTwo` / `PullbackPrincipalityThree`, whose
  input is the fibre description `[n]∗((S) − (O)) = ∑_{R ∈ E[n]} ((P ⊕ R) − (R))` — merged **only**
  at those two indices (`MulByTwoFibreAffine`, `MulByThreeFibre`).  At `3`-smooth `n > 3` no such
  description exists, so the corollary would be one nothing can feed.  That is the `#944` vacuity
  trap, and `#1304` refused the same corollary for the same reason.
* **`n = 5` is not reached.**  The ceiling is `transcendental_xCoord_nsmul_of_smooth`'s, and behind
  it stand `#404`/`#251` and `#1184`.
* **Non-degeneracy is untouched**, and stays over `F̄`: there `[IsAlgClosed F]` is load-bearing and
  enters twice (`WeilPairingNondegenerateTwo`, module docstring, "the closure enters twice").
* **No pairing on `W.Point × W.Point`**, and no effect on the two-slot `weilPairingTwoHom` /
  `weilPairingThreeHom` of `#922`/`#925`, whose `[IsAlgClosed F]` does not lift.

## ⚠️ `ωₙ` is not the gate **here**, and that verdict does not transfer to the neighbours

The heading at the top of this docstring says the twin's scope bullet blamed the wrong gate, and it
did.  ⚠️ **The reason it was wrong is local to statements that take `hprin` as a hypothesis, and the
same sentence is *correct* in every file that discharges it.**  The discriminator is recorded here
because this is the file a reader carries the wrong generalisation out of.

* **`hprin` a hypothesis** — this file and its twin.  The only `n`-indexed input is the
  non-constancy of `[n]`, which is a side condition and not a coordinate statement:
  `transcendental_xCoord_nsmul_of_smooth` discharges it at every `3`-smooth `n`, and
  `transcendental_xCoord_nsmul_of_isAlgClosed` (`EllipticCurves.FunctionField.MulByNTranscendence`)
  discharges it over `F̄` of characteristic `≠ 2` at **every** `n ≠ 0`.  No `ωₙ` at either index.
* **`hprin` discharged** — every `_of_isAlgClosed` statement on this front.  It has exactly two
  producers in this tree, `exists_gS_two_of_isAlgClosed`
  (`EllipticCurves.FunctionField.PullbackPrincipalityTwo`) and `exists_gS_three_of_isAlgClosed`
  (`EllipticCurves.FunctionField.PullbackPrincipalityThree`).  Those consume the fibre description,
  which consumes `EllipticCurves.FunctionField.MulByTwoFibreAffine` and
  `EllipticCurves.FunctionField.MulByThreeFibre`, and the step *those* need is the `y`-coordinate of
  `n • P` in division-polynomial form: `addY_self_eq_div` (`EllipticCurves.Torsion.DoublingCoords`),
  `y(2P) = ω₂/(2 ψ₂³)`, and its mirror `3 • (x, y) = (Φ₃/ΨSq₃, ω₃/(2 ψ₃³))`
  (`EllipticCurves.Torsion.TriplingCoords`).  ⚠️ `DoublingCoords` names the general-`n` form of
  exactly that content, in its own *What is not here* section: *"Any general `ωₙ` duplication
  formula — that is `#404`, and nothing here approaches it."*

So *"general `n` (`#404`'s `ωₙ`)"* is a true description of **this tree's route** to a general index
wherever `hprin` is discharged, which is what a scope bullet claims.  ⚠️ It is not a claim that no
other route exists and must not be strengthened into one.  ⚠️ **The bullets that say it elsewhere
are therefore correct, and correcting them would install a falsehood.**  Matching the phrase
*general `n`* or *uniform `n`* within 170 characters of `ωₙ`, on whitespace-normalised source,
returns **39 sites in 30 modules**: 18 across the nine modules that say `ωₙ` is *not* used, and
**21 — exactly one in each of 21 modules — citing it as the general-`n` gate, every one of those
`hprin`-discharged and every one correct**.  ⚠️ Three of the 39 belong to the paragraph you are
reading, which is why the match is written out here rather than merely cited: a later reader who
runs it should not be startled by this file's own five hits.

⚠️ **The cheapest check that the split is real**: of the six `…Hprin` modules only the twin ever
carried the bullet.  `WeilPairingDivisorSlotBilinearHprin`, `WeilPairingGaloisRootHprin`,
`WeilPairingProductRelationHprin` and `WeilPairingProductRelationRootIndependentHprin` never blamed
`ωₙ`, and `#1308` corrected the one module that did.

## Non-vacuity

Two blocks, answering different questions.

* `Recovery` derives all six merged headlines from the general ones, through the bridges
  `mulByNEndo_two` / `mulByNEndo_three`.  ⚠️ This is what separates a faithful generalisation from a
  new statement that merely resembles one; all six are `private`, since public copies would
  duplicate merged names.
* `Nonvacuity` instantiates the `3`-smooth corollaries at **`n = 4`**, an index no merged rung-5 or
  rung-6 statement reaches, over **`ℚ`** — which is not algebraically closed, so neither the merged
  headlines nor the twin's `AlgClosedRecovery` block applies to it.  On `y² = x³ − x` the three
  rational `2`-torsion points `(0, 0)`, `(1, 0)`, `(−1, 0)` are pairwise distinct, are `4`-torsion
  because `4 • X = 2 • (2 • X)`, and satisfy `(0, 0) ⊕ (1, 0) = (−1, 0)`.  ⚠️ `hprin` remains a
  hypothesis there, exactly as it does at `n = 2, 3`; the certificate says the *other*
  hypotheses are inhabited at a new index, and claims nothing more.

## References

* [J. Silverman, *The arithmetic of elliptic curves*][silverman2009], III.8.1(a).
-/

namespace WeierstrassCurve.Affine

namespace CoordinateRing

variable {F : Type*} [Field F] {W : Affine F} [W.IsElliptic] {xT yT : F}

/-! ### The one new input: `e(T, g) ^ k = 1` from `n`-torsion of `T`, at every `n` -/

open Classical in
/-- **`e(T, g) ^ k = 1` from the base-field `n`-torsion of `T`, at every `n`.**  The general-`n`
form of `weilPairingElt_pow_eq_one_of_gS_two_torsion` (`TranslationTorsion`): given a rung-5 datum
`u · g ^ k = [n]∗ f` and `n • T = 0` over the base field, the translation `τ_T∗` fixes `[n]∗ f`
(`translateEndo_mulByNEndo_apply_torsion_of_baseField`) and fixes the constant unit `u`
(`translateEndo_algebraMap_unit`), so it fixes `g ^ k` and the pairing value is a `k`-th root of
unity.

⚠️ **The two indices are independent and both are needed.**  `n` is the isogeny `[n]∗`; `k` is the
exponent of the root.  The merged twin is stated the same way — `mulByTwoEndo` against an arbitrary
exponent — and collapsing `k` to `n` here would give a statement *weaker* than its own twin.

⚠️ Nothing in the proof is `[2]`-specific and nothing needs `ωₙ`: `translateEndo_pow_eq_self_of`
takes the pulled-back function as an arbitrary element of `F(W)`, and the only `n`-dependence is in
which commutation discharges `hcomm`. -/
theorem weilPairingElt_pow_eq_one_of_gS_n_torsion (hT : W.Equation xT yT) (n : ℕ)
    (hn : Transcendental F (n • genericPoint (W := W)).xCoord)
    (htors : n • torsionPoint hT = 0)
    {f g : W.FunctionField} {u : W.CoordinateRingˣ} {k : ℕ} (hg : g ≠ 0)
    (hu : (u : W.CoordinateRing) • g ^ k = mulByNEndo n hn f) :
    weilPairingElt hT g ^ k = 1 :=
  weilPairingElt_pow_eq_one hT hg
    (translateEndo_pow_eq_self_of hT hu
      (translateEndo_mulByNEndo_apply_torsion_of_baseField hT n hn htors f)
      (translateEndo_algebraMap_unit hT u))

/-! ### The bundled homomorphism `e_n(S, ·) : E[n] → μ_n(F)` at general `n` -/

open Classical in
/-- **Every `n`-torsion point carries the datum**, the general-`n` form of
`torsion_le_weilPairingPointSubgroup_two` (`WeilPairingTranslationSlotHom`).  The `O` corner is the
subgroup's own `zero_mem`; on an affine point it is `weilPairingElt_pow_eq_one_of_gS_n_torsion` fed
`mem_torsion_iff`.

⚠️ No `[IsAlgClosed F]`: the rung-5 datum `hu` is an argument here, not something produced. -/
theorem torsion_le_weilPairingPointSubgroup_n {n : ℕ} [NeZero n]
    (hn : Transcendental F (n • genericPoint (W := W)).xCoord)
    {f g : W.FunctionField} {u : W.CoordinateRingˣ} (hg : g ≠ 0)
    (hu : (u : W.CoordinateRing) • g ^ n = mulByNEndo n hn f) :
    W.torsion n ≤ weilPairingPointSubgroup hg n := by
  rintro (_ | ⟨x, y, h⟩) hP
  · exact (weilPairingPointSubgroup hg n).zero_mem
  · exact weilPairingElt_pow_eq_one_of_gS_n_torsion h.left n hn (mem_torsion_iff.mp hP) hg hu

open Classical in
/-- **`e_n(S, ·) : E[n] → μ_n(F)` as a homomorphism of groups, at every `n`**, for a rung-5 root `g`
at `S` over an arbitrary field.  `weilPairingPointMuHom` — already general in `n` — restricted along
the inclusion of `E[n]`.

⚠️ `nolint defsWithUnderscore`, for the reason the merged `weilPairingTorsionMuHom_two` gives
(`#1277`): `_n` is this development's index suffix for the isogeny track, the same slot `_two` and
`_three` occupy, and is not a compound name. -/
@[nolint defsWithUnderscore]
noncomputable def weilPairingTorsionMuHom_n {n : ℕ} [NeZero n]
    (hn : Transcendental F (n • genericPoint (W := W)).xCoord)
    {f g : W.FunctionField} {u : W.CoordinateRingˣ} (hg : g ≠ 0)
    (hu : (u : W.CoordinateRing) • g ^ n = mulByNEndo n hn f) :
    Multiplicative (W.torsion n) →* rootsOfUnity n F :=
  (weilPairingPointMuHom hg n).comp
    (AddMonoidHom.toMultiplicative
      (AddSubgroup.inclusion (torsion_le_weilPairingPointSubgroup_n hn hg hu)))

open Classical in
/-- The values of `weilPairingTorsionMuHom_n` are the pairing values. -/
@[simp]
theorem algebraMap_coe_weilPairingTorsionMuHom_n {n : ℕ} [NeZero n]
    (hn : Transcendental F (n • genericPoint (W := W)).xCoord)
    {f g : W.FunctionField} {u : W.CoordinateRingˣ} (hg : g ≠ 0)
    (hu : (u : W.CoordinateRing) • g ^ n = mulByNEndo n hn f) (P : W.torsion n) :
    algebraMap F W.FunctionField
        ((weilPairingTorsionMuHom_n hn hg hu (Multiplicative.ofAdd P) : Fˣ) : F)
      = weilPairingPointElt g (P : W.Point) :=
  algebraMap_coe_weilPairingPointMu hg (torsion_le_weilPairingPointSubgroup_n hn hg hu P.2)

end CoordinateRing

open CoordinateRing IsDedekindDomain IsDedekindDomain.HeightOneSpectrum

variable {F : Type*} [Field F] {W : Affine F} [W.IsElliptic]

/-! ### The three headlines at an arbitrary `n` -/

open Classical in
/-- **Translation-slot bilinearity at an arbitrary `n` over an arbitrary field, with `hprin` the
only gate.**

```
e_n(R, g) = e_n(P, g) · e_n(Q, g),     for  P ⊕ Q = R.
```

`exists_weilPairingElt_translatePoint_add_two_of_hprin` (`#873`, `WeilPairingTranslationSlotHprin`)
with the numeral removed: `exists_gS_two` becomes `exists_gS_n` and
`weilPairingElt_pow_eq_one_of_gS_two_torsion` becomes its general-`n` form.  The bilinearity step
`weilPairingElt_translatePoint_add_of_baseField` was already stated at an arbitrary `n`.

⚠️ `hprin` is stated at the **divisor** point `S` only, and is `exists_gS_n`'s own hypothesis: the
three translation points `P`, `Q`, `R` do not index a root.  See the twin's module docstring for why
this is not `#907`'s quantified shape.

⚠️ As in the twin, only `Q`'s `n`-torsion is assumed among the translation points —
`weilPairingElt_translatePoint_add_of_baseField` needs the pairing value to be a root of unity at
the *middle* point only. -/
theorem exists_weilPairingElt_translatePoint_add_n_of_hprin {n : ℕ}
    (hn : Transcendental F (n • genericPoint (W := W)).xCoord) (hnz : n ≠ 0)
    {xP yP xQ yQ xR yR xS yS : F} (hP : W.Nonsingular xP yP) (hQ : W.Nonsingular xQ yQ)
    (hR : W.Nonsingular xR yR) (hS : W.Nonsingular xS yS)
    (hmQ : Point.some xQ yQ hQ ∈ W.torsion n) (hmS : Point.some xS yS hS ∈ W.torsion n)
    (hadd : Point.some xP yP hP + Point.some xQ yQ hQ = Point.some xR yR hR)
    (hprin : ∀ f : W.FunctionField, f ≠ 0 →
      divisor W f = Finsupp.single (pointClosedPoint hS.left) (n : ℤ) →
      ∃ g₀ : W.FunctionField, g₀ ≠ 0 ∧
        n • divisor W g₀ = divisor W (mulByNEndo n hn f)) :
    ∃ g : W.FunctionField, g ≠ 0 ∧
      (∃ f : W.FunctionField, f ≠ 0 ∧
        divisor W f = Finsupp.single (pointClosedPoint hS.left) (n : ℤ) ∧
        ∃ u : W.CoordinateRingˣ, (u : W.CoordinateRing) • g ^ n = mulByNEndo n hn f) ∧
      weilPairingElt hR.left g = weilPairingElt hP.left g * weilPairingElt hQ.left g := by
  obtain ⟨f, hf, hd, g, hg, u, hu⟩ := exists_gS_n hn hS hmS hprin
  have hpowQ : weilPairingElt hQ.left g ^ n = 1 :=
    weilPairingElt_pow_eq_one_of_gS_n_torsion hQ.left n hn (mem_torsion_iff.mp hmQ) hg hu
  exact ⟨g, hg, ⟨f, hf, hd, u, hu⟩,
    weilPairingElt_translatePoint_add_of_baseField hP.left hQ.left hR.left hadd hg hnz hpowQ⟩

open Classical in
/-- **Translation-slot bilinearity at an arbitrary `n` in `μ_n(F)`, with `hprin` the only gate.**

```
μ_n(R, g) = μ_n(P, g) · μ_n(Q, g)   in rootsOfUnity n F.
```

`exists_weilPairingMu_translatePoint_add_two_of_hprin` (`#873`) with the numeral removed.  The three
`hpow` data are bound existentially because `weilPairingMu` is indexed by the *proof*, and they are
**produced** — not assumed — from the single rung-5 certificate the envelope already carries, by
`weilPairingElt_pow_eq_one_of_gS_n_torsion` at each of `P`, `Q`, `R`.

⚠️ `hmP` is required here and is not in the `F(W)`-level headline; that is a consequence of
`weilPairingMu` being indexed by `hpow`, not of the mathematics changing.  `hmR` is derived from
`hadd`, not assumed. -/
theorem exists_weilPairingMu_translatePoint_add_n_of_hprin {n : ℕ} [NeZero n]
    (hn : Transcendental F (n • genericPoint (W := W)).xCoord)
    {xP yP xQ yQ xR yR xS yS : F} (hP : W.Nonsingular xP yP) (hQ : W.Nonsingular xQ yQ)
    (hR : W.Nonsingular xR yR) (hS : W.Nonsingular xS yS)
    (hmP : Point.some xP yP hP ∈ W.torsion n) (hmQ : Point.some xQ yQ hQ ∈ W.torsion n)
    (hmS : Point.some xS yS hS ∈ W.torsion n)
    (hadd : Point.some xP yP hP + Point.some xQ yQ hQ = Point.some xR yR hR)
    (hprin : ∀ f : W.FunctionField, f ≠ 0 →
      divisor W f = Finsupp.single (pointClosedPoint hS.left) (n : ℤ) →
      ∃ g₀ : W.FunctionField, g₀ ≠ 0 ∧
        n • divisor W g₀ = divisor W (mulByNEndo n hn f)) :
    ∃ g : W.FunctionField, g ≠ 0 ∧
      (∃ f : W.FunctionField, f ≠ 0 ∧
        divisor W f = Finsupp.single (pointClosedPoint hS.left) (n : ℤ) ∧
        ∃ u : W.CoordinateRingˣ, (u : W.CoordinateRing) • g ^ n = mulByNEndo n hn f) ∧
      ∃ hpowP : weilPairingElt hP.left g ^ n = 1,
        ∃ hpowQ : weilPairingElt hQ.left g ^ n = 1,
          ∃ hpowR : weilPairingElt hR.left g ^ n = 1,
            weilPairingMu hR.left hpowR
              = weilPairingMu hP.left hpowP * weilPairingMu hQ.left hpowQ := by
  have hmR : Point.some xR yR hR ∈ W.torsion n := hadd ▸ add_mem hmP hmQ
  obtain ⟨f, hf, hd, g, hg, u, hu⟩ := exists_gS_n hn hS hmS hprin
  have hpowP : weilPairingElt hP.left g ^ n = 1 :=
    weilPairingElt_pow_eq_one_of_gS_n_torsion hP.left n hn (mem_torsion_iff.mp hmP) hg hu
  have hpowQ : weilPairingElt hQ.left g ^ n = 1 :=
    weilPairingElt_pow_eq_one_of_gS_n_torsion hQ.left n hn (mem_torsion_iff.mp hmQ) hg hu
  have hpowR : weilPairingElt hR.left g ^ n = 1 :=
    weilPairingElt_pow_eq_one_of_gS_n_torsion hR.left n hn (mem_torsion_iff.mp hmR) hg hu
  exact ⟨g, hg, ⟨f, hf, hd, u, hu⟩, hpowP, hpowQ, hpowR,
    weilPairingMu_translatePoint_add_of_baseField hP.left hQ.left hR.left hadd hg hpowP hpowQ
      hpowR⟩

open Classical in
/-- **`e_n(S, ·) : E[n] → μ_n(F)` is a group homomorphism at an arbitrary `n` over an arbitrary
field, with `hprin` the only gate.**

`exists_weilPairingTorsionMuHom_two_of_hprin` (`#890`) with the numeral removed.  ⚠️ The whole of
`E[n]` is the domain, named as a group rather than point by point, so this is the one headline here
whose statement constrains a single point — the divisor point `S`, which is also the only point
`hprin` mentions. -/
theorem exists_weilPairingTorsionMuHom_n_of_hprin {n : ℕ} [NeZero n]
    (hn : Transcendental F (n • genericPoint (W := W)).xCoord) {xS yS : F}
    (hS : W.Nonsingular xS yS) (hmS : Point.some xS yS hS ∈ W.torsion n)
    (hprin : ∀ f : W.FunctionField, f ≠ 0 →
      divisor W f = Finsupp.single (pointClosedPoint hS.left) (n : ℤ) →
      ∃ g₀ : W.FunctionField, g₀ ≠ 0 ∧
        n • divisor W g₀ = divisor W (mulByNEndo n hn f)) :
    ∃ g : W.FunctionField, g ≠ 0 ∧
      (∃ f : W.FunctionField, f ≠ 0 ∧
        divisor W f = Finsupp.single (pointClosedPoint hS.left) (n : ℤ) ∧
        ∃ u : W.CoordinateRingˣ, (u : W.CoordinateRing) • g ^ n = mulByNEndo n hn f) ∧
      ∃ φ : Multiplicative (W.torsion n) →* rootsOfUnity n F, ∀ P : W.torsion n,
        algebraMap F W.FunctionField ((φ (Multiplicative.ofAdd P) : Fˣ) : F)
          = weilPairingPointElt g (P : W.Point) := by
  obtain ⟨f, hf, hd, g, hg, u, hu⟩ := exists_gS_n hn hS hmS hprin
  exact ⟨g, hg, ⟨f, hf, hd, u, hu⟩, weilPairingTorsionMuHom_n hn hg hu,
    fun P => algebraMap_coe_weilPairingTorsionMuHom_n hn hg hu P⟩

/-! ### The three headlines at every `3`-smooth `n`, with the non-constancy hypothesis discharged -/

open Classical in
/-- **Translation-slot bilinearity at every `3`-smooth `n ≠ 0`, with `hprin` the only hypothesis
beyond the setting.**  `exists_weilPairingElt_translatePoint_add_n_of_hprin` with `hn` discharged by
`transcendental_xCoord_nsmul_of_smooth`.

⚠️ The first index this does **not** cover is `n = 5`, exactly as for `exists_gS_of_smooth` and for
`[F(W) : [n]∗F(W)] = n²`, and for the same reason: the argument manufactures no new prime. -/
theorem exists_weilPairingElt_translatePoint_add_of_smooth_of_hprin (h2 : (2 : F) ≠ 0)
    (h3 : (3 : F) ≠ 0) {n : ℕ} (hnz : n ≠ 0) (hfac : ∀ p ∈ n.primeFactors, p = 2 ∨ p = 3)
    {xP yP xQ yQ xR yR xS yS : F} (hP : W.Nonsingular xP yP) (hQ : W.Nonsingular xQ yQ)
    (hR : W.Nonsingular xR yR) (hS : W.Nonsingular xS yS)
    (hmQ : Point.some xQ yQ hQ ∈ W.torsion n) (hmS : Point.some xS yS hS ∈ W.torsion n)
    (hadd : Point.some xP yP hP + Point.some xQ yQ hQ = Point.some xR yR hR)
    (hprin : ∀ f : W.FunctionField, f ≠ 0 →
      divisor W f = Finsupp.single (pointClosedPoint hS.left) (n : ℤ) →
      ∃ g₀ : W.FunctionField, g₀ ≠ 0 ∧
        n • divisor W g₀ =
          divisor W (mulByNEndo n (transcendental_xCoord_nsmul_of_smooth h2 h3 hnz hfac) f)) :
    ∃ g : W.FunctionField, g ≠ 0 ∧
      (∃ f : W.FunctionField, f ≠ 0 ∧
        divisor W f = Finsupp.single (pointClosedPoint hS.left) (n : ℤ) ∧
        ∃ u : W.CoordinateRingˣ, (u : W.CoordinateRing) • g ^ n
          = mulByNEndo n (transcendental_xCoord_nsmul_of_smooth h2 h3 hnz hfac) f) ∧
      weilPairingElt hR.left g = weilPairingElt hP.left g * weilPairingElt hQ.left g :=
  exists_weilPairingElt_translatePoint_add_n_of_hprin _ hnz hP hQ hR hS hmQ hmS hadd hprin

open Classical in
/-- **Translation-slot bilinearity in `μ_n(F)` at every `3`-smooth `n ≠ 0`.**  The `μ` mirror of
`exists_weilPairingElt_translatePoint_add_of_smooth_of_hprin`.

⚠️ This one takes `[NeZero n]` where its `F(W)`-level sibling takes `hnz : n ≠ 0`, and the asymmetry
is forced rather than chosen: `weilPairingMu` occurs in the **statement** and needs the instance to
elaborate, so it cannot be produced inside the proof.  `NeZero.ne n` recovers `n ≠ 0` for the
transcendence bridge.  The general-`n` headlines split the same way, for the same reason. -/
theorem exists_weilPairingMu_translatePoint_add_of_smooth_of_hprin (h2 : (2 : F) ≠ 0)
    (h3 : (3 : F) ≠ 0) {n : ℕ} [NeZero n] (hfac : ∀ p ∈ n.primeFactors, p = 2 ∨ p = 3)
    {xP yP xQ yQ xR yR xS yS : F} (hP : W.Nonsingular xP yP) (hQ : W.Nonsingular xQ yQ)
    (hR : W.Nonsingular xR yR) (hS : W.Nonsingular xS yS)
    (hmP : Point.some xP yP hP ∈ W.torsion n) (hmQ : Point.some xQ yQ hQ ∈ W.torsion n)
    (hmS : Point.some xS yS hS ∈ W.torsion n)
    (hadd : Point.some xP yP hP + Point.some xQ yQ hQ = Point.some xR yR hR)
    (hprin : ∀ f : W.FunctionField, f ≠ 0 →
      divisor W f = Finsupp.single (pointClosedPoint hS.left) (n : ℤ) →
      ∃ g₀ : W.FunctionField, g₀ ≠ 0 ∧
        n • divisor W g₀ = divisor W
          (mulByNEndo n (transcendental_xCoord_nsmul_of_smooth h2 h3 (NeZero.ne n) hfac) f)) :
    ∃ g : W.FunctionField, g ≠ 0 ∧
      (∃ f : W.FunctionField, f ≠ 0 ∧
        divisor W f = Finsupp.single (pointClosedPoint hS.left) (n : ℤ) ∧
        ∃ u : W.CoordinateRingˣ, (u : W.CoordinateRing) • g ^ n
          = mulByNEndo n (transcendental_xCoord_nsmul_of_smooth h2 h3 (NeZero.ne n) hfac) f) ∧
      ∃ hpowP : weilPairingElt hP.left g ^ n = 1,
        ∃ hpowQ : weilPairingElt hQ.left g ^ n = 1,
          ∃ hpowR : weilPairingElt hR.left g ^ n = 1,
            weilPairingMu hR.left hpowR
              = weilPairingMu hP.left hpowP * weilPairingMu hQ.left hpowQ :=
  exists_weilPairingMu_translatePoint_add_n_of_hprin _ hP hQ hR hS hmP hmQ hmS hadd hprin

open Classical in
/-- **`e_n(S, ·) : E[n] → μ_n(F)` is a group homomorphism at every `3`-smooth `n ≠ 0`.**  The
bundled-hom mirror of the two above, and the sharpest of the three: its conclusion names the whole
of `E[n]` as a group. -/
theorem exists_weilPairingTorsionMuHom_of_smooth_of_hprin (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0)
    {n : ℕ} (hnz : n ≠ 0) (hfac : ∀ p ∈ n.primeFactors, p = 2 ∨ p = 3) {xS yS : F}
    (hS : W.Nonsingular xS yS) (hmS : Point.some xS yS hS ∈ W.torsion n)
    (hprin : ∀ f : W.FunctionField, f ≠ 0 →
      divisor W f = Finsupp.single (pointClosedPoint hS.left) (n : ℤ) →
      ∃ g₀ : W.FunctionField, g₀ ≠ 0 ∧
        n • divisor W g₀ =
          divisor W (mulByNEndo n (transcendental_xCoord_nsmul_of_smooth h2 h3 hnz hfac) f)) :
    ∃ g : W.FunctionField, g ≠ 0 ∧
      (∃ f : W.FunctionField, f ≠ 0 ∧
        divisor W f = Finsupp.single (pointClosedPoint hS.left) (n : ℤ) ∧
        ∃ u : W.CoordinateRingˣ, (u : W.CoordinateRing) • g ^ n
          = mulByNEndo n (transcendental_xCoord_nsmul_of_smooth h2 h3 hnz hfac) f) ∧
      ∃ φ : Multiplicative (W.torsion n) →* rootsOfUnity n F, ∀ P : W.torsion n,
        algebraMap F W.FunctionField ((φ (Multiplicative.ofAdd P) : Fˣ) : F)
          = weilPairingPointElt g (P : W.Point) :=
  have : NeZero n := ⟨hnz⟩
  exists_weilPairingTorsionMuHom_n_of_hprin _ hS hmS hprin

/-! ### Recovery of the six merged headlines

⚠️ Each statement below is its merged twin **verbatim**, and each is proved *through* the general
form rather than re-proved.  This is the check that distinguishes a faithful generalisation from a
new statement that resembles one; the elaborator does it, so no reader has to take *"the proofs are
the merged proofs with the numeral removed"* on faith.

⚠️ All six are `private`: public copies would duplicate merged names. -/

section Recovery

open Classical in
/-- `exists_weilPairingElt_translatePoint_add_two_of_hprin`, recovered.

⚠️ `Nat.cast_ofNat` is not decoration: the general form writes the divisor coefficient as
`((2 : ℕ) : ℤ)` and the merged statement writes `(2 : ℤ)`, so without it **both** the hypothesis and
the conclusion fail to match. -/
private theorem exists_weilPairingElt_translatePoint_add_two_of_general (h2 : (2 : F) ≠ 0)
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
  have key := exists_weilPairingElt_translatePoint_add_n_of_hprin
    (transcendental_xCoord_two_nsmul (W := W) h2) two_ne_zero hP hQ hR hS hmQ hmS hadd
    (by simpa only [mulByNEndo_two h2, Nat.cast_ofNat] using hprin)
  simpa only [mulByNEndo_two h2, Nat.cast_ofNat] using key

open Classical in
/-- `exists_weilPairingElt_translatePoint_add_three_of_hprin`, recovered, through
`mulByNEndo_three`. -/
private theorem exists_weilPairingElt_translatePoint_add_three_of_general (h2 : (2 : F) ≠ 0)
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
  have key := exists_weilPairingElt_translatePoint_add_n_of_hprin
    (transcendental_xCoord_three_nsmul (W := W) h2 h3) three_ne_zero hP hQ hR hS hmQ hmS hadd
    (by simpa only [mulByNEndo_three h2 h3, Nat.cast_ofNat] using hprin)
  simpa only [mulByNEndo_three h2 h3, Nat.cast_ofNat] using key

open Classical in
/-- `exists_weilPairingMu_translatePoint_add_two_of_hprin`, recovered. -/
private theorem exists_weilPairingMu_translatePoint_add_two_of_general (h2 : (2 : F) ≠ 0)
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
  have key := exists_weilPairingMu_translatePoint_add_n_of_hprin
    (transcendental_xCoord_two_nsmul (W := W) h2) hP hQ hR hS hmP hmQ hmS hadd
    (by simpa only [mulByNEndo_two h2, Nat.cast_ofNat] using hprin)
  simpa only [mulByNEndo_two h2, Nat.cast_ofNat] using key

open Classical in
/-- `exists_weilPairingMu_translatePoint_add_three_of_hprin`, recovered. -/
private theorem exists_weilPairingMu_translatePoint_add_three_of_general (h2 : (2 : F) ≠ 0)
    (h3 : (3 : F) ≠ 0) {xP yP xQ yQ xR yR xS yS : F} (hP : W.Nonsingular xP yP)
    (hQ : W.Nonsingular xQ yQ) (hR : W.Nonsingular xR yR) (hS : W.Nonsingular xS yS)
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
  have key := exists_weilPairingMu_translatePoint_add_n_of_hprin
    (transcendental_xCoord_three_nsmul (W := W) h2 h3) hP hQ hR hS hmP hmQ hmS hadd
    (by simpa only [mulByNEndo_three h2 h3, Nat.cast_ofNat] using hprin)
  simpa only [mulByNEndo_three h2 h3, Nat.cast_ofNat] using key

open Classical in
/-- `exists_weilPairingTorsionMuHom_two_of_hprin`, recovered. -/
private theorem exists_weilPairingTorsionMuHom_two_of_general (h2 : (2 : F) ≠ 0) {xS yS : F}
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
  have key := exists_weilPairingTorsionMuHom_n_of_hprin
    (transcendental_xCoord_two_nsmul (W := W) h2) hS hmS
    (by simpa only [mulByNEndo_two h2, Nat.cast_ofNat] using hprin)
  simpa only [mulByNEndo_two h2, Nat.cast_ofNat] using key

open Classical in
/-- `exists_weilPairingTorsionMuHom_three_of_hprin`, recovered. -/
private theorem exists_weilPairingTorsionMuHom_three_of_general (h2 : (2 : F) ≠ 0)
    (h3 : (3 : F) ≠ 0) {xS yS : F} (hS : W.Nonsingular xS yS)
    (hmS : Point.some xS yS hS ∈ W.torsion 3)
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
  have key := exists_weilPairingTorsionMuHom_n_of_hprin
    (transcendental_xCoord_three_nsmul (W := W) h2 h3) hS hmS
    (by simpa only [mulByNEndo_three h2 h3, Nat.cast_ofNat] using hprin)
  simpa only [mulByNEndo_three h2 h3, Nat.cast_ofNat] using key

end Recovery

/-! ### Non-vacuity at `n = 4`, over `ℚ`

⚠️ The base field is **`ℚ`**, which is not algebraically closed, so neither the merged headlines nor
the twin file's `AlgClosedRecovery` block applies to it — and `n = 4` is an index no merged
rung-5 or rung-6 statement reaches at all.

`y² = x³ − x` has three rational `2`-torsion points `(0, 0)`, `(1, 0)`, `(−1, 0)`; each is
`4`-torsion because `4 • X = 2 • (2 • X)`, and `exampleAdd` verifies `(0, 0) ⊕ (1, 0) = (−1, 0)` by
Mathlib's secant formula.  So `P`, `Q`, `R` are named, distinct and rational.  The divisor point `S`
is a free variable of the statement and is taken to be `P`.

⚠️ `hprin` remains a hypothesis here, exactly as it does at `n = 2, 3` over a general field.  What
these certificates establish is that every *other* hypothesis — `3`-smoothness at a composite index,
the elliptic instance, non-singularity, `n`-torsion at three distinct points and the group relation
between them — is inhabited outside `{2, 3}`. -/

section Nonvacuity

private lemma exampleTwo : (2 : ℚ) ≠ 0 := by norm_num

private lemma exampleThree : (3 : ℚ) ≠ 0 := by norm_num

/-- `4` is `3`-smooth.  ⚠️ Not `by decide`: the `Decidable` instance for the bounded quantifier over
`primeFactors` gets stuck (`#1213`).  This is `NthRootOfPullbackN`'s `primeFactors_four` idiom. -/
private lemma primeFactorsFour : ∀ p ∈ (4 : ℕ).primeFactors, p = 2 ∨ p = 3 := by
  intro p hp
  obtain ⟨hpp, hdvd, -⟩ := Nat.mem_primeFactors.mp hp
  rw [show (4 : ℕ) = 2 ^ 2 from rfl] at hdvd
  exact Or.inl ((Nat.prime_dvd_prime_iff_eq hpp Nat.prime_two).mp (hpp.dvd_of_dvd_pow hdvd))

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
private lemma exampleTorTwoP : Point.some (0 : ℚ) 0 exampleNsP ∈ exampleCurve.torsion 2 :=
  (mem_torsion_two_some_iff exampleNsP).mpr (by norm_num [exampleCurve])

open Classical in
private lemma exampleTorTwoQ : Point.some (1 : ℚ) 0 exampleNsQ ∈ exampleCurve.torsion 2 :=
  (mem_torsion_two_some_iff exampleNsQ).mpr (by norm_num [exampleCurve])

open Classical in
private lemma exampleTorTwoR : Point.some (-1 : ℚ) 0 exampleNsR ∈ exampleCurve.torsion 2 :=
  (mem_torsion_two_some_iff exampleNsR).mpr (by norm_num [exampleCurve])

open Classical in
/-- `(0, 0)` is `4`-torsion because it is `2`-torsion: `4 • X = 2 • (2 • X)`. -/
private lemma exampleTorFourP : Point.some (0 : ℚ) 0 exampleNsP ∈ exampleCurve.torsion 4 := by
  rw [mem_torsion_iff, show (4 : ℕ) = 2 * 2 from rfl, mul_nsmul,
    mem_torsion_iff.mp exampleTorTwoP, smul_zero]

open Classical in
private lemma exampleTorFourQ : Point.some (1 : ℚ) 0 exampleNsQ ∈ exampleCurve.torsion 4 := by
  rw [mem_torsion_iff, show (4 : ℕ) = 2 * 2 from rfl, mul_nsmul,
    mem_torsion_iff.mp exampleTorTwoQ, smul_zero]

open Classical in
private lemma exampleTorFourR : Point.some (-1 : ℚ) 0 exampleNsR ∈ exampleCurve.torsion 4 := by
  rw [mem_torsion_iff, show (4 : ℕ) = 2 * 2 from rfl, mul_nsmul,
    mem_torsion_iff.mp exampleTorTwoR, smul_zero]

/-- `(0, 0) ⊕ (1, 0) = (−1, 0)` on `y² = x³ − x` over `ℚ`.  The `x`-coordinates differ, so this is
Mathlib's secant case: the slope is `0`, `addX = −1` and `addY = 0`. -/
private lemma exampleAdd : Point.some (0 : ℚ) 0 exampleNsP + Point.some (1 : ℚ) 0 exampleNsQ
    = Point.some (-1 : ℚ) 0 exampleNsR := by
  rw [Point.add_of_X_ne (by norm_num)]
  norm_num [WeierstrassCurve.Affine.addX, WeierstrassCurve.Affine.addY,
    WeierstrassCurve.Affine.negAddY, WeierstrassCurve.Affine.negY,
    WeierstrassCurve.Affine.slope, exampleCurve]

open Classical in
/-- **Translation-slot bilinearity applies at `n = 4` on a curve over `ℚ`**, at three distinct
rational `4`-torsion translation points, with `hprin` the only hypothesis left.

⚠️ **Every `by convert` is load-bearing.**  `ℚ` has a genuine `DecidableEq` instance, so anything
stated over `ℚ` is indexed by `instDecidableEqRat`, while the headline — stated for a general `F`
under `open Classical in` — is indexed by `Classical.propDecidable`, a *low-priority* local
instance.  The objects are propositionally but not syntactically equal and `convert` closes each gap
by `Subsingleton.elim`.  It bites in the `torsion` memberships and in the `Point.instAdd` inside
`hadd`, but **not** inside `hprin`, which mentions no `torsion` membership — the point-local shape
of `hprin` showing through again. -/
example (hprin : ∀ f : exampleCurve.FunctionField, f ≠ 0 →
      divisor exampleCurve f = Finsupp.single (pointClosedPoint exampleNsP.left) (4 : ℤ) →
      ∃ g₀ : exampleCurve.FunctionField, g₀ ≠ 0 ∧
        4 • divisor exampleCurve g₀ = divisor exampleCurve (mulByNEndo 4
          (transcendental_xCoord_nsmul_of_smooth exampleTwo exampleThree (by norm_num)
            primeFactorsFour) f)) :
    ∃ g : exampleCurve.FunctionField, g ≠ 0 ∧
      (∃ f : exampleCurve.FunctionField, f ≠ 0 ∧
        divisor exampleCurve f = Finsupp.single (pointClosedPoint exampleNsP.left) (4 : ℤ) ∧
        ∃ u : exampleCurve.CoordinateRingˣ, (u : exampleCurve.CoordinateRing) • g ^ 4
          = mulByNEndo 4 (transcendental_xCoord_nsmul_of_smooth exampleTwo exampleThree
              (by norm_num) primeFactorsFour) f) ∧
      weilPairingElt exampleNsR.left g
        = weilPairingElt exampleNsP.left g * weilPairingElt exampleNsQ.left g := by
  refine exists_weilPairingElt_translatePoint_add_of_smooth_of_hprin exampleTwo exampleThree
    (n := 4) (by norm_num) primeFactorsFour exampleNsP exampleNsQ exampleNsR exampleNsP
    (by convert exampleTorFourQ) (by convert exampleTorFourP) (by convert exampleAdd) ?_
  simpa only [Nat.cast_ofNat] using hprin

open Classical in
/-- **The `μ_4(ℚ)`-valued form applies at `n = 4` too**, with the three `hpow` data produced rather
than assumed.  ⚠️ `hmP` is needed here and not above; that is a consequence of `weilPairingMu` being
indexed by `hpow`, not of the mathematics changing. -/
example (hprin : ∀ f : exampleCurve.FunctionField, f ≠ 0 →
      divisor exampleCurve f = Finsupp.single (pointClosedPoint exampleNsP.left) (4 : ℤ) →
      ∃ g₀ : exampleCurve.FunctionField, g₀ ≠ 0 ∧
        4 • divisor exampleCurve g₀ = divisor exampleCurve (mulByNEndo 4
          (transcendental_xCoord_nsmul_of_smooth exampleTwo exampleThree (by norm_num)
            primeFactorsFour) f)) :
    ∃ g : exampleCurve.FunctionField, g ≠ 0 ∧
      (∃ f : exampleCurve.FunctionField, f ≠ 0 ∧
        divisor exampleCurve f = Finsupp.single (pointClosedPoint exampleNsP.left) (4 : ℤ) ∧
        ∃ u : exampleCurve.CoordinateRingˣ, (u : exampleCurve.CoordinateRing) • g ^ 4
          = mulByNEndo 4 (transcendental_xCoord_nsmul_of_smooth exampleTwo exampleThree
              (by norm_num) primeFactorsFour) f) ∧
      ∃ hpowP : weilPairingElt exampleNsP.left g ^ 4 = 1,
        ∃ hpowQ : weilPairingElt exampleNsQ.left g ^ 4 = 1,
          ∃ hpowR : weilPairingElt exampleNsR.left g ^ 4 = 1,
            weilPairingMu exampleNsR.left hpowR
              = weilPairingMu exampleNsP.left hpowP * weilPairingMu exampleNsQ.left hpowQ := by
  refine exists_weilPairingMu_translatePoint_add_of_smooth_of_hprin exampleTwo exampleThree
    (n := 4) primeFactorsFour exampleNsP exampleNsQ exampleNsR exampleNsP
    (by convert exampleTorFourP) (by convert exampleTorFourQ) (by convert exampleTorFourP)
    (by convert exampleAdd) ?_
  simpa only [Nat.cast_ofNat] using hprin

/-! ⚠️ **The bundled-hom certificate needs more than a `by convert`, and the reason is structural.**
Every `DecidableEq` mismatch above sits in a *hypothesis*, where `convert` bridges it by
`Subsingleton.elim`.  `exists_weilPairingTorsionMuHom_of_smooth_of_hprin`'s **conclusion** names
`E[4]`, and `W.torsion` takes the `DecidableEq F` instance as an argument — so over `ℚ` the two
statements differ in *the type of a bound variable*, which no hypothesis-side conversion can reach.

The fix is the twin file's: state the certificate at the same instance the headline is elaborated
at, by pinning `Classical.propDecidable` for this section only.  ⚠️ Nothing is assumed away —
`DecidableEq ℚ` is a `Subsingleton`, so the pinned instance and `instDecidableEqRat` give the same
subgroup.  It is scoped so that the blocks above keep the `convert` form, which is the one that
generalises. -/

section HomNonvacuity

attribute [local instance 10000] Classical.propDecidable

/-- **`e_4(S, ·) : E[4] → μ_4(ℚ)` is a group homomorphism on a curve over `ℚ`**, with `hprin` the
only hypothesis left.

⚠️ This is the sharpest of the three `ℚ` certificates, because its conclusion names the *whole* of
`E[4]` as a group rather than a finite list of points: the domain is `exampleCurve.torsion 4`, which
over `ℚ` is a proper subgroup of the `F̄`-torsion and is not assumed to be anything in
particular. -/
example (hprin : ∀ f : exampleCurve.FunctionField, f ≠ 0 →
      divisor exampleCurve f = Finsupp.single (pointClosedPoint exampleNsP.left) (4 : ℤ) →
      ∃ g₀ : exampleCurve.FunctionField, g₀ ≠ 0 ∧
        4 • divisor exampleCurve g₀ = divisor exampleCurve (mulByNEndo 4
          (transcendental_xCoord_nsmul_of_smooth exampleTwo exampleThree (by norm_num)
            primeFactorsFour) f)) :
    ∃ g : exampleCurve.FunctionField, g ≠ 0 ∧
      (∃ f : exampleCurve.FunctionField, f ≠ 0 ∧
        divisor exampleCurve f = Finsupp.single (pointClosedPoint exampleNsP.left) (4 : ℤ) ∧
        ∃ u : exampleCurve.CoordinateRingˣ, (u : exampleCurve.CoordinateRing) • g ^ 4
          = mulByNEndo 4 (transcendental_xCoord_nsmul_of_smooth exampleTwo exampleThree
              (by norm_num) primeFactorsFour) f) ∧
      ∃ φ : Multiplicative (exampleCurve.torsion 4) →* rootsOfUnity 4 ℚ,
        ∀ P : exampleCurve.torsion 4,
          algebraMap ℚ exampleCurve.FunctionField ((φ (Multiplicative.ofAdd P) : ℚˣ) : ℚ)
            = weilPairingPointElt g (P : exampleCurve.Point) := by
  refine exists_weilPairingTorsionMuHom_of_smooth_of_hprin exampleTwo exampleThree (n := 4)
    (by norm_num) primeFactorsFour exampleNsP (by convert exampleTorFourP) ?_
  simpa only [Nat.cast_ofNat] using hprin

end HomNonvacuity

end Nonvacuity

end WeierstrassCurve.Affine
