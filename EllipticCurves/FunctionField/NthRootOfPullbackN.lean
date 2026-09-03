/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import EllipticCurves.Fixtures
import EllipticCurves.FunctionField.CoordinateRingNormalGeneral
import EllipticCurves.FunctionField.MulByNComposition
import EllipticCurves.FunctionField.MulByNXCoordFormula
import EllipticCurves.FunctionField.NthRootOfPullback

/-!
# The `n`-th root `g_S` at general `n` (Weil-pairing rung 5)

`EllipticCurves.FunctionField.NthRootOfPullback` builds the rung-5 datum of the divisor-theoretic
Weil pairing — a nonzero `g_S ∈ F(W)` with `u · g_S ^ n = [n]∗ f_S` for a unit `u` of `F[W]` — at
two indices, `exists_gS_two` and `exists_gS_three`.  This file states it at **every** `n`, and
discharges the one side condition at every `3`-smooth `n` **and at every `n` with
`(n : F) ≠ 0`** — two independent routes, the second strictly wider.

## ⚠️ The restriction to `n = 2, 3` was chronological, not mathematical

Strip the numerals from `exists_gS_two` and `exists_gS_three` and the two proof bodies are
byte-identical.  Every input they use is already stated at a general index, and three of them
always were:

| input | generality |
| --- | --- |
| `exists_smul_pow_eq_of_nsmul_divisor`, the `n`-th-root engine | `{m : ℕ}`, arbitrary |
| `exists_generator_divisor_eq_of_torsion` (`PrincipalDivisorOfPoint`) | `{n : ℕ}`, arbitrary |
| `exists_unit_of_nsmul_divisor_eq`, uniqueness up to a unit | `{m : ℕ}`, arbitrary |
| `[n]∗` itself — `mulByNEndo`, `mulByNEndo_injective` (`MulByNPullback`) | arbitrary `n` |
| the non-constancy side condition, `transcendental_xCoord_nsmul_of_smooth` | every `3`-smooth `n` |
| the same, `transcendental_xCoord_nsmul_genericPoint_of_intCast_ne_zero` | every `(n : F) ≠ 0` |

The only gated input to rung 5 is `hprin`, and `hprin` is a **hypothesis** of the statement at every
`n` — it does not get harder as `n` grows, it stays open.  So nothing about the mathematics was
`[2]`- or `[3]`-specific; only `mulByNEndo`'s arrival date was.

## ⚠️ This does NOT subsume `exists_gS_two` / `exists_gS_three`

`mulByNEndo` is built from the **generic point** and so carries `[W.IsElliptic]`.  The merged
statements carry `[IsDedekindDomain W.CoordinateRing]` and **not** `[W.IsElliptic]`.  Being elliptic
supplies the Dedekind instance (`CoordinateRingNormalGeneral.instIsDedekindDomain`) and not
conversely, so the two hypothesis sets are **incomparable**: what is below is more general in `n`
and strictly stronger in the setting.

⚠️ **`exists_gS_two` and `exists_gS_three` are therefore not deprecated, restated or touched.**
They are the general-*curve* statements and remain the right thing to cite at `n = 2, 3`.  Nothing
in this file edits `NthRootOfPullback.lean`.

The extra instance costs nothing in practice, and that is measured rather than asserted: of the
**18** files that name `exists_gS_two` / `exists_gS_three`, **16** carry a
`variable … [W.IsElliptic]`.  The two that do not are `NthRootOfPullback.lean` itself and
`PullbackTorsionDivisor.lean`, whose two hits are both **prose** (`:87` and `:124` there).  No
existing consumer would lose anything by citing the general form instead.

## Main statements

* `WeierstrassCurve.Affine.exists_gS_n` — rung 5 at an arbitrary `n`, with the non-constancy of
  `[n]` taken as the explicit hypothesis `hn`.
* `WeierstrassCurve.Affine.exists_gS_of_smooth` — rung 5 at every `3`-smooth `n ≠ 0`, with `hn`
  **discharged**.  This is the first rung-5 statement on this board that reaches an index other than
  `2` and `3`.
* `WeierstrassCurve.Affine.exists_gS_of_ne_zero` — rung 5 at every `n` with `(2 : F) ≠ 0` and
  `((n : ℤ) : F) ≠ 0`, `hn` discharged by the division-polynomial route instead.  ⚠️ **Strictly
  wider**: it reaches `n = 5`, `n = 10` and every other index prime to the characteristic, and the
  `example` beside it derives `exists_gS_of_smooth` from it verbatim, so the containment is
  compiled rather than claimed.

Uniqueness needs nothing new: `exists_unit_of_nsmul_divisor_eq` (`NthRootOfPullback`) already pins
the root up to a unit of `F[W]` at an arbitrary exponent.

## ⚠️ What is NOT here, and one corollary that must not be added

* **`hprin` is not discharged at any `n`.**  It is an *existence* statement, and `#899`'s test —
  *is the obstruction used to prove an equality, or to produce a witness?* — puts it firmly on the
  witness side.
* ⚠️ **There is deliberately no `exists_gS_of_smooth_of_isAlgClosed`.**  At `n = 2` and `n = 3`
  `hprin` is discharged over `F̄` by `PullbackPrincipalityTwo` / `PullbackPrincipalityThree`, whose
  input is the fibre description `[n]∗((S) − (O)) = ∑_{R ∈ E[n]} ((P ⊕ R) − (R))` — merged **only**
  at those two indices (`MulByTwoFibreAffine`, `MulByThreeFibre`).  At `3`-smooth `n > 3` no such
  description exists, so a hypothesis-free corollary would be one nothing can feed.  That is the
  vacuity trap, not a gap to fill.
* ⚠️ **`n = 5` IS reached, and this bullet used to say it was not.**  It read *"the ceiling is
  `transcendental_xCoord_nsmul_of_smooth`'s, and behind it stands `#1184`"*, with the hedge that
  *"which of this file's inputs is now the binding one was not re-measured"*.  It has now been
  measured, and the answer is that **nothing stood behind that ceiling**: the side condition is
  `Transcendental F (n • 𝒫).xCoord` and nothing else, and
  `transcendental_xCoord_nsmul_genericPoint_of_intCast_ne_zero`
  (`EllipticCurves.FunctionField.MulByNXCoordFormula`) has proved it at every `n` with
  `(n : F) ≠ 0` since `#1213`.  ⚠️ **`#1184` was never a gate on this file** — it gates
  `isCoprime_ΨSq_adjacent` over an arbitrary commutative ring, and the field case it was cited for
  landed in PR #576.  The cost of the correction was **one `import`**, which is the same shape as
  PR #593's finding that half a `3`-smooth ceiling was a missing import, and PR #599's that the
  pole-order route was a merged citation nobody had consumed.
* **The pairing itself stays at `n = 2, 3`.**  Rung 5 is the `n`-th root; `weilPairingElt` and the
  rung-6 board are limited by their *other* inputs, not by this one.

⚠️ **That pair is paid on both halves, and `#1184` is what is left.**  PR #557 proved the on-curve
identity for `(Φₙ/ΨSqₙ, ωₙ/ψₙ³)` at every index over every commutative ring
(`WeierstrassCurve.Affine.equation_div_of_ψ_ne_zero`, `EllipticCurves.Torsion.OmegaCrux`) — that was
`#404`, and it says only that those coordinates lie on the curve.  Identifying the `x`-coordinate
with the group-law multiple `n • P` is `#251`, and it is **closed**:
`WeierstrassCurve.Affine.hasXCoordFormula_of_two_ne_zero`
(`EllipticCurves.Torsion.NsmulOrder`) at every index over any field with `(2 : F) ≠ 0`, and in
function-field form `nMulRatFunc_eq_ΦDivΨSq`
(`EllipticCurves.FunctionField.MulByNXCoordFormula`) at every `n` with `(n : F) ≠ 0`.  ⚠️ **`#1184`
is untouched** and now stands alone beside `(n : F) ≠ 0`; ⚠️ and the `y`-half — `ωₙ/(2ψₙ³)` as
`y(n • P)` — **is closed too, at every index**: `nsmul_eq_some_omegaY_of_ΨSq_ne_zero`
(`EllipticCurves.Torsion.NsmulYPeriodic`, PR #579), under the same `ΨSqₙ(x) ≠ 0` and `(2 : F) ≠ 0`
the `x`-half asks.  ⚠️ So the whole *pair* is available at every index, and the `#251` bullets on
the Weil-pairing front no longer name an open gate.  ⚠️ `EllipticCurves.Torsion.NsmulOrder` is
cited and not consumed — it is not in this file's import closure.  ⚠️ **`MulByNXCoordFormula` is
now consumed**: this sentence used to say that it too was only cited, and that was exactly the
reason `n = 5` looked unreachable.  The edge costs **10 modules** in the import closure
(`79 → 89`) and cannot cycle — that file names nothing in this one.  The two-reading account is
`EllipticCurves.FunctionField.MulByNPullback`.

## Non-vacuity

Two blocks, answering different questions.

* `Recovery` recovers `exists_gS_two` and `exists_gS_three` **on the nose** — statements identical
  to the merged ones apart from the `[W.IsElliptic]` binder — through `exists_gS_n` and the bridges
  `mulByNEndo_two` / `mulByNEndo_three`.  ⚠️ This is what separates a faithful generalisation from a
  new statement that merely resembles one; both are `private`, since public copies would duplicate
  merged names.
* `Nonvacuity` instantiates `exists_gS_of_smooth` at **`n = 4`**, an index no merged rung-5
  statement reaches, on `y² = x³ − x` over `ℚ` at the `2`-torsion point `(0, 0)` — which is
  `4`-torsion because `4 • P = 2 • (2 • P)`.  ⚠️ `hprin` remains a hypothesis there, exactly as it
  does at `n = 2, 3` over a general field; the certificate says the *other* hypotheses are
  inhabited at a new index, and claims nothing more.
  ⚠️ It then instantiates `exists_gS_of_ne_zero` at **`n = 10`**, on the same curve and at the same
  point.  `10 = 2 · 5` is **even and not `3`-smooth**, so that one is reachable by
  `exists_gS_of_smooth` at no hypotheses at all and by no odd-`n` statement anywhere: it can come
  only from the general theorem, which is what makes it the certificate that can falsify the claim.

## References

* [J. H. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.8.
-/

namespace WeierstrassCurve.Affine

open CoordinateRing

variable {F : Type*} [Field F] {W : Affine F} [W.IsElliptic]

/-! ### Rung 5 at an arbitrary `n` -/

/-- **The rung-5 `n`-th root at an arbitrary `n`.**  For a nonsingular `n`-torsion point
`S = (x, y)`, take the principal function `f_S` of `#409` (`divisor W f_S = n·(S)` on the affine
chart) and its pullback `[n]∗ f_S = mulByNEndo n hn f_S`.  Assuming the effective divisor of the
`n`-th root is principal (`hprin`), there is a nonzero `g_S ∈ F(W)` with
`u · g_S ^ n = mulByNEndo n hn f_S` for a unit `u` of `F[W]`.

`hn` — transcendence of the `x`-coordinate of `n • 𝒫` — is what says `[n]` is non-constant, and is
exactly `mulByNEndo`'s own hypothesis.  `hprin` is the single gated input, as at `n = 2` and
`n = 3`; the proof is the merged one with the numeral removed. -/
theorem exists_gS_n [DecidableEq F] {n : ℕ}
    (hn : Transcendental F ((n • genericPoint (W := W)).xCoord))
    {x y : F} (h : W.Nonsingular x y) (hS : Point.some x y h ∈ W.torsion n)
    (hprin : ∀ f : W.FunctionField, f ≠ 0 →
      divisor W f = Finsupp.single (CoordinateRing.pointClosedPoint h.1) (n : ℤ) →
      ∃ g₀ : W.FunctionField, g₀ ≠ 0 ∧
        n • divisor W g₀ = divisor W (mulByNEndo n hn f)) :
    ∃ f : W.FunctionField, f ≠ 0 ∧
      divisor W f = Finsupp.single (CoordinateRing.pointClosedPoint h.1) (n : ℤ) ∧
      ∃ gS : W.FunctionField, gS ≠ 0 ∧
        ∃ u : W.CoordinateRingˣ, (u : W.CoordinateRing) • gS ^ n = mulByNEndo n hn f := by
  obtain ⟨f, hf, hfdiv⟩ := exists_generator_divisor_eq_of_torsion h hS
  obtain ⟨g₀, hg₀, hdiv⟩ := hprin f hf hfdiv
  have hne : mulByNEndo n hn f ≠ 0 := fun hz =>
    hf (mulByNEndo_injective n hn (by rw [hz, map_zero]))
  exact ⟨f, hf, hfdiv, g₀, hg₀, exists_smul_pow_eq_of_nsmul_divisor hne hg₀ hdiv⟩

/-- **Rung 5 at every `3`-smooth `n ≠ 0`.**  `exists_gS_n` with its non-constancy hypothesis
discharged by `transcendental_xCoord_nsmul_of_smooth`, leaving `hprin` as the only hypothesis
beyond the setting.

⚠️ The first index this does **not** cover is `n = 5`, exactly as for `[F(W) : [n]∗F(W)] = n²`
(`finrank_mulByNFieldRange_of_smooth`) and for the torsion structure theorem, and for the same
reason: the argument manufactures no new prime. -/
theorem exists_gS_of_smooth [DecidableEq F] (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) {n : ℕ}
    (hn : n ≠ 0) (hfac : ∀ p ∈ n.primeFactors, p = 2 ∨ p = 3)
    {x y : F} (h : W.Nonsingular x y) (hS : Point.some x y h ∈ W.torsion n)
    (hprin : ∀ f : W.FunctionField, f ≠ 0 →
      divisor W f = Finsupp.single (CoordinateRing.pointClosedPoint h.1) (n : ℤ) →
      ∃ g₀ : W.FunctionField, g₀ ≠ 0 ∧
        n • divisor W g₀ =
          divisor W (mulByNEndo n (transcendental_xCoord_nsmul_of_smooth h2 h3 hn hfac) f)) :
    ∃ f : W.FunctionField, f ≠ 0 ∧
      divisor W f = Finsupp.single (CoordinateRing.pointClosedPoint h.1) (n : ℤ) ∧
      ∃ gS : W.FunctionField, gS ≠ 0 ∧
        ∃ u : W.CoordinateRingˣ, (u : W.CoordinateRing) • gS ^ n
          = mulByNEndo n (transcendental_xCoord_nsmul_of_smooth h2 h3 hn hfac) f :=
  exists_gS_n _ h hS hprin

/-- **Rung 5 at every `n` with `(n : F) ≠ 0`** — `exists_gS_n` with its non-constancy hypothesis
discharged by `transcendental_xCoord_nsmul_genericPoint_of_intCast_ne_zero`
(`EllipticCurves.FunctionField.MulByNXCoordFormula`) instead of by the `3`-smooth ladder, leaving
`hprin` as the only hypothesis beyond the setting.

⚠️ **Strictly wider than `exists_gS_of_smooth`, and the containment is committed below**: `n = 10`
is here and not there, `n = 12` in characteristic `0` is in both, and the `3`-smooth hypotheses
imply `hn` — the `example` after this proves that statement from this one rather than leaving the
relation to a docstring.  The `_of_smooth` form is nevertheless kept: its proof composes `[2]∗` and
`[3]∗` and touches no division polynomial, so it is an independent route.

⚠️ **`hn` is a condition of this *route*, not a limit on rung 5, and the difference is worth
keeping straight.**  At `n = char F` the map `[n]` is inseparable but still non-constant, so
`Transcendental F (n • 𝒫).xCoord` is **true** there — it is `natDegree_ΨSq` that needs
`(n : F) ≠ 0`, and over an algebraically closed field `transcendental_xCoord_nsmul_of_isAlgClosed`
(`EllipticCurves.FunctionField.MulByNTranscendence`) discharges the same side condition at every
`n ≠ 0`, characteristic included.  ⚠️ That third route is deliberately **not** given a name here:
it widens the *setting* axis rather than the index axis, and this file's *"does NOT subsume"*
section is the account of why those two axes do not compare.  `exists_gS_n` remains the statement
to cite when the transcendence proof is in hand.

⚠️ This does **not** discharge `hprin` at any index — see the module docstring's *"what is NOT
here"* section, which is unchanged by this. -/
theorem exists_gS_of_ne_zero [DecidableEq F] (h2 : (2 : F) ≠ 0) {n : ℕ}
    (hn : ((n : ℤ) : F) ≠ 0)
    {x y : F} (h : W.Nonsingular x y) (hS : Point.some x y h ∈ W.torsion n)
    (hprin : ∀ f : W.FunctionField, f ≠ 0 →
      divisor W f = Finsupp.single (CoordinateRing.pointClosedPoint h.1) (n : ℤ) →
      ∃ g₀ : W.FunctionField, g₀ ≠ 0 ∧
        n • divisor W g₀ =
          divisor W (mulByNEndo n
            (transcendental_xCoord_nsmul_genericPoint_of_intCast_ne_zero h2 hn) f)) :
    ∃ f : W.FunctionField, f ≠ 0 ∧
      divisor W f = Finsupp.single (CoordinateRing.pointClosedPoint h.1) (n : ℤ) ∧
      ∃ gS : W.FunctionField, gS ≠ 0 ∧
        ∃ u : W.CoordinateRingˣ, (u : W.CoordinateRing) • gS ^ n
          = mulByNEndo n (transcendental_xCoord_nsmul_genericPoint_of_intCast_ne_zero h2 hn) f :=
  exists_gS_n _ h hS hprin

/-! ### The subsumption of the `3`-smooth layer, machine-checked

⚠️ **The containment between the two layers is committed here rather than asserted in a
docstring**, following `EllipticCurves.FunctionField.MulByNPlaceComposition` and
`EllipticCurves.TateModule.OpenKernel`, which do the same on their fronts and say why:
`(2 : F) ≠ 0`, `(3 : F) ≠ 0`, `n ≠ 0` and `3`-smoothness force `((n : ℤ) : F) ≠ 0` in a field, so
`exists_gS_of_smooth` is a corollary of `exists_gS_of_ne_zero`.

⚠️ **Nothing above is deleted, and the reason is not compatibility.**  The `_of_smooth` route runs
`[m · n]∗ = [m]∗ ∘ [n]∗` against the merged `n = 2` and `n = 3` layers and consumes no division
polynomial at all; the `_of_ne_zero` route goes through `Φₙ`/`ΨSqₙ`.  Two independent routes to one
conclusion are the cheapest cross-check available on this front. -/

/-- **A `3`-smooth `n ≠ 0` is prime to the characteristic as soon as `2` and `3` are** — the
`((n : ℤ) : K)` form, stated over a fresh field `K` so that no section variable is drawn in.

⚠️ Deliberately a copy rather than a cross-file citation: the twin in
`EllipticCurves.FunctionField.MulByNPlaceComposition` is `private` there, and that file is **not**
in this one's import closure. -/
private lemma intCastNthRoot_ne_zero_of_smooth {K : Type*} [Field K] (h2 : (2 : K) ≠ 0)
    (h3 : (3 : K) ≠ 0) {n : ℕ} (hn : n ≠ 0) (hfac : ∀ p ∈ n.primeFactors, p = 2 ∨ p = 3) :
    ((n : ℤ) : K) ≠ 0 := by
  obtain ⟨a, b, rfl⟩ := Nat.exists_eq_two_pow_mul_three_pow n hn hfac
  push_cast
  exact mul_ne_zero (pow_ne_zero _ h2) (pow_ne_zero _ h3)

/-- **`exists_gS_of_smooth` is a corollary of `exists_gS_of_ne_zero`** — its statement verbatim,
proved from the general layer.  ⚠️ The two `mulByNEndo` terms carry *different* transcendence
proofs, and they are interchangeable because `Transcendental` is a `Prop`; that is what makes the
`example` typecheck at all, and it is the trap `EllipticCurves.FunctionField.MulByNDegreeGeneral`
records at its own `:72-76`. -/
example [DecidableEq F] (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) {n : ℕ} (hn : n ≠ 0)
    (hfac : ∀ p ∈ n.primeFactors, p = 2 ∨ p = 3)
    {x y : F} (h : W.Nonsingular x y) (hS : Point.some x y h ∈ W.torsion n)
    (hprin : ∀ f : W.FunctionField, f ≠ 0 →
      divisor W f = Finsupp.single (CoordinateRing.pointClosedPoint h.1) (n : ℤ) →
      ∃ g₀ : W.FunctionField, g₀ ≠ 0 ∧
        n • divisor W g₀ =
          divisor W (mulByNEndo n (transcendental_xCoord_nsmul_of_smooth h2 h3 hn hfac) f)) :
    ∃ f : W.FunctionField, f ≠ 0 ∧
      divisor W f = Finsupp.single (CoordinateRing.pointClosedPoint h.1) (n : ℤ) ∧
      ∃ gS : W.FunctionField, gS ≠ 0 ∧
        ∃ u : W.CoordinateRingˣ, (u : W.CoordinateRing) • gS ^ n
          = mulByNEndo n (transcendental_xCoord_nsmul_of_smooth h2 h3 hn hfac) f :=
  exists_gS_of_ne_zero h2 (intCastNthRoot_ne_zero_of_smooth h2 h3 hn hfac) h hS hprin

/-! ### Recovery of the merged `n = 2` and `n = 3` statements -/

section Recovery

/-- **`exists_gS_two` recovered from `exists_gS_n`.**  The statement is the merged one verbatim, the
`[W.IsElliptic]` binder of this file aside; the proof goes through the general theorem and the
bridge `mulByNEndo_two`.

⚠️ `Nat.cast_ofNat` is not decoration: `exists_gS_n` writes the divisor coefficient as
`((2 : ℕ) : ℤ)` and the merged statement writes `(2 : ℤ)`, so without it both the hypothesis and
the conclusion fail to match. -/
private theorem exists_gS_two_of_general [DecidableEq F] (h2 : (2 : F) ≠ 0) {x y : F}
    (h : W.Nonsingular x y) (hP : Point.some x y h ∈ W.torsion 2)
    (hprin : ∀ f : W.FunctionField, f ≠ 0 →
      divisor W f = Finsupp.single (CoordinateRing.pointClosedPoint h.1) (2 : ℤ) →
      ∃ g₀ : W.FunctionField, g₀ ≠ 0 ∧
        2 • divisor W g₀ = divisor W (mulByTwoEndo h2 f)) :
    ∃ f : W.FunctionField, f ≠ 0 ∧
      divisor W f = Finsupp.single (CoordinateRing.pointClosedPoint h.1) (2 : ℤ) ∧
      ∃ gS : W.FunctionField, gS ≠ 0 ∧
        ∃ u : W.CoordinateRingˣ, (u : W.CoordinateRing) • gS ^ 2 = mulByTwoEndo h2 f := by
  have key := exists_gS_n (transcendental_xCoord_two_nsmul (W := W) h2) h hP
    (by simpa only [mulByNEndo_two h2, Nat.cast_ofNat] using hprin)
  simpa only [mulByNEndo_two h2, Nat.cast_ofNat] using key

/-- **`exists_gS_three` recovered from `exists_gS_n`**, by the same route through
`mulByNEndo_three`. -/
private theorem exists_gS_three_of_general [DecidableEq F] (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0)
    {x y : F} (h : W.Nonsingular x y) (hP : Point.some x y h ∈ W.torsion 3)
    (hprin : ∀ f : W.FunctionField, f ≠ 0 →
      divisor W f = Finsupp.single (CoordinateRing.pointClosedPoint h.1) (3 : ℤ) →
      ∃ g₀ : W.FunctionField, g₀ ≠ 0 ∧
        3 • divisor W g₀ = divisor W (mulByThreeEndo h2 h3 f)) :
    ∃ f : W.FunctionField, f ≠ 0 ∧
      divisor W f = Finsupp.single (CoordinateRing.pointClosedPoint h.1) (3 : ℤ) ∧
      ∃ gS : W.FunctionField, gS ≠ 0 ∧
        ∃ u : W.CoordinateRingˣ, (u : W.CoordinateRing) • gS ^ 3 = mulByThreeEndo h2 h3 f := by
  have key := exists_gS_n (transcendental_xCoord_three_nsmul (W := W) h2 h3) h hP
    (by simpa only [mulByNEndo_three h2 h3, Nat.cast_ofNat] using hprin)
  simpa only [mulByNEndo_three h2 h3, Nat.cast_ofNat] using key

end Recovery

/-! ### Non-vacuity at `n = 4` -/

section Nonvacuity

private lemma exampleTwo : (2 : ℚ) ≠ 0 := by norm_num

private lemma exampleThree : (3 : ℚ) ≠ 0 := by norm_num

/-- Every prime factor of `4 = 2²` is `2` or `3`.

⚠️ **Not `by decide`**: the `Decidable` instance for `∀ p ∈ Nat.primeFactors 4, p = 2 ∨ p = 3` gets
stuck rather than reducing, exactly as `EllipticCurves.Torsion.ThreePrimary` records at `72`.  This
is that file's `primeFactors_seventytwo` idiom at a smaller index. -/
private lemma primeFactors_four : ∀ p ∈ (4 : ℕ).primeFactors, p = 2 ∨ p = 3 := by
  intro p hp
  obtain ⟨hpp, hdvd, -⟩ := Nat.mem_primeFactors.mp hp
  rw [show (4 : ℕ) = 2 ^ 2 from rfl] at hdvd
  exact Or.inl ((Nat.prime_dvd_prime_iff_eq hpp Nat.prime_two).mp (hpp.dvd_of_dvd_pow hdvd))

/-! The certificate curve `y² = x³ − x` is the shared `EllipticCurves.Fixture.y2EqX3SubX`, whose
single `[CharZero F]` instance also supplies `IsElliptic` here. -/

open EllipticCurves.Fixture

private lemma exampleNsP : (y2EqX3SubX ℚ).Nonsingular 0 0 :=
  (y2EqX3SubX ℚ).equation_iff_nonsingular.mp (by
    norm_num [y2EqX3SubX, WeierstrassCurve.Affine.equation_iff])

open Classical in
private lemma exampleTorTwo : Point.some (0 : ℚ) 0 exampleNsP ∈ (y2EqX3SubX ℚ).torsion 2 :=
  (mem_torsion_two_some_iff exampleNsP).mpr (by norm_num [y2EqX3SubX])

open Classical in
/-- `(0, 0)` is `4`-torsion because it is `2`-torsion: `4 • P = 2 • (2 • P)`. -/
private lemma exampleTorFour : Point.some (0 : ℚ) 0 exampleNsP ∈ (y2EqX3SubX ℚ).torsion 4 := by
  rw [mem_torsion_iff, show (4 : ℕ) = 2 * 2 from rfl, mul_nsmul,
    mem_torsion_iff.mp exampleTorTwo, smul_zero]

open Classical in
/-- **Rung 5 applies at `n = 4`**, an index no merged rung-5 statement reaches, on `y² = x³ − x`
over `ℚ` at the point `(0, 0)`.

⚠️ `hprin` is still a hypothesis, exactly as it is at `n = 2` and `n = 3` over a general field.
What this certifies is that every *other* hypothesis of `exists_gS_of_smooth` — `3`-smoothness at a
composite index, the elliptic instance, non-singularity, and `n`-torsion — is inhabited at an index
outside `{2, 3}`.  It does not certify that `hprin` can be met there; it cannot be, at present. -/
private theorem exampleGSFour
    (hprin : ∀ f : (y2EqX3SubX ℚ).FunctionField, f ≠ 0 →
      divisor (y2EqX3SubX ℚ) f
          = Finsupp.single (CoordinateRing.pointClosedPoint exampleNsP.1) (4 : ℤ) →
      ∃ g₀ : (y2EqX3SubX ℚ).FunctionField, g₀ ≠ 0 ∧
        4 • divisor (y2EqX3SubX ℚ) g₀ = divisor (y2EqX3SubX ℚ) (mulByNEndo 4
          (transcendental_xCoord_nsmul_of_smooth exampleTwo exampleThree
            (by norm_num) primeFactors_four) f)) :
    ∃ f : (y2EqX3SubX ℚ).FunctionField, f ≠ 0 ∧
      divisor (y2EqX3SubX ℚ) f
          = Finsupp.single (CoordinateRing.pointClosedPoint exampleNsP.1) (4 : ℤ) ∧
      ∃ gS : (y2EqX3SubX ℚ).FunctionField, gS ≠ 0 ∧
        ∃ u : (y2EqX3SubX ℚ).CoordinateRingˣ, (u : (y2EqX3SubX ℚ).CoordinateRing) • gS ^ 4
          = mulByNEndo 4 (transcendental_xCoord_nsmul_of_smooth exampleTwo exampleThree
              (by norm_num) primeFactors_four) f := by
  simpa only [Nat.cast_ofNat] using
    exists_gS_of_smooth exampleTwo exampleThree (n := 4) (by norm_num) primeFactors_four
      exampleNsP exampleTorFour (by simpa only [Nat.cast_ofNat] using hprin)

open Classical in
/-- `(0, 0)` is `10`-torsion because it is `2`-torsion: `10 • P = 5 • (2 • P)`.

⚠️ `mul_nsmul` reads `(m * n) • a = n • m • a`, so the factorisation has to be written `2 * 5` for
the inner multiple to be the `2` that `exampleTorTwo` kills; `4 = 2 * 2` above cannot see the
difference. -/
private lemma exampleTorTen : Point.some (0 : ℚ) 0 exampleNsP ∈ (y2EqX3SubX ℚ).torsion 10 := by
  rw [mem_torsion_iff, show (10 : ℕ) = 2 * 5 from rfl, mul_nsmul,
    mem_torsion_iff.mp exampleTorTwo, smul_zero]

open Classical in
/-- **Rung 5 applies at `n = 10`**, on the same curve and at the same point as the `n = 4`
certificate above.

⚠️ `10 = 2 · 5` is **even and not `3`-smooth**, so this certificate is reachable by
`exists_gS_of_smooth` at no hypotheses whatsoever, and by nothing odd-`n` anywhere: it can come
only from `exists_gS_of_ne_zero` by name.  That is what makes it the load-bearing one — `n = 5`
alone would be consistent with a `{2, 3, 5}`-parametrised statement.

⚠️ `hprin` is still a hypothesis, exactly as at `n = 2`, `n = 3` and `n = 4`.  What is certified is
that every *other* hypothesis of `exists_gS_of_ne_zero` is inhabited at an index outside the
`3`-smooth class. -/
private theorem exampleGSTen
    (hprin : ∀ f : (y2EqX3SubX ℚ).FunctionField, f ≠ 0 →
      divisor (y2EqX3SubX ℚ) f
          = Finsupp.single (CoordinateRing.pointClosedPoint exampleNsP.1) (10 : ℤ) →
      ∃ g₀ : (y2EqX3SubX ℚ).FunctionField, g₀ ≠ 0 ∧
        10 • divisor (y2EqX3SubX ℚ) g₀ = divisor (y2EqX3SubX ℚ) (mulByNEndo 10
          (transcendental_xCoord_nsmul_genericPoint_of_intCast_ne_zero exampleTwo
            (by norm_num)) f)) :
    ∃ f : (y2EqX3SubX ℚ).FunctionField, f ≠ 0 ∧
      divisor (y2EqX3SubX ℚ) f
          = Finsupp.single (CoordinateRing.pointClosedPoint exampleNsP.1) (10 : ℤ) ∧
      ∃ gS : (y2EqX3SubX ℚ).FunctionField, gS ≠ 0 ∧
        ∃ u : (y2EqX3SubX ℚ).CoordinateRingˣ, (u : (y2EqX3SubX ℚ).CoordinateRing) • gS ^ 10
          = mulByNEndo 10 (transcendental_xCoord_nsmul_genericPoint_of_intCast_ne_zero exampleTwo
              (by norm_num)) f := by
  simpa only [Nat.cast_ofNat] using
    exists_gS_of_ne_zero exampleTwo (n := 10) (by norm_num) exampleNsP exampleTorTen
      (by simpa only [Nat.cast_ofNat] using hprin)

end Nonvacuity

end WeierstrassCurve.Affine
