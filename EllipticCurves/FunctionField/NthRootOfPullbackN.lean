/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import EllipticCurves.FunctionField.CoordinateRingNormalGeneral
import EllipticCurves.FunctionField.MulByNComposition
import EllipticCurves.FunctionField.NthRootOfPullback

/-!
# The `n`-th root `g_S` at general `n` (Weil-pairing rung 5)

`EllipticCurves.FunctionField.NthRootOfPullback` builds the rung-5 datum of the divisor-theoretic
Weil pairing — a nonzero `g_S ∈ F(W)` with `u · g_S ^ n = [n]∗ f_S` for a unit `u` of `F[W]` — at
two indices, `exists_gS_two` and `exists_gS_three`.  This file states it at **every** `n`, and
discharges the one side condition at every `3`-smooth `n`.

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
* **`n = 5` is not reached.**  The ceiling is `transcendental_xCoord_nsmul_of_smooth`'s, and behind
  it stand `#404`/`#251` and `#1184`.  This file moves nothing there.
* **The pairing itself stays at `n = 2, 3`.**  Rung 5 is the `n`-th root; `weilPairingElt` and the
  rung-6 board are limited by their *other* inputs, not by this one.

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

/-- The curve `y² = x³ − x` over `ℚ`, of discriminant `64`. -/
private noncomputable def exampleCurve : Affine ℚ := ⟨0, 0, 0, -1, 0⟩

private instance : exampleCurve.IsElliptic := by
  rw [WeierstrassCurve.isElliptic_iff, isUnit_iff_ne_zero]
  norm_num [exampleCurve, WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈]

private lemma exampleNsP : exampleCurve.Nonsingular 0 0 :=
  exampleCurve.equation_iff_nonsingular.mp (by
    norm_num [exampleCurve, WeierstrassCurve.Affine.equation_iff])

open Classical in
private lemma exampleTorTwo : Point.some (0 : ℚ) 0 exampleNsP ∈ exampleCurve.torsion 2 :=
  (mem_torsion_two_some_iff exampleNsP).mpr (by norm_num [exampleCurve])

open Classical in
/-- `(0, 0)` is `4`-torsion because it is `2`-torsion: `4 • P = 2 • (2 • P)`. -/
private lemma exampleTorFour : Point.some (0 : ℚ) 0 exampleNsP ∈ exampleCurve.torsion 4 := by
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
    (hprin : ∀ f : exampleCurve.FunctionField, f ≠ 0 →
      divisor exampleCurve f
          = Finsupp.single (CoordinateRing.pointClosedPoint exampleNsP.1) (4 : ℤ) →
      ∃ g₀ : exampleCurve.FunctionField, g₀ ≠ 0 ∧
        4 • divisor exampleCurve g₀ = divisor exampleCurve (mulByNEndo 4
          (transcendental_xCoord_nsmul_of_smooth exampleTwo exampleThree
            (by norm_num) primeFactors_four) f)) :
    ∃ f : exampleCurve.FunctionField, f ≠ 0 ∧
      divisor exampleCurve f
          = Finsupp.single (CoordinateRing.pointClosedPoint exampleNsP.1) (4 : ℤ) ∧
      ∃ gS : exampleCurve.FunctionField, gS ≠ 0 ∧
        ∃ u : exampleCurve.CoordinateRingˣ, (u : exampleCurve.CoordinateRing) • gS ^ 4
          = mulByNEndo 4 (transcendental_xCoord_nsmul_of_smooth exampleTwo exampleThree
              (by norm_num) primeFactors_four) f := by
  simpa only [Nat.cast_ofNat] using
    exists_gS_of_smooth exampleTwo exampleThree (n := 4) (by norm_num) primeFactors_four
      exampleNsP exampleTorFour (by simpa only [Nat.cast_ofNat] using hprin)

end Nonvacuity

end WeierstrassCurve.Affine
