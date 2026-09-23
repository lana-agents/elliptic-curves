/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import EllipticCurves.FunctionField.DivisorBaseChangeRationalPoint
import EllipticCurves.FunctionField.DivisorGaloisDescentNsmul
import EllipticCurves.FunctionField.PullbackPrincipalityTwoRationalTorsion
import EllipticCurves.Torsion.HalvingGaloisTower

/-!
# `[2]∗((S) − (O))` is twice a principal divisor over an ARBITRARY field

`EllipticCurves.FunctionField.PullbackPrincipalityTwo` discharges `hprin` at `n = 2` over an
algebraically closed base; `EllipticCurves.FunctionField.PullbackPrincipalityTwoRationalTorsion`
replaces the closure by two rationality hypotheses, `hcard : Nat.card (W.torsion 2) = 4` and
`hP : 2 • P = S`.  **This file discharges it with neither**: over any field `F` with `(2 : F) ≠ 0`,
for any nonsingular `F`-rational `2`-torsion point `S`.

⚠️ **`(2 : F) ≠ 0` stays, and it is not a rationality fact.** It is the binder `mulByTwoEndo h2`
takes, and `mulByTwoEndo h2 f` occurs in the headline's own *statement*, so no proof change can drop
it.  ⚠️ **`S` rational stays too**, and it is not a hypothesis that could be dropped either: it is
what the statement is *about* — `pointClosedPoint h.left` is the closed point cut out by `(x, y)`.

## The route: build the field where both hypotheses become true, then descend

Neither hypothesis is proved.  Both are **bought over an extension and paid back by Galois
descent**:

1. `N := W.halvingGaloisField x₀` — the Galois closure over `F` of the tower
   `F ⊆ F(E[2]) ⊆ F(E[2])(halving of S)`.  It is finite Galois over `F`, `#E[2] = 4` over it and `S`
   is twice a point of `E(N)`: `EllipticCurves.Torsion.HalvingGaloisTower`, whose three statements
   are exactly the two hypotheses of `…_of_card` plus the Galois property this file's descent needs.
2. `divisor_functionFieldMap_eq_single`
   (`EllipticCurves.FunctionField.DivisorBaseChangeRationalPoint`) carries `div f = 2·(S)` up to `N`
   **on the nose**, because the fibre over the closed point of a *rational* point is a singleton
   with `e = 1` there.
3. `…_of_card` over `N` gives a `g` with `2 · div g = div ([2]∗ f)` upstairs.
4. `exists_nsmul_divisor_eq_of_functionFieldMap`
   (`EllipticCurves.FunctionField.DivisorGaloisDescentNsmul`) brings the identity back down to `F`,
   by Hilbert 90 at the finite level.  ⚠️ The function it returns is **not** the descent of `g`.

⚠️ **The `F̄` route is closed and this is not a matter of taste**: Mathlib's Hilbert 90 is
`[FiniteDimensional]`-only and its own `## TODO` says the infinite case is undeveloped, so
`H¹(Gal(F̄/F), F̄ˣ) = 0` is not available at the pin.  The finite tower is the route, not a
convenience.

## Main statements

* `WeierstrassCurve.Affine.exists_nsmul_divisor_eq_divisor_mulByTwoEndo_general` — `hprin` at
  `n = 2` over an arbitrary field with `(2 : F) ≠ 0`: the `#418` / `#962` gate at this index.
* `WeierstrassCurve.Affine.exists_gS_two_general` — rung 5 of the Weil pairing at `n = 2` over an
  arbitrary field with `(2 : F) ≠ 0`, with **no** gated hypothesis left.
* `WeierstrassCurve.Affine.not_exists_nsmul_two_eq_some_of_forall_eval_ne` — the converse of
  `exists_nsmul_two_eq_some_of_root` (`EllipticCurves.Torsion.DoublingSurjective`): no root of
  `Φ₂ − x₀·Ψ₂Sq`, no halving.  ⚠️ **It belongs beside that theorem and is stated here because this
  file is its only consumer**; it needs neither `(2 : F) ≠ 0` nor `[W.IsElliptic]`.

## ⚠️ The name clash, said rather than left to be discovered

`exists_nsmul_divisor_eq_divisor_mulByTwoEndo` is **taken** — it is the `[IsAlgClosed F]` headline
of `PullbackPrincipalityTwo` — and `…_of_card` is taken by the rational-torsion file.  The general
statement therefore lands as `…_general`, the tree's word for *over a general base*
(`CoordinateRingNormalGeneral`, `MulByNDegreeGeneral`, `PlaceInertiaGeneral`).  ⚠️ **Neither of the
two older headlines is retired or moved here**: both are still true, both are still the right thing
for a consumer that already has a closure or the two rationality facts, and `#907`'s rule asks for a
recovery only where a merged name would be duplicated.

## ⚠️ What is *not* here

* **`n = 3` is untouched.** `#962`'s ledger row *"`n = 3` throughout"* is unaudited and nothing
  below reaches it: `Ψ₃` is a quartic, `EllipticCurves.Torsion.HalvingGaloisTower` is `n = 2` in
  every statement, and the halving tower has no `n = 3` analogue in this tree.
  ⚠️ **This file must not be reported as closing `#962`.**
* **No characteristic-`2` statement.** `(2 : F) ≠ 0` is assumed throughout.
* **Nothing about a non-rational `S`.** Every statement below is at an affine point of `W(F)`.
* **`e = 1` in general is still not stated**, and is not needed: step 2 uses
  `EllipticCurves.FunctionField.DivisorBaseChangeRationalPoint`, which computes the index **only**
  at the closed point of a rational point, and step 4 needs only `e ≠ 0`.
* **No count of `E[2]` over `F` is claimed.** `#E[2]` over `F` may be `1`, `2` or `4` below; the
  non-vacuity section exhibits `2` on one curve and the `4` case is the older file's.
* **Rung 6 is not here.** The translation slot and non-degeneracy
  (`EllipticCurves.FunctionField.WeilPairingTranslationSlotHprin`) consume `hprin` and are not
  restated; what this file does for them is remove their gate at `n = 2`.

## Non-vacuity over `ℚ`

`#916`'s rule, and it takes **two** curves because no fixture in this tree fails both older
hypotheses at once:

* `y² = x³ − x` at `(0, 0)` — full rational `E[2]`, so `hcard` holds, and ⚠️ **no rational
  halving**: `Φ₂ = (X² + 1)²` here, so `not_exists_nsmul_two_eq_zero_y2EqX3SubX` refutes `hP`
  outright.  `…_of_card` cannot certify this instance.
* `y² = x³ + 4x` at `(0, 0)` — `Ψ₂Sq = 4X(X² + 4)` has one rational root, so `#E[2] = 2` and
  `hcard` fails.  (`hP` does hold here: `(2, 4)` halves `(0, 0)`.)

Both are over `ℚ`, which is not algebraically closed, so neither certifies the merged headline
either.  ⚠️ **A single curve failing both would need `Ψ₂Sq` with exactly one rational root AND a
non-square halving quadratic at it** — `#2029` says the tree has no such fixture to hand, and this
file adds none.

## References

* [Silverman, *The arithmetic of elliptic curves*][silverman2009], III.8 (the Weil pairing) and
  VIII.2 (Hilbert 90).
-/

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum

namespace WeierstrassCurve.Affine

open CoordinateRing

variable {F : Type*} [Field F] {W : Affine F} [DecidableEq F] [W.IsElliptic]

omit [DecidableEq F] [W.IsElliptic] in
private lemma algebraMap_two_ne_zero {L : Type*} [Field L] [Algebra F L] (h2 : (2 : F) ≠ 0) :
    (2 : L) ≠ 0 := fun hzero =>
  h2 ((algebraMap F L).injective (by rw [map_ofNat, map_zero]; exact hzero))

/-- **`hprin` at `n = 2` over an arbitrary field with `(2 : F) ≠ 0`**, in the shape `exists_gS_two`
consumes it: for a nonsingular `F`-rational `2`-torsion point `S = (x, y)` and a nonzero `f` with
`div f = 2·(S)`, the pullback `[2]∗ f` is twice a principal divisor.

⚠️ **No hypothesis on `F` beyond `(2 : F) ≠ 0`**: no algebraic closure, no `hcard`, no halving `hP`.
Both of `…_of_card`'s rationality hypotheses are bought over `W.halvingGaloisField x`, a finite
Galois extension of `F`, and paid back by Hilbert 90 —
`exists_nsmul_divisor_eq_of_functionFieldMap`
(`EllipticCurves.FunctionField.DivisorGaloisDescentNsmul`).

⚠️ **The `g₀` this returns is not the base change of the `g` obtained over that extension**, and is
not claimed to be: only its divisor identity descends.  ⚠️ **`n = 3` is untouched** — see the module
docstring. -/
theorem exists_nsmul_divisor_eq_divisor_mulByTwoEndo_general (h2 : (2 : F) ≠ 0) {x y : F}
    (h : W.Nonsingular x y) (hS : Point.some x y h ∈ W.torsion 2)
    {f : W.FunctionField} (hf : f ≠ 0)
    (hfdiv : divisor W f = Finsupp.single (pointClosedPoint h.left) (2 : ℤ)) :
    ∃ g₀ : W.FunctionField, g₀ ≠ 0 ∧ 2 • divisor W g₀ = divisor W (mulByTwoEndo h2 f) := by
  classical
  have hx : W.Ψ₂Sq.eval x = 0 := Ψ₂Sq_eval_eq_zero_of_mem_torsion_two hS
  haveI : IsGalois F (W.halvingGaloisField x) := isGalois_halvingGaloisField h2 hx
  haveI : FiniteDimensional F (W.halvingGaloisField x) := finiteDimensional_halvingGaloisField
  set N := W.halvingGaloisField x with hN
  haveI : DecidableEq N := Classical.decEq N
  have h2' : (2 : N) ≠ 0 := algebraMap_two_ne_zero h2
  -- the base-changed point
  have h' : (W⁄N).Nonsingular (algebraMap F N x) (algebraMap F N y) :=
    (W.map_nonsingular (algebraMap F N).injective x y).mpr h
  have hS' : Point.some (algebraMap F N x) (algebraMap F N y) h' ∈ (W⁄N).torsion 2 := by
    rw [mem_torsion_two_some_iff]
    have hxy := (mem_torsion_two_some_iff h).mp hS
    have hmap := congrArg (algebraMap F N) hxy
    simpa [map_ofNat] using hmap
  obtain ⟨P, hP⟩ := exists_nsmul_two_eq_halvingGaloisField h2 h hx
  have hcard : Nat.card ((W⁄N).torsion 2) = 4 := card_torsion_two_halvingGaloisField h2 x
  -- transport `f` and its divisor
  have hf' : functionFieldMap W N f ≠ 0 :=
    (map_ne_zero_iff _ (functionFieldMap_injective W N)).mpr hf
  have hfdiv' : divisor (W⁄N) (functionFieldMap W N f)
      = Finsupp.single (pointClosedPoint h'.left) (2 : ℤ) :=
    divisor_functionFieldMap_eq_single N h.left hf hfdiv
  -- rung 5 over `N`
  obtain ⟨g, hg, hgdiv⟩ := exists_nsmul_divisor_eq_divisor_mulByTwoEndo_of_card h2' hcard h' hS'
    hP hf' hfdiv'
  -- descend
  have hz : mulByTwoEndo h2 f ≠ 0 :=
    (map_ne_zero_iff _ (mulByTwoEndo h2).injective).mpr hf
  refine exists_nsmul_divisor_eq_of_functionFieldMap N two_ne_zero hz hg ?_
  rw [hgdiv, functionFieldMap_mulByTwoEndo h2 h2' f]
  rfl

omit [W.IsElliptic] in
/-- **No root of `Φ₂ - x₀·Ψ₂Sq`, no halving** — the converse of
`EllipticCurves.Torsion.DoublingSurjective`'s `exists_nsmul_two_eq_some_of_root`. -/
theorem not_exists_nsmul_two_eq_some_of_forall_eval_ne {x₀ y₀ : F} (hQ : W.Nonsingular x₀ y₀)
    (hroot : ∀ x : F, (W.Φ 2).eval x ≠ x₀ * W.Ψ₂Sq.eval x) :
    ¬ ∃ P : W.Point, 2 • P = Point.some x₀ y₀ hQ := by
  rintro ⟨P, hP⟩
  cases P with
  | zero =>
    rw [show (Point.zero : W.Point) = 0 from rfl, smul_zero] at hP
    exact (Point.some_ne_zero hQ) hP.symm
  | @some x₁ y₁ h₁ =>
    by_cases hy : W.Ψ₂Sq.eval x₁ = 0
    · have htors : Point.some x₁ y₁ h₁ ∈ W.torsion 2 := by
        rw [mem_torsion_two_some_iff]
        have hsq := Ψ₂Sq_eval_eq_sq (W := W) h₁.left
        rw [hy] at hsq
        exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hsq.symm
      rw [mem_torsion_iff] at htors
      rw [htors] at hP
      exact (Point.some_ne_zero hQ) hP.symm
    · obtain ⟨y', h', hxy⟩ :=
        hasXCoordFormula_two (W := W) h₁ (by simpa only [Nat.cast_ofNat, ΨSq_two] using hy)
      rw [hxy] at hP
      have hx := (Point.some.injEq _ _ _ _ _ _).mp hP
      refine hroot x₁ ?_
      simp only [Nat.cast_ofNat, ΨSq_two] at hx
      field_simp at hx
      exact hx.1.trans (mul_comm _ _)

/-- **Rung 5 of the Weil pairing at `n = 2` over an arbitrary field with `(2 : F) ≠ 0`**, with no
gated hypothesis left: for a nonsingular `F`-rational `2`-torsion point `S` there are a principal
`f_S` with `div f_S = 2·(S)` and a nonzero `g_S` with `u · g_S ^ 2 = [2]∗ f_S` for a unit `u` of
`F[W]`.

`exists_gS_two` (`EllipticCurves.FunctionField.NthRootOfPullback`) with its `hprin` discharged by
the theorem above; `exists_gS_two_of_isAlgClosed` and `exists_gS_two_of_card` are the same statement
under a closure and under the two rationality hypotheses respectively, and **neither is superseded
for a caller that already holds those** — this one asks for less and proves the same thing. -/
theorem exists_gS_two_general (h2 : (2 : F) ≠ 0) {x y : F}
    (h : W.Nonsingular x y) (hS : Point.some x y h ∈ W.torsion 2) :
    ∃ f : W.FunctionField, f ≠ 0 ∧
      divisor W f = Finsupp.single (pointClosedPoint h.left) (2 : ℤ) ∧
      ∃ gS : W.FunctionField, gS ≠ 0 ∧
        ∃ u : W.CoordinateRingˣ, (u : W.CoordinateRing) • gS ^ 2 = mulByTwoEndo h2 f :=
  exists_gS_two h2 h hS fun _ hf hfdiv =>
    exists_nsmul_divisor_eq_divisor_mulByTwoEndo_general h2 h hS hf hfdiv

/-! ### Non-vacuity over `ℚ` -/

section Nonvacuity

open EllipticCurves.Fixture Polynomial

/-- The `2`-torsion point `(0, 0)` of `y² = x³ - x`. -/
private lemma equation_zero_y2EqX3SubX : (y2EqX3SubX ℚ).Equation 0 0 := by
  rw [Affine.equation_iff]; norm_num [y2EqX3SubX]

private lemma nonsingular_zero_y2EqX3SubX : (y2EqX3SubX ℚ).Nonsingular 0 0 :=
  equation_iff_nonsingular.mp equation_zero_y2EqX3SubX

private lemma mem_torsion_two_zero_y2EqX3SubX :
    Point.some 0 0 nonsingular_zero_y2EqX3SubX ∈ (y2EqX3SubX ℚ).torsion 2 := by
  rw [mem_torsion_two_some_iff]; norm_num [y2EqX3SubX]

/-- **`Φ₂ = (X² + 1)²` on `y² = x³ - x`**, computed through `Φ_two_eval` rather than by unfolding
the recursion: `x · (4x³ - 4x) - (3x⁴ - 6x² - 1) = (x² + 1)²`. -/
private lemma eval_Φ_two_y2EqX3SubX (x : ℚ) :
    ((y2EqX3SubX ℚ).Φ 2).eval x = (x ^ 2 + 1) ^ 2 := by
  rw [Φ_two_eval]
  simp only [WeierstrassCurve.Ψ₂Sq, WeierstrassCurve.Ψ₃, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈, y2EqX3SubX]
  norm_num
  ring

/-- **`(0, 0)` has no rational halving on `y² = x³ - x`** -/
private theorem not_exists_nsmul_two_eq_zero_y2EqX3SubX :
    ¬ ∃ P : (y2EqX3SubX ℚ).Point, 2 • P = Point.some 0 0 nonsingular_zero_y2EqX3SubX :=
  not_exists_nsmul_two_eq_some_of_forall_eval_ne _ fun x => by
    rw [eval_Φ_two_y2EqX3SubX, zero_mul]; positivity

/-- **Rung 5 at `n = 2` on `y² = x³ - x` over `ℚ`, with no hypothesis at all.** -/
private theorem exampleRungFiveTwoGeneral :
    ∃ f : (y2EqX3SubX ℚ).FunctionField, f ≠ 0 ∧
      divisor (y2EqX3SubX ℚ) f
          = Finsupp.single (pointClosedPoint nonsingular_zero_y2EqX3SubX.left) (2 : ℤ) ∧
      ∃ gS : (y2EqX3SubX ℚ).FunctionField, gS ≠ 0 ∧
        ∃ u : (y2EqX3SubX ℚ).CoordinateRingˣ, (u : (y2EqX3SubX ℚ).CoordinateRing) • gS ^ 2
          = mulByTwoEndo (by norm_num) f :=
  exists_gS_two_general (by norm_num) nonsingular_zero_y2EqX3SubX mem_torsion_two_zero_y2EqX3SubX

/-! The other hypothesis, on a second shared fixture. -/

/-- `Ψ₂Sq = 4 · X · (X² + 4)` for `y² = x³ + 4x`. -/
private lemma Ψ₂Sq_y2EqX3Add4X :
    (y2EqX3Add4X ℚ).Ψ₂Sq = C 4 * X * (X ^ 2 + C 4) := by
  simp only [WeierstrassCurve.Ψ₂Sq, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, y2EqX3Add4X]
  norm_num only
  simp only [map_ofNat, Polynomial.C_0]
  ring

/-- **The only rational root of the cubic is `0`**, because `x² + 4` is positive. -/
private lemma eval_Ψ₂Sq_y2EqX3Add4X_eq_zero_iff {x : ℚ} :
    (y2EqX3Add4X ℚ).Ψ₂Sq.eval x = 0 ↔ x = 0 := by
  rw [Ψ₂Sq_y2EqX3Add4X]
  simp only [eval_mul, eval_add, eval_pow, eval_C, eval_X]
  constructor
  · intro h
    rcases mul_eq_zero.mp h with h' | h'
    · rcases mul_eq_zero.mp h' with h'' | h''
      · norm_num at h''
      · exact h''
    · nlinarith [sq_nonneg x]
  · rintro rfl
    ring

private lemma card_roots_Ψ₂Sq_y2EqX3Add4X :
    Nat.card {x : ℚ // (y2EqX3Add4X ℚ).Ψ₂Sq.eval x = 0} = 1 := by
  rw [Nat.card_eq_one_iff_unique]
  exact ⟨⟨fun a b => Subtype.ext ((eval_Ψ₂Sq_y2EqX3Add4X_eq_zero_iff.mp a.2).trans
    (eval_Ψ₂Sq_y2EqX3Add4X_eq_zero_iff.mp b.2).symm)⟩,
    ⟨⟨0, eval_Ψ₂Sq_y2EqX3Add4X_eq_zero_iff.mpr rfl⟩⟩⟩

/-- **`#E[2] = 2 ≠ 4` over `ℚ`** for `y² = x³ + 4x`. -/
private theorem card_torsion_two_y2EqX3Add4X :
    Nat.card ((y2EqX3Add4X ℚ).torsion 2) = 2 := by
  haveI := (y2EqX3Add4X ℚ).finite_roots_Ψ₂Sq (by norm_num)
  rw [Nat.card_congr (torsionTwoEquiv (W := y2EqX3Add4X ℚ) (by norm_num)), Finite.card_option,
    card_roots_Ψ₂Sq_y2EqX3Add4X]

private lemma equation_zero_y2EqX3Add4X : (y2EqX3Add4X ℚ).Equation 0 0 := by
  rw [Affine.equation_iff]; norm_num [y2EqX3Add4X]

private lemma nonsingular_zero_y2EqX3Add4X : (y2EqX3Add4X ℚ).Nonsingular 0 0 :=
  equation_iff_nonsingular.mp equation_zero_y2EqX3Add4X

private lemma mem_torsion_two_zero_y2EqX3Add4X :
    Point.some 0 0 nonsingular_zero_y2EqX3Add4X ∈ (y2EqX3Add4X ℚ).torsion 2 := by
  rw [mem_torsion_two_some_iff]; norm_num [y2EqX3Add4X]

/-- **Rung 5 at `n = 2` on `y² = x³ + 4x` over `ℚ`, with no hypothesis at all** — where
`card_torsion_two_y2EqX3Add4X` says `#E[2] = 2`. -/
private theorem exampleRungFiveTwoGeneralAdd4X :
    ∃ f : (y2EqX3Add4X ℚ).FunctionField, f ≠ 0 ∧
      divisor (y2EqX3Add4X ℚ) f
          = Finsupp.single (pointClosedPoint nonsingular_zero_y2EqX3Add4X.left) (2 : ℤ) ∧
      ∃ gS : (y2EqX3Add4X ℚ).FunctionField, gS ≠ 0 ∧
        ∃ u : (y2EqX3Add4X ℚ).CoordinateRingˣ, (u : (y2EqX3Add4X ℚ).CoordinateRing) • gS ^ 2
          = mulByTwoEndo (by norm_num) f :=
  exists_gS_two_general (by norm_num) nonsingular_zero_y2EqX3Add4X
    mem_torsion_two_zero_y2EqX3Add4X

end Nonvacuity

end WeierstrassCurve.Affine
