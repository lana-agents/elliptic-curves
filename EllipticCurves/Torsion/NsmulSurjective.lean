/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import EllipticCurves.Torsion.DoublingSurjective
import EllipticCurves.Torsion.TriplingSurjective

/-!
# Surjectivity of `[n]` on `E(F̄)` from the multiplication-by-`n` coordinate formula

`EllipticCurves.Torsion.DoublingSurjective` and `EllipticCurves.Torsion.TriplingSurjective` prove
that `[2]` and `[3]` are surjective on `E(F̄)`, for an elliptic curve over an algebraically closed
field with `(2 : F) ≠ 0`.  Read side by side, **the two proofs are the same proof**.  Only two of
their inputs mention the index at all:

1. the denominator-cleared coordinate formula `x(nP) · ΨSqₙ(x) = Φₙ(x)`, and
2. the fact that `Φₙ` and `ΨSqₙ` have no common root in `F`.

Everything else — the degree count on `Φₙ − x₀·ΨSqₙ`, the root extraction over `F̄`, the choice of a
point above the root, and the absorption of the sign ambiguity `nP = ±Q` — is uniform in `n`.  This
file writes that uniform half **once, at general `n`**, taking (1) and (2) as hypotheses, and then
re-derives `nsmul_two_surjective` and `nsmul_three_surjective` through it.

## What this does and does not settle

⚠️ **Nothing is proved here at any index where it was not already known.**  Both inputs are
established only at `n = 2` and `n = 3`, in both cases from the already-merged closed-point results:
input (1) as `hasXCoordFormula_two` / `hasXCoordFormula_three`, input (2) as
`eval_Φ_two_ne_zero_of_root_ΨSq` / `eval_Φ_three_ne_zero_of_root_ΨSq`.

What the file *does* settle is **how much is needed, and that it is exactly two things**.
`EllipticCurves.Torsion.CoprimeStructure` reduces the structure theorem `E[n] ≅ (ℤ/nℤ)²` to prime
powers and records that every prime `p ≥ 5` is blocked on `[p]`-surjectivity, "which still needs the
general coordinate formula".  That sentence remains true, and its subject now has names: what is
missing at a prime `p ≥ 5` is a term of `HasXCoordFormula W p` (issue `#251`) **and** a term of
`∀ x, (W.ΨSq p).eval x = 0 → (W.Φ p).eval x ≠ 0` (implied by issue `#1184`, and strictly weaker than
it).  Beyond those two, nothing — no degree hypothesis, no Bézout certificate, and no hypothesis on
`(n : F)`.

⚠️ So `#1184` is **not** only a gate under rung 3's degree count, which is where it is filed: a
weakening of it is also a gate under the structure theorem at every prime `p ≥ 5`.  The two merged
instances show the weakening is the cheaper target — neither `n = 2` nor `n = 3` obtains it through
Bézout.

## Two economies of the merged proofs are preserved deliberately

* **No hypothesis on `(n : F)`.**  The degree input is `natDegree_Φ (n : ℤ) = n.natAbs ^ 2` with
  leading coefficient `1`, against `natDegree_ΨSq_le (n : ℤ) ≤ n.natAbs ^ 2 - 1`; **both are
  unconditional in Mathlib**, so `n ≠ 0` alone gives `Φₙ − C x₀ · ΨSqₙ` degree `n²`.  Mathlib's
  sharp `natDegree_ΨSq` carries `(n : R) ≠ 0` and is *not* used.  `TriplingSurjective`'s docstring
  records that this is exactly what makes `nsmul_three_surjective` hold in characteristic `3`; the
  same economy survives at general `n`.
* **No Bézout certificate.**  Input (2) is taken in the weak pointwise form
  `∀ x, (ΨSqₙ).eval x = 0 → (Φₙ).eval x ≠ 0`, which is what both merged proofs establish directly —
  at `n = 2` through `Ψ₂Sq_eval_ne_zero_of_root_Ψ₃` and at `n = 3` through
  `Φ_three_eval_ne_zero_of_Ψ₃`, each stating in terms that no resultant and no identity
  `A·Φₙ + B·ΨSqₙ = Δ` is needed.
  The full coprimality `IsCoprime (W.Φ n) (W.ΨSq n)` — issue `#1184`, proved in this tree only at
  `n = 2` and `n = 3` — is **strictly stronger** than what is used, and
  `eval_Φ_ne_zero_of_isCoprime` below is the one-line bridge that lets it be plugged in if it ever
  lands at general `n`.

## Main definitions

* `WeierstrassCurve.Affine.HasXCoordFormula`: the multiplication-by-`n` coordinate formula at an
  affine point where `ΨSqₙ` does not vanish, as a predicate on `(W, n)`.

## Main statements

* `WeierstrassCurve.Affine.natDegree_Φ_sub_C_mul_ΨSq`: `Φₙ − C x₀ · ΨSqₙ` has degree `n²`.
* `WeierstrassCurve.Affine.exists_eval_Φ_eq`: over `F̄`, every `x₀` solves `Φₙ(x) = x₀·ΨSqₙ(x)`.
* `WeierstrassCurve.Affine.eval_Φ_ne_zero_of_isCoprime`: `IsCoprime (Φₙ, ΨSqₙ)` implies the
  pointwise no-common-root hypothesis.
* `WeierstrassCurve.Affine.eval_Φ_two_ne_zero_of_root_ΨSq`,
  `WeierstrassCurve.Affine.eval_Φ_three_ne_zero_of_root_ΨSq`: that hypothesis at `n = 2` and
  `n = 3`, by the Bézout-free arguments of the merged surjectivity proofs.
* `WeierstrassCurve.Affine.exists_nsmul_some_of_hasXCoordFormula`: every `x₀` is the `x`-coordinate
  of an `n`-fold multiple.
* **`WeierstrassCurve.Affine.exists_nsmul_eq_of_hasXCoordFormula`** and
  **`WeierstrassCurve.Affine.nsmul_surjective_of_hasXCoordFormula`**: the headline, `[n]` is
  surjective on `E(F̄)`.
* `WeierstrassCurve.Affine.hasXCoordFormula_two`, `WeierstrassCurve.Affine.hasXCoordFormula_three`:
  the two available instances of the hypothesis, from the merged closed-point formulæ.

Every public declaration of this file is listed above.

## References

* [J. H. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.4, Corollary 4.9.
-/

open Polynomial

namespace WeierstrassCurve.Affine

variable {F : Type*} [Field F] {W : Affine F}

/-! ## Solving the multiplication-by-`n` equation for the `x`-coordinate -/

/-- The auxiliary polynomial `Φₙ − x₀·ΨSqₙ`, whose roots are the `x`-coordinates of the points `P`
with `x(nP) = x₀`, is monic of degree `n²`: `Φₙ` is monic of degree `n²` while `ΨSqₙ` has degree at
most `n² − 1`.

**No hypothesis on `(n : F)`**: both Mathlib inputs, `natDegree_Φ` and `natDegree_ΨSq_le`, are
unconditional.  This is the general-`n` form of `natDegree_Φ_two_sub_C_mul_Ψ₂Sq` and
`natDegree_Φ_three_sub_C_mul_ΨSq_three`. -/
lemma natDegree_Φ_sub_C_mul_ΨSq {n : ℕ} (hn : n ≠ 0) (x₀ : F) :
    (W.Φ n - C x₀ * W.ΨSq n).natDegree = n ^ 2 := by
  have hpos : 0 < n ^ 2 := Nat.pos_of_ne_zero (pow_ne_zero 2 hn)
  have hΦ : (W.Φ (n : ℤ)).natDegree = n ^ 2 := by
    rw [W.natDegree_Φ (n : ℤ), Int.natAbs_natCast]
  have hΨ : (C x₀ * W.ΨSq (n : ℤ)).natDegree < n ^ 2 := by
    refine lt_of_le_of_lt ((natDegree_C_mul_le x₀ _).trans (W.natDegree_ΨSq_le (n : ℤ))) ?_
    rw [Int.natAbs_natCast]
    exact Nat.sub_lt hpos one_pos
  rw [natDegree_sub_eq_left_of_natDegree_lt (hΦ ▸ hΨ), hΦ]

/-- **Every value of `x` solves the multiplication-by-`n` equation.**  Over an algebraically closed
field the degree-`n²` polynomial `Φₙ − x₀·ΨSqₙ` has a root. -/
lemma exists_eval_Φ_eq [IsAlgClosed F] {n : ℕ} (hn : n ≠ 0) (x₀ : F) :
    ∃ x : F, (W.Φ n).eval x = x₀ * (W.ΨSq n).eval x := by
  have hdeg : (W.Φ (n : ℤ) - C x₀ * W.ΨSq (n : ℤ)).degree ≠ 0 :=
    (natDegree_pos_iff_degree_pos.mp
      (by rw [natDegree_Φ_sub_C_mul_ΨSq hn]; exact Nat.pos_of_ne_zero (pow_ne_zero 2 hn))).ne'
  obtain ⟨x, hx⟩ := IsAlgClosed.exists_root _ hdeg
  rw [IsRoot.def, eval_sub, eval_mul, eval_C, sub_eq_zero] at hx
  exact ⟨x, hx⟩

/-- The bridge from the Bézout form of coprimality to the pointwise no-common-root hypothesis used
below.  `IsCoprime (W.Φ n) (W.ΨSq n)` at general `n` is issue `#1184` and is available in this tree
only at `n = 2` (`isCoprime_Φ_two_Ψ₂Sq`) and `n = 3` (`isCoprime_Φ_three_ΨSq_three`); the
surjectivity engine below needs only the conclusion, which both merged surjectivity proofs obtain
without any Bézout certificate. -/
lemma eval_Φ_ne_zero_of_isCoprime {n : ℕ} (h : IsCoprime (W.Φ n) (W.ΨSq n)) {x : F}
    (hx : (W.ΨSq n).eval x = 0) : (W.Φ n).eval x ≠ 0 := by
  obtain ⟨a, b, hab⟩ := h
  intro h0
  have heval := congrArg (Polynomial.eval x) hab
  rw [eval_add, eval_mul, eval_mul, h0, hx, mul_zero, mul_zero, add_zero, eval_one] at heval
  exact zero_ne_one heval

/-! ## The no-common-root hypothesis at `n = 2` and `n = 3`

Both are the Bézout-free arguments the merged surjectivity proofs use, restated in the pointwise
form the engine consumes. -/

/-- **`Φ₂` and `Ψ₂Sq` have no common root.**  A common root would be a root of
`Ψ₃ = X·Ψ₂Sq − Φ₂`, and a root of `Ψ₃` is never a root of `Ψ₂Sq`
(`Ψ₂Sq_eval_ne_zero_of_root_Ψ₃`).  This is the `hne` step of `exists_addX_self_eq`, isolated. -/
theorem eval_Φ_two_ne_zero_of_root_ΨSq [IsAlgClosed F] [W.IsElliptic] (h2 : (2 : F) ≠ 0) (x : F)
    (hx : (W.ΨSq 2).eval x = 0) : (W.Φ 2).eval x ≠ 0 := by
  rw [ΨSq_two] at hx
  intro h0
  exact Ψ₂Sq_eval_ne_zero_of_root_Ψ₃ h2 (by rw [Ψ₃_eval_eq_sub, hx, h0]; ring) hx

/-- **`Φ₃` and `ΨSq₃` have no common root.**  `ΨSq₃ = Ψ₃²`, so a root of `ΨSq₃` is a root of `Ψ₃`,
and `Φ_three_eval_ne_zero_of_Ψ₃` is the merged statement that `Φ₃` does not vanish there. -/
theorem eval_Φ_three_ne_zero_of_root_ΨSq [IsAlgClosed F] [W.IsElliptic] (h2 : (2 : F) ≠ 0) (x : F)
    (hx : (W.ΨSq 3).eval x = 0) : (W.Φ 3).eval x ≠ 0 := by
  rw [ΨSq_three_eval] at hx
  exact Φ_three_eval_ne_zero_of_Ψ₃ h2 (pow_eq_zero_iff two_ne_zero |>.mp hx)

/-! ## The coordinate formula as a hypothesis -/

section Formula

variable [DecidableEq F]

/-- **The multiplication-by-`n` coordinate formula**, as a predicate.  It says that at an affine
point `(x, y)` of `W` at which `ΨSqₙ` does not vanish, the multiple `n • (x, y)` is affine with
`x`-coordinate `Φₙ(x)/ΨSqₙ(x)`.

This is the one index-dependent input of the surjectivity engine below.  Establishing it at general
`n` is issue `#251`; `hasXCoordFormula_two` and `hasXCoordFormula_three` are the two cases available
in this tree. -/
def HasXCoordFormula (W : Affine F) (n : ℕ) : Prop :=
  ∀ ⦃x y : F⦄ (h : W.Nonsingular x y), (W.ΨSq n).eval x ≠ 0 →
    ∃ (y' : F) (h' : W.Nonsingular ((W.Φ n).eval x / (W.ΨSq n).eval x) y'),
      n • Point.some x y h = Point.some _ y' h'

/-! ## Surjectivity of multiplication by `n` -/

/-- **Every value of `x` is the `x`-coordinate of an `n`-fold multiple.**  Over an algebraically
closed field of characteristic `≠ 2`, given the coordinate formula at `n` and the absence of a
common root of `Φₙ` and `ΨSqₙ`, every `x₀` is `x(nP)` for some point `P`.

This is the general-`n` form of `exists_addX_self_eq` and `exists_nsmul_three_some`. -/
theorem exists_nsmul_some_of_hasXCoordFormula [IsAlgClosed F] [W.IsElliptic] (h2 : (2 : F) ≠ 0)
    {n : ℕ}
    (hn : n ≠ 0) (hroot : ∀ x : F, (W.ΨSq n).eval x = 0 → (W.Φ n).eval x ≠ 0)
    (hform : HasXCoordFormula W n) (x₀ : F) :
    ∃ (P : W.Point) (y' : F) (h' : W.Nonsingular x₀ y'), n • P = Point.some x₀ y' h' := by
  obtain ⟨x, hx⟩ := exists_eval_Φ_eq (W := W) hn x₀
  have hne : (W.ΨSq n).eval x ≠ 0 := fun h0 => hroot x h0 (by rw [hx, h0, mul_zero])
  obtain ⟨y, hyeq⟩ := exists_equation (W := W) h2 x
  have hns : W.Nonsingular x y := equation_iff_nonsingular.mp hyeq
  obtain ⟨y', h', hP⟩ := hform hns hne
  have hxx : (W.Φ n).eval x / (W.ΨSq n).eval x = x₀ := by
    rw [hx, mul_div_assoc, div_self hne, mul_one]
  subst hxx
  exact ⟨Point.some x y hns, y', h', hP⟩

/-- **Multiplication by `n` is surjective on `E(F̄)`**, given the coordinate formula at `n`.  The
point at infinity is `n • 0`; an affine `Q` is matched by `exists_nsmul_some_of_hasXCoordFormula`,
which pins the `x`-coordinate, leaving the sign ambiguity `nP = ±Q` that `Point.X_eq_iff` resolves
and `−P` absorbs. -/
theorem exists_nsmul_eq_of_hasXCoordFormula [IsAlgClosed F] [W.IsElliptic] (h2 : (2 : F) ≠ 0)
    {n : ℕ} (hn : n ≠ 0)
    (hroot : ∀ x : F, (W.ΨSq n).eval x = 0 → (W.Φ n).eval x ≠ 0)
    (hform : HasXCoordFormula W n) (Q : W.Point) : ∃ P : W.Point, n • P = Q := by
  rcases Q with _ | ⟨x₀, y₀, hQ⟩
  · exact ⟨0, smul_zero n⟩
  · obtain ⟨P, y', h', hP⟩ := exists_nsmul_some_of_hasXCoordFormula h2 hn hroot hform x₀
    rcases (Point.X_eq_iff (h₁ := h') (h₂ := hQ)).mp rfl with hc | hc
    · exact ⟨P, by rw [hP, hc]⟩
    · exact ⟨-P, by rw [smul_neg, hP, hc, neg_neg]⟩

/-- **Multiplication by `n` is surjective on `E(F̄)`**, stated as `Function.Surjective` — the form
`EllipticCurves.Torsion.Divisible`'s `torsionSmulHom_surjective` consumes, and the general-`n` form
of `nsmul_two_surjective` and `nsmul_three_surjective`. -/
theorem nsmul_surjective_of_hasXCoordFormula [IsAlgClosed F] [W.IsElliptic] (h2 : (2 : F) ≠ 0)
    {n : ℕ} (hn : n ≠ 0)
    (hroot : ∀ x : F, (W.ΨSq n).eval x = 0 → (W.Φ n).eval x ≠ 0)
    (hform : HasXCoordFormula W n) : Function.Surjective fun P : W.Point => n • P :=
  exists_nsmul_eq_of_hasXCoordFormula h2 hn hroot hform

/-! ## The two available instances of the hypothesis -/

/-- **The coordinate formula at `n = 2`.**  A point at which `Ψ₂Sq` does not vanish is not fixed by
negation, so `2 • P` is the tangent sum, whose `x`-coordinate is `Φ₂(x)/Ψ₂Sq(x)` by the merged
`addX_self_mul_Ψ₂Sq_eval`. -/
theorem hasXCoordFormula_two : HasXCoordFormula W 2 := by
  intro x y h hne
  simp only [Nat.cast_ofNat] at hne ⊢
  rw [ΨSq_two] at hne
  have hyeq : W.Equation x y := h.1
  have hyne : y ≠ W.negY x y := by
    intro hcon
    have hd : 2 * y + W.a₁ * x + W.a₃ = 0 := by
      rw [WeierstrassCurve.Affine.negY] at hcon
      linear_combination hcon
    exact hne (by rw [Ψ₂Sq_eval_eq_sq hyeq, hd]; ring)
  have hX : W.addX x x (W.slope x x y y) = (W.Φ 2).eval x / (W.ΨSq 2).eval x := by
    rw [ΨSq_two, eq_div_iff hne]
    exact addX_self_mul_Ψ₂Sq_eval hyeq hyne
  have hns₂ : W.Nonsingular ((W.Φ 2).eval x / (W.ΨSq 2).eval x)
      (W.addY x x y (W.slope x x y y)) := by
    rw [← hX]
    exact nonsingular_add h h fun hxy => hyne hxy.right
  refine ⟨W.addY x x y (W.slope x x y y), hns₂, ?_⟩
  rw [two_nsmul, Point.add_self_of_Y_ne hyne]
  simp only [Point.some.injEq, and_true]
  exact hX

/-- **The coordinate formula at `n = 3`.**  Since `ΨSq₃ = Ψ₃²`, the hypothesis is `Ψ₃(x) ≠ 0`.

⚠️ **Both branches are genuine.**  `Ψ₂Sq(x) = 0` is *not* excluded, and there `2P = O`, so the
secant construction of `3P = 2P + P` does not apply; but then `Φ₃(x) = x·Ψ₃(x)²` and
`ΨSq₃(x) = Ψ₃(x)²`, so `3P = P` already has `x`-coordinate `Φ₃(x)/ΨSq₃(x)`.  Otherwise the merged
`addX_add_self_mul_ΨSq_three_eval` computes it.  This is the branch structure of
`exists_nsmul_three_some`, which records the same warning. -/
theorem hasXCoordFormula_three (h2 : (2 : F) ≠ 0) : HasXCoordFormula W 3 := by
  intro x y h hne
  simp only [Nat.cast_ofNat] at hne ⊢
  have hyeq : W.Equation x y := h.1
  have hT : W.Ψ₃.eval x ≠ 0 := fun h0 => hne (by rw [ΨSq_three_eval, h0]; ring)
  have h3P : (3 : ℕ) • Point.some x y h
      = Point.some x y h + Point.some x y h + Point.some x y h := by
    rw [show (3 : ℕ) = 2 + 1 from rfl, add_smul, two_nsmul, one_nsmul]
  by_cases hyeqn : y = W.negY x y
  · -- `P` is `2`-torsion: `3 • P = P`, and `Φ₃(x)/ΨSq₃(x) = x`
    have hs0 : 2 * y + W.a₁ * x + W.a₃ = 0 := by
      have h' := hyeqn
      rw [WeierstrassCurve.Affine.negY] at h'
      linear_combination h'
    have hp : W.Ψ₂Sq.eval x = 0 := by rw [Ψ₂Sq_eval_eq_sq hyeq, hs0]; ring
    have hxx : (W.Φ 3).eval x / (W.ΨSq 3).eval x = x := by
      rw [Φ_three_eval, hp, mul_zero, sub_zero, ΨSq_three_eval, mul_div_assoc,
        div_self (pow_ne_zero 2 hT), mul_one]
    have hns₃ : W.Nonsingular ((W.Φ 3).eval x / (W.ΨSq 3).eval x) y := by rw [hxx]; exact h
    refine ⟨y, hns₃, ?_⟩
    rw [h3P, Point.add_self_of_Y_eq hyeqn, zero_add]
    simp only [Point.some.injEq, and_true]
    exact hxx.symm
  · -- the secant branch: `3 • P = 2 • P + P`
    have hx₂ne : W.addX x x (W.slope x x y y) ≠ x := by
      rw [Ne, addX_self_eq_iff hyeq hyeqn]
      exact hT
    have hX : W.addX (W.addX x x (W.slope x x y y)) x
        (W.slope (W.addX x x (W.slope x x y y)) x (W.addY x x y (W.slope x x y y)) y)
        = (W.Φ 3).eval x / (W.ΨSq 3).eval x := by
      rw [eq_div_iff hne]
      exact addX_add_self_mul_ΨSq_three_eval h2 hyeq hyeqn hT
    have hns₃ : W.Nonsingular ((W.Φ 3).eval x / (W.ΨSq 3).eval x)
        (W.addY (W.addX x x (W.slope x x y y)) x (W.addY x x y (W.slope x x y y))
          (W.slope (W.addX x x (W.slope x x y y)) x (W.addY x x y (W.slope x x y y)) y)) := by
      rw [← hX]
      exact nonsingular_add (nonsingular_add h h fun hxy => hyeqn hxy.right) h
        fun hxy => hx₂ne hxy.left
    refine ⟨W.addY (W.addX x x (W.slope x x y y)) x (W.addY x x y (W.slope x x y y))
        (W.slope (W.addX x x (W.slope x x y y)) x (W.addY x x y (W.slope x x y y)) y),
      hns₃, ?_⟩
    rw [h3P, Point.add_self_of_Y_ne hyeqn, Point.add_of_X_ne hx₂ne]
    simp only [Point.some.injEq, and_true]
    exact hX

/-! ## Validation: the merged `n = 2` and `n = 3` surjectivity, re-derived through the engine

Both merged headlines are instances of `nsmul_surjective_of_hasXCoordFormula`, and the inputs each
instance needs are exactly the inputs the corresponding merged proof uses — the coordinate formula
`addX_self_mul_Ψ₂Sq_eval` / `addX_add_self_mul_ΨSq_three_eval` and the no-common-root statement
`Ψ₂Sq_eval_ne_zero_of_root_Ψ₃` / `Φ_three_eval_ne_zero_of_Ψ₃`.  Nothing else enters, which is the
evidence that the engine abstracts those two proofs rather than re-parametrising them.

They are `example`s and not `theorem`s: their statements *are* `nsmul_two_surjective` and
`nsmul_three_surjective`, and two names on one statement is the worse outcome. -/

example [IsAlgClosed F] [W.IsElliptic] (h2 : (2 : F) ≠ 0) :
    Function.Surjective fun P : W.Point => (2 : ℕ) • P :=
  nsmul_surjective_of_hasXCoordFormula h2 (by norm_num)
    (by simp only [Nat.cast_ofNat]; exact eval_Φ_two_ne_zero_of_root_ΨSq h2)
    hasXCoordFormula_two

example [IsAlgClosed F] [W.IsElliptic] (h2 : (2 : F) ≠ 0) :
    Function.Surjective fun P : W.Point => (3 : ℕ) • P :=
  nsmul_surjective_of_hasXCoordFormula h2 (by norm_num)
    (by simp only [Nat.cast_ofNat]; exact eval_Φ_three_ne_zero_of_root_ΨSq h2)
    (hasXCoordFormula_three h2)

end Formula

end WeierstrassCurve.Affine
