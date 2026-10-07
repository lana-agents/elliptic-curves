/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import EllipticCurves.Torsion.NsmulOrderCharFree
import EllipticCurves.Torsion.OddTorsionCount

/-!
# Counting `E[n]` with `(2 : F) ≠ 0` deleted, and `E[3] ≅ (ℤ/3ℤ)²` in characteristic `2`

`EllipticCurves.Torsion.XSupport` proves `Finite E[n]` and the sharp `#E[n] ≤ n²`, and
`EllipticCurves.Torsion.OddTorsionCount` proves `#E[n] = 2·#{roots of preΨₙ} + 1` and the gate
`#E[n] = n² ↔ Separable preΨₙ` at an odd index.  Every one of those four statements binds
`(2 : F) ≠ 0`, and in all four the hypothesis has exactly one source: the supplier
`WeierstrassCurve.Affine.ψ_evalEval_eq_zero_of_nsmul_eq_zero`, which used to need it.

`EllipticCurves.Torsion.NsmulOrderCharFree` removed that need.  Its
`ψ_evalEval_eq_zero_of_nsmul_eq_zero'` is `n • P = 0 → ψₙ(P) = 0` at **every** point of **every**
curve over **every** field, with no hypothesis on `2` and nothing in its place.  This file spends
it, and the whole counting lane comes out unconditional.

## What is proved here

* `card_torsion_le_sq'` — **`#E[n] ≤ n²` whenever `(n : F) ≠ 0`**, with no hypothesis on `2`;
  `finite_torsion_of_intCast_ne_zero'` is finiteness under the same hypothesis.
* `card_torsion_odd'` and `card_torsion_eq_sq_iff_separable_preΨ'` — **`#E[n] = n²` is exactly
  separability of `preΨₙ`**, at odd `n` with `(n : F) ≠ 0` over an algebraically closed field,
  with no hypothesis on `2`.
* `nonempty_torsion_addEquiv_of_odd_of_separable` — **`E[n] ≃+ ℤ/nℤ × ℤ/nℤ`** at odd `n` with
  `(n : F) ≠ 0` over an algebraically closed field, given `Separable preΨₙ` and `Separable preΨ_q`
  at every prime `q ∣ n`, with no hypothesis on `2`.
* `separable_Ψ₃_of_two_eq_zero` — **`Ψ₃` is separable in characteristic `2`**, for every elliptic
  curve over every field with `2 = 0`, and hence `card_torsion_three_of_two_eq_zero`
  (`#E[3] = 9`) and `nonempty_torsion_three_addEquiv_of_two_eq_zero` (`E[3] ≃+ (ℤ/3ℤ)²`) over an
  algebraically closed field of characteristic `2`.
* `nonempty_torsion_three_pow_addEquiv_of_two_eq_zero` and `card_torsion_three_pow_of_two_eq_zero`
  — **the whole `3`-primary tower in characteristic `2`**: `E[3^k] ≃+ (ℤ/3^kℤ)²` and
  `#E[3^k] = (3^k)²` at **every** `k`, over an algebraically closed field with `2 = 0`.  These
  consume `EllipticCurves.Torsion.PrimaryTower`, which binds no hypothesis on `2` at all, so
  the single count at `k = 1` is the whole price of the tower.

## Why none of this is an edit to the file it generalises

`EllipticCurves.Torsion.NsmulOrderCharFree` imports
`EllipticCurves.Torsion.NsmulLadderOmegaStepDvd`, which sits **above** the whole `ω` tower, and
that tower sits above `EllipticCurves.Torsion.NsmulOrder`, which
`EllipticCurves.Torsion.XSupport` imports and `EllipticCurves.Torsion.OddTorsionCount` imports
through it.  So the unconditional supplier is not visible in either of the two files whose
theorems are generalised below, and *"delete the hypothesis in place"* is unavailable for the same
reason it was unavailable to `NsmulOrderCharFree` itself.  **No landed file is edited by this one
and no landed signature changes.**

## The two hypotheses that are *not* removed, and why neither is a gap

* **`(n : F) ≠ 0` is sharp** and is untouched: it is what makes `ΨSqₙ` and `preΨₙ` nonzero
  polynomials, and without it the `x`-support is all of `F`.
* ⚠️ **At an even index there is nothing to remove.**  `(n : F) ≠ 0` at even `n` *implies*
  `(2 : F) ≠ 0`, since `n = m + m` makes `(n : F)` a multiple of `(2 : F)`.  So the even branch of
  `card_torsion_le_sq'` may use the landed even-parity argument — which needs `Ψ₂Sq ≠ 0` and
  therefore `(4 : F) ≠ 0` — and does: the hypothesis is **derived inside the branch that reaches
  it** rather than assumed.  This is why the bound below is stated at every `n` and not only at
  odd `n`.
* ⚠️ The `2`-torsion branch of the dictionary is the one place the argument is genuinely new.
  `nsmul_eq_zero_iff_ψ_evalEval_eq_zero'` keeps `ψ₂(x, y) ≠ 0`, which in characteristic `2` reads
  `a₁x + a₃ ≠ 0`; at a point where it fails, **both sides of the odd-index dictionary are false**,
  the `←` because a root of `preΨₙ` at odd `n` is never a root of `Ψ₂Sq`
  (`eval_Ψ₂Sq_ne_zero_of_eval_preΨ_eq_zero`, which binds no hypothesis on `2`) and the `→` by the
  unconditional supplier.  So no hypothesis replaces `h2` in
  `nsmul_eq_zero_iff_eval_preΨ_eq_zero'`.

## ⚠️ What is **not** proved here

* **`#E[n] = n²` at a general odd `n` in characteristic `2`.**  What is proved is the
  *equivalence* with `Separable preΨₙ`, plus the one family `n = 3^k` above; the separability
  itself is the Wronskian lane
  (`EllipticCurves.Torsion.OmegaPairCoprime`, `EllipticCurves.Torsion.WronskianSeparable`,
  `EllipticCurves.Torsion.OmegaChordSum`), whose own `(2 : F) ≠ 0` this file does not touch.  ⚠️ So
  `card_torsion_eq_sq_of_odd` is **unchanged**, and the statements below that consume separability
  take it as a hypothesis rather than discharging it.
* **`Separable Ψ₃` at `(3 : F) ≠ 0` in general.**  The characteristic-`2` certificate below is one
  `linear_combination`; the general statement is a resultant computation and is not attempted.
* **Anything at `n` even beyond the bound**, anything about the `2`-primary tower in
  characteristic `2` (where `#E[2^a] = 4^a` is false), and anything at `n = char F`.

## References

Silverman, *The Arithmetic of Elliptic Curves*, III.6.4 and III.7.1 for the classical statement
that `E[n] ≅ (ℤ/nℤ)²` whenever `char F ∤ n`, with no condition on `2`.
-/

open Polynomial

namespace WeierstrassCurve.Affine

variable {F : Type*} [Field F] {W : Affine F}

/-! ## The `x`-support of `E[n]`, with `(2 : F) ≠ 0` deleted -/

/-- A nonzero polynomial over a field has at most `natDegree` many distinct roots.

⚠️ This is `EllipticCurves.Torsion.XSupport`'s helper of the same name, which is `private` there
and so cannot be consumed from here.  It is re-declared rather than moved: moving it would edit a
landed file, which this round is scoped out of. -/
private theorem ncard_setOf_isRoot_le {p : F[X]} (hp : p ≠ 0) :
    {x : F | p.IsRoot x}.ncard ≤ p.natDegree := by
  classical
  have hset : {x : F | p.IsRoot x} = (p.roots.toFinset : Set F) := by
    ext x; simp [mem_roots hp]
  rw [hset, Set.ncard_coe_finset]
  exact (Multiset.toFinset_card_le _).trans p.card_roots'

variable [DecidableEq F]

/-- **Every nonzero affine `n`-torsion point has its `x`-coordinate in `torsionXSupport n`**, at
every index and with no hypothesis on the field —
`EllipticCurves.Torsion.XSupport`'s `mem_torsionXSupport_of_mem_torsion` with `(2 : F) ≠ 0`
deleted.

The supplier is `ψ_evalEval_eq_zero_of_nsmul_eq_zero'`, which gives `ψₙ(x, y) = 0` at the index `n`
itself with no hypothesis on `2`; squaring with `ψ_sq_evalEval` moves it onto the `x`-axis. -/
theorem mem_torsionXSupport_of_mem_torsion' {n : ℕ} ⦃x y : F⦄ ⦃h : W.Nonsingular x y⦄
    (hP : (.some x y h : W.Point) ∈ W.torsion n) : x ∈ W.torsionXSupport (n : ℤ) := by
  have hψ := ψ_evalEval_eq_zero_of_nsmul_eq_zero' h (mem_torsion_iff.mp hP)
  have hsq := ψ_sq_evalEval h.left (n : ℤ)
  rw [hψ] at hsq
  simpa [torsionXSupport, IsRoot] using hsq.symm

/-- The split form of `mem_torsionXSupport_of_mem_torsion'`: the `x`-coordinate is a root of
`preΨₙ` **or** of `Ψ₂Sq`, from the factorisation `ΨSqₙ = preΨₙ² · Ψ₂Sq` at even `n` —
`EllipticCurves.Torsion.XSupport`'s `mem_preΨ_union_Ψ₂Sq_of_mem_torsion` with `(2 : F) ≠ 0`
deleted.

⚠️ Stated at every `n` rather than only at even `n`, because that is the shape
`card_torsion_le_of_xCoords_of_selfNeg` consumes; at odd `n` the proof always takes the first
alternative. -/
theorem mem_preΨ_union_Ψ₂Sq_of_mem_torsion' {n : ℕ} ⦃x y : F⦄ ⦃h : W.Nonsingular x y⦄
    (hP : (.some x y h : W.Point) ∈ W.torsion n) :
    x ∈ {x : F | (W.preΨ (n : ℤ)).IsRoot x} ∪ {x : F | W.Ψ₂Sq.IsRoot x} := by
  have hx := mem_torsionXSupport_of_mem_torsion' hP
  rw [torsionXSupport, Set.mem_setOf_eq, IsRoot, ΨSq, eval_mul, eval_pow] at hx
  rcases mul_eq_zero.mp hx with hp | hq
  · exact Or.inl (pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hp)
  · by_cases he : Even (n : ℤ)
    · rw [if_pos he] at hq
      exact Or.inr hq
    · rw [if_neg he] at hq
      simp at hq

/-- **`E[n]` is finite whenever `(n : F) ≠ 0`**, over every field and at every index —
`EllipticCurves.Torsion.XSupport`'s `finite_torsion_of_intCast_ne_zero` with `(2 : F) ≠ 0`
deleted.

⚠️ In characteristic `2` the tree already had this at `n = 3`, so what is new here is every
index with `(n : F) ≠ 0` at once rather than a first one.
`EllipticCurves.Torsion.ThreeTorsion`'s `finite_torsion_three` binds `(3 : F) ≠ 0` alone, which
`three_ne_zero_of_two_eq_zero` below discharges at `2 = 0`, and `card_torsion_three_le` beside
it gives `#E[3] ≤ 9` the same way.  ⚠️ **And the landed reach is wider than that one index**:
`EllipticCurves.Torsion.Multiplicative`'s `finite_torsion_mul` takes finiteness as a hypothesis
and binds nothing, so every power of `3` came with it — `Finite E[9]` at `2 = 0` is two of
those composed. -/
theorem finite_torsion_of_intCast_ne_zero' {n : ℕ} (hn : (n : F) ≠ 0) :
    Finite (W.torsion n) :=
  W.finite_torsion_of_xCoords (finite_torsionXSupport (by exact_mod_cast hn))
    (mem_torsionXSupport_of_mem_torsion')

/-- **`#E[n] ≤ n²` whenever `(n : F) ≠ 0`**, over every field and at every index —
`EllipticCurves.Torsion.XSupport`'s `card_torsion_le_sq` with `(2 : F) ≠ 0` deleted and nothing in
its place.

Both parities take the landed routes.  At odd `n` the support is the root set of `preΨₙ`, of degree
`(n² − 1)/2`, and two points per fibre plus `O` give `n²`.  ⚠️ **At even `n` the deleted hypothesis
is derived rather than assumed**: `n = m + m` makes `(n : F)` a multiple of `(2 : F)`, so
`(n : F) ≠ 0` forces `(2 : F) ≠ 0` inside that branch, which is what the `Ψ₂Sq ≠ 0` of the
even-parity argument needs.  So the bound is unconditional although its even half still spends a
hypothesis on `2` — the hypothesis is just no longer one the caller has to supply.

⚠️ This is the **upper** bound only; the matching `≥` is the separability gate below. -/
theorem card_torsion_le_sq' {n : ℕ} (hn : (n : F) ≠ 0) : Nat.card (W.torsion n) ≤ n ^ 2 := by
  have hn' : ((n : ℤ) : F) ≠ 0 := by exact_mod_cast hn
  have hdeg := (ncard_setOf_isRoot_le (W.preΨ_ne_zero hn')).trans (W.natDegree_preΨ_le (n : ℤ))
  rw [Int.natAbs_natCast] at hdeg
  rcases Nat.even_or_odd n with he | ho
  -- Even `n`: `(n : F) ≠ 0` forces `(2 : F) ≠ 0`, and the roots of `Ψ₂Sq` are the
  -- `x`-coordinates of `2`-torsion points and are charged one point each.
  · have h2 : (2 : F) ≠ 0 := fun h => hn (by
      obtain ⟨m, rfl⟩ := he
      push_cast
      linear_combination (m : F) * h)
    rw [if_pos (by exact_mod_cast he : Even ((n : ℤ)))] at hdeg
    have h₀ := (ncard_setOf_isRoot_le
      (W.Ψ₂Sq_ne_zero (four_ne_zero_of_two_ne_zero h2))).trans W.natDegree_Ψ₂Sq_le
    have hcard := W.card_torsion_le_of_xCoords_of_selfNeg (n := n)
      (finite_setOf_isRoot (W.preΨ_ne_zero hn'))
      (finite_setOf_isRoot (W.Ψ₂Sq_ne_zero (four_ne_zero_of_two_ne_zero h2)))
      (mem_preΨ_union_Ψ₂Sq_of_mem_torsion')
      (fun _ _ hns _ hx => selfNeg_of_isRoot_Ψ₂Sq hns.left hx)
    obtain ⟨m, rfl⟩ := he
    have hsq : (m + m) ^ 2 = 4 * m ^ 2 := by ring
    have hm : 1 ≤ m := by
      rcases Nat.eq_zero_or_pos m with rfl | hm
      · simp at hn
      · exact hm
    rw [hsq] at hdeg ⊢
    have : 1 ≤ m ^ 2 := Nat.one_le_pow _ _ (by omega)
    omega
  -- Odd `n`: the support is the root set of `preΨₙ` outright.
  · have hoZ : Odd ((n : ℤ)) := by exact_mod_cast ho
    rw [if_neg (Int.not_even_iff_odd.mpr hoZ)] at hdeg
    have hcard := W.card_torsion_le_of_xCoords (finite_setOf_isRoot (W.preΨ_ne_zero hn'))
      (fun _ _ _ hP => by
        have := mem_torsionXSupport_of_mem_torsion' hP
        rwa [torsionXSupport_of_odd hoZ] at this)
    obtain ⟨m, rfl⟩ := ho
    have hsq : (2 * m + 1) ^ 2 = 4 * m ^ 2 + 4 * m + 1 := by ring
    rw [hsq] at hdeg ⊢
    omega

/-! ## The exact count at an odd index, with `(2 : F) ≠ 0` deleted -/

omit [DecidableEq F] in
/-- Finiteness of the root subtype of a nonzero polynomial.

⚠️ `EllipticCurves.Torsion.OddTorsionCount`'s helper of the same name is `private` there; as with
`ncard_setOf_isRoot_le` above, it is re-declared rather than moved. -/
private lemma finite_root_subtype {p : F[X]} (hp : p ≠ 0) : Finite {x : F // p.eval x = 0} :=
  Set.finite_coe_iff.mpr (finite_setOf_isRoot hp)

/-- `2·((n² − 1)/2) + 1 = n²` at odd `n`, over `ℕ` with its truncated division.

⚠️ `EllipticCurves.Torsion.OddTorsionCount`'s helper of the same name is `private` there. -/
private lemma two_mul_pred_sq_div_two_add_one {n : ℕ} (hn : Odd n) :
    2 * ((n ^ 2 - 1) / 2) + 1 = n ^ 2 := by
  obtain ⟨k, hk⟩ := hn
  have hsq : n ^ 2 = 4 * k ^ 2 + 4 * k + 1 := by subst hk; ring
  have hdiv : (n ^ 2 - 1) / 2 = 2 * k ^ 2 + 2 * k := by
    rw [hsq]
    omega
  omega

section Count

variable [IsAlgClosed F] [W.IsElliptic]

/-- **`n • (x, y) = 0 ↔ preΨₙ(x) = 0`** at an odd index and at every point of `W`, over an
algebraically closed field, with `(2 : F) ≠ 0` deleted —
`EllipticCurves.Torsion.OddTorsionCount`'s `nsmul_eq_zero_iff_eval_preΨ_eq_zero` without its
hypothesis on `2`.

Away from `2`-torsion this is `nsmul_eq_zero_iff_ψ_evalEval_eq_zero'` moved onto the `x`-axis:
`ψₙ² = ΨSqₙ = preΨₙ²` at odd `n`, and a field has no zero divisors.  ⚠️ **At a `2`-torsion point
both sides are false**, so the equivalence holds there too and needs no hypothesis in place of
`h2`: a root of `preΨₙ` at odd `n` is never a root of `Ψ₂Sq`
(`eval_Ψ₂Sq_ne_zero_of_eval_preΨ_eq_zero`) while `ψ₂(x, y) = 0` makes it one, and `n • P = 0` would
force `ψₙ(x, y) = 0` by `ψ_evalEval_eq_zero_of_nsmul_eq_zero'` and so put `x` among those roots.

⚠️ **It keeps `[IsAlgClosed F]`, which the landed form explicitly omits.**  That is where the
`2`-torsion branch above gets `eval_Ψ₂Sq_ne_zero_of_eval_preΨ_eq_zero`, whose closure-free sibling
`eval_Ψ₂Sq_ne_zero_of_eval_preΨ_eq_zero'` buys `(2 : F) ≠ 0` back and so cannot be used here.
Every consumer in this file is over a closed field anyway. -/
theorem nsmul_eq_zero_iff_eval_preΨ_eq_zero' {n : ℕ} (hn : Odd n) {x y : F}
    (hns : W.Nonsingular x y) :
    ((n • Point.some x y hns : W.Point) = 0) ↔ (W.preΨ (n : ℤ)).eval x = 0 := by
  have key := ψ_sq_evalEval hns.left (n : ℤ)
  rw [ΨSq_natCast_eq_sq_of_odd hn, eval_pow] at key
  have hbridge : (W.ψ (n : ℤ)).evalEval x y = 0 ↔ (W.preΨ (n : ℤ)).eval x = 0 := by
    constructor
    · intro h
      rw [h, zero_pow (two_ne_zero (α := ℕ))] at key
      exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp key.symm
    · intro h
      rw [h, zero_pow (two_ne_zero (α := ℕ))] at key
      exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp key
  by_cases ht : (W.ψ 2).evalEval x y = 0
  · have hfalse : (W.preΨ (n : ℤ)).eval x ≠ 0 := fun hpre =>
      eval_Ψ₂Sq_ne_zero_of_eval_preΨ_eq_zero hn hpre
        (by rw [← ΨSq_two, ← ψ_sq_evalEval hns.left, ht]; ring)
    exact ⟨fun hz => absurd (hbridge.mp (ψ_evalEval_eq_zero_of_nsmul_eq_zero' hns hz)) hfalse,
      fun h => absurd h hfalse⟩
  · rw [nsmul_eq_zero_iff_ψ_evalEval_eq_zero' hns ht n, hbridge]

variable (W) in
/-- **The `n`-torsion point above a root of `preΨₙ` selected by a `Bool`**, with `none` sent to the
point at infinity — `EllipticCurves.Torsion.OddTorsionCount`'s `torsionOddOfRoot` with
`(2 : F) ≠ 0` deleted.  At an odd index this exhausts `E[n]`
(`torsionOddOfRoot_bijective'`). -/
noncomputable def torsionOddOfRoot' {n : ℕ} (hn : Odd n) :
    Option ({x : F // (W.preΨ (n : ℤ)).eval x = 0} × Bool) → W.torsion n
  | none => 0
  | some (x, b) =>
      ⟨Point.some x.1 (W.fibreY x.1 b) (W.nonsingular_fibreY x.1 b),
        mem_torsion_iff.mpr ((nsmul_eq_zero_iff_eval_preΨ_eq_zero' hn _).mpr x.2)⟩

/-- `torsionOddOfRoot'` is a bijection: the fibre data above a root of `preΨₙ` is exactly a sign,
by `fibreY_injective`, and every nonzero `n`-torsion point arises, by
`nsmul_eq_zero_iff_eval_preΨ_eq_zero'`. -/
lemma torsionOddOfRoot_bijective' {n : ℕ} (hn : Odd n) :
    Function.Bijective (torsionOddOfRoot' W hn) := by
  constructor
  · rintro (_ | ⟨⟨x₁, hx₁⟩, b₁⟩) (_ | ⟨⟨x₂, hx₂⟩, b₂⟩) hab
    · rfl
    · exact absurd (congrArg Subtype.val hab).symm (Point.some_ne_zero _)
    · exact absurd (congrArg Subtype.val hab) (Point.some_ne_zero _)
    · have hv := congrArg Subtype.val hab
      rw [torsionOddOfRoot', torsionOddOfRoot', Point.some.injEq] at hv
      obtain ⟨rfl, hy⟩ := hv
      have hb : b₁ = b₂ :=
        fibreY_injective (eval_Ψ₂Sq_ne_zero_of_eval_preΨ_eq_zero hn hx₁) hy
      subst hb
      rfl
  · rintro ⟨(_ | ⟨x, y, hns⟩), hP⟩
    · exact ⟨none, rfl⟩
    · have hx : (W.preΨ (n : ℤ)).eval x = 0 :=
        (nsmul_eq_zero_iff_eval_preΨ_eq_zero' hn hns).mp (mem_torsion_iff.mp hP)
      have hy : ∃ b : Bool, W.fibreY x b = y := by
        rcases Y_eq_of_X_eq (W.equation_someY hns.left) hns.left rfl with h | h
        · exact ⟨true, by simpa only [fibreY] using h⟩
        · exact ⟨false, by simp only [fibreY, h, negY_negY]⟩
      obtain ⟨b, hb⟩ := hy
      refine ⟨some (⟨x, hx⟩, b), Subtype.ext ?_⟩
      rw [torsionOddOfRoot']
      exact (by rintro y' h' rfl; rfl :
        ∀ (y' : F) (h' : W.Nonsingular x y'), W.fibreY x b = y' →
          Point.some x (W.fibreY x b) (W.nonsingular_fibreY x b) = Point.some x y' h')
        y hns hb

/-- **`E[n]` is the point at infinity together with two points over each root of `preΨₙ`**, at an
odd index over an algebraically closed field, with `(2 : F) ≠ 0` deleted. -/
noncomputable def torsionOddEquiv' {n : ℕ} (hn : Odd n) :
    W.torsion n ≃ Option ({x : F // (W.preΨ (n : ℤ)).eval x = 0} × Bool) :=
  (Equiv.ofBijective _ (torsionOddOfRoot_bijective' (W := W) hn)).symm

/-- **`#E[n] = 2 · #{roots of preΨₙ} + 1`** at an odd index `n` with `(n : F) ≠ 0`, over an
algebraically closed field, with `(2 : F) ≠ 0` deleted.

⚠️ An **equality**, unlike the `≤` of `card_torsion_le_sq'`: no `y`-fibre over the support
degenerates, by `eval_Ψ₂Sq_ne_zero_of_eval_preΨ_eq_zero`. -/
theorem card_torsion_odd' {n : ℕ} (hn : Odd n) (hchar : (n : F) ≠ 0) :
    Nat.card (W.torsion n) = 2 * Nat.card {x : F // (W.preΨ (n : ℤ)).eval x = 0} + 1 := by
  haveI := finite_root_subtype (W.preΨ_ne_zero (R := F) (n := (n : ℤ)) (by push_cast; exact hchar))
  rw [Nat.card_congr (torsionOddEquiv' hn), Finite.card_option, Nat.card_prod]
  simp [Nat.card_eq_fintype_card, mul_comm]

/-- **The gate, and it is an equivalence**: over an algebraically closed field, at an odd `n` with
`(n : F) ≠ 0` and with no hypothesis on `2`,

```
#E[n] = n²   ↔   preΨₙ has no repeated root.
```

This is `EllipticCurves.Torsion.OddTorsionCount`'s `card_torsion_eq_sq_iff_separable_preΨ` with
`(2 : F) ≠ 0` deleted.  ⚠️ **Read both directions, and note what the `→` now says**: any proof of
`#E[n] = n²` in characteristic `2` at an odd index *is* a proof that `preΨₙ` is separable there, so
the separability is not a convenience of the route but the content of the count. -/
theorem card_torsion_eq_sq_iff_separable_preΨ' {n : ℕ} (hn : Odd n) (hchar : (n : F) ≠ 0) :
    Nat.card (W.torsion n) = n ^ 2 ↔ (W.preΨ (n : ℤ)).Separable := by
  classical
  have hp : W.preΨ (n : ℤ) ≠ 0 := W.preΨ_ne_zero (R := F) (by push_cast; exact hchar)
  have hsplits : (W.preΨ (n : ℤ)).Splits := IsAlgClosed.splits _
  have hdeg : (W.preΨ (n : ℤ)).natDegree = (n ^ 2 - 1) / 2 := by
    rw [W.natDegree_preΨ (R := F) (by push_cast; exact hchar)]
    simp [Nat.not_even_iff_odd.mpr hn]
  have hroots : Multiset.card (W.preΨ (n : ℤ)).roots = (n ^ 2 - 1) / 2 := by
    rw [← hdeg]; exact splits_iff_card_roots.mp hsplits
  rw [card_torsion_odd' hn hchar, card_root_subtype hp, ← two_mul_pred_sq_div_two_add_one hn,
    ← hroots, ← nodup_roots_iff_of_splits hp hsplits]
  exact ⟨fun h => Multiset.toFinset_card_eq_card_iff_nodup.mp (by omega),
    fun h => by rw [Multiset.toFinset_card_of_nodup h]⟩

/-! ## The structure theorem at odd `n`, reduced to separability -/

/-- **The rank bound `#E[n][q] ≤ q²` at every prime `q`**, at odd `n` with `(n : F) ≠ 0` and with
`Separable preΨ_q` at every prime `q ∣ n`, over an algebraically closed field and with no
hypothesis on `2` — the second hypothesis of `AddCommGroup.equiv_zmod_sq_of_card_sq`.

Both branches are those of `EllipticCurves.Torsion.PrimaryTowerOdd`'s
`card_nsmul_eq_zero_torsion_le_of_odd`, with the count supplied by
`card_torsion_eq_sq_iff_separable_preΨ'` instead of by `card_torsion_eq_sq_of_odd`.  If `q ∣ n`
then an element of `E[n]` killed by `q` is a point of `E[q]`, and `q ∣ n` forces `q` odd with
`(q : F) ≠ 0`; if `q ∤ n` then `q` and `n` are coprime and the subgroup is trivial. -/
theorem card_nsmul_eq_zero_torsion_le_of_odd_of_separable {n : ℕ} (hodd : Odd n)
    (hn : (n : F) ≠ 0)
    (hsep : ∀ q : ℕ, q.Prime → q ∣ n → (W.preΨ (q : ℤ)).Separable) {q : ℕ} (hq : q.Prime) :
    Nat.card {a : W.torsion n // q • a = 0} ≤ q ^ 2 := by
  by_cases hdvd : q ∣ n
  · have hqodd : Odd q := by
      rcases Nat.even_or_odd q with he | ho
      · obtain ⟨k, rfl⟩ := hdvd
        exact absurd (he.mul_right k) (Nat.not_even_iff_odd.mpr hodd)
      · exact ho
    have hqF : (q : F) ≠ 0 := by
      intro h
      obtain ⟨k, rfl⟩ := hdvd
      exact hn (by push_cast; rw [h, zero_mul])
    haveI : Finite (W.torsion q) := finite_torsion_of_intCast_ne_zero' hqF
    have hinj : Function.Injective
        fun a : {a : W.torsion n // q • a = 0} => (⟨(a.1 : W.Point), by
          rw [mem_torsion_iff]
          exact congrArg Subtype.val a.2⟩ : W.torsion q) := by
      intro a b hab
      simp only [Subtype.mk.injEq] at hab
      exact Subtype.ext (Subtype.ext hab)
    calc Nat.card {a : W.torsion n // q • a = 0}
        ≤ Nat.card (W.torsion q) := Nat.card_le_card_of_injective _ hinj
      _ = q ^ 2 := (card_torsion_eq_sq_iff_separable_preΨ' hqodd hqF).mpr (hsep q hq hdvd)
  · have hcop : IsCoprime (q : ℤ) (n : ℤ) := by
      have hnat : Nat.Coprime q n := (Nat.Prime.coprime_iff_not_dvd hq).mpr hdvd
      simpa using Nat.isCoprime_iff_coprime.mpr hnat
    obtain ⟨u, v, huv⟩ := hcop
    have hzero : ∀ a : W.torsion n, q • a = 0 → a = 0 := by
      intro a ha
      have hqa : (q : ℤ) • a = 0 := by
        rw [show (q : ℤ) = ((q : ℕ) : ℤ) from rfl, natCast_zsmul, ha]
      have hna : (n : ℤ) • a = 0 := by
        rw [show (n : ℤ) = ((n : ℕ) : ℤ) from rfl, natCast_zsmul]
        exact nsmul_mem_torsion a
      have h1 : (1 : ℤ) • a = 0 := by
        rw [← huv, add_smul, mul_smul, mul_smul, hqa, hna, smul_zero, smul_zero, add_zero]
      simpa using h1
    have hcard1 : Nat.card {a : W.torsion n // q • a = 0} = 1 := by
      rw [Nat.card_eq_one_iff_unique]
      exact ⟨⟨fun a b => Subtype.ext ((hzero a.1 a.2).trans (hzero b.1 b.2).symm)⟩, ⟨⟨0, by simp⟩⟩⟩
    rw [hcard1]
    exact Nat.one_le_pow 2 q hq.pos

/-- **`E[n] ≃+ ℤ/nℤ × ℤ/nℤ` at every odd `n` with `(n : F) ≠ 0`**, over an algebraically closed
field, given `Separable preΨₙ` and `Separable preΨ_q` at every prime `q ∣ n`, and with no
hypothesis on `2`.

⚠️ **This is a reduction and not a discharge**: `EllipticCurves.Torsion.PrimaryTowerOdd`'s
`nonempty_torsion_addEquiv_of_odd` supplies its own count from `card_torsion_eq_sq_of_odd`, whose
`(2 : F) ≠ 0` this file does not remove, so the separability arrives here as a hypothesis.  What it
buys is that in characteristic `2` the structure theorem at odd `n` is **exactly** the separability
of `preΨ` at `n` and at the primes dividing `n` — and `separable_Ψ₃_of_two_eq_zero` below pays that
at `n = 3`.

⚠️ The two separability hypotheses are not one: `n` need not be prime, and at prime `n` the first
is the `q = n` instance of the second. -/
theorem nonempty_torsion_addEquiv_of_odd_of_separable {n : ℕ} (hodd : Odd n) (hn : (n : F) ≠ 0)
    (hsepn : (W.preΨ (n : ℤ)).Separable)
    (hsep : ∀ q : ℕ, q.Prime → q ∣ n → (W.preΨ (q : ℤ)).Separable) :
    Nonempty (W.torsion n ≃+ ZMod n × ZMod n) := by
  haveI : Finite (W.torsion n) := finite_torsion_of_intCast_ne_zero' hn
  have hn0 : 0 < n := Nat.pos_of_ne_zero (by rintro rfl; exact hn (by norm_num))
  exact AddCommGroup.equiv_zmod_sq_of_card_sq hn0 (fun a => nsmul_mem_torsion a)
    ((card_torsion_eq_sq_iff_separable_preΨ' hodd hn).mpr hsepn)
    (fun q hq => card_nsmul_eq_zero_torsion_le_of_odd_of_separable hodd hn hsep hq)

end Count

/-! ## `Ψ₃` is separable in characteristic `2` -/

section CharTwo

omit [DecidableEq F] in
/-- `(3 : F) ≠ 0` whenever `(2 : F) = 0`: there `3 = 1`.

⚠️ So characteristic `2` is inside the régime of every statement above that asks `(n : F) ≠ 0` at
`n = 3`, and no separate hypothesis on `3` is owed by anything in this section. -/
theorem three_ne_zero_of_two_eq_zero (h2 : (2 : F) = 0) : (3 : F) ≠ 0 := fun h3 =>
  one_ne_zero (α := F) (by linear_combination h3 - h2)

omit [DecidableEq F] in
/-- **A root of `Ψ₃` is never a root of `Ψ₂Sq` in characteristic `2`**, for an elliptic curve over
any field with `2 = 0`.

⚠️ **This is the characteristic-`2` counterpart of
`EllipticCurves.Torsion.ThreeTorsionStructure`'s `Ψ₂Sq_eval_ne_zero_of_root_Ψ₃`, and the two are
proved by unrelated arguments.**  That one puts the `2`-torsion `y`-coordinate
`twoTorsionY = −(a₁x + a₃)/2` above `x` and contradicts nonsingularity; ⚠️ **that point does not
exist at `2 = 0`** — `equation_twoTorsionY` binds `(2 : F) ≠ 0` — so the route does not transfer
and no point above `x` is used here at all.

What replaces it is one elimination identity.  Write `x` for the common root.  At `2 = 0` the two
hypotheses collapse to
```
b₂x² + b₆ = 0            (from Ψ₂Sq(x) = 0)
x⁴ + b₂x³ + b₄x² + b₆x + b₈ = 0     (from Ψ₃(x) = 0)
```
and then `Δ = −b₂²b₈ − 8b₄³ − 27b₆² + 9b₂b₄b₆` is a combination of the two with the coefficients
written out in the proof, so `Δ = 0` — contradicting `IsElliptic`.  ⚠️ The derivation uses the
relation `4b₈ = b₂b₆ − b₄²` **nowhere**: it reduces `Δ` by `b₆ = b₂x²` to `b₂²(b₈ + x⁴ + b₄x²)` and
then the second hypothesis turns the bracket into `b₂x³ + b₆x = 2b₂x³`, which is `0`.  ⚠️ **No case
split on `b₂ = a₁²` is needed**, although the two cases are the ordinary and supersingular ones and
the identity specialises differently in each. -/
theorem Ψ₂Sq_eval_ne_zero_of_root_Ψ₃_of_two_eq_zero [W.IsElliptic] (h2 : (2 : F) = 0) {x : F}
    (hx : W.Ψ₃.eval x = 0) : W.Ψ₂Sq.eval x ≠ 0 := by
  intro hΨ₂
  refine isUnit_iff_ne_zero.mp W.isUnit_Δ ?_
  rw [WeierstrassCurve.Ψ₂Sq] at hΨ₂
  rw [WeierstrassCurve.Ψ₃] at hx
  simp only [eval_add, eval_mul, eval_pow, eval_C, eval_X, eval_ofNat] at hx hΨ₂
  have h6 : W.b₂ * x ^ 2 + W.b₆ = 0 := by
    linear_combination hΨ₂ - (2 * x ^ 3 + W.b₄ * x) * h2
  have h4 : x ^ 4 + W.b₂ * x ^ 3 + W.b₄ * x ^ 2 + W.b₆ * x + W.b₈ = 0 := by
    linear_combination hx - (x ^ 4 + W.b₄ * x ^ 2 + W.b₆ * x) * h2
  rw [WeierstrassCurve.Δ]
  linear_combination (W.b₂ ^ 2) * h4 +
      (-27 * W.b₆ + 9 * W.b₂ * W.b₄ - W.b₂ ^ 2 * x + 27 * W.b₂ * x ^ 2) * h6 +
      (-W.b₂ ^ 2 * W.b₈ - 4 * W.b₄ ^ 3 - 14 * W.b₂ ^ 2 * x ^ 4 -
        5 * W.b₂ ^ 2 * W.b₄ * x ^ 2) * h2

omit [DecidableEq F] in
/-- `Ψ₃` is separable in characteristic `2` over an **algebraically closed** field: its derivative
is `3·Ψ₂Sq` (`derivative_Ψ₃`), the factor `3` is a unit at `2 = 0`, and the two have no common
root.  The closure is where the no-common-root criterion applies; the general field is
`separable_Ψ₃_of_two_eq_zero` below. -/
private theorem separable_Ψ₃_of_two_eq_zero_of_isAlgClosed [IsAlgClosed F] [W.IsElliptic]
    (h2 : (2 : F) = 0) : W.Ψ₃.Separable := by
  rw [Separable, Polynomial.isCoprime_iff_aeval_ne_zero_of_isAlgClosed (k := F) F]
  intro a
  simp only [aeval_def, eval₂_eq_eval_map, Algebra.algebraMap_self, Polynomial.map_id]
  by_cases hroot : W.Ψ₃.eval a = 0
  · refine Or.inr ?_
    rw [derivative_Ψ₃, eval_mul, eval_ofNat]
    exact mul_ne_zero (three_ne_zero_of_two_eq_zero h2)
      (Ψ₂Sq_eval_ne_zero_of_root_Ψ₃_of_two_eq_zero h2 hroot)
  · exact Or.inl hroot

omit [DecidableEq F] in
/-- **`Ψ₃` is separable in characteristic `2`**, for every elliptic curve over every field with
`2 = 0`.

⚠️ **The landed `separable_Ψ₃` (`EllipticCurves.Torsion.ThreeDivisionField`) binds `(2 : F) ≠ 0`
and `(3 : F) ≠ 0`, so the two statements are complementary rather than comparable**: between them
they cover every characteristic except `3`, where `Ψ₃` has degree `3` rather than `4` and the
conclusion is a different statement.  ⚠️ **This is not the general `(3 : F) ≠ 0` form**, which
would need the resultant of `Ψ₃` and `Ψ₂Sq` rather than the one `linear_combination` the `2 = 0`
case admits, and is not attempted here.

⚠️ It is stated over an arbitrary field although it is proved over `AlgebraicClosure F`: having no
common root *in `F`* would not give coprimality, since a common factor can be irreducible over `F`,
so the criterion is applied over the closure and `Polynomial.separable_map` carries the conclusion
back along `map_Ψ₃`. -/
theorem separable_Ψ₃_of_two_eq_zero [W.IsElliptic] (h2 : (2 : F) = 0) : W.Ψ₃.Separable := by
  haveI : (W⁄(AlgebraicClosure F)).IsElliptic :=
    inferInstanceAs (W.map (algebraMap F (AlgebraicClosure F))).IsElliptic
  have h2' : (2 : AlgebraicClosure F) = 0 := by
    rw [← map_ofNat (algebraMap F (AlgebraicClosure F)) 2, h2, map_zero]
  have hmap : (W⁄(AlgebraicClosure F)).Ψ₃
      = W.Ψ₃.map (algebraMap F (AlgebraicClosure F)) := map_Ψ₃ ..
  have hsep := separable_Ψ₃_of_two_eq_zero_of_isAlgClosed (W := W⁄(AlgebraicClosure F)) h2'
  rw [hmap] at hsep
  exact (Polynomial.separable_map _).mp hsep

omit [DecidableEq F] in
/-- **`preΨ₃` is separable in characteristic `2`**, `preΨ 3` and `Ψ₃` being Mathlib's two names for
one polynomial.  This is the form `card_torsion_eq_sq_iff_separable_preΨ'` consumes. -/
theorem separable_preΨ_three_of_two_eq_zero [W.IsElliptic] (h2 : (2 : F) = 0) :
    (W.preΨ (3 : ℤ)).Separable := by
  have h : W.preΨ (3 : ℤ) = W.Ψ₃ := by simp [WeierstrassCurve.preΨ]
  rw [h]
  exact separable_Ψ₃_of_two_eq_zero h2

variable [IsAlgClosed F] [W.IsElliptic]

/-- **`#E[3] = 9` in characteristic `2`**, over an algebraically closed field with `2 = 0`.

The gate `card_torsion_eq_sq_iff_separable_preΨ'` read forwards at `n = 3`, with its separability
supplied by `separable_preΨ_three_of_two_eq_zero` and its `(3 : F) ≠ 0` by
`three_ne_zero_of_two_eq_zero`.  ⚠️ **No statement of this tree reaches this count before this
file**: `card_torsion_three` and `card_torsion_eq_sq_of_odd` both bind `(2 : F) ≠ 0`, which
`2 = 0` refutes rather than fails to supply. -/
theorem card_torsion_three_of_two_eq_zero (h2 : (2 : F) = 0) : Nat.card (W.torsion 3) = 9 := by
  have h3 : ((3 : ℕ) : F) ≠ 0 := by
    rw [Nat.cast_ofNat]
    exact three_ne_zero_of_two_eq_zero h2
  have hsep : (W.preΨ ((3 : ℕ) : ℤ)).Separable := by
    rw [show (((3 : ℕ) : ℤ)) = (3 : ℤ) by norm_num]
    exact separable_preΨ_three_of_two_eq_zero h2
  have hcard := (card_torsion_eq_sq_iff_separable_preΨ' (W := W) (n := 3) (by decide) h3).mpr hsep
  rw [hcard]
  norm_num

/-- **`E[3] ≃+ ℤ/3ℤ × ℤ/3ℤ` in characteristic `2`**, over an algebraically closed field with
`2 = 0`.

⚠️ **This is the first instance of the structure theorem `E[n] ≅ (ℤ/nℤ)²` this tree proves in
characteristic `2`.**  Every landed form that supplies its own count —
`nonempty_torsion_addEquiv_of_odd`, `nonempty_torsion_addEquiv`,
`nonempty_torsion_addEquiv_zmod_sq_of_smooth`, `nonempty_torsionPow_addEquiv_of_odd` — binds
`(2 : F) ≠ 0`.  ⚠️ **Two landed forms bind no hypothesis on `2` at all** —
`EllipticCurves.Torsion.PrimaryTower`'s `nonempty_torsionPow_addEquiv` and
`EllipticCurves.Torsion.CoprimeStructure`'s `nonempty_torsion_addEquiv_zmod_sq_of_coprime` —
and neither was reachable at `2 = 0` before this count, because each takes the count it needs
as a hypothesis.  The section below hands this one to the first of them.

It is `nonempty_torsion_addEquiv_of_odd_of_separable` at `n = 3`, where the only prime divisor is
`3` itself, so the two separability hypotheses are one statement and
`separable_preΨ_three_of_two_eq_zero` pays both. -/
theorem nonempty_torsion_three_addEquiv_of_two_eq_zero (h2 : (2 : F) = 0) :
    Nonempty (W.torsion 3 ≃+ ZMod 3 × ZMod 3) := by
  have h3 : ((3 : ℕ) : F) ≠ 0 := by
    rw [Nat.cast_ofNat]
    exact three_ne_zero_of_two_eq_zero h2
  have hsep : (W.preΨ ((3 : ℕ) : ℤ)).Separable := by
    rw [show (((3 : ℕ) : ℤ)) = (3 : ℤ) by norm_num]
    exact separable_preΨ_three_of_two_eq_zero h2
  refine nonempty_torsion_addEquiv_of_odd_of_separable (W := W) (n := 3) (by decide) h3 hsep ?_
  intro q hq hdvd
  obtain rfl : q = 3 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_three).mp hdvd
  exact hsep

/-! ### The whole `3`-primary tower in characteristic `2` -/

/-- **`E[3^k] ≃+ ℤ/3^kℤ × ℤ/3^kℤ` in characteristic `2`** at every `k`, over an algebraically
closed field with `2 = 0`.

`EllipticCurves.Torsion.PrimaryTower`'s `nonempty_torsionPow_addEquiv` binds no hypothesis on
`2`: it takes `#E[p] = p²` and surjectivity of `[p]` as hypotheses instead, and at `p = 3`
both are now available at `2 = 0` — the count is `card_torsion_three_of_two_eq_zero` above and
the surjectivity is `EllipticCurves.Torsion.TriplingSurjective`'s `nsmul_three_surjective`,
which binds none either.  ⚠️ **So the tower needs no separability above `k = 1`**: every rung
is bootstrapped from the `k = 1` count, and `preΨ` at `3^k` is never asked about. -/
theorem nonempty_torsion_three_pow_addEquiv_of_two_eq_zero (h2 : (2 : F) = 0) (k : ℕ) :
    Nonempty (W.torsion (3 ^ k) ≃+ ZMod (3 ^ k) × ZMod (3 ^ k)) :=
  nonempty_torsionPow_addEquiv Nat.prime_three nsmul_three_surjective
    (card_torsion_three_of_two_eq_zero h2) k

/-- **`#E[3^k] = (3^k)²` in characteristic `2`** at every `k`, over an algebraically closed
field with `2 = 0` — `EllipticCurves.Torsion.PrimaryTower`'s `card_torsion_pow_mul_self` on
the same two inputs as the equivalence above. -/
theorem card_torsion_three_pow_of_two_eq_zero (h2 : (2 : F) = 0) (k : ℕ) :
    Nat.card (W.torsion (3 ^ k)) = 3 ^ k * 3 ^ k :=
  card_torsion_pow_mul_self nsmul_three_surjective (card_torsion_three_of_two_eq_zero h2) k

end CharTwo

/-! ## Non-vacuity: the statements above, committed on a characteristic-`2` curve -/

section Nonvacuity

open EllipticCurves.Fixture

/-- The base field really is of characteristic `2`, which is what makes the `example`s below
statements that the `(2 : F) ≠ 0` forms cannot express rather than merely fail to reach. -/
private lemma two_eq_zero_closureCharTwo : (2 : AlgebraicClosure (ZMod 2)) = 0 := by
  have : CharP (AlgebraicClosure (ZMod 2)) 2 :=
    charP_of_injective_algebraMap
      (algebraMap (ZMod 2) (AlgebraicClosure (ZMod 2))).injective 2
  exact_mod_cast CharP.cast_eq_zero (AlgebraicClosure (ZMod 2)) 2

private noncomputable instance : DecidableEq (AlgebraicClosure (ZMod 2)) := Classical.decEq _

/-- `y² + xy = x³ + 1` over `AlgebraicClosure (ZMod 2)` — `EllipticCurves.Fixture`'s
`y2AddXYEqX3AddC` at `c = 1`, the shared `a₁ ≠ 0` ordinary family.

⚠️ It is a `def` and not an `abbrev`, so the instance below is found for this name and is **not**
found for `y2AddXYEqX3AddC (AlgebraicClosure (ZMod 2)) 1`, which `EllipticCurves.Fixtures` says in
terms carries no `IsElliptic` instance anywhere in the tree.  ⚠️ `noncomputable` because
`AlgebraicClosure.instField` is. -/
private noncomputable def curveClosureCharTwo : Affine (AlgebraicClosure (ZMod 2)) :=
  y2AddXYEqX3AddC (AlgebraicClosure (ZMod 2)) 1

/-- The witness is a genuine elliptic curve: `Δ = c` wherever `2 = 0`
(`Δ_y2AddXYEqX3AddC_of_two_eq_zero`), so `c ≠ 0` is the whole condition and `one_ne_zero`
discharges it. -/
private instance : curveClosureCharTwo.IsElliptic :=
  isElliptic_y2AddXYEqX3AddC two_eq_zero_closureCharTwo one_ne_zero

/-- **`Ψ₃` is separable on `y² + xy = x³ + 1` over `AlgebraicClosure (ZMod 2)`, committed.** -/
example : curveClosureCharTwo.Ψ₃.Separable :=
  separable_Ψ₃_of_two_eq_zero two_eq_zero_closureCharTwo

/-- **`#E[3] = 9` on that curve, in characteristic `2`, committed.** -/
example : Nat.card (curveClosureCharTwo.torsion 3) = 9 :=
  card_torsion_three_of_two_eq_zero two_eq_zero_closureCharTwo

/-- **`E[3] ≃+ ℤ/3ℤ × ℤ/3ℤ` on that curve, in characteristic `2`, committed** — the structure
theorem at an index and over a field no landed form of it can be instantiated at. -/
example : Nonempty (curveClosureCharTwo.torsion 3 ≃+ ZMod 3 × ZMod 3) :=
  nonempty_torsion_three_addEquiv_of_two_eq_zero two_eq_zero_closureCharTwo

/-- **`E[9] ≃+ ℤ/9ℤ × ℤ/9ℤ` on that curve, in characteristic `2`, committed** — the `k = 2`
rung of the tower, at an index whose `preΨ` this file never asks about. -/
example : Nonempty (curveClosureCharTwo.torsion (3 ^ 2) ≃+ ZMod (3 ^ 2) × ZMod (3 ^ 2)) :=
  nonempty_torsion_three_pow_addEquiv_of_two_eq_zero two_eq_zero_closureCharTwo 2

/-- **`#E[9] = 81` on that curve, in characteristic `2`, committed.** -/
example : Nat.card (curveClosureCharTwo.torsion (3 ^ 2)) = 3 ^ 2 * 3 ^ 2 :=
  card_torsion_three_pow_of_two_eq_zero two_eq_zero_closureCharTwo 2

/-- `(5 : AlgebraicClosure (ZMod 2)) ≠ 0`: it is `1` there. -/
private lemma five_ne_zero_closureCharTwo : ((5 : ℕ) : AlgebraicClosure (ZMod 2)) ≠ 0 := by
  rw [Nat.cast_ofNat]
  intro h
  exact one_ne_zero (α := AlgebraicClosure (ZMod 2))
    (by linear_combination h - 2 * two_eq_zero_closureCharTwo)

/-- **`E[5]` is finite in characteristic `2`, committed** — an index where this file's bound is the
only statement of finiteness available, `finite_torsion_of_intCast_ne_zero` binding `(2 : F) ≠ 0`.
⚠️ At `n = 5` nothing here claims the count: that is the separability of `preΨ₅`, which this file
does not prove. -/
example : Finite (curveClosureCharTwo.torsion 5) :=
  finite_torsion_of_intCast_ne_zero' five_ne_zero_closureCharTwo

/-- **`#E[5] ≤ 25` in characteristic `2`, committed.** -/
example : Nat.card (curveClosureCharTwo.torsion 5) ≤ 5 ^ 2 :=
  card_torsion_le_sq' five_ne_zero_closureCharTwo

end Nonvacuity

/-! ## ⚠️ The next rung, and why the coprimality route to separability dies at `2 = 0` -/

section Obstruction

variable [IsAlgClosed F] [W.IsElliptic]

omit [DecidableEq F] in
/-- **In characteristic `2`, `preΩₙ` vanishes at every root of `preΨₙ`** at odd `n`, under the
`hpair` hypothesis of `EllipticCurves.Torsion.WronskianSeparable`.

⚠️ **This is an obstruction and not a step**: it says the one route this tree has to
`IsCoprime (preΨₙ) (preΩₙ)` cannot work at `2 = 0`, and `not_isCoprime_preΨ_preΩ_of_two_eq_zero`
below turns it into a refutation.

The mechanism is one cancellation.  `WeierstrassCurve.Ω_factor` at odd `n` reads
`Ψ_{n+2}·Ψ_{n−1}² − Ψ_{n−2}·Ψ_{n+1}² = ψ₂²·preΩₙ`, so at a point `(x, y)` above a root of `preΨₙ`
— where `ψₙ(x, y) = 0` — the left-hand side is `A − B` with `A = ψ_{n+2}ψ_{n−1}²` and
`B = ψ_{n−2}ψ_{n+1}²`.  `hpair` says `A = −B`, so `A − B = 2A`, and at `2 = 0` that is `0`.  Since
`ψ₂(x, y) ≠ 0` at such a point (`eval_Ψ₂Sq_ne_zero_of_eval_preΨ_eq_zero`), `preΩₙ(x) = 0`.

⚠️ **The same cancellation read forwards is what `eval_preΩ_ne_zero_of_eval_preΨ_eq_zero` spends
its `(2 : F) ≠ 0` on**: that proof derives `2·A = 0` from `preΩₙ(x) = 0` and concludes `A = 0`,
which contradicts `ψ_{n+2} ≠ 0` and `ψ_{n−1} ≠ 0`.  At `2 = 0` the derivation is not merely
unavailable, it is vacuous — and this statement is why.

⚠️ `hpair` is a **hypothesis here and is not discharged**.  It is the conclusion of
`EllipticCurves.Torsion.OmegaPairCoprime`'s `ψ_pair_of_equation`, which binds `(2 : F) ≠ 0`, so
nothing below asserts that the hypothesis is satisfiable at `2 = 0`. -/
theorem eval_preΩ_eq_zero_of_eval_preΨ_eq_zero_of_two_eq_zero (h2 : (2 : F) = 0) {n : ℕ}
    (hodd : Odd n)
    (hpair : ∀ x y : F, W.Equation x y → (W.ψ (n : ℤ)).evalEval x y = 0 →
      (W.ψ ((n : ℤ) + 2)).evalEval x y * (W.ψ ((n : ℤ) - 1)).evalEval x y ^ 2 =
        -((W.ψ ((n : ℤ) - 2)).evalEval x y * (W.ψ ((n : ℤ) + 1)).evalEval x y ^ 2))
    {x : F} (hx : (W.preΨ (n : ℤ)).eval x = 0) : (W.preΩ (n : ℤ)).eval x = 0 := by
  obtain ⟨y, hxy⟩ := exists_equation' (W := W) x
  have hΨSq : (W.ΨSq (n : ℤ)).eval x = 0 := by
    rw [ΨSq_natCast_eq_sq_of_odd hodd, eval_pow, hx, zero_pow (two_ne_zero (α := ℕ))]
  have hψn : (W.ψ (n : ℤ)).evalEval x y = 0 :=
    pow_eq_zero_iff (n := 2) (by norm_num) |>.mp (by rw [ψ_sq_evalEval hxy, hΨSq])
  have hΨ₂ : W.Ψ₂Sq.eval x ≠ 0 := eval_Ψ₂Sq_ne_zero_of_eval_preΨ_eq_zero hodd hx
  have hψ₂ : (W.ψ 2).evalEval x y ≠ 0 := fun hc => hΨ₂ (by
    rw [← ΨSq_two, ← ψ_sq_evalEval hxy, hc]; ring)
  have hfac := congrArg (Polynomial.evalEval x y) (W.Ω_factor (n : ℤ))
  rw [if_neg (Int.not_even_iff_odd.mpr (by exact_mod_cast hodd : Odd ((n : ℤ))))] at hfac
  simp only [evalEval_mul, evalEval_sub, evalEval_pow, evalEval_C, ← ψ_evalEval hxy,
    ← ψ_two] at hfac
  have hzero : (W.ψ 2).evalEval x y ^ 2 * (W.preΩ (n : ℤ)).eval x = 0 := by
    linear_combination -hfac + hpair x y hxy hψn +
      (-((W.ψ ((n : ℤ) - 2)).evalEval x y * (W.ψ ((n : ℤ) + 1)).evalEval x y ^ 2)) * h2
  exact (mul_eq_zero.mp hzero).resolve_left (pow_ne_zero 2 hψ₂)

omit [DecidableEq F] in
/-- **`preΨₙ` and `preΩₙ` are NOT coprime in characteristic `2`** at odd `n ≠ 1` with
`(n : F) ≠ 0` over an algebraically closed field, under the same `hpair`.

⚠️ **So the landed route to `Separable preΨₙ` — the Wronskian identity plus
`isCoprime_preΨ_preΩ_of_odd` — is not merely unproved at `2 = 0`: its middle term is false there,
conditionally on `hpair`.** A worker taking `#2340`'s `#E[n] = n²` at odd `n` in characteristic `2`
must therefore prove separability some other way; the equivalence
`card_torsion_eq_sq_iff_separable_preΨ'` above is unaffected, and `separable_Ψ₃_of_two_eq_zero` is
an example of a route that does work (a direct elimination against `Δ`).

`preΨₙ` has degree `(n² − 1)/2 ≥ 4` at odd `n ≥ 3` with `(n : F) ≠ 0`, so over an algebraically
closed field it has a root; `preΩₙ` vanishes there too, and a Bézout identity evaluated at that
root would read `0 = 1`.  ⚠️ `n ≠ 1` is sharp for this argument rather than incidental: `preΨ₁ = 1`
has no root at all. -/
theorem not_isCoprime_preΨ_preΩ_of_two_eq_zero (h2 : (2 : F) = 0) {n : ℕ} (hodd : Odd n)
    (hn : (n : F) ≠ 0) (hn1 : n ≠ 1)
    (hpair : ∀ x y : F, W.Equation x y → (W.ψ (n : ℤ)).evalEval x y = 0 →
      (W.ψ ((n : ℤ) + 2)).evalEval x y * (W.ψ ((n : ℤ) - 1)).evalEval x y ^ 2 =
        -((W.ψ ((n : ℤ) - 2)).evalEval x y * (W.ψ ((n : ℤ) + 1)).evalEval x y ^ 2)) :
    ¬ IsCoprime (W.preΨ (n : ℤ)) (W.preΩ (n : ℤ)) := by
  intro hcop
  have hnz : W.preΨ (n : ℤ) ≠ 0 := W.preΨ_ne_zero (R := F) (by push_cast; exact hn)
  have hdeg : (W.preΨ (n : ℤ)).natDegree = (n ^ 2 - 1) / 2 := by
    rw [W.natDegree_preΨ (R := F) (by push_cast; exact hn)]
    simp [Nat.not_even_iff_odd.mpr hodd]
  have hpos : 0 < (W.preΨ (n : ℤ)).natDegree := by
    obtain ⟨k, rfl⟩ := hodd
    rw [hdeg]
    have hk : 1 ≤ k := by omega
    have hsq : (2 * k + 1) ^ 2 = 4 * k ^ 2 + 4 * k + 1 := by ring
    rw [hsq]
    omega
  have hdeg0 : (W.preΨ (n : ℤ)).degree ≠ 0 := by
    rw [Polynomial.degree_eq_natDegree hnz]
    exact_mod_cast Nat.pos_iff_ne_zero.mp hpos
  obtain ⟨x, hx⟩ := IsAlgClosed.exists_root (W.preΨ (n : ℤ)) hdeg0
  have hxe : (W.preΨ (n : ℤ)).eval x = 0 := hx
  have hΩ := eval_preΩ_eq_zero_of_eval_preΨ_eq_zero_of_two_eq_zero h2 hodd hpair hxe
  obtain ⟨u, v, huv⟩ := hcop
  have hone := congrArg (Polynomial.eval x) huv
  simp only [eval_add, eval_mul, eval_one, hxe, hΩ, mul_zero, add_zero] at hone
  exact zero_ne_one hone

end Obstruction

end WeierstrassCurve.Affine
