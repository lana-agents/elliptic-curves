/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import EllipticCurves.Torsion.PrimaryTowerAlgClosed
import EllipticCurves.Torsion.XSupport

/-!
# `#E[n] = n²` at odd `n` is exactly separability of `preΨₙ`

`EllipticCurves.Torsion.XSupport` proves `#E[n] ≤ n²`.  `EllipticCurves.Torsion.PrimaryTower` takes
the matching equality `#E[p] = p²` as a hypothesis, and its gate list records that it does not
follow from surjectivity of `[p]`.  This file settles what it *does* follow from, at an odd index
over an algebraically closed field: **exactly the statement that `preΨₙ` has no repeated root**.

⚠️ That is the route by which the equality was eventually proved: the separability side is
discharged in `EllipticCurves.Torsion.WronskianSeparable` from the Wronskian identity, which
`EllipticCurves.Torsion.OmegaChordSum` proves outright, giving `card_torsion_eq_sq_of_odd`.  The
`iff` below is still the load-bearing step and is still stated as an `iff` — it is what says there
is no cheaper road.

## The correspondence

At an odd `n` the `x`-coordinate is a `2`-to-`1` map from the nonzero `n`-torsion onto the roots of
`preΨₙ`, with **no degenerate fibre**:

* `ΨSqₙ = preΨₙ²` at odd `n` by Mathlib's definition (`ΨSq_ofNat`, whose `if Even n then Ψ₂Sq
  else 1` factor is `1` on the odd branch),
  and `ψₙ(x, y)² = ΨSqₙ(x)`, so `n • (x, y) = 0 ↔ preΨₙ(x) = 0`
  (`nsmul_eq_zero_iff_eval_preΨ_eq_zero`), using the dictionary
  `nsmul_eq_zero_iff_ψ_evalEval_eq_zero_of_isElliptic` at *every* point;
* a root of `preΨₙ` is never a root of `Ψ₂Sq` (`eval_Ψ₂Sq_ne_zero_of_eval_preΨ_eq_zero`), so the two
  points above it are distinct.  ⚠️ This is the only step that is not bookkeeping, and it is where
  oddness is spent: such a point would be `2`-torsion, and at a `2`-torsion point `ψ` does not
  vanish at an odd index (`ψ_odd_evalEval_ne_zero_of_ψ_two_evalEval_eq_zero`).

`torsionOddEquiv` packages this as a bijection `E[n] ≃ Option ({x // preΨₙ(x) = 0} × Bool)`, in the
style of `torsionTwoEquiv` (`EllipticCurves.Torsion.TwoTorsion`), and `card_torsion_odd` reads the
count off it:

```
Nat.card (W.torsion n) = 2 * Nat.card {x // (W.preΨ n).eval x = 0} + 1 .
```

⚠️ That is an **equality**, not the inequality of `card_torsion_le_sq`, and the equality is the
point: over an algebraically closed field the root count of the nonzero polynomial `preΨₙ` is its
`natDegree = (n² − 1)/2` **iff** it has no repeated root, so

> **`#E[n] = n²` ↔ `Separable (W.preΨ n)`** (`card_torsion_eq_sq_iff_separable_preΨ`)

at every odd `n` with `char F ∤ 2n`.

⚠️ The merged `WeierstrassCurve.Affine.card_torsion_le_sq` is **not** superseded: it carries neither
`[IsAlgClosed F]` nor `[W.IsElliptic]`, and holds at every index rather than at odd ones.  It is
used below only in a consistency check — the exact count of `card_torsion_odd` must not exceed it,
and that is machine-checked rather than assumed.

## ⚠️ What this does and does not settle

* It settles that the remaining gate on the `p`-primary tower is, at an odd `p`, **a statement about
  one univariate polynomial** and nothing more.  `nonempty_torsionPow_addEquiv_of_separable` is the
  signature to read: over `F̄`, at an odd prime `p` with `char F ∤ 2p`, `E[pᵏ] ≅ (ℤ/pᵏℤ)²` is owed
  `Separable (W.preΨ p)` and nothing else.
* ⚠️ It does **not prove** `Separable (W.preΨ n)`, and asserts no route to it.  The classical
  argument is separability of the isogeny `[n]`, via `[n]∗ω = nω ≠ 0` on the invariant differential
  ([Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.4.10 and III.5.3), and this
  tree has no isogeny-degree layer.  Whether a division-polynomial-only route exists is
  **unmeasured** here.
* ⚠️ Because the statement is an `iff`, it also says there is no cheaper road: any proof of
  `#E[p] = p²` at an odd `p` over `F̄` *is* a proof that `preΨ p` is separable.  It settles in
  particular that surjectivity of `[p]` is not the missing input, on grounds that need no argument
  about images and kernels: `WeierstrassCurve.Affine.nsmul_surjective_of_two_ne_zero` is a
  **theorem** here at every `n ≠ 0` under `(2 : F) ≠ 0` alone, so if it supplied the gate the gate
  would already be discharged.  ⚠️ That is a statement about what is *available*, not a proof that
  no implication exists.
* ⚠️ **Odd `n` only**, deliberately.  At even `n` the roots of `Ψ₂Sq` *are* roots of `ΨSqₙ`, their
  fibres are singletons, and the count picks up the `+3` that `EllipticCurves.Torsion.XSupport`
  describes; that is a second case with its own arithmetic and it is not what the `p`-primary tower
  at `p ≥ 5` needs.  The `2`-primary tower is closed by hand elsewhere.

## Main definitions

* `WeierstrassCurve.Affine.torsionOddOfRoot` : the `n`-torsion point above a root of `preΨₙ`
  selected by a `Bool`, with `none` sent to the point at infinity.
* `WeierstrassCurve.Affine.torsionOddEquiv` : the bijection
  `E[n] ≃ Option ({x // preΨₙ(x) = 0} × Bool)`.

## Main statements

* `WeierstrassCurve.Affine.eval_Ψ₂Sq_ne_zero_of_eval_preΨ_eq_zero` : at odd `n`, a root of `preΨₙ`
  is not a root of `Ψ₂Sq`.
* `WeierstrassCurve.Affine.nsmul_eq_zero_iff_eval_preΨ_eq_zero` : `n • (x, y) = 0 ↔ preΨₙ(x) = 0`.
* `WeierstrassCurve.Affine.card_torsion_odd` : `#E[n] = 2 · #{roots of preΨₙ} + 1`.
* **`WeierstrassCurve.Affine.card_torsion_eq_sq_iff_separable_preΨ`** : `#E[n] = n²` ↔
  `Separable (W.preΨ n)`.
* `WeierstrassCurve.Affine.card_torsion_pow_of_separable`,
  `WeierstrassCurve.Affine.finite_torsion_pow_of_separable`,
  **`WeierstrassCurve.Affine.nonempty_torsionPow_addEquiv_of_separable`** : the `p`-primary tower
  with the gate substituted.
* `WeierstrassCurve.Affine.separable_preΨ_three` and its `Ψ₃` form
  `WeierstrassCurve.Affine.separable_Ψ₃` : the gate read *backwards* at `n = 3` against the merged
  sharp count — this file's non-vacuity certificate.  ⚠️ A **round trip, not a new statement**:
  `WeierstrassCurve.Affine.nodup_roots_Ψ₃` (`EllipticCurves.Torsion.ThreeTorsionStructure`) is
  merged, and over `F̄` it *is* separability of `Ψ₃`, one `Polynomial.nodup_roots_iff_of_splits`
  away.  See the theorem's own docstring.

## References

* [J. H. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.4.10, III.5.3 and
  III.6, Corollary 6.4.
-/

open Polynomial

namespace WeierstrassCurve.Affine

variable {F : Type*} [Field F] {W : Affine F}

/-! ### `ΨSq` at an odd index is a square -/

/-- **`ΨSqₙ = preΨₙ²` at odd `n`.**  Mathlib's `ΨSq_ofNat` carries the factor `Ψ₂Sq` only in the
even branch, so at an odd index the `x`-support is cut out by `preΨₙ` alone. -/
theorem ΨSq_natCast_eq_sq_of_odd {n : ℕ} (hn : Odd n) : W.ΨSq (n : ℤ) = W.preΨ (n : ℤ) ^ 2 := by
  rw [ΨSq_ofNat, if_neg (Nat.not_even_iff_odd.mpr hn), mul_one, preΨ_ofNat]

/-! ### A root of `preΨₙ` is not a root of `Ψ₂Sq`, at odd `n` -/

/-- **At an odd index, a root of `preΨₙ` is not a root of `Ψ₂Sq`.**

A common root carries a point `(x, y)` of `W` (`exists_equation`) with `ψ₂(x, y) = 0` — a
`2`-torsion point — and with `ψₙ(x, y)² = ΨSqₙ(x) = preΨₙ(x)² = 0`.  But `ψ` does not vanish at an
odd index at a `2`-torsion point
(`WeierstrassCurve.Affine.ψ_odd_evalEval_ne_zero_of_ψ_two_evalEval_eq_zero`).

⚠️ This is the step that makes every `y`-fibre over the support a genuine *pair*, and so the step
that turns the counting inequality of `EllipticCurves.Torsion.XSupport` into an equality. -/
theorem eval_Ψ₂Sq_ne_zero_of_eval_preΨ_eq_zero [IsAlgClosed F] [W.IsElliptic] (h2 : (2 : F) ≠ 0)
    {n : ℕ} (hn : Odd n) {x : F} (hx : (W.preΨ (n : ℤ)).eval x = 0) : W.Ψ₂Sq.eval x ≠ 0 := by
  intro hΨ₂
  obtain ⟨y, hxy⟩ := exists_equation (W := W) h2 x
  have ht : (W.ψ 2).evalEval x y = 0 :=
    pow_eq_zero_iff (n := 2) (by norm_num) |>.mp (by rw [ψ_sq_evalEval hxy 2, ΨSq_two, hΨ₂])
  have hψn : (W.ψ (n : ℤ)).evalEval x y = 0 :=
    pow_eq_zero_iff (n := 2) (by norm_num) |>.mp (by
      rw [ψ_sq_evalEval hxy, ΨSq_natCast_eq_sq_of_odd hn, eval_pow, hx,
        zero_pow (two_ne_zero (α := ℕ))])
  obtain ⟨m, hm⟩ := hn
  refine ψ_odd_evalEval_ne_zero_of_ψ_two_evalEval_eq_zero ht
    (ψ_three_evalEval_ne_zero_of_ψ_two_evalEval_eq_zero hxy ht) m ?_
  rw [show 2 * (m : ℤ) + 1 = ((n : ℕ) : ℤ) by rw [hm]; push_cast; ring]
  exact hψn

/-! ### Counting the roots of a polynomial over an algebraically closed field -/

private lemma finite_root_subtype {p : F[X]} (hp : p ≠ 0) : Finite {x : F // p.eval x = 0} :=
  Set.Finite.to_subtype (finite_setOf_isRoot hp)

private lemma card_root_subtype [DecidableEq F] {p : F[X]} (hp : p ≠ 0) :
    Nat.card {x : F // p.eval x = 0} = p.roots.toFinset.card := by
  classical
  have h : {x : F // p.eval x = 0} ≃ {x : F // x ∈ p.roots.toFinset} :=
    Equiv.subtypeEquivRight fun x => by simp [Multiset.mem_toFinset, mem_roots hp, IsRoot.def]
  rw [Nat.card_congr h, Nat.card_eq_finsetCard]

/-! ### The dictionary in terms of `preΨ` -/

section Count

variable [DecidableEq F] [IsAlgClosed F] [W.IsElliptic]

omit [IsAlgClosed F] in
/-- **`n • (x, y) = 0 ↔ preΨₙ(x) = 0`** at an odd index and at every point of `W`.

The dictionary `nsmul_eq_zero_iff_ψ_evalEval_eq_zero_of_isElliptic` gives `n • P = 0 ↔ ψₙ(P) = 0`;
squaring moves that onto the `x`-axis, and at an odd index `ΨSqₙ` is the square of `preΨₙ`. -/
theorem nsmul_eq_zero_iff_eval_preΨ_eq_zero (h2 : (2 : F) ≠ 0) {n : ℕ} (hn : Odd n) {x y : F}
    (hns : W.Nonsingular x y) :
    ((n • Point.some x y hns : W.Point) = 0) ↔ (W.preΨ (n : ℤ)).eval x = 0 := by
  rw [nsmul_eq_zero_iff_ψ_evalEval_eq_zero_of_isElliptic h2 hns n]
  have key := ψ_sq_evalEval hns.left (n : ℤ)
  rw [ΨSq_natCast_eq_sq_of_odd hn, eval_pow] at key
  constructor
  · intro h
    rw [h, zero_pow (two_ne_zero (α := ℕ))] at key
    exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp key.symm
  · intro h
    rw [h, zero_pow (two_ne_zero (α := ℕ))] at key
    exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp key

/-! ### The two points above a root -/

variable (W) in
/-- The `y`-coordinate above `x` selected by a `Bool`: `true` picks the designated solution
`someY x` of the Weierstrass equation, `false` its negation. -/
noncomputable def fibreY (x : F) : Bool → F
  | true => W.someY x
  | false => W.negY x (W.someY x)

omit [DecidableEq F] [WeierstrassCurve.IsElliptic W] in
lemma equation_fibreY (h2 : (2 : F) ≠ 0) (x : F) (b : Bool) : W.Equation x (W.fibreY x b) := by
  obtain ⟨y, hy⟩ := exists_equation (W := W) h2 x
  cases b
  · exact (W.equation_neg x (W.someY x)).mpr (W.equation_someY hy)
  · exact W.equation_someY hy

omit [DecidableEq F] in
lemma nonsingular_fibreY (h2 : (2 : F) ≠ 0) (x : F) (b : Bool) :
    W.Nonsingular x (W.fibreY x b) :=
  equation_iff_nonsingular.mp (W.equation_fibreY h2 x b)

omit [DecidableEq F] [WeierstrassCurve.IsElliptic W] in
/-- **The two points above a root of `preΨₙ` are distinct**, because the root is not a root of
`Ψ₂Sq`: `someY x = negY x (someY x)` says exactly `ψ₂ = 2y + a₁x + a₃` vanishes there. -/
lemma fibreY_injective (h2 : (2 : F) ≠ 0) {x : F} (hΨ : W.Ψ₂Sq.eval x ≠ 0) :
    Function.Injective (W.fibreY x) := by
  have hne : W.someY x ≠ W.negY x (W.someY x) := by
    intro h
    refine hΨ ?_
    have hxy : W.Equation x (W.someY x) := by
      obtain ⟨y, hy⟩ := exists_equation (W := W) h2 x
      exact W.equation_someY hy
    have ht : (W.ψ 2).evalEval x (W.someY x) = 0 := by
      rw [ψ_two_evalEval]
      simp only [negY] at h
      linear_combination h
    rw [← ΨSq_two, ← ψ_sq_evalEval hxy 2, ht]
    ring
  rintro (_ | _) (_ | _) h
  · rfl
  · simp only [fibreY] at h
    exact absurd h.symm hne
  · simp only [fibreY] at h
    exact absurd h hne
  · rfl

/-! ### The bijection -/

variable (W) in
/-- **The `n`-torsion point above a root of `preΨₙ` selected by a `Bool`**, with `none` sent to the
point at infinity.  At an odd index this exhausts `E[n]`
(`WeierstrassCurve.Affine.torsionOddOfRoot_bijective`). -/
noncomputable def torsionOddOfRoot (h2 : (2 : F) ≠ 0) {n : ℕ} (hn : Odd n) :
    Option ({x : F // (W.preΨ (n : ℤ)).eval x = 0} × Bool) → W.torsion n
  | none => 0
  | some (x, b) =>
      ⟨Point.some x.1 (W.fibreY x.1 b) (W.nonsingular_fibreY h2 x.1 b),
        mem_torsion_iff.mpr ((nsmul_eq_zero_iff_eval_preΨ_eq_zero h2 hn _).mpr x.2)⟩

lemma torsionOddOfRoot_bijective (h2 : (2 : F) ≠ 0) {n : ℕ} (hn : Odd n) :
    Function.Bijective (torsionOddOfRoot W h2 hn) := by
  constructor
  · rintro (_ | ⟨⟨x₁, hx₁⟩, b₁⟩) (_ | ⟨⟨x₂, hx₂⟩, b₂⟩) hab
    · rfl
    · exact absurd (congrArg Subtype.val hab).symm (Point.some_ne_zero _)
    · exact absurd (congrArg Subtype.val hab) (Point.some_ne_zero _)
    · have hv := congrArg Subtype.val hab
      rw [torsionOddOfRoot, torsionOddOfRoot, Point.some.injEq] at hv
      obtain ⟨rfl, hy⟩ := hv
      have hb : b₁ = b₂ :=
        fibreY_injective h2 (eval_Ψ₂Sq_ne_zero_of_eval_preΨ_eq_zero h2 hn hx₁) hy
      subst hb
      rfl
  · rintro ⟨(_ | ⟨x, y, hns⟩), hP⟩
    · exact ⟨none, rfl⟩
    · have hx : (W.preΨ (n : ℤ)).eval x = 0 :=
        (nsmul_eq_zero_iff_eval_preΨ_eq_zero h2 hn hns).mp (mem_torsion_iff.mp hP)
      have hy : ∃ b : Bool, W.fibreY x b = y := by
        rcases Y_eq_of_X_eq (W.equation_someY hns.left) hns.left rfl with h | h
        · exact ⟨true, by simpa only [fibreY] using h⟩
        · exact ⟨false, by simp only [fibreY, h, negY_negY]⟩
      obtain ⟨b, hb⟩ := hy
      refine ⟨some (⟨x, hx⟩, b), Subtype.ext ?_⟩
      rw [torsionOddOfRoot]
      exact (by rintro y' h' rfl; rfl :
        ∀ (y' : F) (h' : W.Nonsingular x y'), W.fibreY x b = y' →
          Point.some x (W.fibreY x b) (W.nonsingular_fibreY h2 x b) = Point.some x y' h')
        y hns hb

/-- **`E[n]` is the point at infinity together with two points over each root of `preΨₙ`**, at an
odd index over an algebraically closed field of characteristic `≠ 2`. -/
noncomputable def torsionOddEquiv (h2 : (2 : F) ≠ 0) {n : ℕ} (hn : Odd n) :
    W.torsion n ≃ Option ({x : F // (W.preΨ (n : ℤ)).eval x = 0} × Bool) :=
  (Equiv.ofBijective _ (torsionOddOfRoot_bijective (W := W) h2 hn)).symm

/-! ### The count -/

/-- **`#E[n] = 2 · #{roots of preΨₙ} + 1`** at an odd index.

⚠️ An **equality**, unlike the `≤` of `EllipticCurves.Torsion.XSupport`: no `y`-fibre over the
support degenerates, by `eval_Ψ₂Sq_ne_zero_of_eval_preΨ_eq_zero`. -/
theorem card_torsion_odd (h2 : (2 : F) ≠ 0) {n : ℕ} (hn : Odd n) (hchar : (n : F) ≠ 0) :
    Nat.card (W.torsion n) = 2 * Nat.card {x : F // (W.preΨ (n : ℤ)).eval x = 0} + 1 := by
  haveI := finite_root_subtype (W.preΨ_ne_zero (R := F) (n := (n : ℤ)) (by push_cast; exact hchar))
  rw [Nat.card_congr (torsionOddEquiv h2 hn), Finite.card_option, Nat.card_prod]
  simp [Nat.card_eq_fintype_card, mul_comm]

/-! ### The gate: `#E[n] = n²` is separability of `preΨₙ` -/

private lemma two_mul_pred_sq_div_two_add_one {n : ℕ} (hn : Odd n) :
    2 * ((n ^ 2 - 1) / 2) + 1 = n ^ 2 := by
  obtain ⟨k, hk⟩ := hn
  have hsq : n ^ 2 = 4 * k ^ 2 + 4 * k + 1 := by subst hk; ring
  have hdiv : (n ^ 2 - 1) / 2 = 2 * k ^ 2 + 2 * k := by
    rw [hsq]
    omega
  omega

/-- **The gate, and it is an equivalence**: over an algebraically closed field of characteristic
`≠ 2`, at an odd `n` with `char F ∤ n`,

```
#E[n] = n²   ↔   preΨₙ has no repeated root.
```

⚠️ Read both directions.  The `←` is what `EllipticCurves.Torsion.PrimaryTower`'s remaining gate
asks for; the `→` says there is no cheaper substitute for it, because any proof of `#E[n] = n²`
here *is* a proof that `preΨₙ` is separable.

⚠️ `Separable` rather than `Squarefree`: `Polynomial.nodup_roots_iff_of_splits` is what makes this
proof one line rather than a factorisation argument.  Over an algebraically closed field the two
notions agree — that is standard and is **not** proved here, and nothing below needs it. -/
theorem card_torsion_eq_sq_iff_separable_preΨ (h2 : (2 : F) ≠ 0) {n : ℕ} (hn : Odd n)
    (hchar : (n : F) ≠ 0) :
    Nat.card (W.torsion n) = n ^ 2 ↔ (W.preΨ (n : ℤ)).Separable := by
  classical
  have hp : W.preΨ (n : ℤ) ≠ 0 := W.preΨ_ne_zero (R := F) (by push_cast; exact hchar)
  have hsplits : (W.preΨ (n : ℤ)).Splits := IsAlgClosed.splits _
  have hdeg : (W.preΨ (n : ℤ)).natDegree = (n ^ 2 - 1) / 2 := by
    rw [W.natDegree_preΨ (R := F) (by push_cast; exact hchar)]
    simp [Nat.not_even_iff_odd.mpr hn]
  have hroots : Multiset.card (W.preΨ (n : ℤ)).roots = (n ^ 2 - 1) / 2 := by
    rw [← hdeg]; exact splits_iff_card_roots.mp hsplits
  rw [card_torsion_odd h2 hn hchar, card_root_subtype hp, ← two_mul_pred_sq_div_two_add_one hn,
    ← hroots, ← nodup_roots_iff_of_splits hp hsplits]
  exact ⟨fun h => Multiset.toFinset_card_eq_card_iff_nodup.mp (by omega),
    fun h => by rw [Multiset.toFinset_card_of_nodup h]⟩

/-- ⚠️ **A consistency check, not a new result.**  At an odd index the *exact* count of
`card_torsion_odd` must not exceed the merged bound
`WeierstrassCurve.Affine.card_torsion_le_sq`, and this is where that is machine-checked instead of
assumed: a slip in the fibre count above would show up here.

⚠️ One-directional on purpose.  The merged bound carries neither `[IsAlgClosed F]` nor
`[W.IsElliptic]` and holds at every index, so nothing in this file supersedes it. -/
example (h2 : (2 : F) ≠ 0) {n : ℕ} (hn : Odd n) (hchar : (n : F) ≠ 0) :
    2 * Nat.card {x : F // (W.preΨ (n : ℤ)).eval x = 0} + 1 ≤ n ^ 2 := by
  rw [← card_torsion_odd h2 hn hchar]
  exact card_torsion_le_sq h2 hchar

end Count

/-! ### The `p`-primary tower with the gate substituted -/

section Tower

variable [DecidableEq F] [IsAlgClosed F] [W.IsElliptic]

/-- **`#E[pᵏ] = (pᵏ)²` at an odd `p`, from separability of `preΨ p` alone.** -/
theorem card_torsion_pow_of_separable (h2 : (2 : F) ≠ 0) {p : ℕ} (hp : Odd p)
    (hchar : (p : F) ≠ 0) (hsep : (W.preΨ (p : ℤ)).Separable) (k : ℕ) :
    Nat.card (W.torsion (p ^ k)) = (p ^ k) ^ 2 :=
  card_torsion_pow_of_card h2 (by rintro rfl; simp at hp)
    ((card_torsion_eq_sq_iff_separable_preΨ h2 hp hchar).mpr hsep) k

/-- **`E[pᵏ]` is finite**, at an odd `p`, from separability of `preΨ p` alone. -/
theorem finite_torsion_pow_of_separable (h2 : (2 : F) ≠ 0) {p : ℕ} (hp : Odd p)
    (hchar : (p : F) ≠ 0) (hsep : (W.preΨ (p : ℤ)).Separable) (k : ℕ) :
    Finite (W.torsion (p ^ k)) :=
  finite_torsion_pow_of_card h2 (by rintro rfl; simp at hp)
    ((card_torsion_eq_sq_iff_separable_preΨ h2 hp hchar).mpr hsep) k

/-- **The structure theorem for `E[pᵏ]` at an odd prime `p`, owed one separability statement.**

⚠️ This is the signature the whole file exists to produce.  Compare
`WeierstrassCurve.Affine.nonempty_torsionPow_addEquiv_of_card`, whose remaining hypothesis is
`#E[p] = p²` — a statement about the curve.  Here it is `Separable (W.preΨ p)`, a statement about
**one univariate polynomial**.

⚠️ The exchange is not free, and this form does **not** subsume the one it is built on: it
additionally asks `Odd p` and `(p : F) ≠ 0`, neither of which
`nonempty_torsionPow_addEquiv_of_card` needs.  Inside that range the two hypotheses are equivalent
(`card_torsion_eq_sq_iff_separable_preΨ`) so nothing is given away *there*; at `p = 2`, and in
characteristic `p`, this form says nothing at all.

⚠️ Not proved here, and no route asserted: `Separable (W.preΨ p)` itself.  See the module
docstring. -/
theorem nonempty_torsionPow_addEquiv_of_separable (h2 : (2 : F) ≠ 0) {p : ℕ} (hp : p.Prime)
    (hodd : Odd p) (hchar : (p : F) ≠ 0) (hsep : (W.preΨ (p : ℤ)).Separable) (k : ℕ) :
    Nonempty (W.torsion (p ^ k) ≃+ ZMod (p ^ k) × ZMod (p ^ k)) :=
  nonempty_torsionPow_addEquiv_of_card h2 hp
    ((card_torsion_eq_sq_iff_separable_preΨ h2 hodd hchar).mpr hsep) k

end Tower

/-! ### Non-vacuity: the gate read backwards at `p = 3` -/

section Nonvacuity

variable [DecidableEq F] [IsAlgClosed F] [W.IsElliptic]

omit [DecidableEq F] in
/-- **`preΨ 3` is separable**, over an algebraically closed field of characteristic `∉ {2, 3}`.

⚠️ This is the gate of `card_torsion_eq_sq_iff_separable_preΨ` read **backwards** at `n = 3`,
against the merged sharp count `WeierstrassCurve.Affine.card_torsion_three`.  Nothing in this file
proves it directly, and it is the evidence that the equivalence is oriented correctly.

⚠️ **It is a round trip, not a new statement, and must not be read as one.**
`WeierstrassCurve.Affine.nodup_roots_Ψ₃` (`EllipticCurves.Torsion.ThreeTorsionStructure`) is merged
and in this file's import closure; over an algebraically closed field it *is* separability of `Ψ₃`,
one `Polynomial.nodup_roots_iff_of_splits` away — the same lemma
`card_torsion_eq_sq_iff_separable_preΨ` runs on.  And `card_torsion_three` is proved *from*
`nodup_roots_Ψ₃`, through `card_roots_Ψ₃`.  So what this certifies is that the equivalence returns
its own input, which is the whole of what a check at a settled index can certify — and it is *not*
evidence that the general `Separable (W.preΨ n)` is any closer. -/
theorem separable_preΨ_three (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) :
    (W.preΨ (3 : ℤ)).Separable := by
  classical
  exact (card_torsion_eq_sq_iff_separable_preΨ (n := 3) h2 (by decide) (by exact_mod_cast h3)).mp
    (by rw [card_torsion_three h2 h3]; norm_num)

omit [DecidableEq F] in
/-- **`Ψ₃` is separable**, the same statement under Mathlib's other name for `preΨ 3`. -/
theorem separable_Ψ₃ (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) : W.Ψ₃.Separable := by
  have h : W.preΨ (3 : ℤ) = W.Ψ₃ := by simp [WeierstrassCurve.preΨ]
  exact h ▸ separable_preΨ_three h2 h3

/-- **At `p = 3` the tower of this file is the merged `nonempty_torsionThreePow_addEquiv`.**

⚠️ The `rfl` is definitional proof irrelevance and proves nothing on its own; what is checked is
that the equation **elaborates**, i.e. that the merged theorem and the separability form applied at
`p = 3` have the *same statement*.  A form that had drifted from the one it generalises would fail
here rather than pass quietly. -/
example (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) (k : ℕ) :
    nonempty_torsionThreePow_addEquiv (W := W) h2 h3 k =
      nonempty_torsionPow_addEquiv_of_separable h2 Nat.prime_three (by decide)
        (by exact_mod_cast h3) (separable_preΨ_three h2 h3) k :=
  rfl

end Nonvacuity

end WeierstrassCurve.Affine
