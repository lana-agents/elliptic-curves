/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import EllipticCurves.TateModule.Basic
import EllipticCurves.Torsion.TwoPrimary

/-!
# The projections of the Tate module are surjective

`EllipticCurves.TateModule.Basic` builds the Tate module `T_ℓE = lim_k E[ℓ^k]` as the group of
compatible families and equips it with its `ℤ_ℓ`-module structure, but proves nothing that would
distinguish it from the zero module: every statement there holds vacuously for `T_ℓE = 0`. This
file supplies the first such theorem.

If multiplication by `ℓ` is surjective on `E(F̄)` then each projection

```
tateModule.proj k : T_ℓE →+ E[ℓ^k]
```

is surjective. Over an algebraically closed field with `(2 : F) ≠ 0`, `[2]` *is* surjective
(`EllipticCurves.Torsion.DoublingSurjective`), so `T₂E` surjects onto a group of order `4 ^ k` for
every `k` (`EllipticCurves.Torsion.TwoPrimary`) and is therefore **infinite**, in particular
nontrivial.

## The construction

Given `x ∈ E[ℓ^k]`, first climb: choose `u 0 = x` and `u (n + 1)` a preimage of `u n` under `[ℓ]`,
so that `u n ∈ E[ℓ^{k+n}]`. Then glue the descending and ascending halves into a single family with
**truncated** subtraction,

```
f j := ℓ ^ (k - j) • u (j - k),
```

which reads as `ℓ^{k-j} • x` for `j ≤ k` and as `u (j - k)` for `k ≤ j`; the two readings agree at
`j = k`, where the value is `x`. Membership and the compatibility `ℓ • f (j + 1) = f j` are then
each a two-case split on `j < k` versus `k ≤ j`.

Nothing in the argument inspects `ℓ`, so the general statement costs nothing over the `ℓ = 2` one
and will apply verbatim to the first odd prime for which `[ℓ]`-surjectivity is established.

## Main statements

* `WeierstrassCurve.Affine.tateModule.exists_mem_tateModule_apply_eq`: a compatible family with a
  prescribed value at a prescribed level.
* `WeierstrassCurve.Affine.tateModule.proj_surjective`: surjectivity of the projections.
* `WeierstrassCurve.Affine.tateModule.proj_two_surjective`: the case `ℓ = 2`, unconditional over an
  algebraically closed field of characteristic `≠ 2`.
* `WeierstrassCurve.Affine.tateModule.infinite_tateModule_two`,
  `WeierstrassCurve.Affine.tateModule.nontrivial_tateModule_two`: `T₂E` is infinite, hence nonzero.

## References

* [Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.7.
-/

open scoped AddSubgroup

namespace WeierstrassCurve.Affine

variable {F : Type*} [Field F] [DecidableEq F] {W : Affine F} {ℓ : ℕ}

namespace tateModule

/-- **Every level value is attained by a compatible family.** If `[ℓ]` is surjective on `E(F̄)` then
for every `x ∈ E[ℓ^k]` there is an element of the Tate module whose level-`k` value is `x`. -/
theorem exists_mem_tateModule_apply_eq (hℓ : Function.Surjective fun R : W.Point => ℓ • R)
    {k : ℕ} {x : W.Point} (hx : x ∈ W.torsion (ℓ ^ k)) :
    ∃ f ∈ W.tateModule ℓ, f k = x := by
  classical
  choose lift hlift using hℓ
  obtain ⟨u, hu0, hus⟩ : ∃ u : ℕ → W.Point, u 0 = x ∧ ∀ n, u (n + 1) = lift (u n) :=
    ⟨fun n => Nat.rec x (fun _ ih => lift ih) n, rfl, fun _ => rfl⟩
  have hstep : ∀ n, ℓ • u (n + 1) = u n := fun n => by rw [hus]; exact hlift (u n)
  -- The climbing family lands one level higher at each step.
  have hmem : ∀ n, u n ∈ W.torsion (ℓ ^ (k + n)) := by
    intro n
    induction n with
    | zero => rw [Nat.add_zero, hu0]; exact hx
    | succ n ih =>
      rw [mem_torsion_iff, ← Nat.add_assoc, pow_succ, mul_smul, hstep]
      exact ih
  refine ⟨fun j => ℓ ^ (k - j) • u (j - k), ⟨fun j => ?_, fun j => ?_⟩, ?_⟩
  · -- membership at level `j`
    change ℓ ^ (k - j) • u (j - k) ∈ W.torsion (ℓ ^ j)
    rcases le_or_gt j k with hjk | hjk
    · rw [Nat.sub_eq_zero_of_le hjk, hu0, mem_torsion_iff, ← mul_smul, ← pow_add,
        Nat.add_sub_cancel' hjk]
      exact hx
    · rw [Nat.sub_eq_zero_of_le hjk.le, pow_zero, one_smul]
      have := hmem (j - k)
      rwa [Nat.add_sub_cancel' hjk.le] at this
  · -- compatibility `ℓ • f (j + 1) = f j`
    change ℓ • (ℓ ^ (k - (j + 1)) • u (j + 1 - k)) = ℓ ^ (k - j) • u (j - k)
    rcases lt_or_ge j k with hjk | hjk
    · rw [Nat.sub_eq_zero_of_le hjk.le, Nat.sub_eq_zero_of_le hjk, hu0, ← mul_smul, ← pow_succ',
        show k - (j + 1) + 1 = k - j by omega]
    · rw [Nat.sub_eq_zero_of_le hjk, Nat.sub_eq_zero_of_le (hjk.trans (Nat.le_succ j)), pow_zero,
        one_smul, one_smul, show j + 1 - k = (j - k) + 1 by omega, hstep]
  · change ℓ ^ (k - k) • u (k - k) = x
    rw [Nat.sub_self, pow_zero, one_smul, hu0]

/-- **The projections of the Tate module are surjective** as soon as multiplication by `ℓ` is
surjective on `E(F̄)`. -/
theorem proj_surjective (hℓ : Function.Surjective fun R : W.Point => ℓ • R) (k : ℕ) :
    Function.Surjective (proj (W := W) (ℓ := ℓ) k) := by
  rintro ⟨x, hx⟩
  obtain ⟨f, hf, hfk⟩ := exists_mem_tateModule_apply_eq hℓ hx
  exact ⟨⟨f, hf⟩, Subtype.ext hfk⟩

variable [IsAlgClosed F] [W.IsElliptic]

/-- **The projections of `T₂E` are surjective**, unconditionally, over an algebraically closed field
of characteristic `≠ 2`. -/
theorem proj_two_surjective (h2 : (2 : F) ≠ 0) (k : ℕ) :
    Function.Surjective (proj (W := W) (ℓ := 2) k) :=
  proj_surjective (nsmul_two_surjective h2) k

/-- **`T₂E` is infinite.** It surjects onto `E[2^k]`, which has `4 ^ k` elements, for every `k`; a
finite group cannot dominate `4 ^ k` for all `k`.

This is the first statement about a Tate module in this development that is incompatible with
`T_ℓE = 0`, and so the first evidence that the constructions of `EllipticCurves.TateModule.Basic`
are not vacuous. -/
theorem infinite_tateModule_two (h2 : (2 : F) ≠ 0) : Infinite (W.tateModule 2) := by
  rw [← not_finite_iff_infinite]
  intro hfin
  have hle : ∀ k, Nat.card (W.torsion (2 ^ k)) ≤ Nat.card (W.tateModule 2) := fun k =>
    Nat.card_le_card_of_surjective _ (proj_two_surjective h2 k)
  have hk := hle (Nat.card (W.tateModule 2))
  rw [card_torsion_two_pow h2] at hk
  exact absurd hk (Nat.lt_pow_self (by norm_num)).not_ge

/-- **`T₂E` is nonzero.** -/
theorem nontrivial_tateModule_two (h2 : (2 : F) ≠ 0) : Nontrivial (W.tateModule 2) :=
  haveI := infinite_tateModule_two (W := W) h2
  inferInstance

/-- An explicit nonzero element of `T₂E`. -/
theorem exists_ne_zero_tateModule_two (h2 : (2 : F) ≠ 0) : ∃ f : W.tateModule 2, f ≠ 0 :=
  haveI := nontrivial_tateModule_two (W := W) h2
  exists_ne 0

end tateModule

end WeierstrassCurve.Affine
