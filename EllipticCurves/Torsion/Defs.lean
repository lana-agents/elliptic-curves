/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point

/-!
# The `n`-torsion subgroup `E[n]` of a Weierstrass curve

For a Weierstrass curve `W` over a field `F`, the group of affine points `W.Point`
(`WeierstrassCurve.Affine.Point`) carries an `AddCommGroup` structure. Mathlib already provides the
`n`-torsion subgroup of an arbitrary additive commutative group `A` as `AddSubgroup.torsionBy`, with
the scoped notation `A[n]` for `n : ℤ` and the membership characterisation
`AddSubgroup.torsionBy.nsmul_iff`.

This file records the small pieces of general API that are still missing at the
`AddSubgroup.torsionBy` level (the values at `0` and `1`, and monotonicity in the divisibility
order), and specialises the construction to Weierstrass curves as
`WeierstrassCurve.Affine.torsion W n`, the `n`-torsion subgroup `E[n]` — equivalently the kernel of
multiplication by `n` on `W.Point`.

The finiteness of `E[n]` and the structure theorem `E[n] ≃ (ℤ/nℤ)²` require relating torsion points
to the division polynomials, and are developed separately.

## Main definitions

* `WeierstrassCurve.Affine.torsion W n`: the `n`-torsion subgroup `E[n]` of `W.Point`.

## Main statements

* `WeierstrassCurve.Affine.mem_torsion_iff`: `P ∈ E[n] ↔ n • P = 0`.
* `WeierstrassCurve.Affine.torsion_zero`, `WeierstrassCurve.Affine.torsion_one`:
  `E[0] = ⊤` and `E[1] = ⊥`.
* `WeierstrassCurve.Affine.torsion_mono`: `m ∣ n → E[m] ≤ E[n]`.
-/

open scoped AddSubgroup

namespace AddSubgroup

variable {A : Type*} [AddCommGroup A]

/-- Membership in the integer `n`-torsion subgroup: `a ∈ A[n] ↔ n • a = 0`. -/
lemma torsionBy.zsmul_iff {n : ℤ} {a : A} : a ∈ A[n] ↔ n • a = 0 := by
  rw [torsionBy, Submodule.mem_toAddSubgroup, Submodule.mem_torsionBy_iff]

/-- The `0`-torsion subgroup is the whole group, since `0 • a = 0` for every `a`. -/
@[simp]
lemma torsionBy_zero : A[(0 : ℤ)] = ⊤ := by
  ext a
  simp

/-- The `1`-torsion subgroup is trivial. -/
@[simp]
lemma torsionBy_one : A[(1 : ℤ)] = ⊥ := by
  ext a
  simp only [torsionBy.zsmul_iff, one_smul, AddSubgroup.mem_bot]

/-- The integer torsion subgroups are monotone in the divisibility order:
if `m ∣ n` then `A[m] ≤ A[n]`. -/
lemma torsionBy_le_torsionBy_of_dvd {m n : ℤ} (h : m ∣ n) : A[m] ≤ A[n] := by
  intro a ha
  rw [torsionBy.zsmul_iff] at ha ⊢
  obtain ⟨k, rfl⟩ := h
  rw [mul_comm, mul_smul, ha, smul_zero]

end AddSubgroup

namespace WeierstrassCurve.Affine

variable {F : Type*} [Field F] [DecidableEq F]

variable (W : Affine F) in
/-- The `n`-torsion subgroup `E[n]` of a Weierstrass curve `W` over a field `F`: the subgroup of
points `P` of `W` with `n • P = 0`, i.e. the kernel of multiplication by `n` on `W.Point`. -/
abbrev torsion (n : ℕ) : AddSubgroup W.Point :=
  W.Point[(n : ℤ)]

variable {W : Affine F}

/-- A point lies in `E[n]` exactly when it is killed by multiplication by `n`. -/
lemma mem_torsion_iff {n : ℕ} {P : W.Point} : P ∈ W.torsion n ↔ n • P = 0 :=
  AddSubgroup.torsionBy.nsmul_iff

@[simp]
lemma nsmul_mem_torsion {n : ℕ} (P : W.torsion n) : n • P = 0 :=
  AddSubgroup.torsionBy.nsmul P

/-- The `0`-torsion subgroup `E[0]` is the whole group of points. -/
@[simp]
lemma torsion_zero : W.torsion 0 = ⊤ := by
  ext P
  simp

/-- The `1`-torsion subgroup `E[1]` is trivial. -/
@[simp]
lemma torsion_one : W.torsion 1 = ⊥ := by
  ext P
  simp

/-- The torsion subgroups are monotone in the divisibility order: `m ∣ n → E[m] ≤ E[n]`. -/
lemma torsion_mono {m n : ℕ} (h : m ∣ n) : W.torsion m ≤ W.torsion n :=
  AddSubgroup.torsionBy_le_torsionBy_of_dvd (Int.natCast_dvd_natCast.mpr h)

end WeierstrassCurve.Affine
