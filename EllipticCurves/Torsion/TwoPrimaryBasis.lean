/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import EllipticCurves.Torsion.PrimaryBasis
import EllipticCurves.Torsion.TwoPrimary

/-!
# Compatible bases for the `2`-primary tower

`EllipticCurves.Torsion.TwoPrimary` shows that `E[2^k] ≃+ ZMod (2^k) × ZMod (2^k)` for an elliptic
curve over an algebraically closed field with `2 ≠ 0`. Those isomorphisms are **non-canonical**, and
worse, a family of them chosen level by level need not commute with the transition maps
`E[2^{k+1}] → E[2^k]`, `x ↦ 2 • x`. Any consumer that takes an inverse limit — above all the Tate
module `T₂E = lim_k E[2^k]` — needs a **coherent** system instead:

```
∃ P Q : ℕ → W.Point,
  (∀ k, AddSubgroup.closure {P k, Q k} = W.torsion (2 ^ k)) ∧
  (∀ k, 2 • P (k + 1) = P k) ∧ (∀ k, 2 • Q (k + 1) = Q k)
```

## What this file contains, and what it does not

The construction is in `EllipticCurves.Torsion.PrimaryBasis`, stated for an arbitrary `ℓ` in terms
of two inputs: surjectivity of `[ℓ]` on `E(F̄)`, and a generating pair of `E[ℓ]`. **This file
supplies those two inputs at `ℓ = 2` and specialises every statement; it contains no argument.**
The two inputs are

* `nsmul_two_surjective` (`EllipticCurves.Torsion.DoublingSurjective`), and
* `nonempty_torsionTwo_addEquiv` (`EllipticCurves.Torsion.TwoTorsion`), which
  `exists_closure_pair_eq_torsion_of_addEquiv` turns into a generating pair of `E[2]`,

together with the count `card_torsion_two_pow`, which is what upgrades the coefficient map
`(ℤ/2^kℤ)² →+ E[2^k]` from surjective to bijective.

⚠️ Earlier revisions of this file carried the whole argument and observed, in prose, that "the same
proof works verbatim for any prime `ℓ` whose `[ℓ]`-surjectivity is established, with `2` replaced by
`ℓ`". That observation is now a fact about the *statements* and not only about the *proofs*:
`EllipticCurves.Torsion.ThreePrimaryBasis` is the `ℓ = 3` instance and duplicates nothing.

## Main statements

* `WeierstrassCurve.Affine.exists_two_nsmul_eq_of_mem_torsion`: lifting along `[2]` in the tower.
* `WeierstrassCurve.Affine.exists_closure_pair_eq_torsion_two`: a generating pair of `E[2]`.
* `WeierstrassCurve.Affine.exists_compatible_basis`: the coherent system.
* `WeierstrassCurve.Affine.torsionPairEquiv`: the explicit `(ℤ/2^kℤ)² ≃+ E[2^k]`.
* `WeierstrassCurve.Affine.zmod_pair_eq_zero_iff`: uniqueness of the coefficients.
* `WeierstrassCurve.Affine.ne_zero_and_ne_of_closure_pair`: a generating pair is non-degenerate.

## References

* [Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.7.
-/

open scoped AddSubgroup

namespace WeierstrassCurve.Affine

variable {F : Type*} [Field F] [DecidableEq F] {W : Affine F}

variable [IsAlgClosed F] [W.IsElliptic]

/-! ### The two prime-specific inputs at `ℓ = 2` -/

/-- **Lifting inside the `2`-primary tower.** Every element of `E[2^k]` is twice an element of
`E[2^{k+1}]`. This is `exists_nsmul_eq_of_mem_torsion` fed with `nsmul_two_surjective`. -/
theorem exists_two_nsmul_eq_of_mem_torsion (h2 : (2 : F) ≠ 0) {k : ℕ} {y : W.Point}
    (hy : y ∈ W.torsion (2 ^ k)) : ∃ x ∈ W.torsion (2 ^ (k + 1)), 2 • x = y :=
  exists_nsmul_eq_of_mem_torsion (nsmul_two_surjective h2) hy

/-- `E[2]` has a generating pair: it is isomorphic to `ZMod 2 × ZMod 2`, in which the two standard
vectors generate. -/
theorem exists_closure_pair_eq_torsion_two (h2 : (2 : F) ≠ 0) :
    ∃ P Q : W.Point, P ∈ W.torsion 2 ∧ Q ∈ W.torsion 2 ∧
      AddSubgroup.closure ({P, Q} : Set W.Point) = W.torsion 2 :=
  (nonempty_torsionTwo_addEquiv (W := W) h2).elim exists_closure_pair_eq_torsion_of_addEquiv

/-! ### The coherent system -/

/-- **Compatible bases for the `2`-primary tower.** Over an algebraically closed field with
`2 ≠ 0` there is a system of generating pairs of the groups `E[2^k]`, coherent for the transition
maps `x ↦ 2 • x` of the tower:

```
∀ k, AddSubgroup.closure {P k, Q k} = W.torsion (2 ^ k)
∀ k, 2 • P (k + 1) = P k        ∀ k, 2 • Q (k + 1) = Q k
```

The family is *chosen*, so the statement is existential; every consumer only ever needs one such
system. -/
theorem exists_compatible_basis (h2 : (2 : F) ≠ 0) :
    ∃ P Q : ℕ → W.Point,
      (∀ k, AddSubgroup.closure ({P k, Q k} : Set W.Point) = W.torsion (2 ^ k)) ∧
      (∀ k, 2 • P (k + 1) = P k) ∧ (∀ k, 2 • Q (k + 1) = Q k) :=
  exists_compatible_basis_of_surjective (nsmul_two_surjective h2)
    (exists_closure_pair_eq_torsion_two h2)

/-! ### The explicit isomorphism `(ℤ/2^kℤ)² ≃+ E[2^k]` -/

/-- `torsionPairHom` is bijective: it is surjective by `exists_zmod_pair_eq`, and both sides have
`4 ^ k` elements by `card_torsion_two_pow`. -/
theorem torsionPairHom_bijective (h2 : (2 : F) ≠ 0) {k : ℕ} {P Q : W.Point}
    (hgen : AddSubgroup.closure ({P, Q} : Set W.Point) = W.torsion (2 ^ k)) :
    Function.Bijective (torsionPairHom hgen) :=
  haveI := finite_torsion_two_pow (W := W) h2 k
  torsionPairHom_bijective_of_card (card_torsion_two_pow_mul_self h2 k) hgen

/-- **The explicit structure isomorphism `(ℤ/2^kℤ)² ≃+ E[2^k]`** attached to a generating pair of
`E[2^k]`.

`AddCommGroup.equiv_zmod_sq_of_two_gen` concludes only `Nonempty`; inverse-limit arguments need the
map itself, and in particular its injectivity, which is what this bundles. -/
noncomputable def torsionPairEquiv (h2 : (2 : F) ≠ 0) {k : ℕ} {P Q : W.Point}
    (hgen : AddSubgroup.closure ({P, Q} : Set W.Point) = W.torsion (2 ^ k)) :
    ZMod (2 ^ k) × ZMod (2 ^ k) ≃+ W.torsion (2 ^ k) :=
  AddEquiv.ofBijective _ (torsionPairHom_bijective h2 hgen)

@[simp]
lemma torsionPairEquiv_apply_coe (h2 : (2 : F) ≠ 0) {k : ℕ} {P Q : W.Point}
    (hgen : AddSubgroup.closure ({P, Q} : Set W.Point) = W.torsion (2 ^ k))
    (ab : ZMod (2 ^ k) × ZMod (2 ^ k)) :
    ((torsionPairEquiv h2 hgen ab : W.torsion (2 ^ k)) : W.Point)
      = ab.1.val • P + ab.2.val • Q := rfl

/-- **Uniqueness of the coefficients**: a `ZMod (2^k)`-combination of a generating pair vanishes
only for zero coefficients. This is the half that `AddCommGroup.equiv_zmod_sq_of_two_gen` discards,
and it is what identifies the inverse limit of the tower. -/
theorem zmod_pair_eq_zero_iff (h2 : (2 : F) ≠ 0) {k : ℕ} {P Q : W.Point}
    (hgen : AddSubgroup.closure ({P, Q} : Set W.Point) = W.torsion (2 ^ k))
    {a b : ZMod (2 ^ k)} : a.val • P + b.val • Q = 0 ↔ a = 0 ∧ b = 0 :=
  haveI := finite_torsion_two_pow (W := W) h2 k
  zmod_pair_eq_zero_iff_of_card (card_torsion_two_pow_mul_self h2 k) hgen

/-- **A generating pair of `E[2^k]` with `k ≥ 1` is non-degenerate**: both members are nonzero and
they are distinct. This is the qualitative content of the injectivity half, and it is what rules out
the degenerate systems that the existential statements would otherwise permit — for instance a
"basis" with `P = Q`, which is exactly the configuration that makes the inductive step fail at
`k = 0`. -/
theorem ne_zero_and_ne_of_closure_pair (h2 : (2 : F) ≠ 0) {k : ℕ} (hk : 1 ≤ k) {P Q : W.Point}
    (hgen : AddSubgroup.closure ({P, Q} : Set W.Point) = W.torsion (2 ^ k)) :
    P ≠ 0 ∧ Q ≠ 0 ∧ P ≠ Q :=
  haveI := finite_torsion_two_pow (W := W) h2 k
  ne_zero_and_ne_of_closure_pair_of_card (card_torsion_two_pow_mul_self h2 k)
    (by calc 1 < 2 := one_lt_two
      _ = 2 ^ 1 := (pow_one 2).symm
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk) hgen

end WeierstrassCurve.Affine
