/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import EllipticCurves.Torsion.PrimaryBasis
import EllipticCurves.Torsion.ThreePrimary

/-!
# Compatible bases for the `3`-primary tower

`EllipticCurves.Torsion.ThreePrimary` shows that `E[3^k] ≃+ ZMod (3^k) × ZMod (3^k)` for an
elliptic curve over an algebraically closed field with `2 ≠ 0` and `3 ≠ 0`. Those isomorphisms hold
at each level *independently*, and `EllipticCurves.TateModule.Free` says of the `ℓ = 2` situation,
copy-paste:

> Coherence is essential and is not supplied by the structure theorem: `E[2^k] ≃+ (ZMod (2^k))²`
> holds at each level *independently*, and a family of unrelated isomorphisms says nothing about an
> inverse limit.

The same is true at `ℓ = 3`. This file supplies the missing coherent system:

```
∃ P Q : ℕ → W.Point,
  (∀ k, AddSubgroup.closure {P k, Q k} = W.torsion (3 ^ k)) ∧
  (∀ k, 3 • P (k + 1) = P k) ∧ (∀ k, 3 • Q (k + 1) = Q k)
```

## What this file contains, and what it does not

The construction is in `EllipticCurves.Torsion.PrimaryBasis`, stated for an arbitrary `ℓ` in terms
of two inputs: surjectivity of `[ℓ]` on `E(F̄)`, and a generating pair of `E[ℓ]`. **This file
supplies those two inputs at `ℓ = 3`; it contains no argument, and it duplicates no proof from
`EllipticCurves.Torsion.TwoPrimaryBasis`, which is the same list of instantiations at `ℓ = 2`.**
⚠️ It used to add *"and specialises every statement"*, which overstates in the same way that file's
copy of the sentence did: it specialises **8** of `PrimaryBasis.lean`'s **22** public statements,
and the four stated there at a general modulus `n` — `closure_pair_eq_torsion_succ`,
`torsionPairHom`, `torsionPairHom_apply_coe`, `exists_zmod_pair_eq` — are consumed **unspecialised**
at `ℓ = 3`, which is why there is no `exists_zmod_pair_eq_three`. The two inputs are

* `nsmul_three_surjective` (`EllipticCurves.Torsion.TriplingSurjective`), and
* `nonempty_torsionThree_addEquiv` (`EllipticCurves.Torsion.ThreeTorsionStructure`), which
  `exists_closure_pair_eq_torsion_of_addEquiv` turns into a generating pair of `E[3]`,

together with the count `card_torsion_three_pow` (`EllipticCurves.Torsion.ThreePrimary`), which is
what upgrades the coefficient map `(ℤ/3^kℤ)² →+ E[3^k]` from surjective to bijective.

## Naming

Every declaration below is the `ℓ = 3` twin of a public declaration of
`EllipticCurves.Torsion.TwoPrimaryBasis` in the same namespace `WeierstrassCurve.Affine`, so every
name would collide. **The rule is: the `ℓ = 2` file owns the unsuffixed name, and the twin here
carries `_three` (or `Three` for a `def`).** The one exception is
`exists_three_nsmul_eq_of_mem_torsion`, which mirrors `exists_two_nsmul_eq_of_mem_torsion` and so
takes the numeral in the same position.

## Where `h2` and `h3` enter

⚠️ **This file carries two hypotheses where `TwoPrimaryBasis.lean` carries one, and they enter in
different places.**

* `(2 : F) ≠ 0` enters through **`[3]`-surjectivity**. `nsmul_three_surjective` takes `h2` and
  **no** `h3` (`EllipticCurves.Torsion.TriplingSurjective`), which is why
  `exists_three_nsmul_eq_of_mem_torsion` below has a one-hypothesis binder list, exactly like its
  `ℓ = 2` twin.
* `(3 : F) ≠ 0` enters **only through counting `E[3]`** — through `nonempty_torsionThree_addEquiv`
  for the base of the tower and through `card_torsion_three_pow` for bijectivity, and through
  nothing else. This is the same provenance that `EllipticCurves.Torsion.ThreePrimary` records for
  the tower itself, measured there with a deletion test; the deletion test for this file is in the
  docstring of `exists_closure_pair_eq_torsion_three`.

## Scope

* **`ℓ = 3` only.** A general odd `ℓ` needs `[ℓ]`-surjectivity on `E(F̄)`, which needs the general
  coordinate formula `x(ℓP) = Φ_ℓ/ΨSq_ℓ`; at `ℓ = 3` that formula is proved
  (`EllipticCurves.Torsion.TriplingSurjective`) and for `ℓ ≥ 5` it is not. The generic layer in
  `EllipticCurves.Torsion.PrimaryBasis` is ready for any such `ℓ` the moment one arrives.
* ⚠️ **`TwoPrimaryBasis.lean` used to say of itself that nothing in it uses `x(nP) = Φₙ/ΨSqₙ`. That
  sentence is not true here and is not repeated.** This file consumes the coordinate formula, at
  `n = 3` only and where it is proved, through `nsmul_three_surjective` — exactly as
  `EllipticCurves.Torsion.ThreePrimary` does and says. Ward's theorem and the elliptic-net
  recurrence remain unused.
* **`T₃E ≅ ℤ₃²` is not in scope.** This file delivers the coherent system, which is the input
  `EllipticCurves.TateModule.Free` consumes at `ℓ = 2`; the `ℓ = 3` Tate module is a separate
  module and a separate deliverable. That deliverable now exists — it is
  `EllipticCurves.TateModule.FreeThree`, which consumes `exists_compatible_basis_three` below
  through the `ℓ`-generic `EllipticCurves.TateModule.PrimaryFree` — and this bullet remains a
  statement about *this file's* scope, not about the development's.

## Main statements

* `WeierstrassCurve.Affine.exists_three_nsmul_eq_of_mem_torsion`: lifting along `[3]` in the tower.
* `WeierstrassCurve.Affine.exists_closure_pair_eq_torsion_three`: a generating pair of `E[3]`.
* `WeierstrassCurve.Affine.exists_compatible_basis_three`: the coherent system.
* `WeierstrassCurve.Affine.torsionPairEquivThree`: the explicit `(ℤ/3^kℤ)² ≃+ E[3^k]`.
* `WeierstrassCurve.Affine.zmod_pair_eq_zero_iff_three`: uniqueness of the coefficients.
* `WeierstrassCurve.Affine.ne_zero_and_ne_of_closure_pair_three`: a generating pair is
  non-degenerate.

## References

* [Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.7.
-/

open scoped AddSubgroup

namespace WeierstrassCurve.Affine

variable {F : Type*} [Field F] [DecidableEq F] {W : Affine F}

variable [IsAlgClosed F] [W.IsElliptic]

/-! ### The two prime-specific inputs at `ℓ = 3` -/

/-- **Lifting inside the `3`-primary tower.** Every element of `E[3^k]` is three times an element
of `E[3^{k+1}]`. This is `exists_nsmul_eq_of_mem_torsion` fed with `nsmul_three_surjective`.

⚠️ **Only `h2` appears**, and that is not an oversight: `nsmul_three_surjective` is stated with
`(2 : F) ≠ 0` and no `(3 : F) ≠ 0`. Nothing in the `3`-primary lifting step counts anything, so
there is nothing here for `h3` to do. -/
theorem exists_three_nsmul_eq_of_mem_torsion (h2 : (2 : F) ≠ 0) {k : ℕ} {y : W.Point}
    (hy : y ∈ W.torsion (3 ^ k)) : ∃ x ∈ W.torsion (3 ^ (k + 1)), 3 • x = y :=
  exists_nsmul_eq_of_mem_torsion (nsmul_three_surjective h2) hy

/-- `E[3]` has a generating pair: it is isomorphic to `ZMod 3 × ZMod 3`, in which the two standard
vectors generate.

⚠️ **This is where `h3` enters the file, and a deletion test says it enters nowhere else in the
recursion.** Deleting the input `nonempty_torsionThree_addEquiv (W := W) h2 h3` — that is,
replacing this proof by `by refine Nonempty.elim ?_ exists_closure_pair_eq_torsion_of_addEquiv`,
which keeps the consumer and removes only the thing consumed — leaves, measured on this file as
committed:

```
error: unsolved goals
F : Type u_1
inst✝³ : Field F
inst✝² : DecidableEq F
W : Affine F
inst✝¹ : IsAlgClosed F
inst✝ : WeierstrassCurve.IsElliptic W
h2 : 2 ≠ 0
h3 : 3 ≠ 0
⊢ Nonempty (↥(W.torsion 3) ≃+ ZMod 3 × ZMod 3)
```

⚠️ The information is in the residual **goal**, which no type mismatch could ever show: what is
missing is precisely a structure theorem for `E[3]`, and `h2` and `h3` both survive untouched in
the context because `exists_closure_pair_eq_torsion_of_addEquiv` wants neither of them. -/
theorem exists_closure_pair_eq_torsion_three (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) :
    ∃ P Q : W.Point, P ∈ W.torsion 3 ∧ Q ∈ W.torsion 3 ∧
      AddSubgroup.closure ({P, Q} : Set W.Point) = W.torsion 3 :=
  (nonempty_torsionThree_addEquiv (W := W) h2 h3).elim exists_closure_pair_eq_torsion_of_addEquiv

/-! ### The coherent system -/

/-- **Compatible bases for the `3`-primary tower.** Over an algebraically closed field with
`2 ≠ 0` and `3 ≠ 0` there is a system of generating pairs of the groups `E[3^k]`, coherent for the
transition maps `x ↦ 3 • x` of the tower:

```
∀ k, AddSubgroup.closure {P k, Q k} = W.torsion (3 ^ k)
∀ k, 3 • P (k + 1) = P k        ∀ k, 3 • Q (k + 1) = Q k
```

This is the input that an inverse-limit description of `T₃E = lim_k E[3^k]` needs and that the
levelwise structure theorem `nonempty_torsionThreePow_addEquiv` does not provide. The family is
*chosen*, so the statement is existential; every consumer only ever needs one such system. -/
theorem exists_compatible_basis_three (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) :
    ∃ P Q : ℕ → W.Point,
      (∀ k, AddSubgroup.closure ({P k, Q k} : Set W.Point) = W.torsion (3 ^ k)) ∧
      (∀ k, 3 • P (k + 1) = P k) ∧ (∀ k, 3 • Q (k + 1) = Q k) :=
  exists_compatible_basis_of_surjective (nsmul_three_surjective h2)
    (exists_closure_pair_eq_torsion_three h2 h3)

/-! ### The explicit isomorphism `(ℤ/3^kℤ)² ≃+ E[3^k]` -/

/-- `torsionPairHom` is bijective at `3 ^ k`: it is surjective by `exists_zmod_pair_eq`, and both
sides have `9 ^ k` elements by `card_torsion_three_pow`. -/
theorem torsionPairHom_bijective_three (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) {k : ℕ}
    {P Q : W.Point}
    (hgen : AddSubgroup.closure ({P, Q} : Set W.Point) = W.torsion (3 ^ k)) :
    Function.Bijective (torsionPairHom hgen) :=
  haveI := finite_torsion_three_pow (W := W) h2 h3 k
  torsionPairHom_bijective_of_card (card_torsion_three_pow_mul_self h2 h3 k) hgen

/-- **The explicit structure isomorphism `(ℤ/3^kℤ)² ≃+ E[3^k]`** attached to a generating pair of
`E[3^k]`.

`nonempty_torsionThreePow_addEquiv` concludes only `Nonempty`; inverse-limit arguments need the map
itself, and in particular its injectivity, which is what this bundles. -/
noncomputable def torsionPairEquivThree (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) {k : ℕ}
    {P Q : W.Point}
    (hgen : AddSubgroup.closure ({P, Q} : Set W.Point) = W.torsion (3 ^ k)) :
    ZMod (3 ^ k) × ZMod (3 ^ k) ≃+ W.torsion (3 ^ k) :=
  AddEquiv.ofBijective _ (torsionPairHom_bijective_three h2 h3 hgen)

@[simp]
lemma torsionPairEquivThree_apply_coe (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) {k : ℕ}
    {P Q : W.Point}
    (hgen : AddSubgroup.closure ({P, Q} : Set W.Point) = W.torsion (3 ^ k))
    (ab : ZMod (3 ^ k) × ZMod (3 ^ k)) :
    ((torsionPairEquivThree h2 h3 hgen ab : W.torsion (3 ^ k)) : W.Point)
      = ab.1.val • P + ab.2.val • Q := rfl

/-- **Uniqueness of the coefficients**: a `ZMod (3^k)`-combination of a generating pair vanishes
only for zero coefficients. This is the half that `nonempty_torsionThreePow_addEquiv` discards, and
it is what identifies the inverse limit of the tower. -/
theorem zmod_pair_eq_zero_iff_three (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) {k : ℕ} {P Q : W.Point}
    (hgen : AddSubgroup.closure ({P, Q} : Set W.Point) = W.torsion (3 ^ k))
    {a b : ZMod (3 ^ k)} : a.val • P + b.val • Q = 0 ↔ a = 0 ∧ b = 0 :=
  haveI := finite_torsion_three_pow (W := W) h2 h3 k
  zmod_pair_eq_zero_iff_of_card (card_torsion_three_pow_mul_self h2 h3 k) hgen

/-- **A generating pair of `E[3^k]` with `k ≥ 1` is non-degenerate**: both members are nonzero and
they are distinct. This is the qualitative content of the injectivity half, and it is what rules out
the degenerate systems that the existential statements would otherwise permit — for instance a
"basis" with `P = Q`, which is exactly the configuration that makes the inductive step
`closure_pair_eq_torsion_succ` fail at `k = 0`. -/
theorem ne_zero_and_ne_of_closure_pair_three (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) {k : ℕ}
    (hk : 1 ≤ k) {P Q : W.Point}
    (hgen : AddSubgroup.closure ({P, Q} : Set W.Point) = W.torsion (3 ^ k)) :
    P ≠ 0 ∧ Q ≠ 0 ∧ P ≠ Q :=
  haveI := finite_torsion_three_pow (W := W) h2 h3 k
  ne_zero_and_ne_of_closure_pair_of_card (card_torsion_three_pow_mul_self h2 h3 k)
    (by calc 1 < 3 := by norm_num
      _ = 3 ^ 1 := (pow_one 3).symm
      _ ≤ 3 ^ k := Nat.pow_le_pow_right (by norm_num) hk) hgen

/-! ### Non-vacuity

The headline `exists_compatible_basis_three` is existential, so it would be satisfied by the
degenerate family `P = Q = 0` if the closure equations did not rule it out; that is what
`ne_zero_and_ne_of_closure_pair_three` certifies, and it is certified below on a curve that exists
rather than only in the abstract. The hypotheses `[IsAlgClosed F]`, `[W.IsElliptic]`, `(2 : F) ≠ 0`
and `(3 : F) ≠ 0` are simultaneously satisfiable on the standard certificate curve `y² + y = x³`
over an algebraic closure of `ℚ`, which is the curve
`EllipticCurves.Torsion.ThreePrimary` uses for the same purpose. -/

section Nonvacuity

/-- The curve `y² + y = x³` over `ℚ`, this development's standard `n = 3` certificate curve. -/
private noncomputable def exampleCurveThree : Affine ℚ := ⟨0, 0, 1, 0, 0⟩

/-- An algebraically closed extension of `ℚ`. -/
private abbrev exampleField : Type := AlgebraicClosure ℚ

private instance : exampleCurveThree.IsElliptic := by
  rw [WeierstrassCurve.isElliptic_iff, isUnit_iff_ne_zero]
  norm_num [exampleCurveThree, WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈]

/-- ⚠️ `WeierstrassCurve.baseChange` is a plain `def`, so `[(W⁄F).IsElliptic]` is **not** found by
bare `inferInstance` from `[W.IsElliptic]`. -/
private instance : (exampleCurveThree⁄exampleField).IsElliptic :=
  inferInstanceAs (exampleCurveThree.map (algebraMap ℚ exampleField)).IsElliptic

private lemma exampleTwo : (2 : exampleField) ≠ 0 := by norm_num

private lemma exampleThree : (3 : exampleField) ≠ 0 := by norm_num

open Classical in
/-- **⚠️ THE LOAD-BEARING CERTIFICATE**: on a curve that exists, the `3`-primary tower really does
carry a coherent system of generating pairs. -/
example : ∃ P Q : ℕ → (exampleCurveThree⁄exampleField).Point,
    (∀ k, AddSubgroup.closure ({P k, Q k} : Set (exampleCurveThree⁄exampleField).Point)
      = (exampleCurveThree⁄exampleField).torsion (3 ^ k)) ∧
    (∀ k, 3 • P (k + 1) = P k) ∧ (∀ k, 3 • Q (k + 1) = Q k) :=
  exists_compatible_basis_three exampleTwo exampleThree

open Classical in
/-- **⚠️ The certificate that the coherent system is not the degenerate one.** Level `1` of some
coherent system is a genuine pair of distinct nonzero `3`-torsion points, so
`exists_compatible_basis_three` is not satisfied vacuously by `P = Q = 0`.

⚠️ Deleting `ne_zero_and_ne_of_closure_pair_three exampleTwo exampleThree le_rfl (hgen 1)` from
this script — replacing the last component of the anonymous constructor by a hole, and changing
nothing else — leaves, measured:

```
error: unsolved goals
F : Type u_1
inst✝³ : Field F
inst✝² : DecidableEq F
W : Affine F
inst✝¹ : IsAlgClosed F
inst✝ : WeierstrassCurve.IsElliptic W
P Q : ℕ → (exampleCurveThree⁄exampleField).Point
hgen : ∀ (k : ℕ),
  AddSubgroup.closure {P k, Q k} = (exampleCurveThree⁄exampleField).torsion (3 ^ k)
⊢ P 1 ≠ 0 ∧ Q 1 ≠ 0 ∧ P 1 ≠ Q 1
```

⚠️ `hgen` **survives** — the coherent system is still there — so what the deletion removes is
exactly the non-degeneracy, and `hgen` alone does not give it. (The ambient `F`, `W` and their
instances appear in the context because this `example` sits inside the file's section variable
block; they are not used.) ⚠️ The `hgen` line is reflowed here to stay inside 100 columns; the
compiler prints it on one line. -/
example : ∃ P Q : (exampleCurveThree⁄exampleField).Point,
    AddSubgroup.closure ({P, Q} : Set (exampleCurveThree⁄exampleField).Point)
      = (exampleCurveThree⁄exampleField).torsion (3 ^ 1) ∧ P ≠ 0 ∧ Q ≠ 0 ∧ P ≠ Q := by
  obtain ⟨P, Q, hgen, -, -⟩ :=
    exists_compatible_basis_three (W := exampleCurveThree⁄exampleField) exampleTwo exampleThree
  exact ⟨P 1, Q 1, hgen 1,
    ne_zero_and_ne_of_closure_pair_three exampleTwo exampleThree le_rfl (hgen 1)⟩

end Nonvacuity

end WeierstrassCurve.Affine
