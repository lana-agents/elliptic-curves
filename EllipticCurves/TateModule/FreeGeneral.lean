/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import EllipticCurves.Fixtures
import EllipticCurves.TateModule.PrimaryFree
import EllipticCurves.Torsion.StructureGeneral

/-!
# `T_ℓE ≅ ℤ_ℓ²` at every prime `ℓ ≠ char F` — `#268`

For an elliptic curve `W` over an algebraically closed field `F` with `(2 : F) ≠ 0`, and a prime
`ℓ` with `(ℓ : F) ≠ 0`, the `ℓ`-adic Tate module `T_ℓE = lim_k E[ℓ^k]` is a free `ℤ_[ℓ]`-module of
rank `2` (Silverman, *AEC*, III.7.1 and Remark 7.1.2):

```
Nonempty (W.tateModule ℓ ≃ₗ[ℤ_[ℓ]] ℤ_[ℓ] × ℤ_[ℓ])
Module.Free ℤ_[ℓ] (W.tateModule ℓ)        Module.finrank ℤ_[ℓ] (W.tateModule ℓ) = 2
```

That is `#268`. ⚠️ **`(ℓ : F) ≠ 0` is the same condition as `ℓ ≠ char F`**, stated in the form the
merged lemmas take rather than through `CharP`, and it is sharp: at `ℓ = char F` the conclusion is
**false**, not unproved — `E[ℓ]` is `0` or `ℤ/ℓℤ` there, so `T_ℓE` has rank `0` or `1`.

## This file contains no argument

Every ingredient was already on `main`; what was missing until now was a structure theorem for
`E[ℓ]` at a general prime, and `EllipticCurves.Torsion.StructureGeneral` supplies it. The four
inputs, and none of them is new here:

* `WeierstrassCurve.Affine.nonempty_torsion_addEquiv` (`EllipticCurves.Torsion.StructureGeneral`) —
  `E[n] ≃+ (ℤ/nℤ)²` at every `n` with `(2 : F) ≠ 0` and `(n : F) ≠ 0`. ⚠️ **Both** hypotheses,
  which is why every `_of_natCast_ne_zero` statement below carries `h2` as well as `hℓ`; the name
  records only the second. ⚠️ **And so does every declaration headline below**, which is a separate
  place from this paragraph: `README.md` (`## Docstring conventions` → `### Reach clauses`) rules
  that a headline is a reach clause in its own right and that module prose does not repair a partial
  one. ⚠️ This is *the* new input.
  `exists_closure_pair_eq_torsion_of_addEquiv` calls itself *"the only place where a structure
  theorem for `E[ℓ]` is used"*, and `EllipticCurves.Torsion.ThreePrimaryBasis` records that at
  `ℓ = 3` the residual goal was exactly `Nonempty (E[3] ≃+ ZMod 3 × ZMod 3)`, supplied by hand.
* `WeierstrassCurve.Affine.card_torsion_eq_sq` (same file) — `#E[n] = n²`, which gives `hcard` in
  the `ℓ^k · ℓ^k` shape `EllipticCurves.TateModule.PrimaryFree` asks for.
* `WeierstrassCurve.Affine.nsmul_surjective_of_two_ne_zero`
  (`EllipticCurves.Torsion.TwoTorsionOrder`) — surjectivity of `[ℓ]` at every `ℓ ≠ 0`, a theorem
  since PR #569. ⚠️ It needs only `(2 : F) ≠ 0`, **not** `(ℓ : F) ≠ 0`.
* `EllipticCurves.TateModule.PrimaryFree` and `EllipticCurves.Torsion.PrimaryBasis`, both already
  written at an arbitrary prime `ℓ`.

⚠️ **Coherence is the load-bearing input, and the levelwise structure theorem does not supply it.**
`nonempty_torsion_addEquiv` gives an isomorphism `E[ℓ^k] ≃+ (ℤ/ℓ^kℤ)²` at each level
*independently*, and a family of unrelated isomorphisms says nothing about an inverse limit. What
`exists_compatible_basis_of_surjective` builds from `[ℓ]`-surjectivity and **one** generating pair
of `E[ℓ]` is the coherent system `ℓ • P (k+1) = P k`; that recursion, not the structure theorem, is
why `E[ℓ]` alone suffices.

## Relation to the `ℓ = 2` and `ℓ = 3` files

`EllipticCurves.TateModule.Free` (`ℓ = 2`) and `EllipticCurves.TateModule.FreeThree` (`ℓ = 3`)
are **subsumed** at the level of conclusions: `2` and `3` are primes, and `(2 : F) ≠ 0`,
`(3 : F) ≠ 0` are exactly what those files assume. ⚠️ **They are nevertheless kept, and should be.**
`Free.lean` reaches `ℓ = 2` through the tangent-line doubling argument and `FreeThree.lean` through
`x(3P) = Φ₃/Ψ₃²`; this file reaches every prime through `#E[n] = n²` and the Wronskian identity.
Those are genuinely different routes to the same conclusion, and the cheapest available cross-check
on both. The `example`s at the bottom of this file make that subsumption machine-checked rather
than asserted.

⚠️ This file also does **not** subsume `EllipticCurves.TateModule.FreeThree`'s
`infinite_tateModule_three` / `nontrivial_tateModule_three` in the sense of making them
uninstantiable — it generalises them, and the `_three` names remain what
`EllipticCurves.TateModule.ImageThree` and its neighbours consume.

## ⚠️ What this does NOT do

* **Nothing at `ℓ = char F`**, where the conclusion is false rather than open.
* **Nothing about the Galois action, its continuity, its image or its determinant.**
  `EllipticCurves.TateModule.PrimaryMatrixRep`, `…PrimaryMatrixContinuity`, `…PrimaryImage`,
  `…PrimaryDeterminant` and `…PrimaryMatrixRepCompat` are all written at an arbitrary prime and all
  record that there was nothing to instantiate them with at `ℓ ≥ 5`. ⚠️ **There is now**, and
  instantiating them is separate work, not done here.
* **No new construction.** Every statement below is an application; the constructions live in
  `EllipticCurves.TateModule.PrimaryFree`, `EllipticCurves.Torsion.PrimaryBasis` and
  `EllipticCurves.Torsion.StructureGeneral`.

## Naming

⚠️ The suffix `_of_natCast_ne_zero` names the hypothesis `(ℓ : F) ≠ 0`, following
`WeierstrassCurve.Affine.finite_torsion_of_intCast_ne_zero`. The unsuffixed name
`nonempty_tateModuleEquivProd` is **already taken by the `ℓ = 2` statement** in
`EllipticCurves.TateModule.Free` — `EllipticCurves.TateModule.FreeThree`'s *Naming* section records
that as a pre-existing irregularity — so a general form cannot have it without renaming a merged
declaration, which is out of scope here.

## Main statements

⚠️ Every public declaration of this file is listed: **8 public, 3 private** (`factPrimeFive`,
`exampleTwoGen`, `exampleFiveGen`, the certificates the non-vacuity `example`s use).

* `WeierstrassCurve.Affine.exists_closure_pair_eq_torsion` : a generating pair of `E[n]` at every
  `n` with `(2 : F) ≠ 0` and `(n : F) ≠ 0` — the base of the tower, and the one place the structure
  theorem enters.
* `WeierstrassCurve.Affine.exists_compatible_basis_of_natCast_ne_zero` : the coherent system of
  generating pairs of the `E[ℓ^k]`.
* `WeierstrassCurve.Affine.card_torsion_pow_mul_self_of_natCast_ne_zero` : `#E[ℓ^k] = ℓ^k · ℓ^k`,
  the shape `EllipticCurves.TateModule.PrimaryFree` takes its count in.
* `WeierstrassCurve.Affine.tateModule.proj_surjective_of_two_ne_zero` : the level projections
  `T_ℓE →+ E[ℓ^k]` are surjective, at every prime `ℓ` with `(2 : F) ≠ 0`. ⚠️ And no
  `(ℓ : F) ≠ 0`.
* **`WeierstrassCurve.Affine.tateModule.nonempty_tateModuleEquivProd_of_natCast_ne_zero`** :
  `T_ℓE ≃ₗ[ℤ_[ℓ]] ℤ_[ℓ] × ℤ_[ℓ]`.
* **`WeierstrassCurve.Affine.tateModule.free_tateModule_of_natCast_ne_zero`**,
  **`…finrank_tateModule_of_natCast_ne_zero`** : `#268`'s deliverable, choice-free.
* `WeierstrassCurve.Affine.tateModule.finite_tateModule_of_natCast_ne_zero` : `T_ℓE` is a finitely
  generated `ℤ_[ℓ]`-module — the shape `ρ_{E,ℓ} : G_F → GL₂(ℤ_ℓ)` needs.

## References

* [J. H. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.7.1 and Remark 7.1.2.
-/

open PadicInt

namespace WeierstrassCurve.Affine

variable {F : Type*} [Field F] [DecidableEq F] {W : Affine F} [IsAlgClosed F] [W.IsElliptic]

/-! ### The base of the tower: a generating pair of `E[n]` at a general `n` -/

/-- **A generating pair of `E[n]`, at every `n` with `(2 : F) ≠ 0` and `(n : F) ≠ 0`.**

`exists_closure_pair_eq_torsion_of_addEquiv` (`EllipticCurves.Torsion.PrimaryBasis`) transports the
two standard vectors of `(ℤ/nℤ)²` along any isomorphism `E[n] ≃+ (ℤ/nℤ)²`, and
`nonempty_torsion_addEquiv` (`EllipticCurves.Torsion.StructureGeneral`) supplies one.

⚠️ This is the `_three`-free twin of `exists_closure_pair_eq_torsion_three`
(`EllipticCurves.Torsion.ThreePrimaryBasis`), whose docstring records — with a deletion test — that
the *only* thing missing at a general prime was the structure theorem for `E[ℓ]`. It is missing no
longer, and nothing else in the tower changes. -/
theorem exists_closure_pair_eq_torsion (h2 : (2 : F) ≠ 0) {n : ℕ} [NeZero n] (hn : (n : F) ≠ 0) :
    ∃ P Q : W.Point, P ∈ W.torsion n ∧ Q ∈ W.torsion n ∧
      AddSubgroup.closure ({P, Q} : Set W.Point) = W.torsion n :=
  (nonempty_torsion_addEquiv (W := W) h2 hn).elim exists_closure_pair_eq_torsion_of_addEquiv

/-! ### The coherent system and the count -/

/-- **Compatible bases for the `ℓ`-primary tower, at every `ℓ` with `(2 : F) ≠ 0` and
`(ℓ : F) ≠ 0`**:

```
∀ k, AddSubgroup.closure {P k, Q k} = W.torsion (ℓ ^ k)
∀ k, ℓ • P (k + 1) = P k        ∀ k, ℓ • Q (k + 1) = Q k
```

⚠️ **This, and not the levelwise structure theorem, is what an inverse limit needs.**
`nonempty_torsion_addEquiv` gives `E[ℓ^k] ≃+ (ℤ/ℓ^kℤ)²` at each level independently; the coherence
`ℓ • P (k+1) = P k` comes from `exists_compatible_basis_of_surjective`'s recursion, which climbs
from a generating pair of `E[ℓ]` using surjectivity of `[ℓ]` alone.

⚠️ Note the asymmetry in the hypotheses: `nsmul_surjective_of_two_ne_zero` needs only `h2` and
`ℓ ≠ 0`, so `(ℓ : F) ≠ 0` is spent **entirely** on the base case — the structure theorem for
`E[ℓ]`. -/
theorem exists_compatible_basis_of_natCast_ne_zero (h2 : (2 : F) ≠ 0) {ℓ : ℕ} [NeZero ℓ]
    (hℓ : (ℓ : F) ≠ 0) :
    ∃ P Q : ℕ → W.Point,
      (∀ k, AddSubgroup.closure ({P k, Q k} : Set W.Point) = W.torsion (ℓ ^ k)) ∧
      (∀ k, ℓ • P (k + 1) = P k) ∧ (∀ k, ℓ • Q (k + 1) = Q k) :=
  exists_compatible_basis_of_surjective (nsmul_surjective_of_two_ne_zero h2 (NeZero.ne ℓ))
    (exists_closure_pair_eq_torsion h2 hℓ)

/-- **`#E[ℓ^k] = ℓ^k · ℓ^k` at every `ℓ` with `(2 : F) ≠ 0` and `(ℓ : F) ≠ 0`**, the shape
`EllipticCurves.TateModule.PrimaryFree` and `EllipticCurves.Torsion.PrimaryBasis` take their
cardinality hypothesis in.

⚠️ No primality: this is `card_torsion_eq_sq` at the index `ℓ^k`, and the only thing checked is
that `(ℓ : F) ≠ 0` propagates to `(ℓ^k : F) ≠ 0`. The `ℓ^k · ℓ^k` shape rather than `(ℓ^k)^2` is
deliberate — `card_torsion_pow_mul_self`'s docstring records that the consumers need it and that
the conversion is a real rewrite, not `rfl`. -/
theorem card_torsion_pow_mul_self_of_natCast_ne_zero (h2 : (2 : F) ≠ 0) {ℓ : ℕ}
    (hℓ : (ℓ : F) ≠ 0) (k : ℕ) : Nat.card (W.torsion (ℓ ^ k)) = ℓ ^ k * ℓ ^ k := by
  have h : ((ℓ ^ k : ℕ) : F) ≠ 0 := by push_cast; exact pow_ne_zero _ hℓ
  rw [card_torsion_eq_sq h2 h, sq]

namespace tateModule

variable {ℓ : ℕ} [Fact ℓ.Prime]

/-! ### `T_ℓE ≅ ℤ_ℓ²` -/

/-- **The level projections `T_ℓE →+ E[ℓ^k]` are surjective**, at every prime `ℓ` with
`(2 : F) ≠ 0`.

⚠️ **No `(ℓ : F) ≠ 0`**: this is a statement about lifting along the tower, and
`nsmul_surjective_of_two_ne_zero` asks only that `ℓ ≠ 0` and `(2 : F) ≠ 0`. It is the general twin
of `proj_three_surjective` (`EllipticCurves.TateModule.FreeThree`), which makes the same
observation at `ℓ = 3`. -/
theorem proj_surjective_of_two_ne_zero (h2 : (2 : F) ≠ 0) (k : ℕ) :
    Function.Surjective (proj (W := W) (ℓ := ℓ) k) :=
  proj_surjective (nsmul_surjective_of_two_ne_zero h2 (Fact.out : ℓ.Prime).pos.ne') k

/-- **`T_ℓE` is `ℤ_[ℓ]`-linearly isomorphic to `ℤ_[ℓ] × ℤ_[ℓ]`, at every prime `ℓ` with
`(2 : F) ≠ 0` and `(ℓ : F) ≠ 0`.**

The isomorphism depends on a choice of coherent system of generating pairs, so it is stated as a
`Nonempty`; the choice-free consequences are `free_tateModule_of_natCast_ne_zero` and
`finrank_tateModule_of_natCast_ne_zero`. -/
theorem nonempty_tateModuleEquivProd_of_natCast_ne_zero (h2 : (2 : F) ≠ 0) (hℓ : (ℓ : F) ≠ 0) :
    Nonempty (W.tateModule ℓ ≃ₗ[ℤ_[ℓ]] ℤ_[ℓ] × ℤ_[ℓ]) :=
  haveI : NeZero ℓ := ⟨(Fact.out : ℓ.Prime).pos.ne'⟩
  nonempty_tateModuleEquivProd_of_card (card_torsion_pow_mul_self_of_natCast_ne_zero h2 hℓ)
    (exists_compatible_basis_of_natCast_ne_zero h2 hℓ)

/-- **`T_ℓE` is a free `ℤ_[ℓ]`-module**, at every prime `ℓ` with `(2 : F) ≠ 0` and
`(ℓ : F) ≠ 0` (Silverman, *AEC*, III.7.1). -/
theorem free_tateModule_of_natCast_ne_zero (h2 : (2 : F) ≠ 0) (hℓ : (ℓ : F) ≠ 0) :
    Module.Free ℤ_[ℓ] (W.tateModule ℓ) :=
  haveI : NeZero ℓ := ⟨(Fact.out : ℓ.Prime).pos.ne'⟩
  free_tateModule_of_card (card_torsion_pow_mul_self_of_natCast_ne_zero h2 hℓ)
    (exists_compatible_basis_of_natCast_ne_zero h2 hℓ)

/-- **`T_ℓE` has rank two over `ℤ_[ℓ]`**, at every prime `ℓ` with `(2 : F) ≠ 0` and
`(ℓ : F) ≠ 0`.

Together with `free_tateModule_of_natCast_ne_zero` this is `#268`: `T_ℓE ≅ ℤ_ℓ²` for every
`ℓ ≠ char F`. -/
theorem finrank_tateModule_of_natCast_ne_zero (h2 : (2 : F) ≠ 0) (hℓ : (ℓ : F) ≠ 0) :
    Module.finrank ℤ_[ℓ] (W.tateModule ℓ) = 2 :=
  haveI : NeZero ℓ := ⟨(Fact.out : ℓ.Prime).pos.ne'⟩
  finrank_tateModule_of_card (card_torsion_pow_mul_self_of_natCast_ne_zero h2 hℓ)
    (exists_compatible_basis_of_natCast_ne_zero h2 hℓ)

/-- **`T_ℓE` is a finitely generated `ℤ_[ℓ]`-module.** Free of rank two, so in particular finite as
a module; this is the shape `ρ_{E,ℓ} : G_F → GL₂(ℤ_ℓ)` needs. -/
theorem finite_tateModule_of_natCast_ne_zero (h2 : (2 : F) ≠ 0) (hℓ : (ℓ : F) ≠ 0) :
    Module.Finite ℤ_[ℓ] (W.tateModule ℓ) :=
  haveI : NeZero ℓ := ⟨(Fact.out : ℓ.Prime).pos.ne'⟩
  finite_tateModule_of_card (card_torsion_pow_mul_self_of_natCast_ne_zero h2 hℓ)
    (exists_compatible_basis_of_natCast_ne_zero h2 hℓ)

/-- **`T_ℓE` is infinite**, at every prime `ℓ` with `(2 : F) ≠ 0` and `(ℓ : F) ≠ 0`: it surjects
onto `E[ℓ^k]`, which has `ℓ^{2k}` elements, for every `k`.

⚠️ Recorded as an `example` and not as a theorem: it is `infinite_tateModule_of_card`
(`EllipticCurves.TateModule.LevelStructure`) applied to the two statements above, and a named twin
would add nothing a consumer cannot write in one line. The point of having it here at all is that
it is an **independent** witness of non-triviality — it never mentions the equivalence — which is
the role `infinite_tateModule_three` plays at `ℓ = 3`. -/
example (h2 : (2 : F) ≠ 0) (hℓ : (ℓ : F) ≠ 0) : Infinite (W.tateModule ℓ) :=
  infinite_tateModule_of_card (Fact.out : ℓ.Prime).one_lt (proj_surjective_of_two_ne_zero h2)
    (card_torsion_pow_mul_self_of_natCast_ne_zero h2 hℓ)

/-! ### Non-vacuity, and the subsumption of the `ℓ = 2` and `ℓ = 3` files

⚠️ `ℓ = 5` is the first prime at which no earlier statement in this development reaches `T_ℓE`:
`EllipticCurves.TateModule.Free` is `ℓ = 2` and `EllipticCurves.TateModule.FreeThree` is `ℓ = 3`.
The certificate curve is the shared `EllipticCurves.Fixture.y2AddYEqX3` over
`EllipticCurves.Fixture.AlgClosedQ`, the same one those two files use. -/

section Nonvacuity

open EllipticCurves.Fixture

/-- ⚠️ `Fact (Nat.Prime 5)` is not in `Mathlib` the way `Nat.fact_prime_two` and
`Nat.fact_prime_three` are, and the *statements* below need it — `ℤ_[5]` does not elaborate without
it — so it cannot be a `haveI` inside a proof. -/
private instance factPrimeFive : Fact (Nat.Prime 5) := ⟨by decide⟩

private lemma exampleTwoGen : (2 : AlgClosedQ) ≠ 0 := two_ne_zero

private lemma exampleFiveGen : ((5 : ℕ) : AlgClosedQ) ≠ 0 := by
  have : ((5 : ℕ) : AlgClosedQ) = 5 := by push_cast; ring
  rw [this]; norm_num

open Classical in
/-- **⚠️ THE LOAD-BEARING CERTIFICATE**: on a curve that exists, `T₅E` really is free of rank two
over `ℤ_[5]`.

`5` is the first prime outside `{2, 3}`, i.e. the first at which neither
`EllipticCurves.TateModule.Free` nor `EllipticCurves.TateModule.FreeThree` says anything. -/
example : Module.Free ℤ_[5] (((y2AddYEqX3 ℚ)⁄AlgClosedQ).tateModule 5) ∧
    Module.finrank ℤ_[5] (((y2AddYEqX3 ℚ)⁄AlgClosedQ).tateModule 5) = 2 :=
  ⟨free_tateModule_of_natCast_ne_zero exampleTwoGen exampleFiveGen,
    finrank_tateModule_of_natCast_ne_zero exampleTwoGen exampleFiveGen⟩

open Classical in
/-- ⚠️ **The subsumption of `EllipticCurves.TateModule.Free` and
`EllipticCurves.TateModule.FreeThree`, machine-checked.** Both conclusions are re-derived here from
the general statements alone, on the same certificate curve those files use — so *"this is at least
as wide as the two special cases"* is a compiled claim and not a docstring assertion.

⚠️ It does **not** follow that those files are redundant: they reach `ℓ = 2` and `ℓ = 3` by
routes (tangent-line doubling; `x(3P) = Φ₃/Ψ₃²`) that this one does not use, so each is a check on
the other. -/
example : Module.Free ℤ_[2] (((y2AddYEqX3 ℚ)⁄AlgClosedQ).tateModule 2) ∧
    Module.Free ℤ_[3] (((y2AddYEqX3 ℚ)⁄AlgClosedQ).tateModule 3) :=
  ⟨free_tateModule_of_natCast_ne_zero exampleTwoGen (by exact_mod_cast exampleTwoGen),
    free_tateModule_of_natCast_ne_zero exampleTwoGen
      (by have : ((3 : ℕ) : AlgClosedQ) = 3 := by push_cast; ring
          rw [this]; exact three_ne_zero_of_charZero _)⟩

end Nonvacuity

end tateModule

end WeierstrassCurve.Affine
