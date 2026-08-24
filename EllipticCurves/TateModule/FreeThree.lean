/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import EllipticCurves.TateModule.PrimaryFree
import EllipticCurves.Torsion.ThreePrimaryBasis

/-!
# `T₃E ≅ ℤ₃²` : the Tate module at `ℓ = 3` is free of rank two

For an elliptic curve `W` over an algebraically closed field `F` with `(2 : F) ≠ 0` and
`(3 : F) ≠ 0`, the `3`-adic Tate module `T₃E = lim_k E[3^k]` is a free `ℤ_[3]`-module of rank `2`
(Silverman, *AEC*, III.7.1 and Remark 7.1.2):

```
Nonempty (W.tateModule 3 ≃ₗ[ℤ_[3]] ℤ_[3] × ℤ_[3])
Module.Free ℤ_[3] (W.tateModule 3)          Module.finrank ℤ_[3] (W.tateModule 3) = 2
```

This is the **second** prime at which `T_ℓE ≅ ℤ_ℓ²` is available in this development, and the first
odd one.

## What this file contains, and what it does not

The construction is in `EllipticCurves.TateModule.PrimaryFree`, stated for an arbitrary prime `ℓ`
in terms of three inputs: a coherent system of generating pairs of the groups `E[ℓ^k]`, the count
`#E[ℓ^k] = ℓ^k · ℓ^k`, and finiteness of `E[ℓ^k]`. **This file supplies those three inputs at
`ℓ = 3` and specialises every statement; it contains no argument.** They are

* `exists_compatible_basis_three` (`EllipticCurves.Torsion.ThreePrimaryBasis`), the coherent
  system — coherence is essential and is not supplied by the structure theorem:
  `E[3^k] ≃+ (ZMod (3^k))²` holds at each level *independently*, and a family of unrelated
  isomorphisms says nothing about an inverse limit;
* `card_torsion_three_pow_mul_self` and `finite_torsion_three_pow`
  (`EllipticCurves.Torsion.ThreePrimary`).

⚠️ **Two hypotheses, not one.** Where the `ℓ = 2` file `EllipticCurves.TateModule.Free` carries only
`h2`, everything here carries both `h2` and `h3`, and the provenance is not symmetric:
`nsmul_three_surjective` needs **only** `(2 : F) ≠ 0`, so the coherent system's *lifting* step is
`h3`-free; `h3` enters exclusively through the counting theorem `card_torsion_three_pow`, i.e.
through `#E[3] = 9`. That is the same split `EllipticCurves.Torsion.ThreePrimary` and
`EllipticCurves.Torsion.ThreePrimaryBasis` document for the tower below.

## Naming

Every statement here is the `ℓ = 3` twin of a public name in `EllipticCurves.TateModule.Free` or in
the `section Two` of `EllipticCurves.TateModule.LevelStructure`, and both of those live in the same
namespace `WeierstrassCurve.Affine.tateModule`. ⚠️ **The rule is: theorem names take a `_three`
suffix where the `2`-version takes `_two`, and `nonempty_tateModuleEquivProd`, which has no `_two`,
becomes `nonempty_tateModuleEquivProd_three`.** This matches
`EllipticCurves.Torsion.ThreePrimaryBasis`, which turns `torsionPairHom_bijective` into
`torsionPairHom_bijective_three`.

⚠️ There is deliberately **no** `padicPairEquivThree`, `padicPairHomThree` or the like. Those names
are already general in `ℓ` in `EllipticCurves.TateModule.PrimaryFree`, so `padicPairEquiv …` is the
call at `ℓ = 3` exactly as it is at `ℓ = 2`; a twin of an already-generic definition would be pure
duplication.

## Where the `ℓ = 3` twins of `LevelStructure`'s `section Two` live, and why here

`EllipticCurves.TateModule.LevelStructure` states level surjectivity generically
(`proj_surjective`, which takes `[ℓ]`-surjectivity as a hypothesis) and non-vacuity generically
(`infinite_tateModule_of_card`, which takes the count as a hypothesis), and then instantiates both
at `ℓ = 2` in its own `section Two`. The `ℓ = 2` instances can live there because that file already
imports `EllipticCurves.Torsion.TwoPrimary`.

⚠️ **The `ℓ = 3` instances are placed here instead, and the asymmetry is deliberate.** Putting them
in `LevelStructure.lean` would mean adding `import EllipticCurves.Torsion.ThreePrimary` — and hence
the whole tripling-surjectivity and division-polynomial stack — to a file whose stated purpose is
the *levelwise-generic* structure of `T_ℓE`. The cost of the choice made here is exactly this
paragraph; the cost of the other choice would have been paid by every future reader of
`LevelStructure.lean`.

## Non-vacuity

`Module.Free` and `finrank = 2` would both be *false* for the zero module, so they cannot be
satisfied vacuously. `infinite_tateModule_three` establishes that independently of the equivalence
built here, by a route that never mentions it: `T₃E` surjects onto `E[3^k]`, which has `9^k`
elements. Both routes, and the concrete curve on which the hypotheses are simultaneously
satisfiable, are certified in the `Nonvacuity` section at the end of this file.

## Scope

* ⚠️ **This file consumes the multiplication-by-`n` coordinate formula `x(nP) = Φₙ/ΨSqₙ`**, at
  `n = 3`, through `EllipticCurves.Torsion.TriplingSurjective`. `EllipticCurves.TateModule.Free`
  says of itself that nothing in it uses that formula; **that sentence must not be read as applying
  here.** Ward's theorem and the elliptic-net recurrence remain unused at every `ℓ`.
* **General odd `ℓ` stays out.** `[ℓ]`-surjectivity for `ℓ ≥ 5` needs the *general* coordinate
  formula, still gated behind the `ωₙ` crux; `EllipticCurves.TateModule.PrimaryFree` is already
  stated at an arbitrary prime, so when that gate is paid the `ℓ ≥ 5` file will again be a list of
  instantiations and no argument will have to be written a third time.
* **The Galois action on `T₃E` and `ρ_{E,3} : G → GL₂(ℤ_3)` are NOT in scope.**
  `EllipticCurves.TateModule.Free` names them as its own follow-up at `ℓ = 2` and the same split
  applies at `ℓ = 3`.
* ⚠️ **`det ρ_{E,3} = χ_3` `3`-adically is NOT unblocked by this.** The **mod-`3`** identity landed
  as `EllipticCurves.FunctionField.WeilPairingDeterminantCharacter`; the `3`-adic one needs the Weil
  pairing on `E[3^k]` for **every** `k`, which needs the pairing at composite `n`. This rung
  supplies the module, not the pairing. After the mod-`3` identity,
  `EllipticCurves.TateModule.Determinant` looks like it just got closer to the `3`-adic statement;
  it did not.

## Main statements

* `WeierstrassCurve.Affine.tateModule.proj_three_surjective`: `proj k : T₃E →+ E[3^k]` is onto.
* `WeierstrassCurve.Affine.tateModule.infinite_tateModule_three` and
  `WeierstrassCurve.Affine.tateModule.nontrivial_tateModule_three`: `T₃E` is not the zero module.
* `WeierstrassCurve.Affine.tateModule.nonempty_tateModuleEquivProd_three`:
  `Nonempty (T₃E ≃ₗ[ℤ_[3]] ℤ_[3] × ℤ_[3])`.
* `WeierstrassCurve.Affine.tateModule.free_tateModule_three`: `Module.Free ℤ_[3] T₃E`.
* `WeierstrassCurve.Affine.tateModule.finrank_tateModule_three`: `finrank ℤ_[3] T₃E = 2`.
* `WeierstrassCurve.Affine.tateModule.finite_tateModule_three`: `Module.Finite ℤ_[3] T₃E`.

## References

* [J. H. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.7.1 and Remark 7.1.2.
-/

open scoped AddSubgroup

namespace WeierstrassCurve.Affine

namespace tateModule

variable {F : Type*} [Field F] [DecidableEq F] {W : Affine F}

section Three

variable [IsAlgClosed F] [W.IsElliptic]

/-! ### The `ℓ = 3` twins of `LevelStructure`'s `section Two` -/

/-- **`proj k : T₃E →+ E[3^k]` is surjective** over an algebraically closed field in which `2 ≠ 0`,
because multiplication by `3` is then surjective on `E(F̄)`.

⚠️ No `h3`: `nsmul_three_surjective` does not need it. -/
theorem proj_three_surjective (h2 : (2 : F) ≠ 0) (k : ℕ) :
    Function.Surjective (proj (W := W) (ℓ := 3) k) :=
  proj_surjective (nsmul_three_surjective h2) k

/-- **`T₃E` is infinite.** It surjects onto `E[3^k]`, which has `9^k` elements, for every `k`.

This is where `h3` first appears in the file, and it appears through the count. -/
theorem infinite_tateModule_three (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) :
    Infinite (W.tateModule 3) :=
  infinite_tateModule_of_card (by norm_num) (proj_three_surjective h2)
    (card_torsion_three_pow_mul_self h2 h3)

/-- **`T₃E` is nontrivial**, i.e. it is not the zero module. Weaker than
`infinite_tateModule_three`, but this is the form a consumer usually wants. -/
theorem nontrivial_tateModule_three (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) :
    Nontrivial (W.tateModule 3) :=
  nontrivial_tateModule_of_card (by norm_num) (proj_three_surjective h2)
    (card_torsion_three_pow_mul_self h2 h3)

/-! ### `T₃E ≅ ℤ₃²` -/

/-- **The Tate module at `ℓ = 3` is `ℤ_[3]`-linearly isomorphic to `ℤ_[3] × ℤ_[3]`.** The
isomorphism depends on a choice of coherent system of generating pairs, so it is stated as a
`Nonempty`; the choice-free consequences are `free_tateModule_three` and
`finrank_tateModule_three`.

⚠️ **The coherent system is the load-bearing input, and a deletion test says so.** Replacing
`(exists_compatible_basis_three h2 h3)` by a hole — keeping the consumer
`nonempty_tateModuleEquivProd_of_card` and both cardinality inputs — leaves, measured on this file
as committed:

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
⊢ ∃ P Q,
    (∀ (k : ℕ), AddSubgroup.closure {P k, Q k} = W.torsion (3 ^ k)) ∧
      (∀ (k : ℕ), 3 • P (k + 1) = P k) ∧ ∀ (k : ℕ), 3 • Q (k + 1) = Q k
```

⚠️ Two mechanical changes accompany the deletion and neither adds information: the proof is turned
into `by refine … ?_` so that a hole is legal, and `W` is pinned with `(W := W)`, which the
term-mode form infers from the expected type. `h2` and `h3` **survive** in the context, so what the
deletion removes is not a hypothesis but the construction.

The residual is a **goal**, and it is precisely the coherence requirement: what the levelwise
structure theorem `nonempty_torsionThreePow_addEquiv` gives is an isomorphism at each level with no
relation between levels, and no amount of that supplies this. -/
theorem nonempty_tateModuleEquivProd_three (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) :
    Nonempty (W.tateModule 3 ≃ₗ[ℤ_[3]] ℤ_[3] × ℤ_[3]) :=
  nonempty_tateModuleEquivProd_of_card (finite_torsion_three_pow h2 h3)
    (card_torsion_three_pow_mul_self h2 h3) (exists_compatible_basis_three h2 h3)

/-- **`T₃E` is a free `ℤ_[3]`-module** (Silverman, *AEC*, III.7.1 at `ℓ = 3`). -/
theorem free_tateModule_three (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) :
    Module.Free ℤ_[3] (W.tateModule 3) :=
  free_tateModule_of_card (finite_torsion_three_pow h2 h3)
    (card_torsion_three_pow_mul_self h2 h3) (exists_compatible_basis_three h2 h3)

/-- **`T₃E` has rank two over `ℤ_[3]`.** -/
theorem finrank_tateModule_three (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) :
    Module.finrank ℤ_[3] (W.tateModule 3) = 2 :=
  finrank_tateModule_of_card (finite_torsion_three_pow h2 h3)
    (card_torsion_three_pow_mul_self h2 h3) (exists_compatible_basis_three h2 h3)

/-- **`T₃E` is a finitely generated `ℤ_[3]`-module.** Free of rank two, so in particular finite as
a module; this is the shape `ρ_{E,3} : G_F → GL₂(ℤ_3)` would need. -/
theorem finite_tateModule_three (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) :
    Module.Finite ℤ_[3] (W.tateModule 3) :=
  finite_tateModule_of_card (finite_torsion_three_pow h2 h3)
    (card_torsion_three_pow_mul_self h2 h3) (exists_compatible_basis_three h2 h3)

end Three

/-! ### Non-vacuity

`[IsAlgClosed F]`, `[W.IsElliptic]`, `(2 : F) ≠ 0` and `(3 : F) ≠ 0` are simultaneously satisfiable
on the standard certificate curve `y² + y = x³` over an algebraic closure of `ℚ`, which is the
curve `EllipticCurves.Torsion.ThreePrimary` and `EllipticCurves.Torsion.ThreePrimaryBasis` use for
the same purpose. -/

section Nonvacuity

/-- The curve `y² + y = x³` over `ℚ`, this development's standard `n = 3` certificate curve. -/
private noncomputable def exampleCurveThree : Affine ℚ := ⟨0, 0, 1, 0, 0⟩

/-- An algebraic closure of `ℚ`: a field of characteristic `0`, so both `2 ≠ 0` and `3 ≠ 0`. -/
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
/-- **⚠️ THE LOAD-BEARING CERTIFICATE**: on a curve that exists, `T₃E` really is free of rank two
over `ℤ_[3]` **and** not the zero module.

⚠️ Deleting `nontrivial_tateModule_three exampleTwo exampleThree` from this script — replacing the
last component of the anonymous constructor by a hole (`by refine ⟨…, …, ?_⟩`), and changing
nothing else — leaves, measured:

```
error: unsolved goals
F : Type u_1
inst✝¹ : Field F
inst✝ : DecidableEq F
W : Affine F
⊢ Nontrivial ↥((exampleCurveThree⁄exampleField).tateModule 3)
```

⚠️ The two surviving components are the freeness and the rank, so what the deletion removes is
exactly the statement that the module is not the zero module; and the residual is a **goal**, which
no type mismatch could show. (The ambient `F` and `W` appear because this `example` sits inside the
file's section variable block; they are not used.) -/
example : Module.Free ℤ_[3] ((exampleCurveThree⁄exampleField).tateModule 3) ∧
    Module.finrank ℤ_[3] ((exampleCurveThree⁄exampleField).tateModule 3) = 2 ∧
    Nontrivial ((exampleCurveThree⁄exampleField).tateModule 3) :=
  ⟨free_tateModule_three exampleTwo exampleThree,
    finrank_tateModule_three exampleTwo exampleThree,
    nontrivial_tateModule_three exampleTwo exampleThree⟩

open Classical in
/-- **The independent non-vacuity route on the same curve**: `T₃E` is infinite, proved through the
level projections and `#E[3^k] = 9^k` without ever mentioning the equivalence. -/
example : Infinite ((exampleCurveThree⁄exampleField).tateModule 3) :=
  infinite_tateModule_three exampleTwo exampleThree

end Nonvacuity

end tateModule

end WeierstrassCurve.Affine
