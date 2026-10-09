/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import EllipticCurves.TateModule.FreeThreeCharTwo
import EllipticCurves.TateModule.PrimaryImage

/-!
# `ρ_{E,3} : G_F → GL₂(ℤ₃)` and its continuity in characteristic `2` — `#2340` deliverable 6

For an elliptic curve over an algebraically closed field `F` **of characteristic `2`**, the `3`-adic
Galois representation exists in matrix form, is continuous, has `tr ρ(1) = 2`, and has compact and
closed determinant image:

```
exists_galoisRepMatrix_three_of_two_eq_zero            galoisTrace_one_three_of_two_eq_zero
exists_continuous_galoisRepMatrix_three_of_two_eq_zero isCompact_range_galoisDet_…_of_two_eq_zero
```

⚠️ **Every statement in this file binds `h2 : (2 : F) = 0`** — the *hypothesis* that the base field
has characteristic `2`, not its negation — and that is written into each declaration headline below
as well as into this paragraph, `README.md` (`## Docstring conventions` → `### Reach clauses`)
ruling that module prose does not repair a partial headline. ⚠️ **`[IsAlgClosed F]`,
`[(W'⁄F).IsElliptic]`, `[Algebra.IsIntegral S F]` and `[IsGalois S F]` are `instImplicit` and so
sit outside that rule** (`#2350`, and the landed `### Reach clauses` text).

## What is new, and what is merely instantiated

⛔ **No argument is made here.** Nine landed declarations take
`Nonempty ((W'⁄F).tateModule ℓ ≃ₗ[ℤ_[ℓ]] ℤ_[ℓ] × ℤ_[ℓ])` as a hypothesis and bind nothing whatever
about `2`; `EllipticCurves.TateModule.FreeThreeCharTwo`'s
`nonempty_tateModuleEquivProd_three_of_two_eq_zero` supplies exactly that hypothesis at `ℓ = 3`
over a field of characteristic `2`. **This file is those nine compositions and nothing else** —
each one a single term — so what is new is a reachable characteristic and not a proof.

⚠️ **ALL NINE ARE DELIVERED; the complement is empty.** The nine, with the instance block each
sits under in its own module, measured from the `variable` lines in force at each declaration:

| landed declaration | base-changed? | extra instances |
|---|---|---|
| `tateModule.nonempty_basis_tateModule_of_nonempty` | ⛔ **no**, `{W : Affine F}` | — |
| `exists_galoisRepMatrix_of_nonempty` | yes | — |
| `galoisTrace_one_of_nonempty` | yes | — |
| `charpoly_galoisRepMatrix_one_of_nonempty` | yes | — |
| `continuous_galoisDet_of_nonempty` | yes | `[Algebra.IsIntegral S F]` |
| `continuous_galoisTrace_of_nonempty` | yes | `[Algebra.IsIntegral S F]` |
| `exists_continuous_galoisRepMatrix_of_nonempty` | yes | `[Algebra.IsIntegral S F]` |
| `isCompact_range_galoisDet_of_nonempty` | yes | `[Algebra.IsIntegral S F]`, `[IsGalois S F]` |
| `isClosed_range_galoisDet_of_nonempty` | yes | `[Algebra.IsIntegral S F]`, `[IsGalois S F]` |

⚠️ **The split is 4 / 3 / 2 and ONE of the nine is not base-changed at all.**
`nonempty_basis_tateModule_of_nonempty` lives in `EllipticCurves.TateModule.PrimaryMatrixRep`'s
first `variable` block, over `{W : Affine F}` with no `S` in sight, so its characteristic-`2` form
needs no base change and is stated here in the `tateModule` namespace over `W` directly. The other
eight are stated for `(W'⁄F)` and are grouped by the two extra instance blocks:
`EllipticCurves.TateModule.PrimaryMatrixContinuity`'s `variable [Algebra.IsIntegral S F]` (which is
in force from its line to the end of that namespace — there is no `section` to close it) and
`EllipticCurves.TateModule.PrimaryImage`'s `variable [Algebra.IsIntegral S F] [IsGalois S F]`.

## ⚠️ The fixture decision, stated rather than slipped in

⛔ **This file declares NO fifth copy of `curveClosureCharTwo`, and that is a decision and not an
omission.** Three modules carry a `private noncomputable def curveClosureCharTwo` —
`EllipticCurves.Torsion.TorsionCountCharFree`, `EllipticCurves.Torsion.NsmulSmoothSurjective` and
`EllipticCurves.TateModule.FreeThreeCharTwo` — each being `y2AddXYEqX3AddC F 1` over
`F = AlgebraicClosure (ZMod 2)` **directly**, with no base change. ⚠️ **None of the three can
witness eight of the nine statements here**, whose subject is `(W'⁄F)` for `W' : Affine S`: a
closure-level curve is not a base change of anything.

⇒ **What the non-vacuity block below declares is a different object: the `ZMod 2`-rational curve
`y² + xy = x³ + 1`, base-changed to its own algebraic closure.** It is `curveCharTwoBase` over
`ZMod 2` plus the shared `EllipticCurves.Fixture.instIsEllipticBaseChange`, so the `Δ` computation
is **not** re-run on the base change and is **not** transported by hand:
`isElliptic_y2AddXYEqX3AddC` is applied at the base `ZMod 2`, where `(2 : ZMod 2) = 0` is
`by decide`, and the general base-change instance carries it up. ⚠️ That answers the one question
the fixture cost raised — *"the `Δ` computation has to be re-run on `(W'⁄F)` or transported; say
which"* — with **neither**.

⛔ **And `EllipticCurves.Fixtures` is NOT edited, which is also a decision.** A public base-changed
characteristic-`2` curve there would mean either an `IsElliptic` instance on `y2AddXYEqX3AddC`,
which that module's own docstring rules out in terms because `(2 : F) = 0` and `c ≠ 0` are
hypotheses no instance can carry, or a new `ZMod`-valued fixture in a leaf whose whole point is its
two Mathlib imports. ⚠️ **Judged out of scope, and said so rather than left silent.** The fixture
here is `private` and local, like the three it is not a copy of.

## What is NOT here

* ⛔ **Nothing at odd `ℓ ≠ 3`, and nothing is owed there.** The boundary is inherited exactly from
  `EllipticCurves.TateModule.FreeThreeCharTwo` and is widened nowhere: `Separable (preΨ_ℓ)` at
  `2 = 0` is proved at `ℓ = 3` and at no other prime, and
  `EllipticCurves.Torsion.TorsionCountCharFree`'s `section Obstruction` **refutes** the one
  available route to a general odd `ℓ` (`not_isCoprime_preΨ_preΩ_of_two_eq_zero`). ⚠️ So this is a
  gap in the *input*, one prime wide in the other direction, and not a gap in this file.
* ⛔ **Nothing at `ℓ = 2`**, where the conclusion is false rather than unproved: `ℓ = char F` there.
* ⛔ **No landed signature changes, nothing is deprecated and nothing is deleted.** All nine take
  the `Nonempty` as a hypothesis already.
* ⛔ **Not `det ρ_{E,3} = χ₃` in characteristic `2`.** `galoisDet_eq_galoisCyclotomicChar`
  (`EllipticCurves.FunctionField.TateDeterminantCyclotomic`) binds `(2 : F) ≠ 0`; knowing the
  determinant image is closed says nothing about *which* character it is.
* ⛔ **Not surjectivity or openness of the image**, in any characteristic.

## ⚠️ On the file name

The name is the **headline**'s, and the file instantiates four modules rather than one:
`EllipticCurves.TateModule.PrimaryMatrixRep` (two), `…PrimaryDeterminant` (two),
`…PrimaryMatrixContinuity` (three) and `…PrimaryImage` (two). ⚠️ The char-free `ℓ = 3`
instantiations of those four are **four separate files** (`MatrixRepThree`, `DeterminantThree`,
`MatrixContinuityThree`, `ImageThree`); one file is chosen here because every statement below is a
one-line substitution and four leaves carrying one term each would be four module docstrings
arguing the same point.

## Main statements

* `WeierstrassCurve.Affine.tateModule.nonempty_basis_tateModule_three_of_two_eq_zero` :
  `T₃E` has a basis indexed by `Fin 2`, over an algebraically closed field with `2 = 0`.
* `WeierstrassCurve.Affine.exists_galoisRepMatrix_three_of_two_eq_zero` : a basis of `T₃E` and a
  representation `ρ : G →* GL (Fin 2) ℤ_[3]` computing the Galois action exist, with `2 = 0`.
* `WeierstrassCurve.Affine.exists_continuous_galoisRepMatrix_three_of_two_eq_zero` : ⚠️ **the
  headline** — the same with `Continuous ρ`.
* `WeierstrassCurve.Affine.galoisTrace_one_three_of_two_eq_zero`,
  `WeierstrassCurve.Affine.charpoly_galoisRepMatrix_one_three_of_two_eq_zero` : `tr ρ(1) = 2` and
  `charpoly ρ(1) = X² - 2X + 1`, with `2 = 0`.
* `WeierstrassCurve.Affine.continuous_galoisDet_three_of_two_eq_zero`,
  `WeierstrassCurve.Affine.continuous_galoisTrace_three_of_two_eq_zero` : `det ρ` and `tr ρ` are
  continuous, with `2 = 0`.
* `WeierstrassCurve.Affine.isCompact_range_galoisDet_three_of_two_eq_zero`,
  `WeierstrassCurve.Affine.isClosed_range_galoisDet_three_of_two_eq_zero` : `range (det ρ)` is
  compact and closed, with `2 = 0`.

## References

* [J. H. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.7 and VII.7.
-/

open Matrix Polynomial

namespace WeierstrassCurve.Affine

namespace tateModule

/-! ### A basis of `T₃E` in characteristic `2`

⚠️ This is the one of the nine that is **not** stated for a base change: it lives over
`{W : Affine F}`. -/

variable {F : Type*} [Field F] [DecidableEq F] {W : Affine F} [IsAlgClosed F] [W.IsElliptic]

/-- **`T₃E` has a basis indexed by `Fin 2` over an algebraically closed field with `2 = 0`.** The
basis itself depends on the choice of equivalence `T₃E ≃ₗ[ℤ_[3]] ℤ_[3] × ℤ_[3]`; its existence does
not.

This is `nonempty_basis_tateModule_of_nonempty`
(`EllipticCurves.TateModule.PrimaryMatrixRep`) with its hypothesis supplied by
`nonempty_tateModuleEquivProd_three_of_two_eq_zero`
(`EllipticCurves.TateModule.FreeThreeCharTwo`). ⚠️ **`h2` is the whole content**: delete the
argument and the residual is a `Nonempty (T₃E ≃ₗ[ℤ_[3]] ℤ_[3] × ℤ_[3])` **goal** with `h2` still in
context, which is `#2340`'s residue of `#245` and not a type mismatch. -/
theorem nonempty_basis_tateModule_three_of_two_eq_zero (h2 : (2 : F) = 0) :
    Nonempty (Module.Basis (Fin 2) ℤ_[3] (W.tateModule 3)) :=
  nonempty_basis_tateModule_of_nonempty (nonempty_tateModuleEquivProd_three_of_two_eq_zero h2)

end tateModule

/-! ### The matrix representation in characteristic `2`

The subject from here on is the base-changed curve `W'⁄F`, which is what the eight remaining landed
declarations are stated for. ⚠️ `WeierstrassCurve.baseChange` is a plain `def`, so
`[(W'⁄F).IsElliptic]` is **not** found from `[W'.IsElliptic]` by bare `inferInstance`; it is bound
as an instance here and discharged on the fixture below by
`EllipticCurves.Fixture.instIsEllipticBaseChange`. -/

variable {S F : Type*} [Field S] [Field F] [DecidableEq F] [Algebra S F] {W' : Affine S}
variable [IsAlgClosed F] [(W'⁄F).IsElliptic]

/-- **`ρ_{E,3} : G_F → GL₂(ℤ₃)` exists over a field of characteristic `2`**, as a matrix
representation that really does compute the Galois action: there are a basis of `T₃E` and a
homomorphism `ρ : G →* GL₂(ℤ_[3])` whose matrices act on coordinate vectors the way `G` acts on
`T₃E`.

⚠️ The compatibility clause is the point. `Nonempty ((F ≃ₐ[S] F) →* GL (Fin 2) ℤ_[3])` on its own
would be vacuous — the trivial homomorphism witnesses it, and the statement would not mention the
curve at all. -/
theorem exists_galoisRepMatrix_three_of_two_eq_zero (h2 : (2 : F) = 0) :
    ∃ (b : Module.Basis (Fin 2) ℤ_[3] ((W'⁄F).tateModule 3))
      (ρ : (F ≃ₐ[S] F) →* GL (Fin 2) ℤ_[3]), ∀ (σ : F ≃ₐ[S] F) (f : (W'⁄F).tateModule 3),
        ⇑(b.repr (σ • f)) = (ρ σ : Matrix (Fin 2) (Fin 2) ℤ_[3]) *ᵥ ⇑(b.repr f) :=
  exists_galoisRepMatrix_of_nonempty
    (tateModule.nonempty_tateModuleEquivProd_three_of_two_eq_zero h2)

/-- **`tr ρ_{E,3}(1) = 2` over a field of characteristic `2`.** ⚠️ The `2` is in `ℤ_[3]` and not in
`F`: it is the rank of `T₃E`, and it is `2` precisely because the rank is `2`. ⚠️ **Without rank
two the statement is false** and not merely unproved — the trace of the identity is `0` on the zero
module — which is why `h2` cannot be dropped even though the conclusion never mentions `F`. -/
theorem galoisTrace_one_three_of_two_eq_zero (h2 : (2 : F) = 0) :
    galoisTrace (W' := W') (F := F) (ℓ := 3) 1 = 2 :=
  galoisTrace_one_of_nonempty
    (tateModule.nonempty_tateModuleEquivProd_three_of_two_eq_zero h2)

/-- **The characteristic polynomial of `ρ_{E,3}(1)` is `X² - 2X + 1` over a field of characteristic
`2`**, for any basis `b` of `T₃E`. This is `galoisTrace_one_three_of_two_eq_zero` and
`galoisDet_one` combined, and fails for the zero module for the same reason. -/
theorem charpoly_galoisRepMatrix_one_three_of_two_eq_zero
    (b : Module.Basis (Fin 2) ℤ_[3] ((W'⁄F).tateModule 3)) (h2 : (2 : F) = 0) :
    (galoisRepMatrix b 1 : Matrix (Fin 2) (Fin 2) ℤ_[3]).charpoly = X ^ 2 - C 2 * X + C 1 :=
  charpoly_galoisRepMatrix_one_of_nonempty b
    (tateModule.nonempty_tateModuleEquivProd_three_of_two_eq_zero h2)

section IsIntegral

/-! ⚠️ `[Algebra.IsIntegral S F]` is what `EllipticCurves.TateModule.PrimaryMatrixContinuity` puts
the profinite topology on `F ≃ₐ[S] F` under; the three statements below are under it and the four
above are not. -/

variable [Algebra.IsIntegral S F]

/-- **`det ρ_{E,3}` is continuous over a field of characteristic `2`**, with no basis supplied:
a basis exists as soon as `T₃E` is `ℤ_[3]`-linearly `ℤ_[3]²`, and continuity is a `Prop`, so the
choice can be discharged. -/
theorem continuous_galoisDet_three_of_two_eq_zero (h2 : (2 : F) = 0) :
    Continuous (galoisDet (W' := W') (F := F) (ℓ := 3)) :=
  continuous_galoisDet_of_nonempty
    (tateModule.nonempty_tateModuleEquivProd_three_of_two_eq_zero h2)

/-- **`tr ρ_{E,3}` is continuous over a field of characteristic `2`**, with no basis supplied. -/
theorem continuous_galoisTrace_three_of_two_eq_zero (h2 : (2 : F) = 0) :
    Continuous (galoisTrace (W' := W') (F := F) (ℓ := 3)) :=
  continuous_galoisTrace_of_nonempty
    (tateModule.nonempty_tateModuleEquivProd_three_of_two_eq_zero h2)

/-- ⚠️⚠️ **THE HEADLINE: `ρ_{E,3}` is a CONTINUOUS `GL₂(ℤ₃)`-valued representation of `G_F` over a
field of characteristic `2`** — `#2340` deliverable 6 in the one characteristic its `ℓ ≠ char F`
condition leaves, at the one prime `EllipticCurves.TateModule.FreeThreeCharTwo` reaches.

⚠️ `continuous_galoisRep` (`EllipticCurves.TateModule.Continuity`) is already `h2`-free and
`hℓ`-free, so the **`T₃E`-valued** representation needed nothing from this file. **It is the
`GL₂(ℤ₃)` matrix form that goes through the rank-two equivalence**, and that is what was missing in
characteristic `2`.

⚠️ Both clauses are kept — `Continuous ρ` **and** the compatibility clause — because either alone
is vacuous: continuity is satisfied by the trivial homomorphism, and compatibility is satisfied by
anything over a zero module. The non-vacuity block below certifies the module is infinite and the
Galois group is non-trivial, on a curve that exists. -/
theorem exists_continuous_galoisRepMatrix_three_of_two_eq_zero (h2 : (2 : F) = 0) :
    ∃ (b : Module.Basis (Fin 2) ℤ_[3] ((W'⁄F).tateModule 3))
      (ρ : (F ≃ₐ[S] F) →* GL (Fin 2) ℤ_[3]), Continuous ρ ∧
        ∀ (σ : F ≃ₐ[S] F) (f : (W'⁄F).tateModule 3),
          ⇑(b.repr (σ • f)) = (ρ σ : Matrix (Fin 2) (Fin 2) ℤ_[3]) *ᵥ ⇑(b.repr f) :=
  exists_continuous_galoisRepMatrix_of_nonempty
    (tateModule.nonempty_tateModuleEquivProd_three_of_two_eq_zero h2)

section IsGalois

/-! ⚠️ `EllipticCurves.TateModule.PrimaryImage` adds `[IsGalois S F]` on top of
`[Algebra.IsIntegral S F]`, which is what makes `F ≃ₐ[S] F` compact; the two statements below are
the only ones here under it. -/

variable [IsGalois S F]

/-- **`range (det ρ_{E,3})` is compact over a field of characteristic `2`.** -/
theorem isCompact_range_galoisDet_three_of_two_eq_zero (h2 : (2 : F) = 0) :
    IsCompact (Set.range (galoisDet (W' := W') (F := F) (ℓ := 3))) :=
  isCompact_range_galoisDet_of_nonempty
    (tateModule.nonempty_tateModuleEquivProd_three_of_two_eq_zero h2)

/-- **`range (det ρ_{E,3})` is a closed subgroup of `ℤ_[3]ˣ` over a field of characteristic `2`.**
⚠️ This is the layer the identification of `det ρ_{E,3}` with the cyclotomic character consumes, and
**that identification binds `(2 : F) ≠ 0`** — `galoisDet_eq_galoisCyclotomicChar`
(`EllipticCurves.FunctionField.TateDeterminantCyclotomic`) — so nothing here supplies it in
characteristic `2`. Knowing the image of a character is closed says nothing about *which* character
it is. -/
theorem isClosed_range_galoisDet_three_of_two_eq_zero (h2 : (2 : F) = 0) :
    IsClosed (Set.range (galoisDet (W' := W') (F := F) (ℓ := 3))) :=
  isClosed_range_galoisDet_of_nonempty
    (tateModule.nonempty_tateModuleEquivProd_three_of_two_eq_zero h2)

end IsGalois

end IsIntegral

/-! ### Non-vacuity

⚠️ Six of the nine statements above are existentials or topological `Prop`s, so they are the
vacuity-prone kind. **Three things have to be certified and they are different:**

1. that the hypotheses are **simultaneously satisfiable** on a curve that exists — including
   `[IsGalois S F]`, the strongest of them, which only the two `PrimaryImage` statements need;
2. that the module the matrices act on is **not the zero module**, by a route that never mentions
   the matrix representation (`Infinite (T₃E)`);
3. ⚠️ that the **Galois group is not trivial**, without which the compatibility clause
   `b.repr (σ • f) = ρ σ *ᵥ b.repr f` is witnessed by `ρ = 1` and says nothing.

⚠️ **Point 3 is MACHINE-CHECKED here and is not asserted in prose.**
`EllipticCurves.TateModule.MatrixRepGeneral`'s block takes `S = ℚ` and leaves *"a base `S` whose
absolute Galois group is not trivial"* as a docstring claim; over `𝔽₂` the Frobenius gives it
cheaply, so it is proved. `Gal(𝔽̄₂/𝔽₂) ≅ Ẑ` is the full truth and only `Nontrivial` is certified.

⚠️ **The curve is `ZMod 2`-rational and base-changed**, which is what eight of the nine statements
need and what no landed characteristic-`2` fixture supplies — see *The fixture decision* above for
why this is not a fifth `curveClosureCharTwo`. -/

section Nonvacuity

open EllipticCurves.Fixture

/-- `AlgebraicClosure (ZMod 2)`, abbreviated because it occurs in every statement below.
⚠️ `private`, and `private` hides a **name** and not an **instance** (`#1397`). -/
private abbrev ClosureZModTwo : Type := AlgebraicClosure (ZMod 2)

/-- `(2 : ZMod 2) = 0` at the **base**, where it is decidable — which is the whole reason the
fixture is `ZMod 2`-rational rather than closure-level. -/
private lemma two_eq_zero_zmodTwo : (2 : ZMod 2) = 0 := by decide

/-- `y² + xy = x³ + 1` over `ZMod 2` — `EllipticCurves.Fixture.y2AddXYEqX3AddC` at `c = 1`, the
shared `a₁ ≠ 0` ordinary family, **at the base field and not at its closure**.

⛔ **This is not a fourth copy of `curveClosureCharTwo`.** That curve is
`y2AddXYEqX3AddC (AlgebraicClosure (ZMod 2)) 1`, a closure-level object which cannot witness a
statement about `(W'⁄F)`; this one is over `ZMod 2` and is base-changed below.
⚠️ A `def` and not an `abbrev`, so the instance below is found for this name. ⚠️ No
`noncomputable`: `ZMod 2` is a computable field, unlike `AlgebraicClosure (ZMod 2)`. -/
private def curveCharTwoBase : Affine (ZMod 2) := y2AddXYEqX3AddC (ZMod 2) 1

/-- The witness is a genuine elliptic curve **over `ZMod 2`**: `Δ = c` wherever `2 = 0`
(`Δ_y2AddXYEqX3AddC_of_two_eq_zero`), so `c ≠ 0` is the whole condition and `one_ne_zero`
discharges it. ⚠️ `(curveCharTwoBase⁄ClosureZModTwo).IsElliptic` then comes from
`EllipticCurves.Fixture.instIsEllipticBaseChange` — **so the `Δ` computation is neither re-run on
the base change nor transported by hand.** -/
private instance : curveCharTwoBase.IsElliptic :=
  isElliptic_y2AddXYEqX3AddC two_eq_zero_zmodTwo one_ne_zero

/-- ⚠️ **`AlgebraicClosure (ZMod 2)` carries no `DecidableEq` instance**, and Mathlib's
`WeierstrassCurve.Affine.Point` addition sits under `[DecidableEq F]`, so no statement mentioning
`T₃E` over this field elaborates without one.

⚠️ **This instance is a no-op at this head and is kept deliberately, which is measured rather than
asserted**: three modules in this tree declare the same instance `private`, and a `private`
*instance* still participates in synthesis across a module boundary even though its *name* cannot
be imported — so the certificates below elaborate with this line deleted. **It is here so that this
file does not rest on another module's private instance.** -/
private noncomputable instance : DecidableEq ClosureZModTwo := Classical.decEq _

/-- The base field really is of characteristic `2`. ⚠️ This is the closure-level statement, got
from the base by `charP_of_injective_algebraMap`, and it is what every theorem above consumes. -/
private lemma two_eq_zero_closureZModTwo : (2 : ClosureZModTwo) = 0 := by
  have : CharP ClosureZModTwo 2 :=
    charP_of_injective_algebraMap (algebraMap (ZMod 2) ClosureZModTwo).injective 2
  exact_mod_cast CharP.cast_eq_zero ClosureZModTwo 2

/-- `𝔽̄₂/𝔽₂` is Galois, which the two `PrimaryImage` statements need and the other seven do not.
⚠️ Built by the anonymous constructor rather than found: `IsGalois` is a two-field structure and
instance search does not assemble it from `Algebra.IsSeparable` and `Normal`, **both of which are
already instances here** — separability because `ZMod 2` is finite, hence perfect
(`Algebra.IsAlgebraic.isSeparable_of_perfectField`). -/
private instance : IsGalois (ZMod 2) ClosureZModTwo := ⟨⟩

/-- ⚠️ **THE LOAD-BEARING CERTIFICATE**: on a curve that exists, over a base field `S = 𝔽₂` **of
characteristic `2`**, `ρ_{E,3}` really is a continuous `GL₂(ℤ₃)`-valued representation that computes
the Galois action.

⚠️ The statement is restated in full rather than obtained-and-projected (`#916`), and both the
`Continuous ρ` clause and the compatibility clause are kept. -/
example : ∃ (b : Module.Basis (Fin 2) ℤ_[3]
      ((curveCharTwoBase⁄ClosureZModTwo).tateModule 3))
    (ρ : (ClosureZModTwo ≃ₐ[ZMod 2] ClosureZModTwo) →* GL (Fin 2) ℤ_[3]),
      Continuous ρ ∧
        ∀ (σ : ClosureZModTwo ≃ₐ[ZMod 2] ClosureZModTwo)
          (f : (curveCharTwoBase⁄ClosureZModTwo).tateModule 3),
          ⇑(b.repr (σ • f)) = (ρ σ : Matrix (Fin 2) (Fin 2) ℤ_[3]) *ᵥ ⇑(b.repr f) :=
  exists_continuous_galoisRepMatrix_three_of_two_eq_zero two_eq_zero_closureZModTwo

/-- ⚠️ **The two statements under `[IsGalois S F]`, committed on the same curve** — the strongest
instance block of the nine, and the one a closure-level fixture could not reach at all. -/
example : IsCompact (Set.range (galoisDet (W' := curveCharTwoBase)
      (F := ClosureZModTwo) (ℓ := 3))) ∧
    IsClosed (Set.range (galoisDet (W' := curveCharTwoBase)
      (F := ClosureZModTwo) (ℓ := 3))) :=
  ⟨isCompact_range_galoisDet_three_of_two_eq_zero two_eq_zero_closureZModTwo,
    isClosed_range_galoisDet_three_of_two_eq_zero two_eq_zero_closureZModTwo⟩

/-- **`tr ρ(1) = 2` and `charpoly ρ(1) = X² - 2X + 1`, committed.** ⚠️ The second needs a basis, so
it is the one statement of the nine that is not choice-free, and the basis is taken from
`nonempty_basis_tateModule_three_of_two_eq_zero` — this file's own non-base-changed member. -/
example : galoisTrace (W' := curveCharTwoBase) (F := ClosureZModTwo) (ℓ := 3) 1 = 2 ∧
    ∃ b : Module.Basis (Fin 2) ℤ_[3] ((curveCharTwoBase⁄ClosureZModTwo).tateModule 3),
      (galoisRepMatrix b 1 : Matrix (Fin 2) (Fin 2) ℤ_[3]).charpoly =
        X ^ 2 - C 2 * X + C 1 :=
  ⟨galoisTrace_one_three_of_two_eq_zero two_eq_zero_closureZModTwo,
    (tateModule.nonempty_basis_tateModule_three_of_two_eq_zero
        (W := curveCharTwoBase⁄ClosureZModTwo) two_eq_zero_closureZModTwo).elim
      fun b => ⟨b, charpoly_galoisRepMatrix_one_three_of_two_eq_zero b
        two_eq_zero_closureZModTwo⟩⟩

/-- **The module the matrices act on is not the zero module**, by a route that never mentions the
matrix representation: `T₃E` surjects onto `E[3^k]`, which has `9^k` elements.

⚠️ This is what rules out the degenerate reading of the certificates above. `GL (Fin 2) ℤ_[3]`,
`Continuous ρ` and the `mulVec` clause are all perfectly satisfiable over a zero module — every
coordinate vector would be `0` — so the certificates need this. -/
example : Infinite ((curveCharTwoBase⁄ClosureZModTwo).tateModule 3) :=
  tateModule.infinite_tateModule_three_of_two_eq_zero two_eq_zero_closureZModTwo

/-- Frobenius `x ↦ x²` as a `ZMod 2`-algebra automorphism of `𝔽̄₂`. ⚠️ It is `ZMod 2`-linear for a
reason special to `𝔽₂`: `x² = x` for **both** elements of `ZMod 2`, which `decide` settles. ⚠️
`AlgebraicClosure (ZMod 2)` is a `PerfectRing` at `2` because `ZMod 2` is finite hence perfect and
the closure is algebraic over it, so `frobeniusEquiv` is available. -/
private noncomputable def frobeniusClosureZModTwo : ClosureZModTwo ≃ₐ[ZMod 2] ClosureZModTwo :=
  { frobeniusEquiv ClosureZModTwo 2 with
    commutes' := fun x => by
      change (algebraMap (ZMod 2) ClosureZModTwo x) ^ 2 = algebraMap (ZMod 2) ClosureZModTwo x
      rw [← map_pow, show x ^ 2 = x from by revert x; decide] }

/-- `𝔽̄₂` has an element outside `𝔽₂`, exhibited as a root of `X² + X + 1`. ⚠️ The argument is the
characteristic: if `y² = y` then `y² + y + 1 = 0` gives `2y + 1 = 0`, hence `1 = 0`. -/
private lemma exists_sq_ne_self_closureZModTwo : ∃ y : ClosureZModTwo, y ^ 2 ≠ y := by
  obtain ⟨y, hy⟩ := IsAlgClosed.exists_root (k := ClosureZModTwo) (X ^ 2 + X + 1) (by
    have hd : (X ^ 2 + X + 1 : ClosureZModTwo[X]).degree = 2 := by compute_degree!
    rw [hd]; decide)
  refine ⟨y, ?_⟩
  simp only [eval_add, eval_pow, eval_X, eval_one, IsRoot.def] at hy
  intro hsq
  rw [hsq] at hy
  have h : (2 : ClosureZModTwo) * y + 1 = 0 := by linear_combination hy
  rw [two_eq_zero_closureZModTwo] at h
  simp at h

/-- ⚠️⚠️ **THE GALOIS GROUP IS NOT TRIVIAL**, so the compatibility clause of the certificates above
is not witnessed by `ρ = 1` and really does say something about the curve.

⚠️ This is the clause `EllipticCurves.TateModule.MatrixRepGeneral`'s non-vacuity block leaves as a
docstring claim about `Gal(ℚ̄/ℚ)`; here it is compiled. Frobenius moves any `y` with `y² ≠ y`, and
`exists_sq_ne_self_closureZModTwo` produces one. ⚠️ `Gal(𝔽̄₂/𝔽₂) ≅ Ẑ` is the full truth and only
`Nontrivial` is certified — nothing below needs more. -/
example : Nontrivial (ClosureZModTwo ≃ₐ[ZMod 2] ClosureZModTwo) := by
  obtain ⟨y, hy⟩ := exists_sq_ne_self_closureZModTwo
  refine ⟨frobeniusClosureZModTwo, 1, fun h => hy ?_⟩
  simpa [frobeniusClosureZModTwo, frobeniusEquiv_def, frobenius_def] using
    congrArg (fun e => e y) h

end Nonvacuity

end WeierstrassCurve.Affine
