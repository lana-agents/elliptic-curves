/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import EllipticCurves.TateModule.Determinant
import EllipticCurves.TateModule.PrimaryMatrixContinuity

/-!
# `ρ_{E,2} : G → GL₂(ℤ_[2])` is continuous for the `2`-adic topology

`EllipticCurves.TateModule.MatrixRep` builds the matrix form `galoisRepMatrixTwo b` of the `2`-adic
Galois representation out of a basis `b` of `T₂E`, as a homomorphism of abstract groups;
`EllipticCurves.TateModule.Continuity` proves that the *abstract* representation
`galoisRep 2 : G →* Aut(T₂E)` is continuous for the profinite topology on `T₂E`. Neither says
anything about `GL₂(ℤ_[2])` with its `2`-adic topology, which is what "the `2`-adic representation"
classically means. This file closes that gap at `ℓ = 2`.

## What this file contains, and what it does not

The argument is in `EllipticCurves.TateModule.PrimaryMatrixContinuity`, stated for an arbitrary
prime `ℓ`. **This file supplies its one input at `ℓ = 2` and contains no argument**: every proof
below is one line. The input is `nonempty_tateModuleEquivProd` (`EllipticCurves.TateModule.Free`),
and it is needed only by the three basis-free statements — the four that are handed a basis need
nothing at all.

⚠️ **The compact-to-Hausdorff argument this file used to carry, and the "circularity" it
dissolves, are now in `EllipticCurves.TateModule.PrimaryMatrixContinuity`**, where they are stated
at an arbitrary prime. They were never `2`-specific; nothing about them changed in moving.

## ⚠️ Nine declarations left this file and did NOT become `Two`-suffixed twins

⚠️ **This is the one thing to know before reading the extraction, and it is a departure from
`EllipticCurves.TateModule.MatrixRep` and `EllipticCurves.TateModule.Determinant`.** Those files
kept `2`-suffixed spellings of their generic definitions, because their `ℓ = 2` names always were
suffixed (`tateModuleBasisTwo`, `galoisDetTwo`). The nine coordinate-homeomorphism declarations
this file used to carry were **not** suffixed:

```
tateModule.continuous_equivFun_symm      tateModule.coordContinuousLinearEquiv
tateModule.coordHomeomorph               tateModule.coe_coordContinuousLinearEquiv
tateModule.coe_coordHomeomorph           tateModule.coordContinuousLinearEquiv_toLinearEquiv
tateModule.coe_coordHomeomorph_symm      tateModule.continuous_equivFun
tateModule.continuous_repr_apply
```

so a generic twin in the same namespace would be a **name collision**, not a duplication. They are
therefore *generalised in place*: each is now the `ℓ`-generic declaration of the same full name in
`EllipticCurves.TateModule.PrimaryMatrixContinuity`, and every existing use — `coordHomeomorph b`
for `b : Module.Basis (Fin 2) ℤ_[2] ((W'⁄F).tateModule 2)` — elaborates to exactly what it used
to, because `ℓ` is determined by `b`. ⚠️ **This is why there is no `coordHomeomorphThree`, and why
`EllipticCurves.TateModule.MatrixContinuityThree` does not restate any of the nine.**

> ⚠️ **A declaration whose `ℓ = 2` name is unsuffixed cannot have a generic twin; it can only be
> generalised.** `EllipticCurves.Torsion.PrimaryBasis` did the same to four names of
> `EllipticCurves.Torsion.TwoPrimaryBasis`. The build cannot tell the two situations apart, which
> is why it is written down here.

⚠️ **A tenth and eleventh declaration also left, for a different reason.**
`PadicInt.not_discreteTopology` and `Matrix.GeneralLinearGroup.not_discreteTopology_padicInt` were
written at an arbitrary prime `p` from the very beginning; they are now in the generic file so that
both instantiations can **cite** them. `EllipticCurves.TateModule.Image` and
`EllipticCurves.TateModule.ImageProfinite` reach them through this file's imports exactly as
before.

## ⚠️ Seven declarations need a `Three` twin, not eighteen and not sixteen

⚠️ **Two sentences on `main` said each of this file's eighteen declarations had to be restated at
`ℓ = 3`** — this file's own Scope paragraph and `EllipticCurves.TateModule.MatrixRepThree`'s
Continuity bullet, measured with `git grep -n eighteen <base> -- EllipticCurves/TateModule/` before
the repair. ⚠️ **A third count, in `#1013`, cut that to sixteen. All three are wrong, and
the true number is seven** — the `Two`-suffixed statements below. Of the eighteen this file used to
have: nine are unsuffixed and were generalised in place (above), two were already `p`-generic
(above), and seven remain here as
`ℓ = 2` instantiations. `EllipticCurves.TateModule.MatrixContinuityThree` has exactly seven
mathematical declarations for that reason.

> ⚠️ **`grep -c` counts a file; only the `variable` blocks and the *names* say how much work a twin
> is.** The first count came from counting declarations, the second from reading `variable` blocks,
> and it still took reading the *names* to get it right.

## What is proved

* `continuous_galoisRepMatrixTwo` — `ρ_{E,2} : G →* GL₂(ℤ_[2])` is continuous, for the Krull
  topology on `G` and the topology `GL₂(ℤ_[2])` inherits from `ℤ_[2]` through
  `Units.instTopologicalSpaceUnits`.
* `continuous_galoisDetTwo`, `continuous_galoisTraceTwo` — the invariants of
  `EllipticCurves.TateModule.Determinant` are continuous.
* `exists_continuous_galoisRepMatrixTwo` — the choice-free capstone, the continuous refinement of
  `exists_galoisRepMatrixTwo`.

This supersedes the remark "Continuity is not asserted" in `galoisRepMatrixTwo`'s docstring. That
file is not edited here.

## Non-degeneracy

`Continuous ρ` is true whenever `G = F ≃ₐ[S] F` is trivial, and no theorem about `G` alone can
exclude that: it is a fact about the extension `F / S`, not about the curve. The capstone therefore
keeps the compatibility clause `⇑(b.repr (σ • f)) = ↑(ρ σ) *ᵥ ⇑(b.repr f)` — without it,
`∃ ρ, Continuous ρ` is witnessed by the trivial homomorphism and mentions neither the curve nor its
Tate module.

The reading that *this file* must exclude is a different one: that continuity into `GL₂(ℤ_[2])` is
automatic. It would be, if the codomain were discrete — and that is exactly the situation of
`continuous_galoisRepMod`, where `E[n]` carries the discrete topology and continuity is only
levelwise local constancy. It is not the situation here, and
`Matrix.GeneralLinearGroup.not_discreteTopology_padicInt` says so: `GL₂(ℤ_[p])` is not discrete,
because the unipotent line `x ↦ !![1, x; 0, 1]` embeds the non-discrete `ℤ_[p]` into it. So the
statement proved here is a genuine constraint on `ρ_{E,2}`, not a formality. ⚠️ That certificate
now lives in `EllipticCurves.TateModule.PrimaryMatrixContinuity` and is cited, not restated.

On the source side the same discrimination is already available: `T₂E` is not discrete
(`tateModule.not_discreteTopology_tateModule_two`, from `EllipticCurves.TateModule.Profinite`), so
`coordHomeomorph` is not a homeomorphism between discrete spaces either.

## Scope

⚠️ **`ℓ = 3` is no longer missing.** The clause this paragraph used to carry — *"the `ℓ = 3` twin
of this file is a genuine follow-up … each of the eighteen declarations below has to be
restated"* — is superseded on both counts: the twin exists
(`EllipticCurves.TateModule.MatrixContinuityThree`), and the number of declarations it restates is
seven. ⚠️ Two earlier clauses of this paragraph were already recorded as false and repaired before
that: *"Odd `ℓ` needs `T_ℓE ≅ ℤ_ℓ²`, which is gated on the finiteness of `E[ℓ^k]`"*, false at
`ℓ = 3` on both counts (`finite_torsion_three_pow`, `EllipticCurves.Torsion.ThreePrimary`;
`EllipticCurves.TateModule.FreeThree`), and *"What is missing at `ℓ = 3` is the matrix
representation `galoisRepMatrixThree`, which nothing in this development states yet"*, false since
`EllipticCurves.TateModule.MatrixRepThree`.

⚠️ **This file does not reach `EllipticCurves.TateModule.Profinite`** — not directly and not
transitively, measured by walking the `import` graph — so no proof below consumes anything from it
and the single mention above is a prose cross-reference. That file is **not** `ℓ = 2` only either:
its `variable` block is `(W : Affine F) (ℓ : ℕ)` and `compactSpace`, `isCompact_coe`, `levelFamily`
and `isClosedEmbedding_levelFamily` are all stated at an arbitrary prime, with instantiated layers
at `ℓ = 2` **and** `ℓ = 3`, five declarations each. ⚠️ The cross-reference at *"`T₂E` is not
discrete"* above is a **different** sentence and is correct: it cites a true statement of that file
as a fact, not as a gate.

⚠️ At `ℓ ≥ 5` the gate is real, but it is **not** the general coordinate formula.  This paragraph
used to name that formula, and it is proved at every index (`hasXCoordFormula_of_two_ne_zero`,
`EllipticCurves.Torsion.NsmulOrder`), as is `[ℓ]`-surjectivity with it
(`nsmul_surjective_of_two_ne_zero`, `EllipticCurves.Torsion.TwoTorsionOrder`).  What nothing
supplies at `ℓ ≥ 5` is still the generic file's hypothesis `Nonempty (T_ℓE ≃ₗ ℤ_[ℓ]²)`, and what
that rests on is the count `#E[ℓ^k]`.  ⚠️ That count is no longer owed:
`card_torsion_pow_mul_self_of_odd` (`EllipticCurves.Torsion.PrimaryTowerOdd`) supplies it at every
odd `ℓ` with `(ℓ : F) ≠ 0`, so what is left at `ℓ ≥ 5` is to build the linear equivalence on top of
it — `#268`, and not this file.

Everything is stated for a base change `W'⁄F` of a curve `W' : Affine S` rather than for a bare
`W : Affine F`, matching the representation section of `EllipticCurves.TateModule.MatrixRep`. This
is forced: `tateModule.instContinuousSMulPadicInt` and `tateModule.continuous_galois_smul` are
themselves stated about `(W'⁄F).tateModule ℓ`, and instance search will not unify a bare `W` with
`?W'.baseChange F`.

Not proved here: that `det ρ_{E,2}` is the cyclotomic character (Weil-pairing gated); that the
image of `ρ_ℓ` is open or closed (`G` is not known compact); that `ρ_{E,2}` is locally constant (it
is not — see `EllipticCurves.TateModule.OpenKernel`).

## Main statements

* `WeierstrassCurve.Affine.continuous_galoisRepMatrixTwo`
* `WeierstrassCurve.Affine.continuous_galoisDetTwo`,
  `WeierstrassCurve.Affine.continuous_galoisTraceTwo`
* `WeierstrassCurve.Affine.exists_continuous_galoisRepMatrixTwo`

## References

* [J. H. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.7.
-/

open Matrix

open scoped WeierstrassCurve.Affine.ProfiniteTopology

namespace WeierstrassCurve.Affine

variable {S F : Type*} [Field S] [Field F] [DecidableEq F] [Algebra S F] {W' : Affine S}

/-! ### Continuity of the matrix representation -/

variable [Algebra.IsIntegral S F]
variable (b : Module.Basis (Fin 2) ℤ_[2] ((W'⁄F).tateModule 2))

/-- **The matrix of `ρ_{E,2}(σ)` depends continuously on `σ`.**

Entrywise: `(ρ σ) i j = b.repr (σ • b j) i` is the composite of the continuous orbit map
`σ ↦ σ • b j` with the continuous coordinate function. Definitionally
`continuous_galoisRepMatrix_coe` at `ℓ = 2`. -/
theorem continuous_galoisRepMatrixTwo_coe :
    Continuous fun σ : F ≃ₐ[S] F =>
      (galoisRepMatrixTwo b σ : Matrix (Fin 2) (Fin 2) ℤ_[2]) :=
  continuous_galoisRepMatrix_coe b

/-- **`ρ_{E,2} : G →* GL₂(ℤ_[2])` is continuous**, for the Krull topology on `G` and the `2`-adic
topology on `GL₂(ℤ_[2])`.

This is the classical statement that `galoisRepMatrixTwo` was one step short of. `GL` carries the
topology induced from `Matrix × Matrix` by `u ↦ (u, u⁻¹)`, so both the matrix and its inverse must
vary continuously; the inverse costs nothing, since `↑(ρ σ)⁻¹ = ↑(ρ σ⁻¹)` and inversion is
continuous in the topological group `G`. -/
theorem continuous_galoisRepMatrixTwo : Continuous (galoisRepMatrixTwo b) :=
  continuous_galoisRepMatrix b

/-! ### The invariants are continuous -/

/-- **The determinant character `det ρ_{E,2} : G →* ℤ_[2]ˣ` is continuous.**

`galoisDetTwo` is basis-free, but its continuity is proved through a basis, which is why one is
taken as an argument; `continuous_galoisDetTwo` removes it at `ℓ = 2`. -/
theorem continuous_galoisDetTwo_of_basis
    (b : Module.Basis (Fin 2) ℤ_[2] ((W'⁄F).tateModule 2)) :
    Continuous (galoisDetTwo (W' := W') (F := F)) :=
  continuous_galoisDet_of_basis b

/-- **The trace `tr ρ_{E,2} : G → ℤ_[2]` is continuous.** Unlike the determinant this is not a
homomorphism, so there is no unit-topology bookkeeping: it is the matrix trace of a continuously
varying matrix. -/
theorem continuous_galoisTraceTwo_of_basis
    (b : Module.Basis (Fin 2) ℤ_[2] ((W'⁄F).tateModule 2)) :
    Continuous (galoisTraceTwo (W' := W') (F := F)) :=
  continuous_galoisTrace_of_basis b

/-! ### The unconditional `ℓ = 2` layer and the capstone -/

section Two

variable [IsAlgClosed F] [(W'⁄F).IsElliptic]

/-- `det ρ_{E,2}` is continuous, with no basis supplied: over an algebraically closed field of
characteristic `≠ 2` a basis exists (`nonempty_tateModuleEquivProd`), and continuity is a `Prop`,
so the choice can be discharged. -/
theorem continuous_galoisDetTwo (h2 : (2 : F) ≠ 0) :
    Continuous (galoisDetTwo (W' := W') (F := F)) :=
  continuous_galoisDet_of_nonempty (tateModule.nonempty_tateModuleEquivProd h2)

/-- `tr ρ_{E,2}` is continuous, with no basis supplied. -/
theorem continuous_galoisTraceTwo (h2 : (2 : F) ≠ 0) :
    Continuous (galoisTraceTwo (W' := W') (F := F)) :=
  continuous_galoisTrace_of_nonempty (tateModule.nonempty_tateModuleEquivProd h2)

/-- **`ρ_{E,2}` is a continuous `2`-adic matrix representation.**

The continuous refinement of `exists_galoisRepMatrixTwo`: there are a basis of `T₂E` and a
**continuous** homomorphism `ρ : G →* GL₂(ℤ_[2])` whose matrices compute the Galois action on
coordinate vectors.

The compatibility clause is load-bearing. `∃ ρ, Continuous ρ` alone is witnessed by the trivial
homomorphism and would mention neither the curve nor its Tate module; it is the clause that ties
`ρ` to `σ • ·` on `T₂E`.

⚠️ **Deletion test**, measured on this file as committed. Replacing the argument
`(tateModule.nonempty_tateModuleEquivProd h2)` by a hole — `by refine
exists_continuous_galoisRepMatrix_of_nonempty (W' := W') (F := F) (ℓ := 2) ?_` — leaves

```
error: unsolved goals
S : Type u_1
F : Type u_2
inst✝⁶ : Field S
inst✝⁵ : Field F
inst✝⁴ : DecidableEq F
inst✝³ : Algebra S F
W' : Affine S
inst✝² : Algebra.IsIntegral S F
inst✝¹ : IsAlgClosed F
inst✝ : WeierstrassCurve.IsElliptic W'⁄F
h2 : 2 ≠ 0
⊢ Nonempty (↥((W'⁄F).tateModule 2) ≃ₗ[ℤ_[2]] ℤ_[2] × ℤ_[2])
```

⚠️ `h2` **survives** in the context, and so do `[IsAlgClosed F]` and `[(W'⁄F).IsElliptic]`, so what
the deletion removes is a construction and not a hypothesis; the residual is a **goal**, which no
type mismatch could produce. It is the rank-two input of `EllipticCurves.TateModule.Free`.

⚠️ The residual goal itself mentions neither `[IsAlgClosed F]` nor `[(W'⁄F).IsElliptic]` — they are
consumed *inside* `nonempty_tateModuleEquivProd` — so the surviving instances are not a route to
discharging it by hand; the theorem is. ⚠️ There is **no knock-on**: nothing below consumes this
declaration. -/
theorem exists_continuous_galoisRepMatrixTwo (h2 : (2 : F) ≠ 0) :
    ∃ (b : Module.Basis (Fin 2) ℤ_[2] ((W'⁄F).tateModule 2))
      (ρ : (F ≃ₐ[S] F) →* GL (Fin 2) ℤ_[2]), Continuous ρ ∧
        ∀ (σ : F ≃ₐ[S] F) (f : (W'⁄F).tateModule 2),
          ⇑(b.repr (σ • f)) = (ρ σ : Matrix (Fin 2) (Fin 2) ℤ_[2]) *ᵥ ⇑(b.repr f) :=
  exists_continuous_galoisRepMatrix_of_nonempty (tateModule.nonempty_tateModuleEquivProd h2)

end Two

end WeierstrassCurve.Affine
