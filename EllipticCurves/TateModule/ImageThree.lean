/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import EllipticCurves.Fixtures
import EllipticCurves.TateModule.MatrixContinuityThree
import EllipticCurves.TateModule.PrimaryImage

/-!
# The image of `ρ_{E,3}` is a closed subgroup of `GL₂(ℤ_[3])`

For a Weierstrass curve `W'` over a field `S`, an algebraically closed extension `F / S` integral
over `S` and Galois over `S`, with `(2 : F) ≠ 0` and `(3 : F) ≠ 0` and `W'⁄F` elliptic, and
`G = F ≃ₐ[S] F`, the image of the `3`-adic Galois representation is a compact — hence closed —
subgroup of `GL₂(ℤ_[3])`:

```
isClosed_range_galoisRepMatrixThree :
  IsClosed ((galoisRepMatrixThree b).range : Set (GL (Fin 2) ℤ_[3])).
```

This is the **second** prime at which the image is available in this development, and the first odd
one.

## What this file contains, and what it does not

The argument is in `EllipticCurves.TateModule.PrimaryImage`, stated for an arbitrary prime `ℓ`.
**This file supplies its one input at `ℓ = 3` and contains no argument**: every proof below is one
line. The input is `nonempty_tateModuleEquivProd_three` (`EllipticCurves.TateModule.FreeThree`,
`#974`), and it is needed only by the two basis-free statements — the eight that are handed a basis
need nothing at all.

⚠️ **Two hypotheses, not one.** Where the `ℓ = 2` file `EllipticCurves.TateModule.Image` carries
only `h2`, the basis-free statements here carry both `h2` and `h3`, and the provenance is not
symmetric: `nsmul_three_surjective` needs **only** `(2 : F) ≠ 0`, so the coherent system's *lifting*
step is `h3`-free; `h3` enters exclusively through the counting theorem `card_torsion_three_pow`,
i.e. through `#E[3] = 9`. `EllipticCurves.TateModule.MatrixContinuityThree` documents that split
and this file inherits it unchanged rather than re-deriving it.

## ⚠️ Ten declarations, not sixteen

⚠️ `EllipticCurves.TateModule.Image` had **sixteen** declarations, and a `grep` that counts them
returns **seventeen** — because `:27` of that file is a fenced ```` ```lean ```` block in its module
docstring, quoting Mathlib's `instance [IsGalois k K] : CompactSpace Gal(K/k)`. ⚠️ **A fenced code
block looks exactly like a declaration, because it is one — somebody else's.** The board already
records that this grep counts docstring lines *beginning with the word* `theorem`; this is the same
trap wearing a code fence.

Of the sixteen, they split three ways:

* **ten** carried a `Two` suffix. These are what this file twins.
* **two** — `quotientKerContinuousMulEquivRange` and its `_apply_mk` — carried **unsuffixed** names,
  so an `ℓ = 3` twin would be a name collision rather than a duplication. They were generalised in
  place and now live at the same full names in `EllipticCurves.TateModule.PrimaryImage`. ⚠️ **This
  file restates neither, and there is deliberately no `quotientKerContinuousMulEquivRangeThree`**:
  `galoisRepMatrixThree b` is *definitionally* `galoisRepMatrix b`, so the generic statement
  applied to a basis of `T₃E` already **is** the `ℓ = 3` one.
* **four** — `PadicInt.range_intCast_ne_univ`, `PadicInt.not_isClosed_range_intCast`,
  `Matrix.GeneralLinearGroup.unipotentIntSubgroup` and
  `Matrix.GeneralLinearGroup.not_isClosed_unipotentIntSubgroup` — were `_root_`-level, unsuffixed,
  and stated at a **hardcoded** `ℤ_[2]`. They are now stated at an arbitrary prime `p`. ⚠️ **Cited
  here, in the `Non-vacuity` section, not duplicated.**

> ⚠️ **Unsuffixed rows are not automatically cheap.** In
> `EllipticCurves.TateModule.MatrixContinuity` the nine unsuffixed rows were already generic in all
> but their `variable` block. Here two of the
> six were, and four were stated at a hardcoded prime — one of them with a proof that used `3`
> being a unit of `ℤ_[2]`, which is false at `ℓ = 3`. *"May this be twinned?"* and *"what does
> generalising cost?"* are different questions and need different measurements.

## Naming, and why there are `Three` twins of generic statements here

⚠️ The rule `EllipticCurves.TateModule.MatrixRepThree` records applies verbatim: a twin of an
already-generic declaration is normally pure duplication, and the ten below are the same deliberate
exception. Their `ℓ = 2` twins `isClosed_range_galoisRepMatrixTwo`, `isClosed_range_galoisDetTwo`
and the rest predate the extraction and cannot be removed; leaving `ℓ = 3` without the matching
spellings would put the two primes on different footings for every downstream file that extends by
pattern. ⚠️ The six unsuffixed and `p`-generic declarations are the *other* side of that rule and
get no twin at all — see above.

## Non-degeneracy

⚠️ **`IsClosed` inside a compact ambient group looks free**, since inside `GL₂(ℤ_[3])` — which is
itself compact — *closed* and *compact* agree.
`Matrix.GeneralLinearGroup.not_isClosed_unipotentIntSubgroup 3` is the certificate that it is not:
`GL₂(ℤ_[3])` really does have a subgroup that is not closed, namely the integral points of the
unipotent line. ⚠️ **It is stated at an arbitrary prime `p`, so `ℓ = 3` is covered by citation**,
and the `Non-vacuity` section below cites it rather than restating it — even though generalising it
to `p` was work done in the very change that adds this file.

On the source side, every statement here about `G` remains true when `G` is trivial, and no theorem
about `G` alone can exclude that: it is a fact about `F / S`, not about the curve. The certificate
offered instead is `Infinite (T₃E)`, by a route that never mentions images or matrices.

## Scope

* ⚠️ **This file consumes the multiplication-by-`n` coordinate formula `x(nP) = Φₙ/ΨSqₙ`**, at
  `n = 3`, through `EllipticCurves.Torsion.TriplingSurjective` and hence through
  `EllipticCurves.TateModule.FreeThree`. `EllipticCurves.TateModule.Image` says of the `ℓ = 2`
  route that it needs no such thing; **that sentence must not be read as applying here.**
* ⚠️ **Openness of `im ρ_{E,3}` is NOT proved here and is not close.** That is Serre's theorem, it
  is **false** for curves with complex multiplication, and nothing about compactness approaches it.
  Compact and closed are the *hypotheses* an open-image theorem starts from, not a step towards it.
* **Surjectivity and injectivity of `ρ_{E,3}` stay out.** An isomorphism onto `G ⧸ ker ρ` says
  nothing about whether `ker ρ` is trivial.
* ⚠️ **`det ρ_{E,3} = χ_3` `3`-adically is NOT unblocked by this file**, and
  `isClosed_range_galoisDetThree` will look exactly like progress towards it. The `3`-adic identity
  needs the Weil pairing on `E[3^k]` for **every** `k`, i.e. the pairing at composite `n`; this
  development has the pairing at `n = 2` and `n = 3` only. The **mod-`3`** identity
  `galoisDetMod 3 = χ_3` is a *different statement about a different object* — valued in
  `(ZMod 3)ˣ`, not `ℤ_[3]ˣ` — and it landed separately as
  `EllipticCurves.FunctionField.WeilPairingDeterminantCharacter`. Knowing that the image of a
  character is closed says nothing about which character it is.
* **The profinite packaging is not here.** ⚠️ **The clause this bullet used to carry has been
  paid** — it read *"`EllipticCurves.TateModule.ImageProfinite` is still `ℓ = 2` only; its `ℓ = 3`
  layer is a separate follow-up over `EllipticCurves.TateModule.PrimaryImage`, and nothing gates it
  once this lands"*. It landed, and it went over
  `EllipticCurves.TateModule.PrimaryImageProfinite` — which sits over
  `EllipticCurves.TateModule.PrimaryImage` — as
  `EllipticCurves.TateModule.ImageProfiniteThree`. The packaging is still not in *this* file.
* **General odd `ℓ ≥ 5` stays out.** `EllipticCurves.TateModule.PrimaryImage` is already stated at
  an arbitrary prime, so the `ℓ = 5` file will again be a list of instantiations — but its input
  `Nonempty (T₅E ≃ₗ ℤ_[5]²)` is gated on `#E[5^k]`.  ⚠️ This bullet used to say it was gated *"on
  `[5]`-surjectivity and `#E[5^k]`, both of which need the general coordinate formula, i.e. the
  `ωₙ` crux"*, and all three clauses are wrong: `[5]`-surjectivity holds at every nonzero index
  (`nsmul_surjective_of_two_ne_zero`, `EllipticCurves.Torsion.TwoTorsionOrder`); the coordinate
  formula is proved at every index (`hasXCoordFormula_of_two_ne_zero`,
  `EllipticCurves.Torsion.NsmulOrder`); and it is **not** the `ωₙ` crux, which is `#404`'s on-curve
  identity, closed in `EllipticCurves.Torsion.OmegaCrux` (PR #557).
  ⚠️ **`#E[5^k]` is no longer open at `ℓ ≥ 5`.**  `card_torsion_pow_mul_self_of_odd`
  (`EllipticCurves.Torsion.PrimaryTowerOdd`) supplies it at every odd `ℓ` with `(ℓ : F) ≠ 0`, over
  `F̄` with `(2 : F) ≠ 0`, and discharges `EllipticCurves.Torsion.PrimaryTower`'s gate list — which
  this bullet used to cite as open — with it.  Instantiating this file at `ℓ ≥ 5` on top of that
  count is separate work and is not done here.  `ℓ ≥ 5` gains the generic file and nothing else.

## Using this file

`[IsGalois S F]` is carried throughout, as in the `ℓ = 2` file: it is what supplies compactness of
`G`, and compactness of `G` is what every statement below rests on. ⚠️ It is a hypothesis on the
extension and not on the curve, and it is **not** automatic — for `F` an algebraic closure of an
imperfect `S` the extension is normal but not separable.

## Main statements

* `WeierstrassCurve.Affine.isClosed_range_galoisRepMatrixThree` : the image of `ρ_{E,3}` is a
  closed subgroup of `GL₂(ℤ_[3])`.
* `WeierstrassCurve.Affine.isClosed_range_galoisDetThree` : the same for `det ρ_{E,3}`.

## References

* [J. H. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.7.
-/

open Matrix

open scoped WeierstrassCurve.Affine.ProfiniteTopology

namespace WeierstrassCurve.Affine

variable {S F : Type*} [Field S] [Field F] [DecidableEq F] [Algebra S F] {W' : Affine S}
variable [Algebra.IsIntegral S F] [IsGalois S F]
variable (b : Module.Basis (Fin 2) ℤ_[3] ((W'⁄F).tateModule 3))

/-! ### The image is compact and closed, at `ℓ = 3` -/

omit [Algebra.IsIntegral S F] [IsGalois S F] in
/-- The underlying set of the subgroup `(galoisRepMatrixThree b).range` is the set-theoretic range.
Definitionally `coe_range_galoisRepMatrix` at `ℓ = 3`. -/
theorem coe_range_galoisRepMatrixThree :
    ((galoisRepMatrixThree b).range : Set (GL (Fin 2) ℤ_[3]))
      = Set.range (galoisRepMatrixThree b) :=
  coe_range_galoisRepMatrix b

/-- **The image of `ρ_{E,3}` is compact.** `G = Gal(F/S)` is compact for the Krull topology and
`ρ_{E,3}` is continuous (`continuous_galoisRepMatrixThree`), so the image is a continuous image of
a compact space. -/
theorem isCompact_range_galoisRepMatrixThree :
    IsCompact ((galoisRepMatrixThree b).range : Set (GL (Fin 2) ℤ_[3])) :=
  isCompact_range_galoisRepMatrix b

/-- **The image of `ρ_{E,3}` is a closed subgroup of `GL₂(ℤ_[3])`.**

This is the classical statement at the first odd prime available here, and the standing hypothesis
of every theorem about the image of an `ℓ`-adic representation. ⚠️ It is not a formality:
`Matrix.GeneralLinearGroup.not_isClosed_unipotentIntSubgroup 3` exhibits a subgroup of
`GL₂(ℤ_[3])` that is not closed. ⚠️ It is also **not** a step towards Serre's open-image theorem,
which is false for curves with complex multiplication. -/
theorem isClosed_range_galoisRepMatrixThree :
    IsClosed ((galoisRepMatrixThree b).range : Set (GL (Fin 2) ℤ_[3])) :=
  isClosed_range_galoisRepMatrix b

/-- The image of `ρ_{E,3}`, as a topological group in its own right, is compact. -/
instance compactSpace_range_galoisRepMatrixThree :
    CompactSpace ((galoisRepMatrixThree b).range) :=
  compactSpace_range_galoisRepMatrix b

/-- `ρ_{E,3}` is a closed map: it carries closed subgroups of `G` to closed subgroups of
`GL₂(ℤ_[3])`, not merely to subgroups. -/
theorem isClosedMap_galoisRepMatrixThree : IsClosedMap (galoisRepMatrixThree b) :=
  isClosedMap_galoisRepMatrix b

omit [IsGalois S F] in
/-- `ρ_{E,3}` corestricted to its image is continuous. -/
theorem continuous_rangeRestrict_galoisRepMatrixThree :
    Continuous fun σ : F ≃ₐ[S] F =>
      (⟨galoisRepMatrixThree b σ, ⟨σ, rfl⟩⟩ : (galoisRepMatrixThree b).range) :=
  continuous_rangeRestrict_galoisRepMatrix b

/-! ### The determinant character

⚠️ There is deliberately no `quotientKerContinuousMulEquivRangeThree` between the two sections
above and below. `WeierstrassCurve.Affine.quotientKerContinuousMulEquivRange`
(`EllipticCurves.TateModule.PrimaryImage`) carries no `Two`, so it was generalised in place, and
`quotientKerContinuousMulEquivRange b` for a basis `b` of `T₃E` already *is* the `ℓ = 3` first
isomorphism theorem `G ⧸ ker ρ_{E,3} ≃ₜ* im ρ_{E,3}`. -/

/-- The image of `det ρ_{E,3} : G →* ℤ_[3]ˣ` is compact. A basis is taken because continuity of
`galoisDetThree` is proved through one, even though `galoisDetThree` itself is basis-free. -/
theorem isCompact_range_galoisDetThree_of_basis
    (b : Module.Basis (Fin 2) ℤ_[3] ((W'⁄F).tateModule 3)) :
    IsCompact (Set.range (galoisDetThree (W' := W') (F := F))) :=
  isCompact_range_galoisDet_of_basis b

/-- The image of `det ρ_{E,3}` is a closed subgroup of `ℤ_[3]ˣ`. -/
theorem isClosed_range_galoisDetThree_of_basis
    (b : Module.Basis (Fin 2) ℤ_[3] ((W'⁄F).tateModule 3)) :
    IsClosed (Set.range (galoisDetThree (W' := W') (F := F))) :=
  isClosed_range_galoisDet_of_basis b

section Nondegenerate

variable [IsAlgClosed F] [(W'⁄F).IsElliptic]

/-- The image of `det ρ_{E,3}` is compact, with no basis supplied: over an algebraically closed
field in which `2` and `3` are invertible a basis of `T₃E` exists
(`nonempty_tateModuleEquivProd_three`), and compactness is a `Prop`, so the choice can be
discharged. -/
theorem isCompact_range_galoisDetThree (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) :
    IsCompact (Set.range (galoisDetThree (W' := W') (F := F))) :=
  isCompact_range_galoisDet_of_nonempty (tateModule.nonempty_tateModuleEquivProd_three h2 h3)

/-- **The image of the determinant character `det ρ_{E,3}` is a closed subgroup of `ℤ_[3]ˣ`.**

⚠️ **This is not progress towards `det ρ_{E,3} = χ_3`.** That identification needs the Weil pairing
on `E[3^k]` for every `k`; knowing that the image of a character is closed says nothing about which
character it is.

⚠️ **Deletion test**, measured on this file as committed. Replacing the argument
`(tateModule.nonempty_tateModuleEquivProd_three h2 h3)` in `isCompact_range_galoisDetThree` above
by a hole — `by refine isCompact_range_galoisDet_of_nonempty (W' := W') (F := F) (ℓ := 3) ?_` —
leaves, copy-paste:

```
error: unsolved goals
S : Type u_1
F : Type u_2
inst✝⁷ : Field S
inst✝⁶ : Field F
inst✝⁵ : DecidableEq F
inst✝⁴ : Algebra S F
W' : Affine S
inst✝³ : Algebra.IsIntegral S F
inst✝² : IsGalois S F
inst✝¹ : IsAlgClosed F
inst✝ : WeierstrassCurve.IsElliptic W'⁄F
h2 : 2 ≠ 0
h3 : 3 ≠ 0
⊢ Nonempty (↥((W'⁄F).tateModule 3) ≃ₗ[ℤ_[3]] ℤ_[3] × ℤ_[3])
```

⚠️ `h2` and `h3` both **survive** in the context, so what the deletion removes is a construction
and not a hypothesis, and the residual is a **goal**, which no type mismatch could produce. It is
`#974`'s theorem — the rank-two input, and the only *mathematical* input at `ℓ = 3` that costs
anything. ⚠️ **There is no knock-on, and the reason is worth stating**: this declaration consumes
`isCompact_range_galoisDetThree`, but the deletion above removes only its *proof term*, not its
*hypotheses*, so its statement is unchanged and nothing downstream notices. ⚠️ The deletion test in
`EllipticCurves.TateModule.PrimaryImage` is the opposite case — there `h` is removed from the
statement, and the knock-on it produces is disclosed there. *Whether a deletion test has a knock-on
is decided by whether it touches the signature, not by what consumes the declaration.* -/
theorem isClosed_range_galoisDetThree (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) :
    IsClosed (Set.range (galoisDetThree (W' := W') (F := F))) :=
  (isCompact_range_galoisDetThree h2 h3).isClosed

end Nondegenerate

/-! ### Non-vacuity

⚠️ Three risks, three certificates, following the idiom
`EllipticCurves.TateModule.MatrixRepThree` introduced and
`EllipticCurves.TateModule.MatrixContinuityThree` extended.

1. **The statement is not trivially satisfiable.** ⚠️ `IsClosed` inside the **compact** group
   `GL₂(ℤ_[3])` looks free, because inside a compact space closed and compact agree.
   `Matrix.GeneralLinearGroup.not_isClosed_unipotentIntSubgroup` is stated at an arbitrary prime
   `p` in `EllipticCurves.TateModule.PrimaryImage`, so `ℓ = 3` is covered **by citation** and the
   first certificate below is that citation. ⚠️ It is tempting to restate it at `3` precisely
   because generalising it to `p` was work done in this same change; **do not.**
2. **The hypothesis class is inhabited.** `[IsAlgClosed F]`, `[(W'⁄F).IsElliptic]`,
   `[Algebra.IsIntegral S F]`, **`[IsGalois S F]`**, `(2 : F) ≠ 0` and `(3 : F) ≠ 0` all hold
   simultaneously for `y² + y = x³` over `ℚ` base-changed to `AlgebraicClosure ℚ`, with **`S = ℚ`**
   so that `Gal(F/S)` is not the trivial group. The second certificate closes **by application** of
   `isClosed_range_galoisRepMatrixThree`, not by `rfl`, `decide` or `norm_num`, so it consumes the
   theorem it certifies (`#944`).
3. **The target is not degenerate.** Every statement here is true over a zero Tate module, where
   the representation is trivial and its image is `{1}` — compact and closed for free. The third
   certificate says `T₃E` is infinite, by a route that never mentions images or matrices.

⚠️ **Two instances have to be supplied by hand and neither is found by search.** Both are
`ℚ`-algebra instance traps of the shape `EllipticCurves.TateModule.Continuity` documents:
`DivisionRing.toRatAlgebra` outranks `AlgebraicClosure.instAlgebra ℚ` once `ℤ_[ℓ]` has pulled in
the analysis imports, and the facts one wants are registered against the latter.

* `Algebra.IsIntegral ℚ AlgClosedQ` — first hit by
  `EllipticCurves.TateModule.MatrixContinuityThree`, and inherited here.
* ⚠️ **`IsGalois ℚ AlgClosedQ` — new here, and no earlier certificate block on this front warns
  about it**, because this is the first statement on the front to carry `[IsGalois S F]` at all.
  The failure is `failed to synthesize instance of type class IsGalois ℚ AlgClosedQ`, reported at
  the `example`, several lines from the `AlgClosedQ` fixture that causes it.

Both are supplied as `private lemma`s introduced with `haveI` at the point of use rather than as
`private instance`s, so that no importing file silently acquires a `ℚ`-specific instance this file
needed for two `example`s. ⚠️ `private` in Lean 4 restricts *name resolution*, not instance search.

⚠️ **`open Classical in` is load-bearing on the last two certificates and is not optional.** The
`TateModule` family carries `[DecidableEq F]` in its `variable` blocks, but `AlgClosedQ` is
`AlgebraicClosure ℚ`, which has no decidable equality.

⚠️ Every `TateModule` certificate block now names the one shared fixture
`EllipticCurves.Fixture.y2AddYEqX3`; the `private` per-file copies this note used to describe are
gone.
-/

section Nonvacuity

/-- **⚠️ THE CERTIFICATE THAT THE STATEMENT IS NOT FREE**: `GL₂(ℤ_[3])` has a subgroup that is not
closed, so `isClosed_range_galoisRepMatrixThree` is a constraint on `im ρ_{E,3}` rather than an
artefact of the ambient group being compact.

⚠️ This is a **citation**, not a restatement: the theorem is stated at an arbitrary prime `p` in
`EllipticCurves.TateModule.PrimaryImage` and needs no `ℓ = 3` twin. -/
example : ¬ IsClosed
    (Matrix.GeneralLinearGroup.unipotentIntSubgroup 3 : Set (GL (Fin 2) ℤ_[3])) :=
  Matrix.GeneralLinearGroup.not_isClosed_unipotentIntSubgroup 3

/-! The certificate curve `y² + y = x³` over `ℚ` and its base — algebraically closed so that
`Gal(F/ℚ)` is not the trivial group, and of characteristic `0` so that `2 ≠ 0` and `3 ≠ 0` — are the
shared `EllipticCurves.Fixture.y2AddYEqX3` and `EllipticCurves.Fixture.AlgClosedQ`, which also
supply `(y2AddYEqX3 ℚ).IsElliptic` from a single `[CharZero F]` instance. The **base-changed**
`((y2AddYEqX3 ℚ)⁄AlgClosedQ).IsElliptic` comes from the same module, via
`EllipticCurves.Fixture.instIsEllipticBaseChange`; this block declares no fixture of its own
(`#1408`). -/

open EllipticCurves.Fixture

/-- The `ℚ`-algebra instance trap, as `EllipticCurves.TateModule.MatrixContinuityThree` documents
it. Introduced with `haveI` at the point of use, not registered as an instance. -/
private lemma exampleIsIntegral : Algebra.IsIntegral ℚ AlgClosedQ := by
  have : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) := by
    rw [show (DivisionRing.toRatAlgebra : Algebra ℚ (AlgebraicClosure ℚ))
        = AlgebraicClosure.instAlgebra ℚ from Subsingleton.elim _ _]
    infer_instance
  infer_instance

/-- ⚠️ **The same trap, one class further on, and this one is new to this front.**
`IsGalois ℚ (AlgebraicClosure ℚ)` is not found by bare instance search here either, for exactly the
reason `exampleIsIntegral` is not: `AlgebraicClosure`'s `Normal` and `IsSeparable` instances are
registered against `AlgebraicClosure.instAlgebra ℚ`, which `DivisionRing.toRatAlgebra` outranks.

⚠️ **No earlier `#916` certificate block on this front had to supply it**, because
`EllipticCurves.TateModule.Image` is the first file on the front whose theorems carry
`[IsGalois S F]` — so a reader copying `MatrixContinuityThree.lean`'s block verbatim gets a failure
its docstring does not mention. -/
private lemma exampleIsGalois : IsGalois ℚ AlgClosedQ := by
  rw [show (DivisionRing.toRatAlgebra : Algebra ℚ (AlgebraicClosure ℚ))
      = AlgebraicClosure.instAlgebra ℚ from Subsingleton.elim _ _]
  infer_instance

private lemma exampleTwo : (2 : AlgClosedQ) ≠ 0 := two_ne_zero

private lemma exampleThree : (3 : AlgClosedQ) ≠ 0 := three_ne_zero_of_charZero _

open Classical in
/-- **⚠️ THE LOAD-BEARING CERTIFICATE**: on a curve that exists, over a base field `S = ℚ` whose
absolute Galois group is not trivial, the image of `ρ_{E,3}` really is a closed subgroup of
`GL₂(ℤ_[3])`.

⚠️ The statement is restated in full rather than obtained-and-projected (`#916`), and it closes by
**application** of `isClosed_range_galoisRepMatrixThree` rather than by `rfl`, `decide` or
`norm_num`, so it consumes the theorem it certifies. -/
example (b : Module.Basis (Fin 2) ℤ_[3] (((y2AddYEqX3 ℚ)⁄AlgClosedQ).tateModule 3)) :
    IsClosed ((galoisRepMatrixThree b).range : Set (GL (Fin 2) ℤ_[3])) := by
  haveI := exampleIsIntegral
  haveI := exampleIsGalois
  exact isClosed_range_galoisRepMatrixThree b

open Classical in
/-- **The module the representation acts on is not the zero module**, on the same curve, by a route
that never mentions the image or the matrices: `T₃E` surjects onto `E[3^k]`, which has `9^k`
elements. Without this, the image would be `{1}` and closed for free. -/
example : Infinite (((y2AddYEqX3 ℚ)⁄AlgClosedQ).tateModule 3) :=
  tateModule.infinite_tateModule_three exampleTwo exampleThree

end Nonvacuity

end WeierstrassCurve.Affine
