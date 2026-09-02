/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import EllipticCurves.Fixtures
import EllipticCurves.TateModule.MatrixRepThree
import EllipticCurves.TateModule.OpenKernel
import EllipticCurves.TateModule.PrimaryMatrixRepBasisChange

/-!
# Changing the basis conjugates `ρ_{E,3}`

`galoisRepMatrixThree b : G →* GL₂(ℤ_[3])` of `EllipticCurves.TateModule.MatrixRepThree` depends on
a choice of basis `b` of `T₃E`. This file records that the dependence is exactly a conjugation:

```
galoisRepMatrixThree b' σ = c * galoisRepMatrixThree b σ * c⁻¹,   c = basisChangeGL b b'
```

and adds the topological corollary `isClosed_ker_galoisRepMatrixThree`. This is the **second**
prime at which the conjugation law is available in this development, and the first odd one.

## What this file contains, and what it does not

The argument is in `EllipticCurves.TateModule.PrimaryMatrixRepBasisChange`, stated for an arbitrary
prime. ⚠️ **That file takes no hypothesis at all** — the conjugation law is about two bases that
are given — so, unlike `EllipticCurves.TateModule.MatrixRepThree`,
`EllipticCurves.TateModule.FreeThree` and `EllipticCurves.TateModule.DeterminantThree`, the five
instantiations below carry **no `h2` and no `h3`**. A reader who has seen those three files will
expect them; they are genuinely absent.

⚠️ Measured rather than assumed, in both directions. The `unusedSectionVars` linter is silent on
every declaration below, so no section variable is carried idly; and `omit [DecidableEq F] in` on
`galoisRepMatrixThree_conj` gives `cannot omit referenced section variable`, so the one instance
that could plausibly have been idle is not. (⚠️ `omit … in` must be written *above* the
`open tateModule in`; between the docstring and the `theorem` it is a parse error, and the cascade
that follows includes a spurious `declaration uses sorry` several lines away.)

⚠️ `isClosed_ker_galoisRepMatrixThree` is the exception and it carries both. It is the only
statement here with a real input, and its two inputs enter through different doors:

* `ker_galoisRepMatrix` (`EllipticCurves.TateModule.Kernel`) is unconditional and is stated at an
  arbitrary prime, so it applies to `galoisRepMatrixThree` — which is *definitionally*
  `galoisRepMatrix` at `ℓ = 3` — with no restatement. ⚠️ **The clause this bullet used to carry has
  gone false and its policy was reversed deliberately.** It read *"There is deliberately no
  `ker_galoisRepMatrixThree`; the proof below exhibits the generic lemma being used at `ℓ = 3`
  directly, which is the whole reason `EllipticCurves.TateModule.MatrixRepThree` declines to make
  `Three` twins of already-generic theorems."* `WeierstrassCurve.Affine.ker_galoisRepMatrixThree`
  now exists, in `EllipticCurves.TateModule.Kernel` beside its `ℓ = 2` twin. ⚠️ **The reason is the
  proof below**: `isClosed_ker_galoisRepMatrixTwo` closes with `rw [ker_galoisRepMatrixTwo b]`,
  while this file has to open with a `have hker := ker_galoisRepMatrix b` first, because `rw` cannot
  see through the definitional equality that makes the generic lemma apply. *Definitional
  applicability is not the same as being usable by `rw`, so declining the named twin does not save
  work — it moves the work to every consumer at the un-named prime.* The `ℓ = 2` named theorems
  predate the question and cannot be removed, so this is the same exception
  `EllipticCurves.TateModule.MatrixRepThree` already makes for generic *definitions*, applied to
  theorems for the same stated reason.
* ⚠️ **The proof below is nonetheless left using the generic lemma**, not rewritten to
  `rw [ker_galoisRepMatrixThree b]`, so that this file still exhibits the generic route being used
  at `ℓ = 3` directly — and because rewriting it would invalidate the pasted deletion-test residual
  below, in which `hker` appears. Either form works now; that is the point.
* `isClosed_ker_galoisRepThree` (`EllipticCurves.TateModule.OpenKernel`) needs `h2` for the level
  filtration, through `nsmul_three_surjective`, and `h3` for the openness of each level kernel,
  through `finite_torsion_three_pow`. Its `ℓ = 2` twin needs only `h2` because at `ℓ = 2` both
  doors open with it.

## Scope

* ⚠️ **The non-vacuity certificate for the conjugation law is not restated here.**
  `tateModule.basisChangeGL_reindex_swap_ne_one` is stated over an arbitrary `Nontrivial`
  commutative ring and an arbitrary `Fin 2`-indexed basis, so it already covers `ℓ = 3`; the
  `Nonvacuity` section below *uses* it on a named curve rather than proving a `_three` copy.
* ⚠️ **This file consumes the multiplication-by-`n` coordinate formula `x(nP) = Φₙ/ΨSqₙ`**, at
  `n = 3`, through `EllipticCurves.TateModule.MatrixRepThree` and hence
  `EllipticCurves.Torsion.TriplingSurjective`. `EllipticCurves.TateModule.MatrixRepBasisChange`
  says of the `ℓ = 2` route that it needs no such thing; that sentence must not be read here.
  Ward's theorem and the elliptic-net recurrence remain unused at every `ℓ`.
* ⚠️ **Continuity is not asserted**, at either prime — but it is no longer *missing* at either.
  The clause this bullet used to carry — *"`continuous_galoisRepMatrixTwo`
  (`EllipticCurves.TateModule.MatrixContinuity`) is `ℓ = 2` only; its `ℓ = 3` twin is a separate
  follow-up"* — was a correct prediction and has been paid:
  `continuous_galoisRepMatrixThree` is in `EllipticCurves.TateModule.MatrixContinuityThree`, over
  the `ℓ`-generic `EllipticCurves.TateModule.PrimaryMatrixContinuity`. ⚠️ Neither of those files
  consumes this one, and none of the five statements below asserts continuity of anything.
* ⚠️ **`det ρ_{E,3} = χ_3` `3`-adically is not touched by any of this.** The conjugation law says
  the determinant does not depend on the basis, which is already known directly
  (`EllipticCurves.TateModule.Determinant`); the `3`-adic identity with the cyclotomic character
  needs the Weil pairing on `E[3^k]` for every `k`, i.e. the pairing at composite `n`. The
  **mod-`3`** identity is a different statement and landed separately as
  `EllipticCurves.FunctionField.WeilPairingDeterminantCharacter`.
* **`ℓ ≥ 5` stays out.** `EllipticCurves.TateModule.PrimaryMatrixRepBasisChange` is already stated
  at an arbitrary prime, so the `ℓ = 5` file will again be a list of instantiations — but it needs
  a basis of `T₅E`, which is gated on `#E[5^k]`.  ⚠️ This bullet used to say it was gated *"on
  `[5]`-surjectivity and `#E[5^k]`, both of which need the general coordinate formula, i.e. the
  `ωₙ` crux"*, and all three clauses are wrong: `[5]`-surjectivity holds at every nonzero index
  (`nsmul_surjective_of_two_ne_zero`, `EllipticCurves.Torsion.TwoTorsionOrder`); the coordinate
  formula is proved at every index (`hasXCoordFormula_of_two_ne_zero`,
  `EllipticCurves.Torsion.NsmulOrder`); and it is **not** the `ωₙ` crux, which is `#404`'s
  on-curve identity, closed in `EllipticCurves.Torsion.OmegaCrux` (PR #557).  `#E[5^k]` is
  genuinely open; its gate list is `EllipticCurves.Torsion.PrimaryTower`'s.

## Main statements

* `WeierstrassCurve.Affine.galoisRepMatrixThree_conj` : `ρ_{b'}(σ) = c ρ_b(σ) c⁻¹`.
* `WeierstrassCurve.Affine.galoisRepMatrixThree_eq_conj_comp` : the same as an equality of monoid
  homomorphisms `G →* GL₂(ℤ_[3])`.
* `WeierstrassCurve.Affine.range_galoisRepMatrixThree_map` : the image of `ρ_{E,3}` is well defined
  up to conjugacy in `GL₂(ℤ_[3])`.
* `WeierstrassCurve.Affine.isClosed_ker_galoisRepMatrixThree` : `ker ρ_{E,3}` is closed in `G`, in
  every basis.

## References

* [J. H. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.7.
-/

open Matrix

namespace WeierstrassCurve.Affine

/-! ### The conjugation law for `ρ_{E,3}` -/

variable {S F : Type*} [Field S] [Field F] [DecidableEq F] [Algebra S F] {W' : Affine S}

variable (b b' : Module.Basis (Fin 2) ℤ_[3] ((W'⁄F).tateModule 3))

open tateModule in
/-- **The matrix form of the conjugation law**: `ρ_{b'}(σ)` and `ρ_b(σ)` intertwine the change of
basis. `coe_galoisRepMatrix_mul_basisChange` at `ℓ = 3`. -/
theorem coe_galoisRepMatrixThree_mul_basisChange (σ : F ≃ₐ[S] F) :
    (galoisRepMatrixThree b' σ : Matrix (Fin 2) (Fin 2) ℤ_[3]) * b'.toMatrix b
      = b'.toMatrix b * (galoisRepMatrixThree b σ : Matrix (Fin 2) (Fin 2) ℤ_[3]) :=
  coe_galoisRepMatrix_mul_basisChange b b' σ

open tateModule in
/-- **`ρ_{b'}(σ) · c = c · ρ_b(σ)`** in `GL₂(ℤ_[3])`, where `c = basisChangeGL b b'`. -/
theorem galoisRepMatrixThree_mul_basisChangeGL (σ : F ≃ₐ[S] F) :
    galoisRepMatrixThree b' σ * basisChangeGL b b'
      = basisChangeGL b b' * galoisRepMatrixThree b σ :=
  galoisRepMatrix_mul_basisChangeGL b b' σ

open tateModule in
/-- **Changing the basis conjugates the `3`-adic representation.**

`ρ_{E,3}` depends on a choice of basis of `T₃E`, and this is exactly how. It is the theorem behind
the classical phrase *"the `3`-adic representation attached to `E`, well defined up to
conjugation"*, and it is what makes every conjugation-invariant of `ρ_{E,3}` — its kernel, its
determinant and trace, its image up to conjugacy — independent of the choice. -/
theorem galoisRepMatrixThree_conj (σ : F ≃ₐ[S] F) :
    galoisRepMatrixThree b' σ
      = basisChangeGL b b' * galoisRepMatrixThree b σ * (basisChangeGL b b')⁻¹ :=
  galoisRepMatrix_conj b b' σ

open tateModule in
/-- **The conjugation law as an identity of representations**, not merely of their values: the two
monoid homomorphisms `G →* GL₂(ℤ_[3])` differ by an inner automorphism of `GL₂(ℤ_[3])`. -/
theorem galoisRepMatrixThree_eq_conj_comp :
    galoisRepMatrixThree b' =
      (MulAut.conj (basisChangeGL b b')).toMonoidHom.comp (galoisRepMatrixThree b) :=
  galoisRepMatrix_eq_conj_comp b b'

open tateModule in
/-- **The image of `ρ_{E,3}` is well defined up to conjugacy in `GL₂(ℤ_[3])`.** Not merely
isomorphic: it is carried onto the other by an inner automorphism of the ambient group. -/
theorem range_galoisRepMatrixThree_map :
    (galoisRepMatrixThree b').range =
      (galoisRepMatrixThree b).range.map (MulAut.conj (basisChangeGL b b')).toMonoidHom :=
  range_galoisRepMatrix_map b b'

/-- **`ker ρ_{E,3}` is closed in `G`, in every basis.**

`ker_galoisRepMatrix` of `EllipticCurves.TateModule.Kernel` identifies the kernel with
`ker (galoisRep 3)`, which `isClosed_ker_galoisRepThree` of
`EllipticCurves.TateModule.OpenKernel` shows is closed; this is the two together, in the shape a
consumer of the matrix representation wants. Note it is *closed* and not, in general, open.

⚠️ The `have` in the proof is where `galoisRepMatrixThree` being **definitionally**
`galoisRepMatrix` at `ℓ = 3` is used: `ker_galoisRepMatrix b` proves a statement about
`galoisRepMatrix b`, and it is accepted for `galoisRepMatrixThree b` with no coercion and no
restatement. `rw` cannot see through the definition, which is the only reason the `have` is
written out rather than applied inline.

⚠️ **Deletion test**, measured on this file as committed. Deleting `h3` from the statement and
replacing its use in the last line by a hole — `refine isClosed_ker_galoisRepThree h2 ?_` — leaves

```
error: unsolved goals
S : Type u_1
F : Type u_2
inst✝⁶ : Field S
inst✝⁵ : Field F
inst✝⁴ : DecidableEq F
inst✝³ : Algebra S F
W' : Affine S
b : Module.Basis (Fin 2) ℤ_[3] ↥((W'⁄F).tateModule 3)
inst✝² : Algebra.IsIntegral S F
inst✝¹ : IsAlgClosed F
inst✝ : WeierstrassCurve.IsElliptic W'⁄F
h2 : 2 ≠ 0
hker : (galoisRepMatrixThree b).ker = (galoisRep 3).ker
⊢ 3 ≠ 0
```

⚠️ `h2` and `hker` both **survive**, so what the test removes is a hypothesis and not a
construction, and the residual is a **goal** which no type mismatch could produce. It is exactly
`(3 : F) ≠ 0`, i.e. the input to `finite_torsion_three_pow` and hence to the *openness* of each
level kernel — the half of `isClosed_ker_galoisRepThree` that `h2` does not supply. One mechanical
change accompanies the deletion and adds no information: `exact` becomes `refine … ?_` so that a
hole is legal. -/
theorem isClosed_ker_galoisRepMatrixThree [Algebra.IsIntegral S F] [IsAlgClosed F]
    [(W'⁄F).IsElliptic] (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) :
    IsClosed ((galoisRepMatrixThree b).ker : Set (F ≃ₐ[S] F)) := by
  have hker : (galoisRepMatrixThree b).ker = (galoisRep (W' := W') (F := F) 3).ker :=
    ker_galoisRepMatrix b
  rw [hker]
  exact isClosed_ker_galoisRepThree h2 h3

/-! ### Non-vacuity

⚠️ The five conjugation statements above take no hypothesis, so there is **nothing to run a
deletion test against**; saying so is the honest report, and inventing one would measure nothing.
What they do need is a certificate that their hypothesis *class* — a curve with two bases of `T₃E`
— is inhabited, and that the law is not `b' = b` in disguise.

The single `example` below does both at once on a named curve, which is stronger than either half
separately: it exhibits a pair of bases of `T₃E` whose change-of-basis element is **not `1`** and
for which the conjugation law holds. The second `example` rules out the degenerate reading in
which `T₃E` is the zero module, where every matrix is `1` and every conjugation identity is
vacuously true.

`[IsAlgClosed F]`, `[(W'⁄F).IsElliptic]`, `(2 : F) ≠ 0` and `(3 : F) ≠ 0` all hold for `y² + y = x³`
over `ℚ` base-changed to an algebraic closure of `ℚ`, with **`S = ℚ`** so that `Gal(F/S)` is not
the trivial group — this front's standard `n = 3` certificate curve.
-/

section Nonvacuity

/-! The certificate curve `y² + y = x³` over `ℚ` and its base — algebraically closed so that
`Gal(F/ℚ)` is not the trivial group, and of characteristic `0` so that `2 ≠ 0` and `3 ≠ 0` — are the
shared `EllipticCurves.Fixture.y2AddYEqX3` and `EllipticCurves.Fixture.AlgClosedQ`, which also
supply `(y2AddYEqX3 ℚ).IsElliptic` from a single `[CharZero F]` instance. The **base-changed**
`((y2AddYEqX3 ℚ)⁄AlgClosedQ).IsElliptic` comes from the same module, via
`EllipticCurves.Fixture.instIsEllipticBaseChange`; this block declares no fixture of its own
(`#1408`). -/

open EllipticCurves.Fixture

private lemma exampleTwo : (2 : AlgClosedQ) ≠ 0 := two_ne_zero

private lemma exampleThree : (3 : AlgClosedQ) ≠ 0 := three_ne_zero_of_charZero _

open Classical tateModule in
/-- **⚠️ THE LOAD-BEARING CERTIFICATE**: on a curve that exists, over a base field `S = ℚ` whose
absolute Galois group is not trivial, there really are two bases of `T₃E` that differ — their
change-of-basis element is not `1` — and `ρ_{E,3}` in the one is the conjugate of `ρ_{E,3}` in the
other.

⚠️ The statement is restated in full rather than obtained-and-projected (`#916`), and the clause
`basisChangeGL b b' ≠ 1` is what stops it from being witnessed by `b' = b`, in which case the
conjugation law would say nothing. The witnesses are `b` and its reindexing along the transposition
of the two indices, which is exactly what `basisChangeGL_reindex_swap_ne_one` discriminates. -/
example : ∃ b b' : Module.Basis (Fin 2) ℤ_[3] (((y2AddYEqX3 ℚ)⁄AlgClosedQ).tateModule 3),
    basisChangeGL b b' ≠ 1 ∧ ∀ σ : AlgClosedQ ≃ₐ[ℚ] AlgClosedQ,
      galoisRepMatrixThree b' σ
        = basisChangeGL b b' * galoisRepMatrixThree b σ * (basisChangeGL b b')⁻¹ := by
  obtain ⟨b⟩ := nonempty_basis_tateModule_three (W := (y2AddYEqX3 ℚ)⁄AlgClosedQ)
    exampleTwo exampleThree
  exact ⟨b, b.reindex (Equiv.swap 0 1), basisChangeGL_reindex_swap_ne_one b,
    galoisRepMatrixThree_conj b _⟩

open Classical in
/-- **The module the matrices act on is not the zero module**, on the same curve, by a route that
never mentions the matrix representation: `T₃E` surjects onto `E[3^k]`, which has `9^k` elements.

⚠️ This is what rules out the degenerate reading of the certificate above. `GL (Fin 2) ℤ_[3]` and a
conjugation identity are both perfectly satisfiable over a zero module, where every matrix is `1`
and `basisChangeGL b b' ≠ 1` would be the only surviving content. -/
example : Infinite (((y2AddYEqX3 ℚ)⁄AlgClosedQ).tateModule 3) :=
  tateModule.infinite_tateModule_three exampleTwo exampleThree

end Nonvacuity

end WeierstrassCurve.Affine
