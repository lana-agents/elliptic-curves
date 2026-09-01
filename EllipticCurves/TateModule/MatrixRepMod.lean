/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import EllipticCurves.Fixtures
import EllipticCurves.TateModule.DeterminantModSmooth
import EllipticCurves.TateModule.GeneralLinearGroup
import EllipticCurves.TateModule.PrimaryMatrixRepBasisChange

/-!
# `ρ_{E,n} : G →* GL₂(ℤ/n)` : the mod-`n` representation in matrix form

`EllipticCurves.TateModule.DeterminantMod` turns the mod-`n` Galois action into a `ZMod n`-linear
representation

```
galoisRepModLinear n : G →* (E[n] ≃ₗ[ZMod n] E[n]) ,
```

with no hypothesis beyond `[NeZero n]`, and builds the basis-free determinant character
`galoisDetMod n : G →* (ZMod n)ˣ` on top of it.  `EllipticCurves.TateModule.DeterminantModSmooth`
(`#1240`) then supplies what makes those objects mean anything — `E[n]` is a finite free
`ZMod n`-module of rank `2` at every `3`-smooth `n > 1`, with a basis `basisTorsionOfSmooth`
indexed by `Fin 2`.  This file reads the representation through such a basis:

```
galoisRepModMatrix b : G →* GL (Fin 2) (ZMod n) .
```

It is the finite-level analogue of `EllipticCurves.TateModule.MatrixRep` (`ρ_{E,ℓ} : G →* GL₂(ℤ_ℓ)`)
together with `EllipticCurves.TateModule.MatrixRepBasisChange` (the conjugation law), and the two
halves are here in one file for the reason the `ℓ`-adic side does not need: the conjugation law is
what makes a basis-dependent object usable, and `basisTorsionOfSmooth`'s own docstring warns that
*"any statement proved with it must be one whose truth does not depend on which basis is chosen"*.
Shipping the matrix without the conjugacy would be shipping exactly the noise that warns against.

## The three statements, and which one pays for the file

* `galoisRepModMatrix_mulVec` / `galoisRepModMatrix_apply_coe` — the computation rules.  A
  `GL`-valued definition with no computation rule is worth little; these say the matrix acts on
  `b`-coordinates the way `σ` acts on `E[n]`, and that column `j` is the coordinate vector of
  `σ • b j`.
* `galoisRepModMatrix_conj` — two bases give conjugate representations, so every
  conjugation-invariant of `ρ_{E,n}` is independent of the choice.  ⚠️ Non-vacuous: the conjugating
  element is not always `1`, by `basisChangeGL_reindex_swap_ne_one`, which is stated over an
  arbitrary `Nontrivial` commutative ring in `EllipticCurves.TateModule.PrimaryMatrixRepBasisChange`
  and is therefore reused here rather than restated.
* `det_galoisRepModMatrix` — **the statement that makes the file pay for itself.**
  `det (ρ_{E,n}(σ)) = galoisDetMod n σ` in `(ZMod n)ˣ`.  The left side is computed from a basis, the
  right side is `LinearEquiv.det` and is defined without one; a consumer holding a matrix wants to
  know they agree.  It also re-proves the basis-independence of the determinant for free, since the
  right-hand side does not mention `b` — which is why no separate `det`-invariance lemma is stated
  below.

## What is reused rather than re-derived

* **`Module.Basis.linearEquivMulEquivGL`** (`EllipticCurves.TateModule.GeneralLinearGroup`) is the
  `Aut_R(M) → GL n R` chain, and it is what `galoisRepModMatrix` is defined through.  ⚠️ It already
  lands in the *units* — `Units.mapEquiv` of `LinearMap.toMatrixAlgEquiv` — so nothing here ever
  inverts a matrix, which is the hazard `EllipticCurves.TateModule.MatrixRep` records on the
  `ℓ`-adic side.  It is stated over an arbitrary commutative ring, so `ZMod n` at composite `n`
  costs nothing: **no step below needs `ZMod n` to be a field.**
* **`WeierstrassCurve.Affine.tateModule.basisChangeGL`**
  (`EllipticCurves.TateModule.PrimaryMatrixRepBasisChange`) is `Module.Basis.toMatrix` packaged as a
  unit, and its own section docstring says *"this section is about an arbitrary finite-rank free
  module; nothing about elliptic curves enters"*.  It and all five of its computation rules are
  consumed unchanged.

⚠️ **What is duplicated, and named as such rather than hidden**: the four-line proof of
`coe_galoisRepModMatrix_mul_basisChange` is the proof of `coe_galoisRepMatrix_mul_basisChange`
(`EllipticCurves.TateModule.PrimaryMatrixRepBasisChange`) with `galoisRepMatrix` replaced by
`galoisRepModMatrix`.  Both are instances of one statement about an arbitrary group acting
`R`-linearly on a free module, and neither file states it.  Extracting it would touch a merged file
and change no theorem, so it is left as a `#699`-style de-duplication rather than folded in here.

## The basis is a parameter, and that is deliberate

`galoisRepModMatrix` takes the basis as an **explicit argument**; `basisTorsionOfSmooth` is not
baked into it.  That definition is `noncomputable` and depends on four arguments, and a definition
carrying it would force every consumer to produce syntactically the same four.  The choice-free
statements are `exists_galoisRepModMatrix_of_smooth` and its `n = 2` and `n = 3` instances, which
package a basis, a representation, the computation rule *and* the determinant identity together —
`Nonempty (G →* GL (Fin 2) (ZMod n))` alone would be witnessed by the trivial homomorphism and would
not mention the curve.

## Scope

⚠️ **This is not `det ρ_{E,n} = χ_n`.**  `det_galoisRepModMatrix` identifies two determinants of the
*same* representation.  The cyclotomic character is the Weil pairing, and the identification
`galoisDetMod 3 = χ_3` lives in `EllipticCurves.FunctionField.WeilPairingDeterminantCharacter`
(`#958`), one directory away and downstream of this one.

⚠️ **The clause that used to end that paragraph — *"composing the two is a statement for a
`FunctionField/` file, not for this one"* — has been acted on and is RETIRED.**  The composition is
`det_galoisRepModMatrix_three_eq_galoisModularCyclotomicChar` in
`EllipticCurves.FunctionField.MatrixRepDeterminantCharacter` (`#1260`), which imports this file and
`WeilPairingDeterminantCharacter` and is a leaf: **nothing here or elsewhere under `TateModule/`
imports it**, and the sentence above about where the identification lives is unchanged and still
right.  What that file adds beyond the composition is the consequence neither half can state —
given a `σ` with `χ_3(σ) ≠ 1`, the image of `ρ_{E,3}` is not contained in `SL₂(ℤ/3)`, which needs a
matrix and a `Matrix.SpecialLinearGroup` and therefore cannot live under `TateModule/` either.

**`#951` is not subsumed, and the reason is structural.**
`EllipticCurves.FunctionField.WeilPairingDeterminant` proves `a * d − b * c ≡ χ_n(σ)` with the four
entries carried as **integers in hypotheses**, relative to a pair `P, T` with `e_n(P, T) ≠ 1`; its
own docstring is explicit that it uses no `Module (ZMod n)` structure and no `LinearMap.det`, and
its inputs are a counting argument (`exists_zsmul_add_zsmul_eq_three`) and a uniqueness argument
(`intCast_eq_zero_of_zsmul_add_zsmul_eq_zero_three`).  This file has no pairing, no `χ_n`, and no
distinguished pair; it has a functor `b ↦ ρ_b` and a conjugacy.  The relation is exactly the one
`EllipticCurves.TateModule.DeterminantMod` states between `#951` and `galoisDetMod` — *"`#951` has
an **equation**; this file has an **object**"* — and it holds verbatim one level up.  Nor does
`#951` subsume this: a pairing basis exists only at `n = 2` and `n = 3`, where the pairing does.

**Nothing at `n = 5`**: `basisTorsionOfSmooth` is `3`-smooth, and behind that stand
`[5]`-surjectivity and `#E[5]`.  **No trace and no characteristic polynomial**:
`EllipticCurves.TateModule.DeterminantMod` records that `galoisTraceTwo`'s finite-level analogue has
no consumer, `#1240` retired the freeness half of that sentence and explicitly not the consumer
half, and this file does not retire it either.  **No `Gal(F/S)`-stable basis**: it does not exist in
general, `galoisRepModMatrix_conj` is what makes its absence harmless, and three files already say
so.

## Main definitions

Every public declaration of this file is listed, here and under `## Main statements`, and all are in
namespace `WeierstrassCurve.Affine`.

* `galoisRepModMatrix` : the representation `G →* GL (Fin 2) (ZMod n)` attached to a basis of
  `E[n]`.

## Main statements

* `galoisRepModMatrix_apply`, `coe_galoisRepModMatrix`, `galoisRepModMatrix_apply_coe`,
  `galoisRepModMatrix_mulVec`, `galoisRepModMatrix_smul_basis_eq_sum` : what the matrix is and how
  it acts.
* `det_galoisRepModMatrix` and `det_comp_galoisRepModMatrix` : `det ∘ ρ_{E,n} = galoisDetMod n`,
  pointwise and as an identity of homomorphisms.
* `coe_galoisRepModMatrix_mul_basisChange`, `galoisRepModMatrix_mul_basisChangeGL`,
  `galoisRepModMatrix_conj`, `galoisRepModMatrix_eq_conj_comp`, `range_galoisRepModMatrix_map` :
  the basis-change conjugacy and what it makes well defined up to conjugacy.
* `ker_galoisRepModMatrix` and `ker_galoisRepModMatrix_eq` : the kernel is `ker (galoisRepMod n)` in
  every basis, so it is basis-independent on the nose and not merely up to conjugacy.
* `exists_galoisRepModMatrix_of_smooth`, `exists_galoisRepModMatrix_two`,
  `exists_galoisRepModMatrix_three` : the choice-free existence statements.

## References

* [J. H. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.7.
-/

open Matrix

namespace WeierstrassCurve.Affine

variable {S F : Type*} [Field S] [Field F] [DecidableEq F] [Algebra S F] {W' : Affine S}

section Representation

variable {n : ℕ} [NeZero n] (b b' : Module.Basis (Fin 2) (ZMod n) ((W'⁄F).torsion n))

/-- **The mod-`n` Galois representation in matrix form**, `ρ_{E,n} : G →* GL₂(ℤ/n)`, obtained by
reading `galoisRepModLinear n` (`EllipticCurves.TateModule.DeterminantMod`) through a basis of
`E[n]`.

The chain is `Module.Basis.linearEquivMulEquivGL` (`EllipticCurves.TateModule.GeneralLinearGroup`),
which is `Units.mapEquiv` of `LinearMap.toMatrixAlgEquiv` and therefore lands in the units with no
matrix ever being inverted.  ⚠️ It is stated over an arbitrary commutative ring, so nothing here
asks `ZMod n` to be a field, and the definition is available at every `n` with `[NeZero n]` — with
no rank hypothesis at all.  What a rank hypothesis buys is that the matrix is *faithful* to the
module rather than a `2 × 2` shadow of something else, and that is `basisTorsionOfSmooth`'s job, not
this definition's.

Different bases give conjugate representations, so this depends on `b`; see
`galoisRepModMatrix_conj` for the law and `exists_galoisRepModMatrix_of_smooth` for the choice-free
statement.  ⚠️ `b` is an explicit argument and `basisTorsionOfSmooth` is deliberately not baked in;
see the module docstring. -/
noncomputable def galoisRepModMatrix : (F ≃ₐ[S] F) →* GL (Fin 2) (ZMod n) :=
  b.linearEquivMulEquivGL.toMonoidHom.comp (galoisRepModLinear n)

lemma galoisRepModMatrix_apply (σ : F ≃ₐ[S] F) :
    galoisRepModMatrix b σ = b.linearEquivMulEquivGL (galoisRepModLinear n σ) := rfl

/-- **The entries of `ρ_{E,n}(σ)`.**  The `j`-th column is the coordinate vector of the Galois
translate of the `j`-th basis vector; equivalently, matrices here act on column vectors.  This is
Mathlib's `LinearMap.toMatrix` convention, and `linearEquivMulEquivGL_symm` records that the chain
used here and the one `EllipticCurves.TateModule.MatrixRep` uses differ by no transpose. -/
@[simp]
lemma galoisRepModMatrix_apply_coe (σ : F ≃ₐ[S] F) (i j : Fin 2) :
    (galoisRepModMatrix b σ : Matrix (Fin 2) (Fin 2) (ZMod n)) i j = b.repr (σ • b j) i := by
  rw [galoisRepModMatrix_apply, Module.Basis.coe_linearEquivMulEquivGL_apply,
    galoisRepModLinear_apply_coe]

/-- **The underlying matrix is `LinearMap.toMatrix` of the linear representation.**  The bridge to
everything Mathlib proves about `LinearMap.toMatrix`, and in particular the one step of
`det_galoisRepModMatrix`. -/
lemma coe_galoisRepModMatrix (σ : F ≃ₐ[S] F) :
    (galoisRepModMatrix b σ : Matrix (Fin 2) (Fin 2) (ZMod n))
      = LinearMap.toMatrix b b
          ((galoisRepModLinear (W' := W') (F := F) n σ : _ ≃ₗ[ZMod n] _) : _ →ₗ[ZMod n] _) := by
  ext i j
  rw [galoisRepModMatrix_apply_coe, LinearMap.toMatrix_apply]
  rfl

/-- **The matrix acts on coordinate vectors exactly as `σ` acts on `E[n]`.**  This is the identity
that ties `galoisRepModMatrix` back to the Galois action, and the form later computations use. -/
lemma galoisRepModMatrix_mulVec (σ : F ≃ₐ[S] F) (P : (W'⁄F).torsion n) :
    ⇑(b.repr (σ • P))
      = (galoisRepModMatrix b σ : Matrix (Fin 2) (Fin 2) (ZMod n)) *ᵥ ⇑(b.repr P) := by
  rw [coe_galoisRepModMatrix, LinearMap.toMatrix_mulVec_repr]
  rfl

/-- **`σ` translates a basis vector into the corresponding column of its matrix.**  The unbundled
reading of `galoisRepModMatrix_apply_coe`. -/
lemma galoisRepModMatrix_smul_basis_eq_sum (σ : F ≃ₐ[S] F) (j : Fin 2) :
    σ • b j = ∑ i, (galoisRepModMatrix b σ : Matrix (Fin 2) (Fin 2) (ZMod n)) i j • b i := by
  conv_lhs => rw [← b.sum_repr (σ • b j)]
  exact Finset.sum_congr rfl fun i _ => by rw [galoisRepModMatrix_apply_coe]

/-- **The determinant of the matrix representation is the basis-free determinant character**,
`det (ρ_{E,n}(σ)) = galoisDetMod n σ` in `(ZMod n)ˣ`.

This is the statement the file exists for.  `galoisDetMod` is `LinearEquiv.det` of
`galoisRepModLinear n` and mentions no basis; `galoisRepModMatrix b` mentions one throughout.  The
proof is `LinearMap.det_toMatrix` against `coe_galoisRepModMatrix`, and `LinearEquiv.coe_det`
across the last coercion.

⚠️ **Unconditional in `n`, and therefore not by itself evidence that either side is interesting**:
at an `n` where `E[n]` is not free of rank `2`, `LinearMap.det` returns its junk value `1` and this
says `1 = 1`.  What rules that out is `finrank_torsion_of_smooth`
(`EllipticCurves.TateModule.DeterminantModSmooth`), and it is the reason the existence statements
below carry `3`-smoothness while this one does not.

⚠️ **It also settles basis-independence of the determinant**, since the right-hand side does not
mention `b`; that is why no separate `det`-invariance corollary is stated. -/
theorem det_galoisRepModMatrix (σ : F ≃ₐ[S] F) :
    Matrix.GeneralLinearGroup.det (galoisRepModMatrix b σ)
      = galoisDetMod (W' := W') (F := F) n σ :=
  Units.ext <| by
    rw [galoisDetMod_apply]
    change (galoisRepModMatrix b σ : Matrix (Fin 2) (Fin 2) (ZMod n)).det = _
    rw [coe_galoisRepModMatrix, LinearMap.det_toMatrix, LinearEquiv.coe_det]

/-- **`det ∘ ρ_{E,n} = galoisDetMod n` as an identity of homomorphisms** — the form to quote when
the point is that the character, and not merely each of its values, is the basis-free one. -/
theorem det_comp_galoisRepModMatrix :
    (Matrix.GeneralLinearGroup.det : GL (Fin 2) (ZMod n) →* (ZMod n)ˣ).comp
        (galoisRepModMatrix b) = galoisDetMod (W' := W') (F := F) n :=
  MonoidHom.ext (det_galoisRepModMatrix b)

/-! ### The basis-change conjugacy

`basisChangeGL` and its computation rules come from
`EllipticCurves.TateModule.PrimaryMatrixRepBasisChange`, whose section on them is stated for an
arbitrary finite-rank free module over an arbitrary commutative ring; nothing is restated here. -/

open tateModule in
/-- **The matrix form of the conjugation law**: `ρ_{b'}(σ)` and `ρ_b(σ)` intertwine the change of
basis.  Stated multiplicatively rather than as a conjugation because that is the form the proof
produces and the form with no inverses in it. -/
theorem coe_galoisRepModMatrix_mul_basisChange (σ : F ≃ₐ[S] F) :
    (galoisRepModMatrix b' σ : Matrix (Fin 2) (Fin 2) (ZMod n)) * b'.toMatrix b
      = b'.toMatrix b * (galoisRepModMatrix b σ : Matrix (Fin 2) (Fin 2) (ZMod n)) := by
  refine Matrix.ext_iff_mulVec.2 fun v => ?_
  obtain ⟨m, rfl⟩ : ∃ m, ⇑(b.repr m) = v :=
    ⟨b.equivFun.symm v, by rw [← Module.Basis.equivFun_apply]; exact b.equivFun.apply_symm_apply v⟩
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Module.Basis.toMatrix_mulVec_repr,
    ← galoisRepModMatrix_mulVec, ← galoisRepModMatrix_mulVec, Module.Basis.toMatrix_mulVec_repr]

open tateModule in
/-- **`ρ_{b'}(σ) · c = c · ρ_b(σ)`** in `GL₂(ℤ/n)`, where `c = basisChangeGL b b'`. -/
theorem galoisRepModMatrix_mul_basisChangeGL (σ : F ≃ₐ[S] F) :
    galoisRepModMatrix b' σ * basisChangeGL b b'
      = basisChangeGL b b' * galoisRepModMatrix b σ :=
  Units.ext <| by
    simpa [coe_basisChangeGL] using coe_galoisRepModMatrix_mul_basisChange b b' σ

open tateModule in
/-- **Changing the basis conjugates the mod-`n` representation.**

`ρ_{E,n}` depends on a choice of basis of `E[n]`, and this is exactly how: the representations
attached to two bases differ by conjugation by the change-of-basis element, uniformly in `σ`.  It is
what makes every conjugation-invariant of `ρ_{E,n}` — its kernel, its determinant, its image up to
conjugacy — independent of the choice, and it is the finite-level twin of `galoisRepMatrix_conj`.

⚠️ Without it the matrix representation would be noise, because `basisTorsionOfSmooth` is not
canonical; its own docstring says any statement proved with it must be one whose truth does not
depend on the choice. -/
theorem galoisRepModMatrix_conj (σ : F ≃ₐ[S] F) :
    galoisRepModMatrix b' σ
      = basisChangeGL b b' * galoisRepModMatrix b σ * (basisChangeGL b b')⁻¹ := by
  rw [← galoisRepModMatrix_mul_basisChangeGL, mul_inv_cancel_right]

open tateModule in
/-- **The conjugation law as an identity of representations**, not merely of their values: the two
homomorphisms `G →* GL₂(ℤ/n)` differ by an inner automorphism of `GL₂(ℤ/n)`.  This is the form to
quote when the point is that the *representation* is well defined up to conjugation. -/
theorem galoisRepModMatrix_eq_conj_comp :
    galoisRepModMatrix b' =
      (MulAut.conj (basisChangeGL b b')).toMonoidHom.comp (galoisRepModMatrix b) :=
  MonoidHom.ext fun σ => by
    simpa using galoisRepModMatrix_conj b b' σ

open tateModule in
/-- **The image of `ρ_{E,n}` is well defined up to conjugacy in `GL₂(ℤ/n)`.**  Not merely
isomorphic: it is carried onto the other by an inner automorphism of the ambient group. -/
theorem range_galoisRepModMatrix_map :
    (galoisRepModMatrix b').range =
      (galoisRepModMatrix b).range.map (MulAut.conj (basisChangeGL b b')).toMonoidHom := by
  rw [galoisRepModMatrix_eq_conj_comp b b', MonoidHom.range_comp]

/-- **The matrix representation has the same kernel as `galoisRepMod n`, in every basis.**  The
finite-level twin of `ker_galoisRepMatrix` (`EllipticCurves.TateModule.Kernel`), and proved by that
statement's shorter-than-conjugation route: `galoisRepModMatrix b` is `galoisRepMod n` postcomposed
with two *equivalences*, so no choice of basis survives into the kernel.

⚠️ Unconditional in `n` — it needs neither `3`-smoothness nor a rank, because it is a statement
about a composite of injections and not about `E[n]`.  With `ker_galoisRepModLinear`
(`EllipticCurves.TateModule.DeterminantMod`) it lets every statement of
`EllipticCurves.TateModule.Kernel` be quoted against the matrix representation. -/
theorem ker_galoisRepModMatrix :
    (galoisRepModMatrix b).ker = (galoisRepMod (W' := W') (F := F) n).ker := by
  rw [← ker_galoisRepModLinear]
  ext σ
  simp only [MonoidHom.mem_ker, galoisRepModMatrix, MonoidHom.coe_comp, Function.comp_apply,
    MulEquiv.coe_toMonoidHom, EmbeddingLike.map_eq_one_iff]

/-- **The kernel does not depend on the basis at all**, not merely up to conjugacy — the two kernels
are equal as subgroups.  The conjugacy `galoisRepModMatrix_conj` would give it too; this is the
one-line reading off `ker_galoisRepModMatrix`, which does not go through conjugation at all. -/
theorem ker_galoisRepModMatrix_eq :
    (galoisRepModMatrix b').ker = (galoisRepModMatrix b).ker := by
  rw [ker_galoisRepModMatrix, ker_galoisRepModMatrix]

end Representation

/-! ### The choice-free existence statements

⚠️ These are where `3`-smoothness enters, and it enters through the *basis* and not through the
representation: `galoisRepModMatrix` needs only `[NeZero n]`, but a basis of `E[n]` indexed by
`Fin 2` needs `finrank_torsion_of_smooth`.  The determinant clause is carried along because without
it the statement would be about a homomorphism into `GL₂(ℤ/n)` that never mentions the curve. -/

section Existence

variable [IsAlgClosed F] [(W'⁄F).IsElliptic] {n : ℕ} [NeZero n]

open Classical in
/-- **The mod-`n` matrix representation exists at every `3`-smooth `n > 1`**, as a representation
that really does compute the Galois action and whose determinant is the basis-free character.

⚠️ `1 < n` is not bookkeeping: it is what `finrank_torsion_of_smooth` needs, and
`EllipticCurves.TateModule.DeterminantModSmooth` certifies that the rank is `1` and not `2` at
`n = 1`, where `ZMod 1` is the trivial ring. -/
theorem exists_galoisRepModMatrix_of_smooth (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) (hn : 1 < n)
    (hfac : ∀ p ∈ n.primeFactors, p = 2 ∨ p = 3) :
    ∃ (c : Module.Basis (Fin 2) (ZMod n) ((W'⁄F).torsion n))
      (ρ : (F ≃ₐ[S] F) →* GL (Fin 2) (ZMod n)),
      (∀ (σ : F ≃ₐ[S] F) (P : (W'⁄F).torsion n),
        ⇑(c.repr (σ • P)) = (ρ σ : Matrix (Fin 2) (Fin 2) (ZMod n)) *ᵥ ⇑(c.repr P)) ∧
      ∀ σ : F ≃ₐ[S] F,
        Matrix.GeneralLinearGroup.det (ρ σ) = galoisDetMod (W' := W') (F := F) n σ :=
  ⟨basisTorsionOfSmooth (W := W'⁄F) h2 h3 hn hfac, galoisRepModMatrix _,
    galoisRepModMatrix_mulVec _, det_galoisRepModMatrix _⟩

open Classical in
/-- **The mod-`2` matrix representation exists**, on `(2 : F) ≠ 0` alone.

⚠️ **No `(3 : F) ≠ 0`.**  Routing this through `exists_galoisRepModMatrix_of_smooth` would compile
and would charge a hypothesis `#E[2] = 4` does not need; the basis is `basisTorsionTwo`, which
`EllipticCurves.TateModule.DeterminantModSmooth` states from the `n = 2` inputs for exactly that
reason. -/
theorem exists_galoisRepModMatrix_two (h2 : (2 : F) ≠ 0) :
    ∃ (c : Module.Basis (Fin 2) (ZMod 2) ((W'⁄F).torsion 2))
      (ρ : (F ≃ₐ[S] F) →* GL (Fin 2) (ZMod 2)),
      (∀ (σ : F ≃ₐ[S] F) (P : (W'⁄F).torsion 2),
        ⇑(c.repr (σ • P)) = (ρ σ : Matrix (Fin 2) (Fin 2) (ZMod 2)) *ᵥ ⇑(c.repr P)) ∧
      ∀ σ : F ≃ₐ[S] F,
        Matrix.GeneralLinearGroup.det (ρ σ) = galoisDetMod (W' := W') (F := F) 2 σ :=
  ⟨basisTorsionTwo (W := W'⁄F) h2, galoisRepModMatrix _,
    galoisRepModMatrix_mulVec _, det_galoisRepModMatrix _⟩

open Classical in
/-- **The mod-`3` matrix representation exists.**  The basis is `basisTorsionThree`
(`EllipticCurves.TateModule.DeterminantMod`), which rests on `#E[3] = 9`. -/
theorem exists_galoisRepModMatrix_three (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) :
    ∃ (c : Module.Basis (Fin 2) (ZMod 3) ((W'⁄F).torsion 3))
      (ρ : (F ≃ₐ[S] F) →* GL (Fin 2) (ZMod 3)),
      (∀ (σ : F ≃ₐ[S] F) (P : (W'⁄F).torsion 3),
        ⇑(c.repr (σ • P)) = (ρ σ : Matrix (Fin 2) (Fin 2) (ZMod 3)) *ᵥ ⇑(c.repr P)) ∧
      ∀ σ : F ≃ₐ[S] F,
        Matrix.GeneralLinearGroup.det (ρ σ) = galoisDetMod (W' := W') (F := F) 3 σ :=
  ⟨basisTorsionThree (W := W'⁄F) h2 h3, galoisRepModMatrix _,
    galoisRepModMatrix_mulVec _, det_galoisRepModMatrix _⟩

end Existence

/-! ### Non-vacuity

⚠️ **The load-bearing certificates are at a composite index.**  At `n = 2` and `n = 3` everything
below elaborates through `Field (ZMod n)` and exercises none of what is new; the index used here is
`12`, which is `3`-smooth, composite and divisible by both primes, following
`EllipticCurves.TateModule.DeterminantModSmooth`.

The curve is this front's standard one, `y² + y = x³` over `ℚ` base-changed to `AlgebraicClosure ℚ`,
with **`S = ℚ` and not `S = F`** — over `S = F` the group `Gal(F/S)` is trivial and a certificate
for a Galois *representation* says nothing. -/

section Nonvacuity

/-! The certificate curve `y² + y = x³` over `ℚ` and its base — algebraically closed so that
`Gal(F/ℚ)` is not the trivial group, and of characteristic `0` so that `2 ≠ 0` and `3 ≠ 0` — are the
shared `EllipticCurves.Fixture.y2AddYEqX3` and `EllipticCurves.Fixture.AlgClosedQ`, which also
supply `(y2AddYEqX3 ℚ).IsElliptic` from a single `[CharZero F]` instance.  Only the
**base-changed** instance below is still local to this file; see its docstring for why. -/

open EllipticCurves.Fixture

/-- ⚠️ `WeierstrassCurve.baseChange` is a plain `def`, so `[(W⁄F).IsElliptic]` is **not** found by
bare `inferInstance` from `[W.IsElliptic]`; this is the idiom
`EllipticCurves.TateModule.Determinant` documents for exactly that reason.

⚠️ **Measured dead** (`#1405`, at `db0c65b`): deleting this instance leaves the file elaborating
with exit `0` and zero errors. The winner is the `private` fixture in
`EllipticCurves.TateModule.DeterminantModSmooth`, live here because `private` hides a *name*, not
an *instance*, so it takes part in resolution in every module downstream of the one that declares
it.

⚠️ **That is not a licence to delete it.** The supplier is another file's `private` declaration,
named by no import and pinned by nothing, and the whole `TateModule/` chain traces back to
`EllipticCurves.TateModule.FreeThree`'s, which is load-bearing. `#1408` is the safe removal, and
`EllipticCurves.Fixtures` carries the 18-site matrix and the rule that decides it. -/
private instance : ((y2AddYEqX3 ℚ)⁄AlgClosedQ).IsElliptic :=
  inferInstanceAs ((y2AddYEqX3 ℚ).map (algebraMap ℚ AlgClosedQ)).IsElliptic

private lemma exampleTwo : (2 : AlgClosedQ) ≠ 0 := two_ne_zero

private lemma exampleThree : (3 : AlgClosedQ) ≠ 0 := three_ne_zero_of_charZero _

/-- `12 = 2² · 3` is `3`-smooth.  ⚠️ `decide` does not close this: `Nat.primeFactors` is the support
of a factorisation defined by well-founded recursion. -/
private lemma smoothTwelve : ∀ p ∈ (12 : ℕ).primeFactors, p = 2 ∨ p = 3 := by
  have h : (12 : ℕ) = 2 ^ 2 * 3 ^ 1 := by norm_num
  rw [h, Nat.primeFactors_mul (by norm_num) (by norm_num),
    Nat.primeFactors_prime_pow two_ne_zero Nat.prime_two,
    Nat.primeFactors_prime_pow one_ne_zero Nat.prime_three]
  simp

open Classical in
/-- A `ZMod 12`-basis of `E[12]` on the certificate curve, fixed once so that the three certificates
below all speak about the same representation. -/
private noncomputable def exampleBasis :
    Module.Basis (Fin 2) (ZMod 12) (((y2AddYEqX3 ℚ)⁄AlgClosedQ).torsion 12) :=
  basisTorsionOfSmooth exampleTwo exampleThree (by norm_num) smoothTwelve

open Classical in
/-- **⚠️ THE LOAD-BEARING CERTIFICATE**: on a curve that exists and at a *composite* index, there
really is a matrix representation `Gal(F/ℚ) →* GL₂(ℤ/12)` computing the Galois action, whose
determinant is `galoisDetMod 12`. -/
example : ∃ (c : Module.Basis (Fin 2) (ZMod 12) (((y2AddYEqX3 ℚ)⁄AlgClosedQ).torsion 12))
      (ρ : (AlgClosedQ ≃ₐ[ℚ] AlgClosedQ) →* GL (Fin 2) (ZMod 12)),
      (∀ (σ : AlgClosedQ ≃ₐ[ℚ] AlgClosedQ) (P : ((y2AddYEqX3 ℚ)⁄AlgClosedQ).torsion 12),
        ⇑(c.repr (σ • P)) = (ρ σ : Matrix (Fin 2) (Fin 2) (ZMod 12)) *ᵥ ⇑(c.repr P)) ∧
      ∀ σ : AlgClosedQ ≃ₐ[ℚ] AlgClosedQ,
        Matrix.GeneralLinearGroup.det (ρ σ)
          = galoisDetMod (W' := y2AddYEqX3 ℚ) (F := AlgClosedQ) 12 σ :=
  exists_galoisRepModMatrix_of_smooth exampleTwo exampleThree (by norm_num) smoothTwelve

open Classical in
/-- The determinant bridge on the same curve at `n = 12`, written out at an arbitrary `σ` rather
than obtained-and-projected. -/
example (σ : AlgClosedQ ≃ₐ[ℚ] AlgClosedQ) :
    Matrix.GeneralLinearGroup.det (galoisRepModMatrix exampleBasis σ)
      = galoisDetMod (W' := y2AddYEqX3 ℚ) (F := AlgClosedQ) 12 σ :=
  det_galoisRepModMatrix exampleBasis σ

open Classical in
/-- **⚠️ The conjugation law is not vacuous at `n = 12`**: the conjugating element is not always
`1`, so `galoisRepModMatrix_conj` is not a disguised `b' = b`.  The witness is the reindexing of
`exampleBasis` along the transposition of the two indices, and the statement that it moves the
representation is `basisChangeGL_reindex_swap_ne_one`, stated over an arbitrary `Nontrivial`
commutative ring in `EllipticCurves.TateModule.PrimaryMatrixRepBasisChange`.  ⚠️ `Nontrivial
(ZMod 12)` is where `1 < n` shows up again: at `n = 1` the certificate would be false. -/
example : tateModule.basisChangeGL exampleBasis (exampleBasis.reindex (Equiv.swap 0 1)) ≠ 1 :=
  haveI : Fact (1 < 12) := ⟨by norm_num⟩
  tateModule.basisChangeGL_reindex_swap_ne_one exampleBasis

open Classical in
/-- The conjugacy itself on the same curve, at the same pair of bases. -/
example (σ : AlgClosedQ ≃ₐ[ℚ] AlgClosedQ) :
    galoisRepModMatrix (exampleBasis.reindex (Equiv.swap 0 1)) σ
      = tateModule.basisChangeGL exampleBasis (exampleBasis.reindex (Equiv.swap 0 1))
          * galoisRepModMatrix exampleBasis σ
          * (tateModule.basisChangeGL exampleBasis (exampleBasis.reindex (Equiv.swap 0 1)))⁻¹ :=
  galoisRepModMatrix_conj exampleBasis (exampleBasis.reindex (Equiv.swap 0 1)) σ

open Classical in
/-- The `n = 2` instance on the same curve, on `h2` alone. -/
example : ∃ (c : Module.Basis (Fin 2) (ZMod 2) (((y2AddYEqX3 ℚ)⁄AlgClosedQ).torsion 2))
      (ρ : (AlgClosedQ ≃ₐ[ℚ] AlgClosedQ) →* GL (Fin 2) (ZMod 2)),
      (∀ (σ : AlgClosedQ ≃ₐ[ℚ] AlgClosedQ) (P : ((y2AddYEqX3 ℚ)⁄AlgClosedQ).torsion 2),
        ⇑(c.repr (σ • P)) = (ρ σ : Matrix (Fin 2) (Fin 2) (ZMod 2)) *ᵥ ⇑(c.repr P)) ∧
      ∀ σ : AlgClosedQ ≃ₐ[ℚ] AlgClosedQ,
        Matrix.GeneralLinearGroup.det (ρ σ)
          = galoisDetMod (W' := y2AddYEqX3 ℚ) (F := AlgClosedQ) 2 σ :=
  exists_galoisRepModMatrix_two exampleTwo

open Classical in
/-- The `n = 3` instance on the same curve. -/
example : ∃ (c : Module.Basis (Fin 2) (ZMod 3) (((y2AddYEqX3 ℚ)⁄AlgClosedQ).torsion 3))
      (ρ : (AlgClosedQ ≃ₐ[ℚ] AlgClosedQ) →* GL (Fin 2) (ZMod 3)),
      (∀ (σ : AlgClosedQ ≃ₐ[ℚ] AlgClosedQ) (P : ((y2AddYEqX3 ℚ)⁄AlgClosedQ).torsion 3),
        ⇑(c.repr (σ • P)) = (ρ σ : Matrix (Fin 2) (Fin 2) (ZMod 3)) *ᵥ ⇑(c.repr P)) ∧
      ∀ σ : AlgClosedQ ≃ₐ[ℚ] AlgClosedQ,
        Matrix.GeneralLinearGroup.det (ρ σ)
          = galoisDetMod (W' := y2AddYEqX3 ℚ) (F := AlgClosedQ) 3 σ :=
  exists_galoisRepModMatrix_three exampleTwo exampleThree

end Nonvacuity

end WeierstrassCurve.Affine
