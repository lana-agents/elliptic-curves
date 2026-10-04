/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import EllipticCurves.Fixtures
import EllipticCurves.TateModule.FreeGeneral
import EllipticCurves.TateModule.MatrixRepMod
import EllipticCurves.TateModule.PrimaryDeterminant

/-!
# The level-`k` reduction of the `ℓ`-adic determinant character

`EllipticCurves.TateModule.PrimaryDeterminant` builds `galoisDet : G →* ℤ_[ℓ]ˣ`, the determinant of
the `ℓ`-adic representation on `T_ℓE`, and `EllipticCurves.TateModule.DeterminantMod` builds
`galoisDetMod n : G →* (ZMod n)ˣ`, the determinant of the mod-`n` representation on `E[n]`.  They
had never been compared.  This file proves that the second is the first read modulo `ℓ^k`:

```
PadicInt.toZModPow k (galoisDet σ) = galoisDetMod (ℓ ^ k) σ
```

at every prime `ℓ` with `(2 : F) ≠ 0` and `(ℓ : F) ≠ 0`.

## Why it is the missing step, and what it is missing *from*

`ℤ_[ℓ]` is the inverse limit of the `ZMod (ℓ^k)`, so `PadicInt.ext_of_toZModPow` turns an identity
of `ℓ`-adic characters into the family of its mod-`ℓ^k` shadows.  The identity this development is
built towards — `det ρ_{E,ℓ} = χ_ℓ`, which `EllipticCurves.TateModule.Determinant`,
`EllipticCurves.TateModule.DeterminantMod`, `EllipticCurves.TateModule.MatrixRepGeneral` and
`EllipticCurves.Galois.CyclotomicCharacter` all name as the goal of the Weil-pairing effort —
therefore reduces to two facts: that `χ_ℓ`'s level-`k` shadow is `χ_{ℓ^k}`
(`galoisCyclotomicChar_toZModPow`, merged), and that `det ρ_{E,ℓ}`'s level-`k` shadow is
`det ρ_{E,ℓ^k}` (**this file**).  The composition is
`EllipticCurves.FunctionField.TateDeterminantCyclotomic`, which cannot live here: it needs the
Weil pairing, and ⚠️ **no module under `TateModule/` imports anything under `FunctionField/`** —
no file in this directory carries an `import` line naming a `FunctionField` module, and this file
does not change that.

⚠️⚠️ **The natural one-line check for that invariant cannot be written down here, and the
first draft of this paragraph wrote it anyway.**  It is a `grep` for the literal import prefix
across `EllipticCurves/TateModule/`; quoting it inside a file *in* that directory makes the
command match its own text and report `1` where the invariant still holds — measured, not
supposed.  So the check is described rather than quoted, and a reader running it should run it
from the prefix and not from this page.

## ⚠️ The whole content is that the coordinates reduce, and `padicPairEquiv` already said so

`EllipticCurves.TateModule.PrimaryFree`'s `padicPairEquiv_apply_coe` reads, verbatim: the
level-`k` value of the element of `T_ℓE` with `ℓ`-adic coordinates `(a, b)` against a coherent
system `(P, Q)` is

```
(PadicInt.toZModPow k a).val • P k + (PadicInt.toZModPow k b).val • Q k
```

i.e. the level-`k` coordinates against `(P k, Q k)` *are* the residues of `a` and `b`.  That
single identity — whose docstring there says it is "the identity that a later analysis of the
Galois action on `T_ℓE` will run on" — is `toZModPow_padicPairBasis_repr` below, and everything
after it is bookkeeping: the Galois action commutes with the level projection
(`proj_galois_smul`, a `rfl`), matrix entries on both sides are `b.repr (σ • b j) i` by definition,
and `RingHom.map_det` carries a ring hom through a determinant.

⚠️ **The coherence `ℓ • P (k + 1) = P k` is spent exactly once, inside `padicPairEquiv`, and
not again here.**  A system of levelwise bases that is *not* coherent would still give a basis at
every level and a basis of `T_ℓE` would not exist at all; what coherence buys is that one basis of
`T_ℓE` projects onto the chosen basis at *every* level simultaneously, which is
`proj_padicPairBasis`.

## The two bases, and why they are built the same way

Both are `Module.Basis.ofEquivFun` of an explicit linear equivalence onto `Fin 2 → R`:

* `torsionPairBasis` — out of `torsionPairEquivOfCard` (`EllipticCurves.Torsion.PrimaryBasis`), the
  structure isomorphism `(ℤ/nℤ)² ≃+ E[n]` attached to a generating pair when `#E[n] = n²`.  ⚠️ Its
  `ZMod n`-linearity is free (`AddEquiv.toZModLinearEquiv`), and there is no instance diamond to
  navigate: `torsionZModModule` is the only `Module (ZMod n) E[n]` instance in the tree and it is
  `AddCommGroup.zmodModule`, which is what `ZMod.map_smul` is stated against.
* `padicPairBasis` — out of `padicPairEquiv` through `tateModuleBasis`
  (`EllipticCurves.TateModule.PrimaryMatrixRep`), which is the same `ofEquivFun` construction.

Using the *same* construction on both sides is what makes `toZModPow_padicPairBasis_repr` a
`Fin`-case split on `![a, b]` rather than a coordinate computation.

## Main definitions

* `WeierstrassCurve.Affine.torsionPairBasis` — the `Fin 2`-indexed `ZMod n`-basis of `E[n]`
  attached to a generating pair with `#E[n] = n²`.
* `WeierstrassCurve.Affine.padicPairBasis` — the `Fin 2`-indexed `ℤ_[ℓ]`-basis of `T_ℓE` attached
  to a coherent system of generating pairs.

## Main statements

* `WeierstrassCurve.Affine.toZModPow_padicPairBasis_repr` — the level-`k` coordinates of an element
  of `T_ℓE` are the residues of its `ℓ`-adic coordinates.
* `WeierstrassCurve.Affine.proj_padicPairBasis` — the level projection carries the `ℓ`-adic basis
  to the level-`k` basis.
* `WeierstrassCurve.Affine.toZModPow_galoisRepMatrix` — the matrix representation reduces entrywise.
* `WeierstrassCurve.Affine.toZModPow_coe_galoisDet_of_natCast_ne_zero` — **the statement this file
  exists for**, in `ZMod (ℓ ^ k)`, with no basis and no coherent system in sight.
* `WeierstrassCurve.Affine.toZModPow_galoisDet_of_natCast_ne_zero` — the same in `(ZMod (ℓ ^ k))ˣ`.

## References

* [J. H. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.7.
-/

open Matrix

namespace WeierstrassCurve.Affine

open scoped AddSubgroup

/-! ### A `Fin 2`-indexed basis of `E[n]` from a generating pair -/

section TorsionBasis

variable {F : Type*} [Field F] [DecidableEq F] {W : Affine F}

/-- **The `Fin 2`-indexed `ZMod n`-basis of `E[n]` attached to a generating pair `(P, Q)`**, when
`#E[n] = n²`.

`Fin 2 → ZMod n` rather than `ZMod n × ZMod n` for the reason `tateModuleBasis` gives: `Matrix`,
`LinearMap.toMatrix` and `GL` are all indexed by a `Fintype`, so the `Prod` is crossed once here
rather than carried through every later statement. -/
noncomputable def torsionPairBasis {n : ℕ} [NeZero n] (hcard : Nat.card (W.torsion n) = n * n)
    {P Q : W.Point} (hgen : AddSubgroup.closure ({P, Q} : Set W.Point) = W.torsion n) :
    Module.Basis (Fin 2) (ZMod n) (W.torsion n) :=
  Module.Basis.ofEquivFun
    ((AddEquiv.toZModLinearEquiv (torsionPairEquivOfCard hcard hgen).symm).trans
      (LinearEquiv.finTwoArrow (ZMod n) (ZMod n)).symm)

lemma torsionPairBasis_repr {n : ℕ} [NeZero n] (hcard : Nat.card (W.torsion n) = n * n)
    {P Q : W.Point} (hgen : AddSubgroup.closure ({P, Q} : Set W.Point) = W.torsion n)
    (x : W.torsion n) (i : Fin 2) :
    (torsionPairBasis hcard hgen).repr x i =
      ![((torsionPairEquivOfCard hcard hgen).symm x).1,
        ((torsionPairEquivOfCard hcard hgen).symm x).2] i := by
  rw [torsionPairBasis, Module.Basis.ofEquivFun_repr_apply]
  rfl

/-- The coordinates of an element of `E[n]` against `torsionPairBasis` are the unique `ZMod n`
coefficients expressing it in the generating pair. -/
lemma torsionPairBasis_repr_eq {n : ℕ} [NeZero n] (hcard : Nat.card (W.torsion n) = n * n)
    {P Q : W.Point} (hgen : AddSubgroup.closure ({P, Q} : Set W.Point) = W.torsion n)
    {x : W.torsion n} {a b : ZMod n} (hx : (x : W.Point) = a.val • P + b.val • Q) (i : Fin 2) :
    (torsionPairBasis hcard hgen).repr x i = ![a, b] i := by
  have hxab : x = torsionPairEquivOfCard hcard hgen (a, b) := Subtype.ext (by
    rw [hx, torsionPairEquivOfCard_apply_coe])
  rw [torsionPairBasis_repr, hxab, AddEquiv.symm_apply_apply]

end TorsionBasis

/-! ### A `Fin 2`-indexed basis of `T_ℓE` from a coherent system, and its level-`k` reduction -/

section PadicBasis

variable {F : Type*} [Field F] [DecidableEq F] {W : Affine F} {ℓ : ℕ} [Fact ℓ.Prime]
  {P Q : ℕ → W.Point}

/-- **The `Fin 2`-indexed `ℤ_[ℓ]`-basis of `T_ℓE` attached to a coherent system of generating
pairs.**  This is `tateModuleBasis` of `padicPairEquiv`, so it is built by exactly the
construction `torsionPairBasis` uses at each finite level — which is what makes the two
comparable. -/
noncomputable def padicPairBasis
    (hcard : ∀ k, Nat.card (W.torsion (ℓ ^ k)) = ℓ ^ k * ℓ ^ k)
    (hgen : ∀ k, AddSubgroup.closure ({P k, Q k} : Set W.Point) = W.torsion (ℓ ^ k))
    (hP : ∀ k, ℓ • P (k + 1) = P k) (hQ : ∀ k, ℓ • Q (k + 1) = Q k) :
    Module.Basis (Fin 2) ℤ_[ℓ] (W.tateModule ℓ) :=
  tateModule.tateModuleBasis (tateModule.padicPairEquiv hcard hgen hP hQ).symm

lemma padicPairBasis_repr
    (hcard : ∀ k, Nat.card (W.torsion (ℓ ^ k)) = ℓ ^ k * ℓ ^ k)
    (hgen : ∀ k, AddSubgroup.closure ({P k, Q k} : Set W.Point) = W.torsion (ℓ ^ k))
    (hP : ∀ k, ℓ • P (k + 1) = P k) (hQ : ∀ k, ℓ • Q (k + 1) = Q k)
    (x : W.tateModule ℓ) (i : Fin 2) :
    (padicPairBasis hcard hgen hP hQ).repr x i =
      ![((tateModule.padicPairEquiv hcard hgen hP hQ).symm x).1,
        ((tateModule.padicPairEquiv hcard hgen hP hQ).symm x).2] i := by
  rw [padicPairBasis, tateModule.tateModuleBasis, Module.Basis.ofEquivFun_repr_apply]
  rfl

/-- **The level-`k` coordinates are the residues of the `ℓ`-adic ones.**

The whole mathematical content of this file.  It is `padicPairEquiv_apply_coe` — the level-`k`
value of the family attached to `(a, b)` is `(toZModPow k a).val • P k + (toZModPow k b).val • Q k`
— read as a statement about coordinates rather than about points. -/
lemma toZModPow_padicPairBasis_repr
    (hcard : ∀ k, Nat.card (W.torsion (ℓ ^ k)) = ℓ ^ k * ℓ ^ k)
    (hgen : ∀ k, AddSubgroup.closure ({P k, Q k} : Set W.Point) = W.torsion (ℓ ^ k))
    (hP : ∀ k, ℓ • P (k + 1) = P k) (hQ : ∀ k, ℓ • Q (k + 1) = Q k)
    (x : W.tateModule ℓ) (k : ℕ) (i : Fin 2) :
    PadicInt.toZModPow k ((padicPairBasis hcard hgen hP hQ).repr x i) =
      (torsionPairBasis (hcard k) (hgen k)).repr (tateModule.proj k x) i := by
  haveI : NeZero (ℓ ^ k) := ⟨pow_ne_zero k (Fact.out : ℓ.Prime).pos.ne'⟩
  set ab := (tateModule.padicPairEquiv hcard hgen hP hQ).symm x with hab
  have hx : x = tateModule.padicPairEquiv hcard hgen hP hQ ab := by
    rw [hab, LinearEquiv.apply_symm_apply]
  have hproj : ((tateModule.proj k x : W.torsion (ℓ ^ k)) : W.Point) =
      (PadicInt.toZModPow k ab.1).val • P k + (PadicInt.toZModPow k ab.2).val • Q k := by
    conv_lhs => rw [hx]
    exact tateModule.padicPairEquiv_apply_coe hcard hgen hP hQ ab k
  rw [padicPairBasis_repr, torsionPairBasis_repr_eq (hcard k) (hgen k) hproj]
  fin_cases i <;> simp [hab]

/-- **The level projection carries the `ℓ`-adic basis to the level-`k` basis.**  The one statement
that uses coherence of the system, and it uses it only through `padicPairEquiv`. -/
lemma proj_padicPairBasis
    (hcard : ∀ k, Nat.card (W.torsion (ℓ ^ k)) = ℓ ^ k * ℓ ^ k)
    (hgen : ∀ k, AddSubgroup.closure ({P k, Q k} : Set W.Point) = W.torsion (ℓ ^ k))
    (hP : ∀ k, ℓ • P (k + 1) = P k) (hQ : ∀ k, ℓ • Q (k + 1) = Q k) (k : ℕ) (j : Fin 2) :
    tateModule.proj k (padicPairBasis hcard hgen hP hQ j) =
      torsionPairBasis (hcard k) (hgen k) j := by
  haveI : NeZero (ℓ ^ k) := ⟨pow_ne_zero k (Fact.out : ℓ.Prime).pos.ne'⟩
  refine (torsionPairBasis (hcard k) (hgen k)).repr.injective (Finsupp.ext fun i => ?_)
  rw [← toZModPow_padicPairBasis_repr hcard hgen hP hQ, Module.Basis.repr_self,
    Module.Basis.repr_self, Finsupp.single_apply, Finsupp.single_apply]
  split <;> simp

end PadicBasis

/-! ### The determinant character reduces -/

section Galois

variable {S F : Type*} [Field S] [Field F] [DecidableEq F] [Algebra S F] {W' : Affine S}
  [IsAlgClosed F] [(W'⁄F).IsElliptic] {ℓ : ℕ} [Fact ℓ.Prime] {P Q : ℕ → (W'⁄F).Point}

omit [IsAlgClosed F] [(W'⁄F).IsElliptic] in
/-- **The matrix representation reduces entrywise.**  `galoisRepMatrix` and `galoisRepModMatrix`
both have `b.repr (σ • b j) i` for their `(i, j)` entry, so this is
`toZModPow_padicPairBasis_repr` and `proj_padicPairBasis` with the equivariance of the projection
(`proj_galois_smul`) in between. -/
lemma toZModPow_galoisRepMatrix
    (hcard : ∀ k, Nat.card ((W'⁄F).torsion (ℓ ^ k)) = ℓ ^ k * ℓ ^ k)
    (hgen : ∀ k, AddSubgroup.closure ({P k, Q k} : Set (W'⁄F).Point) = (W'⁄F).torsion (ℓ ^ k))
    (hP : ∀ k, ℓ • P (k + 1) = P k) (hQ : ∀ k, ℓ • Q (k + 1) = Q k)
    (σ : F ≃ₐ[S] F) (k : ℕ) (i j : Fin 2) :
    PadicInt.toZModPow k
        ((galoisRepMatrix (padicPairBasis hcard hgen hP hQ) σ :
          Matrix (Fin 2) (Fin 2) ℤ_[ℓ]) i j) =
      (galoisRepModMatrix (torsionPairBasis (hcard k) (hgen k)) σ :
        Matrix (Fin 2) (Fin 2) (ZMod (ℓ ^ k))) i j := by
  haveI : NeZero (ℓ ^ k) := ⟨pow_ne_zero k (Fact.out : ℓ.Prime).pos.ne'⟩
  rw [galoisRepMatrix_apply_coe, galoisRepModMatrix_apply_coe,
    toZModPow_padicPairBasis_repr hcard hgen hP hQ, tateModule.proj_galois_smul,
    proj_padicPairBasis hcard hgen hP hQ]

omit [IsAlgClosed F] [(W'⁄F).IsElliptic] in
/-- **The level-`k` reduction of `det ρ_{E,ℓ}`, from a coherent system.**  The choice-free form is
`toZModPow_coe_galoisDet_of_natCast_ne_zero`. -/
theorem toZModPow_coe_galoisDet
    (hcard : ∀ k, Nat.card ((W'⁄F).torsion (ℓ ^ k)) = ℓ ^ k * ℓ ^ k)
    (hgen : ∀ k, AddSubgroup.closure ({P k, Q k} : Set (W'⁄F).Point) = (W'⁄F).torsion (ℓ ^ k))
    (hP : ∀ k, ℓ • P (k + 1) = P k) (hQ : ∀ k, ℓ • Q (k + 1) = Q k)
    (σ : F ≃ₐ[S] F) (k : ℕ) :
    PadicInt.toZModPow k ((galoisDet (W' := W') (F := F) (ℓ := ℓ) σ : ℤ_[ℓ]ˣ) : ℤ_[ℓ]) =
      ((galoisDetMod (W' := W') (F := F) (ℓ ^ k) σ : (ZMod (ℓ ^ k))ˣ) : ZMod (ℓ ^ k)) := by
  haveI : NeZero (ℓ ^ k) := ⟨pow_ne_zero k (Fact.out : ℓ.Prime).pos.ne'⟩
  rw [coe_galoisDet (padicPairBasis hcard hgen hP hQ) σ,
    ← det_galoisRepModMatrix (torsionPairBasis (hcard k) (hgen k)) σ]
  change _ = ((galoisRepModMatrix (torsionPairBasis (hcard k) (hgen k)) σ :
    Matrix (Fin 2) (Fin 2) (ZMod (ℓ ^ k)))).det
  rw [RingHom.map_det]
  exact congrArg Matrix.det (Matrix.ext fun i j =>
    toZModPow_galoisRepMatrix hcard hgen hP hQ σ k i j)

/-- **`det ρ_{E,ℓ}` read modulo `ℓ^k` is `det ρ_{E,ℓ^k}`**, at every prime `ℓ` with `(2 : F) ≠ 0`
and `(ℓ : F) ≠ 0`, in `ZMod (ℓ ^ k)`.

No basis and no coherent system appears: `exists_compatible_basis_of_natCast_ne_zero` produces one
and `card_torsion_pow_mul_self_of_natCast_ne_zero` the counting hypothesis, and neither side of the
equation mentions either. -/
theorem toZModPow_coe_galoisDet_of_natCast_ne_zero (h2 : (2 : F) ≠ 0)
    (hℓ : (ℓ : F) ≠ 0) (σ : F ≃ₐ[S] F) (k : ℕ) :
    PadicInt.toZModPow k ((galoisDet (W' := W') (F := F) (ℓ := ℓ) σ : ℤ_[ℓ]ˣ) : ℤ_[ℓ]) =
      ((galoisDetMod (W' := W') (F := F) (ℓ ^ k) σ : (ZMod (ℓ ^ k))ˣ) : ZMod (ℓ ^ k)) := by
  haveI : NeZero ℓ := ⟨(Fact.out : ℓ.Prime).pos.ne'⟩
  obtain ⟨P, Q, hgen, hP, hQ⟩ :=
    exists_compatible_basis_of_natCast_ne_zero (W := W'⁄F) h2 (ℓ := ℓ) hℓ
  exact toZModPow_coe_galoisDet
    (card_torsion_pow_mul_self_of_natCast_ne_zero (W := W'⁄F) h2 hℓ) hgen hP hQ σ k

/-- **The same in `(ZMod (ℓ ^ k))ˣ`**: the level-`k` reduction of the unit `det ρ_{E,ℓ}(σ)` is the
unit `det ρ_{E,ℓ^k}(σ)`. -/
theorem toZModPow_galoisDet_of_natCast_ne_zero (h2 : (2 : F) ≠ 0)
    (hℓ : (ℓ : F) ≠ 0) (σ : F ≃ₐ[S] F) (k : ℕ) :
    Units.map (PadicInt.toZModPow k (p := ℓ)).toMonoidHom
        (galoisDet (W' := W') (F := F) (ℓ := ℓ) σ) =
      galoisDetMod (W' := W') (F := F) (ℓ ^ k) σ :=
  Units.ext (toZModPow_coe_galoisDet_of_natCast_ne_zero h2 hℓ σ k)

end Galois

/-! ### Non-vacuity

The curve is this front's standard certificate curve, `y² + y = x³` over `ℚ` base-changed to
`AlgebraicClosure ℚ`, with **`S = ℚ` and not `S = F`** — over `S = F` the group `Gal(F/S)` is
trivial and a certificate about a Galois *representation* says nothing.  This block declares no
fixture of its own (`#1408`).

⚠️ **The index is `ℓ = 2`, and that is the cheap choice rather than the interesting one**:
`Fact (Nat.Prime 2)` is a global instance, so no `Fact` instance is declared here and nothing in
this block can collide with the one
`EllipticCurves.FunctionField.TateDeterminantCyclotomic` declares for its own `ℓ = 5` certificate.
⚠️ It is not a degenerate index for *this* file's statements the way it is for `galoisDetMod 2`:
the level map here lands in `ZMod (2 ^ k)` at every `k`, and `(ZMod (2 ^ k))ˣ` is a subsingleton
only at `k ≤ 1`.

⚠️ **The two `example`s say nothing about either side being non-trivial.**  What they price is the
hypothesis set — that `[IsAlgClosed F]`, `[(W'⁄F).IsElliptic]`, `[Fact ℓ.Prime]`, `(2 : F) ≠ 0` and
`(ℓ : F) ≠ 0` are simultaneously inhabited — and the fact that `h2` discharges `hℓ` at `ℓ = 2`,
which is why `exampleTwo` appears twice. -/

section Nonvacuity

open EllipticCurves.Fixture

private lemma exampleTwo : (2 : AlgClosedQ) ≠ 0 := two_ne_zero

open Classical in
/-- **⚠️ THE CERTIFICATE FOR THIS FILE'S HEADLINE**: `det ρ_{E,2}` read modulo `2 ^ k` is
`det ρ_{E,2^k}`, on a curve that exists, at every level `k`, with both sides written out.
Unconditional. -/
example (σ : AlgClosedQ ≃ₐ[ℚ] AlgClosedQ) (k : ℕ) :
    PadicInt.toZModPow k
        ((galoisDet (W' := y2AddYEqX3 ℚ) (F := AlgClosedQ) (ℓ := 2) σ : ℤ_[2]ˣ) : ℤ_[2]) =
      ((galoisDetMod (W' := y2AddYEqX3 ℚ) (F := AlgClosedQ) (2 ^ k) σ : (ZMod (2 ^ k))ˣ) :
        ZMod (2 ^ k)) :=
  toZModPow_coe_galoisDet_of_natCast_ne_zero exampleTwo exampleTwo σ k

open Classical in
/-- The same in `(ZMod (2 ^ k))ˣ`, on the same curve. -/
example (σ : AlgClosedQ ≃ₐ[ℚ] AlgClosedQ) (k : ℕ) :
    Units.map (PadicInt.toZModPow k (p := 2)).toMonoidHom
        (galoisDet (W' := y2AddYEqX3 ℚ) (F := AlgClosedQ) (ℓ := 2) σ) =
      galoisDetMod (W' := y2AddYEqX3 ℚ) (F := AlgClosedQ) (2 ^ k) σ :=
  toZModPow_galoisDet_of_natCast_ne_zero exampleTwo exampleTwo σ k

end Nonvacuity

end WeierstrassCurve.Affine
