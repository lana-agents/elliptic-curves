/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import EllipticCurves.FunctionField.MulByNGalois

/-!
# `Gal(F(W) / [n]∗F(W)) ≃* E[n]`: the Galois group is the group of translations

`EllipticCurves.FunctionField.MulByNGalois` (`#1233`) closes the Artin sandwich

```
[n]∗F(W)  ⊆  Fixed(E[n])  ⊆  F(W),     [F(W) : [n]∗F(W)] = n² = |E[n]| = [F(W) : Fixed(E[n])]
```

and concludes `IsGalois ([n]∗F(W)) F(W)` at every `3`-smooth `n`.  It then says, in its
`## What is not here`, that *"the Galois **group** is not identified with `E[n]`"*, and that
*"the equality of subfields is **not** the group isomorphism and must not be read as one"*.  The
`n = 2` and `n = 3` files carry the same bullet.  This file supplies the isomorphism, at all three
indices, and those three bullets are retired in the same change.

```
torsionNMulGaloisEquiv : E[n] ≃* (F(W) ≃ₐ[ [n]∗F(W) ] F(W))
```

## ⚠️ The computation rule is the content, not the `≃*`

An abstract multiplicative equivalence between a torsion group and an automorphism group says only
that two finite groups are isomorphic.  What makes this the classical statement is that the map
**is** translation:

```lean
torsionNMulGaloisEquiv … T g = translateAut (T.toAdd : W.Point) g
```

and it holds by `rfl`, because Mathlib's `FixedPoints.toAlgAutMulEquiv` is `MulEquiv.ofBijective` of
`MulSemiringAction.toAlgAut` and the action on `F(W)` is `translateAut` by construction
(`torsionNMul_smul_def`).  The converse reading is
`exists_mem_torsion_translateAut_eq_of_smooth`: **every** `[n]∗F(W)`-automorphism of `F(W)` is
translation by an `n`-torsion point.  Those two statements are what a consumer wants; the `≃*` is
the packaging.

## Why this is short: every input was already merged

Mathlib supplies the engine, `FixedPoints.toAlgAutMulEquiv` (`Mathlib/FieldTheory/Fixed.lean`), and
its three hypotheses are already discharged in this tree at every index:

* the `MulSemiringAction` and the `FaithfulSMul` are unconditional **instances** —
  `EllipticCurves.FunctionField.TranslationActionN` at general `n`,
  `EllipticCurves.FunctionField.TranslationAction` at `n = 2`,
  `EllipticCurves.FunctionField.TranslationActionThree` at `n = 3`;
* `Finite` is `finite_torsionNMul` / `finite_torsionTwoMul` / `finite_torsionThreeMul`, fired as a
  `haveI` inside the definitions because it rests on hypotheses rather than typeclasses — the
  discipline those three docstrings ask for, so no `Fintype` is named in any statement below.

What Mathlib gives has `FixedPoints.subfield (E[n]) F(W)` as its base field, and the sandwich
theorems `fixedPoints_subfield_eq_mulByNEndoFieldRange` (`#1233`),
`fixedPoints_subfield_eq_mulByTwoEndoFieldRange` (`#759`) and
`fixedPoints_subfield_eq_mulByThreeEndoFieldRange` (`#775`) say that subfield **is** `[n]∗F(W)`.  So
the only thing that had to be built is `Subfield.autMulEquivOfEq`, below.

## `Subfield.autMulEquivOfEq` is curve-free, and Mathlib has no name for it

`S = T` in `Subfield K` gives `(K ≃ₐ[S] K) ≃* (K ≃ₐ[T] K)`.  ⚠️ Grepped before writing it:
`AlgEquiv.autCongr` moves the **top** field over a fixed base and is not this;
`IntermediateField.equivOfEq` is an `AlgEquiv` between the two subfields themselves, not between
their automorphism groups; and there is no hit for a base-changing `autCongr` anywhere in Mathlib.
The section that holds it says in its own docstring that nothing about elliptic curves enters, and
it is an upstream candidate.

## ⚠️ The two presentations of `[n]∗F(W)` give the *same type* here — no second declaration

`[n]∗F(W)` appears in this tree as an `IntermediateField` (`(mulByNEndoAlgHom n h).fieldRange`) and
as a `Subfield` (`(mulByNEndo n h).fieldRange`), and `EllipticCurves.FunctionField.MulByNGalois`
needs a `Normal.of_equiv_equiv` to carry normality between them.  **The automorphism groups need
nothing**: `F(W) ≃ₐ[↥(mulByNEndoAlgHom n h).fieldRange] F(W)` and
`F(W) ≃ₐ[↥(mulByNEndo n h).fieldRange] F(W)` are definitionally equal, which is *committed* as an
`example` below rather than asserted.  So there is deliberately **no** `IntermediateField` twin of
any declaration here — a second name for a definitionally equal type is the noise `#699` exists to
remove — and a consumer holding the `IntermediateField` form applies the `Subfield` names directly.

## ⚠️ `n = 2` and `n = 3` are not instances of the general `n`, and must not be derived from it

`mulByTwoEndo h2` and `mulByNEndo 2 h` are different terms, and the general-`n` results carry
`(3 : F) ≠ 0` in addition, because Artin's right-hand side runs through
`card_torsion_eq_sq_of_smooth`.  This is the same asymmetry `isGalois_mulByNFieldRange_two`'s
docstring records of the `IsGalois` package, and it is exactly why the `n = 2` and `n = 3` bullets
could not have been retired by the general-`n` statement alone.  The two low-index equivalences
below are therefore built from the merged `n = 2` and `n = 3` sandwiches, at the merged (weaker)
hypotheses, and each is **sharper** than the general-`n` one at its index.

## Main definitions

Every public declaration of this file is listed, here and under `## Main statements`.
`Subfield.autMulEquivOfEq` and its two `apply` lemmas are in namespace `Subfield`; everything else
is in namespace `WeierstrassCurve.Affine.CoordinateRing`.

* `Subfield.autMulEquivOfEq` — transport of `Aut K` along an equality of base subfields;
* `torsionNMulGaloisEquiv` — `E[n] ≃* Gal(F(W) / [n]∗F(W))` at every `3`-smooth `n ≠ 0`;
* `torsionTwoMulGaloisEquiv`, `torsionThreeMulGaloisEquiv` — the same at `n = 2` and `n = 3`, at the
  merged hypotheses.

## Main statements

* `Subfield.autMulEquivOfEq_apply` and `Subfield.autMulEquivOfEq_symm_apply` — the transport is the
  identity on underlying functions;
* `torsionNMulGaloisEquiv_apply`, `torsionTwoMulGaloisEquiv_apply`,
  `torsionThreeMulGaloisEquiv_apply` — the isomorphism **is** translation, by `rfl`;
* `exists_mem_torsion_translateAut_eq_of_smooth`, `exists_mem_torsion_two_translateAut_eq`,
  `exists_mem_torsion_three_translateAut_eq` — the converse: every automorphism over `[n]∗F(W)` is
  translation by an `n`-torsion point;
* `card_galoisGroup_mulByNEndoFieldRange` — `|Gal(F(W) / [n]∗F(W))| = n²`, with
  `card_galoisGroup_mulByTwoEndoFieldRange` and `card_galoisGroup_mulByThreeEndoFieldRange` giving
  the values `4` and `9` at `n = 2` and `n = 3`.

## What is *not* here

* **Nothing at `n = 5`.**  Both sides of Artin's theorem are `3`-smooth and a group isomorphism
  manufactures no new prime.
* **Not `Gal(F(W) / F(x)) ≃* ⟨ι⟩`.**  It is a different fixed-point setup in a different file and
  is untouched here — but it is no longer absent from the tree: ⚠️ **this bullet used to end**
  *"`Subfield.autMulEquivOfEq` is what it would consume"*, and
  `EllipticCurves.FunctionField.NegYGaloisGroup` now consumes it, in
  `negYGroupGaloisEquiv`.  ⚠️ That file needs one step this one did not: its merged sandwich
  `ratFuncRange_eq_fixedField_negYGroup` is an `IntermediateField` equality, so it drops to the
  `Subfield` level by `SetLike.ext` before the helper applies.  ⚠️ **And it is sharper in one
  respect than anything here**: it carries neither `[IsAlgClosed F]` nor a condition on the
  characteristic, so it holds in characteristic `2`, where every statement in this file is
  unavailable.
* **No `#E[n] = n²` from a degree.**  `card_torsionNMul` is an **input**, proved by the torsion
  route in `EllipticCurves.Torsion.ThreePrimary`.  Six merged files record that *"a separable
  isogeny has as many points in its kernel as its degree"* is absent from this tree and all six are
  still right; putting the count and the degree into one `≃*` supplies none of it, and the
  temptation to read one off the other is exactly the one
  `EllipticCurves.FunctionField.MulByNGalois` warns about.
* **No Galois correspondence** — no lattice of intermediate fields, no
  `IntermediateField.fixingSubgroup` statements, nothing about subgroups of `E[n]`.
* **Nothing about places, divisors, ramification, the Weil pairing or `hprin`** (`#962`).

## ⚠️ One merged docstring was read and deliberately **not** amended

`EllipticCurves.FunctionField.MulByNSeparable`'s heading says the statement `IsGalois ([n]∗F(W))
F(W)` is true *"with Galois group `E[n]` acting by translation"*.  That is a description of the
mathematics and was true when it was written; nothing in it is falsified by this file, so it is a
pointer that could be added rather than a claim that must be retired, and it is left alone.  The
three sentences that *are* retired below all begin *"is not identified with"* — claims about the
tree, which this file makes false.

## References

* [J. H. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.4.
* Artin's theorem on fixed fields, [stacks 09I3].
-/

open Module Polynomial

/-! ### Transport of the automorphism group along an equality of base subfields

⚠️ **Nothing about elliptic curves enters this section.**  It is stated for an arbitrary field `K`
and an arbitrary pair of equal subfields, and it is an upstream candidate: Mathlib has
`AlgEquiv.autCongr` for a change of the *top* field and `IntermediateField.equivOfEq` for an
`AlgEquiv` between the subfields themselves, but nothing that moves the base of an automorphism
group along an equality. -/

namespace Subfield

variable {K : Type*} [Field K] {S T : Subfield K}

/-- **Equal base subfields give isomorphic automorphism groups**, by the identity on underlying
functions.

An `S`-algebra automorphism of `K` is a ring automorphism that fixes `S` pointwise, and `S = T` says
the two subsets are the same, so nothing is transported except the proof obligation.  The
`MulEquiv` is therefore built out of `AlgEquiv.ofRingEquiv` in both directions and all three
coherence fields are `rfl`. -/
def autMulEquivOfEq (hST : S = T) : (K ≃ₐ[↥S] K) ≃* (K ≃ₐ[↥T] K) where
  toFun e := AlgEquiv.ofRingEquiv (f := (e : K ≃+* K)) fun r => e.commutes ⟨r, hST.ge r.2⟩
  invFun e := AlgEquiv.ofRingEquiv (f := (e : K ≃+* K)) fun r => e.commutes ⟨r, hST.le r.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

@[simp] lemma autMulEquivOfEq_apply (hST : S = T) (e : K ≃ₐ[↥S] K) (x : K) :
    autMulEquivOfEq hST e x = e x := rfl

@[simp] lemma autMulEquivOfEq_symm_apply (hST : S = T) (e : K ≃ₐ[↥T] K) (x : K) :
    (autMulEquivOfEq hST).symm e x = e x := rfl

end Subfield

namespace WeierstrassCurve.Affine

namespace CoordinateRing

variable {F : Type*} [Field F] {W : Affine F} [W.IsElliptic]

/-! ### The Galois group at every `3`-smooth `n` -/

open Classical in
/-- **`Gal(F(W) / [n]∗F(W)) ≃* E[n]` at every `3`-smooth `n ≠ 0`**, over an algebraically closed
base field of characteristic `≠ 2, 3` — the identification
`EllipticCurves.FunctionField.MulByNGalois` records as missing, on top of the sandwich it proves.

`FixedPoints.toAlgAutMulEquiv` gives `E[n] ≃* (F(W) ≃ₐ[Fixed(E[n])] F(W))` from the action, its
faithfulness and its finiteness; `fixedPoints_subfield_eq_mulByNEndoFieldRange` says the base is
`[n]∗F(W)`; `Subfield.autMulEquivOfEq` moves it there.

⚠️ The `Finite` instance is fired as a `haveI` inside the definition and never appears in the
statement, which is what `finite_torsionNMul`'s docstring asks for.  ⚠️ See
`torsionNMulGaloisEquiv_apply`: the map is translation, and that is the content. -/
noncomputable def torsionNMulGaloisEquiv [IsAlgClosed F] (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0)
    {n : ℕ} (hn : n ≠ 0) (hfac : ∀ p ∈ n.primeFactors, p = 2 ∨ p = 3)
    (h : Transcendental F (n • genericPoint (W := W)).xCoord) :
    TorsionNMul W n ≃*
      (W.FunctionField ≃ₐ[↥(mulByNEndo (W := W) n h).fieldRange] W.FunctionField) :=
  haveI := finite_torsionNMul (W := W) h2 h3 hn hfac
  (FixedPoints.toAlgAutMulEquiv (TorsionNMul W n) W.FunctionField).trans
    (Subfield.autMulEquivOfEq (fixedPoints_subfield_eq_mulByNEndoFieldRange h2 h3 hn hfac h))

open Classical in
/-- **The isomorphism is translation.**  True by `rfl`: `FixedPoints.toAlgAutMulEquiv` is
`MulEquiv.ofBijective` of `MulSemiringAction.toAlgAut`, `torsionNMul_smul_def` says the action of
`E[n]` on `F(W)` is `translateAut`, and `Subfield.autMulEquivOfEq` changes no underlying function.

⚠️ This is the statement that distinguishes the classical theorem from *"two finite groups of the
same order"*. -/
@[simp] lemma torsionNMulGaloisEquiv_apply [IsAlgClosed F] (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0)
    {n : ℕ} (hn : n ≠ 0) (hfac : ∀ p ∈ n.primeFactors, p = 2 ∨ p = 3)
    (h : Transcendental F (n • genericPoint (W := W)).xCoord) (T : TorsionNMul W n)
    (g : W.FunctionField) :
    torsionNMulGaloisEquiv h2 h3 hn hfac h T g = translateAut (T.toAdd : W.Point) g := rfl

open Classical in
/-- **Every `[n]∗F(W)`-automorphism of `F(W)` is translation by an `n`-torsion point** — the
surjectivity half, in the form a consumer that holds a `σ` and wants a point reaches for.

The `n`-torsion point is unique, by `translateAut_injective`
(`EllipticCurves.FunctionField.TranslationAction`); uniqueness is not restated here because it is
`n`-agnostic and already merged. -/
theorem exists_mem_torsion_translateAut_eq_of_smooth [IsAlgClosed F] (h2 : (2 : F) ≠ 0)
    (h3 : (3 : F) ≠ 0) {n : ℕ} (hn : n ≠ 0) (hfac : ∀ p ∈ n.primeFactors, p = 2 ∨ p = 3)
    (h : Transcendental F (n • genericPoint (W := W)).xCoord)
    (σ : W.FunctionField ≃ₐ[↥(mulByNEndo (W := W) n h).fieldRange] W.FunctionField) :
    ∃ P ∈ W.torsion n, ∀ g : W.FunctionField, σ g = translateAut P g := by
  classical
  obtain ⟨T, hT⟩ := (torsionNMulGaloisEquiv h2 h3 hn hfac h).surjective σ
  exact ⟨(T.toAdd : W.Point), T.toAdd.2, fun g => by rw [← hT]; rfl⟩

open Classical in
/-- **`|Gal(F(W) / [n]∗F(W))| = n²`.**  `Nat.card` off the equivalence and `card_torsionNMul`.

⚠️ This is a *transport* of the merged count, not a second proof of it: `card_torsionNMul` runs
through `card_torsion_eq_sq_of_smooth` and nothing here reads `n²` off the degree
`[F(W) : [n]∗F(W)]`.  Six merged files record that the step *"a separable isogeny has as many points
in its kernel as its degree"* is absent from this tree, and this statement does not supply it. -/
theorem card_galoisGroup_mulByNEndoFieldRange [IsAlgClosed F] (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0)
    {n : ℕ} (hn : n ≠ 0) (hfac : ∀ p ∈ n.primeFactors, p = 2 ∨ p = 3)
    (h : Transcendental F (n • genericPoint (W := W)).xCoord) :
    Nat.card (W.FunctionField ≃ₐ[↥(mulByNEndo (W := W) n h).fieldRange] W.FunctionField) = n ^ 2 :=
  (Nat.card_congr (torsionNMulGaloisEquiv h2 h3 hn hfac h).toEquiv).symm.trans
    (card_torsionNMul h2 h3 hn hfac)

open Classical in
/-- ⚠️ **The `IntermediateField` and `Subfield` presentations give the same automorphism group, and
this commits it.**  `EllipticCurves.FunctionField.MulByNGalois` needs `Normal.of_equiv_equiv` to
carry normality between the two presentations of `[n]∗F(W)`; the automorphism groups need nothing,
being definitionally equal.  That is why no declaration above has an `IntermediateField` twin. -/
example {n : ℕ} [IsAlgClosed F] (h : Transcendental F (n • genericPoint (W := W)).xCoord) :
    (W.FunctionField ≃ₐ[↥(mulByNEndoAlgHom (W := W) n h).fieldRange] W.FunctionField)
      = (W.FunctionField ≃ₐ[↥(mulByNEndo (W := W) n h).fieldRange] W.FunctionField) := rfl

/-! ### `n = 2` and `n = 3` at the merged hypotheses

⚠️ Neither is an instance of the general-`n` equivalence: `mulByTwoEndo h2` and `mulByNEndo 2 h` are
different terms, and the general-`n` route additionally carries `(3 : F) ≠ 0`.  Each of the two
below is **sharper** than the general statement at its index, and each is what retires its own
file's `## What is not here` bullet. -/

open Classical in
/-- **`Gal(F(W) / [2]∗F(W)) ≃* E[2]`**, needing only `(2 : F) ≠ 0` — sharper at `n = 2` than
`torsionNMulGaloisEquiv`, which also needs `(3 : F) ≠ 0`. -/
noncomputable def torsionTwoMulGaloisEquiv [IsAlgClosed F] (h2 : (2 : F) ≠ 0) :
    TorsionTwoMul W ≃*
      (W.FunctionField ≃ₐ[↥(mulByTwoEndo (W := W) h2).fieldRange] W.FunctionField) :=
  haveI := finite_torsionTwoMul (W := W) h2
  (FixedPoints.toAlgAutMulEquiv (TorsionTwoMul W) W.FunctionField).trans
    (Subfield.autMulEquivOfEq (fixedPoints_subfield_eq_mulByTwoEndoFieldRange h2))

open Classical in
/-- The `n = 2` isomorphism is translation, by `rfl`. -/
@[simp] lemma torsionTwoMulGaloisEquiv_apply [IsAlgClosed F] (h2 : (2 : F) ≠ 0)
    (T : TorsionTwoMul W) (g : W.FunctionField) :
    torsionTwoMulGaloisEquiv h2 T g = translateAut (T.toAdd : W.Point) g := rfl

open Classical in
/-- Every `[2]∗F(W)`-automorphism of `F(W)` is translation by a `2`-torsion point. -/
theorem exists_mem_torsion_two_translateAut_eq [IsAlgClosed F] (h2 : (2 : F) ≠ 0)
    (σ : W.FunctionField ≃ₐ[↥(mulByTwoEndo (W := W) h2).fieldRange] W.FunctionField) :
    ∃ P ∈ W.torsion 2, ∀ g : W.FunctionField, σ g = translateAut P g := by
  classical
  obtain ⟨T, hT⟩ := (torsionTwoMulGaloisEquiv h2).surjective σ
  exact ⟨(T.toAdd : W.Point), T.toAdd.2, fun g => by rw [← hT]; rfl⟩

open Classical in
/-- **`|Gal(F(W) / [2]∗F(W))| = 4`.** -/
theorem card_galoisGroup_mulByTwoEndoFieldRange [IsAlgClosed F] (h2 : (2 : F) ≠ 0) :
    Nat.card (W.FunctionField ≃ₐ[↥(mulByTwoEndo (W := W) h2).fieldRange] W.FunctionField) = 4 :=
  (Nat.card_congr (torsionTwoMulGaloisEquiv h2).toEquiv).symm.trans (card_torsionTwoMul h2)

open Classical in
/-- **`Gal(F(W) / [3]∗F(W)) ≃* E[3]`**, at the merged `n = 3` hypotheses. -/
noncomputable def torsionThreeMulGaloisEquiv [IsAlgClosed F] (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) :
    TorsionThreeMul W ≃*
      (W.FunctionField ≃ₐ[↥(mulByThreeEndo (W := W) h2 h3).fieldRange] W.FunctionField) :=
  haveI := finite_torsionThreeMul (W := W) h2 h3
  (FixedPoints.toAlgAutMulEquiv (TorsionThreeMul W) W.FunctionField).trans
    (Subfield.autMulEquivOfEq (fixedPoints_subfield_eq_mulByThreeEndoFieldRange h2 h3))

open Classical in
/-- The `n = 3` isomorphism is translation, by `rfl`. -/
@[simp] lemma torsionThreeMulGaloisEquiv_apply [IsAlgClosed F] (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0)
    (T : TorsionThreeMul W) (g : W.FunctionField) :
    torsionThreeMulGaloisEquiv h2 h3 T g = translateAut (T.toAdd : W.Point) g := rfl

open Classical in
/-- Every `[3]∗F(W)`-automorphism of `F(W)` is translation by a `3`-torsion point. -/
theorem exists_mem_torsion_three_translateAut_eq [IsAlgClosed F] (h2 : (2 : F) ≠ 0)
    (h3 : (3 : F) ≠ 0)
    (σ : W.FunctionField ≃ₐ[↥(mulByThreeEndo (W := W) h2 h3).fieldRange] W.FunctionField) :
    ∃ P ∈ W.torsion 3, ∀ g : W.FunctionField, σ g = translateAut P g := by
  classical
  obtain ⟨T, hT⟩ := (torsionThreeMulGaloisEquiv h2 h3).surjective σ
  exact ⟨(T.toAdd : W.Point), T.toAdd.2, fun g => by rw [← hT]; rfl⟩

open Classical in
/-- **`|Gal(F(W) / [3]∗F(W))| = 9`.** -/
theorem card_galoisGroup_mulByThreeEndoFieldRange [IsAlgClosed F] (h2 : (2 : F) ≠ 0)
    (h3 : (3 : F) ≠ 0) :
    Nat.card (W.FunctionField ≃ₐ[↥(mulByThreeEndo (W := W) h2 h3).fieldRange] W.FunctionField)
      = 9 :=
  (Nat.card_congr (torsionThreeMulGaloisEquiv h2 h3).toEquiv).symm.trans
    (card_torsionThreeMul h2 h3)

/-! ### Non-vacuity

The headline needs `[IsAlgClosed F]`, `[W.IsElliptic]`, `(2 : F) ≠ 0`, `(3 : F) ≠ 0`, `n ≠ 0`,
`3`-smoothness and the transcendence of `x([n]𝒫)` at once, and its value is a group whose order is
computed rather than assumed — so a curve on which the whole chain elaborates is committed rather
than quoted.  The curve is `y² + y = x³` over `AlgebraicClosure ℚ` and the index is `n = 12`,
following `EllipticCurves.FunctionField.MulByNGalois`: a certificate at `n = 2` or `n = 3` would
prove nothing about a general-`n` file.  ⚠️ Every hypothesis is **produced**, not assumed. -/

section Nonvacuity

/-- An algebraically closed field of characteristic zero. -/
private abbrev exampleField : Type := AlgebraicClosure ℚ

/-- The curve `y² + y = x³` over `AlgebraicClosure ℚ`, of discriminant `−27`. -/
private noncomputable def exampleCurveGaloisGroup : Affine exampleField := ⟨0, 0, 1, 0, 0⟩

private instance : exampleCurveGaloisGroup.IsElliptic := by
  rw [WeierstrassCurve.isElliptic_iff, isUnit_iff_ne_zero]
  norm_num [exampleCurveGaloisGroup, WeierstrassCurve.Δ, WeierstrassCurve.b₂,
    WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]

private lemma exampleTwo : (2 : exampleField) ≠ 0 := by norm_num

private lemma exampleThree : (3 : exampleField) ≠ 0 := by norm_num

/-- ⚠️ `decide` does **not** close this: `Nat.primeFactors` goes through `Nat.primeFactorsList`,
whose `Decidable` instance gets stuck on `Nat.minFac`'s well-founded recursion. -/
private lemma exampleSmoothTwelve : ∀ p ∈ Nat.primeFactors 12, p = 2 ∨ p = 3 := by
  intro p hp
  obtain ⟨hp1, hp2, -⟩ := Nat.mem_primeFactors.mp hp
  have hle : p ≤ 12 := Nat.le_of_dvd (by norm_num) hp2
  interval_cases p <;> revert hp1 hp2 <;> decide

private lemma exampleTranscendentalTwelve :
    Transcendental exampleField
      ((12 : ℕ) • genericPoint (W := exampleCurveGaloisGroup)).xCoord :=
  transcendental_xCoord_nsmul_of_isAlgClosed exampleTwo (by norm_num)

open Classical in
/-- **The group identification on a genuine curve at `n = 12`.** -/
noncomputable example : TorsionNMul exampleCurveGaloisGroup 12 ≃*
    (exampleCurveGaloisGroup.FunctionField ≃ₐ[↥(mulByNEndo (W := exampleCurveGaloisGroup) 12
      exampleTranscendentalTwelve).fieldRange] exampleCurveGaloisGroup.FunctionField) :=
  torsionNMulGaloisEquiv exampleTwo exampleThree (by norm_num) exampleSmoothTwelve
    exampleTranscendentalTwelve

open Classical in
/-- **`|Gal(F(W) / [12]∗F(W))| = 144` on a genuine curve.** -/
example : Nat.card (exampleCurveGaloisGroup.FunctionField ≃ₐ[↥(mulByNEndo
    (W := exampleCurveGaloisGroup) 12 exampleTranscendentalTwelve).fieldRange]
    exampleCurveGaloisGroup.FunctionField) = 144 :=
  card_galoisGroup_mulByNEndoFieldRange exampleTwo exampleThree (by norm_num) exampleSmoothTwelve
    exampleTranscendentalTwelve

open Classical in
/-- **Every automorphism over `[12]∗F(W)` is a translation**, committed on the same curve. -/
example (σ : exampleCurveGaloisGroup.FunctionField ≃ₐ[↥(mulByNEndo
    (W := exampleCurveGaloisGroup) 12 exampleTranscendentalTwelve).fieldRange]
    exampleCurveGaloisGroup.FunctionField) :
    ∃ P ∈ exampleCurveGaloisGroup.torsion 12,
      ∀ g : exampleCurveGaloisGroup.FunctionField, σ g = translateAut P g :=
  exists_mem_torsion_translateAut_eq_of_smooth exampleTwo exampleThree (by norm_num)
    exampleSmoothTwelve exampleTranscendentalTwelve σ

end Nonvacuity

end CoordinateRing

end WeierstrassCurve.Affine
