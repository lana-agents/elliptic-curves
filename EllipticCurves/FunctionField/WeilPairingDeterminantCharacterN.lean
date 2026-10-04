/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import EllipticCurves.Fixtures
import EllipticCurves.FunctionField.WeilPairingDeterminantN
import EllipticCurves.FunctionField.WeilPairingRationalTorsionGalois
import EllipticCurves.TateModule.DeterminantMod

/-!
# `galoisDetMod n = χ_n` as an identity of monoid homomorphisms, at a general index

The bundled reading of `EllipticCurves.FunctionField.WeilPairingDeterminantN` (`#2281`).  That file
has the identification **in coordinates**: for a **primitive** pairing pair `(P, T)` — one with
`orderOf (e_n(P, T)) = n` — and a quadruple of integers carried in hypotheses,
`a * d − b * c ≡ χ_n(σ) (mod n)`.  This file has the form a consumer actually holds, at which the
pair disappears from the statement:

```
galoisDetMod n = galoisModularCyclotomicChar S F hn'   as monoid homs  (F ≃ₐ[S] F) →* (ZMod n)ˣ.
```

⚠️ **The choice of `(P, T)` is invisible in the conclusion, and that is the whole point of the
file.**  `LinearEquiv.det` is basis-free, so the headline quantifies over nothing but the curve and
the field, where `#2281`'s statements quantify over a pair and a matrix as well.  Bases exist below
only to *compute* the determinant, inside proofs; no statement mentions one.  A primitive pair
exists unconditionally in this setting — `exists_orderOf_weilPairingN_eq` — which is what lets the
hypothesis be **discharged** rather than assumed.

At `n = 3` this rung is `EllipticCurves.FunctionField.WeilPairingDeterminantCharacter` (`#958`), and
this file is that one with the index freed.  ⚠️ **It is not a transcription of it**, and the two
paragraphs below are where it parts company.

## ⚠️ `#958`'s route to the basis is a DIVISION-RING route and it does not survive a composite index

`#958` builds its coordinate isomorphism from **surjectivity alone**: `(P, T)` spans, and
`LinearMap.injective_iff_surjective_of_finrank_eq_finrank` upgrades that to bijectivity off the
rank.  ⚠️ **That lemma is stated over a `DivisionRing` and there is nothing to put in its place at a
composite index.**  Mathlib declares it in `Mathlib/LinearAlgebra/FiniteDimensional/Lemmas.lean`
under `variable [DivisionRing K] … [FiniteDimensional K V] [FiniteDimensional K V₂]`, and `ZMod n`
is a division ring exactly when `n` is prime — so at `n = 3` the route runs and at `n = 4` there is
no ring to run it over.  The rank statement itself survives
(`finrank_torsion_of_natCast_ne_zero`, `EllipticCurves.TateModule.DeterminantModGeneral`); what does
not survive is the implication *rank equal ⇒ surjective gives injective*.

So **injectivity is proved here, not deduced**, and its input is `#2281`'s independence lemma
`intCast_eq_zero_of_zsmul_add_zsmul_eq_zero_n` used by name.  ⚠️ **That inverts `#958`'s own
caveat rather than repeating it**: `#958` warns that it *looks* independent of the independence
lemma and is not, because `exists_zsmul_add_zsmul_eq_three` consumes it one level down.  Here the
lemma is cited at this level, so the caveat has nothing to correct — and the one thing `#958`'s
rank argument bought, that injectivity is not re-derived, is exactly what is given up.

## ⚠️ And the consequence is that no `1 < n` is bound anywhere in this file

`#958`'s route needs the rank, the rank needs `Fact (1 < n)`, and `1 < n` would then be a hypothesis
of the headline.  Proving injectivity from the independence lemma needs neither, and
`LinearMap.det_toMatrix` — which is what reduces the bundled determinant to a matrix one — asks for
a basis and for nothing else, no `Module.Free` and no `Module.Finite` instance.  **So the headline
holds at every `n` with `(2 : F) ≠ 0` and `((n : ℤ) : F) ≠ 0` over an algebraically closed `F`, with
`n = 1` and `n = 2` included rather than excluded.**  ⚠️ No *rank* is claimed below and none may be
read off `basisTorsionNOfPairing`: it is indexed by `Fin 2` at every such `n`, and at `n = 1` the
coefficient ring `ZMod 1` is the zero ring, which has no invariant basis number.
`finrank_torsion_of_natCast_ne_zero` binds `1 < n` for that reason and is consumed nowhere here.

## ⚠️ `EllipticCurves.TateModule.DeterminantModGeneral` is NOT imported, and that is measured

No name of it is used, so it is not imported — the import discipline
`EllipticCurves.FunctionField.WeilPairingDeterminantCharacter` states for its own three imports.
Measured over project modules only, at the head this file was written against (`7ba33ed`), counting
each module's own import closure including itself: this file reaches **242** modules and
`DeterminantModGeneral` reaches **73**, and the two are **incomparable** — exactly **2** modules lie
in the second closure and not in the first, namely `DeterminantModGeneral` itself and
`EllipticCurves.TateModule.DeterminantModSmooth`.

⚠️ **The claim that file makes is nonetheless discharged, and here rather than there.**  What
`DeterminantModGeneral` supplies is that `E[n]` is free of rank `2` over `ZMod n`, so that
`galoisDetMod n` is an honest determinant and not `LinearEquiv.det`'s value on a module it cannot
see.  `basisTorsionNOfPairing` below **is** a `Fin 2`-indexed `ZMod n`-basis of `E[n]`, produced
from a pair that exists unconditionally, so freeness is exhibited in this file at strictly fewer
hypotheses than the rank statement carries.

## The route, and the one thing that makes it short

`#2281` supplies, for each `σ` and each primitive `(P, T)`, integers `a b c d` with
`σ • P = a • P + c • T`, `σ • T = b • P + d • T` and `a * d − b * c ≡ χ_n(σ)`.  What is needed is
that the *bundled* determinant of `ρ_{E,n}(σ)` is that same number, and Mathlib reduces the
determinant of a bundled map to the determinant of a matrix by `LinearMap.det_toMatrix` — for
**any** basis.  So the work is: manufacture one basis out of `(P, T)`, identify the matrix, and take
`Matrix.det_fin_two_of`.

⚠️ **No abstract `e_n(α x, α y) = e_n(x, y) ^ det α` is needed.**
`EllipticCurves.FunctionField.WeilPairingDeterminantLinear`'s own docstring records that such a
statement (`#957`, proved at `n = 3`) is *"a genuine generalisation with no consumer"* and a detour,
because `LinearMap.det_toMatrix` already performs the reduction.  ⚠️ Its docstring also says its
*prospective* value is that *"a general-`n` or `ℓ`-adic treatment wanting the transformation law
without a Galois group has to prove exactly this"* — that is a claim about a **different**
statement, and it is not a claim that this file needs the `n = 3` file or a general-`n` version of
it.  Nothing below names either.

⚠️ **The `ℤ`-to-`ZMod n` scalar bridge is `Int.cast_smul_eq_zsmul`**, at three call sites:
`torsionNCoord_surjective`, `zmod_smul_torsion` (which is where injectivity meets `#2281`'s
`ℤ`-scalar hypotheses) and the column computation inside
`coe_galoisDetMod_n_eq_galoisModularCyclotomicChar`.

## ⚠️ The two-layer split of the headline is forced by `Units`

`galoisDetMod` lands in `(ZMod n)ˣ` and `#2281`'s equation lives in `ZMod n`.  `Units.ext` is what
crosses between them, so the bridge is stated on the **coercion** and the unit-level statement is
its one-line consequence.  Trying to run the matrix computation directly in `(ZMod n)ˣ` means
carrying `Units.val` through `Matrix.det_fin_two_of`, and there is no reason to.

## Main definitions

* `WeierstrassCurve.Affine.torsionNCoord` — `(a, b) ↦ a • P + b • T`, as a `ZMod n`-linear map
  `(Fin 2 → ZMod n) →ₗ[ZMod n] E[n]`.  ⚠️ `ZMod n`-linearity of an additive map is free: `E[n]` is a
  `ZMod n`-module through `torsionZModModule`, which is `AddCommGroup.zmodModule` applied to
  `nsmul_mem_torsion` and carries no hypothesis beyond `[NeZero n]`.
* `WeierstrassCurve.Affine.torsionNPairingEquiv` — the same map, bijective at a primitive pair.
* `WeierstrassCurve.Affine.basisTorsionNOfPairing` — `(P, T)` as a `ZMod n`-basis of `E[n]`.

## Main statements

* `WeierstrassCurve.Affine.coe_galoisDetMod_n_eq_galoisModularCyclotomicChar` — the identity in
  `ZMod n`, for a fixed `σ`.
* `WeierstrassCurve.Affine.galoisDetMod_n_apply_eq_galoisModularCyclotomicChar` — the same in
  `(ZMod n)ˣ`.
* `WeierstrassCurve.Affine.galoisDetMod_n_eq_galoisModularCyclotomicChar` — **the headline**,
  `det ρ_{E,n} = χ_n` as an equation between monoid homomorphisms.
* `WeierstrassCurve.Affine.galoisDetMod_n_ne_one_of_galoisModularCyclotomicChar_ne_one` — the form
  that turns a `σ` with `χ_n(σ) ≠ 1` into a statement about the determinant.

## ⚠️ `n = 2` and `n = 1` are subsumed, not excluded

`galoisDetMod 2 = χ_2` is **content-free**: `(ZMod 2)ˣ` is a subsingleton, so both sides are
constantly `1` and the equation holds of any pair of characters into it
(`galoisModularCyclotomicChar_two_eq_one`,
`EllipticCurves.FunctionField.WeilPairingFunctionCyclotomic`).  `#1243` declines to state the matrix
form at `n = 2` for exactly that reason.  At `n = 1` every group in sight is trivial.  ⚠️ **A
general-`n` statement subsumes a degenerate index rather than omitting it**, so nothing is excluded
below — and nothing below may be read as *strengthening* anything at those two indices, where there
is nothing to strengthen.

## Layering

This file is under `FunctionField/` because it consumes the Weil pairing.  ⚠️ It **cannot** move
under `TateModule/`: nothing under `TateModule/` imports anything under `FunctionField/`, and
`EllipticCurves.TateModule.DeterminantMod` records that this is deliberate.  Grepped in both
directions at `7ba33ed`, the head this file was written against:
`grep -rn 'import EllipticCurves.FunctionField' EllipticCurves/TateModule/` returns **0** lines, and
this file's own imports cross the other way only.  It is a **leaf**; nothing under `TateModule/`
may import it.

## Explicitly out of scope

* **The `ℓ`-adic statement.**  The index here is a single `n`, not a tower, so
  `galoisDet = χ_ℓ` over `ℤ_[ℓ]` is not stated here.  ⚠️ **It is no longer out of reach, and this
  bullet used to say so** — it read *"`galoisDetTwo = χ_2` over `ℤ_[2]` needs the pairing on
  `E[2 ^ k]` for every `k` and is untouched"*.  Both halves are spent:
  `EllipticCurves.FunctionField.TateDeterminantCyclotomic` consumes the headline below at **every**
  index `ℓ ^ k`, which is exactly the *"pairing on `E[2 ^ k]` for every `k`"* the clause named, and
  glues the levels by `EllipticCurves.TateModule.PrimaryDeterminantLevel`.  The retirement is
  recorded once, at `galoisDet` in `EllipticCurves.TateModule.PrimaryDeterminant`.
* **A `Gal(F/S)`-stable basis.**  Does not exist in general and is not needed; see the note above on
  why the headline mentions no basis.
* **The trace and the characteristic polynomial** mod `n`.  No consumer.
* **The matrix form.**  `det ∘ ρ_{E,n} = χ_n` for `galoisRepModMatrix` is
  `EllipticCurves.FunctionField.MatrixRepDeterminantCharacterN`, which imports this file.

## References

* [J. H. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.8.1(a), (b), (d), and
  III.8.6.  ⚠️ **This identity is not a numbered result there and in particular it is not
  III.8.1(e)**, which is the compatibility relation; the five letters are tabulated verbatim in
  `EllipticCurves.FunctionField.WeilPairing`.
-/
namespace WeierstrassCurve.Affine

open CoordinateRing

/-! ### A `ZMod n`-basis of `E[n]` from a primitive pairing pair -/

section PairingBasis

variable {F : Type*} [Field F] [IsAlgClosed F] {W : Affine F} [W.IsElliptic] {n : ℕ} [NeZero n]

open Classical in
/-- **The map `(a, b) ↦ a • P + b • T`** on `E[n]`, as a `ZMod n`-linear map out of
`Fin 2 → ZMod n`.

Nothing is assumed about `P` and `T`: this is `Fintype.linearCombination` against the family
`![P, T]`, and it is linear because `E[n]` is a `ZMod n`-module (`torsionZModModule`, which carries
no hypothesis beyond `[NeZero n]`). -/
noncomputable def torsionNCoord (P T : W.torsion n) :
    (Fin 2 → ZMod n) →ₗ[ZMod n] W.torsion n :=
  Fintype.linearCombination (ZMod n) ![P, T]

omit [IsAlgClosed F] [W.IsElliptic] in
open Classical in
@[simp]
lemma torsionNCoord_apply (P T : W.torsion n) (c : Fin 2 → ZMod n) :
    torsionNCoord P T c = c 0 • P + c 1 • T := by
  simp [torsionNCoord, Fintype.linearCombination_apply, Fin.sum_univ_two]

omit [IsAlgClosed F] [W.IsElliptic] in
open Classical in
/-- **A `ZMod n`-scalar on `E[n]` is the `ℤ`-scalar given by its representative.**

The bridge between the `ZMod n`-action the determinant needs and the `ℤ`-action `#2281` states its
hypotheses with, in the direction the *injectivity* argument uses; `torsionNCoord_surjective` needs
it the other way round and takes `Int.cast_smul_eq_zsmul` directly.

⚠️ `ZMod.val` is what makes this an equation rather than a coercion identity: `u.val` is a natural
number, `((u.val : ℤ) : ZMod n) = u` needs `[NeZero n]`, and that instance is on the section. -/
lemma zmod_smul_torsion (u : ZMod n) (P : W.torsion n) : u • P = ((u.val : ℤ)) • P := by
  rw [← Int.cast_smul_eq_zsmul (ZMod n)]
  push_cast
  rw [ZMod.natCast_val, ZMod.cast_id]

open Classical in
/-- **A primitive pair spans `E[n]` over `ZMod n`.**

This is `#2281`'s `exists_zsmul_add_zsmul_eq_n` — which spans with **integer** coefficients — read
through `Int.cast_smul_eq_zsmul`.

⚠️ The hypothesis is `orderOf (e_n(P, T)) = n` and **not** `e_n(P, T) ≠ 1`.  Off a prime index the
second does not bound the order of the value, and `#2281` carries a compiled `μ_4` witness for why;
at a prime index the two coincide, which is why `#958` never had to see the difference. -/
theorem torsionNCoord_surjective (h2 : (2 : F) ≠ 0) (hn : ((n : ℤ) : F) ≠ 0)
    {P T : W.torsion n} (horder : orderOf (weilPairingN h2 hn P T) = n) :
    Function.Surjective (torsionNCoord P T) := by
  intro Q
  obtain ⟨a, b, hab⟩ := exists_zsmul_add_zsmul_eq_n h2 hn horder Q
  refine ⟨![(a : ZMod n), (b : ZMod n)], ?_⟩
  rw [torsionNCoord_apply]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [Int.cast_smul_eq_zsmul, Int.cast_smul_eq_zsmul]
  exact hab.symm

open Classical in
/-- **A primitive pair is `ZMod n`-independent in `E[n]`.**

⚠️ **This is where the file parts company with `#958`, and the reason is Mathlib's and not this
development's.**  `#958` deduces injectivity from surjectivity by
`LinearMap.injective_iff_surjective_of_finrank_eq_finrank`, which is stated over a `DivisionRing`;
`ZMod n` is one exactly when `n` is prime, so at a composite index there is no ring to run that
argument over and injectivity has to be proved.

It is proved from `#2281`'s `intCast_eq_zero_of_zsmul_add_zsmul_eq_zero_n`, used **by name**.  ⚠️ So
`#958`'s careful caveat — that it *looks* independent of the independence lemma and is not, because
`exists_zsmul_add_zsmul_eq_three` consumes it one level down — has nothing to correct here: the
lemma is consumed at this level, in the open. -/
theorem torsionNCoord_injective (h2 : (2 : F) ≠ 0) (hn : ((n : ℤ) : F) ≠ 0)
    {P T : W.torsion n} (horder : orderOf (weilPairingN h2 hn P T) = n) :
    Function.Injective (torsionNCoord P T) := by
  refine (injective_iff_map_eq_zero (torsionNCoord P T)).mpr fun c hc => ?_
  rw [torsionNCoord_apply, zmod_smul_torsion, zmod_smul_torsion] at hc
  obtain ⟨h0, h1⟩ := intCast_eq_zero_of_zsmul_add_zsmul_eq_zero_n h2 hn horder hc
  push_cast at h0 h1
  rw [ZMod.natCast_val, ZMod.cast_id] at h0 h1
  funext i
  fin_cases i
  · exact h0
  · exact h1

open Classical in
/-- **`(a, b) ↦ a • P + b • T` is a linear equivalence at a primitive pair.**

Both halves are theorems of this file, and neither is a rank computation.  ⚠️ **No `1 < n` is bound
and none is available to bind**: the rank statement `finrank_torsion_of_natCast_ne_zero`
(`EllipticCurves.TateModule.DeterminantModGeneral`) needs it, and nothing below needs the rank. -/
noncomputable def torsionNPairingEquiv (h2 : (2 : F) ≠ 0) (hn : ((n : ℤ) : F) ≠ 0)
    {P T : W.torsion n} (horder : orderOf (weilPairingN h2 hn P T) = n) :
    (Fin 2 → ZMod n) ≃ₗ[ZMod n] W.torsion n :=
  LinearEquiv.ofBijective (torsionNCoord P T)
    ⟨torsionNCoord_injective h2 hn horder, torsionNCoord_surjective h2 hn horder⟩

open Classical in
/-- **`(P, T)` as a `ZMod n`-basis of `E[n]`**, at a primitive pair.

⚠️ Not canonical, and deliberately confined to proofs: no statement in this file mentions it.  It
differs from `basisTorsionOfNatCastNeZero` (`EllipticCurves.TateModule.DeterminantModGeneral`)
precisely in that its two vectors are the *given* `P` and `T` — which is what lets `#2281`'s matrix
hypotheses, stated about `P` and `T`, be read as statements about basis vectors — and in carrying no
`1 < n`.

⚠️ **This is also the file's own exhibition that `E[n]` is free over `ZMod n`**, which is what makes
`galoisDetMod n` an honest determinant rather than `LinearEquiv.det`'s value on a module it cannot
see.  ⚠️ **No rank may be read off it.**  It is indexed by `Fin 2` at every `n` with the two pairing
hypotheses, `n = 1` included, and there `ZMod 1` is the zero ring and has no invariant basis
number. -/
noncomputable def basisTorsionNOfPairing (h2 : (2 : F) ≠ 0) (hn : ((n : ℤ) : F) ≠ 0)
    {P T : W.torsion n} (horder : orderOf (weilPairingN h2 hn P T) = n) :
    Module.Basis (Fin 2) (ZMod n) (W.torsion n) :=
  Module.Basis.ofEquivFun (torsionNPairingEquiv h2 hn horder).symm

open Classical in
/-- The first vector of `basisTorsionNOfPairing` is `P`. -/
lemma basisTorsionNOfPairing_zero (h2 : (2 : F) ≠ 0) (hn : ((n : ℤ) : F) ≠ 0)
    {P T : W.torsion n} (horder : orderOf (weilPairingN h2 hn P T) = n) :
    basisTorsionNOfPairing h2 hn horder 0 = P := by
  rw [basisTorsionNOfPairing, Module.Basis.coe_ofEquivFun]
  simp only [LinearEquiv.symm_symm, torsionNPairingEquiv, LinearEquiv.ofBijective_apply]
  rw [torsionNCoord_apply]
  simp

open Classical in
/-- The second vector of `basisTorsionNOfPairing` is `T`. -/
lemma basisTorsionNOfPairing_one (h2 : (2 : F) ≠ 0) (hn : ((n : ℤ) : F) ≠ 0)
    {P T : W.torsion n} (horder : orderOf (weilPairingN h2 hn P T) = n) :
    basisTorsionNOfPairing h2 hn horder 1 = T := by
  rw [basisTorsionNOfPairing, Module.Basis.coe_ofEquivFun]
  simp only [LinearEquiv.symm_symm, torsionNPairingEquiv, LinearEquiv.ofBijective_apply]
  rw [torsionNCoord_apply]
  simp

end PairingBasis

/-! ### `det ρ_{E,n} = χ_n` -/

section Galois

variable {S F : Type*} [Field S] [Field F] [Algebra S F] {W : Affine S} [W.IsElliptic]
  [IsAlgClosed F]

open Classical in
/-- **The bridge: `EllipticCurves.TateModule.DeterminantMod`'s object is `#2281`'s number.**

`det ρ_{E,n}(σ) = χ_n(σ)` in `ZMod n`, for a fixed `σ`, at every `n` with `(2 : F) ≠ 0` and
`((n : ℤ) : F) ≠ 0` over an algebraically closed `F`.  The primitive pair `(P, T)` is produced
inside the proof by `exists_orderOf_weilPairingN_eq` and the matrix by
`exists_smul_eq_zsmul_add_zsmul_and_det_n_eq`; neither appears in the statement, because
`LinearEquiv.det` does not depend on them.

⚠️ **The matrix is identified through `Matrix.toLin`, not through `Module.Basis.repr`.**  The
`toMatrix`/`toLin` equivalence is run backwards: what is checked is that `ρ_{E,n}(σ)` agrees with
`Matrix.toLin bas bas M` on each basis vector (`Module.Basis.ext` plus `Matrix.toLin_self`), and
`← LinearMap.toMatrix_symm` then converts that into the value of `toMatrix`.  `#958` records the
motive failure that going forwards through `repr` produces, and it is the same here: `horder`'s own
type mentions `P`.

⚠️ **Index convention, checked rather than assumed.**  `Matrix.toLin_self bas bas M i = ∑ j, M j i •
bas j`, so column `i` holds the image of `bas i`.  With `hP : σ • P = a • P + c • T` the entries
land as `M 0 0 = a`, `M 1 0 = c`, `M 0 1 = b`, `M 1 1 = d`, and `Matrix.det_fin_two_of` produces
`a * d − b * c` — `#2281`'s naming, with no transpose.

⚠️ `LinearMap.det_toMatrix` asks for a basis and for nothing else: no `Module.Free` and no
`Module.Finite` instance is supplied here, and none is needed. -/
theorem coe_galoisDetMod_n_eq_galoisModularCyclotomicChar (σ : F ≃ₐ[S] F) (h2 : (2 : F) ≠ 0)
    {n : ℕ} [NeZero n] (hn : ((n : ℤ) : F) ≠ 0) :
    ((galoisDetMod (W' := W) (F := F) n σ : ZMod n))
      = (galoisModularCyclotomicChar S F (natCard_rootsOfUnity_of_intCast_ne_zero hn) σ :
          ZMod n) := by
  obtain ⟨P, T, horder⟩ := exists_orderOf_weilPairingN_eq (W := W⁄F) h2 hn
  obtain ⟨a, b, c, d, hP, hT, hdet⟩ :=
    exists_smul_eq_zsmul_add_zsmul_and_det_n_eq (W := W) σ h2 hn horder
  set bas := basisTorsionNOfPairing (W := W⁄F) h2 hn horder
  set M : Matrix (Fin 2) (Fin 2) (ZMod n) :=
    !![(a : ZMod n), (b : ZMod n); (c : ZMod n), (d : ZMod n)] with hMdef
  have hb0 : bas 0 = P := basisTorsionNOfPairing_zero h2 hn horder
  have hb1 : bas 1 = T := basisTorsionNOfPairing_one h2 hn horder
  have hcol : ∀ i : Fin 2,
      ((galoisRepModLinear (W' := W) (F := F) n σ :
          (W⁄F).torsion n ≃ₗ[ZMod n] (W⁄F).torsion n) :
            (W⁄F).torsion n →ₗ[ZMod n] (W⁄F).torsion n) (bas i)
        = M 0 i • bas 0 + M 1 i • bas 1 := by
    intro i
    match i with
    | 0 => simpa [hMdef, hb0, hb1, Int.cast_smul_eq_zsmul] using hP
    | 1 => simpa [hMdef, hb0, hb1, Int.cast_smul_eq_zsmul] using hT
  have hM : LinearMap.toMatrix bas bas
      ((galoisRepModLinear (W' := W) (F := F) n σ :
        (W⁄F).torsion n ≃ₗ[ZMod n] (W⁄F).torsion n) :
          (W⁄F).torsion n →ₗ[ZMod n] (W⁄F).torsion n) = M := by
    rw [show ((galoisRepModLinear (W' := W) (F := F) n σ :
        (W⁄F).torsion n ≃ₗ[ZMod n] (W⁄F).torsion n) :
          (W⁄F).torsion n →ₗ[ZMod n] (W⁄F).torsion n) = Matrix.toLin bas bas M from
      bas.ext fun i => by rw [Matrix.toLin_self, Fin.sum_univ_two]; exact hcol i,
      ← LinearMap.toMatrix_symm, LinearEquiv.apply_symm_apply]
  rw [galoisDetMod_apply, LinearEquiv.coe_det, ← LinearMap.det_toMatrix bas, hM, hMdef,
    Matrix.det_fin_two_of, ← hdet]
  push_cast
  ring

open Classical in
/-- **`det ρ_{E,n}(σ) = χ_n(σ)` in `(ZMod n)ˣ`**, the pointwise form of the headline.

`Units.ext` on the previous statement; the module docstring's section on the two-layer split says
why the two layers are separate. -/
theorem galoisDetMod_n_apply_eq_galoisModularCyclotomicChar (σ : F ≃ₐ[S] F) (h2 : (2 : F) ≠ 0)
    {n : ℕ} [NeZero n] (hn : ((n : ℤ) : F) ≠ 0) :
    galoisDetMod (W' := W) (F := F) n σ
      = galoisModularCyclotomicChar S F (natCard_rootsOfUnity_of_intCast_ne_zero hn) σ :=
  Units.ext (coe_galoisDetMod_n_eq_galoisModularCyclotomicChar σ h2 hn)

open Classical in
/-- **`det ρ_{E,n} = χ_n`**, Silverman *AEC* III.8.1(a), (b) and (d), as an identity of monoid
homomorphisms `(F ≃ₐ[S] F) →* (ZMod n)ˣ`, at every `n` with `(2 : F) ≠ 0` and `((n : ℤ) : F) ≠ 0`
over an algebraically closed `F`.

⚠️ **Nothing but `σ` is quantified away here — no pair, no matrix, no basis.**  That is what
distinguishes this statement from `#2281`'s `exists_smul_eq_zsmul_add_zsmul_and_det_n_eq`, which is
the same mathematics stated about a chosen primitive pair, and it is the reason
`EllipticCurves.TateModule.Determinant` names this identity as the goal of the whole Weil-pairing
effort.

⚠️ It is *not* the `ℓ`-adic statement, but it is what the `ℓ`-adic statement consumes:
`galoisDet_eq_galoisCyclotomicChar`
(`EllipticCurves.FunctionField.TateDeterminantCyclotomic`) applies this theorem at every index
`ℓ ^ k`.  ⚠️ **This sentence used to end** *"and is untouched"*; the retirement is recorded once, at
`galoisDet` in `EllipticCurves.TateModule.PrimaryDeterminant`. -/
theorem galoisDetMod_n_eq_galoisModularCyclotomicChar (h2 : (2 : F) ≠ 0)
    {n : ℕ} [NeZero n] (hn : ((n : ℤ) : F) ≠ 0) :
    galoisDetMod (W' := W) (F := F) n
      = galoisModularCyclotomicChar S F (natCard_rootsOfUnity_of_intCast_ne_zero hn) :=
  MonoidHom.ext fun σ => galoisDetMod_n_apply_eq_galoisModularCyclotomicChar σ h2 hn

open Classical in
/-- **If `χ_n(σ) ≠ 1` then `det ρ_{E,n}(σ) ≠ 1`.**

The form in which the identity has arithmetic consequences.  ⚠️ **It produces no such `σ` and this
development has one only at `n = 3`**: `exists_galoisModularCyclotomicChar_three_ne_one` (`#947`,
`EllipticCurves.FunctionField.WeilPairingRationalTorsionGalois`) is a statement about
`AlgebraicClosure ℚ` and not about any curve, and there is no general-`n` twin of it on `main`.  The
non-vacuity block below fires it at `n = 3` through this lemma, which is the whole of what the
general layer buys there. -/
theorem galoisDetMod_n_ne_one_of_galoisModularCyclotomicChar_ne_one {σ : F ≃ₐ[S] F}
    (h2 : (2 : F) ≠ 0) {n : ℕ} [NeZero n] (hn : ((n : ℤ) : F) ≠ 0)
    (hσ : galoisModularCyclotomicChar S F (natCard_rootsOfUnity_of_intCast_ne_zero hn) σ ≠ 1) :
    galoisDetMod (W' := W) (F := F) n σ ≠ 1 := by
  rw [galoisDetMod_n_apply_eq_galoisModularCyclotomicChar σ h2 hn]
  exact hσ

end Galois

/-! ### Subsumption

⚠️ Compiled, not asserted, exactly as in `EllipticCurves.TateModule.DeterminantModGeneral` and
`EllipticCurves.TateModule.MatrixRepModGeneral`: the `example` below restates `#958`'s headline
`galoisDetMod_three_eq_galoisModularCyclotomicChar` **binder for binder** — including its own
naming of the character through `natCard_rootsOfUnity_of_ne_zero h3` rather than this file's
`natCard_rootsOfUnity_of_intCast_ne_zero` — and proves it from the general layer.

⚠️ The two namings are interchangeable because the count is a `Prop` and
`galoisModularCyclotomicChar` takes it as a proof argument, so proof irrelevance makes the two
characters the same term; the `example` is what checks that, and `by exact_mod_cast h3` is the only
step. -/

section Subsumption

variable {S F : Type*} [Field S] [Field F] [Algebra S F] {W : Affine S} [W.IsElliptic]
  [IsAlgClosed F]

open Classical in
/-- `galoisDetMod_three_eq_galoisModularCyclotomicChar`, restated verbatim and proved from the
general layer. -/
example (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) :
    galoisDetMod (W' := W) (F := F) 3
      = galoisModularCyclotomicChar S F (natCard_rootsOfUnity_of_ne_zero h3) :=
  galoisDetMod_n_eq_galoisModularCyclotomicChar h2 (n := 3) (by exact_mod_cast h3)

end Subsumption

/-! ### Non-vacuity

The curve is this front's standard certificate curve, `y² + y = x³` over `ℚ` base-changed to
`AlgebraicClosure ℚ`, with **`S = ℚ` and not `S = F`** — over `S = F` the group `Gal(F/S)` is
trivial and a certificate about a Galois *representation* says nothing.  This block declares no
fixture of its own (`#1408`).

⚠️ **The two certificates below are load-bearing in different ways, and neither is load-bearing in
both.**

* **At `n = 5` the index is what is new.**  `5` is not `3`-smooth, so `#958`'s headline cannot state
  the first certificate at any hypotheses, and neither can
  `EllipticCurves.TateModule.DeterminantModSmooth`'s layer.  ⚠️ **What is not certified there is
  that either side is non-trivial**: `χ_5` of `ℚ` being a non-trivial character is a statement about
  `AlgebraicClosure ℚ`, `#947` proves it at `n = 3` only, and nothing on `main` proves it at `5`.
  So that certificate is an equation between two characters that could, for all this development
  says, both be `1`.
* **At `n = 3` the non-triviality is what is new here, and the mathematics is not.**  The last
  certificate is `#958`'s own load-bearing one, re-derived through
  `galoisDetMod_n_ne_one_of_galoisModularCyclotomicChar_ne_one` instead of through its `n = 3` twin.
  ⚠️ **It is stated for exactly that reason** — it is what shows the general layer keeps the teeth,
  and it is *not* evidence that this file proves anything new at `n = 3`.

⚠️ **`∃ σ, det ρ_{E,3}(σ) ≠ 1` and `det ρ_{E,3} ≠ 1` are different statements** and both are below.
Only the second is the sentence *"the determinant character of `E[3]` is non-trivial"* as a reader
would write it, and it needs the first plus a `MonoidHom.one_apply` step.

⚠️ **Each certificate was tested by deleting the last named lemma from its script** (`#944`).
Deleting the `exact galoisDetMod_n_ne_one_of_galoisModularCyclotomicChar_ne_one …` line from the
load-bearing one, leaving the rest of its script untouched, gives

```
error: unsolved goals
σ : Gal(AlgebraicClosure ℚ/ℚ)
hσ : (galoisModularCyclotomicChar ℚ (AlgebraicClosure ℚ) ⋯) σ ≠ 1
hEq : galoisDetMod 3 = 1
⊢ False
```

⚠️ **Read the hypothesis list, not the error tag.**  What survives is a statement about `χ_3` and a
statement about `galoisDetMod`, and *nothing relating them*: the certificate is closed by this
file's identity and by nothing else.

⚠️ **There is deliberately no certificate in which `E[n]` is `ℚ`-rational.**  `#947`'s
`ker_galoisRepMod_three_le_ker_galoisModularCyclotomicChar` *rules one out* over `ℚ` at `n = 3`,
since `E[3] ⊆ E(ℚ)` would force `χ_3` of `ℚ` to be trivial;
`EllipticCurves.FunctionField.WeilPairingDeterminantCharacter` records this at length. -/

section Nonvacuity

open EllipticCurves.Fixture

private lemma exampleTwo : (2 : AlgClosedQ) ≠ 0 := two_ne_zero

/-- The index condition `((n : ℤ) : F) ≠ 0` at `n = 3` over a field of characteristic `0`. -/
private lemma exampleIndexThree : (((3 : ℕ) : ℤ) : AlgClosedQ) ≠ 0 := by
  have h : (((3 : ℕ) : ℤ) : AlgClosedQ) = 3 := by push_cast; ring
  rw [h]; norm_num

/-- The same at `n = 5`, which is **not** `3`-smooth. -/
private lemma exampleIndexFive : (((5 : ℕ) : ℤ) : AlgClosedQ) ≠ 0 := by
  have h : (((5 : ℕ) : ℤ) : AlgClosedQ) = 5 := by push_cast; ring
  rw [h]; norm_num

open Classical in
/-- **⚠️ THE CERTIFICATE THAT PRICES THE INDEX**: the headline on a curve that exists, at `n = 5`,
with both sides written out.  Unconditional.

⚠️ It says nothing about either side being non-trivial; see the block docstring. -/
example : galoisDetMod (W' := y2AddYEqX3 ℚ) (F := AlgClosedQ) 5
    = galoisModularCyclotomicChar ℚ AlgClosedQ
        (natCard_rootsOfUnity_of_intCast_ne_zero (F := AlgClosedQ) (n := 5) exampleIndexFive) :=
  galoisDetMod_n_eq_galoisModularCyclotomicChar exampleTwo exampleIndexFive

open Classical in
/-- **A `ZMod 5`-basis of `E[5]` whose two vectors are a primitive pairing pair**, on the same
curve — the basis machinery at an index where no `1 < n`-carrying construction was needed.  Both
vectors are named, so nothing is projected away. -/
example : ∃ (P T : ((y2AddYEqX3 ℚ)⁄AlgClosedQ).torsion 5)
    (b : Module.Basis (Fin 2) (ZMod 5) (((y2AddYEqX3 ℚ)⁄AlgClosedQ).torsion 5)),
    b 0 = P ∧ b 1 = T := by
  obtain ⟨P, T, horder⟩ := exists_orderOf_weilPairingN_eq
    (W := (y2AddYEqX3 ℚ)⁄AlgClosedQ) exampleTwo exampleIndexFive
  exact ⟨P, T, basisTorsionNOfPairing exampleTwo exampleIndexFive horder,
    basisTorsionNOfPairing_zero _ _ horder, basisTorsionNOfPairing_one _ _ horder⟩

open Classical in
/-- Some `σ ∈ Gal(ℚ̄/ℚ)` has `det ρ_{E,3}(σ) ≠ 1`, on the same curve — the existential form, weaker
than the certificate below. -/
example : ∃ σ : AlgClosedQ ≃ₐ[ℚ] AlgClosedQ,
    galoisDetMod (W' := y2AddYEqX3 ℚ) (F := AlgClosedQ) 3 σ ≠ 1 := by
  obtain ⟨σ, hσ⟩ := exists_galoisModularCyclotomicChar_three_ne_one
    (natCard_rootsOfUnity_of_intCast_ne_zero (F := AlgClosedQ) (n := 3) exampleIndexThree)
  exact ⟨σ, galoisDetMod_n_ne_one_of_galoisModularCyclotomicChar_ne_one
    (W := y2AddYEqX3 ℚ) exampleTwo exampleIndexThree hσ⟩

open Classical in
/-- **⚠️ THE LOAD-BEARING CERTIFICATE**: on `y² + y = x³` over `ℚ`, the mod-`3` determinant
character is **not** the trivial homomorphism `Gal(ℚ̄/ℚ) →* (ZMod 3)ˣ`.

Unconditional, and the negated *character* equation rather than an existential about a point of the
group.  ⚠️ **It is `#958`'s certificate and not a new theorem** — what is new is that it is closed
through the general layer; see the block docstring. -/
example : galoisDetMod (W' := y2AddYEqX3 ℚ) (F := AlgClosedQ) 3
    ≠ (1 : (AlgClosedQ ≃ₐ[ℚ] AlgClosedQ) →* (ZMod 3)ˣ) := by
  obtain ⟨σ, hσ⟩ := exists_galoisModularCyclotomicChar_three_ne_one
    (natCard_rootsOfUnity_of_intCast_ne_zero (F := AlgClosedQ) (n := 3) exampleIndexThree)
  intro hEq
  exact galoisDetMod_n_ne_one_of_galoisModularCyclotomicChar_ne_one
    (W := y2AddYEqX3 ℚ) exampleTwo exampleIndexThree hσ (by rw [hEq]; rfl)

end Nonvacuity

end WeierstrassCurve.Affine
