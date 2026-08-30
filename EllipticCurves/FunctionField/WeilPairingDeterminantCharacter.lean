/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import EllipticCurves.FunctionField.WeilPairingDeterminant
import EllipticCurves.FunctionField.WeilPairingRationalTorsionGalois
import EllipticCurves.TateModule.DeterminantMod

/-!
# `det ρ_{E,3} = χ_3` as an identity of monoid homomorphisms

Silverman *AEC* III.8.1(e).  Two files each hold one half of this statement and neither holds the
statement:

* `EllipticCurves.TateModule.DeterminantMod` (`#956`) has the **object**, the determinant character
  `galoisDetMod 3 : (F ≃ₐ[S] F) →* (ZMod 3)ˣ`, defined basis-free through `LinearEquiv.det`;
* `EllipticCurves.FunctionField.WeilPairingDeterminant` (`#951`) has the **equation**, the number
  `a * d − b * c ≡ χ_3(σ)` for a *chosen* pairing-generating pair `(P, T)` and a quadruple of
  integers carried in hypotheses.

This file proves that the object equals the character:

```
galoisDetMod 3 = galoisModularCyclotomicChar S F hn.
```

⚠️ **The choice of `(P, T)` is invisible in the conclusion, and that is the whole point of the
file.**  `LinearEquiv.det` is basis-free, so the headline quantifies over nothing but the curve and
the field — where `#951`'s statements quantify over a pair and a matrix as well.  `pairing`-derived
bases exist below only to *compute* the determinant, inside proofs; no statement mentions one.  That
is the entire difference between this file and `#951`, and it is why the two are complementary
rather than one subsuming the other.

## The route, and the one thing that makes it short

`#951` supplies, for each `σ`, integers `a b c d` with `σ • P = a • P + c • T`,
`σ • T = b • P + d • T` and `a * d − b * c ≡ χ_3(σ)`.  What is needed is that the *bundled*
determinant of `ρ_{E,3}(σ)` is that same number, and Mathlib reduces the determinant of a bundled
map to the determinant of a matrix by `LinearMap.det_toMatrix` — for **any** basis.  So the work is
exactly: manufacture one basis out of `(P, T)`, identify the matrix, and take
`Matrix.det_fin_two_of`.

⚠️ **No abstract `e_3(α x, α y) = e_3(x, y) ^ (det α)` is needed** — that statement (`#957`) is true
and is a detour, because `LinearMap.det_toMatrix` already performs the reduction to a matrix that
`#951` has computed.

⚠️ **The `ℤ`-to-`ZMod 3` scalar bridge is `Int.cast_smul_eq_zsmul`.**  `#951`'s hypotheses are
`ℤ`-scalar equations and everything here is a `ZMod 3`-module statement; that one lemma is the only
place the two actions meet, and it is used at exactly two call sites
(`torsionThreeCoord_surjective`, and the column computation inside
`coe_galoisDetMod_three_eq_galoisModularCyclotomicChar`).

## ⚠️ Uniqueness of coordinates is implied by the rank here, not assumed

`basisTorsionThreeOfPairing` is built from *surjectivity alone*:
`exists_zsmul_add_zsmul_eq_three` says `(P, T)` spans, and
`LinearMap.injective_iff_surjective_of_finrank_eq_finrank` upgrades that to bijectivity because
`Module.finrank (ZMod 3) E[3] = 2 = Module.finrank (ZMod 3) (Fin 2 → ZMod 3)`.

⚠️ **Be exact about what that avoids, because it is less than it looks.**  Nothing below *cites*
`#951`'s independence lemma `intCast_eq_zero_of_zsmul_add_zsmul_eq_zero_three` — the only `#951`
lemmas named here are `exists_zsmul_add_zsmul_eq_three`, `exists_weilPairingThree_ne_one` and
`exists_smul_eq_zsmul_add_zsmul_and_det_three_eq`.  But `exists_zsmul_add_zsmul_eq_three` proves
injectivity of `(ℤ/3)² → E[3]` *with* the independence lemma before counting, so it is consumed one
level down and this file is not independent of it.  What the rank argument buys is only that
injectivity is not re-derived here.

## Main definitions

* `WeierstrassCurve.Affine.torsionThreeCoord` — `(a, b) ↦ a • P + b • T`, as a `ZMod 3`-linear map
  `(Fin 2 → ZMod 3) →ₗ[ZMod 3] E[3]`.
* `WeierstrassCurve.Affine.torsionThreePairingEquiv` — the same map, bijective when
  `e_3(P, T) ≠ 1`.
* `WeierstrassCurve.Affine.basisTorsionThreeOfPairing` — the `ZMod 3`-basis `(P, T)` of `E[3]`.

## Main statements

* `WeierstrassCurve.Affine.coe_galoisDetMod_three_eq_galoisModularCyclotomicChar` — the identity in
  `ZMod 3`, for a fixed `σ`.
* `WeierstrassCurve.Affine.galoisDetMod_three_apply_eq_galoisModularCyclotomicChar` — the same in
  `(ZMod 3)ˣ`.
* `WeierstrassCurve.Affine.galoisDetMod_three_eq_galoisModularCyclotomicChar` — **the headline**,
  `det ρ_{E,3} = χ_3` as an equation between monoid homomorphisms.
* `WeierstrassCurve.Affine.galoisDetMod_three_ne_one_of_galoisModularCyclotomicChar_ne_one` — the
  form that turns `#947`'s `χ_3 ≠ 1` over `ℚ` into a statement about the determinant.

## ⚠️ The two-layer split of the headline is forced by `Units`

`galoisDetMod` lands in `(ZMod 3)ˣ` and `#951`'s equation lives in `ZMod 3`.  `Units.ext` is what
crosses between them, so the bridge is stated on the **coercion** and the unit-level statement is
its one-line consequence.  Trying to run the matrix computation directly in `(ZMod 3)ˣ` means
carrying `Units.val` through `Matrix.det_fin_two_of`, and there is no reason to.

## Layering

This file is under `FunctionField/` because it consumes the Weil pairing.  ⚠️ It **cannot** move
under `TateModule/`: nothing under `TateModule/` imports anything under `FunctionField/`, and
`EllipticCurves.TateModule.DeterminantMod` records that this is deliberate.  Grepped in both
directions at the commit that adds this file: `grep -rn 'import EllipticCurves.FunctionField'
EllipticCurves/TateModule/` is empty, and this file's own imports cross the other way only.

## Explicitly out of scope

* **`n = 2`.**  `galoisDetMod 2 = χ_2` is true and content-free: `(ZMod 2)ˣ` is a subsingleton, so
  both sides are the constant `1` and the statement holds for *any* pair of characters into it.  It
  is not stated below, on the same grounds `EllipticCurves.TateModule.DeterminantMod` gives for not
  stating `free_torsion_three`.  ⚠️ It is also **not** the `ℓ`-adic `galoisDetTwo = χ_2` over
  `ℤ_[2]`, which is a genuine theorem and remains open: it needs the pairing at every level
  `E[2 ^ k]`, and this development has it at `k = 1` only.
* **General `n`.**  Only `n = 3` is available.  ⚠️ **The reason this bullet used to give is spent
  and the restriction is not.**  It read *"because only `n = 3` has `finrank_torsion_three`, which
  in turn has only `card_torsion_three`"*, and both halves have been paid:
  `card_torsion_eq_sq_of_smooth` gives `#E[n] = n²` and
  `EllipticCurves.TateModule.DeterminantModSmooth`'s `finrank_torsion_of_smooth` (`#1240`) gives the
  rank, at every `3`-smooth `n > 1`.  What confines this file to `n = 3` is now the **pairing**:
  `weilPairingThree` and its `n = 2` twin are all this development has, and no rank statement
  manufactures one.
* **A `Gal(F/S)`-stable basis.**  Does not exist in general and is not needed; see the note above on
  why the headline mentions no basis.
* **The trace and the characteristic polynomial** mod `n`.  No consumer.

## References

* [J. H. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.8.1(e).
-/

namespace WeierstrassCurve.Affine

open CoordinateRing

/-! ### A `ZMod 3`-basis of `E[3]` from a pairing-nonvanishing pair -/

section PairingBasis

variable {F : Type*} [Field F] [IsAlgClosed F] {W : Affine F} [W.IsElliptic]

open Classical in
/-- **The map `(a, b) ↦ a • P + b • T`** on `E[3]`, as a `ZMod 3`-linear map out of
`Fin 2 → ZMod 3`.

Nothing is assumed about `P` and `T`: this is `Fintype.linearCombination` against the family
`![P, T]`, and it is linear because `E[3]` is a `ZMod 3`-module (`torsionZModModule`,
unconditionally). -/
noncomputable def torsionThreeCoord (P T : W.torsion 3) :
    (Fin 2 → ZMod 3) →ₗ[ZMod 3] W.torsion 3 :=
  Fintype.linearCombination (ZMod 3) ![P, T]

omit [IsAlgClosed F] [W.IsElliptic] in
open Classical in
@[simp]
lemma torsionThreeCoord_apply (P T : W.torsion 3) (c : Fin 2 → ZMod 3) :
    torsionThreeCoord P T c = c 0 • P + c 1 • T := by
  simp [torsionThreeCoord, Fintype.linearCombination_apply, Fin.sum_univ_two]

open Classical in
/-- **A pair with `e_3(P, T) ≠ 1` spans `E[3]` over `ZMod 3`.**

This is `#951`'s `exists_zsmul_add_zsmul_eq_three` — which spans with **integer** coefficients —
read through `Int.cast_smul_eq_zsmul`.  ⚠️ That lemma is the only bridge between the `ℤ`-action
`#951` works with and the `ZMod 3`-action the determinant needs. -/
theorem torsionThreeCoord_surjective (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0)
    {P T : W.torsion 3} (hPT : weilPairingThree h2 h3 P T ≠ 1) :
    Function.Surjective (torsionThreeCoord P T) := by
  intro Q
  obtain ⟨a, b, hab⟩ := exists_zsmul_add_zsmul_eq_three h2 h3 hPT Q
  refine ⟨![(a : ZMod 3), (b : ZMod 3)], ?_⟩
  rw [torsionThreeCoord_apply]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [Int.cast_smul_eq_zsmul, Int.cast_smul_eq_zsmul]
  exact hab.symm

open Classical in
/-- **`(a, b) ↦ a • P + b • T` is a linear equivalence when `e_3(P, T) ≠ 1`.**

⚠️ **Injectivity is not proved; it is deduced from the rank.**  Both sides have `ZMod 3`-rank `2`
(`finrank_torsion_three` and `Module.finrank_fin_fun`), so
`LinearMap.injective_iff_surjective_of_finrank_eq_finrank` turns the surjectivity above into
bijectivity, off the counting that `#E[3] = 9` already performed inside `finrank_torsion_three`.

⚠️ **That buys less than "independent of `#951`'s independence lemma", and the file's Scope section
says so.**  `intCast_eq_zero_of_zsmul_add_zsmul_eq_zero_three` is not *cited* anywhere below, but
`exists_zsmul_add_zsmul_eq_three` — which is cited — proves injectivity of `(ℤ/3)² → E[3]` with it
before it counts, at `EllipticCurves/FunctionField/WeilPairingDeterminant.lean:357`.  So it is
consumed one level down and this file is not independent of it; what the rank argument buys is only
that injectivity is not re-derived here. -/
noncomputable def torsionThreePairingEquiv (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0)
    {P T : W.torsion 3} (hPT : weilPairingThree h2 h3 P T ≠ 1) :
    (Fin 2 → ZMod 3) ≃ₗ[ZMod 3] W.torsion 3 :=
  haveI := finite_torsion_three_zmod (W := W) h3
  LinearEquiv.ofBijective (torsionThreeCoord P T)
    ⟨(LinearMap.injective_iff_surjective_of_finrank_eq_finrank
        (by rw [Module.finrank_fin_fun, finrank_torsion_three h2 h3])).mpr
      (torsionThreeCoord_surjective h2 h3 hPT),
     torsionThreeCoord_surjective h2 h3 hPT⟩

open Classical in
/-- **`(P, T)` as a `ZMod 3`-basis of `E[3]`**, when `e_3(P, T) ≠ 1`.

⚠️ Not canonical, and deliberately confined to proofs: no statement in this file mentions it.  It
differs from `basisTorsionThree` (`EllipticCurves.TateModule.DeterminantMod`) precisely in that its
two vectors are the *given* `P` and `T` — which is what lets `#951`'s matrix hypotheses, stated
about `P` and `T`, be read as statements about basis vectors. -/
noncomputable def basisTorsionThreeOfPairing (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0)
    {P T : W.torsion 3} (hPT : weilPairingThree h2 h3 P T ≠ 1) :
    Module.Basis (Fin 2) (ZMod 3) (W.torsion 3) :=
  Module.Basis.ofEquivFun (torsionThreePairingEquiv h2 h3 hPT).symm

open Classical in
/-- The first vector of `basisTorsionThreeOfPairing` is `P`. -/
lemma basisTorsionThreeOfPairing_zero (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0)
    {P T : W.torsion 3} (hPT : weilPairingThree h2 h3 P T ≠ 1) :
    basisTorsionThreeOfPairing h2 h3 hPT 0 = P := by
  rw [basisTorsionThreeOfPairing, Module.Basis.coe_ofEquivFun]
  simp only [LinearEquiv.symm_symm, torsionThreePairingEquiv, LinearEquiv.ofBijective_apply]
  rw [torsionThreeCoord_apply]
  simp

open Classical in
/-- The second vector of `basisTorsionThreeOfPairing` is `T`. -/
lemma basisTorsionThreeOfPairing_one (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0)
    {P T : W.torsion 3} (hPT : weilPairingThree h2 h3 P T ≠ 1) :
    basisTorsionThreeOfPairing h2 h3 hPT 1 = T := by
  rw [basisTorsionThreeOfPairing, Module.Basis.coe_ofEquivFun]
  simp only [LinearEquiv.symm_symm, torsionThreePairingEquiv, LinearEquiv.ofBijective_apply]
  rw [torsionThreeCoord_apply]
  simp

end PairingBasis

/-! ### `det ρ_{E,3} = χ_3` -/

section Galois

variable {S F : Type*} [Field S] [Field F] [Algebra S F] {W : Affine S} [W.IsElliptic]
  [IsAlgClosed F]

open Classical in
/-- **The bridge: `#956`'s object is `#951`'s number.**

`det ρ_{E,3}(σ) = χ_3(σ)` in `ZMod 3`, for a fixed `σ`.  The pair `(P, T)` is produced inside the
proof by `exists_weilPairingThree_ne_one` and the matrix by
`exists_smul_eq_zsmul_add_zsmul_and_det_three_eq`; neither appears in the statement, because
`LinearEquiv.det` does not depend on them.

⚠️ **The matrix is identified through `Matrix.toLin`, not through `Module.Basis.repr`.**  The
`toMatrix`/`toLin` equivalence is run backwards: what is checked is that `ρ_{E,3}(σ)` agrees with
`Matrix.toLin bas bas M` on each basis vector (`Module.Basis.ext` plus `Matrix.toLin_self`), and
`← LinearMap.toMatrix_symm` then converts that into the value of `toMatrix`.  Going forwards
through `repr` also works, but it forces `basisTorsionThreeOfPairing_zero` to be rewritten
*backwards*, and `hPT`'s own type mentions `P`, so the motive does not typecheck.  Measured, on a
`repr`-shaped goal against this file as committed:

```
error: Tactic `rewrite` failed: motive is not type correct:
  fun _a => ((basisTorsionThreeOfPairing h2 h3 hPT).repr (u • _a + v • T)) 0 = u
Error: Application type mismatch: The argument
  hPT
has type
  weilPairingThree h2 h3 P T ≠ 1
but is expected to have type
  weilPairingThree h2 h3 _a T ≠ 1
in the application
  basisTorsionThreeOfPairing h2 h3 hPT
```

⚠️ **Index convention, checked rather than assumed.**  `Matrix.toLin_self bas bas M i = ∑ j, M j i •
bas j`, so column `i` holds the image of `bas i`.  With `hP : σ • P = a • P + c • T` the entries
land as `M 0 0 = a`, `M 1 0 = c`, `M 0 1 = b`, `M 1 1 = d`, and `Matrix.det_fin_two_of` produces
`a * d − b * c` — `#951`'s naming, with no transpose. -/
theorem coe_galoisDetMod_three_eq_galoisModularCyclotomicChar (σ : F ≃ₐ[S] F) (h2 : (2 : F) ≠ 0)
    (h3 : (3 : F) ≠ 0) :
    ((galoisDetMod (W' := W) (F := F) 3 σ : ZMod 3))
      = (galoisModularCyclotomicChar S F (natCard_rootsOfUnity_of_ne_zero h3) σ : ZMod 3) := by
  obtain ⟨P, T, hPT⟩ := exists_weilPairingThree_ne_one (W := W⁄F) h2 h3
  obtain ⟨a, b, c, d, hP, hT, hdet⟩ :=
    exists_smul_eq_zsmul_add_zsmul_and_det_three_eq (W := W) σ h2 h3 hPT
  set bas := basisTorsionThreeOfPairing (W := W⁄F) h2 h3 hPT
  set M : Matrix (Fin 2) (Fin 2) (ZMod 3) :=
    !![(a : ZMod 3), (b : ZMod 3); (c : ZMod 3), (d : ZMod 3)] with hMdef
  have hb0 : bas 0 = P := basisTorsionThreeOfPairing_zero h2 h3 hPT
  have hb1 : bas 1 = T := basisTorsionThreeOfPairing_one h2 h3 hPT
  have hcol : ∀ i : Fin 2,
      ((galoisRepModLinear (W' := W) (F := F) 3 σ :
          (W⁄F).torsion 3 ≃ₗ[ZMod 3] (W⁄F).torsion 3) :
            (W⁄F).torsion 3 →ₗ[ZMod 3] (W⁄F).torsion 3) (bas i)
        = M 0 i • bas 0 + M 1 i • bas 1 := by
    intro i
    match i with
    | 0 => simpa [hMdef, hb0, hb1, Int.cast_smul_eq_zsmul] using hP
    | 1 => simpa [hMdef, hb0, hb1, Int.cast_smul_eq_zsmul] using hT
  have hM : LinearMap.toMatrix bas bas
      ((galoisRepModLinear (W' := W) (F := F) 3 σ :
        (W⁄F).torsion 3 ≃ₗ[ZMod 3] (W⁄F).torsion 3) :
          (W⁄F).torsion 3 →ₗ[ZMod 3] (W⁄F).torsion 3) = M := by
    rw [show ((galoisRepModLinear (W' := W) (F := F) 3 σ :
        (W⁄F).torsion 3 ≃ₗ[ZMod 3] (W⁄F).torsion 3) :
          (W⁄F).torsion 3 →ₗ[ZMod 3] (W⁄F).torsion 3) = Matrix.toLin bas bas M from
      bas.ext fun i => by rw [Matrix.toLin_self, Fin.sum_univ_two]; exact hcol i,
      ← LinearMap.toMatrix_symm, LinearEquiv.apply_symm_apply]
  rw [galoisDetMod_apply, LinearEquiv.coe_det, ← LinearMap.det_toMatrix bas, hM, hMdef,
    Matrix.det_fin_two_of, ← hdet]
  push_cast
  ring

open Classical in
/-- **`det ρ_{E,3}(σ) = χ_3(σ)` in `(ZMod 3)ˣ`**, the pointwise form of the headline.

`Units.ext` on the previous statement; see the file's Scope section for why the two layers are
separate. -/
theorem galoisDetMod_three_apply_eq_galoisModularCyclotomicChar (σ : F ≃ₐ[S] F) (h2 : (2 : F) ≠ 0)
    (h3 : (3 : F) ≠ 0) :
    galoisDetMod (W' := W) (F := F) 3 σ
      = galoisModularCyclotomicChar S F (natCard_rootsOfUnity_of_ne_zero h3) σ :=
  Units.ext (coe_galoisDetMod_three_eq_galoisModularCyclotomicChar σ h2 h3)

open Classical in
/-- **`det ρ_{E,3} = χ_3`**, Silverman *AEC* III.8.1(e), as an identity of monoid homomorphisms
`(F ≃ₐ[S] F) →* (ZMod 3)ˣ`.

⚠️ **Nothing but `σ` is quantified away here — no pair, no matrix, no basis.**  That is what
distinguishes this statement from `#951`'s
`exists_smul_eq_zsmul_add_zsmul_and_det_three_eq`, which is the same mathematics stated about a
chosen generating pair, and it is the reason `EllipticCurves.TateModule.Determinant` names this
identity as the goal of the whole Weil-pairing effort.

⚠️ It is *not* the `ℓ`-adic statement.  `galoisDetTwo = χ_2` over `ℤ_[2]` needs the pairing on
`E[2 ^ k]` for every `k` and is untouched. -/
theorem galoisDetMod_three_eq_galoisModularCyclotomicChar (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) :
    galoisDetMod (W' := W) (F := F) 3
      = galoisModularCyclotomicChar S F (natCard_rootsOfUnity_of_ne_zero h3) :=
  MonoidHom.ext fun σ => galoisDetMod_three_apply_eq_galoisModularCyclotomicChar σ h2 h3

open Classical in
/-- **If `χ_3(σ) ≠ 1` then `det ρ_{E,3}(σ) ≠ 1`.**

The form in which the identity has arithmetic consequences: `#947`'s
`exists_galoisModularCyclotomicChar_three_ne_one` produces such a `σ` over `ℚ` unconditionally, so
this is what makes `det ρ_{E,3}` a *non-trivial* character on a curve that exists.  See the
non-vacuity block. -/
theorem galoisDetMod_three_ne_one_of_galoisModularCyclotomicChar_ne_one
    {σ : F ≃ₐ[S] F} (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0)
    (hσ : galoisModularCyclotomicChar S F (natCard_rootsOfUnity_of_ne_zero h3) σ ≠ 1) :
    galoisDetMod (W' := W) (F := F) 3 σ ≠ 1 := by
  rw [galoisDetMod_three_apply_eq_galoisModularCyclotomicChar σ h2 h3]
  exact hσ

/-! ### Non-vacuity

⚠️ **The load-bearing certificate is the last but one below**: on the curve `y² + y = x³` over `ℚ`,
base-changed to `AlgebraicClosure ℚ` with **`S = ℚ`**, the determinant character
`det ρ_{E,3}` is **not** the trivial homomorphism.  It is unconditional — no `σ` is assumed, no
rationality is assumed, and the input is `#947`'s theorem that `χ_3` of `ℚ` is not trivial.

That certificate is what makes the identity worth proving rather than merely true.  Every other
statement in this file, and every statement in
`EllipticCurves.TateModule.DeterminantMod`, is satisfied verbatim by the constant character `1`;
this one is not.

⚠️ **`∃ σ, det ρ_{E,3}(σ) ≠ 1` and `det ρ_{E,3} ≠ 1` are different statements** and both are below.
Only the second is the sentence "the determinant character of `E[3]` is non-trivial" as a reader
would write it, and it needs the first plus a `MonoidHom.one_apply` step.

⚠️ **There is deliberately no certificate in which `E[3]` is `ℚ`-rational.**  Not for want of
searching: `#947`'s `ker_galoisRepMod_three_le_ker_galoisModularCyclotomicChar` *rules one out* over
`ℚ`, since `E[3] ⊆ E(ℚ)` would force `χ_3` of `ℚ` to be trivial, which
`exists_galoisModularCyclotomicChar_three_ne_one` says it is not.  So over `ℚ` such a curve does not
exist and hunting for one is wasted effort — that is Silverman III.8.1.1 doing its job.

⚠️ **Each certificate was tested by deleting the last named lemma from its script** (`#944`), so
that none of them closes by `rfl` or by a rationality that consumes nothing.

* Deleting the `exact galoisDetMod_three_ne_one_of_galoisModularCyclotomicChar_ne_one …` line from
  the load-bearing certificate, leaving the rest of its script untouched, gives

  ```
  error: unsolved goals
  σ : Gal(AlgebraicClosure ℚ/ℚ)
  hσ : (galoisModularCyclotomicChar ℚ (AlgebraicClosure ℚ) ⋯) σ ≠ 1
  hEq : galoisDetMod 3 = 1
  ⊢ False
  ```

  ⚠️ **Read the hypothesis list, not the error tag.**  What survives is a statement about `χ_3` and
  a statement about `galoisDetMod`, and *nothing relating them*: the certificate is closed by this
  file's identity and by nothing else.  A type mismatch could never have shown that
  (`EllipticCurves.TateModule.DeterminantMod` records the same distinction), which is why the test
  deletes the line rather than substituting a differently-typed argument into it.

* Deleting `galoisDetMod_three_eq_galoisModularCyclotomicChar` from the headline certificate leaves
  the whole headline as the residual goal, with nothing in scope to close it:

  ```
  error: unsolved goals
  ⊢ galoisDetMod 3 = galoisModularCyclotomicChar ℚ exampleField ⋯
  ```

The `ker ρ_{E,3} ≤ ker χ_3` certificate is stated as an `example` on purpose: it is **not** a new
statement.  `#947` already ships it as
`ker_galoisRepMod_three_le_ker_galoisModularCyclotomicChar`, proved from Silverman III.8.1.1
directly.  What the `example` shows is that the *same* theorem is now a two-line corollary of an
identity of characters rather than of an inclusion of kernels — which is the sense in which this
file subsumes that one. -/

section Nonvacuity

/-- The curve `y² + y = x³` over `ℚ`, this front's standard `n = 3` certificate curve. -/
private noncomputable def exampleCurveThree : Affine ℚ := ⟨0, 0, 1, 0, 0⟩

/-- An algebraically closed extension of `ℚ`, so that `Gal(F/ℚ)` is not the trivial group. -/
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
/-- The headline on a curve that exists, with both sides written out. -/
example : galoisDetMod (W' := exampleCurveThree) (F := exampleField) 3
    = galoisModularCyclotomicChar ℚ exampleField
        (natCard_rootsOfUnity_of_ne_zero (F := exampleField) (n := 3) exampleThree) :=
  galoisDetMod_three_eq_galoisModularCyclotomicChar exampleTwo exampleThree

open Classical in
/-- Some `σ ∈ Gal(ℚ̄/ℚ)` has `det ρ_{E,3}(σ) ≠ 1`, on the same curve. -/
example : ∃ σ : exampleField ≃ₐ[ℚ] exampleField,
    galoisDetMod (W' := exampleCurveThree) (F := exampleField) 3 σ ≠ 1 := by
  obtain ⟨σ, hσ⟩ := exists_galoisModularCyclotomicChar_three_ne_one
    (natCard_rootsOfUnity_of_ne_zero (F := exampleField) (n := 3) exampleThree)
  exact ⟨σ, galoisDetMod_three_ne_one_of_galoisModularCyclotomicChar_ne_one
    (W := exampleCurveThree) exampleTwo exampleThree hσ⟩

open Classical in
/-- **⚠️ THE LOAD-BEARING CERTIFICATE**: on `y² + y = x³` over `ℚ`, the mod-`3` determinant
character is **not** the trivial homomorphism `Gal(ℚ̄/ℚ) →* (ZMod 3)ˣ`.

Unconditional, and the negated *character* equation rather than an existential about a point of the
group. -/
example : galoisDetMod (W' := exampleCurveThree) (F := exampleField) 3
    ≠ (1 : (exampleField ≃ₐ[ℚ] exampleField) →* (ZMod 3)ˣ) := by
  obtain ⟨σ, hσ⟩ := exists_galoisModularCyclotomicChar_three_ne_one
    (natCard_rootsOfUnity_of_ne_zero (F := exampleField) (n := 3) exampleThree)
  intro hEq
  exact galoisDetMod_three_ne_one_of_galoisModularCyclotomicChar_ne_one
    (W := exampleCurveThree) exampleTwo exampleThree hσ (by rw [hEq]; rfl)

open Classical in
/-- **`ker ρ_{E,3} ≤ ker χ_3` re-derived from the headline.**

⚠️ **Not a new theorem.**  It is `#947`'s
`ker_galoisRepMod_three_le_ker_galoisModularCyclotomicChar`
(`EllipticCurves.FunctionField.WeilPairingRationalTorsionGalois`) verbatim, and it is stated here as
an `example` for exactly that reason.  The point is the *proof*: `#947` derives it from Silverman
III.8.1.1, and here it falls out of `galoisDetMod_eq_one_of_mem_ker` — which is unconditional and
true of the constant character — plus this file's identity. -/
example {S F : Type*} [Field S] [Field F] [Algebra S F] {W : Affine S} [W.IsElliptic]
    [IsAlgClosed F] (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) :
    (galoisRepMod (W' := W) (F := F) 3).ker
      ≤ (galoisModularCyclotomicChar S F
          (natCard_rootsOfUnity_of_ne_zero (F := F) (n := 3) h3)).ker :=
  fun σ hσ => MonoidHom.mem_ker.mpr
    (by rw [← galoisDetMod_three_apply_eq_galoisModularCyclotomicChar (W := W) σ h2 h3]
        exact galoisDetMod_eq_one_of_mem_ker 3 hσ)

end Nonvacuity

end Galois

end WeierstrassCurve.Affine
