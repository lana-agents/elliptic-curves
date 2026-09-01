/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import EllipticCurves.Fixtures
import EllipticCurves.TateModule.Kernel
import EllipticCurves.Torsion.ThreeTorsionStructure
import Mathlib.Algebra.Module.ZMod
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.LinearAlgebra.Determinant

/-!
# The mod-`n` determinant character `det ρ_{E,n} : G →* (ZMod n)ˣ`

`EllipticCurves.TateModule.Determinant` builds `galoisDetTwo : G →* ℤ_[2]ˣ` by feeding the `2`-adic
representation `galoisRep 2` into `LinearEquiv.det`.  There was no finite-level analogue, for a
single reason: `galoisRepMod n` lands in `E[n] ≃ₗ[ℤ] E[n]`, and the determinant of a `ℤ`-linear
endomorphism of a finite group is not the invariant one wants.  The right base ring is `ZMod n`, and
`E[n]` is a `ZMod n`-module for free:

```lean
instance : Module (ZMod n) (W.torsion n) := AddCommGroup.zmodModule fun P => nsmul_mem_torsion P
```

`nsmul_mem_torsion` is `(n : ℕ) • P = 0` on `E[n]`, which is exactly the hypothesis
`AddCommGroup.zmodModule` asks for.  No `[IsAlgClosed F]`, no `[W.IsElliptic]`, no characteristic
assumption.  Everything in the first half of this file follows from that instance alone.

## What this file supplies, and what it does not

It supplies `galoisDetMod n : (F ≃ₐ[S] F) →* (ZMod n)ˣ`, the mod-`n` determinant of the Galois
action on `E[n]` — the odd-`n` companion of `galoisDetTwo`, which exists only `ℓ`-adically and only
at `ℓ = 2`.

⚠️ **It supplies the left-hand side of `det ρ_{E,3} = χ_3` and nothing else.**  The cyclotomic
character does not appear below, the Weil pairing does not appear below, and nothing here should be
read as progress on the identification that `EllipticCurves.TateModule.Determinant` names as the
reason the determinant is interesting.  That identification is a separate deliverable, it needs the
pairing, and it is delivered — at `n = 3` — in
`EllipticCurves.FunctionField.WeilPairingDeterminantCharacter` (`#958`), which imports this file.
⚠️ Nothing below changed when it landed: this file still supplies only the left-hand side, and the
statement `galoisDetMod 3 = χ_3` is not available from this file's imports.

⚠️ **`EllipticCurves.FunctionField.WeilPairingDeterminant` (`#951`) proves that identification in
coordinates, and priced this file's object as out of reach.**  It states `a * d - b * c ≡ χ_n(σ)`
for a *chosen* generating pair, with the four matrix entries carried as integers in hypotheses —
deliberately using no `Module (ZMod n)` structure, no basis and no `LinearMap.det`.  Verbatim,
its Scope section said

> Writing the conclusion as an equation between `LinearEquiv.det ∘ ρ_{E,3}` and `χ_3` needs a
> `Module (ZMod 3)` structure on `E[3]` and a `Basis` for it; `nonempty_torsionThree_addEquiv`
> supplies an `≃+` and not that.

⚠️ **Be exact about which clause of that is wrong, because two of the three are true.**  The
`Basis` clause is false — `LinearEquiv.det` is basis-free, and `galoisDetMod` below uses no basis.
The `Module (ZMod 3)` clause is true, and so is the clause about `nonempty_torsionThree_addEquiv`,
since an `≃+` is indeed not a module structure.  What fails is the *inference*, that no such
module structure is available at all.  `AddCommGroup.zmodModule` applied to `nsmul_mem_torsion`
supplies one, *unconditionally* — no algebraically closed field, no ellipticity, no `#E[3] = 9`.
See `torsionZModModule`.  ⚠️ The quotation is of the text as `#951` merged it; that sentence is
repaired in place in the same pull request as this file, so a grep of `main` will not find it.

⚠️ The two are complementary rather than competing, and it is worth being exact about how.  `#951`
has an **equation**; this file has an **object**.  A coordinate determinant is a number attached to
a chosen pair; `galoisDetMod n` is a group homomorphism `G →* (ZMod n)ˣ`, which is the form a
representation-theoretic consumer wants and the form `galoisDetTwo` already takes `2`-adically.
⚠️ That the two agree — `galoisDetMod 3 = χ_3` as an identity of monoid homomorphisms — is neither
file's content; it is `galoisDetMod_three_eq_galoisModularCyclotomicChar` in
`EllipticCurves.FunctionField.WeilPairingDeterminantCharacter` (`#958`), which consumes this file's
`galoisDetMod`, `galoisRepModLinear_apply_coe`, `finite_torsion_three_zmod` and
`finrank_torsion_three`, and `#951`'s coordinate identity.  ⚠️ It does **not** cite
`basisTorsionThree`: it builds its own basis out of the pairing pair, because `#951`'s hypotheses
are about a *given* `P` and `T` while `basisTorsionThree` is an arbitrary basis.  So the sentence
below calling `basisTorsionThree` "the interface a coordinate computation downstream will need"
predicted the wrong interface; what the downstream computation needed was `finrank_torsion_three`,
from which it builds the basis it can name.

## ⚠️ `LinearEquiv.det` is basis-free, and that is why no `Gal(F/S)`-stable basis is needed

The obstruction usually quoted against a finite-level determinant is that `E[n]` carries no basis
compatible with the Galois action.  True, and irrelevant: `LinearEquiv.det` is defined without
reference to a basis, exactly as `galoisDetTwo` is.  A basis enters this file in one place only —
`basisTorsionThree`, which exists to be the interface a *coordinate* computation downstream will
need.  ⚠️ It is not canonical, nothing here may depend on which basis it picks, and it is
deliberately not used to compute any determinant.  Even the rank is proved without it: see
`finrank_torsion_three`.

## ⚠️ Freeness is automatic; finiteness is not; and the rank is the whole point

`LinearMap.det` is `1`, and `LinearMap.trace` is `0`, on modules that are **not** free and finite.
So `galoisDetMod` is definable with no hypotheses whatsoever and would be identically `1` on an
`E[n]` that happened to be zero — the same trap `EllipticCurves.TateModule.Determinant` records for
`galoisTraceTwo`.  At `n = 3` the two halves of that hypothesis cost very different amounts, and
both figures below are measured rather than assumed:

* **`Module.Free (ZMod 3) (E[3])` is found by `inferInstance`, with no hypotheses at all.**
  `Fact (Nat.Prime 3)` is an instance, so `Field (ZMod 3)` is, so every `ZMod 3`-module is free.
  ⚠️ There is therefore **no `free_torsion_three` below**: it would be a theorem proved by
  `inferInstance`.  It is certified in the Non-vacuity block instead.
* **`Module.Finite (ZMod 3) (E[3])` is not.**  It is `finite_torsion_three_zmod`, and it needs
  `(3 : F) ≠ 0`.

`finrank_torsion_three` is what actually rules the junk value out, and it is the statement carrying
`[IsAlgClosed F]`, `[W.IsElliptic]`, `(2 : F) ≠ 0` and `(3 : F) ≠ 0`.

## Main definitions

* `AddEquiv.toZModLinearEquiv` — an additive equivalence of `ZMod n`-modules is `ZMod n`-linear.
* `LinearEquiv.intAutMulEquivZModAut` — `(M ≃ₗ[ℤ] M) ≃* (M ≃ₗ[ZMod n] M)`.
* `WeierstrassCurve.Affine.torsionZModModule` — `E[n]` as a `ZMod n`-module.
* `WeierstrassCurve.Affine.galoisRepModLinear` — `ρ_{E,n}` as a `ZMod n`-linear representation.
* `WeierstrassCurve.Affine.galoisDetMod` — the determinant character `G →* (ZMod n)ˣ`.
* `WeierstrassCurve.Affine.basisTorsionThree` — a `ZMod 3`-basis of `E[3]` indexed by `Fin 2`.

## Main statements

* `WeierstrassCurve.Affine.galoisRepModLinear_apply_coe` — the `ZMod n`-linear representation is the
  same function as `galoisRepMod n`; it is `rfl`.
* `WeierstrassCurve.Affine.ker_galoisRepModLinear` — and therefore has the same kernel.
* `WeierstrassCurve.Affine.galoisDetMod_eq_one_of_mem_ker` — the mod-`n` twin of
  `galoisDetTwo_eq_one_of_mem_ker`.
* `WeierstrassCurve.Affine.ker_galoisRepMod_le_ker_galoisDetMod` — the same as an inclusion.
* `WeierstrassCurve.Affine.finite_torsion_three_zmod` — `E[3]` is a finite `ZMod 3`-module.
* `WeierstrassCurve.Affine.finrank_torsion_three` — `Module.finrank (ZMod 3) E[3] = 2`.

## Naming and placement

`AddEquiv.toZModLinearEquiv` and `LinearEquiv.intAutMulEquivZModAut` mention no curve and are
generic module theory; they sit at the root, in the namespaces of the objects they convert, beside
Mathlib's `AddMonoidHom.toZModLinearMap`.  Their natural home is `Mathlib.Algebra.Module.ZMod`.

⚠️ The file is under `TateModule/` rather than `FunctionField/` **and that is load-bearing for what
comes next**: nothing under `TateModule/` imports anything under `FunctionField/` (grepped in both
directions), and the identification of this determinant with the cyclotomic character has to import
the pairing.  Putting the character here would invert the layering.

## Explicitly out of scope

* **The Weil pairing**, and hence `det ρ_{E,3} = χ_3`.  Named above.
* **The `ℓ`-adic determinant.**  `galoisDetTwo` is untouched.  ⚠️ Note also that `det ρ_{E,2} = χ_2`
  *mod `2`* is content-free — `(ZMod 2)ˣ` is trivial, so both sides are `1` — and is **not** the
  `ℓ`-adic statement over `ℤ_[2]`, which remains open.  The two are easily confused and only one of
  them is interesting.
* **Finiteness and rank at general `n`** — ⚠️ **still out of scope of *this file*, but no longer
  out of reach.**  This bullet used to read *"Only `n = 3` is done, because only `n = 3` has
  `card_torsion_three` available.  ⚠️ `n = 2` has `exists_closure_pair_eq_torsion_two` and could be
  done the same way; it is not done here because nothing consumes it."*  Both clauses are spent:
  `EllipticCurves.Torsion.ThreePrimary`'s `nonempty_torsion_addEquiv_zmod_sq_of_smooth` supplies the
  structure theorem at every `3`-smooth `n`, and `EllipticCurves.TateModule.DeterminantModSmooth`
  (`#1240`) turns it into `Module.Free`, `Module.Finite`, `finrank = 2` and a `Fin 2`-basis there —
  including the `n = 2` instances, which it takes from `card_torsion_two` rather than from
  `exists_closure_pair_eq_torsion_two`.  ⚠️ **The third clause was not stale and is the reason that
  file exists**: *"at composite `n`, `ZMod n` is not a field, so even freeness stops being
  automatic"* is true, `Module.Free (ZMod 12) (E[12])` is genuinely not found by instance search,
  and freeness there is a theorem transported along a chosen isomorphism rather than the
  `inferInstance` it is at `n = 2` and `n = 3`.  ⚠️ Nothing below changed when that file landed:
  `finrank_torsion_three` is still proved here from the cardinality, precisely to keep an arbitrary
  choice out of the proof of a choice-independent number, and the general statement — which makes
  that choice — does not replace it.
* **A `Gal(F/S)`-stable basis of `E[3]`.**  Does not exist in general and is not needed.
* **The trace and characteristic polynomial** mod `n`.  `galoisTraceTwo`'s finite-level analogue
  would need the same freeness input and has no consumer.  ⚠️ Only the first half of that is spent:
  `EllipticCurves.TateModule.DeterminantModSmooth` supplies the freeness input at every `3`-smooth
  `n`, and there is still no consumer.

## References

* [J. H. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.7.
-/

section ZModLinear

variable {n : ℕ} {M M₁ : Type*} [AddCommGroup M] [Module (ZMod n) M] [AddCommGroup M₁]
  [Module (ZMod n) M₁]

/-- **An additive equivalence between `ZMod n`-modules is `ZMod n`-linear.**

The `ZMod n`-action on a group killed by `n` is determined by the additive structure, so there is
nothing to check beyond `ZMod.map_smul`.  This is the equivalence-level companion of Mathlib's
`AddMonoidHom.toZModLinearMap`. -/
def AddEquiv.toZModLinearEquiv (e : M ≃+ M₁) : M ≃ₗ[ZMod n] M₁ :=
  { e with map_smul' := ZMod.map_smul (n := n) e.toAddMonoidHom }

@[simp]
lemma AddEquiv.coe_toZModLinearEquiv (e : M ≃+ M₁) : ⇑(e.toZModLinearEquiv (n := n)) = e := rfl

/-- **`ℤ`-linear and `ZMod n`-linear automorphisms of a `ZMod n`-module are the same group.**

Both are just additive automorphisms: a `ℤ`-linear map is an additive map, and an additive map
between `ZMod n`-modules is `ZMod n`-linear.  ⚠️ All three of `left_inv`, `right_inv` and `map_mul'`
are `rfl`, which is what lets `galoisRepModLinear` below be a plain `MonoidHom.comp` rather than a
hand-built structure — and hence what makes `galoisRepModLinear_apply_coe` a `rfl` too. -/
def LinearEquiv.intAutMulEquivZModAut : (M ≃ₗ[ℤ] M) ≃* (M ≃ₗ[ZMod n] M) where
  toFun e := AddEquiv.toZModLinearEquiv e.toAddEquiv
  invFun e := { e.toAddEquiv with map_smul' := fun c x => by simp }
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

@[simp]
lemma LinearEquiv.coe_intAutMulEquivZModAut (e : M ≃ₗ[ℤ] M) :
    ⇑(LinearEquiv.intAutMulEquivZModAut (n := n) e) = e := rfl

end ZModLinear

namespace WeierstrassCurve.Affine

open scoped AddSubgroup

/-- **`E[n]` is a `ZMod n`-module**, because every one of its elements is killed by `n`
(`nsmul_mem_torsion`).

Unconditional: no algebraically closed field, no ellipticity, no characteristic hypothesis.  It is
the instance the whole file rests on, and the reason there was no mod-`n` determinant before is that
it had not been written down.

⚠️ **`[NeZero n]` is unused in the elaborated term and is kept on purpose** (`#1277`,
`nolint unusedArguments`; `#1272`'s Part C reached the same verdict).  `ZMod 0 = ℤ` and the module
structure does survive at `n = 0`, but the object this instance names is *`E[n]` as a
`ZMod n`-module* and every consumer is at `n ≠ 0`; dropping it would change the instance's type
and every mention of it downstream. -/
@[nolint unusedArguments]
instance torsionZModModule {F : Type*} [Field F] [DecidableEq F] {W : Affine F} (n : ℕ)
    [NeZero n] : Module (ZMod n) (W.torsion n) :=
  AddCommGroup.zmodModule fun P => nsmul_mem_torsion P

variable {S F : Type*} [Field S] [Field F] [DecidableEq F] [Algebra S F] {W' : Affine S}

section Representation

variable (n : ℕ) [NeZero n]

/-- **The mod-`n` Galois representation as a `ZMod n`-linear representation**,
`ρ_{E,n} : G →* Aut_{ℤ/n}(E[n])`.

`galoisRepMod n` (`EllipticCurves.TateModule.GaloisAction`) already produces the action as a
`ℤ`-linear automorphism; over a `ZMod n`-module that is the *same* automorphism, transported by
`LinearEquiv.intAutMulEquivZModAut`.  ⚠️ It is a transport and not a redefinition, which is why
`galoisRepModLinear_apply_coe` and `ker_galoisRepModLinear` below cost nothing. -/
noncomputable def galoisRepModLinear :
    (F ≃ₐ[S] F) →* ((W'⁄F).torsion n ≃ₗ[ZMod n] (W'⁄F).torsion n) :=
  (LinearEquiv.intAutMulEquivZModAut (n := n)).toMonoidHom.comp
    (galoisRepMod (W' := W') (F := F) n)

@[simp]
lemma galoisRepModLinear_apply_coe (σ : F ≃ₐ[S] F) (P : (W'⁄F).torsion n) :
    galoisRepModLinear (W' := W') (F := F) n σ P = σ • P :=
  rfl

/-- **The mod-`n` determinant character**, `det ρ_{E,n} : G →* (ZMod n)ˣ`.

`LinearEquiv.det` applied to `galoisRepModLinear n`, so — exactly as for `galoisDetTwo` — it
involves **no choice of basis**.

⚠️ This is where the "`E[n]` has no `Gal(F/S)`-stable basis" objection dissolves: a stable basis
would be needed to make the *matrix* of `ρ_{E,n}` canonical, and the matrix is not canonical.  The
determinant is, and Mathlib defines it without one.

⚠️ Definable with no hypotheses at all, and *worthless* without freeness: `LinearMap.det` is `1` on
a module that is not free and finite.  See `finrank_torsion_three` for the statement that rules that
out at `n = 3`, and `EllipticCurves.TateModule.DeterminantModSmooth`'s `finrank_torsion_of_smooth`
for the one that rules it out at every `3`-smooth `n > 1`. -/
noncomputable def galoisDetMod : (F ≃ₐ[S] F) →* (ZMod n)ˣ :=
  (LinearEquiv.det : ((W'⁄F).torsion n ≃ₗ[ZMod n] (W'⁄F).torsion n) →* (ZMod n)ˣ).comp
    (galoisRepModLinear n)

theorem galoisDetMod_apply (σ : F ≃ₐ[S] F) :
    galoisDetMod (W' := W') (F := F) n σ
      = LinearEquiv.det (M := (W'⁄F).torsion n) (galoisRepModLinear n σ) :=
  rfl

/-- The determinant character is trivial at the identity. -/
@[simp]
theorem galoisDetMod_one : galoisDetMod (W' := W') (F := F) n 1 = 1 := map_one _

/-- **The `ZMod n`-linear representation has the same kernel as the `ℤ`-linear one.**

The transport is an equivalence, so this is `EmbeddingLike.map_eq_one_iff`; it is what lets every
kernel statement in `EllipticCurves.TateModule.Kernel` be quoted against `galoisRepModLinear`
without restating it. -/
theorem ker_galoisRepModLinear :
    (galoisRepModLinear (W' := W') (F := F) n).ker = (galoisRepMod (W' := W') (F := F) n).ker := by
  ext σ
  simp only [MonoidHom.mem_ker, galoisRepModLinear, MonoidHom.coe_comp, Function.comp_apply,
    MulEquiv.coe_toMonoidHom, EmbeddingLike.map_eq_one_iff]

/-- **On `ker ρ_{E,n}` the mod-`n` determinant character is trivial** — the mod-`n` twin of
`galoisDetTwo_eq_one_of_mem_ker`, stated in the same shape.

⚠️ Unconditional, and therefore *not* evidence that the character is interesting: it would hold
verbatim for the constant map `1`.  The statement that distinguishes it is
`finrank_torsion_three`. -/
theorem galoisDetMod_eq_one_of_mem_ker {σ : F ≃ₐ[S] F}
    (hσ : σ ∈ (galoisRepMod (W' := W') (F := F) n).ker) :
    galoisDetMod (W' := W') (F := F) n σ = 1 := by
  rw [galoisDetMod_apply, MonoidHom.mem_ker.mp ((ker_galoisRepModLinear n).ge hσ), map_one]

/-- **`ker ρ_{E,n} ≤ ker (det ρ_{E,n})`**, the subgroup form of the previous statement. -/
theorem ker_galoisRepMod_le_ker_galoisDetMod :
    (galoisRepMod (W' := W') (F := F) n).ker ≤ (galoisDetMod (W' := W') (F := F) n).ker :=
  fun _ hσ => MonoidHom.mem_ker.mpr (galoisDetMod_eq_one_of_mem_ker n hσ)

end Representation

/-! ### `E[3]` is free of rank `2` over `ZMod 3`

The statements that make `galoisDetMod 3` worth defining.  They are the only ones in this file
carrying `[IsAlgClosed F]`, `[W.IsElliptic]`, `(2 : F) ≠ 0` and `(3 : F) ≠ 0`. -/

section ThreeTorsion

variable {W : Affine F} [W.IsElliptic] [IsAlgClosed F]

omit [W.IsElliptic] [IsAlgClosed F] in
/-- **`E[3]` is a finite `ZMod 3`-module.**

⚠️ This is the half of `LinearEquiv.det`'s hypothesis that is *not* automatic; see the note above.
`finite_torsion_three` (`EllipticCurves.Torsion.ThreeTorsion`) supplies `Finite (E[3])` from `h3`,
and `Module.Finite.of_finite` upgrades it.

⚠️ It cannot be an `instance`: it carries the hypothesis `(3 : F) ≠ 0`. -/
theorem finite_torsion_three_zmod (h3 : (3 : F) ≠ 0) : Module.Finite (ZMod 3) (W.torsion 3) :=
  haveI := W.finite_torsion_three h3
  Module.Finite.of_finite

open Classical in
/-- **`E[3]` has rank `2` over `ZMod 3`.**

The discriminating statement of the file, and the finite-level analogue of
`Module.finrank ℤ_[2] (T₂E) = 2` (`EllipticCurves.TateModule.Free`).  ⚠️ `Module.finrank` is `0` on
a module that is not free and finite, so this is simultaneously the rank computation *and* the
certificate that `galoisDetMod 3` is not `LinearEquiv.det`'s junk value — the same double duty
`galoisTraceTwo_one` performs `2`-adically.

⚠️ **Proved from the cardinality, not from a chosen isomorphism.**  `nonempty_torsionThree_addEquiv`
would give `E[3] ≃ₗ[ZMod 3] (ℤ/3)²` in one line through `AddEquiv.toZModLinearEquiv`, and the rank
would follow — but only after `.some` had picked one of the isomorphisms, putting an arbitrary
choice into the proof of a choice-independent number.  `Module.card_eq_pow_finrank` against
`card_torsion_three` avoids it, and it makes visible that the load-bearing input is `#E[3] = 9`.

⚠️ The script below consumes `h2` at exactly one place, `card_torsion_three h2 h3`, but **inside
that lemma `h2` is used three times over and not once**: `card_setOf_equation_eq_two h2` (the fibre
above an `x` has exactly two points), `Ψ₂Sq_eval_ne_zero_of_root_Ψ₃ h2` (a root of `Ψ₃` is never a
root of `Ψ₂Sq`) and `card_roots_Ψ₃ h2 h3`.  ⚠️ So "`h2` enters through the separability of `Ψ₃`" is
too narrow a reading — the fibre count is at least as fundamental, and `card_roots_Ψ₃` consumes both
hypotheses at once, so they do not split cleanly into "`h2` for `Ψ₃`, `h3` for the value group".
The two are not interchangeable; see the third measured run below for what does and does not
establish that. -/
theorem finrank_torsion_three (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) :
    Module.finrank (ZMod 3) (W.torsion 3) = 2 := by
  haveI := W.finite_torsion_three h3
  haveI := finite_torsion_three_zmod (W := W) h3
  haveI : Fintype (W.torsion 3) := Fintype.ofFinite _
  have hpow : Fintype.card (W.torsion 3)
      = Fintype.card (ZMod 3) ^ Module.finrank (ZMod 3) (W.torsion 3) :=
    Module.card_eq_pow_finrank
  rw [ZMod.card, ← Nat.card_eq_fintype_card, card_torsion_three h2 h3] at hpow
  exact (Nat.pow_right_injective (by norm_num) (show (3 : ℕ) ^ 2 = 3 ^ _ by omega)).symm

/-- **A `ZMod 3`-basis of `E[3]` indexed by `Fin 2`.**

`Module.finBasisOfFinrankEq` against `finrank_torsion_three`.  ⚠️ Not canonical — it is the
interface a coordinate computation needs, and any statement proved with it must be one whose truth
does not depend on which basis is chosen.  `galoisDetMod` does **not** use it, deliberately:
`LinearEquiv.det` is basis-free. -/
noncomputable def basisTorsionThree (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) :
    Module.Basis (Fin 2) (ZMod 3) (W.torsion 3) :=
  haveI := finite_torsion_three_zmod (W := W) h3
  Module.finBasisOfFinrankEq _ _ (finrank_torsion_three h2 h3)

end ThreeTorsion

/-! ### Non-vacuity

⚠️ **The load-bearing certificate is `finrank_torsion_three` on a curve that exists**, because it is
the only statement here that `LinearEquiv.det`'s junk value cannot satisfy.  Everything else in this
file — `galoisDetMod`, `galoisDetMod_one`, `galoisDetMod_eq_one_of_mem_ker`,
`ker_galoisRepMod_le_ker_galoisDetMod` — is true verbatim of the constant character `1`, and would
be true if `E[3]` were the zero module.  That is precisely the hazard
`EllipticCurves.TateModule.Determinant` records for `galoisTraceTwo`, one level down.

The certificate curve is this front's standard `n = 3` one, `y² + y = x³` over `ℚ`, base-changed to
`AlgebraicClosure ℚ` with **`S = ℚ` and not `S = F`** — over `S = F` the group `Gal(F/S)` is trivial
and the schema certificate for `galoisDetMod` says nothing.

⚠️ **Four measured runs under three headings, one of which refuted what this file's first draft
asserted.**  ⚠️ The third heading carries two runs on purpose — a substitution test and a deletion
test — because they establish different things and only the second establishes anything;
the substitution test additionally reports **two** errors, a `Type mismatch` at the certificate
followed by the `Application type mismatch` at the argument, and only the second is quoted.  All
were re-run against the text as committed, with `lake env lean` on this file from the project root.
⚠️ That command reports errors in the `<file>:<line>:<col>: error(<tag>):` form quoted below;
`lake build` reports the same errors with an `error: <file>:<line>:<col>:` prefix instead.  ⚠️ And
`lake env lean` does **not** apply the `leanOptions` of `lakefile.toml`, so it does not run
`linter.style.longLine`: a file can be silent under `lake env lean` and still warn under
`lake build`.  This one did.

* **Freeness IS automatic, and the draft said it was not.**  `Module.Free (ZMod 3) (E[3])` is found
  by `inferInstance` with no hypotheses at all, because `Fact (Nat.Prime 3)` is an instance, hence
  `Field (ZMod 3)` is, hence every `ZMod 3`-module is free.  It is certified below rather than
  proved.  ⚠️ The consequence is that the file states no `free_torsion_three`: a theorem whose proof
  is `inferInstance` is noise, and one whose *docstring* claims it is hard is worse than noise.
* **Finiteness is NOT automatic.**  Deleting `finite_torsion_three_zmod` from a certificate and
  asking for `inferInstance` gives
  ```
  error(lean.synthInstanceFailed): failed to synthesize instance of type class
    Module.Finite (ZMod 3) ↥(((y2AddYEqX3 ℚ)⁄AlgClosedQ).torsion 3)
  ```
  So the two halves of `LinearEquiv.det`'s hypothesis have genuinely different costs here, and only
  one of them needs a hypothesis on `F`.
* **`(2 : F) ≠ 0` is consumed by the rank statement, and here is exactly how much a substitution
  test shows.**  Passing `exampleThree` where the certificate wants `exampleTwo` gives
  ```
  error: Application type mismatch: The argument
    exampleThree
  has type
    3 ≠ 0
  but is expected to have type
    2 ≠ 0
  in the application
    finrank_torsion_three exampleThree
  ```
  ⚠️ **That error says only that `3 ≠ 0` is not `2 ≠ 0`, and it would say the same of a hypothesis
  the proof never used** — a substituted argument is not a deleted input, which is the distinction
  this front recorded against `#951`.  ⚠️ Substituting `h3` for `h2` one level in, at
  `card_torsion_three`, is the *same* test and no better: it too reports a type mismatch rather than
  an unprovable goal.  The test that shows `h2` is load-bearing has to **delete** it from the
  statement and leave the script alone, and then the goal is what is left standing.  ⚠️ That run
  emits two messages as well — an `` Unknown identifier `h2` `` where the script still names it, and
  the one that carries the information:
  ```
  error: unsolved goals
  …
  h3 : 3 ≠ 0
  …
  hpow : Nat.card ↥(W.torsion 3) = 3 ^ Module.finrank (ZMod 3) ↥(W.torsion 3)
  ⊢ Module.finrank (ZMod 3) ↥(W.torsion 3) = 2
  ```
  ⚠️ Read that hypothesis list: `hpow` **survives**, because `Module.card_eq_pow_finrank` never
  wanted `h2`, and `finite_torsion_three`/`finite_torsion_three_zmod` do not either.  What is lost
  is only `card_torsion_three`, so the cardinality is never evaluated and the rank is not wrong but
  simply uncomputable from what remains.  That is the precise sense in which `#E[3] = 9` is the
  load-bearing input. -/

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

open Classical in
/-- **⚠️ THE LOAD-BEARING CERTIFICATE**: on a curve that exists, `E[3]` really has rank `2` over
`ZMod 3`, so `LinearEquiv.det` is not returning its junk value. -/
example : Module.finrank (ZMod 3) (((y2AddYEqX3 ℚ)⁄AlgClosedQ).torsion 3) = 2 :=
  finrank_torsion_three exampleTwo exampleThree

open Classical in
/-- **Freeness is automatic**, and this is the certificate that says so: no hypothesis, no lemma of
this development, just `inferInstance`, because `Field (ZMod 3)` is an instance.  ⚠️ This file's
first draft claimed the opposite in a docstring; the run is what corrected it. -/
example : Module.Free (ZMod 3) (((y2AddYEqX3 ℚ)⁄AlgClosedQ).torsion 3) := inferInstance

open Classical in
/-- Finiteness, which is **not** automatic, restated in full. -/
example : Module.Finite (ZMod 3) (((y2AddYEqX3 ℚ)⁄AlgClosedQ).torsion 3) :=
  finite_torsion_three_zmod exampleThree

open Classical in
/-- A `ZMod 3`-basis of `E[3]` on the same curve exists — the interface a coordinate computation
downstream will consume. -/
example : Nonempty (Module.Basis (Fin 2) (ZMod 3) (((y2AddYEqX3 ℚ)⁄AlgClosedQ).torsion 3)) :=
  ⟨basisTorsionThree exampleTwo exampleThree⟩

open Classical in
/-- The `ZMod 3`-module structure on `E[3]` on the same curve, with no hypotheses at all:
`torsionZModModule` is unconditional, and this is the check that it is found. -/
example : Nonempty (Module (ZMod 3) (((y2AddYEqX3 ℚ)⁄AlgClosedQ).torsion 3)) :=
  ⟨inferInstance⟩

open Classical in
/-- The determinant character exists on a curve that exists and is trivial at `1`, restated in full
rather than obtained-and-projected. -/
example : galoisDetMod (W' := y2AddYEqX3 ℚ) (F := AlgClosedQ) 3 1 = 1 :=
  galoisDetMod_one 3

open Classical in
/-- The determinant character on the same curve, at a schema `σ` in the kernel of `ρ_{E,3}`, with
the conclusion written out. -/
example (σ : AlgClosedQ ≃ₐ[ℚ] AlgClosedQ)
    (hσ : σ ∈ (galoisRepMod (W' := y2AddYEqX3 ℚ) (F := AlgClosedQ) 3).ker) :
    galoisDetMod (W' := y2AddYEqX3 ℚ) (F := AlgClosedQ) 3 σ = 1 :=
  galoisDetMod_eq_one_of_mem_ker 3 hσ

open Classical in
/-- The kernel inclusion on the same curve, with both subgroups written out. -/
example :
    (galoisRepMod (W' := y2AddYEqX3 ℚ) (F := AlgClosedQ) 3).ker
      ≤ (galoisDetMod (W' := y2AddYEqX3 ℚ) (F := AlgClosedQ) 3).ker :=
  ker_galoisRepMod_le_ker_galoisDetMod 3

end Nonvacuity

end WeierstrassCurve.Affine
