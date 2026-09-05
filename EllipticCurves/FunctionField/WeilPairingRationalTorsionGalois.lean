/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import EllipticCurves.Fixtures
import EllipticCurves.FunctionField.WeilPairingRationalTorsion
import EllipticCurves.TateModule.Kernel
import Mathlib.FieldTheory.Galois.Infinite

/-!
# `μ_3 ⊆ K` literally, `ker ρ_{E,3} ≤ ker χ_3`, and the fact that `χ_3` of `ℚ` is not trivial

`EllipticCurves.FunctionField.WeilPairingRationalTorsion` (`#948`) proved Silverman AEC III.8.1.1 at
`n = 3` in the form a consumer can check:

```
(∀ P ∈ E[3], σ • P = P)  →  ∀ t ∈ μ_3(F), σ t = t.
```

Its Scope section then named three things it did not deliver.  Two of those were declared out of
reach on grounds that turn out to be false, and this file is the three of them.

* **`μ_3 ⊆ K`, in Silverman's own words.**  That file says the field-theoretic restatement "needs
  `[IsGalois S F]`, and this front carries no `IsGalois` instance anywhere".  True as observed —
  and the cause is a **synthesis trap**, described below, not an absence.  Two `private instance`
  lines repair it, and `mem_range_algebraMap_of_torsion_three_fixed` is then one term.
* **`ker ρ_{E,3} ≤ ker χ_3`.**  Not named there at all.  This is the shape
  `EllipticCurves.TateModule` consumes: `mem_ker_galoisRepMod_iff` unfolds membership in
  `ker (galoisRepMod 3)` to exactly `#948`'s hypothesis, so the inclusion is immediate.
* **`χ_3` of `ℚ` is not the trivial character.**  Both `#944` and `#948` declared this out of scope
  because "it needs an automorphism of `AlgebraicClosure ℚ` moving a primitive cube root of unity",
  and both recorded it as unspiked.  ⚠️ **It needs no such automorphism.**

## ⚠️ The reusable finding: count, do not construct

`exists_restrictRootsOfUnity_three_ne_self` produces a `σ` moving a cube root of unity without ever
naming one.  Suppose no `σ` moved any: then by `InfiniteGalois.mem_range_algebraMap_iff_fixed` every
element of `μ_3(Q̄)` would lie in the image of `ℚ`, so would be `algebraMap ℚ _ q` with `q ^ 3 = 1`
in `ℚ`, hence `1` — and `μ_3(Q̄)` has three elements.  The existential falls out of the
contradiction.

> **When the target is "this action is non-trivial", reach for a counting contradiction before
> reaching for an explicit element.**  Two issues in a row priced this statement as a construction,
> and that is what made it look expensive.

⚠️ **Why it is worth having rather than trivia.**  `#948`'s
`exists_torsion_three_smul_ne_self_of_galoisModularCyclotomicChar_ne_one` is a contrapositive whose
hypothesis nothing had ever been shown to satisfy; this satisfies it.  More sharply, it is the
non-vacuity certificate for that whole front: **drop the torsion hypothesis from
`forall_mem_rootsOfUnity_three_fixed_of_forall_torsion_fixed` and the conclusion is false**, not
merely unproved.  That is the strongest form a non-vacuity claim can take on a conditional theorem,
and it is exactly what `#916`'s rule is asking for.

## ⚠️ `IsGalois ℚ (AlgebraicClosure ℚ)` is unreachable by `inferInstance` in this project

It resolves in a file importing only Mathlib.  It stops resolving as soon as
`Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass` — hence `EllipticCurves.Basic`, hence anything
on this front — is in the import closure.  The `synthInstance` trace says why: the winning
`Algebra ℚ (AlgebraicClosure ℚ)` instance becomes `DivisionRing.toRatAlgebra`, whereas
`AlgebraicClosure.isAlgebraic` is stated for `AlgebraicClosure.instAlgebra`.  The two are defeq at
*default* transparency but not at *reducible*, so `tryResolve` rejects the instance and the chain
`Algebra.IsAlgebraic → IsAlgClosure → IsGalois` collapses.  ⚠️ Raising `maxSynthPendingDepth`,
`synthInstance.maxSize` or `synthInstance.maxHeartbeats` does **not** help; it is not a budget
problem.

The two `private instance` lines below repair it, and they are legal precisely because
`AlgebraicClosure.isAlgebraic ℚ` *does* typecheck against the goal: `exact` uses default
transparency where instance search does not.

## Main statements

* `exists_restrictRootsOfUnity_three_ne_self` — some `σ ∈ Gal(Q̄/ℚ)` moves some cube root of unity.
* `exists_galoisModularCyclotomicChar_three_ne_one` — the same, as `χ_3 σ ≠ 1`.
* `WeierstrassCurve.Affine.galoisModularCyclotomicChar_three_eq_one_of_forall_fixed` — if all of
  `Gal(F/S)` fixes all of `E[3]` then `χ_3` is the trivial homomorphism.
* `WeierstrassCurve.Affine.ker_galoisRepMod_three_le_ker_galoisModularCyclotomicChar` —
  `ker ρ_{E,3} ≤ ker χ_3`.
* `WeierstrassCurve.Affine.mem_range_algebraMap_of_torsion_three_fixed` — **`μ_3 ⊆ S`**.

## Naming and placement

The two statements about `ℚ ⊆ AlgebraicClosure ℚ` mention no curve and sit at the root, above
`namespace WeierstrassCurve.Affine`; `#938`, `#940`, `#944` and `#948` placed their curve-free
inputs the same way, and a curve namespace on a curve-free statement is `#903`'s defect one level
up.  ⚠️ Their natural home is `EllipticCurves.Galois.CyclotomicCharacter`, whose own docstring says
the character "is a genuine invariant of `σ`, and not bookkeeping that could be trivial for every
`σ` … no concrete field is needed to see it" — a claim these two finally *witness*.  ⚠️ Moving them
there would **not** be a pure relocation, though: neither *statement* mentions
`natCard_rootsOfUnity_of_ne_zero` — the second takes the count as an argument — but the *proof* of
`exists_restrictRootsOfUnity_three_ne_self` calls it, and it lives in
`EllipticCurves.FunctionField.WeilPairingSurjective`, which
`EllipticCurves.Galois.CyclotomicCharacter` does not import (measured: the identifier is unknown
there).  A move has to carry that lemma with it.  They are here for that reason and to keep
`Mathlib.FieldTheory.Galois.Infinite` out of the import closure of a file that most of this
development depends on.

Everything else is in `WeierstrassCurve.Affine` with `open CoordinateRing`, and `open Classical in`
on everything mentioning `torsion`.

## Explicitly out of scope

* **Everything in `EllipticCurves.FunctionField.WeilPairingRationalTorsion`** — its five
  declarations are imported, not restated.
* **`n = 2`.**  ⚠️ Not merely absent: at `n = 2` the analogue of
  `exists_galoisModularCyclotomicChar_three_ne_one` is **false**.  `χ_2` is the trivial character of
  every extension (`galoisModularCyclotomicChar_two_eq_one`, `#944`), and `#948`'s
  `forall_mem_rootsOfUnity_two_fixed` says so without a curve.  There is nothing here to mirror.
* **General `n`** — out of scope here (⚠️ no longer `#251`, which is closed — see below).  ⚠️ The
  ceiling inherited here is `#938`'s and **not** `#940`'s: everything routes through `#948`, which
  routes through surjectivity, which is blocked at composite `n` twice — by the crux and
  independently by the prime-order step.  `#940`'s "blocked only once" must not be quoted against
  this file.
* **`det ρ_{E,3} = χ_3`.**  ⚠️ `ker_galoisRepMod_three_le_ker_galoisModularCyclotomicChar` compares
  *kernels* and is strictly weaker, and nothing below moves the determinant identity.  ⚠️ This
  bullet originally added that the identity "needs a basis of `E[3]` as a free `ℤ/3`-module together
  with its Galois action, which does not exist here"; that reason was wrong and has been retired.
  `EllipticCurves.FunctionField.WeilPairingDeterminant` (`#951`) proves it in coordinates, taking
  the four matrix entries as integers in hypotheses — no module structure and no `Basis` anywhere.
* **The `ℓ`-adic level**, `ker ρ_{E,ℓ} ≤ ker χ_ℓ` for the Tate module.  Wants the pairing on
  `E[ℓ ^ k]` for every `k`.
* **The `IntermediateField` spelling** `μ_3(F) ⊆ (⊥ : IntermediateField S F)`.  It is
  `IntermediateField.mem_bot` away from what is stated and shipping both would be noise; Mathlib's
  own lemma is phrased with `Set.range (algebraMap S F)`, so that is what is used.

⚠️ **`#404` is closed — and so is the statement the general-`n` entry above was relettered to.**
PR #557 proved the on-curve identity for `(Φₙ/ΨSqₙ, ωₙ/ψₙ³)` at every index over a field with
`(2 : F) ≠ 0` and under `ψₙ(x, y) ≠ 0` — `WeierstrassCurve.Affine.equation_div_of_ψ_ne_zero`,
`EllipticCurves.Torsion.OmegaCrux`.  The *other* statement this tree also called `ωₙ` — the
identification of those coordinates with the **group-law** multiple `n • P` — is `#251` on its
`x`-half and `#1500` on its `y`-half, and **both are closed**: `hasXCoordFormula_of_two_ne_zero`
(`EllipticCurves.Torsion.NsmulOrder`) and `nsmul_eq_some_omegaY_of_ΨSq_ne_zero`
(`EllipticCurves.Torsion.NsmulYPeriodic`, PR #579), each at every index over a field with
`(2 : F) ≠ 0` and under the same `ΨSqₙ(x) ≠ 0`.  ⚠️ **So the entry is retired, not relettered a
second time**: the coordinate formula gates nothing here.  ⚠️ What *does* stand between this file
and a general index was **not** re-measured when the entry was retired — do not read this paragraph
as putting `#1184`, `#938` or `#962` in its place.  The two-reading account is
`EllipticCurves.FunctionField.MulByNPullback`.

## References

* [J. H. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.8, Corollary 8.1.1.
-/

section RationalCubeRoots

/-- `AlgebraicClosure ℚ` is algebraic over `ℚ`.

⚠️ Instance search does **not** find this once
`Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass` is in the import closure: the
`Algebra ℚ (AlgebraicClosure ℚ)` instance it settles on is `DivisionRing.toRatAlgebra`, whereas
`AlgebraicClosure.isAlgebraic` is stated for `AlgebraicClosure.instAlgebra`, and the two unify only
at default transparency.  `exact` uses default transparency, so naming the instance works where
searching for it does not.

⚠️ Named rather than anonymous (`#1277`): the auto-generated name was
`instIsAlgebraicRatAlgebraicClosure_ellipticCurves`, with the lake library name appended because the
type mentions no constant of this project.  `private` keeps it out of the linter's report but not
out of the environment. -/
private instance instIsAlgebraicRatAlgebraicClosure :
    Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) := AlgebraicClosure.isAlgebraic ℚ

/-- `AlgebraicClosure ℚ` is an algebraic closure of `ℚ`, supplied by hand for the reason above: the
library instance is blocked by the same unification failure, one level up.  With it,
`IsGalois ℚ (AlgebraicClosure ℚ)` is found.

⚠️ Named rather than anonymous, as for `instIsAlgebraicRatAlgebraicClosure`: the auto-generated name
was `instIsAlgClosureRatAlgebraicClosure_ellipticCurves`. -/
private instance instIsAlgClosureRatAlgebraicClosure :
    IsAlgClosure ℚ (AlgebraicClosure ℚ) := ⟨inferInstance, inferInstance⟩

/-- **Some `σ ∈ Gal(Q̄/ℚ)` moves some cube root of unity.**

⚠️ No automorphism is constructed, and none is needed.  If every `σ` fixed every element of
`μ_3(Q̄)` then each of them would lie in the image of `ℚ`
(`InfiniteGalois.mem_range_algebraMap_iff_fixed`), so each would be `algebraMap ℚ _ q` with
`q ^ 3 = 1` in `ℚ`, hence `q = 1`; but `μ_3(Q̄)` has three elements.  The witness falls out of the
count.

⚠️ `#944` and `#948` both declared this out of scope as needing an explicit automorphism of
`AlgebraicClosure ℚ`.  It does not, and the difference between the two prices is the whole reason
this lemma is worth writing down. -/
theorem exists_restrictRootsOfUnity_three_ne_self :
    ∃ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (ζ : rootsOfUnity 3 (AlgebraicClosure ℚ)),
      restrictRootsOfUnity (σ.toRingEquiv.toRingHom) 3 ζ ≠ ζ := by
  by_contra hcontra
  have hcon : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
      (ζ : rootsOfUnity 3 (AlgebraicClosure ℚ)),
      restrictRootsOfUnity (σ.toRingEquiv.toRingHom) 3 ζ = ζ := fun σ ζ =>
    not_not.mp fun h => hcontra ⟨σ, ζ, h⟩
  have h3 : (3 : AlgebraicClosure ℚ) ≠ 0 := by norm_num
  have hcard : Nat.card (rootsOfUnity 3 (AlgebraicClosure ℚ)) = 3 :=
    natCard_rootsOfUnity_of_ne_zero (F := AlgebraicClosure ℚ) (n := 3) h3
  haveI : Finite (rootsOfUnity 3 (AlgebraicClosure ℚ)) :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  haveI : Nontrivial (rootsOfUnity 3 (AlgebraicClosure ℚ)) :=
    Finite.one_lt_card_iff_nontrivial.mp (by rw [hcard]; norm_num)
  obtain ⟨ζ, hζ⟩ := exists_ne (1 : rootsOfUnity 3 (AlgebraicClosure ℚ))
  obtain ⟨q, hq⟩ := (InfiniteGalois.mem_range_algebraMap_iff_fixed
      (((ζ : (AlgebraicClosure ℚ)ˣ) : AlgebraicClosure ℚ))).mpr fun σ => by
    have := congrArg (fun ξ : rootsOfUnity 3 (AlgebraicClosure ℚ) =>
      ((ξ : (AlgebraicClosure ℚ)ˣ) : AlgebraicClosure ℚ)) (hcon σ ζ)
    simpa using this
  have hz : ((ζ : (AlgebraicClosure ℚ)ˣ) : AlgebraicClosure ℚ) ^ 3 = 1 := by
    have h := ζ.2
    rw [mem_rootsOfUnity] at h
    have := congrArg (Units.val) h
    push_cast at this
    exact this
  have hq3 : q ^ 3 = 1 := by
    have : (algebraMap ℚ (AlgebraicClosure ℚ)) (q ^ 3) = (algebraMap ℚ (AlgebraicClosure ℚ)) 1 := by
      rw [map_pow, hq, hz, map_one]
    exact (algebraMap ℚ (AlgebraicClosure ℚ)).injective this
  have hq1 : q = 1 := by nlinarith [sq_nonneg q, sq_nonneg (q - 1), sq_nonneg (q + 1)]
  refine hζ (Subtype.ext (Units.ext ?_))
  rw [← hq, hq1, map_one, OneMemClass.coe_one, Units.val_one]

/-- **The mod-`3` cyclotomic character of `ℚ` is not trivial**, which is
`exists_restrictRootsOfUnity_three_ne_self` read through
`galoisModularCyclotomicChar_eq_one_iff`.

⚠️ Contrast `galoisModularCyclotomicChar_two_eq_one` (`#944`), which says `χ_2` is trivial for
*every* extension.  Together the two are why Silverman III.8.1.1 has content at `n = 3` and none at
`n = 2`, and why `#948` states the `n = 2` case without a torsion hypothesis.

⚠️ The count `hn` is an argument rather than derived from `natCard_rootsOfUnity_of_ne_zero`, so this
statement depends on nothing in `EllipticCurves.FunctionField`; a caller on this front discharges it
with that lemma at `(3 : AlgebraicClosure ℚ) ≠ 0`. -/
theorem exists_galoisModularCyclotomicChar_three_ne_one
    (hn : Nat.card { x // x ∈ rootsOfUnity 3 (AlgebraicClosure ℚ) } = 3) :
    ∃ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ,
      galoisModularCyclotomicChar ℚ (AlgebraicClosure ℚ) hn σ ≠ 1 := by
  obtain ⟨σ, ζ, hσ⟩ := exists_restrictRootsOfUnity_three_ne_self
  refine ⟨σ, fun h => hσ ?_⟩
  have := (galoisModularCyclotomicChar_eq_one_iff hn σ).mp h (ζ : (AlgebraicClosure ℚ)ˣ) ζ.2
  exact Subtype.ext (Units.ext (by rw [restrictRootsOfUnity_coe_apply]; exact this))

end RationalCubeRoots

namespace WeierstrassCurve.Affine

open CoordinateRing

variable {S F : Type*} [Field S] [Field F] [Algebra S F] {W : Affine S} [W.IsElliptic]
  [IsAlgClosed F]

open Classical in
/-- **`E[3] ⊆ E(S)` makes `χ_3` the trivial homomorphism.**

`#948` fixes `σ` and concludes `χ_3 σ = 1`; this quantifies over `σ` on both sides and concludes an
equation between homomorphisms, which is the form "the whole of `E[3]` is `S`-rational" actually
delivers and the form `ker_galoisRepMod_three_le_ker_galoisModularCyclotomicChar` compares against.

⚠️ The hypothesis is stated as `∀ σ P, σ • P = P` rather than through a rationality predicate on
points because this development has no such predicate; `mem_ker_galoisRepMod_iff` shows it is
equivalent to `galoisRepMod 3` being the trivial representation. -/
theorem galoisModularCyclotomicChar_three_eq_one_of_forall_fixed (h2 : (2 : F) ≠ 0)
    (h3 : (3 : F) ≠ 0) (hfix : ∀ (σ : F ≃ₐ[S] F) (P : (W⁄F).torsion 3), σ • P = P) :
    galoisModularCyclotomicChar S F (natCard_rootsOfUnity_of_ne_zero (F := F) (n := 3) h3)
      = (1 : (F ≃ₐ[S] F) →* (ZMod 3)ˣ) :=
  MonoidHom.ext fun σ =>
    galoisModularCyclotomicChar_eq_one_of_forall_torsion_three_fixed (W := W) σ h2 h3 (hfix σ)

open Classical in
/-- **`ker ρ_{E,3} ≤ ker χ_3`**, Silverman III.8.1.1 as an inclusion of subgroups of `Gal(F/S)`.

`galoisRepMod 3` is the mod-`3` Galois representation on `E[3]`
(`EllipticCurves.TateModule.GaloisAction`) and `mem_ker_galoisRepMod_iff` unfolds membership in its
kernel to exactly `#948`'s hypothesis, so the inclusion is that theorem with no work in between.
This is the shape the Tate-module front can consume without knowing anything about the pairing.

⚠️ **This is not `det ρ_{E,3} = χ_3` and must not be read as progress on it.**  An inclusion of
kernels is strictly weaker than an identity of characters; the identity itself is
`exists_smul_eq_zsmul_add_zsmul_and_det_three_eq`
(`EllipticCurves.FunctionField.WeilPairingDeterminant`, `#951`), of which this inclusion is the
special case where `σ` has matrix `(1, 0, 0, 1)`.

⚠️ `galoisRepMod` is stated under a `[DecidableEq F]` section variable while this front runs under
`open Classical in`.  That is not a mismatch — both `torsion` and `galoisRepMod` pick up the same
classical instance here, so the two spellings of `E[3]` are the same term. -/
theorem ker_galoisRepMod_three_le_ker_galoisModularCyclotomicChar (h2 : (2 : F) ≠ 0)
    (h3 : (3 : F) ≠ 0) :
    (galoisRepMod (W' := W) (F := F) 3).ker
      ≤ (galoisModularCyclotomicChar S F
          (natCard_rootsOfUnity_of_ne_zero (F := F) (n := 3) h3)).ker :=
  fun σ hσ => MonoidHom.mem_ker.mpr
    (galoisModularCyclotomicChar_eq_one_of_forall_torsion_three_fixed (W := W) σ h2 h3
      ((mem_ker_galoisRepMod_iff 3 σ).mp hσ))

open Classical in
/-- **`μ_3 ⊆ S` — Silverman's own statement.**

If `Gal(F/S)` fixes `E[3]` pointwise then every cube root of unity of `F` lies in the image of `S`.
`#948` reaches "fixed by every `σ`"; the step from there to "lies in the base field" is
`InfiniteGalois.mem_range_algebraMap_iff_fixed` and is the only thing in this development that needs
`[IsGalois S F]`.

⚠️ `[IsGalois S F]` is a genuine restriction, not bookkeeping.  `F` is algebraically closed here, so
the instance holds when `F` is an algebraic closure of a perfect `S` and fails for, say, `S = ℚ`
inside `F = ℂ`.  Nothing else in this file or in `#948` asks for it, deliberately.

⚠️ Stated with `Set.range (algebraMap S F)` rather than `(⊥ : IntermediateField S F)` because that
is how Mathlib phrases the fixed-point characterisation; the two are `IntermediateField.mem_bot`
apart and shipping both would be noise. -/
theorem mem_range_algebraMap_of_torsion_three_fixed [IsGalois S F] (h2 : (2 : F) ≠ 0)
    (h3 : (3 : F) ≠ 0) (hfix : ∀ (σ : F ≃ₐ[S] F) (P : (W⁄F).torsion 3), σ • P = P)
    (ζ : rootsOfUnity 3 F) : ((ζ : Fˣ) : F) ∈ Set.range (algebraMap S F) :=
  (InfiniteGalois.mem_range_algebraMap_iff_fixed _).mpr fun σ =>
    forall_mem_rootsOfUnity_three_fixed_of_forall_torsion_fixed (W := W) σ h2 h3 (hfix σ)
      (ζ : Fˣ) ζ.2

/-! ### Non-vacuity

The curve-level statements carry `[IsAlgClosed F]`, so `ℚ` cannot witness them; the certificates
below are on `#948`'s curve `y² + y = x³` base-changed to `AlgebraicClosure ℚ`, with **`S = ℚ` and
not `S = F`** — over `S = F` the group `Gal(F/S)` is trivial and every certificate is empty.

⚠️ **Which certificate is load-bearing.**  It is the first one, `χ_3` of `ℚ` being non-trivial: it
is the only statement here that is *unconditional*, and it says that the hypothesis carried by
everything else on this front — and by `#948`'s whole file — can fail.  Drop the torsion hypothesis
from `forall_mem_rootsOfUnity_three_fixed_of_forall_torsion_fixed` and the conclusion becomes
**false**, not merely unproved.  ⚠️ That is a strictly stronger kind of certificate than `#940`'s
weightless instantiation and than a schema instance, and it is available here only because the
counting argument replaced the automorphism `#944` and `#948` had priced.

⚠️ **The `μ_3 ⊆ ℚ` certificate is also a check on the workaround**, not only on the theorem: it
could not be *written* before the two `private instance` lines at the top of this file, because
`IsGalois ℚ (AlgebraicClosure ℚ)` does not synthesize in this project.

⚠️ **There is deliberately no certificate in which the hypothesis is satisfied.**  On `y² + y = x³`
over `ℚ` the `X = −1` fibre of `Ψ₃ = 3X(X³ + 1)` is `y² + y + 1 = 0`, so `E[3]` is not `ℚ`-rational,
and no curve with rational `3`-torsion is to hand in this tree.  Saying why beats hunting for one.
⚠️ Indeed the first certificate below rules such a curve out over `ℚ` itself: a `σ` with
`χ_3 σ ≠ 1` moves a `3`-torsion point on *every* elliptic curve over `ℚ`
(`exists_torsion_three_smul_ne_self_of_galoisModularCyclotomicChar_ne_one`, `#948`). -/

section Nonvacuity

/-! The certificate curve `y² + y = x³` is the shared `EllipticCurves.Fixture.y2AddYEqX3`, and the
base — algebraically closed, and of characteristic `0` so that `2 ≠ 0` and `3 ≠ 0` — is
`EllipticCurves.Fixture.AlgClosedQ`, whose single `[CharZero F]` instance also supplies
`IsElliptic` here. -/

open EllipticCurves.Fixture

private lemma exampleTwo : (2 : AlgClosedQ) ≠ 0 := two_ne_zero

private lemma exampleThree : (3 : AlgClosedQ) ≠ 0 := three_ne_zero_of_charZero _

/-- **⚠️ THE LOAD-BEARING CERTIFICATE: the hypothesis carried by this whole front can fail.**

Some `σ ∈ Gal(Q̄/ℚ)` has `χ_3 σ ≠ 1`.  Stated in full rather than obtained-and-projected (`#916`),
with the count discharged by `natCard_rootsOfUnity_of_ne_zero` at `exampleThree` — which is exactly
the discharge the curve-level statements perform internally, so the character named here is the one
they name. -/
example : ∃ σ : AlgClosedQ ≃ₐ[ℚ] AlgClosedQ,
    galoisModularCyclotomicChar ℚ AlgClosedQ
      (natCard_rootsOfUnity_of_ne_zero (F := AlgClosedQ) (n := 3) exampleThree) σ ≠ 1 :=
  exists_galoisModularCyclotomicChar_three_ne_one _

/-- **And the underlying fact, also in full**: the Galois action on `μ_3(Q̄)` is not trivial. -/
example : ∃ (σ : AlgClosedQ ≃ₐ[ℚ] AlgClosedQ) (ζ : rootsOfUnity 3 AlgClosedQ),
    restrictRootsOfUnity (σ.toRingEquiv.toRingHom) 3 ζ ≠ ζ :=
  exists_restrictRootsOfUnity_three_ne_self

open Classical in
/-- **The bundled character form, on a curve that exists.**  A schema instance in the hypothesis. -/
example (hfix : ∀ (σ : AlgClosedQ ≃ₐ[ℚ] AlgClosedQ)
      (P : ((y2AddYEqX3 ℚ)⁄AlgClosedQ).torsion 3), σ • P = P) :
    galoisModularCyclotomicChar ℚ AlgClosedQ
        (natCard_rootsOfUnity_of_ne_zero (F := AlgClosedQ) (n := 3) exampleThree)
      = (1 : (AlgClosedQ ≃ₐ[ℚ] AlgClosedQ) →* (ZMod 3)ˣ) :=
  galoisModularCyclotomicChar_three_eq_one_of_forall_fixed (W := y2AddYEqX3 ℚ) exampleTwo
    exampleThree hfix

open Classical in
/-- **`ker ρ_{E,3} ≤ ker χ_3` on the same curve**, with both subgroups written out. -/
example :
    (galoisRepMod (W' := y2AddYEqX3 ℚ) (F := AlgClosedQ) 3).ker
      ≤ (galoisModularCyclotomicChar ℚ AlgClosedQ
          (natCard_rootsOfUnity_of_ne_zero (F := AlgClosedQ) (n := 3) exampleThree)).ker :=
  ker_galoisRepMod_three_le_ker_galoisModularCyclotomicChar exampleTwo exampleThree

open Classical in
/-- **`μ_3 ⊆ ℚ` on the same curve** — the certificate that could not be written at all before the
two `private instance` lines at the top of this file, and therefore the check that they work. -/
example (hfix : ∀ (σ : AlgClosedQ ≃ₐ[ℚ] AlgClosedQ)
      (P : ((y2AddYEqX3 ℚ)⁄AlgClosedQ).torsion 3), σ • P = P)
    (ζ : rootsOfUnity 3 AlgClosedQ) :
    ((ζ : AlgClosedQˣ) : AlgClosedQ) ∈ Set.range (algebraMap ℚ AlgClosedQ) :=
  mem_range_algebraMap_of_torsion_three_fixed (W := y2AddYEqX3 ℚ) exampleTwo exampleThree
    hfix ζ

end Nonvacuity

end WeierstrassCurve.Affine
