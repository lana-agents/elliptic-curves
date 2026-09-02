/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import EllipticCurves.Fixtures
import EllipticCurves.FunctionField.WeilPairingFunctionCyclotomic
import EllipticCurves.FunctionField.WeilPairingPerfect

/-!
# Rational `3`-torsion forces rational cube roots of unity

Every rung-6 theorem on this front so far says something about the **Weil pairing**.  This file
says something about the **base field**: if `Gal(F/S)` fixes every point of `E[3]`, then it fixes
every element of `μ_3(F)`.  Classically that is `E[m] ⊆ E(K) ⟹ μ_m ⊆ K`, the corollary Silverman
draws immediately after the proposition whose parts
`EllipticCurves.FunctionField.WeilPairingFunctionGalois` (`#936`),
`EllipticCurves.FunctionField.WeilPairingSurjective` (`#938`) and
`EllipticCurves.FunctionField.WeilPairingFunctionCyclotomic` (`#944`) have been assembling.

The argument is three steps and every input is already public:

```
σ fixes every point of E[3]
  ⟹ e_3(σ • P, σ • T) = e_3(P, T)      for all P, T
  ⟹ σ fixes the value e_3(P, T)        by #936's equivariance
  ⟹ σ fixes every element of μ_3(F)    by #938's surjectivity, for any single P ≠ 0
```

## What each step actually costs, since the two inputs are not interchangeable

⚠️ **Equivariance alone is not enough, and it is worth being precise about why.**
`weilPairingThree_galois` says `σ` carries the value at `(P, T)` to the value at `(σ • P, σ • T)`;
under the hypothesis those are the same pair, so `σ` fixes every *pairing value*.  That is a
statement about the image of `e_3`, and it is `weilPairingThree_surjective` (`#938`) that says the
image is all of `μ_3(F)`.  ⚠️ This is the first consumer of `#938` on this board that is not itself
a statement about the pairing.

⚠️ **`#E[3] = 9` is the second load-bearing input.**  Surjectivity is stated with a *nonzero* first
argument, so the proof must produce one; `nontrivial_torsion_three` below gets it from
`card_torsion_three` (`EllipticCurves.Torsion.ThreeTorsionStructure`).  The Non-vacuity section
compiles what happens without it.

## ⚠️ At `n = 2` there is nothing for the curve to prove

`μ_2 = {±1}` lies in the prime field, so **every** `S`-algebra automorphism fixes it — for any
extension `F / S` whatsoever, with no `[IsAlgClosed F]`, no `(2 : F) ≠ 0`, no curve and no torsion
hypothesis: `forall_mem_rootsOfUnity_two_fixed`.  So at `n = 2` Silverman's corollary is not the
easier mirror of `n = 3`; its conclusion is unconditional and the hypothesis buys nothing.

⚠️ This is the second place where the two `n` genuinely part company on this front, and it has the
same cause as the first.  `#944` recorded that `χ_2` is the trivial character because `(ZMod 2)ˣ` is
a subsingleton; this is that observation's arithmetic shadow — the obstruction is the value group,
and `μ_2` is too small to obstruct anything.  There is no `n = 3` analogue of the curve-free
statement, and the Non-vacuity section compiles its absence rather than asserting it.

## Main statements

* `forall_mem_rootsOfUnity_two_fixed` — every `σ` fixes `μ_2(F)` pointwise, for every extension
  `F / S`; a statement about a field extension and nothing else, in the root namespace.
* `WeierstrassCurve.Affine.nontrivial_torsion_three` — `E[3]` has a nonzero point over an
  algebraically closed field of characteristic `≠ 2, 3`.
* `WeierstrassCurve.Affine.forall_mem_rootsOfUnity_three_fixed_of_forall_torsion_fixed` —
  **the theorem**: `σ` fixing `E[3]` pointwise fixes `μ_3(F)` pointwise.
* `WeierstrassCurve.Affine.galoisModularCyclotomicChar_eq_one_of_forall_torsion_three_fixed` — the
  same conclusion as `χ_3 σ = 1`, via `galoisModularCyclotomicChar_eq_one_iff`.
* `WeierstrassCurve.Affine.exists_torsion_three_smul_ne_self_of_galoisModularCyclotomicChar_ne_one`
  — the contrapositive, which is the direction one applies: a `σ` that moves a cube root of unity
  must move a `3`-torsion point.

## Naming and placement

`forall_mem_rootsOfUnity_two_fixed` mentions no curve and sits at the root, above
`namespace WeierstrassCurve.Affine`, as `#938`, `#940` and `#944` placed their curve-free inputs;
putting a curve namespace on a curve-free statement is `#903`'s defect one level up.  The rest is in
`WeierstrassCurve.Affine` with `open CoordinateRing`, `#903`'s house pattern as enforced by `#918`
and `#927`, in two sections because the variable blocks differ: `nontrivial_torsion_three` is
about a curve over `F` itself, everything else about a curve over `S` base-changed to `F`.

## Explicitly out of scope

* **General `n`** — `#251`, as everywhere on this front (⚠️ **not** `#404`, see below).
  ⚠️ The ceiling here is
  `#938`'s and not `#940`'s, and the difference matters: surjectivity is blocked at composite `n`
  **twice**, by the crux and independently by the prime-order step in
  `MonoidHom.surjective_of_ne_one_of_natCard_prime`.  This theorem inherits both, so `#940`'s
  "blocked only once" does not transfer to it.
* **The field-theoretic restatement**, i.e. literally `μ_3 ⊆ K`.  Turning "fixed by every `σ`"
  into "lies in the base field" needs `[IsGalois S F]`, which nothing *here* asks for.  ⚠️ This
  bullet used to add "and this front carries no `IsGalois` instance anywhere", which was true but
  misleading about the cost: the instance is blocked by a **synthesis trap**, not missing.  It is
  delivered as `mem_range_algebraMap_of_torsion_three_fixed`
  (`EllipticCurves.FunctionField.WeilPairingRationalTorsionGalois`, `#947`), which repairs the trap
  in two `private instance` lines and is then one term off the theorem below.  The pointwise-fixed
  form stated here remains what `galoisModularCyclotomicChar_eq_one_iff` speaks and what a consumer
  without `[IsGalois S F]` can check.
* **Exhibiting a `σ` with `χ_3 σ ≠ 1`**, which is what makes the contrapositive bite over `ℚ`.
  ⚠️ This bullet used to say it needed an automorphism of `AlgebraicClosure ℚ` moving a primitive
  cube root of unity and was unspiked.  **Both halves were wrong**, and the correction is worth more
  than the statement: it is `exists_galoisModularCyclotomicChar_three_ne_one`
  (`EllipticCurves.FunctionField.WeilPairingRationalTorsionGalois`, `#947`), and **no automorphism
  is constructed** — if every `σ` fixed every cube root of unity each would lie in `ℚ`, and the only
  rational cube root of `1` is `1`, contradicting `Nat.card μ_3(Q̄) = 3`.  The first two refutations
  below remain the in-file checkable substitutes.
* **An `n = 2` form with a torsion hypothesis.**  There is no such theorem to write, because the
  conclusion holds without one.  Recording that is the deliverable; a hypothesis-carrying
  restatement would be strictly weaker than what is proved.

⚠️ **`#404` is closed, and the general-`n` entry above named it as the gate.**  PR #557 proved the
on-curve identity for `(Φₙ/ΨSqₙ, ωₙ/ψₙ³)` at every index over every commutative ring —
`WeierstrassCurve.Affine.equation_div_of_ψ_ne_zero`, `EllipticCurves.Torsion.OmegaCrux`.  What still
gates a general index is the *other* statement this tree also called `ωₙ`: the identification of
those coordinates with the **group-law** multiple `n • P`, which is `#251`.  ⚠️ The two-reading
account is `EllipticCurves.FunctionField.MulByNPullback`; the gate is relettered here, not lifted.

## References

* [J. H. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.8, Cor. 8.1.1.
-/

/-- **Every `S`-algebra automorphism of `F` fixes `μ_2(F)` pointwise.**

A square root of `1` in a field is `± 1`, and both lie in the image of the prime field, so a ring
homomorphism has no choice.  ⚠️ Note what is *absent* from the hypotheses: no `[IsAlgClosed F]`, no
`(2 : F) ≠ 0`, no curve, and — the point of the file — no assumption about torsion points.  At
`n = 3` the corresponding statement is false without one; see
`WeierstrassCurve.Affine.forall_mem_rootsOfUnity_three_fixed_of_forall_torsion_fixed` and the
Non-vacuity section, which compiles the failure of the unconditional form.

Over an algebraically closed `F` with `2 ≠ 0` this also follows from
`galoisModularCyclotomicChar_two_eq_one` (`#944`) through `galoisModularCyclotomicChar_eq_one_iff`,
and the Non-vacuity section compiles that route too; it is not the statement made here because it
would carry two hypotheses this one does not need.

A statement about a field extension and nothing else. -/
theorem forall_mem_rootsOfUnity_two_fixed {S F : Type*} [Field S] [Field F] [Algebra S F]
    (σ : F ≃ₐ[S] F) :
    ∀ t ∈ rootsOfUnity 2 F, σ ((t : Fˣ) : F) = ((t : Fˣ) : F) := by
  intro t ht
  rw [mem_rootsOfUnity, ← Units.val_eq_one, Units.val_pow_eq_pow_val, sq,
    mul_self_eq_one_iff] at ht
  rcases ht with h | h <;> rw [h] <;> simp

namespace WeierstrassCurve.Affine

open CoordinateRing

section Torsion

variable {F : Type*} [Field F] [IsAlgClosed F] {W : Affine F} [W.IsElliptic]

open Classical in
/-- **`E[3]` has a nonzero point** over an algebraically closed field of characteristic `≠ 2, 3`,
because it has nine.

⚠️ This is the file's only consumer of `card_torsion_three`, and it is not decoration: the
surjectivity of `e_3(P, ·)` is stated for a **nonzero** `P`, so the theorem below cannot even begin
without a witness.  The Non-vacuity section compiles what the proof does when this line is
removed. -/
theorem nontrivial_torsion_three (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) :
    Nontrivial (W.torsion 3) := by
  haveI := W.finite_torsion_three h3
  exact Finite.one_lt_card_iff_nontrivial.mp (by rw [card_torsion_three h2 h3]; omega)

end Torsion

section Galois

variable {S F : Type*} [Field S] [Field F] [Algebra S F] {W : Affine S} [W.IsElliptic]
  [IsAlgClosed F]

open Classical in
/-- **A `σ` fixing `E[3]` pointwise fixes `μ_3(F)` pointwise** — Silverman III.8.1.1 at `n = 3`,
the statement usually written `E[3] ⊆ E(K) ⟹ μ_3 ⊆ K`.

Pick any nonzero `P ∈ E[3]` (`nontrivial_torsion_three`).  Given `t ∈ μ_3(F)`, surjectivity of
`e_3(P, ·)` (`#938`) produces a `T` with `e_3(P, T) = t`, and then equivariance (`#936`) reads

```
σ · t = σ · e_3(P, T) = e_3(σ • P, σ • T) = e_3(P, T) = t,
```

the middle equality being the hypothesis applied at `P` and at `T`.

⚠️ **The hypothesis is consumed twice, once in each slot**, and that is not an artefact of the
proof: surjectivity sweeps the *second* argument with the first one held fixed, so both the held
point and the swept point have to be fixed by `σ`.  A proof that fixes only `P` does not close; the
Non-vacuity section quotes the goal it leaves. -/
theorem forall_mem_rootsOfUnity_three_fixed_of_forall_torsion_fixed (σ : F ≃ₐ[S] F)
    (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0)
    (hfix : ∀ P : (W⁄F).torsion 3, σ • P = P) :
    ∀ t ∈ rootsOfUnity 3 F, σ ((t : Fˣ) : F) = ((t : Fˣ) : F) := by
  haveI := nontrivial_torsion_three (W := W⁄F) h2 h3
  obtain ⟨P, hP⟩ := exists_ne (0 : (W⁄F).torsion 3)
  intro t ht
  obtain ⟨T, hT⟩ := weilPairingThree_surjective h2 h3 hP ⟨t, ht⟩
  have hval : restrictRootsOfUnity (σ.toRingEquiv.toRingHom) 3 (weilPairingThree h2 h3 P T)
      = weilPairingThree h2 h3 P T := by
    rw [weilPairingThree_galois σ h2 h3 P T, hfix P, hfix T]
  rw [hT] at hval
  have := congrArg (fun x : rootsOfUnity 3 F => ((x : Fˣ) : F)) hval
  simpa [restrictRootsOfUnity_coe_apply] using this

open Classical in
/-- **The same conclusion as a value of the cyclotomic character**: `χ_3 σ = 1` for every `σ`
fixing `E[3]` pointwise.

`galoisModularCyclotomicChar_eq_one_iff` is an iff, so this loses nothing relative to the pointwise
form and gains the shape `#944`'s exponent theorems consume:
`weilPairingThree_galois_eq_self_of_forall_fixed` asks exactly for the pointwise hypothesis, and
this supplies it from the curve instead of from the field. -/
theorem galoisModularCyclotomicChar_eq_one_of_forall_torsion_three_fixed (σ : F ≃ₐ[S] F)
    (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0)
    (hfix : ∀ P : (W⁄F).torsion 3, σ • P = P) :
    galoisModularCyclotomicChar S F (natCard_rootsOfUnity_of_ne_zero h3) σ = 1 :=
  (galoisModularCyclotomicChar_eq_one_iff _ σ).mpr
    (forall_mem_rootsOfUnity_three_fixed_of_forall_torsion_fixed σ h2 h3 hfix)

open Classical in
/-- **The contrapositive, which is the direction one applies**: a `σ` acting nontrivially on
`μ_3(F)` must move some `3`-torsion point.

Read as an obstruction, this is `μ_3 ⊄ K ⟹ E[3] ⊄ E(K)`: rational `3`-torsion is impossible over a
field that does not already contain the cube roots of unity.  ⚠️ Stated rather than left to `mt`
because the hypothesis a consumer can actually check is the character one, and recovering it from
the pointwise form costs the `iff` at every call site. -/
theorem exists_torsion_three_smul_ne_self_of_galoisModularCyclotomicChar_ne_one (σ : F ≃ₐ[S] F)
    (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0)
    (hσ : galoisModularCyclotomicChar S F (natCard_rootsOfUnity_of_ne_zero h3) σ ≠ 1) :
    ∃ P : (W⁄F).torsion 3, σ • P ≠ P := by
  by_contra h
  exact hσ (galoisModularCyclotomicChar_eq_one_of_forall_torsion_three_fixed σ h2 h3
    (by simpa using h))

/-! ### Non-vacuity

The `n = 3` statements carry `[IsAlgClosed F]`, so `ℚ` cannot witness them; the certificates below
are on `#936`'s curve `y² + y = x³` base-changed to `AlgebraicClosure ℚ`, with `S = ℚ`, so that
`Gal(F/S)` is a genuine group and not the trivial one.  The `n = 2` statement needs neither.

⚠️ **Which certificates are load-bearing, and the four compiled checks that say so.**  `#944`
shipped with the finding that a certificate can be green and consume nothing, and its reviewer added
that the deletion test has to remove *every* input rather than only the last one named.  Both were
applied to what follows; all four failures below are compiler output, quoted and not paraphrased.

* **The `n = 3` analogue of `forall_mem_rootsOfUnity_two_fixed` does not exist.**  Asking for a
  `forall_mem_rootsOfUnity_three_fixed` with no torsion hypothesis gives
  `` error(lean.unknownIdentifier): Unknown identifier `forall_mem_rootsOfUnity_three_fixed` ``.
  That is the compiled half of this file's asymmetry, and it is why the `n = 2` theorem is here.
* **One named fixed point is not the hypothesis.**  `#936` and `#944` both certify with
  `exampleSThree_fixed`, the `ℚ`-rationality of a single `3`-torsion point.  This theorem cannot be:
  supplying `fun _ => exampleSThree_fixed σ` where `hfix` is wanted gives
  `error: Type mismatch`, `exampleSThree_fixed σ` `has type` `σ • exampleSThree = exampleSThree`
  `but is expected to have type` `σ • x✝ = x✝`.  The hypothesis really is about all of `E[3]`, and
  the type checker is what says so.
* **The hypothesis is used twice, at both slots.**  Dropping `hfix T` from the rewrite chain leaves
  `error: unsolved goals` with
  `⊢ weilPairingThree h2 h3 P (σ • T) = weilPairingThree h2 h3 P T` — the second-slot obligation,
  which is exactly the point that surjectivity sweeps `T` while `P` is held.
* **`#E[3] = 9` is load-bearing.**  Deleting the `nontrivial_torsion_three` line gives
  `error(lean.synthInstanceFailed): failed to synthesize instance of type class`
  `Nontrivial ↥((W⁄F).torsion 3)`, followed by
  `` error: Tactic `rcases` failed: `x✝ : ?m.62` is not an inductive datatype ``. -/

section Nonvacuity

/-! The certificate curve `y² + y = x³` is the shared `EllipticCurves.Fixture.y2AddYEqX3`, and the
base — algebraically closed, and of characteristic `0` so that `2 ≠ 0` and `3 ≠ 0` — is
`EllipticCurves.Fixture.AlgClosedQ`, whose single `[CharZero F]` instance also supplies
`IsElliptic` here. -/

open EllipticCurves.Fixture

private lemma exampleTwo : (2 : AlgClosedQ) ≠ 0 := two_ne_zero

private lemma exampleThree : (3 : AlgClosedQ) ≠ 0 := three_ne_zero_of_charZero _

/-- `S = (0, 0)` lies on the base-changed curve `y² + y = x³` and is nonsingular. -/
private lemma exampleNonsingularThree : ((y2AddYEqX3 ℚ)⁄AlgClosedQ).Nonsingular 0 0 :=
  ((y2AddYEqX3 ℚ)⁄AlgClosedQ).equation_iff_nonsingular.mp (by
    simp [y2AddYEqX3, WeierstrassCurve.Affine.equation_iff])

open Classical in
/-- `S = (0, 0)` is `3`-torsion: `Ψ₃ = 3X⁴ + 3b₆X` vanishes at `0`. -/
private lemma exampleTorsionThree :
    Point.some (0 : AlgClosedQ) 0 exampleNonsingularThree
      ∈ ((y2AddYEqX3 ℚ)⁄AlgClosedQ).torsion 3 :=
  mem_torsion_three_some_iff'.mpr (by
    simp [y2AddYEqX3, WeierstrassCurve.Ψ₃, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
      WeierstrassCurve.b₆, WeierstrassCurve.b₈])

open Classical in
/-- `S = (0, 0)` as an element of `E[3]`. -/
private noncomputable def exampleSThree : ((y2AddYEqX3 ℚ)⁄AlgClosedQ).torsion 3 :=
  ⟨Point.some 0 0 exampleNonsingularThree, exampleTorsionThree⟩

open Classical in
/-- `(0, 0)` is `ℚ`-rational on `y² + y = x³`, so every `σ` fixes it.

⚠️ Kept even though no certificate below closes with it: it is the input the *refutation* uses, and
the refutation is the load-bearing half.  See the second bullet of the Non-vacuity note. -/
private lemma exampleSThree_fixed (σ : AlgClosedQ ≃ₐ[ℚ] AlgClosedQ) :
    σ • exampleSThree = exampleSThree :=
  Subtype.ext ((Point.galois_smul_some_eq_some_iff σ exampleNonsingularThree
    exampleNonsingularThree).mpr ⟨(map_zero σ).symm, (map_zero σ).symm⟩)

open Classical in
/-- **The number an independent input had to supply**: `#E[3] = 9` on a curve that exists.  It is
`false` at every other value and is what `nontrivial_torsion_three` consumes. -/
example : Nat.card (((y2AddYEqX3 ℚ)⁄AlgClosedQ).torsion 3) = 9 :=
  card_torsion_three exampleTwo exampleThree

open Classical in
/-- **`E[3]` on a curve that exists is nontrivial**, so the theorem below has a `P` to run on. -/
example : Nontrivial (((y2AddYEqX3 ℚ)⁄AlgClosedQ).torsion 3) :=
  nontrivial_torsion_three exampleTwo exampleThree

open Classical in
/-- **The theorem, on a curve that exists.**  A schema instance, universally quantified in `σ` and
in the hypothesis. -/
example (σ : AlgClosedQ ≃ₐ[ℚ] AlgClosedQ)
    (hfix : ∀ P : ((y2AddYEqX3 ℚ)⁄AlgClosedQ).torsion 3, σ • P = P) :
    ∀ t ∈ rootsOfUnity 3 AlgClosedQ, σ ((t : AlgClosedQˣ) : AlgClosedQ)
      = ((t : AlgClosedQˣ) : AlgClosedQ) :=
  forall_mem_rootsOfUnity_three_fixed_of_forall_torsion_fixed σ exampleTwo exampleThree hfix

open Classical in
/-- **The contrapositive on the same curve**: over `ℚ`, a `σ` moving a cube root of unity moves a
`3`-torsion point of `y² + y = x³`.

⚠️ Not overclaimed: this does **not** exhibit such a `σ`, and the file's Scope section says why that
is a statement about `AlgebraicClosure ℚ` rather than about this curve. -/
example (σ : AlgClosedQ ≃ₐ[ℚ] AlgClosedQ)
    (hσ : galoisModularCyclotomicChar ℚ AlgClosedQ
      (natCard_rootsOfUnity_of_ne_zero exampleThree) σ ≠ 1) :
    ∃ P : ((y2AddYEqX3 ℚ)⁄AlgClosedQ).torsion 3, σ • P ≠ P :=
  exists_torsion_three_smul_ne_self_of_galoisModularCyclotomicChar_ne_one σ exampleTwo
    exampleThree hσ

/-- **The `n = 2` statement on the same field, with no hypothesis and no curve.**  Compare the
`n = 3` certificate above, which needs a curve, a nonzero point and a hypothesis on all of
`E[3]`. -/
example (σ : AlgClosedQ ≃ₐ[ℚ] AlgClosedQ) :
    ∀ t ∈ rootsOfUnity 2 AlgClosedQ, σ ((t : AlgClosedQˣ) : AlgClosedQ)
      = ((t : AlgClosedQˣ) : AlgClosedQ) :=
  forall_mem_rootsOfUnity_two_fixed σ

/-- **The `#944` route to the same `n = 2` conclusion**, which compiles and therefore agrees.

⚠️ This is what justifies deriving the theorem the other way:
`galoisModularCyclotomicChar_two_eq_one` does reach the conclusion, but only after
`natCard_rootsOfUnity_of_ne_zero` has been fed
`exampleTwo` and `[IsAlgClosed F]` — two inputs `forall_mem_rootsOfUnity_two_fixed` does without.
Both terms are here so the comparison is checkable rather than asserted. -/
example (σ : AlgClosedQ ≃ₐ[ℚ] AlgClosedQ) :
    ∀ t ∈ rootsOfUnity 2 AlgClosedQ, σ ((t : AlgClosedQˣ) : AlgClosedQ)
      = ((t : AlgClosedQˣ) : AlgClosedQ) :=
  (galoisModularCyclotomicChar_eq_one_iff (natCard_rootsOfUnity_of_ne_zero exampleTwo) σ).mp
    (galoisModularCyclotomicChar_two_eq_one _ σ)

end Nonvacuity

end Galois

end WeierstrassCurve.Affine
