/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import EllipticCurves.TateModule.FreeThree
import EllipticCurves.Torsion.TorsionCountCharFree

/-!
# `T₃E ≅ ℤ₃²` in characteristic `2` — `#2340` deliverables 4 and 5 at `ℓ = 3`

For an elliptic curve `W` over an algebraically closed field `F` **of characteristic `2`**, the
`3`-adic Tate module `T₃E = lim_k E[3^k]` is a free `ℤ_[3]`-module of rank `2`:

```
Nonempty (W.tateModule 3 ≃ₗ[ℤ_[3]] ℤ_[3] × ℤ_[3])      Module.Free ℤ_[3] (W.tateModule 3)
Module.finrank ℤ_[3] (W.tateModule 3) = 2              Module.Finite ℤ_[3] (W.tateModule 3)
```

⚠️ **Every statement in this file binds `h2 : (2 : F) = 0`** — the *hypothesis* that the base field
has characteristic `2`, not its negation — and that is written into each declaration headline below
as well as into this paragraph, `README.md` (`## Docstring conventions` → `### Reach clauses`)
ruling that module prose does not repair a partial headline.

## Why this is new, and what it is not

⚠️ **Every landed statement of this tree whose conclusion is one of the four above and which
supplies its own count binds `(2 : F) ≠ 0`** — `EllipticCurves.TateModule.Free`'s
`free_tateModule_two` group at `ℓ = 2`, `EllipticCurves.TateModule.LevelStructure`'s
`infinite_tateModule_two` and `nontrivial_tateModule_two`,
`EllipticCurves.TateModule.FreeThree`'s `free_tateModule_three` group at `ℓ = 3`, and
`EllipticCurves.TateModule.FreeGeneral`'s `…_of_natCast_ne_zero` group at every prime
`ℓ ≠ char F` — and `2 = 0` **refutes** that hypothesis rather than failing to supply it.  ⚠️ They
are named rather than counted, `README.md` (`### Reach clauses`) ruling that a cardinal over a
population an edit can move is the weaker form.

⚠️⚠️ **But the universal that would be convenient here is FALSE, and the true claim is about
instantiation rather than about the page.** `EllipticCurves.TateModule.PrimaryFree`'s
`nonempty_tateModuleEquivProd_of_card`, `free_tateModule_of_card`, `finrank_tateModule_of_card` and
`finite_tateModule_of_card` **bind no hypothesis on `2` at all**, and neither do
`EllipticCurves.TateModule.LevelStructure`'s `infinite_tateModule_of_card` and
`nontrivial_tateModule_of_card`: ⚠️ **those SIX are the landed forms with a `T_ℓE` conclusion that
this file consumes**, the first four taking `#E[ℓ^k] = ℓ^k · ℓ^k` together with a coherent system
of generating pairs as *hypotheses*, the last two taking it together with `1 < ℓ` and surjectivity
of the level projections.  ⚠️ **Four further landed forms this file consumes bind nothing about `2`
either** — `nsmul_three_surjective`, `proj_three_surjective`,
`exists_closure_pair_eq_torsion_of_addEquiv` and `exists_compatible_basis_of_surjective` — **and
they are named here because the six above are scoped by their conclusion and are therefore not
everything this file uses.**  ⚠️ **So nothing below is a new argument about curves.** What was
unavailable at
`2 = 0` was those two inputs, and `EllipticCurves.Torsion.TorsionCountCharFree` is where the first
of them landed.  ⇒ ⚠️ **The honest statement is: before this file no `T_ℓE` conclusion of this tree
could be INSTANTIATED over a field of characteristic `2` at any `ℓ`, and the `Nonvacuity` section
below is what exhibits that it now can.**

⚠️ **It is `ℓ = 3` and not "odd `ℓ`", and the boundary is not an accident.**  The three inputs the
general route needs are, at `ℓ`:

1. surjectivity of `[ℓ]` on `E(F̄)`;
2. `#E[ℓ^k] = ℓ^k · ℓ^k` at every `k`;
3. a generating pair of `E[ℓ]`.

Input 1 is unconditional at `ℓ = 3` — `EllipticCurves.Torsion.TriplingSurjective`'s
`nsmul_three_surjective` binds nothing — and inputs 2 and 3 come from
`EllipticCurves.Torsion.TorsionCountCharFree`'s `card_torsion_three_pow_mul_self_of_two_eq_zero` and
`nonempty_torsion_three_addEquiv_of_two_eq_zero`.  ⚠️ **Those two rest on
`separable_Ψ₃_of_two_eq_zero`, and separability of `preΨ_ℓ` at `2 = 0` is proved in this tree at
`ℓ = 3` and nowhere else**: that file's own `section Obstruction` shows the coprimality route to it
*dies* at `2 = 0` (`not_isCoprime_preΨ_preΩ_of_two_eq_zero`).  **So `ℓ = 3` is the whole of what is
available, and a general-odd-`ℓ` twin of this file is blocked on that separability and not on
anything here.**

⚠️ **`ℓ = 2` in characteristic `2` is not a gap this file leaves open**: there `ℓ = char F`, where
the conclusion is **false** — `E[2]` is `0` or `ℤ/2ℤ`, so `T₂E` has rank `0` or `1`.  At
characteristic `2` the odd primes are the whole of the question.

## This file contains no argument about curves

Every ingredient is landed, and the only work here is the composition.  The two torsion-level
lemmas (`exists_closure_pair_eq_torsion_three_of_two_eq_zero` and
`exists_compatible_basis_three_of_two_eq_zero`) are the characteristic-`2` twins of
`EllipticCurves.Torsion.ThreePrimaryBasis`'s `exists_closure_pair_eq_torsion_three` and
`exists_compatible_basis_three`.  ⚠️ **They sit here rather than beside their twins because the
structure theorem that states them lives in `EllipticCurves.Torsion.TorsionCountCharFree`, which
`ThreePrimaryBasis` does not import**; putting them there would mean editing a landed file's import
block for no mathematical gain.

⚠️ **Coherence is the load-bearing input and the levelwise structure theorem does not supply it.**
`nonempty_torsion_three_pow_addEquiv_of_two_eq_zero` gives `E[3^k] ≃+ (ℤ/3^kℤ)²` at each level
*independently*, and a family of unrelated isomorphisms says nothing about an inverse limit.  What
`exists_compatible_basis_of_surjective` builds from `[3]`-surjectivity and **one** generating pair
of `E[3]` is the coherent system `3 • P (k+1) = P k`; that recursion, not the tower, is why `E[3]`
alone suffices — which is also why this file needs the `k = 1` structure theorem and not the tower.
-/

open scoped AddSubgroup

namespace WeierstrassCurve.Affine

variable {F : Type*} [Field F] [DecidableEq F] {W : Affine F}

section CharTwo

variable [IsAlgClosed F] [W.IsElliptic]

/-! ### The base of the tower, and the coherent system, at `2 = 0` -/

/-- **`E[3]` has a generating pair in characteristic `2`**, over an algebraically closed field with
`2 = 0`: it is isomorphic to `ZMod 3 × ZMod 3`, in which the two standard vectors generate.

This is the characteristic-`2` twin of `EllipticCurves.Torsion.ThreePrimaryBasis`'s
`exists_closure_pair_eq_torsion_three`, and it is the **only** place in this file where a structure
theorem for `E[3]` is used — `exists_closure_pair_eq_torsion_of_addEquiv` asks nothing about `2`,
so the whole of `h2` is spent on `nonempty_torsion_three_addEquiv_of_two_eq_zero`. -/
theorem exists_closure_pair_eq_torsion_three_of_two_eq_zero (h2 : (2 : F) = 0) :
    ∃ P Q : W.Point, P ∈ W.torsion 3 ∧ Q ∈ W.torsion 3 ∧
      AddSubgroup.closure ({P, Q} : Set W.Point) = W.torsion 3 :=
  (nonempty_torsion_three_addEquiv_of_two_eq_zero (W := W) h2).elim
    exists_closure_pair_eq_torsion_of_addEquiv

/-- **Compatible bases for the `3`-primary tower in characteristic `2`**, over an algebraically
closed field with `2 = 0`: a system of generating pairs of the groups `E[3^k]`, coherent for the
transition maps `x ↦ 3 • x` of the tower:

```
∀ k, AddSubgroup.closure {P k, Q k} = W.torsion (3 ^ k)
∀ k, 3 • P (k + 1) = P k        ∀ k, 3 • Q (k + 1) = Q k
```

⚠️ **This, and not the levelwise tower, is what an inverse limit needs**, and the recursion that
builds it asks only for surjectivity of `[3]` — `nsmul_three_surjective`, which binds nothing at
all — so `h2` is spent **entirely** on the base case.  The family is *chosen*, so the statement is
existential; every consumer only ever needs one such system. -/
theorem exists_compatible_basis_three_of_two_eq_zero (h2 : (2 : F) = 0) :
    ∃ P Q : ℕ → W.Point,
      (∀ k, AddSubgroup.closure ({P k, Q k} : Set W.Point) = W.torsion (3 ^ k)) ∧
      (∀ k, 3 • P (k + 1) = P k) ∧ (∀ k, 3 • Q (k + 1) = Q k) :=
  exists_compatible_basis_of_surjective nsmul_three_surjective
    (exists_closure_pair_eq_torsion_three_of_two_eq_zero h2)

namespace tateModule

/-! ### `T₃E ≅ ℤ₃²` at `2 = 0` -/

/-- **The Tate module at `ℓ = 3` is `ℤ_[3]`-linearly isomorphic to `ℤ_[3] × ℤ_[3]` in
characteristic `2`**, over an algebraically closed field with `2 = 0`.

The isomorphism depends on a choice of coherent system of generating pairs, so it is stated as a
`Nonempty`; the choice-free consequences are `free_tateModule_three_of_two_eq_zero` and
`finrank_tateModule_three_of_two_eq_zero`. -/
theorem nonempty_tateModuleEquivProd_three_of_two_eq_zero (h2 : (2 : F) = 0) :
    Nonempty (W.tateModule 3 ≃ₗ[ℤ_[3]] ℤ_[3] × ℤ_[3]) :=
  nonempty_tateModuleEquivProd_of_card (card_torsion_three_pow_mul_self_of_two_eq_zero h2)
    (exists_compatible_basis_three_of_two_eq_zero h2)

/-- **`T₃E` is a free `ℤ_[3]`-module in characteristic `2`**, over an algebraically closed field
with `2 = 0` — Silverman, *AEC*, III.7.1 at `ℓ = 3`, in the one characteristic its `ℓ ≠ char F`
hypothesis permits and no landed statement of this tree reaches. -/
theorem free_tateModule_three_of_two_eq_zero (h2 : (2 : F) = 0) :
    Module.Free ℤ_[3] (W.tateModule 3) :=
  free_tateModule_of_card (card_torsion_three_pow_mul_self_of_two_eq_zero h2)
    (exists_compatible_basis_three_of_two_eq_zero h2)

/-- **`T₃E` has rank two over `ℤ_[3]` in characteristic `2`**, over an algebraically closed field
with `2 = 0`.

Together with `free_tateModule_three_of_two_eq_zero` this is `T₃E ≅ ℤ₃²`. -/
theorem finrank_tateModule_three_of_two_eq_zero (h2 : (2 : F) = 0) :
    Module.finrank ℤ_[3] (W.tateModule 3) = 2 :=
  finrank_tateModule_of_card (card_torsion_three_pow_mul_self_of_two_eq_zero h2)
    (exists_compatible_basis_three_of_two_eq_zero h2)

/-- **`T₃E` is a finitely generated `ℤ_[3]`-module in characteristic `2`**, over an algebraically
closed field with `2 = 0`.  Free of rank two, so in particular finite as a module; this is the
shape `ρ_{E,3} : G_F → GL₂(ℤ_3)` needs. -/
theorem finite_tateModule_three_of_two_eq_zero (h2 : (2 : F) = 0) :
    Module.Finite ℤ_[3] (W.tateModule 3) :=
  finite_tateModule_of_card (card_torsion_three_pow_mul_self_of_two_eq_zero h2)
    (exists_compatible_basis_three_of_two_eq_zero h2)

/-- **`T₃E` is infinite in characteristic `2`**, over an algebraically closed field with `2 = 0`:
it surjects onto `E[3^k]`, which has `9^k` elements, for every `k`.

⚠️ An **independent** witness of non-triviality — it never mentions the equivalence — which is the
role `infinite_tateModule_three` plays at `(2 : F) ≠ 0`.  ⚠️ **No hypothesis on `2` reaches the
projections**: `proj_three_surjective` binds nothing, so `h2` enters here only through the count. -/
theorem infinite_tateModule_three_of_two_eq_zero (h2 : (2 : F) = 0) :
    Infinite (W.tateModule 3) :=
  infinite_tateModule_of_card (by norm_num) proj_three_surjective
    (card_torsion_three_pow_mul_self_of_two_eq_zero h2)

/-- **`T₃E` is nontrivial in characteristic `2`**, i.e. it is not the zero module.  Weaker than
`infinite_tateModule_three_of_two_eq_zero`, but this is the form a consumer usually wants. -/
theorem nontrivial_tateModule_three_of_two_eq_zero (h2 : (2 : F) = 0) :
    Nontrivial (W.tateModule 3) :=
  nontrivial_tateModule_of_card (by norm_num) proj_three_surjective
    (card_torsion_three_pow_mul_self_of_two_eq_zero h2)

/-- **`T₃E` has a nonzero element in characteristic `2`.**  The unbundled form of
`nontrivial_tateModule_three_of_two_eq_zero`. -/
theorem exists_ne_zero_tateModule_three_of_two_eq_zero (h2 : (2 : F) = 0) :
    ∃ f : W.tateModule 3, f ≠ 0 :=
  haveI := nontrivial_tateModule_three_of_two_eq_zero (W := W) h2
  exists_ne 0

end tateModule

end CharTwo

/-! ## Non-vacuity: the statements above, committed on a characteristic-`2` curve

⚠️ **Exhibited and not asserted** — `#2340`'s deliverable 5.  The certificate is a specific
elliptic curve over a specific field of characteristic `2`, and ⚠️ **the landed statements that
would otherwise give these conclusions cannot be instantiated here**: `free_tateModule_three`,
`free_tateModule_of_natCast_ne_zero` and `EllipticCurves.TateModule.Free`'s `free_tateModule_two`
each bind `(2 : F) ≠ 0`, which `two_eq_zero_closureCharTwo` **refutes**.  ⚠️ **`PrimaryFree`'s
`…_of_card` forms and `LevelStructure`'s `infinite_tateModule_of_card` and
`nontrivial_tateModule_of_card` bind nothing about `2` and are not excluded by that** — those six
are the landed forms **with a `T_ℓE` conclusion** that the theorems above feed — the same scope
the paragraph at the head of this file puts on those six — and the feeding is the whole of what
those theorems do rather than of this file, which also holds four private declarations and five
`example`s: all nine theorems accounted for, the four equivalence-route statements feed
`PrimaryFree`'s four, `infinite_tateModule_three_of_two_eq_zero` and
`nontrivial_tateModule_three_of_two_eq_zero` feed `LevelStructure`'s two independently of the
equivalence, and the remaining three are the two inputs that feeding needs together with the
unbundled form of `nontrivial_…`.  ⚠️ **Two further landed forms are fed and sit outside the six
because neither concludes about `T_ℓE`** — `EllipticCurves.Torsion.PrimaryBasis`'
`exists_closure_pair_eq_torsion_of_addEquiv` and `exists_compatible_basis_of_surjective`, each at
the head of one input's own proof term. -/

section Nonvacuity

open EllipticCurves.Fixture

/-- The base field really is of characteristic `2`, which is what makes the `example`s below
statements that the `(2 : F) ≠ 0` forms cannot express rather than merely fail to reach. -/
private lemma two_eq_zero_closureCharTwo : (2 : AlgebraicClosure (ZMod 2)) = 0 := by
  have : CharP (AlgebraicClosure (ZMod 2)) 2 :=
    charP_of_injective_algebraMap
      (algebraMap (ZMod 2) (AlgebraicClosure (ZMod 2))).injective 2
  exact_mod_cast CharP.cast_eq_zero (AlgebraicClosure (ZMod 2)) 2

/-- `y² + xy = x³ + 1` over `AlgebraicClosure (ZMod 2)` — `EllipticCurves.Fixture`'s
`y2AddXYEqX3AddC` at `c = 1`, the shared `a₁ ≠ 0` ordinary family, and the same curve
`EllipticCurves.Torsion.TorsionCountCharFree` commits `E[3] ≃+ (ℤ/3ℤ)²` on.

⚠️ It is a `def` and not an `abbrev`, so the instance below is found for this name and is **not**
found for `y2AddXYEqX3AddC (AlgebraicClosure (ZMod 2)) 1`, which `EllipticCurves.Fixtures` says in
terms carries no `IsElliptic` instance anywhere in the tree.  ⚠️ `noncomputable` because
`AlgebraicClosure.instField` is.  ⚠️ **Three declarations here are re-declarations, each
`private` where it was first written and so not importable by name: this one, the characteristic
lemma `two_eq_zero_closureCharTwo`, and the `IsElliptic` instance below.**  ⛔ **A bare-name
collision sweep reaches the first TWO and cannot reach the third**, which is an anonymous
`private instance` here and in both files it is re-declared from
(`EllipticCurves.Torsion.TorsionCountCharFree` and `EllipticCurves.Torsion.NsmulSmoothSurjective`),
so there is no bare name for such a sweep to flag ⇒ **the expected reading for this file is two
private collisions and not three.**  For those two the resolution is the `_private.<Module>.0.`
prefix plus the whole-tree build.  ⛔ **`Δ_curveClosureCharTwo` is NOT re-declared here**: it is
`NsmulSmoothSurjective`'s alone, and this file needs no discriminant lemma of its own because
`isElliptic_y2AddXYEqX3AddC` takes `2 = 0` and `c ≠ 0` directly. -/
private noncomputable def curveClosureCharTwo : Affine (AlgebraicClosure (ZMod 2)) :=
  y2AddXYEqX3AddC (AlgebraicClosure (ZMod 2)) 1

/-- ⚠️ **`AlgebraicClosure (ZMod 2)` carries no `DecidableEq` instance**, and Mathlib's
`WeierstrassCurve.Affine.Point` addition sits under `[DecidableEq F]`, so no statement mentioning
`n • P` or `W.torsion n` over this field elaborates without one.

⚠️ **This instance is a no-op at this head and is kept deliberately, which is measured rather than
asserted**: `EllipticCurves.Torsion.TorsionCountCharFree` and
`EllipticCurves.Torsion.NsmulSmoothSurjective` each declare the same instance `private`, and a
`private` *instance* still participates in synthesis across a module boundary even though its
*name* cannot be imported — so the `example`s below elaborate with this line deleted.  **It is here
so that this file does not rest on another module's private instance**, which is the form both of
those files took and which nothing outside them guarantees. -/
private noncomputable instance : DecidableEq (AlgebraicClosure (ZMod 2)) := Classical.decEq _

/-- The witness is a genuine elliptic curve: `Δ = c` wherever `2 = 0`
(`Δ_y2AddXYEqX3AddC_of_two_eq_zero`), so `c ≠ 0` is the whole condition and `one_ne_zero`
discharges it. -/
private instance : curveClosureCharTwo.IsElliptic :=
  isElliptic_y2AddXYEqX3AddC two_eq_zero_closureCharTwo one_ne_zero

/-- **`T₃E` is a free `ℤ_[3]`-module of rank `2` on `y² + xy = x³ + 1` over
`AlgebraicClosure (ZMod 2)`, committed** — `T₃E ≅ ℤ₃²` over a field of characteristic `2`, which is
`#2340`'s residue of `#245` at `ℓ = 3`. -/
example : Module.Free ℤ_[3] (curveClosureCharTwo.tateModule 3) ∧
    Module.finrank ℤ_[3] (curveClosureCharTwo.tateModule 3) = 2 :=
  ⟨tateModule.free_tateModule_three_of_two_eq_zero two_eq_zero_closureCharTwo,
    tateModule.finrank_tateModule_three_of_two_eq_zero two_eq_zero_closureCharTwo⟩

/-- **The equivalence itself, committed on that curve.** -/
example : Nonempty (curveClosureCharTwo.tateModule 3 ≃ₗ[ℤ_[3]] ℤ_[3] × ℤ_[3]) :=
  tateModule.nonempty_tateModuleEquivProd_three_of_two_eq_zero two_eq_zero_closureCharTwo

/-- **`T₃E` is a finitely generated `ℤ_[3]`-module on that curve, committed** — the shape
`ρ_{E,3} : G_F → GL₂(ℤ_3)` needs. -/
example : Module.Finite ℤ_[3] (curveClosureCharTwo.tateModule 3) :=
  tateModule.finite_tateModule_three_of_two_eq_zero two_eq_zero_closureCharTwo

/-- **`T₃E` is infinite on that curve, committed** — the independent non-triviality witness, which
never mentions the equivalence. -/
example : Infinite (curveClosureCharTwo.tateModule 3) :=
  tateModule.infinite_tateModule_three_of_two_eq_zero two_eq_zero_closureCharTwo

/-- **`T₃E` has a nonzero element on that curve, committed.** -/
example : ∃ f : curveClosureCharTwo.tateModule 3, f ≠ 0 :=
  tateModule.exists_ne_zero_tateModule_three_of_two_eq_zero two_eq_zero_closureCharTwo

end Nonvacuity

end WeierstrassCurve.Affine
