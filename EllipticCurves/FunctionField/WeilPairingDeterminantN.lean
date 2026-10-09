/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import EllipticCurves.Fixtures
import EllipticCurves.FunctionField.WeilPairingDeterminant
import EllipticCurves.FunctionField.WeilPairingFunctionGaloisN
import EllipticCurves.FunctionField.WeilPairingSurjective
import EllipticCurves.Torsion.StructureGeneral

/-!
# `det ρ_{E,n} = χ_n` at a general index, in coordinates

`EllipticCurves.FunctionField.WeilPairingDeterminant` (`#951`) proves, at `n = 2` and `n = 3`,

```
σ • P = a • P + c • T ,   σ • T = b • P + d • T   ⟹   a * d − b * c ≡ χ_n(σ)   (mod n),
```

and, with nothing left assumed about `σ`, `exists_smul_eq_zsmul_add_zsmul_and_det_{two,three}_eq`.
This file is that identification at **every** `n` with `(2 : F) ≠ 0` and `((n : ℤ) : F) ≠ 0` over an
algebraically closed `F`.  ⚠️ It is the **coordinate** half: the bundled reading
`galoisDetMod n = χ_n` and the matrix reading `det ∘ ρ_{E,n} = χ_n` are the next rung and are not
here (`## Scope`).

⚠️ **This identity is not a numbered result in Silverman *AEC*, and in particular it is not
III.8.1(e)**, which is the compatibility relation `e_{mm'}(S, T) = e_{m'}([m]S, T)`.  It is the
standard consequence of III.8.1(a) (bilinear), (b) (alternating) and (d) (Galois invariant), by the
computation Silverman runs inside the proof of III.8.6 with `α = ρ_{E,n}(σ)` in place of an
endomorphism of the Tate module.  The five letters are tabulated verbatim in
`EllipticCurves.FunctionField.WeilPairing`.

## ⚠️ The one place this is NOT a transcription of `#951`, and it is the hypothesis

`#951` hangs everything on `hPT : e_n(P, T) ≠ 1` and converts it to an order by
`orderOf_rootsOfUnity_eq_of_prime` — *"a `p`-th root of unity other than `1` has order exactly
`p`"*.  **That lemma is stated for a prime `p` and there is nothing to put in its place at a
composite index**: in `μ_4(F)` the element `−1` is `≠ 1` and has order `2`, so an equality
`ζ ^ (a * d − b * c) = ζ ^ χ_4(σ)` at such a `ζ` yields a congruence mod `2` and not mod `4`.
⚠️ **That witness is compiled and not asserted** — the first `example` of `### Non-vacuity` below
exhibits it in `μ_4(AlgebraicClosure ℚ)` — so `hPT` is **not** a sufficient hypothesis for any of
the three conclusions this file reaches.

The hypothesis used instead is `horder : orderOf (weilPairingN h2 hn P T) = n` — that the pair is
**primitive**, not merely non-degenerate.  At a prime index the two coincide, which is why `#951`
never had to see the difference, and `### Recovery of the numeral layer, compiled` below closes
that gap in the only direction it goes: both of `#951`'s determinant identities come back out of
the general one with `hPT` converted to `horder` by the prime lemma, at `n = 3` **and** at `n = 2`.

⚠️ **And the extra hypothesis costs nothing at the consumer, because a primitive pair always
exists** in this setting: `exists_orderOf_weilPairingN_eq` produces one from the structure theorem,
non-degeneracy and the cyclicity of `μ_n(F)`, with no hypothesis beyond the two the pairing already
carries.  That is the genuinely new content of this file; everything else is `#951` with the index
freed.

## The three halves, and which inputs do what

**The algebra.**  `weilPairingN_zsmul_add_zsmul` expands `e_n` on a pair of integer combinations of
`P` and `T`.  Four terms come out of bilinearity; the two diagonal ones die by `weilPairingN_self`
(alternation) and the off-diagonal pair collapses to a single power by `weilPairingN_swap`
(antisymmetry), leaving the exponent `a * d − b * c`.  ⚠️ **That is the whole reason a determinant
appears at all**: it is the statement that an alternating bilinear form on a rank-`2` module is a
multiple of the determinant, run in coordinates.  Alternation and antisymmetry are both consumed
here and neither is decorative.

**The arithmetic.**  `weilPairingN_galois_eq_pow` (`#2280`,
`EllipticCurves.FunctionField.WeilPairingFunctionGaloisN`) says `σ` raises `e_n(P, T)` to the power
`χ_n(σ)`.  Comparing the two expressions for `e_n(σ • P, σ • T)` gives
`ζ ^ (a * d − b * c) = ζ ^ χ_n(σ)` for `ζ = e_n(P, T)`, and `horder` turns that into a congruence
mod `n`.

**The existence.**  `exists_orderOf_weilPairingN_eq` is the one argument with no `#951` antecedent.
Take `P` of additive order exactly `n` — the structure theorem `nonempty_torsion_addEquiv`
(`EllipticCurves.Torsion.StructureGeneral`, `#242`) pulls `(1, 0)` back — and let `H ≤ μ_n(F)` be
the image of `e_n(P, ·)`, of order `d`.  Every element of `H` is killed by `d`, so
`e_n(d • P, T) = 1` for every `T`, so `d • P = 0` by non-degeneracy, so `n ∣ d`; and `d ∣ n` because
`H` is a subgroup of a group of order `n`.  Hence `H = ⊤`, and a generator of the cyclic group
`μ_n(F)` is a value.  ⚠️ **Non-degeneracy is what makes this work and the alternating law plays no
part in it** — `weilPairingN_self` is named nowhere in that proof, while antisymmetry enters only
through `weilPairingN_zsmul_left`, exactly as it does at the numerals.

## ⚠️ `n = 2` and `n = 1` are subsumed, not excluded

At `n = 2` the conclusion is `a * d − b * c ≡ 1 (mod 2)`, since `(ZMod 2)ˣ` is a subsingleton; that
is a genuine constraint on four integers and `WeilPairingDeterminant`'s own `## Scope` argues at
length why it is not the empty mirror that `#948` found at that index.  At `n = 1` every group in
sight is trivial and the conclusion is an equation in `ZMod 1`, which holds of anything.  ⚠️ **A
general-`n` statement subsumes a degenerate index rather than omitting it**, so nothing is excluded
below and `1 < n` is bound nowhere; the corollaries that *have* content are the ones at `n ≥ 3`,
where `(ZMod n)ˣ` is nontrivial, and the non-vacuity block is keyed to `n = 5` for that reason.

## ⚠️ `[NeZero n]` binds on exactly 2 of the 8, and this paragraph is a record of a widening

The span is the **eight** declarations at the variable index `n`, `weilPairingN_zsmul_right` through
`exists_smul_eq_zsmul_add_zsmul_and_det_n_eq`; ⚠️ the `n = 3` bridge and the two numeral recoveries
are outside it, being stated at literal indices.  **All eight bound `[NeZero n]` when this file was
written, and two do now** — measured from source, and a source census is sound here because
`grep -n variable` shows no `variable [NeZero n]` anywhere in the file.  ⚠️ **That is not a decision
taken here.**  `weilPairingN` and `weilPairingNHom` bound the instance in their own signatures, and
six of the eight were forced through those signatures and through nothing else; `#2286` widened both
roots one file up, and the binders then had nothing to carry.  **No statement below changed — only
what writing it costs**, `hn : ((n : ℤ) : F) ≠ 0` yielding `NeZero n` in one line, so the reach
recorded on every bullet of `## Main results` is the same reach it always was.

⚠️ **The two survivors are `galoisModularCyclotomicChar_n_eq_det` and
`exists_smul_eq_zsmul_add_zsmul_and_det_n_eq`, and `weilPairingN` is not what forces them.**  Their
conclusions name `galoisModularCyclotomicChar` (`EllipticCurves.Galois.CyclotomicCharacter`), which
binds `[NeZero n]` in its own signature, so the instance is needed to **write** the right-hand
side — ⚠️ **and a `haveI` in the tactic block cannot reach it, the statement being elaborated
first.**  Measured discriminatingly rather than argued: dropping either binder fails to synthesize
the instance **at the statement**, at the `galoisModularCyclotomicChar` application in the
conclusion and not in the proof.  ⚠️ The numeral recoveries name the same character and bind
nothing, because at the literal indices `3` and `2` synthesis finds `NeZero 3` and `NeZero 2` with
no binder to supply them — the same phenomenon `WeilPairingFunctionN` records of
`weilPairingN_eq_weilPairingTwo`.

⚠️ **Of the six that lost the binder, four needed nothing and two needed one line, and the split is
the statement/proof one that `WeilPairingFunctionGaloisN` is the sharpest case of.**  The four are
`weilPairingN_zsmul_{right,left}`, `weilPairingN_zsmul_add_zsmul` and
`intCast_eq_zero_of_zsmul_add_zsmul_eq_zero_n`, on which the instance was unused outright — ⚠️ **and
that is a hard gate and not a tidying: `unusedArguments` fires on an unused instance binder, so
leaving them would fail `lake lint`.**  The two are `exists_orderOf_weilPairingN_eq` and
`exists_zsmul_add_zsmul_eq_n`, each of which took one
`haveI : NeZero n := ⟨fun h => hn (by simp [h])⟩` as its first tactic: their statements never needed
the instance and their proofs always did, and only the first of those two facts was ever about
`weilPairingN`.  ⚠️ **A binder the proof uses is invisible to `unusedArguments`**, which is why the
count here is not read off the linter.

## Main results

* `weilPairingN_zsmul_{left,right}` — `e_n` is `ℤ`-homogeneous in each slot, at every `n` with
  `(2 : F) ≠ 0` and `((n : ℤ) : F) ≠ 0` over an algebraically closed `F`.
* `weilPairingN_zsmul_add_zsmul` — the determinant formula
  `e_n(aP + cT, bP + dT) = e_n(P, T) ^ (ad − bc)`, at the same reach.
* `exists_orderOf_weilPairingN_eq` — a **primitive** pair exists, at the same reach.
* `intCast_eq_zero_of_zsmul_add_zsmul_eq_zero_n` — a primitive pair is `ℤ/n`-independent.
* `exists_zsmul_add_zsmul_eq_n` — and it spans `E[n]`.
* `galoisModularCyclotomicChar_n_eq_det` — the determinant identity.
* `exists_smul_eq_zsmul_add_zsmul_and_det_n_eq` — the same with the matrix produced, so nothing is
  left assumed about `σ`.
* `weilPairingN_eq_weilPairingThree`, `weilPairingEltN_eq_weilPairingEltThree` — the `n = 3` bridge
  to the merged numeral layer, which `WeilPairingFunctionN` states is *"not here"* on placement
  grounds; see `### Recovery of the numeral layer, compiled` for why placement does not bind here.

## Scope

⚠️ **The bundled and matrix forms are not here.**  `galoisDetMod n = χ_n` as an identity of monoid
homomorphisms, and `det ∘ ρ_{E,n} = χ_n`, are the next rung; at `n = 3` they are
`EllipticCurves.FunctionField.WeilPairingDeterminantCharacter` (`#958`) and
`EllipticCurves.FunctionField.MatrixRepDeterminantCharacter` (`#1243`).  `#951`'s own docstring is
explicit that the coordinate statement *is* the content and the bundling is structural; the same
division applies here, and `exists_orderOf_weilPairingN_eq` is what will let that rung discharge
`horder` rather than assume it.

⚠️ **`[IsAlgClosed F]` is not droppable and this is not a placement choice**: `weilPairingN` does
not exist without it, `hprin` at a general index being available only over `F̄`
(`exists_gS_n_of_isAlgClosed`, `EllipticCurves.FunctionField.PullbackPrincipalityN`).  `#962` is the
gate that would change that and it is discharged at `n = 2` and `n = 3` only.

⚠️ **Nothing here touches `EllipticCurves.TateModule.Determinant`'s `2`-adic `galoisDetTwo`**, which
is `LinearEquiv.det` on `T₂E` and needs the pairing on `E[2 ^ k]` at every `k` **over the base
field**; no statement below is in that setting.  ⚠️ `n = char F` is outside every statement below by
`((n : ℤ) : F) ≠ 0`, and the **trace** of `ρ_{E,n}` has no pairing-theoretic description at all.

⚠️ `EllipticCurves.TateModule.DeterminantModGeneral`'s `## What is NOT here` says of this
identification that *"this file widens the indices at which the left-hand side is well defined and
says nothing about the identification, which needs the Weil pairing"*.  That is a claim about **that
file**, which stays true of it, so it takes a pointer in place and is not retired.

## References

* [J. H. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.7,
  III.8.1(a), (b), (d), and III.8.6.
-/

namespace WeierstrassCurve.Affine

open CoordinateRing

/-! ### The determinant formula at a general index -/

section Bilinear

variable {F : Type*} [Field F] [IsAlgClosed F] {W : Affine F} [W.IsElliptic]

open Classical in
/-- **`e_n` is `ℤ`-homogeneous in the translation slot**, at every `n` with `(2 : F) ≠ 0` and
`((n : ℤ) : F) ≠ 0` over an algebraically closed `F`.

⚠️ Proved from `map_zpow` on the *bundled* `weilPairingNHom` rather than by induction on `k`;
`ofAdd_zsmul` is the bridge between the `ℤ`-action on `E[n]` and the `zpow` on its multiplicative
copy.  ⚠️ `rootsOfUnity n F` is a commutative group, so `zpow` is available with no hypothesis
beyond the two the pairing already carries — in particular this needs no `1 < n`. -/
theorem weilPairingN_zsmul_right (h2 : (2 : F) ≠ 0) {n : ℕ} (hn : ((n : ℤ) : F) ≠ 0)
    (S T : W.torsion n) (k : ℤ) :
    weilPairingN h2 hn S (k • T) = weilPairingN h2 hn S T ^ k := by
  simpa [ofAdd_zsmul] using
    map_zpow (weilPairingNHom h2 hn (Multiplicative.ofAdd S)) (Multiplicative.ofAdd T) k

open Classical in
/-- **`e_n` is `ℤ`-homogeneous in the divisor slot**, by antisymmetry from the translation slot, at
every `n` with `(2 : F) ≠ 0` and `((n : ℤ) : F) ≠ 0` over an algebraically closed `F`. -/
theorem weilPairingN_zsmul_left (h2 : (2 : F) ≠ 0) {n : ℕ} (hn : ((n : ℤ) : F) ≠ 0)
    (S T : W.torsion n) (k : ℤ) :
    weilPairingN h2 hn (k • S) T = weilPairingN h2 hn S T ^ k := by
  rw [weilPairingN_swap h2 hn, weilPairingN_zsmul_right, weilPairingN_swap h2 hn, inv_zpow, inv_inv]

open Classical in
/-- **The determinant formula at a general index**:
`e_n(aP + cT, bP + dT) = e_n(P, T) ^ (ad − bc)`, at every `n` with `(2 : F) ≠ 0` and
`((n : ℤ) : F) ≠ 0` over an algebraically closed `F`.

Bilinearity produces four terms; `weilPairingN_self` kills the two diagonal ones and
`weilPairingN_swap` inverts one of the others, which is where the difference `ad − bc` comes from.
⚠️ This transcribes `weilPairingThree_zsmul_add_zsmul` (`#951`) line for line — the index is free in
that argument and always was; what was not free is the hypothesis the identity is consumed under. -/
theorem weilPairingN_zsmul_add_zsmul (h2 : (2 : F) ≠ 0) {n : ℕ}
    (hn : ((n : ℤ) : F) ≠ 0) (P T : W.torsion n) (a b c d : ℤ) :
    weilPairingN h2 hn (a • P + c • T) (b • P + d • T)
      = weilPairingN h2 hn P T ^ (a * d - b * c) := by
  rw [weilPairingN_add_left, weilPairingN_add_right, weilPairingN_add_right,
    weilPairingN_zsmul_left, weilPairingN_zsmul_left, weilPairingN_zsmul_left,
    weilPairingN_zsmul_left, weilPairingN_zsmul_right, weilPairingN_zsmul_right,
    weilPairingN_zsmul_right, weilPairingN_zsmul_right, weilPairingN_self,
    weilPairingN_self, weilPairingN_swap h2 hn P T]
  rw [one_zpow, one_zpow, one_zpow, one_zpow, one_mul, mul_one, ← zpow_mul, ← zpow_mul,
    inv_zpow, ← zpow_neg, ← zpow_add]
  ring_nf

/-! ### A primitive pair exists

⚠️ **The only argument in this file with no `#951` antecedent**, and the reason the stronger
hypothesis costs a consumer nothing. -/

open Classical in
/-- **A primitive pairing pair exists**, at every `n` with `(2 : F) ≠ 0` and `((n : ℤ) : F) ≠ 0`
over an algebraically closed `F`: there are `P T ∈ E[n]` with `orderOf (e_n(P, T)) = n`.

Three inputs, and the docstring says what each does rather than listing them:

* the **structure theorem** `nonempty_torsion_addEquiv` (`EllipticCurves.Torsion.StructureGeneral`,
  `#242`) supplies a point of additive order exactly `n`, by pulling `(1, 0)` back along
  `E[n] ≃+ ZMod n × ZMod n`.  ⚠️ Exactly `n` is what is needed and *nonzero* is not enough — see
  refutation R4 below, whose residual goal is the divisibility this equality discharges;
* **non-degeneracy** `eq_zero_of_forall_weilPairingN_eq_one` (`WeilPairingFunctionN`) turns
  *"every value of `e_n(P, ·)` is killed by `d`"* into `d • P = 0`, hence `n ∣ d` where
  `d = #(range of e_n(P, ·))`.  Together with `d ∣ n`, which is Lagrange in `μ_n(F)`, that forces
  the range to be everything;
* **cyclicity** of `μ_n(F)` (`rootsOfUnity.isCyclic`, with `Nat.card μ_n(F) = n` from `#938`) then
  produces an element of order `n` inside the range, and its preimage is the `T`.

⚠️ **The alternating law takes no part**: `weilPairingN_self` is named nowhere below, and
antisymmetry enters only through `weilPairingN_zsmul_left`.  ⚠️ At `n = 1` the statement is
`orderOf (1 : μ_1(F)) = 1` and is true for the trivial reason, so no `1 < n` is bound. -/
theorem exists_orderOf_weilPairingN_eq (h2 : (2 : F) ≠ 0) {n : ℕ}
    (hn : ((n : ℤ) : F) ≠ 0) :
    ∃ P T : W.torsion n, orderOf (weilPairingN h2 hn P T) = n := by
  haveI : NeZero n := ⟨fun h => hn (by simp [h])⟩
  have hnF : (n : F) ≠ 0 := by exact_mod_cast hn
  have hcard : Nat.card (rootsOfUnity n F) = n := natCard_rootsOfUnity_of_ne_zero hnF
  haveI : Finite (rootsOfUnity n F) :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; exact NeZero.ne n)
  obtain ⟨e⟩ := nonempty_torsion_addEquiv (W := W) h2 hnF
  obtain ⟨P, hordP⟩ : ∃ P : W.torsion n, addOrderOf P = n := by
    refine ⟨e.symm (1, 0), ?_⟩
    have h1 : addOrderOf ((1, 0) : ZMod n × ZMod n) = n := by
      rw [Prod.addOrderOf, ZMod.addOrderOf_one, addOrderOf_zero, Nat.lcm_one_right]
    calc addOrderOf (e.symm (1, 0))
        = addOrderOf ((1, 0) : ZMod n × ZMod n) :=
          addOrderOf_injective e.symm.toAddMonoidHom e.symm.injective _
      _ = n := h1
  obtain ⟨H, hH⟩ : ∃ H : Subgroup (rootsOfUnity n F),
      H = (weilPairingNHom h2 hn (Multiplicative.ofAdd P)).range := ⟨_, rfl⟩
  have hmem : ∀ T : W.torsion n, weilPairingN h2 hn P T ∈ H := fun T =>
    hH ▸ ⟨Multiplicative.ofAdd T, rfl⟩
  have hkill : ∀ x ∈ H, x ^ Nat.card H = 1 := fun x hx =>
    Subtype.ext_iff.mp (pow_card_eq_one' (x := (⟨x, hx⟩ : H)))
  have hzero : ((Nat.card H : ℕ) : ℤ) • P = 0 := by
    refine eq_zero_of_forall_weilPairingN_eq_one h2 hn fun T => ?_
    rw [weilPairingN_zsmul_left, zpow_natCast]
    exact hkill _ (hmem T)
  have hndvd : n ∣ Nat.card H := by
    have h := addOrderOf_dvd_of_nsmul_eq_zero
      ((natCast_zsmul P (Nat.card H)).symm.trans hzero)
    rwa [hordP] at h
  have hdvdn : Nat.card H ∣ n := by
    have h := Subgroup.card_subgroup_dvd_card H
    rwa [hcard] at h
  have htop : H = ⊤ :=
    Subgroup.eq_top_of_card_eq H (by rw [hcard]; exact Nat.dvd_antisymm hdvdn hndvd)
  obtain ⟨ζ, hζ⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := rootsOfUnity n F)
  have hζH : ζ ∈ (weilPairingNHom h2 hn (Multiplicative.ofAdd P)).range := by
    rw [← hH, htop]; exact Subgroup.mem_top ζ
  obtain ⟨T, hT⟩ := hζH
  exact ⟨P, T.toAdd, by
    rw [show weilPairingN h2 hn P T.toAdd
      = weilPairingNHom h2 hn (Multiplicative.ofAdd P) T from rfl, hT, hζ, hcard]⟩

/-! ### Independence and spanning -/

open Classical in
/-- **A primitive pair is `ℤ/n`-independent**, at every `n` with `(2 : F) ≠ 0` and
`((n : ℤ) : F) ≠ 0` over an algebraically closed `F`.

⚠️ The hypothesis is consumed **twice, at both slots**: pairing the relation against `P` bounds `v`
and pairing it against `T` bounds `u`.  Neither half gives the other (refutation R2 below).

⚠️ The conclusion is a pair of congruences mod `n` and cannot be strengthened to `u = 0 ∧ v = 0`
over `ℤ`: `u = n` satisfies the hypothesis.  That is exactly why the determinant statements below
live in `ZMod n`.

⚠️ `horder` is where this parts company with `#951`'s
`intCast_eq_zero_of_zsmul_add_zsmul_eq_zero_three`, whose `hPT : e_3(P, T) ≠ 1` buys the same
divisibility only because `3` is prime. -/
theorem intCast_eq_zero_of_zsmul_add_zsmul_eq_zero_n (h2 : (2 : F) ≠ 0) {n : ℕ}
    (hn : ((n : ℤ) : F) ≠ 0) {P T : W.torsion n}
    (horder : orderOf (weilPairingN h2 hn P T) = n) {u v : ℤ} (huv : u • P + v • T = 0) :
    ((u : ZMod n) = 0 ∧ (v : ZMod n) = 0) := by
  have hv : weilPairingN h2 hn P T ^ v = 1 := by
    have hpair := congrArg (weilPairingN h2 hn P) huv
    rwa [weilPairingN_add_right, weilPairingN_zsmul_right, weilPairingN_zsmul_right,
      weilPairingN_self, one_zpow, one_mul, weilPairingN_zero_right] at hpair
  have hu : weilPairingN h2 hn P T ^ (-u) = 1 := by
    have hpair := congrArg (weilPairingN h2 hn T) huv
    rwa [weilPairingN_add_right, weilPairingN_zsmul_right, weilPairingN_zsmul_right,
      weilPairingN_self, one_zpow, mul_one, weilPairingN_swap h2 hn, inv_zpow, ← zpow_neg,
      weilPairingN_zero_right] at hpair
  have hdvdv : (n : ℤ) ∣ v := by
    have hd := orderOf_dvd_iff_zpow_eq_one.mpr hv
    rwa [horder] at hd
  have hdvdu : (n : ℤ) ∣ u := by
    have hd := orderOf_dvd_iff_zpow_eq_one.mpr hu
    rw [horder] at hd
    exact (dvd_neg).mp hd
  exact ⟨(ZMod.intCast_zmod_eq_zero_iff_dvd _ n).mpr hdvdu,
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ n).mpr hdvdv⟩

open Classical in
/-- **A primitive pair spans `E[n]`**, at every `n` with `(2 : F) ≠ 0` and `((n : ℤ) : F) ≠ 0` over
an algebraically closed `F`.

⚠️ A **counting** argument and not a linear-algebra one: the pairing gives injectivity of
`(ℤ/n)² → E[n]` and `card_torsion_eq_sq` (`#E[n] = n²`,
`EllipticCurves.Torsion.StructureGeneral`) upgrades it to bijectivity.  Refutation R3 below deletes
the count and the residual goal is literally `n * n = #E[n]`. -/
theorem exists_zsmul_add_zsmul_eq_n (h2 : (2 : F) ≠ 0) {n : ℕ}
    (hn : ((n : ℤ) : F) ≠ 0) {P T : W.torsion n}
    (horder : orderOf (weilPairingN h2 hn P T) = n) (Q : W.torsion n) :
    ∃ a b : ℤ, Q = a • P + b • T := by
  haveI : NeZero n := ⟨fun h => hn (by simp [h])⟩
  have hnF : (n : F) ≠ 0 := by exact_mod_cast hn
  haveI := finite_torsion_of_intCast_ne_zero (W := W) h2 hnF
  set f : ZMod n × ZMod n → W.torsion n :=
    fun p => (p.1.val : ℤ) • P + (p.2.val : ℤ) • T with hf
  have hinj : Function.Injective f := by
    rintro ⟨u₁, v₁⟩ ⟨u₂, v₂⟩ hEq
    simp only [hf] at hEq
    have h0 : ((u₁.val : ℤ) - (u₂.val : ℤ)) • P + ((v₁.val : ℤ) - (v₂.val : ℤ)) • T = 0 := by
      rw [sub_zsmul, sub_zsmul, ← sub_eq_zero.mpr hEq]
      abel
    obtain ⟨hu, hv⟩ := intCast_eq_zero_of_zsmul_add_zsmul_eq_zero_n h2 hn horder h0
    push_cast at hu hv
    rw [sub_eq_zero] at hu hv
    simp only [ZMod.natCast_val, ZMod.cast_id] at hu hv
    exact Prod.ext hu hv
  have hbij : Function.Bijective f :=
    (Nat.bijective_iff_injective_and_card f).mpr ⟨hinj, by
      rw [card_torsion_eq_sq h2 hnF, Nat.card_prod, Nat.card_zmod, sq]⟩
  obtain ⟨p, hp⟩ := hbij.2 Q
  exact ⟨(p.1.val : ℤ), (p.2.val : ℤ), hp.symm⟩

end Bilinear

/-! ### `det ρ_{E,n} = χ_n` -/

section Galois

variable {S F : Type*} [Field S] [Field F] [Algebra S F] {W : Affine S} [W.IsElliptic]
  [IsAlgClosed F]

open Classical in
/-- **The determinant identity at a general index**, in coordinates — Silverman *AEC* III.8.1(a),
(b) and (d), ⚠️ **not** III.8.1(e): if `σ` acts on a primitive pair `(P, T)` of `E[n]` by the matrix
`(a, b; c, d)` then

```
a * d − b * c ≡ χ_n(σ)   (mod n),
```

at every `n` with `(2 : F) ≠ 0` and `((n : ℤ) : F) ≠ 0` over an algebraically closed `F`.

⚠️ **`horder` is load-bearing and its absence makes the statement false, not merely unproved**: at
`P = T = 0` every quadruple satisfies both matrix hypotheses, so no value of `a * d − b * c` is
determined.  Refutation R1 below deletes it and the leftover goal is the whole conclusion with both
matrix hypotheses still in hand.

⚠️ **`horder` and not `hPT : e_n(P, T) ≠ 1`**, which is `#951`'s hypothesis and is strictly weaker
off a prime index — the `μ_4` witness in `### Non-vacuity` is the reason, and
`### Recovery of the numeral layer, compiled` is where the two are reconciled at `n = 2` and
`n = 3`.

⚠️ The character is named through `natCard_rootsOfUnity_of_intCast_ne_zero`
(`WeilPairingFunctionGaloisN`), which is the cast bridge `weilPairingN_galois_eq_pow` already uses,
so the caller supplies nothing. -/
theorem galoisModularCyclotomicChar_n_eq_det (σ : F ≃ₐ[S] F) (h2 : (2 : F) ≠ 0) {n : ℕ} [NeZero n]
    (hn : ((n : ℤ) : F) ≠ 0) {P T : (W⁄F).torsion n}
    (horder : orderOf (weilPairingN h2 hn P T) = n) {a b c d : ℤ}
    (hP : σ • P = a • P + c • T) (hT : σ • T = b • P + d • T) :
    ((a * d - b * c : ℤ) : ZMod n)
      = (galoisModularCyclotomicChar S F (natCard_rootsOfUnity_of_intCast_ne_zero hn) σ :
          ZMod n) := by
  set ζ := weilPairingN h2 hn P T with hζ
  have key : ζ ^ (a * d - b * c)
      = ζ ^ ((galoisModularCyclotomicChar S F (natCard_rootsOfUnity_of_intCast_ne_zero hn) σ :
          ZMod n)).val := by
    rw [← weilPairingN_zsmul_add_zsmul h2 hn P T a b c d, ← hP, ← hT,
      weilPairingN_galois_eq_pow σ h2 hn P T]
  rw [← zpow_natCast] at key
  have hmod := (zpow_eq_zpow_iff_modEq (x := ζ)).mp key
  rw [horder] at hmod
  have hcast := (ZMod.intCast_eq_intCast_iff _ _ n).mpr hmod
  push_cast at hcast
  simpa using hcast

open Classical in
/-- **`det ρ_{E,n} = χ_n`, with nothing left assumed about `σ`**, at every `n` with `(2 : F) ≠ 0`
and `((n : ℤ) : F) ≠ 0` over an algebraically closed `F`.

Every `σ` has a matrix in a primitive pair — that is `exists_zsmul_add_zsmul_eq_n`, which is where
`#E[n] = n²` enters — and the determinant of that matrix is `χ_n(σ)`.  The four integers are only
determined mod `n`, but so is the conclusion
(`intCast_eq_zero_of_zsmul_add_zsmul_eq_zero_n`), so the statement does not depend on the choice.

⚠️ Read as `det ρ_{E,n} = χ_n` this is the whole content of the identification.  What it is not is
an equation between `LinearEquiv.det ∘ ρ_{E,n}` and `χ_n`; that bundling is a separate, structural
matter, which at `n = 3` is `galoisDetMod_three_eq_galoisModularCyclotomicChar`
(`EllipticCurves.FunctionField.WeilPairingDeterminantCharacter`, `#958`) and at a general index is
the next rung.  ⚠️ **The pair is still a hypothesis here and it need not be**:
`exists_orderOf_weilPairingN_eq` discharges it unconditionally, which is what lets a bundled
statement quantify over nothing but the curve and the field. -/
theorem exists_smul_eq_zsmul_add_zsmul_and_det_n_eq (σ : F ≃ₐ[S] F) (h2 : (2 : F) ≠ 0) {n : ℕ}
    [NeZero n] (hn : ((n : ℤ) : F) ≠ 0) {P T : (W⁄F).torsion n}
    (horder : orderOf (weilPairingN h2 hn P T) = n) :
    ∃ a b c d : ℤ, σ • P = a • P + c • T ∧ σ • T = b • P + d • T ∧
      ((a * d - b * c : ℤ) : ZMod n)
        = (galoisModularCyclotomicChar S F (natCard_rootsOfUnity_of_intCast_ne_zero hn) σ :
            ZMod n) := by
  obtain ⟨a, c, hac⟩ := exists_zsmul_add_zsmul_eq_n h2 hn horder (σ • P)
  obtain ⟨b, d, hbd⟩ := exists_zsmul_add_zsmul_eq_n h2 hn horder (σ • T)
  exact ⟨a, b, c, d, hac, hbd, galoisModularCyclotomicChar_n_eq_det σ h2 hn horder hac hbd⟩

end Galois

/-! ### Recovery of the numeral layer, compiled

Both of `#951`'s determinant identities come back out of `galoisModularCyclotomicChar_n_eq_det`
with their statements **verbatim** — at `n = 3` and at `n = 2` — with `hPT : e_n(P, T) ≠ 1`
converted to `horder` by `orderOf_rootsOfUnity_eq_of_prime`.  ⚠️ That conversion is the *only*
direction the prime lemma travels, and it is why the general statement is a widening of `#951`
rather than an incomparable one.

⚠️ **The `n = 3` bridge is written here, and `WeilPairingFunctionN`'s reason for not writing it
does not bind this file.**  That module says of the mirror that it *"would put
`WeilPairingFunctionThree` into this module's import closure for a second instance of an
identification the `n = 2` pair already compiles"* and calls the omission *"a placement decision
and not a claim that the mirror is harder"*.  Both halves are right about **that** file and neither
transfers here, because the premise is false of this one: **`WeilPairingFunctionThree` and
`MulByNPullback` — the latter carrying `mulByNEndo_three` — are both in the import closure of
`WeilPairingFunctionGaloisN` alone**, which this file imports for the equivariance equation, so
neither arrives on the mirror's account and neither arrives through the
`WeilPairingDeterminant` import taken below for `orderOf_rootsOfUnity_eq_of_prime`.  ⚠️ **Those are
membership claims and carry no sha, which `README.md`'s `## Import-closure figures` rules is the
right form for them; the module-count delta is in this commit's message, keyed to a head there and
not restated here.**

⚠️ **The bridge is consumed through proof irrelevance and no transport is written**, exactly as
`weilPairingEltN_eq_weilPairingEltTwo` records at `n = 2`: `mulByNEndo_three` is stated at
`transcendental_xCoord_three_nsmul h2 h3` while `IsWeilRootN` carries
`transcendental_xCoord_nsmul_genericPoint_of_intCast_ne_zero h2 hn`, and the two `mulByNEndo 3 _`
terms are definitionally equal because `Transcendental` is a `Prop`. -/

section Recovery

variable {F : Type*} [Field F] [IsAlgClosed F] {W : Affine F} [W.IsElliptic]

open Classical in
/-- **At `n = 3` this file's pairing is the merged `weilPairingEltThree`**, value for value, on the
nose and not up to anything.  The chosen rung-5 roots need not agree; the values do. -/
theorem weilPairingEltN_eq_weilPairingEltThree (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0)
    (hn : (((3 : ℕ) : ℤ) : F) ≠ 0) (S T : W.torsion 3) :
    weilPairingEltN h2 hn S T = weilPairingEltThree h2 h3 S T := by
  obtain ⟨hg0, f, hf, hd, u, hu⟩ := isWeilRootThree_weilPairingRootThree h2 h3 S
  refine weilPairingEltN_eq h2 hn (g := weilPairingRootThree h2 h3 S) ?_ T
  refine ⟨hg0, f, hf, by exact_mod_cast hd, u, ?_⟩
  rw [← mulByNEndo_three h2 h3] at hu
  exact hu

open Classical in
/-- The `μ_3(F)` twin of `weilPairingEltN_eq_weilPairingEltThree`, and the `n = 3` mirror of
`weilPairingN_eq_weilPairingTwo` (`WeilPairingFunctionN`). -/
theorem weilPairingN_eq_weilPairingThree (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0)
    (hn : (((3 : ℕ) : ℤ) : F) ≠ 0) (S T : W.torsion 3) :
    weilPairingN h2 hn S T = weilPairingThree h2 h3 S T := by
  refine Subtype.ext (Units.ext ((algebraMap F W.FunctionField).injective ?_))
  rw [algebraMap_coe_weilPairingN, algebraMap_coe_weilPairingThree,
    weilPairingEltN_eq_weilPairingEltThree h2 h3 hn]

end Recovery

section RecoveryGalois

variable {S F : Type*} [Field S] [Field F] [Algebra S F] {W : Affine S} [W.IsElliptic]
  [IsAlgClosed F]

open Classical in
/-- `galoisModularCyclotomicChar_three_eq_det` (`#951`), restated **verbatim** and proved from the
general layer.  ⚠️ `orderOf_rootsOfUnity_eq_of_prime Nat.prime_three` is the whole distance between
the two hypotheses, and it is a step that exists at `n = 3` and at no composite index. -/
example (σ : F ≃ₐ[S] F) (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) {P T : (W⁄F).torsion 3}
    (hPT : weilPairingThree h2 h3 P T ≠ 1) {a b c d : ℤ} (hP : σ • P = a • P + c • T)
    (hT : σ • T = b • P + d • T) :
    ((a * d - b * c : ℤ) : ZMod 3)
      = (galoisModularCyclotomicChar S F (natCard_rootsOfUnity_of_ne_zero h3) σ : ZMod 3) := by
  have hn : (((3 : ℕ) : ℤ) : F) ≠ 0 := by exact_mod_cast h3
  have horder : orderOf (weilPairingN h2 hn P T) = 3 := by
    rw [weilPairingN_eq_weilPairingThree h2 h3 hn]
    exact orderOf_rootsOfUnity_eq_of_prime Nat.prime_three hPT
  exact galoisModularCyclotomicChar_n_eq_det σ h2 hn horder hP hT

open Classical in
/-- `galoisModularCyclotomicChar_two_eq_det` (`#951`), restated **verbatim** and proved from the
general layer, through the `n = 2` bridge `weilPairingN_eq_weilPairingTwo` that
`WeilPairingFunctionN` already carries.  ⚠️ At this index the right-hand side is the fixed value
`1`, so what the recovery certifies is the congruence and not a varying character. -/
example (σ : F ≃ₐ[S] F) (h2 : (2 : F) ≠ 0) {P T : (W⁄F).torsion 2}
    (hPT : weilPairingTwo h2 P T ≠ 1) {a b c d : ℤ} (hP : σ • P = a • P + c • T)
    (hT : σ • T = b • P + d • T) :
    ((a * d - b * c : ℤ) : ZMod 2)
      = (galoisModularCyclotomicChar S F (natCard_rootsOfUnity_of_ne_zero h2) σ : ZMod 2) := by
  have hn : (((2 : ℕ) : ℤ) : F) ≠ 0 := by exact_mod_cast h2
  have horder : orderOf (weilPairingN h2 hn P T) = 2 := by
    rw [weilPairingN_eq_weilPairingTwo h2 hn]
    exact orderOf_rootsOfUnity_eq_of_prime Nat.prime_two hPT
  exact galoisModularCyclotomicChar_n_eq_det σ h2 hn horder hP hT

end RecoveryGalois

/-! ### Non-vacuity

Every statement above carries `[IsAlgClosed F]`, so `ℚ` cannot witness it; the certificates below
are on `#936`'s curve `y² + y = x³` base-changed to `AlgebraicClosure ℚ`, with **`S = ℚ` and not
`S = F`**, so that `Gal(F/S)` is a genuine group and not the trivial one.

⚠️ **The index is `5`**, which is neither `3`-smooth nor an index at which
`WeilPairingDeterminant` says anything, and at which `(ZMod n)ˣ` is nontrivial so the right-hand
side genuinely varies with `σ`.  The certificates restate each conclusion **in full** rather than
projecting out of an `obtain` (`#916`), and each one produces the pair `(P, T)` existentially rather
than assuming one: the whole point of `exists_orderOf_weilPairingN_eq` is that no such assumption is
needed.

⚠️ **The first `example` is not a non-vacuity certificate and is the one control this file cannot
do without**: it exhibits, in `μ_4(AlgebraicClosure ℚ)`, an element `≠ 1` whose order is `2` and not
`4`.  That is the whole reason `horder` replaces `#951`'s `hPT`, and every sentence above about the
prime lemma is keyed to it.  ⚠️ It is a statement about a **field** and mentions no curve; it sits
here rather than at the root because the fixture base is here.

⚠️ **Four refutations, all measured against this file as committed** (`#948`'s rule) and pasted
rather than paraphrased (`#940`, `#944`).

**R1 — `horder` is load-bearing in the determinant identity.**  Delete it from the binder:

```
error: Unknown identifier `horder`
error: unsolved goals
…
P T : ↥((W⁄F).torsion n)
a b c d : ℤ
hP : σ • P = a • P + c • T
hT : σ • T = b • P + d • T
ζ : ↥(rootsOfUnity n F) := weilPairingN h2 hn P T
hζ : ζ = weilPairingN h2 hn P T
key : ζ ^ (a * d - b * c) = ζ ^ ↑(↑((galoisModularCyclotomicChar S F ⋯) σ)).val
hmod : a * d - b * c ≡ ↑(↑((galoisModularCyclotomicChar S F ⋯) σ)).val [ZMOD ↑(orderOf ζ)]
⊢ ↑(a * d - b * c) = ↑((galoisModularCyclotomicChar S F ⋯) σ)
```

⚠️ Without `horder` the theorem is **false**, not merely unproved: at `P = T = 0` every quadruple
`(a, b, c, d)` satisfies both matrix hypotheses, so no value of `a * d − b * c` is determined.
⚠️ **And `hmod` is the discriminating line**: the congruence survives, at modulus `orderOf ζ`, which
is exactly the quantity `horder` identifies with `n`.  The refutation is not that the argument
collapses; it is that the modulus is unpinned.

**R2 — the independence lemma consumes both slots.**  Pair the relation against `P` only, deleting
the `hu` block and the `hdvdu` it feeds:

```
error: unsolved goals
…
horder : orderOf (weilPairingN h2 hn P T) = n
u v : ℤ
huv : u • P + v • T = 0
hv : weilPairingN h2 hn P T ^ v = 1
hdvdv : ↑n ∣ v
⊢ ↑u = 0
```

⚠️ The first slot bounds `v` and says nothing about `u`; the `u` half needs the *second* slot.  Same
shape as `#951`'s own second refutation and for the same reason — a statement about a **pair** has
to be paired against both members.

**R3 — `#E[n] = n²` is load-bearing in the spanning lemma.**  Drop `card_torsion_eq_sq` and try to
reach bijectivity from injectivity alone:

```
error: unsolved goals
…
f : ZMod n × ZMod n → ↥(W.torsion n) := fun p ↦ ↑p.1.val • P + ↑p.2.val • T
hf : f = fun p ↦ ↑p.1.val • P + ↑p.2.val • T
hinj : Function.Injective f
⊢ n * n = Nat.card ↥(W.torsion n)
```

⚠️ The residual goal is literally the torsion count.  The pairing supplies injectivity of
`(ℤ/n)² → E[n]` and nothing else, which is why the spanning lemma is a counting argument.

**R4 — a point of order exactly `n` is load-bearing, and *nonzero* is not enough.**  Replace the
structure-theorem block of `exists_orderOf_weilPairingN_eq` by `obtain ⟨P⟩ : Nonempty (W.torsion n)`
and drop the `rwa [hordP]`:

```
error: unsolved goals
…
hkill : ∀ x ∈ H, x ^ Nat.card ↥H = 1
hzero : ↑(Nat.card ↥H) • P = 0
h : addOrderOf P ∣ Nat.card ↥H
⊢ n ∣ Nat.card ↥H
```

⚠️ **This is the refutation that prices the structure theorem** and it is the only input of that
lemma a weaker substitute would not supply: the whole argument runs to `addOrderOf P ∣ d`, and the
step from there to `n ∣ d` *is* `addOrderOf P = n`.  A nonzero `P` gives `addOrderOf P ∣ n` in the
wrong direction, and at a composite `n` a nonzero point of order `< n` exists, so the gap is real
and not a proof artefact. -/

section Nonvacuity

open EllipticCurves.Fixture

private lemma exampleTwo : (2 : AlgClosedQ) ≠ 0 := two_ne_zero

/-- The index condition `((n : ℤ) : F) ≠ 0` at `n = 5` over a field of characteristic `0`. -/
private lemma exampleIndexFive : (((5 : ℕ) : ℤ) : AlgClosedQ) ≠ 0 := by
  have h : (((5 : ℕ) : ℤ) : AlgClosedQ) = 5 := by push_cast; ring
  rw [h]; norm_num

/-- **⚠️ THE CONTROL THAT PRICES THE HYPOTHESIS, and it is not a non-vacuity certificate**: in
`μ_4(AlgebraicClosure ℚ)` the element `−1` is `≠ 1` and has order `2`.

So `orderOf_rootsOfUnity_eq_of_prime` (`#951`) has no composite-index analogue to be replaced by,
and `hPT : e_n(P, T) ≠ 1` cannot yield a congruence mod `n`: at such a `ζ` the equation
`ζ ^ (a * d − b * c) = ζ ^ χ_4(σ)` says only that the two exponents agree mod `2`.  ⚠️ **Both
conjuncts are needed and neither alone is the point** — `ζ ≠ 1` is what makes `ζ` a legal input to
`#951`'s hypothesis, and `orderOf ζ = 2` is what makes the conclusion weaker than asked. -/
example : ∃ ζ : rootsOfUnity 4 AlgClosedQ, ζ ≠ 1 ∧ orderOf ζ = 2 := by
  have hmem : (-1 : AlgClosedQˣ) ∈ rootsOfUnity 4 AlgClosedQ := by
    rw [mem_rootsOfUnity]
    refine Units.ext ?_
    push_cast
    norm_num
  have hne : (⟨-1, hmem⟩ : rootsOfUnity 4 AlgClosedQ) ≠ 1 := by
    intro h
    have h' : ((-1 : AlgClosedQˣ) : AlgClosedQ) = ((1 : AlgClosedQˣ) : AlgClosedQ) :=
      congrArg (fun u : AlgClosedQˣ => (u : AlgClosedQ)) (Subtype.ext_iff.mp h)
    norm_num at h'
  refine ⟨⟨-1, hmem⟩, hne, orderOf_eq_prime ?_ hne⟩
  refine Subtype.ext (Units.ext ?_)
  push_cast
  norm_num

open Classical in
/-- **A primitive pair of `E[5]` exists on a curve that exists**, and it spans.  Both halves are
stated, so nothing is projected away. -/
example : ∃ P T : ((y2AddYEqX3 ℚ)⁄AlgClosedQ).torsion 5,
    orderOf (weilPairingN exampleTwo exampleIndexFive P T) = 5 ∧
      ∀ Q : ((y2AddYEqX3 ℚ)⁄AlgClosedQ).torsion 5, ∃ a b : ℤ, Q = a • P + b • T := by
  obtain ⟨P, T, horder⟩ := exists_orderOf_weilPairingN_eq
    (W := (y2AddYEqX3 ℚ)⁄AlgClosedQ) exampleTwo exampleIndexFive
  exact ⟨P, T, horder, fun Q => exists_zsmul_add_zsmul_eq_n exampleTwo exampleIndexFive horder Q⟩

open Classical in
/-- **And it is `ℤ/5`-independent on that curve.** -/
example : ∃ P T : ((y2AddYEqX3 ℚ)⁄AlgClosedQ).torsion 5,
    orderOf (weilPairingN exampleTwo exampleIndexFive P T) = 5 ∧
      ∀ u v : ℤ, u • P + v • T = 0 → ((u : ZMod 5) = 0 ∧ (v : ZMod 5) = 0) := by
  obtain ⟨P, T, horder⟩ := exists_orderOf_weilPairingN_eq
    (W := (y2AddYEqX3 ℚ)⁄AlgClosedQ) exampleTwo exampleIndexFive
  exact ⟨P, T, horder, fun _ _ huv =>
    intCast_eq_zero_of_zsmul_add_zsmul_eq_zero_n exampleTwo exampleIndexFive horder huv⟩

open Classical in
/-- **`det ρ_{E,5} = χ_5` on a curve that exists**, a schema instance in `σ`: there is a primitive
pair, `σ` has a matrix in it, and the determinant of that matrix is `χ_5(σ)`.

⚠️ Nothing here exhibits a `σ` with `χ_5 σ ≠ 1`; that is a statement about `AlgebraicClosure ℚ` and
not about this curve, and `#947` owns the `n = 3` form of it. -/
example (σ : AlgClosedQ ≃ₐ[ℚ] AlgClosedQ) :
    ∃ P T : ((y2AddYEqX3 ℚ)⁄AlgClosedQ).torsion 5,
      orderOf (weilPairingN exampleTwo exampleIndexFive P T) = 5 ∧
        ∃ a b c d : ℤ, σ • P = a • P + c • T ∧ σ • T = b • P + d • T ∧
          ((a * d - b * c : ℤ) : ZMod 5)
            = (galoisModularCyclotomicChar ℚ AlgClosedQ
                (natCard_rootsOfUnity_of_intCast_ne_zero exampleIndexFive) σ : ZMod 5) := by
  obtain ⟨P, T, horder⟩ := exists_orderOf_weilPairingN_eq
    (W := (y2AddYEqX3 ℚ)⁄AlgClosedQ) exampleTwo exampleIndexFive
  exact ⟨P, T, horder,
    exists_smul_eq_zsmul_add_zsmul_and_det_n_eq σ exampleTwo exampleIndexFive horder⟩

end Nonvacuity

end WeierstrassCurve.Affine
