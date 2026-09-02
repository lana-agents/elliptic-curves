/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import EllipticCurves.Fixtures
import EllipticCurves.FunctionField.WeilPairingRationalTorsion

/-!
# The determinant of the mod-`n` Galois representation is the cyclotomic character

`EllipticCurves.TateModule.Determinant` builds the determinant character `det ρ_{E,2}` of the
`2`-adic representation and says, of the identification with the cyclotomic character, that "it
needs the Weil pairing and its Galois equivariance".  Those exist now, and this file carries out
the identification at the **mod-`n`** level, for the two `n` at which this development has a
pairing:

```
σ • P = a • P + c • T ,   σ • T = b • P + d • T   ⟹   a * d − b * c ≡ χ_n(σ)   (mod n).
```

⚠️ **This identity is not a numbered result in Silverman *AEC*, and in particular it is not
III.8.1(e)**, which is the compatibility relation `e_{mm'}(S, T) = e_{m'}([m]S, T)`.  It is the
standard consequence of III.8.1(a) (bilinear), (b) (alternating) and (d) (Galois invariant), by the
computation Silverman runs inside the proof of III.8.6 with `α = ρ_{E,n}(σ)` in place of an
endomorphism of the Tate module.  The five letters are tabulated verbatim in
`EllipticCurves.FunctionField.WeilPairing`.  The mod-`n` statement is what the pairing proves
directly; the `ℓ`-adic one is its inverse limit.

## The two halves, and which inputs do what

**The algebra.**  `weilPairing{Two,Three}_zsmul_add_zsmul` expands `e_n` on a pair of integer
combinations of `P` and `T`.  Four terms come out of bilinearity; the two diagonal ones die by
`weilPairing{Two,Three}_self` (alternation) and the off-diagonal pair collapses to a single power by
`weilPairing{Two,Three}_swap` (antisymmetry), leaving the exponent `a * d − b * c`.  ⚠️ **That is
the whole reason a determinant appears at all**: it is the statement that an alternating bilinear
form on a rank-`2` module is a multiple of the determinant, run in coordinates.  Alternation and
antisymmetry are both consumed and neither is decorative.

**The arithmetic.**  `weilPairing{Two,Three}_galois_eq_pow` (`#944`) says `σ` raises `e_n(P, T)` to
the power `χ_n(σ)`.  Comparing the two expressions for `e_n(σ • P, σ • T)` gives
`ζ ^ (a * d − b * c) = ζ ^ χ_n(σ)` for `ζ = e_n(P, T)`, and `orderOf_rootsOfUnity_eq_of_prime` turns
that into a congruence mod `n` as soon as `ζ ≠ 1`.

## ⚠️ NO BASIS IS NEEDED, and the four integers are not assumed to exist

The identification is usually priced as needing `E[n]` presented as a free `ℤ/n`-module with a basis
and Mathlib's `LinearMap.det`.  It does not: taking the four matrix entries as **integers in
hypotheses** costs nothing, and the two facts that make those hypotheses harmless are proved here.

* `exists_zsmul_add_zsmul_eq_three` — every `Q ∈ E[3]` is `a • P + b • T`, as soon as
  `e_3(P, T) ≠ 1`.  ⚠️ This is a **counting** argument, not a linear-algebra one: the pairing gives
  injectivity of `(ℤ/3)² → E[3]` and `card_torsion_three` (`#E[3] = 9`) upgrades it to bijectivity.
* `intCast_eq_zero_of_zsmul_add_zsmul_eq_zero_three` — those coordinates are unique mod `3`, so the
  quantity `a * d − b * c` reduced mod `3` does not depend on which quadruple is chosen.

Together, `exists_smul_eq_zsmul_add_zsmul_and_det_three_eq` says of an **arbitrary** `σ` that it
*has* a matrix in a pairing-basis and that the determinant of that matrix is `χ_3(σ)`.  That is
`det ρ_{E,3} = χ_3` with nothing left assumed.

⚠️ **What is not delivered is the bundling, not the content.**  Writing the conclusion as an
equation between `LinearEquiv.det ∘ ρ_{E,3}` and `χ_3` needs `E[3]` presented as a `ZMod 3`-module,
with a determinant character built on it.  ⚠️ This paragraph originally added that it needs a
`Basis` as well, and that `nonempty_torsionThree_addEquiv` "supplies an `≃+` and not that"; the
first clause was wrong — `LinearEquiv.det` is basis-free — and the second, though true of
`nonempty_torsionThree_addEquiv`, was read as saying the module structure is unavailable, and it is
not.  `EllipticCurves.TateModule.DeterminantMod` (`#956`) supplies both halves: `torsionZModModule`
is `AddCommGroup.zmodModule` applied to `nsmul_mem_torsion`, with no hypothesis at all, and
`galoisDetMod 3 : G →* (ZMod 3)ˣ` is the bundled character, defined with no basis.  ⚠️ The identity
`galoisDetMod 3 = χ_3` between that character and this file's coordinate statement is now proved
too, in `EllipticCurves.FunctionField.WeilPairingDeterminantCharacter` (`#958`), and it consumes
`exists_smul_eq_zsmul_add_zsmul_and_det_three_eq` below — so this paragraph's "not delivered" is
spent, and what it named as the remaining gap is closed.  A reader should not conclude from the
absence of `LinearMap.det` below that the identification is unavailable — it is here, in
coordinates, and bundled one file away.

## ⚠️ `n = 2` is NOT the empty mirror it was in `#948`

`EllipticCurves.FunctionField.WeilPairingRationalTorsion` (`#948`) found that at `n = 2` its
corollary had no content at all: the conclusion held for every extension with no curve and no
hypothesis.  **That does not transfer here.**  At `n = 2` this file's conclusion is

```
a * d − b * c ≡ 1   (mod 2),
```

which is a genuine constraint on four integers, deduced from the pairing: the image of `ρ_{E,2}`
lands in `SL₂(𝔽₂)`.  ⚠️ It is true that the constraint is *also* reachable without the pairing,
because `GL₂(𝔽₂) = SL₂(𝔽₂)` makes "determinant `1`" and "invertible" the same condition — but that
is a statement about `𝔽₂`, and it is a different observation from `#948`'s, which was that there was
nothing to prove.  Here there is something to prove and the pairing proves it.

## Main results

* `orderOf_rootsOfUnity_eq_of_prime` — a `p`-th root of unity other than `1` has order exactly `p`.
* `weilPairing{Two,Three}_zsmul_{left,right}` — `e_n` is `ℤ`-homogeneous in each slot.
* `weilPairing{Two,Three}_zsmul_add_zsmul` — the determinant formula
  `e_n(aP + cT, bP + dT) = e_n(P, T) ^ (ad − bc)`.
* `intCast_eq_zero_of_zsmul_add_zsmul_eq_zero_{two,three}` — `P` and `T` are `ℤ/n`-independent.
* `exists_zsmul_add_zsmul_eq_{two,three}` — and they span `E[n]`.
* `exists_weilPairing{Two,Three}_ne_one` — such a pair exists.
* `galoisModularCyclotomicChar_{two,three}_eq_det` — the determinant identity.
* `exists_smul_eq_zsmul_add_zsmul_and_det_{two,three}_eq` — the same with the matrix produced.

## Scope

⚠️ **This does not close `EllipticCurves.TateModule.Determinant`'s gap and nothing below should be
read as closing it.**  `galoisDetTwo` there is `LinearEquiv.det` on the `2`-adic Tate module `T₂E`,
and identifying *it* with the cyclotomic character needs the pairing at **every** level `E[2 ^ k]`.
This development has the pairing at `n = 2` and `n = 3` and nowhere else, so the inverse limit
cannot be taken.  The only sentence there this file falsifies is the parenthetical claim that the
Weil pairing and its Galois equivariance are unavailable.

Also out of scope: general `n` (`#251`; ⚠️ **not** `#404`, see below); ⚠️ the ceiling inherited
here is `#938`'s
and **not** `#940`'s, since `exists_weilPairing{Two,Three}_ne_one` routes through surjectivity,
which is blocked at composite `n` twice.  The **trace** of `ρ_{E,n}` has no pairing-theoretic
description at all and `galoisTraceTwo` is untouched by any of this.

⚠️ **`#404` is closed, and the general-`n` entry above named it as the gate.**  PR #557 proved the
on-curve identity for `(Φₙ/ΨSqₙ, ωₙ/ψₙ³)` at every index over every commutative ring —
`WeierstrassCurve.Affine.equation_div_of_ψ_ne_zero`, `EllipticCurves.Torsion.OmegaCrux`.  What still
gates a general index is the *other* statement this tree also called `ωₙ`: the identification of
those coordinates with the **group-law** multiple `n • P`, which is `#251`.  ⚠️ The two-reading
account is `EllipticCurves.FunctionField.MulByNPullback`; the gate is relettered here, not lifted.

⚠️ `ker ρ_{E,3} ≤ ker χ_3` is the special case of the headline in which `σ` has matrix
`(1, 0, 0, 1)`.  It is already merged as
`EllipticCurves.FunctionField.WeilPairingRationalTorsionGalois`'s
`ker_galoisRepMod_three_le_ker_galoisModularCyclotomicChar` (`#947`), proved directly from `#948`,
and is not restated here.  ⚠️ That file's two statements that the determinant identity "needs a
basis of `E[3]` as a free `ℤ/3`-module together with its Galois action" were written before this
one existed and are retired by it; the repair is in this PR.

## References

* [J. H. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.7,
  III.8.1(a), (b), (d), and III.8.6.
-/

/-- **A `p`-th root of unity other than `1` has order exactly `p`**, for `p` prime.

This is what converts an equality of powers into a congruence of exponents mod `p`, and it is the
only reason the determinant statements below are congruences rather than equalities of integers.

⚠️ Stated over `[CommMonoid M]` for a general prime, at the root namespace: it mentions no curve, no
field and no pairing, and it is used at both `p = 2` and `p = 3`. -/
theorem orderOf_rootsOfUnity_eq_of_prime {M : Type*} [CommMonoid M] {p : ℕ} (hp : p.Prime)
    {ζ : rootsOfUnity p M} (hζ : ζ ≠ 1) : orderOf ζ = p := by
  have hpow : ζ ^ p = 1 := by
    refine Subtype.ext (Units.ext ?_)
    have hmem := ζ.2
    rw [mem_rootsOfUnity] at hmem
    push_cast
    exact congrArg (Units.val) hmem
  rcases hp.eq_one_or_self_of_dvd _ (orderOf_dvd_of_pow_eq_one hpow) with h | h
  · exact absurd (orderOf_eq_one_iff.mp h) hζ
  · exact h

namespace WeierstrassCurve.Affine

open CoordinateRing

section Torsion

variable {F : Type*} [Field F] [IsAlgClosed F] {W : Affine F} [W.IsElliptic]

open Classical in
/-- **`E[2]` is nontrivial**, the `n = 2` companion of `#948`'s `nontrivial_torsion_three`, which
is what supplies the nonzero point that surjectivity of the pairing needs. -/
theorem nontrivial_torsion_two (h2 : (2 : F) ≠ 0) : Nontrivial (W.torsion 2) := by
  haveI := W.finite_torsion_two h2
  exact Finite.one_lt_card_iff_nontrivial.mp (by rw [card_torsion_two h2]; omega)

end Torsion

/-! ### The determinant formula at `n = 2` -/

section BilinearTwo

variable {F : Type*} [Field F] [IsAlgClosed F] {W : Affine F} [W.IsElliptic]

open Classical in
/-- **`e_2` is `ℤ`-homogeneous in the second slot.**

⚠️ Proved from `map_zpow` on the *bundled* `weilPairingTwoHom` rather than by induction on `k`;
`ofAdd_zsmul` is the bridge between the `ℤ`-action on `E[2]` and the `zpow` on its multiplicative
copy. -/
theorem weilPairingTwo_zsmul_right (h2 : (2 : F) ≠ 0) (S T : W.torsion 2) (k : ℤ) :
    weilPairingTwo h2 S (k • T) = weilPairingTwo h2 S T ^ k := by
  simpa [ofAdd_zsmul] using
    map_zpow (weilPairingTwoHom h2 (Multiplicative.ofAdd S)) (Multiplicative.ofAdd T) k

open Classical in
/-- **`e_2` is `ℤ`-homogeneous in the first slot**, by antisymmetry from the second. -/
theorem weilPairingTwo_zsmul_left (h2 : (2 : F) ≠ 0) (S T : W.torsion 2) (k : ℤ) :
    weilPairingTwo h2 (k • S) T = weilPairingTwo h2 S T ^ k := by
  rw [weilPairingTwo_swap h2, weilPairingTwo_zsmul_right, weilPairingTwo_swap h2, inv_zpow, inv_inv]

open Classical in
/-- **The determinant formula at `n = 2`**: `e_2(aP + cT, bP + dT) = e_2(P, T) ^ (ad − bc)`.

Bilinearity produces four terms; `weilPairingTwo_self` kills the two diagonal ones and
`weilPairingTwo_swap` inverts one of the others, which is where the difference `ad − bc` comes
from. -/
theorem weilPairingTwo_zsmul_add_zsmul (h2 : (2 : F) ≠ 0) (P T : W.torsion 2) (a b c d : ℤ) :
    weilPairingTwo h2 (a • P + c • T) (b • P + d • T)
      = weilPairingTwo h2 P T ^ (a * d - b * c) := by
  rw [weilPairingTwo_add_left, weilPairingTwo_add_right, weilPairingTwo_add_right,
    weilPairingTwo_zsmul_left, weilPairingTwo_zsmul_left, weilPairingTwo_zsmul_left,
    weilPairingTwo_zsmul_left, weilPairingTwo_zsmul_right, weilPairingTwo_zsmul_right,
    weilPairingTwo_zsmul_right, weilPairingTwo_zsmul_right, weilPairingTwo_self,
    weilPairingTwo_self, weilPairingTwo_swap h2 P T]
  rw [one_zpow, one_zpow, one_zpow, one_zpow, one_mul, mul_one, ← zpow_mul, ← zpow_mul,
    inv_zpow, ← zpow_neg, ← zpow_add]
  ring_nf

open Classical in
/-- **`P` and `T` are `ℤ/2`-independent** as soon as `e_2(P, T) ≠ 1`.

⚠️ The hypothesis is consumed **twice, at both slots**: pairing the relation against `P` bounds `v`
and pairing it against `T` bounds `u`.  Neither half gives the other. -/
theorem intCast_eq_zero_of_zsmul_add_zsmul_eq_zero_two (h2 : (2 : F) ≠ 0) {P T : W.torsion 2}
    (hPT : weilPairingTwo h2 P T ≠ 1) {u v : ℤ} (huv : u • P + v • T = 0) :
    ((u : ZMod 2) = 0 ∧ (v : ZMod 2) = 0) := by
  have horder := orderOf_rootsOfUnity_eq_of_prime Nat.prime_two hPT
  have hv : weilPairingTwo h2 P T ^ v = 1 := by
    have hpair := congrArg (weilPairingTwo h2 P) huv
    rwa [weilPairingTwo_add_right, weilPairingTwo_zsmul_right, weilPairingTwo_zsmul_right,
      weilPairingTwo_self, one_zpow, one_mul, weilPairingTwo_zero_right] at hpair
  have hu : weilPairingTwo h2 P T ^ (-u) = 1 := by
    have hpair := congrArg (weilPairingTwo h2 T) huv
    rwa [weilPairingTwo_add_right, weilPairingTwo_zsmul_right, weilPairingTwo_zsmul_right,
      weilPairingTwo_self, one_zpow, mul_one, weilPairingTwo_swap h2, inv_zpow, ← zpow_neg,
      weilPairingTwo_zero_right] at hpair
  have hdvdv : (2 : ℤ) ∣ v := by
    have hd := orderOf_dvd_iff_zpow_eq_one.mpr hv
    rwa [horder] at hd
  have hdvdu : (2 : ℤ) ∣ u := by
    have hd := orderOf_dvd_iff_zpow_eq_one.mpr hu
    rw [horder] at hd
    exact (dvd_neg).mp hd
  exact ⟨(ZMod.intCast_zmod_eq_zero_iff_dvd _ 2).mpr hdvdu,
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ 2).mpr hdvdv⟩

open Classical in
/-- **A pair with `e_2(P, T) ≠ 1` spans `E[2]`.**

⚠️ A counting argument, not a linear-algebra one: the pairing gives injectivity of
`(ℤ/2)² → E[2]`, and `card_torsion_two` (`#E[2] = 4`) upgrades that to bijectivity. -/
theorem exists_zsmul_add_zsmul_eq_two (h2 : (2 : F) ≠ 0) {P T : W.torsion 2}
    (hPT : weilPairingTwo h2 P T ≠ 1) (Q : W.torsion 2) : ∃ a b : ℤ, Q = a • P + b • T := by
  haveI := W.finite_torsion_two h2
  set f : ZMod 2 × ZMod 2 → W.torsion 2 :=
    fun p => (p.1.val : ℤ) • P + (p.2.val : ℤ) • T with hf
  have hinj : Function.Injective f := by
    rintro ⟨u₁, v₁⟩ ⟨u₂, v₂⟩ hEq
    simp only [hf] at hEq
    have h0 : ((u₁.val : ℤ) - (u₂.val : ℤ)) • P + ((v₁.val : ℤ) - (v₂.val : ℤ)) • T = 0 := by
      rw [sub_zsmul, sub_zsmul, ← sub_eq_zero.mpr hEq]
      abel
    obtain ⟨hu, hv⟩ := intCast_eq_zero_of_zsmul_add_zsmul_eq_zero_two h2 hPT h0
    push_cast at hu hv
    rw [sub_eq_zero] at hu hv
    simp only [ZMod.natCast_val, ZMod.cast_id] at hu hv
    exact Prod.ext hu hv
  have hbij : Function.Bijective f :=
    (Nat.bijective_iff_injective_and_card f).mpr ⟨hinj, by rw [card_torsion_two h2]; simp⟩
  obtain ⟨p, hp⟩ := hbij.2 Q
  exact ⟨(p.1.val : ℤ), (p.2.val : ℤ), hp.symm⟩

open Classical in
/-- **A pair with `e_2(P, T) ≠ 1` exists**, so the hypotheses above are never vacuous.

The nonzero point comes from `nontrivial_torsion_two` and the nonzero value from surjectivity of
`e_2(P, ·)` onto `μ_2(F)` (`#938`), which has two elements. -/
theorem exists_weilPairingTwo_ne_one (h2 : (2 : F) ≠ 0) :
    ∃ P T : W.torsion 2, weilPairingTwo h2 P T ≠ 1 := by
  haveI := nontrivial_torsion_two (W := W) h2
  obtain ⟨P, hP⟩ := exists_ne (0 : W.torsion 2)
  have hcard := natCard_rootsOfUnity_of_ne_zero (F := F) (n := 2) h2
  haveI : Finite (rootsOfUnity 2 F) := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  haveI : Nontrivial (rootsOfUnity 2 F) :=
    Finite.one_lt_card_iff_nontrivial.mp (by rw [hcard]; norm_num)
  obtain ⟨ζ, hζ⟩ := exists_ne (1 : rootsOfUnity 2 F)
  obtain ⟨T, hT⟩ := weilPairingTwo_surjective h2 hP ζ
  exact ⟨P, T, hT ▸ hζ⟩

end BilinearTwo

/-! ### The determinant formula at `n = 3` -/

section BilinearThree

variable {F : Type*} [Field F] [IsAlgClosed F] {W : Affine F} [W.IsElliptic]

open Classical in
/-- **`e_3` is `ℤ`-homogeneous in the second slot**, the `n = 3` mirror of
`weilPairingTwo_zsmul_right`. -/
theorem weilPairingThree_zsmul_right (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) (S T : W.torsion 3)
    (k : ℤ) : weilPairingThree h2 h3 S (k • T) = weilPairingThree h2 h3 S T ^ k := by
  simpa [ofAdd_zsmul] using
    map_zpow (weilPairingThreeHom h2 h3 (Multiplicative.ofAdd S)) (Multiplicative.ofAdd T) k

open Classical in
/-- **`e_3` is `ℤ`-homogeneous in the first slot.** -/
theorem weilPairingThree_zsmul_left (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) (S T : W.torsion 3)
    (k : ℤ) : weilPairingThree h2 h3 (k • S) T = weilPairingThree h2 h3 S T ^ k := by
  rw [weilPairingThree_swap h2 h3, weilPairingThree_zsmul_right, weilPairingThree_swap h2 h3,
    inv_zpow, inv_inv]

open Classical in
/-- **The determinant formula at `n = 3`**: `e_3(aP + cT, bP + dT) = e_3(P, T) ^ (ad − bc)`. -/
theorem weilPairingThree_zsmul_add_zsmul (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) (P T : W.torsion 3)
    (a b c d : ℤ) :
    weilPairingThree h2 h3 (a • P + c • T) (b • P + d • T)
      = weilPairingThree h2 h3 P T ^ (a * d - b * c) := by
  rw [weilPairingThree_add_left, weilPairingThree_add_right, weilPairingThree_add_right,
    weilPairingThree_zsmul_left, weilPairingThree_zsmul_left, weilPairingThree_zsmul_left,
    weilPairingThree_zsmul_left, weilPairingThree_zsmul_right, weilPairingThree_zsmul_right,
    weilPairingThree_zsmul_right, weilPairingThree_zsmul_right, weilPairingThree_self,
    weilPairingThree_self, weilPairingThree_swap h2 h3 P T]
  rw [one_zpow, one_zpow, one_zpow, one_zpow, one_mul, mul_one, ← zpow_mul, ← zpow_mul,
    inv_zpow, ← zpow_neg, ← zpow_add]
  ring_nf

open Classical in
/-- **`P` and `T` are `ℤ/3`-independent** as soon as `e_3(P, T) ≠ 1`.

⚠️ The conclusion is a pair of congruences mod `3` and cannot be strengthened to `u = 0 ∧ v = 0`
over `ℤ`: `u = 3` satisfies the hypothesis.  That is exactly why the determinant statements below
live in `ZMod n`. -/
theorem intCast_eq_zero_of_zsmul_add_zsmul_eq_zero_three (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0)
    {P T : W.torsion 3} (hPT : weilPairingThree h2 h3 P T ≠ 1) {u v : ℤ}
    (huv : u • P + v • T = 0) : ((u : ZMod 3) = 0 ∧ (v : ZMod 3) = 0) := by
  have horder := orderOf_rootsOfUnity_eq_of_prime Nat.prime_three hPT
  have hv : weilPairingThree h2 h3 P T ^ v = 1 := by
    have hpair := congrArg (weilPairingThree h2 h3 P) huv
    rwa [weilPairingThree_add_right, weilPairingThree_zsmul_right, weilPairingThree_zsmul_right,
      weilPairingThree_self, one_zpow, one_mul, weilPairingThree_zero_right] at hpair
  have hu : weilPairingThree h2 h3 P T ^ (-u) = 1 := by
    have hpair := congrArg (weilPairingThree h2 h3 T) huv
    rwa [weilPairingThree_add_right, weilPairingThree_zsmul_right, weilPairingThree_zsmul_right,
      weilPairingThree_self, one_zpow, mul_one, weilPairingThree_swap h2 h3, inv_zpow, ← zpow_neg,
      weilPairingThree_zero_right] at hpair
  have hdvdv : (3 : ℤ) ∣ v := by
    have hd := orderOf_dvd_iff_zpow_eq_one.mpr hv
    rwa [horder] at hd
  have hdvdu : (3 : ℤ) ∣ u := by
    have hd := orderOf_dvd_iff_zpow_eq_one.mpr hu
    rw [horder] at hd
    exact (dvd_neg).mp hd
  exact ⟨(ZMod.intCast_zmod_eq_zero_iff_dvd _ 3).mpr hdvdu,
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ 3).mpr hdvdv⟩

open Classical in
/-- **A pair with `e_3(P, T) ≠ 1` spans `E[3]`.**

⚠️ `card_torsion_three` (`#E[3] = 9`) is load-bearing and is what makes this a counting argument;
the pairing only supplies injectivity. -/
theorem exists_zsmul_add_zsmul_eq_three (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) {P T : W.torsion 3}
    (hPT : weilPairingThree h2 h3 P T ≠ 1) (Q : W.torsion 3) : ∃ a b : ℤ, Q = a • P + b • T := by
  haveI := W.finite_torsion_three h3
  set f : ZMod 3 × ZMod 3 → W.torsion 3 :=
    fun p => (p.1.val : ℤ) • P + (p.2.val : ℤ) • T with hf
  have hinj : Function.Injective f := by
    rintro ⟨u₁, v₁⟩ ⟨u₂, v₂⟩ hEq
    simp only [hf] at hEq
    have h0 : ((u₁.val : ℤ) - (u₂.val : ℤ)) • P + ((v₁.val : ℤ) - (v₂.val : ℤ)) • T = 0 := by
      rw [sub_zsmul, sub_zsmul, ← sub_eq_zero.mpr hEq]
      abel
    obtain ⟨hu, hv⟩ := intCast_eq_zero_of_zsmul_add_zsmul_eq_zero_three h2 h3 hPT h0
    push_cast at hu hv
    rw [sub_eq_zero] at hu hv
    simp only [ZMod.natCast_val, ZMod.cast_id] at hu hv
    exact Prod.ext hu hv
  have hbij : Function.Bijective f :=
    (Nat.bijective_iff_injective_and_card f).mpr ⟨hinj, by rw [card_torsion_three h2 h3]; simp⟩
  obtain ⟨p, hp⟩ := hbij.2 Q
  exact ⟨(p.1.val : ℤ), (p.2.val : ℤ), hp.symm⟩

open Classical in
/-- **A pair with `e_3(P, T) ≠ 1` exists.**

⚠️ Its two inputs are `#948`'s `nontrivial_torsion_three` and `#938`'s surjectivity, so this is the
second consumer of `#948` and the fourth deliverable `#938` has unblocked without that having been
its purpose. -/
theorem exists_weilPairingThree_ne_one (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) :
    ∃ P T : W.torsion 3, weilPairingThree h2 h3 P T ≠ 1 := by
  haveI := nontrivial_torsion_three (W := W) h2 h3
  obtain ⟨P, hP⟩ := exists_ne (0 : W.torsion 3)
  have hcard := natCard_rootsOfUnity_of_ne_zero (F := F) (n := 3) h3
  haveI : Finite (rootsOfUnity 3 F) := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  haveI : Nontrivial (rootsOfUnity 3 F) :=
    Finite.one_lt_card_iff_nontrivial.mp (by rw [hcard]; norm_num)
  obtain ⟨ζ, hζ⟩ := exists_ne (1 : rootsOfUnity 3 F)
  obtain ⟨T, hT⟩ := weilPairingThree_surjective h2 h3 hP ζ
  exact ⟨P, T, hT ▸ hζ⟩

end BilinearThree

/-! ### `det ρ_{E,n} = χ_n` -/

section Galois

variable {S F : Type*} [Field S] [Field F] [Algebra S F] {W : Affine S} [W.IsElliptic]
  [IsAlgClosed F]

open Classical in
/-- **The determinant identity at `n = 2`**: if `σ` acts on the pairing-basis `(P, T)` by the matrix
`(a, b; c, d)` then `a * d − b * c ≡ χ_2(σ)` mod `2`. -/
theorem galoisModularCyclotomicChar_two_eq_det (σ : F ≃ₐ[S] F) (h2 : (2 : F) ≠ 0)
    {P T : (W⁄F).torsion 2} (hPT : weilPairingTwo h2 P T ≠ 1) {a b c d : ℤ}
    (hP : σ • P = a • P + c • T) (hT : σ • T = b • P + d • T) :
    ((a * d - b * c : ℤ) : ZMod 2)
      = (galoisModularCyclotomicChar S F (natCard_rootsOfUnity_of_ne_zero h2) σ : ZMod 2) := by
  set ζ := weilPairingTwo h2 P T with hζ
  have horder := orderOf_rootsOfUnity_eq_of_prime Nat.prime_two hPT
  have key : ζ ^ (a * d - b * c)
      = ζ ^ ((galoisModularCyclotomicChar S F (natCard_rootsOfUnity_of_ne_zero h2) σ :
          ZMod 2)).val := by
    rw [← weilPairingTwo_zsmul_add_zsmul h2 P T a b c d, ← hP, ← hT,
      weilPairingTwo_galois_eq_pow σ h2 P T]
  rw [← zpow_natCast] at key
  have hmod := (zpow_eq_zpow_iff_modEq (x := ζ)).mp key
  rw [horder] at hmod
  have hcast := (ZMod.intCast_eq_intCast_iff _ _ 2).mpr hmod
  push_cast at hcast
  simpa using hcast

open Classical in
/-- **`im ρ_{E,2} ⊆ SL₂(𝔽₂)`**: the matrix of any `σ` in a pairing-basis of `E[2]` has odd
determinant.

⚠️ **This is not the empty `n = 2` mirror that `#948` found**, and its finding must not be quoted
here.  There the `n = 2` conclusion held with no curve and no hypothesis, so there was nothing to
prove; here there is a genuine constraint on four integers and the pairing is what proves it.  What
is true is that the same constraint is reachable another way, since `GL₂(𝔽₂) = SL₂(𝔽₂)` — but that
is a fact about `𝔽₂`, not about this statement. -/
theorem intCast_det_two_eq_one (σ : F ≃ₐ[S] F) (h2 : (2 : F) ≠ 0) {P T : (W⁄F).torsion 2}
    (hPT : weilPairingTwo h2 P T ≠ 1) {a b c d : ℤ} (hP : σ • P = a • P + c • T)
    (hT : σ • T = b • P + d • T) : ((a * d - b * c : ℤ) : ZMod 2) = 1 := by
  rw [galoisModularCyclotomicChar_two_eq_det σ h2 hPT hP hT,
    galoisModularCyclotomicChar_two_eq_one (natCard_rootsOfUnity_of_ne_zero h2) σ]
  rfl

open Classical in
/-- **Every `σ` has a matrix in a pairing-basis of `E[2]`, and its determinant is `1`.** -/
theorem exists_smul_eq_zsmul_add_zsmul_and_det_two_eq (σ : F ≃ₐ[S] F) (h2 : (2 : F) ≠ 0)
    {P T : (W⁄F).torsion 2} (hPT : weilPairingTwo h2 P T ≠ 1) :
    ∃ a b c d : ℤ, σ • P = a • P + c • T ∧ σ • T = b • P + d • T ∧
      ((a * d - b * c : ℤ) : ZMod 2) = 1 := by
  obtain ⟨a, c, hac⟩ := exists_zsmul_add_zsmul_eq_two h2 hPT (σ • P)
  obtain ⟨b, d, hbd⟩ := exists_zsmul_add_zsmul_eq_two h2 hPT (σ • T)
  exact ⟨a, b, c, d, hac, hbd, intCast_det_two_eq_one σ h2 hPT hac hbd⟩

open Classical in
/-- **The determinant identity at `n = 3`**, in coordinates — Silverman *AEC* III.8.1(a), (b) and
(d), ⚠️ **not** III.8.1(e): if `σ` acts on a pairing-basis `(P, T)` of `E[3]` by the matrix
`(a, b; c, d)` then

```
a * d − b * c ≡ χ_3(σ)   (mod 3).
```

⚠️ Unlike its `n = 2` companion this is **not** a fixed value: `(ZMod 3)ˣ` has two elements, so the
right-hand side genuinely varies with `σ`.  ⚠️ `hPT` is load-bearing and its absence makes the
statement *false*, not merely unproved: at `P = T = 0` every quadruple satisfies both matrix
hypotheses. -/
theorem galoisModularCyclotomicChar_three_eq_det (σ : F ≃ₐ[S] F) (h2 : (2 : F) ≠ 0)
    (h3 : (3 : F) ≠ 0) {P T : (W⁄F).torsion 3} (hPT : weilPairingThree h2 h3 P T ≠ 1)
    {a b c d : ℤ} (hP : σ • P = a • P + c • T) (hT : σ • T = b • P + d • T) :
    ((a * d - b * c : ℤ) : ZMod 3)
      = (galoisModularCyclotomicChar S F (natCard_rootsOfUnity_of_ne_zero h3) σ : ZMod 3) := by
  set ζ := weilPairingThree h2 h3 P T with hζ
  have horder := orderOf_rootsOfUnity_eq_of_prime Nat.prime_three hPT
  have key : ζ ^ (a * d - b * c)
      = ζ ^ ((galoisModularCyclotomicChar S F (natCard_rootsOfUnity_of_ne_zero h3) σ :
          ZMod 3)).val := by
    rw [← weilPairingThree_zsmul_add_zsmul h2 h3 P T a b c d, ← hP, ← hT,
      weilPairingThree_galois_eq_pow σ h2 h3 P T]
  rw [← zpow_natCast] at key
  have hmod := (zpow_eq_zpow_iff_modEq (x := ζ)).mp key
  rw [horder] at hmod
  have hcast := (ZMod.intCast_eq_intCast_iff _ _ 3).mpr hmod
  push_cast at hcast
  simpa using hcast

open Classical in
/-- **`det ρ_{E,3} = χ_3`, with nothing left assumed about `σ`.**

Every `σ` has a matrix in a pairing-basis of `E[3]` — that is `exists_zsmul_add_zsmul_eq_three`,
which is where `#E[3] = 9` enters — and the determinant of that matrix is `χ_3(σ)`.  The four
integers are only determined mod `3`, but so is the conclusion
(`intCast_eq_zero_of_zsmul_add_zsmul_eq_zero_three`), so the statement does not depend on the
choice.

⚠️ Read as `det ρ_{E,3} = χ_3` this is the whole content of the identification.  What it is not is
an equation between `LinearEquiv.det ∘ ρ_{E,3}` and `χ_3`; that bundling is a separate, structural,
matter, and it is `galoisDetMod_three_eq_galoisModularCyclotomicChar`
(`EllipticCurves.FunctionField.WeilPairingDeterminantCharacter`, `#958`), a consumer of the
statement below.  ⚠️ None of it touches `EllipticCurves.TateModule.Determinant`'s `2`-adic
`galoisDetTwo`. -/
theorem exists_smul_eq_zsmul_add_zsmul_and_det_three_eq (σ : F ≃ₐ[S] F) (h2 : (2 : F) ≠ 0)
    (h3 : (3 : F) ≠ 0) {P T : (W⁄F).torsion 3} (hPT : weilPairingThree h2 h3 P T ≠ 1) :
    ∃ a b c d : ℤ, σ • P = a • P + c • T ∧ σ • T = b • P + d • T ∧
      ((a * d - b * c : ℤ) : ZMod 3)
        = (galoisModularCyclotomicChar S F (natCard_rootsOfUnity_of_ne_zero h3) σ : ZMod 3) := by
  obtain ⟨a, c, hac⟩ := exists_zsmul_add_zsmul_eq_three h2 h3 hPT (σ • P)
  obtain ⟨b, d, hbd⟩ := exists_zsmul_add_zsmul_eq_three h2 h3 hPT (σ • T)
  exact ⟨a, b, c, d, hac, hbd, galoisModularCyclotomicChar_three_eq_det σ h2 h3 hPT hac hbd⟩

/-! ### Non-vacuity

Every statement above carries `[IsAlgClosed F]`, so `ℚ` cannot witness it; the certificates below
are on `#936`'s curve `y² + y = x³` base-changed to `AlgebraicClosure ℚ`, with **`S = ℚ` and not
`S = F`**, so that `Gal(F/S)` is a genuine group and not the trivial one.

⚠️ The certificates restate each conclusion **in full** rather than projecting out of an
`obtain` (`#916`), and each one names a pair `(P, T)` existentially rather than assuming one: the
whole point of `exists_weilPairing{Two,Three}_ne_one` is that no such assumption is needed.

⚠️ **Four refutations, all measured against this file as committed** (`#948`'s rule) and pasted
rather than paraphrased (`#940`, `#944`).

**R1 — `hPT` is load-bearing in the `n = 3` determinant identity.**  Delete it from the binder:

```
error(lean.unknownIdentifier): Unknown identifier `hPT`
error: unsolved goals
…
hP : σ • P = a • P + c • T
hT : σ • T = b • P + d • T
ζ : ↥(rootsOfUnity 3 F) := weilPairingThree h2 h3 P T
⊢ ↑(a * d - b * c) = ↑((galoisModularCyclotomicChar S F ⋯) σ)
```

⚠️ Without `hPT` the theorem is **false**, not merely unproved: at `P = T = 0` every quadruple
`(a, b, c, d)` satisfies both matrix hypotheses, so no value of `a * d − b * c` is determined.  The
leftover goal above is exactly the whole conclusion, with both matrix hypotheses still in hand.

**R2 — the independence lemma consumes both slots.**  Pair the relation against `P` only, deleting
the `hu` block and the `hdvdu` it feeds:

```
error: unsolved goals
…
huv : u • P + v • T = 0
horder : orderOf (weilPairingThree h2 h3 P T) = 3
hv : weilPairingThree h2 h3 P T ^ v = 1
hdvdv : 3 ∣ v
⊢ ↑u = 0
```

⚠️ The first slot bounds `v` and says nothing about `u`; the `u` half needs the *second* slot.  Same
shape as `#948`'s third refutation and for the same reason — a statement about a **pair** has to be
paired against both members.

**R3 — `#E[3] = 9` is load-bearing in the spanning lemma.**  Drop `card_torsion_three` and try to
reach bijectivity from injectivity alone:

```
error: unsolved goals
…
hinj : Function.Injective f
⊢ 9 = Nat.card { x // 3 • x = 0 }
```

⚠️ The residual goal is literally the torsion count.  The pairing supplies injectivity of
`(ℤ/3)² → E[3]` and nothing else; the count is the only other input, which is why this file calls
the spanning lemma a counting argument.

**R4 — the conclusion does not lift to `ℤ`.**  Strengthen the independence lemma to `u = 0 ∧ v = 0`:

```
error: Application type mismatch: The argument
  (ZMod.intCast_zmod_eq_zero_iff_dvd u 3).mpr hdvdu
has type
  ↑u = 0
but is expected to have type
  u = 0
```

⚠️ **A refutation that changes only a type ascription is not a refutation.**  The first attempt at
R4 was to write the determinant identity's left-hand side as `(a * d - b * c : ℤ)` against a
`ZMod 3`-valued right-hand side — and it **compiled**, because elaboration simply re-inserts the
coercion and recovers the original statement.  Only moving the *whole* conclusion into `ℤ`, as
above, actually tests anything.  This belongs beside `#944`'s finding that a certificate can be
green and consume nothing: here a *refutation* was green and refuted nothing. -/

section Nonvacuity

/-! The certificate curve `y² + y = x³` is the shared `EllipticCurves.Fixture.y2AddYEqX3`, and the
base — algebraically closed, and of characteristic `0` so that `2 ≠ 0` and `3 ≠ 0` — is
`EllipticCurves.Fixture.AlgClosedQ`, whose single `[CharZero F]` instance also supplies
`IsElliptic` here. -/

open EllipticCurves.Fixture

private lemma exampleTwo : (2 : AlgClosedQ) ≠ 0 := two_ne_zero

private lemma exampleThree : (3 : AlgClosedQ) ≠ 0 := three_ne_zero_of_charZero _

open Classical in
/-- **A pairing-basis of `E[3]` exists on a curve that exists**: a pair `(P, T)` with
`e_3(P, T) ≠ 1` which spans.  Both halves are stated, so nothing is projected away. -/
example : ∃ P T : ((y2AddYEqX3 ℚ)⁄AlgClosedQ).torsion 3,
    weilPairingThree exampleTwo exampleThree P T ≠ 1 ∧
      ∀ Q : ((y2AddYEqX3 ℚ)⁄AlgClosedQ).torsion 3, ∃ a b : ℤ, Q = a • P + b • T := by
  obtain ⟨P, T, hPT⟩ := exists_weilPairingThree_ne_one
    (W := (y2AddYEqX3 ℚ)⁄AlgClosedQ) exampleTwo exampleThree
  exact ⟨P, T, hPT, fun Q => exists_zsmul_add_zsmul_eq_three exampleTwo exampleThree hPT Q⟩

open Classical in
/-- **`det ρ_{E,3} = χ_3` on a curve that exists**, a schema instance in `σ`: there is a
pairing-basis, `σ` has a matrix in it, and the determinant of that matrix is `χ_3(σ)`.

⚠️ Nothing here exhibits a `σ` with `χ_3 σ ≠ 1`; that is a statement about `AlgebraicClosure ℚ` and
not about this curve, and `#947` owns it. -/
example (σ : AlgClosedQ ≃ₐ[ℚ] AlgClosedQ) :
    ∃ P T : ((y2AddYEqX3 ℚ)⁄AlgClosedQ).torsion 3,
      weilPairingThree exampleTwo exampleThree P T ≠ 1 ∧
        ∃ a b c d : ℤ, σ • P = a • P + c • T ∧ σ • T = b • P + d • T ∧
          ((a * d - b * c : ℤ) : ZMod 3)
            = (galoisModularCyclotomicChar ℚ AlgClosedQ
                (natCard_rootsOfUnity_of_ne_zero exampleThree) σ : ZMod 3) := by
  obtain ⟨P, T, hPT⟩ := exists_weilPairingThree_ne_one
    (W := (y2AddYEqX3 ℚ)⁄AlgClosedQ) exampleTwo exampleThree
  exact ⟨P, T, hPT,
    exists_smul_eq_zsmul_add_zsmul_and_det_three_eq σ exampleTwo exampleThree hPT⟩

open Classical in
/-- **`im ρ_{E,2} ⊆ SL₂(𝔽₂)` on the same curve.**  The `n = 2` statement, whose right-hand side is
the fixed value `1` rather than a character of `σ` — and which, unlike `#948`'s `n = 2` corollary,
still needs a curve, a pairing-basis and a matrix. -/
example (σ : AlgClosedQ ≃ₐ[ℚ] AlgClosedQ) :
    ∃ P T : ((y2AddYEqX3 ℚ)⁄AlgClosedQ).torsion 2,
      weilPairingTwo exampleTwo P T ≠ 1 ∧
        ∃ a b c d : ℤ, σ • P = a • P + c • T ∧ σ • T = b • P + d • T ∧
          ((a * d - b * c : ℤ) : ZMod 2) = 1 := by
  obtain ⟨P, T, hPT⟩ := exists_weilPairingTwo_ne_one (W := (y2AddYEqX3 ℚ)⁄AlgClosedQ) exampleTwo
  exact ⟨P, T, hPT, exists_smul_eq_zsmul_add_zsmul_and_det_two_eq σ exampleTwo hPT⟩

end Nonvacuity

end Galois

end WeierstrassCurve.Affine
