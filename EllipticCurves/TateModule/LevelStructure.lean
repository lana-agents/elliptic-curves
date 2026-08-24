/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import EllipticCurves.TateModule.Basic
import EllipticCurves.Torsion.TwoPrimary

/-!
# Level structure of the Tate module: torsion-freeness, the kernel of `proj k`, and surjectivity

`EllipticCurves.TateModule.Basic` constructs the `ℓ`-adic Tate module `T_ℓ E = lim_k E[ℓ^k]` as the
additive subgroup of compatible families `f : ℕ → W.Point` (`f k ∈ E[ℓ^k]`, `ℓ • f (k+1) = f k`),
together with its level projections `proj k : T_ℓ E →+ E[ℓ^k]` and its `ℤ_[ℓ]`-module structure.
This file records the first structural facts about that module (Silverman, *AEC*, III.7 and
Remark 7.1.2).

## What is unconditional and what is not

* **Torsion-freeness is unconditional.** `T_ℓ E` has no `ℤ_[ℓ]`-torsion whatsoever
  (`NoZeroSMulDivisors ℤ_[ℓ] (W.tateModule ℓ)`) — no hypothesis on `F`, on `W`, or on divisibility.
  This is the half of Silverman III.7.1 that needs no structure theory, and it is what makes
  `T_ℓ E` an `ℓ`-adic *lattice* rather than merely a module.
* **The kernel computation is unconditional.** `ker (proj k)` is exactly `ℓ^k · T_ℓ E`
  (`mem_ker_proj_iff`). The nontrivial inclusion is a *shift*: a family vanishing at level `k` is
  `ℓ^k` times the family `j ↦ f (j + k)`.
* **Level surjectivity is conditional**, on multiplication by `ℓ` being surjective on `W.Point`
  (`proj_surjective`). This is the only hypothesis in the file, and it is stated in exactly the
  shape `EllipticCurves.Torsion.DoublingSurjective` delivers at `ℓ = 2`.

## The `ℓ = 2` layer

Over an algebraically closed field with `2 ≠ 0`, `nsmul_two_surjective` discharges that hypothesis,
so `proj k : T_2 E →+ E[2^k]` is surjective for every `k`. Combined with the kernel computation this
gives `T_2 E / 2^k T_2 E ≃+ E[2^k]`, and combined with `#E[2^k] = 4^k`
(`EllipticCurves.Torsion.TwoPrimary`) it shows `T_2 E` is infinite. No hypothesis on `(3 : F)` is
used — ⚠️ **and that sentence is about this layer only**: at `ℓ = 3`, `nsmul_three_surjective`
likewise needs `(2 : F) ≠ 0` alone, and `(3 : F) ≠ 0` enters only through the *count*
`#E[3^k] = 9^k`. `EllipticCurves.TateModule.FreeThree` records that split.

⚠️ The clause this paragraph used to carry — *"The analogous statements for `ℓ ≠ 2` wait on
surjectivity of `[ℓ]`"* — is false at `ℓ = 3`, and so is the reading of its continuation that made
`x(nP) = Φₙ/ΨSqₙ` a *gate*: at `n = 3` that formula is **proved**
(`EllipticCurves.Torsion.TriplingSurjective`), so `[3]`-surjectivity is available and the `ℓ = 3`
instances of everything in this file exist. They are stated in
`EllipticCurves.TateModule.FreeThree` rather than here, so as not to drag
`EllipticCurves.Torsion.ThreePrimary` into a file whose subject is the levelwise-generic structure
of `T_ℓE`. For `ℓ ≥ 5` the original sentence stands verbatim: the general coordinate formula is
still the gate.

⚠️ **The quotient statement is no longer part of this layer.**
`WeierstrassCurve.Affine.tateModule.quotientProjEquiv` is stated at an arbitrary `ℓ`, above the
`ℓ = 2` section, and takes the surjectivity witness directly; the `ℓ = 2` reading is
`quotientProjEquiv (nsmul_two_surjective h2) k` and the `ℓ = 3` reading is
`quotientProjEquiv (nsmul_three_surjective h2) k`, certified as an `example` in
`EllipticCurves.TateModule.FreeThree`. It is unsuffixed, so it was generalised in place rather than
twinned: a second `quotientProjEquiv` would be a name collision. *Renaming it to
`quotientProjEquivTwo` and adding a `…Three` would also have avoided the collision, and was
rejected because it renames a public declaration to buy nothing the generic form does not.*

## What this file does *not* do

It does **not** prove `T_ℓ E ≃ₗ[ℤ_[ℓ]] ℤ_[ℓ]²`. The torsion structure theorem supplies an
isomorphism `E[ℓ^k] ≃+ (ZMod (ℓ^k))²` at each level *independently*, and a family of unrelated
isomorphisms says nothing about an inverse limit; the freeness statement needs a system of levelwise
bases *compatible* with the transition maps, obtained by lifting a basis of `E[ℓ]` up the tower.
The facts proved here — torsion-freeness, `T_ℓ E / ℓ^k T_ℓ E ≃+ E[ℓ^k]`, and level surjectivity —
are the ambient input that construction consumes.

## Main statements

* `WeierstrassCurve.Affine.tateModule.smul_pow_coe`: iterated compatibility `ℓ^m • f (k+m) = f k`.
* `WeierstrassCurve.Affine.tateModule.eq_zero_of_smul_eq_zero` and the resulting
  `NoZeroSMulDivisors ℤ_[ℓ] (W.tateModule ℓ)` instance: `T_ℓ E` is torsion-free.
* `WeierstrassCurve.Affine.tateModule.mem_ker_proj_iff`: `ker (proj k) = ℓ^k · T_ℓ E`.
* `WeierstrassCurve.Affine.tateModule.proj_surjective`: the level projections are surjective when
  `[ℓ]` is surjective on `W.Point`; `…exists_mem_tateModule_apply_eq`, its unbundled form; and
  `…exists_nsmul_pow_eq_of_proj_surjective`, the converse divisibility content of that conclusion.
* `WeierstrassCurve.Affine.tateModule.infinite_tateModule_of_card` and
  `WeierstrassCurve.Affine.tateModule.nontrivial_tateModule_of_card`: `T_ℓE` is not the zero
  module, given level surjectivity and the count `#E[ℓ^k] = ℓ^k · ℓ^k`.
* `WeierstrassCurve.Affine.tateModule.quotientProjEquiv`: `T_ℓ E / ℓ^k T_ℓ E ≃+ E[ℓ^k]`, given
  level surjectivity. ⚠️ **Stated at an arbitrary `ℓ`.** The clause this bullet used to carry —
  which listed it among *"the `ℓ = 2` instance"* — is retired: the declaration is unsuffixed and
  was hardcoded at `2`, so it was generalised in place rather than twinned.
* `WeierstrassCurve.Affine.tateModule.proj_two_surjective`,
  `WeierstrassCurve.Affine.tateModule.infinite_tateModule_two`,
  `WeierstrassCurve.Affine.tateModule.nontrivial_tateModule_two`,
  `WeierstrassCurve.Affine.tateModule.exists_ne_zero_tateModule_two`: the `ℓ = 2` instance.
  ⚠️ **Their `ℓ = 3` twins all exist and are in `EllipticCurves.TateModule.FreeThree`**, not here —
  `proj_three_surjective`, `infinite_tateModule_three`, `nontrivial_tateModule_three` and
  `exists_ne_zero_tateModule_three` — because that file may import
  `EllipticCurves.Torsion.ThreePrimaryBasis` and this one deliberately may not. *That file is
  downstream of this one, so the citation can only run in this direction.*

`nontrivial_tateModule_two` is worth singling out: `EllipticCurves.TateModule.Basic` proves nothing
that would distinguish `T_ℓ E` from the zero module, so it is the statement that certifies the
construction there is not vacuous. It is now a one-line instance of
`nontrivial_tateModule_of_card`, whose `ℓ = 3` instance is `infinite_tateModule_three` in
`EllipticCurves.TateModule.FreeThree`.

## References

* [J. H. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.7 and Remark 7.1.2.
-/

open scoped AddSubgroup

namespace WeierstrassCurve.Affine

namespace tateModule

variable {F : Type*} [Field F] [DecidableEq F] {W : Affine F} {ℓ : ℕ}

/-! ## Iterated compatibility -/

/-- **Iterated compatibility**: descending `m` levels multiplies by `ℓ^m`. -/
lemma smul_pow_coe (f : W.tateModule ℓ) (k m : ℕ) :
    ℓ ^ m • (f : ℕ → W.Point) (k + m) = (f : ℕ → W.Point) k := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [pow_succ, mul_smul, show k + (m + 1) = (k + m) + 1 from rfl, smul_coe_succ, ih]

/-- Two natural numbers with the same residue modulo `ℓ^k` act identically on `ℓ^k`-torsion.

`EllipticCurves.TateModule.Basic` proves this as a `private` lemma for its own use; `private` does
not cross file boundaries, so it is restated here rather than by editing that file. -/
lemma nsmul_eq_of_natCast_eq {k : ℕ} {x : W.Point} (hx : x ∈ W.torsion (ℓ ^ k)) {s t : ℕ}
    (h : (s : ZMod (ℓ ^ k)) = (t : ZMod (ℓ ^ k))) : s • x = t • x := by
  rw [AddSubgroup.torsionBy.mod_self_nsmul' s hx, AddSubgroup.torsionBy.mod_self_nsmul' t hx,
    (ZMod.natCast_eq_natCast_iff _ _ _).mp h]

/-! ## Torsion-freeness over `ℤ_[ℓ]` -/

open PadicInt in
/-- **`T_ℓ E` has no `ℤ_[ℓ]`-torsion.** If `a ≠ 0` kills `f`, then `f = 0`.

Write `a = u · ℓ^v` with `u` a unit and `v = a.valuation`. At level `k + v` the residue of `a` is
`ℓ^v` times a unit of `ZMod (ℓ^(k+v))`, so multiplying the hypothesis by the inverse of that unit
gives `ℓ^v • f (k + v) = 0`; but `ℓ^v • f (k + v) = f k`. As `k` was arbitrary, `f = 0`.

This is unconditional: it needs nothing about `F`, about `W`, or about divisibility. -/
theorem eq_zero_of_smul_eq_zero [Fact ℓ.Prime] {a : ℤ_[ℓ]} (ha : a ≠ 0) {f : W.tateModule ℓ}
    (hf : a • f = 0) : f = 0 := by
  have hpos : ∀ m : ℕ, 0 < ℓ ^ m := fun m => pow_pos (Fact.out : ℓ.Prime).pos m
  refine tateModule.ext fun k => ?_
  set v := a.valuation with hv
  set n := k + v with hn
  haveI : NeZero (ℓ ^ n) := ⟨(hpos n).ne'⟩
  have h0 : (toZModPow n a).val • (f : ℕ → W.Point) n = 0 := by
    have := congrArg (fun g : W.tateModule ℓ => (g : ℕ → W.Point) n) hf
    simpa using this
  have hw : IsUnit (toZModPow n ((unitCoeff ha : ℤ_[ℓ]))) :=
    ((unitCoeff ha).isUnit).map (toZModPow n)
  have hares : ((toZModPow n a).val : ZMod (ℓ ^ n))
      = toZModPow n ((unitCoeff ha : ℤ_[ℓ])) * ((ℓ : ZMod (ℓ ^ n)) ^ v) := by
    rw [ZMod.natCast_val, ZMod.cast_id]
    conv_lhs => rw [unitCoeff_spec ha]
    push_cast [map_mul, map_pow]
    simp [← hv]
  set t : ℕ := (↑(hw.unit⁻¹) : ZMod (ℓ ^ n)).val with ht
  have hts : ((t * (toZModPow n a).val : ℕ) : ZMod (ℓ ^ n)) = ((ℓ ^ v : ℕ) : ZMod (ℓ ^ n)) := by
    push_cast [ht, ZMod.natCast_val, ZMod.cast_id, hares]
    rw [← mul_assoc, IsUnit.val_inv_mul hw, one_mul]
  have hkey := nsmul_eq_of_natCast_eq (f.2.1 n) hts
  rw [mul_smul, h0, smul_zero] at hkey
  have hfk : (f : ℕ → W.Point) k = 0 := by
    rw [← smul_pow_coe f k v, ← hn]
    exact hkey.symm
  simpa using hfk

/-- **`T_ℓ E` is a torsion-free `ℤ_[ℓ]`-module** (Silverman, *AEC*, III.7.1). -/
instance [Fact ℓ.Prime] : NoZeroSMulDivisors ℤ_[ℓ] (W.tateModule ℓ) where
  eq_zero_or_eq_zero_of_smul_eq_zero {a f} h := by
    by_cases ha : a = 0
    · exact Or.inl ha
    · exact Or.inr (eq_zero_of_smul_eq_zero ha h)

/-! ## The kernel of the level projection -/

/-- `ℓ^k` kills the level-`k` projection: the easy inclusion `ℓ^k · T_ℓ E ≤ ker (proj k)`. -/
lemma proj_nsmul_pow (g : W.tateModule ℓ) (k : ℕ) : proj k (ℓ ^ k • g) = 0 := by
  refine Subtype.ext ?_
  change ℓ ^ k • (g : ℕ → W.Point) k = 0
  exact mem_torsion_iff.mp (g.2.1 k)

/-- **A family vanishing at level `k` is `ℓ^k` times a family**: the hard inclusion
`ker (proj k) ≤ ℓ^k · T_ℓ E`. The witness is the shifted family `j ↦ f (j + k)`, which is
`ℓ^j`-torsion precisely because `ℓ^j • f (j + k) = f k = 0`. -/
lemma exists_nsmul_pow_eq_of_proj_eq_zero {k : ℕ} {f : W.tateModule ℓ} (h : proj k f = 0) :
    ∃ g : W.tateModule ℓ, ℓ ^ k • g = f := by
  have hfk : (f : ℕ → W.Point) k = 0 := congrArg Subtype.val h
  refine ⟨⟨fun j => (f : ℕ → W.Point) (j + k), ⟨fun j => ?_, fun j => ?_⟩⟩, ?_⟩
  · rw [mem_torsion_iff]
    change ℓ ^ j • (f : ℕ → W.Point) (j + k) = 0
    rw [add_comm j k, smul_pow_coe f k j, hfk]
  · change ℓ • (f : ℕ → W.Point) (j + 1 + k) = (f : ℕ → W.Point) (j + k)
    rw [show j + 1 + k = (j + k) + 1 by omega, smul_coe_succ]
  · refine tateModule.ext fun j => ?_
    change ℓ ^ k • (f : ℕ → W.Point) (j + k) = (f : ℕ → W.Point) j
    exact smul_pow_coe f j k

/-- **The kernel of `proj k` is exactly `ℓ^k · T_ℓ E`.** Unconditional. -/
lemma mem_ker_proj_iff {k : ℕ} {f : W.tateModule ℓ} :
    f ∈ (proj (W := W) (ℓ := ℓ) k).ker ↔ ∃ g : W.tateModule ℓ, ℓ ^ k • g = f := by
  refine ⟨fun h => exists_nsmul_pow_eq_of_proj_eq_zero (AddMonoidHom.mem_ker.mp h), ?_⟩
  rintro ⟨g, rfl⟩
  exact AddMonoidHom.mem_ker.mpr (proj_nsmul_pow g k)

/-! ## Level surjectivity for a divisible curve -/

/-- The chain of successive `[ℓ]`-preimages of `x`. -/
private noncomputable def chain (hℓ : Function.Surjective fun P : W.Point => ℓ • P)
    (x : W.Point) : ℕ → W.Point
  | 0 => x
  | i + 1 => (hℓ (chain hℓ x i)).choose

private lemma chain_zero (hℓ : Function.Surjective fun P : W.Point => ℓ • P) (x : W.Point) :
    chain hℓ x 0 = x := rfl

private lemma smul_chain_succ (hℓ : Function.Surjective fun P : W.Point => ℓ • P) (x : W.Point)
    (i : ℕ) : ℓ • chain hℓ x (i + 1) = chain hℓ x i :=
  (hℓ (chain hℓ x i)).choose_spec

private lemma smul_pow_chain (hℓ : Function.Surjective fun P : W.Point => ℓ • P) (x : W.Point)
    (i : ℕ) : ℓ ^ i • chain hℓ x i = x := by
  induction i with
  | zero => simp [chain_zero]
  | succ i ih => rw [pow_succ, mul_smul, smul_chain_succ, ih]

/-- **The level projections of the Tate module are surjective** as soon as multiplication by `ℓ` is
surjective on the points of `W`.

Given `x ∈ E[ℓ^k]`, the family `j ↦ ℓ^(k-j) • c (j-k)`, where `c` is a chain of successive
`[ℓ]`-preimages of `x`, is compatible and hits `x` at level `k`: truncated subtraction makes it
`ℓ^(k-j) • x` below level `k` and `c (j-k)` above it. -/
theorem proj_surjective (hℓ : Function.Surjective fun P : W.Point => ℓ • P) (k : ℕ) :
    Function.Surjective (proj (W := W) (ℓ := ℓ) k) := by
  rintro ⟨x, hx⟩
  have hxk : ℓ ^ k • x = 0 := mem_torsion_iff.mp hx
  refine ⟨⟨fun j => ℓ ^ (k - j) • chain hℓ x (j - k), ⟨fun j => ?_, fun j => ?_⟩⟩, ?_⟩
  · rw [mem_torsion_iff]
    change ℓ ^ j • (ℓ ^ (k - j) • chain hℓ x (j - k)) = 0
    rcases le_or_gt k j with h | h
    · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
      simp only [Nat.sub_eq_zero_of_le (Nat.le_add_right k d), Nat.add_sub_cancel_left, pow_zero,
        one_smul, pow_add, mul_smul, smul_pow_chain, hxk]
    · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h.le
      simp only [Nat.sub_eq_zero_of_le (Nat.le_add_right j d), Nat.add_sub_cancel_left, chain_zero,
        smul_smul, ← pow_add, hxk]
  · change ℓ • (ℓ ^ (k - (j + 1)) • chain hℓ x (j + 1 - k)) = ℓ ^ (k - j) • chain hℓ x (j - k)
    rcases le_or_gt k j with h | h
    · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
      simp only [Nat.sub_eq_zero_of_le (by omega : k ≤ k + d + 1),
        Nat.sub_eq_zero_of_le (Nat.le_add_right k d), pow_zero, one_smul,
        show k + d + 1 - k = d + 1 by omega, Nat.add_sub_cancel_left, smul_chain_succ]
    · obtain ⟨e, rfl⟩ := Nat.exists_eq_add_of_le h
      rw [show j + 1 + e - (j + 1) = e by omega, show j + 1 - (j + 1 + e) = 0 by omega,
        show j + 1 + e - j = e + 1 by omega, show j - (j + 1 + e) = 0 by omega, chain_zero,
        smul_smul, ← pow_succ']
  · refine Subtype.ext ?_
    change ℓ ^ (k - k) • chain hℓ x (k - k) = x
    simp [chain_zero]

/-- **Every level value is attained by a compatible family.** The unbundled form of
`proj_surjective`: if `[ℓ]` is surjective on `W.Point` then for every `x ∈ E[ℓ^k]` there is a
compatible family in `T_ℓ E` whose level-`k` value is literally `x`.

This says nothing new — it is `proj_surjective` with the `Subtype` packaging peeled off — but a
consumer that wants the *family* rather than an element of the subgroup would otherwise have to
re-derive the coercion each time. -/
lemma exists_mem_tateModule_apply_eq (hℓ : Function.Surjective fun P : W.Point => ℓ • P) (k : ℕ)
    {x : W.Point} (hx : x ∈ W.torsion (ℓ ^ k)) :
    ∃ f ∈ W.tateModule ℓ, f k = x := by
  obtain ⟨f, hf⟩ := proj_surjective hℓ k ⟨x, hx⟩
  exact ⟨(f : ℕ → W.Point), f.2, congrArg Subtype.val hf⟩

/-- **Level surjectivity forces divisibility.** If `proj k` is surjective then every point of
`E[ℓ^k]` is `ℓ^m`-divisible in `E`, for every `m`. This is the converse content of
`proj_surjective` and certifies that its hypothesis is load-bearing: the conclusion is not a formal
property of the inverse limit but a genuine divisibility statement about `W`. -/
lemma exists_nsmul_pow_eq_of_proj_surjective {k : ℕ}
    (h : Function.Surjective (proj (W := W) (ℓ := ℓ) k)) (m : ℕ) {x : W.Point}
    (hx : x ∈ W.torsion (ℓ ^ k)) : ∃ y : W.Point, ℓ ^ m • y = x := by
  obtain ⟨f, hf⟩ := h ⟨x, hx⟩
  exact ⟨(f : ℕ → W.Point) (k + m), (smul_pow_coe f k m).trans (congrArg Subtype.val hf)⟩

/-- **`T_ℓ E / ℓ^k T_ℓ E ≃+ E[ℓ^k]`**: the level-`k` projection identifies the quotient of the Tate
module by its `ℓ^k`-multiples with the `ℓ^k`-torsion. The kernel really is `ℓ^k · T_ℓ E` by
`mem_ker_proj_iff`.

⚠️ **This declaration is unsuffixed and was stated at `ℓ = 2`; it is generalised in place, with no
`…Two` or `…Three` twin, because a second `WeierstrassCurve.Affine.tateModule.quotientProjEquiv`
would be a name collision rather than a duplication.** It carried `(h2 : (2 : F) ≠ 0)`,
`[IsAlgClosed F]` and `[W.IsElliptic]`, and needed none of the three: the proof is
`QuotientAddGroup.quotientKerEquivOfSurjective`, which knows nothing about the prime, and the only
`ℓ = 2`-specific input was the surjectivity witness. It now takes that witness directly, in the
shape `proj_surjective` already uses, so at `ℓ = 2` read it as
`quotientProjEquiv (nsmul_two_surjective h2) k` and at `ℓ = 3` as
`quotientProjEquiv (nsmul_three_surjective h2) k`. ⚠️ *The generalisation was free here, but
"unsuffixed" answers only whether a twin is legal — it does not say the statement is already
generic, and this one was hardcoded at `2` in three places.* -/
noncomputable def quotientProjEquiv (hℓ : Function.Surjective fun P : W.Point => ℓ • P) (k : ℕ) :
    (W.tateModule ℓ ⧸ (proj (W := W) (ℓ := ℓ) k).ker) ≃+ W.torsion (ℓ ^ k) :=
  QuotientAddGroup.quotientKerEquivOfSurjective _ (proj_surjective hℓ k)

/-! ## Non-vacuity from a levelwise count -/

/-- **`T_ℓE` is infinite** as soon as the level projections are surjective and the levels grow:
were `T_ℓE` finite with `N` elements it would surject onto `E[ℓ^N]`, which has `ℓ^N · ℓ^N > N`
elements.

The cardinality is taken as a hypothesis in the form `#E[ℓ^k] = ℓ^k · ℓ^k`, which is the shape the
`ℓ`-primary counting theorems are consumed in throughout this development
(`EllipticCurves.Torsion.PrimaryBasis.torsionPairHom_bijective_of_card`). -/
theorem infinite_tateModule_of_card (hℓ : 1 < ℓ)
    (hproj : ∀ k, Function.Surjective (proj (W := W) (ℓ := ℓ) k))
    (hcard : ∀ k, Nat.card (W.torsion (ℓ ^ k)) = ℓ ^ k * ℓ ^ k) :
    Infinite (W.tateModule ℓ) := by
  rw [← not_finite_iff_infinite]
  intro hfin
  set N := Nat.card (W.tateModule ℓ) with hN
  have hle : Nat.card (W.torsion (ℓ ^ N)) ≤ N := Nat.card_le_card_of_surjective _ (hproj N)
  rw [hcard N] at hle
  have hlt : N < ℓ ^ N := Nat.lt_pow_self hℓ
  have hmul : ℓ ^ N ≤ ℓ ^ N * ℓ ^ N := Nat.le_mul_of_pos_left _ (pow_pos (by omega) N)
  omega

/-- **`T_ℓE` is nontrivial**, i.e. it is not the zero module, under the hypotheses of
`infinite_tateModule_of_card`.

Weaker than `infinite_tateModule_of_card`, but this is the form a consumer usually wants: every
statement in `EllipticCurves.TateModule.Basic` holds vacuously for the zero module, so citing
`Nontrivial` is what certifies that the Tate module constructed there has content. -/
theorem nontrivial_tateModule_of_card (hℓ : 1 < ℓ)
    (hproj : ∀ k, Function.Surjective (proj (W := W) (ℓ := ℓ) k))
    (hcard : ∀ k, Nat.card (W.torsion (ℓ ^ k)) = ℓ ^ k * ℓ ^ k) :
    Nontrivial (W.tateModule ℓ) :=
  haveI := infinite_tateModule_of_card hℓ hproj hcard
  inferInstance

/-! ## The `ℓ = 2` instance -/

section Two

variable [IsAlgClosed F] [W.IsElliptic]

/-- **`proj k : T_2 E →+ E[2^k]` is surjective** over an algebraically closed field of
characteristic `≠ 2`, because multiplication by `2` is surjective on `E(F̄)`. -/
theorem proj_two_surjective (h2 : (2 : F) ≠ 0) (k : ℕ) :
    Function.Surjective (proj (W := W) (ℓ := 2) k) :=
  proj_surjective (nsmul_two_surjective h2) k

/-- **`T_2 E` is infinite.** It surjects onto `E[2^k]`, which has `4^k` elements, for every `k`. -/
theorem infinite_tateModule_two (h2 : (2 : F) ≠ 0) : Infinite (W.tateModule 2) :=
  infinite_tateModule_of_card (by norm_num) (proj_two_surjective h2)
    (card_torsion_two_pow_mul_self h2)

/-- **`T_2 E` is nontrivial**, i.e. it is not the zero module.

Weaker than `infinite_tateModule_two`, but this is the form a consumer usually wants: every
statement in `EllipticCurves.TateModule.Basic` holds vacuously for the zero module, so citing
`Nontrivial` is what certifies that the Tate module constructed there has content. -/
theorem nontrivial_tateModule_two (h2 : (2 : F) ≠ 0) : Nontrivial (W.tateModule 2) :=
  nontrivial_tateModule_of_card (by norm_num) (proj_two_surjective h2)
    (card_torsion_two_pow_mul_self h2)

/-- **`T_2 E` has a nonzero element.** The unbundled form of `nontrivial_tateModule_two`. -/
theorem exists_ne_zero_tateModule_two (h2 : (2 : F) ≠ 0) : ∃ f : W.tateModule 2, f ≠ 0 :=
  haveI := nontrivial_tateModule_two (W := W) h2
  exists_ne 0

/-! ⚠️ **`T_2 E / 2^k T_2 E ≃+ E[2^k]` is no longer stated here and has no `…Two` name.** It used
to be `quotientProjEquiv (h2 : (2 : F) ≠ 0) (k : ℕ)`, in this section; that declaration was
unsuffixed, so it was generalised in place rather than twinned and now lives above, taking the
surjectivity witness directly. -/

/-- ⚠️ **Nothing was lost at `ℓ = 2` when `quotientProjEquiv` was generalised**: its old conclusion
is still derivable here, verbatim, by feeding it `nsmul_two_surjective`. Recorded as an `example`
rather than as prose because *the build cannot otherwise tell a namespace-preserving generalisation
from a silent deletion* — both are green, and both leave every existing consumer working, there
being none. -/
noncomputable example (h2 : (2 : F) ≠ 0) (k : ℕ) :
    (W.tateModule 2 ⧸ (proj (W := W) (ℓ := 2) k).ker) ≃+ W.torsion (2 ^ k) :=
  quotientProjEquiv (nsmul_two_surjective h2) k

end Two

end tateModule

end WeierstrassCurve.Affine
