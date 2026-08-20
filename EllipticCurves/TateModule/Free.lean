/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import EllipticCurves.TateModule.LevelStructure
import EllipticCurves.TateModule.PadicInverseLimit
import EllipticCurves.Torsion.TwoPrimaryBasis

/-!
# `T₂E ≅ ℤ₂²` : the Tate module at `ℓ = 2` is free of rank two

For an elliptic curve `W` over an algebraically closed field `F` with `(2 : F) ≠ 0`, the `2`-adic
Tate module `T₂E = lim_k E[2^k]` is a free `ℤ_[2]`-module of rank `2` (Silverman, *AEC*, III.7.1
and Remark 7.1.2):

```
Nonempty (W.tateModule 2 ≃ₗ[ℤ_[2]] ℤ_[2] × ℤ_[2])
Module.Free ℤ_[2] (W.tateModule 2)          Module.finrank ℤ_[2] (W.tateModule 2) = 2
```

This is the `ℓ = 2` case of the general statement `T_ℓE ≅ ℤ_ℓ²` for `ℓ ≠ char F`, and the first
structural description of any Tate module in this development. Nothing here uses Ward's theorem,
the elliptic-net recurrence, or the multiplication-by-`n` coordinate formula `x(nP) = Φₙ/ΨSqₙ`: at
`ℓ = 2` the whole `2`-primary tower is available from surjectivity of `[2]` on `E(F̄)` alone.

## The construction

Fix a system of generating pairs `P k, Q k` of `E[2^k]` that is *coherent* for the transition maps,
i.e. `2 • P (k+1) = P k` and `2 • Q (k+1) = Q k`
(`EllipticCurves.Torsion.TwoPrimaryBasis.exists_compatible_basis`). Coherence is essential and is
not supplied by the structure theorem: `E[2^k] ≃+ (ZMod (2^k))²` holds at each level
*independently*, and a family of unrelated isomorphisms says nothing about an inverse limit. The
map is

```
Φ : ℤ_[2] × ℤ_[2] → (ℕ → W.Point),
Φ (a, b) k = (PadicInt.toZModPow k a).val • P k + (PadicInt.toZModPow k b).val • Q k,
```

matching the `ℤ_[2]`-action on `T₂E` from `EllipticCurves.TateModule.Basic`, where `a` acts on
level `k` through its residue `toZModPow k a`.

* **`Φ` lands in `T₂E`** (`padicPairFamily_mem`). Level membership is `AddSubgroup.nsmul_mem`.
  Compatibility is the one real computation: `2 • Φ (a, b) (k+1)` moves the `2` past the residue
  coefficients onto `P (k+1)`, `Q (k+1)`, where coherence turns it into `P k`, `Q k`; the
  coefficients are then reduced from level `k+1` to level `k`, which is legitimate because `P k`
  and `Q k` are killed by `2^k`.
* **`Φ` is `ℤ_[2]`-linear** (`padicPairHom`). Both `map_add` and `map_smul` reduce to the statement
  that natural numbers with the same residue mod `2^k` act identically on `E[2^k]`, applied to
  `map_add` / `map_mul` of `toZModPow k`.
* **`Φ` is injective** (`padicPairHom_injective`). If `Φ (a, b) = 0` then at every level
  `(toZModPow k a).val • P k + (toZModPow k b).val • Q k = 0`, so `toZModPow k a = 0` and
  `toZModPow k b = 0` by uniqueness of coefficients (`zmod_pair_eq_zero_iff`, the injectivity half
  of the levelwise basis property), whence `a = b = 0` by `PadicInt.ext_of_toZModPow`.
* **`Φ` is surjective** (`padicPairHom_surjective`). Write each `f k` as
  `(α k).val • P k + (β k).val • Q k`, possible by the surjectivity half
  (`exists_zmod_pair_eq`). The sequences `α, β` are *compatible*: applying `2 • −` to level `k+1`
  and using coherence rewrites `f k` with the level-`(k+1)` coefficients reduced mod `2^k`, and
  uniqueness at level `k` forces `ZMod.castHom … (α (k+1)) = α k`. So `α, β` lie in
  `PadicInt.compatSeq 2` and `PadicInt.compatSeqEquiv` converts them back into `2`-adic integers.

The last step is exactly what `EllipticCurves.TateModule.PadicInverseLimit` was built for:
`ℤ_[2] = lim_k ZMod (2^k)` as an explicit equivalence rather than only a universal property.

## Non-vacuity

`Module.Free` and `finrank = 2` would both be *false* for the zero module, so they cannot be
satisfied vacuously; independently, `nontrivial_tateModule_two` records `Nontrivial (T₂E)` by a
route that does not mention the equivalence at all (it comes from `infinite_tateModule_two`, i.e.
from `T₂E` surjecting onto groups of order `4^k`).

## Scope

Odd `ℓ` is **not** covered: the tower rests on surjectivity of `[2]`, and `[ℓ]`-surjectivity for
odd `ℓ` still needs `x(ℓP) = Φ_ℓ/ΨSq_ℓ`. The Galois action on `T₂E`
(`EllipticCurves.TateModule.GaloisAction`) and the representation `ρ_{E,2} : G_F → GL₂(ℤ_2)` are a
separate follow-up, which the rank statement here makes meaningful for the first time.

## Main statements

* `WeierstrassCurve.Affine.tateModule.padicPairEquiv`: the equivalence
  `ℤ_[2] × ℤ_[2] ≃ₗ[ℤ_[2]] T₂E` attached to a coherent system of generating pairs.
* `WeierstrassCurve.Affine.tateModule.padicPairEquiv_apply_coe`: its levelwise formula.
* `WeierstrassCurve.Affine.tateModule.nonempty_tateModuleEquivProd`:
  `Nonempty (T₂E ≃ₗ[ℤ_[2]] ℤ_[2] × ℤ_[2])`.
* `WeierstrassCurve.Affine.tateModule.free_tateModule_two`: `Module.Free ℤ_[2] T₂E`.
* `WeierstrassCurve.Affine.tateModule.finrank_tateModule_two`: `finrank ℤ_[2] T₂E = 2`.
* `WeierstrassCurve.Affine.tateModule.nontrivial_tateModule_two`: `Nontrivial T₂E`.

## References

* [J. H. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.7.1 and Remark 7.1.2.
-/

open scoped AddSubgroup

open PadicInt

namespace WeierstrassCurve.Affine

namespace tateModule

variable {F : Type*} [Field F] [DecidableEq F] {W : Affine F}

/-! ### Reducing a `ℓ`-adic residue from one level to a lower one -/

section Residues

variable {ℓ : ℕ} [Fact ℓ.Prime]

/-- The residues of a `ℓ`-adic integer at two levels agree after reduction to the lower one.

`EllipticCurves.TateModule.Basic` proves the `n = m + 1` case as a `private` lemma
(`toZModPow_val_modEq`) for its own use; `private` does not cross file boundaries, so the general
statement is proved here rather than by editing that file. -/
private lemma toZModPow_val_natCast_eq (a : ℤ_[ℓ]) {m n : ℕ} (h : m ≤ n) :
    (((toZModPow n a).val : ℕ) : ZMod (ℓ ^ m)) = (((toZModPow m a).val : ℕ) : ZMod (ℓ ^ m)) := by
  haveI : NeZero (ℓ ^ n) := ⟨(pow_pos (Fact.out : ℓ.Prime).pos n).ne'⟩
  haveI : NeZero (ℓ ^ m) := ⟨(pow_pos (Fact.out : ℓ.Prime).pos m).ne'⟩
  rw [ZMod.natCast_val, ZMod.natCast_val, ZMod.cast_id, cast_toZModPow m n h]

end Residues

/-! ### The map `Φ (a, b) k = (toZModPow k a).val • P k + (toZModPow k b).val • Q k` -/

section Basis

variable [IsAlgClosed F] [W.IsElliptic]

/-- The compatible family attached to a pair of `2`-adic integers and a coherent system of
generating pairs: at level `k` the residues of `a` and `b` modulo `2^k` are used as coefficients
on `P k` and `Q k`. -/
noncomputable def padicPairFamily (P Q : ℕ → W.Point) (ab : ℤ_[2] × ℤ_[2]) : ℕ → W.Point := fun k =>
  (toZModPow k ab.1).val • P k + (toZModPow k ab.2).val • Q k

variable {P Q : ℕ → W.Point}

omit [IsAlgClosed F] [W.IsElliptic] in
private lemma mem_torsion_fst
    (hgen : ∀ k, AddSubgroup.closure ({P k, Q k} : Set W.Point) = W.torsion (2 ^ k)) (k : ℕ) :
    P k ∈ W.torsion (2 ^ k) := by
  have hmem : P k ∈ ({P k, Q k} : Set W.Point) := Set.mem_insert _ _
  rw [← hgen k]
  exact AddSubgroup.subset_closure hmem

omit [IsAlgClosed F] [W.IsElliptic] in
private lemma mem_torsion_snd
    (hgen : ∀ k, AddSubgroup.closure ({P k, Q k} : Set W.Point) = W.torsion (2 ^ k)) (k : ℕ) :
    Q k ∈ W.torsion (2 ^ k) := by
  have hmem : Q k ∈ ({P k, Q k} : Set W.Point) := Set.mem_insert_of_mem _ rfl
  rw [← hgen k]
  exact AddSubgroup.subset_closure hmem

omit [IsAlgClosed F] [W.IsElliptic] in
/-- `Φ (a, b)` is a compatible family, i.e. an element of `T₂E`. Coherence of the system
(`2 • P (k+1) = P k`) is what makes the level-`(k+1)` value descend to the level-`k` one. -/
lemma padicPairFamily_mem
    (hgen : ∀ k, AddSubgroup.closure ({P k, Q k} : Set W.Point) = W.torsion (2 ^ k))
    (hP : ∀ k, 2 • P (k + 1) = P k) (hQ : ∀ k, 2 • Q (k + 1) = Q k) (ab : ℤ_[2] × ℤ_[2]) :
    padicPairFamily P Q ab ∈ W.tateModule 2 := by
  refine ⟨fun k => AddSubgroup.add_mem _
    (AddSubgroup.nsmul_mem _ (mem_torsion_fst hgen k) _)
    (AddSubgroup.nsmul_mem _ (mem_torsion_snd hgen k) _), fun k => ?_⟩
  change 2 • ((toZModPow (k + 1) ab.1).val • P (k + 1) + (toZModPow (k + 1) ab.2).val • Q (k + 1))
      = (toZModPow k ab.1).val • P k + (toZModPow k ab.2).val • Q k
  rw [smul_add, smul_comm 2 (toZModPow (k + 1) ab.1).val,
    smul_comm 2 (toZModPow (k + 1) ab.2).val, hP k, hQ k,
    nsmul_eq_of_natCast_eq (ℓ := 2) (mem_torsion_fst hgen k)
      (toZModPow_val_natCast_eq ab.1 k.le_succ),
    nsmul_eq_of_natCast_eq (ℓ := 2) (mem_torsion_snd hgen k)
      (toZModPow_val_natCast_eq ab.2 k.le_succ)]

omit [IsAlgClosed F] [W.IsElliptic] in
/-- **The `ℤ_[2]`-linear map `ℤ_[2] × ℤ_[2] →ₗ[ℤ_[2]] T₂E`** attached to a coherent system of
generating pairs. -/
noncomputable def padicPairHom
    (hgen : ∀ k, AddSubgroup.closure ({P k, Q k} : Set W.Point) = W.torsion (2 ^ k))
    (hP : ∀ k, 2 • P (k + 1) = P k) (hQ : ∀ k, 2 • Q (k + 1) = Q k) :
    ℤ_[2] × ℤ_[2] →ₗ[ℤ_[2]] W.tateModule 2 where
  toFun ab := ⟨padicPairFamily P Q ab, padicPairFamily_mem hgen hP hQ ab⟩
  map_add' ab cd := by
    refine tateModule.ext fun k => ?_
    change (toZModPow k (ab.1 + cd.1)).val • P k + (toZModPow k (ab.2 + cd.2)).val • Q k
        = ((toZModPow k ab.1).val • P k + (toZModPow k ab.2).val • Q k)
          + ((toZModPow k cd.1).val • P k + (toZModPow k cd.2).val • Q k)
    rw [nsmul_eq_of_natCast_eq (ℓ := 2) (mem_torsion_fst hgen k)
        (t := (toZModPow k ab.1).val + (toZModPow k cd.1).val)
        (by push_cast [ZMod.natCast_val, ZMod.cast_id, map_add]; ring),
      nsmul_eq_of_natCast_eq (ℓ := 2) (mem_torsion_snd hgen k)
        (t := (toZModPow k ab.2).val + (toZModPow k cd.2).val)
        (by push_cast [ZMod.natCast_val, ZMod.cast_id, map_add]; ring),
      add_nsmul, add_nsmul]
    abel
  map_smul' c ab := by
    refine tateModule.ext fun k => ?_
    rw [smul_coe]
    change (toZModPow k (c * ab.1)).val • P k + (toZModPow k (c * ab.2)).val • Q k
        = (toZModPow k c).val • ((toZModPow k ab.1).val • P k + (toZModPow k ab.2).val • Q k)
    rw [smul_add, smul_smul, smul_smul,
      nsmul_eq_of_natCast_eq (ℓ := 2) (mem_torsion_fst hgen k)
        (t := (toZModPow k c).val * (toZModPow k ab.1).val)
        (by push_cast [ZMod.natCast_val, ZMod.cast_id, map_mul]; ring),
      nsmul_eq_of_natCast_eq (ℓ := 2) (mem_torsion_snd hgen k)
        (t := (toZModPow k c).val * (toZModPow k ab.2).val)
        (by push_cast [ZMod.natCast_val, ZMod.cast_id, map_mul]; ring)]

omit [IsAlgClosed F] [W.IsElliptic] in
@[simp]
lemma padicPairHom_apply_coe
    (hgen : ∀ k, AddSubgroup.closure ({P k, Q k} : Set W.Point) = W.torsion (2 ^ k))
    (hP : ∀ k, 2 • P (k + 1) = P k) (hQ : ∀ k, 2 • Q (k + 1) = Q k) (ab : ℤ_[2] × ℤ_[2])
    (k : ℕ) :
    ((padicPairHom hgen hP hQ ab : W.tateModule 2) : ℕ → W.Point) k
      = (toZModPow k ab.1).val • P k + (toZModPow k ab.2).val • Q k := rfl

/-! ### Injectivity and surjectivity -/

/-- **`Φ` is injective.** Uniqueness of the coefficients at every level forces all residues of `a`
and `b` to vanish, and a `2`-adic integer is determined by its residues. -/
theorem padicPairHom_injective (h2 : (2 : F) ≠ 0)
    (hgen : ∀ k, AddSubgroup.closure ({P k, Q k} : Set W.Point) = W.torsion (2 ^ k))
    (hP : ∀ k, 2 • P (k + 1) = P k) (hQ : ∀ k, 2 • Q (k + 1) = Q k) :
    Function.Injective (padicPairHom hgen hP hQ) := by
  refine (injective_iff_map_eq_zero _).mpr fun ab hab => ?_
  have hlev : ∀ k, toZModPow k ab.1 = 0 ∧ toZModPow k ab.2 = 0 := by
    intro k
    refine (zmod_pair_eq_zero_iff h2 (hgen k)).mp ?_
    have := congrArg (fun f : W.tateModule 2 => (f : ℕ → W.Point) k) hab
    simpa [padicPairHom, padicPairFamily] using this
  refine Prod.ext ?_ ?_
  · exact ext_of_toZModPow.mp fun n => by rw [(hlev n).1]; simp
  · exact ext_of_toZModPow.mp fun n => by rw [(hlev n).2]; simp

/-- **`Φ` is surjective.** The levelwise coefficient pairs of a compatible family are themselves a
compatible sequence, so they come from a pair of `2`-adic integers via
`PadicInt.compatSeqEquiv`. -/
theorem padicPairHom_surjective (h2 : (2 : F) ≠ 0)
    (hgen : ∀ k, AddSubgroup.closure ({P k, Q k} : Set W.Point) = W.torsion (2 ^ k))
    (hP : ∀ k, 2 • P (k + 1) = P k) (hQ : ∀ k, 2 • Q (k + 1) = Q k) :
    Function.Surjective (padicPairHom hgen hP hQ) := by
  intro f
  choose α β hαβ using fun k => exists_zmod_pair_eq (hgen k) (f.2.1 k)
  -- The level-`(k+1)` coefficients, reduced mod `2^k`, also describe `f k`; uniqueness at level
  -- `k` then identifies them with the level-`k` coefficients.
  have hcompat : ∀ k, (ZMod.castHom (pow_dvd_pow 2 k.le_succ) (ZMod (2 ^ k)) (α (k + 1)) = α k)
      ∧ ZMod.castHom (pow_dvd_pow 2 k.le_succ) (ZMod (2 ^ k)) (β (k + 1)) = β k := by
    intro k
    have hstep : (α (k + 1)).val • P k + (β (k + 1)).val • Q k = (f : ℕ → W.Point) k := by
      rw [← smul_coe_succ f k, ← hαβ (k + 1), smul_add,
        smul_comm 2 (α (k + 1)).val, smul_comm 2 (β (k + 1)).val, hP k, hQ k]
    have hred : ∀ {x : W.Point} (_ : x ∈ W.torsion (2 ^ k)) (a : ZMod (2 ^ (k + 1))),
        a.val • x = (ZMod.castHom (pow_dvd_pow 2 k.le_succ) (ZMod (2 ^ k)) a).val • x := by
      intro x hx a
      refine nsmul_eq_of_natCast_eq (ℓ := 2) hx ?_
      rw [ZMod.natCast_val, ZMod.natCast_val, ZMod.cast_id, ZMod.castHom_apply]
    rw [hred (mem_torsion_fst hgen k) (α (k + 1)), hred (mem_torsion_snd hgen k) (β (k + 1))]
      at hstep
    have hfk : (ZMod.castHom (pow_dvd_pow 2 k.le_succ) (ZMod (2 ^ k)) (α (k + 1)),
        ZMod.castHom (pow_dvd_pow 2 k.le_succ) (ZMod (2 ^ k)) (β (k + 1))) = (α k, β k) := by
      refine (torsionPairHom_bijective h2 (hgen k)).1 (Subtype.ext ?_)
      rw [torsionPairHom_apply_coe, torsionPairHom_apply_coe, hstep, hαβ k]
    exact ⟨congrArg Prod.fst hfk, congrArg Prod.snd hfk⟩
  have hαmem : α ∈ compatSeq 2 := fun k => (hcompat k).1
  have hβmem : β ∈ compatSeq 2 := fun k => (hcompat k).2
  refine ⟨(compatSeqEquiv.symm ⟨α, hαmem⟩, compatSeqEquiv.symm ⟨β, hβmem⟩), tateModule.ext
    fun k => ?_⟩
  rw [padicPairHom_apply_coe]
  simpa using hαβ k

/-! ### The equivalence, freeness and the rank -/

/-- **`T₂E ≅ ℤ₂²`**: the equivalence `ℤ_[2] × ℤ_[2] ≃ₗ[ℤ_[2]] T₂E` attached to a coherent system of
generating pairs of the groups `E[2^k]`. -/
noncomputable def padicPairEquiv (h2 : (2 : F) ≠ 0)
    (hgen : ∀ k, AddSubgroup.closure ({P k, Q k} : Set W.Point) = W.torsion (2 ^ k))
    (hP : ∀ k, 2 • P (k + 1) = P k) (hQ : ∀ k, 2 • Q (k + 1) = Q k) :
    (ℤ_[2] × ℤ_[2]) ≃ₗ[ℤ_[2]] W.tateModule 2 :=
  LinearEquiv.ofBijective _
    ⟨padicPairHom_injective h2 hgen hP hQ, padicPairHom_surjective h2 hgen hP hQ⟩

/-- The level-`k` value of the family attached to `(a, b)`: the residues of `a` and `b` modulo
`2^k` read as coefficients on the level-`k` basis. This is the identity that a later analysis of
the Galois action on `T₂E` will run on. -/
@[simp]
lemma padicPairEquiv_apply_coe (h2 : (2 : F) ≠ 0)
    (hgen : ∀ k, AddSubgroup.closure ({P k, Q k} : Set W.Point) = W.torsion (2 ^ k))
    (hP : ∀ k, 2 • P (k + 1) = P k) (hQ : ∀ k, 2 • Q (k + 1) = Q k) (ab : ℤ_[2] × ℤ_[2])
    (k : ℕ) :
    ((padicPairEquiv h2 hgen hP hQ ab : W.tateModule 2) : ℕ → W.Point) k
      = (toZModPow k ab.1).val • P k + (toZModPow k ab.2).val • Q k := rfl

end Basis

section Structure

variable [IsAlgClosed F] [W.IsElliptic]

/-- **The Tate module at `ℓ = 2` is `ℤ_[2]`-linearly isomorphic to `ℤ_[2] × ℤ_[2]`.** The
isomorphism depends on a choice of coherent system of generating pairs, so it is stated as a
`Nonempty`; the choice-free consequences are `free_tateModule_two` and
`finrank_tateModule_two`. -/
theorem nonempty_tateModuleEquivProd (h2 : (2 : F) ≠ 0) :
    Nonempty (W.tateModule 2 ≃ₗ[ℤ_[2]] ℤ_[2] × ℤ_[2]) := by
  obtain ⟨P, Q, hgen, hP, hQ⟩ := exists_compatible_basis (W := W) h2
  exact ⟨(padicPairEquiv h2 hgen hP hQ).symm⟩

/-- **`T₂E` is a free `ℤ_[2]`-module** (Silverman, *AEC*, III.7.1 at `ℓ = 2`). -/
theorem free_tateModule_two (h2 : (2 : F) ≠ 0) : Module.Free ℤ_[2] (W.tateModule 2) := by
  obtain ⟨e⟩ := nonempty_tateModuleEquivProd (W := W) h2
  exact Module.Free.of_equiv e.symm

/-- **`T₂E` has rank two over `ℤ_[2]`.** -/
theorem finrank_tateModule_two (h2 : (2 : F) ≠ 0) :
    Module.finrank ℤ_[2] (W.tateModule 2) = 2 := by
  obtain ⟨e⟩ := nonempty_tateModuleEquivProd (W := W) h2
  rw [e.finrank_eq, Module.finrank_prod, Module.finrank_self]

/-- **`T₂E` is nontrivial**, by a route independent of the equivalence above: it surjects onto
`E[2^k]`, which has `4^k` elements. Together with `free_tateModule_two` this rules out the
degenerate reading of the rank statement. -/
theorem nontrivial_tateModule_two (h2 : (2 : F) ≠ 0) : Nontrivial (W.tateModule 2) :=
  haveI := infinite_tateModule_two (W := W) h2
  inferInstance

end Structure

end tateModule

end WeierstrassCurve.Affine
