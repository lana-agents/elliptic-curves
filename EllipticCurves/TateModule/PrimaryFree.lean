/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import EllipticCurves.TateModule.LevelStructure
import EllipticCurves.TateModule.PadicInverseLimit
import EllipticCurves.Torsion.PrimaryBasis

/-!
# `T_ℓE ≅ ℤ_ℓ²` from a coherent system of generating pairs, for a general `ℓ`

For an elliptic curve `W` over a field and a prime `ℓ`, this file turns a *coherent system of
generating pairs* of the groups `E[ℓ^k]` into an explicit `ℤ_[ℓ]`-linear isomorphism

```
ℤ_[ℓ] × ℤ_[ℓ] ≃ₗ[ℤ_[ℓ]] T_ℓE = lim_k E[ℓ^k]
```

and deduces `Module.Free`, `finrank = 2` and `Module.Finite` (Silverman, *AEC*, III.7.1 and
Remark 7.1.2).

Nothing here is specific to a prime: the file takes as **hypotheses** exactly the two prime-specific
facts the argument consumes, and proves nothing about either.

* `hbasis` — a coherent system exists, i.e.
  `∀ k, closure {P k, Q k} = E[ℓ^k]`, `∀ k, ℓ • P (k+1) = P k`, `∀ k, ℓ • Q (k+1) = Q k`. This is
  what `EllipticCurves.Torsion.PrimaryBasis.exists_compatible_basis_of_surjective` produces from
  `[ℓ]`-surjectivity, and it is the input a levelwise structure theorem does **not** give:
  `E[ℓ^k] ≃+ (ZMod (ℓ^k))²` holds at each level *independently*, and a family of unrelated
  isomorphisms says nothing about an inverse limit.
* `hcard` — `#E[ℓ^k] = ℓ^k · ℓ^k`. **Two** declarations below use it, and they are the two halves
  of bijectivity: `padicPairHom_injective`, through
  `EllipticCurves.Torsion.PrimaryBasis.zmod_pair_eq_zero_iff_of_card`, and
  `padicPairHom_surjective`, through
  `EllipticCurves.Torsion.PrimaryBasis.torsionPairHom_bijective_of_card`, which is what identifies
  the level-`(k+1)` coefficients with the level-`k` ones. Everything from `padicPairEquiv` onwards
  only *passes it on* to those two, and `padicPairFamily`, `padicPairFamily_mem`, `padicPairHom`
  and `padicPairHom_apply_coe` do not take it at all: those are `hbasis` alone.
⚠️ **There used to be a third input, `hfin`, and it is gone from every declaration in this file.**
This list used to open *"`hcard` and `hfin` — `#E[ℓ^k] = ℓ^k · ℓ^k`, and that group is finite.
**Two** declarations below actually use them, and they are the two halves of bijectivity"*. The
`hcard` half of that is still exactly right; the `hfin` half was true of the text and false of the
mathematics.

`EllipticCurves.Torsion.PrimaryBasis.torsionPairHom_bijective_of_card` carried
`[Finite ↥(W.torsion n)]`, and that instance occurred in neither the remainder of its type nor its
proof term: `Nat.bijective_iff_surjective_and_card` asks for the **domain** to be finite, and the
domain is `ZMod n × ZMod n`, which `[NeZero n]` already makes finite. The finiteness of `E[n]` was
never used — there, or in the three declarations of that file which only pass it on
(`torsionPairEquivOfCard`, `zmod_pair_eq_zero_iff_of_card`,
`ne_zero_and_ne_of_closure_pair_of_card`). Deleting it (`#1272`) left `padicPairHom_injective` and
`padicPairHom_surjective` each with one `haveI := hfin k` that elaborated away, and the `hfin`
argument then unwound through `padicPairEquiv` to the four `Structure` results below.

⚠️ **So `T_ℓE` is free of rank two on `hbasis` and `hcard` alone**, and a consumer no longer has to
produce `∀ k, Finite (E[ℓ^k])` — which `EllipticCurves.TateModule.Free` and
`EllipticCurves.TateModule.FreeThree` were each supplying, and no longer do.

⚠️ **Taking the prime-specific inputs as hypotheses is this development's established idiom** for
exactly this situation: `EllipticCurves.TateModule.LevelStructure.proj_surjective` is stated that
way with `proj_two_surjective` its one-line `ℓ = 2` instance, and
`EllipticCurves.Torsion.PrimaryBasis` is the whole `ℓ`-primary basis construction written that way,
with `Torsion/TwoPrimaryBasis.lean` and `Torsion/ThreePrimaryBasis.lean` as lists of
instantiations. `EllipticCurves.TateModule.Free` (at `ℓ = 2`) and
`EllipticCurves.TateModule.FreeThree` (at `ℓ = 3`) are the instantiations of this file.

## The construction

Fix a coherent system `P k, Q k`. The map is

```
Φ : ℤ_[ℓ] × ℤ_[ℓ] → (ℕ → W.Point),
Φ (a, b) k = (PadicInt.toZModPow k a).val • P k + (PadicInt.toZModPow k b).val • Q k,
```

matching the `ℤ_[ℓ]`-action on `T_ℓE` from `EllipticCurves.TateModule.Basic`, where `a` acts on
level `k` through its residue `toZModPow k a`.

* **`Φ` lands in `T_ℓE`** (`padicPairFamily_mem`). Level membership is `AddSubgroup.nsmul_mem`.
  Compatibility is the one real computation: `ℓ • Φ (a, b) (k+1)` moves the `ℓ` past the residue
  coefficients onto `P (k+1)`, `Q (k+1)`, where coherence turns it into `P k`, `Q k`; the
  coefficients are then reduced from level `k+1` to level `k`, which is legitimate because `P k`
  and `Q k` are killed by `ℓ^k`.
* **`Φ` is `ℤ_[ℓ]`-linear** (`padicPairHom`). Both `map_add` and `map_smul` reduce to the statement
  that natural numbers with the same residue mod `ℓ^k` act identically on `E[ℓ^k]`, applied to
  `map_add` / `map_mul` of `toZModPow k`.
* **`Φ` is injective** (`padicPairHom_injective`). If `Φ (a, b) = 0` then at every level
  `(toZModPow k a).val • P k + (toZModPow k b).val • Q k = 0`, so `toZModPow k a = 0` and
  `toZModPow k b = 0` by uniqueness of coefficients (`zmod_pair_eq_zero_iff_of_card`, the
  injectivity half of the levelwise basis property), whence `a = b = 0` by
  `PadicInt.ext_of_toZModPow`.
* **`Φ` is surjective** (`padicPairHom_surjective`). Write each `f k` as
  `(α k).val • P k + (β k).val • Q k`, possible by the surjectivity half
  (`exists_zmod_pair_eq`). The sequences `α, β` are *compatible*: applying `ℓ • −` to level `k+1`
  and using coherence rewrites `f k` with the level-`(k+1)` coefficients reduced mod `ℓ^k`, and
  uniqueness at level `k` forces `ZMod.castHom … (α (k+1)) = α k`. So `α, β` lie in
  `PadicInt.compatSeq ℓ` and `PadicInt.compatSeqEquiv` converts them back into `ℓ`-adic integers.
  ⚠️ That "uniqueness at level `k`" is `torsionPairHom_bijective_of_card`, so this half consumes
  `hcard` too — the cardinality is **not** an injectivity-only price. ⚠️ **This sentence used to
  read** *"so this half consumes `hcard`/`hfin` too — the two hypotheses are **not** an
  injectivity-only price"*. It survives verbatim for `hcard`, which is the clause that was doing
  the work; `hfin` no longer exists in this file at all — see the ⚠️ paragraph after the input list
  above.

The last step is exactly what `EllipticCurves.TateModule.PadicInverseLimit` was built for:
`ℤ_[ℓ] = lim_k ZMod (ℓ^k)` as an explicit equivalence rather than only a universal property.

## Non-vacuity

`Module.Free` and `finrank = 2` would both be *false* for the zero module, so they cannot be
satisfied vacuously. Independently of the equivalence built here,
`EllipticCurves.TateModule.LevelStructure.infinite_tateModule_of_card` gets `Infinite (T_ℓE)` by a
route that never mentions it: `T_ℓE` surjects onto `E[ℓ^k]`, which has `ℓ^k · ℓ^k` elements. That
statement lives there and is imported, not restated.

## Scope

This file proves **no** `[ℓ]`-surjectivity and **no** cardinality of `E[ℓ^k]`; both are hypotheses.
At the time of writing the development discharges them at `ℓ = 2`
(`EllipticCurves.Torsion.DoublingSurjective`, `EllipticCurves.Torsion.TwoPrimary`) and at `ℓ = 3`
(`EllipticCurves.Torsion.TriplingSurjective`, `EllipticCurves.Torsion.ThreePrimary`), and at no
other prime: `[ℓ]`-surjectivity for `ℓ ≥ 5` still needs the general multiplication-by-`n` coordinate
formula `x(ℓP) = Φ_ℓ/ΨSq_ℓ`. ⚠️ Ward's theorem and the elliptic-net recurrence are not used at any
`ℓ`; the coordinate formula is used, but only at `ℓ = 3`, where it is proved.

The Galois action on `T_ℓE` (`EllipticCurves.TateModule.GaloisAction`) and the representation
`ρ_{E,ℓ} : G_F → GL₂(ℤ_ℓ)` are a separate follow-up, which the rank statement here makes meaningful
for the first time.

## Main statements

* `WeierstrassCurve.Affine.tateModule.padicPairHom`: the `ℤ_[ℓ]`-linear map
  `ℤ_[ℓ] × ℤ_[ℓ] →ₗ[ℤ_[ℓ]] T_ℓE` attached to a coherent system, with `…_injective` and
  `…_surjective`.
* `WeierstrassCurve.Affine.tateModule.padicPairEquiv`: the resulting equivalence, and
  `…_apply_coe`, its levelwise formula.
* `WeierstrassCurve.Affine.tateModule.nonempty_tateModuleEquivProd_of_card`,
  `…free_tateModule_of_card`, `…finrank_tateModule_of_card`, `…finite_tateModule_of_card`: the
  choice-free consequences.

## Provenance

The contents of this file were extracted from `EllipticCurves.TateModule.Free`, which proved them
at `ℓ = 2` only. That file's own Scope paragraph said odd `ℓ` was not covered *because the tower
rests on surjectivity of `[2]`*; making `ℓ` a variable and the tower an argument is what lets
`EllipticCurves.TateModule.FreeThree` be a list of instantiations rather than a second copy of a
333-line construction.

## References

* [J. H. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.7.1 and Remark 7.1.2.
-/

open scoped AddSubgroup

open PadicInt

namespace WeierstrassCurve.Affine

namespace tateModule

variable {F : Type*} [Field F] [DecidableEq F] {W : Affine F} {ℓ : ℕ}

/-! ### Reducing a `ℓ`-adic residue from one level to a lower one -/

section Residues

variable [Fact ℓ.Prime]

/-- `ℓ ^ k ≠ 0` for a prime `ℓ`. Restated here because
`EllipticCurves.TateModule.Basic` keeps its copy `private`, and used as a `haveI` rather than
registered as an instance so that nothing downstream changes shape. -/
private lemma neZero_pow (k : ℕ) : NeZero (ℓ ^ k) :=
  ⟨(pow_pos (Fact.out : ℓ.Prime).pos k).ne'⟩

/-- The residues of a `ℓ`-adic integer at two levels agree after reduction to the lower one.

`EllipticCurves.TateModule.Basic` proves the `n = m + 1` case as a `private` lemma
(`toZModPow_val_modEq`) for its own use; `private` does not cross file boundaries, so the general
statement is proved here rather than by editing that file. -/
private lemma toZModPow_val_natCast_eq (a : ℤ_[ℓ]) {m n : ℕ} (h : m ≤ n) :
    (((toZModPow n a).val : ℕ) : ZMod (ℓ ^ m)) = (((toZModPow m a).val : ℕ) : ZMod (ℓ ^ m)) := by
  haveI : NeZero (ℓ ^ n) := neZero_pow n
  haveI : NeZero (ℓ ^ m) := neZero_pow m
  rw [ZMod.natCast_val, ZMod.natCast_val, ZMod.cast_id, cast_toZModPow m n h]

end Residues

/-! ### The map `Φ (a, b) k = (toZModPow k a).val • P k + (toZModPow k b).val • Q k` -/

section Basis

variable [Fact ℓ.Prime]

/-- The compatible family attached to a pair of `ℓ`-adic integers and a coherent system of
generating pairs: at level `k` the residues of `a` and `b` modulo `ℓ^k` are used as coefficients
on `P k` and `Q k`. -/
noncomputable def padicPairFamily (P Q : ℕ → W.Point) (ab : ℤ_[ℓ] × ℤ_[ℓ]) : ℕ → W.Point := fun k =>
  (toZModPow k ab.1).val • P k + (toZModPow k ab.2).val • Q k

variable {P Q : ℕ → W.Point}

omit [Fact ℓ.Prime] in
private lemma mem_torsion_fst
    (hgen : ∀ k, AddSubgroup.closure ({P k, Q k} : Set W.Point) = W.torsion (ℓ ^ k)) (k : ℕ) :
    P k ∈ W.torsion (ℓ ^ k) := by
  have hmem : P k ∈ ({P k, Q k} : Set W.Point) := Set.mem_insert _ _
  rw [← hgen k]
  exact AddSubgroup.subset_closure hmem

omit [Fact ℓ.Prime] in
private lemma mem_torsion_snd
    (hgen : ∀ k, AddSubgroup.closure ({P k, Q k} : Set W.Point) = W.torsion (ℓ ^ k)) (k : ℕ) :
    Q k ∈ W.torsion (ℓ ^ k) := by
  have hmem : Q k ∈ ({P k, Q k} : Set W.Point) := Set.mem_insert_of_mem _ rfl
  rw [← hgen k]
  exact AddSubgroup.subset_closure hmem

/-- `Φ (a, b)` is a compatible family, i.e. an element of `T_ℓE`. Coherence of the system
(`ℓ • P (k+1) = P k`) is what makes the level-`(k+1)` value descend to the level-`k` one. -/
lemma padicPairFamily_mem
    (hgen : ∀ k, AddSubgroup.closure ({P k, Q k} : Set W.Point) = W.torsion (ℓ ^ k))
    (hP : ∀ k, ℓ • P (k + 1) = P k) (hQ : ∀ k, ℓ • Q (k + 1) = Q k) (ab : ℤ_[ℓ] × ℤ_[ℓ]) :
    padicPairFamily P Q ab ∈ W.tateModule ℓ := by
  refine ⟨fun k => AddSubgroup.add_mem _
    (AddSubgroup.nsmul_mem _ (mem_torsion_fst hgen k) _)
    (AddSubgroup.nsmul_mem _ (mem_torsion_snd hgen k) _), fun k => ?_⟩
  change ℓ • ((toZModPow (k + 1) ab.1).val • P (k + 1) + (toZModPow (k + 1) ab.2).val • Q (k + 1))
      = (toZModPow k ab.1).val • P k + (toZModPow k ab.2).val • Q k
  rw [smul_add, smul_comm ℓ (toZModPow (k + 1) ab.1).val,
    smul_comm ℓ (toZModPow (k + 1) ab.2).val, hP k, hQ k,
    nsmul_eq_of_natCast_eq (ℓ := ℓ) (mem_torsion_fst hgen k)
      (toZModPow_val_natCast_eq ab.1 k.le_succ),
    nsmul_eq_of_natCast_eq (ℓ := ℓ) (mem_torsion_snd hgen k)
      (toZModPow_val_natCast_eq ab.2 k.le_succ)]

/-- **The `ℤ_[ℓ]`-linear map `ℤ_[ℓ] × ℤ_[ℓ] →ₗ[ℤ_[ℓ]] T_ℓE`** attached to a coherent system of
generating pairs. -/
noncomputable def padicPairHom
    (hgen : ∀ k, AddSubgroup.closure ({P k, Q k} : Set W.Point) = W.torsion (ℓ ^ k))
    (hP : ∀ k, ℓ • P (k + 1) = P k) (hQ : ∀ k, ℓ • Q (k + 1) = Q k) :
    ℤ_[ℓ] × ℤ_[ℓ] →ₗ[ℤ_[ℓ]] W.tateModule ℓ where
  toFun ab := ⟨padicPairFamily P Q ab, padicPairFamily_mem hgen hP hQ ab⟩
  map_add' ab cd := by
    refine tateModule.ext fun k => ?_
    change (toZModPow k (ab.1 + cd.1)).val • P k + (toZModPow k (ab.2 + cd.2)).val • Q k
        = ((toZModPow k ab.1).val • P k + (toZModPow k ab.2).val • Q k)
          + ((toZModPow k cd.1).val • P k + (toZModPow k cd.2).val • Q k)
    rw [nsmul_eq_of_natCast_eq (ℓ := ℓ) (mem_torsion_fst hgen k)
        (t := (toZModPow k ab.1).val + (toZModPow k cd.1).val)
        (by push_cast [ZMod.natCast_val, ZMod.cast_id, map_add]; ring),
      nsmul_eq_of_natCast_eq (ℓ := ℓ) (mem_torsion_snd hgen k)
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
      nsmul_eq_of_natCast_eq (ℓ := ℓ) (mem_torsion_fst hgen k)
        (t := (toZModPow k c).val * (toZModPow k ab.1).val)
        (by push_cast [ZMod.natCast_val, ZMod.cast_id, map_mul]; ring),
      nsmul_eq_of_natCast_eq (ℓ := ℓ) (mem_torsion_snd hgen k)
        (t := (toZModPow k c).val * (toZModPow k ab.2).val)
        (by push_cast [ZMod.natCast_val, ZMod.cast_id, map_mul]; ring)]

@[simp]
lemma padicPairHom_apply_coe
    (hgen : ∀ k, AddSubgroup.closure ({P k, Q k} : Set W.Point) = W.torsion (ℓ ^ k))
    (hP : ∀ k, ℓ • P (k + 1) = P k) (hQ : ∀ k, ℓ • Q (k + 1) = Q k) (ab : ℤ_[ℓ] × ℤ_[ℓ])
    (k : ℕ) :
    ((padicPairHom hgen hP hQ ab : W.tateModule ℓ) : ℕ → W.Point) k
      = (toZModPow k ab.1).val • P k + (toZModPow k ab.2).val • Q k := rfl

/-! ### Injectivity and surjectivity -/

/-- **`Φ` is injective.** Uniqueness of the coefficients at every level forces all residues of `a`
and `b` to vanish, and a `ℓ`-adic integer is determined by its residues.

⚠️ This is one of the **two** declarations in this file that consume a cardinality — the other is
`padicPairHom_surjective` — and therefore one of the two whose `ℓ = 2` and `ℓ = 3` instances need
the counting theorems `card_torsion_two_pow` and `card_torsion_three_pow`. -/
theorem padicPairHom_injective
    (hcard : ∀ k, Nat.card (W.torsion (ℓ ^ k)) = ℓ ^ k * ℓ ^ k)
    (hgen : ∀ k, AddSubgroup.closure ({P k, Q k} : Set W.Point) = W.torsion (ℓ ^ k))
    (hP : ∀ k, ℓ • P (k + 1) = P k) (hQ : ∀ k, ℓ • Q (k + 1) = Q k) :
    Function.Injective (padicPairHom hgen hP hQ) := by
  refine (injective_iff_map_eq_zero _).mpr fun ab hab => ?_
  have hlev : ∀ k, toZModPow k ab.1 = 0 ∧ toZModPow k ab.2 = 0 := by
    intro k
    haveI : NeZero (ℓ ^ k) := neZero_pow k
    refine (zmod_pair_eq_zero_iff_of_card (hcard k) (hgen k)).mp ?_
    have := congrArg (fun f : W.tateModule ℓ => (f : ℕ → W.Point) k) hab
    simpa [padicPairHom, padicPairFamily] using this
  refine Prod.ext ?_ ?_
  · exact ext_of_toZModPow.mp fun n => by rw [(hlev n).1]; simp
  · exact ext_of_toZModPow.mp fun n => by rw [(hlev n).2]; simp

/-- **`Φ` is surjective.** The levelwise coefficient pairs of a compatible family are themselves a
compatible sequence, so they come from a pair of `ℓ`-adic integers via
`PadicInt.compatSeqEquiv`.

⚠️ This is the second of the two declarations in this file that consume a cardinality: the
compatibility of those pairs is exactly *uniqueness* of the level-`k` coefficients, and uniqueness
is what `torsionPairHom_bijective_of_card` extracts from `hcard`. -/
theorem padicPairHom_surjective
    (hcard : ∀ k, Nat.card (W.torsion (ℓ ^ k)) = ℓ ^ k * ℓ ^ k)
    (hgen : ∀ k, AddSubgroup.closure ({P k, Q k} : Set W.Point) = W.torsion (ℓ ^ k))
    (hP : ∀ k, ℓ • P (k + 1) = P k) (hQ : ∀ k, ℓ • Q (k + 1) = Q k) :
    Function.Surjective (padicPairHom hgen hP hQ) := by
  intro f
  choose α β hαβ using fun k => by
    haveI : NeZero (ℓ ^ k) := neZero_pow k
    exact exists_zmod_pair_eq (hgen k) (f.2.1 k)
  -- The level-`(k+1)` coefficients, reduced mod `ℓ^k`, also describe `f k`; uniqueness at level
  -- `k` then identifies them with the level-`k` coefficients.
  have hcompat : ∀ k, (ZMod.castHom (pow_dvd_pow ℓ k.le_succ) (ZMod (ℓ ^ k)) (α (k + 1)) = α k)
      ∧ ZMod.castHom (pow_dvd_pow ℓ k.le_succ) (ZMod (ℓ ^ k)) (β (k + 1)) = β k := by
    intro k
    haveI : NeZero (ℓ ^ k) := neZero_pow k
    have hstep : (α (k + 1)).val • P k + (β (k + 1)).val • Q k = (f : ℕ → W.Point) k := by
      rw [← smul_coe_succ f k, ← hαβ (k + 1), smul_add,
        smul_comm ℓ (α (k + 1)).val, smul_comm ℓ (β (k + 1)).val, hP k, hQ k]
    have hred : ∀ {x : W.Point} (_ : x ∈ W.torsion (ℓ ^ k)) (a : ZMod (ℓ ^ (k + 1))),
        a.val • x = (ZMod.castHom (pow_dvd_pow ℓ k.le_succ) (ZMod (ℓ ^ k)) a).val • x := by
      intro x hx a
      haveI : NeZero (ℓ ^ (k + 1)) := neZero_pow (k + 1)
      refine nsmul_eq_of_natCast_eq (ℓ := ℓ) hx ?_
      rw [ZMod.natCast_val, ZMod.natCast_val, ZMod.cast_id, ZMod.castHom_apply]
    rw [hred (mem_torsion_fst hgen k) (α (k + 1)), hred (mem_torsion_snd hgen k) (β (k + 1))]
      at hstep
    have hfk : (ZMod.castHom (pow_dvd_pow ℓ k.le_succ) (ZMod (ℓ ^ k)) (α (k + 1)),
        ZMod.castHom (pow_dvd_pow ℓ k.le_succ) (ZMod (ℓ ^ k)) (β (k + 1))) = (α k, β k) := by
      refine (torsionPairHom_bijective_of_card (hcard k) (hgen k)).1 (Subtype.ext ?_)
      rw [torsionPairHom_apply_coe, torsionPairHom_apply_coe, hstep, hαβ k]
    exact ⟨congrArg Prod.fst hfk, congrArg Prod.snd hfk⟩
  have hαmem : α ∈ compatSeq ℓ := fun k => (hcompat k).1
  have hβmem : β ∈ compatSeq ℓ := fun k => (hcompat k).2
  refine ⟨(compatSeqEquiv.symm ⟨α, hαmem⟩, compatSeqEquiv.symm ⟨β, hβmem⟩), tateModule.ext
    fun k => ?_⟩
  rw [padicPairHom_apply_coe]
  simpa using hαβ k

/-! ### The equivalence, freeness and the rank -/

/-- **`T_ℓE ≅ ℤ_ℓ²`**: the equivalence `ℤ_[ℓ] × ℤ_[ℓ] ≃ₗ[ℤ_[ℓ]] T_ℓE` attached to a coherent system
of generating pairs of the groups `E[ℓ^k]`. -/
noncomputable def padicPairEquiv
    (hcard : ∀ k, Nat.card (W.torsion (ℓ ^ k)) = ℓ ^ k * ℓ ^ k)
    (hgen : ∀ k, AddSubgroup.closure ({P k, Q k} : Set W.Point) = W.torsion (ℓ ^ k))
    (hP : ∀ k, ℓ • P (k + 1) = P k) (hQ : ∀ k, ℓ • Q (k + 1) = Q k) :
    (ℤ_[ℓ] × ℤ_[ℓ]) ≃ₗ[ℤ_[ℓ]] W.tateModule ℓ :=
  LinearEquiv.ofBijective _
    ⟨padicPairHom_injective hcard hgen hP hQ,
      padicPairHom_surjective hcard hgen hP hQ⟩

/-- The level-`k` value of the family attached to `(a, b)`: the residues of `a` and `b` modulo
`ℓ^k` read as coefficients on the level-`k` basis. This is the identity that a later analysis of
the Galois action on `T_ℓE` will run on. -/
@[simp]
lemma padicPairEquiv_apply_coe
    (hcard : ∀ k, Nat.card (W.torsion (ℓ ^ k)) = ℓ ^ k * ℓ ^ k)
    (hgen : ∀ k, AddSubgroup.closure ({P k, Q k} : Set W.Point) = W.torsion (ℓ ^ k))
    (hP : ∀ k, ℓ • P (k + 1) = P k) (hQ : ∀ k, ℓ • Q (k + 1) = Q k) (ab : ℤ_[ℓ] × ℤ_[ℓ])
    (k : ℕ) :
    ((padicPairEquiv hcard hgen hP hQ ab : W.tateModule ℓ) : ℕ → W.Point) k
      = (toZModPow k ab.1).val • P k + (toZModPow k ab.2).val • Q k := rfl

end Basis

section Structure

variable [Fact ℓ.Prime]

/-- **The Tate module is `ℤ_[ℓ]`-linearly isomorphic to `ℤ_[ℓ] × ℤ_[ℓ]`** as soon as a coherent
system of generating pairs exists and `#E[ℓ^k] = ℓ^k · ℓ^k`. The isomorphism depends on the choice
of system, so it is stated as a `Nonempty`; the choice-free consequences are
`free_tateModule_of_card` and `finrank_tateModule_of_card`. -/
theorem nonempty_tateModuleEquivProd_of_card
    (hcard : ∀ k, Nat.card (W.torsion (ℓ ^ k)) = ℓ ^ k * ℓ ^ k)
    (hbasis : ∃ P Q : ℕ → W.Point,
      (∀ k, AddSubgroup.closure ({P k, Q k} : Set W.Point) = W.torsion (ℓ ^ k)) ∧
      (∀ k, ℓ • P (k + 1) = P k) ∧ (∀ k, ℓ • Q (k + 1) = Q k)) :
    Nonempty (W.tateModule ℓ ≃ₗ[ℤ_[ℓ]] ℤ_[ℓ] × ℤ_[ℓ]) := by
  obtain ⟨P, Q, hgen, hP, hQ⟩ := hbasis
  exact ⟨(padicPairEquiv hcard hgen hP hQ).symm⟩

/-- **`T_ℓE` is a free `ℤ_[ℓ]`-module** (Silverman, *AEC*, III.7.1). -/
theorem free_tateModule_of_card
    (hcard : ∀ k, Nat.card (W.torsion (ℓ ^ k)) = ℓ ^ k * ℓ ^ k)
    (hbasis : ∃ P Q : ℕ → W.Point,
      (∀ k, AddSubgroup.closure ({P k, Q k} : Set W.Point) = W.torsion (ℓ ^ k)) ∧
      (∀ k, ℓ • P (k + 1) = P k) ∧ (∀ k, ℓ • Q (k + 1) = Q k)) :
    Module.Free ℤ_[ℓ] (W.tateModule ℓ) := by
  obtain ⟨e⟩ := nonempty_tateModuleEquivProd_of_card hcard hbasis
  exact Module.Free.of_equiv e.symm

/-- **`T_ℓE` has rank two over `ℤ_[ℓ]`.** -/
theorem finrank_tateModule_of_card
    (hcard : ∀ k, Nat.card (W.torsion (ℓ ^ k)) = ℓ ^ k * ℓ ^ k)
    (hbasis : ∃ P Q : ℕ → W.Point,
      (∀ k, AddSubgroup.closure ({P k, Q k} : Set W.Point) = W.torsion (ℓ ^ k)) ∧
      (∀ k, ℓ • P (k + 1) = P k) ∧ (∀ k, ℓ • Q (k + 1) = Q k)) :
    Module.finrank ℤ_[ℓ] (W.tateModule ℓ) = 2 := by
  obtain ⟨e⟩ := nonempty_tateModuleEquivProd_of_card hcard hbasis
  rw [e.finrank_eq, Module.finrank_prod, Module.finrank_self]

/-- **`T_ℓE` is a finitely generated `ℤ_[ℓ]`-module.** Free of rank two, so in particular finite as
a module; this is the shape `ρ_{E,ℓ} : G_F → GL₂(ℤ_ℓ)` will need. -/
theorem finite_tateModule_of_card
    (hcard : ∀ k, Nat.card (W.torsion (ℓ ^ k)) = ℓ ^ k * ℓ ^ k)
    (hbasis : ∃ P Q : ℕ → W.Point,
      (∀ k, AddSubgroup.closure ({P k, Q k} : Set W.Point) = W.torsion (ℓ ^ k)) ∧
      (∀ k, ℓ • P (k + 1) = P k) ∧ (∀ k, ℓ • Q (k + 1) = Q k)) :
    Module.Finite ℤ_[ℓ] (W.tateModule ℓ) := by
  obtain ⟨e⟩ := nonempty_tateModuleEquivProd_of_card hcard hbasis
  exact Module.Finite.equiv e.symm

end Structure

end tateModule

end WeierstrassCurve.Affine
