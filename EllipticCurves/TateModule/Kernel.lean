/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import EllipticCurves.Fixtures
import EllipticCurves.TateModule.Determinant
import EllipticCurves.TateModule.DeterminantThree
import EllipticCurves.TateModule.LevelStructure
import EllipticCurves.Torsion.TriplingSurjective

/-!
# The level filtration of `ρ_ℓ` : `ker ρ_ℓ = ⋂_k ker (G → Aut E[ℓ^k])`

`EllipticCurves.TateModule.GaloisAction` builds the `ℓ`-adic representation
`ρ_ℓ = galoisRep ℓ : G →* Aut_{ℤ_ℓ}(T_ℓ E)` and the finite-level representations
`galoisRepMod n : G →* Aut_ℤ(E[n])`, and records that the level projections `proj k` are
`G`-equivariant. This file proves that `ρ_ℓ` is *determined by its finite levels*, in the precise
sense that its kernel is the intersection of the level kernels:

```
ker (galoisRep ℓ) = ⨅ k, ker (galoisRepMod (ℓ ^ k)),
```

equivalently `σ` acts trivially on `T_ℓ E` if and only if it fixes every `ℓ`-power torsion point.

## What is unconditional and what is not

The two inclusions are *not* symmetric in their hypotheses, and the asymmetry is the mathematical
content of the file.

* `⨅ k, ker (galoisRepMod (ℓ ^ k)) ≤ ker (galoisRep ℓ)` is **unconditional**
  (`iInf_ker_galoisRepMod_pow_le_ker_galoisRep`). An element of `T_ℓ E` is a compatible family of
  torsion points, so fixing every torsion point fixes it levelwise, and `tateModule.ext` finishes.
* `ker (galoisRep ℓ) ≤ ker (galoisRepMod (ℓ ^ k))` **needs level surjectivity**
  (`ker_galoisRep_le_ker_galoisRepMod_pow`). From `σ • f = f` for all `f ∈ T_ℓ E` one learns only
  that `σ` fixes the points of `E[ℓ^k]` that are `proj k` of a compatible family; that these are
  *all* of `E[ℓ^k]` is exactly `tateModule.proj_surjective`, which is conditional on multiplication
  by `ℓ` being surjective on `W.Point`. Without it the statement is not available: for all this
  layer knows, `T_ℓ E` could be zero while `E[ℓ^k]` is not.
* The congruence tower is descending, `ker (galoisRepMod (ℓ^k)) ≤ ker (galoisRepMod (ℓ^j))` for
  `j ≤ k`, **unconditionally** (`ker_galoisRepMod_pow_antitone`) — this is just `E[ℓ^j] ⊆ E[ℓ^k]`.
* At `ℓ = 2` over an algebraically closed field with `2 ≠ 0` the hypothesis is discharged by
  `nsmul_two_surjective`, so `ker_galoisRepTwo_eq_iInf` and `galoisRepTwo_eq_one_iff` are
  unconditional. ⚠️ Two clauses this bullet used to carry are false and are replaced. The first,
  *"No odd `ℓ` has that shortcut yet"*, is false at `ℓ = 3`, where `nsmul_three_surjective`
  (`EllipticCurves.Torsion.TriplingSurjective`) discharges the same hypothesis, also from
  `(2 : F) ≠ 0` alone. The second, *"the `ℓ = 3` specialisations are simply not stated in this
  file"*, was a description of this file and is no longer one: `ker_galoisRepThree_eq_iInf` and
  `galoisRepThree_eq_one_iff` are stated below, and they carry `h2` and **not** `h3`, for the
  reason the `§ The unconditional ℓ = 3 layer` heading gives. No prime `ℓ ≥ 5` has the shortcut.

## Why this is worth having

It is the algebraic half of **continuity** of `ρ_ℓ`: the profinite statement is that each level
kernel is open in the Krull topology on `G`, and it is this identity that says those kernels
exhaust `ker ρ_ℓ`. **No topology appears anywhere in this file and continuity is not asserted.**
It is also the form the Néron–Ogg–Shafarevich criterion (#73) consumes: "the inertia group acts
trivially on `T_ℓ E`" is only usable once it is known to mean "trivially on every `E[ℓ^k]`".

Nothing here claims that `ρ_ℓ` is *injective* — that `ker ρ_ℓ` is trivial is a genuine theorem about
`F / S`, not a formal consequence of anything proved below, and it is not attempted.

## Main statements

* `WeierstrassCurve.Affine.tateModule.galois_smul_eq_self_iff` : `σ • f = f` iff `σ` fixes every
  level value of `f`.
* `WeierstrassCurve.Affine.ker_galoisRep_eq_iInf` and its unbundled form
  `WeierstrassCurve.Affine.galoisRep_eq_one_iff`.
* `WeierstrassCurve.Affine.ker_galoisRepMod_pow_antitone` : the congruence tower is descending.
* `WeierstrassCurve.Affine.galoisRepTwo_eq_one_iff` : the unconditional `ℓ = 2` form.
* `WeierstrassCurve.Affine.galoisRepThree_eq_one_iff` : the unconditional `ℓ = 3` form.
* `WeierstrassCurve.Affine.ker_galoisRepMatrix` : the matrix representation has the same kernel as
  `galoisRep ℓ`, for *every* basis and at every prime, and
  `WeierstrassCurve.Affine.galoisRepMatrix_eq_one_iff` reads it off.
  ⚠️ **The clause this bullet used to end with is retired**: it read *"`ker_galoisRepMatrixTwo` and
  `galoisRepMatrixTwo_eq_one_iff` are the `ℓ = 2` names"*, and named only one prime because only
  one prime had them. Both do now —
  `WeierstrassCurve.Affine.ker_galoisRepMatrixTwo` / `…galoisRepMatrixTwo_eq_one_iff` at `ℓ = 2`
  and `WeierstrassCurve.Affine.ker_galoisRepMatrixThree` / `…galoisRepMatrixThree_eq_one_iff` at
  `ℓ = 3`.
* `WeierstrassCurve.Affine.galoisDetTwo_eq_one_of_mem_ker` and
  `WeierstrassCurve.Affine.galoisTraceTwo_eq_two_of_mem_ker`, with their `ℓ = 3` twins
  `WeierstrassCurve.Affine.galoisDetThree_eq_one_of_mem_ker` and
  `WeierstrassCurve.Affine.galoisTraceThree_eq_two_of_mem_ker` : the invariants on the kernel.
  ⚠️ **The trace rows are the only ones that distinguish `T_ℓE` from the zero module**, and the
  `two` in both their names is the **rank**, not the prime.

## References

* [J. H. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.7 and VII.7.
-/

namespace WeierstrassCurve.Affine

variable {S F : Type*} [Field S] [Field F] [DecidableEq F] [Algebra S F] {W' : Affine S}

/-! ### Acting trivially on a torsion subgroup -/

/-- `galoisRepMod n σ` is the identity exactly when `σ` fixes every `n`-torsion point. -/
lemma galoisRepMod_eq_one_iff (n : ℕ) (σ : F ≃ₐ[S] F) :
    galoisRepMod (W' := W') n σ = 1 ↔ ∀ P : (W'⁄F).torsion n, σ • P = P := by
  refine ⟨fun h P => ?_, fun h => LinearEquiv.ext fun P => ?_⟩
  · simpa using DFunLike.congr_fun h P
  · simpa using h P

/-- Membership in `ker (galoisRepMod n)`, unfolded: `σ` fixes every `n`-torsion point. -/
lemma mem_ker_galoisRepMod_iff (n : ℕ) (σ : F ≃ₐ[S] F) :
    σ ∈ (galoisRepMod (W' := W') (F := F) n).ker ↔ ∀ P : (W'⁄F).torsion n, σ • P = P := by
  rw [MonoidHom.mem_ker, galoisRepMod_eq_one_iff]

/-- **The congruence tower is descending.** If `σ` fixes every `ℓ^k`-torsion point then it fixes
every `ℓ^j`-torsion point for `j ≤ k`, because `E[ℓ^j] ⊆ E[ℓ^k]`.

This needs no divisibility hypothesis: it is monotonicity of the torsion subgroups, nothing more. -/
theorem ker_galoisRepMod_pow_antitone (ℓ : ℕ) {j k : ℕ} (h : j ≤ k) :
    (galoisRepMod (W' := W') (F := F) (ℓ ^ k)).ker
      ≤ (galoisRepMod (W' := W') (F := F) (ℓ ^ j)).ker := by
  intro σ hσ
  rw [mem_ker_galoisRepMod_iff] at hσ ⊢
  intro P
  exact Subtype.ext congr(($(hσ ⟨(P : (W'⁄F).Point), torsion_mono (pow_dvd_pow ℓ h) P.2⟩) : _))

/-- The tower `k ↦ ker (galoisRepMod (ℓ ^ k))` is antitone. -/
theorem antitone_ker_galoisRepMod_pow (ℓ : ℕ) :
    Antitone fun k => (galoisRepMod (W' := W') (F := F) (ℓ ^ k)).ker :=
  fun _ _ h => ker_galoisRepMod_pow_antitone ℓ h

/-! ### Acting trivially on the Tate module -/

namespace tateModule

/-- **`σ` fixes a compatible family iff it fixes all of its level values.** Both sides concern the
same `f`, so this direction of the comparison is free of any divisibility hypothesis. -/
theorem galois_smul_eq_self_iff (ℓ : ℕ) (σ : F ≃ₐ[S] F) (f : (W'⁄F).tateModule ℓ) :
    σ • f = f ↔ ∀ k, σ • proj k f = proj k f := by
  refine ⟨fun h k => ?_, fun h => tateModule.ext fun k => ?_⟩
  · rw [← proj_galois_smul, h]
  · exact congrArg Subtype.val (h k)

end tateModule

/-- `galoisRep ℓ σ` is the identity exactly when `σ` fixes every element of `T_ℓ E`. -/
lemma galoisRep_eq_one_iff_forall (ℓ : ℕ) [Fact ℓ.Prime] (σ : F ≃ₐ[S] F) :
    galoisRep (W' := W') ℓ σ = 1 ↔ ∀ f : (W'⁄F).tateModule ℓ, σ • f = f := by
  refine ⟨fun h f => ?_, fun h => LinearEquiv.ext fun f => ?_⟩
  · simpa using DFunLike.congr_fun h f
  · simpa using h f

/-- Membership in `ker (galoisRep ℓ)`, unfolded. -/
lemma mem_ker_galoisRep_iff (ℓ : ℕ) [Fact ℓ.Prime] (σ : F ≃ₐ[S] F) :
    σ ∈ (galoisRep (W' := W') (F := F) ℓ).ker ↔ ∀ f : (W'⁄F).tateModule ℓ, σ • f = f := by
  rw [MonoidHom.mem_ker, galoisRep_eq_one_iff_forall]

/-! ### The two inclusions -/

/-- **The unconditional inclusion.** An automorphism fixing every `ℓ`-power torsion point fixes
every compatible family, hence acts trivially on `T_ℓ E`.

No surjectivity is needed: a compatible family *is* a family of torsion points, so this direction
only ever looks at points that are already known to exist. -/
theorem iInf_ker_galoisRepMod_pow_le_ker_galoisRep (ℓ : ℕ) [Fact ℓ.Prime] :
    (⨅ k, (galoisRepMod (W' := W') (F := F) (ℓ ^ k)).ker)
      ≤ (galoisRep (W' := W') (F := F) ℓ).ker := by
  intro σ hσ
  simp only [Subgroup.mem_iInf, mem_ker_galoisRepMod_iff] at hσ
  rw [mem_ker_galoisRep_iff]
  exact fun f => tateModule.ext fun k => congrArg Subtype.val (hσ k (tateModule.proj k f))

/-- **The conditional inclusion.** If multiplication by `ℓ` is surjective on `W'⁄F`, an
automorphism acting trivially on `T_ℓ E` fixes every `ℓ^k`-torsion point.

The hypothesis is load-bearing and is used exactly once, through `tateModule.proj_surjective`:
what an element of `ker (galoisRep ℓ)` directly tells you about `E[ℓ^k]` is that `σ` fixes the
image of `proj k`, and surjectivity is what upgrades that image to all of `E[ℓ^k]`. -/
theorem ker_galoisRep_le_ker_galoisRepMod_pow (ℓ : ℕ) [Fact ℓ.Prime]
    (hℓ : Function.Surjective fun P : (W'⁄F).Point => ℓ • P) (k : ℕ) :
    (galoisRep (W' := W') (F := F) ℓ).ker
      ≤ (galoisRepMod (W' := W') (F := F) (ℓ ^ k)).ker := by
  intro σ hσ
  rw [mem_ker_galoisRep_iff] at hσ
  rw [mem_ker_galoisRepMod_iff]
  intro P
  obtain ⟨f, rfl⟩ := tateModule.proj_surjective hℓ k P
  rw [← tateModule.proj_galois_smul, hσ f]

/-- **`ρ_ℓ` is determined by its finite levels**: `σ` acts trivially on `T_ℓ E` if and only if it
fixes every `ℓ`-power torsion point. -/
theorem ker_galoisRep_eq_iInf (ℓ : ℕ) [Fact ℓ.Prime]
    (hℓ : Function.Surjective fun P : (W'⁄F).Point => ℓ • P) :
    (galoisRep (W' := W') (F := F) ℓ).ker
      = ⨅ k, (galoisRepMod (W' := W') (F := F) (ℓ ^ k)).ker :=
  le_antisymm (le_iInf fun k => ker_galoisRep_le_ker_galoisRepMod_pow ℓ hℓ k)
    (iInf_ker_galoisRepMod_pow_le_ker_galoisRep ℓ)

/-- The unbundled form of `ker_galoisRep_eq_iInf`, and the statement a consumer applies:
`ρ_ℓ(σ) = 1` exactly when `σ` fixes every `ℓ`-power torsion point. -/
theorem galoisRep_eq_one_iff (ℓ : ℕ) [Fact ℓ.Prime]
    (hℓ : Function.Surjective fun P : (W'⁄F).Point => ℓ • P) (σ : F ≃ₐ[S] F) :
    galoisRep (W' := W') ℓ σ = 1 ↔ ∀ (k : ℕ) (P : (W'⁄F).torsion (ℓ ^ k)), σ • P = P := by
  rw [← MonoidHom.mem_ker, ker_galoisRep_eq_iInf ℓ hℓ, Subgroup.mem_iInf]
  exact forall_congr' fun k => mem_ker_galoisRepMod_iff _ _

/-! ### The unconditional `ℓ = 2` layer -/

section Two

variable [IsAlgClosed F] [(W'⁄F).IsElliptic]

/-- **`ker ρ_{E,2} = ⋂_k ker (G → Aut E[2^k])`**, unconditionally over an algebraically closed
field of characteristic `≠ 2`: multiplication by `2` is surjective on `E(F̄)`, which discharges the
hypothesis of `ker_galoisRep_eq_iInf`. -/
theorem ker_galoisRepTwo_eq_iInf (h2 : (2 : F) ≠ 0) :
    (galoisRep (W' := W') (F := F) 2).ker
      = ⨅ k, (galoisRepMod (W' := W') (F := F) (2 ^ k)).ker :=
  ker_galoisRep_eq_iInf 2 (nsmul_two_surjective h2)

/-- **`ρ_{E,2}(σ) = 1` iff `σ` fixes every `2`-power torsion point**, unconditionally over an
algebraically closed field of characteristic `≠ 2`. -/
theorem galoisRepTwo_eq_one_iff (h2 : (2 : F) ≠ 0) (σ : F ≃ₐ[S] F) :
    galoisRep (W' := W') 2 σ = 1 ↔ ∀ (k : ℕ) (P : (W'⁄F).torsion (2 ^ k)), σ • P = P :=
  galoisRep_eq_one_iff 2 (nsmul_two_surjective h2) σ

end Two

/-! ### The unconditional `ℓ = 3` layer

⚠️ **Only `h2` appears below, and that is not an oversight.** The hypothesis
`ker_galoisRep_eq_iInf` wants is surjectivity of multiplication by `3` on `E(F̄)`, and
`nsmul_three_surjective` (`EllipticCurves.Torsion.TriplingSurjective`) supplies it from
`(2 : F) ≠ 0` alone — `(3 : F) ≠ 0` enters the `ℓ = 3` story only through the *counting* theorem
`card_torsion_three_pow`, which nothing in this file consumes.
`EllipticCurves.TateModule.FreeThree` records the same split for the module.
-/

section Three

variable [IsAlgClosed F] [(W'⁄F).IsElliptic]

/-- **`ker ρ_{E,3} = ⋂_k ker (G → Aut E[3^k])`**, unconditionally over an algebraically closed
field of characteristic `≠ 2`: multiplication by `3` is surjective on `E(F̄)`, which discharges the
hypothesis of `ker_galoisRep_eq_iInf`.

⚠️ **Deletion test**, measured on this file as committed. Replacing the argument
`(nsmul_three_surjective h2)` by a hole —
`by refine ker_galoisRep_eq_iInf (W' := W') (F := F) 3 ?_` — leaves

```
error: unsolved goals
S : Type u_1
F : Type u_2
inst✝⁵ : Field S
inst✝⁴ : Field F
inst✝³ : DecidableEq F
inst✝² : Algebra S F
W' : Affine S
inst✝¹ : IsAlgClosed F
inst✝ : WeierstrassCurve.IsElliptic W'⁄F
h2 : 2 ≠ 0
⊢ Function.Surjective fun P ↦ 3 • P
```

⚠️ `h2` **survives** in the context, so what is removed is a construction and not a hypothesis;
and the residual is a **goal**, which no type mismatch could produce. It is exactly
`[3]`-surjectivity, which is where the whole cost of the `ℓ = 3` case sits: no prime `ℓ ≥ 5` has it,
and without it the inclusion `ker ρ_ℓ ≤ ker (galoisRepMod (ℓ^k))` is unavailable. -/
theorem ker_galoisRepThree_eq_iInf (h2 : (2 : F) ≠ 0) :
    (galoisRep (W' := W') (F := F) 3).ker
      = ⨅ k, (galoisRepMod (W' := W') (F := F) (3 ^ k)).ker :=
  ker_galoisRep_eq_iInf 3 (nsmul_three_surjective h2)

/-- **`ρ_{E,3}(σ) = 1` iff `σ` fixes every `3`-power torsion point**, unconditionally over an
algebraically closed field of characteristic `≠ 2`. -/
theorem galoisRepThree_eq_one_iff (h2 : (2 : F) ≠ 0) (σ : F ≃ₐ[S] F) :
    galoisRep (W' := W') 3 σ = 1 ↔ ∀ (k : ℕ) (P : (W'⁄F).torsion (3 ^ k)), σ • P = P :=
  galoisRep_eq_one_iff 3 (nsmul_three_surjective h2) σ

end Three

/-! ### The matrix representation

⚠️ **The generic statements below need no per-prime restatement and get none**: they are stated at
an arbitrary prime, and `galoisRepMatrixThree` (`EllipticCurves.TateModule.MatrixRepThree`) is
*definitionally* `galoisRepMatrix` at `ℓ = 3`, so they apply to it verbatim.

⚠️ **The clause this paragraph used to end with was about the wrong thing and is retired.** It read
*"so there are deliberately no `_three` restatements of them anywhere in this development"* — which
was a claim about the **named** `ℓ = 3` forms, not about the generic ones, and it was already
contradicted, in the `MatrixTwo` section of this same file, by `ker_galoisRepMatrixTwo` and
`galoisRepMatrixTwo_eq_one_iff`.
**Both primes now carry the named forms**, per
`EllipticCurves.TateModule.MatrixRepThree`'s settled rule that leaving `ℓ = 3` without the matching
spellings puts the two primes on different footings for every downstream file that extends by
pattern.

⚠️ **That cost was already paid once, and it is measurable.** `isClosed_ker_galoisRepMatrixTwo`
(`EllipticCurves.TateModule.MatrixRepBasisChange`) closes with `rw [ker_galoisRepMatrixTwo b]`;
its twin `isClosed_ker_galoisRepMatrixThree`
(`EllipticCurves.TateModule.MatrixRepBasisChangeThree`) has to open with a
`have hker : … := ker_galoisRepMatrix b` first, **because `rw` cannot see through the definitional
equality that makes the generic statement apply.** *Definitional applicability is not the same as
being usable by `rw`, and a policy that conflates them exports work to every consumer at the
un-named prime.*

⚠️ **This reverses a policy stated in a second file, and that file records the reversal.**
`EllipticCurves.TateModule.MatrixRepBasisChangeThree` said *"there is deliberately no
`ker_galoisRepMatrixThree` … which is the whole reason
`EllipticCurves.TateModule.MatrixRepThree` declines to make `Three` twins of already-generic
theorems"*. The exception `EllipticCurves.TateModule.MatrixRepThree` states for generic
*definitions* — *"their `ℓ = 2` twins already exist and cannot be removed; leaving `ℓ = 3` without
the matching spellings would put the two primes on different footings for every downstream file
that extends by pattern"* — applies verbatim to these two theorems, whose `ℓ = 2` named forms are
in the `MatrixTwo` section immediately below this paragraph. **The general rule is unchanged: a
twin of an already-generic statement is duplication *unless the other prime already has the named
form*.** -/

variable {ℓ : ℕ} [Fact ℓ.Prime]

/-- **The matrix representation has the same kernel as `galoisRep ℓ`, in every basis.** Changing
the basis conjugates `ρ_{E,ℓ}` (`galoisRepMatrix_conj`,
`EllipticCurves.TateModule.PrimaryMatrixRepBasisChange`), so the kernel — unlike the individual
matrices — does not depend on the choice. Unconditional, and proved by a shorter route than
conjugation: `galoisRepMatrix b` is `galoisRep ℓ` postcomposed with the *equivalence*
`(matrixAutEquiv b).symm`. -/
theorem ker_galoisRepMatrix (b : Module.Basis (Fin 2) ℤ_[ℓ] ((W'⁄F).tateModule ℓ)) :
    (galoisRepMatrix b).ker = (galoisRep (W' := W') (F := F) ℓ).ker := by
  ext σ
  simp only [MonoidHom.mem_ker, galoisRepMatrix, MonoidHom.coe_comp,
    Function.comp_apply, MulEquiv.coe_toMonoidHom, EmbeddingLike.map_eq_one_iff]

/-- **`ρ_{E,ℓ}(σ)` is the identity matrix — in any basis — exactly when `σ` fixes every `ℓ`-power
torsion point.** The headline reading of the level filtration.

The hypothesis is `ker_galoisRep_eq_iInf`'s and not the matrix layer's: passing to matrices is an
equivalence and adds nothing. -/
theorem galoisRepMatrix_eq_one_iff (b : Module.Basis (Fin 2) ℤ_[ℓ] ((W'⁄F).tateModule ℓ))
    (hℓ : Function.Surjective fun P : (W'⁄F).Point => ℓ • P) (σ : F ≃ₐ[S] F) :
    galoisRepMatrix b σ = 1 ↔ ∀ (k : ℕ) (P : (W'⁄F).torsion (ℓ ^ k)), σ • P = P := by
  rw [← MonoidHom.mem_ker, ker_galoisRepMatrix, MonoidHom.mem_ker, galoisRep_eq_one_iff ℓ hℓ]

section MatrixTwo

variable (b : Module.Basis (Fin 2) ℤ_[2] ((W'⁄F).tateModule 2))

/-- **The matrix representation has the same kernel as `galoisRep 2`, in every basis.**
`ker_galoisRepMatrix` at `ℓ = 2`. -/
theorem ker_galoisRepMatrixTwo :
    (galoisRepMatrixTwo b).ker = (galoisRep (W' := W') (F := F) 2).ker :=
  ker_galoisRepMatrix b

/-- **`ρ_{E,2}(σ)` is the identity matrix — in any basis — exactly when `σ` fixes every `2`-power
torsion point.** The headline reading of the level filtration. -/
theorem galoisRepMatrixTwo_eq_one_iff [IsAlgClosed F] [(W'⁄F).IsElliptic] (h2 : (2 : F) ≠ 0)
    (σ : F ≃ₐ[S] F) :
    galoisRepMatrixTwo b σ = 1 ↔ ∀ (k : ℕ) (P : (W'⁄F).torsion (2 ^ k)), σ • P = P :=
  galoisRepMatrix_eq_one_iff b (nsmul_two_surjective h2) σ

/-- On `ker ρ_{E,2}` the determinant character is trivial. -/
theorem galoisDetTwo_eq_one_of_mem_ker {σ : F ≃ₐ[S] F}
    (hσ : σ ∈ (galoisRep (W' := W') (F := F) 2).ker) : galoisDetTwo (W' := W') (F := F) σ = 1 := by
  rw [galoisDetTwo_apply, MonoidHom.mem_ker.mp hσ, map_one]

/-- On `ker ρ_{E,2}` the trace character takes the value `2`, **not** `0`.

This is the discriminating statement of the file. `LinearMap.trace` is defined to be `0` on a module
that is not free and finite, so every kernel identity above would survive `T₂E = 0` intact; the
value `2` here is `Module.finrank ℤ_[2] (T₂E)` and is available only because `T₂E` really is free of
rank `2`. It is why the hypotheses `[IsAlgClosed F]`, `[(W'⁄F).IsElliptic]` and `(2 : F) ≠ 0` are
carried rather than dropped. -/
theorem galoisTraceTwo_eq_two_of_mem_ker [IsAlgClosed F] [(W'⁄F).IsElliptic] (h2 : (2 : F) ≠ 0)
    {σ : F ≃ₐ[S] F} (hσ : σ ∈ (galoisRep (W' := W') (F := F) 2).ker) :
    galoisTraceTwo (W' := W') (F := F) σ = 2 := by
  have h1 : galoisTraceTwo (W' := W') (F := F) σ = galoisTraceTwo (W' := W') (F := F) 1 := by
    unfold galoisTraceTwo galoisTrace
    rw [MonoidHom.mem_ker.mp hσ, map_one]
  rw [h1]
  exact galoisTraceTwo_one (W' := W') (F := F) h2

end MatrixTwo

/-! ### The matrix representation at `ℓ = 3`

⚠️ **The hypotheses are NOT uniform across the four rows and the asymmetry is the content.** Three
of them carry `h2` alone; only `galoisTraceThree_eq_two_of_mem_ker` carries `h3` as well. The
reason is the one the `§ The unconditional ℓ = 3 layer` heading above gives:
`nsmul_three_surjective` needs `(2 : F) ≠ 0` alone, and `(3 : F) ≠ 0` enters the `ℓ = 3` story only
through the *counting* theorem `card_torsion_three_pow` — which `galoisTraceThree_one` goes through
and nothing else here does. ⚠️ *Do not infer the split from the `ℓ = 2` rows by symmetry; at `ℓ = 2`
the two doors open with the same key and here they do not.*

⚠️ **`galoisTraceThree_eq_two_of_mem_ker` is spelled with `_two`, and that is not a typo.** The
first `Three` is the **prime**; the `two` is the **value** `2 = Module.finrank ℤ_[3] (T₃E)
= tr(I₂)`, which is `2` at every prime. A mechanical `Two → Three` rename of the `ℓ = 2` row
produces `…_eq_three_of_mem_ker`, whose statement is **false**. *A name is not a substitution
target just because it contains a numeral; read what each numeral denotes.* -/

section MatrixThree

variable [IsAlgClosed F] [(W'⁄F).IsElliptic]
variable (b : Module.Basis (Fin 2) ℤ_[3] ((W'⁄F).tateModule 3))

omit [IsAlgClosed F] [(W'⁄F).IsElliptic] in
/-- **The matrix representation has the same kernel as `galoisRep 3`, in every basis.**
`ker_galoisRepMatrix` at `ℓ = 3`, and unconditional exactly as at `ℓ = 2`.

⚠️ The generic statement already applies to `galoisRepMatrixThree` definitionally; this named form
exists so that `rw` can use it, which is the thing definitional applicability does not give — see
the section heading above for the consumer that paid for its absence. -/
theorem ker_galoisRepMatrixThree :
    (galoisRepMatrixThree b).ker = (galoisRep (W' := W') (F := F) 3).ker :=
  ker_galoisRepMatrix b

/-- **`ρ_{E,3}(σ)` is the identity matrix — in any basis — exactly when `σ` fixes every `3`-power
torsion point.** The headline reading of the level filtration at `ℓ = 3`.

⚠️ **`h2` alone**, with no `h3`: the hypothesis is `galoisRepMatrix_eq_one_iff`'s, namely
`[3]`-surjectivity on `E(F̄)`, and `nsmul_three_surjective` supplies that from `(2 : F) ≠ 0`. -/
theorem galoisRepMatrixThree_eq_one_iff (h2 : (2 : F) ≠ 0) (σ : F ≃ₐ[S] F) :
    galoisRepMatrixThree b σ = 1 ↔ ∀ (k : ℕ) (P : (W'⁄F).torsion (3 ^ k)), σ • P = P :=
  galoisRepMatrix_eq_one_iff b (nsmul_three_surjective h2) σ

omit [IsAlgClosed F] [(W'⁄F).IsElliptic] in
/-- On `ker ρ_{E,3}` the determinant character is trivial.

⚠️ **This is not progress towards `det ρ_{E,3} = χ_3`.** Every character is trivial on the kernel
of the representation it is built from; the `3`-adic identification needs the Weil pairing on
`E[3^k]` for *every* `k`.  ⚠️ This sentence used to add *"i.e. the `ωₙ` crux"*, and that equation
is false twice over: the `ωₙ` crux is `#404`'s on-curve identity, closed in
`EllipticCurves.Torsion.OmegaCrux` (PR #557), and it is neither the pairing at every level nor the
coordinate formula. The **mod-`3`** identity is a different statement
about a different object and is
`EllipticCurves.FunctionField.WeilPairingDeterminantCharacter`. -/
theorem galoisDetThree_eq_one_of_mem_ker {σ : F ≃ₐ[S] F}
    (hσ : σ ∈ (galoisRep (W' := W') (F := F) 3).ker) :
    galoisDetThree (W' := W') (F := F) σ = 1 := by
  rw [galoisDetThree_apply, MonoidHom.mem_ker.mp hσ, map_one]

/-- On `ker ρ_{E,3}` the trace character takes the value `2`, **not** `0` and **not** `3`.

This is the discriminating statement of the `ℓ = 3` layer, for the same reason its `ℓ = 2` twin is
the discriminating statement of the file: `LinearMap.trace` is defined to be `0` on a module that is
not free and finite, so every kernel identity above survives `T₃E = 0` intact and this one does not.
The value `2` is `Module.finrank ℤ_[3] (T₃E)` and is available only because `T₃E` really is free of
rank `2`, which is why `[IsAlgClosed F]`, `[(W'⁄F).IsElliptic]`, `(2 : F) ≠ 0` and `(3 : F) ≠ 0` are
carried rather than dropped.

⚠️ **The `2` in the name is the rank, not the prime**, and this is the only row in the section that
needs `h3` — it reaches the count `#E[3] = 9` through `galoisTraceThree_one`.

⚠️ **Deletion test**, measured on this file as committed. Deleting `(h3 : (3 : F) ≠ 0)` from the
signature and replacing `h3` by a hole — `refine galoisTraceThree_one (W' := W') (F := F) h2 ?_` —
leaves, copy-paste:

```
error: unsolved goals
S : Type u_1
F : Type u_2
inst✝⁵ : Field S
inst✝⁴ : Field F
inst✝³ : DecidableEq F
inst✝² : Algebra S F
W' : Affine S
inst✝¹ : IsAlgClosed F
inst✝ : WeierstrassCurve.IsElliptic W'⁄F
h2 : 2 ≠ 0
σ : Gal(F/S)
hσ : σ ∈ (galoisRep 3).ker
h1 : galoisTraceThree σ = galoisTraceThree 1
⊢ 3 ≠ 0
```

⚠️ `h2` and `h1` both **survive** and the residual is a **goal**, which no type mismatch could
produce. It is exactly the counting input, so the test *localises* `h3` to `#E[3] = 9` and confirms
that the lifting step is `h3`-free. One mechanical edit accompanies it and adds no information
(`exact` becomes `refine … ?_`).

⚠️ **There IS a knock-on and it is disclosed**: the load-bearing `#916` certificate below consumes
this theorem by application, so with the hypothesis deleted it reports a further
`Function expected at galoisTraceThree_eq_two_of_mem_ker exampleTwo ?m` and an
`Application type mismatch` on `exampleThree`. **That is not part of the test** — it is the
certificate doing its job, and a deletion test that produced *no* knock-on here would mean the
certificate was not consuming the declaration it certifies.

⚠️ Two further notes, because *"character-for-character"* is this board's standard and two lines of
this paste cannot meet it from the file as committed. The `file:line:col` header drifts when the
docstring itself is added. And the section variable `b` is **absent** from the context above even
though it is in scope: it is an *explicit* section variable, so Lean includes it only in
declarations that mention it, and this one does not. *An explicit section variable that does not
appear in the residual has not been dropped; it was never added.* -/
theorem galoisTraceThree_eq_two_of_mem_ker (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0)
    {σ : F ≃ₐ[S] F} (hσ : σ ∈ (galoisRep (W' := W') (F := F) 3).ker) :
    galoisTraceThree (W' := W') (F := F) σ = 2 := by
  have h1 : galoisTraceThree (W' := W') (F := F) σ = galoisTraceThree (W' := W') (F := F) 1 := by
    unfold galoisTraceThree galoisTrace
    rw [MonoidHom.mem_ker.mp hσ, map_one]
  rw [h1]
  exact galoisTraceThree_one (W' := W') (F := F) h2 h3

end MatrixThree

/-! ### Non-vacuity

⚠️ **The risk in this file is specific and it is not the usual one.** Almost everything above
survives `T₃E = 0` intact: `LinearMap.trace` is *defined* to be `0` on a module that is not free and
finite, `galoisRep` on the zero module is trivial, and every kernel identity then holds for free.
The single statement falsified by `T₃E = 0` is `galoisTraceThree_eq_two_of_mem_ker`, whose value
`2` is `Module.finrank ℤ_[3] (T₃E)`. (Its `ℓ = 2` twin is falsified by `T₂E = 0` for the same
reason; the count of one here is a count *at this prime*.)

⚠️ **So a certificate that only exhibits a curve satisfying the hypotheses would certify nothing
here; the load-bearing one has to consume the trace row.**

⚠️ Neither `[Algebra.IsIntegral S F]` nor `[IsGalois S F]` appears in this file's `variable` block
or in any statement above, so — unlike `EllipticCurves.TateModule.ImageThree` and
`EllipticCurves.TateModule.ImageProfiniteThree` — no `ℚ`-algebra instance workaround is needed here
at all, by either the `haveI` or the `attribute [local instance]` route. **Checked against the
`variable` block, not assumed from the neighbouring files.** `open Classical in` *is* load-bearing:
`AlgClosedQ` is `AlgebraicClosure ℚ`, which carries no `DecidableEq`.

⚠️ Every `TateModule` certificate block now names the one shared fixture
`EllipticCurves.Fixture.y2AddYEqX3`; the `private` per-file copies this note used to describe are
gone. -/

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
/-- **⚠️ THE LOAD-BEARING CERTIFICATE**: on a curve that exists, over a base field `S = ℚ` whose
absolute Galois group is not trivial, the two invariants really do take the values claimed on
`ker ρ_{E,3}` — and the trace really is `2`, which is the one statement at `ℓ = 3` in this file
that a zero Tate module would falsify.

It closes by **application** of `galoisTraceThree_eq_two_of_mem_ker` and
`galoisDetThree_eq_one_of_mem_ker`, not by `rfl`, `decide` or `norm_num`, so it consumes the
declarations it certifies. -/
example : ∀ σ ∈ (galoisRep (W' := y2AddYEqX3 ℚ) (F := AlgClosedQ) 3).ker,
    galoisTraceThree (W' := y2AddYEqX3 ℚ) (F := AlgClosedQ) σ = 2 ∧
      galoisDetThree (W' := y2AddYEqX3 ℚ) (F := AlgClosedQ) σ = 1 :=
  fun _ hσ => ⟨galoisTraceThree_eq_two_of_mem_ker exampleTwo exampleThree hσ,
    galoisDetThree_eq_one_of_mem_ker hσ⟩

open Classical in
/-- **The matrix rows are certified on the same curve**, with the basis **existentially quantified
inside the statement** rather than taken as an argument, so this does not certify a family that
might be empty. Closes by application of `ker_galoisRepMatrixThree` and
`galoisRepMatrixThree_eq_one_iff`. -/
example : ∃ b : Module.Basis (Fin 2) ℤ_[3] (((y2AddYEqX3 ℚ)⁄AlgClosedQ).tateModule 3),
    (galoisRepMatrixThree b).ker
        = (galoisRep (W' := y2AddYEqX3 ℚ) (F := AlgClosedQ) 3).ker ∧
      ∀ σ : AlgClosedQ ≃ₐ[ℚ] AlgClosedQ, galoisRepMatrixThree b σ = 1 ↔
        ∀ (k : ℕ) (P : ((y2AddYEqX3 ℚ)⁄AlgClosedQ).torsion (3 ^ k)), σ • P = P := by
  obtain ⟨b⟩ := tateModule.nonempty_basis_tateModule_three
    (W := (y2AddYEqX3 ℚ)⁄AlgClosedQ) exampleTwo exampleThree
  exact ⟨b, ker_galoisRepMatrixThree b, galoisRepMatrixThree_eq_one_iff b exampleTwo⟩

open Classical in
/-- **The module the representation acts on is not the zero module**, on the same curve, by a route
that never mentions kernels or matrices: `T₃E` surjects onto `E[3^k]`, which has `9^k` elements.
Without this the trace certificate above would be an assertion about `LinearMap.trace`'s default
value on a degenerate module. -/
example : Infinite (((y2AddYEqX3 ℚ)⁄AlgClosedQ).tateModule 3) :=
  tateModule.infinite_tateModule_three exampleTwo exampleThree

end Nonvacuity

end WeierstrassCurve.Affine
