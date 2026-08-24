/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import EllipticCurves.TateModule.Determinant
import EllipticCurves.TateModule.LevelStructure

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
  unconditional. ⚠️ The clause this bullet used to carry — *"No odd `ℓ` has that shortcut yet"* —
  is false at `ℓ = 3`, where `nsmul_three_surjective`
  (`EllipticCurves.Torsion.TriplingSurjective`) discharges the same hypothesis, also from
  `(2 : F) ≠ 0` alone; the `ℓ = 3` specialisations are simply not stated in this file. No prime
  `ℓ ≥ 5` has the shortcut.

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
* `WeierstrassCurve.Affine.ker_galoisRepMatrixTwo` : the matrix representation has the same kernel
  as `galoisRep 2`, for *every* basis, and `galoisRepMatrixTwo_eq_one_iff` reads it off.

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

/-! ### The matrix representation -/

variable (b : Module.Basis (Fin 2) ℤ_[2] ((W'⁄F).tateModule 2))

/-- **The matrix representation has the same kernel as `galoisRep 2`, in every basis.** Changing
the basis conjugates `ρ_{E,2}`, so the kernel — unlike the individual matrices — does not depend on
the choice. Unconditional: `galoisRepMatrixTwo b` is `galoisRep 2` postcomposed with the
*equivalence* `(matrixAutEquivTwo b).symm`. -/
theorem ker_galoisRepMatrixTwo :
    (galoisRepMatrixTwo b).ker = (galoisRep (W' := W') (F := F) 2).ker := by
  ext σ
  simp only [MonoidHom.mem_ker, galoisRepMatrixTwo, galoisRepMatrix, MonoidHom.coe_comp,
    Function.comp_apply, MulEquiv.coe_toMonoidHom, EmbeddingLike.map_eq_one_iff]

/-- **`ρ_{E,2}(σ)` is the identity matrix — in any basis — exactly when `σ` fixes every `2`-power
torsion point.** The headline reading of the level filtration. -/
theorem galoisRepMatrixTwo_eq_one_iff [IsAlgClosed F] [(W'⁄F).IsElliptic] (h2 : (2 : F) ≠ 0)
    (σ : F ≃ₐ[S] F) :
    galoisRepMatrixTwo b σ = 1 ↔ ∀ (k : ℕ) (P : (W'⁄F).torsion (2 ^ k)), σ • P = P := by
  rw [← MonoidHom.mem_ker, ker_galoisRepMatrixTwo, MonoidHom.mem_ker, galoisRepTwo_eq_one_iff h2]

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
    unfold galoisTraceTwo
    rw [MonoidHom.mem_ker.mp hσ, map_one]
  rw [h1]
  exact galoisTraceTwo_one (W' := W') (F := F) h2

end WeierstrassCurve.Affine
