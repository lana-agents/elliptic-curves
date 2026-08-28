/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import Mathlib.Algebra.Module.Equiv.Basic
import EllipticCurves.TateModule.Basic

/-!
# The Galois action on the Tate module and the `ℓ`-adic representation `ρ_ℓ`

Let `W'` be a Weierstrass curve defined over a field `S`, let `F` be a field extension of `S`, and
let `G = F ≃ₐ[S] F` be its group of `S`-algebra automorphisms (the Galois group when `F / S` is
Galois). Every `σ ∈ G` acts on the points of the base-changed curve `W'⁄F` by the functoriality of
points under an algebra homomorphism (`WeierstrassCurve.Affine.Point.map`), and this action is by
*additive group automorphisms*. Consequently it preserves each torsion subgroup `E[ℓ^k]` and
commutes with the multiplication-by-`ℓ` transition maps, so it assembles into an action on the
`ℓ`-adic Tate module `T_ℓ E`. Because the levelwise action is additive, it is `ℤ_ℓ`-linear, giving
the **`ℓ`-adic Galois representation**
$$ \rho_\ell : G \longrightarrow \operatorname{Aut}_{\mathbb{Z}_\ell}(T_\ell E). $$

This file records the pointwise action, the induced actions on `E[ℓ^k]` and on `T_ℓ E`, the
`ℤ_ℓ`-linearity (`SMulCommClass`), the representation `ρ_ℓ`, the mod-`ℓ` representation on `E[ℓ]`,
and the `G`-equivariance of the level projections. Continuity of `ρ_ℓ` for the profinite topology
on `G` and the `ℓ`-adic topology on `T_ℓ E` is *not* addressed here and is left to a follow-up; the
representation is constructed purely as an abstract group homomorphism.

## Main definitions

* `WeierstrassCurve.Affine.Point.instSMulAlgEquiv` : the action `σ • P = Point.map σ P` of
  `G = F ≃ₐ[S] F` on `(W'⁄F).Point`, promoted to a `DistribMulAction`.
* `WeierstrassCurve.Affine.galoisRep` : the `ℓ`-adic representation
  `ρ_ℓ : G →* (T_ℓ E ≃ₗ[ℤ_[ℓ]] T_ℓ E)`.
* `WeierstrassCurve.Affine.galoisRepMod` : the mod-`ℓ` representation `G →* (E[ℓ] ≃+ E[ℓ])`.

## Main statements

* `WeierstrassCurve.Affine.Point.galois_smul_nsmul` : the action commutes with `nsmul`, so it is
  additive and preserves torsion.
* `WeierstrassCurve.Affine.tateModule.proj_galois_smul` : the level projections `proj k` are
  `G`-equivariant.

## References

Silverman, *The Arithmetic of Elliptic Curves*, III.7 and VII.7.
-/

namespace WeierstrassCurve.Affine

variable {S F : Type*} [Field S] [Field F] [DecidableEq F] [Algebra S F] {W' : Affine S}

namespace Point

/-! ### The pointwise action of `F ≃ₐ[S] F` -/

/-- An `S`-algebra automorphism `σ` of `F` acts on the points of the base-changed curve `W'⁄F` by
the functoriality of points, `σ • P = Point.map σ P`. -/
noncomputable instance instSMulAlgEquiv : SMul (F ≃ₐ[S] F) (W'⁄F).Point where
  smul σ P := Point.map (σ : F →ₐ[S] F) P

lemma galois_smul_def (σ : F ≃ₐ[S] F) (P : (W'⁄F).Point) :
    σ • P = Point.map (σ : F →ₐ[S] F) P :=
  rfl

noncomputable instance : MulAction (F ≃ₐ[S] F) (W'⁄F).Point where
  one_smul P := by cases P <;> rfl
  mul_smul σ τ P := by
    change Point.map ((σ * τ : F ≃ₐ[S] F) : F →ₐ[S] F) P
        = Point.map (σ : F →ₐ[S] F) (Point.map (τ : F →ₐ[S] F) P)
    rw [Point.map_map]
    rfl

noncomputable instance : DistribMulAction (F ≃ₐ[S] F) (W'⁄F).Point where
  smul_zero σ := (Point.map (σ : F →ₐ[S] F)).map_zero
  smul_add σ P Q := (Point.map (σ : F →ₐ[S] F)).map_add P Q

/-- The Galois action commutes with `nsmul`: `σ • (n • P) = n • (σ • P)`. This expresses additivity
of `σ •` and is the source of both torsion preservation and compatibility with the transition maps.
-/
lemma galois_smul_nsmul (σ : F ≃ₐ[S] F) (n : ℕ) (P : (W'⁄F).Point) :
    σ • (n • P) = n • (σ • P) :=
  (Point.map (σ : F →ₐ[S] F)).map_nsmul n P

end Point

/-! ### The induced action on the torsion subgroups `E[ℓ^k]` -/

open Point in
/-- `G = F ≃ₐ[S] F` acts on the `n`-torsion `E[n]`, since the additive action preserves torsion. -/
noncomputable instance instSMulAlgEquivTorsion (n : ℕ) :
    SMul (F ≃ₐ[S] F) ((W'⁄F).torsion n) where
  smul σ P := ⟨σ • (P : (W'⁄F).Point), by
    rw [mem_torsion_iff, ← galois_smul_nsmul, mem_torsion_iff.mp P.2]
    exact smul_zero σ⟩

@[simp]
lemma torsion_galois_smul_coe (n : ℕ) (σ : F ≃ₐ[S] F) (P : (W'⁄F).torsion n) :
    ((σ • P : (W'⁄F).torsion n) : (W'⁄F).Point) = σ • (P : (W'⁄F).Point) :=
  rfl

noncomputable instance (n : ℕ) : MulAction (F ≃ₐ[S] F) ((W'⁄F).torsion n) where
  one_smul _ := Subtype.ext (one_smul _ _)
  mul_smul _ _ _ := Subtype.ext (mul_smul _ _ _)

noncomputable instance (n : ℕ) : DistribMulAction (F ≃ₐ[S] F) ((W'⁄F).torsion n) where
  smul_zero σ := Subtype.ext (smul_zero σ)
  smul_add σ _ _ := Subtype.ext (smul_add σ _ _)

/-! ### The induced action on the Tate module `T_ℓ E` -/

variable (ℓ : ℕ)

namespace tateModule

open Point

/-- `G = F ≃ₐ[S] F` acts on the Tate module `T_ℓ E` levelwise, `(σ • f) k = σ • (f k)`; the family
stays compatible because the action preserves torsion and commutes with the transition maps. -/
noncomputable instance instSMulAlgEquiv : SMul (F ≃ₐ[S] F) ((W'⁄F).tateModule ℓ) where
  smul σ f := ⟨fun k => σ • (f : ℕ → (W'⁄F).Point) k, by
    refine ⟨fun k => ?_, fun k => ?_⟩
    · rw [mem_torsion_iff, ← galois_smul_nsmul, mem_torsion_iff.mp (coe_mem_torsion f k)]
      exact smul_zero σ
    · rw [← galois_smul_nsmul, smul_coe_succ]⟩

@[simp]
lemma galois_smul_coe (σ : F ≃ₐ[S] F) (f : (W'⁄F).tateModule ℓ) (k : ℕ) :
    ((σ • f : (W'⁄F).tateModule ℓ) : ℕ → (W'⁄F).Point) k = σ • (f : ℕ → (W'⁄F).Point) k :=
  rfl

noncomputable instance : MulAction (F ≃ₐ[S] F) ((W'⁄F).tateModule ℓ) where
  one_smul _ := tateModule.ext fun _ => one_smul _ _
  mul_smul _ _ _ := tateModule.ext fun _ => mul_smul _ _ _

noncomputable instance : DistribMulAction (F ≃ₐ[S] F) ((W'⁄F).tateModule ℓ) where
  smul_zero _ := tateModule.ext fun _ => by
    simp only [galois_smul_coe, ZeroMemClass.coe_zero, Pi.zero_apply, smul_zero]
  smul_add _ _ _ := tateModule.ext fun _ => by
    simp only [galois_smul_coe, AddSubgroup.coe_add, Pi.add_apply, smul_add]

/-- The Galois action on `T_ℓ E` commutes with the `ℤ_ℓ`-scalar multiplication: it is
`ℤ_ℓ`-linear. Both act levelwise, the Galois action additively and the `ℓ`-adic integer by `nsmul`,
and additive maps commute with `nsmul`. -/
instance [Fact ℓ.Prime] :
    SMulCommClass (F ≃ₐ[S] F) ℤ_[ℓ] ((W'⁄F).tateModule ℓ) where
  smul_comm _ _ _ := tateModule.ext fun _ => by
    simp only [galois_smul_coe, smul_coe, galois_smul_nsmul]

/-- The level projection `proj k : T_ℓ E →+ E[ℓ^k]` is `G`-equivariant. -/
lemma proj_galois_smul (σ : F ≃ₐ[S] F) (f : (W'⁄F).tateModule ℓ) (k : ℕ) :
    proj k (σ • f) = σ • proj k f :=
  rfl

end tateModule

/-! ### The `ℓ`-adic and mod-`ℓ` Galois representations -/

/-- The **`ℓ`-adic Galois representation** attached to `W'⁄F`:
`ρ_ℓ : (F ≃ₐ[S] F) →* (T_ℓ E ≃ₗ[ℤ_[ℓ]] T_ℓ E)`, sending a Galois automorphism to the
`ℤ_ℓ`-linear automorphism of the Tate module it induces. When `F / S` is the separable closure and
`ℓ ≠ char S`, this is the classical representation `Gal(S̄ / S) → GL₂(ℤ_ℓ)` of Silverman AEC III.7.
Continuity is not asserted here. It is proved downstream as `continuous_galoisRep`
(`EllipticCurves.TateModule.Continuity`), and in exactly one shape: for the **Krull** topology on
`F ≃ₐ[S] F` and **pointwise convergence** on `T_ℓ E → T_ℓ E`, not for the compact-open topology and
not for `GL₂(ℤ_[ℓ])` with its `ℓ`-adic topology. It also assumes `[Algebra.IsIntegral S F]` on top
of this file's hypotheses, so a consumer of `ρ_ℓ` does not get it for free. -/
noncomputable def galoisRep [Fact ℓ.Prime] :
    (F ≃ₐ[S] F) →* ((W'⁄F).tateModule ℓ ≃ₗ[ℤ_[ℓ]] (W'⁄F).tateModule ℓ) :=
  DistribMulAction.toModuleAut ℤ_[ℓ] ((W'⁄F).tateModule ℓ)

@[simp]
lemma galoisRep_apply_coe [Fact ℓ.Prime] (σ : F ≃ₐ[S] F) (f : (W'⁄F).tateModule ℓ) :
    galoisRep ℓ σ f = σ • f :=
  rfl

/-- The **mod-`ℓ` Galois representation** on the `ℓ`-torsion `E[ℓ]`:
`(F ≃ₐ[S] F) →* (E[ℓ] ≃ₗ[ℤ] E[ℓ])`. As `E[ℓ]` is an abelian group, a `ℤ`-linear automorphism is
the same as an additive one; this is the object the Néron–Ogg–Shafarevich criterion (#73) consumes
for the reduction of `ρ_ℓ`. -/
noncomputable def galoisRepMod :
    (F ≃ₐ[S] F) →* ((W'⁄F).torsion ℓ ≃ₗ[ℤ] (W'⁄F).torsion ℓ) :=
  DistribMulAction.toModuleAut ℤ ((W'⁄F).torsion ℓ)

@[simp]
lemma galoisRepMod_apply_coe (σ : F ≃ₐ[S] F) (P : (W'⁄F).torsion ℓ) :
    galoisRepMod ℓ σ P = σ • P :=
  rfl

end WeierstrassCurve.Affine
