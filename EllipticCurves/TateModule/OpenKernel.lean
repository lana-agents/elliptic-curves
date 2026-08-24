/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import EllipticCurves.TateModule.Continuity
import EllipticCurves.TateModule.Kernel
import EllipticCurves.Torsion.Multiplicative
import EllipticCurves.Torsion.ThreePrimary
import EllipticCurves.Torsion.TwoPrimary
import Mathlib.Topology.LocallyConstant.Basic

/-!
# The level kernels of `ρ_{E,ℓ}` are open, and `ker ρ_{E,ℓ}` is closed

`EllipticCurves.TateModule.Kernel` proves the level filtration

```
ker (galoisRep ℓ) = ⨅ k, ker (galoisRepMod (ℓ ^ k))
```

as a statement about subgroups, with no topology anywhere; `EllipticCurves.TateModule.Continuity`
puts the Krull topology to work and proves that the stabiliser of a *point* of `E(F)` is open. This
file is the one place the two meet: it upgrades the level filtration to a **topological** statement.

The two headline results are

* `isOpen_ker_galoisRepMod` — `ker (galoisRepMod n)` is **open**, provided `E[n]` is finite;
* `isClosed_ker_galoisRepTwo` — `ker ρ_{E,2}` is **closed**, unconditionally over an algebraically
  closed field of characteristic `≠ 2`, and `isClosed_ker_galoisRepThree` — the same at `ℓ = 3`,
  where `(3 : F) ≠ 0` is needed as well.

## Why finiteness is the hinge, and where it comes from

`σ` lies in `ker (galoisRepMod n)` exactly when it fixes every point of `E[n]`, so that kernel is
the intersection of the stabilisers of the points of `E[n]`
(`ker_galoisRepMod_eq_iInter_stabilizer`). Each stabiliser is open. An **arbitrary** intersection of
open sets is only closed; a **finite** one is open. So the whole content of the openness statement
is that `E[n]` is finite, and the whole reason `ker ρ_ℓ` is *not* claimed open is that the
intersection over all levels `k` is genuinely infinite.

That contrast is not decoration — it is the mathematics. `ρ_{E,2}` is continuous
(`continuous_galoisRep`) without being locally constant, and the two theorems above are precisely
where the difference shows up: locally constant at each finite level
(`isLocallyConstant_galoisRepMod`), only continuous in the limit.

At `ℓ = 2` the finiteness input is unconditional: `EllipticCurves.Torsion.TwoPrimary` proves
`finite_torsion_two_pow` from the count `#E[2^k] = 4^k`, which comes from the tangent-line doubling
shortcut and needs neither the elliptic-net recurrence nor the coordinate formula
`x(nP) = Φₙ/ΨSqₙ`. ⚠️ The clause this paragraph used to carry — *"For odd `ℓ` the finiteness of
`E[ℓ^k]` is still open"* — is false at `ℓ = 3` and was already false when it was written:
`finite_torsion_three_pow` (`EllipticCurves.Torsion.ThreePrimary`) proves it from `#E[3^k] = 9^k`,
at the price of the coordinate formula at `n = 3` and of `(3 : F) ≠ 0`. It remains open for every
prime `ℓ ≥ 5`. Either way `isOpen_ker_galoisRepMod` carries finiteness as a hypothesis rather than
assuming it away, so the general statement applies verbatim at each `ℓ` where it is discharged.

⚠️ **That last sentence is now cashed rather than promised.** The `§ Every 3-smooth level` section
below discharges the hypothesis at `3 ^ k` (`finite_torsion_three_pow`) and, more generally, at
every `3`-smooth `n ≠ 0` (`finite_torsion_of_smooth`, `EllipticCurves.Torsion.Multiplicative`).
Nothing new is proved there: each of the four statements is one application of a theorem in this
file to a theorem in `EllipticCurves.Torsion`.

## What this file does not do

It says nothing about the *Tate module* as a topological space: compactness and profiniteness of
`T_ℓ E` are a separate matter, and this file neither needs them nor supplies them. It also does not
claim `ker ρ_{E,2}` is open — it is not, in general — nor anything about the image of `ρ_ℓ`, whose
openness would be a statement about `F / S` that nothing here bears on. ⚠️ **That disclaimer covers
the `3`-smooth statements below verbatim.** Openness of every *level* kernel is exactly what
`ker ρ_ℓ = ⨅ k, ker (galoisRepMod (ℓ ^ k))` fails to inherit — an infinite intersection of open
subgroups is closed and no more — so widening the set of levels at which the level kernels are known
open moves `ker ρ_ℓ` not at all. Continuity of
`galoisRepMatrixTwo b` into `GL₂(ℤ_[2])` with its `2`-adic topology is not proved here either, but
it *is* available — `continuous_galoisRepMatrixTwo` in
`EllipticCurves.TateModule.MatrixContinuity`, for an arbitrary basis. An earlier version of this
docstring said it needed a basis compatible with the level filtration; that was wrong.

## On non-vacuity

Every statement here is true when `G = F ≃ₐ[S] F` is trivial, and no theorem about `G` alone can
exclude that — it is a fact about the extension `F / S`, not about the curve. What the file *does*
discriminate is the degenerate reading in which the finiteness hypothesis is doing no work: it is,
and the evidence is internal. The same argument that yields `IsOpen` at a finite level yields only
`IsClosed` in the limit, and both are stated. If finiteness were idle, `isClosed_ker_galoisRepTwo`
could have been strengthened to `IsOpen` by the identical proof; it cannot.

The concrete input is `card_torsion_two_pow : Nat.card (E[2^k]) = 4^k`, so the index set of the
intersection in `ker_galoisRepMod_eq_iInter_stabilizer` really does grow with `k` — the level
conditions are a genuine descending tower of open subgroups (`ker_galoisRepMod_pow_antitone`), not a
constant sequence.

## Main statements

* `WeierstrassCurve.Affine.ker_galoisRepMod_eq_iInter_stabilizer` : the level kernel is the
  intersection of the stabilisers of the `n`-torsion points.
* `WeierstrassCurve.Affine.isOpen_ker_galoisRepMod`,
  `WeierstrassCurve.Affine.openSubgroupKerGaloisRepMod` : it is open when `E[n]` is finite.
* `WeierstrassCurve.Affine.isLocallyConstant_galoisRepMod` : the mod-`n` representation is locally
  constant.
* `WeierstrassCurve.Affine.isOpen_ker_galoisRepMod_two_pow`,
  `WeierstrassCurve.Affine.isLocallyConstant_galoisRepMod_two_pow` : unconditional at `ℓ = 2`.
* `WeierstrassCurve.Affine.isClosed_ker_galoisRepTwo` : `ker ρ_{E,2}` is closed.
* `WeierstrassCurve.Affine.isOpen_ker_galoisRepMod_smooth`,
  `WeierstrassCurve.Affine.isLocallyConstant_galoisRepMod_smooth` : the same at every `3`-smooth
  `n ≠ 0`, over a field in which `2` and `3` are invertible and with **no `[IsAlgClosed F]`**.
* `WeierstrassCurve.Affine.isOpen_ker_galoisRepMod_three_pow`,
  `WeierstrassCurve.Affine.isLocallyConstant_galoisRepMod_three_pow` : the `ℓ = 3` layer.
* `WeierstrassCurve.Affine.isClosed_ker_galoisRepThree` : `ker ρ_{E,3}` is closed.

## References

* [J. H. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.7 and VII.7.
-/

open scoped WeierstrassCurve.Affine.ProfiniteTopology

namespace WeierstrassCurve.Affine

variable {S F : Type*} [Field S] [Field F] [DecidableEq F] [Algebra S F] {W' : Affine S}

/-- **The kernel of the mod-`n` representation is the intersection of the stabilisers of the
`n`-torsion points.** An automorphism acts trivially on `E[n]` exactly when it fixes each of its
points, and fixing a point of the subtype is fixing the underlying point of `E(F)`.

No topology and no finiteness: this is `mem_ker_galoisRepMod_iff` rewritten as a set identity, and
it is the bridge every statement below crosses. -/
theorem ker_galoisRepMod_eq_iInter_stabilizer (n : ℕ) :
    ((galoisRepMod (W' := W') (F := F) n).ker : Set (F ≃ₐ[S] F))
      = ⋂ P : (W'⁄F).torsion n,
          (MulAction.stabilizer (F ≃ₐ[S] F) ((P : (W'⁄F).Point)) : Set (F ≃ₐ[S] F)) := by
  ext σ
  simp only [SetLike.mem_coe, Set.mem_iInter, MulAction.mem_stabilizer_iff,
    mem_ker_galoisRepMod_iff]
  exact ⟨fun h P => congrArg Subtype.val (h P), fun h P => Subtype.ext (h P)⟩

variable [Algebra.IsIntegral S F]

/-- **The level kernels are open.** `ker (galoisRepMod n)` is an intersection of open stabilisers
indexed by `E[n]`; when `E[n]` is finite the intersection is finite, hence open.

Finiteness is load-bearing and is the only hypothesis beyond what `Point.isOpen_stabilizer` needs.
Drop it and the argument still gives a *closed* subgroup — a countable intersection of open sets
need not be open, and `ker ρ_ℓ` itself is the standard example (`isClosed_ker_galoisRepTwo`). -/
theorem isOpen_ker_galoisRepMod (n : ℕ) (hfin : Finite ((W'⁄F).torsion n)) :
    IsOpen ((galoisRepMod (W' := W') (F := F) n).ker : Set (F ≃ₐ[S] F)) := by
  haveI := hfin
  rw [ker_galoisRepMod_eq_iInter_stabilizer]
  exact isOpen_iInter_of_finite fun P => Point.isOpen_stabilizer _

/-- `ker (galoisRepMod n)` packaged as an `OpenSubgroup`, which is the form the Krull-topology API
consumes (it is where `OpenSubgroup.isClosed` comes from, used below). -/
noncomputable def openSubgroupKerGaloisRepMod (n : ℕ) (hfin : Finite ((W'⁄F).torsion n)) :
    OpenSubgroup (F ≃ₐ[S] F) where
  toSubgroup := (galoisRepMod (W' := W') (F := F) n).ker
  isOpen' := isOpen_ker_galoisRepMod n hfin

/-- **Each level representation is locally constant**: it is constant on the cosets of its kernel,
which is an open subgroup.

This is the concrete form of "`ρ` is continuous with open kernel", and it is the property that
`ρ_ℓ` itself does *not* have — see the module docstring. -/
theorem isLocallyConstant_galoisRepMod (n : ℕ) (hfin : Finite ((W'⁄F).torsion n)) :
    IsLocallyConstant (galoisRepMod (W' := W') (F := F) n) := by
  rw [IsLocallyConstant.iff_isOpen_fiber_apply]
  intro σ₀
  have h : (galoisRepMod (W' := W') (F := F) n) ⁻¹' {galoisRepMod n σ₀}
      = (fun τ : F ≃ₐ[S] F => σ₀ * τ) ''
          ((galoisRepMod (W' := W') (F := F) n).ker : Set (F ≃ₐ[S] F)) := by
    ext σ
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_image, SetLike.mem_coe,
      MonoidHom.mem_ker]
    refine ⟨fun hσ => ⟨σ₀⁻¹ * σ, ?_, mul_inv_cancel_left σ₀ σ⟩, ?_⟩
    · rw [map_mul, map_inv, hσ, inv_mul_cancel]
    · rintro ⟨τ, hτ, rfl⟩
      rw [map_mul, hτ, mul_one]
  rw [h]
  exact (Homeomorph.mulLeft σ₀).isOpenMap _ (isOpen_ker_galoisRepMod n hfin)

/-! ### The unconditional `ℓ = 2` layer -/

section Two

variable [IsAlgClosed F] [(W'⁄F).IsElliptic]

/-- **The level kernels of `ρ_{E,2}` are open**, unconditionally over an algebraically closed field
of characteristic `≠ 2`: `finite_torsion_two_pow` discharges the finiteness hypothesis, and it does
so without the division polynomials. -/
theorem isOpen_ker_galoisRepMod_two_pow (h2 : (2 : F) ≠ 0) (k : ℕ) :
    IsOpen ((galoisRepMod (W' := W') (F := F) (2 ^ k)).ker : Set (F ≃ₐ[S] F)) :=
  isOpen_ker_galoisRepMod _ (finite_torsion_two_pow h2 k)

/-- Each mod-`2^k` representation is locally constant, unconditionally. -/
theorem isLocallyConstant_galoisRepMod_two_pow (h2 : (2 : F) ≠ 0) (k : ℕ) :
    IsLocallyConstant (galoisRepMod (W' := W') (F := F) (2 ^ k)) :=
  isLocallyConstant_galoisRepMod _ (finite_torsion_two_pow h2 k)

/-- **`ker ρ_{E,2}` is closed.** By the level filtration of `EllipticCurves.TateModule.Kernel` it is
`⨅ k, ker (galoisRepMod (2^k))`, a countable intersection of open — hence also closed — subgroups.

It is **not** claimed open, and in general it is not: `ρ_{E,2}` is continuous without being locally
constant, the same phenomenon `tateModule.isClosed_stabilizer` records for stabilisers in `T₂E`.
This is the shape the Néron–Ogg–Shafarevich criterion consumes — "the inertia group acts trivially
on `T₂E`" is a closed condition, cut out by the open congruence conditions at each level. -/
theorem isClosed_ker_galoisRepTwo (h2 : (2 : F) ≠ 0) :
    IsClosed ((galoisRep (W' := W') (F := F) 2).ker : Set (F ≃ₐ[S] F)) := by
  rw [ker_galoisRepTwo_eq_iInf h2, Subgroup.coe_iInf]
  exact isClosed_iInter fun k => OpenSubgroup.isClosed (openSubgroupKerGaloisRepMod (2 ^ k)
    (finite_torsion_two_pow h2 k))

end Two

/-! ### Every `3`-smooth level, and no algebraic closure

⚠️ The two `_smooth` statements below sit **outside** any `[IsAlgClosed F]` block, and that is a
measurement rather than a preference: their finiteness input `finite_torsion_of_smooth`
(`EllipticCurves.Torsion.Multiplicative`) descends from `#E[2] ≤ 4` and `#E[3] ≤ 9`, which are
bounds over an arbitrary field. The `2 ^ k` and `3 ^ k` layers do **not** share that property —
their inputs `finite_torsion_two_pow` and `finite_torsion_three_pow` come from the *exact* counts
`4 ^ k` and `9 ^ k`, and those are stated under `[IsAlgClosed F]`.

⚠️ Measured, not assumed. Putting `omit [IsAlgClosed F] in` on `isOpen_ker_galoisRepMod_two_pow`
above gives

```
error(lean.synthInstanceFailed): failed to synthesize instance of type class
  IsAlgClosed F
```

so the `ℓ = 2` layer really does use the instance and does not move out of its section. Conversely
the `unusedSectionVars` linter is what says the two `_smooth` statements do not: written inside an
`[IsAlgClosed F]` block they draw *"automatically included section variable(s) unused"*, which is
why they are outside one.
-/

section Smooth

variable [(W'⁄F).IsElliptic]

/-- **The level kernels are open at every `3`-smooth `n ≠ 0`**, over a field in which `2` and `3`
are invertible — and with **no algebraic closure**.

⚠️ This does **not** subsume `isOpen_ker_galoisRepMod_two_pow`, even though `2 ^ k` is `3`-smooth:
this statement needs `h3` and that one does not. Neither implies the other, so both are kept.

⚠️ **Deletion test**, measured on this file as committed. Replacing the finiteness argument by a
hole — `by refine isOpen_ker_galoisRepMod (W' := W') (F := F) _ ?_` — leaves:

```
error: unsolved goals
S : Type u_1
F : Type u_2
inst✝⁵ : Field S
inst✝⁴ : Field F
inst✝³ : DecidableEq F
inst✝² : Algebra S F
W' : Affine S
inst✝¹ : Algebra.IsIntegral S F
inst✝ : WeierstrassCurve.IsElliptic W'⁄F
h2 : 2 ≠ 0
h3 : 3 ≠ 0
n : ℕ
hn : n ≠ 0
hfac : ∀ p ∈ n.primeFactors, p = 2 ∨ p = 3
⊢ Finite ↥((W'⁄F).torsion n)
```

Two mechanical changes accompany the deletion and neither adds information: term mode becomes
`by refine … ?_` so a hole is legal, and `W'`/`F` are pinned, which the term-mode form infers from
the expected type. ⚠️ `h2`, `h3`, `hn` and `hfac` all **survive** in the context, so what is removed
is a construction and not a hypothesis; and the residual is a **goal**, which no type mismatch could
produce. It is exactly the finiteness input, which is what makes openness non-trivial: without it
the same argument yields only `IsClosed`. -/
theorem isOpen_ker_galoisRepMod_smooth (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) {n : ℕ} (hn : n ≠ 0)
    (hfac : ∀ p ∈ n.primeFactors, p = 2 ∨ p = 3) :
    IsOpen ((galoisRepMod (W' := W') (F := F) n).ker : Set (F ≃ₐ[S] F)) :=
  isOpen_ker_galoisRepMod _ (finite_torsion_of_smooth h2 h3 hn hfac)

/-- **Each mod-`n` representation is locally constant at every `3`-smooth `n ≠ 0`**, with no
algebraic closure.

This is the statement `EllipticCurves.TateModule.Continuity.continuous_galoisRepMod` explicitly
declines to make; its docstring says, copy-paste, that local constancy of the representation itself
*"would need `E[n]` to be finite"*. At a `3`-smooth `n` it now is, and that sentence remains correct
about what is needed.

⚠️ The same deletion test run on this statement gives the **identical** residual goal
`⊢ Finite ↥((W'⁄F).torsion n)` under the identical hypothesis list, measured — the two `_smooth`
statements consume the same input through the same argument slot. -/
theorem isLocallyConstant_galoisRepMod_smooth (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) {n : ℕ}
    (hn : n ≠ 0) (hfac : ∀ p ∈ n.primeFactors, p = 2 ∨ p = 3) :
    IsLocallyConstant (galoisRepMod (W' := W') (F := F) n) :=
  isLocallyConstant_galoisRepMod _ (finite_torsion_of_smooth h2 h3 hn hfac)

end Smooth

section Three

variable [IsAlgClosed F] [(W'⁄F).IsElliptic]

/-- **The level kernels of `ρ_{E,3}` are open**, over an algebraically closed field in which `2` and
`3` are invertible: `finite_torsion_three_pow` discharges the finiteness hypothesis.

⚠️ Unlike its `ℓ = 2` twin this one **does** consume the multiplication-by-`n` coordinate formula,
at `n = 3`: `card_torsion_three_pow` reaches `#E[3^k] = 9^k` through
`EllipticCurves.Torsion.TriplingSurjective`. The module docstring's sentence about `ℓ = 2` needing
neither the elliptic-net recurrence nor the coordinate formula is a claim about `ℓ = 2` and must not
be read here.

⚠️ **Deletion test**, same shape as `isOpen_ker_galoisRepMod_smooth`'s and measured on this file as
committed:

```
error: unsolved goals
S : Type u_1
F : Type u_2
inst✝⁶ : Field S
inst✝⁵ : Field F
inst✝⁴ : DecidableEq F
inst✝³ : Algebra S F
W' : Affine S
inst✝² : Algebra.IsIntegral S F
inst✝¹ : IsAlgClosed F
inst✝ : WeierstrassCurve.IsElliptic W'⁄F
h2 : 2 ≠ 0
h3 : 3 ≠ 0
k : ℕ
⊢ Finite ↥((W'⁄F).torsion (3 ^ k))
```

⚠️ Note `inst✝¹ : IsAlgClosed F` in this context and its **absence** from the `_smooth` one above.
That is the asymmetry this section's header records, visible in the two goal states. -/
theorem isOpen_ker_galoisRepMod_three_pow (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) (k : ℕ) :
    IsOpen ((galoisRepMod (W' := W') (F := F) (3 ^ k)).ker : Set (F ≃ₐ[S] F)) :=
  isOpen_ker_galoisRepMod _ (finite_torsion_three_pow h2 h3 k)

/-- Each mod-`3^k` representation is locally constant. The deletion test gives the identical
residual goal `⊢ Finite ↥((W'⁄F).torsion (3 ^ k))` as `isOpen_ker_galoisRepMod_three_pow`,
measured. -/
theorem isLocallyConstant_galoisRepMod_three_pow (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) (k : ℕ) :
    IsLocallyConstant (galoisRepMod (W' := W') (F := F) (3 ^ k)) :=
  isLocallyConstant_galoisRepMod _ (finite_torsion_three_pow h2 h3 k)

/-- **`ker ρ_{E,3}` is closed.** By `ker_galoisRepThree_eq_iInf`
(`EllipticCurves.TateModule.Kernel`) it is `⨅ k, ker (galoisRepMod (3^k))`, a countable
intersection of open — hence also closed — subgroups.

⚠️ **Both `h2` and `h3` are needed, and they enter through different doors.** `h2` alone gives the
level filtration, because `nsmul_three_surjective` needs nothing more; `h3` is what
`finite_torsion_three_pow` needs to make each level kernel *open*. Its `ℓ = 2` twin
`isClosed_ker_galoisRepTwo` carries only `h2` because at `ℓ = 2` both doors open with it.

It is **not** claimed open, and in general it is not — see `isClosed_ker_galoisRepTwo` for the
reason, which is insensitive to `ℓ`. -/
theorem isClosed_ker_galoisRepThree (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) :
    IsClosed ((galoisRep (W' := W') (F := F) 3).ker : Set (F ≃ₐ[S] F)) := by
  rw [ker_galoisRepThree_eq_iInf h2, Subgroup.coe_iInf]
  exact isClosed_iInter fun k => OpenSubgroup.isClosed (openSubgroupKerGaloisRepMod (3 ^ k)
    (finite_torsion_three_pow h2 h3 k))

end Three

end WeierstrassCurve.Affine
