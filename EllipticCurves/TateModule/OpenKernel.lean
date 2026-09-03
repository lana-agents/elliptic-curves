/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import EllipticCurves.Fixtures
import EllipticCurves.TateModule.Continuity
import EllipticCurves.TateModule.Kernel
import EllipticCurves.Torsion.Multiplicative
import EllipticCurves.Torsion.ThreePrimary
import EllipticCurves.Torsion.TwoPrimary
import EllipticCurves.Torsion.XSupport
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
at the price of the coordinate formula at `n = 3` and of `(3 : F) ≠ 0`. ⚠️ **And the sentence that
followed — *"it remains open for every prime `ℓ ≥ 5`"* — is false too, and was false long before it
was written here.** `finite_torsion_of_intCast_ne_zero` (`EllipticCurves.Torsion.XSupport`) gives
`Finite (E[n])` at **every** `n` with `(n : F) ≠ 0`, from `(2 : F) ≠ 0` alone; nothing in this file
consumed it until the `§ Every level prime to the characteristic` section below did. Either way
`isOpen_ker_galoisRepMod` carries finiteness as a hypothesis rather than assuming it away, so the
general statement applies verbatim at each `n` where it is discharged.

⚠️ **That last sentence is cashed rather than promised, at four different widths.** The sections
below discharge the hypothesis at `2 ^ k` (`finite_torsion_two_pow`), at `3 ^ k`
(`finite_torsion_three_pow`), at every `3`-smooth `n ≠ 0` (`finite_torsion_of_smooth`,
`EllipticCurves.Torsion.Multiplicative`), and — widest, and needing neither `[IsAlgClosed F]` nor
`[(W'⁄F).IsElliptic]` — at every `n` with `(2 : F) ≠ 0` and `(n : F) ≠ 0`
(`finite_torsion_of_intCast_ne_zero`). ⚠️ **`(2 : F) ≠ 0` is a hypothesis of the widest one too,
and this sentence used to name only the index condition**; it is not a fourth width, it is the
second hypothesis of the fourth. ⚠️ **Nothing new is proved in any of them**: each statement
is one application of a theorem in this file to a theorem in `EllipticCurves.Torsion`. The four
routes to finiteness are genuinely different, which is why the narrower three are kept rather than
deleted — see the `§ Every level prime to the characteristic` header.

## What this file does not do

It says nothing about the *Tate module* as a topological space: compactness and profiniteness of
`T_ℓ E` are a separate matter, and this file neither needs them nor supplies them. It also does not
claim `ker ρ_{E,2}` is open — it is not, in general — nor anything about the image of `ρ_ℓ`, whose
openness would be a statement about `F / S` that nothing here bears on. ⚠️ **That disclaimer covers
the `3`-smooth statements below verbatim, and the general ones with them.** Openness of every
*level* kernel is exactly what
`ker ρ_ℓ = ⨅ k, ker (galoisRepMod (ℓ ^ k))` fails to inherit — an infinite intersection of open
subgroups is closed and no more — so widening the set of levels at which the level kernels are
known open moves `ker ρ_ℓ` not at all. ⚠️ That is why
`isOpen_ker_galoisRepMod_of_natCast_ne_zero`, which reaches every level prime to the
characteristic, still yields only `IsClosed (ker ρ_{E,ℓ})`
(`EllipticCurves.TateModule.OpenKernelGeneral`) and not `IsOpen`. Continuity of
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

⚠️ **The general layer adds concrete certificates on top of that internal argument, and they answer
three different risks.** `§ Non-vacuity for the general layer` compiles the hypotheses of
`isOpen_ker_galoisRepMod_of_natCast_ne_zero` at `n = 10` and `n = 91` over `F = ℚ` — indices no
statement in this file carrying `[IsAlgClosed F]` or `[(W'⁄F).IsElliptic]` reaches, and which
nothing in this file other than the two `_of_natCast_ne_zero` theorems reaches without a `Finite`
hypothesis supplied by hand, over a field that is not algebraically closed — and then again at
`n = 10` over `AlgClosedQ`, where the Galois group is **not** trivial, and at `n = 91` on a curve
whose `IsElliptic` instance is provably unavailable. The `ℚ` pair is labelled
*hypothesis-inhabitation* rather than non-vacuity, precisely because `ℚ ≃ₐ[ℚ] ℚ` is trivial and
openness is free there; no certificate answers another's risk.

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
* `WeierstrassCurve.Affine.isOpen_ker_galoisRepMod_of_natCast_ne_zero`,
  `WeierstrassCurve.Affine.isLocallyConstant_galoisRepMod_of_natCast_ne_zero` : the same at
  **every** `n` with `(2 : F) ≠ 0` and `(n : F) ≠ 0`, with **no `[IsAlgClosed F]`** and **no
  `[(W'⁄F).IsElliptic]`** — the widest form, and the one that subsumes the three below at the
  level of indices.
* `WeierstrassCurve.Affine.isOpen_ker_galoisRepMod_two_pow`,
  `WeierstrassCurve.Affine.isLocallyConstant_galoisRepMod_two_pow` : unconditional **in the
  exponent** at `ℓ = 2` — every `2 ^ k`, with no side condition on `k` — over an algebraically
  closed field with `(2 : F) ≠ 0` and `[(W'⁄F).IsElliptic]`.
* `WeierstrassCurve.Affine.isClosed_ker_galoisRepTwo` : `ker ρ_{E,2}` is closed.
* `WeierstrassCurve.Affine.isOpen_ker_galoisRepMod_smooth`,
  `WeierstrassCurve.Affine.isLocallyConstant_galoisRepMod_smooth` : the same at every `3`-smooth
  `n ≠ 0`, over a field in which `2` and `3` are invertible, under `[(W'⁄F).IsElliptic]` and with
  **no `[IsAlgClosed F]`**.
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

/-! ### Every level prime to the characteristic

⚠️ **This is the widest layer in the file, and it needs the least.**
`finite_torsion_of_intCast_ne_zero` (`EllipticCurves.Torsion.XSupport`) proves `Finite (E[n])`
from `(2 : F) ≠ 0` and `(n : F) ≠ 0` **alone** — no algebraic closure, no
`[(W'⁄F).IsElliptic]`, no smoothness of `n`, and no exact count. Feeding it to
`isOpen_ker_galoisRepMod` widens the level-kernel statements in **two**
directions at once: from `3`-smooth indices to every index prime to the characteristic, and from
the instance list of the sections below to none of it.

The two statements here therefore sit outside `section Two`, `section Smooth` and `section Three`,
in the same region as `isOpen_ker_galoisRepMod` itself: the only ambient hypotheses are the
`Field`/`Algebra` basics and `[Algebra.IsIntegral S F]`, which `Point.isOpen_stabilizer` needs.

⚠️ **The three earlier layers are kept, and none of them is dead.** They reach their indices by
genuinely different routes — `finite_torsion_two_pow` through the tangent-line doubling count,
`finite_torsion_three_pow` through `x(3P) = Φ₃/Ψ₃²`, `finite_torsion_of_smooth` through
multiplicativity off `#E[2] ≤ 4` and `#E[3] ≤ 9` — where the statements here route through the
`x`-support root count of `ΨSqₙ`. Independent routes to one conclusion are the cheapest available
cross-check on both, and `isClosed_ker_galoisRepTwo` / `isClosed_ker_galoisRepThree` consume
`finite_torsion_two_pow` / `finite_torsion_three_pow` by name.
-/

/-- **The level kernels are open at every `n` with `(n : F) ≠ 0`**, over a field in which `2` is
invertible — with **no algebraic closure** and **no `[(W'⁄F).IsElliptic]`**.

⚠️ `(n : F) ≠ 0` is the same condition as `char F ∤ n`, stated in the form
`finite_torsion_of_intCast_ne_zero` takes it, and it is sharp in the sense that at `char F ∣ n` the
finiteness input is not available from this route at all.

This subsumes `isOpen_ker_galoisRepMod_two_pow` and `isOpen_ker_galoisRepMod_three_pow` at the
level of indices, and subsumes `isOpen_ker_galoisRepMod_smooth` modulo the factorisation argument
`Nat.natCast_ne_zero_of_smooth` (`EllipticCurves.Torsion.ThreePrimary`) — which is proved rather
than asserted, and the subsumption is then machine-checked by the `example` below. ⚠️ None of the
three is deleted; see the section header.

⚠️ **Deletion test**, measured on this file as committed. Replacing the finiteness argument by a
hole — `by refine isOpen_ker_galoisRepMod (W' := W') (F := F) _ ?_` — leaves

```
error: unsolved goals
S : Type u_1
F : Type u_2
inst✝⁴ : Field S
inst✝³ : Field F
inst✝² : DecidableEq F
inst✝¹ : Algebra S F
W' : Affine S
inst✝ : Algebra.IsIntegral S F
h2 : 2 ≠ 0
n : ℕ
hn : ↑n ≠ 0
⊢ Finite ↥((W'⁄F).torsion n)
```

⚠️ `h2` and `hn` both **survive** and the residual is a **goal**, not a type mismatch, so what the
deletion removes is a construction rather than a hypothesis. ⚠️ Compare the same residual in
`isOpen_ker_galoisRepMod_smooth`'s docstring: there the context carries
`inst✝ : WeierstrassCurve.IsElliptic W'⁄F` and here it does not.

⚠️ **That absence is evidence and not proof, and the difference has bitten this front before.** A
goal state shows the instance is not in the context; it does not show that none exists. The
`cuspQ` certificate in `§ Non-vacuity for the general layer` is the stronger form — it applies both
theorems to a curve on which `IsElliptic` is *provably false* — and it is where a reader should
look for the second half of the widening. -/
theorem isOpen_ker_galoisRepMod_of_natCast_ne_zero (h2 : (2 : F) ≠ 0) {n : ℕ} (hn : (n : F) ≠ 0) :
    IsOpen ((galoisRepMod (W' := W') (F := F) n).ker : Set (F ≃ₐ[S] F)) :=
  isOpen_ker_galoisRepMod _ (finite_torsion_of_intCast_ne_zero h2 hn)

/-- **Each mod-`n` representation is locally constant at every `n` with `(n : F) ≠ 0`**, over a
field in which `2` is invertible — with no algebraic closure and no `[(W'⁄F).IsElliptic]`.

This is the statement `EllipticCurves.TateModule.Continuity.continuous_galoisRepMod` explicitly
declines to make; its docstring says, copy-paste, that local constancy of the representation itself
*"would need `E[n]` to be finite"*. At every `n` prime to the characteristic it now is, and that
sentence remains correct about what is needed.

⚠️ The deletion test gives the **identical** residual goal `⊢ Finite ↥((W'⁄F).torsion n)` under the
identical hypothesis list as `isOpen_ker_galoisRepMod_of_natCast_ne_zero`, measured — the two
statements consume the same input through the same argument slot. -/
theorem isLocallyConstant_galoisRepMod_of_natCast_ne_zero (h2 : (2 : F) ≠ 0) {n : ℕ}
    (hn : (n : F) ≠ 0) : IsLocallyConstant (galoisRepMod (W' := W') (F := F) n) :=
  isLocallyConstant_galoisRepMod _ (finite_torsion_of_intCast_ne_zero h2 hn)

/-- **The subsumption of `isOpen_ker_galoisRepMod_smooth`, machine-checked** — and with
`[(W'⁄F).IsElliptic]` dropped, which is why this `example` lives here rather than in
`section Smooth`. The statement below is `isOpen_ker_galoisRepMod_smooth`'s verbatim, minus that
instance; it is proved from `isOpen_ker_galoisRepMod_of_natCast_ne_zero` and the factorisation
lemma `Nat.natCast_ne_zero_of_smooth` (`EllipticCurves.Torsion.ThreePrimary`, which this file
imports directly).

⚠️ **That lemma used to be a `private theorem` in this file** (`#1552`): the `(n : K) ≠ 0` and
`((n : ℤ) : K) ≠ 0` forms of one four-line argument had grown **eight** `private` copies across
`TateModule/` and `FunctionField/`, and this was the last of them. It is proved rather than
asserted either way; only its address changed.

⚠️ This is what turns *"subsumes the `3`-smooth layer"* from a docstring claim into a compiled
one. `isOpen_ker_galoisRepMod_smooth` is nevertheless kept, for the independent-route reason in the
section header. -/
example (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) {n : ℕ} (hn : n ≠ 0)
    (hfac : ∀ p ∈ n.primeFactors, p = 2 ∨ p = 3) :
    IsOpen ((galoisRepMod (W' := W') (F := F) n).ker : Set (F ≃ₐ[S] F)) :=
  isOpen_ker_galoisRepMod_of_natCast_ne_zero h2 (Nat.natCast_ne_zero_of_smooth h2 h3 hn hfac)

/-! ### The unconditional `ℓ = 2` layer -/

section Two

variable [IsAlgClosed F] [(W'⁄F).IsElliptic]

/-- **The level kernels of `ρ_{E,2}` are open at every exponent `k`** — unconditional in `k`, and
otherwise over an algebraically closed field with `(2 : F) ≠ 0` and `[(W'⁄F).IsElliptic]`:
`finite_torsion_two_pow` discharges the finiteness hypothesis, and it does so without the division
polynomials. -/
theorem isOpen_ker_galoisRepMod_two_pow (h2 : (2 : F) ≠ 0) (k : ℕ) :
    IsOpen ((galoisRepMod (W' := W') (F := F) (2 ^ k)).ker : Set (F ≃ₐ[S] F)) :=
  isOpen_ker_galoisRepMod _ (finite_torsion_two_pow h2 k)

/-- **Each mod-`2^k` representation is locally constant at every exponent `k`** — unconditional in
`k`, and otherwise over an algebraically closed field with `(2 : F) ≠ 0` and
`[(W'⁄F).IsElliptic]`. -/
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

⚠️ **This is no longer the widest layer in the file** — `§ Every level prime to the characteristic`
above reaches every `n` with `(2 : F) ≠ 0` and `(n : F) ≠ 0`, and needs neither `[IsAlgClosed F]`
nor `[(W'⁄F).IsElliptic]`. The two statements here are kept because their finiteness input is a
genuinely different theorem (multiplicativity off `#E[2] ≤ 4` and `#E[3] ≤ 9`, versus the
`x`-support root count of `ΨSqₙ`), and the containment of indices is proved rather than asserted:
see `Nat.natCast_ne_zero_of_smooth` (`EllipticCurves.Torsion.ThreePrimary`) and the `example` that
consumes it in `§ Every level prime to the characteristic`.

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
*"would need `E[n]` to be finite"*. At a `3`-smooth `n` it now is — and, more widely, at every `n`
with `(2 : F) ≠ 0` and `(n : F) ≠ 0` (`isLocallyConstant_galoisRepMod_of_natCast_ne_zero`) — and
that sentence remains correct about what is needed. ⚠️ The quotation is unchanged and is
re-checked against `EllipticCurves.TateModule.Continuity` as committed; only the qualifier moved.

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

/-! ### Non-vacuity for the general layer

⚠️ **Three different risks, three different certificates, and none of them answers another's.**

* The `ℚ`-only pair below is a **hypothesis-inhabitation** certificate: it shows that the shortened
  hypothesis list of `isOpen_ker_galoisRepMod_of_natCast_ne_zero` is satisfiable at indices no
  statement in this file carrying `[IsAlgClosed F]` or `[(W'⁄F).IsElliptic]` reaches — `n = 10` is
  even but not `3`-smooth, `n = 91 = 7 · 13` is neither — over a field that is **not algebraically
  closed** and with no `[IsAlgClosed F]` anywhere. ⚠️ **Scope the claim that way and no wider.**
  `isOpen_ker_galoisRepMod`, the hypothesis form at the top of this file, reaches both indices over
  `ℚ` already, and it is what the new theorem is one line away from; what the new theorem removes
  is the `Finite` hypothesis, not the index. ⚠️ It says nothing about the Galois group either:
  `ℚ ≃ₐ[ℚ] ℚ` is trivial, so *"that subgroup is open"* is free there. That is exactly why it is not
  the only one.
* The `AlgClosedQ` certificate answers the second risk: `Gal(ℚ̄/ℚ)` is not trivial, and the level
  kernel is open there too, again at `n = 10`.
* ⚠️ **The `cuspQ` certificate answers a third risk, and it is the one this front keeps getting
  wrong: an *absent* instance and an *unavailable* one are different things.** The two theorems
  above are advertised as needing neither `[IsAlgClosed F]` nor `[(W'⁄F).IsElliptic]`, and the
  deletion-test transcript in `isOpen_ker_galoisRepMod_of_natCast_ne_zero`'s docstring shows only
  that the `IsElliptic` instance is not *in the context*. `cuspQ` is `y² = x³`, whose `Δ` is `0`,
  so `(cuspQ⁄ℚ).IsElliptic` is **provably false** and no such instance can be silently supplying
  anything. That is a certificate rather than a goal state, and it is shorter.

⚠️ The `Algebra ℚ AlgClosedQ` instance trap applies as everywhere on this front: the integrality
instance is supplied as a `private lemma` and introduced with `haveI` at the point of use rather
than registered. See `EllipticCurves.Fixtures`.
-/

section Nonvacuity

open EllipticCurves.Fixture

private lemma exampleIsIntegralLevel : Algebra.IsIntegral ℚ AlgClosedQ := by
  have : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) := by
    rw [show (DivisionRing.toRatAlgebra : Algebra ℚ (AlgebraicClosure ℚ))
        = AlgebraicClosure.instAlgebra ℚ from Subsingleton.elim _ _]
    infer_instance
  infer_instance

private lemma exampleTenAlgClosed : ((10 : ℕ) : AlgClosedQ) ≠ 0 := by
  have : ((10 : ℕ) : AlgClosedQ) = 10 := by push_cast; ring
  rw [this]; norm_num

open Classical in
/-- **⚠️ HYPOTHESIS-INHABITATION, NOT NON-VACUITY**, and the label is the point: `ℚ ≃ₐ[ℚ] ℚ` is
trivial, so openness of a subgroup of it is free. What this certifies is the *index* and the
*hypothesis list* — `n = 10` is even and not `3`-smooth, `n = 91 = 7 · 13` is neither, and the
ambient field is `ℚ`, which is not algebraically closed. **No statement in this file carrying
`[IsAlgClosed F]` or `[(W'⁄F).IsElliptic]` reaches either index over any field**, which is the
claim the `AlgClosedQ` certificate below already states correctly by naming
`isOpen_ker_galoisRepMod_two_pow`, `_three_pow` and `_smooth`.

⚠️ **Do not widen that to *"no statement above this section reaches these indices"* or to *"none of
them can be stated over `ℚ`"*; both are false and both were asserted here once.**
`isOpen_ker_galoisRepMod`, the hypothesis form at the top of this file, reaches `n = 10` over `ℚ`
— it is the very theorem this `example`'s own proof term passes through, one
`finite_torsion_of_intCast_ne_zero` away — and
`isOpen_ker_galoisRepMod_smooth` lives in `section Smooth`, which carries `[(W'⁄F).IsElliptic]` and
**not** `[IsAlgClosed F]`, so it is perfectly statable over `ℚ` (at `n = 4`, say). Compiled
falsifiers for both were exhibited when this sentence was corrected. -/
example : IsOpen ((galoisRepMod (W' := y2AddYEqX3 ℚ) (F := ℚ) 10).ker : Set (ℚ ≃ₐ[ℚ] ℚ)) ∧
    IsOpen ((galoisRepMod (W' := y2AddYEqX3 ℚ) (F := ℚ) 91).ker : Set (ℚ ≃ₐ[ℚ] ℚ)) :=
  ⟨isOpen_ker_galoisRepMod_of_natCast_ne_zero two_ne_zero (by norm_num),
    isOpen_ker_galoisRepMod_of_natCast_ne_zero two_ne_zero (by norm_num)⟩

open Classical in
/-- **The certificate over a non-trivial Galois group.** `Gal(ℚ̄/ℚ)` is not trivial, so this one is
not free the way the `ℚ`-only pair above is, and it is still at `n = 10` — an index neither
`isOpen_ker_galoisRepMod_two_pow` nor `isOpen_ker_galoisRepMod_three_pow` nor
`isOpen_ker_galoisRepMod_smooth` reaches. -/
example : IsOpen ((galoisRepMod (W' := y2AddYEqX3 ℚ) (F := AlgClosedQ) 10).ker :
    Set (AlgClosedQ ≃ₐ[ℚ] AlgClosedQ)) := by
  haveI := exampleIsIntegralLevel
  exact isOpen_ker_galoisRepMod_of_natCast_ne_zero two_ne_zero exampleTenAlgClosed

open Classical in
/-- Local constancy at the same index over the same non-trivial Galois group, so that the second
new statement is certified and not only the first. -/
example : IsLocallyConstant (galoisRepMod (W' := y2AddYEqX3 ℚ) (F := AlgClosedQ) 10) := by
  haveI := exampleIsIntegralLevel
  exact isLocallyConstant_galoisRepMod_of_natCast_ne_zero two_ne_zero exampleTenAlgClosed

/-- `y² = x³`, the cuspidal cubic, of discriminant `0`.

⚠️ **Deliberately not in `EllipticCurves.Fixtures`.** Every curve there is elliptic and is shared;
this one exists to be *non*-elliptic and has exactly one consumer, the certificate below. Move it
to `Fixtures` if and when a second file wants it. -/
private def cuspQ : Affine ℚ := ⟨0, 0, 0, 0, 0⟩

/-- **`(cuspQ⁄ℚ).IsElliptic` is false, not merely absent.** This is the hypothesis of the
certificate below, and proving it is the whole point: without it, that certificate would show only
that the instance is not supplied, which the deletion-test transcript above already shows. -/
private lemma not_isElliptic_cuspQ : ¬ (cuspQ⁄ℚ).IsElliptic := by
  intro h
  have := h.isUnit
  simp [cuspQ, WeierstrassCurve.baseChange, WeierstrassCurve.map, WeierstrassCurve.Δ,
    WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈] at this

open Classical in
/-- **⚠️ THE STRONG FORM OF THE SECOND WIDENING: both theorems on a singular curve, over a field
that is not algebraically closed, at `n = 91 = 7 · 13`.**

`not_isElliptic_cuspQ` above proves `(cuspQ⁄ℚ).IsElliptic` false, so **neither dropped instance can
be silently supplying anything here, because neither exists**. `n = 91` is odd and not `3`-smooth,
so no `_two_pow`, `_three_pow` or `_smooth` statement reaches it either.

⚠️ This is what the deletion-test transcript in
`isOpen_ker_galoisRepMod_of_natCast_ne_zero`'s docstring cannot do: an absent instance and an
unavailable one look identical in a goal state.

⚠️ **It answers only the instance question.** Like the `ℚ` pair above it says nothing about the
Galois group — `ℚ ≃ₐ[ℚ] ℚ` is trivial, so openness is free here too — and it makes no claim that
the level kernels are interesting on a cuspidal cubic. The `AlgClosedQ` certificate remains the
one that answers the Galois-group risk. -/
example : IsOpen ((galoisRepMod (W' := cuspQ) (F := ℚ) 91).ker : Set (ℚ ≃ₐ[ℚ] ℚ)) ∧
    IsLocallyConstant (galoisRepMod (W' := cuspQ) (F := ℚ) 91) :=
  ⟨isOpen_ker_galoisRepMod_of_natCast_ne_zero two_ne_zero (by norm_num),
    isLocallyConstant_galoisRepMod_of_natCast_ne_zero two_ne_zero (by norm_num)⟩

end Nonvacuity

end WeierstrassCurve.Affine
