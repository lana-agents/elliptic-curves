/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import EllipticCurves.Fixtures
import EllipticCurves.TateModule.Continuity
import EllipticCurves.TateModule.FreeThree
import EllipticCurves.TateModule.LevelStructure
import EllipticCurves.Torsion.TwoPrimary
import Mathlib.Topology.Algebra.Category.ProfiniteGrp.Basic

/-!
# `T_ℓ E` is profinite

`EllipticCurves.TateModule.Continuity` puts the inverse-limit topology on `T_ℓ E` — the subspace
topology it inherits from `ℕ → E(F)` with `E(F)` discrete — and proves that it is a Hausdorff,
totally disconnected topological group on which the Galois group acts continuously. It stops short
of **compactness**, and says so.

This file supplies the missing piece. It rests on two observations.

* `T_ℓ E` does not merely sit inside `ℕ → E(F)`, which is *not* compact because `E(F)` is infinite:
  it sits inside the much smaller product `∏_k E[ℓ^k]`, which **is** compact as soon as every level
  `E[ℓ^k]` is finite, and inside which `T_ℓ E` is cut out by the closed conditions
  `ℓ · g (k+1) = g k`.
* At `ℓ = 2` **and at `ℓ = 3`** the finiteness of every level is **already available and
  unconditional**: `EllipticCurves.Torsion.TwoPrimary` proves `#E[2^k] = 4^k` from the tangent-line
  doubling shortcut, and `EllipticCurves.Torsion.ThreePrimary` proves `#E[3^k] = 9^k` by induction
  from `#E[3] = 9`.

⚠️ **The two counts are not equally cheap, and a file that lists them side by side will be misread
if it does not say so.** The `2`-primary one appeals neither to Ward's theorem, nor to the
elliptic-net recurrence, nor to the multiplication-by-`n` coordinate formula
`x(nP) = Φₙ(x)/ΨSqₙ(x)`. The `3`-primary one **does** consume that formula, at `n = 3`, through
`EllipticCurves.Torsion.TriplingSurjective` — and it additionally needs `(3 : F) ≠ 0`.
`EllipticCurves.TateModule.OpenKernel` draws exactly this distinction for the same pair of inputs;
this file follows it rather than restating it in different words.

So `T_2 E` and `T_3 E` are honest profinite abelian groups, and `ρ_{E,2}` and `ρ_{E,3}` are
continuous representations of a topological group *on a profinite module* rather than merely on a
topological one (`continuous_galoisRep`, which is stated at every prime `ℓ`).

## The topology is the inverse-limit topology — as a theorem

The deliverable that carries the mathematical content is not compactness but
`WeierstrassCurve.Affine.tateModule.isClosedEmbedding_levelFamily`: the level-family map

```
levelFamily : T_ℓ E →+ ∏ k, E[ℓ^k],    f ↦ (proj k f)_k
```

is a **closed topological embedding**, with range exactly the compatible families
(`range_levelFamily`). `EllipticCurves.TateModule.Continuity` asserts in prose that the subspace
topology inherited from `ℕ → E(F)` "is the `ℓ`-adic (inverse-limit) topology"; this is that
assertion made checkable. Compactness is then a two-line corollary of Tychonoff.

## Conditionality

* `isClosed_setOf_isCompatibleLevels`, `range_levelFamily`, `isEmbedding_levelFamily`,
  `isClosedEmbedding_levelFamily`, `isOpen_ker_proj` and `iInf_ker_proj` are **unconditional**:
  they hold for every `ℓ` and every Weierstrass curve, finite levels or not.
* `compactSpace` and `isCompact_coe` take the hypothesis `∀ k, Finite (W.torsion (ℓ ^ k))`.
* `compactSpace_two`, `isCompact_coe_two`, `not_discreteTopology_tateModule_two` and
  `profiniteAddGrpTwo` discharge that hypothesis **unconditionally at `ℓ = 2`** via
  `finite_torsion_two_pow`.
* `compactSpace_three`, `isCompact_coe_three`, `not_discreteTopology_tateModule_three` and
  `profiniteAddGrpThree` do the same **at `ℓ = 3`** via `finite_torsion_three_pow`, at the price of
  `(3 : F) ≠ 0` and of the coordinate formula recorded above.

**This supersedes, at `ℓ = 2` and at `ℓ = 3`, the "No compactness" paragraph in the module docstring
of `EllipticCurves.TateModule.Continuity`.** ⚠️ That paragraph no longer *says* finiteness of `E[n]`
"is not available in this development": `#985` repaired it, and it now quotes that clause and names
it false at every `3`-smooth `n` (`finite_torsion_of_smooth`, in
`EllipticCurves.Torsion.Multiplicative`) — wider than the `2^k` and `3^k` this file consumes.
What is superseded is only the *conclusion* the clause was offered for. Compactness is still not
that file's job, and it is this file's: `T_2 E` and `T_3 E` are compact, unconditionally.

⚠️ **The clause this paragraph used to carry — *"For **odd** `ℓ` the paragraph still stands:
`Finite (E[ℓ^k])` needs `#E[ℓ] ≤ ℓ²`, which needs the coordinate formula"* — is false at `ℓ = 3`.**
The coordinate formula *is* available at `n = 3` (`EllipticCurves.Torsion.TriplingSurjective`), so
naming it as the obstruction proved the wrong thing: it is a cost at `ℓ = 3`, not a gate. The clause
is true for every prime `ℓ ≥ 5`, where the formula is the general `x(nP) = Φₙ/ΨSqₙ` and is genuinely
unavailable, and it is restated in that form under `## Scope`. Either way `compactSpace` carries
finiteness as a hypothesis rather than assuming it away, so it applies verbatim at each `ℓ` where
the hypothesis is discharged — which is the whole reason the `ℓ = 3` layer below is four one-line
theorems and not a new argument.

## Non-degeneracy

`CompactSpace` is free for the zero module, and `ProfiniteAddGrp.of` accepts it, so a file proving
`T_ℓ E` compact certifies nothing on its own. The discriminating statements are in the file:
`not_discreteTopology_tateModule_two` and `not_discreteTopology_tateModule_three`, i.e. `T_2 E` and
`T_3 E` are compact **and infinite** (`infinite_tateModule_two`,
`infinite_tateModule_three`), hence their topologies are not the discrete one. A compact discrete
space is finite, so each of these single statements rules out both degenerate readings at once — the
zero module, and the possibility that "the profinite topology" is secretly discrete and every
continuity theorem about it vacuous.

⚠️ That closes the *degeneracy* half of non-vacuity but not the *inhabitation* half: every statement
in the two layers below carries `[IsAlgClosed F]` and `[W.IsElliptic]`, and a theorem quantified
over an empty class is vacuously true however many negations it asserts. The `### Non-vacuity`
section at the end of the file closes that half on a curve that exists, for **both** `ℓ = 2` and
`ℓ = 3`.

## Main statements

* `WeierstrassCurve.Affine.tateModule.isClosedEmbedding_levelFamily` : `T_ℓ E ↪ ∏_k E[ℓ^k]` is a
  closed embedding — the topology on `T_ℓ E` *is* the inverse-limit topology.
* `WeierstrassCurve.Affine.tateModule.compactSpace` : `T_ℓ E` is compact when every level is finite.
* `WeierstrassCurve.Affine.tateModule.compactSpace_two`,
  `WeierstrassCurve.Affine.tateModule.compactSpace_three` : `T_2 E` and `T_3 E` are compact,
  unconditionally.
* `WeierstrassCurve.Affine.tateModule.not_discreteTopology_tateModule_two`,
  `WeierstrassCurve.Affine.tateModule.not_discreteTopology_tateModule_three` : neither is discrete.
* `WeierstrassCurve.Affine.tateModule.profiniteAddGrpTwo`,
  `WeierstrassCurve.Affine.tateModule.profiniteAddGrpThree` : `T_2 E` and `T_3 E` as objects of
  `ProfiniteAddGrp`.
* `WeierstrassCurve.Affine.tateModule.isOpen_ker_proj`,
  `WeierstrassCurve.Affine.tateModule.iInf_ker_proj` : the level filtration is a filtration by open
  subgroups intersecting in `0`.

## Scope

⚠️ **`ℓ ≥ 5` is where the gate actually is, and it has not moved.** `Finite (E[ℓ^k])` at a prime
`ℓ ≥ 5` needs `#E[ℓ] ≤ ℓ²` and hence the general multiplication-by-`n` coordinate formula
`x(nP) = Φₙ/ΨSqₙ`, which this development does not have. `compactSpace` and `isCompact_coe` will
apply verbatim the day it lands — they take finiteness as a hypothesis and never assume it — so what
is missing at `ℓ ≥ 5` is the input and not anything in this file.

⚠️ **There is no `3`-smooth analogue of the two layers below, and a reader arriving from
`EllipticCurves.TateModule.OpenKernel` will expect one.** That file's
`isOpen_ker_galoisRepMod_smooth` exists because `isOpen_ker_galoisRepMod` takes
`Finite ((W'⁄F).torsion n)` — a hypothesis about a **single** `n`, which `finite_torsion_of_smooth`
supplies at every `3`-smooth `n`. `compactSpace` takes `∀ k, Finite (W.torsion (ℓ ^ k))` — a
hypothesis about the **`ℓ`-power family** — and `3`-smoothness is a condition on one composite `n`,
so it does not slot in. The four-theorem `2 ^ k` / `3 ^ k` / smooth / no-`IsAlgClosed` shape of that
file therefore does **not** transpose here. This is not a gap: `T_ℓ E` is an inverse limit along
powers of a single `ℓ` and is only of interest at prime `ℓ`, so a `3`-smooth `T_n E` is not a thing
this development wants.

Nothing here bears on `T_ℓ E ≅ ℤ_ℓ²`, on the image of `ρ_ℓ`, or on `det ρ_{E,ℓ}` and the cyclotomic
character. ⚠️ In particular `compactSpace_three` is **not** progress towards `det ρ_{E,3} = χ_3`
`3`-adically, which needs the Weil pairing on `E[3^k]` for every `k`; the mod-`3` identity
`galoisDetMod 3 = χ_3` is a different statement and lives in
`EllipticCurves.FunctionField.WeilPairingDeterminantCharacter`.

Continuity of `ρ_{E,2}` into `GL₂(ℤ_[2])` **with its `2`-adic topology** is likewise not supplied
here, but it is available: `continuous_galoisRepMatrixTwo` in
`EllipticCurves.TateModule.MatrixContinuity`. An earlier version of this docstring said it needed a
basis compatible with the level filtration and that compactness did not supply it; **both halves
were wrong.** It needs no compatible basis, and it is exactly a compactness argument — run on the
compactness of the *coordinate space* `Fin 2 → ℤ_[2]`, which is Mathlib's, rather than on the
compactness of `T₂E` proved below.

## References

* [J. H. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.7.
-/

open scoped WeierstrassCurve.Affine.ProfiniteTopology

namespace WeierstrassCurve.Affine

namespace tateModule

variable {F : Type*} [Field F] [DecidableEq F] (W : Affine F) (ℓ : ℕ)

/-! ### The compatible families inside the product of the levels -/

/-- The transition relations, read on a family of *level* points `g k ∈ E[ℓ^k]` rather than on a
family of points of `E(F)`. Compare `WeierstrassCurve.Affine.IsCompatibleFamily`, which additionally
has to record the torsion condition; here it is carried by the types. -/
def IsCompatibleLevels (g : ∀ k, W.torsion (ℓ ^ k)) : Prop :=
  ∀ k, ℓ • ((g (k + 1) : W.Point)) = (g k : W.Point)

/-- **The compatible families form a closed subset of `∏_k E[ℓ^k]`.** Each transition relation is
an equaliser of two continuous maps into `E(F)`, which is discrete and hence Hausdorff. This is the
only topological input to compactness. -/
theorem isClosed_setOf_isCompatibleLevels :
    IsClosed {g : ∀ k, W.torsion (ℓ ^ k) | IsCompatibleLevels W ℓ g} := by
  have hset : {g : ∀ k, W.torsion (ℓ ^ k) | IsCompatibleLevels W ℓ g}
      = ⋂ k : ℕ, {g : ∀ k, W.torsion (ℓ ^ k) |
          ℓ • ((g (k + 1) : W.Point)) = (g k : W.Point)} := by
    ext g
    simp only [Set.mem_setOf_eq, Set.mem_iInter, IsCompatibleLevels]
  rw [hset]
  refine isClosed_iInter fun k => isClosed_eq ?_ ?_
  · exact (continuous_of_discreteTopology (f := fun P : W.Point => ℓ • P)).comp
      (continuous_subtype_val.comp (continuous_apply (k + 1)))
  · exact continuous_subtype_val.comp (continuous_apply k)

/-! ### The level-family map -/

/-- The **level family** of an element of the Tate module, packaged as an additive homomorphism
`T_ℓ E →+ ∏_k E[ℓ^k]`. This is the tautological map into the inverse system; the theorems below say
it is a closed topological embedding onto the compatible families. -/
@[simps]
def levelFamily : W.tateModule ℓ →+ ∀ k, W.torsion (ℓ ^ k) where
  toFun f k := proj k f
  map_zero' := rfl
  map_add' _ _ := rfl

theorem levelFamily_injective : Function.Injective (levelFamily W ℓ) := fun _ _ h =>
  tateModule.ext fun k => congrArg Subtype.val (congrFun h k)

/-- **The range of the level family is exactly the compatible families.** -/
theorem range_levelFamily :
    Set.range (levelFamily W ℓ) = {g : ∀ k, W.torsion (ℓ ^ k) | IsCompatibleLevels W ℓ g} := by
  ext g
  simp only [Set.mem_range, Set.mem_setOf_eq]
  constructor
  · rintro ⟨f, rfl⟩ k
    exact f.2.2 k
  · intro hg
    exact ⟨⟨fun k => (g k : W.Point), ⟨fun k => (g k).2, hg⟩⟩, rfl⟩

/-- The inclusion of the product of the level groups into `ℕ → E(F)`, through which the level
family factors the coercion of `T_ℓ E`. -/
private def levelInclusion (g : ∀ k, W.torsion (ℓ ^ k)) : ℕ → W.Point := fun k => (g k : W.Point)

private theorem continuous_levelInclusion : Continuous (levelInclusion W ℓ) :=
  continuous_pi fun k => continuous_subtype_val.comp (continuous_apply k)

/-- The level family is continuous. -/
theorem continuous_levelFamily : Continuous (levelFamily W ℓ) :=
  continuous_pi fun k =>
    continuous_induced_rng.2 ((continuous_apply k).comp continuous_subtype_val)

/-- **The topology on `T_ℓ E` is the inverse-limit topology.** Formally: the level family is
inducing, i.e. the subspace topology `T_ℓ E` inherits from `ℕ → E(F)` coincides with the topology
pulled back from `∏_k E[ℓ^k]`.

The proof is the factorisation `levelInclusion ∘ levelFamily = Subtype.val`: the composite is
inducing because `T_ℓ E` carries the subspace topology by construction, so `IsInducing.of_comp`
gives it for the first factor. -/
theorem isInducing_levelFamily : Topology.IsInducing (levelFamily W ℓ) := by
  refine Topology.IsInducing.of_comp (continuous_levelFamily W ℓ)
    (continuous_levelInclusion W ℓ) ?_
  exact Topology.IsInducing.subtypeVal

theorem isEmbedding_levelFamily : Topology.IsEmbedding (levelFamily W ℓ) :=
  ⟨isInducing_levelFamily W ℓ, levelFamily_injective W ℓ⟩

/-- **`T_ℓ E ↪ ∏_k E[ℓ^k]` is a closed embedding**: `T_ℓ E` is homeomorphic, as a topological
group, onto a closed subgroup of the product of its levels. Everything below is a corollary. -/
theorem isClosedEmbedding_levelFamily : Topology.IsClosedEmbedding (levelFamily W ℓ) :=
  ⟨isEmbedding_levelFamily W ℓ, by
    rw [range_levelFamily]
    exact isClosed_setOf_isCompatibleLevels W ℓ⟩

/-! ### Compactness -/

/-- **`T_ℓ E` is compact whenever every level `E[ℓ^k]` is finite.** Tychonoff for the product of
finite discrete spaces, plus the closed embedding above. -/
theorem compactSpace (hfin : ∀ k, Finite (W.torsion (ℓ ^ k))) :
    CompactSpace (W.tateModule ℓ) := by
  haveI : ∀ k, CompactSpace (W.torsion (ℓ ^ k)) := fun k => by
    haveI := hfin k
    infer_instance
  exact (isClosedEmbedding_levelFamily W ℓ).compactSpace

/-- The set form of `compactSpace`: `T_ℓ E` is a compact subset of `ℕ → E(F)`. Note that the
ambient space is *not* compact — `E(F)` is infinite — so this is not inherited from it. -/
theorem isCompact_coe (hfin : ∀ k, Finite (W.torsion (ℓ ^ k))) :
    IsCompact ((W.tateModule ℓ : Set (ℕ → W.Point))) :=
  isCompact_iff_compactSpace.2 (compactSpace W ℓ hfin)

/-! ### The unconditional `ℓ = 2` layer

⚠️ *Unconditional* here means *no finiteness hypothesis*, not *no hypotheses*: `[IsAlgClosed F]`,
`[W.IsElliptic]` and `(2 : F) ≠ 0` are all still carried, because `#E[2^k] = 4^k` is. -/

section Two

variable [IsAlgClosed F] [W.IsElliptic]

/-- **`T_2 E` is compact**, with no hypothesis beyond `(2 : F) ≠ 0`. The finiteness of every level
is `finite_torsion_two_pow`, which comes from `#E[2^k] = 4^k`; that count uses only the tangent-line
doubling identity, so this is independent of Ward's theorem, of the elliptic-net recurrence and of
the coordinate formula `x(nP) = Φₙ/ΨSqₙ`. -/
theorem compactSpace_two (h2 : (2 : F) ≠ 0) : CompactSpace (W.tateModule 2) :=
  compactSpace W 2 (finite_torsion_two_pow h2)

/-- The set form of `compactSpace_two`. ⚠️ Added alongside `isCompact_coe_three` rather than for a
consumer: `isCompact_coe` had no instantiated layer at all, and giving it one only at `ℓ = 3` would
have left the file asserting a fact about `T_3 E` that it declines to assert about `T_2 E`. -/
theorem isCompact_coe_two (h2 : (2 : F) ≠ 0) :
    IsCompact ((W.tateModule 2 : Set (ℕ → W.Point))) :=
  isCompact_coe W 2 (finite_torsion_two_pow h2)

/-- **`T_2 E` is compact but not discrete.**

This is the statement that rules out the degenerate readings of everything above and of
`EllipticCurves.TateModule.Continuity`: a compact *discrete* space is finite, whereas `T_2 E` is
infinite (`infinite_tateModule_two`). So the profinite topology on `T_2 E` is genuinely a new
topology — neither indiscrete (it is Hausdorff) nor discrete — and the continuity statements proved
about it are not vacuous. It is also the precise reason a stabiliser in `T_2 E` can be closed
without being open. -/
theorem not_discreteTopology_tateModule_two (h2 : (2 : F) ≠ 0) :
    ¬ DiscreteTopology (W.tateModule 2) := by
  intro hd
  haveI := hd
  haveI := compactSpace_two W h2
  haveI := infinite_tateModule_two (W := W) h2
  haveI : Finite (W.tateModule 2) := finite_of_compact_of_discrete
  exact not_finite (W.tateModule 2)

/-- **`T_2 E` as an object of `ProfiniteAddGrp`**: a compact, totally disconnected topological
abelian group. `ProfiniteAddGrp.of` does not ask for `T2Space` — in a topological group, total
disconnectedness already forces it — so Hausdorffness is not being skipped here; it is
`tateModule.t2Space`. -/
def profiniteAddGrpTwo (h2 : (2 : F) ≠ 0) : ProfiniteAddGrp :=
  haveI := compactSpace_two W h2
  ProfiniteAddGrp.of (W.tateModule 2)

@[simp]
theorem coe_profiniteAddGrpTwo (h2 : (2 : F) ≠ 0) :
    (profiniteAddGrpTwo W h2 : Type _) = W.tateModule 2 :=
  rfl

end Two

/-! ### The unconditional `ℓ = 3` layer

Four one-line instantiations of the conditional statements above, discharging
`∀ k, Finite (W.torsion (3 ^ k))` with `finite_torsion_three_pow`
(`EllipticCurves.Torsion.ThreePrimary`). Nothing new is proved here.

⚠️ **The price is not the same as at `ℓ = 2` and the docstrings below say so individually.** Each
statement carries `(3 : F) ≠ 0` in addition to `(2 : F) ≠ 0`, and its finiteness input reaches
`#E[3^k] = 9^k` through the multiplication-by-`n` coordinate formula at `n = 3`
(`EllipticCurves.Torsion.TriplingSurjective`), which the `2`-primary count does not use. -/

section Three

variable [IsAlgClosed F] [W.IsElliptic]

/-- **`T_3 E` is compact**, with no hypothesis beyond `(2 : F) ≠ 0` and `(3 : F) ≠ 0`. The
finiteness of every level is `finite_torsion_three_pow`, which comes from `#E[3^k] = 9^k`.

⚠️ Unlike `compactSpace_two` this **does** consume the multiplication-by-`n` coordinate formula, at
`n = 3`: `card_torsion_three_pow` reaches the count through
`EllipticCurves.Torsion.TriplingSurjective`. `compactSpace_two`'s docstring says its count needs
neither the elliptic-net recurrence nor that formula; that is a claim about `ℓ = 2` and must not be
read here.

⚠️ **Deletion test**, run on this file as committed: replacing the proof by
`by refine compactSpace W 3 ?_` — deleting the `finite_torsion_three_pow h2 h3` argument and
changing nothing else — leaves

```
error: unsolved goals
F : Type u_1
inst✝³ : Field F
inst✝² : DecidableEq F
W : Affine F
inst✝¹ : IsAlgClosed F
inst✝ : WeierstrassCurve.IsElliptic W
h2 : 2 ≠ 0
h3 : 3 ≠ 0
⊢ ∀ (k : ℕ), Finite ↥(W.torsion (3 ^ k))
```

a **goal** rather than a type mismatch, and it is exactly the hypothesis of `compactSpace`.

⚠️ `[IsAlgClosed F]` is **measured** to be necessary here rather than assumed to be. Placing
`omit [IsAlgClosed F] in` on this theorem, immediately above its docstring, gives
`failed to synthesize instance of type class IsAlgClosed F` — `card_torsion_three_pow` is an exact
count and is stated over an algebraically closed field. The `unusedSectionVars` linter answers in
the other direction and is silent on every declaration in this section. ⚠️ Two traps in reproducing
that: the `omit` line must go **above** the docstring, not between it and the `theorem` keyword,
where it is a parse error; and the run additionally reports `coe_profiniteAddGrpThree` as having an
unused section variable, which is a **cascade** of this theorem failing and not a finding about
that one. -/
theorem compactSpace_three (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) :
    CompactSpace (W.tateModule 3) :=
  compactSpace W 3 (finite_torsion_three_pow h2 h3)

/-- The set form of `compactSpace_three`: `T_3 E` is a compact subset of `ℕ → E(F)`. As at `ℓ = 2`,
the ambient space is not compact. -/
theorem isCompact_coe_three (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) :
    IsCompact ((W.tateModule 3 : Set (ℕ → W.Point))) :=
  isCompact_coe W 3 (finite_torsion_three_pow h2 h3)

/-- **`T_3 E` is compact but not discrete**, the `ℓ = 3` twin of
`not_discreteTopology_tateModule_two` and, as there, the statement that rules out the degenerate
readings: a compact *discrete* space is finite, whereas `T_3 E` is infinite.

⚠️ The infinitude input is `infinite_tateModule_three`
(`EllipticCurves.TateModule.FreeThree`) and it is **not** in the same file as its `ℓ = 2`
counterpart — `infinite_tateModule_two` is in `EllipticCurves.TateModule.LevelStructure`. That is
the whole reason this file imports `EllipticCurves.TateModule.FreeThree`; the compactness half needs
only `EllipticCurves.Torsion.ThreePrimary`. -/
theorem not_discreteTopology_tateModule_three (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) :
    ¬ DiscreteTopology (W.tateModule 3) := by
  intro hd
  haveI := hd
  haveI := compactSpace_three W h2 h3
  haveI := infinite_tateModule_three (W := W) h2 h3
  haveI : Finite (W.tateModule 3) := finite_of_compact_of_discrete
  exact not_finite (W.tateModule 3)

/-- **`T_3 E` as an object of `ProfiniteAddGrp`**, exactly as `profiniteAddGrpTwo`. -/
def profiniteAddGrpThree (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) : ProfiniteAddGrp :=
  haveI := compactSpace_three W h2 h3
  ProfiniteAddGrp.of (W.tateModule 3)

@[simp]
theorem coe_profiniteAddGrpThree (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) :
    (profiniteAddGrpThree W h2 h3 : Type _) = W.tateModule 3 :=
  rfl

end Three

/-! ### The level filtration is a filtration by open subgroups -/

/-- The kernel of the level-`k` projection is **open**: `E[ℓ^k]` is discrete and `proj k` is
continuous. Together with `iInf_ker_proj` this exhibits the level filtration as a neighbourhood
basis of `0` by open subgroups, which is what makes `T_ℓ E` the inverse limit of its quotients
`T_ℓ E ⧸ ker (proj k)`; that identification is not proved here. -/
theorem isOpen_ker_proj (k : ℕ) :
    IsOpen (((proj (W := W) (ℓ := ℓ) k).ker : AddSubgroup (W.tateModule ℓ)) :
      Set (W.tateModule ℓ)) := by
  have hset : (((proj (W := W) (ℓ := ℓ) k).ker : AddSubgroup (W.tateModule ℓ)) :
      Set (W.tateModule ℓ)) = (fun f => proj (W := W) (ℓ := ℓ) k f) ⁻¹' {0} := by
    ext f
    simp [AddMonoidHom.mem_ker]
  rw [hset]
  exact ((continuous_apply k).comp (continuous_levelFamily W ℓ)).isOpen_preimage _
    (isOpen_discrete _)

/-- The level filtration is **separated**: a compatible family vanishing at every level is `0`. -/
theorem iInf_ker_proj : (⨅ k : ℕ, (proj (W := W) (ℓ := ℓ) k).ker) = ⊥ := by
  refine le_antisymm (fun f hf => ?_) bot_le
  simp only [AddSubgroup.mem_iInf, AddMonoidHom.mem_ker] at hf
  exact AddSubgroup.mem_bot.2 (tateModule.ext fun k => congrArg Subtype.val (hf k))

/-! ### Non-vacuity

⚠️ Everything in the two unconditional layers above carries `[IsAlgClosed F]` and `[W.IsElliptic]`,
so `ℚ` cannot witness it and every one of those statements would be vacuously true if nothing
inhabited those classes. `[IsAlgClosed F]`, `[W.IsElliptic]`, `(2 : F) ≠ 0` and `(3 : F) ≠ 0` are
simultaneously satisfiable on this development's standard certificate curve `y² + y = x³` over an
algebraic closure of `ℚ`, which is the curve `EllipticCurves.Torsion.ThreePrimary` and
`EllipticCurves.TateModule.FreeThree` use for the same purpose — and all three now name the one
shared fixture `EllipticCurves.Fixture.y2AddYEqX3` rather than each carrying a `private` copy.

⚠️ **This closes a different risk from `not_discreteTopology_tateModule_two` and
`not_discreteTopology_tateModule_three`.** Those rule out the *degenerate* readings — the zero
module, and a secretly discrete topology. This rules out an *empty hypothesis class*. Neither
implies the other, and the file previously closed only the first. -/

section Nonvacuity

/-! The certificate curve `y² + y = x³` over `ℚ` and its base, an algebraic closure of `ℚ` — of
characteristic `0`, so that `2 ≠ 0` and `3 ≠ 0` — are the shared
`EllipticCurves.Fixture.y2AddYEqX3` and `EllipticCurves.Fixture.AlgClosedQ`, which also supply
`(y2AddYEqX3 ℚ).IsElliptic` from a single `[CharZero F]` instance. The **base-changed**
`((y2AddYEqX3 ℚ)⁄AlgClosedQ).IsElliptic` comes from the same module, via
`EllipticCurves.Fixture.instIsEllipticBaseChange`; this block declares no fixture of its own
(`#1408`). -/

open EllipticCurves.Fixture

private lemma exampleTwo : (2 : AlgClosedQ) ≠ 0 := two_ne_zero

private lemma exampleThree : (3 : AlgClosedQ) ≠ 0 := three_ne_zero_of_charZero _

open Classical in
/-- **On a curve that exists**: `T_2 E` and `T_3 E` are both compact and both non-discrete.

⚠️ It closes by **application** of the four theorems above, not by `rfl`, `decide` or `norm_num`, so
it consumes them. Its only content beyond that is that `(y2AddYEqX3 ℚ)⁄AlgClosedQ` inhabits
`[IsAlgClosed F]` and `[W.IsElliptic]` at all — which is precisely the half a statement quantified
over those classes cannot certify about itself.

⚠️ Both `ℓ = 2` clauses are here even though this issue's deliverable is the `ℓ = 3` layer: the
`ℓ = 2` layer has been on `main` since this file landed and had **no** named curve either, and the
boilerplate above serves both at no extra cost. -/
example : CompactSpace (((y2AddYEqX3 ℚ)⁄AlgClosedQ).tateModule 2) ∧
    ¬ DiscreteTopology (((y2AddYEqX3 ℚ)⁄AlgClosedQ).tateModule 2) ∧
    CompactSpace (((y2AddYEqX3 ℚ)⁄AlgClosedQ).tateModule 3) ∧
    ¬ DiscreteTopology (((y2AddYEqX3 ℚ)⁄AlgClosedQ).tateModule 3) :=
  ⟨compactSpace_two _ exampleTwo,
    not_discreteTopology_tateModule_two _ exampleTwo,
    compactSpace_three _ exampleTwo exampleThree,
    not_discreteTopology_tateModule_three _ exampleTwo exampleThree⟩

end Nonvacuity

end tateModule

end WeierstrassCurve.Affine
