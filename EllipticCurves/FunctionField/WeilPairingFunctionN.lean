/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import EllipticCurves.Fixtures
import EllipticCurves.FunctionField.WeilPairingAlternatingAssemblyN
import EllipticCurves.FunctionField.WeilPairingDivisorSlotBilinearHprinN
import EllipticCurves.FunctionField.WeilPairingFunctionTwo
import EllipticCurves.FunctionField.WeilPairingNondegenerateN
import EllipticCurves.Torsion.StructureGeneral

/-!
# The Weil pairing at a general `n` as a function of two torsion points

`EllipticCurves.FunctionField.WeilPairingFunctionTwo` (`#922`) and
`EllipticCurves.FunctionField.WeilPairingFunctionThree` (`#925`) replaced the existential packaging
of rung 6 at `n = 2` and `n = 3` by genuine functions

```
weilPairing{Two,Three} : E[n] → E[n] → μ_n(F),
```

bundled as `weilPairing{Two,Three}Hom` with `MonoidHom.ker _ = ⊥`.  **At every other index the
pairing is not a function anywhere in this tree**: `WeilPairingNondegenerateN`,
`WeilPairingDivisorSlotBilinearHprinN`, `WeilPairingTranslationSlotHprinN` and
`WeilPairingAlternatingAssemblyN` all quantify over the rung-5 *data* `f_S`, `g_S`, and
`WeilPairingNondegenerateN`'s `## Scope` rules that gap out of scope for itself in terms — *"a
general-`n` version of those is a separate question with its own design decisions"*, ⚠️ **whose
`those` the source italicises, named here rather than reproduced** because a lone-asterisk span
inside a marked quotation is `<em>` inside `<em>` and shows a reader nothing (`README.md`
`### Retired claims`, `#1875`).  This file is that question.

⚠️ **Almost everything here is a transcription, and the module docstring says which part is not.**
The construction is `WeilPairingFunctionTwo`'s, with `mulByNEndo n hn` for `mulByTwoEndo h2` and the
general-`n` form of each merged input; the one argument that is genuinely different is the
`S₁ ⊕ S₂ = O` corner of divisor-slot bilinearity, and it is written up at
`weilPairingEltN_add_left`.

## The setting, once, so that the reach clauses below can defer to it

The span these clauses defer to is the **39** declarations from `### The pairing as a function` to
the end of `### Recovery of the merged numeral layers, compiled` — **37** public and **2**
`example`s, no `private`.  `### Non-vacuity` is outside it, being stated over a named field rather
than over the variable `F`.  All **39** carry `[W.IsElliptic]`, `[IsAlgClosed F]` and
`(2 : F) ≠ 0`; **35** carry `((n : ℤ) : F) ≠ 0`, and the other **4** are the recovery declarations,
where the index is the literal `2` and the same hypothesis is written `(((2 : ℕ) : ℤ) : F) ≠ 0` or
produced from `(2 : F) ≠ 0` inside the proof.  That is `WeilPairingNondegenerateN`'s setting
exactly, and **not one hypothesis more**.

⚠️ **`[NeZero n]` is bound by the `μ_n(F)`-valued layer and by nothing else — which is a claim
about all 39 declarations, so here is the count and the key.**  Exactly **15** of the 39 bind it:
`weilPairingN`, `algebraMap_coe_weilPairingN`, `weilPairingN_eq_one_iff`,
`weilPairingN_eq_weilPairingMu`, `weilPairingN_zero_right`, `weilPairingN_zero_left`,
`weilPairingN_add_right`, `weilPairingN_add_left`, `weilPairingN_self`, `weilPairingN_mul_swap`,
`weilPairingN_swap`, `eq_zero_of_forall_weilPairingN_eq_one`, `weilPairingNHom`,
`weilPairingNHom_apply_apply` and `ker_weilPairingNHom`.  The key returning exactly those is
*the **statement** mentions `weilPairingN` or `weilPairingNHom`*, less the one exception below; and
on those 15 the instance is **forced and not chosen**, because both of those names elaborate
through `rootsOfUnity n F`, which does not elaborate without it.  Same shape and same reason as
`weilPairingTorsionMuHom_n` (`EllipticCurves.FunctionField.WeilPairingTranslationSlotHprinN`).

⚠️ **The one exception to that key is `weilPairingN_eq_weilPairingTwo`** — μ-valued, mentions
`weilPairingN`, binds no instance: its index is the literal `2`, so `NeZero 2` is found.

⚠️ **The other 24 are `F(W)`-valued and bind none of it — and six of them did until this paragraph
was scored against the binders rather than read.**  `weilPairingPointElt_weilPairingRootN_pow`,
`weilPairingEltN_pow_eq_one`, `weilPairingEltN_add_right`, `weilPairingEltN_add_left`,
`weilPairingEltN_mul_swap` and `weilPairingEltN_swap` carried `[NeZero n]` while needing only
`n ≠ 0`, which `((n : ℤ) : F) ≠ 0` yields in one line (`by rintro rfl; simp at hn`) — the file's own
idiom at `weilPairingEltN_self`.  There it was **chosen**, by the paragraph's own criterion;
dropping it strictly widens all six and is what makes the sentence above true as written.  The
comparison target is `WeilPairingNondegenerateN`, which opens `variable [NeZero n]` at its own `μ`
layer and gives its four `F(W)`-valued statements none.

Of the six declarations of `### The rung-5 datum at a point, uniform in the point`, five carry no
`[IsAlgClosed F]`.  ⚠️ **One of the five says so in its own docstring** — `isWeilRootN_one`,
*"Unconditional — no `[IsAlgClosed F]`, and no condition on `n`"* — and the claim for the section is
made once, by the sixth: `exists_isWeilRootN`'s docstring names
`exists_gS_of_ne_zero_of_isAlgClosed` as *"the only place `[IsAlgClosed F]` enters this section"*.
That sixth carries the four above and nothing more.

⚠️ **`[IsAlgClosed F]` is load-bearing and this file adds no new source of it.**  It enters through
`exists_gS_of_ne_zero_of_isAlgClosed`, through the alternating headline, through the `hprin`
discharge and through `card_torsion_eq_sq`; `WeilPairingNondegenerateN`'s `## Scope` records that
the closure reaches that front by two independent routes and this file inherits the account
unchanged.  The arbitrary-field form is not weaker but **false** — over a non-closed `F` the rung-5
root need not exist (`#962`).

## What each property is read off, and every one of them was already general

| property | merged general-`n` input |
| --- | --- |
| a root at every torsion point | `exists_gS_of_ne_zero_of_isAlgClosed` |
| well-definedness of the value | `weilPairingElt_eq_of_smul_pow_eq_of_divisor_eq` |
| `e_n(S, T) ^ n = 1` | `torsion_le_weilPairingPointSubgroup_n` |
| the translation slot | `weilPairingPointElt_add` |
| the alternating law | `exists_weilPairingElt_self_eq_one_of_hprin_n_of_algClosed_of_ne_zero` |
| the divisor slot | `exists_weilPairingElt_divisorSlot_add_of_ne_zero_of_hprin` |
| non-degeneracy | `eq_zero_of_forall_weilPairingElt_eq_one_n` |
| the `hprin` the last two take | `exists_nsmul_divisor_eq_divisor_mulByNEndo` |

Rows 1 and 8 are `PullbackPrincipalityN`'s, rows 3 and 5 are
`WeilPairingTranslationSlotHprinN`'s and `WeilPairingAlternatingAssemblyN`'s, row 6 is
`WeilPairingDivisorSlotBilinearHprinN`'s, row 7 is `WeilPairingNondegenerateN`'s, and rows 2 and 4
are `#854`'s (`WeilPairingProductRelationRootIndependent`) and `#890`'s
(`WeilPairingTranslationSlotHom`).

⚠️ **Three of those seven modules are `import`s of this file and four are reached through them** —
`import` meaning a line of this file's own import block, which has six lines.  Rows 5, 6 and 7 are
direct; the other four are not, and the route is measured and not inferred
(`ModuleData.imports`, transitively, from each direct import):
`PullbackPrincipalityN` through `WeilPairingNondegenerateN`; `WeilPairingTranslationSlotHprinN`
through `WeilPairingDivisorSlotBilinearHprinN` and `WeilPairingNondegenerateN`; `#890`'s through
those two and `WeilPairingFunctionTwo`; and `#854`'s **only** through `WeilPairingFunctionTwo`.
⚠️ **That last route is worth knowing before anyone reorganises the imports**: the module supplying
the one lemma this file rests on (row 2, well-definedness) rides in on the import taken for
`### Recovery of the merged numeral layers, compiled`, and on no other.

Two of those are worth naming because they are what make the general index cheap rather than merely
possible, and both were noticed by `WeilPairingFunctionThree` at its own index:

* `weilPairingElt_eq_of_smul_pow_eq_of_divisor_eq` is generic in the pullback `φ` **and in the
  exponent**, so well-definedness needs nothing added; here `φ := mulByNEndo n hn`.
* `eq_zero_of_forall_weilPairingElt_eq_one_n` states its divisor hypothesis as
  `divisor W f = (n : ℤ) • pointDivisorAff W S`, the same uniform `pointDivisorAff` shape both
  numeral files use.  Taking that as `IsWeilRootN`'s definition is why `S = O` needs no special
  treatment anywhere and why non-degeneracy is three lines.

⚠️ **The transcendence proofs are not syntactically equal and do not have to be.**  `mulByNEndo n h`
is proof-irrelevant in `h : Transcendental F (n • genericPoint).xCoord` because `Transcendental` is
a `Prop`; `EllipticCurves.FunctionField.MulByNDegreeGeneral` records that trap at its own `:72-76`.
`IsWeilRootN` is parametrised by an explicit `h`, and the three producers above — which supply
`transcendental_xCoord_nsmul_genericPoint_of_intCast_ne_zero`,
`transcendental_xCoord_nsmul_of_isAlgClosed` and a caller's own proof respectively — match
definitionally.

## Main statements

* `WeierstrassCurve.Affine.IsWeilRootN` — the rung-5 datum at a point of `W`, uniform in the point,
  with `isWeilRootN_one`, `isWeilRootN_some`, `exists_isWeilRootN` and the well-definedness lemma
  `weilPairingPointElt_eq_of_isWeilRootN` beside it.
* `WeierstrassCurve.Affine.weilPairingRootN` — **the chosen root**, the file's one
  `Classical.choose`, which `weilPairingEltN` is defined at and which nothing downstream may
  unfold; the three lemmas whose names also contain `weilPairingRootN` are its service layer.
* `WeierstrassCurve.Affine.weilPairingEltN`, `…weilPairingN` — **the pairing as a function** of two
  `n`-torsion points, valued in `F(W)` and in `μ_n(F)`, with `weilPairingEltN_eq` the bridge that
  computes it at any root a caller holds — the only sanctioned way past the choice above.
* `WeierstrassCurve.Affine.weilPairingEltN_add_right`, `…_add_left`, `…_self`, `…_mul_swap`,
  `…_swap`, `eq_zero_of_forall_weilPairingEltN_eq_one` — bilinearity in each slot, the alternating
  property, antisymmetry and non-degeneracy, and the `μ_n(F)` twin of each.
* **`WeierstrassCurve.Affine.weilPairingNHom`** and
  **`WeierstrassCurve.Affine.ker_weilPairingNHom`** — the two-slot bundled map and its trivial
  kernel.

* `WeierstrassCurve.Affine.weilPairingEltN_eq_weilPairingEltTwo`,
  `…weilPairingN_eq_weilPairingTwo` — the identification, in
  `### Recovery of the merged numeral layers, compiled`, of this file's function with the merged
  `n = 2` one, which is an equation between the two *functions*.

⚠️ **The six bullets above are a complete account of the public declarations and not a summary**:
the module has **43** public source declarations — **38** `theorem`s and **5** `def`s — plus **4**
`private` lemmas, **1** `private` definition and **6** `example`s, and every one of the 43 is named
above, or has `weilPairingRootN` in its name, or is one of the
`…eq_one_of_{left,right}_eq_zero` / `…ne_zero` (dotted or suffixed) / `_pow_eq_one` /
`_eq_weilPairingElt` / `_eq_weilPairingMu` / `_zero_{left,right}` / `_eq_one_iff` /
`algebraMap_coe_…` / `weilPairingNHom_apply_apply` / `_add_left_of_ne_zero` service lemmas of the
objects named.
⚠️ **Scored name by name against those clauses and not by eye**, because the first version of this
sentence was not: it left `weilPairingRootN` itself, `isWeilRootN_weilPairingRootN` and
`weilPairingPointElt_weilPairingRootN_pow` outside every clause it offered, and its `_ne_zero`
spelling missed `IsWeilRootN.ne_zero`, which is dotted.  The partition, in that order, is
**19 + 6 + 3 + 15 = 43**: 19 named outright, 6 by the twin clause, 3 more carrying
`weilPairingRootN`, and 15 matching one of the ten patterns.

⚠️ **A `ConstantInfo.type.getUsedConstants` census returns 67 constants and not 43**, and a
re-implementer will not reproduce the source count from it: over the same 67, `isPrivateName`
returns **6** and `Name.isInternal` returns **19**, and the two overlap — the `private`
declarations are internal names, which is why a census that tests `isPrivateName` only inside an
`!isInternal` branch reports **0** private.  Over all 67, `IsAlgClosed` occurs in the elaborated
type of **51**, `NeZero` in **25** and `WeierstrassCurve.IsElliptic` in **56**.  Axioms over all
67: `propext`, `Classical.choice`, `Quot.sound`, and nothing else.
⚠️ **The 25 here and the setting section's 15 answer different questions, and neither is a check
on the other**: this census runs over all **67** environment constants — equation lemmas and the
`### Non-vacuity` block included — and asks whether `NeZero` occurs in an elaborated type at all, at
any index; the **15** is a binder count over the **39** source declarations of one span, at the
variable `n`.

## Naming and placement

`WeierstrassCurve.Affine` with `open CoordinateRing`, `#903`'s house pattern as enforced by `#918`
and `#927`.  The `_n` suffix is this development's index suffix for the isogeny track, the same slot
`_two` and `_three` occupy in the two merged files, and it is not a compound name — the reason
`weilPairingTorsionMuHom_n` gives for its own `nolint` (`#1277`).  ⚠️ Nothing here is at the root
namespace: unlike `WeilPairingPerfect`, this file states nothing that is curve-free.

## Scope

⚠️ **`#242` is spent by the *pairing* here, and that is new on this front.**
`WeilPairingNondegenerateN`'s `## Scope` says `card_torsion_eq_sq` (`#E[n] = n²`,
`EllipticCurves.Torsion.StructureGeneral`) enters *"through `#1843`, and only there"*.  It is not
edited, and here is the exact reason, because the obvious one is wrong: **the sentence says
`front`, not `file`**, and read as written this file falsifies it — the count is spent here
directly, by `weilPairingEltN_add_left` and by nothing else, to produce a third `n`-torsion point
in the `S₁ ⊕ S₂ = O` corner, and that is the only declaration here that needs a torsion count.
⚠️ **What saves the sentence is its own next clause**, which names `exists_nonsingular_mem_torsion`
in that file's non-vacuity block as a second spender — itself not through `#1843` — so the strict
reading was already false where it stands and the sentence is scoped in practice to that file's
argument, where it is true.  Read that way it is untouched by this landing; read as written it has
a pre-existing defect that is not this file's to repair.

⚠️ **The merged `n = 2` layer is recovered, and the recovery is an equation between the two
functions and not merely between their properties.**  `weilPairingEltN … = weilPairingEltTwo …` and
its `μ_2(F)` twin are compiled in `### Recovery of the merged numeral layers, compiled`, off the
merged bridge `mulByNEndo_two` (`MulByNPullback`) and the two well-definedness lemmas;
`ker_weilPairingTwoHom` then comes back out of `ker_weilPairingNHom` by `MonoidHom.ext`.
⚠️ **That the two functions are equal is not obvious from their definitions and was very nearly
asserted the other way here**: each picks its root by `Classical.choose` at a *different*
existential, and `mulByTwoEndo` (an `IsFractionRing.lift` of a coordinate-ring hom) and
`mulByNEndo` (`pointEndo` at the generic point)
are different constructions.  Neither numeral file is deprecated, restated or touched — `#1304`'s
and `#1308`'s rule, and at `n = 2, 3` the merged ones are still the right thing to cite, since
their proofs do not route through the generic point.

⚠️ **The statements below are pinned to `Classical.propDecidable`**, as every file on this front is:
`open Classical in` is required, not decorative, because `TorsionNMul` bakes the classical
`DecidableEq F` instance in and the statements mention `W.torsion n`.

## Explicitly out of scope

* **Perfectness at a general `n`** — `bijective_weilPairingNHom`, the `MulEquiv` onto the dual
  group, the `∃!` reading and `#E[n]^∨ = n²`.  `EllipticCurves.FunctionField.WeilPairingPerfect`'s
  `General n` bullet names `weilPairingNHom` and `ker_weilPairingNHom` as the whole precondition for
  transcribing its argument, and this file supplies them; the transcription itself is a separate
  module and is `#2031`, whose description carries it spiked.  ⚠️ **The duality count needs only
  injectivity and equal finite cardinality**, so it re-spends nothing from this file beyond
  `ker_weilPairingNHom`.  ⚠️ This file leaves a pointer in that bullet and changes none of its
  prose: the sentence it makes factual was stated as a condition and is still true as written.
* **The arbitrary-field (`_of_hprin`) form.**  ⚠️ False rather than weaker at the perfectness end —
  over a non-closed `F` the dual group is smaller than `E[n]` — and unavailable at this end too,
  since the rung-5 root is `hprin`-gated off `F̄` (`#962`).  There is nothing to lift.
* **Galois-equivariance of the bundled map.**  `#936` left bundled-hom equivariance unfiled for want
  of a consumer and that reasoning is unchanged here.
* **`E[n] ≅ (ℤ/nℤ)²`** — `#242`/`#293`, a different statement.  ⚠️ Unlike `WeilPairingPerfect`,
  which deliberately does *not* route through it, this file **does** consume its cardinality
  corollary; see the Scope section.

## References

* [J. H. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.8, Prop. 8.1.
-/

namespace WeierstrassCurve.Affine

open CoordinateRing

variable {F : Type*} [Field F] {W : Affine F} [W.IsElliptic]

/-! ### The rung-5 datum at a point, uniform in the point -/

section Root

open Classical in
/-- **`g` is a rung-5 root at the `n`-torsion point `S`**: there is a nonzero `f` with
`div f = n · (S)` — in the affine divisor group, so `O` contributes nothing — of which `g` is an
`n`-th root of the `[n]∗`-pullback, up to a unit of `F[W]`.

⚠️ The divisor is written against `pointDivisorAff`, not against
`Finsupp.single (pointClosedPoint h.left) (n : ℤ)`, so that `S = O` is covered by the same formula;
`isWeilRootN_some` is the bridge to the shape the merged headlines use. -/
def IsWeilRootN (n : ℕ) (hn : Transcendental F (n • genericPoint (W := W)).xCoord)
    (S : W.Point) (g : W.FunctionField) : Prop :=
  g ≠ 0 ∧ ∃ f : W.FunctionField, f ≠ 0 ∧ divisor W f = (n : ℤ) • pointDivisorAff W S ∧
    ∃ u : W.CoordinateRingˣ, (u : W.CoordinateRing) • g ^ n = mulByNEndo n hn f

open Classical in
/-- A rung-5 root is nonzero, by definition. -/
theorem IsWeilRootN.ne_zero {n : ℕ} {hn : Transcendental F (n • genericPoint (W := W)).xCoord}
    {S : W.Point} {g : W.FunctionField} (hg : IsWeilRootN n hn S g) : g ≠ 0 := hg.1

open Classical in
/-- **`1` is a rung-5 root at `O`**, with `f = 1` and `u = 1`: the point at infinity has empty
affine divisor (`pointDivisorAff_zero`) and `[n]∗` is a ring homomorphism.

⚠️ Unconditional — no `[IsAlgClosed F]`, and no condition on `n`. -/
theorem isWeilRootN_one (n : ℕ) (hn : Transcendental F (n • genericPoint (W := W)).xCoord) :
    IsWeilRootN n hn (0 : W.Point) (1 : W.FunctionField) :=
  ⟨one_ne_zero, 1, one_ne_zero, by rw [divisor_one, pointDivisorAff_zero, smul_zero], 1, by
    rw [Units.val_one, one_smul, one_pow, map_one]⟩

open Classical in
/-- **The bridge from the shape the merged headlines use.**  At an affine point the uniform divisor
condition is `Finsupp.single (pointClosedPoint h.left) (n : ℤ)`, which is what every
`exists_gS_n`-style statement in this tree hands the caller. -/
theorem isWeilRootN_some (n : ℕ) (hn : Transcendental F (n • genericPoint (W := W)).xCoord)
    {x y : F} (h : W.Nonsingular x y) {g f : W.FunctionField} (hg : g ≠ 0) (hf : f ≠ 0)
    (hd : divisor W f = Finsupp.single (pointClosedPoint h.left) (n : ℤ))
    {u : W.CoordinateRingˣ} (hu : (u : W.CoordinateRing) • g ^ n = mulByNEndo n hn f) :
    IsWeilRootN n hn (Point.some x y h) g :=
  ⟨hg, f, hf, by rw [pointDivisorAff_some, Finsupp.smul_single, smul_eq_mul, mul_one]; exact hd,
    u, hu⟩

open Classical in
/-- **Every `n`-torsion point carries a rung-5 root**, over an algebraically closed field.  At `O`
this is `isWeilRootN_one`; at an affine point it is `exists_gS_of_ne_zero_of_isAlgClosed`
(`PullbackPrincipalityN`, `#1843`), which is the only place `[IsAlgClosed F]` enters this
section. -/
theorem exists_isWeilRootN [IsAlgClosed F] (h2 : (2 : F) ≠ 0) {n : ℕ} (hn : ((n : ℤ) : F) ≠ 0)
    {S : W.Point} (hS : S ∈ W.torsion n) :
    ∃ g : W.FunctionField,
      IsWeilRootN n (transcendental_xCoord_nsmul_genericPoint_of_intCast_ne_zero h2 hn) S g := by
  rcases S with _ | ⟨x, y, h⟩
  · exact ⟨1, by rw [← Point.zero_def]; exact isWeilRootN_one n _⟩
  · obtain ⟨f, hf, hd, g, hg, u, hu⟩ := exists_gS_of_ne_zero_of_isAlgClosed h2 hn h hS
    exact ⟨g, isWeilRootN_some n _ h hg hf hd hu⟩

open Classical in
/-- **Well-definedness, and the only lemma this file rests on**: two rung-5 roots at the same `S`
give the same pairing value at *every* point of `W`, the point at infinity included.

At `O` both values are `1`.  At an affine point this is
`weilPairingElt_eq_of_smul_pow_eq_of_divisor_eq` (`#854`) instantiated at `φ = [n]∗` — that theorem
is generic in the pullback **and in the exponent**, so nothing has to be added here — with its
`hfdiv` the two roots' divisor conditions read transitively, which is exactly why `IsWeilRootN`
pins `div f` rather than `f`. -/
theorem weilPairingPointElt_eq_of_isWeilRootN {n : ℕ} (hnz : n ≠ 0)
    {hn : Transcendental F (n • genericPoint (W := W)).xCoord} {S : W.Point}
    {g₁ g₂ : W.FunctionField} (hg₁ : IsWeilRootN n hn S g₁) (hg₂ : IsWeilRootN n hn S g₂)
    (P : W.Point) : weilPairingPointElt g₁ P = weilPairingPointElt g₂ P := by
  obtain ⟨hg₁0, f₁, hf₁, hd₁, u₁, hu₁⟩ := hg₁
  obtain ⟨hg₂0, f₂, hf₂, hd₂, u₂, hu₂⟩ := hg₂
  rcases P with _ | ⟨x, y, h⟩
  · rw [← Point.zero_def, weilPairingPointElt_zero hg₁0, weilPairingPointElt_zero hg₂0]
  · exact weilPairingElt_eq_of_smul_pow_eq_of_divisor_eq h.left (mulByNEndo n hn)
      (mulByNEndo_algebraMap_base n hn) hnz hf₁ hf₂ (hd₁.trans hd₂.symm) hg₁0 hg₂0 hu₁ hu₂

end Root

/-! ### The pairing as a function -/

section Pairing

variable [IsAlgClosed F]

open Classical in
/-- **A chosen rung-5 root at `S`.**  Which one is chosen never matters —
`weilPairingPointElt_eq_of_isWeilRootN` — and the only way to use this definition is through
`weilPairingEltN_eq`, which never unfolds the choice. -/
noncomputable def weilPairingRootN (h2 : (2 : F) ≠ 0) {n : ℕ} (hn : ((n : ℤ) : F) ≠ 0)
    (S : W.torsion n) : W.FunctionField :=
  (exists_isWeilRootN h2 hn S.2).choose

open Classical in
/-- The chosen root is a root. -/
theorem isWeilRootN_weilPairingRootN (h2 : (2 : F) ≠ 0) {n : ℕ} (hn : ((n : ℤ) : F) ≠ 0)
    (S : W.torsion n) :
    IsWeilRootN n (transcendental_xCoord_nsmul_genericPoint_of_intCast_ne_zero h2 hn)
      (S : W.Point) (weilPairingRootN h2 hn S) :=
  (exists_isWeilRootN h2 hn S.2).choose_spec

open Classical in
theorem weilPairingRootN_ne_zero (h2 : (2 : F) ≠ 0) {n : ℕ} (hn : ((n : ℤ) : F) ≠ 0)
    (S : W.torsion n) : weilPairingRootN h2 hn S ≠ 0 :=
  (isWeilRootN_weilPairingRootN h2 hn S).ne_zero

open Classical in
/-- **The Weil pairing at a general `n`, valued in `F(W)`**: `e_n(S, T) = τ_T∗(g_S) / g_S` at a
chosen rung-5 root `g_S`.  A function of two `n`-torsion points, with no existential and no data
argument. -/
noncomputable def weilPairingEltN (h2 : (2 : F) ≠ 0) {n : ℕ} (hn : ((n : ℤ) : F) ≠ 0)
    (S T : W.torsion n) : W.FunctionField :=
  weilPairingPointElt (weilPairingRootN h2 hn S) (T : W.Point)

open Classical in
/-- **The bridge, and the lemma every consumer wants.**  The value is computed by *any* rung-5 root
at `S` the caller happens to hold — in particular by the roots the merged existential headlines
produce, which is how each of them is read through this function below. -/
theorem weilPairingEltN_eq (h2 : (2 : F) ≠ 0) {n : ℕ} (hn : ((n : ℤ) : F) ≠ 0)
    {S : W.torsion n} {g : W.FunctionField}
    (hg : IsWeilRootN n (transcendental_xCoord_nsmul_genericPoint_of_intCast_ne_zero h2 hn)
      (S : W.Point) g) (T : W.torsion n) :
    weilPairingEltN h2 hn S T = weilPairingPointElt g (T : W.Point) :=
  weilPairingPointElt_eq_of_isWeilRootN (by rintro rfl; simp at hn)
    (isWeilRootN_weilPairingRootN h2 hn S) hg _

open Classical in
theorem weilPairingEltN_ne_zero (h2 : (2 : F) ≠ 0) {n : ℕ} (hn : ((n : ℤ) : F) ≠ 0)
    (S T : W.torsion n) : weilPairingEltN h2 hn S T ≠ 0 :=
  weilPairingPointElt_ne_zero (weilPairingRootN_ne_zero h2 hn S) _

open Classical in
/-- The value is an `n`-th root of unity, in the form `weilPairingPointMu` consumes.  Stated against
`weilPairingPointElt` rather than against `weilPairingEltN` so that `weilPairingN` can be defined by
it without an intervening transport. -/
theorem weilPairingPointElt_weilPairingRootN_pow (h2 : (2 : F) ≠ 0) {n : ℕ}
    (hn : ((n : ℤ) : F) ≠ 0) (S T : W.torsion n) :
    weilPairingPointElt (weilPairingRootN h2 hn S) (T : W.Point) ^ n = 1 := by
  haveI : NeZero n := ⟨by rintro rfl; simp at hn⟩
  obtain ⟨hg0, f, hf, hd, u, hu⟩ := isWeilRootN_weilPairingRootN h2 hn S
  exact torsion_le_weilPairingPointSubgroup_n _ hg0 hu T.2

open Classical in
/-- **`e_n(S, T) ^ n = 1`**, for every pair of `n`-torsion points. -/
theorem weilPairingEltN_pow_eq_one (h2 : (2 : F) ≠ 0) {n : ℕ}
    (hn : ((n : ℤ) : F) ≠ 0) (S T : W.torsion n) : weilPairingEltN h2 hn S T ^ n = 1 :=
  weilPairingPointElt_weilPairingRootN_pow h2 hn S T

open Classical in
/-- **`e_n(S, O) = 1`**: translation by the point at infinity is the identity. -/
@[simp]
theorem weilPairingEltN_zero_right (h2 : (2 : F) ≠ 0) {n : ℕ} (hn : ((n : ℤ) : F) ≠ 0)
    (S : W.torsion n) : weilPairingEltN h2 hn S 0 = 1 := by
  rw [weilPairingEltN, ZeroMemClass.coe_zero,
    weilPairingPointElt_zero (weilPairingRootN_ne_zero h2 hn S)]

open Classical in
/-- **`e_n(O, T) = 1`**: `1` is a rung-5 root at `O` (`isWeilRootN_one`) and pairs trivially with
every point.  ⚠️ Proved through the bridge, not by unfolding the choice — the chosen root at `O`
need not be `1`, and nothing below ever needs to know what it is. -/
@[simp]
theorem weilPairingEltN_zero_left (h2 : (2 : F) ≠ 0) {n : ℕ} (hn : ((n : ℤ) : F) ≠ 0)
    (T : W.torsion n) : weilPairingEltN h2 hn 0 T = 1 := by
  rw [weilPairingEltN_eq h2 hn (S := 0)
      (by rw [ZeroMemClass.coe_zero]; exact isWeilRootN_one n _) T,
    weilPairingPointElt_one]

open Classical in
/-- **The Weil pairing at a general `n`, valued in `μ_n(F)`.**  The value group form, off
`weilPairingPointMu` (`#890`). -/
noncomputable def weilPairingN (h2 : (2 : F) ≠ 0) {n : ℕ} [NeZero n] (hn : ((n : ℤ) : F) ≠ 0)
    (S T : W.torsion n) : rootsOfUnity n F :=
  weilPairingPointMu (weilPairingRootN_ne_zero h2 hn S)
    (weilPairingPointElt_weilPairingRootN_pow h2 hn S T)

open Classical in
/-- **Defining property**: pushing the `μ_n(F)` value into `F(W)` recovers the `F(W)` value. -/
@[simp]
theorem algebraMap_coe_weilPairingN (h2 : (2 : F) ≠ 0) {n : ℕ} [NeZero n]
    (hn : ((n : ℤ) : F) ≠ 0) (S T : W.torsion n) :
    algebraMap F W.FunctionField ((weilPairingN h2 hn S T : Fˣ) : F) = weilPairingEltN h2 hn S T :=
  algebraMap_coe_weilPairingPointMu _ _

open Classical in
/-- Triviality in `μ_n(F)` is triviality in `F(W)`; the transport used by every `μ`-level statement
below whose `F(W)` form is an equality with `1`. -/
theorem weilPairingN_eq_one_iff (h2 : (2 : F) ≠ 0) {n : ℕ} [NeZero n] (hn : ((n : ℤ) : F) ≠ 0)
    (S T : W.torsion n) : weilPairingN h2 hn S T = 1 ↔ weilPairingEltN h2 hn S T = 1 :=
  weilPairingPointMu_eq_one_iff _ _

end Pairing

/-! ### The properties, each one merged general-`n` headline read through the bridge -/

section Properties

variable [IsAlgClosed F]

open Classical in
/-- Specialisation of the bridge to an affine translation point, which is the form the merged
headlines — all stated at `weilPairingElt` — apply in. -/
theorem weilPairingEltN_eq_weilPairingElt (h2 : (2 : F) ≠ 0) {n : ℕ} (hn : ((n : ℤ) : F) ≠ 0)
    {S : W.torsion n} {g : W.FunctionField}
    (hg : IsWeilRootN n (transcendental_xCoord_nsmul_genericPoint_of_intCast_ne_zero h2 hn)
      (S : W.Point) g) {T : W.torsion n} {x y : F} (h : W.Nonsingular x y)
    (hT : (T : W.Point) = Point.some x y h) :
    weilPairingEltN h2 hn S T = weilPairingElt h.left g := by
  rw [weilPairingEltN_eq h2 hn hg, hT, weilPairingPointElt_some]

open Classical in
/-- **The `μ_n(F)` bridge**, the value-group twin of `weilPairingEltN_eq_weilPairingElt`.

⚠️ Needed because the merged headlines state their `μ_n(F)` conclusion against `weilPairingMu`, so a
consumer reading them through this function has to compare two elements of `rootsOfUnity n F`
rather than two elements of `F(W)`.  Two elements of `rootsOfUnity n F` are equal as soon as their
images in `F` agree, and `algebraMap F F(W)` is injective, so the two `algebraMap_coe_…` defining
properties turn the goal into the `F(W)`-level bridge above.  The `Classical.choose` inside
`weilPairingN` is never unfolded. -/
theorem weilPairingN_eq_weilPairingMu (h2 : (2 : F) ≠ 0) {n : ℕ} [NeZero n]
    (hn : ((n : ℤ) : F) ≠ 0) {S : W.torsion n} {g : W.FunctionField}
    (hg : IsWeilRootN n (transcendental_xCoord_nsmul_genericPoint_of_intCast_ne_zero h2 hn)
      (S : W.Point) g) {T : W.torsion n} {x y : F} (h : W.Nonsingular x y)
    (hT : (T : W.Point) = Point.some x y h) (hpow : weilPairingElt h.left g ^ n = 1) :
    weilPairingN h2 hn S T = weilPairingMu h.left hpow := by
  refine Subtype.ext (Units.ext ((algebraMap F W.FunctionField).injective ?_))
  rw [algebraMap_coe_weilPairingN, algebraMap_coe_weilPairingMu,
    weilPairingEltN_eq_weilPairingElt h2 hn hg h hT]

open Classical in
theorem weilPairingEltN_eq_one_of_right_eq_zero (h2 : (2 : F) ≠ 0) {n : ℕ}
    (hn : ((n : ℤ) : F) ≠ 0) (S : W.torsion n) {T : W.torsion n} (hT : (T : W.Point) = 0) :
    weilPairingEltN h2 hn S T = 1 := by
  rw [weilPairingEltN, hT, weilPairingPointElt_zero (weilPairingRootN_ne_zero h2 hn S)]

open Classical in
theorem weilPairingEltN_eq_one_of_left_eq_zero (h2 : (2 : F) ≠ 0) {n : ℕ}
    (hn : ((n : ℤ) : F) ≠ 0) {S : W.torsion n} (hS : (S : W.Point) = 0) (T : W.torsion n) :
    weilPairingEltN h2 hn S T = 1 := by
  rw [weilPairingEltN_eq h2 hn (g := 1) (by rw [hS]; exact isWeilRootN_one n _) T,
    weilPairingPointElt_one]

/-! #### The translation slot -/

open Classical in
/-- **`e_n(S, T₁ ⊕ T₂) = e_n(S, T₁) · e_n(S, T₂)`**, as an equation between values of a function.
`weilPairingPointElt_add` (`#890`) — already general in `n` — with its root-of-unity datum supplied
by the chosen root. -/
theorem weilPairingEltN_add_right (h2 : (2 : F) ≠ 0) {n : ℕ} (hn : ((n : ℤ) : F) ≠ 0)
    (S T₁ T₂ : W.torsion n) :
    weilPairingEltN h2 hn S (T₁ + T₂)
      = weilPairingEltN h2 hn S T₁ * weilPairingEltN h2 hn S T₂ := by
  have hnz : n ≠ 0 := by rintro rfl; simp at hn
  rw [weilPairingEltN, weilPairingEltN, weilPairingEltN, AddSubgroup.coe_add]
  exact weilPairingPointElt_add (weilPairingRootN_ne_zero h2 hn S) _ hnz
    (weilPairingPointElt_weilPairingRootN_pow h2 hn S T₂)

/-! #### The alternating property -/

open Classical in
/-- **`e_n(S, S) = 1`.**  At `O` this is `weilPairingEltN_zero_left`; at an affine `S` it is
`exists_weilPairingElt_self_eq_one_of_hprin_n_of_algClosed_of_ne_zero`
(`WeilPairingAlternatingAssemblyN`) read through the bridge, its `hprin` discharged by
`exists_nsmul_divisor_eq_divisor_mulByNEndo` (`PullbackPrincipalityN`) and its `f` converted from
the projective divisor condition by `divisor_eq_of_divisorProj_eq`. -/
@[simp]
theorem weilPairingEltN_self (h2 : (2 : F) ≠ 0) {n : ℕ} (hn : ((n : ℤ) : F) ≠ 0)
    (S : W.torsion n) : weilPairingEltN h2 hn S S = 1 := by
  have hnz : n ≠ 0 := by rintro rfl; simp at hn
  cases hS : (S : W.Point) with
  | zero =>
      exact weilPairingEltN_eq_one_of_left_eq_zero h2 hn (hS.trans Point.zero_def.symm) S
  | some x y h =>
      have htors : Point.some x y h ∈ W.torsion n := hS ▸ S.2
      obtain ⟨f, hf, hdproj, g, hg, ⟨u, hu⟩, -, hone⟩ :=
        exists_weilPairingElt_self_eq_one_of_hprin_n_of_algClosed_of_ne_zero h2 hnz h htors
          (fun f hf hfdiv => exists_nsmul_divisor_eq_divisor_mulByNEndo h2 hn _ h htors hf hfdiv)
      have hroot : IsWeilRootN n
          (transcendental_xCoord_nsmul_genericPoint_of_intCast_ne_zero h2 hn) (S : W.Point) g := by
        rw [hS]
        exact isWeilRootN_some n _ h hg hf (divisor_eq_of_divisorProj_eq h hdproj) hu
      rw [weilPairingEltN_eq_weilPairingElt h2 hn hroot h hS]
      exact hone

/-! #### The divisor slot -/

open Classical in
/-- **`e_n(A ⊕ B, T) = e_n(A, T) · e_n(B, T)` when all four points are affine** — the case that *is*
an instance of the merged headline `exists_weilPairingElt_divisorSlot_add_of_ne_zero_of_hprin`
(`WeilPairingDivisorSlotBilinearHprinN`), read through the bridge with its `hprin` discharged by
`exists_nsmul_divisor_eq_divisor_mulByNEndo` (`PullbackPrincipalityN`).

⚠️ Stated for `A`, `B` rather than for `S₁`, `S₂` because `weilPairingEltN_add_left` applies it
**twice, at two different pairs**, and only one of those pairs is the one in its own statement. -/
theorem weilPairingEltN_add_left_of_ne_zero (h2 : (2 : F) ≠ 0) {n : ℕ}
    (hn : ((n : ℤ) : F) ≠ 0) {A B T : W.torsion n} (hA : A ≠ 0) (hB : B ≠ 0)
    (hAB : A + B ≠ 0) (hT : T ≠ 0) :
    weilPairingEltN h2 hn (A + B) T = weilPairingEltN h2 hn A T * weilPairingEltN h2 hn B T := by
  have key : ∀ X : W.torsion n, X ≠ 0 →
      ∃ x y, ∃ h : W.Nonsingular x y, (X : W.Point) = Point.some x y h := by
    have aux : ∀ P : W.Point, P ≠ 0 → ∃ x y, ∃ h : W.Nonsingular x y, P = Point.some x y h := by
      rintro (_ | ⟨x, y, h⟩) hP
      · exact absurd Point.zero_def.symm hP
      · exact ⟨x, y, h, rfl⟩
    exact fun X hX => aux _ fun hz => hX (ZeroMemClass.coe_eq_zero.mp hz)
  obtain ⟨xP, yP, hP, hPc⟩ := key T hT
  obtain ⟨xA, yA, hAns, hAc⟩ := key A hA
  obtain ⟨xB, yB, hBns, hBc⟩ := key B hB
  obtain ⟨xR, yR, hRns, hRc⟩ := key (A + B) hAB
  have hmP : Point.some xP yP hP ∈ W.torsion n := hPc ▸ T.2
  have hmA : Point.some xA yA hAns ∈ W.torsion n := hAc ▸ A.2
  have hmB : Point.some xB yB hBns ∈ W.torsion n := hBc ▸ B.2
  have hadd : Point.some xA yA hAns + Point.some xB yB hBns = Point.some xR yR hRns := by
    rw [← hAc, ← hBc, ← AddSubgroup.coe_add, hRc]
  obtain ⟨gA, gB, gR, hgA, hgB, hgR, ⟨fA, hfA, hdA, uA, huA⟩, ⟨fB, hfB, hdB, uB, huB⟩,
    ⟨fR, hfR, hdR, uR, huR⟩, hbil⟩ :=
    exists_weilPairingElt_divisorSlot_add_of_ne_zero_of_hprin h2 hn hP hAns hBns hRns
      hmP hmA hmB hadd
      (fun {_ _} h hmem f hf hfdiv =>
        exists_nsmul_divisor_eq_divisor_mulByNEndo h2 hn _ h hmem hf hfdiv)
  rw [weilPairingEltN_eq_weilPairingElt h2 hn (S := A + B)
        (by rw [hRc]; exact isWeilRootN_some n _ hRns hgR hfR hdR huR) hP hPc,
    weilPairingEltN_eq_weilPairingElt h2 hn (S := A)
        (by rw [hAc]; exact isWeilRootN_some n _ hAns hgA hfA hdA huA) hP hPc,
    weilPairingEltN_eq_weilPairingElt h2 hn (S := B)
        (by rw [hBc]; exact isWeilRootN_some n _ hBns hgB hfB hdB huB) hP hPc]
  exact hbil

open Classical in
/-- **`e_n(S₁ ⊕ S₂, T) = e_n(S₁, T) · e_n(S₂, T)`.**

`weilPairingEltN_add_left_of_ne_zero` is the case where all four points are affine.  ⚠️ **The other
four are not instances of it and are done here:** `T = O` (all three values are `1`), `S₁ = O` or
`S₂ = O` (the corner lemmas), and `S₁ ⊕ S₂ = O` with both affine.

⚠️ **That last case is where neither merged numeral proof transfers.**  At `n = 2` it is settled by
*a `2`-torsion point is its own negative*, which gives `S₂ = S₁` and collapses the goal to
`e_2(S₁, T) ^ 2 = 1`.  At `n = 3` (`weilPairingEltThree_add_left`, whose docstring calls it the one
place in that file where anything has to be thought about) `3 • S₁ = 0` gives `S₁ ⊕ S₁ = −S₁ = S₂`
and the goal collapses to `e_3(S₁, T) ^ 3 = 1`.  At a general `n` both steps are false:
`S₁ ⊕ S₂ = O` gives only `S₂ = −S₁`, and `e_n(S₁, T) · e_n(−S₁, T) = 1` **is** the inverse law
being proved, so copying either argument is circular.

**What works instead spends the affine case twice and adds no new mathematics.**  Choose
`U ∈ E[n]` with `U ≠ O` and `U ≠ S₁`; then `S₂ ⊕ U ≠ O` (it would force `U = −S₂ = S₁`) and
`S₁ ⊕ (S₂ ⊕ U) = U ≠ O`, so all four points of each triple are affine and

```
e(S₂ ⊕ U, T) = e(S₂, T) · e(U, T)                 at the pair (S₂, U)
e(U, T)      = e(S₁, T) · e(S₂ ⊕ U, T)            at the pair (S₁, S₂ ⊕ U)
```

Substituting the first into the second and cancelling `e(U, T) ≠ 0` gives `e(S₁, T) · e(S₂, T) = 1`,
which is the goal since `e(O, T) = 1`.

⚠️ **Such a `U` exists because `#E[n] = n² ≥ 4 > 2`** — `card_torsion_eq_sq`
(`EllipticCurves.Torsion.StructureGeneral`, `#242`/`#293`), and `2 ≤ n` because `S₁ ≠ O` lies in
`E[n]` and `E[1]` is trivial.  This is the only declaration in this file that spends the torsion
count; see the Scope section. -/
theorem weilPairingEltN_add_left (h2 : (2 : F) ≠ 0) {n : ℕ} (hn : ((n : ℤ) : F) ≠ 0)
    (S₁ S₂ T : W.torsion n) :
    weilPairingEltN h2 hn (S₁ + S₂) T
      = weilPairingEltN h2 hn S₁ T * weilPairingEltN h2 hn S₂ T := by
  by_cases hT : T = 0
  · subst hT
    rw [weilPairingEltN_zero_right, weilPairingEltN_zero_right, weilPairingEltN_zero_right, one_mul]
  by_cases hS₁ : S₁ = 0
  · subst hS₁
    rw [zero_add, weilPairingEltN_zero_left, one_mul]
  by_cases hS₂ : S₂ = 0
  · subst hS₂
    rw [add_zero, weilPairingEltN_zero_left, mul_one]
  by_cases hR : S₁ + S₂ = 0
  · have hnz : n ≠ 0 := by rintro rfl; simp at hn
    have hnF : (n : F) ≠ 0 := by exact_mod_cast hn
    have hn2 : 2 ≤ n := by
      rcases Nat.lt_or_ge n 2 with hlt | hge
      · exfalso
        have hone : n = 1 := by omega
        subst hone
        have hz : (1 : ℕ) • (S₁ : W.Point) = 0 := mem_torsion_iff.mp S₁.2
        rw [one_nsmul] at hz
        exact hS₁ (Subtype.ext (by rw [ZeroMemClass.coe_zero]; exact hz))
      · exact hge
    have hcard : Nat.card (W.torsion n) = n ^ 2 := card_torsion_eq_sq h2 hnF
    have h4 : 4 ≤ n ^ 2 := by
      calc (4 : ℕ) = 2 ^ 2 := by norm_num
        _ ≤ n ^ 2 := Nat.pow_le_pow_left hn2 2
    haveI : Finite (W.torsion n) :=
      Nat.finite_of_card_ne_zero (by rw [hcard]; exact pow_ne_zero 2 hnz)
    obtain ⟨U, hU0, hUS⟩ : ∃ U : W.torsion n, U ≠ 0 ∧ U ≠ S₁ := by
      by_contra hcon
      have hsub : (Set.univ : Set (W.torsion n)) ⊆ {0, S₁} := by
        intro U _
        by_contra hU
        exact hcon ⟨U, fun h => hU (Or.inl h), fun h => hU (Or.inr h)⟩
      have hle : ({0, S₁} : Set (W.torsion n)).ncard ≤ 2 := by
        simpa using Set.ncard_insert_le (0 : W.torsion n) ({S₁} : Set (W.torsion n))
      have hstep := Set.ncard_le_ncard hsub (Set.toFinite _)
      rw [Set.ncard_univ, hcard] at hstep
      exact absurd (h4.trans (hstep.trans hle)) (by norm_num)
    have hBU : S₂ + U ≠ 0 := by
      intro hz
      refine hUS ?_
      have h1 : S₂ = -U := add_eq_zero_iff_eq_neg.mp hz
      have h2' : S₁ = -S₂ := add_eq_zero_iff_eq_neg.mp hR
      rw [h1, neg_neg] at h2'
      exact h2'.symm
    have hsum : S₁ + (S₂ + U) = U := by rw [← add_assoc, hR, zero_add]
    have e1 : weilPairingEltN h2 hn (S₂ + U) T
        = weilPairingEltN h2 hn S₂ T * weilPairingEltN h2 hn U T :=
      weilPairingEltN_add_left_of_ne_zero h2 hn hS₂ hU0 hBU hT
    have e2 : weilPairingEltN h2 hn (S₁ + (S₂ + U)) T
        = weilPairingEltN h2 hn S₁ T * weilPairingEltN h2 hn (S₂ + U) T :=
      weilPairingEltN_add_left_of_ne_zero h2 hn hS₁ hBU (by rw [hsum]; exact hU0) hT
    rw [hsum, e1] at e2
    rw [hR, weilPairingEltN_zero_left]
    refine mul_right_cancel₀ (weilPairingEltN_ne_zero h2 hn U T) ?_
    rw [one_mul, mul_assoc]
    exact e2
  · exact weilPairingEltN_add_left_of_ne_zero h2 hn hS₁ hS₂ hR hT

/-! #### Antisymmetry -/

open Classical in
/-- **`e_n(S, T) · e_n(T, S) = 1`.**  ⚠️ Free from the alternating property and bilinearity, by
expanding `e_n(S ⊕ T, S ⊕ T) = 1` — Silverman's own derivation, and it needs none of the
`WeilPairingProductRelation*` machinery, which the existential packaging did need. -/
theorem weilPairingEltN_mul_swap (h2 : (2 : F) ≠ 0) {n : ℕ} (hn : ((n : ℤ) : F) ≠ 0)
    (S T : W.torsion n) :
    weilPairingEltN h2 hn S T * weilPairingEltN h2 hn T S = 1 := by
  have h := weilPairingEltN_self h2 hn (S + T)
  rwa [weilPairingEltN_add_left, weilPairingEltN_add_right, weilPairingEltN_add_right,
    weilPairingEltN_self, weilPairingEltN_self, one_mul, mul_one] at h

open Classical in
/-- **`e_n(T, S) = e_n(S, T)⁻¹`**, the quotable form. -/
theorem weilPairingEltN_swap (h2 : (2 : F) ≠ 0) {n : ℕ} (hn : ((n : ℤ) : F) ≠ 0)
    (S T : W.torsion n) :
    weilPairingEltN h2 hn T S = (weilPairingEltN h2 hn S T)⁻¹ :=
  eq_inv_of_mul_eq_one_left ((mul_comm _ _).trans (weilPairingEltN_mul_swap h2 hn S T))

/-! #### Non-degeneracy -/

open Classical in
/-- **Silverman III.8.1(c), as a statement about points**: if `e_n(S, ·)` is trivial on all of
`E[n]` then `S = O`.  `eq_zero_of_forall_weilPairingElt_eq_one_n` (`WeilPairingNondegenerateN`)
applied to the chosen root — and it applies *directly*, with no divisor bookkeeping, because
`IsWeilRootN` states its divisor condition in exactly the shape that theorem takes. -/
theorem eq_zero_of_forall_weilPairingEltN_eq_one (h2 : (2 : F) ≠ 0) {n : ℕ}
    (hn : ((n : ℤ) : F) ≠ 0) {S : W.torsion n}
    (hone : ∀ T : W.torsion n, weilPairingEltN h2 hn S T = 1) : S = 0 := by
  obtain ⟨hg0, f, hf, hd, u, hu⟩ := isWeilRootN_weilPairingRootN h2 hn S
  refine Subtype.ext (eq_zero_of_forall_weilPairingElt_eq_one_n h2 hn _ hf hd hg0 hu ?_)
  intro x y h hmem
  have hT := hone ⟨Point.some x y h, hmem⟩
  rwa [weilPairingEltN, weilPairingPointElt_some] at hT

/-! #### The same statements in `μ_n(F)` -/

open Classical in
@[simp]
theorem weilPairingN_zero_right (h2 : (2 : F) ≠ 0) {n : ℕ} [NeZero n] (hn : ((n : ℤ) : F) ≠ 0)
    (S : W.torsion n) : weilPairingN h2 hn S 0 = 1 :=
  (weilPairingN_eq_one_iff h2 hn S 0).mpr (weilPairingEltN_zero_right h2 hn S)

open Classical in
@[simp]
theorem weilPairingN_zero_left (h2 : (2 : F) ≠ 0) {n : ℕ} [NeZero n] (hn : ((n : ℤ) : F) ≠ 0)
    (T : W.torsion n) : weilPairingN h2 hn 0 T = 1 :=
  (weilPairingN_eq_one_iff h2 hn 0 T).mpr (weilPairingEltN_zero_left h2 hn T)

open Classical in
/-- **Bilinearity in the translation slot, in `μ_n(F)`.** -/
theorem weilPairingN_add_right (h2 : (2 : F) ≠ 0) {n : ℕ} [NeZero n] (hn : ((n : ℤ) : F) ≠ 0)
    (S T₁ T₂ : W.torsion n) :
    weilPairingN h2 hn S (T₁ + T₂) = weilPairingN h2 hn S T₁ * weilPairingN h2 hn S T₂ := by
  refine algebraMap_coe_rootsOfUnity_injective (W := W) ?_
  simp only [Subgroup.coe_mul, Units.val_mul, map_mul, algebraMap_coe_weilPairingN]
  exact weilPairingEltN_add_right h2 hn S T₁ T₂

open Classical in
/-- **Bilinearity in the divisor slot, in `μ_n(F)`.** -/
theorem weilPairingN_add_left (h2 : (2 : F) ≠ 0) {n : ℕ} [NeZero n] (hn : ((n : ℤ) : F) ≠ 0)
    (S₁ S₂ T : W.torsion n) :
    weilPairingN h2 hn (S₁ + S₂) T = weilPairingN h2 hn S₁ T * weilPairingN h2 hn S₂ T := by
  refine algebraMap_coe_rootsOfUnity_injective (W := W) ?_
  simp only [Subgroup.coe_mul, Units.val_mul, map_mul, algebraMap_coe_weilPairingN]
  exact weilPairingEltN_add_left h2 hn S₁ S₂ T

open Classical in
/-- **The alternating property in `μ_n(F)`.** -/
@[simp]
theorem weilPairingN_self (h2 : (2 : F) ≠ 0) {n : ℕ} [NeZero n] (hn : ((n : ℤ) : F) ≠ 0)
    (S : W.torsion n) : weilPairingN h2 hn S S = 1 :=
  (weilPairingN_eq_one_iff h2 hn S S).mpr (weilPairingEltN_self h2 hn S)

open Classical in
/-- **Antisymmetry in `μ_n(F)`.** -/
theorem weilPairingN_mul_swap (h2 : (2 : F) ≠ 0) {n : ℕ} [NeZero n] (hn : ((n : ℤ) : F) ≠ 0)
    (S T : W.torsion n) : weilPairingN h2 hn S T * weilPairingN h2 hn T S = 1 := by
  refine algebraMap_coe_rootsOfUnity_injective (W := W) ?_
  simp only [Subgroup.coe_mul, Units.val_mul, map_mul, algebraMap_coe_weilPairingN,
    Subgroup.coe_one, Units.val_one, map_one]
  exact weilPairingEltN_mul_swap h2 hn S T

open Classical in
theorem weilPairingN_swap (h2 : (2 : F) ≠ 0) {n : ℕ} [NeZero n] (hn : ((n : ℤ) : F) ≠ 0)
    (S T : W.torsion n) : weilPairingN h2 hn T S = (weilPairingN h2 hn S T)⁻¹ :=
  eq_inv_of_mul_eq_one_left ((mul_comm _ _).trans (weilPairingN_mul_swap h2 hn S T))

open Classical in
/-- **Non-degeneracy in `μ_n(F)`.** -/
theorem eq_zero_of_forall_weilPairingN_eq_one (h2 : (2 : F) ≠ 0) {n : ℕ} [NeZero n]
    (hn : ((n : ℤ) : F) ≠ 0) {S : W.torsion n}
    (hone : ∀ T : W.torsion n, weilPairingN h2 hn S T = 1) : S = 0 :=
  eq_zero_of_forall_weilPairingEltN_eq_one h2 hn fun T =>
    (weilPairingN_eq_one_iff h2 hn S T).mp (hone T)

/-! ### The bundled bilinear map

⚠️ This is the object the tree did not have at a general index, and the reason for the file.  Each
field below is one of the equations above; the bundling adds nothing mathematically and everything
to what a consumer can say. -/

open Classical in
/-- **The Weil pairing at a general `n` as a bilinear map**

```
weilPairingNHom h2 hn : Multiplicative E[n] →* Multiplicative E[n] →* μ_n(F),
                        S ↦ T ↦ e_n(S, T).
```

Silverman *AEC* III.8.1(a) with both slots bundled at once.  The inner `map_one'`/`map_mul'` are
`weilPairingN_zero_right`/`_add_right`; the outer two are `weilPairingN_zero_left`/`_add_left`
under `MonoidHom.ext`. -/
noncomputable def weilPairingNHom (h2 : (2 : F) ≠ 0) {n : ℕ} [NeZero n]
    (hn : ((n : ℤ) : F) ≠ 0) :
    Multiplicative (W.torsion n) →* Multiplicative (W.torsion n) →* rootsOfUnity n F where
  toFun S :=
    { toFun := fun T => weilPairingN h2 hn S.toAdd T.toAdd
      map_one' := weilPairingN_zero_right h2 hn S.toAdd
      map_mul' := fun T₁ T₂ => weilPairingN_add_right h2 hn S.toAdd T₁.toAdd T₂.toAdd }
  map_one' := MonoidHom.ext fun T => weilPairingN_zero_left h2 hn T.toAdd
  map_mul' S₁ S₂ := MonoidHom.ext fun T =>
    weilPairingN_add_left h2 hn S₁.toAdd S₂.toAdd T.toAdd

open Classical in
/-- The bundled map's values are the pairing values. -/
@[simp]
theorem weilPairingNHom_apply_apply (h2 : (2 : F) ≠ 0) {n : ℕ} [NeZero n]
    (hn : ((n : ℤ) : F) ≠ 0) (S T : Multiplicative (W.torsion n)) :
    weilPairingNHom h2 hn S T = weilPairingN h2 hn S.toAdd T.toAdd :=
  rfl

open Classical in
/-- **Non-degeneracy as a property of the bilinear map**: `MonoidHom.ker (e_n) = ⊥`.

⚠️ This is the sentence `WeilPairingPerfect`'s `General n` bullet names as the one thing missing
between that file's argument and a perfect pairing at every index: *"the argument in this file
would transcribe unchanged to any `n` for which `weilPairingNHom` and `ker_weilPairingNHom`
existed"*.  It is one `MonoidHom.ext` away from `eq_zero_of_forall_weilPairingN_eq_one`, and the
distance between the two is exactly the packaging this file supplies. -/
theorem ker_weilPairingNHom (h2 : (2 : F) ≠ 0) {n : ℕ} [NeZero n] (hn : ((n : ℤ) : F) ≠ 0) :
    MonoidHom.ker (weilPairingNHom (W := W) h2 hn) = ⊥ := by
  refine le_antisymm (fun S hS => ?_) bot_le
  rw [Subgroup.mem_bot]
  rw [MonoidHom.mem_ker] at hS
  have hval : ∀ T : W.torsion n, weilPairingN h2 hn S.toAdd T = 1 := fun T => by
    have hT := congrArg (fun φ => φ (Multiplicative.ofAdd T)) hS
    simpa using hT
  exact eq_zero_of_forall_weilPairingN_eq_one h2 hn hval

end Properties

/-! ### Recovery of the merged numeral layers, compiled

⚠️ **The two functions are not the same term, and they are the same function.**  `weilPairingTwo`
and `weilPairingN` at `n = 2` each pick a rung-5 root by `Classical.choose` at a *different*
existential, and the two pullbacks they are chosen against are different constructions —
`mulByTwoEndo` is `IsFractionRing.lift` of a coordinate-ring hom (`MulByTwoEndomorphism`),
`mulByNEndo` is `pointEndo` at the generic point (`MulByNPullback`).  What identifies the values is
that neither function depends on which root was chosen (`weilPairingPointElt_eq_of_isWeilRootTwo`,
`weilPairingPointElt_eq_of_isWeilRootN`) together with **`mulByNEndo_two`**, the merged bridge
`mulByNEndo 2 _ = mulByTwoEndo h2`.

⚠️ **The bridge is consumed through proof irrelevance and no transport is written.**
`mulByNEndo_two` is stated at `transcendental_xCoord_two_nsmul h2` while `IsWeilRootN` here carries
`transcendental_xCoord_nsmul_genericPoint_of_intCast_ne_zero h2 hn`; the two `mulByNEndo 2 _` terms
are definitionally equal because `Transcendental` is a `Prop`, so `exact` closes what `rw` would
not.  `MulByNGaloisGroup` records at its own `:97` and `:443` that this bridge is what such a
recovery has to go through.

The `n = 3` mirror is the same three lines off `mulByNEndo_three`, and is **not** here: it would put
`WeilPairingFunctionThree` into this module's import closure for a second instance of an
identification the `n = 2` pair already compiles.  ⚠️ That is a placement decision and not a claim
that the mirror is harder — it is not. -/

section Recovery

variable [IsAlgClosed F]

open Classical in
/-- **At `n = 2` this file's pairing is the merged `weilPairingEltTwo`**, value for value, on the
nose and not up to anything.  The chosen roots need not agree; the values do. -/
theorem weilPairingEltN_eq_weilPairingEltTwo (h2 : (2 : F) ≠ 0)
    (hn : (((2 : ℕ) : ℤ) : F) ≠ 0) (S T : W.torsion 2) :
    weilPairingEltN h2 hn S T = weilPairingEltTwo h2 S T := by
  obtain ⟨hg0, f, hf, hd, u, hu⟩ := isWeilRootTwo_weilPairingRootTwo h2 S
  refine weilPairingEltN_eq h2 hn (g := weilPairingRootTwo h2 S) ?_ T
  refine ⟨hg0, f, hf, by exact_mod_cast hd, u, ?_⟩
  rw [← mulByNEndo_two h2] at hu
  exact hu

open Classical in
/-- The `μ_2(F)` twin of `weilPairingEltN_eq_weilPairingEltTwo`. -/
theorem weilPairingN_eq_weilPairingTwo (h2 : (2 : F) ≠ 0)
    (hn : (((2 : ℕ) : ℤ) : F) ≠ 0) (S T : W.torsion 2) :
    weilPairingN h2 hn S T = weilPairingTwo h2 S T := by
  refine Subtype.ext (Units.ext ((algebraMap F W.FunctionField).injective ?_))
  rw [algebraMap_coe_weilPairingN, algebraMap_coe_weilPairingTwo,
    weilPairingEltN_eq_weilPairingEltTwo h2 hn]

open Classical in
/-- `weilPairingEltTwo_add_left` (`#922`), restated verbatim and proved from the general layer —
⚠️ the divisor-slot corner this file had to re-argue at a general index, recovered at the index
whose own proof it cannot copy. -/
example (h2 : (2 : F) ≠ 0) (S₁ S₂ T : W.torsion 2) :
    weilPairingEltTwo h2 (S₁ + S₂) T
      = weilPairingEltTwo h2 S₁ T * weilPairingEltTwo h2 S₂ T := by
  have hn : (((2 : ℕ) : ℤ) : F) ≠ 0 := by exact_mod_cast h2
  rw [← weilPairingEltN_eq_weilPairingEltTwo h2 hn, ← weilPairingEltN_eq_weilPairingEltTwo h2 hn,
    ← weilPairingEltN_eq_weilPairingEltTwo h2 hn]
  exact weilPairingEltN_add_left h2 hn S₁ S₂ T

open Classical in
/-- `ker_weilPairingTwoHom` (`#922`) is `ker_weilPairingNHom` at `n = 2`, through the pointwise
identification and `MonoidHom.ext`. -/
example (h2 : (2 : F) ≠ 0) : MonoidHom.ker (weilPairingTwoHom (W := W) h2) = ⊥ := by
  have hn : (((2 : ℕ) : ℤ) : F) ≠ 0 := by exact_mod_cast h2
  have hhom : weilPairingTwoHom (W := W) h2 = weilPairingNHom (W := W) h2 hn :=
    MonoidHom.ext fun S => MonoidHom.ext fun T =>
      (weilPairingN_eq_weilPairingTwo h2 hn S.toAdd T.toAdd).symm
  rw [hhom, ker_weilPairingNHom]

end Recovery

/-! ### Non-vacuity

Everything above carries `[IsAlgClosed F]` and `[W.IsElliptic]`, so `ℚ` cannot witness it; the curve
is `y² = x³ − x` over `AlgebraicClosure ℚ`, which is what the whole rung-5/rung-6 front uses, and
the torsion point is **named**: `S = (0, 0)`, at `n = 2`.

⚠️ The load-bearing certificate is the **non-degeneracy** one, and it is the last `example` below:
it asserts that some `T ∈ E[2]` pairs non-trivially with a *named* point, which no hypothesis-free
term reaches.  The bilinearity, alternating and kernel certificates are equations that hold for all
arguments, so they certify that the construction elaborates on a curve that exists — real, but
weaker, and said here rather than left to be inferred (`#916`).

⚠️ **The index is `2` and the statements are the general-`n` ones**, instantiated: the point of the
block is that the *general* declarations elaborate and are non-vacuous, not that `n = 2` is new.
Naming a `3`-smooth or a larger index would need a second named torsion point on this curve and
would certify nothing this does not. -/

section Nonvacuity

open EllipticCurves.Fixture

private lemma exampleTwo : (2 : AlgClosedQ) ≠ 0 := two_ne_zero

/-- The index condition `((n : ℤ) : F) ≠ 0` at `n = 2` over a field of characteristic `0`. -/
private lemma exampleIndex : (((2 : ℕ) : ℤ) : AlgClosedQ) ≠ 0 := by norm_num

/-- `S = (0, 0)` lies on `y² = x³ − x` and is nonsingular. -/
private lemma exampleNonsingular : (y2EqX3SubX AlgClosedQ).Nonsingular 0 0 :=
  (y2EqX3SubX AlgClosedQ).equation_iff_nonsingular.mp (by
    norm_num [y2EqX3SubX, WeierstrassCurve.Affine.equation_iff])

open Classical in
/-- `S = (0, 0)` is `2`-torsion: `2y + a₁x + a₃ = 0` reads `0 = 0`. -/
private lemma exampleTorsion :
    Point.some (0 : AlgClosedQ) 0 exampleNonsingular ∈ (y2EqX3SubX AlgClosedQ).torsion 2 :=
  (mem_torsion_two_some_iff exampleNonsingular).mpr (by norm_num [y2EqX3SubX])

open Classical in
/-- The named `2`-torsion point, as an element of `E[2]`. -/
private noncomputable def exampleS : (y2EqX3SubX AlgClosedQ).torsion 2 :=
  ⟨Point.some 0 0 exampleNonsingular, exampleTorsion⟩

open Classical in
/-- The general-`n` pairing is bilinear on a curve that exists. -/
example (S₁ S₂ T₁ T₂ : (y2EqX3SubX AlgClosedQ).torsion 2) :
    weilPairingN exampleTwo exampleIndex (S₁ + S₂) (T₁ + T₂)
      = weilPairingN exampleTwo exampleIndex S₁ T₁ * weilPairingN exampleTwo exampleIndex S₂ T₁
        * (weilPairingN exampleTwo exampleIndex S₁ T₂
          * weilPairingN exampleTwo exampleIndex S₂ T₂) := by
  rw [weilPairingN_add_right, weilPairingN_add_left, weilPairingN_add_left]

open Classical in
/-- It is alternating, and antisymmetric, on that curve. -/
example (S T : (y2EqX3SubX AlgClosedQ).torsion 2) :
    weilPairingN exampleTwo exampleIndex S S = 1 ∧
      weilPairingN exampleTwo exampleIndex T S
        = (weilPairingN exampleTwo exampleIndex S T)⁻¹ :=
  ⟨weilPairingN_self exampleTwo exampleIndex S, weilPairingN_swap exampleTwo exampleIndex S T⟩

open Classical in
/-- The bundled map exists there, and its kernel is trivial. -/
example :
    MonoidHom.ker (weilPairingNHom (W := y2EqX3SubX AlgClosedQ) exampleTwo exampleIndex) = ⊥ :=
  ker_weilPairingNHom exampleTwo exampleIndex

open Classical in
/-- **The certificate that cannot hold vacuously**: at the named point `S = (0, 0)` of
`y² = x³ − x`, some `T ∈ E[2]` pairs non-trivially.  ⚠️ Stated as an existence over `E[2]` with the
*divisor* point fixed and named, which is what makes it a statement about this curve and not a
schema. -/
example : ∃ T : (y2EqX3SubX AlgClosedQ).torsion 2,
    weilPairingN exampleTwo exampleIndex exampleS T ≠ 1 := by
  by_contra hcon
  have hall : ∀ T : (y2EqX3SubX AlgClosedQ).torsion 2,
      weilPairingN exampleTwo exampleIndex exampleS T = 1 := fun T =>
    not_not.mp fun hne => hcon ⟨T, hne⟩
  have h0 : exampleS = 0 := eq_zero_of_forall_weilPairingN_eq_one exampleTwo exampleIndex hall
  exact Point.some_ne_zero exampleNonsingular (congrArg Subtype.val h0)

end Nonvacuity

end WeierstrassCurve.Affine
