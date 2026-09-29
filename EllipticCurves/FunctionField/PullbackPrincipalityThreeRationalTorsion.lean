/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import EllipticCurves.Fixtures
import EllipticCurves.FunctionField.MulByThreeResidueDegree
import EllipticCurves.FunctionField.PullbackPrincipalityThree
import EllipticCurves.FunctionField.PullbackPrincipalityTwoRationalTorsion

/-!
# `[3]∗((S) − (O))` is principal with `(2 : F) ≠ 0` and `(3 : F) ≠ 0`, at a rational `E[3]`

`EllipticCurves.FunctionField.PullbackPrincipalityThree` discharges `hprin` at `n = 3` — the `#418`
hypothesis of `exists_gS_three` — over an **algebraically closed** base field.  This file replaces
that instance by the two hypotheses it was ever used for:

* `hcard : Nat.card (W.torsion 3) = 9`, i.e. `E[3] ⊆ E(F)`;
* `hP : (3 : ℕ) • P = S` for the `3`-torsion point `S` in question.

⚠️ **The title names two of the four hypotheses and that is a column limit, not a retraction**
(`#1733`): `(2 : F) ≠ 0` and `(3 : F) ≠ 0` are in it, *"at a rational `E[3]`"* is `hcard`, and the
tripling `hP` is the one that did not fit.  ⚠️ `README.md` `### Scope of the rules above` rules that
a heading is one source line and that a reach clause which does not fit the shortened title is
stated in the prose below rather than wrapped; it is stated here, and every headline below names all
four.  The title as written is **91** columns by Python `len()`; naming `hP` as well —
*"… at a rational `E[3]` and a tripling `P`"* — is **110**.

⚠️ **`(2 : F) ≠ 0` and `(3 : F) ≠ 0` are not rationality facts and are not removable.**  They are
the explicit binders `mulByThreeEndo`, `comapProjPointThree`, `ramificationIdxThree`,
`residueDegreeThree` and `pullbackDivisorThree` all take, and `mulByThreeEndo h2 h3 f` occurs in the
headline's own *statement*, so no proof change can drop either.  The headline
`exists_nsmul_divisor_eq_divisor_mulByThreeEndo_of_card` and its consumer form
`exists_gS_three_of_card` are therefore available over any field of characteristic `≠ 2, 3`.

⚠️ **`hsep` is not a fifth hypothesis, and this exemption is declared rather than assumed.**  The
`Algebra.IsSeparable ↥(mulByThreeEndo h2 h3).fieldRange W.FunctionField` that the fibre count needs
is **discharged from `hcard`** inside the two headlines, by
`isSeparable_mulByThreeEndoFieldRange_of_card` below.  It is carried as an explicit binder on the
intermediate statements only, and **every one of those names it** — a reach clause there lists five
items, not four.  The `n = 2` file declares the identical exemption for the identical reason.

## ⚠️ What this does *not* do

**It does not discharge `#962`**, and must not be reported as doing so.  `#962` asks for `hprin`
over a field where `E[3]` is *not* rational and `S` has *no* rational tripling; reaching that from
here needs the `n = 3` analogue of `EllipticCurves.Torsion.HalvingGaloisTower` — a finite Galois
extension of `F` over which **both** hypotheses become true — and nothing here builds it.

⚠️ **The `n = 2` ledger closed in three files and this is the middle one.**
`EllipticCurves.FunctionField.PullbackPrincipalityTwoGeneral` (`#2029`) is the assembly at `n = 2`,
and step 3 of its route is *"`…_of_card` over `N` gives a `g` with `2 · div g = div ([2]∗ f)`
upstairs"* — it **consumes** the middle file.  At `n = 3` that middle file did not exist, so an
assembly written before this one would have had nothing to descend to.  ⚠️ **What this file supplies
is the target of a descent, not the descent.**

⚠️ **The counting floor at `n = 3` is already in the tree and is a different step.**
`EllipticCurves.Torsion.ThreeDivisionField` builds `threeDivisionGaloisField W`, finite **Galois**
over `F` and carrying `#E[3] = 9` (`card_torsion_three_threeDivisionGaloisField`,
`isGalois_threeDivisionGaloisField`).  That is step 1 of the `n = 2` route at `n = 3`; the tripling
half of step 1, and the descent of step 4, are what remain.  ⚠️ **`hcard` over that field is not
invoked below** — this file proves nothing about any particular field.

## The counting argument, which is the mathematical content

Over the fibre of `[3]∗` above a rational point `S`:

* the nine points `P ⊕ R`, `R ∈ E[3]`, are distinct (`projPointOfPoint_add_injective_three` with
  `hcard`) and lie in the fibre (`comapProjPointThree_add_torsion_three`).  ⚠️ **Each of the nine is
  also residually trivial, and that is CONTEXT and not a step of the count**: `f_p` here is
  `residueDegreeThree h2 h3 p` and **not** `residueDegreeProj W p`, so
  `residueDegreeProj_projPointOfPoint`
  (`EllipticCurves.FunctionField.PlaceInertiaGeneral`, which needs no hypothesis on `F`) reaches it
  only through the bridge `residueDegreeThree_eq_one_of_residueDegreeProj_eq_one`
  (`EllipticCurves.FunctionField.MulByThreeResidueDegree`); there is no `[3]∗` analogue of the
  composite `residueDegreeTwo_projPointOfPoint`, and none is needed, because the count below uses
  only `1 ≤ e_p · f_p`;
* `e_p ≥ 1` everywhere (`ramificationIdxThree_pos`) and `f_p ≥ 1` everywhere
  (`residueDegreeThree_pos` below, the `[3]∗` instantiation of `residueDegreeComap_pos`);
* `∑_{p ↦ q} e_p · f_p = 9`
  (`sum_ramificationIdxThree_mul_residueDegreeThree_of_isSeparable`).

Nine terms of a nine-term bound already exhaust it, so every `e_p` is `1` and the fibre is exactly
the coset.  ⚠️ **The second bullet is not decoration.**  Without `f_p ≥ 1` a tenth place could sit
in the fibre contributing `0` to the sum, and both the unramifiedness and the fibre description
would fail.  The `[IsAlgClosed F]` route never needed it, because there every `f_p` is `1` outright
(`residueDegreeProj_eq_one`); over an arbitrary field the `f_p` are unknown and only their
positivity is available.

## ⚠️ Where the uncollapsed identity comes from, and why it is not in this file

`sum_ramificationIdxThree_mul_residueDegreeThree_of_isSeparable` is the one input this rung needed
that the tree did not have, and it is added by this branch to
`EllipticCurves.FunctionField.PlaceInertiaGeneral`, **beside its `[2]∗` twin and at no import
cost** — that file already imports `EllipticCurves.FunctionField.PlaceDegreeComparison`, which
imports `EllipticCurves.FunctionField.MulByThreeResidueDegree`, so the whole `MulByThree*` place
layer is in its scope.  ⚠️ **It is therefore *not* stated here**, and the `## Scope` clause of that
file which said `[3]∗` was not instantiated in it is retired there rather than worked around here.

⚠️ **`sum_ramificationIdxThree_mul_residueDegreeThree_of_charZero` (`MulByNInertia`, `#1221`) would
not have served.**  The consumer of this rung is a descent over `threeDivisionGaloisField W`, which
has the characteristic of `F`; `[CharZero F]` is unavailable there and `hsep` is exactly what the
`n = 2` file carries instead.

## ⚠️ Why `n = 3` and not general `n`, measured rather than asserted

`EllipticCurves.FunctionField.PullbackPrincipalityN` proves the `F̄` principality at **every**
index, and its own prose says it *"transposes every step"* of the `n = 3` file with `3 ↦ n`.  So the
obvious question is why this rung is not written there instead, and the answer is not that it cannot
be:

* the general-`n` fibre description `pullbackDivisorN_single_eq_sum_torsion_of_ne_zero`
  (`EllipticCurves.FunctionField.MulByNFibre`) sits **inside** that file's `section IsAlgClosed`, so
  it is not closure-free and the `_of_card` work at general `n` is the same work, not a
  specialisation of finished work;
* the general-`n` uncollapsed identity `sum_ramificationIdxN_mul_residueDegreeN_of_isSeparable`
  (`EllipticCurves.FunctionField.MulByNInertia`) carries `hn : n ≠ 0`, a `3`-smoothness condition
  `hfac` and a transcendence hypothesis `h`, because the degree it reads off —
  `finrank_mulByNEndoFieldRange_of_smooth` — is only known for `3`-smooth `n` in this tree.
  ⚠️ **The `n = 3` statements below carry none of those three**, because
  `finrank_mulByThreeFieldRange` is unconditional at this index.

⚠️ **So a `3`-smooth-`n` `_of_card` rung is a real and unattempted piece of work, not an
impossibility, and it is not attempted here.**  The consumer this rung exists for is `#962`'s
`n = 3` ledger row and the tripling tower that row needs, both of which are `n = 3`; and a general
form would put `hfac` and a transcendence binder on every statement that a descent at `n = 3` would
then have to carry.  Nothing below is a step towards the general form beyond being its `n = 3`
instance.

## Main statements

Reach clauses below are complete, per `README.md` `## Docstring conventions` option (a).

* `…CoordinateRing.isSeparable_mulByThreeEndoFieldRange_of_card` — the Galois package at `hcard`,
  over a field with `(2 : F) ≠ 0` and `(3 : F) ≠ 0`.
* `…CoordinateRing.residueDegreeThree_pos` — `f_p > 0` at **every** place of the projective curve,
  over an arbitrary field with `(2 : F) ≠ 0` and `(3 : F) ≠ 0`: the `[3]∗` instantiation of
  `residueDegreeComap_pos`
  (`EllipticCurves.FunctionField.PullbackPrincipalityTwoRationalTorsion`), which is stated for an
  arbitrary `φ`.  No separability, no module-finiteness, no fibre.
* `…CoordinateRing.ramificationIdxThree_eq_one_of_card`,
  `…CoordinateRing.fibre_comapProjPointThree_eq_range_of_card` — the fibre over a rational point,
  described without an algebraic closure, over a field with `(2 : F) ≠ 0` and `(3 : F) ≠ 0`, at a
  rational `E[3]`, a tripling `P` and `hsep`.
* **`WeierstrassCurve.Affine.exists_nsmul_divisor_eq_divisor_mulByThreeEndo_of_card`** — `hprin` at
  `n = 3`, over an arbitrary field with `(2 : F) ≠ 0` and `(3 : F) ≠ 0`, at a nonsingular
  `3`-torsion point `S` with a rational `E[3]` and a tripling `P`, for a nonzero `f` whose divisor
  is `3·(S)`.
* **`WeierstrassCurve.Affine.exists_gS_three_of_card`** — rung 5 at `n = 3`, over an arbitrary
  field with `(2 : F) ≠ 0` and `(3 : F) ≠ 0`, on a rational `E[3]` and a tripling `P` at the same
  `S`; it produces the `f` itself.

`Recovery` derives the merged `exists_nsmul_divisor_eq_divisor_mulByThreeEndo` and
`exists_gS_three_of_isAlgClosed` from these, by supplying `card_torsion_three` and
`exists_nsmul_three_eq`.

## ⚠️ There is NO non-vacuity certificate for `hcard` here, and the reason is a theorem

`#916` asks for one and this file **cannot** pay it over `ℚ`, for a reason that is worth writing
down rather than leaving as a silent omission:

* `hcard` says `E[3] ⊆ E(F)`, so `Gal` acts trivially on `E[3]`; the Weil pairing
  `e₃ : E[3] × E[3] → μ₃` is Galois-equivariant and surjective, so `Gal` acts trivially on `μ₃`
  too, i.e. `μ₃ ⊆ F`.  ⚠️ **`μ₃ ⊄ ℚ`, so `hcard` is VACUOUS over `ℚ`** and no rational curve can
  carry it.  ⚠️ **The citation for that argument is Silverman III.8.1, not this tree**: the `n = 3`
  non-degeneracy this tree has, `eq_zero_of_forall_weilPairingElt_eq_one_three`
  (`EllipticCurves.FunctionField.WeilPairingNondegenerateThree`), carries `[IsAlgClosed F]`, and
  over an algebraically closed field the conclusion `μ₃ ⊆ F` is free and says nothing.  This is the
  `n = 3` face of the obstruction `#2105` records one rung down, whose resolution there was a
  `ZMod 7` fixture.
* `hP` and `hcard` together force more: `3 • P = S ≠ 0` and `9 • P = 3 • S = 0`, so `P` has order
  exactly `9` and `E(F) ⊇ ℤ/9 × ℤ/3`.  Over a **finite** field `𝔽_q` that needs `27 ∣ #E(𝔽_q)`
  with `q ≡ 1 mod 3`, and Hasse's bound `#E ≤ q + 1 + 2√q` then excludes every `q < 19`.  ⚠️ **This
  is a necessary condition and not an existence claim**: `q = 19` is the smallest candidate the two
  bounds leave, and whether a curve over `𝔽_19` with `E(𝔽_19) ≅ ℤ/9 × ℤ/3` exists is not settled
  here.
* ⚠️ **Neither bullet is formalised below.**  They are stated as the reason a `ℚ` fixture is absent,
  and the `Recovery` section is what shows the four hypotheses are jointly satisfiable at all — over
  `F̄`, where both rationality facts are theorems.

What the `Nonvacuity` section **does** certify over `ℚ` is the `hsep`-only half of the chain, which
is the half that consumes the new identity: the nine-element fibre bound
`card_fibre_comapProjPointThree_le_nine_of_isSeparable` applies to `y² = x³ − x` over `ℚ`, with
`hsep` produced from `[CharZero ℚ]` and not assumed.

## ⚠️ What is *not* here

* **The tripling tower.**  A finite Galois extension of `F` over which a given `S ∈ E[3]` acquires
  a `P` with `3 • P = S` is the `n = 3` analogue of `EllipticCurves.Torsion.HalvingExtension` and
  `EllipticCurves.Torsion.HalvingGaloisTower`, and **nothing below builds or mentions one**.
* **The assembly.**  There is no `PullbackPrincipalityThreeGeneral` in this tree and nothing below
  is a step of one beyond being its target.
* **No characteristic-`2` or characteristic-`3` statement.**  `(2 : F) ≠ 0` and `(3 : F) ≠ 0` are
  assumed throughout.
* **Nothing about a non-rational `S`.**  Every statement below is at an affine point of `W(F)`.
* **No count of `E[3]` over `F` is claimed.**  `hcard` is a hypothesis at every occurrence below;
  nothing proves it, and nothing below says which fields satisfy it.
* **`e = 1` for `[3]∗` in general is not stated.**  `ramificationIdxThree_eq_one_of_card` is about
  places in the fibre over a *rational* point and needs `hcard`, `hP` and `hsep` to say even that.
* **Rung 6 is not here.**  The translation slot and non-degeneracy
  (`EllipticCurves.FunctionField.WeilPairingTranslationSlotHprin`) consume `hprin` and are not
  restated; what this file does for them is remove their gate at `n = 3` under two rationality
  facts.

## References

* [J. H. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.8.
-/

open Module IsLocalRing IsDedekindDomain IsDedekindDomain.HeightOneSpectrum

namespace WeierstrassCurve.Affine

variable {F : Type*} [Field F] {W : Affine F} [IsDedekindDomain W.CoordinateRing]
  [DecidableEq F] [W.IsElliptic]

namespace CoordinateRing

/-! ### The Galois package at a rational `E[3]` -/

omit [IsDedekindDomain W.CoordinateRing] [W.IsElliptic] in
/-- **`|E[3]| = 9` in the multiplicative packaging**, from the count rather than from the closure.
This is `card_torsionThreeMul` (`EllipticCurves.FunctionField.TranslationActionThree`) with `hcard`
in place of `[IsAlgClosed F]`.

⚠️ The `convert` is the whole `DecidableEq` bridge of this file: `TorsionThreeMul W` bakes in
`Classical.propDecidable` while `hcard` is stated at the ambient binder, and the two are
propositionally but not syntactically equal.  It is discharged by `Subsingleton.elim`. -/
theorem card_torsionThreeMul_of_card (hcard : Nat.card (W.torsion 3) = 9) :
    Nat.card (TorsionThreeMul W) = 9 :=
  (Nat.card_congr Multiplicative.toAdd).trans (by convert hcard)

omit [IsDedekindDomain W.CoordinateRing] [W.IsElliptic] in
/-- `E[3]` is finite once it has nine elements. -/
theorem finite_torsionThreeMul_of_card (hcard : Nat.card (W.torsion 3) = 9) :
    Finite (TorsionThreeMul W) :=
  Nat.finite_of_card_ne_zero (by rw [card_torsionThreeMul_of_card hcard]; omega)

omit [IsDedekindDomain W.CoordinateRing] in
open Classical in
/-- **Artin's theorem for the translation action**, at a rational `E[3]`:
`[F(W) : Fixed(E[3])] = 9`.  `finrank_fixedFieldThree` (`MulByThreeGalois`) with `hcard` in place of
`[IsAlgClosed F]`; the proof is unchanged. -/
theorem finrank_fixedFieldThree_of_card (hcard : Nat.card (W.torsion 3) = 9) :
    finrank ↥(fixedFieldThree W) W.FunctionField = 9 := by
  haveI := finite_torsionThreeMul_of_card hcard
  haveI : Fintype (TorsionThreeMul W) := Fintype.ofFinite _
  have h : finrank ↥(FixedPoints.subfield (TorsionThreeMul W) W.FunctionField) W.FunctionField
      = 9 := by
    rw [FixedPoints.finrank_eq_card (TorsionThreeMul W) W.FunctionField, ← Nat.card_eq_fintype_card,
      card_torsionThreeMul_of_card hcard]
  exact h

omit [IsDedekindDomain W.CoordinateRing] in
open Classical in
/-- **`Fixed(E[3]) = [3]∗F(W)` at a rational `E[3]`, with `(2 : F) ≠ 0` and `(3 : F) ≠ 0`.**  The
sandwich of `fixedFieldThree_eq_mulByThreeFieldRange`: both outer degrees are `9`, the inner
inclusion is `mulByThreeEndo_mem_fixedPoints`, and `IntermediateField.eq_of_le_of_finrank_eq'`
closes it.  `finrank_mulByThreeFieldRange` (`MulByThreeDegree`) never needed a closure. -/
theorem fixedFieldThree_eq_mulByThreeFieldRange_of_card (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0)
    (hcard : Nat.card (W.torsion 3) = 9) :
    (mulByThreeEndoAlgHom (W := W) h2 h3).fieldRange = fixedFieldThree W := by
  have hdeg : finrank ↥(mulByThreeEndoAlgHom (W := W) h2 h3).fieldRange W.FunctionField = 9 :=
    finrank_mulByThreeFieldRange h2 h3
  haveI : FiniteDimensional ↥(mulByThreeEndoAlgHom (W := W) h2 h3).fieldRange W.FunctionField :=
    Module.finite_of_finrank_pos (by rw [hdeg]; norm_num)
  refine IntermediateField.eq_of_le_of_finrank_eq' ?_
    (by rw [hdeg, finrank_fixedFieldThree_of_card hcard])
  rintro _ ⟨f, rfl⟩
  exact mulByThreeEndo_mem_fixedPoints h2 h3 f

omit [IsDedekindDomain W.CoordinateRing] in
open Classical in
/-- **`F(W) / [3]∗F(W)` is separable at a rational `E[3]`, with `(2 : F) ≠ 0` and
`(3 : F) ≠ 0`**, in the `IntermediateField` presentation. -/
theorem isSeparable_mulByThreeFieldRange_of_card (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0)
    (hcard : Nat.card (W.torsion 3) = 9) :
    Algebra.IsSeparable ↥(mulByThreeEndoAlgHom (W := W) h2 h3).fieldRange W.FunctionField := by
  haveI := finite_torsionThreeMul_of_card hcard
  haveI : Algebra.IsSeparable ↥(fixedFieldThree W) W.FunctionField := inferInstanceAs
    (Algebra.IsSeparable ↥(FixedPoints.subfield (TorsionThreeMul W) W.FunctionField)
      W.FunctionField)
  rw [fixedFieldThree_eq_mulByThreeFieldRange_of_card h2 h3 hcard]
  infer_instance

omit [IsDedekindDomain W.CoordinateRing] in
open Classical in
/-- **Separability in the `Subfield` presentation**, which is the one the fibre count consumes, at a
rational `E[3]` and with `(2 : F) ≠ 0` and `(3 : F) ≠ 0`.  Carried across
`mulByThreeFieldRangeEquivSubfield`, the identity on elements.

⚠️ **This is the declaration that makes `hsep` not a hypothesis of the two headlines** — see the
exemption declared in the module docstring — and it is also what
`sum_ramificationIdxThree_mul_residueDegreeThree_of_isSeparable`
(`EllipticCurves.FunctionField.PlaceInertiaGeneral`) names as the consumer it was added for. -/
theorem isSeparable_mulByThreeEndoFieldRange_of_card (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0)
    (hcard : Nat.card (W.torsion 3) = 9) :
    Algebra.IsSeparable ↥(mulByThreeEndo (W := W) h2 h3).fieldRange W.FunctionField := by
  haveI := isSeparable_mulByThreeFieldRange_of_card h2 h3 hcard
  exact Algebra.IsSeparable.of_equiv_equiv (mulByThreeFieldRangeEquivSubfield h2 h3)
    (RingEquiv.refl W.FunctionField) (by ext a; rfl)

/-! ### The fibre over a rational point, without an algebraic closure -/

omit [DecidableEq F] in
/-- **`f_p > 0` for `[3]∗`, at every place of the projective curve**, over an arbitrary field with
`(2 : F) ≠ 0` and `(3 : F) ≠ 0` — the instantiation of `residueDegreeComap_pos`
(`EllipticCurves.FunctionField.PullbackPrincipalityTwoRationalTorsion`), which is stated for an
arbitrary `φ`.  ⚠️ It applies **on the nose**: `residueDegreeThree` is *definitionally*
`residueDegreeComap (mulByThreeEndo_algebraMap_base h2 h3) (mulByThreeEndo_isIntegralElem h2 h3)`,
so nothing is transported.

⚠️ No separability, no module-finiteness and no fibre-membership hypothesis: this holds at *every*
`p : ProjPoint W`, not only at the places lying over a named `q`. -/
theorem residueDegreeThree_pos (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) (p : ProjPoint W) :
    0 < residueDegreeThree h2 h3 p :=
  residueDegreeComap_pos (mulByThreeEndo_algebraMap_base h2 h3)
    (mulByThreeEndo_isIntegralElem h2 h3) p

omit [DecidableEq F] in
/-- Every summand of the fundamental identity is at least `1`, which is what turns a sum of `9` into
a bound on the number of places, over an arbitrary field with `(2 : F) ≠ 0` and `(3 : F) ≠ 0`.  Both
factors are positive: `e_p` by `ramificationIdxThree_pos` and `f_p` by the previous lemma.

⚠️ Like the two positivity lemmas it rests on, this is a statement about an *arbitrary* place: it
needs neither separability nor membership of a fibre.  Only the identity `∑ e_p · f_p = 9` those
summands are compared against does, which is why `hsep` survives on the next lemma and not here. -/
theorem one_le_ramificationIdxThree_mul_residueDegreeThree (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0)
    (p : ProjPoint W) :
    1 ≤ (ramificationIdxThree h2 h3 p).toNat * residueDegreeThree h2 h3 p := by
  have he : 0 < (ramificationIdxThree h2 h3 p).toNat := by
    have := ramificationIdxThree_pos h2 h3 p; omega
  have hf := residueDegreeThree_pos h2 h3 p
  exact Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by omega))

omit [DecidableEq F] in
/-- **At most nine places lie above any place of `[3]∗F(W)`**, over an arbitrary field with
`(2 : F) ≠ 0`, `(3 : F) ≠ 0` and separability carried.

`card_fibre_comapProjPointThree_le_nine` (`MulByThreeRamification`) is this bound over `F̄`, where
it comes from the collapsed `∑ e_p = 9`.  Here it comes from the uncollapsed
`∑ e_p · f_p = 9`, whose summands are bounded below by `1` for the two independent reasons
above. -/
theorem card_fibre_comapProjPointThree_le_nine_of_isSeparable (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0)
    (hsep : Algebra.IsSeparable ↥(mulByThreeEndo (W := W) h2 h3).fieldRange W.FunctionField)
    (q : ProjPoint W) :
    (finite_comapProjPointThree_preimage_singleton h2 h3 q).toFinset.card ≤ 9 := by
  rw [Finset.card_eq_sum_ones,
    ← sum_ramificationIdxThree_mul_residueDegreeThree_of_isSeparable h2 h3 hsep q]
  exact Finset.sum_le_sum fun p _ => one_le_ramificationIdxThree_mul_residueDegreeThree h2 h3 p

/-- **The fibre of `[3]` over a rational point has exactly nine elements**, over an arbitrary field
with `(2 : F) ≠ 0` and `(3 : F) ≠ 0`, at a rational `E[3]`, a tripling `P` and separability carried.

`≤ 9` is the previous lemma; `≥ 9` is the coset `{ P ⊕ R : R ∈ E[3] }`, nine distinct elements of
the fibre by `hcard` and `projPointOfPoint_add_injective_three`.

This is `card_fibre_comapProjPointThree_projPointOfPoint` (`MulByThreeFibre`) with `hcard` and `hP`
replacing `card_torsion_three` and `exists_nsmul_three_eq`. -/
theorem card_fibre_comapProjPointThree_projPointOfPoint_of_card (h2 : (2 : F) ≠ 0)
    (h3 : (3 : F) ≠ 0)
    (hsep : Algebra.IsSeparable ↥(mulByThreeEndo (W := W) h2 h3).fieldRange W.FunctionField)
    (hcard : Nat.card (W.torsion 3) = 9) {S P : W.Point} (hP : (3 : ℕ) • P = S) :
    (finite_comapProjPointThree_preimage_singleton h2 h3
      (projPointOfPoint W S)).toFinset.card = 9 := by
  classical
  haveI := W.finite_torsion_three (F := F) h3
  haveI := Fintype.ofFinite (W.torsion 3)
  refine le_antisymm (card_fibre_comapProjPointThree_le_nine_of_isSeparable h2 h3 hsep _) ?_
  have hc : Fintype.card (W.torsion 3) = 9 := by rw [← Nat.card_eq_fintype_card, hcard]
  rw [← hc, ← Finset.card_univ]
  exact Finset.card_le_card_of_injOn (fun R => projPointOfPoint W (P + R))
    (fun R _ => (Set.Finite.mem_toFinset _).2 (comapProjPointThree_add_torsion_three h2 h3 hP R))
    (Set.injOn_of_injective (projPointOfPoint_add_injective_three P))

/-- **The fibre of `[3]` over a rational point *is* the coset `{ P ⊕ R : R ∈ E[3] }`**, over an
arbitrary field with `(2 : F) ≠ 0` and `(3 : F) ≠ 0`, at a rational `E[3]`, a tripling `P` and
separability carried.  Nine distinct elements inside a nine-element set; no further geometry,
exactly as in `fibre_comapProjPointThree_eq_range`. -/
theorem fibre_comapProjPointThree_eq_range_of_card (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0)
    (hsep : Algebra.IsSeparable ↥(mulByThreeEndo (W := W) h2 h3).fieldRange W.FunctionField)
    (hcard : Nat.card (W.torsion 3) = 9) {S P : W.Point} (hP : (3 : ℕ) • P = S) :
    comapProjPointThree h2 h3 ⁻¹' {projPointOfPoint W S}
      = Set.range fun R : W.torsion 3 => projPointOfPoint W (P + R) := by
  classical
  haveI := W.finite_torsion_three (F := F) h3
  haveI := Fintype.ofFinite (W.torsion 3)
  have hfin := finite_comapProjPointThree_preimage_singleton h2 h3 (projPointOfPoint W S)
  have hsub : (Set.range fun R : W.torsion 3 => projPointOfPoint W (P + R))
      ⊆ comapProjPointThree h2 h3 ⁻¹' {projPointOfPoint W S} := by
    rintro p ⟨R, rfl⟩
    exact comapProjPointThree_add_torsion_three h2 h3 hP R
  refine (Set.eq_of_subset_of_ncard_le hsub ?_ hfin).symm
  have h1 : (comapProjPointThree h2 h3 ⁻¹' {projPointOfPoint W S}).ncard = 9 := by
    rw [Set.ncard_eq_toFinset_card _ hfin]
    exact card_fibre_comapProjPointThree_projPointOfPoint_of_card h2 h3 hsep hcard hP
  have h2' : (Set.range fun R : W.torsion 3 => projPointOfPoint W (P + R)).ncard = 9 := by
    rw [← Nat.card_coe_set_eq, Nat.card_range_of_injective (projPointOfPoint_add_injective_three P),
      hcard]
  omega

/-- **`[3]` is unramified over a rational point**, over an arbitrary field with `(2 : F) ≠ 0` and
`(3 : F) ≠ 0`, at a rational `E[3]`, a tripling `P` and separability carried.

Eight of the nine other fibre terms are already `≥ 1` each and the sum is `9`, so the term at `p` is
`1`; being a product of two positive naturals it forces `e_p = 1`.

⚠️ Compare `ramificationIdxThree_eq_one_of_comapProjPointThree_eq_projPointOfPoint`, which reads the
same conclusion off the *collapsed* identity and is `F̄`-only for that reason.  The extra hypotheses
here are exactly the two rationality facts; `hsep` is not a third, see the module docstring. -/
theorem ramificationIdxThree_eq_one_of_card (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0)
    (hsep : Algebra.IsSeparable ↥(mulByThreeEndo (W := W) h2 h3).fieldRange W.FunctionField)
    (hcard : Nat.card (W.torsion 3) = 9) {p : ProjPoint W} {S P : W.Point} (hP : (3 : ℕ) • P = S)
    (hp : comapProjPointThree h2 h3 p = projPointOfPoint W S) :
    ramificationIdxThree h2 h3 p = 1 := by
  classical
  have hfin := finite_comapProjPointThree_preimage_singleton h2 h3 (projPointOfPoint W S)
  set s := hfin.toFinset with hs
  have hmem : p ∈ s := (Set.Finite.mem_toFinset hfin).2 hp
  have hcards : s.card = 9 :=
    card_fibre_comapProjPointThree_projPointOfPoint_of_card h2 h3 hsep hcard hP
  have hsum : ∑ r ∈ s, (ramificationIdxThree h2 h3 r).toNat * residueDegreeThree h2 h3 r = 9 :=
    sum_ramificationIdxThree_mul_residueDegreeThree_of_isSeparable h2 h3 hsep _
  have hsplit : (ramificationIdxThree h2 h3 p).toNat * residueDegreeThree h2 h3 p
      + ∑ r ∈ s.erase p, (ramificationIdxThree h2 h3 r).toNat * residueDegreeThree h2 h3 r = 9 := by
    rw [Finset.add_sum_erase _
      (fun r => (ramificationIdxThree h2 h3 r).toNat * residueDegreeThree h2 h3 r) hmem]
    exact hsum
  have hlow : (s.erase p).card
      ≤ ∑ r ∈ s.erase p, (ramificationIdxThree h2 h3 r).toNat * residueDegreeThree h2 h3 r := by
    simpa using Finset.card_nsmul_le_sum (s.erase p)
      (fun r => (ramificationIdxThree h2 h3 r).toNat * residueDegreeThree h2 h3 r) 1
      (fun r _ => one_le_ramificationIdxThree_mul_residueDegreeThree h2 h3 r)
  have hec : (s.erase p).card = 8 := by rw [Finset.card_erase_of_mem hmem, hcards]
  have hprod : 1 ≤ (ramificationIdxThree h2 h3 p).toNat * residueDegreeThree h2 h3 p :=
    one_le_ramificationIdxThree_mul_residueDegreeThree h2 h3 p
  set k := (ramificationIdxThree h2 h3 p).toNat * residueDegreeThree h2 h3 p with hk
  have hone : k = 1 := by omega
  have hE : (ramificationIdxThree h2 h3 p).toNat = 1 :=
    Nat.eq_one_of_mul_eq_one_right (hk.symm.trans hone)
  have hepos := ramificationIdxThree_pos h2 h3 p
  omega

/-! ### The fibre description of `[3]∗` -/

/-- **`[3]∗(S) = ∑_{p ↦ S} (p)`, every coefficient `1`**, over an arbitrary field with
`(2 : F) ≠ 0` and `(3 : F) ≠ 0`, at a rational `E[3]`, a tripling `P` and separability carried: the
previous lemma read into the definition of `pullbackDivisorThree`. -/
theorem pullbackDivisorThree_single_projPointOfPoint_of_card (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0)
    (hsep : Algebra.IsSeparable ↥(mulByThreeEndo (W := W) h2 h3).fieldRange W.FunctionField)
    (hcard : Nat.card (W.torsion 3) = 9) {S P : W.Point} (hP : (3 : ℕ) • P = S) :
    pullbackDivisorThree h2 h3 (Finsupp.single (projPointOfPoint W S) (1 : ℤ))
      = ∑ p ∈ (finite_comapProjPointThree_preimage_singleton h2 h3
          (projPointOfPoint W S)).toFinset, Finsupp.single p (1 : ℤ) := by
  classical
  ext q
  have hrhs : (∑ p ∈ (finite_comapProjPointThree_preimage_singleton h2 h3
        (projPointOfPoint W S)).toFinset, Finsupp.single p (1 : ℤ)) q
      = if comapProjPointThree h2 h3 q = projPointOfPoint W S then 1 else 0 := by
    rw [Finset.sum_apply', Finset.sum_congr rfl fun p _ => Finsupp.single_apply,
      Finset.sum_ite_eq' _ q fun _ => (1 : ℤ)]
    simp only [Set.Finite.mem_toFinset, Set.mem_preimage, Set.mem_singleton_iff]
  rw [pullbackDivisorThree_apply, hrhs]
  by_cases hq : comapProjPointThree h2 h3 q = projPointOfPoint W S
  · rw [hq, Finsupp.single_eq_same, mul_one,
      ramificationIdxThree_eq_one_of_card h2 h3 hsep hcard hP hq, if_pos rfl]
  · rw [Finsupp.single_apply, if_neg fun hc => hq hc.symm, mul_zero, if_neg hq]

/-- **`[3]∗(S) = ∑_{R ∈ E[3]} (P ⊕ R)`**, over an arbitrary field with `(2 : F) ≠ 0` and
`(3 : F) ≠ 0`, at a rational `E[3]`, a tripling `P` and separability carried.  `#819`'s formula in
the shape `#418` consumes it, with the closure removed.

The `[Fintype (W.torsion 3)]` is carried in the statement for the reason `#763` gives: the sum
cannot be written without it, and `Fintype.ofFinite` in a statement is a noncomputable leak. -/
theorem pullbackDivisorThree_single_eq_sum_torsion_of_card [Fintype (W.torsion 3)]
    (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0)
    (hsep : Algebra.IsSeparable ↥(mulByThreeEndo (W := W) h2 h3).fieldRange W.FunctionField)
    (hcard : Nat.card (W.torsion 3) = 9) {S P : W.Point} (hP : (3 : ℕ) • P = S) :
    pullbackDivisorThree h2 h3 (Finsupp.single (projPointOfPoint W S) (1 : ℤ))
      = ∑ R : W.torsion 3, Finsupp.single (projPointOfPoint W (P + R)) (1 : ℤ) := by
  classical
  ext q
  rw [pullbackDivisorThree_apply, Finset.sum_apply',
    Finset.sum_congr rfl fun R _ => Finsupp.single_apply]
  by_cases hq : comapProjPointThree h2 h3 q = projPointOfPoint W S
  · obtain ⟨R₀, hR₀⟩ : q ∈ Set.range fun R : W.torsion 3 => projPointOfPoint W (P + R) := by
      rw [← fibre_comapProjPointThree_eq_range_of_card h2 h3 hsep hcard hP]; exact hq
    rw [hq, Finsupp.single_eq_same, mul_one,
      ramificationIdxThree_eq_one_of_card h2 h3 hsep hcard hP hq,
      Finset.sum_eq_single R₀ (fun R _ hRne => if_neg fun hc =>
        hRne (projPointOfPoint_add_injective_three P (hc.trans hR₀.symm)))
      (fun hc => absurd (Finset.mem_univ R₀) hc), if_pos hR₀]
  · rw [Finsupp.single_apply, if_neg fun hc => hq hc.symm, mul_zero, Finset.sum_eq_zero]
    intro R _
    refine if_neg fun hc => hq ?_
    rw [← hc]
    exact comapProjPointThree_add_torsion_three h2 h3 hP R

end CoordinateRing

/-! ### Principality of `[3]∗((S) − (O))` -/

open CoordinateRing

/-- **`[3]∗((S) − (O)) = ∑_{R ∈ E[3]} ((P ⊕ R) − (R))`**, over an arbitrary field with
`(2 : F) ≠ 0` and `(3 : F) ≠ 0`, at a rational `E[3]`, a tripling `P` and separability carried.  The
`(O)` half is the same theorem at `S = O` with `P = O`, since `projPointOfPoint W 0` is `none` by
`rfl`. -/
theorem pullbackDivisorThree_single_sub_single_eq_sum_torsion_of_card [Fintype (W.torsion 3)]
    (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0)
    (hsep : Algebra.IsSeparable ↥(mulByThreeEndo (W := W) h2 h3).fieldRange W.FunctionField)
    (hcard : Nat.card (W.torsion 3) = 9) {S P : W.Point} (hP : (3 : ℕ) • P = S) :
    pullbackDivisorThree h2 h3 (Finsupp.single (projPointOfPoint W S) (1 : ℤ)
        - Finsupp.single (none : ProjPoint W) (1 : ℤ))
      = ∑ R : W.torsion 3, (Finsupp.single (projPointOfPoint W (P + R)) (1 : ℤ)
          - Finsupp.single (projPointOfPoint W (R : W.Point)) (1 : ℤ)) := by
  have hO : (none : ProjPoint W) = projPointOfPoint W 0 := rfl
  rw [map_sub, pullbackDivisorThree_single_eq_sum_torsion_of_card h2 h3 hsep hcard hP, hO,
    pullbackDivisorThree_single_eq_sum_torsion_of_card h2 h3 hsep hcard (smul_zero 3),
    ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun R _ => by rw [zero_add]

/-- The same formula on the affine chart, where `hprin` lives, over an arbitrary field with
`(2 : F) ≠ 0` and `(3 : F) ≠ 0`, at a rational `E[3]`, a tripling `P` and separability carried; each
`(O)` drops out. -/
theorem affinePart_pullbackDivisorThree_single_sub_single_of_card [Fintype (W.torsion 3)]
    (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0)
    (hsep : Algebra.IsSeparable ↥(mulByThreeEndo (W := W) h2 h3).fieldRange W.FunctionField)
    (hcard : Nat.card (W.torsion 3) = 9) {S P : W.Point} (hP : (3 : ℕ) • P = S) :
    affinePart W (pullbackDivisorThree h2 h3 (Finsupp.single (projPointOfPoint W S) (1 : ℤ)
        - Finsupp.single (none : ProjPoint W) (1 : ℤ)))
      = ∑ R : W.torsion 3, (pointDivisorAff W (P + R) - pointDivisorAff W (R : W.Point)) := by
  rw [pullbackDivisorThree_single_sub_single_eq_sum_torsion_of_card h2 h3 hsep hcard hP, map_sum]
  exact Finset.sum_congr rfl fun R _ => map_sub _ _ _

/-- **The class-group computation**, over an arbitrary field with `(2 : F) ≠ 0` and `(3 : F) ≠ 0`,
at a rational `E[3]`, a tripling `P`, separability carried and a `3`-torsion `S`:

```
∑_R toClass (P ⊕ R) − ∑_R toClass R = 9 • toClass P = toClass (9 • P) = toClass (3 • S) = 0.
```

The count of summands is `hcard` here rather than `card_torsion_three`; nothing else changes, and in
particular no step divides a divisor by `3`. -/
theorem classOfDivisor_affinePart_pullbackDivisorThree_eq_one_of_card (h2 : (2 : F) ≠ 0)
    (h3 : (3 : F) ≠ 0)
    (hsep : Algebra.IsSeparable ↥(mulByThreeEndo (W := W) h2 h3).fieldRange W.FunctionField)
    (hcard : Nat.card (W.torsion 3) = 9) {S P : W.Point} (hP : (3 : ℕ) • P = S)
    (hS : (3 : ℕ) • S = 0) :
    classOfDivisor W.FunctionField (affinePart W (pullbackDivisorThree h2 h3
        (Finsupp.single (projPointOfPoint W S) (1 : ℤ)
          - Finsupp.single (none : ProjPoint W) (1 : ℤ)))) = 1 := by
  classical
  haveI := W.finite_torsion_three (F := F) h3
  haveI : Fintype (W.torsion 3) := Fintype.ofFinite _
  have hP9 : (9 : ℕ) • P = 0 := by
    rw [show (9 : ℕ) = 3 * 3 from rfl, mul_smul, hP, hS]
  have hterm : ∀ R ∈ (Finset.univ : Finset (W.torsion 3)),
      classOfDivisor W.FunctionField (pointDivisorAff W (P + R) - pointDivisorAff W (R : W.Point))
        = Additive.toMul (Point.toClass P) := by
    intro R _
    rw [classOfDivisor_sub, classOfDivisor_pointDivisorAff, classOfDivisor_pointDivisorAff,
      map_add, toMul_add, mul_div_cancel_right]
  have hc : Fintype.card (W.torsion 3) = 9 := by
    rw [← Nat.card_eq_fintype_card, hcard]
  rw [affinePart_pullbackDivisorThree_single_sub_single_of_card h2 h3 hsep hcard hP,
    classOfDivisor_sum, Finset.prod_congr rfl hterm, Finset.prod_const, Finset.card_univ, hc,
    ← toMul_nsmul, ← map_nsmul, hP9, Point.toClass_zero]
  rfl

/-- **`[3]∗((S) − (O))` is principal on the affine chart**, over an arbitrary field with
`(2 : F) ≠ 0` and `(3 : F) ≠ 0`, at a rational `E[3]`, a tripling `P`, separability carried and a
`3`-torsion `S`: the vanishing class above turned back into a generator by `#726`'s criterion, which
never needed a closure. -/
theorem exists_divisor_eq_affinePart_pullbackDivisorThree_of_card (h2 : (2 : F) ≠ 0)
    (h3 : (3 : F) ≠ 0)
    (hsep : Algebra.IsSeparable ↥(mulByThreeEndo (W := W) h2 h3).fieldRange W.FunctionField)
    (hcard : Nat.card (W.torsion 3) = 9) {S P : W.Point} (hP : (3 : ℕ) • P = S)
    (hS : (3 : ℕ) • S = 0) :
    ∃ g : W.FunctionField, g ≠ 0 ∧ divisor W g = affinePart W (pullbackDivisorThree h2 h3
      (Finsupp.single (projPointOfPoint W S) (1 : ℤ)
        - Finsupp.single (none : ProjPoint W) (1 : ℤ))) :=
  (exists_divisor_eq_iff_classOfDivisor_eq_one _).2
    (classOfDivisor_affinePart_pullbackDivisorThree_eq_one_of_card h2 h3 hsep hcard hP hS)

/-- **`hprin` at `n = 3` over an arbitrary field with `(2 : F) ≠ 0` and `(3 : F) ≠ 0`**, in the
shape `exists_gS_three` consumes it: for a nonsingular `3`-torsion point `S` on a curve whose
`3`-torsion is rational and which has a tripling point `P` with `[3]P = S`, the pullback
`[3]∗((S) − (O))` is three times a principal divisor.

⚠️ `hsep` is discharged internally from `hcard`; what is left is `h2`, `h3`, `hcard`, `hP`, the
nonsingularity and `3`-torsion of `S`, and a nonzero `f` whose divisor is `3·(S)`.  ⚠️ This is
**not** `#962` — see the module docstring for what still stands between this and `hprin` over a
field where those two rationality facts fail.

The proof is `exists_nsmul_divisor_eq_divisor_mulByThreeEndo`
(`EllipticCurves.FunctionField.PullbackPrincipalityThree`) with `exists_nsmul_three_eq` replaced by
`hP`, and its last step is likewise `natCast_zsmul` rather than a `three_nsmul`/`three_zsmul`
pair. -/
theorem exists_nsmul_divisor_eq_divisor_mulByThreeEndo_of_card (h2 : (2 : F) ≠ 0)
    (h3 : (3 : F) ≠ 0) (hcard : Nat.card (W.torsion 3) = 9) {x y : F}
    (h : W.Nonsingular x y) (hS : Point.some x y h ∈ W.torsion 3)
    {P : W.Point} (hP : (3 : ℕ) • P = Point.some x y h)
    {f : W.FunctionField} (hf : f ≠ 0)
    (hfdiv : divisor W f = Finsupp.single (pointClosedPoint h.left) (3 : ℤ)) :
    ∃ g₀ : W.FunctionField, g₀ ≠ 0 ∧
      3 • divisor W g₀ = divisor W (mulByThreeEndo h2 h3 f) := by
  classical
  have hsep := isSeparable_mulByThreeEndoFieldRange_of_card h2 h3 hcard
  obtain ⟨g, hg, hgdiv⟩ :=
    exists_divisor_eq_affinePart_pullbackDivisorThree_of_card h2 h3 hsep hcard hP
      (mem_torsion_iff.mp hS)
  refine ⟨g, hg, ?_⟩
  obtain ⟨f₀, hf₀, hproj₀⟩ := divisorProj_eq_single_sub_single_of_torsion h hS
  have hd₀ : divisor W f₀ = Finsupp.single (pointClosedPoint h.left) (3 : ℤ) := by
    ext v
    have hv := congrArg (fun D => D (some v)) hproj₀
    simpa [Finsupp.single_apply] using hv
  have hfe : divisor W f = divisor W f₀ := hfdiv.trans hd₀.symm
  have hprojf : divisorProj W f = divisorProj W f₀ :=
    divisorProj_eq_iff.2 ⟨hfe, ordInfty_eq_of_divisor_eq hf hf₀ hfe⟩
  have hkey : divisorProj W (mulByThreeEndo h2 h3 f)
      = (3 : ℤ) • pullbackDivisorThree h2 h3
          (Finsupp.single (projPointOfPoint W (Point.some x y h)) (1 : ℤ)
            - Finsupp.single (none : ProjPoint W) (1 : ℤ)) := by
    rw [divisorProj_mulByThreeEndo h2 h3 hf, hprojf, hproj₀, ← map_zsmul]
    congr 1
    rw [smul_sub, Finsupp.smul_single, Finsupp.smul_single, smul_eq_mul, mul_one,
      projPointOfPoint_some]
    norm_num
  have hdiv3 : divisor W (mulByThreeEndo h2 h3 f)
      = (3 : ℤ) • affinePart W (pullbackDivisorThree h2 h3
        (Finsupp.single (projPointOfPoint W (Point.some x y h)) (1 : ℤ)
          - Finsupp.single (none : ProjPoint W) (1 : ℤ))) := by
    rw [← affinePart_divisorProj, hkey, map_zsmul]
  rw [hdiv3, hgdiv, ← natCast_zsmul]
  norm_num

/-- **Rung 5 of the Weil pairing at `n = 3`, over an arbitrary field with `(2 : F) ≠ 0` and
`(3 : F) ≠ 0`**, at a nonsingular `3`-torsion point `S`, a rational `E[3]` and a tripling `P`.
`exists_gS_three` with its `hprin` discharged from `hcard` and `hP`: there are a principal `f_S`
with `div f_S = 3·(S)` and a nonzero `g_S` with `u · g_S ^ 3 = [3]∗ f_S` for a unit `u` of `F[W]`.

`exists_gS_three_of_isAlgClosed` (`PullbackPrincipalityThree`) is this statement over `F̄`, where
both hypotheses are theorems; the `Recovery` section below derives it from this one. -/
theorem exists_gS_three_of_card (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0)
    (hcard : Nat.card (W.torsion 3) = 9) {x y : F}
    (h : W.Nonsingular x y) (hS : Point.some x y h ∈ W.torsion 3)
    {P : W.Point} (hP : (3 : ℕ) • P = Point.some x y h) :
    ∃ f : W.FunctionField, f ≠ 0 ∧
      divisor W f = Finsupp.single (pointClosedPoint h.left) (3 : ℤ) ∧
      ∃ gS : W.FunctionField, gS ≠ 0 ∧
        ∃ u : W.CoordinateRingˣ, (u : W.CoordinateRing) • gS ^ 3 = mulByThreeEndo h2 h3 f :=
  exists_gS_three h2 h3 h hS fun _ hf hfdiv =>
    exists_nsmul_divisor_eq_divisor_mulByThreeEndo_of_card h2 h3 hcard h hS hP hf hfdiv

/-! ### Recovery -/

section Recovery

variable [IsAlgClosed F]

/-- `exists_nsmul_divisor_eq_divisor_mulByThreeEndo`
(`EllipticCurves.FunctionField.PullbackPrincipalityThree`), recovered. -/
private theorem exists_nsmul_divisor_eq_divisor_mulByThreeEndo_of_general (h2 : (2 : F) ≠ 0)
    (h3 : (3 : F) ≠ 0) {x y : F} (h : W.Nonsingular x y)
    (hS : Point.some x y h ∈ W.torsion 3)
    {f : W.FunctionField} (hf : f ≠ 0)
    (hfdiv : divisor W f = Finsupp.single (pointClosedPoint h.left) (3 : ℤ)) :
    ∃ g₀ : W.FunctionField, g₀ ≠ 0 ∧
      3 • divisor W g₀ = divisor W (mulByThreeEndo h2 h3 f) :=
  let ⟨_, hP⟩ := exists_nsmul_three_eq (Point.some x y h)
  exists_nsmul_divisor_eq_divisor_mulByThreeEndo_of_card h2 h3 (card_torsion_three h2 h3) h hS hP
    hf hfdiv

/-- `exists_gS_three_of_isAlgClosed`
(`EllipticCurves.FunctionField.PullbackPrincipalityThree`), recovered. -/
private theorem exists_gS_three_of_isAlgClosed_of_general (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0)
    {x y : F} (h : W.Nonsingular x y) (hS : Point.some x y h ∈ W.torsion 3) :
    ∃ f : W.FunctionField, f ≠ 0 ∧
      divisor W f = Finsupp.single (pointClosedPoint h.left) (3 : ℤ) ∧
      ∃ gS : W.FunctionField, gS ≠ 0 ∧
        ∃ u : W.CoordinateRingˣ, (u : W.CoordinateRing) • gS ^ 3 = mulByThreeEndo h2 h3 f :=
  let ⟨_, hP⟩ := exists_nsmul_three_eq (Point.some x y h)
  exists_gS_three_of_card h2 h3 (card_torsion_three h2 h3) h hS hP

end Recovery

/-! ### Non-vacuity

⚠️ **`hcard` cannot be certified over `ℚ`, and the module docstring says why: it is vacuous there.**
What is certified below is the `hsep`-only half of the chain — the half that consumes the new
uncollapsed identity — over `ℚ`, a base field that is **not** algebraically closed, so the
certificate is of the general statements and not of their merged `F̄` siblings (`#916`).

⚠️ **Nothing below instantiates a `_of_card` statement**, and that is the honest reading of `#916`
here rather than an omission: a certificate would have to supply `Nat.card (E(F)[3]) = 9` together
with a rational `P` of order `9`, and the two together are unsatisfiable over `ℚ` and open over
every finite field this tree has a fixture for.  The `Recovery` section above is what shows the four
hypotheses are jointly satisfiable at all.

⚠️ `hsep` is **produced** and not assumed: `isSeparable_mulByThreeEndoFieldRange_of_charZero`
(`EllipticCurves.FunctionField.MulByThreeGalois`) discharges it from `[CharZero ℚ]`. -/

section Nonvacuity

/-! The certificate curve `y² = x³ − x` is the shared `EllipticCurves.Fixture.y2EqX3SubX`, whose
single `[CharZero F]` instance also supplies `IsElliptic` here, and it is taken over `ℚ` on
purpose. -/

open EllipticCurves.Fixture

private lemma exampleQTwo : (2 : ℚ) ≠ 0 := by norm_num

private lemma exampleQThree : (3 : ℚ) ≠ 0 := by norm_num

/-- **The nine-element fibre bound over `ℚ`, committed** — at most nine places of `ℚ(W)` lie above
any place of `[3]∗ℚ(W)`, on a genuine curve over a base field that is not algebraically closed,
where `card_fibre_comapProjPointThree_le_nine` (`MulByThreeRamification`) does not apply.

⚠️ This is the statement that consumes
`sum_ramificationIdxThree_mul_residueDegreeThree_of_isSeparable`
(`EllipticCurves.FunctionField.PlaceInertiaGeneral`), so certifying it certifies the new identity in
use rather than only in isolation. -/
private noncomputable example (q : ProjPoint (y2EqX3SubX ℚ)) :
    (CoordinateRing.finite_comapProjPointThree_preimage_singleton exampleQTwo exampleQThree
      q).toFinset.card ≤ 9 :=
  CoordinateRing.card_fibre_comapProjPointThree_le_nine_of_isSeparable exampleQTwo exampleQThree
    (CoordinateRing.isSeparable_mulByThreeEndoFieldRange_of_charZero exampleQTwo exampleQThree) q

/-- **`f_p > 0` for `[3]∗` over `ℚ`, committed** — the positivity the fibre bound rests on, at an
arbitrary place and with no separability, module-finiteness or fibre hypothesis. -/
private noncomputable example (p : ProjPoint (y2EqX3SubX ℚ)) :
    0 < CoordinateRing.residueDegreeThree exampleQTwo exampleQThree p :=
  CoordinateRing.residueDegreeThree_pos exampleQTwo exampleQThree p

end Nonvacuity

end WeierstrassCurve.Affine
