/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import EllipticCurves.Fixtures
import EllipticCurves.FunctionField.MulByNFibre
import EllipticCurves.FunctionField.NthRootOfPullbackN
import EllipticCurves.FunctionField.PullbackPrincipalityThree
import EllipticCurves.Torsion.StructureGeneral

/-!
# `[n]∗((S) − (O))` is principal at every `n`, and rung 5 loses its hypothesis over `F̄`

Rung 5 of the divisor-theoretic Weil pairing (Silverman AEC III.8) produces, from the principal
function `f_S` of an `n`-torsion point `S`, an `n`-th root `g_S` of `f_S ∘ [n]`.  It is merged at
an arbitrary index (`EllipticCurves.FunctionField.NthRootOfPullbackN`, `exists_gS_n`) but
**conditionally**: it carries an explicit hypothesis `hprin` saying that the effective divisor `D`
with `n · D = div (f_S ∘ [n])` is *principal*.  That hypothesis is not formal — `n · D` principal
does **not** imply `D` principal, and the failure is exactly the `n`-torsion of the class group the
Weil pairing measures.

`EllipticCurves.FunctionField.PullbackPrincipalityTwo` (`#791`) and
`EllipticCurves.FunctionField.PullbackPrincipalityThree` (`#825`) discharge it at `n = 2` and
`n = 3` over an algebraically closed base field.  **This file discharges it at every `n` with
`(2 : F) ≠ 0` and `((n : ℤ) : F) ≠ 0`, over an algebraically closed base field**, and the two
numeral files come back out of it verbatim (see the recovery block).

## ⚠️ Why this was believed to be out of reach, and what changed

`EllipticCurves.FunctionField.WeilPairingTranslationSlotHprinN` — the module that holds this seam's
**ceiling**, the sentence a reader consults before pricing anything at a general index — says of a
general index:

> ⚠️ **Retiring them supplies no replacement ceiling** — whether `hprin` at a general index is now
> reachable depends on the fibre description, which is merged only at `n = 2, 3`, and that has
> **not** been re-measured.

⚠️ **It is the ceiling, not the only ruling on the question, and this commit retires three more.**
`EllipticCurves.FunctionField.PullbackPrincipalityThree` said principality at a general index was
*"not measured, here or anywhere"*; `EllipticCurves.FunctionField.NthRootOfPullbackN` said no
hypothesis-free corollary could be fed at a general index; and
`EllipticCurves.FunctionField.WeilPairingGaloisRootN` said *"at general `n` there is no such
producer"*.  Each is retired in its own module, in the marked-quotation form `README.md`'s
`### Retired claims` lays down.

Two things the ceiling names have since become available, and neither was when it was written.

* **The fibre description is merged at every `n` with `(2 : F) ≠ 0` and `((n : ℤ) : F) ≠ 0` over
  `F̄`**, as `pullbackDivisorN_single_eq_sum_torsion_of_ne_zero`
  (`EllipticCurves.FunctionField.MulByNFibre`) — `#774`'s formula at a general index, and the last
  of the eleven declarations `#1540` measured as blocked.  ⚠️ **That sentence's *"merged only at
  `n = 2, 3`"* is therefore false rather than merely partial**, which is why the sentence is
  retired rather than qualified; the retirement is recorded in that module, in the marked-quotation
  form `README.md`'s `### Retired claims` lays down, and `README.md`'s `### What is formalised`
  carries a second retirement of its own, of the bullet this commit falsifies there.
* **`#E[n] = n²` is a theorem at every `n` with `(2 : F) ≠ 0` and `(n : F) ≠ 0`**, as
  `card_torsion_eq_sq` (`EllipticCurves.Torsion.StructureGeneral`, `#242`).  It is the *only*
  mathematical input this route needed that did not exist when the `n = 2` file was written, and it
  enters at exactly one place — the class computation below.
  ⚠️ **The two bullets name different index conditions, and that is not a slip to reconcile.**
  The fibre description binds `((n : ℤ) : F) ≠ 0` and `card_torsion_eq_sq` binds `(n : F) ≠ 0`;
  `README.md`'s `### Scope of the rules above` says *"`(n : F) ≠ 0` and `((n : ℤ) : F) ≠ 0` are
  different clauses"*.  ⚠️ Neither declaration carries an `_of_natCast_ne_zero` /
  `_of_intCast_ne_zero` suffix to say which, and copying one onto the other would make one of them
  false.

## The five steps, and where each comes from

Let `S` be a nonsingular affine `n`-torsion point and pick `P` with `n • P = S`
(`nsmul_surjective_of_two_ne_zero`, `EllipticCurves.Torsion.TwoTorsionOrder`: `[n]` is surjective
on `E(F̄)` at every `n ≠ 0` when `(2 : F) ≠ 0`).

1. **The coset formula.**  `pullbackDivisorN` is an `AddMonoidHom`, so `map_sub` splits
   `[n]∗((S) − (O))`; the fibre description handles the `(S)` half, and **the same theorem at
   `S = O` with `P = O`** handles the `(O)` half, since `projPointOfPoint W 0` is `none` by `rfl`.
   That is `pullbackDivisorN_single_sub_single_eq_sum_torsion`.
2. **The affine part.**  `hprin` is a statement about the affine `divisor W`, while the formula
   lives in `ProjPoint W →₀ ℤ`; `affinePart` (`PullbackPrincipalityTwo`, `#765`) is the passage, and
   under it the point at infinity simply disappears.
3. **The class computation**, and the mathematical content:

   ```
   ∑_R toClass (P ⊕ R) − ∑_R toClass R = n² • toClass P = toClass (n² • P) = toClass (n • S) = 0.
   ```

   Each summand has class `toClass P` on the nose, and there are `#E[n] = n²` of them.
   ⚠️ **No step divides a divisor by `n`** — the argument exhibits the class of `D` as trivial
   directly.
4. **Back to a generator.**  `exists_divisor_eq_iff_classOfDivisor_eq_one` (`#726`).
5. **`hprin`'s `∀`-form.**  `exists_gS_n` quantifies over *every* `f ≠ 0` with
   `divisor W f = n·(S)`, not only over the generator `#409` produces; the gap closes because the
   affine divisor pins the projective one (`ordInfty_eq_of_divisor_eq`, then `divisorProj_eq_iff`).

⚠️ **One line of the `n = 3` proof does not transpose, and the general form is the shorter one.**
`PullbackPrincipalityThree`'s last step is `rw [hdiv3, hgdiv, ← natCast_zsmul]; norm_num`, and its
docstring explains the `natCast_zsmul` as *"not a `three_nsmul`/`three_zsmul` pair … `three'_nsmul`
has no `zsmul` twin"*.  Here `← natCast_zsmul` closes the goal on its own: the numeral was the
obstacle, not the generality.

## Main statements

* `WeierstrassCurve.Affine.pullbackDivisorN_single_sub_single_eq_sum_torsion`,
  `WeierstrassCurve.Affine.affinePart_pullbackDivisorN_single_sub_single` — the coset formula, in
  the projective divisor group and on the affine chart, at every `n` with `(2 : F) ≠ 0` and
  `((n : ℤ) : F) ≠ 0` over `F̄`.
* `WeierstrassCurve.Affine.classOfDivisor_affinePart_pullbackDivisorN_eq_one` — its class is
  trivial, at the same hypotheses.
* `WeierstrassCurve.Affine.exists_divisor_eq_affinePart_pullbackDivisorN` —
  `[n]∗((S) − (O))` is principal on the affine chart, at the same hypotheses.
* `WeierstrassCurve.Affine.exists_nsmul_divisor_eq_divisor_mulByNEndo` — **`hprin` itself**, in the
  shape `exists_gS_n` consumes, at the same hypotheses.
* **`WeierstrassCurve.Affine.exists_gS_n_of_isAlgClosed`** — rung 5 at every `n` with
  `(2 : F) ≠ 0` and `((n : ℤ) : F) ≠ 0` over `F̄`, with no `hprin`, taking the non-constancy of
  `x([n]𝒫)` as `exists_gS_n` does.
* **`WeierstrassCurve.Affine.exists_gS_of_ne_zero_of_isAlgClosed`** — the same with that
  non-constancy discharged, i.e. `exists_gS_of_ne_zero` minus its `hprin`.
* `WeierstrassCurve.Affine.exists_nonsingular_mem_torsion` — non-vacuity at every index, with
  `(2 : F) ≠ 0` and `(n : F) ≠ 0` and `n ≠ 1`: over `F̄` the `n`-torsion of an elliptic curve has an
  affine point, because `#E[n] = n² > 1`.

## Scope

⚠️ **This is not `#962`, and the confusion is one letter deep.**  `#962` is `hprin` over a
**general field** at `n = 2` and `n = 3`; it is a gate record, it says of itself that there is no
spike and that the obvious route is known to fail, and nothing here touches it.  What this file
closes is the **index** axis over `F̄`, which is the axis the two numeral files already close at
their two numerals.  After this, the arbitrary-field statements still carry `hprin` at every `n`,
exactly as they do today at `n = 2` and `n = 3`.
⚠️ `EllipticCurves.FunctionField.PullbackPrincipalityTwoRationalTorsion` carries the same warning
about itself — *"It does not discharge `#962`, and must not be reported as doing so."*  It binds
here too.
⚠️ **Retired, once and here** (`#1888`): **13** blocks in 13 files at `855f993` put `#962` at an
index outside `n = 2` and `n = 3`, and every one of them is **false**, not short.
⚠️ **The count is on the proposition and not on any one sentence.**  Seven of the thirteen — the
`EllipticCurves.TateModule` blocks — carried it as *"there `#962` is the standing gate at a general
index"*, and the other six in their own words, from `README.md`'s *"`#962` is the standing gate
elsewhere"* to `EllipticCurves.FunctionField.WeilPairingAlternatingAssemblyN`'s *"an arbitrary `n`
over an arbitrary field (`#962`)"*.  A grep of the seven-block wording at `855f993` returns
**seven**, so quoting it beside the count of the whole population would send a reader to a check
that fails.
`#962`'s `## Explicitly NOT this issue` section reads *"**General `n`.**  `#404`'s `ωₙ` crux, and
`#938`'s double obstruction at composite `n`.  This issue is `n = 2` and `n = 3` only"*, so a
citation of it at a general index over-reaches, and `README.md` `### Gate-discharge claims` rules
that a `#NNNN` citation reaches exactly what the record it names reaches.  It retires **once**
because all thirteen asserted one proposition about one record and one reading of that record
falsifies them together, and it retires **here** because this is where the tree says what `#962` is
(`### Retired claims`' *"a claim about a subject that lives elsewhere retires at the subject"*).
What replaced it names the gate without the citation and leaves the citation at the two numerals —
in eight of the thirteen in these words, *"`hprin` is the standing gate at every index; `#962` is
that gate at `n = 2` and `n = 3`"*, and in the other five in their own block's sentence shape.
⚠️ **`#962`'s stated reason for that scope is falsified by this file and its scope has not moved.**
The record gives the two numerals *"because those are the only `n` at which the `F̄` statement
exists"*, and `exists_gS_n_of_isAlgClosed` below is that statement at every `n` with `(2 : F) ≠ 0`
and `((n : ℤ) : F) ≠ 0`.  That is an argument for amending the record on the tracker; it is not a
licence for a docstring to read the record as already amended, and nothing here files a record for
the wider gate or is evidence that one is owed.

⚠️ **The hypotheses are strictly stronger than `exists_gS_n`'s.**  Everything below carries
`[IsAlgClosed F]` and `[W.IsElliptic]`, which `exists_gS_n` — stated over an arbitrary field with
`[IsDedekindDomain W.CoordinateRing]` — does not.  The closure is needed **twice and
independently**: for the surjectivity of `[n]` on points (step 5) and for the fibre description
(step 1).  Removing either is not a matter of restating anything here.

⚠️ **This is not the Weil pairing.**  Rung 6, bilinearity, the alternating property and
Galois-equivariance are untouched.  ⚠️ **Non-degeneracy at a general `n` is the natural consumer and
is *not* delivered here**: `EllipticCurves.FunctionField.WeilPairingNondegenerateTwo` reads that
argument as seven steps, of which this file supplies the first and the other six are already stated
at a general index — but assembling them is a separate statement with its own hypotheses, and this
file does not pre-empt it.

⚠️ **`((n : ℤ) : F) ≠ 0` is a condition of this *route*, not a limit on rung 5.**  Over `F̄` the
non-constancy of `[n]` is available at every `n ≠ 0` including `n = char F`
(`transcendental_xCoord_nsmul_of_isAlgClosed`); what needs the index hypothesis here is the fibre
description and `#E[n] = n²`, and at `n = char F` the latter is **false**, not merely unproved.

## References

* [J. H. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.8.
-/

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum

namespace WeierstrassCurve.Affine

open CoordinateRing

variable {F : Type*} [Field F] {W : Affine F} [IsDedekindDomain W.CoordinateRing]

section IsAlgClosed

variable [DecidableEq F] [W.IsElliptic] [IsAlgClosed F]

/-! ### `[n]∗((S) − (O))` and its class -/

/-- **The coset formula at every `n` with `(2 : F) ≠ 0` and `((n : ℤ) : F) ≠ 0`**:

```
[n]∗((S) − (O)) = ∑_{R ∈ E[n]} ((P ⊕ R) − (R))
```

for any `P` with `n • P = S`.  `pullbackDivisorN n h` is an `AddMonoidHom`, so `map_sub` splits the
left-hand side; `pullbackDivisorN_single_eq_sum_torsion_of_ne_zero` handles the `(S)` half, and the
**same theorem at `S = O` with `P = O`** handles the `(O)` half, since `projPointOfPoint W 0` is
`none` by `rfl`.  No new geometry.

The `[Fintype (W.torsion n)]` is carried in the statement rather than produced inside it, for the
reason `#763` records and the fibre description repeats: the sum cannot be written without it, and
`Fintype.ofFinite` in a statement is a noncomputable leak.  `finite_torsion_of_intCast_ne_zero`
supplies it at the point of use. -/
theorem pullbackDivisorN_single_sub_single_eq_sum_torsion {n : ℕ} [Fintype (W.torsion n)]
    (h2 : (2 : F) ≠ 0) (hn : ((n : ℤ) : F) ≠ 0)
    (h : Transcendental F (n • genericPoint (W := W)).xCoord) {S P : W.Point} (hP : n • P = S) :
    pullbackDivisorN n h (Finsupp.single (projPointOfPoint W S) (1 : ℤ)
        - Finsupp.single (none : ProjPoint W) (1 : ℤ))
      = ∑ R : W.torsion n, (Finsupp.single (projPointOfPoint W (P + R)) (1 : ℤ)
          - Finsupp.single (projPointOfPoint W (R : W.Point)) (1 : ℤ)) := by
  have hO : (none : ProjPoint W) = projPointOfPoint W 0 := rfl
  rw [map_sub, pullbackDivisorN_single_eq_sum_torsion_of_ne_zero h2 hn h hP, hO,
    pullbackDivisorN_single_eq_sum_torsion_of_ne_zero h2 hn h (smul_zero n),
    ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun R _ => by rw [zero_add]

/-- The same formula on the affine chart, where `hprin` lives, at `(2 : F) ≠ 0` and
`((n : ℤ) : F) ≠ 0`.  Each `(O)` in the coset sum simply drops out (`affinePart_single_none`). -/
theorem affinePart_pullbackDivisorN_single_sub_single {n : ℕ} [Fintype (W.torsion n)]
    (h2 : (2 : F) ≠ 0) (hn : ((n : ℤ) : F) ≠ 0)
    (h : Transcendental F (n • genericPoint (W := W)).xCoord) {S P : W.Point} (hP : n • P = S) :
    W.affinePart (pullbackDivisorN n h (Finsupp.single (projPointOfPoint W S) (1 : ℤ)
        - Finsupp.single (none : ProjPoint W) (1 : ℤ)))
      = ∑ R : W.torsion n, (W.pointDivisorAff (P + R) - W.pointDivisorAff (R : W.Point)) := by
  rw [pullbackDivisorN_single_sub_single_eq_sum_torsion h2 hn h hP, map_sum]
  exact Finset.sum_congr rfl fun R _ => map_sub _ _ _

/-- **The class-group computation at every `n` with `(2 : F) ≠ 0` and `((n : ℤ) : F) ≠ 0`, and the
mathematical heart of the file.**

```
∑_R toClass (P ⊕ R) − ∑_R toClass R = n² • toClass P = toClass (n² • P) = toClass (n • S) = 0.
```

Each summand of the coset formula has class `toClass P` on the nose — `toClass` is an
`AddMonoidHom`, so `toClass (P ⊕ R)` and `toClass R` differ by exactly `toClass P` — and there are
`#E[n] = n²` of them.  ⚠️ **That count is `#242`** (`card_torsion_eq_sq`), an input and not a
consequence, and it is the single place where this file needs something the `n = 2` and `n = 3`
files did not have: they read `4` and `9` off `card_torsion_two` and `card_torsion_three`, which
count the roots of a fixed division polynomial and do not generalise.  Finally
`n² • P = n • (n • P) = n • S = 0` because `S` is `n`-torsion.

⚠️ No step divides a divisor by `n`.  `n · D` principal does **not** imply `D` principal — that
failure is the `n`-torsion of the class group the Weil pairing measures — and the argument here
exhibits the class of `D` as trivial directly. -/
theorem classOfDivisor_affinePart_pullbackDivisorN_eq_one {n : ℕ}
    (h2 : (2 : F) ≠ 0) (hn : ((n : ℤ) : F) ≠ 0)
    (h : Transcendental F (n • genericPoint (W := W)).xCoord) {S P : W.Point}
    (hP : n • P = S) (hS : n • S = 0) :
    classOfDivisor W.FunctionField (W.affinePart (pullbackDivisorN n h
        (Finsupp.single (projPointOfPoint W S) (1 : ℤ)
          - Finsupp.single (none : ProjPoint W) (1 : ℤ)))) = 1 := by
  classical
  have hnF : (n : F) ≠ 0 := by exact_mod_cast hn
  haveI := W.finite_torsion_of_intCast_ne_zero h2 hnF
  haveI : Fintype (W.torsion n) := Fintype.ofFinite _
  have hPsq : (n ^ 2) • P = 0 := by rw [sq, mul_smul, hP, hS]
  have hterm : ∀ R ∈ (Finset.univ : Finset (W.torsion n)),
      classOfDivisor W.FunctionField (W.pointDivisorAff (P + R) - W.pointDivisorAff (R : W.Point))
        = Additive.toMul (Point.toClass P) := by
    intro R _
    rw [classOfDivisor_sub, classOfDivisor_pointDivisorAff, classOfDivisor_pointDivisorAff,
      map_add, toMul_add, mul_div_cancel_right]
  have hcard : Fintype.card (W.torsion n) = n ^ 2 := by
    rw [← Nat.card_eq_fintype_card, card_torsion_eq_sq h2 hnF]
  rw [affinePart_pullbackDivisorN_single_sub_single h2 hn h hP, classOfDivisor_sum,
    Finset.prod_congr rfl hterm, Finset.prod_const, Finset.card_univ, hcard, ← toMul_nsmul,
    ← map_nsmul, hPsq, Point.toClass_zero]
  rfl

/-- **`[n]∗((S) − (O))` is principal on the affine chart, at every `n` with `(2 : F) ≠ 0` and
`((n : ℤ) : F) ≠ 0`.**  The vanishing class of the previous theorem, turned back into an actual
generator by `#726`'s principality criterion. -/
theorem exists_divisor_eq_affinePart_pullbackDivisorN {n : ℕ}
    (h2 : (2 : F) ≠ 0) (hn : ((n : ℤ) : F) ≠ 0)
    (h : Transcendental F (n • genericPoint (W := W)).xCoord) {S P : W.Point}
    (hP : n • P = S) (hS : n • S = 0) :
    ∃ g : W.FunctionField, g ≠ 0 ∧ W.divisor g = W.affinePart (pullbackDivisorN n h
      (Finsupp.single (projPointOfPoint W S) (1 : ℤ)
        - Finsupp.single (none : ProjPoint W) (1 : ℤ))) :=
  (exists_divisor_eq_iff_classOfDivisor_eq_one _).2
    (classOfDivisor_affinePart_pullbackDivisorN_eq_one h2 hn h hP hS)

/-- **`hprin` at every `n` with `(2 : F) ≠ 0` and `((n : ℤ) : F) ≠ 0`, in the shape `exists_gS_n`
consumes it.**

The statement quantifies over *every* nonzero `f` with `divisor W f = n·(S)`, not only over the
generator `#409` produces, so the proof must first know that the affine divisor pins the projective
one.  It does: `ordInfty_eq_of_divisor_eq` compares `f` with `#409`'s generator at the point at
infinity and `divisorProj_eq_iff` assembles the two halves.  Then `divisorProj_mulByNEndo` moves
`[n]∗` across, `map_zsmul` pulls the `n` out, and `affinePart` restricts to the chart.

⚠️ The halving point comes from `nsmul_surjective_of_two_ne_zero`, which is one of the two places
`[IsAlgClosed F]` is load-bearing. -/
theorem exists_nsmul_divisor_eq_divisor_mulByNEndo {n : ℕ}
    (h2 : (2 : F) ≠ 0) (hn : ((n : ℤ) : F) ≠ 0)
    (h : Transcendental F (n • genericPoint (W := W)).xCoord)
    {x y : F} (hns : W.Nonsingular x y) (hS : Point.some x y hns ∈ W.torsion n)
    {f : W.FunctionField} (hf : f ≠ 0)
    (hfdiv : W.divisor f = Finsupp.single (pointClosedPoint hns.left) (n : ℤ)) :
    ∃ g₀ : W.FunctionField, g₀ ≠ 0 ∧
      n • W.divisor g₀ = W.divisor (mulByNEndo n h f) := by
  classical
  have hnF : (n : F) ≠ 0 := by exact_mod_cast hn
  have hn0 : n ≠ 0 := by rintro rfl; simp at hnF
  obtain ⟨P, hP⟩ := nsmul_surjective_of_two_ne_zero (W := W) h2 hn0 (Point.some x y hns)
  obtain ⟨g, hg, hgdiv⟩ :=
    exists_divisor_eq_affinePart_pullbackDivisorN h2 hn h hP (mem_torsion_iff.mp hS)
  refine ⟨g, hg, ?_⟩
  obtain ⟨f₀, hf₀, hproj₀⟩ := divisorProj_eq_single_sub_single_of_torsion hns hS
  have hd₀ : W.divisor f₀ = Finsupp.single (pointClosedPoint hns.left) (n : ℤ) := by
    ext v
    have hv := congrArg (fun D => D (some v)) hproj₀
    simpa [Finsupp.single_apply] using hv
  have hfe : W.divisor f = W.divisor f₀ := hfdiv.trans hd₀.symm
  have hprojf : W.divisorProj f = W.divisorProj f₀ :=
    divisorProj_eq_iff.2 ⟨hfe, ordInfty_eq_of_divisor_eq hf hf₀ hfe⟩
  have hkey : W.divisorProj (mulByNEndo n h f)
      = (n : ℤ) • pullbackDivisorN n h
          (Finsupp.single (projPointOfPoint W (Point.some x y hns)) (1 : ℤ)
            - Finsupp.single (none : ProjPoint W) (1 : ℤ)) := by
    rw [divisorProj_mulByNEndo n h hf, hprojf, hproj₀, ← map_zsmul]
    congr 1
    rw [smul_sub, Finsupp.smul_single, Finsupp.smul_single, smul_eq_mul, mul_one,
      projPointOfPoint_some]
  have hdivn : W.divisor (mulByNEndo n h f)
      = (n : ℤ) • W.affinePart (pullbackDivisorN n h
        (Finsupp.single (projPointOfPoint W (Point.some x y hns)) (1 : ℤ)
          - Finsupp.single (none : ProjPoint W) (1 : ℤ))) := by
    rw [← affinePart_divisorProj, hkey, map_zsmul]
  rw [hdivn, hgdiv, ← natCast_zsmul]

/-! ### Rung 5 without `hprin`, at every `n` with `(2 : F) ≠ 0` and `((n : ℤ) : F) ≠ 0` -/

/-- **Rung 5 of the Weil pairing at every `n` with `(2 : F) ≠ 0` and `((n : ℤ) : F) ≠ 0`, over an
algebraically closed field, unconditionally.**  `exists_gS_n` with its `hprin` discharged: for a
nonsingular `n`-torsion point `S = (x, y)` there are a principal function `f_S` with
`div f_S = n·(S)` and a nonzero `g_S ∈ F(W)` with `u · g_S ^ n = [n]∗ f_S` for a unit `u` of `F[W]`.

The non-constancy of `x([n]𝒫)` is taken as a hypothesis here, exactly as `exists_gS_n` takes it;
`exists_gS_of_ne_zero_of_isAlgClosed` below is the form with it discharged.

⚠️ Stated with `[IsAlgClosed F]` and `[W.IsElliptic]`, which `exists_gS_n` does not carry — see the
Scope section.  Over a general field `hprin` stands at every `n`. -/
theorem exists_gS_n_of_isAlgClosed {n : ℕ} (h2 : (2 : F) ≠ 0) (hn : ((n : ℤ) : F) ≠ 0)
    (h : Transcendental F (n • genericPoint (W := W)).xCoord)
    {x y : F} (hns : W.Nonsingular x y) (hS : Point.some x y hns ∈ W.torsion n) :
    ∃ f : W.FunctionField, f ≠ 0 ∧
      W.divisor f = Finsupp.single (pointClosedPoint hns.left) (n : ℤ) ∧
      ∃ gS : W.FunctionField, gS ≠ 0 ∧
        ∃ u : W.CoordinateRingˣ, (u : W.CoordinateRing) • gS ^ n = mulByNEndo n h f :=
  exists_gS_n h hns hS fun _ hf hfdiv =>
    exists_nsmul_divisor_eq_divisor_mulByNEndo h2 hn h hns hS hf hfdiv

/-- **`exists_gS_of_ne_zero` minus its `hprin`**, over an algebraically closed field: rung 5 at
every `n` with `(2 : F) ≠ 0` and `((n : ℤ) : F) ≠ 0`, with no hypothesis beyond the setting and a
nonsingular affine `n`-torsion point.

The transcendence proof is `transcendental_xCoord_nsmul_genericPoint_of_intCast_ne_zero`, the same
one `exists_gS_of_ne_zero` writes, so the two statements are about the *syntactically* same
`mulByNEndo` term and a caller holding one can `rw` with the other.  ⚠️ Over `F̄` the closure would
also discharge it at every `n ≠ 0` through `transcendental_xCoord_nsmul_of_isAlgClosed`,
characteristic included; that is not used, because the index hypothesis is needed anyway for the
fibre description and for `#E[n] = n²`, and matching `exists_gS_of_ne_zero` is worth more than
widening a side condition that cannot be widened alone. -/
theorem exists_gS_of_ne_zero_of_isAlgClosed {n : ℕ} (h2 : (2 : F) ≠ 0) (hn : ((n : ℤ) : F) ≠ 0)
    {x y : F} (hns : W.Nonsingular x y) (hS : Point.some x y hns ∈ W.torsion n) :
    ∃ f : W.FunctionField, f ≠ 0 ∧
      W.divisor f = Finsupp.single (pointClosedPoint hns.left) (n : ℤ) ∧
      ∃ gS : W.FunctionField, gS ≠ 0 ∧
        ∃ u : W.CoordinateRingˣ, (u : W.CoordinateRing) • gS ^ n
          = mulByNEndo n (transcendental_xCoord_nsmul_genericPoint_of_intCast_ne_zero h2 hn) f :=
  exists_gS_n_of_isAlgClosed h2 hn _ hns hS

/-! ### Recovery of the two merged numeral layers, compiled

⚠️ **The containment is committed here rather than asserted in a docstring**, following
`EllipticCurves.FunctionField.MulByNFibre` and `EllipticCurves.FunctionField.NthRootOfPullbackN`,
which do the same on their fronts.  Each `example` restates a merged headline **verbatim** and
proves it from the general layer.

⚠️ **The two `mulByNEndo` terms carry different transcendence proofs**, and they are interchangeable
because `Transcendental` is a `Prop`; that is what makes these typecheck at all.  The bridges to the
merged numeral endomorphisms are `mulByNEndo_two` and `mulByNEndo_three`
(`EllipticCurves.FunctionField.MulByNPullback`).

⚠️ **Neither original `omit`s anything from the ambient block**, so these carry the same instances
their originals do.  That was checked against the `omit` lines of
`PullbackPrincipalityTwo`'s and `PullbackPrincipalityThree`'s `IsAlgClosed` sections, not by
comparing signature strings: an `example` that quietly keeps an instance its original omits restates
something *weaker* than the theorem it claims to subsume, and the signatures match either way. -/

/-- **`exists_gS_two_of_isAlgClosed` is a corollary of `exists_gS_n_of_isAlgClosed`** — its
statement verbatim, proved from the general layer. -/
example (h2 : (2 : F) ≠ 0) {x y : F} (h : W.Nonsingular x y)
    (hS : Point.some x y h ∈ W.torsion 2) :
    ∃ f : W.FunctionField, f ≠ 0 ∧
      W.divisor f = Finsupp.single (pointClosedPoint h.left) (2 : ℤ) ∧
      ∃ gS : W.FunctionField, gS ≠ 0 ∧
        ∃ u : W.CoordinateRingˣ, (u : W.CoordinateRing) • gS ^ 2 = mulByTwoEndo h2 f := by
  obtain ⟨f, hf, hfdiv, gS, hgS, u, hu⟩ :=
    exists_gS_n_of_isAlgClosed (W := W) (n := 2) h2 (by exact_mod_cast h2)
      (transcendental_xCoord_two_nsmul h2) h hS
  exact ⟨f, hf, hfdiv, gS, hgS, u, by rwa [mulByNEndo_two h2] at hu⟩

/-- **`exists_gS_three_of_isAlgClosed` is a corollary of `exists_gS_n_of_isAlgClosed`** — its
statement verbatim, proved from the general layer. -/
example (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) {x y : F} (h : W.Nonsingular x y)
    (hS : Point.some x y h ∈ W.torsion 3) :
    ∃ f : W.FunctionField, f ≠ 0 ∧
      W.divisor f = Finsupp.single (pointClosedPoint h.left) (3 : ℤ) ∧
      ∃ gS : W.FunctionField, gS ≠ 0 ∧
        ∃ u : W.CoordinateRingˣ, (u : W.CoordinateRing) • gS ^ 3 = mulByThreeEndo h2 h3 f := by
  obtain ⟨f, hf, hfdiv, gS, hgS, u, hu⟩ :=
    exists_gS_n_of_isAlgClosed (W := W) (n := 3) h2 (by exact_mod_cast h3)
      (transcendental_xCoord_three_nsmul h2 h3) h hS
  exact ⟨f, hf, hfdiv, gS, hgS, u, by rwa [mulByNEndo_three h2 h3] at hu⟩

/-! ### Non-vacuity at every index, not only at a numeral

⚠️ **A certificate at `n = 2` or `n = 3` would prove nothing this file's two ancestors do not**, so
the witness has to be produced at an arbitrary index.  It can be: `#242` says `#E[n] = n²`, which is
`> 1` as soon as `n ≥ 2`, and every nonzero point of `W.Point` is affine by construction.  ⚠️ **The
point is not nameable** — that is what `exists_nonsingular_mem_torsion` being an existence statement
records, and it is why the certificate below is stated at a *quantified* index rather than
exhibiting coordinates the way `PullbackPrincipalityThree` exhibits `(0, 0)`. -/

omit [IsDedekindDomain W.CoordinateRing] in
/-- **Over `F̄` the `n`-torsion has an affine point at every `n ≠ 0, 1` with `(2 : F) ≠ 0` and
`(n : F) ≠ 0`.**  `#E[n] = n² ≥ 4 > 1` (`card_torsion_eq_sq`, `#242`), so `E[n]` is nontrivial, and
a nonzero point of `W.Point` is a `Point.some` by construction. -/
theorem exists_nonsingular_mem_torsion (h2 : (2 : F) ≠ 0) {n : ℕ} (hn : (n : F) ≠ 0) (hn1 : n ≠ 1) :
    ∃ (x y : F) (h : W.Nonsingular x y), Point.some x y h ∈ W.torsion n := by
  have hn0 : n ≠ 0 := by rintro rfl; simp at hn
  haveI := W.finite_torsion_of_intCast_ne_zero h2 hn
  have hcard : Nat.card (W.torsion n) = n ^ 2 := card_torsion_eq_sq h2 hn
  have h1n : 1 < Nat.card (W.torsion n) := by
    rw [hcard]
    have : 2 ≤ n := by omega
    calc 1 < 2 ^ 2 := by norm_num
    _ ≤ n ^ 2 := Nat.pow_le_pow_left this 2
  haveI : Nontrivial (W.torsion n) := Finite.one_lt_card_iff_nontrivial.mp h1n
  obtain ⟨T, hT⟩ := exists_ne (0 : W.torsion n)
  have hT0 : (T : W.Point) ≠ 0 := fun hc => hT (Subtype.ext hc)
  match hTP : (T : W.Point), hT0 with
  | Point.some x y h, _ => exact ⟨x, y, h, hTP ▸ T.2⟩

/-- **The headline, committed at an index outside `{2, 3}`**: rung 5 with no `hprin` at `n = 5`,
over the algebraic closure of `ℚ`, on the curve `y² + y = x³`.  ⚠️ The `5`-torsion point is produced
by `exists_nonsingular_mem_torsion` and not exhibited; unlike `PullbackPrincipalityThree`'s `(0, 0)`
it has no closed form here, and pretending otherwise is what this block exists to avoid. -/
example : ∃ (x y : EllipticCurves.Fixture.AlgClosedQ)
    (hns : (EllipticCurves.Fixture.y2AddYEqX3 EllipticCurves.Fixture.AlgClosedQ).Nonsingular x y),
    ∃ f : (EllipticCurves.Fixture.y2AddYEqX3 EllipticCurves.Fixture.AlgClosedQ).FunctionField,
      f ≠ 0 ∧
      (EllipticCurves.Fixture.y2AddYEqX3 EllipticCurves.Fixture.AlgClosedQ).divisor f
        = Finsupp.single (pointClosedPoint hns.left) (5 : ℤ) ∧
      ∃ gS : (EllipticCurves.Fixture.y2AddYEqX3
          EllipticCurves.Fixture.AlgClosedQ).FunctionField, gS ≠ 0 ∧
        ∃ u : (EllipticCurves.Fixture.y2AddYEqX3
            EllipticCurves.Fixture.AlgClosedQ).CoordinateRingˣ,
          (u : (EllipticCurves.Fixture.y2AddYEqX3
              EllipticCurves.Fixture.AlgClosedQ).CoordinateRing) • gS ^ 5
            = mulByNEndo 5 (transcendental_xCoord_nsmul_genericPoint_of_intCast_ne_zero
                (W := EllipticCurves.Fixture.y2AddYEqX3 EllipticCurves.Fixture.AlgClosedQ)
                (by norm_num) (by norm_num)) f := by
  classical
  obtain ⟨x, y, hns, hS⟩ :=
    exists_nonsingular_mem_torsion
      (W := EllipticCurves.Fixture.y2AddYEqX3 EllipticCurves.Fixture.AlgClosedQ)
      (n := 5) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨x, y, hns, exists_gS_of_ne_zero_of_isAlgClosed (by norm_num) (by norm_num) hns hS⟩

end IsAlgClosed

end WeierstrassCurve.Affine
