/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import EllipticCurves.FunctionField.PullbackPrincipalityNRationalTorsion
import EllipticCurves.FunctionField.PullbackPrincipalityThreeRationalTorsion

/-!
# `hprin` at a general `n` over an arbitrary field — the two headlines

`EllipticCurves.FunctionField.PullbackPrincipalityN` discharges `hprin` at every `n` with
`(2 : F) ≠ 0` and `((n : ℤ) : F) ≠ 0`, and it does so **inside a `section IsAlgClosed`**.
`EllipticCurves.FunctionField.PullbackPrincipalityNRationalTorsion` takes that section's Galois
scaffolding off `F̄` — seventeen statements, the `_of_card` family — and says in terms, in its
`## What is *not* here`, what it does not do:

> * **No headline.**  Neither `exists_nsmul_divisor_eq_divisor_mulByNEndo_of_card` nor
>   `exists_gS_n_of_card` is stated, so ⚠️ **`hprin` is not discharged at general `n` by this
>   file**

**This file states those two.**  ⚠️ **That bullet closed with one more conjunct** — *"and the
`[IsAlgClosed F]` forms in `PullbackPrincipalityN` remain the only ones"* — **which this file
falsifies, and it is retired at the bullet rather than here**; the two clauses quoted above are
claims about *that* file's reach and stay true of it.

`#962` asked for `hprin` off `F̄` and is landed at `n = 2` and at `n = 3`; `exists_gS_n_of_card`
below is the same conclusion at an arbitrary index.

## What the closure was doing, and what replaces it

`PullbackPrincipalityN`'s chain from the fibre description to the headline is five theorems.
**Three** named closure inputs feed it, and every one of them is a hypothesis here:

* the **fibre description** reaches `fibre_comapProjPointN_eq_range_of_ne_zero` and the
  unramifiedness beside it, both inside `MulByNFibre`'s `section IsAlgClosed` → replaced by
  `fibre_comapProjPointN_eq_range_of_card` and `ramificationIdxN_eq_one_of_card`, which take
  `hsep` and `hcard`;
* the **class-group computation** reaches `card_torsion_eq_sq` (`#242`) for `#E[n] = n²`
  → replaced by `hcard : Nat.card (W.torsion n) = n ^ 2`;
* the **headline** reaches `nsmul_surjective_of_two_ne_zero` for the halving point
  → replaced by `hP : n • P = S`.

⚠️ **`three` is what this file counted, and it is not the number the sources give — read both
before quoting either.**  `PullbackPrincipalityN` says of the third input that it is *"one of the
two places `[IsAlgClosed F]` is load-bearing"*, a count over that file's own chain; `#2217`
round 3 found that the closure enters the **fibre layer** three times on its own, against
`MulByNFibre`'s section header saying twice.  The three above are *named inputs to this chain*,
which is a third population again, and it is the only one this file needs: the claim being made
is that each of the three is discharged, not that some total is `three`.

⚠️ **`hsep` is not a third hypothesis of the headlines.**  The two public headlines discharge it
internally from `hcard` through `isSeparable_mulByNEndoFieldRange_of_card`, which is the
declaration `PullbackPrincipalityNRationalTorsion` records as existing *"to keep `hsep` off the
headlines a later round states"*.  It is bound explicitly on the five intermediate statements,
where a caller may already hold it, and nowhere else.

## ⚠️ Why `hP` and not surjectivity of `[n]`

`hP : n • P = S` asks one point for one preimage.  **Bare `Function.Surjective (n • ·)` would be
the wrong hypothesis and would make the headline vacuous exactly where it is wanted**: with
`hcard` beside it, `#2292` records that it is contradictory over a number field at every
`n ≥ 2`.  `n = 2` has bound `hP` since PR #508, at both of its headlines, and `n = 3` does the
same; ⚠️ **the shape is the landed one at both existing rungs and is not a design choice made
here.**

The collapse that needs it is pointwise — `MulByNFibre` reaches for surjectivity in one `obtain`
and uses the resulting point thereafter — which is `#2292`'s finding and is what makes the
substitution possible at all.

## Main statements

**20** named declarations — **7** public theorems and **13** `private` helpers, two of them in
`## Recovery` and eleven in the `ℚ` block — plus **4** anonymous `example`s, all four of them
recovery certificates.  ⚠️ `#print axioms` over all seven public statements reaches **0**
`sorryAx` and nothing outside `{propext, Classical.choice, Quot.sound}`, all seven returning all
three.

⚠️ **Every one of the seven `omit`s nothing**, and that is a fact about this file rather than a
default: each carries `{F : Type*} [Field F] {W : Affine F}`,
`[IsDedekindDomain W.CoordinateRing]`, `[DecidableEq F]` and `[W.IsElliptic]` from the ambient
`variable` block, and all four are genuinely used in all seven — checked on the elaborated types
and by a warning-free `--wfail` build, whose unused-section-variable linter is what would say
otherwise.  ⚠️ That is the **opposite** of `PullbackPrincipalityNRationalTorsion`, where eleven of
seventeen `omit` `[IsDedekindDomain W.CoordinateRing]`: the Galois package is about a field
extension and this file is about divisors, and the divisor API is where the Dedekind hypothesis
lives.

The explicit-hypothesis census over the seven:

| binder | statements binding it, of 7 |
|---|---|
| `h : Transcendental F (n • genericPoint).xCoord` | 7 |
| `h2 : (2 : F) ≠ 0` | 7 |
| `hn : ((n : ℤ) : F) ≠ 0` | 7 |
| `hcard : Nat.card (W.torsion n) = n ^ 2` | 7 |
| `hP : n • P = S` | 7 |
| `hsep` | ⚠️ **5**, and it is absent from exactly the two headlines |
| `hS : n • S = 0` or `Point.some x y hns ∈ W.torsion n` | 4 |
| `[Fintype (W.torsion n)]` | 3 |
| `hfac` / `h3 : (3 : F) ≠ 0` / `hn : n ≠ 0` | ⚠️ **0** |

⚠️ **No `3`-smoothness anywhere, and no `(3 : F) ≠ 0`.**  `PullbackPrincipalityNRationalTorsion`'s
`intCast_ne_zero_of_smooth` shows the four-hypothesis general form **implies** the six-hypothesis
`3`-smooth one and that the converse fails, so reintroducing either here would narrow the
statement for nothing.

## Non-vacuity, and the index it is confined to

⚠️ **`n = 2` is the only index at which the `_of_card` hypotheses are certified jointly
satisfiable on this board, and this file says so rather than papering over it.**  `hcard` at any
`n ≥ 3` forces `μ_n ⊆ F` and so admits no `ℚ` certificate — the obstruction
`PullbackPrincipalityNRationalTorsion`'s own `## Non-vacuity` section records — and this file
inherits it unchanged.  `exampleRungFiveGeneral` is `exists_gS_n_of_card` at `n = 2` over `ℚ` on
`y² = x³ + 5x² + 4x`, **with no hypothesis at all**, and it names `mulByNEndo 2 …` rather than
`mulByTwoEndo`, so it certifies *this file's* statement and not the `n = 2` one it recovers.

## What is *not* here

* **The abstract-Galois descent.**  A general-`n` mirror of
  `exists_nsmul_divisor_eq_divisor_mulByThreeEndo_of_galois`
  (`EllipticCurves.FunctionField.PullbackPrincipalityThreeGeneral`) — ⚠️ **the `…_of_galois` name
  at a general index is a prospective one and is written without backticks here, because a
  backticked name is a live citation on this development and no such declaration exists** — and
  an unconditional `…_general` headline at a general `n` are `#2295` and `#2296`; the `n = 2` and
  `n = 3` `…General` files buy `hcard` and `hP` over a Galois tower and pay them back by
  Hilbert 90, and ⚠️ **that tower is three layers at `n = 2` and five at `n = 3`, so its depth at
  a general `n` is unbounded** and it is not a rung this file could have taken in passing.
* **Recovery of `PullbackPrincipalityN`'s `[IsAlgClosed F]` headlines into this file's names.**
  The two `private theorem`s in `## Recovery` derive those statements from these, which is the
  containment `#907` asks to be committed rather than asserted; they do **not** replace the
  originals, and a public copy would duplicate a merged name.
* **Any weakening of `hcard`.**  Whether `hprin` holds at a general `n` over a field where `E[n]`
  is *not* rational is `#962`'s question one index up, and nothing here bears on it.

## References

* [J. H. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.8.
-/

open Module IsLocalRing IsDedekindDomain IsDedekindDomain.HeightOneSpectrum

namespace WeierstrassCurve.Affine

variable {F : Type*} [Field F] {W : Affine F} [IsDedekindDomain W.CoordinateRing]
  [DecidableEq F] [W.IsElliptic]

namespace CoordinateRing

/-! ### The fibre description of `[n]∗`, uncollapsed -/

/-- **`[n]∗(S) = ∑_{R ∈ E[n]} (P ⊕ R)`** for any `P` with `n • P = S`, over an arbitrary field at
every `n` with `(2 : F) ≠ 0` and `((n : ℤ) : F) ≠ 0`, at a rational `E[n]` and separability.

⚠️ **Reach, in full**: `(2 : F) ≠ 0`, `((n : ℤ) : F) ≠ 0`, non-constancy of `x([n]𝒫)`,
separability of `F(W) / [n]∗F(W)`, `#E[n] = n²` and a point `P` with `[n]P = S` — six, and the
`[Fintype (W.torsion n)]` instance beside them.

`pullbackDivisorN_single_eq_sum_torsion_of_ne_zero` (`EllipticCurves.FunctionField.MulByNFibre`)
is this statement over `F̄`; the two closure inputs it reaches for — the fibre description and the
unramifiedness — are `fibre_comapProjPointN_eq_range_of_card` and `ramificationIdxN_eq_one_of_card`
here, and nothing else in the proof changes.  The general-`n` form of
`pullbackDivisorTwo_single_eq_sum_torsion_of_card`.

The `[Fintype (W.torsion n)]` is carried in the statement for the reason `#763` gives and both
existing rungs repeat: the sum cannot be written without it, and `Fintype.ofFinite` in a statement
is a noncomputable leak.  `finite_torsion_of_intCast_ne_zero` supplies it at the point of use. -/
theorem pullbackDivisorN_single_eq_sum_torsion_of_card {n : ℕ} [Fintype (W.torsion n)]
    (h2 : (2 : F) ≠ 0) (hn : ((n : ℤ) : F) ≠ 0)
    (h : Transcendental F (n • genericPoint (W := W)).xCoord)
    (hsep : Algebra.IsSeparable ↥(mulByNEndo (W := W) n h).fieldRange W.FunctionField)
    (hcard : Nat.card (W.torsion n) = n ^ 2) {S P : W.Point} (hP : n • P = S) :
    pullbackDivisorN n h (Finsupp.single (projPointOfPoint W S) (1 : ℤ))
      = ∑ R : W.torsion n, Finsupp.single (projPointOfPoint W (P + R)) (1 : ℤ) := by
  classical
  ext q
  rw [pullbackDivisorN_apply, Finset.sum_apply',
    Finset.sum_congr rfl fun R _ => Finsupp.single_apply]
  by_cases hq : comapProjPointN n h q = projPointOfPoint W S
  · obtain ⟨R₀, hR₀⟩ : q ∈ Set.range fun R : W.torsion n => projPointOfPoint W (P + R) := by
      rw [← fibre_comapProjPointN_eq_range_of_card h2 hn h hsep hcard hP]; exact hq
    rw [hq, Finsupp.single_eq_same, mul_one,
      ramificationIdxN_eq_one_of_card h2 hn h hsep hcard hP hq,
      Finset.sum_eq_single R₀ (fun R _ hRne => if_neg fun hc =>
        hRne (projPointOfPoint_add_injective n P (hc.trans hR₀.symm)))
      (fun hc => absurd (Finset.mem_univ R₀) hc), if_pos hR₀]
  · rw [Finsupp.single_apply, if_neg fun hc => hq hc.symm, mul_zero, Finset.sum_eq_zero]
    intro R _
    refine if_neg fun hc => hq ?_
    rw [← hc]
    exact comapProjPointN_add_torsion_of_ne_zero h2 hn h hP R

end CoordinateRing

/-! ### Principality of `[n]∗((S) − (O))` at a rational `E[n]` -/

open CoordinateRing

/-- **`[n]∗((S) − (O)) = ∑_{R ∈ E[n]} ((P ⊕ R) − (R))`**, over an arbitrary field at every `n` with
`(2 : F) ≠ 0`, `((n : ℤ) : F) ≠ 0`, non-constancy of `x([n]𝒫)`, separability, `#E[n] = n²` and a
point `P` with `[n]P = S` — the previous theorem's six hypotheses and no others.  The `(O)` half is
the same theorem at `S = O` with `P = O`, since `projPointOfPoint W 0` is `none` by `rfl`.  No new
geometry. -/
theorem pullbackDivisorN_single_sub_single_eq_sum_torsion_of_card {n : ℕ}
    [Fintype (W.torsion n)] (h2 : (2 : F) ≠ 0) (hn : ((n : ℤ) : F) ≠ 0)
    (h : Transcendental F (n • genericPoint (W := W)).xCoord)
    (hsep : Algebra.IsSeparable ↥(mulByNEndo (W := W) n h).fieldRange W.FunctionField)
    (hcard : Nat.card (W.torsion n) = n ^ 2) {S P : W.Point} (hP : n • P = S) :
    pullbackDivisorN n h (Finsupp.single (projPointOfPoint W S) (1 : ℤ)
        - Finsupp.single (none : ProjPoint W) (1 : ℤ))
      = ∑ R : W.torsion n, (Finsupp.single (projPointOfPoint W (P + R)) (1 : ℤ)
          - Finsupp.single (projPointOfPoint W (R : W.Point)) (1 : ℤ)) := by
  have hO : (none : ProjPoint W) = projPointOfPoint W 0 := rfl
  rw [map_sub, pullbackDivisorN_single_eq_sum_torsion_of_card h2 hn h hsep hcard hP, hO,
    pullbackDivisorN_single_eq_sum_torsion_of_card h2 hn h hsep hcard (smul_zero n),
    ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun R _ => by rw [zero_add]

/-- The same formula on the affine chart, where `hprin` lives, under the same six hypotheses —
`(2 : F) ≠ 0`, `((n : ℤ) : F) ≠ 0`, non-constancy of `x([n]𝒫)`, separability, `#E[n] = n²` and a
point `P` with `[n]P = S`; each `(O)` drops out (`affinePart_single_none`). -/
theorem affinePart_pullbackDivisorN_single_sub_single_of_card {n : ℕ}
    [Fintype (W.torsion n)] (h2 : (2 : F) ≠ 0) (hn : ((n : ℤ) : F) ≠ 0)
    (h : Transcendental F (n • genericPoint (W := W)).xCoord)
    (hsep : Algebra.IsSeparable ↥(mulByNEndo (W := W) n h).fieldRange W.FunctionField)
    (hcard : Nat.card (W.torsion n) = n ^ 2) {S P : W.Point} (hP : n • P = S) :
    W.affinePart (pullbackDivisorN n h (Finsupp.single (projPointOfPoint W S) (1 : ℤ)
        - Finsupp.single (none : ProjPoint W) (1 : ℤ)))
      = ∑ R : W.torsion n, (W.pointDivisorAff (P + R) - W.pointDivisorAff (R : W.Point)) := by
  rw [pullbackDivisorN_single_sub_single_eq_sum_torsion_of_card h2 hn h hsep hcard hP, map_sum]
  exact Finset.sum_congr rfl fun R _ => map_sub _ _ _

/-- **The class-group computation**, over an arbitrary field, under `(2 : F) ≠ 0`,
`((n : ℤ) : F) ≠ 0`, non-constancy of `x([n]𝒫)`, separability, `#E[n] = n²`, a point `P` with
`[n]P = S` and `n • S = 0` — seven, one more than the three above:

```
∑_R toClass (P ⊕ R) − ∑_R toClass R = n² • toClass P = toClass (n² • P) = toClass (n • S) = 0.
```

⚠️ **The count of summands is `hcard` and not `card_torsion_eq_sq`**, which is the single
difference from `classOfDivisor_affinePart_pullbackDivisorN_eq_one`
(`EllipticCurves.FunctionField.PullbackPrincipalityN`) and is the whole reason that theorem sits
inside a `section IsAlgClosed`: `#242` is where the closure entered, and a hypothesis discharges it
here exactly as `card_torsion_two` is replaced by `hcard` at `n = 2`.

⚠️ No step divides a divisor by `n`.  `n · D` principal does **not** imply `D` principal — that
failure is the `n`-torsion of the class group the Weil pairing measures — and the argument exhibits
the class of `D` as trivial directly. -/
theorem classOfDivisor_affinePart_pullbackDivisorN_eq_one_of_card {n : ℕ} (h2 : (2 : F) ≠ 0)
    (hn : ((n : ℤ) : F) ≠ 0)
    (h : Transcendental F (n • genericPoint (W := W)).xCoord)
    (hsep : Algebra.IsSeparable ↥(mulByNEndo (W := W) n h).fieldRange W.FunctionField)
    (hcard : Nat.card (W.torsion n) = n ^ 2) {S P : W.Point} (hP : n • P = S) (hS : n • S = 0) :
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
  have hc : Fintype.card (W.torsion n) = n ^ 2 := by
    rw [← Nat.card_eq_fintype_card, hcard]
  rw [affinePart_pullbackDivisorN_single_sub_single_of_card h2 hn h hsep hcard hP,
    classOfDivisor_sum, Finset.prod_congr rfl hterm, Finset.prod_const, Finset.card_univ, hc,
    ← toMul_nsmul, ← map_nsmul, hPsq, Point.toClass_zero]
  rfl

/-- **`[n]∗((S) − (O))` is principal on the affine chart**, over an arbitrary field, under the
same seven hypotheses as the class computation — `(2 : F) ≠ 0`, `((n : ℤ) : F) ≠ 0`, non-constancy
of `x([n]𝒫)`, separability, `#E[n] = n²`, `[n]P = S` and `n • S = 0`: the vanishing class above
turned back into a generator by `#726`'s criterion, which never needed a closure. -/
theorem exists_divisor_eq_affinePart_pullbackDivisorN_of_card {n : ℕ} (h2 : (2 : F) ≠ 0)
    (hn : ((n : ℤ) : F) ≠ 0)
    (h : Transcendental F (n • genericPoint (W := W)).xCoord)
    (hsep : Algebra.IsSeparable ↥(mulByNEndo (W := W) n h).fieldRange W.FunctionField)
    (hcard : Nat.card (W.torsion n) = n ^ 2) {S P : W.Point} (hP : n • P = S) (hS : n • S = 0) :
    ∃ g : W.FunctionField, g ≠ 0 ∧ W.divisor g = W.affinePart (pullbackDivisorN n h
      (Finsupp.single (projPointOfPoint W S) (1 : ℤ)
        - Finsupp.single (none : ProjPoint W) (1 : ℤ))) :=
  (exists_divisor_eq_iff_classOfDivisor_eq_one _).2
    (classOfDivisor_affinePart_pullbackDivisorN_eq_one_of_card h2 hn h hsep hcard hP hS)

/-! ### The two headlines -/

/-- **`hprin` at a general `n` over an arbitrary field**, in the shape `exists_gS_n` consumes it:
for a nonsingular `n`-torsion point `S = (x, y)` on a curve whose `n`-torsion is rational and which
has a point `P` with `[n]P = S`, the pullback `[n]∗((S) − (O))` is `n` times a principal divisor.

⚠️ **Reach, in full and read off the elaborated type**: `(2 : F) ≠ 0`, `((n : ℤ) : F) ≠ 0`,
non-constancy of `x([n]𝒫)`, `#E[n] = n²`, the nonsingularity and `n`-torsion of `S`, a point `P`
with `[n]P = S`, and a nonzero `f` whose divisor is `n·(S)`.  **Separability is *not* among them**,
and that is the next paragraph.

⚠️ **`hsep` is discharged internally from `hcard`** by `isSeparable_mulByNEndoFieldRange_of_card`,
so it is absent from this signature and from `exists_gS_n_of_card` below; what is left is `h2`,
`hn`, `h`, `hcard`, `hP`, the nonsingularity and `n`-torsion of `S`, and a nonzero `f` whose divisor
is `n·(S)`.

⚠️ **This is `exists_nsmul_divisor_eq_divisor_mulByNEndo`
(`EllipticCurves.FunctionField.PullbackPrincipalityN`) with its two closure inputs replaced by
hypotheses**, and the two are exactly the ones that file names: the halving point, which it takes
from `nsmul_surjective_of_two_ne_zero` and this statement takes as `hP`, and `#242`'s count, which
enters through the class-group computation and is `hcard` here.  ⚠️ **`hP` is one preimage of one
point and not surjectivity of `[n]`**: `#2292` records that bare `Function.Surjective (n • ·)`
beside `hcard` is contradictory over a number field at every `n ≥ 2`, which would make the headline
vacuous exactly where it is wanted, and `n = 2` has bound `hP` rather than surjectivity since
PR #508. -/
theorem exists_nsmul_divisor_eq_divisor_mulByNEndo_of_card {n : ℕ} (h2 : (2 : F) ≠ 0)
    (hn : ((n : ℤ) : F) ≠ 0)
    (h : Transcendental F (n • genericPoint (W := W)).xCoord)
    (hcard : Nat.card (W.torsion n) = n ^ 2)
    {x y : F} (hns : W.Nonsingular x y) (hS : Point.some x y hns ∈ W.torsion n)
    {P : W.Point} (hP : n • P = Point.some x y hns)
    {f : W.FunctionField} (hf : f ≠ 0)
    (hfdiv : W.divisor f = Finsupp.single (pointClosedPoint hns.left) (n : ℤ)) :
    ∃ g₀ : W.FunctionField, g₀ ≠ 0 ∧
      n • W.divisor g₀ = W.divisor (mulByNEndo n h f) := by
  classical
  have hnF : (n : F) ≠ 0 := by exact_mod_cast hn
  have hsep := isSeparable_mulByNEndoFieldRange_of_card h2 hnF h hcard
  obtain ⟨g, hg, hgdiv⟩ :=
    exists_divisor_eq_affinePart_pullbackDivisorN_of_card h2 hn h hsep hcard hP
      (mem_torsion_iff.mp hS)
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

/-- **Rung 5 of the Weil pairing at a general `n`, over an arbitrary field**: there are a principal
`f_S` with `div f_S = n·(S)` and a nonzero `g_S` with `u · g_S ^ n = [n]∗ f_S` for a unit `u` of
`F[W]`.

⚠️ **Reach, in full and read off the elaborated type**: `(2 : F) ≠ 0`, `((n : ℤ) : F) ≠ 0`,
non-constancy of `x([n]𝒫)`, `#E[n] = n²`, the nonsingularity and `n`-torsion of `S`, and a point
`P` with `[n]P = S` — seven, one fewer than the theorem above, which also binds the `f` it
quantifies over.

`exists_gS_n_of_isAlgClosed` (`EllipticCurves.FunctionField.PullbackPrincipalityN`) is this
statement over `F̄`, where both `hcard` and `hP` are theorems; the `## Recovery` section below
derives it from this one.  The general-`n` form of `exists_gS_two_of_card` and
`exists_gS_three_of_card`. -/
theorem exists_gS_n_of_card {n : ℕ} (h2 : (2 : F) ≠ 0) (hn : ((n : ℤ) : F) ≠ 0)
    (h : Transcendental F (n • genericPoint (W := W)).xCoord)
    (hcard : Nat.card (W.torsion n) = n ^ 2)
    {x y : F} (hns : W.Nonsingular x y) (hS : Point.some x y hns ∈ W.torsion n)
    {P : W.Point} (hP : n • P = Point.some x y hns) :
    ∃ f : W.FunctionField, f ≠ 0 ∧
      W.divisor f = Finsupp.single (pointClosedPoint hns.left) (n : ℤ) ∧
      ∃ gS : W.FunctionField, gS ≠ 0 ∧
        ∃ u : W.CoordinateRingˣ, (u : W.CoordinateRing) • gS ^ n = mulByNEndo n h f :=
  exists_gS_n h hns hS fun _ hf hfdiv =>
    exists_nsmul_divisor_eq_divisor_mulByNEndo_of_card h2 hn h hcard hns hS hP hf hfdiv

/-! ### Recovery of the two numeral rungs and of the two merged closed statements

`#907`'s rule, in both directions.  The four `example`s restate the `n = 2` and `n = 3` headlines
**verbatim** and prove each from the general form, so nothing the tree states is given up; the two
`private theorem`s recover the `[IsAlgClosed F]` headlines of
`EllipticCurves.FunctionField.PullbackPrincipalityN`, where `hcard` is `card_torsion_eq_sq` and
`hP` is `nsmul_surjective_of_two_ne_zero`.  Both of the latter are `private`: a public copy would
duplicate a merged name.

⚠️ **The two `mulByNEndo` terms carry different transcendence proofs**, and they are interchangeable
because `Transcendental` is a `Prop`; the bridges to the numeral endomorphisms are `mulByNEndo_two`
and `mulByNEndo_three` (`EllipticCurves.FunctionField.MulByNPullback`).

⚠️ **Neither numeral original `omit`s anything from its ambient block** — checked by reading the
elaborated types of `exists_nsmul_divisor_eq_divisor_mulByTwoEndo_of_card`, `exists_gS_two_of_card`,
`exists_nsmul_divisor_eq_divisor_mulByThreeEndo_of_card` and `exists_gS_three_of_card`, each of
which carries `[IsDedekindDomain W.CoordinateRing]`, `[DecidableEq F]` and `[W.IsElliptic]`, and
not by comparing signature strings: an `example` that quietly keeps an instance its original omits
restates something *weaker* than the theorem it claims to subsume, and the signatures match either
way. -/

section Recovery

/-- **`exists_nsmul_divisor_eq_divisor_mulByTwoEndo_of_card`
(`EllipticCurves.FunctionField.PullbackPrincipalityTwoRationalTorsion`) is a corollary** — its
statement verbatim, proved from the general form. -/
example (h2 : (2 : F) ≠ 0) (hcard : Nat.card (W.torsion 2) = 4) {x y : F}
    (h : W.Nonsingular x y) (hS : Point.some x y h ∈ W.torsion 2)
    {P : W.Point} (hP : 2 • P = Point.some x y h)
    {f : W.FunctionField} (hf : f ≠ 0)
    (hfdiv : W.divisor f = Finsupp.single (pointClosedPoint h.left) (2 : ℤ)) :
    ∃ g₀ : W.FunctionField, g₀ ≠ 0 ∧ 2 • W.divisor g₀ = W.divisor (mulByTwoEndo h2 f) := by
  obtain ⟨g₀, hg₀, hdiv⟩ :=
    exists_nsmul_divisor_eq_divisor_mulByNEndo_of_card (W := W) (n := 2) h2
      (by exact_mod_cast h2) (transcendental_xCoord_two_nsmul h2) (by simpa using hcard) h hS hP hf
      (by exact_mod_cast hfdiv)
  exact ⟨g₀, hg₀, by rwa [mulByNEndo_two h2] at hdiv⟩

/-- **`exists_gS_two_of_card`
(`EllipticCurves.FunctionField.PullbackPrincipalityTwoRationalTorsion`) is a corollary** — its
statement verbatim, proved from the general form. -/
example (h2 : (2 : F) ≠ 0) (hcard : Nat.card (W.torsion 2) = 4) {x y : F}
    (h : W.Nonsingular x y) (hS : Point.some x y h ∈ W.torsion 2)
    {P : W.Point} (hP : 2 • P = Point.some x y h) :
    ∃ f : W.FunctionField, f ≠ 0 ∧
      W.divisor f = Finsupp.single (pointClosedPoint h.left) (2 : ℤ) ∧
      ∃ gS : W.FunctionField, gS ≠ 0 ∧
        ∃ u : W.CoordinateRingˣ, (u : W.CoordinateRing) • gS ^ 2 = mulByTwoEndo h2 f := by
  obtain ⟨f, hf, hfdiv, gS, hgS, u, hu⟩ :=
    exists_gS_n_of_card (W := W) (n := 2) h2 (by exact_mod_cast h2)
      (transcendental_xCoord_two_nsmul h2) (by simpa using hcard) h hS hP
  exact ⟨f, hf, by exact_mod_cast hfdiv, gS, hgS, u, by rwa [mulByNEndo_two h2] at hu⟩

/-- **`exists_nsmul_divisor_eq_divisor_mulByThreeEndo_of_card`
(`EllipticCurves.FunctionField.PullbackPrincipalityThreeRationalTorsion`) is a corollary** — its
statement verbatim, proved from the general form. -/
example (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) (hcard : Nat.card (W.torsion 3) = 9) {x y : F}
    (h : W.Nonsingular x y) (hS : Point.some x y h ∈ W.torsion 3)
    {P : W.Point} (hP : 3 • P = Point.some x y h)
    {f : W.FunctionField} (hf : f ≠ 0)
    (hfdiv : W.divisor f = Finsupp.single (pointClosedPoint h.left) (3 : ℤ)) :
    ∃ g₀ : W.FunctionField, g₀ ≠ 0 ∧ 3 • W.divisor g₀ = W.divisor (mulByThreeEndo h2 h3 f) := by
  obtain ⟨g₀, hg₀, hdiv⟩ :=
    exists_nsmul_divisor_eq_divisor_mulByNEndo_of_card (W := W) (n := 3) h2
      (by exact_mod_cast h3) (transcendental_xCoord_three_nsmul h2 h3) (by simpa using hcard) h hS
      hP hf (by exact_mod_cast hfdiv)
  exact ⟨g₀, hg₀, by rwa [mulByNEndo_three h2 h3] at hdiv⟩

/-- **`exists_gS_three_of_card`
(`EllipticCurves.FunctionField.PullbackPrincipalityThreeRationalTorsion`) is a corollary** — its
statement verbatim, proved from the general form. -/
example (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) (hcard : Nat.card (W.torsion 3) = 9) {x y : F}
    (h : W.Nonsingular x y) (hS : Point.some x y h ∈ W.torsion 3)
    {P : W.Point} (hP : 3 • P = Point.some x y h) :
    ∃ f : W.FunctionField, f ≠ 0 ∧
      W.divisor f = Finsupp.single (pointClosedPoint h.left) (3 : ℤ) ∧
      ∃ gS : W.FunctionField, gS ≠ 0 ∧
        ∃ u : W.CoordinateRingˣ, (u : W.CoordinateRing) • gS ^ 3 = mulByThreeEndo h2 h3 f := by
  obtain ⟨f, hf, hfdiv, gS, hgS, u, hu⟩ :=
    exists_gS_n_of_card (W := W) (n := 3) h2 (by exact_mod_cast h3)
      (transcendental_xCoord_three_nsmul h2 h3) (by simpa using hcard) h hS hP
  exact ⟨f, hf, by exact_mod_cast hfdiv, gS, hgS, u, by rwa [mulByNEndo_three h2 h3] at hu⟩

variable [IsAlgClosed F]

/-- `exists_nsmul_divisor_eq_divisor_mulByNEndo`
(`EllipticCurves.FunctionField.PullbackPrincipalityN`), recovered. -/
private theorem exists_nsmul_divisor_eq_divisor_mulByNEndo_of_general {n : ℕ} (h2 : (2 : F) ≠ 0)
    (hn : ((n : ℤ) : F) ≠ 0)
    (h : Transcendental F (n • genericPoint (W := W)).xCoord)
    {x y : F} (hns : W.Nonsingular x y) (hS : Point.some x y hns ∈ W.torsion n)
    {f : W.FunctionField} (hf : f ≠ 0)
    (hfdiv : W.divisor f = Finsupp.single (pointClosedPoint hns.left) (n : ℤ)) :
    ∃ g₀ : W.FunctionField, g₀ ≠ 0 ∧
      n • W.divisor g₀ = W.divisor (mulByNEndo n h f) :=
  have hnF : (n : F) ≠ 0 := by exact_mod_cast hn
  have hn0 : n ≠ 0 := by rintro rfl; simp at hnF
  let ⟨_, hP⟩ := nsmul_surjective_of_two_ne_zero (W := W) h2 hn0 (Point.some x y hns)
  exists_nsmul_divisor_eq_divisor_mulByNEndo_of_card h2 hn h (card_torsion_eq_sq h2 hnF) hns hS hP
    hf hfdiv

/-- `exists_gS_n_of_isAlgClosed` (`EllipticCurves.FunctionField.PullbackPrincipalityN`),
recovered. -/
private theorem exists_gS_n_of_isAlgClosed_of_general {n : ℕ} (h2 : (2 : F) ≠ 0)
    (hn : ((n : ℤ) : F) ≠ 0)
    (h : Transcendental F (n • genericPoint (W := W)).xCoord)
    {x y : F} (hns : W.Nonsingular x y) (hS : Point.some x y hns ∈ W.torsion n) :
    ∃ f : W.FunctionField, f ≠ 0 ∧
      W.divisor f = Finsupp.single (pointClosedPoint hns.left) (n : ℤ) ∧
      ∃ gS : W.FunctionField, gS ≠ 0 ∧
        ∃ u : W.CoordinateRingˣ, (u : W.CoordinateRing) • gS ^ n = mulByNEndo n h f :=
  have hnF : (n : F) ≠ 0 := by exact_mod_cast hn
  have hn0 : n ≠ 0 := by rintro rfl; simp at hnF
  let ⟨_, hP⟩ := nsmul_surjective_of_two_ne_zero (W := W) h2 hn0 (Point.some x y hns)
  exists_gS_n_of_card h2 hn h (card_torsion_eq_sq h2 hnF) hns hS hP

end Recovery

/-! ### Non-vacuity over `ℚ`, and the index it is confined to

⚠️ **The certificate has to be over a field that is not algebraically closed**, or it certifies
`exists_gS_n_of_isAlgClosed` instead of anything here (`#916`).

⚠️ **`n = 2` is the only index at which the `_of_card` hypotheses are certified jointly
satisfiable, and this file does not paper over that.**  The `## Non-vacuity` section of
`EllipticCurves.FunctionField.PullbackPrincipalityNRationalTorsion` records the obstruction:
`hcard` at any `n ≥ 3` forces `μ_n ⊆ F`, which is false over `ℚ`, so no `ℚ` certificate can exist
there and none is claimed.  What is committed below is the statement of this file at `n = 2`, over
`ℚ`, **with no hypothesis at all** — which is what shows `hcard` and `hP` are not jointly
contradictory, the failure mode `#2292` warns `Function.Surjective (n • ·)` would have walked
into.

The certificate curve `y² = x³ + 5x² + 4x` is the shared
`EllipticCurves.Fixture.y2EqX3Add5X2Add4X`, whose single `[CharZero F]` instance also supplies
`IsElliptic` here.  ⚠️ **The five fixture lemmas below re-derive `private` lemmas of
`PullbackPrincipalityTwoRationalTorsion` and `WeilPairingAlternatingTwoRational`**, which carry the
same block; they are `private` there and so not importable, and re-deriving them per file is what
those two files and `EllipticCurves.Torsion.TwoTorsion` already do. -/

section Nonvacuity

open EllipticCurves.Fixture

private lemma exampleTwo : (2 : ℚ) ≠ 0 := by norm_num

/-- `T = (0, 0)`, the `2`-torsion point cut out by `x = 0`. -/
private lemma exampleNsT : (y2EqX3Add5X2Add4X ℚ).Nonsingular 0 0 :=
  (y2EqX3Add5X2Add4X ℚ).equation_iff_nonsingular.mp (by
    norm_num [y2EqX3Add5X2Add4X, WeierstrassCurve.Affine.equation_iff])

/-- `(2, 6)`, the point of `E(ℚ)` sitting above the root `x = 2` of `Φ₂ − x(T)·Ψ₂Sq`:
`36 = 8 + 20 + 8`.  It enters only as the `Equation` witness `exampleNsP.left`. -/
private lemma exampleNsP : (y2EqX3Add5X2Add4X ℚ).Nonsingular 2 6 :=
  (y2EqX3Add5X2Add4X ℚ).equation_iff_nonsingular.mp (by
    norm_num [y2EqX3Add5X2Add4X, WeierstrassCurve.Affine.equation_iff])

private lemma exampleTorT : Point.some (0 : ℚ) 0 exampleNsT ∈ (y2EqX3Add5X2Add4X ℚ).torsion 2 :=
  (mem_torsion_two_some_iff exampleNsT).mpr (by norm_num [y2EqX3Add5X2Add4X])

open Polynomial in
/-- The `2`-torsion cubic of the example curve, factored: `4X³ + 20X² + 16X = 4·X·(X+1)·(X+4)`.

⚠️ `norm_num only` has to run **before** the `simp only`: the coefficients arrive as
`C (0 ^ 2 + 4 * 5)`, and `map_ofNat` cannot fire until its argument is a literal. -/
private lemma Ψ₂Sq_exampleCurve :
    (y2EqX3Add5X2Add4X ℚ).Ψ₂Sq = C 4 * X * (X + C 1) * (X + C 4) := by
  simp only [WeierstrassCurve.Ψ₂Sq, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, y2EqX3Add5X2Add4X]
  norm_num only
  simp only [map_ofNat, map_one, Polynomial.C_0]
  ring

open Polynomial in
/-- **The splitting hypothesis, discharged over `ℚ`**: a constant times three monic linear factors.

⚠️ Closed by the explicit term rather than by `simp`, which normalises `X + C 1` to `X + 1` first
and can then no longer match `Splits.X_add_C`. -/
private lemma splits_Ψ₂Sq_exampleCurve : (y2EqX3Add5X2Add4X ℚ).Ψ₂Sq.Splits := by
  rw [Ψ₂Sq_exampleCurve]
  exact (((Splits.C 4).mul Splits.X).mul (Splits.X_add_C 1)).mul (Splits.X_add_C 4)

/-- **`#E[2] = 2²` over `ℚ` for this curve**, which is `hcard` in the shape a general index wants.
`card_torsion_two_of_splits` (`EllipticCurves.Torsion.TwoTorsion`) buys from `Ψ₂Sq.Splits` exactly
the lower bound an algebraic closure buys in `card_torsion_two`. -/
private lemma exampleCard : Nat.card ((y2EqX3Add5X2Add4X ℚ).torsion 2) = 2 ^ 2 := by
  simpa using card_torsion_two_of_splits exampleTwo splits_Ψ₂Sq_exampleCurve

/-- **The root that does the work**: `Φ₂(2) = 0 = x(T) · Ψ₂Sq(2)`, since `Φ₂ = (X² − 4)²` here.
Routed through `Φ_two_eval` — `Φ₂(x) = x · Ψ₂Sq(x) − Ψ₃(x)`, giving `2 · 144 − 288 = 0`. -/
private lemma eval_Φ_two_exampleCurve :
    ((y2EqX3Add5X2Add4X ℚ).Φ 2).eval 2 = (0 : ℚ) * (y2EqX3Add5X2Add4X ℚ).Ψ₂Sq.eval 2 := by
  rw [Φ_two_eval]
  simp only [WeierstrassCurve.Ψ₂Sq, WeierstrassCurve.Ψ₃, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈, y2EqX3Add5X2Add4X]
  norm_num

/-- **`T = (0, 0)` is twice a rational point, and that point is not `T`** — the `hP` of
`exists_gS_n_of_card` at `n = 2`, derived from `eval_Φ_two_exampleCurve` rather than exhibited.

⚠️ The `≠ T` guard lives **inside** the existential deliberately, so that the `P` the certificate is
instantiated at is bound from a witness satisfying **both** conjuncts; that second component must
not be "cleaned up" as unused. -/
private lemma exampleExistsHalving :
    ∃ P : (y2EqX3Add5X2Add4X ℚ).Point,
      (2 : ℕ) • P = Point.some (0 : ℚ) 0 exampleNsT ∧ P ≠ Point.some (0 : ℚ) 0 exampleNsT :=
  exists_nsmul_eq_some_of_root_of_mem_torsion_two exampleNsT exampleTorT exampleNsP.left
    eval_Φ_two_exampleCurve (by norm_num)

/-- The transcendence hypothesis at `n = 2` over `ℚ`, **produced and not assumed** —
`transcendental_xCoord_nsmul_genericPoint_of_intCast_ne_zero`
(`EllipticCurves.FunctionField.MulByNXCoordFormula`) from `(2 : ℚ) ≠ 0` and `((2 : ℤ) : ℚ) ≠ 0`,
with no algebraic closure. -/
private theorem exampleTranscendentalTwo :
    Transcendental ℚ ((2 : ℕ) • genericPoint (W := y2EqX3Add5X2Add4X ℚ)).xCoord :=
  transcendental_xCoord_nsmul_genericPoint_of_intCast_ne_zero exampleTwo (by norm_num)

/-- **`exists_gS_n_of_card` at `n = 2` over `ℚ`, with no hypothesis whatsoever.**

⚠️ **This is a certificate for the general statement of this file and not for
`exists_gS_two_of_card`**: the endomorphism it names is `mulByNEndo 2 exampleTranscendentalTwo`,
the term the general headline produces, and the general headline is what is applied.  `hcard` is
`exampleCard` and the halving is `exampleExistsHalving`, both proved, over a field that is not
algebraically closed.

⚠️ It is **not** evidence for `#962`, which asks for the same conclusion on a curve whose
`2`-torsion is *not* rational.  What it certifies is that the hypotheses of `exists_gS_n_of_card`
are simultaneously satisfiable away from `F̄` — at `n = 2`, and, for the reason the section header
gives, at no index this board can currently reach. -/
private theorem exampleRungFiveGeneral :
    ∃ f : (y2EqX3Add5X2Add4X ℚ).FunctionField, f ≠ 0 ∧
      (y2EqX3Add5X2Add4X ℚ).divisor f
          = Finsupp.single (pointClosedPoint exampleNsT.left) ((2 : ℕ) : ℤ) ∧
        ∃ gS : (y2EqX3Add5X2Add4X ℚ).FunctionField, gS ≠ 0 ∧
          ∃ u : (y2EqX3Add5X2Add4X ℚ).CoordinateRingˣ,
            (u : (y2EqX3Add5X2Add4X ℚ).CoordinateRing) • gS ^ (2 : ℕ)
              = mulByNEndo 2 exampleTranscendentalTwo f :=
  let ⟨P, hP, _⟩ := exampleExistsHalving
  exists_gS_n_of_card exampleTwo (by norm_num) exampleTranscendentalTwo exampleCard exampleNsT
    exampleTorT (P := P) hP

end Nonvacuity

end WeierstrassCurve.Affine
