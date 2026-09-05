/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import EllipticCurves.Fixtures
import EllipticCurves.FunctionField.MulByNComposition
import EllipticCurves.FunctionField.MulByNXCoordFormula
import EllipticCurves.FunctionField.WeilPairingAlternatingWorkhorseN

/-!
# Consumers of the general-`n` alternating workhorse, and a non-trivial certificate at `n = 4`

`EllipticCurves.FunctionField.WeilPairingAlternatingWorkhorseN` proves the second product of
Silverman *AEC* III.8.1(b) at an arbitrary `n`:

```
translatePointEndo_eq_self_of_prod_eq_of_pow_eq :
  [n]P = T  →  ∏_{i<n} τ_{[i]T}∗ f = c  →  c₀ · gⁿ = [n]∗ f  →  τ_T∗ g = g
```

⚠️ **This file adds no mathematics.**  It is two corollaries of that theorem and one non-vacuity
certificate.  Nothing here re-proves, restates or edits anything in the merged file.

## Why the corollaries are worth declaring when the merged theorem is more general

The merged statement is indexed by `W.Point` and takes the relation `[n]P = T` there.  Every caller
on this front instead holds `W.Equation` data — a pair of affine coordinates and a proof that they
satisfy the equation — because that is what `translateEndo` is indexed by, and that is the shape of
both merged numeral workhorses (`translateEndo_eq_self_of_mul_algebraMap_{sq,cube}_eq`).  The
conversion is `translatePointEndo_torsionPoint` and `translatePointEndo_nsmul_apply` in both
directions, and it is a rewrite rather than an argument — but it is a rewrite every caller would
otherwise repeat.

⚠️ **And it is load-bearing for the certificate**, which is the second reason this file exists; see
the `Nonvacuity` section.

## The `htel` shape, chosen deliberately

`translateEndo_eq_self_of_mul_algebraMap_pow_eq` takes its telescope as
`∏ i ∈ Finset.range n, (translateEndo hT)^[i] f`, an **iterate**, where the merged theorem takes
`∏ i ∈ Finset.range n, translatePointEndo (i • T) f`.  The two are interconvertible by
`translatePointEndo_nsmul_apply` together with `translatePointEndo_torsionPoint`, factor by factor,
and that conversion is the whole proof below.

⚠️ The iterate form is chosen **for the certificate's sake**, not for elegance.  The alternative
`translateEndo (i • …)` does not typecheck at all: `translateEndo` is indexed by an affine point and
the interior multiples `[i]T` need not be affine — that is exactly why
`EllipticCurves.FunctionField.TranslationPointEndomorphism` exists.  So a `translateEndo`-indexed
telescope must be written with the index on the *endomorphism being iterated*, and it names one
affine point instead of `n` of them.

## Main statements

⚠️ **All three below take a point `P` on the curve, a point `T` on the curve with `[n]P = T`, the
telescope `htel` and the `n`-th-power identity `hpow`; the second and the third take `(2 : F) ≠ 0`
as well, and the second `(3 : F) ≠ 0`.**

⚠️ **Where a bullet says nothing about hypotheses, read it against this register; where a bullet
counts them, the count is that bullet's own claim and no register makes it true.**  Naming some
without counting is neither, and sits under this register unchanged; reporting one *discharged* is a
gate-discharge claim, which `README.md` `### Gate-discharge claims` governs.  That is the house form
`#1647` decided, in `EllipticCurves.FunctionField.WeilPairingAlternatingAssemblyN` (PR #658).

⚠️ **It replaces a universal that was false of this list on the day it landed.**  This register
formerly closed *"The bullets give the conclusions and not the hypotheses"* (`6f7fe82`, `#1626`,
PR #654), and both of the bullets that falsify it were already on the page at that commit: the
second names *"at every `3`-smooth `n ≠ 0`"* over `(hnz : n ≠ 0)` and
`(hfac : ∀ p ∈ n.primeFactors, p = 2 ∨ p = 3)`, and the third *"at every `n` with
`((n : ℤ) : F) ≠ 0`"* over `(hn : ((n : ℤ) : F) ≠ 0)` — explicit binders of the declarations those
bullets are about, not glosses.  ⚠️ **A bullet that NAMES a hypothesis falsifies that sentence**:
it says the bullets give the conclusions *and not the hypotheses*, so giving one is enough, and
**counting** them is the narrower, stronger failure the form above routes separately.  Reading the
form's *"naming some without counting is neither"* back into the sentence it replaced is the error
`README.md` `### Module-block bullets` now warns against by name — that branch is one this form
**adds**, and wanting it is why the old wording had to go.  Same test, same verdict and same repair
as in `…AssemblyN` and `…GaloisRootN` (`#1647`, `#1662`, `#1686`).

* `translateEndo_eq_self_of_mul_algebraMap_pow_eq` — the affine-indexed form of the workhorse;
* `translateEndo_eq_self_of_mul_algebraMap_pow_eq_of_smooth` — the same at every `3`-smooth `n ≠ 0`,
  with the transcendence hypothesis discharged;
* `translateEndo_eq_self_of_mul_algebraMap_pow_eq_of_ne_zero` — **the same at every `n` with
  `((n : ℤ) : F) ≠ 0`** (`#1549`), the transcendence coming from
  `transcendental_xCoord_nsmul_genericPoint_of_intCast_ne_zero`
  (`EllipticCurves.FunctionField.MulByNXCoordFormula`) rather than from the `3`-smooth degree tower.
  ⚠️ `n = 5` and `n = 10` are here, and the `_of_smooth` form is a corollary of it — the `example`
  beside them compiles that containment rather than asserting it.

Both are stated in `WeierstrassCurve.Affine`, beside the merged workhorse and the two merged
numeral workhorses they generalise, rather than in the `CoordinateRing` sub-namespace where the
bricks live.  That is `#918`'s rule.

## ⚠️ One sentence in the merged file is superseded by this one

`WeilPairingAlternatingWorkhorseN`'s `Nonvacuity` docstring says that a certificate binding `htel`
and `hpow` — rather than instantiating at `f = g = c = c₀ = 1` — *"does not terminate inside the
heartbeat budget"*, because every hypothesis would need its own `convert … using 9`.  **The
`convert`-per-hypothesis half is true of a certificate stated through the `W.Point`-indexed theorem
and the affine corollary below removes it**, and the reason is structural rather than a matter of
heartbeats:

> Stated through the affine corollary, `htel` mentions `translateEndo exampleEqT` and never
> `translatePointEndo (i • T)`.  `ℚ` has a genuine `DecidableEq` instance, and the corollary — under
> `open Classical in`, at an abstract `F` — carries `Classical.propDecidable`; the two are
> propositionally but not syntactically equal.  Through `translatePointEndo (i • T)` the mismatch
> appears inside **every factor** of the product, so every hypothesis needs its own `convert`.
> Through `translateEndo hT` the point-level `n • ·` occurs **once**, in `hmul`, and one
> `by convert exampleQuadruple` closes it.

⚠️ **The "does not terminate" half is not a difference between the two shapes**, and this file
originally implied it was.  Measured in `#1415`: through the `W.Point`-indexed theorem the
parameterised certificate does time out with no `convert` at all — at `maxHeartbeats 4000000`, not
merely the default — but `convert … using 12` closes it in about 3.8 s, and
`WeilPairingAlternatingWorkhorseN` now carries that certificate.  The difference between the two
shapes is **one `convert` against one per hypothesis**, not affordable against unaffordable.

## Scope

`[Field F] {W : Affine F} [W.IsElliptic]`.  No `[IsAlgClosed F]`, no `hprin`, no `ωₙ` (`#404`,
since closed), no Ward (`#260`, since closed), no `#251` (⚠️ since closed as well —
`hasXCoordFormula_of_two_ne_zero`, `EllipticCurves.Torsion.NsmulOrder`, with its `y`-half
`nsmul_eq_some_omegaY_of_ΨSq_ne_zero`, `EllipticCurves.Torsion.NsmulYPeriodic`, `#1500`).

Out of scope, and deliberately absent: the divisor telescope at general `n` (the *first* product of
III.8.1(b)), the alternating assembly, and a second `Recovery` block — the merged file's recoveries
of the `n = 2` and `n = 3` workhorses are verified elaborated-type-identical to their twins, and
recovering them again through these corollaries would certify nothing new.

## References

* [J. Silverman, *The arithmetic of elliptic curves*][silverman2009], III.8.1(b), second product.
-/

open Polynomial IsDedekindDomain

namespace WeierstrassCurve.Affine

open CoordinateRing

variable {F : Type*} [Field F] {W : Affine F} [W.IsElliptic]

/-! ### The affine-indexed form -/

open Classical in
/-- **The general-`n` alternating workhorse, indexed by affine points** — the direct analogue of the
merged `translateEndo_eq_self_of_mul_algebraMap_{sq,cube}_eq` at an arbitrary `n`.

`P` and `T` are affine, the relation between them is asked for at the **base-field** level
(`torsionPoint`, in `W.Point`) rather than at the `F(W)` level (`translatePoint`), and the telescope
is the `n`-fold iterate of the single affine translation `τ_T∗`.

⚠️ Only `T` needs to be affine for the *conclusion* to make sense; `P` is asked to be affine only
because a caller holds it that way.  The merged theorem needs neither, and no interior multiple
`[i]P` or `[i]T` is required to be affine here either — that is what
`EllipticCurves.FunctionField.TranslationPointEndomorphism` buys, and it is why the merged `n = 3`
statement's auxiliary point `Q` has no analogue in this list. -/
theorem translateEndo_eq_self_of_mul_algebraMap_pow_eq
    {n : ℕ} (hnz : n ≠ 0) (hn : Transcendental F (n • genericPoint (W := W)).xCoord)
    {xP yP xT yT : F} (hP : W.Equation xP yP) (hT : W.Equation xT yT)
    (hmul : n • torsionPoint hP = torsionPoint hT)
    {f g : W.FunctionField} (hg : g ≠ 0) {c c₀ : F} (hc : c ≠ 0) (hc₀ : c₀ ≠ 0)
    (htel : ∏ i ∈ Finset.range n, (translateEndo hT)^[i] f = algebraMap F W.FunctionField c)
    (hpow : algebraMap F W.FunctionField c₀ * g ^ n = mulByNEndo n hn f) :
    translateEndo hT g = g := by
  have key := translatePointEndo_eq_self_of_prod_eq_of_pow_eq hnz hn hmul hg hc hc₀
    (Eq.trans (Finset.prod_congr rfl fun i _ => by
      rw [translatePointEndo_nsmul_apply, translatePointEndo_torsionPoint]) htel) hpow
  rwa [translatePointEndo_torsionPoint] at key

open Classical in
/-- **The affine workhorse at every `3`-smooth `n ≠ 0`**, with the transcendence hypothesis
discharged by `transcendental_xCoord_nsmul_of_smooth`, and with the telescoping product `htel`, the
`n`-th-root relation `hpow` and their non-vanishing side conditions `hg`, `hc`, `hc₀` the only
hypotheses beyond the setting.

⚠️ **This statement** does not cover `n = 5` — the argument that supplies its transcendence
manufactures no new prime — but **the file does**: `…_of_ne_zero` below is the same conclusion at
every `n` with `((n : ℤ) : F) ≠ 0`, and this one is a corollary of it (`#1549`).  ⚠️ It is kept
because its transcendence comes by composing `[2]` and `[3]` and consumes no division polynomial: an
independent route, not dead weight. -/
theorem translateEndo_eq_self_of_mul_algebraMap_pow_eq_of_smooth
    (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) {n : ℕ} (hnz : n ≠ 0)
    (hfac : ∀ p ∈ n.primeFactors, p = 2 ∨ p = 3)
    {xP yP xT yT : F} (hP : W.Equation xP yP) (hT : W.Equation xT yT)
    (hmul : n • torsionPoint hP = torsionPoint hT)
    {f g : W.FunctionField} (hg : g ≠ 0) {c c₀ : F} (hc : c ≠ 0) (hc₀ : c₀ ≠ 0)
    (htel : ∏ i ∈ Finset.range n, (translateEndo hT)^[i] f = algebraMap F W.FunctionField c)
    (hpow : algebraMap F W.FunctionField c₀ * g ^ n
      = mulByNEndo n (transcendental_xCoord_nsmul_of_smooth h2 h3 hnz hfac) f) :
    translateEndo hT g = g :=
  translateEndo_eq_self_of_mul_algebraMap_pow_eq hnz _ hP hT hmul hg hc hc₀ htel hpow

open Classical in
/-- **The affine workhorse at every `n` with `((n : ℤ) : F) ≠ 0`**, with the transcendence
hypothesis discharged by `transcendental_xCoord_nsmul_genericPoint_of_intCast_ne_zero`
(`EllipticCurves.FunctionField.MulByNXCoordFormula`) instead of by the `3`-smooth ladder, and with
the telescoping product `htel`, the `n`-th-root relation `hpow` and their non-vanishing side
conditions `hg`, `hc`, `hc₀` the only hypotheses beyond the setting.

⚠️ **`n = 5` and `n = 10` are here and are not in `…_of_smooth`**, and the containment runs one way:
the `example` below derives the `3`-smooth statement from this one verbatim, so the relation between
the two layers is compiled rather than claimed.  The `_of_smooth` form is kept — its proof composes
`[2]∗` and `[3]∗` and consumes no division polynomial, so it is an independent route.

⚠️ **`hn` is a condition of this route, not a limit on the conclusion.**  At `n = char F` the map
`[n]` is inseparable but still non-constant, so `Transcendental F (n • 𝒫).xCoord` is **true** there;
what needs `(n : F) ≠ 0` is `natDegree_ΨSq`.  Over an algebraically closed field
`transcendental_xCoord_nsmul_of_isAlgClosed` discharges the same side condition at every `n ≠ 0`,
characteristic included.  `translateEndo_eq_self_of_mul_algebraMap_pow_eq` remains the statement to
cite when the transcendence proof is already in hand. -/
theorem translateEndo_eq_self_of_mul_algebraMap_pow_eq_of_ne_zero
    (h2 : (2 : F) ≠ 0) {n : ℕ} (hn : ((n : ℤ) : F) ≠ 0)
    {xP yP xT yT : F} (hP : W.Equation xP yP) (hT : W.Equation xT yT)
    (hmul : n • torsionPoint hP = torsionPoint hT)
    {f g : W.FunctionField} (hg : g ≠ 0) {c c₀ : F} (hc : c ≠ 0) (hc₀ : c₀ ≠ 0)
    (htel : ∏ i ∈ Finset.range n, (translateEndo hT)^[i] f = algebraMap F W.FunctionField c)
    (hpow : algebraMap F W.FunctionField c₀ * g ^ n
      = mulByNEndo n (transcendental_xCoord_nsmul_genericPoint_of_intCast_ne_zero h2 hn) f) :
    translateEndo hT g = g :=
  translateEndo_eq_self_of_mul_algebraMap_pow_eq (by rintro rfl; simp at hn) _ hP hT hmul hg hc hc₀
    htel hpow

open Classical in
/-- **`…_of_smooth` is a corollary of `…_of_ne_zero`** — its statement verbatim, proved from the
general layer.  ⚠️ The two `mulByNEndo` terms carry *different* transcendence proofs and match only
because `Transcendental` is a `Prop`; `EllipticCurves.FunctionField.MulByNDegreeGeneral` records
that trap at its own `:72-76`. -/
example (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) {n : ℕ} (hnz : n ≠ 0)
    (hfac : ∀ p ∈ n.primeFactors, p = 2 ∨ p = 3)
    {xP yP xT yT : F} (hP : W.Equation xP yP) (hT : W.Equation xT yT)
    (hmul : n • torsionPoint hP = torsionPoint hT)
    {f g : W.FunctionField} (hg : g ≠ 0) {c c₀ : F} (hc : c ≠ 0) (hc₀ : c₀ ≠ 0)
    (htel : ∏ i ∈ Finset.range n, (translateEndo hT)^[i] f = algebraMap F W.FunctionField c)
    (hpow : algebraMap F W.FunctionField c₀ * g ^ n
      = mulByNEndo n (transcendental_xCoord_nsmul_of_smooth h2 h3 hnz hfac) f) :
    translateEndo hT g = g :=
  translateEndo_eq_self_of_mul_algebraMap_pow_eq_of_ne_zero h2
    (Nat.intCast_ne_zero_of_smooth h2 h3 hnz hfac) hP hT hmul hg hc hc₀ htel hpow

/-! ### Non-vacuity at `n = 4`, with `htel` and `hpow` bound rather than instantiated

⚠️ `n = 4` is reached by no merged alternating statement: `WeilPairingAlternatingTwo` and
`…AlternatingThree` are the whole numeral family.

⚠️ **The curve is `y² = x³ + 1`, not this subtree's usual `y² = x³ − x`, and the reason is that the
usual one makes the certificate vacuous.**  On `y² = x³ − x` over `ℚ` every affine rational point is
`2`-torsion, so the only relation available at `n = 4` there would be `[4]T = T` with `T` affine,
which is **false** — and a certificate resting on a false hypothesis proves nothing (`#916`).  On
`y² = x³ + 1` the point `P = (2, 3)` has order `6`, so `T = [4]P = (0, −1)` is affine and distinct
from `P`, and `hmul` is **discharged here, not assumed**.

⚠️ **What is still hypothetical**, stated plainly: `htel`, `hpow`, `hg`, `hc` and `hc₀` — exactly
the five the merged `n = 2` and `n = 3` workhorses also assume, and no more.  Everything else (the
elliptic instance, `3`-smoothness at a composite index, both affine points, and the relation between
them) is inhabited by a named lemma below.

This is strictly stronger than the `f = g = c = c₀ = 1` certificate in
`WeilPairingAlternatingWorkhorseN`, whose conclusion `τ_T∗ 1 = 1` is trivially true and therefore
says nothing about the case the theorem is for.  It is **not** strong enough to claim a real
telescope at `n = 4`: nothing on this tree produces one at a general index yet, and that is the
divisor half of III.8.1(b). -/

namespace ConsumerNonvacuity

/-! The certificate curve `y² = x³ + 1` is the shared `EllipticCurves.Fixture.y2EqX3AddOne`, whose
single `[CharZero F]` instance also supplies `IsElliptic` here. -/

open EllipticCurves.Fixture

private lemma exampleTwo : (2 : ℚ) ≠ 0 := by norm_num

private lemma exampleThree : (3 : ℚ) ≠ 0 := by norm_num

/-- `4` is `3`-smooth.  ⚠️ Not `by decide`: the `Decidable` instance for the bounded quantifier over
`primeFactors` gets stuck (`#1213`).  This is `NthRootOfPullbackN`'s `primeFactors_four` idiom. -/
private lemma primeFactorsFour : ∀ p ∈ (4 : ℕ).primeFactors, p = 2 ∨ p = 3 := by
  intro p hp
  obtain ⟨hpp, hdvd, -⟩ := Nat.mem_primeFactors.mp hp
  rw [show (4 : ℕ) = 2 ^ 2 from rfl] at hdvd
  exact Or.inl ((Nat.prime_dvd_prime_iff_eq hpp Nat.prime_two).mp (hpp.dvd_of_dvd_pow hdvd))

/-- `P = (2, 3)`, a point of order `6`. -/
private lemma exampleEqP : (y2EqX3AddOne ℚ).Equation 2 3 := by
  norm_num [y2EqX3AddOne, WeierstrassCurve.Affine.equation_iff]

/-- `[2]P = (0, 1)`. -/
private lemma exampleEqQ : (y2EqX3AddOne ℚ).Equation 0 1 := by
  norm_num [y2EqX3AddOne, WeierstrassCurve.Affine.equation_iff]

/-- `T = [4]P = (0, −1)`, affine and distinct from `P`. -/
private lemma exampleEqT : (y2EqX3AddOne ℚ).Equation 0 (-1) := by
  norm_num [y2EqX3AddOne, WeierstrassCurve.Affine.equation_iff]

open Classical in
/-- `[2](2, 3) = (0, 1)`: the tangent at `(2, 3)` has slope `2`, so `x([2]P) = 4 − 4 = 0`. -/
private lemma exampleDoubleP :
    torsionPoint exampleEqP + torsionPoint exampleEqP = torsionPoint exampleEqQ := by
  have hy : (3 : ℚ) ≠ (y2EqX3AddOne ℚ).negY 2 3 := by
    norm_num [y2EqX3AddOne, WeierstrassCurve.Affine.negY]
  rw [torsionPoint, torsionPoint, Point.add_self_of_Y_ne hy, Point.some.injEq]
  refine ⟨?_, ?_⟩ <;>
    norm_num [y2EqX3AddOne, WeierstrassCurve.Affine.addX, WeierstrassCurve.Affine.addY,
      WeierstrassCurve.Affine.negAddY, WeierstrassCurve.Affine.negY,
      WeierstrassCurve.Affine.slope]

open Classical in
/-- `[2](0, 1) = (0, −1)`: the tangent at `(0, 1)` is horizontal, so `x` is unchanged and the
`y`-coordinate is negated. -/
private lemma exampleDoubleQ :
    torsionPoint exampleEqQ + torsionPoint exampleEqQ = torsionPoint exampleEqT := by
  have hy : (1 : ℚ) ≠ (y2EqX3AddOne ℚ).negY 0 1 := by
    norm_num [y2EqX3AddOne, WeierstrassCurve.Affine.negY]
  rw [torsionPoint, torsionPoint, Point.add_self_of_Y_ne hy, Point.some.injEq]
  refine ⟨?_, ?_⟩ <;>
    norm_num [y2EqX3AddOne, WeierstrassCurve.Affine.addX, WeierstrassCurve.Affine.addY,
      WeierstrassCurve.Affine.negAddY, WeierstrassCurve.Affine.negY,
      WeierstrassCurve.Affine.slope]

open Classical in
/-- **`[4]P = T` on the nose**, from `[4] = [2] ∘ [2]`.  This is the hypothesis the corollary takes,
and discharging it rather than assuming it is what makes this block a certificate. -/
private lemma exampleQuadruple :
    (4 : ℕ) • torsionPoint exampleEqP = torsionPoint exampleEqT := by
  rw [show (4 : ℕ) = 2 * 2 from rfl, mul_nsmul, two_nsmul (torsionPoint exampleEqP),
    exampleDoubleP, two_nsmul, exampleDoubleQ]

/-- `T = [4]P` is a **different** point from `P`, so the relation `hmul` is not the degenerate
`[4]P = P`; and `T ≠ O`, so `τ_T∗` is not the identity by definition. -/
private lemma examplePNeT : torsionPoint exampleEqP ≠ torsionPoint exampleEqT := by
  rw [torsionPoint, torsionPoint, ne_eq, Point.some.injEq]
  norm_num

open Classical in
/-- **The `3`-smooth affine workhorse applies at `n = 4`**, on a named curve over `ℚ`, at two
distinct named affine points whose relation `[4]P = T` is proved rather than assumed.  Only the
telescope, the `4`-th root and the three non-vanishing hypotheses remain hypothetical, exactly as at
the merged `n = 2` and `n = 3`.

⚠️ The single `by convert` is bookkeeping, not mathematics, and there is exactly **one** of them —
see the module docstring.  `ℚ` has a genuine `DecidableEq` instance, so `exampleQuadruple` is
indexed by `instDecidableEqRat`, while the corollary — stated for a general `F` under
`open Classical in` — is indexed by `Classical.propDecidable`.  The two are propositionally but not
syntactically equal, and `convert` closes the gap by `Subsingleton.elim`.  Depth `9` reaches
`Point.instAddCommGroup`'s own `DecidableEq` argument, since `n • x` goes through
`HSMul → SMul → NSMul → AddMonoid → SubNegMonoid → AddGroup → AddCommGroup`; this is the idiom of
`TranslationMulByNCommGeneral`'s own `Nonvacuity` block. -/
example
    {f g : (y2EqX3AddOne ℚ).FunctionField} (hg : g ≠ 0) {c c₀ : ℚ} (hc : c ≠ 0) (hc₀ : c₀ ≠ 0)
    (htel : ∏ i ∈ Finset.range 4, (translateEndo exampleEqT)^[i] f
      = algebraMap ℚ (y2EqX3AddOne ℚ).FunctionField c)
    (hpow : algebraMap ℚ (y2EqX3AddOne ℚ).FunctionField c₀ * g ^ 4
      = mulByNEndo 4 (transcendental_xCoord_nsmul_of_smooth exampleTwo exampleThree
          (by norm_num) primeFactorsFour) f) :
    translateEndo exampleEqT g = g :=
  translateEndo_eq_self_of_mul_algebraMap_pow_eq_of_smooth exampleTwo exampleThree
    (n := 4) (by norm_num) primeFactorsFour exampleEqP exampleEqT (by convert exampleQuadruple)
    hg hc hc₀ htel hpow

end ConsumerNonvacuity

end WeierstrassCurve.Affine
