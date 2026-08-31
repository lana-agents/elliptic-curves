/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import EllipticCurves.FunctionField.PullbackPrincipalityTwoRationalTorsion
import EllipticCurves.FunctionField.WeilPairingAlternatingAssemblyN
import EllipticCurves.FunctionField.WeilPairingAlternatingTwoAlgClosed

/-!
# `e_2(T, T) = 1` over an arbitrary field, with `hprin` discharged

`EllipticCurves.FunctionField.WeilPairingAlternatingAssemblyN` assembles `e_n(T, T) = 1` over an
arbitrary field with the `#418` datum `hprin` carried as a hypothesis, and
`EllipticCurves.FunctionField.PullbackPrincipalityTwoRationalTorsion` (`#1339`) proves that datum at
`n = 2` over an arbitrary field from two rationality facts.  This file joins them.

## The statement

`exists_weilPairingElt_self_eq_one_of_card_two` is the alternating property at `n = 2` with

* **no `hprin`** — it is discharged, not assumed;
* **no `[IsAlgClosed F]`** — the base field is arbitrary;
* **no `(3 : F) ≠ 0`, no `3`-smoothness and no `[CharZero F]`**;

and exactly two hypotheses beyond `(2 : F) ≠ 0`: that `E[2]` is `F`-rational
(`hcard : Nat.card (W.torsion 2) = 4`) and that the point being paired has an `F`-rational halving
point (`hP : 2 • P = T`).  Both are rationality statements about finitely many points, and the
`Nonvacuity` section proves both on a named curve over `ℚ`, so `exampleAlternatingTwo` below is the
alternating property with an **empty hypothesis list over a field that is not algebraically
closed**.

⚠️ The two hypotheses are **independent**: full rational `2`-torsion does not give a rational
halving point.  See the `Nonvacuity` docstring for the fixture that separates them.

## ⚠️ Why the route is through the *core* and not through `…_of_hprin_n_of_smooth`

The obvious consumer is `exists_weilPairingElt_self_eq_one_of_hprin_n_of_smooth`, which discharges
the transcendence for the caller.  It is the wrong one here: its transcendence comes from
`transcendental_xCoord_nsmul_of_smooth`, which takes `(3 : F) ≠ 0`, so every statement built on it
excludes characteristic `3` — at an index where nothing about the mathematics does.

The route taken instead is the core `exists_weilPairingElt_self_eq_one_of_hprin_n` with `hn`
supplied by `transcendental_xCoord_two_nsmul` (`EllipticCurves.FunctionField.MulByNPullback`), which
needs only `h2`.  That lemma is also the one `mulByNEndo_two` is stated at, so the numeral bridge

```
mulByNEndo_two h2 : mulByNEndo 2 (transcendental_xCoord_two_nsmul h2) = mulByTwoEndo h2
```

rewrites on the nose and `(3 : F) ≠ 0` never enters.  ⚠️ The bridge has to be pushed through
`hprin` **as well as** through the conclusion; the transcendence proofs unify on their own by proof
irrelevance and must not be matched by hand.  This is the idiom of
`WeilPairingAlternatingAssemblyN`'s own `Recovery` section, reused here for the same reason.

## What is discharged, and what `#962` still wants

`hprin` at `n = 2` was `#418`, the last standing gate on this front.  It is now discharged over any
field over which the two rationality facts hold.  ⚠️ **This does not close `#962`**, which asks for
`hprin` over a field where `E[2]` is *not* rational.  That still needs three things, none of them
touched here: a finite `L/F` over which both facts hold, the descent statement
`L(W⁄L)^{Gal(L/F)} = F(W)` (`#692`'s open divisor half), and separability of `L/F` in characteristic
`p`.  Mathlib's *finite* Hilbert 90 suffices for the cohomology; no profinite machinery is needed.

⚠️ Nothing here transfers to `n = 3`.  `PullbackPrincipalityThree` has never been audited for the
arbitrary-field reduction, and `#947` rules out full rational `3`-torsion over `ℚ` for *every*
elliptic curve, so even the certificate would need a different base field.

## The `DecidableEq` decision

Every statement below is elaborated `open Classical in` and **none** binds `[DecidableEq F]`.  That
is deliberate and it follows `WeilPairingAlternatingAssemblyN`'s rule: **the `[DecidableEq F]`
binder is right for a producer of a `torsion` fact, `open Classical in` for a consumer of a
`Classical`-fixed statement.**  This file consumes the `Classical`-fixed core, and binding the
instance would put an extra binder into the recovered statements — which is exactly the failure the
`Recovery` section exists to rule out.

⚠️ The price is paid in the `Nonvacuity` section, where `ℚ` carries `instDecidableEqRat` and wins on
priority whatever is open, so the three `torsion`-indexed inputs need a `convert` apiece.  Those
`convert`s are `Subsingleton.elim` bookkeeping, not mathematics, and writing `open Classical in`
on the `ℚ` lemmas would be a no-op that hid the reason.

## References

* [J. H. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.8, Prop. 8.1(d).
* `EllipticCurves.FunctionField.WeilPairingAlternatingAssemblyN` — the general-`n` core.
* `EllipticCurves.FunctionField.PullbackPrincipalityTwoRationalTorsion` — the `hprin` discharge.
* `EllipticCurves.FunctionField.WeilPairingAlternatingTwoAlgClosed` — the `F̄` statements recovered
  below.
-/

namespace WeierstrassCurve.Affine

open CoordinateRing

variable {F : Type*} [Field F] {W : Affine F}

section Rational

variable [W.IsElliptic] {x₂ y₂ : F}

open Classical in
/-- **`e_2(T, T) = 1` over an arbitrary field**, from a rational `E[2]` and a rational halving
point.

For a nonsingular affine `2`-torsion point `T = (x₂, y₂)` there are a nonzero `f_T` whose projective
divisor is `2(T) − 2(O)` and a nonzero `g_T` with `u · g_T ^ 2 = [2]∗ f_T` for a unit `u` of `F[W]`,
such that `τ_T∗` fixes `g_T` — hence `e_2(T, T) = 1`.

This is `exists_weilPairingElt_self_eq_one_of_isAlgClosed_two`
(`EllipticCurves.FunctionField.WeilPairingAlternatingTwoAlgClosed`) with `[IsAlgClosed F]` traded
for the two facts the closure was ever used for at this index, and the `Recovery` section below
derives that statement from this one.

⚠️ `hcard` and `hP` are **independent**: `y² = x³ − x` over `ℚ` satisfies `hcard` and fails `hP`.

⚠️ No `(3 : F) ≠ 0` — see the module docstring for why the transcendence must come from
`transcendental_xCoord_two_nsmul` rather than from the `3`-smooth corollary. -/
theorem exists_weilPairingElt_self_eq_one_of_card_two (h2 : (2 : F) ≠ 0)
    (hcard : Nat.card (W.torsion 2) = 4) (h : W.Nonsingular x₂ y₂)
    (htors : Point.some x₂ y₂ h ∈ W.torsion 2)
    {P : W.Point} (hP : 2 • P = Point.some x₂ y₂ h) :
    ∃ f : W.FunctionField, f ≠ 0 ∧
      divisorProj W f = Finsupp.single (some (pointClosedPoint h.left)) (2 : ℤ)
          - Finsupp.single (none : ProjPoint W) (2 : ℤ) ∧
        ∃ g : W.FunctionField, g ≠ 0 ∧
          (∃ u : W.CoordinateRingˣ, (u : W.CoordinateRing) • g ^ 2 = mulByTwoEndo h2 f) ∧
          translateEndo h.left g = g ∧ weilPairingElt h.left g = 1 := by
  have key := exists_weilPairingElt_self_eq_one_of_hprin_n (n := 2) (by norm_num)
    (transcendental_xCoord_two_nsmul h2) h htors hP
    (by
      simpa only [mulByNEndo_two h2, Nat.cast_ofNat] using fun f hf hfdiv =>
        exists_nsmul_divisor_eq_divisor_mulByTwoEndo_of_card h2 hcard h htors hP hf hfdiv)
  simpa only [mulByNEndo_two h2, Nat.cast_ofNat] using key

open Classical in
/-- **The alternating property at `n = 2` in the value group `μ_n(F)`, over an arbitrary field.**

The `μ`-valued twin of `exists_weilPairingElt_self_eq_one_of_card_two`.  `weilPairingMu` is indexed
by a proof `hpow` that the pairing element is an `n`-th root of unity, so the statement *produces*
one; that costs nothing, because the previous theorem already gives `e_2(T, T) = 1` and `1 ^ n = 1`.

⚠️ **The index `n` is arbitrary and has nothing to do with the `2`.**  This is the group identity of
`μ_n(F)` for whichever `n` the caller has packaged the value in — not a claim that `e_2` lands in
`μ_n`.  Both merged `μ`-valued statements at this index say the same of themselves, for the same
reason: the root-of-unity witness is manufactured from `1 ^ n = 1`.

⚠️ Routed through the `Elt` statement above rather than through
`exists_weilPairingMu_self_eq_one_of_hprin_n`, so the numeral bridge is crossed once instead of
twice.  The two routes give the same theorem; this one keeps the proof three lines. -/
theorem exists_weilPairingMu_self_eq_one_of_card_two (h2 : (2 : F) ≠ 0)
    (hcard : Nat.card (W.torsion 2) = 4) (h : W.Nonsingular x₂ y₂)
    (htors : Point.some x₂ y₂ h ∈ W.torsion 2)
    {P : W.Point} (hP : 2 • P = Point.some x₂ y₂ h) (n : ℕ) [NeZero n] :
    ∃ f : W.FunctionField, f ≠ 0 ∧
      divisorProj W f = Finsupp.single (some (pointClosedPoint h.left)) (2 : ℤ)
          - Finsupp.single (none : ProjPoint W) (2 : ℤ) ∧
        ∃ g : W.FunctionField, g ≠ 0 ∧
          (∃ u : W.CoordinateRingˣ, (u : W.CoordinateRing) • g ^ 2 = mulByTwoEndo h2 f) ∧
          ∃ hpow : weilPairingElt h.left g ^ n = 1, weilPairingMu h.left hpow = 1 := by
  obtain ⟨f, hf, hdivproj, g, hg, hu, htinv, halt⟩ :=
    exists_weilPairingElt_self_eq_one_of_card_two h2 hcard h htors hP
  exact ⟨f, hf, hdivproj, g, hg, hu, by rw [halt, one_pow],
    weilPairingMu_self_of_translateEndo_fixed h.left hg _ htinv⟩

end Rational

/-! ### Recovery of the algebraically closed statements

`#907`'s rule.  Over `F̄` both hypotheses are theorems — `card_torsion_two` and
`exists_nsmul_two_eq` — so the two merged headlines come straight back out.  Both are `private`: a
public copy would duplicate a merged name.

⚠️ Checked by the **elaborated-type** comparison (`pp.explicit`, `pp.universes`, `pp.deepTerms`)
inside a copy of this module, never by a source diff.  Three distinct binder traps are on record on
this board — a recovery one binder short, one binder too long, and one that is a *permutation* of
the same binders and therefore invisible to a character count.  The `variable` line below is copied
from `WeilPairingAlternatingTwoAlgClosed` in that file's order for exactly that reason.

⚠️ Note in particular that neither statement binds `[IsDedekindDomain W.CoordinateRing]`: it is
supplied by the instance for `[W.IsElliptic]`, and writing it would make both recoveries one binder
too long. -/

section Recovery

variable [W.IsElliptic] [IsAlgClosed F] {x₂ y₂ : F}

open Classical in
/-- `exists_weilPairingElt_self_eq_one_of_isAlgClosed_two`
(`EllipticCurves.FunctionField.WeilPairingAlternatingTwoAlgClosed`), recovered. -/
private theorem exists_weilPairingElt_self_eq_one_of_isAlgClosed_two_of_general (h2 : (2 : F) ≠ 0)
    (h : W.Nonsingular x₂ y₂) (htors : Point.some x₂ y₂ h ∈ W.torsion 2) :
    ∃ f : W.FunctionField, f ≠ 0 ∧
      divisorProj W f = Finsupp.single (some (pointClosedPoint h.left)) (2 : ℤ)
          - Finsupp.single (none : ProjPoint W) (2 : ℤ) ∧
        ∃ g : W.FunctionField, g ≠ 0 ∧
          (∃ u : W.CoordinateRingˣ, (u : W.CoordinateRing) • g ^ 2 = mulByTwoEndo h2 f) ∧
          translateEndo h.left g = g ∧ weilPairingElt h.left g = 1 :=
  let ⟨_, hP⟩ := exists_nsmul_two_eq h2 (Point.some x₂ y₂ h)
  exists_weilPairingElt_self_eq_one_of_card_two h2 (card_torsion_two h2) h htors hP

open Classical in
/-- `exists_weilPairingMu_self_eq_one_of_isAlgClosed_two`
(`EllipticCurves.FunctionField.WeilPairingAlternatingTwoAlgClosed`), recovered. -/
private theorem exists_weilPairingMu_self_eq_one_of_isAlgClosed_two_of_general (h2 : (2 : F) ≠ 0)
    (h : W.Nonsingular x₂ y₂) (htors : Point.some x₂ y₂ h ∈ W.torsion 2) (n : ℕ) [NeZero n] :
    ∃ f : W.FunctionField, f ≠ 0 ∧
      divisorProj W f = Finsupp.single (some (pointClosedPoint h.left)) (2 : ℤ)
          - Finsupp.single (none : ProjPoint W) (2 : ℤ) ∧
        ∃ g : W.FunctionField, g ≠ 0 ∧
          (∃ u : W.CoordinateRingˣ, (u : W.CoordinateRing) • g ^ 2 = mulByTwoEndo h2 f) ∧
          ∃ hpow : weilPairingElt h.left g ^ n = 1, weilPairingMu h.left hpow = 1 :=
  let ⟨_, hP⟩ := exists_nsmul_two_eq h2 (Point.some x₂ y₂ h)
  exists_weilPairingMu_self_eq_one_of_card_two h2 (card_torsion_two h2) h htors hP n

end Recovery

/-! ### Non-vacuity over `ℚ`

⚠️ The certificate **must** be over a field that is not algebraically closed, or it certifies the
merged `…_of_isAlgClosed_two` instead of anything here (`#916`).  Both hypotheses are proved, so
`exampleAlternatingTwo` has **no hypothesis at all**: it is the alternating property of the Weil
pairing at `n = 2`, on a named curve, over `ℚ`.

⚠️ **The curve is forced and the arithmetic is the content.**  `[2]P = T` with `T` of order `2`
forces `ord P = 4`, so the curve needs `E(ℚ)_tors ⊇ ℤ/2 × ℤ/4` — rational `4`-torsion *above*
rational full `2`-torsion.  `y² = x³ + 5x² + 4x = x(x+1)(x+4)` has both:

* `E[2] = {O, (0,0), (−1,0), (−4,0)}`, since the cubic splits over `ℚ` with distinct roots
  (`Δ = 2304 ≠ 0`), which is `hcard`;
* `T = (0,0)` is halved by `P = (2, 6)`: the tangent there has slope
  `(3·4 + 2·5·2 + 4)/(2·6) = 36/12 = 3`, so `x([2]P) = 9 − 5 − 4 = 0` and `y([2]P) = 3(2 − 0) − 6
  = 0`.

⚠️ **`y² = x³ − x` — this subtree's historical default — does not work here**, and the reason is the
one that has now defeated several separate pieces of work on this board.  It *does* have full
rational `2`-torsion, so it satisfies `hcard` perfectly, but `E(ℚ) = (ℤ/2)²`, so no rational point
halves anything and `hP` is unobtainable.  The same underlying fact has appeared as *"no two
distinct multiples"* (`#1325`), *"no point of order `3`"* (`#1328`), *"no point of order `4`"*
(`#1334`) and *"no rational halving"* (`#1339` and here).  **Change curve rather than weakening the
certificate.**  Useful recipe: for `y² = x(x − e₂)(x − e₃)` the point `(e₁, 0)` is `2`-divisible
over `ℚ` exactly when `e₁ − e₂` and `e₁ − e₃` are both rational squares, and then
`x(P) = e₁ + √((e₁ − e₂)(e₁ − e₃))`.

⚠️ **No `open Classical in` on any lemma of this block**, and that is not an oversight: `ℚ` carries
`instDecidableEqRat`, which wins on instance priority whatever is open, so writing it would be a
no-op.  It is also exactly why the final application needs three `convert`s — the theorems above are
elaborated `open Classical in`, so their `torsion`-indexed inputs carry `Classical.propDecidable`
while these lemmas carry `instDecidableEqRat`.  The two are propositionally but not syntactically
equal and `convert` closes the gap by `Subsingleton.elim`.  This is the consumer side of the rule
the module docstring states. -/

section Nonvacuity

/-- The curve `y² = x³ + 5x² + 4x = x(x+1)(x+4)` over `ℚ`, of discriminant `2304`. -/
private noncomputable def exampleCurve : Affine ℚ := ⟨0, 5, 0, 4, 0⟩

private instance : exampleCurve.IsElliptic := by
  rw [WeierstrassCurve.isElliptic_iff, isUnit_iff_ne_zero]
  norm_num [exampleCurve, WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈]

private lemma exampleTwo : (2 : ℚ) ≠ 0 := by norm_num

/-- `T = (0, 0)`, the `2`-torsion point cut out by `x = 0`; this is the point being paired. -/
private lemma exampleNsT : exampleCurve.Nonsingular 0 0 :=
  exampleCurve.equation_iff_nonsingular.mp (by
    norm_num [exampleCurve, WeierstrassCurve.Affine.equation_iff])

/-- `(−1, 0)`, the `2`-torsion point cut out by `x + 1 = 0`. -/
private lemma exampleNsR₁ : exampleCurve.Nonsingular (-1) 0 :=
  exampleCurve.equation_iff_nonsingular.mp (by
    norm_num [exampleCurve, WeierstrassCurve.Affine.equation_iff])

/-- `(−4, 0)`, the `2`-torsion point cut out by `x + 4 = 0`. -/
private lemma exampleNsR₂ : exampleCurve.Nonsingular (-4) 0 :=
  exampleCurve.equation_iff_nonsingular.mp (by
    norm_num [exampleCurve, WeierstrassCurve.Affine.equation_iff])

/-- `P = (2, 6)`, the halving point: `36 = 8 + 20 + 8`. -/
private lemma exampleNsP : exampleCurve.Nonsingular 2 6 :=
  exampleCurve.equation_iff_nonsingular.mp (by
    norm_num [exampleCurve, WeierstrassCurve.Affine.equation_iff])

private lemma exampleTorT : Point.some (0 : ℚ) 0 exampleNsT ∈ exampleCurve.torsion 2 :=
  (mem_torsion_two_some_iff exampleNsT).mpr (by norm_num [exampleCurve])

private lemma exampleTorR₁ : Point.some (-1 : ℚ) 0 exampleNsR₁ ∈ exampleCurve.torsion 2 :=
  (mem_torsion_two_some_iff exampleNsR₁).mpr (by norm_num [exampleCurve])

private lemma exampleTorR₂ : Point.some (-4 : ℚ) 0 exampleNsR₂ ∈ exampleCurve.torsion 2 :=
  (mem_torsion_two_some_iff exampleNsR₂).mpr (by norm_num [exampleCurve])

/-- The four rational `2`-torsion points, as a map out of `Fin 4`.  Named rather than inlined so
that its injectivity — which is the whole of the lower bound in `exampleCard` — is a statement of
its own. -/
private noncomputable def exampleTorsionFour : Fin 4 → exampleCurve.torsion 2 :=
  ![⟨0, zero_mem _⟩, ⟨Point.some (0 : ℚ) 0 exampleNsT, exampleTorT⟩,
    ⟨Point.some (-1 : ℚ) 0 exampleNsR₁, exampleTorR₁⟩,
    ⟨Point.some (-4 : ℚ) 0 exampleNsR₂, exampleTorR₂⟩]

private lemma exampleTorsionFour_injective : Function.Injective exampleTorsionFour := by
  intro i j hij
  fin_cases i <;> fin_cases j <;>
    simp_all [exampleTorsionFour, Subtype.ext_iff]

/-- **`#E[2] = 4` over `ℚ` for this curve**, which is `hcard`.  `card_torsion_two_le`
(`EllipticCurves.Torsion.TwoTorsion`) is unconditional and supplies `≤`; `≥` is the four points
above.  ⚠️ The upper bound is where an algebraic closure would have been useless anyway — what the
closure buys in `card_torsion_two` is exactly this lower bound, and here it is bought by naming the
roots instead. -/
private lemma exampleCard : Nat.card (exampleCurve.torsion 2) = 4 := by
  haveI := exampleCurve.finite_torsion_two exampleTwo
  refine le_antisymm (card_torsion_two_le exampleTwo) ?_
  simpa using Nat.card_le_card_of_injective exampleTorsionFour exampleTorsionFour_injective

/-- **`P + P = T`**: the tangent at `(2, 6)` has slope `3`, so `x([2]P) = 9 − 5 − 4 = 0`. -/
private lemma exampleDoubleP :
    Point.some (2 : ℚ) 6 exampleNsP + Point.some (2 : ℚ) 6 exampleNsP
      = Point.some (0 : ℚ) 0 exampleNsT := by
  have hy : (6 : ℚ) ≠ exampleCurve.negY 2 6 := by
    norm_num [exampleCurve, WeierstrassCurve.Affine.negY]
  rw [Point.add_self_of_Y_ne hy, Point.some.injEq]
  refine ⟨?_, ?_⟩ <;>
    norm_num [exampleCurve, WeierstrassCurve.Affine.addX, WeierstrassCurve.Affine.addY,
      WeierstrassCurve.Affine.negAddY, WeierstrassCurve.Affine.negY,
      WeierstrassCurve.Affine.slope]

/-- **`[2]P = T`** in `nsmul` form, which is the shape the headline takes. -/
private lemma exampleTwoP :
    ((2 : ℕ) • Point.some (2 : ℚ) 6 exampleNsP : exampleCurve.Point)
      = Point.some (0 : ℚ) 0 exampleNsT := by
  rw [two_nsmul]; exact exampleDoubleP

/-- **`P ≠ T`**: the halving relates two *distinct* named affine points.  ⚠️ Checked rather than
implied — `[2]P = T` at `P = T` would only say that `T` is fixed by `[2]`, and a certificate cannot
claim to exercise the halving if it silently runs on the diagonal. -/
private lemma examplePNeT :
    Point.some (2 : ℚ) 6 exampleNsP ≠ Point.some (0 : ℚ) 0 exampleNsT := by
  rw [ne_eq, Point.some.injEq]
  norm_num

/-- **The alternating property of the Weil pairing at `n = 2` over `ℚ`, with no hypothesis
whatsoever.**

⚠️ Compare the merged statements at this index: `exists_weilPairingElt_self_eq_one_of_algClosed_two`
carries `hprin` (`#418`), and `exists_weilPairingElt_self_eq_one_of_isAlgClosed_two` discharges it
only over `F̄`.  This one is over `ℚ` and its hypothesis list is empty — `hcard` is `exampleCard`
and the halving is `exampleTwoP`, both proved.

⚠️ It is **not** evidence for `#962`, which asks for the same conclusion on a curve whose
`2`-torsion is *not* rational.  What it certifies is that the hypotheses of
`exists_weilPairingElt_self_eq_one_of_card_two` are simultaneously satisfiable away from `F̄`. -/
private theorem exampleAlternatingTwo :
    ∃ f : exampleCurve.FunctionField, f ≠ 0 ∧
      divisorProj exampleCurve f
          = Finsupp.single (some (pointClosedPoint exampleNsT.left)) (2 : ℤ)
            - Finsupp.single (none : ProjPoint exampleCurve) (2 : ℤ) ∧
        ∃ g : exampleCurve.FunctionField, g ≠ 0 ∧
          (∃ u : exampleCurve.CoordinateRingˣ,
            (u : exampleCurve.CoordinateRing) • g ^ 2 = mulByTwoEndo exampleTwo f) ∧
          translateEndo exampleNsT.left g = g ∧ weilPairingElt exampleNsT.left g = 1 :=
  -- ⚠️ The three `convert`s are the entire price of the consumed theorem being elaborated
  -- `open Classical in`; see the section docstring.  They are `Subsingleton.elim` bookkeeping.
  exists_weilPairingElt_self_eq_one_of_card_two exampleTwo (by convert exampleCard) exampleNsT
    (by convert exampleTorT) (P := Point.some (2 : ℚ) 6 exampleNsP) (by convert exampleTwoP)

/-- **The `μ_n(ℚ)`-valued form over `ℚ`, also with no hypothesis.**  The same instantiation of
`exists_weilPairingMu_self_eq_one_of_card_two`. -/
private theorem exampleAlternatingMuTwo (n : ℕ) [NeZero n] :
    ∃ f : exampleCurve.FunctionField, f ≠ 0 ∧
      divisorProj exampleCurve f
          = Finsupp.single (some (pointClosedPoint exampleNsT.left)) (2 : ℤ)
            - Finsupp.single (none : ProjPoint exampleCurve) (2 : ℤ) ∧
        ∃ g : exampleCurve.FunctionField, g ≠ 0 ∧
          (∃ u : exampleCurve.CoordinateRingˣ,
            (u : exampleCurve.CoordinateRing) • g ^ 2 = mulByTwoEndo exampleTwo f) ∧
          ∃ hpow : weilPairingElt exampleNsT.left g ^ n = 1,
            weilPairingMu exampleNsT.left hpow = 1 :=
  exists_weilPairingMu_self_eq_one_of_card_two exampleTwo (by convert exampleCard) exampleNsT
    (by convert exampleTorT) (P := Point.some (2 : ℚ) 6 exampleNsP) (by convert exampleTwoP) n

end Nonvacuity

end WeierstrassCurve.Affine
