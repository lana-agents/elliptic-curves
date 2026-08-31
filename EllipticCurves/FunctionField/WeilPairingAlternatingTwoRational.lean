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
rational full `2`-torsion.  `y² = x³ + 5x² + 4x = x(x+1)(x+4)` has both, and **each of the two
facts is one identity between explicit polynomials**:

* `Ψ₂Sq = 4X³ + 20X² + 16X = 4 · X · (X + 1) · (X + 4)` splits over `ℚ`, so
  `card_torsion_two_of_splits` (`EllipticCurves.Torsion.TwoTorsion`) gives `hcard`.  ⚠️ Splitting
  alone does not give the count `4` — the three roots must be *distinct*, and that is
  `Δ = 2304 ≠ 0`, i.e. `[W.IsElliptic]`, applied inside that lemma.
* `Φ₂ = X⁴ − b₄X² − 2b₆X − b₈ = X⁴ − 8X² + 16 = (X² − 4)²` vanishes at `x = 2`, while `x(T) = 0`
  makes the right-hand side `0 · Ψ₂Sq.eval 2` on the nose; the point `(2, 6)` sits above that root
  (`36 = 8 + 20 + 8`).  So `exists_nsmul_two_eq_some_of_root`
  (`EllipticCurves.Torsion.DoublingSurjective`) gives `hP`.

⚠️ **Why this route rather than exhibiting the four points and doubling `(2, 6)` by hand.**  Both
facts are true of `E(ℚ)` and both were once proved that way here — the lower bound by an injection
`Fin 4 → E[2]` and a sixteen-way `fin_cases`, the halving by unfolding
`addX`/`addY`/`negAddY`/`negY`/`slope`.  The route above is not merely shorter.  A `Splits` witness
and a root of `Φ₂ − x₀·Ψ₂Sq` are statements about **two explicit polynomials over the base field**,
so they are exactly the data that survives base change to a splitting field, which is the form
`#962`'s descent will need; an injection out of `Fin 4` and an application of the affine addition
formula are statements about `E(ℚ)` and transport to nothing.

⚠️ **The halving is now anonymous, and the diagonal is ruled out by a lemma rather than by the
witness.**  `exists_nsmul_two_eq_some_of_root` produces *some* `P` above the root, not the named
`(2, 6)`, so `examplePNeT` — which said that two *named* points are distinct — no longer certifies
that the pairing is not silently being run at `P = T`.  `ne_of_nsmul_two_eq_exampleT` replaces that
check with the general fact: `2 • T = 0` and `T ≠ 0`, so no halving of `T` can be `T`.  That holds
for **every** halving, which is strictly more than the old check gave, and it is why deleting the
old check would have been a regression the build cannot see.

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
the module docstring states.  ⚠️ The anonymous halving costs no fourth `convert`: `W.Point` is an
inductive type that does not mention the instance, so `(P := P)` unifies and only the `2 • P` needs
bridging. -/

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

/-- `P = (2, 6)`, the point above the root of `Φ₂ − x(T)·Ψ₂Sq`: `36 = 8 + 20 + 8`. -/
private lemma exampleNsP : exampleCurve.Nonsingular 2 6 :=
  exampleCurve.equation_iff_nonsingular.mp (by
    norm_num [exampleCurve, WeierstrassCurve.Affine.equation_iff])

private lemma exampleTorT : Point.some (0 : ℚ) 0 exampleNsT ∈ exampleCurve.torsion 2 :=
  (mem_torsion_two_some_iff exampleNsT).mpr (by norm_num [exampleCurve])

open Polynomial in
/-- The `2`-torsion cubic of the example curve, factored: `4X³ + 20X² + 16X = 4·X·(X+1)·(X+4)`. -/
private lemma Ψ₂Sq_exampleCurve :
    exampleCurve.Ψ₂Sq = C 4 * X * (X + C 1) * (X + C 4) := by
  simp only [WeierstrassCurve.Ψ₂Sq, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, exampleCurve]
  norm_num only
  simp only [map_ofNat, map_one, Polynomial.C_0]
  ring

open Polynomial in
/-- **The splitting hypothesis, discharged over `ℚ`** — a product of one constant and three monic
linear factors is a `Splits` witness on the nose. -/
private lemma splits_Ψ₂Sq_exampleCurve : exampleCurve.Ψ₂Sq.Splits := by
  rw [Ψ₂Sq_exampleCurve]
  exact (((Splits.C 4).mul Splits.X).mul (Splits.X_add_C 1)).mul (Splits.X_add_C 4)

/-- **`#E[2] = 4` over `ℚ` for this curve**, which is `hcard`.

⚠️ The whole content is the factorisation of one cubic.  The alternative — `card_torsion_two_le`
for `≤ 4` together with an explicit injection `Fin 4 → E[2]` for `≥ 4` — is what this block used to
do, and it costs three more `Nonsingular` obligations, three more `mem_torsion` obligations and a
sixteen-way `fin_cases`. -/
private lemma exampleCard : Nat.card (exampleCurve.torsion 2) = 4 :=
  card_torsion_two_of_splits exampleTwo splits_Ψ₂Sq_exampleCurve

/-- **The root that does the work**: `Φ₂(2) = 0 = x(T) · Ψ₂Sq(2)`, since `Φ₂ = (X² − 4)²` here.

⚠️ Routed through `Φ_two_eval` — `Φ₂(x) = x · Ψ₂Sq(x) − Ψ₃(x)`, giving `2 · 144 − 288 = 0` — rather
than by unfolding `W.Φ 2`, whose definition is a recursion. -/
private lemma eval_Φ_two_exampleCurve :
    (exampleCurve.Φ 2).eval 2 = (0 : ℚ) * exampleCurve.Ψ₂Sq.eval 2 := by
  rw [Φ_two_eval]
  simp only [WeierstrassCurve.Ψ₂Sq, WeierstrassCurve.Ψ₃, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈, exampleCurve]
  norm_num

/-- **`T = (0, 0)` is twice a rational point**, which is `hP`.

⚠️ Obtained from the root of `Φ₂ − x(T)·Ψ₂Sq` at `x = 2` and the point `(2, 6)` above it, not from
the affine addition formula: `exists_nsmul_two_eq_some_of_root` carries no hypothesis on `(2 : ℚ)`
and no algebraic closure, so the arithmetic here is the polynomial identity above and nothing
else. -/
private lemma exampleExistsHalving :
    ∃ P : exampleCurve.Point, 2 • P = Point.some (0 : ℚ) 0 exampleNsT :=
  exists_nsmul_two_eq_some_of_root exampleNsT exampleNsP.left eval_Φ_two_exampleCurve

/-- **`P ≠ T`**: the halving relates two *distinct* named affine points. -/
private lemma examplePNeT :
    Point.some (2 : ℚ) 6 exampleNsP ≠ Point.some (0 : ℚ) 0 exampleNsT := by
  rw [ne_eq, Point.some.injEq]
  norm_num

/-- **No halving of `T` is `T`** — the diagonal check, for the anonymous halving.

⚠️ Checked rather than implied: `[2]P = T` at `P = T` would only say that `T` is fixed by `[2]`, and
a certificate cannot claim to exercise the halving if it silently runs on the diagonal.  Since the
halving produced by `exampleExistsHalving` is anonymous, the check cannot be made on a witness, and
it does not need to be — `T` lies in `E[2]`, so `2 • T = 0`, and `2 • T = T` would force `T = 0`,
which it is not.  This is strictly stronger than checking one named point. -/
private lemma ne_of_nsmul_two_eq_exampleT {P : exampleCurve.Point}
    (hP : 2 • P = Point.some (0 : ℚ) 0 exampleNsT) :
    P ≠ Point.some (0 : ℚ) 0 exampleNsT := by
  rintro rfl
  have h0 : (Point.some (0 : ℚ) 0 exampleNsT : exampleCurve.Point) = 0 :=
    hP.symm.trans (mem_torsion_iff.mp exampleTorT)
  simp at h0

/-- **The alternating property of the Weil pairing at `n = 2` over `ℚ`, with no hypothesis
whatsoever.**

⚠️ Compare the merged statements at this index: `exists_weilPairingElt_self_eq_one_of_algClosed_two`
carries `hprin` (`#418`), and `exists_weilPairingElt_self_eq_one_of_isAlgClosed_two` discharges it
only over `F̄`.  This one is over `ℚ` and its hypothesis list is empty — `hcard` is `exampleCard`
and the halving is `exampleExistsHalving`, both proved.

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
  let ⟨P, hP⟩ := exampleExistsHalving
  exists_weilPairingElt_self_eq_one_of_card_two exampleTwo (by convert exampleCard) exampleNsT
    (by convert exampleTorT) (P := P) (by convert hP)

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
  let ⟨P, hP⟩ := exampleExistsHalving
  exists_weilPairingMu_self_eq_one_of_card_two exampleTwo (by convert exampleCard) exampleNsT
    (by convert exampleTorT) (P := P) (by convert hP) n

end Nonvacuity

end WeierstrassCurve.Affine
