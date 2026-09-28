/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import EllipticCurves.FunctionField.DivisorBaseChangeRationalPoint
import EllipticCurves.FunctionField.DivisorGaloisDescentNsmul
import EllipticCurves.FunctionField.PullbackPrincipalityThreeRationalTorsion
import EllipticCurves.Torsion.TriplingGaloisTower

/-!
# `[3]∗((S) − (O))` is three times a principal divisor over an ARBITRARY field

`EllipticCurves.FunctionField.PullbackPrincipalityThree` discharges `hprin` at `n = 3` over an
algebraically closed base; `EllipticCurves.FunctionField.PullbackPrincipalityThreeRationalTorsion`
replaces the closure by two rationality hypotheses, `hcard : Nat.card (W.torsion 3) = 9` and
`hP : 3 • P = S`.  **This file discharges it with neither**: over any field `F` with `(2 : F) ≠ 0`
and `(3 : F) ≠ 0`, for any nonsingular `F`-rational `3`-torsion point `S`.  It is the `n = 3`
analogue of `EllipticCurves.FunctionField.PullbackPrincipalityTwoGeneral`, and this is `#2216`'s
item 4.

⚠️ **`(2 : F) ≠ 0` and `(3 : F) ≠ 0` stay, and neither is a rationality fact.**  They are the
binders `mulByThreeEndo h2 h3` takes, and `mulByThreeEndo h2 h3 f` occurs in the headline's own
*statement*, so no proof change can drop them.  ⚠️ **`S` rational stays too**, and it is not a
hypothesis that could be dropped either: it is what the statement is *about* —
`pointClosedPoint h.left` is the closed point cut out by `(x, y)`.

## The route: build the field where both hypotheses become true, then descend

Neither hypothesis is proved.  Both are **bought over an extension and paid back by Galois
descent**:

1. `N := W.triplingGaloisField x` — the Galois closure over `F` of the tower
   `F ⊆ F(E[3]) ⊆ F(E[3])(a tripling of S)`.  It is finite Galois over `F`, `#E[3] = 9` over it and
   `S` is three times a point of `E(N)`: `EllipticCurves.Torsion.TriplingGaloisTower`, whose three
   statements are exactly the two hypotheses of `…_of_card` plus the Galois property this file's
   descent needs.
2. `divisor_functionFieldMap_eq_single`
   (`EllipticCurves.FunctionField.DivisorBaseChangeRationalPoint`) carries `div f = 3·(S)` up to `N`
   **on the nose**, because the fibre over the closed point of a *rational* point is a singleton
   with `e = 1` there.
3. `…_of_card` over `N` gives a `g` with `3 · div g = div ([3]∗ f)` upstairs.
4. `exists_nsmul_divisor_eq_of_functionFieldMap`
   (`EllipticCurves.FunctionField.DivisorGaloisDescentNsmul`) brings the identity back down to `F`,
   by Hilbert 90 at the finite level.  ⚠️ The function it returns is **not** the descent of `g`.

⚠️ **The `F̄` route is closed and this is not a matter of taste**: Mathlib's Hilbert 90 is
`[FiniteDimensional]`-only, so `H¹(Gal(F̄/F), F̄ˣ) = 0` is not available at the pin.  The finite
tower is the route, not a convenience.

## ⚠️ The two steps that do NOT transpose from `n = 2`, and one warning that cost nothing

**1. ⚠️ The descent is stated over an ABSTRACT finite Galois `N` here, and at `n = 2` it is not —
and the reason is a measurement rather than a preference.**
`exists_nsmul_divisor_eq_divisor_mulByThreeEndo_of_galois` takes `N` as a variable with
`[FiniteDimensional F N] [IsGalois F N]` and the two facts as hypotheses; the headline instantiates
it at `W.triplingGaloisField x`.  ⚠️ **Transcribing the `n = 2` proof instead — the tower inlined,
`set N := W.triplingGaloisField x`, everything else identical — exceeds the DEFAULT heartbeat
limit**: a control run of exactly that proof fails with
`(deterministic) timeout at 'whnf', maximum number of heartbeats (200000) has been reached`
and needs `set_option maxHeartbeats 400000`.  The cause is depth, not a
loop: `halvingGaloisField` is a three-layer tower of splitting fields and `triplingGaloisField` is a
**five**-layer one (`TriplingGaloisTower`'s own module docstring counts them), so unfolding the
`abbrev` chain inside unification is that much more expensive.  ⚠️ **Abstracting the field out of
the proof removes the bump entirely** — this file carries no `set_option` — and it is better
mathematics besides: the descent step never looks at how `N` was built.

**2. ⚠️ `3`-torsion crosses the base change with NO point-level bridge, and at `n = 2` a `Point`
statement is used.**  `hS'` is proved by `mem_torsion_three_some_iff'` and
`WeierstrassCurve.map_Ψ₃` — membership is re-derived from `Ψ₃.eval x = 0`, which base-changes as a
`Polynomial.eval` — where the `n = 2` file transports `mem_torsion_two_some_iff` through a
`congrArg` on the coordinates.  This is the same *"transport a `Prop`, not a term"* move
`TriplingGaloisTower` makes for its two root equations.

**3. ⚠️ `#2216`'s context note warned that two `n = 2`-specific divisor-descent lemmas carry a
hard-coded multiplicity of `2` and would have to be generalised.  Both are already general, and
this round paid nothing for them.**  The two this file consumes are
`divisor_functionFieldMap_eq_single`, whose coefficient is `{n : ℤ}` and whose own docstring says
*"nothing in the proof looks at it"*, and `exists_nsmul_divisor_eq_of_functionFieldMap`, which takes
`{n : ℕ} (hn : n ≠ 0)`.  ⚠️ **I name the two I consumed rather than asserting which two the note
meant**; if it meant others, they are not on this route.

## Main statements

Reach clauses below are complete, per `README.md` `## Docstring conventions` option (a).

* `WeierstrassCurve.Affine.exists_nsmul_divisor_eq_divisor_mulByThreeEndo_of_galois` — the descent
  step, over an arbitrary field with `(2 : F) ≠ 0` and `(3 : F) ≠ 0` and an arbitrary finite Galois
  extension `N` of it carrying `#E[3] = 9` and a tripling of `S`.  ⚠️ **It is the only one of the
  three that binds no `[DecidableEq F]`** — it binds `[W.IsElliptic]`, which all three do — and it
  is where the whole proof lives.
* `WeierstrassCurve.Affine.exists_nsmul_divisor_eq_divisor_mulByThreeEndo_general` — `hprin` at
  `n = 3` over an arbitrary field with `(2 : F) ≠ 0` and `(3 : F) ≠ 0`, at a nonsingular
  `F`-rational `3`-torsion point `S`, for a nonzero `f` whose divisor is `3·(S)`: the `#418` /
  `#962` gate at this index, with **no** rationality hypothesis left.
* `WeierstrassCurve.Affine.exists_gS_three_general` — rung 5 of the Weil pairing at `n = 3` over an
  arbitrary field with `(2 : F) ≠ 0` and `(3 : F) ≠ 0`, at a nonsingular `F`-rational `3`-torsion
  point `S`, with **no** gated hypothesis left; it produces the `f` itself.

⚠️ **The census, with the construction beside it.**  Under the rule *non-`private`, not
`Name.isInternal`*, `Environment.const2ModIdx` returns **11** constants for this module: **3**
public (the three above, all `theorem`), **8** `private`, **0** internal and **0**
compiler-generated.
`#print axioms` over all **11** reaches **0** `sorryAx` and every one of the 11 returns exactly
`{propext, Classical.choice, Quot.sound}`.  **Four direct imports** and a transitive
`EllipticCurves` closure of **153** modules with this one excluded, ⚠️ **measured at `bebec3f` plus
this round** as `README.md` `## Import-closure figures` requires of a closure *count*; the `n = 2`
mirror `PullbackPrincipalityTwoGeneral` is **112** at the same head, and the difference is **43** in
and **2** out — the `n = 3` divisor layer for the 43, and the halving tower for the 2.

## ⚠️ The name clash, said rather than left to be discovered

`exists_nsmul_divisor_eq_divisor_mulByThreeEndo` is **taken** — it is the `[IsAlgClosed F]` headline
of `PullbackPrincipalityThree` — and `…_of_card` is taken by the rational-torsion file.  The general
statement therefore lands as `…_general`, the tree's word for *over a general base*
(`PullbackPrincipalityTwoGeneral`, `MulByNDegreeGeneral`, `PlaceInertiaGeneral`).  ⚠️ **Neither of
the two older headlines is retired or moved here**: both are still true and both are still the right
thing for a consumer that already has a closure or the two rationality facts.

## ⚠️ What is *not* here

* **No `n` other than `3`.**  `EllipticCurves.Torsion.TriplingGaloisTower` is `n = 3` in every
  statement — its counting floor is `threeDivisionField` — so nothing below reaches a general index,
  and `#962`'s ledger row at an arbitrary `n` is untouched.
* **No characteristic-`2` or characteristic-`3` statement.**  Both `(2 : F) ≠ 0` and `(3 : F) ≠ 0`
  are assumed throughout.
* **Nothing about a non-rational `S`.**  Every statement below is at an affine point of `W(F)`.
* **No count of `E[3]` over `F` is claimed**, and in particular `hcard` is *not* proved to fail
  below; see `## Non-vacuity`.
* **No degree and no Galois group.**  `[N : F]` is not computed, `Gal(N/F)` is not identified, and
  nothing below says `F ⊊ N`.
* **Rung 6 is not here.**  The translation slot and non-degeneracy consume `hprin` and are not
  restated; what this file does for them is remove their gate at `n = 3`.
* ⚠️ **`#962` is not closed by this file.**  `#962`'s two rungs at `n = 2` and `n = 3` are now both
  discharged over a general base, but its ledger has rows beyond them and this file audits none.

## Non-vacuity over `ℚ`

`#916`'s rule.  ⚠️ **ONE curve suffices at `n = 3`, where `n = 2` needed two**, and ⚠️ **BOTH halves
of the certificate are now theorems** — see the retirement at the end of this section for what this
passage used to say and why it was a claim about one route and not about the tree.

`EllipticCurves.Fixture.y2AddYEqX3` at `ℚ`, the point `(0, 0)`:

* **`hP` fails, and that half is a theorem below.**  `Ψ₃ = 3X⁴ + 3X` vanishes at `0`, so `(0, 0)`
  is a rational `3`-torsion point; `triplingX 0 = Φ₃ = X⁹ − 24X⁶ + 3X³ + 1` here and it has **no
  rational root** (monic over `ℤ`, so `IsIntegrallyClosed.isIntegral_iff` puts any rational root in
  `ℤ`, where it divides the constant coefficient `1`, and `±1` give `−19` and `−27`).  With
  `exists_root_triplingX_of_nsmul_three_eq` (`EllipticCurves.Torsion.TriplingGaloisTower`) that
  gives `not_exists_nsmul_three_eq_zero_y2AddYEqX3`: **no rational point of `y² + y = x³` triples to
  `(0, 0)`**, so `…_of_card` cannot certify this instance.
* **`hcard` fails too, and that half is a THEOREM below as well.**  `Ψ₃ = 3X⁴ + 3X` factors here as
  `3X(X + 1)(X² − X + 1)`, and `X² − X + 1` has no rational root, so `Ψ₃` has exactly **two**
  rational roots, `0` and `−1` (`setOf_root_Ψ₃_y2AddYEqX3`).  The counting engine of
  `EllipticCurves.Torsion.Finite` puts at most two points above each and `O` beside them, so
  `#E[3] ≤ 2 · 2 + 1 = 5` (`card_torsion_three_le_five_y2AddYEqX3`) — against
  `card_torsion_three_le`'s `2 · 4 + 1 = 9` — whence
  `not_card_torsion_three_eq_nine_y2AddYEqX3`: **`#E[3] ≠ 9` on this curve**, so `…_of_card` cannot
  certify this instance on **either** of its two hypotheses.
* ⚠️ **THE ROUTE IS NOT THE ARGUMENT THIS PASSAGE USED TO CITE, AND THAT IS THE WHOLE POINT.**
  `PullbackPrincipalityThreeRationalTorsion`'s *"There is NO non-vacuity certificate for `hcard`
  here"* section argues that `hcard` forces `μ₃ ⊆ F` and `μ₃ ⊄ ℚ`, citing Silverman III.8.1 rather
  than this tree because this tree's `n = 3` Weil-pairing non-degeneracy carries `[IsAlgClosed F]`.
  ⚠️ **That argument is about EVERY curve over `ℚ` at once, and a certificate needs the hypothesis
  to fail AT THE FIXTURE** — which is strictly less, and which a root count reaches.  The `μ₃`
  argument is still uncited to this tree and still unformalised, and nothing here changes that.

⚠️ **So the single fixture below refutes `hP` and `hcard` OUTRIGHT, both as theorems** — which is
why one curve does here what took two at `n = 2`, where `#2029` records that no fixture in the tree
fails both hypotheses at once.  ⚠️ **`ℚ` is not algebraically closed, so the fixture certifies
neither older headline either.**

⚠️ **Retired, and the retirement is the useful half.**  This passage read *"only half of the
certificate is formalisable"* and, of `hcard`, *"that half is PROSE and not a theorem"*, *"This tree
has no route from that argument to a Lean statement"* and *"this file adds no route"*, from the
commit that created this file (`#2216` item 4, PR #824) until this one.  ⚠️ **Every clause of it was
true of the `μ₃` ARGUMENT and false as a claim about the TREE'S REACH**: what was missing was not a
route to a Lean statement but the observation that a *certificate* is a statement about one curve.
⚠️ **The class is an absence published as a property of the tree when it is a property of the route
its author had in mind** — and it is the more expensive direction, because the same file's `hP` half
is proved by exactly this shape of argument, counting the rational roots of a polynomial, one
paragraph above.

⚠️ **Seven of the eight `private` declarations below are local copies**, and the eighth is the
inhabitation of this file's own headline.  `EllipticCurves.Torsion.TriplingGaloisTower`'s
`Nonvacuity` section proves the same nonsingularity, the same tripling-polynomial evaluation, the
same no-rational-root fact and the same refutation of `hP`, and
`EllipticCurves.Torsion.TriplingSeparable`'s proves the same equation, the same `Ψ₃(0) = 0` and the
same `3`-torsion membership — **all seven `private` there**.  Promoting any of them would re-key a
published census in a file this round edits only for prose — `TriplingGaloisTower` publishes **42**
written declarations over **71** constants with **12** `private` — so they are restated here
instead, which is what `PullbackPrincipalityTwoGeneral` does with its own fixture arithmetic.

## References

* [Silverman, *The arithmetic of elliptic curves*][silverman2009], III.8 (the Weil pairing) and
  VIII.2 (Hilbert 90).
-/

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum

namespace WeierstrassCurve.Affine

open CoordinateRing

variable {F : Type*} [Field F] {W : Affine F} [DecidableEq F] [W.IsElliptic]

omit [DecidableEq F] in
/-- **The descent step**, over an arbitrary field `F` with `(2 : F) ≠ 0` and `(3 : F) ≠ 0` and an
arbitrary finite Galois extension `N / F` over which `#E[3] = 9` and `S` is three times a point: for
a nonsingular `F`-rational point `S = (x, y)` with `Ψ₃.eval x = 0` and a nonzero `f` with
`div f = 3·(S)`, the pullback `[3]∗ f` is three times a principal divisor **over `F`**.

Steps 2, 3 and 4 of the route in the module docstring; `N` is a variable here and the headline below
instantiates it at `W.triplingGaloisField x`.

⚠️ **`[DecidableEq F]` is NOT bound** — the decidability the `torsion` subgroup needs upstairs is
`[DecidableEq N]` and the rest is supplied by `classical` inside, so the `variable` line's instance
is `omit`ted.  ⚠️ **`[W.IsElliptic]` IS bound**, and it is read off the elaborated type rather than
off the `variable` line: `(W⁄N).IsElliptic`, which `…_of_card` over `N` wants, is synthesised from
it.

⚠️ **The `g₀` this returns is not the base change of the `g` obtained over `N`**, and is not claimed
to be: only its divisor identity descends. -/
theorem exists_nsmul_divisor_eq_divisor_mulByThreeEndo_of_galois (N : Type*) [Field N]
    [Algebra F N] [FiniteDimensional F N] [IsGalois F N] [DecidableEq N]
    (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) {x y : F}
    (h : W.Nonsingular x y) (hcard : Nat.card ((W⁄N).torsion 3) = 9)
    (hP : ∃ P : (W⁄N).Point, (3 : ℕ) • P
      = Point.some (algebraMap F N x) (algebraMap F N y)
        ((W.map_nonsingular (algebraMap F N).injective x y).mpr h))
    (hx : W.Ψ₃.eval x = 0)
    {f : W.FunctionField} (hf : f ≠ 0)
    (hfdiv : divisor W f = Finsupp.single (pointClosedPoint h.left) (3 : ℤ)) :
    ∃ g₀ : W.FunctionField, g₀ ≠ 0 ∧
      3 • divisor W g₀ = divisor W (mulByThreeEndo h2 h3 f) := by
  classical
  have h2' : (2 : N) ≠ 0 := algebraMap_ofNat_ne_zero h2
  have h3' : (3 : N) ≠ 0 := algebraMap_ofNat_ne_zero h3
  have h' : (W⁄N).Nonsingular (algebraMap F N x) (algebraMap F N y) :=
    (W.map_nonsingular (algebraMap F N).injective x y).mpr h
  have hS' : Point.some (algebraMap F N x) (algebraMap F N y) h' ∈ (W⁄N).torsion 3 := by
    rw [mem_torsion_three_some_iff', show (W⁄N) = W.map (algebraMap F N) from rfl,
      WeierstrassCurve.map_Ψ₃, Polynomial.eval_map_apply, hx, map_zero]
  obtain ⟨P, hPeq⟩ := hP
  have hf' : functionFieldMap W N f ≠ 0 :=
    (map_ne_zero_iff _ (functionFieldMap_injective W N)).mpr hf
  have hfdiv' : divisor (W⁄N) (functionFieldMap W N f)
      = Finsupp.single (pointClosedPoint h'.left) (3 : ℤ) :=
    divisor_functionFieldMap_eq_single N h.left hf hfdiv
  obtain ⟨g, hg, hgdiv⟩ :=
    exists_nsmul_divisor_eq_divisor_mulByThreeEndo_of_card h2' h3' hcard h' hS' hPeq hf' hfdiv'
  have hz : mulByThreeEndo h2 h3 f ≠ 0 :=
    (map_ne_zero_iff _ (mulByThreeEndo h2 h3).injective).mpr hf
  refine exists_nsmul_divisor_eq_of_functionFieldMap N (by norm_num) hz hg ?_
  rw [hgdiv, functionFieldMap_mulByThreeEndo h2 h3 h2' h3' f]
  rfl

/-- **`hprin` at `n = 3` over an arbitrary field with `(2 : F) ≠ 0` and `(3 : F) ≠ 0`**, in the
shape `exists_gS_three` consumes it: for a nonsingular `F`-rational `3`-torsion point `S = (x, y)`
and a nonzero `f` with `div f = 3·(S)`, the pullback `[3]∗ f` is three times a principal divisor.

⚠️ **No hypothesis on `F` beyond `(2 : F) ≠ 0` and `(3 : F) ≠ 0`**: no algebraic closure, no
`hcard`, no tripling `hP`.  Both of `…_of_card`'s rationality hypotheses are bought over
`W.triplingGaloisField x`, a finite Galois extension of `F`
(`EllipticCurves.Torsion.TriplingGaloisTower`), and paid back by Hilbert 90 through the abstract
descent step above.

⚠️ **`n = 3` only** — see the module docstring; the tower's counting floor is an `n = 3` object. -/
theorem exists_nsmul_divisor_eq_divisor_mulByThreeEndo_general (h2 : (2 : F) ≠ 0)
    (h3 : (3 : F) ≠ 0) {x y : F}
    (h : W.Nonsingular x y) (hS : Point.some x y h ∈ W.torsion 3)
    {f : W.FunctionField} (hf : f ≠ 0)
    (hfdiv : divisor W f = Finsupp.single (pointClosedPoint h.left) (3 : ℤ)) :
    ∃ g₀ : W.FunctionField, g₀ ≠ 0 ∧
      3 • divisor W g₀ = divisor W (mulByThreeEndo h2 h3 f) := by
  classical
  have hx : W.Ψ₃.eval x = 0 := mem_torsion_three_some_iff'.mp hS
  haveI : IsGalois F (W.triplingGaloisField x) := isGalois_triplingGaloisField h2 h3 hx
  haveI : FiniteDimensional F (W.triplingGaloisField x) := finiteDimensional_triplingGaloisField
  haveI : DecidableEq (W.triplingGaloisField x) := Classical.decEq _
  exact exists_nsmul_divisor_eq_divisor_mulByThreeEndo_of_galois (W.triplingGaloisField x) h2 h3 h
    (card_torsion_three_triplingGaloisField h2 h3 x)
    (exists_nsmul_three_eq_triplingGaloisField h) hx hf hfdiv

/-- **Rung 5 of the Weil pairing at `n = 3` over an arbitrary field with `(2 : F) ≠ 0` and
`(3 : F) ≠ 0`**, with no gated hypothesis left: for a nonsingular `F`-rational `3`-torsion point `S`
there are a principal `f_S` with `div f_S = 3·(S)` and a nonzero `g_S` with `u · g_S ^ 3 = [3]∗ f_S`
for a unit `u` of `F[W]`.

`exists_gS_three` (`EllipticCurves.FunctionField.NthRootOfPullback`) with its `hprin` discharged by
the theorem above.  `exists_gS_three_of_isAlgClosed` and `exists_gS_three_of_card` are the same
statement under a closure and under the two rationality hypotheses respectively, and **neither is
superseded for a caller that already holds those** — this one asks for less and proves the same
thing. -/
theorem exists_gS_three_general (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) {x y : F}
    (h : W.Nonsingular x y) (hS : Point.some x y h ∈ W.torsion 3) :
    ∃ f : W.FunctionField, f ≠ 0 ∧
      divisor W f = Finsupp.single (pointClosedPoint h.left) (3 : ℤ) ∧
      ∃ gS : W.FunctionField, gS ≠ 0 ∧
        ∃ u : W.CoordinateRingˣ, (u : W.CoordinateRing) • gS ^ 3 = mulByThreeEndo h2 h3 f :=
  exists_gS_three h2 h3 h hS fun _ hf hfdiv =>
    exists_nsmul_divisor_eq_divisor_mulByThreeEndo_general h2 h3 h hS hf hfdiv

/-! ### Non-vacuity over `ℚ` -/

section Nonvacuity

open EllipticCurves.Fixture Polynomial

/-- `(0, 0)` lies on `y² + y = x³`. -/
private lemma equation_zero_y2AddYEqX3 : (y2AddYEqX3 ℚ).Equation 0 0 := by
  rw [Affine.equation_iff]; norm_num [y2AddYEqX3]

private lemma nonsingular_zero_y2AddYEqX3 : (y2AddYEqX3 ℚ).Nonsingular 0 0 :=
  equation_iff_nonsingular.mp equation_zero_y2AddYEqX3

/-- `Ψ₃` of `y² + y = x³` vanishes at `0`. -/
private lemma eval_Ψ₃_zero_y2AddYEqX3 : (y2AddYEqX3 ℚ).Ψ₃.eval 0 = 0 := by
  simp only [WeierstrassCurve.Ψ₃, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆,
    WeierstrassCurve.b₈, y2AddYEqX3]
  norm_num

private lemma mem_torsion_three_zero_y2AddYEqX3 :
    Point.some 0 0 nonsingular_zero_y2AddYEqX3 ∈ (y2AddYEqX3 ℚ).torsion 3 :=
  mem_torsion_three_some_iff'.mpr eval_Ψ₃_zero_y2AddYEqX3

/-- The tripling polynomial of `(0, 0)` on `y² + y = x³` is `X⁹ − 24X⁶ + 3X³ + 1`. -/
private lemma eval_triplingX_zero_y2AddYEqX3 (x : ℚ) :
    ((y2AddYEqX3 ℚ).triplingX 0).eval x = x ^ 9 - 24 * x ^ 6 + 3 * x ^ 3 + 1 := by
  rw [eval_triplingX, Φ_three_eval]
  simp only [preΨ₄_eval, WeierstrassCurve.Ψ₃, WeierstrassCurve.Ψ₂Sq, WeierstrassCurve.b₂,
    WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈, y2AddYEqX3]
  simp only [eval_add, eval_mul, eval_pow, eval_X, eval_C, eval_ofNat]
  ring

/-- It has no rational root. -/
private theorem eval_triplingX_zero_y2AddYEqX3_ne_zero (x : ℚ) :
    ((y2AddYEqX3 ℚ).triplingX 0).eval x ≠ 0 := by
  rw [eval_triplingX_zero_y2AddYEqX3]
  intro hzero
  have hmonic : (X ^ 9 - 24 * X ^ 6 + 3 * X ^ 3 + 1 : ℤ[X]).Monic := by monicity!
  have hint : IsIntegral ℤ x := by
    refine ⟨X ^ 9 - 24 * X ^ 6 + 3 * X ^ 3 + 1, hmonic, ?_⟩
    simp only [eval₂_add, eval₂_sub, eval₂_mul, eval₂_pow, eval₂_X, eval₂_ofNat, eval₂_one]
    linear_combination hzero
  obtain ⟨d, hd⟩ := IsIntegrallyClosed.isIntegral_iff.mp hint
  subst hd
  have hdz : d ^ 9 - 24 * d ^ 6 + 3 * d ^ 3 + 1 = 0 := by
    exact_mod_cast (by simpa using hzero :
      (d : ℚ) ^ 9 - 24 * (d : ℚ) ^ 6 + 3 * (d : ℚ) ^ 3 + 1 = 0)
  have hdvd : d ∣ 1 := ⟨-(d ^ 8 - 24 * d ^ 5 + 3 * d ^ 2), by linarith [hdz]⟩
  rcases Int.isUnit_iff.mp (isUnit_of_dvd_one hdvd) with rfl | rfl <;> norm_num at hdz

/-- **`hP` fails**: no rational point of `y² + y = x³` triples to `(0, 0)`. -/
private theorem not_exists_nsmul_three_eq_zero_y2AddYEqX3 :
    ¬ ∃ P : (y2AddYEqX3 ℚ).Point,
      (3 : ℕ) • P = Point.some 0 0 nonsingular_zero_y2AddYEqX3 := by
  rintro ⟨P, hP⟩
  obtain ⟨r, hr⟩ := exists_root_triplingX_of_nsmul_three_eq (by norm_num)
    nonsingular_zero_y2AddYEqX3 hP
  exact eval_triplingX_zero_y2AddYEqX3_ne_zero r hr

/-- **`Ψ₃` of `y² + y = x³` has exactly TWO rational roots**, `0` and `−1`.

`Ψ₃ = 3X⁴ + 3X = 3X(X + 1)(X² − X + 1)` here, and `X² − X + 1` has no rational root — its
discriminant is `−3`, and the `nlinarith` certificate below is `(2x − 1)² + 3 = 0`.

⚠️ **This is the cell the `hcard` half turns on, and it needs no Weil pairing and no `μ₃`.** -/
private theorem setOf_root_Ψ₃_y2AddYEqX3 :
    {x : ℚ | (y2AddYEqX3 ℚ).Ψ₃.eval x = 0} = {0, -1} := by
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff,
    WeierstrassCurve.Ψ₃, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆,
    WeierstrassCurve.b₈, y2AddYEqX3]
  simp only [eval_add, eval_mul, eval_pow, eval_X, eval_C, eval_ofNat]
  constructor
  · intro h
    have h1 : x * (x + 1) * (x ^ 2 - x + 1) = 0 := by linarith [h]
    rcases mul_eq_zero.mp h1 with h2 | h2
    · rcases mul_eq_zero.mp h2 with h3 | h3
      · exact Or.inl h3
      · exact Or.inr (by linarith)
    · nlinarith [sq_nonneg (2 * x - 1)]
  · rintro (rfl | rfl) <;> norm_num

/-- **`#E[3] ≤ 5` on `y² + y = x³` over `ℚ`**: two roots, at most two points above each, plus `O`.

⚠️ **The counting engine is `EllipticCurves.Torsion.Finite`'s and the input is the root set above**:
`card_torsion_three_le`'s `2 · 4 + 1 = 9` becomes `2 · 2 + 1 = 5`, because `Ψ₃` splits off a
quadratic with no rational root. -/
private theorem card_torsion_three_le_five_y2AddYEqX3 :
    Nat.card ((y2AddYEqX3 ℚ).torsion 3) ≤ 5 := by
  classical
  have hfin : {x : ℚ | (y2AddYEqX3 ℚ).Ψ₃.eval x = 0}.Finite := by
    rw [setOf_root_Ψ₃_y2AddYEqX3]; exact (Set.finite_singleton _).insert _
  refine ((y2AddYEqX3 ℚ).card_torsion_le_of_xCoords hfin
    fun _ _ _ hP => Ψ₃_eval_eq_zero_of_mem_torsion_three hP).trans ?_
  rw [setOf_root_Ψ₃_y2AddYEqX3, Set.ncard_pair (by norm_num : (0 : ℚ) ≠ -1)]

/-- **`hcard` fails**: `#E[3] ≠ 9` on `y² + y = x³` over `ℚ`.

⚠️ **THIS IS THE HALF THE MODULE DOCSTRING USED TO SAY THE TREE COULD NOT STATE**, and the route is
not the one that claim was about: it is a **count of rational roots**, not the Weil-pairing argument
that `hcard` forces `μ₃ ⊆ F`.  A non-vacuity certificate needs the hypothesis to fail **at the
fixture**, and for that the counting engine suffices; the `μ₃` argument is about every curve over
`ℚ` at once and is strictly stronger than anything a certificate needs.

So `…_of_card` (`PullbackPrincipalityThreeRationalTorsion`) cannot certify this instance on
**either** of its two hypotheses, and both refutations are now theorems. -/
private theorem not_card_torsion_three_eq_nine_y2AddYEqX3 :
    Nat.card ((y2AddYEqX3 ℚ).torsion 3) ≠ 9 := by
  intro h
  have := card_torsion_three_le_five_y2AddYEqX3
  omega

/-- **The headline, inhabited** at `(0, 0)` on `y² + y = x³` over `ℚ`. -/
private theorem exampleRungFiveThreeGeneral :
    ∃ f : (y2AddYEqX3 ℚ).FunctionField, f ≠ 0 ∧
      divisor (y2AddYEqX3 ℚ) f
        = Finsupp.single (pointClosedPoint nonsingular_zero_y2AddYEqX3.left) (3 : ℤ) ∧
      ∃ gS : (y2AddYEqX3 ℚ).FunctionField, gS ≠ 0 ∧
        ∃ u : (y2AddYEqX3 ℚ).CoordinateRingˣ, (u : (y2AddYEqX3 ℚ).CoordinateRing) • gS ^ 3
          = mulByThreeEndo (by norm_num) (by norm_num) f :=
  exists_gS_three_general (by norm_num) (by norm_num) nonsingular_zero_y2AddYEqX3
    mem_torsion_three_zero_y2AddYEqX3

end Nonvacuity

end WeierstrassCurve.Affine
