/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import EllipticCurves.FunctionField.PullbackPrincipalityNGeneral
import EllipticCurves.Torsion.NthPartGaloisTower

/-!
# `[n]∗((S) − (O))` is `n` times a principal divisor over an ARBITRARY field, at a general index

`EllipticCurves.FunctionField.PullbackPrincipalityNGeneral` (rung 3 of `#962`'s ladder) moves
`hprin`'s two rationality hypotheses — `hcard : #E[n] = n²` and a point `P` with `[n]P = S` — up to
an **abstract** finite Galois `N / F` and brings the conclusion back down by Hilbert 90, and stops
there: *"Constructing the field over which the two hypotheses become theorems … is rung 4, and so
is the unconditional `…_general` headline it unlocks."*

**`EllipticCurves.Torsion.NthPartGaloisTower` builds that field and this file is that headline.**
It is the general-index mirror of `exists_nsmul_divisor_eq_divisor_mulByThreeEndo_general` and
`exists_gS_three_general` (`EllipticCurves.FunctionField.PullbackPrincipalityThreeGeneral`), and it
is the statement that discharges `hprin` off `F̄` at a general index — the hypothesis the whole
`#244` Weil-pairing front has been parametrised by.

## ⚠️ The `F̄` route is closed and this is not a matter of taste

Mathlib's Hilbert 90 is `[FiniteDimensional]`-only at the pin, so `H¹(Gal(F̄/F), F̄ˣ) = 0` is not
available and `W.nthPartGaloisField` is the route rather than a convenience.  That ruling is
`PullbackPrincipalityNGeneral`'s and `#962`'s own and is not re-derived here.

## Main statements

* `WeierstrassCurve.Affine.exists_nsmul_divisor_eq_divisor_mulByNEndo_general` : for a nonsingular
  `F`-rational `n`-torsion point `S = (x, y)` that is **not `2`-torsion**, and a nonzero `f` with
  `div f = n·(S)`, the pullback `[n]∗ f` is `n` times a principal divisor.  Over an elliptic `W`
  with `[DecidableEq F]`, `(2 : F) ≠ 0`, `((n : ℤ) : F) ≠ 0` and `Ψ₂Sq(x) ≠ 0`, and taking the
  `Transcendental F (n • genericPoint).xCoord` datum that `mulByNEndo` **mentions in the
  conclusion**.
* `WeierstrassCurve.Affine.exists_gS_n_general` : rung 5 at the same hypotheses — a principal `f_S`
  with `div f_S = n·(S)` and a nonzero `g_S` with `u · g_S ^ n = [n]∗ f_S` for a unit `u` of `F[W]`.
* `WeierstrassCurve.Affine.exists_nsmul_divisor_eq_divisor_mulByNEndo_general_of_odd` and
  `exists_gS_n_general_of_odd` : **the same two with no hypothesis on the point beyond being
  `n`-torsion**, at every **odd** `n`.  Over an elliptic `W` with `[DecidableEq F]`,
  `(2 : F) ≠ 0`, `Odd n` and `((n : ℤ) : F) ≠ 0`, and the same `Transcendental` datum.

⚠️ **The `Transcendental` argument is DATA for the statement and not an assumption of it** —
`mulByNEndo n h` mentions it — which is `PullbackPrincipalityNGeneral`'s own finding about its own
signature, re-used rather than re-derived.  ⚠️ **It is NOT discharged here and no attempt is made
to discharge it**; `transcendental_xCoord_nsmul_genericPoint` discharges it from a point `P` with
`n • P ≠ 0`, and the rung-3 proof already spends `hP` that way **over `N`**, where the datum this
file's callers must supply is over `F`.

## ⚠️ What the hypothesis `Ψ₂Sq(x) ≠ 0` costs, and why the odd pair is the headline

`Ψ₂Sq(x) ≠ 0` says `S` is not `2`-torsion, and it is the tower's hypothesis rather than the
descent's: `NthPartGaloisTower`'s `## ⚠️⚠️ The hypothesis …` section proves it cannot be dropped,
`separable_Φ_two_sub_C_mul_Ψ₂Sq_iff` (`EllipticCurves.Torsion.NthPartSeparable`) being an **iff**
at `n = 2`.  At **odd** `n` it is free — an `n`-torsion `x`-coordinate at odd `n` is never a
`2`-torsion one (`eval_Ψ₂Sq_ne_zero_of_eval_preΨ_eq_zero_of_odd`, composed here with
`nsmul_eq_zero_iff_eval_preΨ_eq_zero`) — so the `…_of_odd` pair binds nothing about the point and
**that is the pair that generalises `n = 3`**.

⚠️⚠️ **`n = 2` is NOT superseded and is not claimed to be.**
`exists_nsmul_divisor_eq_divisor_mulByTwoEndo_general` and `exists_gS_two_general`
(`EllipticCurves.FunctionField.PullbackPrincipalityTwoGeneral`) are about a `2`-torsion `S` at
`n = 2`, which is **exactly** the case this file's hypothesis excludes.  So of `#2296`'s four
numeral recoveries only the `n = 3` pair is reachable from here; ⚠️ **it is recovered below, as two
anonymous `example`s with those statements verbatim, and the `n = 2` pair is NOT recovered and must
not be read as superseded.**

## ⚠️ What is *not* here

* **No restatement of the abstract descent.**  Rung 3 is instantiated, not re-proved: the two
  general headlines each spend one application of `…_of_galois` / `exists_gS_n` and the two
  `…_of_odd` forms are one application of the general ones.
* **No `README.md` edit.**  `### What is formalised`'s *"four files … two at each of `n = 2` and
  `n = 3`"* and `PullbackPrincipalityThreeGeneral`'s own *"⚠️ **`n = 3` only** — see the module
  docstring; the tower's counting floor is an `n = 3` object"* are both falsified by this file.
  ⚠️⚠️ **Retiring them is `#2296`'s own acceptance item and is deliberately left there**, with the
  `### Reach clauses` / `### Retired claims` test to be applied to each clause individually; a round
  that folded them in would widen its unit past what one reviewer can check, and the two clauses do
  not take the same answer.
* **Nothing about `2`-torsion `S` at even `n`**, and nothing about Mathlib's Hilbert 90.
* ⚠️ **No `set_option` of any kind**, in either new module.  `PullbackPrincipalityNGeneral` carries
  none for the same reason and says so.

⚠️ **The census, source-declared**: **4** public declarations, **0** `private`, and **2** anonymous
`example`s, which generate no constant and are therefore recoveries rather than restatements.  All
**4** bind `[DecidableEq F]` and `[W.IsElliptic]` in the elaborated type.

## References

* [J. H. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.8.
-/

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum Polynomial

namespace WeierstrassCurve.Affine

open CoordinateRing

variable {F : Type*} [Field F] {W : Affine F} [DecidableEq F] [W.IsElliptic]

/-- **`hprin` at a general `n` over an arbitrary field with `(2 : F) ≠ 0` and `((n : ℤ) : F) ≠ 0`,
for an `n`-torsion point that is not `2`-torsion**, in the shape `exists_gS_n` consumes it: for a
nonsingular `F`-rational `n`-torsion `S = (x, y)` with `Ψ₂Sq(x) ≠ 0` and a nonzero `f` with
`div f = n·(S)`, the pullback `[n]∗ f` is `n` times a principal divisor.

⚠️ **No hypothesis on `F` beyond `(2 : F) ≠ 0` and `((n : ℤ) : F) ≠ 0`**: no algebraic closure, no
`hcard`, no `n`-th-part `hP`.  Both of `…_of_card`'s rationality hypotheses are bought over
`W.nthPartGaloisField hn0 x`, a finite Galois extension of `F`
(`EllipticCurves.Torsion.NthPartGaloisTower`), and paid back by Hilbert 90 through
`exists_nsmul_divisor_eq_divisor_mulByNEndo_of_galois`.

⚠️ **`Ψ₂Sq(x) ≠ 0` is the tower's hypothesis and not the descent's**, and it cannot be dropped —
see the module docstring.  At odd `n` it is free: `…_general_of_odd` below.

⚠️ **The `g₀` this returns is not the base change of the `g` obtained over `N`**, and is not claimed
to be: only its divisor identity descends. -/
theorem exists_nsmul_divisor_eq_divisor_mulByNEndo_general (h2 : (2 : F) ≠ 0) {n : ℕ}
    (hn : ((n : ℤ) : F) ≠ 0) (h : Transcendental F (n • genericPoint (W := W)).xCoord)
    {x y : F} (hns : W.Nonsingular x y) (hS : Point.some x y hns ∈ W.torsion n)
    (hx : W.Ψ₂Sq.eval x ≠ 0)
    {f : W.FunctionField} (hf : f ≠ 0)
    (hfdiv : divisor W f = Finsupp.single (pointClosedPoint hns.left) (n : ℤ)) :
    ∃ g₀ : W.FunctionField, g₀ ≠ 0 ∧
      n • divisor W g₀ = divisor W (mulByNEndo n h f) := by
  classical
  have hnF : (n : F) ≠ 0 := by exact_mod_cast hn
  have hn0 : n ≠ 0 := by rintro rfl; simp at hnF
  haveI : IsGalois F (W.nthPartGaloisField hn0 x) :=
    isGalois_nthPartGaloisField h2 hnF (hn := hn0) hx
  haveI : FiniteDimensional F (W.nthPartGaloisField hn0 x) :=
    finiteDimensional_nthPartGaloisField
  haveI : DecidableEq (W.nthPartGaloisField hn0 x) := Classical.decEq _
  exact exists_nsmul_divisor_eq_divisor_mulByNEndo_of_galois (W.nthPartGaloisField hn0 x) h2 hn h
    (card_torsion_eq_sq_nthPartGaloisField h2 hnF (hn := hn0) x) hns
    (mem_torsion_baseChange_of_nsmul_eq_zero _ hns (mem_torsion_iff.mp hS))
    (exists_nsmul_eq_nthPartGaloisField h2 (hn := hn0) hns) hf hfdiv

/-- **Rung 5 of the Weil pairing at a general `n` over an arbitrary field with `(2 : F) ≠ 0` and
`((n : ℤ) : F) ≠ 0`, for an `n`-torsion point that is not `2`-torsion**: there are a principal
`f_S` with `div f_S = n·(S)` and a nonzero `g_S` with `u · g_S ^ n = [n]∗ f_S` for a unit `u` of
`F[W]`.

`exists_gS_n` (`EllipticCurves.FunctionField.NthRootOfPullbackN`) with its `hprin` discharged by
the theorem above.  ⚠️ `exists_gS_n_of_isAlgClosed`, `exists_gS_n_of_card` and
`exists_gS_n_of_galois` are the same statement under a closure, under the two rationality
hypotheses, and over an abstract `N` respectively, and **none is superseded for a caller that
already holds those** — this one asks for less and proves the same thing. -/
theorem exists_gS_n_general (h2 : (2 : F) ≠ 0) {n : ℕ} (hn : ((n : ℤ) : F) ≠ 0)
    (h : Transcendental F (n • genericPoint (W := W)).xCoord) {x y : F}
    (hns : W.Nonsingular x y) (hS : Point.some x y hns ∈ W.torsion n)
    (hx : W.Ψ₂Sq.eval x ≠ 0) :
    ∃ f : W.FunctionField, f ≠ 0 ∧
      divisor W f = Finsupp.single (pointClosedPoint hns.left) (n : ℤ) ∧
      ∃ gS : W.FunctionField, gS ≠ 0 ∧
        ∃ u : W.CoordinateRingˣ, (u : W.CoordinateRing) • gS ^ n = mulByNEndo n h f :=
  exists_gS_n h hns hS fun _ hf hfdiv =>
    exists_nsmul_divisor_eq_divisor_mulByNEndo_general h2 hn h hns hS hx hf hfdiv

/-! ## At an odd index the hypothesis is free -/

/-- **`hprin` at every ODD `n` over an arbitrary field with `(2 : F) ≠ 0` and `((n : ℤ) : F) ≠ 0`,
with no hypothesis on the point beyond being `n`-torsion** — the headline.

⚠️⚠️ **The `Ψ₂Sq(x) ≠ 0` of the general form is DISCHARGED here rather than assumed**: at odd `n`
an `n`-torsion `x`-coordinate is never a `2`-torsion one, which is
`eval_Ψ₂Sq_ne_zero_of_eval_preΨ_eq_zero_of_odd` (`EllipticCurves.Torsion.NthPartSeparable`)
composed with `nsmul_eq_zero_iff_eval_preΨ_eq_zero` (`EllipticCurves.Torsion.OddTorsionCount`).
`exists_nsmul_divisor_eq_divisor_mulByThreeEndo_general` is its `n = 3` instance, recovered
verbatim below. -/
theorem exists_nsmul_divisor_eq_divisor_mulByNEndo_general_of_odd (h2 : (2 : F) ≠ 0) {n : ℕ}
    (hodd : Odd n) (hn : ((n : ℤ) : F) ≠ 0)
    (h : Transcendental F (n • genericPoint (W := W)).xCoord)
    {x y : F} (hns : W.Nonsingular x y) (hS : Point.some x y hns ∈ W.torsion n)
    {f : W.FunctionField} (hf : f ≠ 0)
    (hfdiv : divisor W f = Finsupp.single (pointClosedPoint hns.left) (n : ℤ)) :
    ∃ g₀ : W.FunctionField, g₀ ≠ 0 ∧
      n • divisor W g₀ = divisor W (mulByNEndo n h f) :=
  exists_nsmul_divisor_eq_divisor_mulByNEndo_general h2 hn h hns hS
    (eval_Ψ₂Sq_ne_zero_of_eval_preΨ_eq_zero_of_odd h2 hodd
      ((nsmul_eq_zero_iff_eval_preΨ_eq_zero h2 hodd hns).mp (mem_torsion_iff.mp hS)))
    hf hfdiv

/-- **Rung 5 at every ODD `n` over an arbitrary field with `(2 : F) ≠ 0` and `((n : ℤ) : F) ≠ 0`,
with no hypothesis on the point beyond being `n`-torsion** — the second headline, and
`exists_gS_three_general`'s general-index form.  The `Ψ₂Sq` hypothesis is discharged exactly as in
the theorem above. -/
theorem exists_gS_n_general_of_odd (h2 : (2 : F) ≠ 0) {n : ℕ} (hodd : Odd n)
    (hn : ((n : ℤ) : F) ≠ 0) (h : Transcendental F (n • genericPoint (W := W)).xCoord)
    {x y : F} (hns : W.Nonsingular x y) (hS : Point.some x y hns ∈ W.torsion n) :
    ∃ f : W.FunctionField, f ≠ 0 ∧
      divisor W f = Finsupp.single (pointClosedPoint hns.left) (n : ℤ) ∧
      ∃ gS : W.FunctionField, gS ≠ 0 ∧
        ∃ u : W.CoordinateRingˣ, (u : W.CoordinateRing) • gS ^ n = mulByNEndo n h f :=
  exists_gS_n_general h2 hn h hns hS
    (eval_Ψ₂Sq_ne_zero_of_eval_preΨ_eq_zero_of_odd h2 hodd
      ((nsmul_eq_zero_iff_eval_preΨ_eq_zero h2 hodd hns).mp (mem_torsion_iff.mp hS)))

/-! ## Recovery at `n = 3` -/

section Recovery

/-- **`exists_nsmul_divisor_eq_divisor_mulByThreeEndo_general`
(`EllipticCurves.FunctionField.PullbackPrincipalityThreeGeneral`) is a corollary** — its statement
verbatim, proved from the odd-index form above. -/
example (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) {x y : F}
    (h : W.Nonsingular x y) (hS : Point.some x y h ∈ W.torsion 3)
    {f : W.FunctionField} (hf : f ≠ 0)
    (hfdiv : divisor W f = Finsupp.single (pointClosedPoint h.left) (3 : ℤ)) :
    ∃ g₀ : W.FunctionField, g₀ ≠ 0 ∧
      3 • divisor W g₀ = divisor W (mulByThreeEndo h2 h3 f) := by
  obtain ⟨g₀, hg₀, hdiv⟩ :=
    exists_nsmul_divisor_eq_divisor_mulByNEndo_general_of_odd (W := W) (n := 3) h2 (by decide)
      (by exact_mod_cast h3) (transcendental_xCoord_three_nsmul h2 h3) h hS hf
      (by exact_mod_cast hfdiv)
  exact ⟨g₀, hg₀, by rwa [mulByNEndo_three h2 h3] at hdiv⟩

/-- **`exists_gS_three_general` (`EllipticCurves.FunctionField.PullbackPrincipalityThreeGeneral`) is
a corollary** — its statement verbatim, proved from the odd-index form above. -/
example (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) {x y : F}
    (h : W.Nonsingular x y) (hS : Point.some x y h ∈ W.torsion 3) :
    ∃ f : W.FunctionField, f ≠ 0 ∧
      divisor W f = Finsupp.single (pointClosedPoint h.left) (3 : ℤ) ∧
      ∃ gS : W.FunctionField, gS ≠ 0 ∧
        ∃ u : W.CoordinateRingˣ, (u : W.CoordinateRing) • gS ^ 3 = mulByThreeEndo h2 h3 f := by
  obtain ⟨f, hf, hfdiv, gS, hgS, u, hu⟩ :=
    exists_gS_n_general_of_odd (W := W) (n := 3) h2 (by decide) (by exact_mod_cast h3)
      (transcendental_xCoord_three_nsmul h2 h3) h hS
  exact ⟨f, hf, by exact_mod_cast hfdiv, gS, hgS, u, by rwa [mulByNEndo_three h2 h3] at hu⟩

end Recovery

end WeierstrassCurve.Affine
