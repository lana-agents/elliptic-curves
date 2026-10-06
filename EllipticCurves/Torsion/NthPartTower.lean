/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import EllipticCurves.Torsion.CoprimeAdjacent
import EllipticCurves.Torsion.NDivisionField
import EllipticCurves.Torsion.NthPartSeparable

/-!
# A finite Galois extension carrying both `E[n]` and an `n`-th part of a point, at every index

Let `W` be an elliptic curve over a field `F` with `(2 : F) ≠ 0`, let `n` be an index with
`n ≠ 0` and `(n : F) ≠ 0`, and let `S = (x₀, y₀)` be an affine point of `W` that is **not**
`2`-torsion — `W.Ψ₂Sq.eval x₀ ≠ 0`.  The Galois-descent argument `#962` runs needs **one**
extension of `F` that is finite Galois and over which two things hold at once: `#E[n] = n²`, and
`S` is `n` times another point.  **This file builds it at every such `n`.**

It is the general-`n` analogue of `EllipticCurves.Torsion.TriplingGaloisTower` (`n = 3`) and
`EllipticCurves.Torsion.HalvingGaloisTower` (`n = 2`), and it is `#2296`'s part (a) — the three
facts that row's item list names, over one field:

1. `[FiniteDimensional F N]` and `[IsGalois F N]` — `finiteDimensional_nthPartGaloisField` and
   `isGalois_nthPartGaloisField`;
2. `Nat.card ((W⁄N).torsion n) = n ^ 2` — `card_torsion_eq_sq_nthPartGaloisField`;
3. `∃ P : (W⁄N).Point, n • P = ` the base change of `S` — `exists_nsmul_eq_nthPartGaloisField`.

## The tower, and its layer count

```
F  ⊆  L₁ := (preΨₙ * Ψ₂Sq).SplittingField                 -- #E[n] = n² starts here
   ⊆  L₂ := nDivisionField W n                            -- #E[n] = n² holds here
   ⊆  L₃ := (W⁄L₂).nthPartXField n r₀                     -- x(P) adjoined, r₀ = x₀ over L₂
   ⊆  M  := (W⁄L₂).nthPartField n r₀                      -- y(P) adjoined; M = nthPartTower
   ⊆  N  := normalClosure F M (AlgebraicClosure M)        -- N = nthPartGaloisField
```

⚠️⚠️ **FIVE field extensions, and the count is BOUNDED — it is `5` at every `n`.**  That is
`#2296`'s *"report the layer count the way `TriplingGaloisTower` reports **five**, and whether it
is bounded in `n`"*, answered: **five, bounded**, and the two halves are bounded for different
reasons.  The bottom two are `EllipticCurves.Torsion.NDivisionField`'s first two floors, bounded
because that file's layer one is a splitting field of a **single** polynomial rather than a chain,
which its own docstring argues at length; ⚠️ **its third floor — its own Galois closure
`nDivisionGaloisField` — is NOT used here**, this file taking one normal closure at the top
instead, which is what keeps the total at five rather than six.  The top two are this file's, and
they are `2` because the `n`-th-part polynomial of a point is a **single** polynomial at every
index — `W.Φ n - C x₀ * W.ΨSq n`, of degree `n²` — and the `y`-quadratic above one of its roots is
index-free.  ⚠️ **`TriplingGaloisTower`'s five are five for
the same shape and not by coincidence**: that file warns of itself that *"three named floors are
five field extensions"*, both of its named floors being two-layer towers.

⚠️ **And the heartbeat cost `TriplingGaloisTower` records does not appear here.**  That file needs
`set_option maxHeartbeats 400000` and says the cause is *"depth, not a loop"*, namely unfolding the
`abbrev` chain inside unification.  Nothing below sets any heartbeat option.

## ⚠️⚠️ The one step that was open, and `Ψ₂Sq(x₀) ≠ 0` pays for BOTH layers

`EllipticCurves.Torsion.NthPartSeparable` supplies the separability of the `n`-th-part polynomial
at every `n` from `Ψ₂Sq(x₀) ≠ 0` alone, and its `## What is *not* here` says *"what is still owed
here is the TOWER and not the polynomial"*.  What the tower needs beyond it is the `y`-layer's
separability, that is `Ψ₂Sq(r) ≠ 0` at the root `r` adjoined below it, and the two landed indices
prove that by two different arguments neither of which generalises:

* at `n = 2`, `Ψ₂Sq_eval_ne_zero_of_root_halvingX` argues on points — a halving of a `2`-torsion
  point cannot itself be `2`-torsion;
* at `n = 3`, `Ψ₂Sq_eval_ne_zero_of_root_triplingX` is a polynomial identity in `Φ₃`, and
  `TriplingGaloisTower` says in terms that it *"is not that argument transposed"*.

`Ψ₂Sq_eval_ne_zero_of_root_nthPartX` below is the general-`n` statement, and it binds
`(2 : F) ≠ 0` and `Ψ₂Sq(x₀) ≠ 0` and **no parity, no index condition and no torsion hypothesis**.
⚠️ **So the single hypothesis `Ψ₂Sq(x₀) ≠ 0` that `NthPartSeparable` needs for the `x`-layer is
exactly what the `y`-layer needs too**, and the tower binds nothing else about `S`.

### How it goes, because the parity split is in the proof and not in the statement

At a root `r` of `Φₙ − C x₀·ΨSqₙ` with `Ψ₂Sq(r) = 0` there is a point `(r, y)` of `W` — the
`y`-quadratic has a double root there — and `ψ₂(r, y) = 0`, so `ψ_{2m}(r, y) = 0` at every `m`.
Mathlib's `Φ_eval_eq_of_equation` reads `Φₙ(r) = r·ψₙ(r, y)² − ψ_{n+1}(r, y)·ψ_{n−1}(r, y)`, and:

* at **even** `n` the vanishing factor is `ψₙ` itself, so `ΨSqₙ(r) = ψₙ(r, y)² = 0`;
* at **odd** `n` it is `ψ_{n±1}`, so `Φₙ(r) = r·ΨSqₙ(r)`, which with `Φₙ(r) = x₀·ΨSqₙ(r)` and
  `ΨSqₙ(r) ≠ 0` forces `r = x₀` and hence `Ψ₂Sq(x₀) = 0`.

⚠️ **`ΨSqₙ(r) ≠ 0` is where the coprimality is spent, and it is the reason this file imports
`EllipticCurves.Torsion.CoprimeAdjacent`**: `isCoprime_Φ_ΨSq` binds `(2 : F) ≠ 0` and holds at
every index, and `ΨSq_eval_ne_zero_of_root_nthPartX` is it read at a root.  **The same
coprimality is the `hroot` hypothesis of the `[n]`-surjectivity engine below**, so the import pays
for two steps rather than one.  ⚠️ **No `(n : F) ≠ 0` enters either of the two side conditions**,
and at `n = 0` they are vacuous rather than false: `W.Φ 0 = 1` and `W.ΨSq 0 = 0` by `simp`, so
`W.nthPartX 0 x₀ = 1` has no root and both statements are about the empty set.

## ⚠️ `n ≠ 0` sits in the TYPE of the fields, and that is declared rather than hidden

`nthPartXRoot`, `nthPartYPoly`, `nthPartField`, `nthPartTower` and `nthPartGaloisField` all take
`hn : n ≠ 0` as an argument, so a proof term appears in their types.  **It is forced**: the root is
cut out by `rootOfSplits`, whose side condition is `degree ≠ 0`, and the `n`-th-part polynomial of
degree `n²` is the constant `1` at `n = 0` — there is nothing to adjoin and no root to name.  ⚠️ `n`
is a variable here where `TriplingGaloisTower` has the numeral `3`, which is why that file carries
no such argument and this one cannot avoid it.  **`n ≠ 0` is a `Prop`, so proof irrelevance makes
any two choices definitionally equal** and no statement below needs to transport along one.

## Main definitions

* `WeierstrassCurve.Affine.nthPartX`: the `n`-th-part polynomial `Φₙ − C x₀·ΨSqₙ` of `x₀`.
* `WeierstrassCurve.Affine.nthPartXField` and `nthPartXRoot`: a splitting field of it, and a root
  of it there.
* `WeierstrassCurve.Affine.nthPartYPoly`, `nthPartField` and `nthPartYRoot`: the `y`-quadratic
  above that root, a splitting field of it, and a root of it there.
* `WeierstrassCurve.Affine.nthPartTower`: the same two floors taken over `nDivisionField W n`.
* `WeierstrassCurve.Affine.nthPartGaloisField`: its normal closure over `F`, which is the `N` a
  descent argument consumes.

## Main statements

Every bullet names every hypothesis of the statement it describes.  `[W.IsElliptic]` and
`[DecidableEq …]` are instances and are not listed.

### The polynomial and its two side conditions

* `natDegree_nthPartX`, `nthPartX_ne_zero` and `degree_nthPartX`: degree `n²`, with `n ≠ 0`.
* `eval_nthPartX` and `map_nthPartX`: the evaluation and the base change, with no hypothesis.
* `separable_nthPartX`: separable, with `(2 : F) ≠ 0`, `(n : F) ≠ 0` and `Ψ₂Sq(x₀) ≠ 0` — this is
  `EllipticCurves.Torsion.NthPartSeparable`'s headline, renamed to this file's polynomial.
* `ΨSq_eval_ne_zero_of_root_nthPartX`: at a root `r`, `ΨSqₙ(r) ≠ 0`, with `(2 : F) ≠ 0` and the
  root hypothesis.
* `Ψ₂Sq_eval_ne_zero_of_root_nthPartX`: at a root `r`, `Ψ₂Sq(r) ≠ 0`, with `(2 : F) ≠ 0`,
  `Ψ₂Sq(x₀) ≠ 0` and the root hypothesis.
* `eval_Ψ₂Sq_baseChange_ne_zero`: `Ψ₂Sq(x₀) ≠ 0` goes up any `F`-algebra, with no further
  hypothesis.

### The two new floors

⚠️ **These four are stated over the AMBIENT base `F` and are applied in the tower with `F := L₂`**,
which is the only reason the diagram's `L₃ / L₂` and `M / L₃` read as they do.

* `isGalois_nthPartXField`: the `x`-floor is Galois **over the base**, with `(2 : F) ≠ 0`,
  `(n : F) ≠ 0` and `Ψ₂Sq(x₀) ≠ 0`.  `finiteDimensional_nthPartXField` takes none of the three.
* `Ψ₂Sq_eval_nthPartXRoot_ne_zero`: the `y`-quadratic's discriminant at the adjoined root is
  nonzero, with `(2 : F) ≠ 0`, `n ≠ 0` and `Ψ₂Sq(x₀) ≠ 0`.
* `isGalois_nthPartField`: the `y`-floor is Galois **over the `x`-floor**, with `(2 : F) ≠ 0`,
  `n ≠ 0` and `Ψ₂Sq(x₀) ≠ 0`.
* `isSeparable_nthPartField`: the `y`-floor is separable **over the base**, with `(2 : F) ≠ 0`,
  `n ≠ 0`, `(n : F) ≠ 0` and `Ψ₂Sq(x₀) ≠ 0`.  `finiteDimensional_nthPartField` takes `n ≠ 0`
  alone.

### The tower and its Galois closure

* `isSeparable_nthPartTower`: `M / F` is separable, with `(2 : F) ≠ 0`, `n ≠ 0`, `(n : F) ≠ 0` and
  `Ψ₂Sq(x₀) ≠ 0`.  `finiteDimensional_nthPartTower` takes `n ≠ 0` alone.
* `isGalois_nthPartGaloisField`: `N / F` is **Galois**, with `(2 : F) ≠ 0`, `n ≠ 0`,
  `(n : F) ≠ 0` and `Ψ₂Sq(x₀) ≠ 0`.  `finiteDimensional_nthPartGaloisField` takes `n ≠ 0` alone.
* `card_torsion_eq_sq_nthPartGaloisField`: `#E[n] = n²` over `N`, with `n ≠ 0`, `(2 : F) ≠ 0` and
  `(n : F) ≠ 0` — ⚠️ **and NOT `Ψ₂Sq(x₀) ≠ 0`**, the count being inherited from `L₂` through
  `EllipticCurves.Torsion.NDivisionField`'s `card_torsion_eq_sq_of_algHom` and not from the two
  floors this file adds.
* `exists_nsmul_eq_of_roots_baseChange`: `S` is `n` times a point over any extension reached from a
  field carrying a root of the `n`-th-part polynomial and a root of the `y`-quadratic above it,
  with `(2 : F) ≠ 0`, the nonsingularity of `S` and the two root hypotheses — ⚠️ **and no
  `Ψ₂Sq(x₀) ≠ 0` and no `(n : F) ≠ 0`**: the divisibility half needs only the two roots.
* `exists_nsmul_eq_nthPartGaloisField`: `S` is `n` times a point over `N`, with `(2 : F) ≠ 0`,
  `n ≠ 0` and the nonsingularity of `S`.

### Non-vacuity, at `n = 5` over `ℚ`

`isGalois_nthPartGaloisField_y2AddYEqX3`, `finiteDimensional_nthPartGaloisField_y2AddYEqX3`,
`card_torsion_five_nthPartGaloisField_y2AddYEqX3` and
`exists_nsmul_five_eq_nthPartGaloisField_y2AddYEqX3` bind nothing whatsoever: the curve is
`y² + y = x³` over `ℚ`, the point is `(0, 0)` and the index is `5`.  ⚠️ **`#2296`'s acceptance asks
for a certificate at some `n ≥ 3` over `ℚ` and this is one**, and the point is not `3`-torsion and
`2`-torsion: `Ψ₂Sq(0) = b₆ = a₃² + 4a₆ = 1`, which is what the private lemma below proves.  ⚠️
**`(0, 0)` IS a `3`-torsion point of this curve, and `TriplingGaloisTower` uses exactly this pair
for its own non-vacuity** — which is why the index here is `5` and not `3`: at `3` the two files'
towers would be certified on the same curve at the same point, and the informative certificate is
one at an index no landed file reaches.  ⚠️ **`3` is not excluded and nothing below says it is**;
the `n = 3` statements hold of this pair too, by the same four theorems.

## What is *not* here

* ⚠️⚠️ **`#2296`'s part (b).**  `exists_nsmul_divisor_eq_divisor_mulByNEndo_general` and
  `exists_gS_n_general` — rung 3's abstract descent instantiated at this tower — are **not** here,
  and nothing below mentions a divisor, a function field or a pullback.  This file is part (a) and
  the three facts that row's item list names; part (b) consumes them and is the next rung.
* ⚠️ **The FOUR numeral recoveries that row's acceptance asks for are part (b)'s and not this
  file's**: they are recoveries of the two `_general` headlines and of `exists_gS_two_general` /
  `exists_gS_three_general`, none of which exists yet.  The four `example`s below recover what part
  (a) can: the two landed indices' counts, the tripling, and the odd-index freeness of
  `Ψ₂Sq(x₀) ≠ 0`.
* **Any statement about the degree `[M : F]` or `[N : F]`.**  The construction gives finiteness and
  nothing sharper, and in particular nothing below excludes the closure coinciding with the tower,
  or either new floor being trivial, for any curve, point or index.
* **`E[n] ≃+ ZMod n × ZMod n`.**  The general-`n` closure-free structure theorem is not in the
  tree, so nothing below states a group structure, only a cardinality — this is an absent INPUT
  and not a declined statement, and `NDivisionField`'s own bullet says the same of itself.
* ⚠️ **A `2`-torsion `S`.**  `Ψ₂Sq(x₀) ≠ 0` is bound by every statement about the fields, and at
  `n = 2` it is exactly the condition `HalvingGaloisTower` *negates*: that file's tower is built
  over a `2`-torsion `x₀` and `halvingX` exists as a square root of the quartic only there.  ⚠️ **So
  the `n = 2` recovery below is of the COUNT and not of `HalvingGaloisTower`'s halving**, and the
  two constructions are not comparable at that index.
* **Characteristic `2`.**  Every statement here carries `(2 : F) ≠ 0` and nothing below decides
  anything in characteristic `2`.
* **Minimality of the tower.**  Nothing below claims the five floors cannot be fewer.

## ⚠️ The import cost, measured

⚠️ **A closure COUNT carries a sha** (`README.md` `## Import-closure figures`), and this one is
keyed to base **`14c30ba4`** plus this module's own three `EllipticCurves` import lines, the only
other changed line being the `mk_all` entry for this module in `EllipticCurves.lean`.  This
module's `EllipticCurves` closure is **65** modules counting itself, where
`EllipticCurves.Torsion.NDivisionField`'s is **59** and `EllipticCurves.Torsion.NthPartSeparable`'s
is **59** as well, their union being **63**.  ⚠️⚠️ **The third import costs exactly ONE module**:
`EllipticCurves.Torsion.CoprimeAdjacent` has a **27**-module closure of its own and **26** of those
are already in the union, so adding it adds itself and nothing else.  ⚠️ **That is why the
coprimality is imported rather than restated**, and the measurement is what licenses the sentence.
-/

open Polynomial

namespace WeierstrassCurve.Affine

variable {F : Type*} [Field F] {W : Affine F}

/-! ## The `n`-th-part polynomial -/

variable (W) in
/-- The `n`-th-part polynomial of `x₀`. -/
noncomputable def nthPartX (n : ℕ) (x₀ : F) : F[X] := W.Φ n - C x₀ * W.ΨSq n

theorem natDegree_nthPartX {n : ℕ} (hn : n ≠ 0) (x₀ : F) :
    (W.nthPartX n x₀).natDegree = n ^ 2 :=
  natDegree_Φ_sub_C_mul_ΨSq hn x₀

theorem nthPartX_ne_zero {n : ℕ} (hn : n ≠ 0) (x₀ : F) : W.nthPartX n x₀ ≠ 0 := by
  intro h
  have hd := natDegree_nthPartX (W := W) hn x₀
  rw [h, natDegree_zero] at hd
  exact pow_ne_zero 2 hn hd.symm

theorem degree_nthPartX {n : ℕ} (hn : n ≠ 0) (x₀ : F) :
    (W.nthPartX n x₀).degree = (n ^ 2 : ℕ) := by
  rw [degree_eq_natDegree (nthPartX_ne_zero hn x₀), natDegree_nthPartX hn]

theorem eval_nthPartX (n : ℕ) (x₀ x : F) :
    (W.nthPartX n x₀).eval x = (W.Φ n).eval x - x₀ * (W.ΨSq n).eval x := by
  rw [nthPartX, eval_sub, eval_mul, eval_C]

theorem separable_nthPartX [W.IsElliptic] (h2 : (2 : F) ≠ 0) {n : ℕ} (hn : (n : F) ≠ 0) {x₀ : F}
    (hx₀ : W.Ψ₂Sq.eval x₀ ≠ 0) : (W.nthPartX n x₀).Separable :=
  separable_Φ_sub_C_mul_ΨSq_of_eval_Ψ₂Sq_ne_zero h2 hn hx₀

theorem map_nthPartX {K : Type*} [Field K] (f : F →+* K) (n : ℕ) (x₀ : F) :
    (W.map f).nthPartX n (f x₀) = (W.nthPartX n x₀).map f := by
  simp [nthPartX, Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_pow,
    apply_ite (Polynomial.map f)]

/-! ## A root of the `n`-th-part polynomial is neither `n`-torsion nor `2`-torsion -/

theorem ΨSq_eval_ne_zero_of_root_nthPartX [W.IsElliptic] (h2 : (2 : F) ≠ 0) {n : ℕ} {x₀ r : F}
    (hr : (W.nthPartX n x₀).eval r = 0) : (W.ΨSq n).eval r ≠ 0 := by
  intro h0
  refine eval_Φ_ne_zero_of_isCoprime (isCoprime_Φ_ΨSq h2 n) h0 ?_
  rw [eval_nthPartX, h0, mul_zero, sub_zero] at hr
  exact hr

theorem Ψ₂Sq_eval_ne_zero_of_root_nthPartX [W.IsElliptic] (h2 : (2 : F) ≠ 0) {n : ℕ} {x₀ : F}
    (hx₀ : W.Ψ₂Sq.eval x₀ ≠ 0) {r : F} (hr : (W.nthPartX n x₀).eval r = 0) :
    W.Ψ₂Sq.eval r ≠ 0 := by
  intro hp
  obtain ⟨y, hy⟩ : ∃ y : F, W.Equation r y :=
    exists_equation_of_isSquare h2 (by rw [hp]; exact ⟨0, by ring⟩)
  have hΨSq : (W.ΨSq n).eval r ≠ 0 := ΨSq_eval_ne_zero_of_root_nthPartX h2 hr
  have ht : (W.ψ 2).evalEval r y = 0 := by
    rw [ψ_two_evalEval]
    refine pow_eq_zero_iff two_ne_zero |>.mp ?_
    rw [← Ψ₂Sq_eval_eq_sq hy]
    exact hp
  have hΦ := Φ_eval_eq_of_equation hy (n : ℤ)
  rcases Nat.even_or_odd n with heven | ⟨m, hm⟩
  · obtain ⟨m, hm⟩ := heven
    refine hΨSq ?_
    rw [← ψ_sq_evalEval hy, show ((n : ℤ)) = 2 * (m : ℤ) by rw [hm]; push_cast; ring,
      ψ_evalEval_eq_zero_of_ψ_two_evalEval_eq_zero ht m]
    ring
  · have hup : (W.ψ ((n : ℤ) + 1)).evalEval r y = 0 := by
      rw [show ((n : ℤ) + 1) = 2 * ((m : ℤ) + 1) by rw [hm]; push_cast; ring]
      exact ψ_evalEval_eq_zero_of_ψ_two_evalEval_eq_zero ht _
    have hdown : (W.ψ ((n : ℤ) - 1)).evalEval r y = 0 := by
      rw [show ((n : ℤ) - 1) = 2 * (m : ℤ) by rw [hm]; push_cast; ring]
      exact ψ_evalEval_eq_zero_of_ψ_two_evalEval_eq_zero ht _
    rw [hup, hdown, ψ_sq_evalEval hy] at hΦ
    rw [eval_nthPartX, hΦ] at hr
    have hsplit : (r - x₀) * (W.ΨSq (n : ℤ)).eval r = 0 := by linear_combination hr
    rcases mul_eq_zero.mp hsplit with h1 | h2'
    · exact hx₀ (by rw [← sub_eq_zero.mp h1]; exact hp)
    · exact hΨSq h2'

/-! ## Base change of the two side conditions -/

private lemma ofNat_ne_zero_baseChange {L : Type*} [Field L] [Algebra F L] (n : ℕ)
    [n.AtLeastTwo] (h : (OfNat.ofNat n : F) ≠ 0) : (OfNat.ofNat n : L) ≠ 0 := by
  rw [← map_ofNat (algebraMap F L) n, ne_eq, map_eq_zero]
  exact h

private lemma natCast_ne_zero_baseChange {L : Type*} [Field L] [Algebra F L] {n : ℕ}
    (h : (n : F) ≠ 0) : (n : L) ≠ 0 := by
  rw [← map_natCast (algebraMap F L) n, ne_eq, map_eq_zero]
  exact h

theorem eval_Ψ₂Sq_baseChange_ne_zero {L : Type*} [Field L] [Algebra F L] {x₀ : F}
    (hx₀ : W.Ψ₂Sq.eval x₀ ≠ 0) : (W⁄L).Ψ₂Sq.eval (algebraMap F L x₀) ≠ 0 := by
  rw [show (W⁄L) = W.map (algebraMap F L) from rfl, WeierstrassCurve.map_Ψ₂Sq, eval_map,
    ← Polynomial.aeval_def, Polynomial.aeval_algebraMap_apply]
  simpa using hx₀

/-! ## The first floor: adjoining the `n`-th-part `x`-coordinate -/

/-- A splitting field of the `n`-th-part polynomial. -/
noncomputable abbrev nthPartXField (W : Affine F) (n : ℕ) (x₀ : F) : Type _ :=
  (W.nthPartX n x₀).SplittingField

/-- A root of the `n`-th-part polynomial in its splitting field. -/
noncomputable def nthPartXRoot (W : Affine F) {n : ℕ} (hn : n ≠ 0) (x₀ : F) :
    W.nthPartXField n x₀ :=
  rootOfSplits (IsSplittingField.splits (W.nthPartXField n x₀) (W.nthPartX n x₀))
    (by
      rw [Polynomial.degree_map, degree_nthPartX hn]
      exact_mod_cast pow_ne_zero 2 hn)

theorem eval_nthPartXRoot {W : Affine F} {n : ℕ} (hn : n ≠ 0) (x₀ : F) :
    ((W⁄(W.nthPartXField n x₀)).nthPartX n (algebraMap F (W.nthPartXField n x₀) x₀)).eval
      (W.nthPartXRoot hn x₀) = 0 := by
  rw [show (W⁄(W.nthPartXField n x₀)) = W.map (algebraMap F (W.nthPartXField n x₀)) from rfl,
    map_nthPartX]
  exact eval_rootOfSplits _ _

section FirstFloor

variable {W : Affine F} {n : ℕ} {x₀ : F}

theorem isGalois_nthPartXField [W.IsElliptic] (h2 : (2 : F) ≠ 0) (hn : (n : F) ≠ 0)
    (hx₀ : W.Ψ₂Sq.eval x₀ ≠ 0) : IsGalois F (W.nthPartXField n x₀) :=
  IsGalois.of_separable_splitting_field (p := W.nthPartX n x₀) (separable_nthPartX h2 hn hx₀)

theorem finiteDimensional_nthPartXField : FiniteDimensional F (W.nthPartXField n x₀) :=
  IsSplittingField.finiteDimensional _ (W.nthPartX n x₀)

theorem Ψ₂Sq_eval_nthPartXRoot_ne_zero [W.IsElliptic] (h2 : (2 : F) ≠ 0) (hn : n ≠ 0)
    (hx₀ : W.Ψ₂Sq.eval x₀ ≠ 0) :
    (W⁄(W.nthPartXField n x₀)).Ψ₂Sq.eval (W.nthPartXRoot hn x₀) ≠ 0 := by
  haveI : (W⁄(W.nthPartXField n x₀)).IsElliptic :=
    inferInstanceAs (W.map (algebraMap F (W.nthPartXField n x₀))).IsElliptic
  exact Ψ₂Sq_eval_ne_zero_of_root_nthPartX (ofNat_ne_zero_baseChange 2 h2)
    (eval_Ψ₂Sq_baseChange_ne_zero hx₀) (eval_nthPartXRoot hn x₀)

end FirstFloor

/-! ## The second floor: adjoining the `y`-coordinate above it -/

/-- The `y`-quadratic above the chosen `n`-th-part `x`-coordinate, over the first floor. -/
noncomputable def nthPartYPoly (W : Affine F) {n : ℕ} (hn : n ≠ 0) (x₀ : F) :
    (W.nthPartXField n x₀)[X] :=
  (W⁄(W.nthPartXField n x₀)).halvingY (W.nthPartXRoot hn x₀)

/-- **The `n`-th-part field** of the point at `x₀`. -/
noncomputable abbrev nthPartField (W : Affine F) {n : ℕ} (hn : n ≠ 0) (x₀ : F) : Type _ :=
  (W.nthPartYPoly hn x₀).SplittingField

/-- A root of the `y`-quadratic in the `n`-th-part field. -/
noncomputable def nthPartYRoot (W : Affine F) {n : ℕ} (hn : n ≠ 0) (x₀ : F) :
    W.nthPartField hn x₀ :=
  rootOfSplits (IsSplittingField.splits (W.nthPartField hn x₀) (W.nthPartYPoly hn x₀))
    (by rw [Polynomial.degree_map, nthPartYPoly, degree_halvingY]; exact two_ne_zero)

theorem eval_nthPartYRoot (W : Affine F) {n : ℕ} (hn : n ≠ 0) (x₀ : F) :
    ((W.nthPartYPoly hn x₀).map
      (algebraMap (W.nthPartXField n x₀) (W.nthPartField hn x₀))).eval
        (W.nthPartYRoot hn x₀) = 0 :=
  eval_rootOfSplits _ _

section SecondFloor

variable {W : Affine F} {n : ℕ} {x₀ : F}

theorem isGalois_nthPartField [W.IsElliptic] (h2 : (2 : F) ≠ 0) (hn : n ≠ 0)
    (hx₀ : W.Ψ₂Sq.eval x₀ ≠ 0) :
    IsGalois (W.nthPartXField n x₀) (W.nthPartField hn x₀) :=
  IsGalois.of_separable_splitting_field (p := W.nthPartYPoly hn x₀)
    (separable_halvingY (Ψ₂Sq_eval_nthPartXRoot_ne_zero h2 hn hx₀))

theorem isSeparable_nthPartField [W.IsElliptic] (h2 : (2 : F) ≠ 0) (hn : n ≠ 0)
    (hn' : (n : F) ≠ 0) (hx₀ : W.Ψ₂Sq.eval x₀ ≠ 0) :
    Algebra.IsSeparable F (W.nthPartField hn x₀) := by
  haveI := isGalois_nthPartXField (W := W) (n := n) (x₀ := x₀) h2 hn' hx₀
  haveI := isGalois_nthPartField (W := W) (n := n) (x₀ := x₀) h2 hn hx₀
  exact Algebra.IsSeparable.trans F (W.nthPartXField n x₀) (W.nthPartField hn x₀)

theorem finiteDimensional_nthPartField (hn : n ≠ 0) :
    FiniteDimensional F (W.nthPartField hn x₀) := by
  haveI : FiniteDimensional F (W.nthPartXField n x₀) := finiteDimensional_nthPartXField
  haveI : FiniteDimensional (W.nthPartXField n x₀) (W.nthPartField hn x₀) :=
    IsSplittingField.finiteDimensional _ (W.nthPartYPoly hn x₀)
  exact FiniteDimensional.trans F (W.nthPartXField n x₀) (W.nthPartField hn x₀)

end SecondFloor

/-! ## The tower over the `n`-division field -/

variable (W) in
/-- The `x`-floor of the `n`-th-part tower, taken over the `n`-division field. -/
noncomputable abbrev nthPartTowerX (n : ℕ) (x₀ : F) : Type _ :=
  (W⁄(nDivisionField W n)).nthPartXField n (algebraMap F (nDivisionField W n) x₀)

variable (W) in
/-- **The fourth floor**: the `n`-th-part field of `x₀`, taken over the `n`-division field. -/
noncomputable abbrev nthPartTower {n : ℕ} (hn : n ≠ 0) (x₀ : F) : Type _ :=
  (W⁄(nDivisionField W n)).nthPartField hn (algebraMap F (nDivisionField W n) x₀)

/-- `F ⊆ L₂ ⊆ M` is a tower. -/
instance instIsScalarTowerNthPartTower {n : ℕ} (hn : n ≠ 0) (x₀ : F) :
    IsScalarTower F (nDivisionField W n) (W.nthPartTower hn x₀) := by
  refine IsScalarTower.of_algebraMap_eq fun a => ?_
  rw [IsScalarTower.algebraMap_apply F (W.nthPartTowerX n x₀) (W.nthPartTower hn x₀),
    IsScalarTower.algebraMap_apply F (nDivisionField W n) (W.nthPartTowerX n x₀),
    ← IsScalarTower.algebraMap_apply (nDivisionField W n) (W.nthPartTowerX n x₀)
      (W.nthPartTower hn x₀)]

/-- The `n`-th-part `x`-coordinate, as an element of the fourth floor. -/
noncomputable def nthPartTowerXRoot (W : Affine F) {n : ℕ} (hn : n ≠ 0) (x₀ : F) :
    W.nthPartTower hn x₀ :=
  algebraMap (W.nthPartTowerX n x₀) (W.nthPartTower hn x₀)
    ((W⁄(nDivisionField W n)).nthPartXRoot hn (algebraMap F (nDivisionField W n) x₀))

/-- The `y`-coordinate above it, which is where the fourth floor is adjoined. -/
noncomputable def nthPartTowerYRoot (W : Affine F) {n : ℕ} (hn : n ≠ 0) (x₀ : F) :
    W.nthPartTower hn x₀ :=
  (W⁄(nDivisionField W n)).nthPartYRoot hn (algebraMap F (nDivisionField W n) x₀)

/-! ## The fourth floor is finite and separable over `F` -/

section TowerFacts

variable [W.IsElliptic] {n : ℕ}

/-- **`M / F` is separable.** -/
theorem isSeparable_nthPartTower (h2 : (2 : F) ≠ 0) (hn : n ≠ 0) (hn' : (n : F) ≠ 0) {x₀ : F}
    (hx₀ : W.Ψ₂Sq.eval x₀ ≠ 0) : Algebra.IsSeparable F (W.nthPartTower hn x₀) := by
  haveI : (W⁄(nDivisionField W n)).IsElliptic :=
    inferInstanceAs (W.map (algebraMap F (nDivisionField W n))).IsElliptic
  haveI := isSeparable_nDivisionField W n h2 hn'
  haveI : Algebra.IsSeparable (nDivisionField W n) (W.nthPartTower hn x₀) :=
    isSeparable_nthPartField (ofNat_ne_zero_baseChange 2 h2) hn
      (natCast_ne_zero_baseChange hn') (eval_Ψ₂Sq_baseChange_ne_zero hx₀)
  exact Algebra.IsSeparable.trans F (nDivisionField W n) (W.nthPartTower hn x₀)

omit [W.IsElliptic] in
/-- **`M / F` is finite**, each floor being a splitting field of a polynomial. -/
theorem finiteDimensional_nthPartTower (hn : n ≠ 0) {x₀ : F} :
    FiniteDimensional F (W.nthPartTower hn x₀) := by
  haveI : FiniteDimensional F (nDivisionField W n) := finiteDimensional_nDivisionField W n
  haveI : FiniteDimensional (nDivisionField W n) (W.nthPartTower hn x₀) :=
    finiteDimensional_nthPartField hn
  exact FiniteDimensional.trans F (nDivisionField W n) (W.nthPartTower hn x₀)

end TowerFacts

/-! ## The fifth floor: the Galois closure -/

variable (W) in
/-- **The fifth floor `N`**: the Galois closure of the `n`-th-part tower over `F`. -/
noncomputable abbrev nthPartGaloisField {n : ℕ} (hn : n ≠ 0) (x₀ : F) : Type _ :=
  IntermediateField.normalClosure F (W.nthPartTower hn x₀)
    (AlgebraicClosure (W.nthPartTower hn x₀))

section Closure

variable [W.IsElliptic] {n : ℕ}

/-- **`N / F` is Galois.** -/
theorem isGalois_nthPartGaloisField (h2 : (2 : F) ≠ 0) (hn : n ≠ 0) (hn' : (n : F) ≠ 0) {x₀ : F}
    (hx₀ : W.Ψ₂Sq.eval x₀ ≠ 0) : IsGalois F (W.nthPartGaloisField hn x₀) := by
  haveI := isSeparable_nthPartTower h2 hn hn' hx₀
  exact _root_.isGalois_normalClosure_of_isSeparable F (W.nthPartTower hn x₀)

omit [W.IsElliptic] in
/-- **`N / F` is finite.** -/
theorem finiteDimensional_nthPartGaloisField (hn : n ≠ 0) {x₀ : F} :
    FiniteDimensional F (W.nthPartGaloisField hn x₀) := by
  haveI : FiniteDimensional F (W.nthPartTower hn x₀) := finiteDimensional_nthPartTower hn
  infer_instance

end Closure

/-! ## `#E[n] = n²` over the fifth floor -/

variable (W) in
/-- The composite `F`-algebra hom from the `n`-division field into the Galois closure. -/
noncomputable def nDivisionFieldToNthPartGalois {n : ℕ} (hn : n ≠ 0) (x₀ : F) :
    nDivisionField W n →ₐ[F] W.nthPartGaloisField hn x₀ :=
  (IsScalarTower.toAlgHom F (W.nthPartTower hn x₀) (W.nthPartGaloisField hn x₀)).comp
    (IsScalarTower.toAlgHom F (nDivisionField W n) (W.nthPartTower hn x₀))

/-- **`#E[n] = n²` over `N`.** -/
theorem card_torsion_eq_sq_nthPartGaloisField [W.IsElliptic] {n : ℕ} (hn : n ≠ 0)
    (x₀ : F) [DecidableEq (W.nthPartGaloisField hn x₀)] (h2 : (2 : F) ≠ 0) (hn' : (n : F) ≠ 0) :
    Nat.card ((W⁄(W.nthPartGaloisField hn x₀)).torsion n) = n ^ 2 :=
  card_torsion_eq_sq_of_algHom h2 hn' (W.nDivisionFieldToNthPartGalois hn x₀)
    (splits_preΨ_tower (W := W) (n := n) (L₂ := nDivisionField W n)
      (W.preΨ (n : ℤ) * W.Ψ₂Sq).SplittingField hn' h2)
    (splits_Ψ₂Sq_tower (W := W) (n := n) (L₂ := nDivisionField W n)
      (W.preΨ (n : ℤ) * W.Ψ₂Sq).SplittingField hn' h2)
    fun _ hz =>
      isSquare_Ψ₂Sq_eval_tower_n (W := W) (n := n) (L₂ := nDivisionField W n)
        (W.preΨ (n : ℤ) * W.Ψ₂Sq).SplittingField hn' h2 hz

/-! ## Base change of a root, and the `n`-th part over an extension -/

private lemma baseChange_baseChange_nthPart (W : Affine F) (L₁ : Type*) [Field L₁] [Algebra F L₁]
    (L : Type*) [Field L] [Algebra F L] [Algebra L₁ L] [IsScalarTower F L₁ L] :
    ((W⁄L₁)⁄L) = (W⁄L) :=
  WeierstrassCurve.map_baseChange (R := F) W (IsScalarTower.toAlgHom F L₁ L)

section Bridge

variable {L₁ L : Type*} [Field L₁] [Field L] [Algebra F L₁] [Algebra F L] [Algebra L₁ L]
  [IsScalarTower F L₁ L]

/-- A root of the `n`-th-part polynomial over `L₁` is one over any extension of `L₁`. -/
theorem eval_nthPartX_baseChange {n : ℕ} {x₀ : F} {r : L₁}
    (hr : ((W⁄L₁).nthPartX n (algebraMap F L₁ x₀)).eval r = 0) :
    ((W⁄L).nthPartX n (algebraMap F L x₀)).eval (algebraMap L₁ L r) = 0 := by
  rw [← baseChange_baseChange_nthPart W L₁ L,
    show ((W⁄L₁)⁄L) = (W⁄L₁).map (algebraMap L₁ L) from rfl,
    IsScalarTower.algebraMap_apply F L₁ L x₀, map_nthPartX, eval_map, ← Polynomial.aeval_def,
    Polynomial.aeval_algebraMap_apply, Polynomial.aeval_def, ← eval_map, ← map_nthPartX]
  simp [Algebra.algebraMap_self, hr]

end Bridge

theorem eval_nthPartTowerXRoot {n : ℕ} (hn : n ≠ 0) (x₀ : F) :
    ((W⁄(W.nthPartTower hn x₀)).nthPartX n (algebraMap F (W.nthPartTower hn x₀) x₀)).eval
      (W.nthPartTowerXRoot hn x₀) = 0 := by
  have h : (((W⁄(nDivisionField W n))⁄(W.nthPartTower hn x₀)).nthPartX n
      (algebraMap (nDivisionField W n) (W.nthPartTower hn x₀)
        (algebraMap F (nDivisionField W n) x₀))).eval (W.nthPartTowerXRoot hn x₀) = 0 :=
    eval_nthPartX_baseChange (eval_nthPartXRoot hn _)
  rwa [baseChange_baseChange_nthPart W (nDivisionField W n) (W.nthPartTower hn x₀),
    ← IsScalarTower.algebraMap_apply F (nDivisionField W n) (W.nthPartTower hn x₀) x₀] at h

theorem eval_nthPartTowerYRoot {n : ℕ} (hn : n ≠ 0) (x₀ : F) :
    ((W⁄(W.nthPartTower hn x₀)).halvingY (W.nthPartTowerXRoot hn x₀)).eval
      (W.nthPartTowerYRoot hn x₀) = 0 := by
  have h : (((W⁄(nDivisionField W n))⁄(W.nthPartTower hn x₀)).halvingY
      (W.nthPartTowerXRoot hn x₀)).eval (W.nthPartTowerYRoot hn x₀) = 0 :=
    eval_halvingY_baseChange (eval_nthPartYRoot _ hn _)
  rwa [baseChange_baseChange_nthPart W (nDivisionField W n) (W.nthPartTower hn x₀)] at h

/-! ## `S` is `n` times another point over the fifth floor -/

/-- **`S` is `n` times another point over any extension reached from a field carrying both
roots.** -/
theorem exists_nsmul_eq_of_roots_baseChange [W.IsElliptic] {M L : Type*} [Field M] [Field L]
    [Algebra F M] [Algebra F L] [Algebra M L] [IsScalarTower F M L] [DecidableEq L]
    (h2 : (2 : F) ≠ 0) {n : ℕ} {x₀ y₀ : F} (hQ : W.Nonsingular x₀ y₀)
    {r s : M} (hr : ((W⁄M).nthPartX n (algebraMap F M x₀)).eval r = 0)
    (hs : ((W⁄M).halvingY r).eval s = 0) :
    ∃ P : (W⁄L).Point, n • P = Point.some (algebraMap F L x₀) (algebraMap F L y₀)
      ((W.map_nonsingular (algebraMap F L).injective x₀ y₀).mpr hQ) := by
  haveI : (W⁄L).IsElliptic := inferInstanceAs (W.map (algebraMap F L)).IsElliptic
  have h2L : (2 : L) ≠ 0 := ofNat_ne_zero_baseChange 2 h2
  have hrL : ((W⁄L).nthPartX n (algebraMap F L x₀)).eval (algebraMap M L r) = 0 :=
    eval_nthPartX_baseChange hr
  have hsL : ((W⁄L).halvingY (algebraMap M L r)).eval (algebraMap M L s) = 0 := by
    refine eval_halvingY_baseChange ?_
    rw [Polynomial.eval_map, Polynomial.eval₂_at_apply, hs, map_zero]
  refine exists_nsmul_eq_some_of_hasXCoordFormula_of_root
    (fun x hx => eval_Φ_ne_zero_of_isCoprime (isCoprime_Φ_ΨSq h2L n) hx)
    (hasXCoordFormula_of_two_ne_zero h2L n) _
    (equation_of_eval_halvingY_eq_zero hsL) ?_
  rw [eval_nthPartX] at hrL
  linear_combination hrL

/-- **`S` is `n` times another point over `N`.** -/
theorem exists_nsmul_eq_nthPartGaloisField [W.IsElliptic] (h2 : (2 : F) ≠ 0) {n : ℕ} (hn : n ≠ 0)
    {x₀ y₀ : F} (hQ : W.Nonsingular x₀ y₀) [DecidableEq (W.nthPartGaloisField hn x₀)] :
    ∃ P : (W⁄(W.nthPartGaloisField hn x₀)).Point,
      n • P = Point.some (algebraMap F (W.nthPartGaloisField hn x₀) x₀)
        (algebraMap F (W.nthPartGaloisField hn x₀) y₀)
        ((W.map_nonsingular (algebraMap F (W.nthPartGaloisField hn x₀)).injective x₀ y₀).mpr hQ) :=
  exists_nsmul_eq_of_roots_baseChange h2 hQ (eval_nthPartTowerXRoot hn x₀)
    (eval_nthPartTowerYRoot hn x₀)

/-! ## Recovery at the two landed indices -/

section Recovery

variable [W.IsElliptic]

/-- Recovery at `n = 3`: `#E[3] = 9` over the general `n`-th-part tower, with the torsion
hypothesis of `EllipticCurves.Torsion.TriplingGaloisTower` in place of `Ψ₂Sq(x₀) ≠ 0`. -/
example (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) (hn : (3 : ℕ) ≠ 0) {x₀ : F}
    [DecidableEq (W.nthPartGaloisField hn x₀)] :
    Nat.card ((W⁄(W.nthPartGaloisField hn x₀)).torsion 3) = 9 := by
  simpa using card_torsion_eq_sq_nthPartGaloisField (W := W) hn x₀ h2 (by exact_mod_cast h3)

/-- Recovery at `n = 3`: the tripling, over the general tower. -/
example (h2 : (2 : F) ≠ 0) (hn : (3 : ℕ) ≠ 0) {x₀ y₀ : F} (hQ : W.Nonsingular x₀ y₀)
    [DecidableEq (W.nthPartGaloisField hn x₀)] :
    ∃ P : (W⁄(W.nthPartGaloisField hn x₀)).Point,
      (3 : ℕ) • P = Point.some (algebraMap F (W.nthPartGaloisField hn x₀) x₀)
        (algebraMap F (W.nthPartGaloisField hn x₀) y₀)
        ((W.map_nonsingular (algebraMap F (W.nthPartGaloisField hn x₀)).injective x₀ y₀).mpr hQ) :=
  exists_nsmul_eq_nthPartGaloisField h2 hn hQ

/-- Recovery at `n = 2`: `#E[2] = 4` over the general tower. -/
example (h2 : (2 : F) ≠ 0) (hn : (2 : ℕ) ≠ 0) {x₀ : F}
    [DecidableEq (W.nthPartGaloisField hn x₀)] :
    Nat.card ((W⁄(W.nthPartGaloisField hn x₀)).torsion 2) = 4 := by
  simpa using card_torsion_eq_sq_nthPartGaloisField (W := W) hn x₀ h2 (by exact_mod_cast h2)

/-- ⚠️ **At odd `n` the hypothesis `Ψ₂Sq(x₀) ≠ 0` is FREE from `n`-torsion**, which is what makes
the two landed towers' torsion hypotheses sufficient for the general construction. -/
example (h2 : (2 : F) ≠ 0) {n : ℕ} (hodd : Odd n) {x₀ : F}
    (hx₀ : (W.preΨ (n : ℤ)).eval x₀ = 0) : W.Ψ₂Sq.eval x₀ ≠ 0 :=
  eval_Ψ₂Sq_ne_zero_of_eval_preΨ_eq_zero_of_odd h2 hodd hx₀

end Recovery

/-! ## Non-vacuity: a certificate at `n = 5` over `ℚ` -/

section Nonvacuity

open EllipticCurves.Fixture

private lemma five_ne_zero_nat : (5 : ℕ) ≠ 0 := by norm_num

/-- **`(0, 0)` lies on `y² + y = x³`.** -/
private lemma nonsingular_zero_y2AddYEqX3' : (y2AddYEqX3 ℚ).Nonsingular 0 0 := by
  refine equation_iff_nonsingular.mp ?_
  rw [Affine.equation_iff]; norm_num [y2AddYEqX3]

/-- **`(0, 0)` is not a `2`-torsion point of `y² + y = x³`**: `Ψ₂Sq(0) = 1`. -/
private lemma eval_Ψ₂Sq_zero_y2AddYEqX3_ne_zero : (y2AddYEqX3 ℚ).Ψ₂Sq.eval 0 ≠ 0 := by
  simp only [WeierstrassCurve.Ψ₂Sq, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, y2AddYEqX3]
  norm_num

private noncomputable instance :
    DecidableEq ((y2AddYEqX3 ℚ).nthPartGaloisField five_ne_zero_nat (0 : ℚ)) := Classical.decEq _

/-- **`N / ℚ` is finite Galois** at `n = 5` on the certificate curve. -/
theorem isGalois_nthPartGaloisField_y2AddYEqX3 :
    IsGalois ℚ ((y2AddYEqX3 ℚ).nthPartGaloisField five_ne_zero_nat (0 : ℚ)) :=
  isGalois_nthPartGaloisField (by norm_num) five_ne_zero_nat (by norm_num)
    eval_Ψ₂Sq_zero_y2AddYEqX3_ne_zero

theorem finiteDimensional_nthPartGaloisField_y2AddYEqX3 :
    FiniteDimensional ℚ ((y2AddYEqX3 ℚ).nthPartGaloisField five_ne_zero_nat (0 : ℚ)) :=
  finiteDimensional_nthPartGaloisField five_ne_zero_nat

/-- **`#E[5] = 25` over `N`** on the certificate curve. -/
theorem card_torsion_five_nthPartGaloisField_y2AddYEqX3 :
    Nat.card (((y2AddYEqX3 ℚ)⁄((y2AddYEqX3 ℚ).nthPartGaloisField
      five_ne_zero_nat (0 : ℚ))).torsion 5) = 25 := by
  simpa using card_torsion_eq_sq_nthPartGaloisField (W := y2AddYEqX3 ℚ) five_ne_zero_nat 0
    (by norm_num) (by norm_num)

/-- **`(0, 0)` is five times a point of the curve over `N`.** -/
theorem exists_nsmul_five_eq_nthPartGaloisField_y2AddYEqX3 :
    ∃ P : ((y2AddYEqX3 ℚ)⁄((y2AddYEqX3 ℚ).nthPartGaloisField
        five_ne_zero_nat (0 : ℚ))).Point,
      (5 : ℕ) • P = Point.some
        (algebraMap ℚ ((y2AddYEqX3 ℚ).nthPartGaloisField five_ne_zero_nat (0 : ℚ)) 0)
        (algebraMap ℚ ((y2AddYEqX3 ℚ).nthPartGaloisField five_ne_zero_nat (0 : ℚ)) 0)
        (((y2AddYEqX3 ℚ).map_nonsingular
          (algebraMap ℚ ((y2AddYEqX3 ℚ).nthPartGaloisField five_ne_zero_nat
            (0 : ℚ))).injective 0 0).mpr nonsingular_zero_y2AddYEqX3') :=
  exists_nsmul_eq_nthPartGaloisField (by norm_num) five_ne_zero_nat nonsingular_zero_y2AddYEqX3'

end Nonvacuity

end WeierstrassCurve.Affine
