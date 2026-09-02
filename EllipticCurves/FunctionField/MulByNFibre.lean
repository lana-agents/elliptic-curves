/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import EllipticCurves.Fixtures
import EllipticCurves.FunctionField.MulByNInertia
import EllipticCurves.FunctionField.MulByThreeFibre
import EllipticCurves.Torsion.NsmulSmoothSurjective

/-!
# The place contraction of `[n]∗` **is** `[n]` on rational points, and the fibre over one, at every
`3`-smooth `n`

`EllipticCurves.FunctionField.MulByTwoFibreAffine` (`#774`) proves

```
comapProjPointTwo h2 (projPointOfPoint P) = projPointOfPoint (2 • P)
```

for every `P : W.Point`, and `EllipticCurves.FunctionField.MulByThreeFibre` proves its `n = 3`
mirror.  From each, over `F̄`, that file computes the fibre — a coset of `E[2]` (resp. `E[3]`), of
size `4` (resp. `9`), every ramification index `1`, and the divisor identity `[n]∗(S) = ∑_{p ↦ S}
(p)` that `#418`'s `hprin` consumes.  **Neither had a general-`n` form, and this file supplies one
at every `3`-smooth `n`.**

## Why composition reaches this, and what it costs

`[m · n]∗ = [m]∗ ∘ [n]∗` (`mulByNEndo_mul`, `#1213`) contracts places covariantly
(`comapProjPointN_mul`, `EllipticCurves.FunctionField.MulByNPlaceComposition`), so an index
`2 ^ a · 3 ^ b` is reached by peeling one prime at a time off the two merged computations.  ⚠️ **No
coordinate formula is evaluated at any new index.**  `addY_self_eq_div`
(`EllipticCurves.Torsion.DoublingCoords`) and its `n = 3` mirror
(`EllipticCurves.Torsion.TriplingCoords`) enter exactly where they already did, at `n = 2` and
`n = 3`, and the general-`n` `ωₙ` duplication formula is not approached.  ⚠️ That formula used to
be named here as `#251`, **not** `#404`; the attribution was right and the openness is not — it
holds at every index (`nsmul_eq_some_omegaY_of_ΨSq_ne_zero`,
`EllipticCurves.Torsion.NsmulYPeriodic`, `#1500`, PR #579).  Nothing below consumes it.

## ⚠️ The induction here is *not* the one `#1214` ran, and the difference is the whole difficulty

`comapProjPointN_two_pow_mul_three_pow_none` (`EllipticCurves.FunctionField.MulByNPlaceComposition`)
runs the same double induction at the point at infinity.  **There the point is a fixed point** —
`comapProjPointTwo none = none` — so the induction hypothesis is a statement about one place and
needs no generalisation.  **Here the point moves**: peeling `[2]` off `[2 ^ (a+1) · 3 ^ b]` leaves
`[2 ^ a · 3 ^ b]` applied to `projPointOfPoint (2 • P)`, a *different* rational point.  The
induction must therefore be generalised over `P`, and what makes that legitimate is that
`projPointOfPoint (2 • P)` is again in the rational locus — the class the merged statements are
about is closed under the map.  ⚠️ A reader who reads this file as *"`#1214` with `none` replaced by
`projPointOfPoint P`"* has the shape right and the reason wrong.

## Main statements

⚠️ Every public declaration of this file is listed.

* `…comapProjPointN_two_pow_mul_three_pow_projPointOfPoint` — the double induction, at an index
  presented as `2 ^ a * 3 ^ b`;
* **`…comapProjPointN_projPointOfPoint_of_smooth`** — the headline, `comapProjPointN n h
  (projPointOfPoint P) = projPointOfPoint (n • P)` at every `3`-smooth `n ≠ 0`;
* `…projPointOfPoint_add_injective` — `R ↦ P ⊕ R` is injective into the places, at **every** `n`
  and with no hypothesis on `F`.  ⚠️ The merged `…_two` and `…_three` forms of this carry an index
  that their proof never uses;
* `…comapProjPointN_add_torsion_of_smooth` — the coset `{ P ⊕ R : R ∈ E[n] }` lies in the fibre;
* over `F̄`: `…card_fibre_comapProjPointN_le_sq`, **`…card_fibre_comapProjPointN_projPointOfPoint`**
  (`= n ^ 2`), `…fibre_comapProjPointN_eq_range` (the fibre **is** that coset),
  `…ramificationIdxN_eq_one_of_comapProjPointN_eq_projPointOfPoint`,
  `…pullbackDivisorN_single_projPointOfPoint` (`[n]∗(S) = ∑_{p ↦ S} (p)`) and
  `…pullbackDivisorN_single_eq_sum_torsion` (`[n]∗(S) = ∑_{R ∈ E[n]} (P ⊕ R)`).

## What is *not* here

* **Nothing at `n = 5`.**  Every statement is `3`-smooth, and the ceiling is the one the whole front
  carries: `transcendental_xCoord_nsmul_of_smooth`, `card_torsion_eq_sq_of_smooth` and
  `sum_ramificationIdxN_of_smooth` are each `3`-smooth, and `nsmul_surjective_of_smooth`
  (`EllipticCurves.Torsion.NsmulSmoothSurjective`) is too.  ⚠️ **This bullet used to add that three
  of those four are `3`-smooth for the *same* reason — the general-`n` coordinate formula `#251` —
  and that reason has been removed**: `#251`'s coordinate formula holds at every index
  (`hasXCoordFormula_of_two_ne_zero`, `EllipticCurves.Torsion.NsmulOrder`), `[n]`-surjectivity on
  `E(F̄)` at every `n ≠ 0` is `nsmul_surjective_of_two_ne_zero`
  (`EllipticCurves.Torsion.TwoTorsionOrder`), and the transcendence input is
  `transcendental_xCoord_nsmul_of_isAlgClosed` (`EllipticCurves.FunctionField.MulByNTranscendence`)
  at every `n ≠ 0` over `F̄`.  ⚠️ **The bullet's conclusion is unchanged**: the statements *below*
  are still `3`-smooth, because they consume `card_torsion_eq_sq_of_smooth` (`#E[n] = n²`, still
  `3`-smooth) and `sum_ramificationIdxN_of_smooth`, which routes through
  `finrank_mulByNEndoFieldRange_of_smooth` — so behind it stands the general-`n` degree, i.e.
  `#1184` and `(n : F) ≠ 0`.  Lifting any one input alone still lifts nothing here.
* **No statement at a place that is not the place of a rational point.**  As `#774` records of its
  own `n = 2` case, this is *not* "`[n]` is unramified": a place lying over a closed point which is
  not the closed point of an `F`-rational point is untouched, and this tree has no proof that there
  are none.  Over `F̄` the two coincide, and every `[IsAlgClosed F]` statement here should be read
  that way.
* **No `hprin`.**  `…pullbackDivisorN_single_eq_sum_torsion` is the *fibre description*, which is
  one input to the rung-4 divisor identity; `exists_gS_n` is
  `EllipticCurves.FunctionField.NthRootOfPullbackN` and nothing in this file discharges it.
* **No new `E[n]` structure.**  `#E[n] = n²` at `3`-smooth `n` is the merged
  `card_torsion_eq_sq_of_smooth` (`EllipticCurves.Torsion.ThreePrimary`), consumed here and not
  reproved.

⚠️ **That pair is paid on both halves, and `(n : F) ≠ 0` is what is left.**  PR #557 proved the
on-curve identity for `(Φₙ/ΨSqₙ, ωₙ/ψₙ³)` at every index over every commutative ring
(`WeierstrassCurve.Affine.equation_div_of_ψ_ne_zero`, `EllipticCurves.Torsion.OmegaCrux`) — that was
`#404`, and it says only that those coordinates lie on the curve.  Identifying the `x`-coordinate
with the group-law multiple `n • P` is `#251`, and it is **closed**:
`WeierstrassCurve.Affine.hasXCoordFormula_of_two_ne_zero`
(`EllipticCurves.Torsion.NsmulOrder`) at every index over any field with `(2 : F) ≠ 0`, and in
function-field form `nMulRatFunc_eq_ΦDivΨSq`
(`EllipticCurves.FunctionField.MulByNXCoordFormula`) at every `n` with `(n : F) ≠ 0`.  ⚠️ **`#1184`
has since been discharged over a field** — `WeierstrassCurve.Affine.isCoprime_ΨSq_adjacent`
(`EllipticCurves.Torsion.CoprimeAdjacent`) at every `n : ℤ` for an elliptic curve of characteristic
`≠ 2` — so `[F(W) : [n]∗F(W)] = n²` at general `n`
(`EllipticCurves.FunctionField.MulByNDegreeGeneral`) is owed `(n : F) ≠ 0` and nothing else beyond
the `(2 : F) ≠ 0` and `[W.IsElliptic]` that this whole paragraph already carries.  ⚠️ The
arbitrary-**ring** form that `EllipticCurves.DivisionPolynomial.Coprime` states is still open.
⚠️ And the `y`-half — `ωₙ/(2ψₙ³)` as `y(n • P)` — **is closed too, at every index**:
`nsmul_eq_some_omegaY_of_ΨSq_ne_zero` (`EllipticCurves.Torsion.NsmulYPeriodic`, PR #579), under the
same `ΨSqₙ(x) ≠ 0` and `(2 : F) ≠ 0` the `x`-half asks.  ⚠️ So the whole *pair* is available at
every index, and the `#251` bullets on the Weil-pairing front no longer name an open gate.  ⚠️ None
of `EllipticCurves.Torsion.NsmulOrder`, `EllipticCurves.FunctionField.MulByNXCoordFormula`,
`EllipticCurves.Torsion.CoprimeAdjacent` or `EllipticCurves.FunctionField.MulByNDegreeGeneral` is in
this file's import closure and none is added: all four names are cited, not consumed.  The
two-reading account is `EllipticCurves.FunctionField.MulByNPullback`.

## References

* [J. H. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.4.10 and III.6.4 —
  `[n]` is surjective with kernel of order `n²` over an algebraically closed field, which is the
  statement `card_fibre_comapProjPointN_projPointOfPoint` is the function-field shadow of.
-/

open IsDedekindDomain

namespace WeierstrassCurve.Affine

namespace CoordinateRing

variable {F : Type*} [Field F] [DecidableEq F] {W : Affine F}
  [IsDedekindDomain W.CoordinateRing] [W.IsElliptic]

/-! ### The contraction at a rational point -/

/-- **`[2 ^ a · 3 ^ b]∗` contracts the place of `P` to the place of `(2 ^ a · 3 ^ b) • P`.**

Induction on `a` and then on `b`, **generalising over `P`** at both levels: each step peels one
prime off the index with `comapProjPointN_of_mul_eq` and lands the merged
`comapProjPointTwo_projPointOfPoint` / `comapProjPointThree_projPointOfPoint`, whose output is the
place of a *different* rational point.  See the module docstring on why that is the only difference
from `comapProjPointN_two_pow_mul_three_pow_none` and why it is the load-bearing one. -/
theorem comapProjPointN_two_pow_mul_three_pow_projPointOfPoint (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0)
    (a b : ℕ) (h : Transcendental F ((2 ^ a * 3 ^ b) • genericPoint (W := W)).xCoord)
    (P : W.Point) :
    comapProjPointN (2 ^ a * 3 ^ b) h (projPointOfPoint W P)
      = projPointOfPoint W ((2 ^ a * 3 ^ b) • P) := by
  induction a generalizing P with
  | zero =>
    induction b generalizing P with
    | zero => simpa using comapProjPointN_one h (projPointOfPoint W P)
    | succ b ih =>
      have hb := transcendental_xCoord_two_pow_mul_three_pow_nsmul (W := W) h2 h3 0 b
      rw [comapProjPointN_of_mul_eq (m := 3) (n := 2 ^ 0 * 3 ^ b) (by ring)
        (transcendental_xCoord_three_nsmul h2 h3) hb h, comapProjPointN_three h2 h3,
        comapProjPointThree_projPointOfPoint h2 h3, ih hb, smul_smul]
      ring_nf
  | succ a ih =>
    have ha := transcendental_xCoord_two_pow_mul_three_pow_nsmul (W := W) h2 h3 a b
    rw [comapProjPointN_of_mul_eq (m := 2) (n := 2 ^ a * 3 ^ b) (by ring)
      (transcendental_xCoord_two_nsmul h2) ha h, comapProjPointN_two h2,
      comapProjPointTwo_projPointOfPoint h2, ih ha, smul_smul]
    ring_nf

/-- **The place contraction of `[n]∗` on the rational locus is the group-theoretic `n •`**, at every
`3`-smooth `n ≠ 0`:

```
comapProjPointN n h (projPointOfPoint P) = projPointOfPoint (n • P).
```

The general-`n` form of `#774`'s `comapProjPointTwo_projPointOfPoint` and of
`comapProjPointThree_projPointOfPoint`, and the affine companion of `#1214`'s
`comapProjPointN_none_of_smooth`.  No case hypothesis on `P` and no torsion side condition. -/
theorem comapProjPointN_projPointOfPoint_of_smooth (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) {n : ℕ}
    (hn : n ≠ 0) (hfac : ∀ p ∈ n.primeFactors, p = 2 ∨ p = 3)
    (h : Transcendental F (n • genericPoint (W := W)).xCoord) (P : W.Point) :
    comapProjPointN n h (projPointOfPoint W P) = projPointOfPoint W (n • P) := by
  obtain ⟨a, b, rfl⟩ := Nat.exists_eq_two_pow_mul_three_pow n hn hfac
  exact comapProjPointN_two_pow_mul_three_pow_projPointOfPoint h2 h3 a b h P

omit [W.IsElliptic] in
/-- **`R ↦ P ⊕ R` is injective into the places**, for `R` ranging over `E[n]`: the group law is
cancellative and `projPointOfPoint` is injective.

⚠️ Stated at every `n`, with no hypothesis on `F` and none on the curve beyond what `W.Point`
needs.  The merged `projPointOfPoint_add_injective_two` and `…_three` are this statement with an
index their one-line proofs never use. -/
theorem projPointOfPoint_add_injective (n : ℕ) (P : W.Point) :
    Function.Injective fun R : W.torsion n => projPointOfPoint W (P + R) :=
  fun _ _ hEq => Subtype.ext (add_right_injective P (projPointOfPoint_injective hEq))

/-- **`P ⊕ R` lies over `n • P`, for every `R ∈ E[n]`**: the coset of `E[n]` through any `P` with
`n • P = S` sits inside the fibre over `S`.  This is the inclusion `⊇` of the fibre description; the
reverse is pure counting and needs `[IsAlgClosed F]`. -/
theorem comapProjPointN_add_torsion_of_smooth (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) {n : ℕ}
    (hn : n ≠ 0) (hfac : ∀ p ∈ n.primeFactors, p = 2 ∨ p = 3)
    (h : Transcendental F (n • genericPoint (W := W)).xCoord) {S P : W.Point} (hP : n • P = S)
    (R : W.torsion n) :
    comapProjPointN n h (projPointOfPoint W (P + R)) = projPointOfPoint W S := by
  rw [comapProjPointN_projPointOfPoint_of_smooth h2 h3 hn hfac h, smul_add, hP,
    mem_torsion_iff.mp R.2, add_zero]

/-! ### The fibre over `F̄`

⚠️ `[IsAlgClosed F]` enters twice in this section, independently: once so that every place is
rational and `∑ e_p · f_p` collapses to `∑ e_p` (`sum_ramificationIdxN_of_smooth`), and once so that
`[n]` is surjective on points (`nsmul_surjective_of_smooth`) and the coset exists at all.  Neither
use is removable by progress on the other. -/

section IsAlgClosed

variable [IsAlgClosed F]

omit [DecidableEq F] in
/-- **At most `n²` places lie over any place**, at every `3`-smooth `n ≠ 0` over `F̄`: `n²` positive
indices summing to `n²` (`sum_ramificationIdxN_of_smooth` against `ramificationIdxN_pos`).  The
general-`n` form of `card_fibre_comapProjPointTwo_le_four`. -/
theorem card_fibre_comapProjPointN_le_sq (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) {n : ℕ}
    (hn : n ≠ 0) (hfac : ∀ p ∈ n.primeFactors, p = 2 ∨ p = 3)
    (h : Transcendental F (n • genericPoint (W := W)).xCoord) (q : ProjPoint W) :
    (finite_comapProjPointN_preimage_singleton n h q).toFinset.card ≤ n ^ 2 := by
  classical
  rw [Finset.card_eq_sum_ones, ← sum_ramificationIdxN_of_smooth h2 h3 hn hfac h q]
  exact Finset.sum_le_sum fun p _ => by have := ramificationIdxN_pos n h p; omega

omit [DecidableEq F] in
/-- **The fibre of `[n]` over any rational point has exactly `n²` elements**, at every `3`-smooth
`n ≠ 0` over `F̄`.

`≥ n²` is the coset `{ P ⊕ R : R ∈ E[n] }` for a `P` with `n • P = S` (`exists_nsmul_eq_of_smooth`),
which has `n²` distinct elements by `card_torsion_eq_sq_of_smooth` and
`projPointOfPoint_add_injective` and lies in the fibre by `comapProjPointN_add_torsion_of_smooth`;
`≤ n²` is `card_fibre_comapProjPointN_le_sq`. -/
theorem card_fibre_comapProjPointN_projPointOfPoint (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) {n : ℕ}
    (hn : n ≠ 0) (hfac : ∀ p ∈ n.primeFactors, p = 2 ∨ p = 3)
    (h : Transcendental F (n • genericPoint (W := W)).xCoord) (S : W.Point) :
    (finite_comapProjPointN_preimage_singleton n h (projPointOfPoint W S)).toFinset.card
      = n ^ 2 := by
  classical
  haveI := W.finite_torsion_of_smooth h2 h3 hn hfac
  haveI := Fintype.ofFinite (W.torsion n)
  obtain ⟨P, hP⟩ := exists_nsmul_eq_of_smooth h2 hn hfac S
  refine le_antisymm (card_fibre_comapProjPointN_le_sq h2 h3 hn hfac h _) ?_
  have hcard : Fintype.card (W.torsion n) = n ^ 2 := by
    rw [← Nat.card_eq_fintype_card, card_torsion_eq_sq_of_smooth h2 h3 hn hfac]
  rw [← hcard, ← Finset.card_univ]
  exact Finset.card_le_card_of_injOn (fun R => projPointOfPoint W (P + R))
    (fun R _ => (Set.Finite.mem_toFinset _).2
      (comapProjPointN_add_torsion_of_smooth h2 h3 hn hfac h hP R))
    (Set.injOn_of_injective (projPointOfPoint_add_injective n P))

/-- **The fibre of `[n]` over a rational point *is* the coset `{ P ⊕ R : R ∈ E[n] }`**, for any `P`
with `n • P = S`.

The set-theoretic half of the fibre description at every `3`-smooth `n`.  The inclusion `⊇` is
`comapProjPointN_add_torsion_of_smooth`; the reverse is pure counting — `n²` distinct elements
inside an `n²`-element set, with no further geometry.

Stated with `Set.range` rather than a `Finset.image` because `ProjPoint W` carries no
`DecidableEq`, and baking a classical one into the statement would restrict who can apply it. -/
theorem fibre_comapProjPointN_eq_range (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) {n : ℕ}
    (hn : n ≠ 0) (hfac : ∀ p ∈ n.primeFactors, p = 2 ∨ p = 3)
    (h : Transcendental F (n • genericPoint (W := W)).xCoord) {S P : W.Point} (hP : n • P = S) :
    comapProjPointN n h ⁻¹' {projPointOfPoint W S}
      = Set.range fun R : W.torsion n => projPointOfPoint W (P + R) := by
  classical
  haveI := W.finite_torsion_of_smooth h2 h3 hn hfac
  haveI := Fintype.ofFinite (W.torsion n)
  have hfin := finite_comapProjPointN_preimage_singleton n h (projPointOfPoint W S)
  have hsub : (Set.range fun R : W.torsion n => projPointOfPoint W (P + R))
      ⊆ comapProjPointN n h ⁻¹' {projPointOfPoint W S} := by
    rintro p ⟨R, rfl⟩
    exact comapProjPointN_add_torsion_of_smooth h2 h3 hn hfac h hP R
  refine (Set.eq_of_subset_of_ncard_le hsub ?_ hfin).symm
  have hfibre : (comapProjPointN n h ⁻¹' {projPointOfPoint W S}).ncard = n ^ 2 := by
    rw [Set.ncard_eq_toFinset_card _ hfin]
    exact card_fibre_comapProjPointN_projPointOfPoint h2 h3 hn hfac h S
  have hcoset : (Set.range fun R : W.torsion n => projPointOfPoint W (P + R)).ncard = n ^ 2 := by
    rw [← Nat.card_coe_set_eq, Nat.card_range_of_injective (projPointOfPoint_add_injective n P),
      card_torsion_eq_sq_of_smooth h2 h3 hn hfac]
  omega

omit [DecidableEq F] in
/-- **`[n]` is unramified over every rational point**, at every `3`-smooth `n ≠ 0` over `F̄`: `n²`
positive indices summing to `n²` are all `1`.

⚠️ This is *not* "`[n]` is unramified": a place lying over a closed point that is **not** the closed
point of an `F`-rational point is untouched.  See the module docstring.  ⚠️ Nor is it removable to a
general `n`: `ramificationIdxN_none_of_smooth` records that `[p]` is ramified at infinity in
characteristic `p`, and the `3`-smoothness here is doing the same work. -/
theorem ramificationIdxN_eq_one_of_comapProjPointN_eq_projPointOfPoint (h2 : (2 : F) ≠ 0)
    (h3 : (3 : F) ≠ 0) {n : ℕ} (hn : n ≠ 0) (hfac : ∀ p ∈ n.primeFactors, p = 2 ∨ p = 3)
    (h : Transcendental F (n • genericPoint (W := W)).xCoord) {p : ProjPoint W} {S : W.Point}
    (hp : comapProjPointN n h p = projPointOfPoint W S) :
    ramificationIdxN n h p = 1 := by
  classical
  set s := (finite_comapProjPointN_preimage_singleton n h (projPointOfPoint W S)).toFinset with hs
  have hmem : p ∈ s := (Set.Finite.mem_toFinset _).2 hp
  have hcard : s.card = n ^ 2 := card_fibre_comapProjPointN_projPointOfPoint h2 h3 hn hfac h S
  have hsum : ∑ q ∈ s, (ramificationIdxN n h q).toNat = n ^ 2 :=
    sum_ramificationIdxN_of_smooth h2 h3 hn hfac h _
  have hsplit : (ramificationIdxN n h p).toNat
      + ∑ q ∈ s.erase p, (ramificationIdxN n h q).toNat = n ^ 2 := by
    rw [Finset.add_sum_erase _ (fun q => (ramificationIdxN n h q).toNat) hmem]
    exact hsum
  have hlow : (s.erase p).card ≤ ∑ q ∈ s.erase p, (ramificationIdxN n h q).toNat := by
    simpa using Finset.card_nsmul_le_sum (s.erase p) (fun q => (ramificationIdxN n h q).toNat) 1
      (fun q _ => by have := ramificationIdxN_pos n h q; omega)
  have hec : (s.erase p).card = n ^ 2 - 1 := by rw [Finset.card_erase_of_mem hmem, hcard]
  have hpos := ramificationIdxN_pos n h p
  have hone : 1 ≤ n ^ 2 := Nat.one_le_pow _ _ (Nat.pos_of_ne_zero hn)
  omega

omit [DecidableEq F] in
/-- **The fibre description of `[n]∗` over a rational point**: `[n]∗(S) = ∑_{p ↦ S} (p)`, every
coefficient `1`.

At `S = O` this is `comapProjPointN_none_of_smooth` and `ramificationIdxN_none_of_smooth`
(`EllipticCurves.FunctionField.MulByNPlaceComposition`) read as a divisor; at an affine `S` it is
new at every index outside `{2, 3}`.  The two together give

```
[n]∗((S) − (O)) = ∑_{p ↦ S} (p) − ∑_{p ↦ O} (p).
```
-/
theorem pullbackDivisorN_single_projPointOfPoint (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) {n : ℕ}
    (hn : n ≠ 0) (hfac : ∀ p ∈ n.primeFactors, p = 2 ∨ p = 3)
    (h : Transcendental F (n • genericPoint (W := W)).xCoord) (S : W.Point) :
    pullbackDivisorN n h (Finsupp.single (projPointOfPoint W S) (1 : ℤ))
      = ∑ p ∈ (finite_comapProjPointN_preimage_singleton n h
          (projPointOfPoint W S)).toFinset, Finsupp.single p (1 : ℤ) := by
  classical
  ext q
  have hrhs : (∑ p ∈ (finite_comapProjPointN_preimage_singleton n h
        (projPointOfPoint W S)).toFinset, Finsupp.single p (1 : ℤ)) q
      = if comapProjPointN n h q = projPointOfPoint W S then 1 else 0 := by
    rw [Finset.sum_apply', Finset.sum_congr rfl fun p _ => Finsupp.single_apply,
      Finset.sum_ite_eq' _ q fun _ => (1 : ℤ)]
    simp only [Set.Finite.mem_toFinset, Set.mem_preimage, Set.mem_singleton_iff]
  rw [pullbackDivisorN_apply, hrhs]
  by_cases hq : comapProjPointN n h q = projPointOfPoint W S
  · rw [hq, Finsupp.single_eq_same, mul_one,
      ramificationIdxN_eq_one_of_comapProjPointN_eq_projPointOfPoint h2 h3 hn hfac h hq, if_pos rfl]
  · rw [Finsupp.single_apply, if_neg fun hc => hq hc.symm, mul_zero, if_neg hq]

/-- **The fibre description in the shape a rung-4 consumer wants**: for any `P` with `n • P = S`,

```
[n]∗(S) = ∑_{R ∈ E[n]} (P ⊕ R).
```

Subtracting the same statement at `S = O` (where `P` may be taken to be `O`, so that the sum is
`∑_R (R)`) gives `[n]∗((S) − (O)) = ∑_{R ∈ E[n]} ((P ⊕ R) − (R))` — `#774`'s formula at every
`3`-smooth `n`.

The `[Fintype (W.torsion n)]` is carried in the statement rather than produced inside it: the sum
cannot be written without it, and pushing `Fintype.ofFinite` into a statement is the noncomputable
leak `#763` warns against.  `finite_torsion_of_smooth` supplies it at the point of use. -/
theorem pullbackDivisorN_single_eq_sum_torsion (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) {n : ℕ}
    [Fintype (W.torsion n)] (hn : n ≠ 0) (hfac : ∀ p ∈ n.primeFactors, p = 2 ∨ p = 3)
    (h : Transcendental F (n • genericPoint (W := W)).xCoord) {S P : W.Point} (hP : n • P = S) :
    pullbackDivisorN n h (Finsupp.single (projPointOfPoint W S) (1 : ℤ))
      = ∑ R : W.torsion n, Finsupp.single (projPointOfPoint W (P + R)) (1 : ℤ) := by
  classical
  ext q
  rw [pullbackDivisorN_apply, Finset.sum_apply',
    Finset.sum_congr rfl fun R _ => Finsupp.single_apply]
  by_cases hq : comapProjPointN n h q = projPointOfPoint W S
  · obtain ⟨R₀, hR₀⟩ : q ∈ Set.range fun R : W.torsion n => projPointOfPoint W (P + R) := by
      rw [← fibre_comapProjPointN_eq_range h2 h3 hn hfac h hP]; exact hq
    rw [hq, Finsupp.single_eq_same, mul_one,
      ramificationIdxN_eq_one_of_comapProjPointN_eq_projPointOfPoint h2 h3 hn hfac h hq,
      Finset.sum_eq_single R₀ (fun R _ hRne => if_neg fun hc =>
        hRne (projPointOfPoint_add_injective n P (hc.trans hR₀.symm)))
      (fun hc => absurd (Finset.mem_univ R₀) hc), if_pos hR₀]
  · rw [Finsupp.single_apply, if_neg fun hc => hq hc.symm, mul_zero, Finset.sum_eq_zero]
    intro R _
    refine if_neg fun hc => hq ?_
    rw [← hc]
    exact comapProjPointN_add_torsion_of_smooth h2 h3 hn hfac h hP R

/-! ### Non-vacuity

⚠️ Every statement in this file carries `[IsDedekindDomain W.CoordinateRing]` and `[W.IsElliptic]`
on top of a non-constancy hypothesis, and the `F̄` block adds `[IsAlgClosed F]` and `3`-smoothness;
a theorem whose hypotheses could not all be met at once would be vacuous.  One curve on which the
whole chain elaborates, at an index outside `{2, 3}`, is committed rather than quoted.

⚠️ The non-constancy hypothesis is **produced**, never assumed:
`transcendental_xCoord_nsmul_of_smooth` at `n = 12`. -/

section Nonvacuity

/-! The certificate curve `y² + y = x³` is the shared `EllipticCurves.Fixture.y2AddYEqX3`, and the
base — algebraically closed, and of characteristic `0` so that `2 ≠ 0` and `3 ≠ 0` — is
`EllipticCurves.Fixture.AlgClosedQ`, whose single `[CharZero F]` instance also supplies
`IsElliptic` here. -/

open EllipticCurves.Fixture

private noncomputable instance : DecidableEq AlgClosedQ := Classical.decEq _

private lemma exampleFibreTwo : (2 : AlgClosedQ) ≠ 0 := two_ne_zero

private lemma exampleFibreThree : (3 : AlgClosedQ) ≠ 0 := three_ne_zero_of_charZero _

/-- ⚠️ `decide` does **not** close this: `Nat.primeFactors` goes through `Nat.primeFactorsList`,
whose `Decidable` instance gets stuck on `Nat.minFac`'s well-founded recursion. -/
private lemma smoothTwelveFibre : ∀ p ∈ Nat.primeFactors 12, p = 2 ∨ p = 3 := by
  intro p hp
  obtain ⟨hp1, hp2, -⟩ := Nat.mem_primeFactors.mp hp
  have hle : p ≤ 12 := Nat.le_of_dvd (by norm_num) hp2
  interval_cases p <;> revert hp1 hp2 <;> decide

example : IsDedekindDomain (y2AddYEqX3 AlgClosedQ).CoordinateRing := inferInstance

/-- **The contraction at `n = 12`, committed** — an index at which neither merged computation says
anything. -/
example (P : (y2AddYEqX3 AlgClosedQ).Point) :
    comapProjPointN 12 (transcendental_xCoord_nsmul_of_smooth (W := y2AddYEqX3 AlgClosedQ)
        exampleFibreTwo exampleFibreThree (by norm_num) smoothTwelveFibre)
      (projPointOfPoint (y2AddYEqX3 AlgClosedQ) P)
      = projPointOfPoint (y2AddYEqX3 AlgClosedQ) ((12 : ℕ) • P) :=
  comapProjPointN_projPointOfPoint_of_smooth exampleFibreTwo exampleFibreThree (by norm_num)
    smoothTwelveFibre _ P

/-- **`#{p ↦ S} = 144` at `n = 12`, committed** — the fibre count, on a genuine curve. -/
example (S : (y2AddYEqX3 AlgClosedQ).Point) :
    (finite_comapProjPointN_preimage_singleton 12
      (transcendental_xCoord_nsmul_of_smooth (W := y2AddYEqX3 AlgClosedQ) exampleFibreTwo
        exampleFibreThree (by norm_num) smoothTwelveFibre)
      (projPointOfPoint (y2AddYEqX3 AlgClosedQ) S)).toFinset.card = 144 := by
  have h144 := card_fibre_comapProjPointN_projPointOfPoint (W := y2AddYEqX3 AlgClosedQ)
      exampleFibreTwo
    exampleFibreThree (n := 12) (by norm_num) smoothTwelveFibre
    (transcendental_xCoord_nsmul_of_smooth (W := y2AddYEqX3 AlgClosedQ) exampleFibreTwo
      exampleFibreThree (by norm_num) smoothTwelveFibre) S
  norm_num at h144
  exact h144

end Nonvacuity

end IsAlgClosed

end CoordinateRing

end WeierstrassCurve.Affine
