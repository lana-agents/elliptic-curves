/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import EllipticCurves.FunctionField.MulByTwoPlaceAtInfinity
import EllipticCurves.FunctionField.PlaceRamificationInertia
import EllipticCurves.FunctionField.TranslationProjAction

/-!
# The fibre of `[2]` over the point at infinity, and the first computed affine ramification indices

`#670` (`EllipticCurves.FunctionField.MulByTwoPlaceAtInfinity`) showed that `[2]` fixes the point at
infinity and is unramified there.  `#763`
(`EllipticCurves.FunctionField.PlaceRamificationInertia`) showed that the ramification indices over
any place of `[2]∗F(W)` sum to `4` and that a fibre has at most four elements.  This file identifies
the fibre over the point at infinity completely:

```
comapProjPointTwo h2 ⁻¹' {none} = {none} ∪ { closed point of (x, twoTorsionY x) : Ψ₂Sq.eval x = 0 }
```

which over an algebraically closed base field has **exactly four** elements — and therefore, against
`#763`'s identity, **every ramification index on it is `1`**.

This is the fibre description of `#774` at the point at infinity: the `(O)` half of
`[2]∗((S) − (O)) = ∑_{R ∈ E[2]} ((P ⊕ R) − (R))`.

## ⚠️ This corrects five merged docstrings: `[2]` does **not** ramify at the `2`-torsion points

`MulByTwoPlaceAtInfinity`, `MulByTwoPullbackDivisor` and `PullbackDivisor` each said, in some
wording, that `[2]` "genuinely ramifies at the `2`-torsion points" in characteristic `≠ 2`.  That is
**false**, and `ramificationIdxTwo_pointClosedPoint_of_eval_Ψ₂Sq_eq_zero` below is the
counterexample: over an algebraically closed base field the index is `1` at every affine
`2`-torsion point.

The claim is the ramification of a *different* map.  `x ∘ [2] : ℙ¹ → ℙ¹` has degree `4` and does
ramify over the `2`-torsion `x`-values — `Ψ₂Sq` vanishes there, which is exactly what
`ord_mulByTwoEndo_genX_neg` uses.  But `[2] : E → E` is a separable isogeny, its fibres have as many
points as its degree, and it is unramified.  The two get conflated because the duplication formula
is written on the `x`-line.

⚠️ What is **not** claimed here is that `[2]` is unramified *everywhere*.  Only the fibre over the
point at infinity is computed; over an affine place nothing in this tree computes an index, and the
five docstrings have been rewritten to say that rather than deleted.

## The argument

Two steps, and neither needs the `y`-coordinate of the duplication formula — which is why this half
of `#774` is cheap and the affine half is not.

1. **`comapProjPointTwo_pointClosedPoint_of_eval_Ψ₂Sq_eq_zero`.**  `x ∘ [2] = Φ₂(x)/Ψ₂Sq(x)`
   (`mulByTwoEndo_genX`).  At a root of `Ψ₂Sq` the denominator vanishes and the numerator does not,
   because `Φ₂` and `Ψ₂Sq` are coprime with Bézout constant `Δ²` (`#681`) and `Δ` is a unit.  So
   `x ∘ [2]` has a *pole* at every affine `2`-torsion place.  Running
   `divisorProj_mulByTwoEndo_apply` at `genX` then forces the contracted place to be `none`, since
   `x` has no pole at any affine place and the ramification index is positive.  **This is
   `comapProjPointTwo_none`'s argument (`#670`) run at an affine place instead of at infinity.**
2. **The count.**  Distinct roots of `Ψ₂Sq` give distinct closed points
   (`eq_of_pointClosedPoint_eq`), `Ψ₂Sq` has exactly three roots over an algebraically closed field
   of characteristic `≠ 2` (`card_roots_Ψ₂Sq`), and `none` is a fourth element of the fibre
   (`comapProjPointTwo_none`).  With `#763`'s `card_fibre_comapProjPointTwo_le_four` the fibre has
   exactly four elements, and with `sum_ramificationIdxTwo_eq_four` each index is `1`.

## Main results

* `WeierstrassCurve.Affine.ord_algebraMap_pos_iff` — `ord v g > 0` exactly when `g ∈ v`, for `g` in
  the coordinate ring.  The strict companion of `ord_algebraMap_nonneg`, and general;
* `WeierstrassCurve.eval_Φ_two_ne_zero_of_eval_Ψ₂Sq_eq_zero` — `Φ₂` does not vanish at a root of
  `Ψ₂Sq`;
* **`comapProjPointTwo_pointClosedPoint_of_eval_Ψ₂Sq_eq_zero`** (in
  `WeierstrassCurve.Affine.CoordinateRing`) — `[2]` contracts every affine `2`-torsion place to the
  place at infinity.  No hypothesis on `F`;
* **`WeierstrassCurve.Affine.CoordinateRing.card_fibre_comapProjPointTwo_none`** — over
  `[IsAlgClosed F]`, the fibre over the point at infinity has exactly four elements;
* **`ramificationIdxTwo_eq_one_of_comapProjPointTwo_eq_none`** and
  `ramificationIdxTwo_pointClosedPoint_of_eval_Ψ₂Sq_eq_zero` — every index on that fibre is `1`.
  **The first
  computed values of `ramificationIdxTwo` at an affine place in this tree**;
* **`WeierstrassCurve.Affine.CoordinateRing.pullbackDivisorTwo_single_none`** —
  `[2]∗(O) = ∑_{p ↦ O} (p)`, the fibre description of `#774` at the point at infinity.

## What is *not* here

* **The affine half of `#774`**: `comapProjPointTwo h2 (some (pointClosedPoint h_P))` for a `P` that
  is *not* `2`-torsion.  Not here — but no longer unbuilt: it is
  `EllipticCurves.FunctionField.MulByTwoFibreAffine`, which also subsumes everything below into the
  single statement `comapProjPointTwo (projPointOfPoint P) = projPointOfPoint (2 • P)`.
  ⚠️ Earlier wording said the `y`-coordinate of the duplication formula "exists in this tree **only
  at the generic point** … and specialising it to a closed point is unbuilt".  Both halves have gone
  false: `EllipticCurves.Torsion.DoublingCoords` has it at a closed point, and specialising was not
  what produced it — the generic proof was never generic.  See that file.
* Therefore also the full fibre description `[2]∗((S) − (O)) = ∑_{R ∈ E[2]} ((P ⊕ R) − (R))` — again
  not here, and again merged, as `pullbackDivisorTwo_single_eq_sum_torsion` in
  `MulByTwoFibreAffine`.
  `#418`'s `hprin` is **still open**: what remains of it is the class-group computation, not a
  geometric fact.
* `ramificationIdxTwo` at a place lying over an *affine* place.  Nothing *here* computes one, and
  the argument above genuinely does not reach them: it runs on `genX`, whose only pole is at
  infinity.  `MulByTwoFibreAffine` does compute them, over every rational point.
* **`#E[2] = 4` from any of this.**  The count `card_torsion_two` is an *input* to step 2 by way of
  `card_roots_Ψ₂Sq`, not an output.  The link from the field degree to a point count runs through
  "a separable isogeny has `#ker = deg`", which is nowhere in this tree.
* `[3]∗`.  Step 1 transposes once `Φ₃`/`ΨSq₃` coprimality is available in the same form, but
  `#763`'s right-hand side `4` is `[2]`-specific, so step 2 does not.

## References

* [J. H. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.4.10 and III.8.
-/

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum FractionalIdeal Polynomial

namespace WeierstrassCurve

variable {F : Type*} [Field F]

/-- **`Φ₂` does not vanish at a root of `Ψ₂Sq`.**  The two are coprime with Bézout constant `Δ²`
(`bezout_Φ_two_Ψ₂Sq`, `#681`), and `Δ` is a unit on an elliptic curve, so the Bézout identity
evaluated at a root of `Ψ₂Sq` reads `bezoutΦTwo(x) · Φ₂(x) = Δ²`. -/
theorem eval_Φ_two_ne_zero_of_eval_Ψ₂Sq_eq_zero (W : WeierstrassCurve F) [W.IsElliptic] {x : F}
    (hx : W.Ψ₂Sq.eval x = 0) : (W.Φ 2).eval x ≠ 0 := by
  intro h
  have hb := congrArg (Polynomial.eval x) W.bezout_Φ_two_Ψ₂Sq
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, h, hx,
    mul_zero, add_zero] at hb
  exact (pow_ne_zero 2 W.isUnit_Δ.ne_zero) hb.symm

end WeierstrassCurve

namespace WeierstrassCurve.Affine

variable {F : Type*} [Field F] {W : Affine F} [IsDedekindDomain W.CoordinateRing]

/-! ### Order at a closed point, and membership of its ideal

`ord v` is nonnegative on the coordinate ring (`ord_algebraMap_nonneg`, `PlaceAtInfinity.lean`);
what is needed below is the sharper statement that it is *strictly* positive exactly on `v`.  That
is `ValuationSubringDedekind.lean`'s `mem_asIdeal_iff_mem_nonunits` read through `PlaceOrder.lean`'s
`mem_valuationSubringAtPrime_iff_ord_nonneg`.  Nothing in this section mentions `[2]`. -/

/-- **`ord v g > 0` exactly when `g` lies in `v`**, for `g` in the coordinate ring.  Together with
`ord_algebraMap_nonneg` this pins the order of a regular function at a closed point: it is `0` off
`v` and positive on it. -/
theorem ord_algebraMap_pos_iff (v : HeightOneSpectrum W.CoordinateRing) {g : W.CoordinateRing}
    (hg : g ≠ 0) :
    0 < ord v (algebraMap W.CoordinateRing W.FunctionField g) ↔ g ∈ v.asIdeal := by
  rw [mem_asIdeal_iff_mem_nonunits (K := W.FunctionField), ValuationSubring.mem_nonunits_iff_or]
  constructor
  · intro h
    exact Or.inr fun hmem => absurd
      ((mem_valuationSubringAtPrime_iff_ord_nonneg v
        (inv_ne_zero (by simpa using hg))).1 hmem) (by rw [ord_inv]; omega)
  · rintro (h | h)
    · exact absurd h (by simpa using hg)
    · by_contra hc
      exact h ((mem_valuationSubringAtPrime_iff_ord_nonneg v
        (inv_ne_zero (by simpa using hg))).2 (by rw [ord_inv]; omega))

/-- **A regular function not vanishing at `v` has order `0` there.** -/
theorem ord_algebraMap_eq_zero_of_notMem (v : HeightOneSpectrum W.CoordinateRing)
    {g : W.CoordinateRing} (hg : g ∉ v.asIdeal) :
    ord v (algebraMap W.CoordinateRing W.FunctionField g) = 0 := by
  have hg0 : g ≠ 0 := fun h => hg (h ▸ Ideal.zero_mem _)
  have hnn := ord_algebraMap_nonneg v g
  have hnp : ¬ 0 < ord v (algebraMap W.CoordinateRing W.FunctionField g) :=
    fun h => hg ((ord_algebraMap_pos_iff v hg0).1 h)
  omega

namespace CoordinateRing

variable {x y : F}

/-- **The order of `q(x)` at a closed point is positive exactly when `q` kills its
`x`-coordinate.**  `q(genX)` is the class of the constant bivariate polynomial `C q`
(`genPsi_mk_C_eq_eval_map`), whose image under `evalEvalHom` is `q.eval x`, and the closed-point
ideal is that kernel (`ker_evalEvalHom`). -/
theorem ord_eval_map_genX_pos_iff (h : W.Equation x y) {q : F[X]} (hq : q ≠ 0) :
    0 < ord (pointClosedPoint h) ((q.map (algebraMap F W.FunctionField)).eval (genX W))
      ↔ q.eval x = 0 := by
  rw [← genPsi_mk_C_eq_eval_map, genPsi, ord_algebraMap_pos_iff _ (mk_C_ne_zero hq),
    pointClosedPoint_asIdeal, ← ker_evalEvalHom h, RingHom.mem_ker, evalEvalHom_mk, evalEval_C]

/-- **A polynomial in the generic `x`-coordinate is regular at every affine place.** -/
theorem ord_eval_map_genX_nonneg (v : HeightOneSpectrum W.CoordinateRing) (q : F[X]) :
    0 ≤ ord v ((q.map (algebraMap F W.FunctionField)).eval (genX W)) := by
  rw [← genPsi_mk_C_eq_eval_map, genPsi]
  exact ord_algebraMap_nonneg v _

/-- The scalar `4` is nonzero when `2` is: this is what makes `Ψ₂Sq` a genuine cubic. -/
private lemma four_ne_zero_of_two_ne_zero (h2 : (2 : F) ≠ 0) : (4 : F) ≠ 0 := by
  have h : (4 : F) = 2 * 2 := by norm_num
  rw [h]
  exact mul_ne_zero h2 h2

/-! ### `[2]` carries the affine `2`-torsion to the point at infinity -/

/-- **`x ∘ [2]` has a pole at every affine `2`-torsion point.**  The duplication formula is
`x ∘ [2] = Φ₂(x)/Ψ₂Sq(x)`; at a root of `Ψ₂Sq` the denominator vanishes and the numerator does not
(`eval_Φ_two_ne_zero_of_eval_Ψ₂Sq_eq_zero`). -/
theorem ord_mulByTwoEndo_genX_neg [W.IsElliptic] (h2 : (2 : F) ≠ 0) (h : W.Equation x y)
    (hx : W.Ψ₂Sq.eval x = 0) :
    ord (pointClosedPoint h) (mulByTwoEndo h2 (genX W)) < 0 := by
  have h4 : (4 : F) ≠ 0 := four_ne_zero_of_two_ne_zero h2
  have hΦ : ((W.map (algebraMap F W.FunctionField)).Φ 2)
      = (W.Φ 2).map (algebraMap F W.FunctionField) := map_Φ ..
  have hΨ : ((W.map (algebraMap F W.FunctionField)).Ψ₂Sq)
      = W.Ψ₂Sq.map (algebraMap F W.FunctionField) := map_Ψ₂Sq ..
  have hΦ0 : ord (pointClosedPoint h)
      (((W.Φ 2).map (algebraMap F W.FunctionField)).eval (genX W)) = 0 := by
    have hnn := ord_eval_map_genX_nonneg (pointClosedPoint h) (W.Φ 2)
    have hnp : ¬ 0 < ord (pointClosedPoint h)
        (((W.Φ 2).map (algebraMap F W.FunctionField)).eval (genX W)) := by
      rw [ord_eval_map_genX_pos_iff h (W.Φ_ne_zero 2)]
      exact W.eval_Φ_two_ne_zero_of_eval_Ψ₂Sq_eq_zero hx
    omega
  have hΨ0 : 0 < ord (pointClosedPoint h)
      ((W.Ψ₂Sq.map (algebraMap F W.FunctionField)).eval (genX W)) :=
    (ord_eval_map_genX_pos_iff h (W.Ψ₂Sq_ne_zero h4)).2 hx
  rw [mulByTwoEndo_genX h2, hΦ, hΨ, ord_div _ (eval_map_genX_ne_zero (W.Φ_ne_zero 2))
    (eval_map_genX_ne_zero (W.Ψ₂Sq_ne_zero h4)), hΦ0]
  omega

/-- **`[2]` contracts every affine `2`-torsion place to the place at infinity.**

The affine half of the geometric statement that `[2]` maps `E[2]` to `O`, read on places.  The
argument is `comapProjPointTwo_none`'s (`#670`), run at an affine place instead of at infinity:
`x ∘ [2]` has a pole there (`ord_mulByTwoEndo_genX_neg`), `x` has none at any affine place, and the
ramification index is positive, so the contracted place cannot be affine.

No hypothesis on `F` beyond `(2 : F) ≠ 0`. -/
theorem comapProjPointTwo_pointClosedPoint_of_eval_Ψ₂Sq_eq_zero [W.IsElliptic] (h2 : (2 : F) ≠ 0)
    (h : W.Equation x y) (hx : W.Ψ₂Sq.eval x = 0) :
    comapProjPointTwo h2 (some (pointClosedPoint h)) = none := by
  have hkey := divisorProj_mulByTwoEndo_apply h2 (f := genX W) genX_ne_zero
    (some (pointClosedPoint h))
  rw [divisorProj_apply_some] at hkey
  cases hq : comapProjPointTwo h2 (some (pointClosedPoint h)) with
  | none => rfl
  | some v =>
    exfalso
    rw [hq, divisorProj_apply_some] at hkey
    have hlt := ord_mulByTwoEndo_genX_neg h2 h hx
    have hge : (0 : ℤ) ≤ ord v (genX W) := by
      rw [genX, genPsi]
      exact ord_algebraMap_nonneg v _
    have hnn : (0 : ℤ) ≤ ramificationIdxTwo h2 (some (pointClosedPoint h)) * ord v (genX W) :=
      mul_nonneg (ramificationIdxTwo_pos h2 _).le hge
    omega

/-! ### The fibre over the point at infinity, and its four elements -/

variable [W.IsElliptic] (h2 : (2 : F) ≠ 0)

/-- **The place of the affine `2`-torsion point above a root of `Ψ₂Sq`.** -/
noncomputable def twoTorsionProjPoint (r : {x : F // W.Ψ₂Sq.eval x = 0}) : ProjPoint W :=
  some (pointClosedPoint (equation_twoTorsionY h2 r.2))

omit [W.IsElliptic] in
/-- Distinct roots of `Ψ₂Sq` give distinct places: `eq_of_pointClosedPoint_eq`. -/
theorem twoTorsionProjPoint_injective : Function.Injective (twoTorsionProjPoint (W := W) h2) := by
  intro r r' hr
  rw [twoTorsionProjPoint, twoTorsionProjPoint, Option.some_inj] at hr
  exact Subtype.ext (eq_of_pointClosedPoint_eq _ _ hr).1

omit [W.IsElliptic] in
theorem twoTorsionProjPoint_ne_none (r : {x : F // W.Ψ₂Sq.eval x = 0}) :
    twoTorsionProjPoint h2 r ≠ none := by
  rw [twoTorsionProjPoint]
  exact Option.some_ne_none _

/-- Every affine `2`-torsion place lies over the point at infinity. -/
theorem comapProjPointTwo_twoTorsionProjPoint (r : {x : F // W.Ψ₂Sq.eval x = 0}) :
    comapProjPointTwo h2 (twoTorsionProjPoint h2 r) = none :=
  comapProjPointTwo_pointClosedPoint_of_eval_Ψ₂Sq_eq_zero h2 _ r.2

section IsAlgClosed

variable [IsAlgClosed F]

/-- **The fibre of `[2]` over the point at infinity has exactly four elements.**

`≤ 4` is `#763`'s `card_fibre_comapProjPointTwo_le_four`; `≥ 4` is `none` together with the three
roots of `Ψ₂Sq` (`card_roots_Ψ₂Sq`), which give distinct places by
`twoTorsionProjPoint_injective`. -/
theorem card_fibre_comapProjPointTwo_none :
    (finite_comapProjPointTwo_preimage_singleton h2 (none : ProjPoint W)).toFinset.card = 4 := by
  classical
  haveI : Finite {x : F // W.Ψ₂Sq.eval x = 0} := finite_roots_Ψ₂Sq h2
  haveI := Fintype.ofFinite {x : F // W.Ψ₂Sq.eval x = 0}
  refine le_antisymm (card_fibre_comapProjPointTwo_le_four h2 none) ?_
  have hcard : Fintype.card (Option {x : F // W.Ψ₂Sq.eval x = 0}) = 4 := by
    rw [Fintype.card_option, ← Nat.card_eq_fintype_card, card_roots_Ψ₂Sq h2]
  rw [← hcard, ← Finset.card_univ]
  refine Finset.card_le_card_of_injOn
    (fun o => o.elim (none : ProjPoint W) (twoTorsionProjPoint h2)) (fun o _ => ?_) ?_
  · cases o with
    | none => exact (Set.Finite.mem_toFinset _).2 (comapProjPointTwo_none h2)
    | some r => exact (Set.Finite.mem_toFinset _).2 (comapProjPointTwo_twoTorsionProjPoint h2 r)
  · rintro (_ | r) - (_ | r') - hEq
    · rfl
    · exact absurd hEq.symm (twoTorsionProjPoint_ne_none h2 r')
    · exact absurd hEq (twoTorsionProjPoint_ne_none h2 r)
    · exact congrArg _ (twoTorsionProjPoint_injective h2 hEq)

open scoped Classical in
/-- **`[2]` is unramified at every place above the point at infinity.**

Four positive indices summing to `4` (`#763`'s `sum_ramificationIdxTwo_eq_four` against
`card_fibre_comapProjPointTwo_none`) are all `1`.  **No ramification is computed directly**: the
index is pinned by the count, which is what `#763` bought. -/
theorem ramificationIdxTwo_eq_one_of_comapProjPointTwo_eq_none {p : ProjPoint W}
    (hp : comapProjPointTwo h2 p = none) : ramificationIdxTwo h2 p = 1 := by
  set s := (finite_comapProjPointTwo_preimage_singleton h2 (none : ProjPoint W)).toFinset with hs
  have hmem : p ∈ s := (Set.Finite.mem_toFinset _).2 hp
  have hcard : s.card = 4 := card_fibre_comapProjPointTwo_none h2
  have hsum : ∑ q ∈ s, (ramificationIdxTwo h2 q).toNat = 4 :=
    sum_ramificationIdxTwo_eq_four h2 none
  have hsplit : (ramificationIdxTwo h2 p).toNat
      + ∑ q ∈ s.erase p, (ramificationIdxTwo h2 q).toNat = 4 := by
    rw [Finset.add_sum_erase _ (fun q => (ramificationIdxTwo h2 q).toNat) hmem]
    exact hsum
  have hlow : (s.erase p).card ≤ ∑ q ∈ s.erase p, (ramificationIdxTwo h2 q).toNat := by
    have hone := Finset.card_nsmul_le_sum (s.erase p)
      (fun q => (ramificationIdxTwo h2 q).toNat) 1
      (fun q _ => by have := ramificationIdxTwo_pos h2 q; omega)
    simpa using hone
  have hec : (s.erase p).card = 3 := by rw [Finset.card_erase_of_mem hmem, hcard]
  have hpos := ramificationIdxTwo_pos h2 p
  omega

/-- **`[2]` is unramified at every affine `2`-torsion point.**

⚠️ This is the counterexample to the "`[2]` genuinely ramifies at the `2`-torsion points" claim that
`MulByTwoPlaceAtInfinity`, `MulByTwoPullbackDivisor` and `PullbackDivisor` carried.  What ramifies
there is `x ∘ [2] : ℙ¹ → ℙ¹`, not `[2] : E → E`; see the module docstring.

These are the first computed values of `ramificationIdxTwo` at an affine place in this tree. -/
theorem ramificationIdxTwo_pointClosedPoint_of_eval_Ψ₂Sq_eq_zero {x y : F} (h : W.Equation x y)
    (hx : W.Ψ₂Sq.eval x = 0) :
    ramificationIdxTwo h2 (some (pointClosedPoint h)) = 1 :=
  ramificationIdxTwo_eq_one_of_comapProjPointTwo_eq_none h2
    (comapProjPointTwo_pointClosedPoint_of_eval_Ψ₂Sq_eq_zero h2 h hx)

open scoped Classical in
/-- **The fibre description of `[2]∗` at the point at infinity**: `[2]∗(O) = ∑_{p ↦ O} (p)`, with
every coefficient `1`.

This is `#774`'s deliverable 2 at `q = none` — the `(O)` half of
`[2]∗((S) − (O)) = ∑_{R ∈ E[2]} ((P ⊕ R) − (R))`.  The `(S)` half needs the affine fibre, which is
not here. -/
theorem pullbackDivisorTwo_single_none :
    pullbackDivisorTwo h2 (Finsupp.single (none : ProjPoint W) (1 : ℤ))
      = ∑ p ∈ (finite_comapProjPointTwo_preimage_singleton h2 (none : ProjPoint W)).toFinset,
          Finsupp.single p (1 : ℤ) := by
  ext q
  have hrhs : (∑ p ∈ (finite_comapProjPointTwo_preimage_singleton h2
        (none : ProjPoint W)).toFinset, Finsupp.single p (1 : ℤ)) q
      = if comapProjPointTwo h2 q = none then 1 else 0 := by
    rw [Finset.sum_apply', Finset.sum_congr rfl fun p _ => Finsupp.single_apply,
      Finset.sum_ite_eq' _ q fun _ => (1 : ℤ)]
    simp only [Set.Finite.mem_toFinset, Set.mem_preimage, Set.mem_singleton_iff]
  rw [pullbackDivisorTwo_apply, hrhs]
  by_cases hq : comapProjPointTwo h2 q = none
  · rw [hq, Finsupp.single_eq_same, mul_one,
      ramificationIdxTwo_eq_one_of_comapProjPointTwo_eq_none h2 hq, if_pos rfl]
  · rw [Finsupp.single_apply, if_neg fun hc => hq hc.symm, mul_zero, if_neg hq]

end IsAlgClosed

/-! ### Non-vacuity

Every statement above carries `[IsDedekindDomain W.CoordinateRing]` and `[W.IsElliptic]`, and the
headline additionally needs `[IsAlgClosed F]`.  `y² = x³ − x` over `AlgebraicClosure ℚ` is the curve
`#758`/`#759`/`#763` use, for the same reason: the `ℚ` curve of the rest of `FunctionField/` cannot
witness a statement that needs an algebraically closed base field. -/

section Nonvacuity

/-- An algebraically closed field of characteristic zero. -/
private abbrev exampleField : Type := AlgebraicClosure ℚ

/-- The curve `y² = x³ - x` over `AlgebraicClosure ℚ`, of discriminant `64`. -/
private noncomputable def exampleCurve : Affine exampleField := ⟨0, 0, 0, -1, 0⟩

private instance : exampleCurve.IsElliptic := by
  rw [WeierstrassCurve.isElliptic_iff, isUnit_iff_ne_zero]
  norm_num [exampleCurve, WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈]

private lemma exampleTwo : (2 : exampleField) ≠ 0 := by norm_num

/-- **The fibre over infinity has four elements, on a curve that exists.** -/
example :
    (finite_comapProjPointTwo_preimage_singleton exampleTwo
      (none : ProjPoint exampleCurve)).toFinset.card = 4 :=
  card_fibre_comapProjPointTwo_none exampleTwo

/-- **`[2]` is unramified above infinity, on the same curve.** -/
example {p : ProjPoint exampleCurve} (hp : comapProjPointTwo exampleTwo p = none) :
    ramificationIdxTwo exampleTwo p = 1 :=
  ramificationIdxTwo_eq_one_of_comapProjPointTwo_eq_none exampleTwo hp

/-- The fibre description at the point at infinity, on the same curve. -/
example :
    pullbackDivisorTwo exampleTwo (Finsupp.single (none : ProjPoint exampleCurve) (1 : ℤ))
      = ∑ p ∈ (finite_comapProjPointTwo_preimage_singleton exampleTwo
          (none : ProjPoint exampleCurve)).toFinset, Finsupp.single p (1 : ℤ) :=
  pullbackDivisorTwo_single_none exampleTwo

end Nonvacuity

end CoordinateRing

end WeierstrassCurve.Affine
