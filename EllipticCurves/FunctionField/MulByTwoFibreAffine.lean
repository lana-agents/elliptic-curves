/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import EllipticCurves.FunctionField.MulByTwoFibreInfinity
import EllipticCurves.Torsion.DoublingCoords

/-!
# The place contraction of `[2]` **is** `[2]` on points, and the fibre over a rational point

`#670` showed that `[2]` fixes the point at infinity, and `#774`'s first half
(`EllipticCurves.FunctionField.MulByTwoFibreInfinity`) showed that it carries every affine
`2`-torsion place there.  Both are instances of one statement, which is what this file proves:

```
comapProjPointTwo h2 (projPointOfPoint P) = projPointOfPoint (2 • P)
```

for **every** `P : W.Point`.  The place contraction of the multiplication-by-`2` pullback, read on
the rational locus of `ProjPoint W`, is the group-theoretic doubling map — no case hypothesis, no
`2`-torsion side condition.

From it the fibre over any rational point of `ProjPoint W` is computed: it is `{ P ⊕ R : R ∈ E[2] }`
for any `P` with `2 • P = S`, it has exactly four elements over an algebraically closed base field,
and therefore — against `#763`'s `∑_{p ↦ q} e_p = 4` — every ramification index on it is `1` and

```
[2]∗(S) = ∑_{p ↦ S} (p).
```

At `S = O` this recovers `pullbackDivisorTwo_single_none`; at an affine `S` it is the `(S)` half of
`#774`'s fibre description `[2]∗((S) − (O)) = ∑_{R ∈ E[2]} ((P ⊕ R) − (R))`, which is the last
input `#418`'s `hprin` was waiting on.

## What made this possible, and it is not what `#774` predicted

`#774` named the `y`-coordinate of the duplication formula **at a closed point** as the open
question, observing that this tree had it only at the generic point (`addY_gen_eq_mulByTwo`) and
that its proof runs `linear_combination` under `set_option maxRecDepth 8000`, so specialising it
might be hard.

It is not hard, because **that proof was never generic**: its only inputs are the Weierstrass
equation at the point, `ψ₂ ≠ 0` at the point, and `2 ≠ 0`.  `EllipticCurves.Torsion.DoublingCoords`
records the transcription and the moral.  The `x`-coordinate `#774` expected to be free was free
(`addX_self_mul_Ψ₂Sq_eval`), and the `±S` ambiguity it warned about is resolved exactly as it said
it must be — by the `y`-coordinate, not by a shortcut.

## The shape of the argument

Given the two coordinate identities, the place statement is an ideal computation and needs no
valuation theory beyond what is merged:

1. `[2]∗` is determined on the generators.  `mulByTwoCoordHom_XClass` and `mulByTwoCoordHom_YClass`
   say that `[2]∗` applied to `X - x₂` and to `Y - y₂` is `x ∘ [2] - x₂` and `y ∘ [2] - y₂`.
2. Each of those *vanishes at `P`*, by the duplication formulas — this is where `DoublingCoords`
   enters, and it is the only place it enters.
3. `divisorProj_mulByTwoEndo_apply` transports "vanishes at `P`" across the contraction: with
   `e_p > 0`, `ord_P([2]∗g) > 0` iff `ord_q(g) > 0`, i.e. iff `g` lies in the contracted place.
4. So the contracted prime contains `⟨X - x₂, Y - y₂⟩ = ker (evalEvalHom h₂)`, which is maximal;
   a prime containing a maximal ideal and not equal to `⊤` **is** it.

## Main results

* `WeierstrassCurve.Affine.CoordinateRing.projPointOfPoint` — the rational locus of `ProjPoint W`,
  as a map from `W.Point`: `O ↦ none` and an affine point to its closed point.  Injective;
* `WeierstrassCurve.Affine.CoordinateRing.comapProjPointTwo_pointClosedPoint` — the crux, at an
  affine point that is not `2`-torsion.  **No hypothesis on `F` beyond `(2 : F) ≠ 0`**, and not even
  `[W.IsElliptic]`;
* **`WeierstrassCurve.Affine.CoordinateRing.comapProjPointTwo_projPointOfPoint`** — the uniform
  statement, for every `P : W.Point`;
* `card_fibre_comapProjPointTwo_projPointOfPoint` — over an algebraically closed base field, the
  fibre over any rational point has exactly four elements;
* `fibre_comapProjPointTwo_eq_range` — and it *is* the coset `{ P ⊕ R : R ∈ E[2] }`;
* `ramificationIdxTwo_eq_one_of_comapProjPointTwo_eq_projPointOfPoint` — hence every ramification
  index over a rational point is `1`;
* `pullbackDivisorTwo_single_projPointOfPoint` — hence `[2]∗(S) = ∑_{p ↦ S} (p)`;
* **`pullbackDivisorTwo_single_eq_sum_torsion`** — the same, indexed by `E[2]`:
  `[2]∗(S) = ∑_{R ∈ E[2]} (P ⊕ R)` for any `P` with `2 • P = S`.  This is `#774`'s formula.

## What is *not* here

* **`hprin`, and therefore `#418`.**  The fibre description is an input to the class-group
  computation `∑_R toClass (P ⊕ R) − ∑_R toClass R = 4 · toClass P = toClass ([2]S) = 0`, not the
  computation itself.  This file unblocks `#418`; it does not discharge it.  The computation is
  `EllipticCurves.FunctionField.PullbackPrincipalityTwo` (`#791`), which consumes this file.
* **The fibre over a place that is not the closed point of an `F`-rational point.**  Over an
  algebraically closed base field every closed point *ought* to be rational, but that is a
  Nullstellensatz statement about `HeightOneSpectrum W.CoordinateRing` and it is **nowhere in this
  tree**.  So "`[2]` is unramified" is proved here over the rational locus and only there; do not
  read the results below as an unramifiedness statement about `[2]` tout court.
* **`#E[2] = 4` from any of this.**  `card_torsion_two` is an *input* to the counting, exactly as in
  `MulByTwoFibreInfinity`.  The missing link from a field degree to a kernel count is still
  "a separable isogeny has `#ker = deg`", which no file in this tree contains.
* `[3]∗`.  Steps 1–4 above **have** been transposed, in
  `EllipticCurves.FunctionField.MulByThreeFibre`, which proves the same uniform statement
  `comapProjPointThree (projPointOfPoint P) = projPointOfPoint (3 • P)` and the fibre description
  over a rational point.  ⚠️ Its step 2 is stated about the *division form* `Φ₃(x)/ΨSq₃(x)` rather
  than about `addX`/`addY` of a tripling, which is why it needs no tripling formula at all;
  `EllipticCurves.Torsion.TriplingCoords` enters one layer up, where the closed point of those
  coordinates is identified with the closed point of `3 • P`.
  ⚠️ The counting does *not* transpose.  The fibre here is the coset `{P ⊕ R : R ∈ E[2]}`, one
  point per root of `Ψ₂Sq`, because negation **fixes** the `2`-torsion points.  A `3`-torsion point
  is not `2`-torsion, so each of the four roots of `Ψ₃` carries **two** points and the count there
  is `1 + 2·4 = 9`, reached as a coset of `E[3]` rather than one point per root.
* General `[n]∗`.  `mulByNEndo` does not exist, and `#763`'s right-hand side `4` is `[2]`-specific
  (its `n = 3` counterpart is `EllipticCurves.FunctionField.MulByThreeRamification`'s `9`).

## References

* [J. H. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.2.3, III.4.10, III.8.1.
-/

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum Polynomial

open scoped Polynomial.Bivariate

namespace WeierstrassCurve.Affine.CoordinateRing

variable {F : Type*} [Field F] [DecidableEq F] {W : Affine F}
  [IsDedekindDomain W.CoordinateRing] {x y : F}

/-! ### Order at a closed point of a fraction of coordinate functions -/

omit [DecidableEq F] in
/-- **`ord_p g > 0` exactly when `g` vanishes at `p`**, for `g` in the coordinate ring and `p` the
closed point of an affine point.  `ord_algebraMap_pos_iff` read through `ker_evalEvalHom`. -/
theorem ord_genPsi_pos_iff (h : W.Equation x y) {g : W.CoordinateRing} (hg : g ≠ 0) :
    0 < ord (pointClosedPoint h) (genPsi W g) ↔ evalEvalHom h g = 0 := by
  rw [genPsi, ord_algebraMap_pos_iff _ hg, pointClosedPoint_asIdeal, ← ker_evalEvalHom h,
    RingHom.mem_ker]

omit [DecidableEq F] in
/-- A coordinate function not vanishing at an affine point has order `0` there. -/
theorem ord_genPsi_eq_zero (h : W.Equation x y) {g : W.CoordinateRing}
    (hg : evalEvalHom h g ≠ 0) : ord (pointClosedPoint h) (genPsi W g) = 0 := by
  refine ord_algebraMap_eq_zero_of_notMem _ ?_
  rw [pointClosedPoint_asIdeal, ← ker_evalEvalHom h, RingHom.mem_ker]
  exact hg

omit [DecidableEq F] in
/-- **A fraction of coordinate functions vanishes where its numerator does.**  If a nonzero `f` is
`n(x, y) / d(x, y)` for bivariate `n`, `d` with `n(P) = 0` and `d(P) ≠ 0`, then `ord_P f > 0`.

The nonvanishing of `f` is what supplies `n ≠ 0`; asking for it is cheaper than a degree argument,
since the two numerators used below are values of an injective ring homomorphism. -/
theorem ord_pos_of_eq_evalEval_div (h : W.Equation x y) {f : W.FunctionField} (hf : f ≠ 0)
    {n d : F[X][Y]}
    (hfe : f = (n.map (mapRingHom (algebraMap F W.FunctionField))).evalEval (genX W) (genY W) /
      (d.map (mapRingHom (algebraMap F W.FunctionField))).evalEval (genX W) (genY W))
    (hn0 : n.evalEval x y = 0) (hd0 : d.evalEval x y ≠ 0) :
    0 < ord (pointClosedPoint h) f := by
  rw [← genPsi_mk_map_evalEval, ← genPsi_mk_map_evalEval] at hfe
  have hd : mk W d ≠ 0 := fun hz => hd0 (by rw [← evalEvalHom_mk (h := h), hz, map_zero])
  have hdi : genPsi W (mk W d) ≠ 0 := fun hz => hd
    ((injective_iff_map_eq_zero _).mp
      (IsFractionRing.injective W.CoordinateRing W.FunctionField) _ hz)
  have hni : genPsi W (mk W n) ≠ 0 := fun hz => hf (by rw [hfe, hz, zero_div])
  have hn : mk W n ≠ 0 := fun hz => hni (by rw [hz, map_zero])
  rw [hfe, ord_div _ hni hdi,
    ord_genPsi_eq_zero (g := mk W d) h (by rwa [evalEvalHom_mk]), sub_zero]
  exact (ord_genPsi_pos_iff h hn).2 (by rwa [evalEvalHom_mk])

/-! ### `[2]∗` on the two generators of a closed point -/

omit [DecidableEq F] [IsDedekindDomain W.CoordinateRing] in
/-- `[2]∗(X - x₂) = x ∘ [2] - x₂`. -/
theorem mulByTwoCoordHom_XClass (h2 : (2 : F) ≠ 0) (x₂ : F) :
    mulByTwoCoordHom h2 (XClass W x₂)
      = mulByTwoEndo h2 (genX W) - algebraMap F W.FunctionField x₂ := by
  rw [← mulByTwoEndo_algebraMap h2, ← genPsi, XClass, C_sub, map_sub, map_sub,
    genPsi_mk_CC, ← genX, map_sub, mulByTwoEndo_algebraMap_base]

omit [DecidableEq F] [IsDedekindDomain W.CoordinateRing] in
/-- `[2]∗(Y - y₂) = y ∘ [2] - y₂`. -/
theorem mulByTwoCoordHom_YClass (h2 : (2 : F) ≠ 0) (y₂ : F) :
    mulByTwoCoordHom h2 (YClass W (C y₂))
      = mulByTwoEndo h2 (genY W) - algebraMap F W.FunctionField y₂ := by
  rw [← mulByTwoEndo_algebraMap h2, ← genPsi, YClass, map_sub, map_sub, genPsi_mk_CC,
    show mk W Y = AdjoinRoot.root W.polynomial from rfl, ← genY, map_sub,
    mulByTwoEndo_algebraMap_base]

/-! ### The two generators of the doubled point vanish at `P` -/

/-- **`x ∘ [2] - x(2P)` vanishes at `P`.**  The duplication formula `addX_self_mul_Ψ₂Sq_eval`, read
through the presentation `x ∘ [2] = Φ₂(x)/Ψ₂Sq(x)`. -/
theorem ord_mulByTwoCoordHom_XClass_pos (h2 : (2 : F) ≠ 0) (h : W.Equation x y)
    (hy : y ≠ W.negY x y) :
    0 < ord (pointClosedPoint h)
      (mulByTwoCoordHom h2 (XClass W (W.addX x x (W.slope x x y y)))) := by
  have h4 : (4 : F) ≠ 0 := by
    have hh : (4 : F) = 2 * 2 := by norm_num
    rw [hh]; exact mul_ne_zero h2 h2
  have hΨ0 : W.Ψ₂Sq.eval x ≠ 0 := by
    rw [Ψ₂Sq_eval_eq_sq h]
    exact pow_ne_zero 2 (two_mul_add_ne_zero_of_Y_ne hy)
  have hB : (W.Ψ₂Sq.map (algebraMap F W.FunctionField)).eval (genX W) ≠ 0 :=
    eval_map_genX_ne_zero (W.Ψ₂Sq_ne_zero h4)
  refine ord_pos_of_eq_evalEval_div h ?_
    (n := C (W.Φ 2 - C (W.addX x x (W.slope x x y y)) * W.Ψ₂Sq)) (d := C W.Ψ₂Sq) ?_ ?_ ?_
  · exact fun hz => XClass_ne_zero (W' := W) _
      (mulByTwoCoordHom_injective h2 (by rw [hz, map_zero]))
  · rw [mulByTwoCoordHom_XClass, mulByTwoEndo_genX, map_Φ, map_Ψ₂Sq]
    simp only [Polynomial.map_C, coe_mapRingHom, evalEval_C, Polynomial.map_sub,
      Polynomial.map_mul, eval_sub, eval_mul, eval_C]
    field_simp
  · simp only [evalEval_C, eval_sub, eval_mul, eval_C]
    rw [sub_eq_zero]
    exact (addX_self_mul_Ψ₂Sq_eval h hy).symm
  · simpa only [evalEval_C] using hΨ0

/-- **`y ∘ [2] - y(2P)` vanishes at `P`.**  The `y`-coordinate duplication formula
`addY_self_eq_div`, read through the presentation `y ∘ [2] = ω₂/(2 ψ₂³)`.  This is the step
`#774` could not price. -/
theorem ord_mulByTwoCoordHom_YClass_pos (h2 : (2 : F) ≠ 0) (h : W.Equation x y)
    (hy : y ≠ W.negY x y) :
    0 < ord (pointClosedPoint h)
      (mulByTwoCoordHom h2 (YClass W (C (W.addY x x y (W.slope x x y y))))) := by
  have hs0 : (W.ψ 2).evalEval x y ≠ 0 := by
    rw [ψ_two_evalEval]; exact two_mul_add_ne_zero_of_Y_ne hy
  refine ord_pos_of_eq_evalEval_div h ?_
    (n := C W.preΨ₄ - W.ψ 2 * C (C W.a₁ * W.Φ 2 + C W.a₃ * W.Ψ₂Sq)
      - C (C (W.addY x x y (W.slope x x y y))) * (2 * W.ψ 2 ^ 3))
    (d := 2 * W.ψ 2 ^ 3) ?_ ?_ ?_
  · exact fun hz => YClass_ne_zero (W' := W) _
      (mulByTwoCoordHom_injective h2 (by rw [hz, map_zero]))
  · have hψg : ((W.ψ 2).map (mapRingHom (algebraMap F W.FunctionField))).evalEval
        (genX W) (genY W) ≠ 0 := by rw [← map_ψ]; exact psiTwo_gen_ne h2
    have h2' : (2 : W.FunctionField) ≠ 0 := fun hz =>
      h2 ((algebraMap F W.FunctionField).injective (by rw [map_ofNat, map_zero]; exact hz))
    rw [mulByTwoCoordHom_YClass, mulByTwoEndo_genY]
    simp only [map_ψ, map_preΨ₄, map_Φ, map_Ψ₂Sq, map_a₁, map_a₃, Polynomial.map_sub,
      Polynomial.map_mul, Polynomial.map_add, Polynomial.map_pow, Polynomial.map_C,
      Polynomial.map_ofNat, coe_mapRingHom, evalEval, eval_sub, eval_mul, eval_add, eval_pow,
      eval_C, eval_ofNat] at hψg ⊢
    field_simp
  · have hd0 : 2 * (W.ψ 2).evalEval x y ^ 3 ≠ 0 :=
      mul_ne_zero (by norm_num [h2]) (pow_ne_zero 3 hs0)
    have hkey := addY_self_eq_div h h2 hy
    rw [eq_div_iff hd0] at hkey
    have hpsi : eval x (eval (C y) (W.ψ 2)) = (W.ψ 2).evalEval x y := rfl
    simp only [evalEval, eval_sub, eval_mul, eval_add, eval_pow, eval_C, eval_ofNat]
    rw [sub_eq_zero, hpsi]
    linear_combination -hkey
  · simp only [evalEval, eval_mul, eval_pow, eval_ofNat]
    exact mul_ne_zero (by norm_num [h2]) (pow_ne_zero 3 hs0)

/-! ### The contraction at an affine point that is not `2`-torsion -/

omit [DecidableEq F] in
/-- `x ∘ [2]` is regular at an affine point that is not `2`-torsion: its denominator `Ψ₂Sq(x)` does
not vanish there.  The counterpart of `MulByTwoFibreInfinity`'s
`ord_mulByTwoEndo_genX_neg`, on the other side of the `2`-torsion locus. -/
theorem ord_mulByTwoEndo_genX_nonneg (h2 : (2 : F) ≠ 0) (h : W.Equation x y)
    (hy : y ≠ W.negY x y) :
    0 ≤ ord (pointClosedPoint h) (mulByTwoEndo h2 (genX W)) := by
  have h4 : (4 : F) ≠ 0 := by
    have hh : (4 : F) = 2 * 2 := by norm_num
    rw [hh]; exact mul_ne_zero h2 h2
  have hΨ0 : W.Ψ₂Sq.eval x ≠ 0 := by
    rw [Ψ₂Sq_eval_eq_sq h]
    exact pow_ne_zero 2 (two_mul_add_ne_zero_of_Y_ne hy)
  have hΨ : ord (pointClosedPoint h)
      ((W.Ψ₂Sq.map (algebraMap F W.FunctionField)).eval (genX W)) = 0 := by
    have hnn := ord_eval_map_genX_nonneg (W := W) (pointClosedPoint h) W.Ψ₂Sq
    have hnp : ¬ 0 < ord (pointClosedPoint h)
        ((W.Ψ₂Sq.map (algebraMap F W.FunctionField)).eval (genX W)) := by
      rw [ord_eval_map_genX_pos_iff h (W.Ψ₂Sq_ne_zero h4)]
      exact hΨ0
    omega
  have hΦ := ord_eval_map_genX_nonneg (W := W) (pointClosedPoint h) (W.Φ 2)
  rw [mulByTwoEndo_genX, map_Φ, map_Ψ₂Sq, ord_div _ (eval_map_genX_ne_zero (W.Φ_ne_zero 2))
    (eval_map_genX_ne_zero (W.Ψ₂Sq_ne_zero h4)), hΨ]
  omega

/-- **The crux: `[2]` on places is `[2]` on points at an affine non-`2`-torsion point.**

For `P = (x, y)` on `W` with `y ≠ negY x y`, the contraction of the closed point of `P` along
`[2]∗` is the closed point of `2 • P`, whose coordinates are Mathlib's `addX`/`addY` of `P` with
itself (`Point.add_self_of_Y_ne`).

The `2`-torsion case is `MulByTwoFibreInfinity`'s
`comapProjPointTwo_pointClosedPoint_of_eval_Ψ₂Sq_eq_zero`, and `comapProjPointTwo_none` (`#670`) is
the case `P = O`; `comapProjPointTwo_projPointOfPoint` below assembles all three.

No hypothesis on `F` beyond `(2 : F) ≠ 0`, and — unlike the `2`-torsion case, which needs
`Φ₂ ≠ 0` at a root of `Ψ₂Sq` and hence `IsUnit Δ` — no `[W.IsElliptic]`. -/
theorem comapProjPointTwo_pointClosedPoint (h2 : (2 : F) ≠ 0) (h : W.Equation x y)
    (hy : y ≠ W.negY x y) :
    comapProjPointTwo h2 (some (pointClosedPoint h))
      = some (pointClosedPoint (W.equation_add h h fun hxy => hy hxy.right)) := by
  set h₂ := W.equation_add h h fun hxy => hy hxy.right with hh2def
  have hX := ord_mulByTwoCoordHom_XClass_pos h2 h hy
  have hY := ord_mulByTwoCoordHom_YClass_pos h2 h hy
  cases hq : comapProjPointTwo h2 (some (pointClosedPoint h)) with
  | none =>
    exfalso
    have hkey := divisorProj_mulByTwoEndo_apply h2 (f := genX W) genX_ne_zero
      (some (pointClosedPoint h))
    rw [divisorProj_apply_some, hq, divisorProj_apply_none, ordInfty_genX] at hkey
    have hpos := ramificationIdxTwo_pos h2 (some (pointClosedPoint h))
    have hnn := ord_mulByTwoEndo_genX_nonneg h2 h hy
    rw [hkey] at hnn
    nlinarith [hpos, hnn]
  | some v =>
    have hmem : ∀ g : W.CoordinateRing, g ≠ 0 →
        0 < ord (pointClosedPoint h) (mulByTwoCoordHom h2 g) → g ∈ v.asIdeal := by
      intro g hg hgpos
      have hkey := divisorProj_mulByTwoEndo_apply h2 (f := genPsi W g)
        (fun hz => hg ((injective_iff_map_eq_zero _).mp
          (IsFractionRing.injective W.CoordinateRing W.FunctionField) _ hz))
        (some (pointClosedPoint h))
      rw [divisorProj_apply_some, hq, divisorProj_apply_some, genPsi,
        mulByTwoEndo_algebraMap] at hkey
      have hpos := ramificationIdxTwo_pos h2 (some (pointClosedPoint h))
      rw [hkey] at hgpos
      refine (ord_algebraMap_pos_iff v hg).1 ?_
      nlinarith [hpos, hgpos]
    have hle : (pointClosedPoint h₂).asIdeal ≤ v.asIdeal := by
      rw [pointClosedPoint_asIdeal, XYIdeal, Ideal.span_le]
      rintro g (rfl | rfl)
      · exact hmem _ (XClass_ne_zero _) hX
      · exact hmem _ (YClass_ne_zero _) hY
    have hmax : (pointClosedPoint h₂).asIdeal.IsMaximal :=
      Ideal.IsPrime.isMaximal (pointClosedPoint h₂).isPrime (pointClosedPoint h₂).ne_bot
    exact congrArg some (HeightOneSpectrum.ext (hmax.eq_of_le v.isPrime.ne_top hle).symm)

/-! ### The rational locus of `ProjPoint W`, and the uniform statement -/

variable (W) in
/-- **The place of a rational point**: the point at infinity goes to `none`, an affine point to its
closed point.  The image is the *rational locus* of `ProjPoint W`; a height-one prime with a
nontrivial residue extension is not of this form, and nothing below says anything about one. -/
noncomputable def projPointOfPoint : W.Point → ProjPoint W
  | .zero => none
  | .some _ _ h => some (pointClosedPoint h.left)

omit [DecidableEq F] in
@[simp] theorem projPointOfPoint_zero :
    projPointOfPoint W (0 : W.Point) = none := rfl

omit [DecidableEq F] in
@[simp] theorem projPointOfPoint_some (h : W.Nonsingular x y) :
    projPointOfPoint W (Point.some x y h) = some (pointClosedPoint h.left) := rfl

omit [DecidableEq F] in
/-- **Distinct rational points have distinct places** — `eq_of_pointClosedPoint_eq` with the point
at infinity folded in.  Without this the identifications below would carry no information. -/
theorem projPointOfPoint_injective : Function.Injective (projPointOfPoint W) := by
  rintro (_ | ⟨x₁, y₁, h₁⟩) (_ | ⟨x₂, y₂, h₂⟩) hEq
  · rfl
  · exact absurd hEq (by simp [projPointOfPoint])
  · exact absurd hEq (by simp [projPointOfPoint])
  · obtain ⟨hx, hy⟩ := eq_of_pointClosedPoint_eq h₁.left h₂.left (Option.some.inj hEq)
    subst hx
    subst hy
    rfl

variable [W.IsElliptic]

/-- **The place contraction of `[2]∗` is the doubling map, on the whole rational locus.**

```
comapProjPointTwo h2 (projPointOfPoint P) = projPointOfPoint (2 • P)
```

with no case hypothesis.  The three cases are `comapProjPointTwo_none` (`#670`, `P = O`),
`comapProjPointTwo_pointClosedPoint_of_eval_Ψ₂Sq_eq_zero` (`#774`'s first half, `P` affine
`2`-torsion) and `comapProjPointTwo_pointClosedPoint` above (`P` affine, not `2`-torsion) — the
last of which is what did not exist before.

This is deliverable 1 of `#774`, and the sentence its title asks for: *`comapProjPointTwo` on
points **is** `[2]` on points.* -/
theorem comapProjPointTwo_projPointOfPoint (h2 : (2 : F) ≠ 0) (P : W.Point) :
    comapProjPointTwo h2 (projPointOfPoint W P) = projPointOfPoint W (2 • P) := by
  rcases P with _ | ⟨x, y, hns⟩
  · rw [← Point.zero_def, smul_zero, projPointOfPoint_zero]
    exact comapProjPointTwo_none h2
  · by_cases hy : y = W.negY x y
    · have hzero : (2 : ℕ) • Point.some x y hns = 0 := by
        rw [two_nsmul]; exact Point.add_self_of_Y_eq hy
      have hΨ : W.Ψ₂Sq.eval x = 0 := by
        rw [Ψ₂Sq_eval_eq_sq hns.left]
        rw [negY] at hy
        exact pow_eq_zero_iff (n := 2) (by norm_num) |>.2 (by linear_combination hy)
      rw [hzero, projPointOfPoint_zero, projPointOfPoint_some]
      exact comapProjPointTwo_pointClosedPoint_of_eval_Ψ₂Sq_eq_zero h2 hns.left hΨ
    · rw [two_nsmul, Point.add_self_of_Y_ne hy, projPointOfPoint_some, projPointOfPoint_some]
      exact comapProjPointTwo_pointClosedPoint h2 hns.left hy


/-! ### The fibre over a rational point, and the divisor identity -/

section IsAlgClosed

variable [IsAlgClosed F]

omit [IsAlgClosed F] in
/-- **`P ⊕ R` lies over `2 • P`, for every `R ∈ E[2]`.**  The four preimages of a rational point,
exhibited as a coset of `E[2]`. -/
theorem comapProjPointTwo_add_torsion_two (h2 : (2 : F) ≠ 0) {S P : W.Point} (hP : 2 • P = S)
    (R : W.torsion 2) :
    comapProjPointTwo h2 (projPointOfPoint W (P + R)) = projPointOfPoint W S := by
  rw [comapProjPointTwo_projPointOfPoint h2, smul_add, hP, mem_torsion_iff.mp R.2, add_zero]

omit [W.IsElliptic] [IsAlgClosed F] in
/-- **`R ↦ P ⊕ R` is injective into the places**, for `R` ranging over `E[2]`: the group law is
cancellative and `projPointOfPoint` is injective. -/
theorem projPointOfPoint_add_injective (P : W.Point) :
    Function.Injective fun R : W.torsion 2 => projPointOfPoint W (P + R) :=
  fun _ _ hEq => Subtype.ext (add_right_injective P (projPointOfPoint_injective hEq))

omit [DecidableEq F] in
/-- **The fibre of `[2]` over any rational point has exactly four elements.**

`≥ 4` is `{ P ⊕ R : R ∈ E[2] }` for a `P` with `2 • P = S` (`exists_nsmul_two_eq`), four distinct
elements by `card_torsion_two` and `projPointOfPoint_add_injective`, all in the fibre by
`comapProjPointTwo_add_torsion_two`; `≤ 4` is `#763`'s `card_fibre_comapProjPointTwo_le_four`.

At `S = O` this is `MulByTwoFibreInfinity`'s `card_fibre_comapProjPointTwo_none` reproved
uniformly — there the four preimages are the roots of `Ψ₂Sq` together with `none`, here a coset of
`E[2]`. -/
theorem card_fibre_comapProjPointTwo_projPointOfPoint (h2 : (2 : F) ≠ 0) (S : W.Point) :
    (finite_comapProjPointTwo_preimage_singleton h2 (projPointOfPoint W S)).toFinset.card = 4 := by
  classical
  haveI := W.finite_torsion_two (F := F) h2
  haveI := Fintype.ofFinite (W.torsion 2)
  obtain ⟨P, hP⟩ := exists_nsmul_two_eq h2 S
  refine le_antisymm (card_fibre_comapProjPointTwo_le_four h2 _) ?_
  have hcard : Fintype.card (W.torsion 2) = 4 := by
    rw [← Nat.card_eq_fintype_card, card_torsion_two h2]
  rw [← hcard, ← Finset.card_univ]
  exact Finset.card_le_card_of_injOn (fun R => projPointOfPoint W (P + R))
    (fun R _ => (Set.Finite.mem_toFinset _).2 (comapProjPointTwo_add_torsion_two h2 hP R))
    (Set.injOn_of_injective (projPointOfPoint_add_injective P))

/-- **The fibre of `[2]` over a rational point *is* the coset `{ P ⊕ R : R ∈ E[2] }`**, for any `P`
with `2 • P = S`.

This is the set-theoretic half of `#774`'s title.  The inclusion `⊇` is
`comapProjPointTwo_add_torsion_two`; the reverse is pure counting — four distinct elements inside a
four-element set, with no further geometry.

Stated with `Set.range` rather than a `Finset.image` because `ProjPoint W` carries no `DecidableEq`,
and baking a classical one into the statement would restrict who can apply it. -/
theorem fibre_comapProjPointTwo_eq_range (h2 : (2 : F) ≠ 0) {S P : W.Point} (hP : 2 • P = S) :
    comapProjPointTwo h2 ⁻¹' {projPointOfPoint W S}
      = Set.range fun R : W.torsion 2 => projPointOfPoint W (P + R) := by
  classical
  haveI := W.finite_torsion_two h2
  haveI := Fintype.ofFinite (W.torsion 2)
  have hfin := finite_comapProjPointTwo_preimage_singleton h2 (projPointOfPoint W S)
  have hsub : (Set.range fun R : W.torsion 2 => projPointOfPoint W (P + R))
      ⊆ comapProjPointTwo h2 ⁻¹' {projPointOfPoint W S} := by
    rintro p ⟨R, rfl⟩
    exact comapProjPointTwo_add_torsion_two h2 hP R
  refine (Set.eq_of_subset_of_ncard_le hsub ?_ hfin).symm
  have h1 : (comapProjPointTwo h2 ⁻¹' {projPointOfPoint W S}).ncard = 4 := by
    rw [Set.ncard_eq_toFinset_card _ hfin]
    exact card_fibre_comapProjPointTwo_projPointOfPoint h2 S
  have h2' : (Set.range fun R : W.torsion 2 => projPointOfPoint W (P + R)).ncard = 4 := by
    rw [← Nat.card_coe_set_eq, Nat.card_range_of_injective (projPointOfPoint_add_injective P),
      card_torsion_two h2]
  omega

omit [DecidableEq F] in
/-- **`[2]` is unramified over every rational point.**  Four positive indices summing to `4`
(`#763`'s `sum_ramificationIdxTwo_eq_four` against the count above) are all `1`.

⚠️ This is *not* "`[2]` is unramified": a place lying over a closed point that is **not** the closed
point of an `F`-rational point is untouched, and this tree has no proof that there are none.  See
the module docstring. -/
theorem ramificationIdxTwo_eq_one_of_comapProjPointTwo_eq_projPointOfPoint (h2 : (2 : F) ≠ 0)
    {p : ProjPoint W} {S : W.Point} (hp : comapProjPointTwo h2 p = projPointOfPoint W S) :
    ramificationIdxTwo h2 p = 1 := by
  classical
  set s := (finite_comapProjPointTwo_preimage_singleton h2 (projPointOfPoint W S)).toFinset with hs
  have hmem : p ∈ s := (Set.Finite.mem_toFinset _).2 hp
  have hcard : s.card = 4 := card_fibre_comapProjPointTwo_projPointOfPoint h2 S
  have hsum : ∑ q ∈ s, (ramificationIdxTwo h2 q).toNat = 4 :=
    sum_ramificationIdxTwo_eq_four h2 _
  have hsplit : (ramificationIdxTwo h2 p).toNat
      + ∑ q ∈ s.erase p, (ramificationIdxTwo h2 q).toNat = 4 := by
    rw [Finset.add_sum_erase _ (fun q => (ramificationIdxTwo h2 q).toNat) hmem]
    exact hsum
  have hlow : (s.erase p).card ≤ ∑ q ∈ s.erase p, (ramificationIdxTwo h2 q).toNat := by
    simpa using Finset.card_nsmul_le_sum (s.erase p) (fun q => (ramificationIdxTwo h2 q).toNat) 1
      (fun q _ => by have := ramificationIdxTwo_pos h2 q; omega)
  have hec : (s.erase p).card = 3 := by rw [Finset.card_erase_of_mem hmem, hcard]
  have hpos := ramificationIdxTwo_pos h2 p
  omega

omit [DecidableEq F] in
/-- **The fibre description of `[2]∗` over a rational point**: `[2]∗(S) = ∑_{p ↦ S} (p)`, every
coefficient `1`.

At `S = O` this is `pullbackDivisorTwo_single_none`; at an affine `S` it is the `(S)` half of
`#774`'s description, and the two together give

```
[2]∗((S) − (O)) = ∑_{p ↦ S} (p) − ∑_{p ↦ O} (p).
```

`pullbackDivisorTwo_single_eq_sum_torsion` rewrites each fibre as a sum over `E[2]`. -/
theorem pullbackDivisorTwo_single_projPointOfPoint (h2 : (2 : F) ≠ 0) (S : W.Point) :
    pullbackDivisorTwo h2 (Finsupp.single (projPointOfPoint W S) (1 : ℤ))
      = ∑ p ∈ (finite_comapProjPointTwo_preimage_singleton h2
          (projPointOfPoint W S)).toFinset, Finsupp.single p (1 : ℤ) := by
  classical
  ext q
  have hrhs : (∑ p ∈ (finite_comapProjPointTwo_preimage_singleton h2
        (projPointOfPoint W S)).toFinset, Finsupp.single p (1 : ℤ)) q
      = if comapProjPointTwo h2 q = projPointOfPoint W S then 1 else 0 := by
    rw [Finset.sum_apply', Finset.sum_congr rfl fun p _ => Finsupp.single_apply,
      Finset.sum_ite_eq' _ q fun _ => (1 : ℤ)]
    simp only [Set.Finite.mem_toFinset, Set.mem_preimage, Set.mem_singleton_iff]
  rw [pullbackDivisorTwo_apply, hrhs]
  by_cases hq : comapProjPointTwo h2 q = projPointOfPoint W S
  · rw [hq, Finsupp.single_eq_same, mul_one,
      ramificationIdxTwo_eq_one_of_comapProjPointTwo_eq_projPointOfPoint h2 hq, if_pos rfl]
  · rw [Finsupp.single_apply, if_neg fun hc => hq hc.symm, mul_zero, if_neg hq]

/-- **`#774`'s formula, in the shape `#418` consumes it**: for any `P` with `2 • P = S`,

```
[2]∗(S) = ∑_{R ∈ E[2]} (P ⊕ R).
```

Subtracting the same statement at `S = O` (where `P` may be taken to be `O`, so that the sum is
`∑_R (R)`) gives `[2]∗((S) − (O)) = ∑_{R ∈ E[2]} ((P ⊕ R) − (R))`.

The `[Fintype (W.torsion 2)]` is carried in the statement rather than produced inside it: the sum
cannot be written without it, and pushing `Fintype.ofFinite` into a statement is the noncomputable
leak `#763` warns against.  `finite_torsion_two` supplies it at the point of use. -/
theorem pullbackDivisorTwo_single_eq_sum_torsion [Fintype (W.torsion 2)] (h2 : (2 : F) ≠ 0)
    {S P : W.Point} (hP : 2 • P = S) :
    pullbackDivisorTwo h2 (Finsupp.single (projPointOfPoint W S) (1 : ℤ))
      = ∑ R : W.torsion 2, Finsupp.single (projPointOfPoint W (P + R)) (1 : ℤ) := by
  classical
  ext q
  rw [pullbackDivisorTwo_apply, Finset.sum_apply',
    Finset.sum_congr rfl fun R _ => Finsupp.single_apply]
  by_cases hq : comapProjPointTwo h2 q = projPointOfPoint W S
  · obtain ⟨R₀, hR₀⟩ : q ∈ Set.range fun R : W.torsion 2 => projPointOfPoint W (P + R) := by
      rw [← fibre_comapProjPointTwo_eq_range h2 hP]; exact hq
    rw [hq, Finsupp.single_eq_same, mul_one,
      ramificationIdxTwo_eq_one_of_comapProjPointTwo_eq_projPointOfPoint h2 hq,
      Finset.sum_eq_single R₀ (fun R _ hRne => if_neg fun hc =>
        hRne (projPointOfPoint_add_injective P (hc.trans hR₀.symm)))
      (fun hc => absurd (Finset.mem_univ R₀) hc), if_pos hR₀]
  · rw [Finsupp.single_apply, if_neg fun hc => hq hc.symm, mul_zero, Finset.sum_eq_zero]
    intro R _
    refine if_neg fun hc => hq ?_
    rw [← hc]
    exact comapProjPointTwo_add_torsion_two h2 hP R

end IsAlgClosed


/-! ### Non-vacuity

The headline statements carry `[IsDedekindDomain W.CoordinateRing]`, `[W.IsElliptic]` and (for the
counting) `[IsAlgClosed F]`.  `y² = x³ − x` over `AlgebraicClosure ℚ` is the curve `#758`/`#759`/
`#763`/`#774` use, for the same reason: the `ℚ` curve of the rest of `FunctionField/` cannot
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

open scoped Classical in
/-- **`[2]` on places is `[2]` on points, on a curve that exists.** -/
example (P : exampleCurve.Point) :
    comapProjPointTwo exampleTwo (projPointOfPoint exampleCurve P)
      = projPointOfPoint exampleCurve (2 • P) :=
  comapProjPointTwo_projPointOfPoint exampleTwo P

open scoped Classical in
/-- **Every fibre over a rational point has four elements, on the same curve.** -/
example (S : exampleCurve.Point) :
    (finite_comapProjPointTwo_preimage_singleton exampleTwo
      (projPointOfPoint exampleCurve S)).toFinset.card = 4 :=
  card_fibre_comapProjPointTwo_projPointOfPoint exampleTwo S

open scoped Classical in
/-- The fibre description, on the same curve. -/
example (S : exampleCurve.Point) :
    pullbackDivisorTwo exampleTwo (Finsupp.single (projPointOfPoint exampleCurve S) (1 : ℤ))
      = ∑ p ∈ (finite_comapProjPointTwo_preimage_singleton exampleTwo
          (projPointOfPoint exampleCurve S)).toFinset, Finsupp.single p (1 : ℤ) :=
  pullbackDivisorTwo_single_projPointOfPoint exampleTwo S

open scoped Classical in
/-- **`#774`'s formula itself**, on the same curve: `[2]∗(S) = ∑_{R ∈ E[2]} (P ⊕ R)`. -/
example [Fintype (exampleCurve.torsion 2)] (S P : exampleCurve.Point) (hP : 2 • P = S) :
    pullbackDivisorTwo exampleTwo (Finsupp.single (projPointOfPoint exampleCurve S) (1 : ℤ))
      = ∑ R : exampleCurve.torsion 2,
          Finsupp.single (projPointOfPoint exampleCurve (P + R)) (1 : ℤ) :=
  pullbackDivisorTwo_single_eq_sum_torsion exampleTwo hP

open scoped Classical in
/-- The `Fintype` the statement above carries is available, not an assumption in disguise. -/
example : Finite (exampleCurve.torsion 2) := exampleCurve.finite_torsion_two exampleTwo

end Nonvacuity


end WeierstrassCurve.Affine.CoordinateRing
