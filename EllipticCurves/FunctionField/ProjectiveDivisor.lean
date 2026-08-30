/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import EllipticCurves.FunctionField.DivisorConstant
import EllipticCurves.FunctionField.DivisorProd
import EllipticCurves.FunctionField.RationalPointDegree

/-!
# The projective divisor group of a Weierstrass curve

`EllipticCurves.FunctionField.Divisors` attaches to a rational function its divisor on the
**affine** chart, a `Finsupp` on the closed points `HeightOneSpectrum F[W]`;
`EllipticCurves.FunctionField.PlaceAtInfinity` supplies the one missing place, as a separate
`ℤ`-valued function `ordInfty`; and `EllipticCurves.FunctionField.DivisorDegree` relates them by
the degree-zero theorem `degDiv (div f) + ordInfty f = 0`.

Those are still two objects.  This file makes them one:

```
divisorProj f : ProjPoint W →₀ ℤ,     ProjPoint W = Option (HeightOneSpectrum F[W]),
```

with `none` the point at infinity and `some v` an affine closed point.  On it the degree-zero
theorem becomes a single equation about a single object,

```
degProj (divisorProj f) = 0,
```

and Silverman's `div f_P = n·(P) − n·(O)` becomes literally that:
`divisorProj f_P = single (some P) n − single none n`
(`divisorProj_eq_single_sub_single_of_torsion`).

## Why one object rather than two

A *pullback* cannot act on a pair `(divisor f, ordInfty f)`.  The maps this development needs to
pull divisors back along — multiplication by `n` (`#414`/`#422`) and translation `τ_T` (`#465`
deliverable 2) — do not preserve the affine chart: `[n]` has poles at infinity, and `τ_T` sends the
point at infinity to `T` and `−T` to infinity.  Neither can be described as a map of
`HeightOneSpectrum F[W]` at all, so no amount of work on the affine `Finsupp` reaches them.  They
are maps of `ProjPoint W`.  Building that type, and the divisor and degree on it, is rung 3 of
`#639`; it is what rungs 4 and 5 will act on.

## Main definitions

* `WeierstrassCurve.Affine.ProjPoint` — the points of the projective curve;
* `WeierstrassCurve.Affine.divisorProj` — the projective divisor of a rational function;
* `WeierstrassCurve.Affine.degProjPt` / `degProj` — the degree of a point and of a divisor.

## Main results

* **`degProj_divisorProj`** — the degree-zero theorem, `degProj (divisorProj f) = 0`;
* **`degProjPt_none_unique`** — the weight `1` given to the point at infinity is *forced*: no other
  value of `w` makes `degDiv (div f) + w · ordInfty f = 0` hold for every `f`.  So `degProjPt` is
  not a convention chosen to make the theorem above come out, and that theorem has content;
* `divisorProj_eq_zero_iff` — trivial projective divisor characterises the nonzero constants;
* `exists_eq_algebraMap_of_divisorProj_nonneg` — `H⁰(E, 𝒪) = F` from the single hypothesis
  `0 ≤ divisorProj f`, where `exists_eq_algebraMap_of_nonneg` needed the affine and infinite parts
  separately;
* **`exists_neg_of_ne_algebraMap`** — a nonconstant function has a pole.  The affine analogue is
  *false* (`genX W` is nonconstant with no affine pole), so this is information the projective
  divisor genuinely adds;
* `divisorProj_eq_iff_exists_scalar` — equality of projective divisors is equality up to `F*`;
* **`divisorProj_eq_single_sub_single_of_torsion`** — `div f_P = n·(P) − n·(O)`, as one equation;
* `divisorProj_genX_ne_zero` — the group is not trivial.

## Scope

`[IsDedekindDomain W.CoordinateRing]` as an explicit hypothesis throughout, as in `Divisors.lean`
and `DivisorDegree.lean`; no `[W.IsElliptic]`, with the `Elliptic` namespace at the end
re-exposing the main statements unconditionally, as `DivisorConstant.lean` does.

Nothing here classifies the places of `F(W)`: `ProjPoint W` is *a* set of places, and the
statement that it is *all* of them — which is what makes an `F`-automorphism of `F(W)` permute it,
and which `#465` needs — is rung 4 of `#639` and is not proved here.  No pullback of any kind is
constructed.  Ward-independent, normality-independent.

## ⚠️ One `@[simp]` attribute was removed here, and the lemma kept (`#1278`)

`divisorProj_genX_apply_none` carried `@[simp]`, and the default simp set **already proves it** —
through `divisorProj_apply_none` and `ordInfty_genX`. Measured with Mathlib's `simpNF` environment
linter, which had never been run on this tree. The lemma is unchanged and still has consumers in
`EllipticCurves.FunctionField.PlaceResidueComap` and `…PlaceResidueDegree`; only the attribute
went.

## References

* [J. H. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], II.3.
* Stichtenoth, *Algebraic Function Fields and Codes*, I.4.
-/

open IsDedekindDomain

namespace WeierstrassCurve.Affine

variable {F : Type*} [Field F] {W : Affine F} [IsDedekindDomain W.CoordinateRing]

/-! ### The points of the projective curve -/

/-- **The points of the projective Weierstrass curve**: the affine closed points of `F[W]`
together with the point at infinity, which is `none`.

An `abbrev` rather than a `def`, so that `Option`'s `DecidableEq` and `ext` API applies with no
re-derivation and `cases p` splits into the two cases everywhere below. -/
abbrev ProjPoint (W : Affine F) [IsDedekindDomain W.CoordinateRing] : Type _ :=
  Option (HeightOneSpectrum W.CoordinateRing)

omit [IsDedekindDomain W.CoordinateRing] in
variable (W) in
/-- The affine closed points are distinct points of the projective curve.

Stated separately because `Finsupp.mapDomain_apply` and `Finsupp.sum_mapDomain_index_inj` take the
underlying map *implicitly*: supplying `Option.some_injective _` directly leaves the map a
metavariable, and the elaborator then unfolds `Function.Injective` and consumes an extra
argument. -/
lemma some_injective_projPoint :
    Function.Injective (some : HeightOneSpectrum W.CoordinateRing → ProjPoint W) :=
  Option.some_injective _

/-! ### The projective divisor -/

variable (W) in
/-- **The projective divisor of a rational function**: its affine divisor, together with its order
at the point at infinity. -/
noncomputable def divisorProj (f : W.FunctionField) : ProjPoint W →₀ ℤ :=
  (divisor W f).mapDomain some + Finsupp.single none (ordInfty W f)

@[simp]
lemma divisorProj_apply_some (f : W.FunctionField) (v : HeightOneSpectrum W.CoordinateRing) :
    divisorProj W f (some v) = ord v f := by
  rw [divisorProj, Finsupp.add_apply, Finsupp.mapDomain_apply (some_injective_projPoint W),
    Finsupp.single_apply, if_neg (by simp), add_zero, divisor_apply]

@[simp]
lemma divisorProj_apply_none (f : W.FunctionField) :
    divisorProj W f none = ordInfty W f := by
  rw [divisorProj, Finsupp.add_apply, Finsupp.mapDomain_notin_range _ _ (by simp),
    Finsupp.single_eq_same, zero_add]

/-- The projective divisor determines, and is determined by, the affine divisor and the order at
infinity. -/
lemma divisorProj_eq_iff {f g : W.FunctionField} :
    divisorProj W f = divisorProj W g ↔
      divisor W f = divisor W g ∧ ordInfty W f = ordInfty W g := by
  constructor
  · intro h
    refine ⟨?_, by simpa using congrArg (fun D => D none) h⟩
    ext v
    simpa using congrArg (fun D => D (some v)) h
  · rintro ⟨h1, h2⟩
    ext p
    cases p with
    | none => simpa using h2
    | some v => simpa using congrArg (fun D => D v) h1

/-! ### The group laws -/

@[simp]
lemma divisorProj_zero : divisorProj W (0 : W.FunctionField) = 0 := by
  ext p; cases p <;> simp

@[simp]
lemma divisorProj_one : divisorProj W (1 : W.FunctionField) = 0 := by
  ext p; cases p <;> simp

/-- **The projective divisor is additive.** -/
lemma divisorProj_mul {f g : W.FunctionField} (hf : f ≠ 0) (hg : g ≠ 0) :
    divisorProj W (f * g) = divisorProj W f + divisorProj W g := by
  ext p; cases p <;> simp [ord_mul _ hf hg, ordInfty_mul hf hg]

@[simp]
lemma divisorProj_inv (f : W.FunctionField) : divisorProj W f⁻¹ = -divisorProj W f := by
  ext p; cases p <;> simp [ordInfty_inv]

lemma divisorProj_div {f g : W.FunctionField} (hf : f ≠ 0) (hg : g ≠ 0) :
    divisorProj W (f / g) = divisorProj W f - divisorProj W g := by
  rw [div_eq_mul_inv, divisorProj_mul hf (inv_ne_zero hg), divisorProj_inv, sub_eq_add_neg]

lemma divisorProj_pow (f : W.FunctionField) (n : ℕ) :
    divisorProj W (f ^ n) = n • divisorProj W f := by
  ext p; cases p <;> simp [ord_pow, ordInfty_pow]

lemma divisorProj_zpow (f : W.FunctionField) (n : ℤ) :
    divisorProj W (f ^ n) = n • divisorProj W f := by
  ext p; cases p <;> simp [ord_zpow, ordInfty_zpow]

variable (W) in
/-- **Finite-product law for the projective divisor.**  The form the product-over-`⟨T⟩`
telescoping of `#465` deliverable 2 will consume once it can be stated projectively. -/
lemma divisorProj_prod {ι : Type*} (s : Finset ι) (f : ι → W.FunctionField)
    (hf : ∀ i ∈ s, f i ≠ 0) :
    divisorProj W (∏ i ∈ s, f i) = ∑ i ∈ s, divisorProj W (f i) := by
  ext p
  cases p with
  | none => simpa using ordInfty_prod W s f hf
  | some v => simpa using ord_prod v s f hf

/-- **A nonzero constant has trivial projective divisor**: no zeros, no poles, not even at
infinity. -/
@[simp]
lemma divisorProj_algebraMap_base {c : F} (hc : c ≠ 0) :
    divisorProj W (algebraMap F W.FunctionField c) = 0 := by
  ext p; cases p <;> simp [hc]

/-! ### Degrees -/

variable (W) in
/-- **The degree of a point of the projective curve.**  The point at infinity is `F`-rational, so
its degree is `1`; an affine closed point carries the degree of `DivisorDegree`.

That `1` is not a convention: `degProjPt_none_unique` shows it is the only value for which the
degree-zero theorem below can hold. -/
noncomputable def degProjPt (p : ProjPoint W) : ℕ := p.elim 1 degPt

@[simp] lemma degProjPt_none : degProjPt W (none : ProjPoint W) = 1 := rfl

@[simp] lemma degProjPt_some (v : HeightOneSpectrum W.CoordinateRing) :
    degProjPt W (some v) = degPt v := rfl

/-- **Every point of the projective curve has positive degree.** -/
lemma degProjPt_pos (p : ProjPoint W) : 0 < degProjPt W p := by
  cases p with
  | none => exact Nat.one_pos
  | some v => exact degPt_pos v

variable (W) in
/-- **The degree of a projective divisor.** -/
noncomputable def degProj (D : ProjPoint W →₀ ℤ) : ℤ := D.sum fun p n => n * degProjPt W p

@[simp]
lemma degProj_zero : degProj W (0 : ProjPoint W →₀ ℤ) = 0 := Finsupp.sum_zero_index

lemma degProj_add (D E : ProjPoint W →₀ ℤ) : degProj W (D + E) = degProj W D + degProj W E :=
  Finsupp.sum_add_index' (fun _ => zero_mul _) (fun _ _ _ => add_mul _ _ _)

lemma degProj_sub (D E : ProjPoint W →₀ ℤ) : degProj W (D - E) = degProj W D - degProj W E := by
  have h := degProj_add (W := W) (D - E) E
  rw [sub_add_cancel] at h
  omega

@[simp]
lemma degProj_single (p : ProjPoint W) (n : ℤ) :
    degProj W (Finsupp.single p n) = n * degProjPt W p := by
  rw [degProj, Finsupp.sum_single_index (zero_mul _)]

/-- The degree of a divisor supported on the affine chart is its affine degree. -/
lemma degProj_mapDomain_some (D : HeightOneSpectrum W.CoordinateRing →₀ ℤ) :
    degProj W (D.mapDomain some) = degDiv W D := by
  rw [degProj, Finsupp.sum_mapDomain_index_inj (some_injective_projPoint W), degDiv]
  rfl

/-! ### The degree-zero theorem -/

/-- **The degree-zero theorem on the projective curve.**  A rational function has as many zeros as
poles: the degree of its projective divisor is zero.

This is `EllipticCurves.FunctionField.DivisorDegree`'s `degDiv_divisor_add_ordInfty` with the two
terms assembled into one divisor, which is the form a pullback can act on. -/
theorem degProj_divisorProj {f : W.FunctionField} (hf : f ≠ 0) :
    degProj W (divisorProj W f) = 0 := by
  rw [divisorProj, degProj_add, degProj_mapDomain_some, degProj_single, degProjPt_none]
  have := degDiv_divisor_add_ordInfty (W := W) hf
  push_cast
  omega

/-- **The weight `1` at the point at infinity is forced.**

`degProjPt` gives the point at infinity the degree `1`, and one could reasonably suspect that
`degProj_divisorProj` holds *because* of that choice.  It does not: if any `w : ℤ` makes
`degDiv (div f) + w · ordInfty f = 0` hold for every nonzero `f`, then `w = 1`.  Testing against
the generic `x`-coordinate is enough, since `ordInfty genX = -2` (`#637`) while
`degDiv (div genX) = 2` (`#642`) — two independently computed numbers.

So `degProjPt` is the unique degree function extending `degPt` for which the degree-zero theorem
can hold, and that theorem has content. -/
theorem degProjPt_none_unique (w : ℤ)
    (hw : ∀ f : W.FunctionField, f ≠ 0 → degDiv W (divisor W f) + w * ordInfty W f = 0) :
    w = 1 := by
  have h := hw (CoordinateRing.genX W) genX_ne_zero
  rw [degDiv_divisor genX_ne_zero, ordInfty_genX] at h
  omega

/-! ### Consequences -/

/-- **Trivial projective divisor characterises the nonzero constants.** -/
theorem divisorProj_eq_zero_iff {f : W.FunctionField} (hf : f ≠ 0) :
    divisorProj W f = 0 ↔ ∃ c : F, c ≠ 0 ∧ f = algebraMap F W.FunctionField c := by
  refine ⟨fun h => ?_, ?_⟩
  · refine exists_eq_algebraMap_of_divisor_eq_zero hf ?_
    ext v
    simpa using congrArg (fun D => D (some v)) h
  · rintro ⟨c, hc, rfl⟩
    exact divisorProj_algebraMap_base hc

/-- **An effective projective divisor has nonnegative degree.**  The sharp form is
`eq_zero_of_degProj_eq_zero`; this is the plain inequality, and the companion of
`EllipticCurves.FunctionField.DivisorDegree`'s `degDiv_nonneg`. -/
lemma degProj_nonneg {D : ProjPoint W →₀ ℤ} (hD : ∀ p, 0 ≤ D p) : 0 ≤ degProj W D :=
  Finset.sum_nonneg fun p _ => mul_nonneg (hD p) (Int.natCast_nonneg _)

/-- **An effective projective divisor of degree zero is zero** — because every point of the
projective curve has positive degree. -/
theorem eq_zero_of_degProj_eq_zero {D : ProjPoint W →₀ ℤ} (hD : ∀ p, 0 ≤ D p)
    (h : degProj W D = 0) : D = 0 := by
  ext p
  by_cases hp : p ∈ D.support
  · have hterm := (Finset.sum_eq_zero_iff_of_nonneg
      (fun q _ => mul_nonneg (hD q) (Int.natCast_nonneg (degProjPt W q)))).mp h p hp
    have hpos : (0 : ℤ) < degProjPt W p := by exact_mod_cast degProjPt_pos p
    rcases mul_eq_zero.mp hterm with h0 | h0
    · simpa using h0
    · omega
  · simpa using Finsupp.notMem_support_iff.mp hp

/-- **A rational function with no poles anywhere on the projective curve has no zeros either.** -/
theorem divisorProj_eq_zero_of_nonneg {f : W.FunctionField} (hf : f ≠ 0)
    (hD : ∀ p, 0 ≤ divisorProj W f p) : divisorProj W f = 0 :=
  eq_zero_of_degProj_eq_zero hD (degProj_divisorProj hf)

/-- **The global sections of the structure sheaf are the constants**, from the single hypothesis
that `f` has no pole at any point of the projective curve.

`exists_eq_algebraMap_of_nonneg` (`#642`) asks for the affine and the infinite hypotheses
separately; here they are one condition on one object, which is the point of the projective
divisor. -/
theorem exists_eq_algebraMap_of_divisorProj_nonneg {f : W.FunctionField} (hf : f ≠ 0)
    (hD : ∀ p, 0 ≤ divisorProj W f p) :
    ∃ c : F, c ≠ 0 ∧ f = algebraMap F W.FunctionField c :=
  (divisorProj_eq_zero_iff hf).mp (divisorProj_eq_zero_of_nonneg hf hD)

/-- **A nonconstant rational function has a pole somewhere on the projective curve.**

This is the contrapositive of `exists_eq_algebraMap_of_divisorProj_nonneg`, and it is the
cleanest single witness that the projective divisor carries information the affine one does not:
**the affine analogue is false.**  `genX W` is nonconstant (`CoordinateRing.genX_ne`) and yet has
no affine pole at all, since `ord_algebraMap_nonneg` gives `0 ≤ ord v a` for every `a ∈ F[W]` and
every closed point `v`; all of its poles are at infinity (`exists_neg_divisorProj_genX`).  So the
statement becomes true exactly when `O` joins the divisor group. -/
theorem exists_neg_of_ne_algebraMap {f : W.FunctionField} (hf : f ≠ 0)
    (hconst : ∀ c : F, f ≠ algebraMap F W.FunctionField c) :
    ∃ p : ProjPoint W, divisorProj W f p < 0 := by
  by_contra h
  obtain ⟨c, -, hc⟩ :=
    exists_eq_algebraMap_of_divisorProj_nonneg hf fun p => not_lt.mp fun hp => h ⟨p, hp⟩
  exact hconst c hc

/-- The affine divisor already determines the order at infinity, by the degree-zero theorem. -/
theorem ordInfty_eq_of_divisor_eq {f g : W.FunctionField} (hf : f ≠ 0) (hg : g ≠ 0)
    (h : divisor W f = divisor W g) : ordInfty W f = ordInfty W g := by
  have h1 := degDiv_divisor_add_ordInfty (W := W) hf
  have h2 := degDiv_divisor_add_ordInfty (W := W) hg
  rw [h] at h1
  omega

/-- **The projective divisor determines a rational function up to an `F*`-scalar.** -/
theorem exists_scalar_of_divisorProj_eq {f g : W.FunctionField} (hf : f ≠ 0) (hg : g ≠ 0)
    (h : divisorProj W f = divisorProj W g) :
    ∃ c : F, c ≠ 0 ∧ algebraMap F W.FunctionField c * f = g :=
  exists_scalar_of_divisor_eq hf hg (divisorProj_eq_iff.mp h).1

/-- **Equality of projective divisors is exactly equality up to an `F*`-scalar.**

The converse direction is where the degree-zero theorem does the work: it is not enough that the
affine divisors agree, the orders at infinity must agree too, and `ordInfty_eq_of_divisor_eq` says
the affine data already forces that. -/
theorem divisorProj_eq_iff_exists_scalar {f g : W.FunctionField} (hf : f ≠ 0) (hg : g ≠ 0) :
    divisorProj W f = divisorProj W g ↔
      ∃ c : F, c ≠ 0 ∧ algebraMap F W.FunctionField c * f = g := by
  refine ⟨exists_scalar_of_divisorProj_eq hf hg, fun h => ?_⟩
  have haff := (divisor_eq_iff_exists_scalar hf hg).mpr h
  exact divisorProj_eq_iff.mpr ⟨haff, ordInfty_eq_of_divisor_eq hf hg haff⟩

/-! ### `div f_P = n·(P) − n·(O)` -/

/-- **`div f_P = n·(P) − n·(O)`, as a single equation in the projective divisor group.**

`EllipticCurves.FunctionField.RationalPointDegree` proves this as a *pair* of facts — the affine
divisor is `n·(P)` and the order at infinity is `−n`.  Here it is Silverman's statement verbatim:
one function, one divisor, one equation.  This is the starting datum of the divisor-theoretic Weil
pairing (`#244`) in the shape the construction actually wants, and the shape rung 5's `[n]∗` will
be applied to. -/
theorem divisorProj_eq_single_sub_single_of_torsion [DecidableEq F] {x y : F}
    (h : W.Nonsingular x y) {n : ℕ} (hP : Point.some x y h ∈ W.torsion n) :
    ∃ f : W.FunctionField, f ≠ 0 ∧ divisorProj W f
      = Finsupp.single (some (CoordinateRing.pointClosedPoint h.left)) (n : ℤ)
        - Finsupp.single none (n : ℤ) := by
  classical
  obtain ⟨f, hf, hd, hi⟩ := exists_generator_divisor_eq_of_torsion' h hP
  refine ⟨f, hf, ?_⟩
  ext p
  cases p with
  | none => simp [hi]
  | some v =>
      rw [divisorProj_apply_some, ← divisor_apply, hd, Finsupp.sub_apply]
      simp [Finsupp.single_apply]

/-! ### The group is not trivial -/

/-- The generic `x`-coordinate has a double pole at the point at infinity. -/
lemma divisorProj_genX_apply_none :
    divisorProj W (CoordinateRing.genX W) none = -2 := by
  rw [divisorProj_apply_none, ordInfty_genX]

/-- **A nonzero projective divisor of degree zero exists**, so neither `divisorProj` nor `degProj`
is a trivial functional and nothing above is vacuous. -/
theorem divisorProj_genX_ne_zero : divisorProj W (CoordinateRing.genX W) ≠ 0 := by
  intro h
  have := divisorProj_genX_apply_none (W := W)
  rw [h] at this
  exact absurd this (by norm_num)

variable (W) in
/-- **The witness for `exists_neg_of_ne_algebraMap`**: the generic `x`-coordinate really does have
a pole, and it is at the point at infinity.  Affinely it has none — `ord_algebraMap_nonneg` — so
this pins the theorem to a concrete function rather than leaving it abstract. -/
theorem exists_neg_divisorProj_genX :
    ∃ p : ProjPoint W, divisorProj W (CoordinateRing.genX W) p < 0 :=
  ⟨none, by simp⟩

/-! ### Unconditional forms for an elliptic curve

As in `EllipticCurves.FunctionField.DivisorConstant`, the `Elliptic` namespace re-exposes the main
statements with `[IsDedekindDomain W.CoordinateRing]` discharged by the normality instance that
`[W.IsElliptic]` supplies, since that is the hypothesis style the Weil-pairing consumers run
under. -/

namespace Elliptic

variable {F : Type*} [Field F] {W : Affine F} [W.IsElliptic]

/-- **The degree-zero theorem**, unconditional in `[W.IsElliptic]`. -/
theorem degProj_divisorProj {f : W.FunctionField} (hf : f ≠ 0) :
    degProj W (divisorProj W f) = 0 :=
  WeierstrassCurve.Affine.degProj_divisorProj hf

/-- **Trivial projective divisor characterises the nonzero constants**, unconditional in
`[W.IsElliptic]`. -/
theorem divisorProj_eq_zero_iff {f : W.FunctionField} (hf : f ≠ 0) :
    divisorProj W f = 0 ↔ ∃ c : F, c ≠ 0 ∧ f = algebraMap F W.FunctionField c :=
  WeierstrassCurve.Affine.divisorProj_eq_zero_iff hf

/-- **`H⁰(E, 𝒪) = F`**, unconditional in `[W.IsElliptic]`. -/
theorem exists_eq_algebraMap_of_divisorProj_nonneg {f : W.FunctionField} (hf : f ≠ 0)
    (hD : ∀ p, 0 ≤ divisorProj W f p) :
    ∃ c : F, c ≠ 0 ∧ f = algebraMap F W.FunctionField c :=
  WeierstrassCurve.Affine.exists_eq_algebraMap_of_divisorProj_nonneg hf hD

/-- **A nonconstant function has a pole**, unconditional in `[W.IsElliptic]`. -/
theorem exists_neg_of_ne_algebraMap {f : W.FunctionField} (hf : f ≠ 0)
    (hconst : ∀ c : F, f ≠ algebraMap F W.FunctionField c) :
    ∃ p : ProjPoint W, divisorProj W f p < 0 :=
  WeierstrassCurve.Affine.exists_neg_of_ne_algebraMap hf hconst

/-- **Equality of projective divisors is equality up to an `F*`-scalar**, unconditional in
`[W.IsElliptic]`. -/
theorem divisorProj_eq_iff_exists_scalar {f g : W.FunctionField} (hf : f ≠ 0) (hg : g ≠ 0) :
    divisorProj W f = divisorProj W g ↔
      ∃ c : F, c ≠ 0 ∧ algebraMap F W.FunctionField c * f = g :=
  WeierstrassCurve.Affine.divisorProj_eq_iff_exists_scalar hf hg

/-- **`div f_P = n·(P) − n·(O)`**, unconditional in `[W.IsElliptic]`. -/
theorem divisorProj_eq_single_sub_single_of_torsion [DecidableEq F] {x y : F}
    (h : W.Nonsingular x y) {n : ℕ} (hP : Point.some x y h ∈ W.torsion n) :
    ∃ f : W.FunctionField, f ≠ 0 ∧ divisorProj W f
      = Finsupp.single (some (CoordinateRing.pointClosedPoint h.left)) (n : ℤ)
        - Finsupp.single none (n : ℤ) :=
  WeierstrassCurve.Affine.divisorProj_eq_single_sub_single_of_torsion h hP

/-- **The projective divisor group is not trivial**, unconditional in `[W.IsElliptic]` — so none
of the statements in this namespace is vacuous. -/
theorem divisorProj_genX_ne_zero : divisorProj W (CoordinateRing.genX W) ≠ 0 :=
  WeierstrassCurve.Affine.divisorProj_genX_ne_zero

end Elliptic

end WeierstrassCurve.Affine
