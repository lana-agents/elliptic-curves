/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import EllipticCurves.FunctionField.CountValuationBridge
import EllipticCurves.FunctionField.Places
import EllipticCurves.FunctionField.TranslationAutomorphism

/-!
# The projective divisor transports along every `F`-automorphism of `F(W)`

`EllipticCurves.FunctionField.Places` (rung 4 of the projective divisor theory) shows that an
`F`-algebra automorphism `σ` of `F(W)` permutes the points of the projective curve, as
`mapProjPoint W σ : ProjPoint W ≃ ProjPoint W`.  That is a statement about **sets**: the place of
`mapProjPoint W σ p` is the `σ`-image of the place of `p`.  This file upgrades it to the
statement about **integers** that the divisor calculus needs:

```lean
divisorProj W (σ f) = (divisorProj W f).mapDomain (mapProjPoint W σ)
```

and reads it off at `σ = translateAlgEquiv h_T`, where it is the divisor pullback under
translation:

```lean
divisorProj W (translateEndo h_T f)
    = (divisorProj W f).mapDomain (mapProjPoint W (translateAlgEquiv h_T)).
```

**That last statement is the one `#465` deliverable 2 has been blocked on**, and which
`EllipticCurves.FunctionField.DivisorTransport` records as missing, with the diagnosis that
`translateEndo` is not `IsFractionRing.ringEquivOfRingEquiv e` for any ring automorphism `e` of
`F[W]`, *because it moves the points at infinity*.  Nothing here contradicts that diagnosis: the
formula that module names is the **affine** one, and the affine divisor `divisor W` really does
not transport.  It is `divisorProj`, on the projective point set, that does.

⚠️ **This paragraph used to name `EllipticCurves.FunctionField.WeilPairingAlternating` beside it,
as a second module recording that statement as missing.**  ⚠️ **The note it named was retired by a
commit that edited this module too, and this paragraph was not part of what that commit edited**:
`cf3783d` (2026-08-20 18:26:50) rewrote that module to name `divisorProj_translateEndo`, proved
here, as the pullback its product-over-`⟨T⟩` argument runs on, and in the same change extended the
Scope section of this one, five hours and fifteen minutes after this module landed in `7ffe193`
(13:11:24 the same day).  ⚠️ A retirement has to reach the modules that cite
the retired sentence, and one of them can be the module the same commit is already editing.

⚠️ **Deliverable 2 is no longer blocked, and what unblocked it is the theorem proved here.**
`exists_weilPairingElt_self_eq_one_of_algClosed_two`
(`EllipticCurves.FunctionField.WeilPairingAlternatingTwo`) and
`exists_weilPairingElt_self_eq_one_of_algClosed_three`
(`EllipticCurves.FunctionField.WeilPairingAlternatingThree`) prove `e_n(T, T) = 1` over an
algebraically closed base field, on the telescoping functions
`exists_mul_translateEndo_eq_algebraMap`
(`EllipticCurves.FunctionField.WeilPairingTelescopeTwo`) and
`exists_mul_translateEndo_mul_translateEndo_eq_algebraMap`
(`EllipticCurves.FunctionField.WeilPairingTelescopeThree`), whose divisor steps rewrite with
`divisorProj_translateEndo`.  What that route never needs is the **affine** formula, which is why
`EllipticCurves.FunctionField.DivisorTransport`'s diagnosis is untouched by any of this.

## Why it is not a corollary of rung 4, and the route

`ord v` is defined through `FractionalIdeal.count` at a prime of `F[W]`, and `ordInfty` through the
degree function on `F[W]`.  Neither encoding is preserved by `σ`, and there is no common
generalisation of the two on which to run a transport argument.  Building one — an intrinsic
`ℤ`-valued order attached to a `ValuationSubring` — is real work, and it is **not** what happens
below.  Instead the file uses the classical uniqueness statement

> a surjective homomorphism `Kˣ → ℤ` is determined by the set `{x | 0 ≤ φ x}`

(`eq_of_nonneg_iff_of_exists_eq_one`, proved for a bare field and with no valuation theory in it —
an upstream candidate).  Both `divisorProj W · p` and `divisorProj W (σ ·) (mapProjPoint W σ p)`
are such homomorphisms, and rung 4 says they have the same nonnegativity locus.  So they agree,
and the transport of integers follows from the transport of sets with no new geometry.

The two hypotheses of the uniqueness lemma are supplied by:

* `mem_placeOf_iff_divisorProj_nonneg` — the nonnegativity locus of `divisorProj W · p` **is** the
  place `placeOf W p`.  At `none` this is `mem_ordInftyValuationSubring` (definitional); at
  `some v` it chains Mathlib's `valuationSubringAtPrime_eq_valuationSubring` with this repo's
  `valuation_eq_exp_neg_ord` (`EllipticCurves.FunctionField.CountValuationBridge`, built for
  `#414`'s ramification transport — this is its third consumer).
* `exists_divisorProj_eq_one` — every place has a uniformizer, so the order function is surjective
  onto `ℤ`.  Without it `φ` and `2 • φ` would be indistinguishable.

## Main results

* `WeierstrassCurve.Affine.mem_placeOf_iff_divisorProj_nonneg`;
* `WeierstrassCurve.Affine.exists_divisorProj_eq_one`;
* `WeierstrassCurve.Affine.eq_of_nonneg_iff_of_exists_eq_one` — the abstract uniqueness lemma;
* **`WeierstrassCurve.Affine.divisorProj_algEquiv`** (and its pointwise form
  `divisorProj_algEquiv_apply`) — the transport;
* **`WeierstrassCurve.Affine.divisorProj_translateEndo`** — the payoff, `#465` deliverable 2's
  missing input.

## Implementation notes

The `Finsupp` form is stated with `Finsupp.mapDomain` rather than `Finsupp.equivMapDomain`, to
match `divisorProj`'s own definition (`divisorProj = (divisor W f).mapDomain some + …`) so that the
two compose without a translation lemma; `mapDomain_apply` fires on
`(mapProjPoint W σ).injective`, which is free from the `Equiv`.

## Scope

**Nothing below identifies the permutation `mapProjPoint W (translateAlgEquiv h_T)`, or claims it
is nontrivial.**  Identifying it is a separate computation (it needs
`ordInfty (translateEndo h_{-T} (genX W))`, where the naive estimate cancels against `slope ^ 2`),
and it is not attempted here.  `translateAlgEquiv_ne_one` (`#656`) says the *automorphism* is not
the identity; that does not by itself say the induced permutation is not.  The theorems below hold
either way, and are non-vacuous either way — see `exists_divisorProj_eq_one`, which says the order
function at every place is surjective onto `ℤ`.

That computation has since been done, in two files.
`EllipticCurves.FunctionField.TranslationPlaceAtInfinity` (`#660`) does the two points at the ends:
translation by `T` sends the point at infinity to the closed point of `−T` and the closed point of
`T` to the point at infinity, so the permutation is nontrivial.
`EllipticCurves.FunctionField.TranslationProjAction` (`#663`) does the affine `F`-points:
`mapProjPoint_translateAlgEquiv_pointClosedPoint_affine` sends the closed point of `P` to the
closed point of `P ⊖ T`.  A consumer of `divisorProj_translateEndo` that needs to know *where* the
transported divisor sits should reach for `divisorProj_translateEndo_none` and
`divisorProj_translateEndo_pointClosedPoint` in the former, and
`divisorProj_translateEndo_pointClosedPoint_affine` in the latter.

Together those describe the permutation on the **rational** locus `{O} ∪ {affine F-points}` only,
where it is `p ↦ p ⊖ T`.  `ProjPoint W` is all of `Option (HeightOneSpectrum F[W])`, and a
height-one prime with a nontrivial residue extension is not the closed point of any `F`-rational
point, so none of the three merged files says where it goes.  The transport theorems below are
insensitive to that: they hold at every `p : ProjPoint W`, identified or not.

## References

* [J. H. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], II.3.
* Stichtenoth, *Algebraic Function Fields and Codes*, I.1–I.4 (a discrete valuation is determined
  by its valuation ring).
-/

open IsDedekindDomain

namespace WeierstrassCurve.Affine

open CoordinateRing

variable {F : Type*} [Field F] {W : Affine F}

/-! ### A discrete valuation is determined by its valuation ring

Everything in this section is about a bare field: `φ` and `ψ` are `ℤ`-valued functions that are
additive on products of nonzero elements — the shape both `ord v` and `ordInfty` have, with the
junk value `0` at `0`.  Nothing about curves, and nothing about valuations either; it is an
upstream candidate. -/

section Uniqueness

variable {K : Type*} [Field K] {φ ψ : K → ℤ}

/-- Additivity on nonzero products forces `φ 1 = 0`. -/
private lemma map_one_of_mul (hφ : ∀ x y : K, x ≠ 0 → y ≠ 0 → φ (x * y) = φ x + φ y) :
    φ 1 = 0 := by
  have h := hφ 1 1 one_ne_zero one_ne_zero
  rw [one_mul] at h
  omega

/-- Additivity on nonzero products forces `φ x⁻¹ = -φ x`. -/
private lemma map_inv_of_mul (hφ : ∀ x y : K, x ≠ 0 → y ≠ 0 → φ (x * y) = φ x + φ y)
    {x : K} (hx : x ≠ 0) : φ x⁻¹ = -φ x := by
  have h := hφ x x⁻¹ hx (inv_ne_zero hx)
  rw [mul_inv_cancel₀ hx, map_one_of_mul hφ] at h
  omega

/-- Additivity on nonzero products forces `φ (x ^ n) = n * φ x` for `n : ℤ`. -/
private lemma map_zpow_of_mul (hφ : ∀ x y : K, x ≠ 0 → y ≠ 0 → φ (x * y) = φ x + φ y)
    {x : K} (hx : x ≠ 0) (n : ℤ) : φ (x ^ n) = n * φ x := by
  induction n using Int.induction_on with
  | zero => simpa using map_one_of_mul hφ
  | succ k ih =>
      rw [zpow_add_one₀ hx, hφ _ _ (zpow_ne_zero _ hx) hx, ih]
      ring
  | pred k ih =>
      rw [zpow_sub_one₀ hx, hφ _ _ (zpow_ne_zero _ hx) (inv_ne_zero hx),
        map_inv_of_mul hφ hx, ih]
      ring

/-- If `φ` attains the value `1` and `ψ` vanishes wherever `φ` does, then `ψ` is the constant
multiple `ψ π • φ`: write `x` as `π ^ (φ x)` times something in the kernel. -/
private lemma eq_mul_of_zero_imp_zero
    (hφ : ∀ x y : K, x ≠ 0 → y ≠ 0 → φ (x * y) = φ x + φ y)
    (hψ : ∀ x y : K, x ≠ 0 → y ≠ 0 → ψ (x * y) = ψ x + ψ y)
    (hzero : ∀ y : K, y ≠ 0 → φ y = 0 → ψ y = 0)
    {π : K} (hπ0 : π ≠ 0) (hπ : φ π = 1) {x : K} (hx : x ≠ 0) : ψ x = ψ π * φ x := by
  have hz0 : π ^ (-φ x) ≠ 0 := zpow_ne_zero _ hπ0
  have h0 : φ (x * π ^ (-φ x)) = 0 := by
    rw [hφ _ _ hx hz0, map_zpow_of_mul hφ hπ0, hπ]
    ring
  have h := hzero _ (mul_ne_zero hx hz0) h0
  rw [hψ _ _ hx hz0, map_zpow_of_mul hψ hπ0] at h
  linear_combination h

/-- **A `ℤ`-valued order function is determined by its nonnegativity locus.**

If `φ` and `ψ` are additive on products of nonzero elements, each attains the value `1`, and
`0 ≤ φ x ↔ 0 ≤ ψ x` for every `x ≠ 0`, then `φ = ψ` on the nonzero elements.

This is the algebraic content of "a place determines its order function": the valuation ring
`{x | 0 ≤ φ x}` fixes `φ` outright, not merely up to a positive multiple, once `φ` is known to be
surjective.  Attaining `1` is exactly surjectivity, since the image is a subgroup of `ℤ`. -/
theorem eq_of_nonneg_iff_of_exists_eq_one
    (hφ : ∀ x y : K, x ≠ 0 → y ≠ 0 → φ (x * y) = φ x + φ y)
    (hψ : ∀ x y : K, x ≠ 0 → y ≠ 0 → ψ (x * y) = ψ x + ψ y)
    (hiff : ∀ x : K, x ≠ 0 → (0 ≤ φ x ↔ 0 ≤ ψ x))
    (hφ1 : ∃ x : K, x ≠ 0 ∧ φ x = 1) (hψ1 : ∃ x : K, x ≠ 0 ∧ ψ x = 1)
    {x : K} (hx : x ≠ 0) : φ x = ψ x := by
  -- The two kernels agree: `φ y = 0` iff both `φ y` and `φ y⁻¹` are nonnegative.
  have hzero : ∀ y : K, y ≠ 0 → φ y = 0 → ψ y = 0 := by
    intro y hy h
    have h1 : 0 ≤ ψ y := (hiff y hy).1 h.ge
    have h2 : 0 ≤ ψ y⁻¹ := (hiff y⁻¹ (inv_ne_zero hy)).1 (by rw [map_inv_of_mul hφ hy, h, neg_zero])
    rw [map_inv_of_mul hψ hy] at h2
    omega
  obtain ⟨πφ, hπφ0, hπφ⟩ := hφ1
  obtain ⟨πψ, hπψ0, hπψ⟩ := hψ1
  -- `ψ = c • φ` with `0 ≤ c`; evaluating at a `ψ`-uniformizer gives `c ∣ 1`, so `c = 1`.
  -- (The symmetric `φ = d • ψ` is not needed: divisibility plus `0 ≤ c` already pins `c`.)
  have hc : ∀ y : K, y ≠ 0 → ψ y = ψ πφ * φ y :=
    fun y hy => eq_mul_of_zero_imp_zero hφ hψ hzero hπφ0 hπφ hy
  have hc0 : 0 ≤ ψ πφ := (hiff πφ hπφ0).1 (by rw [hπφ]; norm_num)
  have hunit : ψ πφ * φ πψ = 1 := by
    have := hc πψ hπψ0
    rw [hπψ] at this
    omega
  have hc1 : ψ πφ = 1 := by
    have hdvd : ψ πφ ∣ 1 := ⟨φ πψ, hunit.symm⟩
    have hle := Int.le_of_dvd one_pos hdvd
    have hne : ψ πφ ≠ 0 := by
      intro h
      rw [h, zero_mul] at hunit
      exact absurd hunit (by norm_num)
    omega
  rw [hc x hx, hc1, one_mul]

end Uniqueness

/-! ### The nonnegativity locus of the order at a place -/

section Places

variable [IsDedekindDomain W.CoordinateRing]

/-- **A function is regular at an affine closed point iff it has nonnegative order there.**  The
membership side is Mathlib's localisation-as-valuation-subring
(`valuationSubringAtPrime_eq_valuationSubring`); the order side is this repo's count/valuation
bridge `valuation_eq_exp_neg_ord`. -/
theorem mem_valuationSubringAtPrime_iff_ord_nonneg
    (v : HeightOneSpectrum W.CoordinateRing) {f : W.FunctionField} (hf : f ≠ 0) :
    f ∈ HeightOneSpectrum.valuationSubringAtPrime W.FunctionField v ↔ 0 ≤ ord v f := by
  rw [HeightOneSpectrum.valuationSubringAtPrime_eq_valuationSubring,
    Valuation.mem_valuationSubring_iff, valuation_eq_exp_neg_ord v hf, ← WithZero.exp_zero,
    WithZero.exp_le_exp, neg_nonpos]

/-- **The place of a point is the nonnegativity locus of the order at that point.**  Both branches
are definitional unfoldings of a merged statement: `mem_ordInftyValuationSubring` at `none`, and
`mem_valuationSubringAtPrime_iff_ord_nonneg` at `some v`. -/
theorem mem_placeOf_iff_divisorProj_nonneg (p : ProjPoint W) {f : W.FunctionField} (hf : f ≠ 0) :
    f ∈ placeOf W p ↔ 0 ≤ divisorProj W f p := by
  cases p with
  | none => rw [placeOf_none, mem_ordInftyValuationSubring, divisorProj_apply_none]
  | some v => rw [placeOf_some, divisorProj_apply_some,
      mem_valuationSubringAtPrime_iff_ord_nonneg v hf]

/-- **Every place has a uniformizer**, so the order function at a place is surjective onto `ℤ`.
At infinity the witness is `x / y` (`ordInfty_genX_div_genY`); at an affine closed point it is
Mathlib's `valuation_exists_uniformizer`.

This is what pins the order function down: without it, `divisorProj W · p` would only be determined
up to a positive factor by its nonnegativity locus.  It is also the non-vacuity certificate for
this file — the order at every place really does take a nonzero value. -/
theorem exists_divisorProj_eq_one (p : ProjPoint W) :
    ∃ π : W.FunctionField, π ≠ 0 ∧ divisorProj W π p = 1 := by
  cases p with
  | none =>
      obtain ⟨π, hπ0, hπ⟩ := ordInfty_surjective (W := W) 1
      exact ⟨π, hπ0, by rw [divisorProj_apply_none, hπ]⟩
  | some v =>
      obtain ⟨π, hπ⟩ := v.valuation_exists_uniformizer W.FunctionField
      have hπ0 : π ≠ 0 := by
        intro h
        rw [h, map_zero] at hπ
        exact WithZero.exp_ne_zero hπ.symm
      refine ⟨π, hπ0, ?_⟩
      rw [divisorProj_apply_some, ord_eq_neg_log_valuation v hπ0, hπ, WithZero.log_exp, neg_neg]

end Places

/-! ### The transport -/

section Transport

variable [IsDedekindDomain W.CoordinateRing] (σ : W.FunctionField ≃ₐ[F] W.FunctionField)

omit [IsDedekindDomain W.CoordinateRing] in
/-- `σ` does not kill nonzero elements. -/
private lemma algEquiv_ne_zero {f : W.FunctionField} (hf : f ≠ 0) : σ f ≠ 0 :=
  (map_ne_zero_iff σ σ.injective).2 hf

/-- **The order of `σ f` at `mapProjPoint W σ p` is the order of `f` at `p`.**

The two sides are order functions with the same nonnegativity locus — that is exactly rung 4's
`mem_placeOf_mapProjPoint`, read through `mem_placeOf_iff_divisorProj_nonneg` — and both attain the
value `1`, so `eq_of_nonneg_iff_of_exists_eq_one` identifies them.  No property of `σ` beyond being
an `F`-algebra automorphism is used. -/
theorem divisorProj_algEquiv_apply {f : W.FunctionField} (hf : f ≠ 0) (p : ProjPoint W) :
    divisorProj W (σ f) (mapProjPoint W σ p) = divisorProj W f p := by
  refine eq_of_nonneg_iff_of_exists_eq_one
    (φ := fun g => divisorProj W (σ g) (mapProjPoint W σ p)) (ψ := fun g => divisorProj W g p)
    (fun x y hx hy => ?_) (fun x y hx hy => ?_) (fun x hx => ?_) ?_ ?_ hf
  · rw [map_mul, divisorProj_mul (algEquiv_ne_zero σ hx) (algEquiv_ne_zero σ hy), Finsupp.add_apply]
  · rw [divisorProj_mul hx hy, Finsupp.add_apply]
  · rw [← mem_placeOf_iff_divisorProj_nonneg _ (algEquiv_ne_zero σ hx),
      ← mem_placeOf_iff_divisorProj_nonneg _ hx, mem_placeOf_mapProjPoint,
      AlgEquiv.symm_apply_apply]
  · obtain ⟨π, hπ0, hπ⟩ := exists_divisorProj_eq_one (mapProjPoint W σ p)
    exact ⟨σ.symm π, (map_ne_zero_iff σ.symm σ.symm.injective).2 hπ0, by
      rw [AlgEquiv.apply_symm_apply, hπ]⟩
  · exact exists_divisorProj_eq_one p

/-- **The projective divisor transports along every `F`-automorphism of `F(W)`.**

This is what rung 4 was for.  The affine divisor `divisor W` does *not* transport — `σ` need not
preserve `F[W]` — and `EllipticCurves.FunctionField.DivisorTransport` records exactly that
obstruction for `translateEndo`.  On the projective point set it dissolves. -/
theorem divisorProj_algEquiv {f : W.FunctionField} (hf : f ≠ 0) :
    divisorProj W (σ f) = (divisorProj W f).mapDomain (mapProjPoint W σ) := by
  ext q
  obtain ⟨p, rfl⟩ := (mapProjPoint W σ).surjective q
  rw [Finsupp.mapDomain_apply (mapProjPoint W σ).injective, divisorProj_algEquiv_apply σ hf p]

end Transport

/-! ### The payoff: the divisor pullback under translation -/

section Translation

variable [W.IsElliptic] [IsDedekindDomain W.CoordinateRing] {x₂ y₂ : F}

/-- **The divisor pullback under translation by an affine point `T`.**

`#465` deliverable 2 needs `div (τ_T g)` in terms of `div g`, and
`EllipticCurves.FunctionField.WeilPairingAlternating` records it as the one missing input to the
product-over-`⟨T⟩` argument for `e_n(T, T) = 1`.  Here it is, on the projective divisor group: the
divisor of `τ_T g` is the divisor of `g`, pushed forward along the permutation of `ProjPoint W`
that `τ_T` induces.

What is **not** supplied here is the identification of that permutation (classically: it sends the
point at infinity to the closed point of `−T`).  See this file's module docstring. -/
theorem divisorProj_translateEndo (h₂ : W.Equation x₂ y₂) {f : W.FunctionField} (hf : f ≠ 0) :
    divisorProj W (CoordinateRing.translateEndo h₂ f)
      = (divisorProj W f).mapDomain (mapProjPoint W (CoordinateRing.translateAlgEquiv h₂)) := by
  have h := divisorProj_algEquiv (CoordinateRing.translateAlgEquiv h₂) hf
  rwa [CoordinateRing.translateAlgEquiv_apply] at h

end Translation

end WeierstrassCurve.Affine
