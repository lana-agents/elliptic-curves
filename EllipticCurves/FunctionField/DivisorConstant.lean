/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import EllipticCurves.FunctionField.CoordinateRingUnits
import EllipticCurves.FunctionField.DivisorClassGroup
import EllipticCurves.FunctionField.DivisorInjective
import EllipticCurves.FunctionField.DivisorTheoryElliptic
import EllipticCurves.FunctionField.TranslationPullback

/-!
# A rational function with trivial divisor is a nonzero constant

`EllipticCurves.FunctionField.DivisorInjective` (`#402`) proves that a nonzero rational function on
a Weierstrass curve is determined by its divisor **up to a unit of the coordinate ring `F[W]`**.
Its module docstring cites Silverman II.3, which states the sharper classical fact: the ambiguity
is exactly an **`F*`-scalar**. This file closes that gap, and records the `divisor = 0` special
case that the ambiguity statement specialises to.

The two facts are the same fact. `#402` produces a unit `u : F[W]ˣ`, and
`EllipticCurves.FunctionField.CoordinateRingUnits`'s `exists_eq_algebraMap_of_isUnit` (`#419`) says
that every unit of the affine coordinate ring of a Weierstrass curve is a nonzero constant — the
affine coordinate ring has no interesting units, because a unit would have to have degree `0` in
the `{1, Y}`-basis over `F[X]`. Composing the two turns `F[W]ˣ` into `F*`, which is the form every
consumer actually wants: `F[W]ˣ` is opaque, whereas an `F*`-scalar can be cancelled, moved through
`translateEndo` (an `F`-algebra map), and compared with an `n`-th root of unity.

## Main results

* `WeierstrassCurve.Affine.exists_eq_algebraMap_of_divisor_eq_zero` — a nonzero `f` with
  `divisor W f = 0` is `algebraMap F F(W) c` for a nonzero `c : F`. This is the affine form of
  "a function with no zeros and no poles is constant".
* `WeierstrassCurve.Affine.divisor_eq_zero_iff` — its `iff`, the converse being
  `divisor_algebraMap_base`.
* `WeierstrassCurve.Affine.exists_scalar_of_divisor_eq` / `exists_scalar_of_ord_eq` — the
  `F*`-strengthening of `#402`'s `exists_unit_of_divisor_eq` / `exists_unit_of_ord_eq`.
* `WeierstrassCurve.Affine.divisor_eq_iff_exists_scalar` — the resulting characterisation
  `divisor W f = divisor W g ↔ ∃ c ≠ 0, c • f = g`.

Each of these is re-exposed in the `WeierstrassCurve.Affine.Elliptic` namespace with the
`[IsDedekindDomain W.CoordinateRing]` hypothesis discharged by `[W.IsElliptic]`, following
`EllipticCurves.FunctionField.DivisorTheoryElliptic`. That is the form the rung-5/6 files can use:
`WeilPairingAlternating.lean` and its peers run under `[W.IsElliptic]` and carry no Dedekind
hypothesis, so the conditional forms would not apply to them without a rewrite at each site.

## Why this is wanted

The product-over-`⟨T⟩` / divisor-telescoping argument for the **alternating property**
`e_n(T, T) = 1` (issue `#465`, deliverable 2) runs: form `h := ∏_{i} τ_{[i]T}∗ f_T`, show
`div h = 0` by telescoping, conclude that `h` is a **nonzero constant**, and read off
`τ_T∗ g_T = g_T`. The last two steps are exactly `divisor_eq_zero_iff`, and the review thread on
`#465` named this "`divisor = 0 ⟹ constant` convenience" as one of the three pieces that step still
needed. It is the one of the three that is **not** gated: it needs neither rung 4/5 nor the
divisor-pullback-under-translation formula, only `#402` and `#419`.

It is equally the honest form of the well-definedness backbone of the pairing itself: the rung-1
generator `f_P` with `div f_P = n·(P) − n·(O)` is canonical **up to `F*`**, not merely up to
`F[W]ˣ`, and it is the `F*` statement that makes `e_n(S, T)` independent of the choice of `f_S`.

## Non-degeneracy

`divisor_eq_zero_iff` would be vacuous if every function had trivial divisor, or if
`[IsDedekindDomain W.CoordinateRing]` were unsatisfiable. Neither holds:

* `WeierstrassCurve.Affine.divisor_genX_ne_zero` — the generic `x`-coordinate `genX W` has
  **nonzero** divisor. It is not a constant (`genX_ne`, `#406`) and it is nonzero, so the theorem
  above applies in the contrapositive. So `divisor W f = 0` is a genuine restriction.
* The hypothesis is discharged for every elliptic curve by
  `EllipticCurves.FunctionField.DivisorTheoryElliptic`'s `IsDedekindDomain W.CoordinateRing`
  instance under `[W.IsElliptic]` — which is exactly what the `Elliptic` namespace below uses, so
  the unconditional forms are themselves the certificate that the hypothesis is satisfiable.

Nothing here bounds the *degree* of a divisor or uses the point at infinity; the statement is about
the affine closed points only, which is why "no zeros or poles" reads as "no zeros or poles in the
affine chart" and the conclusion is nevertheless the full classical one — the affine coordinate ring
has no non-constant units.

## Scope

Ward-independent, rung-4/5-independent, and normality-independent: `[IsDedekindDomain
W.CoordinateRing]` is carried as a hypothesis exactly as in `Divisors.lean`, `DivisorInjective.lean`
and `DivisorClassGroup.lean`.

## References

* [J. H. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], II.3.
-/

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum FractionalIdeal
open scoped nonZeroDivisors

namespace WeierstrassCurve.Affine

variable {F : Type*} [Field F] {W : Affine F} [IsDedekindDomain W.CoordinateRing]

/-! ### Constants have trivial divisor -/

/-- **A nonzero constant has no zeros and no poles.** The image of `c ≠ 0` under
`algebraMap F F(W)` is the image of a unit of `F[W]`, so `ord_coe_units` applies. -/
@[simp]
lemma ord_algebraMap_base {c : F} (hc : c ≠ 0) (v : HeightOneSpectrum W.CoordinateRing) :
    ord v (algebraMap F W.FunctionField c) = 0 := by
  have h := ord_coe_units (W := W) ((Ne.isUnit hc).map (algebraMap F W.CoordinateRing)).unit v
  rwa [IsUnit.unit_spec, ← IsScalarTower.algebraMap_apply F W.CoordinateRing W.FunctionField] at h

/-- **The divisor of a nonzero constant is trivial.** -/
@[simp]
lemma divisor_algebraMap_base {c : F} (hc : c ≠ 0) :
    divisor W (algebraMap F W.FunctionField c) = 0 := by
  ext v
  simp [hc]

/-! ### Trivial divisor forces a constant -/

/-- **A rational function with trivial divisor is a nonzero constant.**

The affine form of "a function on a complete curve with no zeros and no poles is constant". By
`exists_unit_of_divisor_eq` (`#402`) applied against `1`, such an `f` satisfies `u • f = 1` for a
unit `u : F[W]ˣ`; by `exists_eq_algebraMap_of_isUnit` (`#419`) that unit is a nonzero constant
`c : F`, and `f = c⁻¹`.

Note that only the *affine* closed points enter: the conclusion is nonetheless the classical one,
because the affine coordinate ring of a Weierstrass curve has no non-constant units. -/
theorem exists_eq_algebraMap_of_divisor_eq_zero {f : W.FunctionField} (hf : f ≠ 0)
    (h : divisor W f = 0) : ∃ c : F, c ≠ 0 ∧ f = algebraMap F W.FunctionField c := by
  obtain ⟨u, hu⟩ := exists_unit_of_divisor_eq hf one_ne_zero (by rw [h, divisor_one])
  obtain ⟨c, hc⟩ := CoordinateRing.exists_eq_algebraMap_of_isUnit u.isUnit
  rw [hc, Algebra.smul_def,
    ← IsScalarTower.algebraMap_apply F W.CoordinateRing W.FunctionField] at hu
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [map_zero, zero_mul] at hu
    exact zero_ne_one hu
  refine ⟨c⁻¹, inv_ne_zero hc0, ?_⟩
  rw [map_inv₀]
  exact eq_inv_of_mul_eq_one_left (by rwa [mul_comm] at hu)

/-- **Trivial divisor characterises the nonzero constants.** -/
theorem divisor_eq_zero_iff {f : W.FunctionField} (hf : f ≠ 0) :
    divisor W f = 0 ↔ ∃ c : F, c ≠ 0 ∧ f = algebraMap F W.FunctionField c := by
  refine ⟨exists_eq_algebraMap_of_divisor_eq_zero hf, ?_⟩
  rintro ⟨c, hc, rfl⟩
  exact divisor_algebraMap_base hc

/-- **A non-constant rational function has a zero or a pole** — the contrapositive of
`exists_eq_algebraMap_of_divisor_eq_zero`, and the direction the telescoping argument of `#465`
uses in reverse. -/
theorem divisor_ne_zero_of_forall_ne {f : W.FunctionField} (hf : f ≠ 0)
    (h : ∀ c : F, f ≠ algebraMap F W.FunctionField c) : divisor W f ≠ 0 := fun hd => by
  obtain ⟨c, -, hfc⟩ := exists_eq_algebraMap_of_divisor_eq_zero hf hd
  exact h c hfc

/-! ### The `F*`-strengthening of `#402` -/

/-- **The divisor determines a rational function up to an `F*`-scalar** (order form).

This is the sharp form of `exists_unit_of_ord_eq` (`#402`), which produces only a unit of `F[W]`.
The two agree because `F[W]ˣ = F*` (`exists_eq_algebraMap_of_isUnit`, `#419`), but the `F*` form is
what consumers need: an `F*`-scalar can be cancelled, and it commutes with every `F`-algebra
endomorphism of `F(W)` — `translateEndo` in particular. -/
theorem exists_scalar_of_ord_eq {f g : W.FunctionField} (hf : f ≠ 0) (hg : g ≠ 0)
    (h : ∀ v : HeightOneSpectrum W.CoordinateRing, ord v f = ord v g) :
    ∃ c : F, c ≠ 0 ∧ algebraMap F W.FunctionField c * f = g := by
  obtain ⟨u, hu⟩ := exists_unit_of_ord_eq hf hg h
  obtain ⟨c, hc⟩ := CoordinateRing.exists_eq_algebraMap_of_isUnit u.isUnit
  rw [hc, Algebra.smul_def,
    ← IsScalarTower.algebraMap_apply F W.CoordinateRing W.FunctionField] at hu
  refine ⟨c, ?_, hu⟩
  rintro rfl
  rw [map_zero, zero_mul] at hu
  exact hg hu.symm

/-- **The divisor determines a rational function up to an `F*`-scalar** (divisor form) — the
statement Silverman II.3 makes and `DivisorInjective.lean` cites but does not prove. -/
theorem exists_scalar_of_divisor_eq {f g : W.FunctionField} (hf : f ≠ 0) (hg : g ≠ 0)
    (h : divisor W f = divisor W g) :
    ∃ c : F, c ≠ 0 ∧ algebraMap F W.FunctionField c * f = g := by
  refine exists_scalar_of_ord_eq hf hg fun v => ?_
  have := DFunLike.congr_fun h v
  rwa [divisor_apply, divisor_apply] at this

/-- **Equality of divisors is exactly equality up to an `F*`-scalar.** -/
theorem divisor_eq_iff_exists_scalar {f g : W.FunctionField} (hf : f ≠ 0) (hg : g ≠ 0) :
    divisor W f = divisor W g ↔
      ∃ c : F, c ≠ 0 ∧ algebraMap F W.FunctionField c * f = g := by
  refine ⟨exists_scalar_of_divisor_eq hf hg, ?_⟩
  rintro ⟨c, hc, rfl⟩
  rw [divisor_mul ((map_ne_zero_iff _ (algebraMap F W.FunctionField).injective).mpr hc) hf,
    divisor_algebraMap_base hc, zero_add]

/-! ### Non-degeneracy: not every function has trivial divisor -/

/-- **The generic `x`-coordinate has a nonzero divisor.**

`genX W` is the image in `F(W)` of the coordinate function `x`, and `genX_ne` (`#406`) says it
differs from `algebraMap F F(W) c` for **every** `c : F` — in particular from `0`. So
`divisor_ne_zero_of_forall_ne` applies, and `divisor W f = 0` is a genuine restriction rather than
a property every rational function enjoys. -/
theorem divisor_genX_ne_zero : divisor W (CoordinateRing.genX W) ≠ 0 :=
  divisor_ne_zero_of_forall_ne
    (fun h => CoordinateRing.genX_ne (W := W) 0 (by rw [h, map_zero]))
    (fun c => CoordinateRing.genX_ne c)

/-! ### Unconditional forms for an elliptic curve

`EllipticCurves.FunctionField.DivisorTheoryElliptic` re-exposes the divisor calculus in the
`Elliptic` namespace with `[IsDedekindDomain W.CoordinateRing]` discharged by the normality
instance for `[W.IsElliptic]`. The results above get the same treatment, because that is the form
the rung-5/6 consumers can use: `WeilPairingAlternating.lean` and its peers all run under
`[W.IsElliptic]` and carry no Dedekind hypothesis. -/

namespace Elliptic

variable {F : Type*} [Field F] {W : Affine F} [W.IsElliptic]

/-- **A rational function with trivial divisor is a nonzero constant**, for an elliptic curve over
an arbitrary field. Unconditional in `[W.IsElliptic]`. -/
theorem exists_eq_algebraMap_of_divisor_eq_zero {f : W.FunctionField} (hf : f ≠ 0)
    (h : divisor W f = 0) : ∃ c : F, c ≠ 0 ∧ f = algebraMap F W.FunctionField c :=
  WeierstrassCurve.Affine.exists_eq_algebraMap_of_divisor_eq_zero hf h

/-- **Trivial divisor characterises the nonzero constants**, unconditional in `[W.IsElliptic]`.
This is the form the product-over-`⟨T⟩` telescoping of `#465` deliverable 2 consumes. -/
theorem divisor_eq_zero_iff {f : W.FunctionField} (hf : f ≠ 0) :
    divisor W f = 0 ↔ ∃ c : F, c ≠ 0 ∧ f = algebraMap F W.FunctionField c :=
  WeierstrassCurve.Affine.divisor_eq_zero_iff hf

/-- **A non-constant rational function has a zero or a pole**, unconditional in
`[W.IsElliptic]`. -/
theorem divisor_ne_zero_of_forall_ne {f : W.FunctionField} (hf : f ≠ 0)
    (h : ∀ c : F, f ≠ algebraMap F W.FunctionField c) : divisor W f ≠ 0 :=
  WeierstrassCurve.Affine.divisor_ne_zero_of_forall_ne hf h

/-- **The divisor determines a rational function up to an `F*`-scalar** (order form),
unconditional in `[W.IsElliptic]` — the sharp form of `Elliptic.exists_unit_of_ord_eq`. -/
theorem exists_scalar_of_ord_eq {f g : W.FunctionField} (hf : f ≠ 0) (hg : g ≠ 0)
    (h : ∀ v : IsDedekindDomain.HeightOneSpectrum W.CoordinateRing, ord v f = ord v g) :
    ∃ c : F, c ≠ 0 ∧ algebraMap F W.FunctionField c * f = g :=
  WeierstrassCurve.Affine.exists_scalar_of_ord_eq hf hg h

/-- **The divisor determines a rational function up to an `F*`-scalar** (divisor form),
unconditional in `[W.IsElliptic]`. This is Silverman II.3 as `DivisorTheoryElliptic.lean`'s own
docstring states it; `Elliptic.exists_unit_of_divisor_eq` proves only the `F[W]ˣ` form. -/
theorem exists_scalar_of_divisor_eq {f g : W.FunctionField} (hf : f ≠ 0) (hg : g ≠ 0)
    (h : divisor W f = divisor W g) :
    ∃ c : F, c ≠ 0 ∧ algebraMap F W.FunctionField c * f = g :=
  WeierstrassCurve.Affine.exists_scalar_of_divisor_eq hf hg h

/-- **Equality of divisors is exactly equality up to an `F*`-scalar**, unconditional in
`[W.IsElliptic]`. -/
theorem divisor_eq_iff_exists_scalar {f g : W.FunctionField} (hf : f ≠ 0) (hg : g ≠ 0) :
    divisor W f = divisor W g ↔
      ∃ c : F, c ≠ 0 ∧ algebraMap F W.FunctionField c * f = g :=
  WeierstrassCurve.Affine.divisor_eq_iff_exists_scalar hf hg

/-- **The generic `x`-coordinate has a nonzero divisor**, unconditional in `[W.IsElliptic]` — so
none of the statements in this namespace is vacuous. -/
theorem divisor_genX_ne_zero : divisor W (CoordinateRing.genX W) ≠ 0 :=
  WeierstrassCurve.Affine.divisor_genX_ne_zero

end Elliptic

end WeierstrassCurve.Affine
