/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import EllipticCurves.FunctionField.DivisorClassGroup
import EllipticCurves.FunctionField.DivisorInjective
import EllipticCurves.FunctionField.PointClosedPoint
import EllipticCurves.Torsion.Defs

/-!
# The principality criterion: a divisor is principal iff its class vanishes

Every principality question on the affine chart of a Weierstrass curve — "is this divisor
`D : HeightOneSpectrum F[W] →₀ ℤ` of the form `divisor W g` for some `g ≠ 0`?" — could until now
only be answered by *exhibiting* `g`, because all the maps went the wrong way:
`divisorHom` sends functions to divisors, `classGroup_mk_toPrincipalIdeal` says a principal
fractional ideal is class-trivial, and `exists_unit_of_divisor_eq` is the *injectivity* of
`divisor`.  Nothing turned a divisor into a class.

This file supplies the missing direction and closes the loop:

```
∃ g ≠ 0, divisor W g = D   ↔   classOfDivisor F(W) D = 1.
```

## Route

The construction is not curve-specific and is stated for an arbitrary Dedekind domain `R` with
fraction field `K`, in the `IsDedekindDomain.HeightOneSpectrum` namespace, exactly as
`DivisorInjective.lean` already does for `eq_of_count_eq`:

* `idealOfDivisor K D = ∏ v ∈ D.support, (v.asIdeal : FractionalIdeal R⁰ K) ^ D v`, the fractional
  ideal of a divisor.  It is nonzero, and Mathlib's `count_finsuppProd` says its `count` at `v` is
  `D v` on the nose — the round trip that makes the construction usable;
* `classOfDivisor K D = ClassGroup.mk K ⟨idealOfDivisor K D⟩`, and `classOfDivisorHom`, which is a
  monoid homomorphism out of the divisor group.  Without the homomorphism the criterion is a
  curiosity; with it, the class of a sum is computed termwise;
* `exists_spanSingleton_eq_iff_classOfDivisor_eq_one`, the criterion at the level of Dedekind
  domains, off `ClassGroup.mk_eq_one_iff`.

On the curve, `ord v f` is *defined* as `count K v ⟨f⟩` (`Divisors.lean`), so
`idealOfDivisor F(W) (divisor W f) = ⟨f⟩` for `f ≠ 0` (`idealOfDivisor_divisor`), and the two
directions are honest inverses on principal divisors.

## The payoff: the converse of `exists_generator_divisor_eq_of_torsion`

Composing the criterion with Mathlib's `Point.toClass` — whose value at an affine point is the class
of `⟨X - x, Y - y⟩`, i.e. exactly the class of the closed point `pointClosedPoint`
(`classOfDivisor_single_pointClosedPoint`) — turns principality of a divisor supported at one
rational point into a statement about the **group law**:

```
(∃ g ≠ 0, divisor W g = n·(P))   ↔   P ∈ E[n].
```

The `←` direction is `exists_generator_divisor_eq_of_torsion` (`PrincipalDivisorOfPoint.lean`,
`#409`); the `→` direction is new here, and with it `n·(P)` is principal for *no other* reason than
torsion.  At `n = 1` it says a single affine rational point is **never** a principal divisor, which
is the certificate that the criterion has teeth: it rules out functions that no amount of
exhibiting could rule out.

## The affine-chart caveat (`#409`)

`Point.toClass` is affine and so is the divisor calculus here, so no degree normalisation appears
anywhere: the classical statement "`(P) − (O)` is principal iff `P = O`" reads on this chart as
"`(P)` is principal iff `P = O`", the `(O)` term being invisible off the affine chart exactly as
`Divisors.lean` and `PrincipalDivisorOfPoint.lean` document.  Nothing here needs the projective
completion.

## Scope

Fully ungated: no Ward (`#260`, since closed anyway), no `#404` (likewise), no rung 4, no `hprin`,
no normality — only the standing
`[IsDedekindDomain W.CoordinateRing]` (`#396`) that the whole divisor calculus carries, and, for the
Dedekind-level results, nothing at all beyond `[IsDedekindDomain R]`.

## Main results

* `IsDedekindDomain.HeightOneSpectrum.idealOfDivisor`, `count_idealOfDivisor`,
  `idealOfDivisor_ne_zero`, `idealOfDivisor_add`, `idealOfDivisor_single`;
* `IsDedekindDomain.HeightOneSpectrum.classOfDivisor`, `classOfDivisorHom`, `classOfDivisor_add`;
* `IsDedekindDomain.HeightOneSpectrum.exists_spanSingleton_eq_iff_classOfDivisor_eq_one`;
* `WeierstrassCurve.Affine.idealOfDivisor_divisor`,
  `WeierstrassCurve.Affine.exists_divisor_eq_iff_classOfDivisor_eq_one`;
* `WeierstrassCurve.Affine.classOfDivisor_single_pointClosedPoint`, the `toClass` bridge;
* `WeierstrassCurve.Affine.exists_divisor_eq_single_iff_mem_torsion` and
  `not_exists_divisor_eq_single_pointClosedPoint`.

## Non-vacuity

The Dedekind-level results are certified at `R = ℤ`, `K = ℚ` at the end of the file, where the class
group is trivial and the criterion degenerates correctly.  The `F[W]`-level results inherit
`[IsDedekindDomain W.CoordinateRing]`, and ⚠️ that is **not** an obstruction to instantiating them
on a concrete curve, though an earlier version of this paragraph said it was: the hypothesis is a
global instance for `[W.IsElliptic]` over an arbitrary field
(`EllipticCurves.FunctionField.CoordinateRingNormalGeneral`), so it is discharged by instance
search.  `not_exists_divisor_eq_single_pointClosedPoint` shows they are not vacuous as statements
about a Dedekind coordinate ring.

## References

Silverman, *The Arithmetic of Elliptic Curves*, II.3 (divisors and the Picard group) and III.3.4
(the group law is the class-group map); Stichtenoth, *Algebraic Function Fields and Codes*, I.4.
-/

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum FractionalIdeal

open scoped nonZeroDivisors

namespace IsDedekindDomain.HeightOneSpectrum

variable {R : Type*} [CommRing R] [IsDedekindDomain R]
  (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K]

/-! ### The fractional ideal of a divisor -/

/-- **The fractional ideal of a divisor.** For a divisor `D : HeightOneSpectrum R →₀ ℤ` over a
Dedekind domain `R` with fraction field `K`, the finite product

```
idealOfDivisor K D = ∏ v ∈ D.support, (v.asIdeal : FractionalIdeal R⁰ K) ^ D v.
```

This is the map missing from the divisor calculus: `divisor` and `ord` go from functions to
divisors, and this goes back. -/
noncomputable def idealOfDivisor (D : HeightOneSpectrum R →₀ ℤ) : FractionalIdeal R⁰ K :=
  D.prod fun v n => (v.asIdeal : FractionalIdeal R⁰ K) ^ n

/-- **The round trip.** The `v`-adic multiplicity of `idealOfDivisor K D` is `D v`, so no
information is lost in passing from a divisor to its fractional ideal. -/
@[simp]
theorem count_idealOfDivisor (v : HeightOneSpectrum R) (D : HeightOneSpectrum R →₀ ℤ) :
    count K v (idealOfDivisor K D) = D v :=
  count_finsuppProd K v D

/-- The fractional ideal of a divisor is nonzero: it is a finite product of powers of the nonzero
fractional ideals `v.asIdeal`. -/
theorem idealOfDivisor_ne_zero (D : HeightOneSpectrum R →₀ ℤ) : idealOfDivisor K D ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr fun v _ => zpow_ne_zero _ (coeIdeal_ne_zero.mpr v.ne_bot)

@[simp]
theorem idealOfDivisor_zero : idealOfDivisor K (0 : HeightOneSpectrum R →₀ ℤ) = 1 :=
  Finsupp.prod_zero_index

/-- The fractional ideal of a divisor supported at a single closed point. -/
@[simp]
theorem idealOfDivisor_single (v : HeightOneSpectrum R) (n : ℤ) :
    idealOfDivisor K (Finsupp.single v n) = (v.asIdeal : FractionalIdeal R⁰ K) ^ n :=
  Finsupp.prod_single_index (zpow_zero _)

/-- **`idealOfDivisor` is additive-to-multiplicative.** Proved by comparing counts: both sides are
nonzero and `count` is additive under multiplication, so `eq_of_count_eq` applies. This is what
makes the criterion below usable — the class of a sum of divisors is computed termwise. -/
theorem idealOfDivisor_add (D₁ D₂ : HeightOneSpectrum R →₀ ℤ) :
    idealOfDivisor K (D₁ + D₂) = idealOfDivisor K D₁ * idealOfDivisor K D₂ := by
  refine eq_of_count_eq (idealOfDivisor_ne_zero K _)
    (mul_ne_zero (idealOfDivisor_ne_zero K D₁) (idealOfDivisor_ne_zero K D₂)) fun v => ?_
  rw [count_idealOfDivisor, count_mul K v (idealOfDivisor_ne_zero K D₁)
    (idealOfDivisor_ne_zero K D₂), count_idealOfDivisor, count_idealOfDivisor, Finsupp.add_apply]

/-- The unit of the group of fractional ideals attached to a divisor. Over a Dedekind domain the
nonzero fractional ideals are exactly the units, so this loses nothing. -/
noncomputable def unitOfDivisor (D : HeightOneSpectrum R →₀ ℤ) : (FractionalIdeal R⁰ K)ˣ :=
  Units.mk0 (idealOfDivisor K D) (idealOfDivisor_ne_zero K D)

@[simp]
theorem coe_unitOfDivisor (D : HeightOneSpectrum R →₀ ℤ) :
    (unitOfDivisor K D : FractionalIdeal R⁰ K) = idealOfDivisor K D :=
  rfl

/-- `unitOfDivisor`, packaged as a group homomorphism from the divisor group (written
multiplicatively) to the group of nonzero fractional ideals. -/
noncomputable def unitOfDivisorHom :
    Multiplicative (HeightOneSpectrum R →₀ ℤ) →* (FractionalIdeal R⁰ K)ˣ where
  toFun D := unitOfDivisor K (Multiplicative.toAdd D)
  map_one' := Units.ext (idealOfDivisor_zero K)
  map_mul' _ _ := Units.ext (idealOfDivisor_add K _ _)

@[simp]
theorem unitOfDivisorHom_apply (D : Multiplicative (HeightOneSpectrum R →₀ ℤ)) :
    unitOfDivisorHom K D = unitOfDivisor K (Multiplicative.toAdd D) :=
  rfl

/-! ### The class of a divisor -/

/-- **The class of a divisor** in `ClassGroup R`. This is the map that was missing: it lets one ask
whether a divisor is principal without exhibiting a generator. -/
noncomputable def classOfDivisor (D : HeightOneSpectrum R →₀ ℤ) : ClassGroup R :=
  ClassGroup.mk K (unitOfDivisor K D)

/-- `classOfDivisor`, as a group homomorphism from the divisor group. -/
noncomputable def classOfDivisorHom :
    Multiplicative (HeightOneSpectrum R →₀ ℤ) →* ClassGroup R :=
  (ClassGroup.mk K).comp (unitOfDivisorHom K)

@[simp]
theorem classOfDivisorHom_apply (D : Multiplicative (HeightOneSpectrum R →₀ ℤ)) :
    classOfDivisorHom K D = classOfDivisor K (Multiplicative.toAdd D) :=
  rfl

@[simp]
theorem classOfDivisor_zero : classOfDivisor K (0 : HeightOneSpectrum R →₀ ℤ) = 1 :=
  map_one (classOfDivisorHom K)

/-- **The class of a sum is the product of the classes** — the additivity that makes the criterion
worth having: the class of `∑ᵢ nᵢ·(Pᵢ)` is computed one point at a time. -/
theorem classOfDivisor_add (D₁ D₂ : HeightOneSpectrum R →₀ ℤ) :
    classOfDivisor K (D₁ + D₂) = classOfDivisor K D₁ * classOfDivisor K D₂ :=
  map_mul (classOfDivisorHom K) (Multiplicative.ofAdd D₁) (Multiplicative.ofAdd D₂)

/-- The class of `n • D` is the `n`-th power of the class of `D`. -/
theorem classOfDivisor_nsmul (D : HeightOneSpectrum R →₀ ℤ) (n : ℕ) :
    classOfDivisor K (n • D) = classOfDivisor K D ^ n :=
  map_pow (classOfDivisorHom K) (Multiplicative.ofAdd D) n

/-! ### The principality criterion -/

/-- **The principality criterion, over an arbitrary Dedekind domain.** A divisor's fractional ideal
is principal exactly when its class vanishes.

`←` is `ClassGroup.mk_eq_one_iff` (which produces a generator of the underlying submodule) together
with the nonvanishing of `idealOfDivisor`; `→` is the same equivalence in the easy direction. -/
theorem exists_spanSingleton_eq_iff_classOfDivisor_eq_one (D : HeightOneSpectrum R →₀ ℤ) :
    (∃ x : K, x ≠ 0 ∧ spanSingleton R⁰ x = idealOfDivisor K D) ↔ classOfDivisor K D = 1 := by
  rw [classOfDivisor, ClassGroup.mk_eq_one_iff]
  constructor
  · rintro ⟨x, -, hx⟩
    exact ⟨⟨x, by rw [coe_unitOfDivisor, ← hx, coe_spanSingleton]⟩⟩
  · rintro ⟨x, hx⟩
    have hspan : idealOfDivisor K D = spanSingleton R⁰ x :=
      coeToSubmodule_injective (by simpa [coe_spanSingleton] using hx)
    refine ⟨x, ?_, hspan.symm⟩
    rintro rfl
    exact idealOfDivisor_ne_zero K D (by rwa [spanSingleton_zero] at hspan)

end IsDedekindDomain.HeightOneSpectrum

namespace WeierstrassCurve.Affine

open CoordinateRing

variable {F : Type*} [Field F] {W : Affine F} [IsDedekindDomain W.CoordinateRing]

/-! ### The round trip against `divisor` -/

/-- **The fractional ideal of a principal divisor is the principal ideal.** Since `ord v f` is by
definition `count K v ⟨f⟩`, the two constructions are inverse on principal divisors: this is the
identity `idealOfDivisor F(W) (div f) = ⟨f⟩`. -/
theorem idealOfDivisor_divisor {f : W.FunctionField} (hf : f ≠ 0) :
    idealOfDivisor W.FunctionField (divisor W f) = spanSingleton W.CoordinateRing⁰ f := by
  have hspan : spanSingleton W.CoordinateRing⁰ f ≠ 0 := by
    rwa [ne_eq, spanSingleton_eq_zero_iff]
  refine eq_of_count_eq (idealOfDivisor_ne_zero W.FunctionField _) hspan fun v => ?_
  rw [count_idealOfDivisor, divisor_apply, ord]

/-- **The principality criterion on a Weierstrass curve.** A divisor of the affine chart is the
divisor of a nonzero rational function exactly when its class in `ClassGroup F[W]` is trivial.

This is the tool every `hprin`-shaped question in this tree wants: it replaces "exhibit a generator"
by "compute a class", and the class is computed termwise by `classOfDivisor_add`. -/
theorem exists_divisor_eq_iff_classOfDivisor_eq_one
    (D : HeightOneSpectrum W.CoordinateRing →₀ ℤ) :
    (∃ g : W.FunctionField, g ≠ 0 ∧ divisor W g = D) ↔
      classOfDivisor W.FunctionField D = 1 := by
  rw [← exists_spanSingleton_eq_iff_classOfDivisor_eq_one]
  constructor
  · rintro ⟨g, hg, rfl⟩
    exact ⟨g, hg, (idealOfDivisor_divisor hg).symm⟩
  · rintro ⟨g, hg, hspan⟩
    refine ⟨g, hg, ?_⟩
    ext v
    rw [divisor_apply, ord, hspan, count_idealOfDivisor]

/-! ### The bridge to `Point.toClass` -/

variable [DecidableEq F] {x y : F}

/-- **The class of a rational point, as a divisor, is its `toClass`.** Mathlib's
`Point.toClass` sends an affine point `(x, y)` to the class of `⟨X - x, Y - y⟩`, and that ideal is
by definition the closed point `pointClosedPoint`.  So the class-group map of the divisor calculus
and the class-group map underlying the *group law* are the same map on rational points.

No degree normalisation intervenes: both sides are affine (see the module docstring). -/
theorem classOfDivisor_single_pointClosedPoint (h : W.Nonsingular x y) :
    classOfDivisor W.FunctionField (Finsupp.single (pointClosedPoint h.left) (1 : ℤ)) =
      Additive.toMul (Point.toClass (Point.some x y h)) := by
  refine congrArg (ClassGroup.mk W.FunctionField) (Units.ext ?_)
  rw [coe_unitOfDivisor, idealOfDivisor_single, zpow_one, pointClosedPoint_asIdeal,
    ← XYIdeal'_eq (W := W) h]

/-- The class of `n·(P)` is the `n`-th power of the class of `P` — `classOfDivisor_nsmul`
specialised through the `toClass` bridge. -/
theorem classOfDivisor_single_pointClosedPoint_natCast (h : W.Nonsingular x y) (n : ℕ) :
    classOfDivisor W.FunctionField (Finsupp.single (pointClosedPoint h.left) (n : ℤ)) =
      Additive.toMul (Point.toClass (Point.some x y h)) ^ n := by
  rw [← classOfDivisor_single_pointClosedPoint h, ← classOfDivisor_nsmul,
    Finsupp.smul_single, nsmul_eq_mul, mul_one]

/-- **`n·(P)` is a principal divisor exactly when `P` is `n`-torsion.**

The `←` direction is `exists_generator_divisor_eq_of_torsion` (`#409`), which produces the rung-1
function `f_P` from the principal-ideal statement.  The `→` direction is the content added here: it
says `n·(P)` is principal for *no other reason* than torsion, which no amount of exhibiting
generators could establish.

Together with `exists_divisor_eq_iff_classOfDivisor_eq_one` this is the affine incarnation of
Silverman III.3.4: the group law on `E` *is* the class-group map. -/
theorem exists_divisor_eq_single_iff_mem_torsion (h : W.Nonsingular x y) (n : ℕ) :
    (∃ g : W.FunctionField, g ≠ 0 ∧
        divisor W g = Finsupp.single (pointClosedPoint h.left) (n : ℤ)) ↔
      Point.some x y h ∈ W.torsion n := by
  rw [exists_divisor_eq_iff_classOfDivisor_eq_one,
    classOfDivisor_single_pointClosedPoint_natCast h n, mem_torsion_iff,
    ← Point.toClass_eq_zero, map_nsmul]
  rfl

omit [DecidableEq F] in
/-- **A single affine rational point is never a principal divisor.** The `n = 1` case of
`exists_divisor_eq_single_iff_mem_torsion`: no nonzero rational function has a simple zero at
`(x, y)` and no other zero or pole on the affine chart, because `(x, y) ≠ O`.

This is the certificate that the criterion is not vacuous — it *rules out* functions, which the
existing exhibiting-a-generator machinery structurally cannot do.

Note the statement mentions no group law, hence no `DecidableEq F`: it is a bare assertion about
rational functions, and only its *proof* passes through the class group. -/
theorem not_exists_divisor_eq_single_pointClosedPoint (h : W.Nonsingular x y) :
    ¬ ∃ g : W.FunctionField, g ≠ 0 ∧
      divisor W g = Finsupp.single (pointClosedPoint h.left) (1 : ℤ) := by
  classical
  intro hex
  have h1 : Point.some x y h ∈ W.torsion 1 := by
    rw [← exists_divisor_eq_single_iff_mem_torsion h 1]
    simpa using hex
  exact Point.some_ne_zero h (by simpa using mem_torsion_iff.mp h1)

/-- Consistency check: the `←` direction of `exists_divisor_eq_single_iff_mem_torsion` is verbatim
the conclusion of `exists_generator_divisor_eq_of_torsion` (`PrincipalDivisorOfPoint.lean`, `#409`),
so the criterion agrees with the already-merged production of `f_P` and the content added above is
exactly the forward direction. -/
example (h : W.Nonsingular x y) {n : ℕ} (hP : Point.some x y h ∈ W.torsion n) :
    ∃ f : W.FunctionField, f ≠ 0 ∧
      divisor W f = Finsupp.single (pointClosedPoint h.left) (n : ℤ) :=
  (exists_divisor_eq_single_iff_mem_torsion h n).mpr hP

end WeierstrassCurve.Affine

/-! ### Non-vacuity over `ℤ`

The Dedekind-level constructions are instantiated at `R = ℤ`, `K = ℚ`, where every divisor is
principal because `ℤ` is a principal ideal domain, so the criterion's right-hand side always holds
and its left-hand side really does produce a generator. -/

section Nonvacuity

open IsDedekindDomain.HeightOneSpectrum

example (D : HeightOneSpectrum ℤ →₀ ℤ) : idealOfDivisor ℚ D ≠ 0 :=
  idealOfDivisor_ne_zero ℚ D

example (v : HeightOneSpectrum ℤ) (D : HeightOneSpectrum ℤ →₀ ℤ) :
    FractionalIdeal.count ℚ v (idealOfDivisor ℚ D) = D v :=
  count_idealOfDivisor ℚ v D

/-- Over `ℤ` every divisor is principal, so the criterion produces a generator for each one. -/
example (D : HeightOneSpectrum ℤ →₀ ℤ) :
    ∃ x : ℚ, x ≠ 0 ∧ FractionalIdeal.spanSingleton (ℤ⁰) x = idealOfDivisor ℚ D := by
  have : Subsingleton (ClassGroup ℤ) :=
    Fintype.card_le_one_iff_subsingleton.mp card_classGroup_eq_one.le
  exact (exists_spanSingleton_eq_iff_classOfDivisor_eq_one ℚ D).mpr (Subsingleton.elim _ _)

end Nonvacuity
