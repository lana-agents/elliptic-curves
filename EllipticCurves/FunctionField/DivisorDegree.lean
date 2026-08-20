/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import EllipticCurves.FunctionField.DivisorConstant
import EllipticCurves.FunctionField.PlaceAtInfinity
import Mathlib.RingTheory.Ideal.Norm.RelNorm

/-!
# The degree of a divisor, and the degree-zero theorem

`EllipticCurves.FunctionField.PlaceAtInfinity` builds the place of `F(W)` at the point at infinity
and its order function `ordInfty`, alongside the affine orders `ord v` of
`EllipticCurves.FunctionField.Divisors`.  This file supplies the **global relation** between them:
a rational function has as many zeros as poles.

Each affine closed point `v` carries a degree `degPt v` — its residue degree over `F`, computed
here through Mathlib's relative ideal norm `Ideal.relNorm F[X] : Ideal F[W] →*₀ Ideal F[X]` — and
the point at infinity has degree `1` (it is `F`-rational: `x / y` is a uniformizer with residue
field `F`).  Weighting the affine orders by `degPt` gives the degree of a divisor, and

```
degDiv (div f) + ordInfty f = 0
```

for every `f ≠ 0`.  This is `deg (div f) = 0` on the projective curve, with the `−n·(O)` term that
`EllipticCurves.FunctionField.PrincipalDivisorOfPoint` had to leave off the affine chart now
accounted for by `ordInfty`.

## Main definitions

* `Ideal.natDegreeGenerator` — the degree of an ideal of `F[X]`, i.e. of a generator;
* `WeierstrassCurve.Affine.ordIdeal` / `divisorIdeal` — the order of an *ideal* of `F[W]` at a
  closed point, and the corresponding divisor.  These are what the factorisation induction runs on;
* `WeierstrassCurve.Affine.degPt` — the degree of a closed point;
* `WeierstrassCurve.Affine.degDiv` — the degree of a divisor, `∑_v D v · degPt v`.

## Main results

* `degX_relNorm` — for a nonzero ideal `I` of `F[W]`, the degree of `relNorm I` is the degree of
  the divisor of `I`.  Proved by induction over the prime factorisation of `I`, using
  multiplicativity of `relNorm` and additivity of both `degPt`-weighted counting and of the degree
  of ideals of `F[X]`;
* `deg_eq_degDiv` — the element form: `deg a = degDiv (div a)` for `a ∈ F[W]` nonzero, i.e. the
  order of the pole at infinity equals the total number of affine zeros counted with degrees;
* **`degDiv_divisor_add_ordInfty`** — the degree-zero theorem `degDiv (div f) + ordInfty f = 0`;
* `degPt_pos` — every closed point has positive degree.  Via the factorisation of the norm as
  `a · ā` (the hyperelliptic conjugate), which gives `relNorm I ≤ I ∩ F[X]`;
* **`divisor_eq_zero_of_nonneg`** and `exists_eq_algebraMap_of_nonneg` — a rational function with
  no pole anywhere, at an affine point *or* at infinity, is a nonzero constant.  This is
  `H⁰(E, 𝒪) = F`, and unlike `exists_eq_algebraMap_of_ordInfty_nonneg` (which assumes the function
  lies in `F[W]`) it assumes only pole-freeness.

## Consequences and what is still missing

`degPt v = 1` for the closed point of an `F`-rational point is **not** proved here; it needs the
residue field of `pointClosedPoint h` to be identified with `F`.  With it, the degree-zero theorem
upgrades `#409`'s `div f_S = n·(S)` to the full classical `n·(S) − n·(O)`, which is the shape the
Weil-pairing rungs want.  That is the natural next step and is deliberately out of scope here.

## Design

Everything carries `[IsDedekindDomain W.CoordinateRing]` as an explicit hypothesis, as
`Divisors.lean` does; for `[W.IsElliptic]` it is discharged by the normality instance and the
`Elliptic` namespace of `DivisorTheoryElliptic.lean` is the place to re-expose these unconditionally
if a consumer needs it.

Two `Prop`-valued instances are registered, `Module.Free F[X] F[W]` and `Module.Finite F[X] F[W]`.
Neither is in Mathlib (both fail `infer_instance` on `v4.32.0`) and `Ideal.relNorm` needs them.
They are `Prop` classes, so they carry no diamond risk, and they are immediate from Mathlib's
`CoordinateRing.basis`.

## References

* [J. H. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], II.3.
* Stichtenoth, *Algebraic Function Fields and Codes*, I.4 (the degree of a principal divisor).
-/

open Polynomial Polynomial.Bivariate IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open FractionalIdeal

open scoped nonZeroDivisors

namespace Ideal

variable {F : Type*} [Field F]

/-- The **degree of an ideal of `F[X]`**: the degree of a generator.  Well defined because two
generators differ by a unit, i.e. by a nonzero constant. -/
noncomputable def natDegreeGenerator (J : Ideal F[X]) : ℕ :=
  (Submodule.IsPrincipal.generator J).natDegree

@[simp]
lemma natDegreeGenerator_span (p : F[X]) : natDegreeGenerator (Ideal.span {p}) = p.natDegree := by
  unfold natDegreeGenerator
  have h : Associated (Submodule.IsPrincipal.generator (Ideal.span {p})) p := by
    rw [← Ideal.span_singleton_eq_span_singleton (α := F[X])]
    exact Ideal.span_singleton_generator _
  exact natDegree_eq_of_degree_eq (degree_eq_degree_of_associated h)

@[simp]
lemma natDegreeGenerator_top : natDegreeGenerator (⊤ : Ideal F[X]) = 0 := by
  rw [← Ideal.span_singleton_one, natDegreeGenerator_span, natDegree_one]

/-- The degree of an ideal of `F[X]` is additive. -/
lemma natDegreeGenerator_mul {I J : Ideal F[X]} (hI : I ≠ 0) (hJ : J ≠ 0) :
    natDegreeGenerator (I * J) = natDegreeGenerator I + natDegreeGenerator J := by
  obtain ⟨p, rfl⟩ : ∃ p, I = Ideal.span {p} := ⟨_, (Ideal.span_singleton_generator I).symm⟩
  obtain ⟨q, rfl⟩ : ∃ q, J = Ideal.span {q} := ⟨_, (Ideal.span_singleton_generator J).symm⟩
  rw [Ideal.span_singleton_mul_span_singleton, natDegreeGenerator_span, natDegreeGenerator_span,
    natDegreeGenerator_span]
  refine natDegree_mul ?_ ?_
  · simpa [Ideal.span_singleton_eq_bot] using hI
  · simpa [Ideal.span_singleton_eq_bot] using hJ

end Ideal

namespace WeierstrassCurve.Affine

open CoordinateRing

variable {F : Type*} [Field F] {W : Affine F}

/-- `F[W]` is a free `F[X]`-module: Mathlib provides the basis `{1, Y}` but no `Module.Free`
instance.  Needed by `Ideal.relNorm`. -/
noncomputable instance instModuleFreeCoordinateRing : Module.Free F[X] W.CoordinateRing :=
  Module.Free.of_basis (CoordinateRing.basis W)

/-- `F[W]` is a finite `F[X]`-module.  Needed by `Ideal.relNorm`. -/
noncomputable instance instModuleFiniteCoordinateRing : Module.Finite F[X] W.CoordinateRing :=
  Module.Finite.of_basis (CoordinateRing.basis W)

/-- The norm of `a ∈ F[W]`, pushed back into `F[W]`, is `a` times its conjugate under the
hyperelliptic involution, so it lies in every ideal `a` lies in. -/
lemma algebraMap_norm_mem {I : Ideal W.CoordinateRing} {a : W.CoordinateRing} (ha : a ∈ I) :
    algebraMap F[X] W.CoordinateRing (Algebra.norm F[X] a) ∈ I := by
  obtain ⟨p, q, rfl⟩ := exists_smul_basis_eq a
  rw [show algebraMap F[X] W.CoordinateRing (Algebra.norm F[X]
      (p • (1 : W.CoordinateRing) + q • CoordinateRing.mk W Y)) = Algebra.norm F[X]
      (p • (1 : W.CoordinateRing) + q • CoordinateRing.mk W Y) from rfl,
    coe_norm_smul_basis, map_mul]
  refine Ideal.mul_mem_right _ _ ?_
  convert ha using 1
  rw [map_add, map_mul]
  simp [CoordinateRing.smul, mul_comm]

variable [IsDedekindDomain W.CoordinateRing]

/-- The relative norm of an ideal is contained in it: `N(I) ⊆ I ∩ F[X]`. -/
lemma relNorm_le_comap (I : Ideal W.CoordinateRing) :
    Ideal.relNorm F[X] I ≤ I.comap (algebraMap F[X] W.CoordinateRing) := by
  rw [Ideal.relNorm_apply, Ideal.span_le]
  rintro _ ⟨a, ha, rfl⟩
  simp only [SetLike.mem_coe] at ha ⊢
  rw [Ideal.mem_comap, Algebra.intNorm_eq_norm]
  exact algebraMap_norm_mem ha

/-! ### Divisors of ideals -/

/-- The **order of an ideal** of `F[W]` at a closed point: the exponent of `v` in its
factorisation.  For a principal ideal this is the order of vanishing of a generator
(`divisorIdeal_span`). -/
noncomputable def ordIdeal (v : HeightOneSpectrum W.CoordinateRing) (I : Ideal W.CoordinateRing) :
    ℤ := count W.FunctionField v (I : FractionalIdeal W.CoordinateRing⁰ W.FunctionField)

variable (W) in
/-- The **divisor of an ideal** of `F[W]`. -/
noncomputable def divisorIdeal (I : Ideal W.CoordinateRing) :
    HeightOneSpectrum W.CoordinateRing →₀ ℤ :=
  Finsupp.ofSupportFinite (fun v => ordIdeal v I)
    (Filter.eventually_cofinite.mp (finite_factors (I : FractionalIdeal W.CoordinateRing⁰ _)))

@[simp]
lemma divisorIdeal_apply (I : Ideal W.CoordinateRing) (v : HeightOneSpectrum W.CoordinateRing) :
    divisorIdeal W I v = ordIdeal v I := rfl

/-- The divisor of a principal ideal is the divisor of a generator. -/
lemma divisorIdeal_span (a : W.CoordinateRing) :
    divisorIdeal W (Ideal.span {a})
      = divisor W (algebraMap W.CoordinateRing W.FunctionField a) := by
  ext v
  rw [divisorIdeal_apply, ordIdeal, divisor_apply, ord, coeIdeal_span_singleton]

@[simp]
lemma divisorIdeal_top : divisorIdeal W (⊤ : Ideal W.CoordinateRing) = 0 := by
  ext v
  rw [divisorIdeal_apply, ordIdeal, ← Ideal.one_eq_top, Ideal.one_eq_top, coeIdeal_top, count_one]
  rfl

lemma divisorIdeal_mul {I J : Ideal W.CoordinateRing} (hI : I ≠ 0) (hJ : J ≠ 0) :
    divisorIdeal W (I * J) = divisorIdeal W I + divisorIdeal W J := by
  ext v
  rw [divisorIdeal_apply, ordIdeal, Finsupp.add_apply, divisorIdeal_apply, divisorIdeal_apply,
    ordIdeal, ordIdeal, coeIdeal_mul, count_mul _ v (coeIdeal_ne_zero.mpr hI)
      (coeIdeal_ne_zero.mpr hJ)]

lemma divisorIdeal_prime (v : HeightOneSpectrum W.CoordinateRing) :
    divisorIdeal W v.asIdeal = Finsupp.single v 1 := by
  classical
  ext w
  rw [divisorIdeal_apply, ordIdeal, count_maximal, Finsupp.single_apply]

/-! ### The degree of a point and of a divisor -/

/-- The **degree of a closed point**: its residue degree over `F`, computed through the relative
ideal norm to `F[X]`. -/
noncomputable def degPt (v : HeightOneSpectrum W.CoordinateRing) : ℕ :=
  Ideal.natDegreeGenerator (Ideal.relNorm F[X] v.asIdeal)

variable (W) in
/-- The **degree of a divisor**: the sum of its coefficients weighted by the degrees of the
corresponding closed points. -/
noncomputable def degDiv (D : HeightOneSpectrum W.CoordinateRing →₀ ℤ) : ℤ :=
  D.sum fun v n => n * degPt v

@[simp]
lemma degDiv_zero : degDiv W (0 : HeightOneSpectrum W.CoordinateRing →₀ ℤ) = 0 :=
  Finsupp.sum_zero_index

lemma degDiv_add (D E : HeightOneSpectrum W.CoordinateRing →₀ ℤ) :
    degDiv W (D + E) = degDiv W D + degDiv W E :=
  Finsupp.sum_add_index' (fun _ => zero_mul _) (fun _ _ _ => add_mul _ _ _)

lemma degDiv_sub (D E : HeightOneSpectrum W.CoordinateRing →₀ ℤ) :
    degDiv W (D - E) = degDiv W D - degDiv W E := by
  have h := degDiv_add (W := W) (D - E) E
  rw [sub_add_cancel] at h
  omega

@[simp]
lemma degDiv_single (v : HeightOneSpectrum W.CoordinateRing) (n : ℤ) :
    degDiv W (Finsupp.single v n) = n * degPt v := by
  rw [degDiv, Finsupp.sum_single_index (zero_mul _)]

/-! ### The degree formula -/

/-- **The degree of the relative norm of an ideal is the degree of its divisor.**

Both sides are additive in the ideal — the left by multiplicativity of `Ideal.relNorm` and
additivity of `Ideal.natDegreeGenerator`, the right by `divisorIdeal_mul` — and they agree on
primes by the definition of `degPt`.  The proof is the corresponding induction over the prime
factorisation. -/
theorem natDegreeGenerator_relNorm (I : Ideal W.CoordinateRing) (hI : I ≠ 0) :
    (Ideal.natDegreeGenerator (Ideal.relNorm F[X] I) : ℤ) = degDiv W (divisorIdeal W I) := by
  induction I using UniqueFactorizationMonoid.induction_on_prime with
  | h₁ => exact absurd rfl hI
  | h₂ x hx =>
      rw [Ideal.isUnit_iff.mp hx, Ideal.relNorm_top, divisorIdeal_top, degDiv_zero,
        Ideal.natDegreeGenerator_top]
      rfl
  | h₃ a p ha hp ih =>
      have hp0 : p ≠ 0 := hp.ne_zero
      have hvp : p.IsPrime := (Ideal.prime_iff_isPrime hp0).mp hp
      set v : HeightOneSpectrum W.CoordinateRing := ⟨p, hvp, hp0⟩ with hv
      have hprime : (Ideal.natDegreeGenerator (Ideal.relNorm F[X] p) : ℤ)
          = degDiv W (divisorIdeal W p) := by
        rw [divisorIdeal_prime v, degDiv_single, one_mul, degPt]
      rw [map_mul, Ideal.natDegreeGenerator_mul
          (by simpa using (Ideal.relNorm_eq_bot_iff (R := F[X])).not.mpr hp0)
          (by simpa using (Ideal.relNorm_eq_bot_iff (R := F[X])).not.mpr ha),
        divisorIdeal_mul hp0 ha, degDiv_add, Nat.cast_add, hprime, ih ha]

/-- **The degree of an element of the coordinate ring is the degree of its affine divisor**: the
order of its pole at infinity is the number of its affine zeros, counted with multiplicity and
with the degrees of the points. -/
theorem deg_eq_degDiv {a : W.CoordinateRing} (ha : a ≠ 0) :
    (deg W a : ℤ) = degDiv W (divisor W (algebraMap W.CoordinateRing W.FunctionField a)) := by
  have h := natDegreeGenerator_relNorm (W := W) (Ideal.span {a})
    (by simpa [Ideal.span_singleton_eq_bot] using ha)
  rw [divisorIdeal_span] at h
  rw [← h, Ideal.relNorm_singleton, Algebra.intNorm_eq_norm, Ideal.natDegreeGenerator_span]
  rfl

/-- **The degree-zero theorem.** A rational function has as many zeros as poles: the degree of its
affine divisor, plus its order at infinity, is zero.

This is `deg (div f) = 0` on the projective curve — the point at infinity has degree `1`, since
`ordInfty_genX_div_genY` exhibits an `F`-rational uniformizer there. -/
theorem degDiv_divisor_add_ordInfty {f : W.FunctionField} (hf : f ≠ 0) :
    degDiv W (divisor W f) + ordInfty W f = 0 := by
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := W.CoordinateRing) f
  set A := algebraMap W.CoordinateRing W.FunctionField a with hA
  set B := algebraMap W.CoordinateRing W.FunctionField b with hB
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  have hB0 : B ≠ 0 := by
    rw [hB]
    exact fun h => hb0 ((IsFractionRing.injective W.CoordinateRing W.FunctionField)
      (by rw [h, map_zero]))
  have hA0 : A ≠ 0 := by
    intro h
    rw [h, zero_div] at hf
    exact hf rfl
  have ha0 : a ≠ 0 := fun h => hA0 (by rw [hA, h, map_zero])
  rw [divisor_div hA0 hB0, degDiv_sub, ← deg_eq_degDiv ha0, ← deg_eq_degDiv hb0,
    ordInfty_div hA0 hB0, ordInfty_algebraMap ha0, ordInfty_algebraMap hb0]
  ring

/-- The degree of the divisor of a rational function, as an equation for `ordInfty`. -/
theorem degDiv_divisor {f : W.FunctionField} (hf : f ≠ 0) :
    degDiv W (divisor W f) = -ordInfty W f := by
  have := degDiv_divisor_add_ordInfty hf
  omega

/-! ### Positivity, and the global sections -/

/-- **Every closed point has positive degree.**

If the degree were zero the relative norm of `v` would be all of `F[X]`, so `1 ∈ v` by
`relNorm_le_comap` — impossible for a prime. -/
lemma degPt_pos (v : HeightOneSpectrum W.CoordinateRing) : 0 < degPt v := by
  rw [degPt, Nat.pos_iff_ne_zero]
  intro h
  have hne : Ideal.relNorm F[X] v.asIdeal ≠ ⊥ := by
    simpa using (Ideal.relNorm_eq_bot_iff (R := F[X])).not.mpr v.ne_bot
  have hgen : Submodule.IsPrincipal.generator (Ideal.relNorm F[X] v.asIdeal) ≠ 0 := by
    intro hg
    exact hne (by rw [← Ideal.span_singleton_generator (Ideal.relNorm F[X] v.asIdeal), hg,
      Ideal.span_singleton_zero])
  have hunit : IsUnit (Submodule.IsPrincipal.generator (Ideal.relNorm F[X] v.asIdeal)) := by
    rw [Polynomial.isUnit_iff_degree_eq_zero, Polynomial.degree_eq_natDegree hgen]
    exact_mod_cast congrArg (Nat.cast : ℕ → WithBot ℕ) h
  have htop : Ideal.relNorm F[X] v.asIdeal = ⊤ := by
    rw [← Ideal.span_singleton_generator (Ideal.relNorm F[X] v.asIdeal),
      Ideal.span_singleton_eq_top]
    exact hunit
  have h1 : (1 : F[X]) ∈ v.asIdeal.comap (algebraMap F[X] W.CoordinateRing) :=
    relNorm_le_comap v.asIdeal (htop ▸ Submodule.mem_top)
  rw [Ideal.mem_comap, map_one] at h1
  exact v.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ h1 isUnit_one)

/-- An effective divisor has nonnegative degree. -/
lemma degDiv_nonneg {D : HeightOneSpectrum W.CoordinateRing →₀ ℤ} (hD : ∀ v, 0 ≤ D v) :
    0 ≤ degDiv W D :=
  Finset.sum_nonneg fun v _ => mul_nonneg (hD v) (Int.natCast_nonneg _)

/-- An effective divisor of degree zero is zero — because every point has positive degree. -/
lemma eq_zero_of_degDiv_eq_zero {D : HeightOneSpectrum W.CoordinateRing →₀ ℤ}
    (hD : ∀ v, 0 ≤ D v) (h : degDiv W D = 0) : D = 0 := by
  ext v
  by_cases hv : v ∈ D.support
  · have hterm := (Finset.sum_eq_zero_iff_of_nonneg
      (fun w _ => mul_nonneg (hD w) (Int.natCast_nonneg (degPt w)))).mp h v hv
    have hpos : (0 : ℤ) < degPt v := by exact_mod_cast degPt_pos v
    rcases mul_eq_zero.mp hterm with h0 | h0
    · simpa using h0
    · omega
  · simpa using Finsupp.notMem_support_iff.mp hv

/-- **A rational function with no poles anywhere has no zeros either.**  If `f` is regular at every
affine closed point and at infinity, then its divisor is trivial and it does not vanish at
infinity. -/
theorem divisor_eq_zero_of_nonneg {f : W.FunctionField} (hf : f ≠ 0)
    (hD : ∀ v, 0 ≤ divisor W f v) (hinf : 0 ≤ ordInfty W f) :
    divisor W f = 0 ∧ ordInfty W f = 0 := by
  have hsum := degDiv_divisor_add_ordInfty hf
  have hnn := degDiv_nonneg (W := W) hD
  have hz : degDiv W (divisor W f) = 0 := by omega
  exact ⟨eq_zero_of_degDiv_eq_zero hD hz, by omega⟩

/-- **The global sections of the structure sheaf are the constants.**  A rational function with no
pole at any affine closed point and none at infinity is a nonzero constant.

This is the complete-curve statement: `exists_eq_algebraMap_of_ordInfty_nonneg`
(`PlaceAtInfinity`) assumes the function already lies in `F[W]`, and
`exists_eq_algebraMap_of_divisor_eq_zero` (`#629`) assumes it has no zeros either.  Here only
pole-freeness is assumed, and the degree-zero theorem supplies the rest. -/
theorem exists_eq_algebraMap_of_nonneg {f : W.FunctionField} (hf : f ≠ 0)
    (hD : ∀ v, 0 ≤ divisor W f v) (hinf : 0 ≤ ordInfty W f) :
    ∃ c : F, c ≠ 0 ∧ f = algebraMap F W.FunctionField c :=
  exists_eq_algebraMap_of_divisor_eq_zero hf (divisor_eq_zero_of_nonneg hf hD hinf).1

end WeierstrassCurve.Affine
