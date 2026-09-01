/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import EllipticCurves.Fixtures
import EllipticCurves.FunctionField.TranslationPointEndomorphism
import EllipticCurves.FunctionField.WeilPairingTelescopeThree
import EllipticCurves.FunctionField.WeilPairingTelescopeTwo

/-!
# The divisor telescoping at general `n`: `∏_{i<n} τ_{[i]T}∗ f_T` is a nonzero constant

The **first** of the two products in Silverman *AEC* III.8.1(d) — the proof that the Weil pairing is
alternating — is a telescoping of divisors over the cyclic group `⟨T⟩`.  This file proves it at an
arbitrary `n`.  `EllipticCurves.FunctionField.WeilPairingTelescopeTwo` and
`EllipticCurves.FunctionField.WeilPairingTelescopeThree` are the merged numeral cases, and both are
recovered from the general form below, verbatim.

For an affine `n`-torsion point `T` and the principal function `f_T` with `div f_T = n(T) − n(O)`,

```
∏_{i<n} τ_{[i]T}∗ f_T = c ∈ F∖{0}.
```

## ⚠️ The argument is a formal telescoping, and it never identifies the permutation

`τ_Q∗` acts on `ProjPoint W` through a permutation `φ_Q`, and the classical proof reads that
permutation off as `p ↦ p ⊖ Q` — so that `div (τ_{[i]T}∗ f_T) = n((1−i)T) − n((−i)T)` and the sum
telescopes point by point.  **That identification is not needed and is not used here.**  Three facts
about `φ` suffice, and none of them mentions any point other than `T` and `O`:

* `φ_O = 1`;
* `φ_{P+Q} = φ_P ∘ φ_Q` — because `mapProjPointHom` is a monoid homomorphism (`Places`) and
  `P ↦ τ_P` is one too (`translatePointAlgEquiv_mul`, below, off `translatePointEndo_comp`);
* `φ_T (T) = O` — the merged `mapProjPoint_translateAlgEquiv_pointClosedPoint`.

With `s i := n · (φ_{[i]T} (T))` as an element of `ProjPoint W →₀ ℤ`, the `i`-th factor's divisor is
`s i − s (i+1)`: its positive part is `s i` by definition, and its negative part is
`n · (φ_{[i]T} (O))`, which is `n · (φ_{[i]T} (φ_T (T)))  = n · (φ_{[i+1]T} (T)) = s (i+1)` by the
composition law.  So `Finset.sum_range_sub'` gives `s 0 − s n`, and `s n = s 0` because
`n • T = 0` sends `φ_{[n]T}` back to `φ_O = 1`.

⚠️ **This is why the support is never counted.**  The `[i]T` need not be distinct — `T` may have
order strictly *dividing* `n`, and then `[i]T = O` for several `i` — so any argument that lists
`n` distinct points of `div (∏ …)` and cancels them pairwise is wrong at exactly the indices this
file exists to cover.  The `n = 6` certificate below is such an index, on purpose.

⚠️ It is also why the merged `n = 2` proof does **not** generalise.  That one goes through
`divisorProj_translateEndo_eq_neg` (`WeilPairingTelescopeTwo`), i.e. `div (τ_T∗ f) = −div f`, which
holds only because `−T = T`; it is a statement about a *transposition* and there is no `n`-fold
analogue of it.

## ⚠️ Why `translatePointEndo` and not `translateEndo`

The `i = 0` factor translates by `O`, which is not an affine point, so `translateEndo` — indexed by
a `W.Equation` datum — cannot state the product uniformly at any `n`.  Once `T` is allowed order
strictly dividing `n` the same happens at interior indices.
`EllipticCurves.FunctionField.TranslationPointEndomorphism` was written for this and its docstring
predicted this consumer; `WeilPairingTelescopeTwo`'s docstring names the missing brick outright.

## Main results

* `WeierstrassCurve.Affine.CoordinateRing.translatePointAlgEquiv` — `τ_P` as an `F`-algebra
  automorphism of `F(W)` at an arbitrary `P : W.Point`, with `translatePointAlgEquiv_mul` the
  composition law;
* `WeierstrassCurve.Affine.translateProjPerm` — the induced permutation of `ProjPoint W`, with
  `translateProjPerm_zero`, `translateProjPerm_apply_apply` and
  `translateProjPerm_pointClosedPoint`;
* `WeierstrassCurve.Affine.divisorProj_translatePointEndo` — `div (τ_P∗ f)` is `div f` pushed
  forward along that permutation, at every `P` including `O`;
* **`WeierstrassCurve.Affine.exists_prod_translatePointEndo_eq_algebraMap`** — the telescoping.

## ⚠️ Placement, stated rather than assumed

`translatePointAlgEquiv` and its three lemmas belong in
`EllipticCurves.FunctionField.TranslationPointEndomorphism`, beside `translatePointEndo`;
`translateProjPerm` and `divisorProj_translatePointEndo` belong beside `divisorProj_translateEndo`
(`EllipticCurves.FunctionField.PlaceOrder`) or beside `mapProjPoint`
(`EllipticCurves.FunctionField.Places`).  All of those files sit *below* this one, so moving them
would cost no import damage and would be purely mechanical.  They are here because this file is
their only consumer today and a one-file diff is cheaper to review — **not** because this is where
they belong.

The headline is in `WeierstrassCurve.Affine`, where both merged telescopes are; the
`translatePointAlgEquiv` bricks are in `CoordinateRing`, where `translateAlgEquiv` and
`translatePointEndo` are.  That is `#918`'s rule, applied in both directions inside one file.

## ⚠️ `[DecidableEq F]` is a binder here, deliberately

`W.Point`'s group law carries a `DecidableEq F` argument, so a statement mentioning `i • T` fixes
one.  Both merged telescopes take it as an **instance binder**, and so does everything below.  That
is the polymorphic choice and it is the one that composes: a caller working `open Classical in` —
which is how the gate-B workhorse this product feeds is written (`#1327`, which lands as
`translatePointEndo_eq_self_of_prod_eq_of_pow_eq` and is **not** on `main` at the commit this file
was written against) — instantiates the binder at `Classical.propDecidable` and the two products
match on the nose, while a certificate over `ℚ` instantiates it at
`instDecidableEqRat` and needs no `convert`.  A statement elaborated under `open Classical in`
instead of taking the binder can only be used in the first of those two contexts.

⚠️ The price is one bridge, in `translatePointAlgEquiv_mul`: the merged
`translatePointEndo_apply_apply` *is* elaborated `open Classical in`, so `rw`-ing it leaves a goal
that is `X = X` up to the `DecidableEq F` argument buried in `Point.instAddCommGroup`.  `congr 5`
reaches it and `Subsingleton.elim` closes it.  This is the same bookkeeping as the `convert … using
9` of `TranslationMulByNCommGeneral`'s Nonvacuity block; the depth differs because the path here is
`HAdd → Add → AddSemigroup → … → AddCommGroup` rather than through `nsmul`.

## This half is ungated

No `[n]∗`, no `mulByNEndo`, no `hprin`, no `g_T`, no `#418`, no `[IsAlgClosed F]`, no Ward, no
`ωₙ` — none of them occurs in any statement below, exactly as `WeilPairingTelescopeTwo` says of
itself.  The halving point and the algebraically closed base field belong to the assembly.

## What is *not* here

* **Gate B, the workhorse `τ_T∗ g = g`** — `#1327`.  The two gates are independent, neither is an
  input to the other, and they meet only in the assembly.  ⚠️ Nothing below imports it or depends on
  it, deliberately: this file compiles and is useful on a `main` where gate B does not yet exist.
* **The assembly** — the general-`n` form of `exists_weilPairingElt_self_eq_one_of_hprin_two`
  (`EllipticCurves.FunctionField.WeilPairingAlternatingBaseChange`), which needs this file *and*
  gate B *and* an `n`-division point over `F̄`.
* Any identification of `translateProjPerm` at a point other than the closed point of `T` and the
  point at infinity.  `mapProjPoint_translateAlgEquiv_pointClosedPoint_affine`
  (`EllipticCurves.FunctionField.TranslationProjAction`) does that at affine `F`-points and is
  deliberately **unused**: the whole point of the argument above is that it is not needed.

## References

* [J. Silverman, *The arithmetic of elliptic curves*][silverman2009], III.8.1(d), first product.
-/

open Polynomial IsDedekindDomain

namespace WeierstrassCurve.Affine

namespace CoordinateRing

variable {F : Type*} [Field F] {W : Affine F} [W.IsElliptic] {x y : F}

/-! ### Translation by an arbitrary point, as an algebra automorphism

`translateAlgEquiv` is indexed by an affine equation point, for the same reason `translateEndo` is.
`translatePointEndo` already removes that restriction on the ring-homomorphism side; the divisor
transport `divisorProj_algEquiv` needs the automorphism side, and this is it. -/

/-- **Translation by an arbitrary point of `W`, as an `F`-algebra automorphism of `F(W)`.**  At the
point at infinity it is the identity; at an affine point it is the merged `translateAlgEquiv`.
Both branches are `rfl`, and `translatePointAlgEquiv_apply` identifies the underlying function with
`translatePointEndo`. -/
noncomputable def translatePointAlgEquiv : W.Point → (W.FunctionField ≃ₐ[F] W.FunctionField)
  | .zero => AlgEquiv.refl
  | .some _ _ h => translateAlgEquiv h.left

@[simp] lemma translatePointAlgEquiv_zero :
    translatePointAlgEquiv (0 : W.Point) = AlgEquiv.refl := rfl

@[simp] lemma translatePointAlgEquiv_some (h : W.Nonsingular x y) :
    translatePointAlgEquiv (Point.some x y h) = translateAlgEquiv h.left := rfl

@[simp] lemma translatePointAlgEquiv_apply (P : W.Point) (f : W.FunctionField) :
    translatePointAlgEquiv P f = translatePointEndo P f := by
  match P with
  | .zero => rfl
  | .some x y h => rfl

/-- **`τ_P ∘ τ_Q = τ_{P+Q}` as automorphisms**, with no side condition — the `AlgEquiv` form of the
merged `translatePointEndo_comp`.  Multiplication of `AlgEquiv`s is composition.

⚠️ `congr 5` and `Subsingleton.elim` are bookkeeping, not mathematics: the merged
`translatePointEndo_apply_apply` is elaborated `open Classical in`, so its `P + Q` carries
`Classical.propDecidable`, while this statement's carries the `[DecidableEq F]` binder.  Depth `5`
reaches that argument of `Point.instAddCommGroup` along `HAdd → Add → AddSemigroup → … `.  See the
module docstring for why the binder is the right choice here. -/
theorem translatePointAlgEquiv_mul [DecidableEq F] (P Q : W.Point) :
    translatePointAlgEquiv P * translatePointAlgEquiv Q = translatePointAlgEquiv (P + Q) :=
  AlgEquiv.ext fun f => by
    rw [AlgEquiv.mul_apply, translatePointAlgEquiv_apply, translatePointAlgEquiv_apply,
      translatePointAlgEquiv_apply, translatePointEndo_apply_apply]
    congr 5
    exact Subsingleton.elim _ _

end CoordinateRing

open CoordinateRing

variable {F : Type*} [Field F] {W : Affine F} [W.IsElliptic]
  [IsDedekindDomain W.CoordinateRing] {x y : F}

/-! ### The induced permutation of the projective curve -/

variable (W) in
/-- **The permutation of `ProjPoint W` induced by translation by an arbitrary point.**  Classically
it is `p ↦ p ⊖ P`; nothing below uses that description, and the module docstring says why. -/
noncomputable def translateProjPerm (P : W.Point) : Equiv.Perm (ProjPoint W) :=
  mapProjPoint W (translatePointAlgEquiv P)

/-- Translation by `O` is the identity permutation. -/
@[simp] lemma translateProjPerm_zero : translateProjPerm W (0 : W.Point) = 1 := by
  rw [translateProjPerm, translatePointAlgEquiv_zero, ← mapProjPointHom_apply]
  exact map_one (mapProjPointHom W)

/-- **The composition law on the projective curve**, in applied form: `φ_P ∘ φ_Q = φ_{P+Q}`.  It is
`translatePointAlgEquiv_mul` read through the monoid homomorphism `mapProjPointHom`. -/
lemma translateProjPerm_apply_apply [DecidableEq F] (P Q : W.Point) (p : ProjPoint W) :
    translateProjPerm W P (translateProjPerm W Q p) = translateProjPerm W (P + Q) p := by
  rw [translateProjPerm, translateProjPerm, translateProjPerm, ← translatePointAlgEquiv_mul,
    ← mapProjPointHom_apply, ← mapProjPointHom_apply, ← mapProjPointHom_apply, map_mul]
  rfl

/-- **`div (τ_P∗ f)` is `div f` pushed forward along `φ_P`, at every `P` including `O`** — the
merged `divisorProj_translateEndo` with the affineness of `P` removed. -/
lemma divisorProj_translatePointEndo (P : W.Point) {f : W.FunctionField} (hf : f ≠ 0) :
    divisorProj W (translatePointEndo P f)
      = (divisorProj W f).mapDomain (translateProjPerm W P) := by
  have h := divisorProj_algEquiv (translatePointAlgEquiv P) hf
  rwa [translatePointAlgEquiv_apply] at h

/-- **`φ_T` sends the closed point of `T` to the point at infinity** — the merged
`mapProjPoint_translateAlgEquiv_pointClosedPoint`, at the `W.Point` indexing.  This is the *only*
value of `φ` the telescoping needs. -/
lemma translateProjPerm_pointClosedPoint (h : W.Equation x y) :
    translateProjPerm W (torsionPoint h) (some (pointClosedPoint h)) = none := by
  rw [translateProjPerm]
  exact mapProjPoint_translateAlgEquiv_pointClosedPoint h

/-! ### The telescoping -/

/-- **The telescoping at an arbitrary `n`.**  For an affine `n`-torsion point `T` there is a
function `f_T` with `div f_T = n(T) − n(O)` whose product with its translates by the successive
multiples of `T` is a nonzero constant:

```
∏_{i<n} τ_{[i]T}∗ f_T = c ∈ F∖{0}.
```

This is the first of the two products of Silverman III.8.1(d).  It carries no hypothesis beyond `T`
being an affine `n`-torsion point — no `[n]∗`, no `hprin`, no algebraically closed base field — and
**no hypothesis that `T` has order exactly `n`**: the `n = 6` certificate below runs at a `T` of
order `3`, where `[i]T = O` at an interior index and the `n` factors are not distinct.

⚠️ The shape of the product is the one gate B (`#1327`) takes as its `htel` hypothesis; the two are
the two halves of III.8.1(d) and are otherwise independent. -/
theorem exists_prod_translatePointEndo_eq_algebraMap [DecidableEq F] {n : ℕ}
    (h : W.Nonsingular x y) (htors : Point.some x y h ∈ W.torsion n) :
    ∃ f : W.FunctionField, f ≠ 0 ∧
      divisorProj W f = Finsupp.single (some (pointClosedPoint h.left)) (n : ℤ)
          - Finsupp.single (none : ProjPoint W) (n : ℤ) ∧
        ∃ c : F, c ≠ 0 ∧
          ∏ i ∈ Finset.range n, translatePointEndo (i • Point.some x y h) f
            = algebraMap F W.FunctionField c := by
  obtain ⟨f, hf, hdiv⟩ := divisorProj_eq_single_sub_single_of_torsion h htors
  refine ⟨f, hf, hdiv, ?_⟩
  set T : W.Point := Point.some x y h with hT
  set A : ProjPoint W := some (pointClosedPoint h.left) with hA
  have hne : ∀ i : ℕ, translatePointEndo (i • T) f ≠ 0 := fun i hz =>
    hf ((translatePointEndo (i • T)).injective (by rw [hz, map_zero]))
  have hTA : translateProjPerm W T A = none := translateProjPerm_pointClosedPoint h.left
  set s : ℕ → (ProjPoint W →₀ ℤ) :=
    fun i => Finsupp.single (translateProjPerm W (i • T) A) (n : ℤ) with hs
  -- The `i`-th factor's divisor is `s i - s (i + 1)`; the composition law is the whole content.
  have hterm : ∀ i : ℕ, divisorProj W (translatePointEndo (i • T) f) = s i - s (i + 1) := by
    intro i
    rw [divisorProj_translatePointEndo _ hf, hdiv, Finsupp.mapDomain_sub,
      Finsupp.mapDomain_single, Finsupp.mapDomain_single, hs]
    congr 2
    rw [succ_nsmul, ← translateProjPerm_apply_apply, hTA]
  -- Telescoping: the sum is `s 0 - s n`, and `n • T = 0` makes the two ends equal.
  have hsum : ∑ i ∈ Finset.range n, divisorProj W (translatePointEndo (i • T) f) = 0 := by
    rw [Finset.sum_congr rfl fun i _ => hterm i, Finset.sum_range_sub' s n, hs]
    simp only [zero_smul, translateProjPerm_zero, Equiv.Perm.coe_one, id_eq,
      show (n • T : W.Point) = 0 from mem_torsion_iff.mp htors, sub_self]
  have hpne : (∏ i ∈ Finset.range n, translatePointEndo (i • T) f) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun i _ => hne i
  exact (divisorProj_eq_zero_iff hpne).mp
    (by rw [divisorProj_prod W _ _ fun i _ => hne i, hsum])

/-! ### Recovery of the merged `n = 2` and `n = 3` telescopes

`#907`'s rule: a general form is only worth having if the merged statements it replaces come back
out of it unchanged.  Both do, and the two statements below are their signatures character for
character, ambient `variable` line included.  Each is proved *through* the general form rather than
re-proved.

⚠️ Both are `private`: public copies would duplicate merged names.  Check them against their twins
with `#check @…` inside a copy of this module rather than by a source diff — a source comparator
cannot see an auto-bound instance binder, and the printed names differ between two files with
different `open` lines. -/

section Recovery

variable {x₂ y₂ x₃ y₃ : F}

/-- `exists_mul_translateEndo_eq_algebraMap`
(`EllipticCurves.FunctionField.WeilPairingTelescopeTwo`), recovered.

The two-factor product `f · τ_T∗ f` is the `Finset.range 2` product with the `i = 0` factor
`τ_O∗ f = f` written out — which is why the merged statement does not look like a product at all. -/
private theorem exists_mul_translateEndo_eq_algebraMap_of_general [DecidableEq F]
    (h : W.Nonsingular x₂ y₂) (hP : Point.some x₂ y₂ h ∈ W.torsion 2) :
    ∃ f : W.FunctionField, f ≠ 0 ∧
      divisorProj W f = Finsupp.single (some (pointClosedPoint h.left)) (2 : ℤ)
        - Finsupp.single (none : ProjPoint W) (2 : ℤ) ∧
      ∃ c : F, c ≠ 0 ∧ f * translateEndo h.left f = algebraMap F W.FunctionField c := by
  obtain ⟨f, hf, hdiv, c, hc, hprod⟩ := exists_prod_translatePointEndo_eq_algebraMap h hP
  refine ⟨f, hf, hdiv, c, hc, ?_⟩
  rwa [Finset.prod_range_succ, Finset.prod_range_one, zero_smul, translatePointEndo_zero,
    RingHom.id_apply, one_smul, translatePointEndo_some] at hprod

/-- `exists_mul_translateEndo_mul_translateEndo_eq_algebraMap`
(`EllipticCurves.FunctionField.WeilPairingTelescopeThree`), recovered.

⚠️ The merged telescope's third factor translates by `−T` and the uniform product's by `[2]T`.  They
agree **because** `[3]T = O`, so this recovery consumes the torsion hypothesis a second time, and
for a different reason than the merged proof does. -/
private theorem exists_mul_translateEndo_mul_translateEndo_eq_algebraMap_of_general
    [DecidableEq F] (h : W.Nonsingular x₃ y₃) (hP : Point.some x₃ y₃ h ∈ W.torsion 3) :
    ∃ f : W.FunctionField, f ≠ 0 ∧
      divisorProj W f = Finsupp.single (some (pointClosedPoint h.left)) (3 : ℤ)
        - Finsupp.single (none : ProjPoint W) (3 : ℤ) ∧
      ∃ c : F, c ≠ 0 ∧
        f * translateEndo h.left f
            * translateEndo ((W.equation_neg x₃ y₃).mpr h.left) f
          = algebraMap F W.FunctionField c := by
  obtain ⟨f, hf, hdiv, c, hc, hprod⟩ := exists_prod_translatePointEndo_eq_algebraMap h hP
  refine ⟨f, hf, hdiv, c, hc, ?_⟩
  have hneg : ((2 : ℕ) • Point.some x₃ y₃ h : W.Point) = -Point.some x₃ y₃ h :=
    add_eq_zero_iff_eq_neg.mp (by
      rw [← succ_nsmul]
      exact mem_torsion_iff.mp hP)
  rwa [Finset.prod_range_succ, Finset.prod_range_succ, Finset.prod_range_one, zero_smul,
    translatePointEndo_zero, RingHom.id_apply, one_smul, translatePointEndo_some, hneg,
    Point.neg_some, translatePointEndo_some] at hprod

end Recovery

/-! ### Non-vacuity

⚠️ **The certificate runs at `n = 6` with a `T` of order `3`**, and that combination is the point of
it.  `n = 6` is an index no merged telescope reaches; more importantly, `T` of order strictly
dividing `n` is the configuration that no `translateEndo`-indexed statement can express at all,
because the interior factor at `i = 3` translates by `[3]T = O`.  `exampleInteriorFactorIsIdentity`
proves that it does, so "this certificate exercises the case the merged files cannot state" is a
checked claim rather than an implied one.  It is also the configuration that refutes any proof of
this theorem that lists `n` distinct points and cancels them pairwise: here the `[i]T` take three
values, not six.

The curve is `y² = x³ + 1` over `ℚ`, of discriminant `−432`, and `T = (0, 1)`; `[2]T = (0, −1)` is
`−T`, so `[3]T = O`.  ⚠️ Deliberately **not** this subtree's usual `y² = x³ − x`, on which every
affine rational point is `2`-torsion, so that no point of order `3` — and hence no `T` of order
properly dividing an `n > 2` — exists there to exhibit.

What remains hypothetical is nothing: every hypothesis of the theorem is discharged, so the
certificate is an unconditional existence statement over `ℚ`. -/

section Nonvacuity

/-! The certificate curve `y² = x³ + 1` is the shared `EllipticCurves.Fixture.y2EqX3AddOne`, whose
single `[CharZero F]` instance also supplies `IsElliptic` here. -/

open EllipticCurves.Fixture

/-- `T = (0, 1)` is a nonsingular point of `y² = x³ + 1`. -/
private lemma exampleNonsingularT : (y2EqX3AddOne ℚ).Nonsingular 0 1 := by
  rw [nonsingular_iff]
  refine ⟨?_, Or.inr ?_⟩ <;>
    norm_num [y2EqX3AddOne, WeierstrassCurve.Affine.equation_iff, WeierstrassCurve.Affine.negY]

/-- **`[2]T = −T`**: the tangent at `(0, 1)` is horizontal, and doubling returns `(0, −1)`. -/
private lemma exampleDouble :
    Point.some (0 : ℚ) 1 exampleNonsingularT + Point.some (0 : ℚ) 1 exampleNonsingularT
      = -Point.some (0 : ℚ) 1 exampleNonsingularT := by
  have hy : (1 : ℚ) ≠ (y2EqX3AddOne ℚ).negY 0 1 := by
    norm_num [y2EqX3AddOne, WeierstrassCurve.Affine.negY]
  rw [Point.add_self_of_Y_ne hy, Point.neg_some, Point.some.injEq]
  constructor <;>
    norm_num [y2EqX3AddOne, WeierstrassCurve.Affine.addX, WeierstrassCurve.Affine.addY,
      WeierstrassCurve.Affine.negAddY, WeierstrassCurve.Affine.negY,
      WeierstrassCurve.Affine.slope]

/-- **`T` has order `3`**, from `[2]T = −T`. -/
private lemma exampleThreeTorsion :
    ((3 : ℕ) • Point.some (0 : ℚ) 1 exampleNonsingularT : (y2EqX3AddOne ℚ).Point) = 0 := by
  rw [show (3 : ℕ) = 2 + 1 from rfl, succ_nsmul, two_nsmul, exampleDouble, neg_add_cancel]

/-- Hence `T` is `6`-torsion, **without having order `6`** — which is the hypothesis the theorem
takes and the configuration this block exists to exercise. -/
private lemma exampleSixTorsion :
    Point.some (0 : ℚ) 1 exampleNonsingularT ∈ (y2EqX3AddOne ℚ).torsion 6 := by
  rw [mem_torsion_iff, show (6 : ℕ) = 3 + 3 from rfl, add_nsmul, exampleThreeTorsion, add_zero]

/-- ⚠️ **The `i = 3` factor of the six-fold product translates by `O`.**  So the product genuinely
cannot be written with `translateEndo`, whose index is an affine equation datum, and the `[i]T` are
not six distinct points. -/
private lemma exampleInteriorFactorIsIdentity :
    translatePointEndo ((3 : ℕ) • Point.some (0 : ℚ) 1 exampleNonsingularT)
      = RingHom.id (y2EqX3AddOne ℚ).FunctionField := by
  rw [exampleThreeTorsion, translatePointEndo_zero]

/-- **The telescoping at `n = 6` on `y² = x³ + 1` over `ℚ`**, at a `T` whose order is `3`. -/
example : ∃ f : (y2EqX3AddOne ℚ).FunctionField, f ≠ 0 ∧
    divisorProj (y2EqX3AddOne ℚ) f
        = Finsupp.single (some (pointClosedPoint exampleNonsingularT.left)) (6 : ℤ)
          - Finsupp.single (none : ProjPoint (y2EqX3AddOne ℚ)) (6 : ℤ) ∧
      ∃ c : ℚ, c ≠ 0 ∧
        ∏ i ∈ Finset.range 6,
            translatePointEndo (i • Point.some (0 : ℚ) 1 exampleNonsingularT) f
          = algebraMap ℚ (y2EqX3AddOne ℚ).FunctionField c :=
  exists_prod_translatePointEndo_eq_algebraMap exampleNonsingularT exampleSixTorsion

end Nonvacuity

end WeierstrassCurve.Affine
