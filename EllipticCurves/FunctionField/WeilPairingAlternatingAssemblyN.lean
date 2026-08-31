/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import EllipticCurves.FunctionField.WeilPairingAlternatingConsumerN
import EllipticCurves.FunctionField.WeilPairingAlternatingMu
import EllipticCurves.FunctionField.WeilPairingTelescopeN

/-!
# The alternating assembly at general `n`: `e_n(T, T) = 1`

`EllipticCurves.FunctionField.WeilPairingTelescopeN` and
`EllipticCurves.FunctionField.WeilPairingAlternatingWorkhorseN` are the two halves of Silverman
*AEC* III.8.1(d) at an arbitrary `n`.  They were deliberately written to be independent of each
other, and they meet here.

```
gate A   ∏_{i<n} τ_{[i]T}∗ f_T = c                     (WeilPairingTelescopeN)
hprin    n · div g₀ = div ([n]∗ f_T)                   (#418, a hypothesis at every index)
gate B   [n]P = T → gate A → hprin ⟹ τ_T∗ g = g       (WeilPairingAlternatingWorkhorseN)
         ⟹ e_n(T, T) = 1                              (WeilPairingAlternating)
```

## ⚠️ What the halving hypothesis is, and why it is a hypothesis

Gate B needs a point `P` with `[n]P = T`.  At `n = 2` and `n = 3` the merged assemblies get one for
free over `F̄`, from `exists_equation_nsmul_two_eq` / `exists_equation_nsmul_three_eq`, and the
general-`n` form of those is **not** on this tree.  So the theorem below takes `hmul` as an explicit
hypothesis.

⚠️ This is the one place where a reader can over-read the file.  Three separate hand-off notes on
this front say the assembly at general `n` *"needs an `n`-division point over `F̄`"* and conclude it
is unreachable.  That is right about the `[IsAlgClosed F]` form and wrong about the assembly: with
the halving assumed, the assembly is a composition of merged statements and nothing else.  The
`F̄` step is what would turn `hmul` into a theorem, and it is **not** here.

## Main statements

* `WeierstrassCurve.Affine.exists_weilPairingElt_self_eq_one_of_hprin_of_nsmul_eq` — the assembly;
* `WeierstrassCurve.Affine.exists_weilPairingMu_self_eq_one_of_hprin_of_nsmul_eq` — its value in
  `μ_m(F)`, at an index `m` that need not be `n`;
* `WeierstrassCurve.Affine.exists_weilPairingElt_self_eq_one_of_smooth_of_nsmul_eq` — the same at
  every `3`-smooth `n ≠ 0`, with the transcendence hypothesis discharged.

All three are in `WeierstrassCurve.Affine`, beside the merged assemblies rather than in the
`CoordinateRing` sub-namespace where the bricks live.  That is `#918`'s rule.

## ⚠️ `[DecidableEq F]`: the two gates are stated differently, and where the cost lands

Gate A takes `[DecidableEq F]` as an instance **binder**; gate B is elaborated `open Classical in`.
Every public statement below is `open Classical in`, matching gate B and every merged assembly, so
**the composition itself is `convert`-free**: gate A's binder instantiates at
`Classical.propDecidable` and gate B's baked-in copy is the same term.

⚠️ The choice is not free and it is worth recording which way it pushes the cost, since PR #501
established that the binder is the better default on this front.  A `Classical`-fixed statement can
only be consumed at `Classical.propDecidable`, so the mismatch appears wherever a caller fixes its
own instance — over `ℚ`, where `instDecidableEqRat` wins on priority.  Concretely:

* stated `open Classical in` (the choice here): the proof body and both recoveries are
  `convert`-free, and the `ℚ` certificate below pays **two** `convert`s, on `htors` and on `hmul`;
* stated with the binder: the `ℚ` certificate would be free and the *proof body* would pay two,
  one of them on `htel` **inside a `Finset.prod` binder**, which is the expensive shape.

Gate B fixes the instance, so the second option cannot avoid the cost either — it only moves it
somewhere worse.  ⚠️ **If gate B is ever restated with the binder, restate this file too and both
`convert`s disappear.**  That is the retrofit PR #501's finding actually buys, and it belongs to
gate B rather than here.

## What is *not* here

* The general-`n` form of `exists_equation_nsmul_two_eq` — an `n`-division point over `F̄`.  It is
  the only thing between this file and an `[IsAlgClosed F]` assembly at general `n`, it is unfiled
  and unspiked, and whether the fibre of `[n]` over a rational point at `3`-smooth `n` is the right
  input to it is **unchecked**.  Nothing below should be read as progress on it.
* `hprin` (`#418`, `#962`).  It is a hypothesis here exactly as it is in every merged assembly, at
  every index, over every field.
* Any claim about `e_n(S, T)` for `S ≠ T`, bilinearity, or the Galois action.

## References

* [J. Silverman, *The arithmetic of elliptic curves*][silverman2009], III.8.1(d).
-/

open Polynomial IsDedekindDomain

namespace WeierstrassCurve.Affine

open CoordinateRing

variable {F : Type*} [Field F] {W : Affine F} [W.IsElliptic]
  [IsDedekindDomain W.CoordinateRing] {xT yT : F}

/-! ### The assembly -/

open Classical in
/-- **`e_n(T, T) = 1` at an arbitrary `n`**, from the divisor telescoping, `hprin`, and the
alternating workhorse.

For an affine `n`-torsion point `T = (xT, yT)`, an affine `P` with `[n]P = T`, and the `#418` datum
`hprin` — the principality of the `n`-divisible divisor `div ([n]∗ f_T)`, in the exact shape
`exists_gS_n` takes it — there are a principal function `f_T` with `div f_T = n(T) − n(O)` and an
`n`-th root `g_T` of `[n]∗ f_T` (up to a unit of `F[W]`) with `τ_T∗ g_T = g_T`, hence
`e_n(T, T) = 1`.

The conclusion is `exists_weilPairingElt_self_eq_one_of_algClosed_two`'s with `2` replaced by `n`,
so every consumer of the merged assemblies destructures this one unchanged.

⚠️ `hmul` is the halving, and it is assumed rather than proved; see the module docstring.  It is
the *only* hypothesis here that the merged `n = 2` and `n = 3` assemblies do not carry. -/
theorem exists_weilPairingElt_self_eq_one_of_hprin_of_nsmul_eq {n : ℕ} (hn0 : n ≠ 0)
    (hn : Transcendental F (n • genericPoint (W := W)).xCoord)
    (h : W.Nonsingular xT yT) (htors : Point.some xT yT h ∈ W.torsion n)
    {xP yP : F} (hP : W.Equation xP yP)
    (hmul : n • torsionPoint hP = Point.some xT yT h)
    (hprin : ∀ f : W.FunctionField, f ≠ 0 →
      divisor W f = Finsupp.single (pointClosedPoint h.left) (n : ℤ) →
      ∃ g₀ : W.FunctionField, g₀ ≠ 0 ∧
        n • divisor W g₀ = divisor W (mulByNEndo n hn f)) :
    ∃ f : W.FunctionField, f ≠ 0 ∧
      divisorProj W f = Finsupp.single (some (pointClosedPoint h.left)) (n : ℤ)
          - Finsupp.single (none : ProjPoint W) (n : ℤ) ∧
        ∃ g : W.FunctionField, g ≠ 0 ∧
          (∃ u : W.CoordinateRingˣ, (u : W.CoordinateRing) • g ^ n = mulByNEndo n hn f) ∧
          translateEndo h.left g = g ∧ weilPairingElt h.left g = 1 := by
  -- Gate A: the telescoping function and its `⟨T⟩`-product.
  obtain ⟨f, hf, hdivproj, c, hc, htel⟩ := exists_prod_translatePointEndo_eq_algebraMap h htors
  -- The `#418` datum, at the telescoping function.
  obtain ⟨g, hg, hgdiv⟩ :=
    hprin f hf (divisor_eq_single_of_divisorProj_eq_single_sub_single hdivproj)
  have hfne : mulByNEndo n hn f ≠ 0 := fun hz =>
    hf (mulByNEndo_injective n hn (by rw [hz, map_zero]))
  obtain ⟨u, hu⟩ := exists_smul_pow_eq_of_nsmul_divisor hfne hg hgdiv
  -- The unit of `F[W]` is a nonzero constant, so the `n`-th root relation lives over `F`.
  obtain ⟨c₀, hc₀, hueq⟩ := isUnit_iff_exists_eq_algebraMap.mp u.isUnit
  have hpow : algebraMap F W.FunctionField c₀ * g ^ n = mulByNEndo n hn f := by
    rw [← hu, Algebra.smul_def, hueq, ← IsScalarTower.algebraMap_apply]
  -- Gate B, at the halving `hmul`.  Its `htel` is gate A's product verbatim.
  have htinv : translateEndo h.left g = g := by
    have key := translatePointEndo_eq_self_of_prod_eq_of_pow_eq hn0 hn hmul hg hc hc₀ htel hpow
    rwa [translatePointEndo_some] at key
  exact ⟨f, hf, hdivproj, g, hg, ⟨u, hu⟩, htinv,
    weilPairingElt_self_of_translateEndo_fixed h.left hg htinv⟩

open Classical in
/-- **The alternating property at general `n` in the value group.**

`weilPairingMu` is indexed by a proof that the pairing element is an `m`-th root of unity, so the
statement produces one; it costs nothing, since the previous theorem gives `e_n(T, T) = 1` and
`1 ^ m = 1`.  ⚠️ The index `m` is arbitrary and **need not be `n`** — this is the group identity of
`μ_m(F)` for whichever `m` the caller has packaged the value in, not a claim that `e_n` lands in
`μ_m` for `m ≠ n`.  Both merged `μ`-valued assemblies say the same of themselves. -/
theorem exists_weilPairingMu_self_eq_one_of_hprin_of_nsmul_eq {n : ℕ} (hn0 : n ≠ 0)
    (hn : Transcendental F (n • genericPoint (W := W)).xCoord)
    (h : W.Nonsingular xT yT) (htors : Point.some xT yT h ∈ W.torsion n)
    {xP yP : F} (hP : W.Equation xP yP)
    (hmul : n • torsionPoint hP = Point.some xT yT h)
    (hprin : ∀ f : W.FunctionField, f ≠ 0 →
      divisor W f = Finsupp.single (pointClosedPoint h.left) (n : ℤ) →
      ∃ g₀ : W.FunctionField, g₀ ≠ 0 ∧
        n • divisor W g₀ = divisor W (mulByNEndo n hn f))
    (m : ℕ) [NeZero m] :
    ∃ f : W.FunctionField, f ≠ 0 ∧
      divisorProj W f = Finsupp.single (some (pointClosedPoint h.left)) (n : ℤ)
          - Finsupp.single (none : ProjPoint W) (n : ℤ) ∧
        ∃ g : W.FunctionField, g ≠ 0 ∧
          (∃ u : W.CoordinateRingˣ, (u : W.CoordinateRing) • g ^ n = mulByNEndo n hn f) ∧
          ∃ hpow : weilPairingElt h.left g ^ m = 1, weilPairingMu h.left hpow = 1 := by
  obtain ⟨f, hf, hdivproj, g, hg, hu, htinv, halt⟩ :=
    exists_weilPairingElt_self_eq_one_of_hprin_of_nsmul_eq hn0 hn h htors hP hmul hprin
  exact ⟨f, hf, hdivproj, g, hg, hu, by rw [halt, one_pow],
    weilPairingMu_self_of_translateEndo_fixed h.left hg _ htinv⟩

open Classical in
/-- **The assembly at every `3`-smooth `n ≠ 0`**, with the transcendence hypothesis discharged by
`transcendental_xCoord_nsmul_of_smooth`.

⚠️ The first index this does **not** cover is `n = 5`, for `exists_gS_of_smooth`'s reason and for
the reason every other `_of_smooth` statement on this front stops there: the argument that supplies
the transcendence manufactures no new prime. -/
theorem exists_weilPairingElt_self_eq_one_of_smooth_of_nsmul_eq (h2 : (2 : F) ≠ 0)
    (h3 : (3 : F) ≠ 0) {n : ℕ} (hn0 : n ≠ 0) (hfac : ∀ p ∈ n.primeFactors, p = 2 ∨ p = 3)
    (h : W.Nonsingular xT yT) (htors : Point.some xT yT h ∈ W.torsion n)
    {xP yP : F} (hP : W.Equation xP yP)
    (hmul : n • torsionPoint hP = Point.some xT yT h)
    (hprin : ∀ f : W.FunctionField, f ≠ 0 →
      divisor W f = Finsupp.single (pointClosedPoint h.left) (n : ℤ) →
      ∃ g₀ : W.FunctionField, g₀ ≠ 0 ∧
        n • divisor W g₀ =
          divisor W (mulByNEndo n (transcendental_xCoord_nsmul_of_smooth h2 h3 hn0 hfac) f)) :
    ∃ f : W.FunctionField, f ≠ 0 ∧
      divisorProj W f = Finsupp.single (some (pointClosedPoint h.left)) (n : ℤ)
          - Finsupp.single (none : ProjPoint W) (n : ℤ) ∧
        ∃ g : W.FunctionField, g ≠ 0 ∧
          (∃ u : W.CoordinateRingˣ, (u : W.CoordinateRing) • g ^ n
            = mulByNEndo n (transcendental_xCoord_nsmul_of_smooth h2 h3 hn0 hfac) f) ∧
          translateEndo h.left g = g ∧ weilPairingElt h.left g = 1 :=
  exists_weilPairingElt_self_eq_one_of_hprin_of_nsmul_eq hn0 _ h htors hP hmul hprin

/-! ### Recovery of the merged `n = 2` and `n = 3` assemblies

`#907`'s rule: the general form is only worth having if the merged statements it replaces come back
out of it unchanged.  Both do.  ⚠️ The recovery is a genuine test here and not a formality, because
the general theorem carries a hypothesis the merged ones do not: over `F̄` that hypothesis is
*discharged* by `exists_equation_nsmul_{two,three}_eq`, and if it were not, no recovery would exist.

Both are `private`: public copies would duplicate merged names.  Check them against their twins with
`#check @…` inside a copy of this module, under `pp.explicit`/`pp.universes`/`pp.deepTerms`, with
this module's `open` lines mirrored into the comparator — a source comparator cannot see an
auto-bound instance binder, and `pp.explicit` does not suppress namespace shortening from `open`. -/

section Recovery

variable {x₂ y₂ x₃ y₃ : F}

open Classical in
/-- `exists_weilPairingElt_self_eq_one_of_algClosed_two`
(`EllipticCurves.FunctionField.WeilPairingAlternatingTwo`), recovered.

Over `F̄` the halving is `exists_equation_nsmul_two_eq`, and `mulByNEndo_two` identifies `[2]∗` with
the merged `mulByTwoEndo`.  ⚠️ `Nat.cast_ofNat` is not decoration: the general theorem writes the
divisor coefficient as `((2 : ℕ) : ℤ)` and the merged statement writes `(2 : ℤ)`, so without it
neither `hprin` nor the conclusion matches. -/
private theorem exists_weilPairingElt_self_eq_one_of_algClosed_two_of_general [IsAlgClosed F]
    (h2 : (2 : F) ≠ 0) (h : W.Nonsingular x₂ y₂) (htors : Point.some x₂ y₂ h ∈ W.torsion 2)
    (hprin : ∀ f : W.FunctionField, f ≠ 0 →
      divisor W f = Finsupp.single (pointClosedPoint h.left) (2 : ℤ) →
      ∃ g₀ : W.FunctionField, g₀ ≠ 0 ∧
        2 • divisor W g₀ = divisor W (mulByTwoEndo h2 f)) :
    ∃ f : W.FunctionField, f ≠ 0 ∧
      divisorProj W f = Finsupp.single (some (pointClosedPoint h.left)) (2 : ℤ)
          - Finsupp.single (none : ProjPoint W) (2 : ℤ) ∧
        ∃ g : W.FunctionField, g ≠ 0 ∧
          (∃ u : W.CoordinateRingˣ, (u : W.CoordinateRing) • g ^ 2 = mulByTwoEndo h2 f) ∧
          translateEndo h.left g = g ∧ weilPairingElt h.left g = 1 := by
  obtain ⟨xP, yP, hP, hdouble⟩ := exists_equation_nsmul_two_eq h2 h
  have hmul : (2 : ℕ) • torsionPoint hP = Point.some x₂ y₂ h := by
    rw [two_nsmul]; exact hdouble
  have key := exists_weilPairingElt_self_eq_one_of_hprin_of_nsmul_eq (n := 2) two_ne_zero
    (transcendental_xCoord_two_nsmul (W := W) h2) h htors hP hmul
    (by simpa only [mulByNEndo_two h2, Nat.cast_ofNat] using hprin)
  simpa only [mulByNEndo_two h2, Nat.cast_ofNat] using key

open Classical in
/-- `exists_weilPairingElt_self_eq_one_of_algClosed_three`
(`EllipticCurves.FunctionField.WeilPairingAlternatingThree`), recovered.

⚠️ `exists_equation_nsmul_three_eq` produces `P` and `Q = [2]P` with `P + Q = T`, so the halving
`[3]P = T` needs the two of them composed — and in the order `Q + P`, whence the `add_comm`.  That
is the same bookkeeping the merged `n = 3` proof does, moved to the caller. -/
private theorem exists_weilPairingElt_self_eq_one_of_algClosed_three_of_general [IsAlgClosed F]
    (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) (h : W.Nonsingular x₃ y₃)
    (htors : Point.some x₃ y₃ h ∈ W.torsion 3)
    (hprin : ∀ f : W.FunctionField, f ≠ 0 →
      divisor W f = Finsupp.single (pointClosedPoint h.left) (3 : ℤ) →
      ∃ g₀ : W.FunctionField, g₀ ≠ 0 ∧
        3 • divisor W g₀ = divisor W (mulByThreeEndo h2 h3 f)) :
    ∃ f : W.FunctionField, f ≠ 0 ∧
      divisorProj W f = Finsupp.single (some (pointClosedPoint h.left)) (3 : ℤ)
          - Finsupp.single (none : ProjPoint W) (3 : ℤ) ∧
        ∃ g : W.FunctionField, g ≠ 0 ∧
          (∃ u : W.CoordinateRingˣ, (u : W.CoordinateRing) • g ^ 3 = mulByThreeEndo h2 h3 f) ∧
          translateEndo h.left g = g ∧ weilPairingElt h.left g = 1 := by
  obtain ⟨xP, yP, xQ, yQ, hP, hQ, hdouble, hsum⟩ := exists_equation_nsmul_three_eq h2 h htors
  have hmul : (3 : ℕ) • torsionPoint hP = Point.some x₃ y₃ h := by
    rw [show (3 : ℕ) = 2 + 1 from rfl, succ_nsmul, two_nsmul, hdouble, add_comm]
    exact hsum
  have key := exists_weilPairingElt_self_eq_one_of_hprin_of_nsmul_eq (n := 3) three_ne_zero
    (transcendental_xCoord_three_nsmul (W := W) h2 h3) h htors hP hmul
    (by simpa only [mulByNEndo_three h2 h3, Nat.cast_ofNat] using hprin)
  simpa only [mulByNEndo_three h2 h3, Nat.cast_ofNat] using key

end Recovery

/-! ### Non-vacuity at `n = 6`

⚠️ **`hprin` stays a hypothesis** — it is `#418`, nothing on this board discharges it at any index,
and the merged `n = 2` and `n = 3` assemblies over a general field carry it too.  What is certified
below is that **every other hypothesis is simultaneously inhabited at an index outside `{2, 3}`**:
the elliptic instance, `3`-smoothness at a composite index, non-singularity, `n`-torsion of `T`, an
affine `P`, and — the one the general theorem adds and the merged ones do not — the halving
`[6]P = T`, which is **discharged here, not assumed**.

⚠️ **The index and the curve are both forced, and the arithmetic behind that is worth stating.**
`[n]P = T` together with `[n]T = O` forces `[n²]P = O`, and `T ≠ O` forces `ord P ∤ n`.  At `n = 4`
that leaves `ord P ∈ {8, 16}`, and `ℤ/16` does not occur over `ℚ` — so a rational certificate at
`n = 4` needs a point of order `8`.  At `n = 6` it leaves `ord P ∈ {4, 9, 12, 18, 36}`, and
**`ord P = 4` works**: then `[6]P = [2]P`, which is `2`-torsion, hence `6`-torsion, hence a legal
`T`.  That is the cheapest genuinely-composite certificate available over `ℚ`, and `6 = 2 · 3` is
`3`-smooth so the `_of_smooth` form applies.

The curve is `y² = x³ + 4x` over `ℚ`, of discriminant `−4096`, with `P = (2, 4)` of order `4` and
`T = [2]P = (0, 0)` of order `2`.

⚠️ Deliberately **not** this subtree's default `y² = x³ − x`: every affine rational point there is
`2`-torsion, so no `P` with `ord P = 4` exists on it and the only relation available at a composite
`n` would be `[n]T = T` with `T` affine, which is **false** — a certificate resting on a false
hypothesis proves nothing (`#916`).  This is the third distinct reason recorded on this front for
abandoning that fixture past `n = 3`. -/

section Nonvacuity

/-- The curve `y² = x³ + 4x` over `ℚ`, of discriminant `−4096`. -/
private noncomputable def exampleCurve : Affine ℚ := ⟨0, 0, 0, 4, 0⟩

private instance : exampleCurve.IsElliptic := by
  rw [WeierstrassCurve.isElliptic_iff, isUnit_iff_ne_zero]
  norm_num [exampleCurve, WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈]

private lemma exampleTwo : (2 : ℚ) ≠ 0 := by norm_num

private lemma exampleThree : (3 : ℚ) ≠ 0 := by norm_num

/-- `6 = 2 · 3` is `3`-smooth.  ⚠️ Not `by decide`: the `Decidable` instance for the bounded
quantifier over `primeFactors` gets stuck rather than reducing, exactly as
`EllipticCurves.Torsion.ThreePrimary` records at `72`. -/
private lemma primeFactorsSix : ∀ p ∈ (6 : ℕ).primeFactors, p = 2 ∨ p = 3 := by
  intro p hp
  obtain ⟨hpp, hdvd, -⟩ := Nat.mem_primeFactors.mp hp
  rw [show (6 : ℕ) = 2 * 3 from rfl] at hdvd
  rcases (Nat.Prime.dvd_mul hpp).mp hdvd with hd | hd
  · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hpp Nat.prime_two).mp hd)
  · exact Or.inr ((Nat.prime_dvd_prime_iff_eq hpp Nat.prime_three).mp hd)

/-- `P = (2, 4)` is a nonsingular point of `y² = x³ + 4x`. -/
private lemma exampleNsP : exampleCurve.Nonsingular 2 4 :=
  exampleCurve.equation_iff_nonsingular.mp (by
    norm_num [exampleCurve, WeierstrassCurve.Affine.equation_iff])

/-- `T = (0, 0)` is a nonsingular point of `y² = x³ + 4x`; it is the `2`-torsion point cut out by
`x = 0`. -/
private lemma exampleNsT : exampleCurve.Nonsingular 0 0 :=
  exampleCurve.equation_iff_nonsingular.mp (by
    norm_num [exampleCurve, WeierstrassCurve.Affine.equation_iff])

/-- **`[2]P = T`**: the tangent at `(2, 4)` has slope `2`, so `x([2]P) = 4 − 4 = 0`. -/
private lemma exampleDoubleP :
    Point.some (2 : ℚ) 4 exampleNsP + Point.some (2 : ℚ) 4 exampleNsP
      = Point.some (0 : ℚ) 0 exampleNsT := by
  have hy : (4 : ℚ) ≠ exampleCurve.negY 2 4 := by
    norm_num [exampleCurve, WeierstrassCurve.Affine.negY]
  rw [Point.add_self_of_Y_ne hy, Point.some.injEq]
  refine ⟨?_, ?_⟩ <;>
    norm_num [exampleCurve, WeierstrassCurve.Affine.addX, WeierstrassCurve.Affine.addY,
      WeierstrassCurve.Affine.negAddY, WeierstrassCurve.Affine.negY,
      WeierstrassCurve.Affine.slope]

/-- `T = (0, 0)` is `2`-torsion: `ψ₂(T) = 2·0 + 0·0 + 0 = 0`.

⚠️ No `open Classical in` on any lemma of this block, unlike every abstract-`F` statement above.
It would be a no-op: `ℚ` has `instDecidableEqRat`, which wins on priority, so the group law here is
indexed by it whatever is open.  That is exactly why the certificate needs the two `convert`s at
the end of the block, and writing `open Classical in` here would hide the reason rather than fix
it. -/
private lemma exampleTorTwoT : Point.some (0 : ℚ) 0 exampleNsT ∈ exampleCurve.torsion 2 :=
  (mem_torsion_two_some_iff exampleNsT).mpr (by norm_num [exampleCurve])

/-- **`T + T = O`**, the `W.Point` form of `exampleTorTwoT`. -/
private lemma exampleDoubleT :
    Point.some (0 : ℚ) 0 exampleNsT + Point.some (0 : ℚ) 0 exampleNsT = 0 := by
  have h := mem_torsion_iff.mp exampleTorTwoT
  rwa [two_nsmul] at h

/-- **`T` is `6`-torsion**, because it is `2`-torsion and `2 ∣ 6`.  ⚠️ Its order is `2`, strictly
dividing `6`; the theorem asks for `n`-torsion and not for order exactly `n`, and this certificate
is at an index where the two differ. -/
private lemma exampleTorSixT : Point.some (0 : ℚ) 0 exampleNsT ∈ exampleCurve.torsion 6 := by
  rw [mem_torsion_iff, show (6 : ℕ) = 2 * 3 from rfl, mul_nsmul, two_nsmul, exampleDoubleT,
    smul_zero]

/-- **`[2]P = T`** in `nsmul` form, which is the shape the multiples below rewrite with. -/
private lemma exampleTwoP :
    ((2 : ℕ) • Point.some (2 : ℚ) 4 exampleNsP : exampleCurve.Point)
      = Point.some (0 : ℚ) 0 exampleNsT := by
  rw [two_nsmul]; exact exampleDoubleP

/-- **`[4]P = O`**: `P` has order `4`, from `[2]P = T` and `[2]T = O`. -/
private lemma exampleFourP :
    ((4 : ℕ) • Point.some (2 : ℚ) 4 exampleNsP : exampleCurve.Point) = 0 := by
  rw [show (4 : ℕ) = 2 * 2 from rfl, mul_nsmul, exampleTwoP, two_nsmul, exampleDoubleT]

/-- **The halving `[6]P = T`, discharged.**  `[6]P = [4]P + [2]P = O + T = T`.  ⚠️ This is the
hypothesis the general assembly adds on top of the merged ones, and the reason this block exists:
it is proved here, not assumed. -/
private lemma exampleSixP :
    (6 : ℕ) • torsionPoint exampleNsP.left = Point.some (0 : ℚ) 0 exampleNsT := by
  change (6 : ℕ) • Point.some (2 : ℚ) 4 exampleNsP = _
  rw [show (6 : ℕ) = 4 + 2 from rfl, add_nsmul, exampleFourP, zero_add, exampleTwoP]

/-- **`P ≠ T`**: the halving relates two *distinct* named affine points.  ⚠️ Checked rather than
implied — `[n]P = T` at `P = T` would say `T` is fixed by `[n]`, and a certificate cannot claim to
exercise the halving if it silently runs at the diagonal. -/
private lemma examplePNeT :
    Point.some (2 : ℚ) 4 exampleNsP ≠ Point.some (0 : ℚ) 0 exampleNsT := by
  rw [ne_eq, Point.some.injEq]
  norm_num

/-- **The assembly applies at `n = 6`**, on a named curve over `ℚ`, at a named affine `T` whose
`6`-torsion is proved and a named affine `P` whose halving relation `[6]P = T` is proved.

⚠️ `hprin` is the **only** hypothesis left bound, exactly as at the merged `n = 2` and `n = 3` over
a general field.  It is `#418` and it is not dischargeable here or anywhere on this board today.
Everything else — including the halving, which the merged assemblies get from `F̄` and this one
cannot at a general index — is inhabited above. -/
private theorem exampleAssemblySix
    (hprin : ∀ f : exampleCurve.FunctionField, f ≠ 0 →
      divisor exampleCurve f
          = Finsupp.single (pointClosedPoint exampleNsT.left) (6 : ℤ) →
      ∃ g₀ : exampleCurve.FunctionField, g₀ ≠ 0 ∧
        6 • divisor exampleCurve g₀ = divisor exampleCurve (mulByNEndo 6
          (transcendental_xCoord_nsmul_of_smooth exampleTwo exampleThree
            (by norm_num) primeFactorsSix) f)) :
    ∃ f : exampleCurve.FunctionField, f ≠ 0 ∧
      divisorProj exampleCurve f
          = Finsupp.single (some (pointClosedPoint exampleNsT.left)) (6 : ℤ)
            - Finsupp.single (none : ProjPoint exampleCurve) (6 : ℤ) ∧
        ∃ g : exampleCurve.FunctionField, g ≠ 0 ∧
          (∃ u : exampleCurve.CoordinateRingˣ, (u : exampleCurve.CoordinateRing) • g ^ 6
            = mulByNEndo 6 (transcendental_xCoord_nsmul_of_smooth exampleTwo exampleThree
              (by norm_num) primeFactorsSix) f) ∧
          translateEndo exampleNsT.left g = g ∧ weilPairingElt exampleNsT.left g = 1 :=
  -- ⚠️ The two `convert`s are the whole price of stating the theorem `open Classical in`, and they
  -- are bookkeeping rather than mathematics.  `ℚ` has a genuine `DecidableEq` instance, which wins
  -- on priority even inside `open Classical in`, so `exampleTorSixT` and `exampleSixP` are indexed
  -- by `instDecidableEqRat` while the theorem's copies carry `Classical.propDecidable`; the two are
  -- propositionally but not syntactically equal, and `convert` closes the gap by
  -- `Subsingleton.elim`.
  -- See the module docstring for why the alternative places the cost somewhere worse.
  exists_weilPairingElt_self_eq_one_of_smooth_of_nsmul_eq exampleTwo exampleThree
    (n := 6) (by norm_num) primeFactorsSix exampleNsT (by convert exampleTorSixT)
    exampleNsP.left (by convert exampleSixP) hprin

end Nonvacuity

end WeierstrassCurve.Affine
