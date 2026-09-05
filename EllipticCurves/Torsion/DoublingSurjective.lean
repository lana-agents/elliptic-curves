/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import EllipticCurves.DivisionPolynomial.Coprime
import EllipticCurves.Fixtures
import EllipticCurves.Torsion.NsmulSurjective

/-!
# Multiplication by `2` is surjective on `E(F̄)`

For an elliptic curve `W : Affine F` over an **algebraically closed** field `F` with `(2 : F) ≠ 0`,
every point of `W` is twice another point:

```
∀ Q : W.Point, ∃ P : W.Point, 2 • P = Q.
```

Silverman deduces this from the general fact that a nonconstant morphism of smooth projective curves
is surjective (*AEC*, II.2.3 and III.4.10). The proof here is elementary and entirely
one-dimensional: it solves the doubling equation for the `x`-coordinate directly. In particular
it is **independent of Ward's theorem, of the elliptic-net recurrence, and of the general
multiplication-by-`n` coordinate formula `x(nP) = Φₙ(x)/ΨSqₙ(x)`**.  ⚠️ The independence is the
point of this sentence and still holds; its trailing *"which is what gates the analogous statement
for `n ≠ 2`"* was dropped, because that statement is no longer gated — `[n]`-surjectivity at every
nonzero index with `(2 : F) ≠ 0` is `nsmul_surjective_of_two_ne_zero`
(`EllipticCurves.Torsion.TwoTorsionOrder`).

## The mechanism

Two inputs, both already available.

* **The doubling formula at `n = 2`, with denominators cleared.** For an affine point `(x, y)` of
  `W` not fixed by negation, `EllipticCurves.Torsion.ThreeTorsion` gives the tangent-line defect
  `x(2P) - x = -Ψ₃(x) / (2y + a₁x + a₃)²`, and `EllipticCurves.Torsion.TwoTorsion` gives
  `Ψ₂Sq.eval x = (2y + a₁x + a₃)²`. Since `Φ₂ = X · Ψ₂Sq - Ψ₃`
  (`WeierstrassCurve.Φ_two_eq`, `EllipticCurves.DivisionPolynomial.Coprime`), these give

  ```
  x(2P) · Ψ₂Sq.eval x = Φ₂.eval x                                       (`addX_self_mul_Ψ₂Sq_eval`)
  ```

  — the `n = 2` instance of `x(nP) = Φₙ(x)/ΨSqₙ(x)`, in a form that needs no division.

* **`Φ₂` and `Ψ₂Sq` have no common root.** Two routes reach this, and the file carries both.

  The route the theorem takes is the general one: `eval_Φ_two_ne_zero_of_root_ΨSq` is the `n = 2`
  instance of `eval_Φ_ne_zero_of_eval_ΨSq_ne_zero`
  (`EllipticCurves.DivisionPolynomial.Coprime`), whose adjacent factors at `n = 2` are `ΨSq₃ = Ψ₃²`
  and `ΨSq₁ = 1`, so the only input is `isCoprime_Ψ₃_Ψ₂Sq` read at a root. ⚠️ **It carries neither
  `[IsAlgClosed F]` nor `(2 : F) ≠ 0`** — see *"The hypotheses of input (2)"* below.

  The geometric route is retained immediately after it, as a compiled `example`: a common root `x`
  would be a root of `Ψ₃ = X · Ψ₂Sq - Φ₂` as well, and
  `EllipticCurves.Torsion.ThreeTorsionStructure` shows that a root of `Ψ₃` is never a root of
  `Ψ₂Sq` (`Ψ₂Sq_eval_ne_zero_of_root_Ψ₃`): the point above it would have both partial derivatives
  of the Weierstrass polynomial vanishing. That route needs **no resultant computation and no
  identity of the form `A · Φ₂ + B · Ψ₂Sq = Δ`** — but it does need the algebraic closure and the
  characteristic condition, which is the whole of the trade recorded below.

⚠️ **Those two inputs are the whole of what is `n`-specific here, and the argument that consumes
them is not in this file.** `EllipticCurves.Torsion.NsmulSurjective` runs it once at general `n`:
the degree count on `Φₙ - C x₀ · ΨSqₙ`, the root extraction over `F̄`, the point above the root and
the absorption of the sign ambiguity `nP = ±Q`. This file packages the two inputs as
`hasXCoordFormula_two` and `eval_Φ_two_ne_zero_of_root_ΨSq`, and `exists_nsmul_two_eq` is the
resulting one-line instance of `exists_nsmul_eq_of_hasXCoordFormula`.

No hypothesis on `(3 : F)` is used anywhere.

## ⚠️ What survives over a field that is not algebraically closed

Surjectivity does not — `y² = x³ − x` over `ℚ` has full rational `2`-torsion and no rational halving
of any of it.  What survives is the **conditional** form: `exists_nsmul_two_eq_some_of_root` below
says a named point is twice another as soon as `Φ₂ − x₀·Ψ₂Sq` has a root with a point of `W` above
it, over any field and in any characteristic, because both of this file's inputs to the engine are
already hypothesis-free.  The closure and `h2` of `exists_nsmul_two_eq` live entirely in the two
existence steps that `EllipticCurves.Torsion.NsmulSurjective` promotes to arguments.

## Main statements

* `WeierstrassCurve.Affine.eval_Φ_two_ne_zero_of_root_ΨSq`: `Φ₂` and `Ψ₂Sq` have no common root —
  input (2) of the engine at `n = 2`, over any field with `Δ` a unit.
* `WeierstrassCurve.Affine.addX_self_mul_Ψ₂Sq_eval`: the doubling formula `x(2P) · Ψ₂Sq(x) = Φ₂(x)`.
* `WeierstrassCurve.Affine.hasXCoordFormula_two`: that formula in the form the engine consumes —
  input (1) at `n = 2`.
* `WeierstrassCurve.Affine.exists_addX_self_eq`: every `x₀` is `x(2P)` for some affine point `P` not
  fixed by negation.
* `WeierstrassCurve.Affine.exists_nsmul_two_eq`, `WeierstrassCurve.Affine.nsmul_two_surjective`:
  multiplication by `2` is surjective on `E(F̄)`.
* `WeierstrassCurve.Affine.exists_nsmul_two_eq_some_of_root`: a named affine point is twice another
  point as soon as `Φ₂ − x₀·Ψ₂Sq` has a root carrying a point of `W` above it — **over an arbitrary
  field, with no hypothesis on `(2 : F)`**.  The `Nonvacuity` section discharges its hypotheses on
  `y² = x(x + 1)(x + 4)` over `ℚ`, where it halves the `2`-torsion point `(0, 0)`.
* `WeierstrassCurve.Affine.exists_nsmul_eq_some_of_root_of_mem_torsion_two`: the same root gives
  `[n]P = T` **and** `P ≠ T` at every `n ≡ 2 (mod 4)`, when `T` is `2`-torsion — the shape the
  composite-index Weil-pairing assemblies take as a hypothesis.

## References

* [Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.4, Corollary 4.9 and
  III.6, Corollary 6.4.
-/

open Polynomial

namespace WeierstrassCurve.Affine

variable {F : Type*} [Field F] {W : Affine F}

/-! ## The `Φ₂` dictionary -/

/-- The pointwise form of `Φ_two_eq`. -/
lemma Ψ₃_eval_eq_sub (x : F) : W.Ψ₃.eval x = x * W.Ψ₂Sq.eval x - (W.Φ 2).eval x := by
  rw [Φ_two_eq]
  simp only [eval_sub, eval_mul, eval_X]
  ring

/-- The pointwise form of `Φ_two_eq`, solved for `Φ₂`. -/
lemma Φ_two_eval (x : F) : (W.Φ 2).eval x = x * W.Ψ₂Sq.eval x - W.Ψ₃.eval x := by
  rw [Ψ₃_eval_eq_sub]
  ring

/-! ## Input (2): `Φ₂` and `Ψ₂Sq` have no common root

⚠️ The degree count and the root extraction that used to stand here are `n`-independent and are now
`natDegree_Φ_sub_C_mul_ΨSq` and `exists_eval_Φ_eq` in
`EllipticCurves.Torsion.NsmulSurjective`.

### The hypotheses of input (2)

⚠️ **`eval_Φ_two_ne_zero_of_root_ΨSq` used to carry `[IsAlgClosed F]` and `(2 : F) ≠ 0`, and it no
longer does.** Its docstring used to end *"No resultant computation and no identity of the form
`A · Φ₂ + B · Ψ₂Sq = Δ` is needed"*, describing the geometric route through
`Ψ₂Sq_eval_ne_zero_of_root_Ψ₃`, which is a statement about the points above an `x` and is where
both hypotheses came from.

The trade is explicit and it is not free in both directions:

* what is gained — the statement is now about polynomials over a field with `Δ` a unit and nothing
  else, matching the `hroot` argument of `exists_nsmul_eq_of_hasXCoordFormula`, which mentions no
  closure either;
* what is paid — the general route runs through `isCoprime_Ψ₃_Ψ₂Sq`, which **is** proved from a
  `Δ`-certificate for the pair `(Ψ₃, Ψ₂Sq)` in `EllipticCurves.DivisionPolynomial.Coprime`. So the
  economy sentence above survives only in its literal reading: no certificate for the pair
  `(Φ₂, Ψ₂Sq)` is needed, and one for `(Ψ₃, Ψ₂Sq)` now is.

⚠️ **Neither route is discarded.** The geometric one is kept as a compiled `example` below, so the
closure-free statement and the certificate-free proof both stay in the file. -/

/-- **`Φ₂` and `Ψ₂Sq` have no common root**, over any field over which `W` is elliptic — with **no
algebraic closure and no hypothesis on `(2 : F)`**.

`ΨSq₃ = Ψ₃²` and `ΨSq₁ = 1` are the factors adjacent to `ΨSq₂ = Ψ₂Sq`, so this is the `n = 2`
instance of `eval_Φ_ne_zero_of_eval_ΨSq_ne_zero`
(`EllipticCurves.DivisionPolynomial.Coprime`) and its only input is `isCoprime_Ψ₃_Ψ₂Sq` read at a
root, through `Polynomial.eval_ne_zero_of_isCoprime` in that same file.  ⚠️ **This docstring used
to say *"through Mathlib's `Polynomial.aeval_ne_zero_of_isCoprime`"***, which was accurate when the
step was inlined here; `#1255` made the `eval`-shaped adapter public rather than leave a third
inline copy of it, and Mathlib's `aeval` lemma is now reached one step further away.

This is the `hroot` hypothesis of `exists_nsmul_eq_of_hasXCoordFormula` at `n = 2`.  For the
geometric route that this replaced, and for what the replacement costs, see *"The hypotheses of
input (2)"* above and the `example` below. -/
theorem eval_Φ_two_ne_zero_of_root_ΨSq [W.IsElliptic] (x : F)
    (hx : (W.ΨSq 2).eval x = 0) : (W.Φ 2).eval x ≠ 0 := by
  have hΨ₃ : W.Ψ₃.eval x ≠ 0 :=
    Polynomial.eval_ne_zero_of_isCoprime W.isCoprime_Ψ₃_Ψ₂Sq (by rwa [ΨSq_two] at hx)
  refine eval_Φ_ne_zero_of_eval_ΨSq_ne_zero hx ?_ ?_
  · rw [show (2 : ℤ) + 1 = 3 from rfl, ΨSq_three, eval_pow]
    exact pow_ne_zero _ hΨ₃
  · rw [show (2 : ℤ) - 1 = 1 from rfl, ΨSq_one, eval_one]
    exact one_ne_zero

/-- **The geometric route to input (2), retained.**  This is the proof
`eval_Φ_two_ne_zero_of_root_ΨSq` used to carry, verbatim, under the two hypotheses it used to
carry: a common root of `Φ₂` and `Ψ₂Sq` would be a root of `Ψ₃ = X·Ψ₂Sq − Φ₂`, and a root of `Ψ₃`
is never a root of `Ψ₂Sq`.

⚠️ It is an `example` and not a theorem because its conclusion **is**
`eval_Φ_two_ne_zero_of_root_ΨSq`'s, under strictly more hypotheses; a second name on a weaker form
of the same statement is the worse outcome.  It is kept because it is the only place in this tree
where input (2) is obtained with no Bézout certificate at all. -/
example [IsAlgClosed F] [W.IsElliptic] (h2 : (2 : F) ≠ 0) (x : F)
    (hx : (W.ΨSq 2).eval x = 0) : (W.Φ 2).eval x ≠ 0 := by
  rw [ΨSq_two] at hx
  intro h0
  exact Ψ₂Sq_eval_ne_zero_of_root_Ψ₃ h2 (by rw [Ψ₃_eval_eq_sub, hx, h0]; ring) hx

/-! ## The doubling formula `x(2P) = Φ₂(x) / Ψ₂Sq(x)` -/

variable [DecidableEq F]

/-- **The doubling formula at `n = 2`, with the denominator cleared.** For an affine point `(x, y)`
of `W` not fixed by negation, the `x`-coordinate of `2 • (x, y)` is `Φ₂(x) / Ψ₂Sq(x)`.

This is the `n = 2` instance of the multiplication-by-`n` coordinate formula
`x(nP) = Φₙ(x) / ΨSqₙ(x)`.  ⚠️ This docstring used to add *"the general case is not available"*,
which is false: `hasXCoordFormula_of_two_ne_zero` (`EllipticCurves.Torsion.NsmulOrder`) proves it at
every index with `(2 : F) ≠ 0`.  What is true, and is why the proof below exists, is that doubling
is computed in closed form by the tangent line, so this file needs none of that machinery. -/
lemma addX_self_mul_Ψ₂Sq_eval {x y : F} (h : W.Equation x y) (hy : y ≠ W.negY x y) :
    W.addX x x (W.slope x x y y) * W.Ψ₂Sq.eval x = (W.Φ 2).eval x := by
  have hd : 2 * y + W.a₁ * x + W.a₃ ≠ 0 := two_mul_add_ne_zero_of_Y_ne hy
  have key : (W.addX x x (W.slope x x y y) - x) * (2 * y + W.a₁ * x + W.a₃) ^ 2
      = -W.Ψ₃.eval x := by
    rw [addX_self_sub h hy, div_mul_cancel₀ _ (pow_ne_zero 2 hd)]
  rw [Φ_two_eval, Ψ₂Sq_eval_eq_sq h]
  linear_combination key

/-- The `x`-coordinate solution, packaged with a point above it. Over an algebraically closed field
of characteristic `≠ 2`, for every `x₀` there is an affine point `(x, y)` of `W`, not fixed by
negation, with `x(2 • (x, y)) = x₀`. -/
lemma exists_addX_self_eq [IsAlgClosed F] [W.IsElliptic] (h2 : (2 : F) ≠ 0) (x₀ : F) :
    ∃ x y : F, W.Nonsingular x y ∧ y ≠ W.negY x y ∧
      W.addX x x (W.slope x x y y) = x₀ := by
  obtain ⟨x, hx⟩ := exists_eval_Φ_eq (W := W) (n := 2) (by norm_num) x₀
  simp only [Nat.cast_ofNat, ΨSq_two] at hx
  have hne : W.Ψ₂Sq.eval x ≠ 0 := fun h0 =>
    eval_Φ_two_ne_zero_of_root_ΨSq x (by rw [ΨSq_two]; exact h0) (by rw [hx, h0, mul_zero])
  obtain ⟨y, hy⟩ := exists_equation (W := W) h2 x
  have hns : W.Nonsingular x y := equation_iff_nonsingular.mp hy
  have hyne : y ≠ W.negY x y := by
    intro hcon
    have hd : 2 * y + W.a₁ * x + W.a₃ = 0 := by
      rw [negY] at hcon
      linear_combination hcon
    exact hne (by rw [Ψ₂Sq_eval_eq_sq hy, hd]; ring)
  refine ⟨x, y, hns, hyne, ?_⟩
  have hmul := addX_self_mul_Ψ₂Sq_eval hy hyne
  rw [hx] at hmul
  exact mul_right_cancel₀ hne hmul

/-! ## Input (1): the coordinate formula in the form the engine consumes -/

/-- **The coordinate formula at `n = 2`.** A point at which `Ψ₂Sq` does not vanish is not fixed by
negation, so `2 • P` is the tangent sum, whose `x`-coordinate is `Φ₂(x)/Ψ₂Sq(x)` by
`addX_self_mul_Ψ₂Sq_eval`. -/
theorem hasXCoordFormula_two : HasXCoordFormula W 2 := by
  intro x y h hne
  simp only [Nat.cast_ofNat] at hne ⊢
  rw [ΨSq_two] at hne
  have hyeq : W.Equation x y := h.1
  have hyne : y ≠ W.negY x y := by
    intro hcon
    have hd : 2 * y + W.a₁ * x + W.a₃ = 0 := by
      rw [negY] at hcon
      linear_combination hcon
    exact hne (by rw [Ψ₂Sq_eval_eq_sq hyeq, hd]; ring)
  have hX : W.addX x x (W.slope x x y y) = (W.Φ 2).eval x / (W.ΨSq 2).eval x := by
    rw [ΨSq_two, eq_div_iff hne]
    exact addX_self_mul_Ψ₂Sq_eval hyeq hyne
  have hns₂ : W.Nonsingular ((W.Φ 2).eval x / (W.ΨSq 2).eval x)
      (W.addY x x y (W.slope x x y y)) := by
    rw [← hX]
    exact nonsingular_add h h fun hxy => hyne hxy.right
  refine ⟨W.addY x x y (W.slope x x y y), hns₂, ?_⟩
  rw [two_nsmul, Point.add_self_of_Y_ne hyne]
  simp only [Point.some.injEq, and_true]
  exact hX

/-! ## Surjectivity of multiplication by `2` -/

/-- **Multiplication by `2` is surjective on `E(F̄)`.** Over an algebraically closed field of
characteristic `≠ 2`, every point of an elliptic curve is twice another point.

The two inputs above, fed to `exists_nsmul_eq_of_hasXCoordFormula`. -/
theorem exists_nsmul_two_eq [IsAlgClosed F] [W.IsElliptic] (h2 : (2 : F) ≠ 0) (Q : W.Point) :
    ∃ P : W.Point, 2 • P = Q :=
  exists_nsmul_eq_of_hasXCoordFormula h2 (by norm_num)
    (by simp only [Nat.cast_ofNat]; exact eval_Φ_two_ne_zero_of_root_ΨSq)
    hasXCoordFormula_two Q

/-- **Multiplication by `2` is surjective on `E(F̄)`**, stated as `Function.Surjective`. -/
theorem nsmul_two_surjective [IsAlgClosed F] [W.IsElliptic] (h2 : (2 : F) ≠ 0) :
    Function.Surjective fun P : W.Point => (2 : ℕ) • P :=
  exists_nsmul_two_eq h2

/-! ## Halving a named point over an arbitrary field -/

/-- **A named affine point is twice another point** as soon as `Φ₂ − x₀·Ψ₂Sq` has a root carrying a
point of `W` above it — over an **arbitrary field**, with no algebraic closure and **no hypothesis
on `(2 : F)`**.

This is `exists_nsmul_eq_some_of_hasXCoordFormula_of_root` at `n = 2`, and it is hypothesis-free
because both of the engine's index-dependent inputs already are:
`eval_Φ_two_ne_zero_of_root_ΨSq` needs only `Δ` a unit, and `hasXCoordFormula_two` needs nothing at
all.  ⚠️ The merged `exists_nsmul_two_eq` above carries `[IsAlgClosed F]` and `h2` **only** through
the two existence steps of the engine; supply their conclusions and neither survives.

⚠️ The hypothesis is stated on `W.Ψ₂Sq`, not on `W.ΨSq 2`.  `ΨSq_two` bridges them inside the
proof, and `Ψ₂Sq` is the name every consumer in this tree uses — a hypothesis a caller has to
restate before it can discharge it is a hypothesis nobody discharges.

⚠️ Existence of a halving is genuinely a *hypothesis-shaped* statement over a field that is not
algebraically closed: `y² = x³ − x` over `ℚ` has full rational `2`-torsion and **no** rational
halving of any of it.  What this lemma buys is that the obstruction is entirely visible in one
polynomial root — see the `Nonvacuity` section below. -/
theorem exists_nsmul_two_eq_some_of_root [W.IsElliptic] {x₀ y₀ : F}
    (hQ : W.Nonsingular x₀ y₀) {x y : F} (hxy : W.Equation x y)
    (hx : (W.Φ 2).eval x = x₀ * W.Ψ₂Sq.eval x) :
    ∃ P : W.Point, 2 • P = Point.some x₀ y₀ hQ :=
  exists_nsmul_eq_some_of_hasXCoordFormula_of_root
    (by simp only [Nat.cast_ofNat]; exact eval_Φ_two_ne_zero_of_root_ΨSq)
    hasXCoordFormula_two hQ hxy (by simpa only [Nat.cast_ofNat, ΨSq_two] using hx)

/-! ## From one halving to every index `n ≡ 2 (mod 4)`

⚠️ **The halving of a `2`-torsion point is much more than a halving.**  If `T ∈ E[2]` and
`[2]P = T` then `[4]P = [2]([2]P) = [2]T = O`, so `P` is killed by `4`; and for `n = 4k + 2`

```
[n]P = [4k]P + [2]P = [k]([4]P) + T = O + T = T.
```

So **one root of `Φ₂ − x₀·Ψ₂Sq` discharges the hypothesis `[n]P = T` at every index `n ≡ 2 (mod 4)`
simultaneously**, over an arbitrary field, and the guard `P ≠ T` comes free: `P = T` would force
`T = [2]P = [2]T = O`.

⚠️ **Why this is not a curiosity.**  The consumers of `[n]P = T` in `FunctionField/` are the
Weil-pairing assemblies, and at a *composite* `n` over a field that is not algebraically closed the
halving is the hypothesis that is hardest to inhabit — `[n]P = T` with `[n]T = O` forces
`ord P ∣ n²` and `T ≠ O` forces `ord P ∤ n`, which at `n = 4` already needs a point of order `8`.
The congruence `n ≡ 2 (mod 4)` is exactly the range where a point of order `4` suffices, and a point
of order `4` is what a single application of `exists_nsmul_two_eq_some_of_root` produces.

⚠️ The congruence is stated as `n % 4 = 2` rather than as `∃ k, n = 4 * k + 2`, so that a caller
at a literal index discharges it by `norm_num` with no witness to supply. -/

/-- **A halving of a `2`-torsion point has order dividing `4`.**  `[4]P = [2]([2]P) = [2]T = O`.

⚠️ `mul_nsmul a m n : (m * n) • a = n • m • a` puts the factors out in the **opposite** order to the
one written.  At `4 = 2 * 2` that is invisible; it is not invisible at the call sites downstream, so
the reversal is recorded here rather than rediscovered there. -/
lemma nsmul_four_eq_zero_of_nsmul_two_eq {P T : W.Point} (hP : (2 : ℕ) • P = T)
    (hT : T ∈ W.torsion 2) : (4 : ℕ) • P = 0 := by
  rw [show (4 : ℕ) = 2 * 2 from rfl, mul_nsmul, hP]
  exact mem_torsion_iff.mp hT

/-- **A halving of a non-zero `2`-torsion point is never the point itself.**

⚠️ This is a *theorem*, not a check on coordinates: it holds of **every** halving of `T`, on every
curve, and its proof does not mention the fixture.  A certificate that instantiates `[n]P = T` at
`P = T` would only be saying that `T` is fixed by `[n]`, so the guard is what makes the certificate
about halving at all — and the enumeration form of it (`Point.some.injEq` plus `norm_num` on two
pairs of coordinates) stops being available the moment `P` is produced by an existential. -/
lemma ne_of_nsmul_two_eq {P T : W.Point} (hP : (2 : ℕ) • P = T) (hT : T ∈ W.torsion 2)
    (hT0 : T ≠ 0) : P ≠ T := by
  rintro rfl
  exact hT0 (hP.symm.trans (mem_torsion_iff.mp hT))

/-- **`[n]P = T` at every index `n ≡ 2 (mod 4)`**, from the single halving `[2]P = T` of a
`2`-torsion point.  Writing `n = 4k + 2`, `[n]P = [k]([4]P) + [2]P = O + T`. -/
lemma nsmul_eq_of_nsmul_two_eq {P T : W.Point} (hP : (2 : ℕ) • P = T) (hT : T ∈ W.torsion 2)
    {n : ℕ} (hn : n % 4 = 2) : n • P = T := by
  conv_lhs => rw [← Nat.div_add_mod n 4, hn]
  rw [add_nsmul, mul_nsmul, nsmul_four_eq_zero_of_nsmul_two_eq hP hT, smul_zero, zero_add, hP]

/-- **A named affine `2`-torsion point is `[n]` of another point, distinct from it, at every index
`n ≡ 2 (mod 4)`** — as soon as `Φ₂ − x₀·Ψ₂Sq` has a root carrying a point of `W` above it, over an
**arbitrary field** and with **no hypothesis on `(2 : F)`**.

`exists_nsmul_two_eq_some_of_root` followed by `nsmul_eq_of_nsmul_two_eq` and `ne_of_nsmul_two_eq`.

⚠️ **The guard `P ≠ T` is inside the existential on purpose.**  Shipped as a sibling lemma it would
be applied nowhere: the `P` a consumer binds comes from this existential, so only a witness of
**both** conjuncts is in its hands.  Folded in, off-diagonality is carried by construction even at a
call site that binds the second component to `_`, and no later reader can delete it as unused
without the build noticing. -/
theorem exists_nsmul_eq_some_of_root_of_mem_torsion_two [W.IsElliptic] {x₀ y₀ : F}
    (hQ : W.Nonsingular x₀ y₀) (hT : Point.some x₀ y₀ hQ ∈ W.torsion 2) {x y : F}
    (hxy : W.Equation x y) (hx : (W.Φ 2).eval x = x₀ * W.Ψ₂Sq.eval x) {n : ℕ} (hn : n % 4 = 2) :
    ∃ P : W.Point, n • P = Point.some x₀ y₀ hQ ∧ P ≠ Point.some x₀ y₀ hQ := by
  obtain ⟨P, hP⟩ := exists_nsmul_two_eq_some_of_root hQ hxy hx
  exact ⟨P, nsmul_eq_of_nsmul_two_eq hP hT hn,
    ne_of_nsmul_two_eq hP hT (Point.some_ne_zero hQ)⟩

/-! ## Non-vacuity: a rational halving over `ℚ`

⚠️ The certificate below **must** be over a field that is not algebraically closed, or it certifies
`exists_nsmul_two_eq` instead of anything this section adds.

`y² = x³ + 5x² + 4x = x(x + 1)(x + 4)` over `ℚ`, i.e. `⟨0, 5, 0, 4, 0⟩`, has `b₂ = 20`, `b₄ = 8`,
`b₆ = 0`, `b₈ = −16` and `Δ = 2304 ≠ 0`.  Its `2`-torsion point `T = (0, 0)` is halved by
`P = (2, 6)`, and the reason is a polynomial root:
`Φ₂ = X⁴ − b₄X² − 2b₆X − b₈ = X⁴ − 8X² + 16 = (X² − 4)²` vanishes at `x = 2`, while `x(T) = 0`, so
`Φ₂.eval 2 = 0 = x(T) · Ψ₂Sq.eval 2` on the nose.

⚠️ **This is the hypothesis `hP : 2 • P = T` of `exists_gS_two_of_card` and of
`exists_weilPairingElt_self_eq_one_of_card_two`** (`EllipticCurves.FunctionField.
PullbackPrincipalityTwoRationalTorsion` and `…WeilPairingAlternatingTwoRational`), which both take
it undischarged.  Those files exhibit the halving point by hand; this section derives it from the
root, which is the form that generalises to a splitting field.

⚠️ The curve is deliberately the same one those two files use, so that one `ℚ` fixture serves the
`Torsion/` and `FunctionField/` fronts.  Its `2`-torsion is fully rational and `(0, 0)` is
`2`-divisible because `0 − (−1) = 1` and `0 − (−4) = 4` are both rational squares, with the halving
at `x = 0 + 1·2 = 2`; `y² = x³ − x`, this subtree's default curve, fails exactly that test. -/

section Nonvacuity

/-! The certificate curve is the shared `EllipticCurves.Fixture.y2EqX3Add5X2Add4X` at `R = ℚ`:
`y² = x³ + 5x² + 4x = x(x + 1)(x + 4)`, of discriminant `2304`.  ⚠️ **It is chosen for split
rational `2`-torsion**, which is what makes `T = (0, 0)` a named `ℚ`-point of order `2` and lets
`Φ₂ = (X² − 4)²` be halved at the rational root `x = 2`; over a curve whose `2`-torsion is not
rational there is no such `T` to halve and the certificate below would be about nothing.  The
shared docstring records the same constraint, and the local lemma names were renamed to the fixture
so that no name here points at a curve that is gone.

`(y2EqX3Add5X2Add4X ℚ).IsElliptic` comes from the single `[CharZero F]` instance in `Fixtures`. -/

open EllipticCurves.Fixture

/-- The `2`-torsion point `T = (0, 0)` lies on the curve. -/
private lemma equation_y2EqX3Add5X2Add4X_zero : (y2EqX3Add5X2Add4X ℚ).Equation 0 0 := by
  rw [Affine.equation_iff]; norm_num [y2EqX3Add5X2Add4X]

/-- The halving point `P = (2, 6)` lies on the curve: `8 + 20 + 8 = 36 = 6²`. -/
private lemma equation_y2EqX3Add5X2Add4X_two : (y2EqX3Add5X2Add4X ℚ).Equation 2 6 := by
  rw [Affine.equation_iff]; norm_num [y2EqX3Add5X2Add4X]

/-- **The root that does the work**: `Φ₂(2) = 0 = x(T) · Ψ₂Sq(2)`, since `Φ₂ = (X² − 4)²` here.

⚠️ Routed through `Φ_two_eval` — `Φ₂(x) = x · Ψ₂Sq(x) − Ψ₃(x)`, giving `2 · 144 − 288 = 0` — rather
than by unfolding `W.Φ 2`, whose definition is a recursion. -/
private lemma eval_Φ_two_y2EqX3Add5X2Add4X :
    ((y2EqX3Add5X2Add4X ℚ).Φ 2).eval 2 = (0 : ℚ) * (y2EqX3Add5X2Add4X ℚ).Ψ₂Sq.eval 2 := by
  rw [Φ_two_eval]
  simp only [WeierstrassCurve.Ψ₂Sq, WeierstrassCurve.Ψ₃, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈, y2EqX3Add5X2Add4X]
  norm_num

/-- **`(0, 0)` is twice a rational point of `y² = x(x + 1)(x + 4)` over `ℚ`, with no hypothesis
whatsoever.**

The `hP : 2 • P = T` that `exists_gS_two_of_card` and
`exists_weilPairingElt_self_eq_one_of_card_two` take as an undischarged hypothesis, obtained here
from one root of `Φ₂` over a field that is not algebraically closed. -/
private theorem exists_nsmul_two_eq_y2EqX3Add5X2Add4X :
    ∃ P : (y2EqX3Add5X2Add4X ℚ).Point,
      2 • P = Point.some 0 0 (equation_iff_nonsingular.mp equation_y2EqX3Add5X2Add4X_zero) :=
  exists_nsmul_two_eq_some_of_root _ equation_y2EqX3Add5X2Add4X_two
    eval_Φ_two_y2EqX3Add5X2Add4X

end Nonvacuity

end WeierstrassCurve.Affine
