/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import EllipticCurves.Torsion.ChordSum
import EllipticCurves.Torsion.WronskianUniversal

/-!
# The Wronskian identity satisfies a two-step recurrence needing no fraction field

`EllipticCurves.Torsion.WronskianUniversal` reduces `#E[n] = n²` at odd `n` to a single polynomial
identity about a single curve over a single ring — `univQ.HasWronskianId n`, `#1506` scope item 1:

```
Φₙ′ · ΨSqₙ  −  Φₙ · ΨSqₙ′  =  n · preΨₙ · preΩₙ            in R[X].
```

The route recorded for it decomposes into four steps `S0`–`S3`, of which `S0` is on `main` and `S1`
— the additive recurrence `Φₘ₊₁ΨSqₘ₋₁ + Φₘ₋₁ΨSqₘ₊₁ = 2XΦₘ² + (2X²+b₂X+b₄)ΦₘΨSqₘ + (b₄X+b₆)ΨSqₘ²`,
issue `#1516` — is `WeierstrassCurve.hasChordSum` (`EllipticCurves.Torsion.ChordSum`), a theorem
over every commutative ring at every index.  ⚠️ **`S1` is therefore not a hypothesis anywhere in
this file.**  It used to be, under the name `WronskianRec.ChordSum` — a second copy of
`WeierstrassCurve.HasChordSum` introduced only because `#1516` was in flight with no head to check
a name against when this file was written.  That copy is gone (`#1520` item 2) and every statement
below takes `hasChordSum` directly.

`S3` was priced as *the* remaining cost, on the grounds that it is a chain rule
`x_{m+1}′ = ∂_uΣ·xₘ′ + ∂_XΣ − x_{m−1}′` for the rational functions `xₘ = Φₘ/ΨSqₘ`, and so wants a
derivation on a **fraction field**, which neither this development nor Mathlib has.

⚠️ **`WeierstrassCurve.wronskian_recurrence` below is that step, and it takes no chain rule and
mentions no quotient.**  The `Wronskian` of the pair at `m ± 1` is determined by the one at `m`, by
differentiating `S1` and `S0` **in `R[X]`** and multiplying by `ΨSqₘ₊₁ · ΨSqₘ₋₁`.  The proof is one
`linear_combination`, over an arbitrary commutative ring, with no hypothesis on the index.

## The derivation, in four lines, so that it is checkable without re-deriving it

Write `a = Φₘ₊₁`, `A = ΨSqₘ₊₁`, `b = Φₘ₋₁`, `B = ΨSqₘ₋₁`, and let `P` be the right-hand side of
`S1`, so that `S1` reads `a·B + b·A = P` and `S0` reads `A·B = Gₘ²` with `Gₘ = X·ΨSqₘ − Φₘ`.
`derivative` is a derivation, so `S1` differentiates to `a′B + aB′ + b′A + bA′ = P′`.  Multiply that
by `A·B` and subtract it from the quantity `a′AB² + b′A²B − aA′B² − bB′A²` we are after:

```
target − A·B·P′ = −aB(A′B + AB′) − bA(A′B + AB′) = −(aB + bA)·(AB)′ = −P·(Gₘ²)′ = −2P·Gₘ·Gₘ′ ,
```

so `target = Gₘ²·P′ − 2P·Gₘ·Gₘ′`, and expanding `P` and `Gₘ` turns the right-hand side into
`Gₘ · (Lₘ · Wrₘ − Rₘ)` for the two explicit polynomials `WronskianRec.L` and `WronskianRec.Rem`
below.  Nothing anywhere is divided by.

## What is still owed, and it is derivative-free

Substituting the *claimed* value `Wrₖ = k · preΨ₂ₖ` into the recurrence leaves two identities with
no derivative in them, `WronskianRec.OmegaSum` and `WronskianRec.OmegaDiff`:

```
C1:   preΨ₂ₘ₊₂·ΨSqₘ₋₁² + preΨ₂ₘ₋₂·ΨSqₘ₊₁²  =  Gₘ · Lₘ · preΨ₂ₘ
C2:   preΨ₂ₘ₊₂·ΨSqₘ₋₁² − preΨ₂ₘ₋₂·ΨSqₘ₊₁²  =  −Gₘ · Rₘ
```

Since `preΨ₂ₖ = preΨₖ · preΩₖ` (`preΨ_two_mul`) and `ψₖ · Ωₖ = ψ₂ₖ · ψ₂`, these are the **sum** and
the **difference** of the `y`-coordinates of `(m±1) • P`, exactly as `S1` is the sum of their
`x`-coordinates: they are `S1`'s `y`-half.  This file proves neither; it proves that they and `S1`
are *all* that is owed.

⚠️ **They are no longer owed.**  `WeierstrassCurve.omegaSum` and `WeierstrassCurve.omegaDiff`
(`EllipticCurves.Torsion.OmegaChordSum`, `#1519`) prove `C1` and `C2` over every commutative ring at
every index, and `WeierstrassCurve.hasWronskianId` in that same file is `#1506` item 1 with **no**
hypotheses.  They remain hypotheses *here* only because that file imports this one; a consumer
should reach for `hasWronskianId` and `WeierstrassCurve.Affine.card_torsion_eq_sq_of_odd` rather
than for the conditional statements below.

## What this file therefore does and does not settle

`WeierstrassCurve.hasWronskianId_of_recurrence` takes the two families as hypotheses and returns
`HasWronskianId` at **every** index, over any characteristic-`0` domain.  Composed with
`WeierstrassCurve.hasWronskianId_of_univQ` that is `#1506` item 1 for every curve over every
commutative ring, and composed further with
`WeierstrassCurve.Affine.card_torsion_eq_sq_of_univQ` it is `#E[n] = n²` at odd `n`.

⚠️ **Nothing *here* is a proof of `#E[n] = n²`**: `C1` and `C2` are hypotheses in every statement
below that mentions them.  ⚠️ But the tree does prove it at odd `n` — see
`WeierstrassCurve.Affine.card_torsion_eq_sq_of_odd` — so a docstring citing this file as evidence
that `#E[n] = n²` is open would be wrong.  Taking that consequence into
`EllipticCurves.Torsion.PrimaryTower`'s gate list, `#1490` and `#293` is `#1522` and is not done
here.

⚠️ **The base cases are why `WronskianUniversal` names three of them.**  The induction runs on pairs
of adjacent indices and its step at `m` cancels `ΨSqₘ₋₁`, so the step from `(0, 1)` does **not**
run: `ΨSq₀ = 0`.  It is `hasWronskianId_two` that gets the induction started, from `(1, 2)`;
`hasWronskianId_neg` then covers the negative indices.

## Main results

⚠️ Every public declaration of this file is listed.

* `WeierstrassCurve.WronskianRec.G`, `.L`, `.Rem` : the three explicit polynomials the recurrence is
  written in.  ⚠️ They are packaging, not content.
* `WeierstrassCurve.WronskianRec.OmegaSum`, `.OmegaDiff` : `C1` and `C2`, the two remaining
  hypothesis shapes.  ⚠️ There is deliberately no `WronskianRec.ChordSum` beside them: `S1`'s shape
  is `WeierstrassCurve.HasChordSum` and this file uses that one.
* `WeierstrassCurve.WronskianRec.omegaSum_zero`, `.omegaDiff_zero` : the two instances of those
  shapes that are affordable to prove outright.  ⚠️ They are a non-vacuity check, not evidence for
  the general shapes; `omegaDiff_zero` is the one that has force, because it fixes the sign and the
  factor `G₀`.  ⚠️ **Keep them.**  They are cheap, and they are what would catch a transcription
  error in `OmegaSum` / `OmegaDiff` reintroduced by a later edit.
* `WeierstrassCurve.wronskian_recurrence` : the step that was thought to need a fraction field.
  Unconditional over an arbitrary commutative ring at an arbitrary index; its only inputs are
  `hasChordSum` and `S0`.
* `WeierstrassCurve.hasWronskianId_add_one` : the induction step, cancelling `ΨSqₘ₋₁`.
* `WeierstrassCurve.hasWronskianId_of_recurrence` : the identity at every index over a
  characteristic-`0` domain, from `C1` and `C2`.
* `WeierstrassCurve.hasWronskianId_of_univQ_recurrence` : the same for every curve over every
  commutative ring, from `C1` and `C2` **at `univQ` only**.
* `WeierstrassCurve.Affine.card_torsion_eq_sq_of_recurrence` : the payoff, `#E[n] = n²` at odd `n`,
  from `C1` and `C2`.  ⚠️ Both are theorems, so prefer the unconditional
  `WeierstrassCurve.Affine.card_torsion_eq_sq_of_odd`.

## References

* [J. Silverman, *The arithmetic of elliptic curves*][silverman2009], III.5 and Exercise 3.7.
-/

open Polynomial

namespace WeierstrassCurve

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R)

namespace WronskianRec

/-! ### The three polynomials the recurrence is written in -/

/-- `Gₘ := X · ΨSqₘ − Φₘ`.  By `Φ_eq_neg_adjacent_add` this is the adjacent product
`preΨₘ₊₁ · preΨₘ₋₁ · Eₘ`, and by `ΨSq_succ_mul_ΨSq_pred` its square is `ΨSqₘ₊₁ · ΨSqₘ₋₁` — which is
the step `S0` of the route, and is the only place either lemma is used here. -/
noncomputable def G (m : ℤ) : R[X] := X * W.ΨSq m - W.Φ m

/-- `Lₘ := (6X² + b₂X + b₄) · Φₘ + (2X³ + b₂X² + 3b₄X + 2b₆) · ΨSqₘ`, the coefficient of the
`Wronskian` at `m` in the recurrence. -/
noncomputable def L (m : ℤ) : R[X] :=
  (6 * X ^ 2 + C W.b₂ * X + C W.b₄) * W.Φ m +
    (2 * X ^ 3 + C W.b₂ * X ^ 2 + 3 * C W.b₄ * X + 2 * C W.b₆) * W.ΨSq m

/-- `Rₘ := 2Φₘ³ + (6X + b₂)Φₘ²ΨSqₘ + (b₂X + 3b₄)ΦₘΨSqₘ² + (b₄X + 2b₆)ΨSqₘ³`, the derivative-free
remainder of the recurrence. -/
noncomputable def Rem (m : ℤ) : R[X] :=
  2 * W.Φ m ^ 3 + (6 * X + C W.b₂) * W.Φ m ^ 2 * W.ΨSq m +
    (C W.b₂ * X + 3 * C W.b₄) * W.Φ m * W.ΨSq m ^ 2 +
    (C W.b₄ * X + 2 * C W.b₆) * W.ΨSq m ^ 3

/-! ### The two hypothesis shapes

⚠️ There were three.  `S1`'s shape used to be duplicated here as `WronskianRec.ChordSum`, because
`#1516` was in flight with no head to check a name against; it is now
`WeierstrassCurve.HasChordSum` (`EllipticCurves.Torsion.ChordSum`) and nothing else, and `S1` is
discharged rather than assumed everywhere below. -/

/-- **`C1`, the sum half of `S1`'s `y`-analogue**:

```
preΨ₂ₘ₊₂ · ΨSqₘ₋₁²  +  preΨ₂ₘ₋₂ · ΨSqₘ₊₁²  =  Gₘ · Lₘ · preΨ₂ₘ .
```

⚠️ The factor `Gₘ` is not optional — the identity is false without it, and the degrees (`4m²` on
both sides) only agree with it. -/
def OmegaSum (m : ℤ) : Prop :=
  W.preΨ (2 * (m + 1)) * W.ΨSq (m - 1) ^ 2 + W.preΨ (2 * (m - 1)) * W.ΨSq (m + 1) ^ 2 =
    WronskianRec.G W m * WronskianRec.L W m * W.preΨ (2 * m)

/-- **`C2`, the difference half of `S1`'s `y`-analogue**:

```
preΨ₂ₘ₊₂ · ΨSqₘ₋₁²  −  preΨ₂ₘ₋₂ · ΨSqₘ₊₁²  =  −Gₘ · Rₘ .
```

⚠️ As with `OmegaSum`, the factor `Gₘ` is not optional. -/
def OmegaDiff (m : ℤ) : Prop :=
  W.preΨ (2 * (m + 1)) * W.ΨSq (m - 1) ^ 2 - W.preΨ (2 * (m - 1)) * W.ΨSq (m + 1) ^ 2 =
    -(WronskianRec.G W m * WronskianRec.Rem W m)


/-! ### Non-vacuity: the two shapes, checked at the index where they are affordable

⚠️ These do **not** certify the general shapes — `EllipticCurves.Torsion.OmegaChordSum` does that,
with a proof.  What they rule out is the failure mode a hypothesis-shaped statement invites: a
`Prop` that nothing satisfies, or one whose two sides were transcribed with a wrong sign or a
dropped factor.  ⚠️ The two `S1` instances that used to sit beside them are gone with
`WronskianRec.ChordSum`; `WeierstrassCurve.hasChordSum` subsumes them. -/

/-- `C1` at `m = 0`: `preΨ₂·ΨSq₋₁² + preΨ₋₂·ΨSq₁² = 1 - 1 = 0`, and the right-hand side carries the
factor `preΨ₀ = 0`. -/
theorem omegaSum_zero : OmegaSum W 0 := by
  rw [OmegaSum, show 2 * ((0 : ℤ) + 1) = 2 by norm_num, show 2 * ((0 : ℤ) - 1) = -2 by norm_num,
    show 2 * (0 : ℤ) = 0 by norm_num, show (0 : ℤ) - 1 = -1 by norm_num,
    show (0 : ℤ) + 1 = 1 by norm_num, preΨ_zero, preΨ_two, preΨ_neg, preΨ_two, ΨSq_neg, ΨSq_one]
  ring

/-- `C2` at `m = 0`, and this one is a genuine check on the sign and on the factor `G₀`:
the left-hand side is `preΨ₂ - preΨ₋₂ = 2`, and the right-hand side is `-(G₀ · R₀) = -((-1) · 2)`,
since `G₀ = X·ΨSq₀ - Φ₀ = -1` and `R₀ = 2·Φ₀³ = 2`.  ⚠️ Dropping the `G₀` would give `-2`. -/
theorem omegaDiff_zero : OmegaDiff W 0 := by
  rw [OmegaDiff, G, Rem, show 2 * ((0 : ℤ) + 1) = 2 by norm_num,
    show 2 * ((0 : ℤ) - 1) = -2 by norm_num, show (0 : ℤ) - 1 = -1 by norm_num,
    show (0 : ℤ) + 1 = 1 by norm_num, preΨ_two, preΨ_neg, preΨ_two, ΨSq_neg, ΨSq_one, Φ_zero,
    ΨSq_zero]
  ring

end WronskianRec

/-! ### The recurrence -/

/-- **The two-step recurrence for the Wronskian, from `S1` at the single index `m`.**

```
Wrₘ₊₁ · ΨSqₘ₋₁²  +  Wrₘ₋₁ · ΨSqₘ₊₁²  =  Gₘ · (Lₘ · Wrₘ  −  Rₘ) ,
```

where `Wrₖ = Φₖ′·ΨSqₖ − Φₖ·ΨSqₖ′` is the left-hand side of `HasWronskianId k`.

⚠️ **This is the step `S3` of `#1506` item 1's route, and it needs no derivation on a fraction
field.**  See the module docstring for the four-line derivation; in Lean it is `derivative` applied
to `S1` and to `S0`, then one `linear_combination`.  There is no hypothesis on `R` and none on `m`.

⚠️ `S1` used to be a hypothesis here.  It is now supplied internally by
`WeierstrassCurve.hasChordSum` (`EllipticCurves.Torsion.ChordSum`, `#1516`), which holds over every
commutative ring at every index — so the *only* thing this statement asserts about `S3` is that it
follows from `S1` and `S0`, and that is what the proof does. -/
theorem wronskian_recurrence (m : ℤ) :
    (derivative (W.Φ (m + 1)) * W.ΨSq (m + 1) - W.Φ (m + 1) * derivative (W.ΨSq (m + 1))) *
        W.ΨSq (m - 1) ^ 2 +
      (derivative (W.Φ (m - 1)) * W.ΨSq (m - 1) - W.Φ (m - 1) * derivative (W.ΨSq (m - 1))) *
        W.ΨSq (m + 1) ^ 2 =
    WronskianRec.G W m *
      (WronskianRec.L W m * (derivative (W.Φ m) * W.ΨSq m - W.Φ m * derivative (W.ΨSq m)) -
        WronskianRec.Rem W m) := by
  have hS1 := W.hasChordSum m
  rw [HasChordSum] at hS1
  have hS0 : W.ΨSq (m + 1) * W.ΨSq (m - 1) = (X * W.ΨSq m - W.Φ m) ^ 2 := by
    rw [ΨSq_succ_mul_ΨSq_pred, Φ_eq_neg_adjacent_add]
    ring
  have hd1 := congrArg derivative hS1
  have hd0 := congrArg derivative hS0
  simp only [derivative_add, derivative_sub, derivative_mul, derivative_pow, derivative_X,
    derivative_C, derivative_ofNat, Nat.cast_ofNat, map_ofNat] at hd1 hd0
  rw [WronskianRec.G, WronskianRec.L, WronskianRec.Rem]
  linear_combination (W.ΨSq (m + 1) * W.ΨSq (m - 1)) * hd1 -
      (2 * X * W.Φ m ^ 2 + (2 * X ^ 2 + C W.b₂ * X + C W.b₄) * W.Φ m * W.ΨSq m +
        (C W.b₄ * X + C W.b₆) * W.ΨSq m ^ 2) * hd0 -
      (derivative (W.ΨSq (m + 1)) * W.ΨSq (m - 1) +
        W.ΨSq (m + 1) * derivative (W.ΨSq (m - 1))) * hS1 +
      (2 * W.Φ m ^ 2 + 4 * X * W.Φ m * derivative (W.Φ m) +
        (4 * X + C W.b₂) * W.Φ m * W.ΨSq m +
        (2 * X ^ 2 + C W.b₂ * X + C W.b₄) *
          (derivative (W.Φ m) * W.ΨSq m + W.Φ m * derivative (W.ΨSq m)) +
        C W.b₄ * W.ΨSq m ^ 2 +
        2 * (C W.b₄ * X + C W.b₆) * W.ΨSq m * derivative (W.ΨSq m)) * hS0

/-! ### The induction -/

/-- **The induction step.**  `HasWronskianId` at `m − 1` and at `m` gives it at `m + 1`, provided
`ΨSqₘ₋₁` may be cancelled.

The recurrence `wronskian_recurrence` and the two derivative-free identities `OmegaSum`,
`OmegaDiff` say the same thing about the actual Wronskians and about their claimed values
`k · preΨ₂ₖ`, so their difference `Dₖ := Wrₖ − k·preΨ₂ₖ` satisfies

```
Dₘ₊₁ · ΨSqₘ₋₁²  +  Dₘ₋₁ · ΨSqₘ₊₁²  =  Gₘ · Lₘ · Dₘ ,
```

and `Dₘ₋₁ = Dₘ = 0` leaves `Dₘ₊₁ · ΨSqₘ₋₁² = 0`.  ⚠️ The `preΨ₂ₖ` of `OmegaSum` / `OmegaDiff` and
the `preΨₖ · preΩₖ` of `HasWronskianId` are matched by `preΨ_two_mul`, which is where the three
`e`-hypotheses of the proof come from. -/
theorem hasWronskianId_add_one [NoZeroDivisors R] {m : ℤ}
    (hC1 : WronskianRec.OmegaSum W m) (hC2 : WronskianRec.OmegaDiff W m)
    (hprev : W.HasWronskianId (m - 1)) (hcur : W.HasWronskianId m) (hne : W.ΨSq (m - 1) ≠ 0) :
    W.HasWronskianId (m + 1) := by
  have key := W.wronskian_recurrence m
  rw [WronskianRec.OmegaSum] at hC1
  rw [WronskianRec.OmegaDiff] at hC2
  rw [HasWronskianId] at hprev hcur ⊢
  have e1 := W.preΨ_two_mul (m + 1)
  have e2 := W.preΨ_two_mul (m - 1)
  have e3 := W.preΨ_two_mul m
  push_cast at hprev hcur ⊢
  have hcancel :
      (derivative (W.Φ (m + 1)) * W.ΨSq (m + 1) - W.Φ (m + 1) * derivative (W.ΨSq (m + 1)) -
        ((m : R[X]) + 1) * W.preΨ (m + 1) * W.preΩ (m + 1)) * W.ΨSq (m - 1) ^ 2 = 0 := by
    linear_combination key - W.ΨSq (m + 1) ^ 2 * hprev +
      (WronskianRec.G W m * WronskianRec.L W m) * hcur + ((m : R[X]) - 1) * W.ΨSq (m + 1) ^ 2 * e2 -
      (m : R[X]) * WronskianRec.G W m * WronskianRec.L W m * e3 - (m : R[X]) * hC1 - hC2 +
      ((m : R[X]) + 1) * W.ΨSq (m - 1) ^ 2 * e1
  exact sub_eq_zero.mp ((mul_eq_zero.mp hcancel).resolve_right (pow_ne_zero _ hne))

/-- **The identity at every index, from `C1` and `C2`.**  Over a characteristic-`0` domain —
`ΨSqₖ ≠ 0` at every `k ≠ 0` is `Mathlib`'s `ΨSq_ne_zero`, whose hypothesis `(k : R) ≠ 0` is free
there — the recurrence propagates from the pair `(1, 2)` to every positive index, and
`hasWronskianId_neg` covers the rest.

⚠️ The pair `(0, 1)` cannot start it: the step at `m = 1` cancels `ΨSq₀`, which is `0`.  That is
why `hasWronskianId_two` exists. -/
theorem hasWronskianId_of_recurrence [IsDomain R] [CharZero R]
    (hC1 : ∀ m : ℤ, WronskianRec.OmegaSum W m)
    (hC2 : ∀ m : ℤ, WronskianRec.OmegaDiff W m) (n : ℤ) :
    W.HasWronskianId n := by
  have step : ∀ k : ℕ, W.HasWronskianId ((k : ℤ) + 1) ∧ W.HasWronskianId ((k : ℤ) + 2) := by
    intro k
    induction k with
    | zero =>
      refine ⟨?_, ?_⟩
      · rw [show ((0 : ℕ) : ℤ) + 1 = 1 by norm_num]
        exact W.hasWronskianId_one
      · rw [show ((0 : ℕ) : ℤ) + 2 = 2 by norm_num]
        exact W.hasWronskianId_two
    | succ k ih =>
      obtain ⟨h1, h2⟩ := ih
      have e : ((k : ℤ) + 2) - 1 = (k : ℤ) + 1 := by ring
      have hne : W.ΨSq (((k : ℤ) + 2) - 1) ≠ 0 := by
        rw [e]
        exact W.ΨSq_ne_zero (Int.cast_ne_zero.mpr (by omega))
      have hstep := W.hasWronskianId_add_one (m := (k : ℤ) + 2) (hC1 _) (hC2 _)
        (by rw [e]; exact h1) h2 hne
      refine ⟨?_, ?_⟩
      · rw [show ((k + 1 : ℕ) : ℤ) + 1 = (k : ℤ) + 2 by push_cast; ring]
        exact h2
      · rw [show ((k + 1 : ℕ) : ℤ) + 2 = (k : ℤ) + 2 + 1 by push_cast; ring]
        exact hstep
  have pos : ∀ k : ℕ, W.HasWronskianId (k : ℤ) := by
    intro k
    match k with
    | 0 =>
      rw [show ((0 : ℕ) : ℤ) = 0 by norm_num]
      exact W.hasWronskianId_zero
    | (k + 1) =>
      rw [show ((k + 1 : ℕ) : ℤ) = (k : ℤ) + 1 by push_cast; ring]
      exact (step k).left
  induction n using Int.negInduction with
  | nat k => exact pos k
  | neg ih k => exact hasWronskianId_neg.mpr (ih k)

/-- **`#1506` item 1 for every curve over every commutative ring, from `C1` and `C2` at `univQ`
alone.**  The induction of `hasWronskianId_of_recurrence` is run once, over
`MvPolynomial (Fin 5) ℚ` — a characteristic-`0` domain, which is exactly what the cancellation in
`hasWronskianId_add_one` asks for — and `hasWronskianId_of_univQ` transports the conclusion. -/
theorem hasWronskianId_of_univQ_recurrence (hC1 : ∀ m : ℤ, WronskianRec.OmegaSum univQ m)
    (hC2 : ∀ m : ℤ, WronskianRec.OmegaDiff univQ m) (n : ℤ) :
    W.HasWronskianId n :=
  hasWronskianId_of_univQ (univQ.hasWronskianId_of_recurrence hC1 hC2 n) W

end WeierstrassCurve

/-! ### The payoff -/

namespace WeierstrassCurve.Affine

variable {F : Type*} [Field F] {W : Affine F}

/-- **`#E[n] = n²` with `(2 : F) ≠ 0`, at odd `n` with `(n : F) ≠ 0`, with `C1` and `C2` at
`univQ` the only gates left.**

What the statement says is that between this tree and `#1490` item 3 there are exactly two
polynomial identities, neither of which mentions a derivative except through the merged
`Polynomial.derivative` on `R[X]`.  ⚠️ It used to carry a third hypothesis, `S1`; that is now
`WeierstrassCurve.hasChordSum` and is supplied internally.

⚠️ **This is no longer the sharpest statement of its conclusion, and a reader should not take it
for one.**  `C1` and `C2` are theorems — `WeierstrassCurve.omegaSum` and
`WeierstrassCurve.omegaDiff` (`EllipticCurves.Torsion.OmegaChordSum`, `#1519`) — so
`WeierstrassCurve.Affine.card_torsion_eq_sq_of_odd` in that file proves the same conclusion with no
hypothesis at all.  This one is kept because it records *which* two identities the conclusion rests
on, which is not visible from the unconditional form. -/
theorem card_torsion_eq_sq_of_recurrence [DecidableEq F] [IsAlgClosed F] [W.IsElliptic]
    (h2 : (2 : F) ≠ 0) {n : ℕ} (hodd : Odd n) (hn : (n : F) ≠ 0)
    (hC1 : ∀ m : ℤ, WronskianRec.OmegaSum univQ m)
    (hC2 : ∀ m : ℤ, WronskianRec.OmegaDiff univQ m) :
    Nat.card (W.torsion n) = n ^ 2 :=
  card_torsion_eq_sq_of_wronskian_identity h2 hodd hn
    (by
      have H := W.hasWronskianId_of_univQ_recurrence hC1 hC2 (n : ℤ)
      rw [HasWronskianId] at H
      rw [H]; push_cast; ring)

end WeierstrassCurve.Affine
