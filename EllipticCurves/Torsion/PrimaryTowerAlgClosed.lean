/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import EllipticCurves.Torsion.ThreePrimary
import EllipticCurves.Torsion.TwoTorsionOrder

/-!
# The `p`-primary tower over `F̄`: `#E[p] = p²` is the only hypothesis left

`EllipticCurves.Torsion.PrimaryTower` runs the `p`-primary ascent once at a general index, taking
two hypotheses:

1. `hsurj : Function.Surjective fun P : W.Point => p • P`, and
2. `hcard : Nat.card (W.torsion p) = p ^ 2`.

Until now both were supplied only at `p = 2` and `p = 3`, by
`EllipticCurves.Torsion.TwoPrimary` and `EllipticCurves.Torsion.ThreePrimary`.  **Hypothesis (1) is
now available at every index**: `WeierstrassCurve.Affine.nsmul_surjective_of_two_ne_zero`
(`EllipticCurves.Torsion.TwoTorsionOrder`) proves it over an algebraically closed field of
characteristic `≠ 2` for every `n ≠ 0`, and its conclusion is *verbatim* `hsurj`.

This file substitutes it.  Every statement below is `PrimaryTower`'s statement with (1) discharged,
so that a reader can see from a single signature that, beyond the hypotheses on the field recorded
in the next section, **`hcard` is the whole of what is owed** at a prime `p ≥ 5`.

⚠️ **`hcard` is not a consequence of (1).**  `PrimaryTower`'s docstring says so and is right:
surjectivity of `[p]` is a statement about the image of `[p]`, `#E[p]` one about its kernel, and
nothing in this tree connects them.  Discharging (1) at every `p` therefore does **not** make the
`p`-primary tower unconditional; it isolates the one gate that is left.

⚠️ **That gate is now closed at every odd `p`, and not here.**  This paragraph used to end *"at any
`p ∉ {2, 3}`"*, which said the tower was conditional at every `p ≥ 5`; `card_torsion_eq_sq_of_odd`
(`EllipticCurves.Torsion.OmegaChordSum`) supplies `hcard` at every odd `p` with `(2 : F) ≠ 0` and
`(p : F) ≠ 0` — ⚠️ **both**, and this clause used to name only the second (`#1137`) — and
`EllipticCurves.Torsion.PrimaryTowerOdd` substitutes it into all four statements below.  Everything
in **this** file stays as it is and stays useful: it is the file that isolates `hcard`, and it is
still the only hypothesis these statements carry.

## What the substitution costs

`nsmul_surjective_of_two_ne_zero` carries `[IsAlgClosed F]`, `[W.IsElliptic]` and `(2 : F) ≠ 0`, so
those three appear below where `PrimaryTower` had none of them.  They are three of the four
hypotheses its own docstring records as *"consumed entirely by the two inputs"*; the fourth,
`(3 : F) ≠ 0`, is not one of them and stays with hypothesis (2).

⚠️ Note what is **not** there: `(p : F) ≠ 0` appears nowhere, at any `p`.  The characteristic
hypothesis is `(2 : F) ≠ 0` and nothing else, at every index.  This is the asymmetry
`EllipticCurves.Torsion.ThreePrimary` already records at `p = 3` — *"`nsmul_three_surjective`
carries `(2 : F) ≠ 0` and **not** `(3 : F) ≠ 0`"* — and it holds at every `p`.  Where `(3 : F) ≠ 0`
does enter at `p = 3` is through `card_torsion_three`, i.e. through hypothesis (2).

## Non-vacuity, and it is a check rather than a decoration

The two `example`s at the bottom **equate** the merged `nonempty_torsionTwoPow_addEquiv` and
`nonempty_torsionThreePow_addEquiv` with the general form applied at `p = 2` and `p = 3`, with
`hcard` discharged from the merged sharp counts `card_torsion_two` and `card_torsion_three`.

⚠️ The `rfl` closing each is definitional proof irrelevance and carries no content; **what is
checked is that the equation elaborates**, i.e. that the two sides have the same statement.  That
is the reproduction claim, and it is machine-checked rather than eyeballed: drifting the index by
one, or applying the general form at the other prime, makes both `example`s fail with a type
mismatch.

## Main statements

⚠️ Each of these is the *conditional* form.  For the same four statements with `hcard` discharged at
every odd `p`, see `EllipticCurves.Torsion.PrimaryTowerOdd`.

* `WeierstrassCurve.Affine.card_torsion_pow_of_card` : `#E[pᵏ] = (pᵏ)²`.
* `WeierstrassCurve.Affine.finite_torsion_pow_of_card` : `E[pᵏ]` is finite.
* `WeierstrassCurve.Affine.card_torsion_pow_mul_self_of_card` : the same count as `pᵏ · pᵏ`, the
  shape the `PrimaryBasis` and `TateModule` consumers take it in.
* **`WeierstrassCurve.Affine.nonempty_torsionPow_addEquiv_of_card`** : `E[pᵏ] ≃+ (ℤ/pᵏℤ)²` at a
  prime `p`, with `hcard` as the only remaining hypothesis — discharged at every odd `p` by
  `nonempty_torsionPow_addEquiv_of_odd` (`EllipticCurves.Torsion.PrimaryTowerOdd`).

## References

* [Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.6, Corollary 6.4.
-/

namespace WeierstrassCurve.Affine

variable {F : Type*} [Field F] [DecidableEq F] {W : Affine F} [IsAlgClosed F] [W.IsElliptic]

/-- **`#E[pᵏ] = (pᵏ)²` from the count at `p` alone.**  `card_torsion_pow` with its surjectivity
hypothesis discharged by `nsmul_surjective_of_two_ne_zero`, which is what `(2 : F) ≠ 0` buys: at
`p ≠ 0` and with `(2 : F) ≠ 0`, `hcard` is the whole of what this statement is owed.  ⚠️ No
primality — like the counting half of `EllipticCurves.Torsion.PrimaryTower`, which asks nothing of
`p` at all.  `p ≠ 0` is asked here only by `nsmul_surjective_of_two_ne_zero`. -/
theorem card_torsion_pow_of_card (h2 : (2 : F) ≠ 0) {p : ℕ} (hp : p ≠ 0)
    (hcard : Nat.card (W.torsion p) = p ^ 2) (k : ℕ) :
    Nat.card (W.torsion (p ^ k)) = (p ^ k) ^ 2 :=
  card_torsion_pow (nsmul_surjective_of_two_ne_zero h2 hp) hcard k

/-- **`E[pᵏ]` is finite**, read off the count rather than from a separate finiteness argument.

⚠️ *Not* hypothesis-free on the curve: `[W.IsElliptic]` is in scope here, as *"What the
substitution costs"* above records — it is what the surjectivity input spends.  What the count
replaces is a finiteness argument, not the smoothness hypothesis. -/
theorem finite_torsion_pow_of_card (h2 : (2 : F) ≠ 0) {p : ℕ} (hp : p ≠ 0)
    (hcard : Nat.card (W.torsion p) = p ^ 2) (k : ℕ) : Finite (W.torsion (p ^ k)) :=
  finite_torsion_pow hp (nsmul_surjective_of_two_ne_zero h2 hp) hcard k

/-- **`#E[pᵏ] = pᵏ · pᵏ`**, the same count as `card_torsion_pow_of_card` in the shape the
`PrimaryBasis` and `TateModule` consumers take their cardinality hypothesis in. -/
theorem card_torsion_pow_mul_self_of_card (h2 : (2 : F) ≠ 0) {p : ℕ} (hp : p ≠ 0)
    (hcard : Nat.card (W.torsion p) = p ^ 2) (k : ℕ) :
    Nat.card (W.torsion (p ^ k)) = p ^ k * p ^ k :=
  card_torsion_pow_mul_self (nsmul_surjective_of_two_ne_zero h2 hp) hcard k

/-- **The structure theorem for `E[pᵏ]` at a prime `p`, with `#E[p] = p²` as the only hypothesis.**

⚠️ This is the signature the gate list of `EllipticCurves.Torsion.PrimaryTower` reduces to: over an
algebraically closed field of characteristic `≠ 2`, at a prime `p`, the `p`-primary half of
`E[n] ≅ (ℤ/nℤ)²` is owed `hcard` and nothing further.  At an **odd** `p` with `(p : F) ≠ 0` even
that is owed no longer: `nonempty_torsionPow_addEquiv_of_odd`
(`EllipticCurves.Torsion.PrimaryTowerOdd`) is this statement with `hcard` supplied.

`p.Prime` enters twice, and only one of the
two uses needs it: the rank check inside `nonempty_torsionPow_addEquiv`, as recorded there, and —
through `hp.pos.ne'` — the `p ≠ 0` that `nsmul_surjective_of_two_ne_zero` asks at any index with
`(2 : F) ≠ 0`, which is why the three counting statements above are stated at `p ≠ 0`. -/
theorem nonempty_torsionPow_addEquiv_of_card (h2 : (2 : F) ≠ 0) {p : ℕ} (hp : p.Prime)
    (hcard : Nat.card (W.torsion p) = p ^ 2) (k : ℕ) :
    Nonempty (W.torsion (p ^ k) ≃+ ZMod (p ^ k) × ZMod (p ^ k)) :=
  nonempty_torsionPow_addEquiv hp (nsmul_surjective_of_two_ne_zero h2 hp.pos.ne') hcard k

/-! ## Non-vacuity: the general form gives back the two towers that are known -/

/-- **At `p = 2` the general form is `nonempty_torsionTwoPow_addEquiv`.**

⚠️ Read what this `example` checks.  The `rfl` is definitional proof irrelevance and proves nothing
on its own; what is checked is that the equation **elaborates**, i.e. that the merged theorem and
the general form applied at `p = 2` have the *same statement*, with `hcard` discharged from the
merged sharp count `card_torsion_two`.  A general theorem that had drifted from the one it
generalises would fail here rather than pass quietly. -/
example (h2 : (2 : F) ≠ 0) (k : ℕ) :
    nonempty_torsionTwoPow_addEquiv (W := W) h2 k =
      nonempty_torsionPow_addEquiv_of_card h2 Nat.prime_two
        (by rw [card_torsion_two h2]; norm_num) k :=
  rfl

/-- **At `p = 3` the general form is `nonempty_torsionThreePow_addEquiv`**, checked the same way.

⚠️ `h3` reaches the conclusion only through `card_torsion_three`, i.e. only through hypothesis (2) —
the general form itself never asks for it.  That is the asymmetry
`EllipticCurves.Torsion.ThreePrimary` records, visible here as a hypothesis that appears on the left
of the equation and inside the `hcard` argument on the right, and nowhere else. -/
example (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) (k : ℕ) :
    nonempty_torsionThreePow_addEquiv (W := W) h2 h3 k =
      nonempty_torsionPow_addEquiv_of_card h2 Nat.prime_three
        (by rw [card_torsion_three h2 h3]; norm_num) k :=
  rfl

end WeierstrassCurve.Affine
