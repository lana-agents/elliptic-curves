/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import EllipticCurves.FunctionField.CoordinateRingUnits
import EllipticCurves.FunctionField.MulByTwoEndomorphism
import EllipticCurves.FunctionField.MulByThreeEndomorphism

/-!
# The Weil-pairing element `e_n(S, T)` (Weil-pairing construction, rung 6)

Let `W` be a Weierstrass curve over a field `F` whose affine coordinate ring `F[W]` is a Dedekind
domain.  The divisor-theoretic Weil pairing (Silverman AEC III.8) is built from the `n`-th root
`g_S ∈ F(W)` of the pulled-back principal function of a nonzero `n`-torsion point `S` (rung 5,
issue #418): a nonzero `g_S` with

```
u · g_S ^ n = [n]∗ f_S   (u a unit of F[W], [n]∗ = mulByTwoEndo the multiplication-by-n pullback).
```

For a second `n`-torsion point `T = (x₂, y₂)` with translation endomorphism
`τ_T∗ = translateEndo h₂ : F(W) →+* F(W)` (issue #406), the pairing value is the ratio

```
e_n(S, T) := τ_T∗(g_S) / g_S ∈ F(W).
```

This file defines that element (`weilPairingElt`) and proves its defining property — that it is an
`n`-th root of unity, `e_n(S, T) ^ n = 1` — reduced to the single algebraic fact that the
translation fixes `g_S ^ n`:

* `weilPairingElt`               — the element `τ_T∗(g_S) / g_S`;
* `weilPairingElt_ne_zero`       — it is nonzero (for `g_S ≠ 0`);
* `weilPairingElt_pow_eq_one`    — `e_n(S, T) ^ n = 1` from `translateEndo h₂ (g_S ^ n) = g_S ^ n`.

## Why `τ_T∗` fixes `g_S ^ n`, and the scope delivered here

The reason `τ_T∗` fixes `g_S ^ n` is the geometric identity `[n](P + T) = [n]P` (valid because
`T` is an `n`-torsion point, `[n]T = O`): pulling `[n]∗ f_S = u · g_S ^ n` back by `τ_T` leaves it
unchanged, so `τ_T∗(u · g_S ^ n) = u · g_S ^ n`.  Cancelling the unit `u` (which `τ_T∗` also fixes,
being a nonzero constant of `F[W]`) yields `τ_T∗(g_S ^ n) = g_S ^ n`.

This file therefore packages the **Ward- and normality-independent algebra** of rung 6: the
definition of `e_n(S, T)`, its non-vanishing, and the `μ_n`-membership `e_n ^ n = 1`, reduced via
`translateEndo_pow_eq_self_of` to exactly two named inputs on the concrete `n = 2`/`n = 3` data —

* `hcomm : translateEndo h₂ ([n]∗ f_S) = [n]∗ f_S` (the `[n](P + T) = [n]P` commuting identity),
* `huf`   : `translateEndo h₂` fixes the unit `u`  (the unit `u` of `F[W]` is a constant),

both of which are genuine rational-function identities carried here as hypotheses, to be discharged
by a follow-on.  Everything else — the definition, non-vanishing, the `n`-th-root-of-unity property,
and the cancellation reducing the two inputs to `τ_T∗(g_S ^ n) = g_S ^ n` — is unconditional.

## Explicitly out of scope (as issue #419 records)

* **Bilinearity, alternating, Galois-equivariance** — separately valuable follow-ons.
* **Non-degeneracy** — out of scope *of this file*, and **not** Ward-gated; see the next section,
  which is the canonical account of what it consumes.  At `n = 2` over an algebraically closed base
  field it is merged, as `EllipticCurves.FunctionField.WeilPairingNondegenerateTwo` (`#796`); at
  `n = 3`, and over a general field at either `n`, it is not.
* **General `n`** — needs the general `[n]∗` (#404 crux); only `n = 2, 3` are concretely available.
* The normality discharge `IsIntegrallyClosed W.CoordinateRing` — out of scope of this file because
  it is **done**, not because it is blocked.
  `EllipticCurves.FunctionField.CoordinateRingNormalGeneral` registers it, and Dedekindness with
  it, as a global **instance** for `[W.IsElliptic]` over an **arbitrary** field.  That is why the
  single `variable` line below carries no Dedekind hypothesis, and why nothing downstream has to
  supply one.  ⚠️ Said relative to the file rather than by line number, which rots: the number
  first written into this bullet was already stale when it was pushed, and the bullet's own added
  lines then moved the block again.

## What non-degeneracy actually consumes (`#769`) — the canonical statement

⚠️ Until `#769` this file and seventeen others said non-degeneracy was *"Ward-gated (`#242`)"* or
*"needs `#E[n] = n²` (`#242`)"*.  **Both halves of that are wrong**, and they are wrong differently
at the two `n` this tree can state the pairing at.  The other sites now point here rather than
restate the gate; keep it that way, so that the next fact to land has one sentence to refresh and
not eighteen.

Silverman *AEC* III.8, Prop. 8.1(d): if `e_n(S, T) = 1` for every `T ∈ E[n]` then `S = O`.  Read at
`n = 2`, for `S = (x, y)` a nonzero affine `2`-torsion point, the argument is

1. take `g_S ≠ 0` with `u · g_S ^ 2 = [2]∗ f_S` — `exists_gS_two` (`NthRootOfPullback`), whose
   hypothesis `hprin` was the **one gated input** and is discharged over `[IsAlgClosed F]` by
   `#791` (see below);
2. `e_2(S, T) = 1` says exactly `τ_T∗ g_S = g_S` — merged, as
   `weilPairingElt_eq_one_iff_translateEndo_fixed` (`WeilPairingAlternating`, `#465`);
3. so `g_S ∈ Fixed(E[2])`, via `mem_fixedFieldTwo_iff` and `translateAut_apply_some`
   (`TranslationAction`), which is `rfl` onto `translateEndo` — a case split on `W.Point`, no new
   mathematics;
4. `Fixed(E[2]) = [2]∗F(W)` — `fixedFieldTwo_eq_mulByTwoFieldRange` (`MulByTwoGalois`, `#759`),
   **merged**, under `[IsAlgClosed F]` and `(2 : F) ≠ 0`;
5. writing `g_S = [2]∗ h` and cancelling: the unit `u` is a constant
   (`exists_eq_algebraMap_of_isUnit`), `[2]∗` fixes constants (`mulByTwoEndo_algebraMap_base`) and
   is injective, so `c · h ^ 2 = f_S`;
6. hence `2 • divisor W h = single p 2` (`divisor_pow`, `divisor_algebraMap_base`), so
   `divisor W h = single p 1`;
7. which is impossible — `not_exists_divisor_eq_single_pointClosedPoint`
   (`DivisorPrincipality`, `#726`), *a single affine rational point is never a principal divisor*.

**`#E[2] = 4` enters at step 4 and nowhere else**, as the right-hand side of Artin's theorem inside
`finrank_fixedFieldTwo`, whose input is `card_torsionTwoMul` and hence `card_torsion_two` — the
roots of the `2`-division cubic, which does not go through Ward.  Ward (`#254`/`#258`/`#260`/`#261`)
gates `#E[n] = n²` at **general** `n` only, i.e. `#242`/`#251`.  So at `n = 2` the dependency the
old prose named is *discharged*, and what took its place was `hprin`, i.e. rung 5 (`#418`) — for
which see `NthRootOfPullback`.  ⚠️ Its own gate used to be the fibre description of `[2]∗`, `#639`
**rung 9** (`#774`, *not* `#701`, rung 8, which merely counts the fibre).  **Rung 9 is merged**
(`MulByTwoFibreInfinity`, then `MulByTwoFibreAffine`), and the class-group computation that was
then all that remained of it has since been run: ✅ **at `n = 2`, over an algebraically closed base
field, `hprin` is discharged** (`EllipticCurves.FunctionField.PullbackPrincipalityTwo`, `#791`),
which also carries the hypothesis-free rung-5 statement `exists_gS_two_of_isAlgClosed`.
`exists_gS_two` itself is unchanged and keeps `hprin`, because it is the general-field statement and
over an arbitrary `F` the gate is untouched.  At `n = 3` the position is different; see the `n = 3`
account below, which is the only place that says why.

So over `[IsAlgClosed F]` and `[W.IsElliptic]`, **no step of the list above is gated any longer** —
step 7's Dedekind hypothesis included.  ⚠️ That step is **not** something `[IsAlgClosed F]` buys:
`instIsDedekindDomain` (`CoordinateRingNormalGeneral`) supplies it for `[W.IsElliptic]` over any
field, so it is discharged before the algebraically-closed hypothesis is ever used, and it does not
belong on the list of what that hypothesis is needed for.  The assembly that was then all that
stood between the list and a theorem is
`EllipticCurves.FunctionField.WeilPairingNondegenerateTwo` (`#796`); it threads one `g_S` through
every `T`, which is what `weilPairingElt` taking `g_S` as an *argument*
(`weilPairingElt_eq_one_iff_translateEndo_fixed`) makes necessary, and it inherits the hypotheses
the ⚠️ below records.

⚠️ **"Non-degeneracy is proved" is true only at `n = 2` and only over an algebraically closed base
field**, where it is `#796`.  At `n = 3`, and over a general field at either `n`, it is not, and
this section remains an account of what non-degeneracy *consumes* rather than of a theorem.

⚠️ **`#418` has two halves, and only the first one is on this path.**  `hprin`, the hypothesis of
`exists_gS_two`, asks that `divisor W ([2]∗ f)` be `2 •` a principal divisor; it mentions the
pullback of a *function* and no divisor-level `[n]∗` at all, so it is rung-4-independent.  The
other half of `#418`, `div g_S = [n]∗(S)`, does mention the divisor-level pullback, and it is what
the `#456` consumers (`GaloisPointAction`, `WeilPairingGaloisPoint`, `Galois/CyclotomicCharacter`)
mean by "rung 5 (`#418`), gated on `#421`/`#422`".  Both readings are correct about their own
statement; taking either for the other gives the wrong dependency picture, and non-degeneracy needs
only the first.

⚠️ **Step 4 carries `[IsAlgClosed F]`, and so does rung 9's fibre description** — `[W.IsElliptic]`
for the contraction-is-doubling statement, `[IsAlgClosed F]` on top of it for the count, the pinned
indices and the divisor identity — whereas this file carries `[W.IsElliptic]` and **not**
`[IsAlgClosed F]`.  `#791`'s discharge of `hprin` inherits the same hypothesis twice over, from the
fibre description and from the surjectivity of `[2]` on points (`exists_nsmul_two_eq`), which is why
it lands in its own module rather than weakening `exists_gS_two` in place.  "The count is merged"
and "the count is merged in the generality this theorem is stated in" are different claims; the
assembled non-degeneracy statement inherits `[IsAlgClosed F]`, which the `#418`/`#465` consumers
already carry but the `WeilPairing*` files do not — which is why `#796` lands in its own module too.

**At `n = 3` every step of the argument now has an analogue, and the gate is the same gate.**
Steps 1, 2, 5, 6 and 7 transpose (`exists_gS_three`, `mulByThreeEndo_algebraMap_base`), and steps 3
and 4 — which had no analogue at all when this section was first written — are
`mem_fixedFieldThree_iff` and `fixedFieldThree_eq_mulByThreeFieldRange`
(`EllipticCurves.FunctionField.MulByThreeGalois`, `#784`).  Artin's two sides under step 4 are
`finrank_mulByThreeFieldRange` (`MulByThreeDegree`, `#775`, by `#682`'s tower with `4 ↦ 9`) on the
left, and `card_torsionThreeMul` — hence `card_torsion_three`, likewise Ward-free —
(`TranslationActionThree`, `#783`) on the right.  So at `n = 3` too the gate is `hprin`, rung 5
(`#418`) — the **same** gate as at `n = 2`, and the last one left at either `n`.

⚠️ **Same gate, but the two `n` are one rung apart and must not be collapsed into each other.**
At `n = 2` `hprin` is discharged over an algebraically closed base field, rung 9 being merged and
`#791` having run the computation on top of it.  At `n = 3` the fibre description is merged too
(`EllipticCurves.FunctionField.MulByThreeFibre`), so `hprin` there is now in exactly the position
`hprin` at `n = 2` was in before `#791`: what is left is the class-group computation on top of the
fibre description, and nobody has scouted it.  This is the one asymmetry that
survives `#775`/`#783`/`#784`, and it is neither a count nor Artin.

⚠️ The `n = 3` chain carries hypotheses in a shape the `n = 2` account never has to draw:
`finrank_mulByThreeFieldRange` needs `[W.IsElliptic]`, `(2 : F) ≠ 0` and `(3 : F) ≠ 0` but **no**
`[IsAlgClosed F]`, while `card_torsion_three` needs it — so the sandwich, and everything
`MulByThreeGalois` exports off it, carries the union.

## References

* [J. Silverman, *The arithmetic of elliptic curves*][silverman2009], III.8.
-/

namespace WeierstrassCurve.Affine

namespace CoordinateRing

variable {F : Type*} [Field F] {W : Affine F} [W.IsElliptic]

/-- **The Weil-pairing element** `e_n(S, T) := τ_T∗(g_S) / g_S ∈ F(W)`.

Here `g = g_S` is the `n`-th root of the pulled-back principal function of `S` (rung 5) and
`h₂ : W.Equation x₂ y₂` encodes the translation point `T = (x₂, y₂)` via `translateEndo h₂`. -/
noncomputable def weilPairingElt {x₂ y₂ : F} (h₂ : W.Equation x₂ y₂) (g : W.FunctionField) :
    W.FunctionField :=
  translateEndo h₂ g / g

/-- The Weil-pairing element is nonzero whenever `g_S` is (the translation endomorphism is
injective, so `τ_T∗(g_S) ≠ 0`, and the quotient of two nonzero elements is nonzero). -/
theorem weilPairingElt_ne_zero {x₂ y₂ : F} (h₂ : W.Equation x₂ y₂) {g : W.FunctionField}
    (hg : g ≠ 0) : weilPairingElt h₂ g ≠ 0 := by
  have hinj : Function.Injective (translateEndo h₂) := RingHom.injective _
  rw [weilPairingElt]
  exact div_ne_zero ((map_ne_zero_iff _ hinj).mpr hg) hg

/-- **`e_n(S, T)` is an `n`-th root of unity.** Given that the translation fixes `g_S ^ n`
(`translateEndo h₂ (g ^ n) = g ^ n`), the pairing value satisfies `e_n(S, T) ^ n = 1`:
`(τ_T∗ g / g) ^ n = τ_T∗(g ^ n) / g ^ n = g ^ n / g ^ n = 1`. -/
theorem weilPairingElt_pow_eq_one {x₂ y₂ : F} (h₂ : W.Equation x₂ y₂) {g : W.FunctionField}
    (hg : g ≠ 0) {n : ℕ} (hfix : translateEndo h₂ (g ^ n) = g ^ n) :
    weilPairingElt h₂ g ^ n = 1 := by
  rw [weilPairingElt, div_pow, ← map_pow, hfix, div_self (pow_ne_zero n hg)]

/-- **The translation fixes `g_S ^ n`.** From the rung-5 datum `u · g ^ n = h` (with `h = [n]∗ f_S`
the pulled-back principal function and `u` a unit of `F[W]`), together with the two inputs

* `hcomm : translateEndo h₂ h = h` — the commuting identity `[n](P + T) = [n]P`, and
* `huf`   : the translation fixes the constant unit `u`,

the translation fixes `g ^ n`.  Applying `translateEndo h₂` to `u · g ^ n = h` and cancelling the
nonzero factor `algebraMap u` gives `translateEndo h₂ (g ^ n) = g ^ n`. -/
theorem translateEndo_pow_eq_self_of {x₂ y₂ : F} (h₂ : W.Equation x₂ y₂)
    {g h : W.FunctionField} {u : W.CoordinateRingˣ} {n : ℕ}
    (hu : (u : W.CoordinateRing) • g ^ n = h)
    (hcomm : translateEndo h₂ h = h)
    (huf : translateEndo h₂ (algebraMap W.CoordinateRing W.FunctionField (u : W.CoordinateRing))
      = algebraMap W.CoordinateRing W.FunctionField (u : W.CoordinateRing)) :
    translateEndo h₂ (g ^ n) = g ^ n := by
  have hsmul : algebraMap W.CoordinateRing W.FunctionField (u : W.CoordinateRing) * g ^ n = h := by
    rw [← Algebra.smul_def]; exact hu
  have hA : algebraMap W.CoordinateRing W.FunctionField (u : W.CoordinateRing) ≠ 0 := by
    rw [Ne, map_eq_zero_iff _ (IsFractionRing.injective W.CoordinateRing W.FunctionField)]
    exact u.ne_zero
  have key : algebraMap W.CoordinateRing W.FunctionField (u : W.CoordinateRing) *
      translateEndo h₂ (g ^ n) =
      algebraMap W.CoordinateRing W.FunctionField (u : W.CoordinateRing) * g ^ n := by
    have hcong := congrArg (translateEndo h₂) hsmul
    rw [map_mul, huf, hcomm] at hcong
    exact hcong.trans hsmul.symm
  exact mul_left_cancel₀ hA key

/-- **The translation fixes every unit of `F[W]` (`huf` discharged).**  The unit `u` produced by the
rung-5 construction is a unit of the affine coordinate ring, hence a nonzero constant
(`exists_eq_algebraMap_of_isUnit`), and `translateEndo` — being an `F`-algebra homomorphism
(`translateCoordHom_algebraMap`) — fixes constants.  This discharges the `huf` hypothesis of
`translateEndo_pow_eq_self_of` unconditionally, for any unit `u`. -/
theorem translateEndo_algebraMap_unit {x₂ y₂ : F} (h₂ : W.Equation x₂ y₂)
    (u : W.CoordinateRingˣ) :
    translateEndo h₂ (algebraMap W.CoordinateRing W.FunctionField (u : W.CoordinateRing))
      = algebraMap W.CoordinateRing W.FunctionField (u : W.CoordinateRing) := by
  obtain ⟨c, hc⟩ := exists_eq_algebraMap_of_isUnit u.isUnit
  rw [hc, translateEndo_algebraMap, translateCoordHom_algebraMap,
    ← IsScalarTower.algebraMap_apply F W.CoordinateRing W.FunctionField]

/-- **`e_n(S, T) ^ n = 1` from the rung-5 datum and the two named inputs.** Combines
`translateEndo_pow_eq_self_of` (which produces `translateEndo h₂ (g ^ n) = g ^ n`) with
`weilPairingElt_pow_eq_one`.  Here `h = [n]∗ f_S = mulByTwoEndo h2 f` and `g = g_S`. -/
theorem weilPairingElt_pow_eq_one_of_gS {x₂ y₂ : F} (h₂ : W.Equation x₂ y₂) (h2 : (2 : F) ≠ 0)
    {f g : W.FunctionField} {u : W.CoordinateRingˣ} {n : ℕ} (hg : g ≠ 0)
    (hu : (u : W.CoordinateRing) • g ^ n = mulByTwoEndo h2 f)
    (hcomm : translateEndo h₂ (mulByTwoEndo h2 f) = mulByTwoEndo h2 f)
    (huf : translateEndo h₂ (algebraMap W.CoordinateRing W.FunctionField (u : W.CoordinateRing))
      = algebraMap W.CoordinateRing W.FunctionField (u : W.CoordinateRing)) :
    weilPairingElt h₂ g ^ n = 1 :=
  weilPairingElt_pow_eq_one h₂ hg (translateEndo_pow_eq_self_of h₂ hu hcomm huf)

/-- **`e_n(S, T) ^ n = 1`, concrete `n = 3` instance.** The `mulByThreeEndo` analogue of
`weilPairingElt_pow_eq_one_of_gS`: here the pulled-back principal function is
`h = [3]∗ f_S = mulByThreeEndo h2 h3 f` and `g = g_S` is the rung-5 `n = 3` root
(`exists_gS_three`, `u · g ^ 3 = mulByThreeEndo h2 h3 f`).  Nothing in the reduction is specific to
`n = 2`: `translateEndo_pow_eq_self_of` and `weilPairingElt_pow_eq_one` are `n`-agnostic, so the two
named inputs `hcomm`/`huf` are supplied on the `mulByThreeEndo` datum and the same cancellation
produces `e_n(S, T) ^ n = 1`. -/
theorem weilPairingElt_pow_eq_one_of_gS_three {x₂ y₂ : F} (h₂ : W.Equation x₂ y₂) (h2 : (2 : F) ≠ 0)
    (h3 : (3 : F) ≠ 0) {f g : W.FunctionField} {u : W.CoordinateRingˣ} {n : ℕ} (hg : g ≠ 0)
    (hu : (u : W.CoordinateRing) • g ^ n = mulByThreeEndo h2 h3 f)
    (hcomm : translateEndo h₂ (mulByThreeEndo h2 h3 f) = mulByThreeEndo h2 h3 f)
    (huf : translateEndo h₂ (algebraMap W.CoordinateRing W.FunctionField (u : W.CoordinateRing))
      = algebraMap W.CoordinateRing W.FunctionField (u : W.CoordinateRing)) :
    weilPairingElt h₂ g ^ n = 1 :=
  weilPairingElt_pow_eq_one h₂ hg (translateEndo_pow_eq_self_of h₂ hu hcomm huf)

/-- **`e_n(S, T) ^ n = 1` from the rung-5 datum and `hcomm` alone (`n = 2`).**  The `huf` hypothesis
of `weilPairingElt_pow_eq_one_of_gS` is now discharged by `translateEndo_algebraMap_unit` (the unit
`u` is a constant), leaving only the geometric commuting identity `hcomm` (`[n](P + T) = [n]P`). -/
theorem weilPairingElt_pow_eq_one_of_gS' {x₂ y₂ : F} (h₂ : W.Equation x₂ y₂) (h2 : (2 : F) ≠ 0)
    {f g : W.FunctionField} {u : W.CoordinateRingˣ} {n : ℕ} (hg : g ≠ 0)
    (hu : (u : W.CoordinateRing) • g ^ n = mulByTwoEndo h2 f)
    (hcomm : translateEndo h₂ (mulByTwoEndo h2 f) = mulByTwoEndo h2 f) :
    weilPairingElt h₂ g ^ n = 1 :=
  weilPairingElt_pow_eq_one_of_gS h₂ h2 hg hu hcomm (translateEndo_algebraMap_unit h₂ u)

/-- **`e_n(S, T) ^ n = 1` from the rung-5 datum and `hcomm` alone (`n = 3`).**  The `mulByThreeEndo`
analogue of `weilPairingElt_pow_eq_one_of_gS'`; `huf` is discharged by
`translateEndo_algebraMap_unit`, leaving only `hcomm`. -/
theorem weilPairingElt_pow_eq_one_of_gS_three' {x₂ y₂ : F} (h₂ : W.Equation x₂ y₂)
    (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) {f g : W.FunctionField} {u : W.CoordinateRingˣ} {n : ℕ}
    (hg : g ≠ 0) (hu : (u : W.CoordinateRing) • g ^ n = mulByThreeEndo h2 h3 f)
    (hcomm : translateEndo h₂ (mulByThreeEndo h2 h3 f) = mulByThreeEndo h2 h3 f) :
    weilPairingElt h₂ g ^ n = 1 :=
  weilPairingElt_pow_eq_one_of_gS_three h₂ h2 h3 hg hu hcomm (translateEndo_algebraMap_unit h₂ u)

end CoordinateRing

end WeierstrassCurve.Affine
