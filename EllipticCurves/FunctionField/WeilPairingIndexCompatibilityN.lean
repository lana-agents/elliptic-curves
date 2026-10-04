/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import EllipticCurves.Fixtures
import EllipticCurves.FunctionField.WeilPairingFunctionN

/-!
# Index compatibility of the Weil pairing

Silverman AEC III.8.1(e), the last of the five properties `#244` asks of `e_n` after the
construction: a pairing value at a *product* index is a pairing value at a *factor* index, once one
of the two points is pushed down by the cofactor.

```
e_{n · n'}(S, T) = e_n(S, [n']T)      for S ∈ E[n] and T ∈ E[n · n'].
```

⚠️ **Which slot carries the `[n']` is a consequence of this tree's argument order and not a
choice.** Silverman writes the pairing with the *translation* point first and the *divisor* point
second, and states (e) as `e_{nn'}(P, Q) = e_n([n']P, Q)` with `Q ∈ E[n]` — so the `[n']` sits on
his translation slot. `weilPairingEltN` is the transpose: its **first** argument is the divisor
point, the one at which the rung-5 root `g_S` is taken (`weilPairingEltN` is
`weilPairingPointElt (weilPairingRootN h2 hn S) T`, and `weilPairingRootN` pins
`div f = n · (S)`), and its **second** argument is the translation point. ⚠️⚠️ **So the form that
comes out of the argument directly is the one with `[n']` on the RIGHT, and the shape that
transcribes Silverman's own left-hand `[n']` literally is the mirror image** — proved below as
`weilPairingEltN_mul_index_nsmul_left`, out of the direct form and `weilPairingEltN_swap` at the
two indices, and so a corollary rather than a second argument.

## The argument, in one paragraph

Everything rests on transporting the rung-5 datum **up** the index rather than down. If `g` is a
rung-5 root at `S` for the index `n` — `div f = n · (S)` and `u • g ^ n = [n]∗f` — then
`[n']∗g` is a rung-5 root at the same `S` for the index `n · n'`, with `f ^ n'` for `f`:
`div (f ^ n') = n' · (n · (S)) = (n · n') · (S)` is divisor arithmetic, and
```
[n · n']∗(f ^ n') = ([n']∗([n]∗f)) ^ n' = ([n']∗(u • g ^ n)) ^ n'
                  = ([n']∗u) ^ n' · ([n']∗g) ^ (n · n')
```
is the composition law `[n · n']∗ = [n']∗ ∘ [n]∗` (`mulByNEndo_mul`). ⚠️ **The unit is where this
could have failed**: `[n']∗` does **not** preserve `F[W]` — it sends `genX` to the `x`-coordinate of
`n' • 𝒫`, a rational function — so `[n']∗u` is not a unit of `F[W]` for any formal reason. What
saves it is that there is nothing to preserve: `exists_eq_algebraMap_of_isUnit`
(`CoordinateRingUnits`) says every unit of `F[W]` is a **constant**, and `[n']∗` fixes constants
(`mulByNEndo_algebraMap_base`). That is the one input of this file that is not pullback formalism.

With the transported root in hand, `weilPairingEltN_eq` reads the left-hand value off it and the
rest is the commutation `τ_T ∘ [n']∗ = [n']∗ ∘ τ_{[n']T}` (`translateAut_mulByNEndo_nsmul` below,
the `W.Point`-level form of `TranslationMulByNCommGeneral`'s two-affine-point statement) together
with the fact that the right-hand value is a **constant** of `F`, so that `[n']∗` leaves it alone
and it cancels out of the quotient. The constancy is not an extra hypothesis: it is
`algebraMap_coe_weilPairingN`, the defining property of the `μ_n(F)`-valued form.

## The three rulings this file makes

1. **Which slot the `[n']` sits on.** Settled above: the right slot is the direct statement, the
   left slot is a corollary via `weilPairingEltN_swap`. Both are proved.
2. ⚠️ **`hnn'` is a binder and it is also derivable.** `intCast_natCast_mul_ne_zero` below derives
   `(((n * n') : ℤ) : F) ≠ 0` from `hn` and `hn'`, so the hypothesis costs a caller nothing. It is
   nonetheless a binder rather than that term inlined, because the statement is *about*
   `weilPairingEltN` at the index `n * n'` and a caller rewrites with it at whichever proof it
   already holds — the same reason `mulByNEndoAlgHom_mul` takes `hmn` rather than building
   `transcendental_xCoord_mul_nsmul hm hn`. ⚠️ This is the *forced*-rather-than-*preferred*
   distinction `#2266` ruled on, and it cuts this way here only because the derivation is supplied
   beside the theorem; a redundant binder with no supplied discharge would not be.
3. ⚠️ **The `μ_n(F)`-valued form is given in `F`, not in `rootsOfUnity`.**
   `coe_weilPairingN_mul_index_nsmul_right` equates the two values **as elements of `F`**, which is
   free from the `F(W)` statement by injectivity of `algebraMap F F(W)`. ⚠️⚠️ **The group-valued
   form is deliberately NOT here**: `rootsOfUnity (n * n') F` and `rootsOfUnity n F` are different
   groups, so it is not a transport but an identity along the inclusion `μ_n ↪ μ_{n·n'}`, which
   this tree does not carry. The `F`-valued form says exactly as much about the two numbers and
   needs nothing new.

## Scope

Taken from `#244`'s list and nothing else. `[IsAlgClosed F]` and `(2 : F) ≠ 0` enter only because
`weilPairingEltN` is a function at all only there (the root is an `Exists.choose` over
`exists_isWeilRootN`); ⚠️ **no principality hypothesis appears, and none is discharged** — `#962`
owns that front and `weilPairingEltN` has already consumed it.

## References

* [J. Silverman, *The arithmetic of elliptic curves*][silverman2009], III.8.1(e).
-/

open Polynomial

/-- The index condition at a product, out of the index conditions at the two factors. ⚠️ This is
what makes `hnn'` below a convenience binder rather than a strengthening: see the module docstring's
ruling 2.

A statement about a field and nothing else; it belongs beside `mul_ne_zero`, and it is declared
OUTSIDE `namespace WeierstrassCurve.Affine` for that reason — the shape
`natCard_rootsOfUnity_of_intCast_ne_zero` takes in `WeilPairingFunctionGaloisN`. -/
lemma intCast_natCast_mul_ne_zero {F : Type*} [Field F] {n n' : ℕ}
    (hn : ((n : ℤ) : F) ≠ 0) (hn' : ((n' : ℤ) : F) ≠ 0) :
    (((n * n' : ℕ) : ℤ) : F) ≠ 0 := by
  push_cast at hn hn' ⊢
  exact mul_ne_zero hn hn'

namespace WeierstrassCurve.Affine

open CoordinateRing

variable {F : Type*} [Field F] {W : Affine F}

/-! ### Two arithmetic conveniences -/

open Classical in
/-- **The cofactor multiple of an `n · n'`-torsion point is `n`-torsion**: `n • (n' • P)` is
`(n · n') • P`.

⚠️ It belongs in `Torsion/Defs.lean`, beside `torsion_mono` — the lemma it is used next to in both
statements below — and in its home the `open Classical in` disappears, that file binding
`[DecidableEq F]` already. -/
lemma nsmul_mem_torsion_of_mem_torsion_mul {n n' : ℕ} {P : W.Point}
    (hP : P ∈ W.torsion (n * n')) : n' • P ∈ W.torsion n :=
  mem_torsion_iff.mpr (by rw [smul_smul, mem_torsion_iff.mp hP])

variable [W.IsElliptic]

/-! ### The composition law at a stated product -/

/-- **`[k]∗ = [m]∗ ∘ [n]∗` at a stated product `m · n = k`, in applied form.**  The `mulByNEndo`
companion of `transcendental_xCoord_nsmul_of_mul_eq`, and wanted for the same reason: the index this
file needs the law at is `n * n'` while the law produces it as `n' * n`, and a caller holding `k` as
a literal should not have to transport along an arithmetic identity.

⚠️ It belongs in `MulByNComposition.lean`, beside `mulByNEndo_mul` and
`transcendental_xCoord_nsmul_of_mul_eq`. -/
theorem mulByNEndo_apply_mul_of_mul_eq {m n k : ℕ} (hk : m * n = k)
    (hm : Transcendental F (m • genericPoint (W := W)).xCoord)
    (hn : Transcendental F (n • genericPoint (W := W)).xCoord)
    (hkt : Transcendental F (k • genericPoint (W := W)).xCoord) (z : W.FunctionField) :
    mulByNEndo k hkt z = mulByNEndo m hm (mulByNEndo n hn z) := by
  subst hk
  rw [mulByNEndo_mul hm hn hkt]
  rfl

/-! ### Translation past `[n]∗`, at a point of `W` -/

open Classical in
/-- **`τ_P ∘ [n]∗ = [n]∗ ∘ τ_{[n]P}` for every `P : W.Point`.**

`TranslationMulByNCommGeneral` states this for **two affine points** `P`, `T` with `[n]P = T`
(`translateEndo_mulByNEndo_apply_of_baseField`), and separately for an affine `n`-torsion `P`, where
the target is the point at infinity and the composite collapses (`translateAut_mulByNEndo`).  ⚠️
Those are the two halves of this statement and neither subsumes the other: `[n]P` is affine in one
and `O` in the other, and `O` is not a value `hT` can take.  Assembling them at the level of
`W.Point` — where `translateAut` is total — is what lets a caller apply the commutation without
knowing whether `[n]P` vanishes, which is exactly the position the index-compatibility proof is in.

⚠️ The third case, `P = O`, is not a case of either: `[n]O = O` and both sides are `[n]∗f`.

⚠️ It belongs in `TranslationMulByNCommGeneral`, which is where both of its ingredients live. -/
theorem translateAut_mulByNEndo_nsmul (n : ℕ)
    (hn : Transcendental F (n • genericPoint (W := W)).xCoord) (P : W.Point)
    (f : W.FunctionField) :
    translateAut P (mulByNEndo n hn f) = mulByNEndo n hn (translateAut (n • P) f) := by
  rcases P with _ | ⟨x, y, h⟩
  · rw [← Point.zero_def, smul_zero, translateAut_zero, AlgEquiv.one_apply, AlgEquiv.one_apply]
  · rcases hQ : (n • Point.some x y h : W.Point) with _ | ⟨x', y', h'⟩
    · rw [← Point.zero_def, translateAut_zero, AlgEquiv.one_apply]
      exact translateAut_mulByNEndo n hn (mem_torsion_iff.mpr hQ) f
    · rw [translateAut_apply_some, translateAut_apply_some]
      exact translateEndo_mulByNEndo_apply_of_baseField h.left h'.left n hn hQ f

/-! ### The rung-5 datum, transported up the index -/

open Classical in
/-- **A rung-5 root at `S` for the index `n` pulls back to one for the index `n · n'`.**  The whole
content of this file: `[n']∗g` is a rung-5 root at the *same* point `S`, with `f ^ n'` for the
divisor witness.

⚠️ The unit is the only step that is not formal — see the module docstring. -/
theorem isWeilRootN_mulByNEndo {n n' : ℕ}
    (hn : Transcendental F (n • genericPoint (W := W)).xCoord)
    (hn' : Transcendental F (n' • genericPoint (W := W)).xCoord)
    (hnn' : Transcendental F ((n * n') • genericPoint (W := W)).xCoord)
    {S : W.Point} {g : W.FunctionField} (hg : IsWeilRootN n hn S g) :
    IsWeilRootN (n * n') hnn' S (mulByNEndo n' hn' g) := by
  obtain ⟨hg0, f, hf, hd, u, hu⟩ := hg
  obtain ⟨c, hcu⟩ := CoordinateRing.exists_eq_algebraMap_of_isUnit u.isUnit
  -- `u` is a constant, and that constant is what the pullback of the unit becomes.
  have hcF : (u : W.CoordinateRing) • g ^ n = algebraMap F W.FunctionField c * g ^ n := by
    rw [hcu, Algebra.smul_def, ← IsScalarTower.algebraMap_apply F W.CoordinateRing W.FunctionField]
  refine ⟨(map_ne_zero_iff _ (mulByNEndo_injective n' hn')).mpr hg0, f ^ n', pow_ne_zero _ hf,
    ?_, u ^ n', ?_⟩
  · rw [divisor_pow, hd, ← Nat.cast_smul_eq_nsmul ℤ, smul_smul]
    congr 1
    push_cast
    ring
  · rw [map_pow, mulByNEndo_apply_mul_of_mul_eq (mul_comm n' n) hn' hn hnn', ← hu, hcF, map_mul,
      mulByNEndo_algebraMap_base, map_pow, mul_pow, ← pow_mul, Units.val_pow_eq_pow_val, hcu,
      Algebra.smul_def, map_pow,
      ← IsScalarTower.algebraMap_apply F W.CoordinateRing W.FunctionField]

/-! ### Index compatibility -/

open Classical in
/-- **Silverman III.8.1(e)**, in the slot order `weilPairingEltN` is written in:

```
e_{n · n'}(S, T) = e_n(S, [n']T)      S ∈ E[n] ≤ E[n · n'],  T ∈ E[n · n'].
```

The `[n']` is on the **translation** slot, which is positionally where Silverman writes his divisor
point — ⚠️ the cofactor's ROLE is the translation role in both and only the POSITION moves. See the
module docstring, and `weilPairingEltN_mul_index_nsmul_left` for the mirror image. -/
theorem weilPairingEltN_mul_index_nsmul_right [IsAlgClosed F] (h2 : (2 : F) ≠ 0) {n n' : ℕ}
    (hn : ((n : ℤ) : F) ≠ 0) (hn' : ((n' : ℤ) : F) ≠ 0) (hnn' : (((n * n' : ℕ) : ℤ) : F) ≠ 0)
    (S : W.torsion n) (T : W.torsion (n * n')) :
    weilPairingEltN h2 hnn' ⟨(S : W.Point), torsion_mono (dvd_mul_right n n') S.2⟩ T
      = weilPairingEltN h2 hn S ⟨n' • (T : W.Point), nsmul_mem_torsion_of_mem_torsion_mul T.2⟩ := by
  have hnt : Transcendental F (n • genericPoint (W := W)).xCoord :=
    transcendental_xCoord_nsmul_genericPoint_of_intCast_ne_zero h2 hn
  have hn't : Transcendental F (n' • genericPoint (W := W)).xCoord :=
    transcendental_xCoord_nsmul_genericPoint_of_intCast_ne_zero h2 hn'
  have hmt : Transcendental F ((n * n') • genericPoint (W := W)).xCoord :=
    transcendental_xCoord_nsmul_genericPoint_of_intCast_ne_zero h2 hnn'
  have hg : IsWeilRootN n hnt (S : W.Point) (weilPairingRootN h2 hn S) :=
    isWeilRootN_weilPairingRootN h2 hn S
  -- the SAME root, read as a rung-5 root at the lifted point for the index `n * n'`
  have hG : IsWeilRootN (n * n') hmt
      ((⟨(S : W.Point), torsion_mono (dvd_mul_right n n') S.2⟩ : W.torsion (n * n')) : W.Point)
      (mulByNEndo n' hn't (weilPairingRootN h2 hn S)) :=
    isWeilRootN_mulByNEndo hnt hn't hmt hg
  have hg0 : weilPairingRootN h2 hn S ≠ 0 := hg.ne_zero
  have hG0 : mulByNEndo n' hn't (weilPairingRootN h2 hn S) ≠ 0 :=
    (map_ne_zero_iff _ (mulByNEndo_injective n' hn't)).mpr hg0
  -- The right-hand value is a constant of `F`: that is what `weilPairingN` is for.
  obtain ⟨c, hc⟩ : ∃ c : F, weilPairingEltN h2 hn S
      ⟨n' • (T : W.Point), nsmul_mem_torsion_of_mem_torsion_mul T.2⟩
        = algebraMap F W.FunctionField c :=
    ⟨_, (algebraMap_coe_weilPairingN h2 hn S _).symm⟩
  -- …so the chosen root at `S` satisfies `τ_{[n']T} g_S = c · g_S`.
  have hτ : translateAut (n' • (T : W.Point)) (weilPairingRootN h2 hn S)
      = algebraMap F W.FunctionField c * weilPairingRootN h2 hn S := by
    rw [← weilPairingPointElt_mul_self hg0 (n' • (T : W.Point))]
    exact congrArg (· * weilPairingRootN h2 hn S) hc
  rw [weilPairingEltN_eq h2 hnn' hG T, hc,
    weilPairingPointElt, translateAut_mulByNEndo_nsmul n' hn't (T : W.Point)
      (weilPairingRootN h2 hn S), hτ, map_mul, mulByNEndo_algebraMap_base, mul_div_assoc,
    div_self hG0, mul_one]

open Classical in
/-- **Silverman III.8.1(e) with the `[n']` on the divisor slot**, which is the shape his own
statement has:

```
e_{n · n'}(S, T) = e_n([n']S, T)      S ∈ E[n · n'],  T ∈ E[n] ≤ E[n · n'].
```

⚠️ A corollary of `weilPairingEltN_mul_index_nsmul_right` and antisymmetry
(`weilPairingEltN_swap`) **at both indices**, not a second argument: the two swaps cancel. -/
theorem weilPairingEltN_mul_index_nsmul_left [IsAlgClosed F] (h2 : (2 : F) ≠ 0) {n n' : ℕ}
    (hn : ((n : ℤ) : F) ≠ 0) (hn' : ((n' : ℤ) : F) ≠ 0) (hnn' : (((n * n' : ℕ) : ℤ) : F) ≠ 0)
    (S : W.torsion (n * n')) (T : W.torsion n) :
    weilPairingEltN h2 hnn' S ⟨(T : W.Point), torsion_mono (dvd_mul_right n n') T.2⟩
      = weilPairingEltN h2 hn ⟨n' • (S : W.Point), nsmul_mem_torsion_of_mem_torsion_mul S.2⟩ T := by
  rw [weilPairingEltN_swap h2 hnn' ⟨(T : W.Point), torsion_mono (dvd_mul_right n n') T.2⟩ S,
    weilPairingEltN_mul_index_nsmul_right h2 hn hn' hnn' T S,
    weilPairingEltN_swap h2 hn ⟨n' • (S : W.Point), nsmul_mem_torsion_of_mem_torsion_mul S.2⟩ T,
    inv_inv]

open Classical in
/-- **Index compatibility of the `μ`-valued pairing, read in `F`.**  The two values live in the
*different* groups `rootsOfUnity (n * n') F` and `rootsOfUnity n F`, so there is no equation
between them to state; what there is, is an equation between the two elements of `F` they name, and
it is free from the `F(W)` form by injectivity of `algebraMap F F(W)`.  See the module docstring's
ruling 3. -/
theorem coe_weilPairingN_mul_index_nsmul_right [IsAlgClosed F] (h2 : (2 : F) ≠ 0) {n n' : ℕ}
    (hn : ((n : ℤ) : F) ≠ 0) (hn' : ((n' : ℤ) : F) ≠ 0) (hnn' : (((n * n' : ℕ) : ℤ) : F) ≠ 0)
    (S : W.torsion n) (T : W.torsion (n * n')) :
    ((weilPairingN h2 hnn' ⟨(S : W.Point), torsion_mono (dvd_mul_right n n') S.2⟩ T : Fˣ) : F)
      = ((weilPairingN h2 hn S
          ⟨n' • (T : W.Point), nsmul_mem_torsion_of_mem_torsion_mul T.2⟩ : Fˣ) : F) :=
  (algebraMap F W.FunctionField).injective <| by
    rw [algebraMap_coe_weilPairingN, algebraMap_coe_weilPairingN,
      weilPairingEltN_mul_index_nsmul_right h2 hn hn' hnn' S T]

/-! ### Non-vacuity -/

section Nonvacuity

open EllipticCurves.Fixture

private lemma exampleTwo : (2 : AlgClosedQ) ≠ 0 := two_ne_zero

/-- The index condition at `n = 2` over a field of characteristic `0`. -/
private lemma exampleIndexTwo : (((2 : ℕ) : ℤ) : AlgClosedQ) ≠ 0 := by norm_num

/-- The index condition at the product `2 · 2`, in the shape the theorem binds it. -/
private lemma exampleIndexFour : (((2 * 2 : ℕ) : ℤ) : AlgClosedQ) ≠ 0 := by norm_num

open Classical in
/-- **Index compatibility on a curve that exists**, at `n = n' = 2` on `y² = x³ − x` over `ℚ̄`: the
pairing at the index `4` is the pairing at the index `2` against the double of the translation
point.  ⚠️ All three index hypotheses are discharged by `norm_num`, so nothing here is schematic. -/
example (S : (y2EqX3SubX AlgClosedQ).torsion 2) (T : (y2EqX3SubX AlgClosedQ).torsion (2 * 2)) :
    weilPairingEltN exampleTwo exampleIndexFour
        ⟨(S : (y2EqX3SubX AlgClosedQ).Point), torsion_mono (dvd_mul_right 2 2) S.2⟩ T
      = weilPairingEltN exampleTwo exampleIndexTwo S
          ⟨2 • (T : (y2EqX3SubX AlgClosedQ).Point),
            nsmul_mem_torsion_of_mem_torsion_mul T.2⟩ :=
  weilPairingEltN_mul_index_nsmul_right exampleTwo exampleIndexTwo exampleIndexTwo
    exampleIndexFour S T

end Nonvacuity

end WeierstrassCurve.Affine
