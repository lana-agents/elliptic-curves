/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import EllipticCurves.FunctionField.FunctionFieldBaseChange
import EllipticCurves.FunctionField.WeilPairing

/-!
# Base change of the Weil-pairing element

Let `W` be a Weierstrass curve over a field `F` and `K` an `F`-algebra which is a field.
`EllipticCurves.FunctionField.FunctionFieldBaseChange` builds the injective base-change map
`functionFieldMap W K : F(W) →+* K(W⁄K)` and intertwines it with the three ring endomorphisms of
`F(W)`.  This file adds the pairing element on top of them:

```
functionFieldMap W K (e_n(S, T)) = e_n(S, T) computed over K
```

and the descent corollaries that follow from injectivity.

## ⚠️ This was priced as part of the divisor half.  It is a one-line `rw`

`FunctionFieldBaseChange`'s `## Remaining work` section used to read

> *"The divisor-level compatibilities — `divisor`, `divisorProj`, **and hence `weilPairingElt`** —
> are not here.  They are not coordinate computations: they need the behaviour of
> `functionFieldMap` on the places of `F(W)`, which is a genuinely different argument."*

The `divisor` / `divisorProj` half of that sentence is correct and stands.  **The
`and hence weilPairingElt` clause was false**, and the reason is visible in the definition
(`EllipticCurves.FunctionField.WeilPairing`):

```lean
noncomputable def weilPairingElt (h₂ : W.Equation x₂ y₂) (g : W.FunctionField) :
    W.FunctionField := translateEndo h₂ g / g
```

`weilPairingElt` is a **quotient of two things that already transport** — it mentions no place, no
order of vanishing and no divisor.  `functionFieldMap` is a ring homomorphism between fields, so
`map_div₀` splits the quotient and `functionFieldMap_translateEndo` handles the numerator.  The
proof of `functionFieldMap_weilPairingElt` below is a single `rw`, and it needs nothing that was not
already merged in `FunctionFieldBaseChange`.

⚠️ **This says nothing whatever about the divisor half.**  `divisor` and `divisorProj` really do
need the action of `functionFieldMap` on the places of `F(W)`; there is no Mathlib `map_*` lemma for
`ord` to lean on the way the endomorphism transports lean on `map_slope` / `map_ψ`; and that work is
untouched here and remains open.  The point of this file is that the pairing element was **never on
that path** — it is the *rung-5 datum* `div g_S = [n]∗(S)` that needs divisors, not `e_n(S, T)`.
Do not read the ease of this file as evidence about the difficulty of that one.

## Why the correction had to land in the source file

The clause had been contradicted in writing three separate times before this file existed — twice in
the issue thread that commissioned `FunctionFieldBaseChange`, and once in
`EllipticCurves.FunctionField.WeilPairingAlternatingBaseChange`, which **imports** it and warns:
*"⚠️ No divisor-level base-change compatibility is used here, and `#692`'s Remaining work section
will lead a reader to expect otherwise."*  ⚠️ A warning in a downstream file only reaches readers
who get to the downstream file.  The reader this mispriced is the one who opens
`FunctionFieldBaseChange` and stops there.

## Main statements

* `functionFieldMap_weilPairingElt` — the intertwining identity, and the whole content of the file.
* `weilPairingElt_baseChange_eq_one_iff` and `weilPairingElt_eq_one_of_baseChange` — `e_n = 1` may
  be checked after base change.
* `weilPairingElt_baseChange_pow_eq_one_iff` and `weilPairingElt_pow_eq_one_of_baseChange` — the
  same for the `n`-th-root-of-unity statement that `weilPairingElt_pow_eq_one` produces.
* `functionFieldMap_weilPairingElt_ne_zero` — the base-changed pairing element is nonzero.

The `_of_baseChange` lemmas are the direction every descent consumer uses: the merged idiom
(`WeilPairingAlternatingBaseChange`) is *push the hypotheses up along `functionFieldMap`, run the
ungated theorem over `K`, pull the conclusion back through `functionFieldMap_injective`*.  They are
supplied by name so that step is not re-derived at each call site.

## Design notes

* **No `[IsAlgClosed K]` and no choice of `K`.**  Every statement is for an arbitrary field
  `K` over `F`.  The instance that matters downstream is `K = AlgebraicClosure F`, but nothing here
  needs it, and fixing `K` would make the file unusable for a finite extension.
* **This file adds a module rather than joining `WeilPairingAlternatingBaseChange`**, which already
  imports both of its parents and would therefore have cost no new module.  Measured over the
  project's own `import` lines at `008fea7`: this file's `EllipticCurves`-import closure is **12**
  (`FunctionFieldBaseChange` 9, `WeilPairing` 10, sharing 9), against **76** for
  `WeilPairingAlternatingBaseChange`.  A consumer that wants only the pairing-element transport
  should not pay the alternating property's closure for it.
* **Nothing here removes an `[IsAlgClosed F]`.**  The alternating property already descended, in
  `WeilPairingAlternatingBaseChange`, and it did so without this lemma.  `hprin` is an *existence*
  statement; base change carries conclusions down, not hypotheses up.

## Non-vacuity

Not applicable in the usual sense: these are intertwining identities and `iff`s between statements
that exist for every `[Algebra F K]`, not existence claims, so there is no hypothesis set that could
be empty.  The merged `functionFieldMap_translateEndo` beside them carries no certificate either,
for the same reason.

## References

* [J. Silverman, *The arithmetic of elliptic curves*][silverman2009], III.8 (the Weil pairing).
-/

namespace WeierstrassCurve.Affine

namespace CoordinateRing

variable {F : Type*} [Field F] {W : Affine F} (K : Type*) [Field K] [Algebra F K]
variable [W.IsElliptic] {x₂ y₂ : F}

/-- **Base change intertwines the Weil-pairing element.**  `e_n(S, T) = τ_T∗(g_S) / g_S` is a
quotient of two things `EllipticCurves.FunctionField.FunctionFieldBaseChange` already transports, so
`map_div₀` and `functionFieldMap_translateEndo` are the whole proof.  The translation point moves
along `F → K` as `h₂.map (algebraMap F K)`. -/
theorem functionFieldMap_weilPairingElt (h₂ : W.Equation x₂ y₂) (g : W.FunctionField) :
    functionFieldMap W K (weilPairingElt h₂ g)
      = weilPairingElt (h₂.map (algebraMap F K)) (functionFieldMap W K g) := by
  rw [weilPairingElt, weilPairingElt, map_div₀, functionFieldMap_translateEndo]

/-- **`e_n(S, T) = 1` may be checked after base change.**  Both directions, since `functionFieldMap`
is injective. -/
theorem weilPairingElt_baseChange_eq_one_iff (h₂ : W.Equation x₂ y₂) (g : W.FunctionField) :
    weilPairingElt (h₂.map (algebraMap F K)) (functionFieldMap W K g) = 1
      ↔ weilPairingElt h₂ g = 1 := by
  rw [← functionFieldMap_weilPairingElt K h₂ g, ← map_one (functionFieldMap W K)]
  exact (functionFieldMap_injective W K).eq_iff

/-- The descent direction of `weilPairingElt_baseChange_eq_one_iff`, named for the call sites: prove
`e_n(S, T) = 1` over `K`, conclude it over `F`. -/
theorem weilPairingElt_eq_one_of_baseChange (h₂ : W.Equation x₂ y₂) {g : W.FunctionField}
    (h : weilPairingElt (h₂.map (algebraMap F K)) (functionFieldMap W K g) = 1) :
    weilPairingElt h₂ g = 1 :=
  (weilPairingElt_baseChange_eq_one_iff K h₂ g).mp h

/-- **`e_n(S, T) ^ n = 1` may be checked after base change.**  This is the shape
`weilPairingElt_pow_eq_one` produces, so it is the one a root-of-unity consumer wants. -/
theorem weilPairingElt_baseChange_pow_eq_one_iff (h₂ : W.Equation x₂ y₂) (g : W.FunctionField)
    (n : ℕ) :
    weilPairingElt (h₂.map (algebraMap F K)) (functionFieldMap W K g) ^ n = 1
      ↔ weilPairingElt h₂ g ^ n = 1 := by
  rw [← functionFieldMap_weilPairingElt K h₂ g, ← map_pow, ← map_one (functionFieldMap W K)]
  exact (functionFieldMap_injective W K).eq_iff

/-- The descent direction of `weilPairingElt_baseChange_pow_eq_one_iff`. -/
theorem weilPairingElt_pow_eq_one_of_baseChange (h₂ : W.Equation x₂ y₂) {g : W.FunctionField}
    {n : ℕ} (h : weilPairingElt (h₂.map (algebraMap F K)) (functionFieldMap W K g) ^ n = 1) :
    weilPairingElt h₂ g ^ n = 1 :=
  (weilPairingElt_baseChange_pow_eq_one_iff K h₂ g n).mp h

/-- The base-changed pairing element is nonzero whenever `g_S` is: base change is injective, so it
does not kill `g_S`, and `weilPairingElt_ne_zero` applies over `K`. -/
theorem functionFieldMap_weilPairingElt_ne_zero (h₂ : W.Equation x₂ y₂) {g : W.FunctionField}
    (hg : g ≠ 0) : weilPairingElt (h₂.map (algebraMap F K)) (functionFieldMap W K g) ≠ 0 :=
  weilPairingElt_ne_zero _ ((map_ne_zero_iff _ (functionFieldMap_injective W K)).mpr hg)

end CoordinateRing

end WeierstrassCurve.Affine
