/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import EllipticCurves.FunctionField.WeilPairing

/-!
# The alternating property `e_n(T, T) = 1` — the reduction (Weil-pairing rung 6)

For the divisor-theoretic Weil-pairing element `e_n(S, T) := τ_T∗(g_S) / g_S ∈ F(W)`
(`weilPairingElt`, issue #419) the third named structural property (Silverman AEC III.8.1(d)) is
that it is **alternating**:

```
weilPairingElt_self : e_n(T, T) = 1.
```

Here the two arguments coincide: the divisor-slot function is `g_T` (the rung-5 `n`-th root attached
to `T`) and the translation is `τ_T∗ = translateEndo h_T` for the *same* point `T`.  Written out,
`e_n(T, T) = τ_T∗(g_T) / g_T`, so the claim is *exactly* that translation by `T` fixes `g_T` on the
nose:

```
τ_T∗ g_T = g_T   ⟺   e_n(T, T) = 1.
```

This file delivers the **Ward- and normality-independent reduction** of the alternating property to
that single translation-invariance fact:

* `weilPairingElt_eq_one_iff_translateEndo_fixed` — the clean characterisation
  `e_n(T, T) = 1 ↔ τ_T∗ g_T = g_T` (for `g_T ≠ 0`);
* `weilPairingElt_self_of_translateEndo_fixed`     — its forward direction, the reduction
  `τ_T∗ g_T = g_T ⟹ e_n(T, T) = 1`.

## Why the remaining content is genuinely gated

Being an `n`-th root of unity — `e_n(T, T) ^ n = 1`, already available from
`weilPairingElt_pow_eq_one` (#156) — is *not* enough to force `e_n(T, T) = 1`.  Pinning the ratio to
exactly `1` is the classical **product-over-`⟨T⟩`** argument (Silverman AEC III.8.1(d)), and it
runs in **two** products, over two *different* translation points:

1. **The divisor telescoping, on `f_T`.**  From `div f_T = n(T) − n(O)` one gets
   `div (f_T ∘ τ_{[i]T}) = n((1 − i)T) − n((−i)T)`, and summing over `i = 0, …, n − 1` the two
   multisets `{(1 − i)T}` and `{(−i)T}` are both all of `⟨T⟩`.  So `c := ∏_i f_T ∘ τ_{[i]T}` has
   divisor `0` and is a nonzero constant.
2. **The function-level telescoping, on `g_T`, translating by a point `P` with `[n]P = T`.**  Since
   `[n] ∘ τ_{[i]P} = τ_{[i]T} ∘ [n]`, raising to the `n`-th power turns the second product into the
   first: `(∏_i g_T ∘ τ_{[i]P}) ^ n = c ∘ [n] = c`, so `h := ∏_i g_T ∘ τ_{[i]P}` is itself
   constant.  Then `h ∘ τ_P = h · (g_T ∘ τ_{[n]P}) / g_T`, and `h` constant forces `τ_T∗ g_T = g_T`.

⚠️ The product in step 2 is over translations by `P`, **not** by `[i]T`, and that is not a
presentational choice.  Because `T` is `n`-torsion, `[n] ∘ τ_{[i]T} = [n]`, so *every* divisor of
the form `[n]∗D` is fixed by the translation permutation; `div g_T = [n]∗((T) − (O))` is of that
form, each `τ_{[i]T}∗ g_T` therefore has the **same** divisor as `g_T`, and
`div (∏_i τ_{[i]T}∗ g_T) = n · div g_T ≠ 0`.  There is no cancellation to be had in that product.

That discharge of the `htinv : τ_T∗ g_T = g_T` hypothesis is the substantial, gated part of the
alternating property (issue #465, deliverable 2).  It runs on the divisor / order-of-vanishing
calculus of `F(W)` (conditional on `IsDedekindDomain W.CoordinateRing`, #396) and on the rung-5
divisor identity `div g_T = [n]∗(T)` (#418, rung-4 gated).  It also needs a
divisor-pullback-under-translation formula, and **that formula is now in `FunctionField/`**:

* `divisorProj_translateEndo` (`EllipticCurves.FunctionField.PlaceOrder`, #658) —
  `divisorProj W (translateEndo h_T f) = (divisorProj W f).mapDomain (mapProjPoint W
  (translateAlgEquiv h_T))`, the pullback itself.  Note it is the **projective** divisor
  `divisorProj` that transports; the affine `divisor W` does not, because `τ_T` moves the points
  at infinity;
* the permutation it pushes forward along is identified on the rational locus by
  `mapProjPoint_translateAlgEquiv_none` and `mapProjPoint_translateAlgEquiv_pointClosedPoint`
  (`EllipticCurves.FunctionField.TranslationPlaceAtInfinity`, #660) at the point at infinity and
  at the closed point of `T`, and by `mapProjPoint_translateAlgEquiv_pointClosedPoint_affine`
  (`EllipticCurves.FunctionField.TranslationProjAction`, #663) at every affine `F`-point, where it
  is `P ↦ P ⊖ T`.

So the indexing is **not** what is left to do, and `#418` is **not** the only gate.  Sorting the
two products against the tree:

* **Step 1 is ungated today.**  Its divisor input is `div f_T = n(T) − n(O)`, the merged
  `divisorProj_eq_single_sub_single_of_torsion` (`EllipticCurves.FunctionField.ProjectiveDivisor`),
  pushed forward along the permutation just listed and summed (`divisorProj_prod`, same file).
  Every point occurring in it lies in `⟨T⟩`, hence is `F`-rational — which is exactly the locus on
  which #658/#660/#663 identify the permutation, and the reason indexing this product needs nothing
  new.
* **Step 2 carries both remaining gates.**  It needs `div g_T = [n]∗(T)` (#418, rung-4 gated),
  which is still missing; and it translates by a point `P` with `[n]P = T`, which is **not
  `F`-rational in general**.  `translateEndo` is built from `h₂ : W.Equation x₂ y₂` with
  `x₂ y₂ : F` (`EllipticCurves.FunctionField.TranslationEndomorphism`), so over a general `F` it
  cannot express `τ_P` at all.

  ⚠️ Over an algebraically closed field that second obstruction is **not** real, and the record
  above overstated it.  There `P` is rational — `nsmul_two_surjective`
  (`EllipticCurves.Torsion.DoublingSurjective`) and `nsmul_three_surjective`
  (`EllipticCurves.Torsion.TriplingSurjective`), both needing only `(2 : F) ≠ 0` — so
  `translateEndo` expresses `τ_P` unchanged.  That is how
  `EllipticCurves.FunctionField.WeilPairingAlternatingTwo` closed #465 deliverable 2 at `n = 2`,
  using neither a base change nor a translation along a non-rational point.  What is left is
  descending an `F̄`-statement to a general `F`, which is the function-field base-change layer
  (deferred, #692), and #418 itself.

This file supplies the ungated scaffolding both halves plug into.

## Out of scope

* **Discharging `τ_T∗ g_T = g_T`** — the product-over-`⟨T⟩` argument (#465 deliverable 2), gated as
  above.
* **Antisymmetry `e_n(T, S) = e_n(S, T)⁻¹`** — merged, as `WeilPairingAntisymmetric` (`#723`),
  together with the divisor-slot bilinearity it runs on; both need `[Field F]` and `[W.IsElliptic]`
  and nothing else.  What stays gated there is only the *production* of the product relation
  `g_{S ⊕ T} = g_S · g_T · w`, carried as the hypothesis `hprod`.  ⚠️ That production is **rung 5
  only and never rung 4**, and is performed in
  `EllipticCurves.FunctionField.WeilPairingProductRelation` (`#845`).
  ⚠️ This bullet used to say two wrong things, both worth naming.  First, the divisor slot is not
  rung-4 gated as a *consumer*: `e_n(·, T)` is multiplicative in it on the nose, and the correction
  factor `w` contributes `1`.  Second, antisymmetry does not "expand `e_n(S ⊕ T, S ⊕ T) = 1`".  The
  alternating property is an **input at three points**, `S`, `T` and `S ⊕ T`, and
  `e_n(S ⊕ T, S ⊕ T) = 1` is a *hypothesis* of the derivation, not a conclusion of it: antisymmetry
  consumes the alternating property and proves it nowhere.  Reading it as one instance of the
  alternating property being unfolded invites exactly the wrong dependency picture.
* **Non-degeneracy** — out of scope, and **not** Ward-gated.  `WeilPairing`'s scope section is the
  canonical account of what it consumes (`#769`).

## References

* [J. Silverman, *The arithmetic of elliptic curves*][silverman2009], III.8.
-/

namespace WeierstrassCurve.Affine

namespace CoordinateRing

variable {F : Type*} [Field F] {W : Affine F} [W.IsElliptic]

/-- **The alternating property is exactly translation-invariance of `g_T`.**  For `g_T ≠ 0` the
Weil-pairing element `e_n(T, T) = τ_T∗(g_T) / g_T` equals `1` if and only if the translation `τ_T∗`
fixes `g_T`:

```
weilPairingElt h₂ g = 1 ↔ translateEndo h₂ g = g.
```

This is the Ward- and normality-independent reduction of the alternating property to the single
geometric fact `τ_T∗ g_T = g_T`; the latter is discharged by the product-over-`⟨T⟩` /
divisor-telescoping argument (#465 deliverable 2), which is gated on the divisor calculus. -/
theorem weilPairingElt_eq_one_iff_translateEndo_fixed {x₂ y₂ : F} (h₂ : W.Equation x₂ y₂)
    {g : W.FunctionField} (hg : g ≠ 0) :
    weilPairingElt h₂ g = 1 ↔ translateEndo h₂ g = g := by
  rw [weilPairingElt, div_eq_iff hg, one_mul]

/-- **The alternating property from translation-invariance (`e_n(T, T) = 1`).**  If the translation
`τ_T∗` fixes the rung-5 root `g_T` (`htinv : translateEndo h₂ g = g`), then the Weil-pairing element
`e_n(T, T) = τ_T∗(g_T) / g_T = g_T / g_T = 1`.

The forward direction of `weilPairingElt_eq_one_iff_translateEndo_fixed`; the hypothesis `htinv` is
the single genuinely-gated input, to be discharged by the product-over-`⟨T⟩` argument
(#465 deliverable 2). -/
theorem weilPairingElt_self_of_translateEndo_fixed {x₂ y₂ : F} (h₂ : W.Equation x₂ y₂)
    {g : W.FunctionField} (hg : g ≠ 0) (htinv : translateEndo h₂ g = g) :
    weilPairingElt h₂ g = 1 :=
  (weilPairingElt_eq_one_iff_translateEndo_fixed h₂ hg).mpr htinv

end CoordinateRing

end WeierstrassCurve.Affine
