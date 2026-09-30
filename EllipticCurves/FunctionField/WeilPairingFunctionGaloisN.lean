/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import EllipticCurves.Fixtures
import EllipticCurves.FunctionField.WeilPairingFunctionCyclotomic
import EllipticCurves.FunctionField.WeilPairingFunctionN
import EllipticCurves.FunctionField.WeilPairingGaloisRootN

/-!
# Galois equivariance of the Weil pairing as a function of two points, at a general `n`

`EllipticCurves.FunctionField.WeilPairingFunctionN` replaced the existential packaging of rung 6 at
a general index by genuine functions

```
weilPairingEltN h2 hn : E[n] → E[n] → F(W) ,      weilPairingN h2 hn : E[n] → E[n] → μ_n(F) ,
```

and read **four** of the five properties of Silverman *AEC* III.8.1 through them: bilinearity in
each slot, the alternating law, antisymmetry and non-degeneracy.  The fifth, III.8.1(d)
**Galois equivariance**, it did not: at a general index this tree had only the existential packaging
of `EllipticCurves.FunctionField.WeilPairingGaloisRootN`.  This file is that property at the
function level,

```
σ⋆(e_n(S, T)) = e_n(σ • S, σ • T) ,
```

at the `F(W⁄F)` level and at the `μ_n(F)` level, together with its cyclotomic exponent form.  It is
`EllipticCurves.FunctionField.WeilPairingFunctionGalois` (`#936`, `n = 2` and `n = 3`) and
`EllipticCurves.FunctionField.WeilPairingFunctionCyclotomic` (`#941`, the same two indices) at every
`n` with `(2 : F) ≠ 0` and `((n : ℤ) : F) ≠ 0` over an algebraically closed `F`.

## Why this is an equation and the merged general-`n` form is not

`exists_weilPairingMu_galois_of_ne_zero_of_hprin` returns *two rung-5 roots* — one at `S`, one at
`σS` — alongside the relation between the two pairing values, because `weilPairingElt` takes the
root as an argument.  It therefore cannot be composed: there is no term `e_n(σS, σT)` to write down.
Once the pairing is a function of the two points, both sides name themselves and the statement is an
equation between two values of one function, so it composes with bilinearity and with
non-degeneracy.  That is the whole content of this file, and it is the same move `#936` made one
index family down.

## ⚠️ No new mathematics is proved, and the one thing that is paid here and was not at `n = 2`, `3`

The content of each `F(W⁄F)`-level proof is a case split on whether each point is `O` and one
application of `exists_weilPairingElt_galois_of_ne_zero_of_hprin`
(`EllipticCurves.FunctionField.WeilPairingGaloisRootN`) read through
`weilPairingEltN_eq_weilPairingElt`; the `μ_n(F)`-level proof is the same with
`exists_weilPairingMu_galois_of_ne_zero_of_hprin` and `weilPairingN_eq_weilPairingMu`.

⚠️ **`hprin` is discharged here and not assumed**, and that is the one line the numeral files did
not have to write.  Both general-`n` headlines above still carry principality of the `[n]∗`-pullback
as a hypothesis, quantified over the point; over an algebraically closed `F` it is
`exists_nsmul_divisor_eq_divisor_mulByNEndo`
(`EllipticCurves.FunctionField.PullbackPrincipalityN`), which is exactly how `weilPairingEltN_self`
and `weilPairingEltN_add_left_of_ne_zero` discharge it in `WeilPairingFunctionN`.  So no statement
below takes it, and `[IsAlgClosed F]` is load-bearing for a second reason on top of the one that
makes `weilPairingN` exist at all.

## The hypotheses, once

The **four** declarations in namespace `WeierstrassCurve.Affine` carry `[W.IsElliptic]`,
`[IsAlgClosed F]`, `(2 : F) ≠ 0` and `((n : ℤ) : F) ≠ 0` — the same setting as
`WeilPairingFunctionN`'s own general-`n` layer, from which every pairing term below comes.
⚠️ **Two of the five publics differ from that list, so it is a register and not a universal**:
`weilPairingN_galois_eq_self_of_forall_fixed` takes `hσ` on top of it, and
`natCard_rootsOfUnity_of_intCast_ne_zero` is declared outside the namespace and carries neither the
curve nor `(2 : F) ≠ 0` — `## Main statements` says so of it below.  Each declaration's own clauses
defer to its **signature**, which is where the whole hypothesis list of that declaration is.

⚠️ **Exactly ONE of the five public declarations binds `[NeZero n]`, and this paragraph records
the widening that brought that count down from three.**  The survivor is
`weilPairingN_galois_eq_pow`, and ⚠️ **`weilPairingN` is not what forces it**: its statement names
`galoisModularCyclotomicChar` (`EllipticCurves.Galois.CyclotomicCharacter`:`133`), which binds
`[NeZero n]` in its own signature, so the instance is needed to **write** the exponent — delete the
binder and elaboration fails on the character, at the statement line, with a `haveI` in the tactic
block powerless to help because the statement is elaborated first.
⚠️ **`weilPairingN_galois` and `weilPairingN_galois_eq_self_of_forall_fixed` were forced by
`weilPairingN`'s signature and are not any more**, that signature having been widened one file up.
⚠️ **Their two proofs then part company, and that is what makes this file the sharpest case of the
statement/proof distinction: it is the sharpest case in BOTH directions.**
`weilPairingN_galois` takes **one** `haveI : NeZero n := ⟨fun h => hn (by simp [h])⟩` as its first
tactic and genuinely wants it — negative-controlled, not asserted: delete that line and the build
fails *inside the proof*, at the `exists_weilPairingMu_galois_of_ne_zero_of_hprin` application
(`failed to synthesize instance of type class`, with `rcases` failing behind it), and never at the
statement.  `weilPairingN_galois_eq_self_of_forall_fixed` takes **none**, and that too is measured
and not argued: without such a line the whole library is `lake build --wfail` EXIT 0 and
`lake lint` EXIT 0.  Its three-line proof routes through `weilPairingN_galois` and `weilPairingN`,
both widened here, which is why the widening left nothing in it to want the instance.
⚠️ **The difference is invisible in either statement** — neither names a constant that binds the
instance, which is why both could be widened at all — **and it is invisible to every gate as well**:
a `haveI` in a tactic block is not a binder, so `unusedArguments` cannot report a dead one, and a
build and a lint are green with or without it.  `EllipticCurves.FunctionField.WeilPairingFunctionN`
records the binder-side companion of that — *unused* and *removable* are different questions and
`unusedArguments` answers only the first; on a `haveI` the linter cannot even pose the question.
⚠️ **Do not generalise from the second half of the pair.**  All **six** `haveI` lines this widening
adds are load-bearing — three in `WeilPairingFunctionN`, this file's one, and two in
`WeilPairingDeterminantN` — and every verdict was reached by deleting the line and rebuilding.
A widened root is not the same thing as a proof that no longer wants the instance — and the other
direction is real too: this file's `weilPairingN_galois_eq_self_of_forall_fixed` and
`WeilPairingFunctionN`'s `weilPairingNHom` route only through constants this round widened, and
neither wants a substitute of any kind.
`weilPairingEltN_galois` is `F(W⁄F)`-valued and binds none of it — ⚠️ **and it needs no substitute
either**: every lemma it consumes takes `((n : ℤ) : F) ≠ 0` itself, so the
`by rintro rfl; simp at hn` step that `weilPairingEltN_self` pays to get `n ≠ 0` does not appear
for it at all.  `natCard_rootsOfUnity_of_intCast_ne_zero` is a statement about a field alone and
binds neither.

## ⚠️ The character in the exponent form is canonical and the caller supplies nothing

`galoisModularCyclotomicChar S F hn` asks for `hn : Nat.card μ_n(F) = n` — that `F` really has `n`
`n`-th roots of unity.  On this front that hypothesis is free:
`natCard_rootsOfUnity_of_ne_zero` (`EllipticCurves.FunctionField.WeilPairingSurjective`, `#938`)
derives it over an algebraically closed `F` from `(n : F) ≠ 0`, which is `((n : ℤ) : F) ≠ 0` after
`push_cast`.  `natCard_rootsOfUnity_of_intCast_ne_zero` below is that one-line bridge, and it is
what `weilPairingN_galois_eq_pow` names the character **in its own statement** with, rather than
taking a proof of its hypothesis as an argument.  ⚠️ Naming the character in the statement is
`#941`'s design and not a new one.  ⚠️ **And the bridge buys a NAME, not possibility**: the same
statement elaborates with `natCard_rootsOfUnity_of_ne_zero (by exact_mod_cast hn)` written inline,
so what a general `n` adds is only that the pairing's index hypothesis is an `ℤ`-cast and the
character's an `ℕ`-cast, and the cast has to be done somewhere.  A named lemma is the better place
for it than every statement that needs it, which is why this one is here.

## ⚠️ `weilPairingN_galois_eq_self_of_forall_fixed` does NOT go through the character

Its `n = 3` twin, `weilPairingThree_galois_eq_self_of_forall_fixed`, rewrites by the exponent form
and then kills the exponent with `galoisModularCyclotomicChar_eq_one_iff` and
`show ((1 : ZMod 3)).val = 1 from by decide`.  That route is **closed at a general index**:
`ZMod.val` of `1` is `1` only when `1 < n`, and at `n = 1` it is `0`.  The direct route — `σ` fixes
the value because the value is an `n`-th root of unity and the hypothesis says `σ` fixes every one
of those — needs no character, no `1 < n` and no case split, so it is the one taken.  ⚠️ **This is
not a claim that the `n = 3` proof is wrong**; at `n = 3` the two routes prove the same thing, and
`1 < 3` is `decide`-able, which is why the question never arose there.

## Main statements

Every public declaration of this file is listed here.  The four in namespace
`WeierstrassCurve.Affine` are stated for `W : Affine S` base-changed along `S → F`, at
`P T : (W⁄F).torsion n` and `σ : F ≃ₐ[S] F`.

* `natCard_rootsOfUnity_of_intCast_ne_zero` — `Nat.card μ_n(F) = n` over an algebraically closed `F`
  from `((n : ℤ) : F) ≠ 0`.  ⚠️ Not in namespace `WeierstrassCurve.Affine`: a statement about a
  field and nothing else, which belongs beside `natCard_rootsOfUnity_of_ne_zero` itself.
* `WeierstrassCurve.Affine.weilPairingEltN_galois` —
  `σ⋆(e_n(P, T)) = e_n(σ • P, σ • T)` in `F(W⁄F)`.
* `WeierstrassCurve.Affine.weilPairingN_galois` — the same in `μ_n(F)`, spelled through
  `restrictRootsOfUnity`.
* `WeierstrassCurve.Affine.weilPairingN_galois_eq_pow` —
  `e_n(σ • P, σ • T) = e_n(P, T) ^ χ_n(σ)`, the cyclotomic exponent form.
* `WeierstrassCurve.Affine.weilPairingN_galois_eq_self_of_forall_fixed` — `e_n` is invariant under
  any `σ` fixing the `n`-th roots of unity pointwise.  ⚠️ The hypothesis is stated as *"`σ` fixes
  every `n`-th root of unity"* rather than as `χ_n σ = 1` because that is the form a consumer can
  check without naming the character; `galoisModularCyclotomicChar_eq_one_iff` says the two are
  equivalent.

## Axioms

⚠️ `#print axioms` over all **five** public declarations reaches **0** `sorryAx` and nothing outside
`{propext, Classical.choice, Quot.sound}`, and the same three at every one of them — measured at the
commit that adds this file, over the five names listed above and not over a pattern.  The file also
carries **two** `private lemma`s and **seven** `example`s, all inside the recovery and non-vacuity
sections below; none of them is a statement this file publishes.

## What is NOT here

* **An arbitrary-field form.**  `weilPairingN` does not exist without `[IsAlgClosed F]` — the rung-5
  root need not exist (`#962`) — so there is no weaker statement being declined.  The merged
  `exists_weilPairing{Elt,Mu}_galois_of_ne_zero_of_hprin` *are* stated over an arbitrary field, and
  they are the statements to quote there; they are not equations, which is this file's whole
  subject.
* **`n = char F`.**  Ruled out by `((n : ℤ) : F) ≠ 0`, and the conclusion there is not merely
  unproved: the pairing is not defined.
* **The determinant.**  `det ρ_{E,n} = χ_n` at a general index consumes
  `weilPairingN_galois_eq_pow` together with the bilinear expansion of `e_n` on a pair of integer
  combinations, and it is `#2281`/`#2282`, not this file.  ⚠️ At `n = 2` and `n = 3` that consumer
  is `EllipticCurves.FunctionField.WeilPairingDeterminant`, whose `hPT : e_n(P, T) ≠ 1` is **not**
  the right hypothesis at a composite index; nothing in this file is affected by that, and nothing
  in it supplies the primitive pair that replaces it.

## References

* [J. H. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.8, Prop. 8.1(d) —
  *"It is Galois invariant"*, `e_m(S,T)^σ = e_m(S^σ, T^σ)`.  ⚠️ **The exponent form is not that
  equation verbatim**: it is that equation composed with the action of `σ` on `μ_n`, which is
  raising to `χ_n(σ)` by the definition of the cyclotomic character.  *AEC* defines no cyclotomic
  character, so there is no letter for the exponent form itself and `(d)` is the closest true
  citation.  It is **not** `(e)`, which is compatibility, `e_{mm'}(S,T) = e_{m'}([m]S, T)`.
-/

/-- **`μ_n(F)` has exactly `n` elements** over an algebraically closed `F`,
from the `ℤ`-cast form of the index hypothesis.

`natCard_rootsOfUnity_of_ne_zero` (`EllipticCurves.FunctionField.WeilPairingSurjective`) with
`push_cast`, and nothing else.  ⚠️ It exists because the general-`n` Weil pairing carries
`((n : ℤ) : F) ≠ 0` while the cyclotomic character's hypothesis is stated from `(n : F) ≠ 0`: the
exponent form below names the character through it rather than through an inline
`by exact_mod_cast hn`, which also elaborates.

A statement about a field and nothing else; it belongs beside `natCard_rootsOfUnity_of_ne_zero`. -/
theorem natCard_rootsOfUnity_of_intCast_ne_zero {F : Type*} [Field F] [IsAlgClosed F] {n : ℕ}
    (hn : ((n : ℤ) : F) ≠ 0) : Nat.card (rootsOfUnity n F) = n :=
  natCard_rootsOfUnity_of_ne_zero (by exact_mod_cast hn)

namespace WeierstrassCurve.Affine

open CoordinateRing

variable {S F : Type*} [Field S] [Field F] [Algebra S F] {W : Affine S} [W.IsElliptic]
  [IsAlgClosed F]

/-! ### The equivariance equation -/

open Classical in
/-- **Galois equivariance of `weilPairingEltN` at a general index**, at the `F(W⁄F)` level:

```
σ⋆(e_n(P, T)) = e_n(σ • P, σ • T) ,
```

at every `n` with `(2 : F) ≠ 0` and `((n : ℤ) : F) ≠ 0` over an algebraically closed `F`.

Three cases, of which two are corners.  If `T = O` or `P = O` both sides are `1`, because the Galois
action fixes `O` (`smul_zero`) and `σ⋆` fixes `1`.  Otherwise both points are affine and
`exists_weilPairingElt_galois_of_ne_zero_of_hprin`
(`EllipticCurves.FunctionField.WeilPairingGaloisRootN`) supplies a rung-5 root at `P` and one at
`σP`; each is read through `weilPairingEltN_eq_weilPairingElt`, whose divisor hypothesis is
*character for character* what `isWeilRootN_some` builds out of what that theorem returns.

⚠️ **`hprin` is discharged and not assumed** — by `exists_nsmul_divisor_eq_divisor_mulByNEndo`
(`EllipticCurves.FunctionField.PullbackPrincipalityN`), the same discharge
`weilPairingEltN_self` makes, and supplied term-mode in one `fun` exactly as
`WeilPairingFunctionN` supplies it at `:615`–`:616`.

⚠️ **No point is added anywhere in this proof**, the only case split being *is this point `O`*, so
the `n = 2` / general-`n` asymmetry that comes from a `2`-torsion point being its own negative — the
one `weilPairingEltN_add_left` had to argue around — cannot arise here. -/
theorem weilPairingEltN_galois (σ : F ≃ₐ[S] F) (h2 : (2 : F) ≠ 0) {n : ℕ}
    (hn : ((n : ℤ) : F) ≠ 0) (P T : (W⁄F).torsion n) :
    galoisFunctionField σ (weilPairingEltN h2 hn P T)
      = weilPairingEltN h2 hn (σ • P) (σ • T) := by
  cases hT : (T : (W⁄F).Point) with
  | zero =>
      have h0 : T = 0 := Subtype.ext (hT.trans Point.zero_def.symm)
      rw [h0, smul_zero, weilPairingEltN_zero_right, weilPairingEltN_zero_right, map_one]
  | some x₂ y₂ h₂ =>
      cases hP : (P : (W⁄F).Point) with
      | zero =>
          have h0 : P = 0 := Subtype.ext hP
          rw [h0, smul_zero, weilPairingEltN_zero_left, weilPairingEltN_zero_left, map_one]
      | some x y h =>
          have hS : Point.some x y h ∈ (W⁄F).torsion n := hP ▸ P.2
          obtain ⟨g, g', hg0, hg0', ⟨f, hf, hfdiv, u, hu⟩, ⟨f', hf', hf'div, u', hu'⟩, hgal⟩ :=
            exists_weilPairingElt_galois_of_ne_zero_of_hprin σ h2 hn h₂.left h hS
              (fun {_ _} h₀ hmem f hf hfdiv =>
                exists_nsmul_divisor_eq_divisor_mulByNEndo h2 hn _ h₀ hmem hf hfdiv)
          rw [weilPairingEltN_eq_weilPairingElt h2 hn
                (by rw [hP]; exact isWeilRootN_some n _ h hg0 hf hfdiv hu) h₂ hT,
            weilPairingEltN_eq_weilPairingElt h2 hn (g := g')
                (by
                  rw [torsion_galois_smul_coe, hP, Point.galois_smul_some]
                  exact isWeilRootN_some n _ (nonsingular_algEquiv σ h) hg0' hf' hf'div hu')
                (nonsingular_algEquiv σ h₂)
                (by rw [torsion_galois_smul_coe, hT, Point.galois_smul_some])]
          exact hgal

open Classical in
/-- **Galois equivariance of `weilPairingN` at a general index**, at the honest value group:

```
σ · e_n(P, T) = e_n(σ • P, σ • T)     in μ_n(F) ,
```

at every `n` with `(2 : F) ≠ 0` and `((n : ℤ) : F) ≠ 0` over an algebraically closed `F`.

The same three cases as the `F(W⁄F)` form, off `exists_weilPairingMu_galois_of_ne_zero_of_hprin` and
`weilPairingN_eq_weilPairingMu`.  ⚠️ The translation point's `n`-torsion hypothesis, which the
`μ_n(F)`-level headline asks for and its `F(W⁄F)` twin does not, is free here — it is `hT ▸ T.2`. -/
theorem weilPairingN_galois (σ : F ≃ₐ[S] F) (h2 : (2 : F) ≠ 0) {n : ℕ}
    (hn : ((n : ℤ) : F) ≠ 0) (P T : (W⁄F).torsion n) :
    restrictRootsOfUnity (σ.toRingEquiv.toRingHom) n (weilPairingN h2 hn P T)
      = weilPairingN h2 hn (σ • P) (σ • T) := by
  haveI : NeZero n := ⟨fun h => hn (by simp [h])⟩
  cases hT : (T : (W⁄F).Point) with
  | zero =>
      have h0 : T = 0 := Subtype.ext (hT.trans Point.zero_def.symm)
      rw [h0, smul_zero, weilPairingN_zero_right, weilPairingN_zero_right, map_one]
  | some x₂ y₂ h₂ =>
      have hm₂ : Point.some x₂ y₂ h₂ ∈ (W⁄F).torsion n := hT ▸ T.2
      cases hP : (P : (W⁄F).Point) with
      | zero =>
          have h0 : P = 0 := Subtype.ext hP
          rw [h0, smul_zero, weilPairingN_zero_left, weilPairingN_zero_left, map_one]
      | some x y h =>
          have hS : Point.some x y h ∈ (W⁄F).torsion n := hP ▸ P.2
          obtain ⟨g, g', hg0, hg0', ⟨f, hf, hfdiv, u, hu⟩, ⟨f', hf', hf'div, u', hu'⟩,
            hpow, hpow', hgal⟩ :=
            exists_weilPairingMu_galois_of_ne_zero_of_hprin σ h2 hn h₂ hm₂ h hS
              (fun {_ _} h₀ hmem f hf hfdiv =>
                exists_nsmul_divisor_eq_divisor_mulByNEndo h2 hn _ h₀ hmem hf hfdiv)
          have e1 : weilPairingN h2 hn P T = weilPairingMu h₂.left hpow :=
            weilPairingN_eq_weilPairingMu h2 hn
              (by rw [hP]; exact isWeilRootN_some n _ h hg0 hf hfdiv hu) h₂ hT hpow
          have e2 : weilPairingN h2 hn (σ • P) (σ • T)
              = weilPairingMu (equation_algEquiv σ h₂.left) hpow' := by
            refine weilPairingN_eq_weilPairingMu h2 hn (g := g') ?_
              (nonsingular_algEquiv σ h₂) ?_ hpow'
            · rw [torsion_galois_smul_coe, hP, Point.galois_smul_some]
              exact isWeilRootN_some n _ (nonsingular_algEquiv σ h) hg0' hf' hf'div hu'
            · rw [torsion_galois_smul_coe, hT, Point.galois_smul_some]
          rw [e1, e2]
          exact hgal

/-! ### The cyclotomic exponent form -/

open Classical in
/-- **The Weil pairing at a general index in cyclotomic form**:

```
e_n(σ • P, σ • T) = e_n(P, T) ^ χ_n(σ) ,
```

at every `n` with `(2 : F) ≠ 0` and `((n : ℤ) : F) ≠ 0` over an algebraically closed `F`.

`weilPairingN_galois` says `σ` acts on the value; this says *how*.  One rewrite by
`restrictRootsOfUnity_eq_pow_galoisModularCyclotomicChar`, with the character's hypothesis
`Nat.card μ_n(F) = n` discharged by `natCard_rootsOfUnity_of_intCast_ne_zero` from the index
hypothesis the pairing already carries — so the character named here is canonical and the caller
supplies nothing.

⚠️ Which hypothesis does what: the character and its hypothesis are gated on
`((n : ℤ) : F) ≠ 0` alone — the value group is `μ_n(F)` — and `(2 : F) ≠ 0` enters only through
`weilPairingN_galois`, which needs it to build the pairing at all.

⚠️ At `n = 2` the exponent is `1` and the statement is `weilPairingTwo_galois_eq_self`'s content
(`galoisModularCyclotomicChar_two_eq_one`); at every index `n ≥ 3` the group `(ZMod n)ˣ` is
nontrivial, so nothing forces the exponent there.  ⚠️ **`n = 1` is a third shape and not a caveat on
the second**: it is inside this statement's own range (`NeZero 1` is an instance), and there the
exponent is `(χ_1 σ : ZMod 1).val = 0` rather than `1` — the same fact about `((1 : ZMod n)).val`
that the `##` section above turns on.  ⚠️ Whether the character records a genuine invariant of `σ`
is a fact about `Gal(F/S)` only at `n ≥ 3`, since `(ZMod n)ˣ` is trivial below that; and at
`S = F`, where `Gal(F/S)` is trivial, the character is `1` at every index. -/
theorem weilPairingN_galois_eq_pow (σ : F ≃ₐ[S] F) (h2 : (2 : F) ≠ 0) {n : ℕ} [NeZero n]
    (hn : ((n : ℤ) : F) ≠ 0) (P T : (W⁄F).torsion n) :
    weilPairingN h2 hn (σ • P) (σ • T)
      = weilPairingN h2 hn P T
        ^ ((galoisModularCyclotomicChar S F (natCard_rootsOfUnity_of_intCast_ne_zero hn) σ :
            ZMod n)).val := by
  rw [← weilPairingN_galois σ h2 hn P T, restrictRootsOfUnity_eq_pow_galoisModularCyclotomicChar]

open Classical in
/-- **`e_n` is invariant under any `σ` fixing the `n`-th roots of unity pointwise**, at every `n`
with `(2 : F) ≠ 0` and `((n : ℤ) : F) ≠ 0` over an algebraically closed `F`:

```
e_n(σ • P, σ • T) = e_n(P, T) .
```

By `galoisModularCyclotomicChar_eq_one_iff` the hypothesis is exactly `χ_n σ = 1`, so this is the
sharp conditional form of which `weilPairingTwo_galois_eq_self` is the unconditional `n = 2` shadow:
there the kernel of the character is everything, here it is a proper subgroup in general.

⚠️ **The proof does not go through the character**, and its `n = 3` twin
`weilPairingThree_galois_eq_self_of_forall_fixed` does.  That route needs
`((1 : ZMod n)).val = 1`, which holds only for `1 < n`; the value of `e_n` is an `n`-th root of
unity and the hypothesis fixes every one of those, so `weilPairingN_galois` plus
`restrictRootsOfUnity_coe_apply` closes it with no condition on `n` and no case split. -/
theorem weilPairingN_galois_eq_self_of_forall_fixed (σ : F ≃ₐ[S] F) (h2 : (2 : F) ≠ 0) {n : ℕ}
    (hn : ((n : ℤ) : F) ≠ 0)
    (hσ : ∀ t ∈ rootsOfUnity n F, σ ((t : Fˣ) : F) = ((t : Fˣ) : F)) (P T : (W⁄F).torsion n) :
    weilPairingN h2 hn (σ • P) (σ • T) = weilPairingN h2 hn P T := by
  rw [← weilPairingN_galois σ h2 hn P T]
  refine Subtype.ext (Units.ext ?_)
  simpa [restrictRootsOfUnity_coe_apply] using hσ _ (weilPairingN h2 hn P T).2

/-! ### Recovery of the merged numeral layer, compiled

⚠️ The `n = 2` statements of `EllipticCurves.FunctionField.WeilPairingFunctionGalois` and
`EllipticCurves.FunctionField.WeilPairingFunctionCyclotomic` come back out of the general ones
**verbatim**, through `weilPairingEltN_eq_weilPairingEltTwo` and `weilPairingN_eq_weilPairingTwo`
(`WeilPairingFunctionN`'s own bridges) and **not** by unfolding either `Classical.choose`: the two
functions pick their rung-5 roots at different existentials against different pullbacks, and what
identifies the values is root-independence together with `mulByNEndo_two`.

⚠️ **The recovery is at `n = 2` and not at `n = 3`, and that is `WeilPairingFunctionN`'s placement
decision and not a claim that the `n = 3` mirror is harder** — it is not; that file records that the
mirror is *"the same three lines off `mulByNEndo_three`"* and that it is absent only because it
would put `WeilPairingFunctionThree` into its import closure.  This file cannot supply it either,
for the same reason one level up: the bridge it would need does not exist on `main`.

⚠️ **The recovery block costs `+2` modules and the figure is measured, not assumed.**  Keyed to
`21562de` and counted over the project's own `import` lines, transitively: this file's own closure
is **219** modules, and the closure of what the four headlines above need on their own —
`Fixtures`, `WeilPairingFunctionN`, `WeilPairingGaloisRootN`, `WeilPairingSurjective`,
`Galois.CyclotomicCharacter` and `TateModule.GaloisAction` — is **217**.  The difference is **two**
modules and they are named: `WeilPairingFunctionCyclotomic` and, through it,
`WeilPairingFunctionGalois`.  ⚠️ **One lemma is what buys both**:
`galoisModularCyclotomicChar_two_eq_one`, consumed by the third example below and by nothing else
here; the first two examples restate `#936`'s statements without citing them and are inside the
`217`.  The `+2` is paid rather than avoided by re-proving that lemma, because it is merged and its
proof is `Subsingleton.elim`. -/

section Recovery

open Classical in
/-- `weilPairingEltTwo_galois` (`#936`), recovered from `weilPairingEltN_galois`.

⚠️ `exact_mod_cast` is what supplies the general layer's `(((2 : ℕ) : ℤ) : F) ≠ 0` from
`(2 : F) ≠ 0`; the two are different terms and the merged statement carries only the second. -/
example (σ : F ≃ₐ[S] F) (h2 : (2 : F) ≠ 0) (P T : (W⁄F).torsion 2) :
    galoisFunctionField σ (weilPairingEltTwo h2 P T)
      = weilPairingEltTwo h2 (σ • P) (σ • T) := by
  have hn : (((2 : ℕ) : ℤ) : F) ≠ 0 := by exact_mod_cast h2
  rw [← weilPairingEltN_eq_weilPairingEltTwo h2 hn, ← weilPairingEltN_eq_weilPairingEltTwo h2 hn]
  exact weilPairingEltN_galois σ h2 hn P T

open Classical in
/-- `weilPairingTwo_galois` (`#936`), recovered from `weilPairingN_galois`. -/
example (σ : F ≃ₐ[S] F) (h2 : (2 : F) ≠ 0) (P T : (W⁄F).torsion 2) :
    restrictRootsOfUnity (σ.toRingEquiv.toRingHom) 2 (weilPairingTwo h2 P T)
      = weilPairingTwo h2 (σ • P) (σ • T) := by
  have hn : (((2 : ℕ) : ℤ) : F) ≠ 0 := by exact_mod_cast h2
  rw [← weilPairingN_eq_weilPairingTwo h2 hn, ← weilPairingN_eq_weilPairingTwo h2 hn]
  exact weilPairingN_galois σ h2 hn P T

open Classical in
/-- `weilPairingTwo_galois_eq_self` (`#941`), recovered from
`weilPairingN_galois_eq_self_of_forall_fixed`.

⚠️ The merged statement is **unconditional** in `σ` and this one is not, so the recovery has to
*produce* the hypothesis: at `n = 2` the only `2`-nd roots of unity are `± 1`, both of which lie in
the prime field, so `galoisModularCyclotomicChar_two_eq_one` and
`galoisModularCyclotomicChar_eq_one_iff` supply it.  That is the same observation
`galoisModularCyclotomicChar_two_eq_one`'s own docstring makes, consumed rather than restated. -/
example (σ : F ≃ₐ[S] F) (h2 : (2 : F) ≠ 0) (P T : (W⁄F).torsion 2) :
    weilPairingTwo h2 (σ • P) (σ • T) = weilPairingTwo h2 P T := by
  have hn : (((2 : ℕ) : ℤ) : F) ≠ 0 := by exact_mod_cast h2
  have hcard : Nat.card { x // x ∈ rootsOfUnity 2 F } = 2 :=
    natCard_rootsOfUnity_of_intCast_ne_zero hn
  have hσ : ∀ t ∈ rootsOfUnity 2 F, σ ((t : Fˣ) : F) = ((t : Fˣ) : F) :=
    (galoisModularCyclotomicChar_eq_one_iff hcard σ).mp
      (galoisModularCyclotomicChar_two_eq_one hcard σ)
  rw [← weilPairingN_eq_weilPairingTwo h2 hn, ← weilPairingN_eq_weilPairingTwo h2 hn]
  exact weilPairingN_galois_eq_self_of_forall_fixed σ h2 hn hσ P T

end Recovery

/-! ### Non-vacuity

⚠️ **This is one of the fronts in this tree whose statements need *two* fields**: a base field, an
extension, and an `S`-automorphism of the extension, plus `[IsAlgClosed F]`.  The curve is
`EllipticCurves.Fixture.y2EqX3SubX` over `ℚ`, base-changed to `EllipticCurves.Fixture.AlgClosedQ`,
with **`S = ℚ` and not `S = F`**, so that `Gal(F/S)` is a genuine group and not the trivial one.

⚠️ **The index is `5` and that is the point of the block**: `5` is outside the `3`-smooth range, so
neither merged numeral file nor the `_of_smooth` layer of `WeilPairingGaloisRootN` states anything
here, and `#E[5] = 25` on this curve is a named figure (`card_torsion_five`) rather than something a
`decide` produces.

⚠️ **`σ` is universally quantified in every certificate below, and so are the two points.**
`AlgebraicClosure ℚ` has no non-identity automorphism this tree can name, and `y² = x³ − x` has
torsion `(ℤ/2)²` over `ℚ`, so it has no `ℚ`-rational `5`-torsion point to name either — which is why
the *load-bearing* certificate here is not the rationality argument `#936`'s block uses at `n = 2`.
Said plainly rather than left for a reader to notice.

⚠️ **Which certificate is load-bearing.**  The first two are the equivariance equations, universally
quantified in `σ` and in both points, so they certify that the construction elaborates at an index
neither numeral file reaches — real, but weak (`#916`).  **The third is the one with weight**: it
says the pairing value at *every* pair of `5`-torsion points is fixed by every `σ` that fixes the
fifth roots of unity, which is not an instance of either equation above — it consumes
`weilPairingN_galois_eq_self_of_forall_fixed`, whose hypothesis is about the field and is false for
a general `σ`.  **The fourth** certifies the exponent form, so it is of the first two's kind rather
than the third's: it adds that the character-valued statement elaborates at `n = 5`, which is where
the cast bridge is exercised, and nothing about a value. -/

section Nonvacuity

/-! The base — algebraically closed, and of characteristic `0` so that `2 ≠ 0` and `5 ≠ 0` — is
`EllipticCurves.Fixture.AlgClosedQ`, whose single `[CharZero F]` instance also supplies
`IsElliptic` here. -/

open EllipticCurves.Fixture

private lemma exampleTwo : (2 : AlgClosedQ) ≠ 0 := two_ne_zero

private lemma exampleFive : (((5 : ℕ) : ℤ) : AlgClosedQ) ≠ 0 := by norm_num

open Classical in
/-- **The `μ_5(F)`-level equivariance equation at `n = 5`, on a curve that exists.** -/
example (σ : AlgClosedQ ≃ₐ[ℚ] AlgClosedQ) (P T : ((y2EqX3SubX ℚ)⁄AlgClosedQ).torsion 5) :
    restrictRootsOfUnity (σ.toRingEquiv.toRingHom) 5 (weilPairingN exampleTwo exampleFive P T)
      = weilPairingN exampleTwo exampleFive (σ • P) (σ • T) :=
  weilPairingN_galois σ exampleTwo exampleFive P T

open Classical in
/-- **The `F(W⁄F)`-level equation at `n = 5`**, so that both levels of this file are certified and
not only the value-group one. -/
example (σ : AlgClosedQ ≃ₐ[ℚ] AlgClosedQ) (P T : ((y2EqX3SubX ℚ)⁄AlgClosedQ).torsion 5) :
    galoisFunctionField σ (weilPairingEltN exampleTwo exampleFive P T)
      = weilPairingEltN exampleTwo exampleFive (σ • P) (σ • T) :=
  weilPairingEltN_galois σ exampleTwo exampleFive P T

open Classical in
/-- **⚠️ The load-bearing certificate**: on `y² = x³ − x` over `AlgebraicClosure ℚ`, the Weil
pairing at index `5` is invariant under every `σ ∈ Gal(F/ℚ)` fixing the fifth roots of unity —
equivalently, under the kernel of `χ_5`, which is a proper subgroup and not everything.  ⚠️ Its
input is the hypothesis on the field and not the equivariance equation, so it is not an instance of
either example above. -/
example (σ : AlgClosedQ ≃ₐ[ℚ] AlgClosedQ)
    (hσ : ∀ t ∈ rootsOfUnity 5 AlgClosedQ, σ ((t : AlgClosedQˣ) : AlgClosedQ)
      = ((t : AlgClosedQˣ) : AlgClosedQ))
    (P T : ((y2EqX3SubX ℚ)⁄AlgClosedQ).torsion 5) :
    weilPairingN exampleTwo exampleFive (σ • P) (σ • T)
      = weilPairingN exampleTwo exampleFive P T :=
  weilPairingN_galois_eq_self_of_forall_fixed σ exampleTwo exampleFive hσ P T

open Classical in
/-- **The exponent form at `n = 5`**, so that the character-valued headline is certified too. -/
example (σ : AlgClosedQ ≃ₐ[ℚ] AlgClosedQ) (P T : ((y2EqX3SubX ℚ)⁄AlgClosedQ).torsion 5) :
    weilPairingN exampleTwo exampleFive (σ • P) (σ • T)
      = weilPairingN exampleTwo exampleFive P T
        ^ ((galoisModularCyclotomicChar ℚ AlgClosedQ
            (natCard_rootsOfUnity_of_intCast_ne_zero exampleFive) σ : ZMod 5)).val :=
  weilPairingN_galois_eq_pow σ exampleTwo exampleFive P T

end Nonvacuity

end WeierstrassCurve.Affine
