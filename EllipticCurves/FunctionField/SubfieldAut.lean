/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import Mathlib.Algebra.Field.Subfield.Basic
import Mathlib.Algebra.Algebra.Equiv

/-!
# Transport of the automorphism group along an equality of base subfields

`S = T` in `Subfield K` gives `(K ≃ₐ[S] K) ≃* (K ≃ₐ[T] K)`, by the identity on underlying
functions.

⚠️ **Nothing about elliptic curves enters this file**, and nothing about function fields either.
It is stated for an arbitrary field `K` and an arbitrary pair of equal subfields, its two imports
are both from `Mathlib`, and its `EllipticCurves`-import closure is **`0`**.

## Why this file exists (`#1267`)

`Subfield.autMulEquivOfEq` was written in `EllipticCurves.FunctionField.MulByNGaloisGroup`
(`#1233`), where the `Gal(F(W) / [n]∗F(W)) ≃* E[n]` identification first needed it.  The heading
comment of the section that held it — deleted there in the same change as this file is added —
said:

> ⚠️ **Nothing about elliptic curves enters this section.**  It is stated for an arbitrary field `K`
> and an arbitrary pair of equal subfields, and it is an upstream candidate

A second consumer then appeared: `EllipticCurves.FunctionField.NegYGaloisGroup` (`#1259`), which
identifies `Gal(F(W) / F(x))` with `⟨ι⟩`.  Measured from the environment rather than grepped —
walk `env.constants`, keep the ones whose `getModuleIdxFor?` is `NegYGaloisGroup`, union
`getUsedConstants` over value **and** type, keep the hits belonging to `MulByNGaloisGroup` — that
file used **one** name from it:

```
NegYGaloisGroup uses from MulByNGaloisGroup: [Subfield.autMulEquivOfEq]
```

and paid **53 project modules** for it: a project-import closure of `71` against the `17` of
`EllipticCurves.FunctionField.NegYGalois`, the file it actually extends.  ⚠️ **That is the wrong
file to pay it in**: `NegYGaloisGroup` carries neither `[IsAlgClosed F]` nor any condition on the
characteristic — it certifies on `y² + y = x³` over `ZMod 2`, where every statement of
`MulByNGaloisGroup` is unavailable — so the file whose selling point is that it needs nothing was
importing the closure of the file that needs everything.

Transitive import closures measured in Python over the `import` lines, at `ca096ac`, before and
after this change.  *Project* counts modules under `EllipticCurves`; *total* counts every package;
neither includes the module itself.

| module | project | total |
|---|---|---|
| this file | **0** | 1738 |
| `FunctionField.NegYGalois` | 17 | 2889 |
| `FunctionField.MulByNGaloisGroup` before → after | 70 → **71** | 3026 → **3027** |
| `FunctionField.NegYGaloisGroup` before → after | 71 → **19** | 3027 → **2891** |

⚠️ This file's closure is a **subset** of `NegYGalois`'s and of `MulByNGaloisGroup`'s — checked as
a set inclusion, not by counting — so it adds no `Mathlib` module to either consumer.
`MulByNGaloisGroup` gains exactly one module, this one; `NegYGaloisGroup` loses **52 project
modules and 136 in total**.

⚠️ **The `^import` regex is not enough to reproduce the total column.**  `Mathlib` at this pin uses
the Lean module system: its files open with `module` and their imports read `public import
Mathlib.…`.  A script matching `^import\s+(\S+)` reads every `Mathlib` file as having no imports
and silently reports a *total* of `111` for `NegYGaloisGroup` instead of `3027` — a plausible
number, off by a factor of thirty, and identical to the project column plus the direct `Mathlib`
imports of the files in it.  Match
`^(?:public |private |meta |protected )*import\s+(\S+)`; this project's own files use plain
`import` and are unaffected, which is exactly why the bug does not announce itself.

## ⚠️ Mathlib has no name for this, re-checked at `v4.32.0` rather than inherited

* `AlgEquiv.autCongr` (`Mathlib/Algebra/Algebra/Equiv.lean`) moves the **top** algebra over a fixed
  base, `(A₁ ≃ₐ[R] A₂) → ((A₁ ≃ₐ[R] A₁) ≃* (A₂ ≃ₐ[R] A₂))`; the base is what moves here.
* `IntermediateField.equivOfEq` is an `AlgEquiv` between the two **subfields themselves**, not
  between the automorphism groups over them, and it is `IntermediateField`-shaped besides.
* `RingEquiv.subfieldCongr` (`Mathlib/Algebra/Field/Subfield/Basic.lean`) and its
  `RingEquiv.subsemiringCongr` sibling take `S = T` to `↥S ≃+* ↥T` — the congruence for the
  subobject itself, again not for the automorphism group over it.

So this is an **upstream candidate exactly as it stands**.  ⚠️ Upstreaming it is *not* this file's
job and has not been attempted: it is a different change with a different review, and this file only
puts the declaration in the shape that change would take.

## Main definitions

* `Subfield.autMulEquivOfEq` — transport of `Aut K` along an equality of base subfields.

## Main statements

* `Subfield.autMulEquivOfEq_apply` and `Subfield.autMulEquivOfEq_symm_apply` — the transport is the
  identity on underlying functions.

⚠️ **Consumer census, from the environment rather than from a grep**, so the reach of the move is
on the record: `autMulEquivOfEq` has **six** consumers — the four Galois-group identifications
`torsionNMulGaloisEquiv`, `torsionTwoMulGaloisEquiv`, `torsionThreeMulGaloisEquiv`
(`EllipticCurves.FunctionField.MulByNGaloisGroup`) and `negYGroupGaloisEquiv`
(`EllipticCurves.FunctionField.NegYGaloisGroup`), plus its own two `apply` lemmas.  Those two have
**zero** named consumers of their own, exactly as before the move: they are `@[simp]` lemmas whose
job is to keep `rfl`-computation rules such as `negYGroupGaloisEquiv_apply` provable, and each of
those is proved by `rfl` rather than by rewriting.  This is disclosed, not hidden — a lemma with no
call site is worth stating as a fact about the file rather than discovering later.

## What is *not* here

* **No generalisation.**  `[Field K]` and `Subfield K` are the hypotheses the two consumers hold.
  The same argument would run for `Subring` or `Subalgebra`, and no consumer wants it there.
* **Nothing `IntermediateField`-shaped.**  `NegYGaloisGroup`'s sandwich is an `IntermediateField`
  equality and drops to the `Subfield` level by `SetLike.ext` *before* this applies; that step
  stays in that file, where its `[W.IsElliptic]` context lives.
-/

namespace Subfield

variable {K : Type*} [Field K] {S T : Subfield K}

/-- **Equal base subfields give isomorphic automorphism groups**, by the identity on underlying
functions.

An `S`-algebra automorphism of `K` is a ring automorphism that fixes `S` pointwise, and `S = T` says
the two subsets are the same, so nothing is transported except the proof obligation.  The
`MulEquiv` is therefore built out of `AlgEquiv.ofRingEquiv` in both directions and all three
coherence fields are `rfl`. -/
def autMulEquivOfEq (hST : S = T) : (K ≃ₐ[↥S] K) ≃* (K ≃ₐ[↥T] K) where
  toFun e := AlgEquiv.ofRingEquiv (f := (e : K ≃+* K)) fun r => e.commutes ⟨r, hST.ge r.2⟩
  invFun e := AlgEquiv.ofRingEquiv (f := (e : K ≃+* K)) fun r => e.commutes ⟨r, hST.le r.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

@[simp] lemma autMulEquivOfEq_apply (hST : S = T) (e : K ≃ₐ[↥S] K) (x : K) :
    autMulEquivOfEq hST e x = e x := rfl

@[simp] lemma autMulEquivOfEq_symm_apply (hST : S = T) (e : K ≃ₐ[↥T] K) (x : K) :
    (autMulEquivOfEq hST).symm e x = e x := rfl

end Subfield
