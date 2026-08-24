/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import EllipticCurves.TateModule.PrimaryFree
import EllipticCurves.Torsion.TwoPrimaryBasis

/-!
# `T₂E ≅ ℤ₂²` : the Tate module at `ℓ = 2` is free of rank two

For an elliptic curve `W` over an algebraically closed field `F` with `(2 : F) ≠ 0`, the `2`-adic
Tate module `T₂E = lim_k E[2^k]` is a free `ℤ_[2]`-module of rank `2` (Silverman, *AEC*, III.7.1
and Remark 7.1.2):

```
Nonempty (W.tateModule 2 ≃ₗ[ℤ_[2]] ℤ_[2] × ℤ_[2])
Module.Free ℤ_[2] (W.tateModule 2)          Module.finrank ℤ_[2] (W.tateModule 2) = 2
```

This is the `ℓ = 2` case of the general statement `T_ℓE ≅ ℤ_ℓ²` for `ℓ ≠ char F`, and the first
structural description of any Tate module in this development.

## What this file contains, and what it does not

The construction is in `EllipticCurves.TateModule.PrimaryFree`, stated for an arbitrary prime `ℓ`
in terms of three inputs: a coherent system of generating pairs of the groups `E[ℓ^k]`, the count
`#E[ℓ^k] = ℓ^k · ℓ^k`, and finiteness of `E[ℓ^k]`. **This file supplies those three inputs at
`ℓ = 2`; it contains no argument.** ⚠️ It used to add *"and specialises every statement"*, which
overstates in exactly the way the same sentence in `EllipticCurves.Torsion.TwoPrimaryBasis` did
before it was repaired: it specialises **4** of `EllipticCurves.TateModule.PrimaryFree`'s **12**
public declarations, and the eight `padicPair…` names are consumed **unspecialised** at a general
`ℓ`, which is the subject of the ⚠️ note below. They are

* `exists_compatible_basis` (`EllipticCurves.Torsion.TwoPrimaryBasis`), the coherent system.
  Coherence is essential and is not supplied by the structure theorem: `E[2^k] ≃+ (ZMod (2^k))²`
  holds at each level *independently*, and a family of unrelated isomorphisms says nothing about an
  inverse limit.
* `card_torsion_two_pow_mul_self` and `finite_torsion_two_pow`
  (`EllipticCurves.Torsion.TwoPrimary`).

⚠️ **The names `padicPairFamily`, `padicPairHom`, `padicPairEquiv` and their lemmas are no longer
declared in this file.** They live in `EllipticCurves.TateModule.PrimaryFree` at a general `ℓ`, in
the same namespace `WeierstrassCurve.Affine.tateModule`, so `padicPairEquiv …` still resolves here
and in every consumer; but their *statements* are the general ones and their `h2` argument has been
replaced by the two cardinality inputs. Only the four `Nonempty`/`Free`/`finrank`/`Finite`
statements below keep the exact signatures this file used to publish.

Nothing here uses Ward's theorem, the elliptic-net recurrence, or the multiplication-by-`n`
coordinate formula `x(nP) = Φₙ/ΨSqₙ`: at `ℓ = 2` the whole `2`-primary tower is available from
surjectivity of `[2]` on `E(F̄)` alone. ⚠️ That sentence is true of *this* file and of `ℓ = 2`; it
is **not** true of `EllipticCurves.TateModule.FreeThree`, which reaches the same conclusion at
`ℓ = 3` through `EllipticCurves.Torsion.TriplingSurjective` and therefore does consume the
coordinate formula at `n = 3`.

## Non-vacuity

`Module.Free` and `finrank = 2` would both be *false* for the zero module, so they cannot be
satisfied vacuously. Independently of the equivalence built here,
`EllipticCurves.TateModule.LevelStructure` records `nontrivial_tateModule_two` by a route that
never mentions it: `T₂E` surjects onto `E[2^k]`, which has `4^k` elements, so `T₂E` is in fact
infinite. That statement lives there and is imported, not restated.

## Scope

Odd `ℓ` is not covered **by this file**, which is about `ℓ = 2` only. ⚠️ Earlier revisions said odd
`ℓ` was not covered *by the development*, "because the tower rests on surjectivity of `[2]`, and
`[ℓ]`-surjectivity for odd `ℓ` still needs `x(ℓP) = Φ_ℓ/ΨSq_ℓ`". Naming the clause: *"the tower
rests on surjectivity of `[2]`"* is now false of the development:
`EllipticCurves.TateModule.PrimaryFree` rests on surjectivity of `[ℓ]`, and
`EllipticCurves.Torsion.TriplingSurjective` pays that at `ℓ = 3`. The rest of the old sentence
survives verbatim **for `ℓ ≥ 5`**, where `x(ℓP) = Φ_ℓ/ΨSq_ℓ` is still the gate.

The Galois action on `T₂E` (`EllipticCurves.TateModule.GaloisAction`) and the representation
`ρ_{E,2} : G_F → GL₂(ℤ_2)` are a separate follow-up, which the rank statement here makes meaningful
for the first time.

## Main statements

* `WeierstrassCurve.Affine.tateModule.nonempty_tateModuleEquivProd`:
  `Nonempty (T₂E ≃ₗ[ℤ_[2]] ℤ_[2] × ℤ_[2])`.
* `WeierstrassCurve.Affine.tateModule.free_tateModule_two`: `Module.Free ℤ_[2] T₂E`.
* `WeierstrassCurve.Affine.tateModule.finrank_tateModule_two`: `finrank ℤ_[2] T₂E = 2`.
* `WeierstrassCurve.Affine.tateModule.finite_tateModule_two`: `Module.Finite ℤ_[2] T₂E`.

`Nontrivial (T₂E)` is **not** restated here: it is
`EllipticCurves.TateModule.LevelStructure.nontrivial_tateModule_two`, which this file imports.

## References

* [J. H. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.7.1 and Remark 7.1.2.
-/

open scoped AddSubgroup

namespace WeierstrassCurve.Affine

namespace tateModule

variable {F : Type*} [Field F] [DecidableEq F] {W : Affine F}

section Structure

variable [IsAlgClosed F] [W.IsElliptic]

/-- **The Tate module at `ℓ = 2` is `ℤ_[2]`-linearly isomorphic to `ℤ_[2] × ℤ_[2]`.** The
isomorphism depends on a choice of coherent system of generating pairs, so it is stated as a
`Nonempty`; the choice-free consequences are `free_tateModule_two` and
`finrank_tateModule_two`. -/
theorem nonempty_tateModuleEquivProd (h2 : (2 : F) ≠ 0) :
    Nonempty (W.tateModule 2 ≃ₗ[ℤ_[2]] ℤ_[2] × ℤ_[2]) :=
  nonempty_tateModuleEquivProd_of_card (finite_torsion_two_pow h2)
    (card_torsion_two_pow_mul_self h2) (exists_compatible_basis h2)

/-- **`T₂E` is a free `ℤ_[2]`-module** (Silverman, *AEC*, III.7.1 at `ℓ = 2`). -/
theorem free_tateModule_two (h2 : (2 : F) ≠ 0) : Module.Free ℤ_[2] (W.tateModule 2) :=
  free_tateModule_of_card (finite_torsion_two_pow h2)
    (card_torsion_two_pow_mul_self h2) (exists_compatible_basis h2)

/-- **`T₂E` has rank two over `ℤ_[2]`.** -/
theorem finrank_tateModule_two (h2 : (2 : F) ≠ 0) :
    Module.finrank ℤ_[2] (W.tateModule 2) = 2 :=
  finrank_tateModule_of_card (finite_torsion_two_pow h2)
    (card_torsion_two_pow_mul_self h2) (exists_compatible_basis h2)

/-- **`T₂E` is a finitely generated `ℤ_[2]`-module.** Free of rank two, so in particular finite as
a module; this is the shape `ρ_{E,2} : G_F → GL₂(ℤ_2)` will need. -/
theorem finite_tateModule_two (h2 : (2 : F) ≠ 0) : Module.Finite ℤ_[2] (W.tateModule 2) :=
  finite_tateModule_of_card (finite_torsion_two_pow h2)
    (card_torsion_two_pow_mul_self h2) (exists_compatible_basis h2)

end Structure

end tateModule

end WeierstrassCurve.Affine
