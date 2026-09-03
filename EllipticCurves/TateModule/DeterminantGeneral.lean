/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import EllipticCurves.Fixtures
import EllipticCurves.TateModule.FreeGeneral
import EllipticCurves.TateModule.PrimaryDeterminant

/-!
# `tr ρ_{E,ℓ}(1) = 2` and `charpoly ρ_{E,ℓ}(1) = (X - 1)²` at EVERY prime `ℓ ≠ char F`

`EllipticCurves.TateModule.PrimaryDeterminant` states the determinant and trace of `ρ_{E,ℓ}` at an
arbitrary prime, but its two *rank-sensitive* statements — the ones that would be false if `T_ℓE`
had rank `0` or `1` — take the rank-two input
`Nonempty (T_ℓE ≃ₗ[ℤ_[ℓ]] ℤ_[ℓ] × ℤ_[ℓ])` as an argument. **This file supplies that input at every
prime `ℓ` with `(2 : F) ≠ 0` and `(ℓ : F) ≠ 0`, and contains no argument**; both proofs are one
line, and the input is `nonempty_tateModuleEquivProd_of_natCast_ne_zero`
(`EllipticCurves.TateModule.FreeGeneral`, `#268`). ⚠️ **`(2 : F) ≠ 0` is the second hypothesis, and
this paragraph used to name only the first** — see `EllipticCurves.Torsion.StructureGeneral`, where
it enters, for why it is there and why it is not the same kind of restriction as `(ℓ : F) ≠ 0`.

This is the `EllipticCurves.TateModule.DeterminantThree` pair
(`galoisTraceThree_one`, `charpoly_galoisRepMatrixThree_one`) with `3` replaced by an arbitrary
prime away from the characteristic, and it is the `Determinant` entry of `#1533` item 4's list.

⚠️ `(ℓ : F) ≠ 0` is **sharp**: at `ℓ = char F` the conclusion is *false*, not unproved. There
`E[ℓ]` is `0` or `ℤ/ℓℤ`, so `T_ℓE` has rank `0` or `1`, and `tr 1` is `0` or `1` rather than `2`.
That is exactly why these two statements — and not the rest of `PrimaryDeterminant` — are the ones
that needed an input.

## What this file does NOT do

* **No `def`s, and no `…General` twins of `galoisDet` / `galoisTrace`.** Those are already the
  general-`ℓ` definitions (`EllipticCurves.TateModule.PrimaryDeterminant`), and every lemma about
  them — `galoisDet_one`, `coe_galoisDet`, `trace_galoisRepMatrix`, `charpoly_galoisRepMatrix` — is
  already stated at an arbitrary prime and needs nothing from here. A twin would be duplication;
  `EllipticCurves.TateModule.MatrixRepGeneral` makes the same call and records why
  `DeterminantThree`'s own `def`s are a deliberate exception that does not transfer.
* **Not `det ρ_{E,ℓ} = χ_ℓ`.** The `ℓ`-adic cyclotomic-character identity needs the Weil pairing on
  `E[ℓ^k]` for every `k`; nothing here supplies a pairing. The mod-`ℓ` identity is a different
  statement and lives in `EllipticCurves.FunctionField.WeilPairingDeterminantCharacter`.
* **Nothing at `ℓ = char F`**, and `EllipticCurves.TateModule.DeterminantThree` is **not** deleted:
  it reaches `ℓ = 3` through `x(3P) = Φ₃/Ψ₃²`, this file reaches every prime through `#E[n] = n²`
  and the Wronskian identity, and two independent routes to one conclusion are the cheapest
  cross-check on both.

## Main statements

* `WeierstrassCurve.Affine.galoisTrace_one_of_natCast_ne_zero` : `tr ρ_{E,ℓ}(1) = 2`.
* `WeierstrassCurve.Affine.charpoly_galoisRepMatrix_one_of_natCast_ne_zero` :
  `charpoly (ρ_b(1)) = X² - 2X + 1`.

## References

* [J. H. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.7.
-/

open Matrix Polynomial

namespace WeierstrassCurve.Affine

variable {S F : Type*} [Field S] [Field F] [DecidableEq F] [Algebra S F] {W' : Affine S}
variable {ℓ : ℕ} [Fact ℓ.Prime] [IsAlgClosed F] [(W'⁄F).IsElliptic]

/-- **`tr ρ_{E,ℓ}(1) = 2` at every prime `ℓ` with `(ℓ : F) ≠ 0`.**

⚠️ The `2` is the **rank** of `T_ℓE`, not the prime, and that is the whole content: over the zero
module the trace of the identity is `0`, and over a rank-one module it is `1`. This is the shape in
which `PrimaryDeterminant` records that `T_ℓE` really is rank two.

⚠️ **Deletion test**, measured on this file as committed. Replacing the argument
`(tateModule.nonempty_tateModuleEquivProd_of_natCast_ne_zero h2 hl)` by a hole — `by refine
galoisTrace_one_of_nonempty (W' := W') (F := F) (ℓ := ℓ) ?_` — leaves

```
error: unsolved goals
S : Type u_1
F : Type u_2
inst✝⁶ : Field S
inst✝⁵ : Field F
inst✝⁴ : DecidableEq F
inst✝³ : Algebra S F
W' : Affine S
ℓ : ℕ
inst✝² : Fact (Nat.Prime ℓ)
inst✝¹ : IsAlgClosed F
inst✝ : WeierstrassCurve.IsElliptic W'⁄F
h2 : 2 ≠ 0
hl : ↑ℓ ≠ 0
⊢ Nonempty (↥((W'⁄F).tateModule ℓ) ≃ₗ[ℤ_[ℓ]] ℤ_[ℓ] × ℤ_[ℓ])
```

⚠️ `h2` and `hl` both **survive**, so what the deletion removes is a construction and not a
hypothesis, and the residual is a **goal**, which no type mismatch could produce. It is `#268`'s
theorem. -/
theorem galoisTrace_one_of_natCast_ne_zero (h2 : (2 : F) ≠ 0) (hl : (ℓ : F) ≠ 0) :
    galoisTrace (W' := W') (F := F) (ℓ := ℓ) 1 = 2 :=
  galoisTrace_one_of_nonempty (tateModule.nonempty_tateModuleEquivProd_of_natCast_ne_zero h2 hl)

/-- **The characteristic polynomial of `ρ_{E,ℓ}(1)` is `(X - 1)²`**, written out as `X² - 2X + 1`,
at every prime `ℓ` with `(ℓ : F) ≠ 0`.

This is `galoisTrace_one_of_natCast_ne_zero` and `galoisDet_one` combined; like the trace statement
it fails over the zero module, where the characteristic polynomial of the identity is `1`. -/
theorem charpoly_galoisRepMatrix_one_of_natCast_ne_zero
    (b : Module.Basis (Fin 2) ℤ_[ℓ] ((W'⁄F).tateModule ℓ)) (h2 : (2 : F) ≠ 0) (hl : (ℓ : F) ≠ 0) :
    (galoisRepMatrix b 1 : Matrix (Fin 2) (Fin 2) ℤ_[ℓ]).charpoly = X ^ 2 - C 2 * X + C 1 :=
  charpoly_galoisRepMatrix_one_of_nonempty b
    (tateModule.nonempty_tateModuleEquivProd_of_natCast_ne_zero h2 hl)

/-! ### Non-vacuity

Three risks, three certificates, following the idiom
`EllipticCurves.TateModule.MatrixRepGeneral` uses for this front.

1. That the hypotheses are simultaneously satisfiable on a curve that exists, over a base `S` whose
   absolute Galois group is not trivial — hence `S = ℚ` and `F = ℚ̄`.
2. ⚠️ That the statement is **general** rather than a re-parametrisation of the primes this
   development already reached. `ℓ = 5` alone does not show that: it proves only that `{2, 3}` was
   left. So the certificates run at `ℓ = 5` **and** at `ℓ = 7` on a second curve, `y² = x³ + 1`
   (Δ = −432), which the `ℓ = 5` block does not mention.
3. That `T_ℓE` is not the zero module — otherwise `tr 1 = 2` would be the statement `0 = 2` and
   could not be a theorem, but the *reader* cannot see that without a witness. The `Infinite`
   certificate below goes through `infinite_tateModule_of_card` and never mentions the trace.

⚠️ `Fact (Nat.Prime p)` is needed in the *statements* (`ℤ_[p]` does not elaborate without it), so it
cannot be a `haveI` inside a proof. `private` hides a **name**, not an **instance** (`#1397`), so
the two below take part in typeclass resolution downstream; that is harmless (`Fact` is a `Prop`)
and is stated rather than left as a surprise. `EllipticCurves.TateModule.FreeGeneral` already leaks
one at `5`; these are deliberate duplicates so this file's certificates do not depend on that
accident. ⚠️ `by norm_num` does **not** close `Nat.Prime 5` in this import closure — the
`NormNum.Prime` extension is not reachable — so these use `by decide`. -/

section Nonvacuity

open EllipticCurves.Fixture

private instance factPrimeFiveDet : Fact (Nat.Prime 5) := ⟨by decide⟩
private instance factPrimeSevenDet : Fact (Nat.Prime 7) := ⟨by decide⟩

private lemma exampleTwoDet : (2 : AlgClosedQ) ≠ 0 := two_ne_zero

private lemma exampleFiveDet : ((5 : ℕ) : AlgClosedQ) ≠ 0 := by
  have : ((5 : ℕ) : AlgClosedQ) = 5 := by push_cast; ring
  rw [this]; norm_num

private lemma exampleSevenDet : ((7 : ℕ) : AlgClosedQ) ≠ 0 := by
  have : ((7 : ℕ) : AlgClosedQ) = 7 := by push_cast; ring
  rw [this]; norm_num

open Classical in
/-- **⚠️ THE LOAD-BEARING CERTIFICATE**: on a curve that exists, over a base field `S = ℚ` whose
absolute Galois group is not trivial, `tr ρ_{E,5}(1) = 2`.

`5` is the first prime at which no earlier statement in this development gives the trace of the
identity: `EllipticCurves.TateModule.Determinant` is `ℓ = 2` and
`EllipticCurves.TateModule.DeterminantThree` is `ℓ = 3`. The statement is restated in full rather
than obtained-and-projected (`#916`) and closes by **application**. -/
example : galoisTrace (W' := y2AddYEqX3 ℚ) (F := AlgClosedQ) (ℓ := 5) 1 = 2 :=
  galoisTrace_one_of_natCast_ne_zero exampleTwoDet exampleFiveDet

open Classical in
/-- ⚠️ **`ℓ = 7`, on a SECOND curve.** `y² = x³ + 1` (Δ = −432) is not the fixture the `ℓ = 5` block
above uses, and `7` is mentioned nowhere in the chain this file consumes. This is the certificate
that the statement is not `{2, 3, 5}`-parametrised, which `ℓ = 5` alone cannot give. -/
example : galoisTrace (W' := y2EqX3AddOne ℚ) (F := AlgClosedQ) (ℓ := 7) 1 = 2 :=
  galoisTrace_one_of_natCast_ne_zero exampleTwoDet exampleSevenDet

open Classical in
/-- The characteristic-polynomial half, at `ℓ = 5`, with the basis **existentially quantified
inside the statement** rather than taken as an argument — so this does not certify a family that
might be empty. -/
example : ∃ b : Module.Basis (Fin 2) ℤ_[5] (((y2AddYEqX3 ℚ)⁄AlgClosedQ).tateModule 5),
    (galoisRepMatrix (S := ℚ) b 1 : Matrix (Fin 2) (Fin 2) ℤ_[5]).charpoly
      = X ^ 2 - C 2 * X + C 1 := by
  obtain ⟨b⟩ := tateModule.nonempty_basis_tateModule_of_nonempty
    (tateModule.nonempty_tateModuleEquivProd_of_natCast_ne_zero
      (W := (y2AddYEqX3 ℚ)⁄AlgClosedQ) exampleTwoDet exampleFiveDet)
  exact ⟨b, charpoly_galoisRepMatrix_one_of_natCast_ne_zero b exampleTwoDet exampleFiveDet⟩

open Classical in
/-- **The module the trace is taken on is not the zero module**, at `ℓ = 5`, by a route that never
mentions the trace: `T₅E` surjects onto `E[5^k]`, which has `25^k` elements. -/
example : Infinite (((y2AddYEqX3 ℚ)⁄AlgClosedQ).tateModule 5) :=
  tateModule.infinite_tateModule_of_card (Fact.out : (5 : ℕ).Prime).one_lt
    (tateModule.proj_surjective_of_two_ne_zero exampleTwoDet)
    (card_torsion_pow_mul_self_of_natCast_ne_zero exampleTwoDet exampleFiveDet)

end Nonvacuity

end WeierstrassCurve.Affine
