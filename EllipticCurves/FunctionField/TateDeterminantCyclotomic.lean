/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import EllipticCurves.Fixtures
import EllipticCurves.FunctionField.WeilPairingDeterminantCharacterN
import EllipticCurves.TateModule.PrimaryDeterminantLevel

/-!
# `det ρ_{E,ℓ} = χ_ℓ`: the determinant of `ρ_{E,ℓ}` is the `ℓ`-adic cyclotomic character

For an elliptic curve `W'` over `S` and an algebraically closed extension `F / S`, the determinant
of the `ℓ`-adic Galois representation on `T_ℓE` is the `ℓ`-adic cyclotomic character of `F / S`:

```lean
galoisDet (W' := W') (F := F) (ℓ := ℓ) = galoisCyclotomicChar S F ℓ
```

at every prime `ℓ` with `(2 : F) ≠ 0` and `(ℓ : F) ≠ 0` (Silverman, *AEC*, III.8.1(a), (b), (d)
assembled over the `ℓ`-power tower).

## ⚠️ The statement the development was built for, and the blocks that denied it

Seven modules name this identification as the reason the determinant character is interesting:
`EllipticCurves.TateModule.Determinant`, `EllipticCurves.TateModule.DeterminantMod`,
`EllipticCurves.TateModule.MatrixRepGeneral`, `EllipticCurves.TateModule.ImageGeneral`,
`EllipticCurves.TateModule.ImageProfiniteGeneral`, `EllipticCurves.TateModule.DeterminantGeneral`
and `EllipticCurves.Galois.CyclotomicCharacter`.  ⚠️ **That is not the set this file is keyed
to.**  The blocks that went further and asserted the identification *unavailable* cut across the
list above rather than sitting inside it, and **every one of them is retired** — recorded once, at
`galoisDet` in `EllipticCurves.TateModule.PrimaryDeterminant`, which carries the roster, its count
and the reason one quotation serves them all (`README.md` `### Retired claims`).  Each wording is
quoted in its own source rather than deleted.

⚠️ **Why the `seven` above is a numeral and the roster's size is not, which is `#2303`/`#2304`'s own
rule and not an exception to it**: the seven modules are enumerated in the sentence that counts
them, so an eighth falsifies the numeral and the list it summarises *in the same block*, where a
reader is already looking.  The roster's size summarises a list that lives in another file, so a
thirteenth block would falsify it here with nothing on this page to catch it — which is exactly the
class those rows convicted, and a `##` heading is the worst place to put one, since it is the line a
reader keys the whole section to.  **So the roster is referred to and not counted here**, and the
members this section does name, it names.

⚠️⚠️ **Most of the roster says *"not proved **here**"* or *"and is untouched"*; two of its members
say it flat** — with no file, no field and no index qualifier, which is why a recogniser keyed to
the first two shapes cannot see them.  **Both are named on this line, so the `two` is counted
here**: they are
`EllipticCurves.FunctionField.GaloisPointAction`'s *"`det ρ_{E,2} = χ_2` is not proved and gets no
closer to being proved"* and `EllipticCurves.FunctionField.WeilPairingDeterminantCharacter`'s
*"remains open … at `k = 1` only"*.  **`EllipticCurves.Galois.CyclotomicCharacter`'s is a third
shape again**: its *"not proved here"* is true of that file and stands, and what is retired there is
the list of three prerequisites it gave *for proving the proposition at all*, since all three are
landed.

The sharpest of the *"not proved **here**"* shape is
`EllipticCurves.FunctionField.WeilPairingDeterminantCharacterN`'s `## Explicitly out of scope`:

> **The `ℓ`-adic statement.**  `galoisDetTwo = χ_2` over `ℤ_[2]` needs the pairing on `E[2 ^ k]`
> for every `k` and is untouched; the index here is a single `n`, not a tower.

⚠️ **That clause's *reason* is correct and is exactly what this file does**: it consumes the
general-index pairing statement at every index `ℓ ^ k`, which is what makes the tower available.
What was missing was never the pairing — it was the comparison of the two determinant characters
level by level, and that is `EllipticCurves.TateModule.PrimaryDeterminantLevel`, which mentions no
pairing at all.

⚠️⚠️ **One member of the roster has a *reason* that cannot be endorsed that way, and its
retirement says so where the rest endorse theirs.  It is
`EllipticCurves.FunctionField.WeilPairingDeterminantCharacter`'s**, whose *"this development has it
at `k = 1` only"* was false when it was written rather than superseded afterwards: `weilPairingN`
(`EllipticCurves.FunctionField.WeilPairingFunctionN`) and
`galoisDetMod_n_eq_galoisModularCyclotomicChar`
(`EllipticCurves.FunctionField.WeilPairingDeterminantCharacterN`) are both at a general `n`, and
both predate this file.  What that clause was missing was the **tower**, which is the level
comparison, and not another index of the pairing.

## The proof is three facts and `PadicInt.ext_of_toZModPow`

`ℤ_[ℓ]` is the inverse limit of the `ZMod (ℓ ^ k)`, so two `ℓ`-adic integers are equal as soon as
all their residues are.  At level `k`:

| | |
|---|---|
| `toZModPow k (det ρ_{E,ℓ}(σ)) = det ρ_{E,ℓ^k}(σ)` | `toZModPow_coe_galoisDet_of_natCast_ne_zero` |
| `det ρ_{E,n}(σ) = χ_n(σ)` at `n = ℓ ^ k` | `galoisDetMod_n_apply_eq_galoisModularCyclotomicChar` |
| `toZModPow k (χ_ℓ(σ)) = χ_{ℓ^k}(σ)` | `galoisCyclotomicChar_toZModPow` |

⚠️ **The two `χ_{ℓ^k}` are produced from different proofs of `Nat.card μ_{ℓ^k}(F) = ℓ ^ k`** —
`natCard_rootsOfUnity_of_intCast_ne_zero` on one side and
`HasEnoughRootsOfUnity.natCard_rootsOfUnity` on the other — and they are nonetheless the *same
term*, because `galoisModularCyclotomicChar`'s counting argument is a `Prop` and proof irrelevance
identifies them.  The proof below closes on `rfl` after the three rewrites, which is the check.

## ⚠️ No roots-of-unity instance is a hypothesis, and that is deliberate

`galoisCyclotomicChar_toZModPow` asks for `[∀ i, HasEnoughRootsOfUnity F (ℓ ^ i)]`.  Over an
algebraically closed `F` with `(ℓ : F) ≠ 0` that instance is *found*, through
`IsAlgClosed.isSepClosed` and `IsSepClosed.hasEnoughRootsOfUnity_pow`
(`EllipticCurves.Galois.CyclotomicCharacter`'s `hasEnoughRootsOfUnity_pow_of_isSepClosed` records
exactly this).  So it is produced inside the proofs from `hℓ` rather than carried in the
statements, and a consumer of the headline discharges nothing it was not already discharging for
`galoisDetMod_n_eq_galoisModularCyclotomicChar`.

## Main statements

* `WeierstrassCurve.Affine.coe_galoisDet_eq_coe_galoisCyclotomicChar` — the identity in `ℤ_[ℓ]`,
  for a fixed `σ`.
* `WeierstrassCurve.Affine.galoisDet_apply_eq_galoisCyclotomicChar` — the same in `ℤ_[ℓ]ˣ`.
* `WeierstrassCurve.Affine.galoisDet_eq_galoisCyclotomicChar` — **the headline**,
  `det ρ_{E,ℓ} = χ_ℓ` as an identity of monoid homomorphisms `(F ≃ₐ[S] F) →* ℤ_[ℓ]ˣ`.
* `WeierstrassCurve.Affine.galoisDetTwo_eq_galoisCyclotomicChar` — the `ℓ = 2` instance, stated
  under its own name because that is the sentence `EllipticCurves.TateModule.Determinant` and
  `EllipticCurves.Galois.CyclotomicCharacter` *used to* call unproved, and a reader greps for
  `galoisDetTwo`.
* `WeierstrassCurve.Affine.galoisDet_ne_one_of_galoisCyclotomicChar_ne_one` — the form in which the
  identity has consequences.

## ⚠️ What is *not* claimed

* **Nothing about `ρ_{E,ℓ}` itself.**  Only its determinant is pinned down; the image of `ρ_{E,ℓ}`
  is not, and `EllipticCurves.TateModule.MatrixRepDeterminantCharacterN`'s
  `range_galoisRepModMatrix_n_not_le_range_toGL` is the only statement on this board about where
  that image is not.
* ⚠️ **No `σ` with `χ_ℓ(σ) ≠ 1` is produced at any prime.**  `#947`'s
  `exists_galoisModularCyclotomicChar_three_ne_one` is a statement about `AlgebraicClosure ℚ` at
  the single index `3` and has no `ℓ`-adic twin, so
  `galoisDet_ne_one_of_galoisCyclotomicChar_ne_one` is stated and never fired here.
* **The matrix form.**  `det ∘ galoisRepMatrix b = χ_ℓ` follows from the headline and
  `coe_galoisDet`, and is not stated: unlike the mod-`n` case there is no consumer.

## References

* [J. H. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.7 and III.8.1.
-/

namespace WeierstrassCurve.Affine

variable {S F : Type*} [Field S] [Field F] [Algebra S F] {W' : Affine S}
  [IsAlgClosed F] [W'.IsElliptic] {ℓ : ℕ} [Fact ℓ.Prime]

open Classical in
/-- **`det ρ_{E,ℓ}(σ) = χ_ℓ(σ)` in `ℤ_[ℓ]`**, at every prime `ℓ` with `(2 : F) ≠ 0` and
`(ℓ : F) ≠ 0`.

Both sides are determined by their residues modulo every `ℓ ^ k`
(`PadicInt.ext_of_toZModPow`), and at level `k` the equation is
`galoisDetMod_n_apply_eq_galoisModularCyclotomicChar` at the index `ℓ ^ k`. -/
theorem coe_galoisDet_eq_coe_galoisCyclotomicChar (h2 : (2 : F) ≠ 0) (hℓ : (ℓ : F) ≠ 0)
    (σ : F ≃ₐ[S] F) :
    ((galoisDet (W' := W') (F := F) (ℓ := ℓ) σ : ℤ_[ℓ]ˣ) : ℤ_[ℓ])
      = ((galoisCyclotomicChar S F ℓ σ : ℤ_[ℓ]ˣ) : ℤ_[ℓ]) := by
  haveI : NeZero ((ℓ : ℕ) : F) := ⟨hℓ⟩
  haveI : ∀ i, HasEnoughRootsOfUnity F (ℓ ^ i) := fun i => inferInstance
  refine PadicInt.ext_of_toZModPow.mp fun k => ?_
  have hk : (((ℓ ^ k : ℕ) : ℤ) : F) ≠ 0 := by push_cast; exact pow_ne_zero k hℓ
  rw [toZModPow_coe_galoisDet_of_natCast_ne_zero h2 hℓ σ k,
    galoisDetMod_n_apply_eq_galoisModularCyclotomicChar σ h2 hk,
    galoisCyclotomicChar_toZModPow]

open Classical in
/-- **`det ρ_{E,ℓ}(σ) = χ_ℓ(σ)` in `ℤ_[ℓ]ˣ`.**  `Units.ext` on the previous statement; the unit
layer is separated for the reason `EllipticCurves.FunctionField.WeilPairingDeterminantCharacterN`
separates its own, namely that `PadicInt.ext_of_toZModPow` lives in `ℤ_[ℓ]` and not in its units. -/
theorem galoisDet_apply_eq_galoisCyclotomicChar (h2 : (2 : F) ≠ 0) (hℓ : (ℓ : F) ≠ 0)
    (σ : F ≃ₐ[S] F) :
    galoisDet (W' := W') (F := F) (ℓ := ℓ) σ = galoisCyclotomicChar S F ℓ σ :=
  Units.ext (coe_galoisDet_eq_coe_galoisCyclotomicChar h2 hℓ σ)

open Classical in
/-- **`det ρ_{E,ℓ} = χ_ℓ`**, Silverman *AEC* III.8.1(a), (b) and (d) assembled over the `ℓ`-power
tower, as an identity of monoid homomorphisms `(F ≃ₐ[S] F) →* ℤ_[ℓ]ˣ`, at every prime `ℓ` with
`(2 : F) ≠ 0` and `(ℓ : F) ≠ 0` over an algebraically closed `F`.

⚠️ **This is the `ℓ`-adic statement that
`EllipticCurves.FunctionField.WeilPairingDeterminantCharacterN` lists as out of scope and
`EllipticCurves.Galois.CyclotomicCharacter` calls a well-formed proposition that is not proved.**
Nothing but `σ` is quantified away: no basis, no coherent system, no matrix and no pairing appears
in the statement. -/
theorem galoisDet_eq_galoisCyclotomicChar (h2 : (2 : F) ≠ 0) (hℓ : (ℓ : F) ≠ 0) :
    galoisDet (W' := W') (F := F) (ℓ := ℓ) = galoisCyclotomicChar S F ℓ :=
  MonoidHom.ext fun σ => galoisDet_apply_eq_galoisCyclotomicChar h2 hℓ σ

open Classical in
/-- **`det ρ_{E,2} = χ_2`**, the `ℓ = 2` instance of the headline.

`galoisDetTwo` is `galoisDet` at `ℓ = 2` definitionally, so this costs nothing beyond supplying
`(2 : F) ≠ 0` twice — once as the standing characteristic hypothesis of the Weil-pairing front and
once as `(ℓ : F) ≠ 0`.  ⚠️ **It is stated under its own name because the two files that call this
identification unproved both spell it `galoisDetTwo`**, so a reader checking whether the claim is
still live greps for that and not for `galoisDet`.

⚠️ Unlike `galoisDetMod 2 = χ_2`, which is content-free because `(ZMod 2)ˣ` is a subsingleton, this
is not: `ℤ_[2]ˣ` is infinite. -/
theorem galoisDetTwo_eq_galoisCyclotomicChar (h2 : (2 : F) ≠ 0) :
    galoisDetTwo (W' := W') (F := F) = galoisCyclotomicChar S F 2 :=
  galoisDet_eq_galoisCyclotomicChar h2 h2

open Classical in
/-- **If `χ_ℓ(σ) ≠ 1` then `det ρ_{E,ℓ}(σ) ≠ 1`.**

The form in which the identity has arithmetic consequences.  ⚠️ **It produces no such `σ`**: the
only non-triviality witness on this board is `exists_galoisModularCyclotomicChar_three_ne_one`
(`#947`), which is about the single index `3` over `AlgebraicClosure ℚ` and has no `ℓ`-adic twin.
This lemma is therefore stated and not fired, exactly as
`galoisDetMod_n_ne_one_of_galoisModularCyclotomicChar_ne_one` is at the finite level. -/
theorem galoisDet_ne_one_of_galoisCyclotomicChar_ne_one {σ : F ≃ₐ[S] F} (h2 : (2 : F) ≠ 0)
    (hℓ : (ℓ : F) ≠ 0) (hσ : galoisCyclotomicChar S F ℓ σ ≠ 1) :
    galoisDet (W' := W') (F := F) (ℓ := ℓ) σ ≠ 1 := by
  rw [galoisDet_apply_eq_galoisCyclotomicChar h2 hℓ σ]
  exact hσ

/-! ### Non-vacuity

The curve is this front's standard certificate curve, `y² + y = x³` over `ℚ` base-changed to
`AlgebraicClosure ℚ`, with **`S = ℚ` and not `S = F`** — over `S = F` the group `Gal(F/S)` is
trivial and a certificate about a Galois *representation* says nothing.  This block declares no
fixture of its own (`#1408`), and it is the block
`EllipticCurves.FunctionField.WeilPairingDeterminantCharacterN`'s own `section Nonvacuity` is the
model for: that file commits the mod-`n` headline on this same curve at `n = 5`, and this one
commits the `ℓ`-adic headline above it at `ℓ = 5` and `ℓ = 2`.

⚠️ **It says nothing about either side being non-trivial**, exactly as the sibling's block
docstring says of its own: `galoisDet_ne_one_of_galoisCyclotomicChar_ne_one` is stated above and
never fired, because `#947`'s witness is at the single index `3` over `AlgebraicClosure ℚ` and has
no `ℓ`-adic twin.  What the two `example`s price is the **hypothesis set** — that
`[IsAlgClosed F]`, `[W'.IsElliptic]`, `[Fact ℓ.Prime]`, `(2 : F) ≠ 0` and `(ℓ : F) ≠ 0` are
simultaneously inhabited, which nothing in the import closure of this file witnessed before.

⚠️ `Fact (Nat.Prime 5)` is discharged by `by decide` and not by `norm_num`: `norm_num`'s primality
extension is not in this file's import closure. -/

section Nonvacuity

open EllipticCurves.Fixture

private lemma exampleTwo : (2 : AlgClosedQ) ≠ 0 := two_ne_zero

/-- The index condition `(ℓ : F) ≠ 0` at `ℓ = 5` over a field of characteristic `0`. -/
private lemma exampleFive : ((5 : ℕ) : AlgClosedQ) ≠ 0 := by
  have h : ((5 : ℕ) : AlgClosedQ) = 5 := by push_cast; ring
  rw [h]; norm_num

private instance : Fact (Nat.Prime 5) := ⟨by decide⟩

open Classical in
/-- **⚠️ THE CERTIFICATE FOR THE HEADLINE**: `det ρ_{E,5} = χ_5` on a curve that exists, with both
sides written out.  Unconditional. -/
example : galoisDet (W' := y2AddYEqX3 ℚ) (F := AlgClosedQ) (ℓ := 5)
    = galoisCyclotomicChar ℚ AlgClosedQ 5 :=
  galoisDet_eq_galoisCyclotomicChar exampleTwo exampleFive

open Classical in
/-- **The `ℓ = 2` instance under its own name**, on the same curve — the sentence
`EllipticCurves.TateModule.Determinant` and `EllipticCurves.Galois.CyclotomicCharacter` used to call
unproved, instantiated. -/
example : galoisDetTwo (W' := y2AddYEqX3 ℚ) (F := AlgClosedQ)
    = galoisCyclotomicChar ℚ AlgClosedQ 2 :=
  galoisDetTwo_eq_galoisCyclotomicChar exampleTwo

end Nonvacuity

end WeierstrassCurve.Affine
