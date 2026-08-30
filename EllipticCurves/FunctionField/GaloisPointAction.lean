/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import EllipticCurves.FunctionField.WeilPairingCyclotomic
import EllipticCurves.TateModule.GaloisAction

/-!
# The Galois action on points is the Galois action of the Weil-pairing statements

There are two Galois actions on the points of `W⁄F` in this development, and until this file
nothing connected them.

* The **`FunctionField` front** never mentions the point group.  Every Weil-pairing equivariance
  statement — `WeilPairingGalois`, `WeilPairingGaloisMu`, `WeilPairingGaloisDivisor`,
  `WeilPairingGaloisPoint`, `WeilPairingCyclotomic` — writes the `σ`-image of an affine point as
  raw coordinates, through
  `equation_algEquiv σ h₂ : (W⁄F).Equation (σ x₂) (σ y₂)`
  (`EllipticCurves.FunctionField.GaloisFunctionField`).
* The **`TateModule` front** acts on the point *group*: `Point.instSMulAlgEquiv` gives
  `σ • P = Point.map (σ : F →ₐ[S] F) P`, a `DistribMulAction` of `Gal(F/S) = F ≃ₐ[S] F` on
  `(W⁄F).Point` (`EllipticCurves.TateModule.GaloisAction`).  *This* is the action `galoisRep`,
  `galoisRepMod`, `galoisDetTwo` and the whole `ρ_ℓ` stack are built from.

The bridge is `Point.galois_smul_some`: on an affine point the abstract `DistribMulAction` acts by
applying `σ` to both coordinates, which is exactly what the Weil-pairing statements assume.  It
holds by `rfl`, because `Point.map` is definitional on `some`-points and the two nonsingularity
proofs agree by proof irrelevance.

## Main statements

* `WeierstrassCurve.Affine.CoordinateRing.nonsingular_algEquiv` — the `Nonsingular` twin of the
  merged `equation_algEquiv`: the `σ`-image of a nonsingular point is nonsingular.  Independently
  useful; it is what has been missing every time a `FunctionField` statement wanted a *point*
  rather than an equation.
* **`WeierstrassCurve.Affine.Point.galois_smul_some`** — the headline,
  `σ • Point.some x y h = Point.some (σ x) (σ y) (nonsingular_algEquiv σ h)`.
* `WeierstrassCurve.Affine.Point.galois_smul_some_eq_some_iff` — its useful form: `σ` carries the
  affine point `(x, y)` to `(x', y')` if and only if `x' = σ x` and `y' = σ y`.
* `WeierstrassCurve.Affine.Point.mem_torsion_galois_smul_some` — the coordinate form of torsion
  preservation.  The group-level statement is already available from the merged
  `Point.galois_smul_nsmul`; this is the form a Weil-pairing consumer wants, since `weilPairingMu`
  is indexed by `Equation`s and not by group elements.
* `WeierstrassCurve.Affine.CoordinateRing.galoisPoint_pointClosedPoint_smul` — the closed-point map
  `E(F) ∖ {O} → HeightOneSpectrum F[W⁄F]` is `Gal(F/S)`-equivariant **for the action `ρ` uses**.
* `WeierstrassCurve.Affine.CoordinateRing.weilPairingMu_galois_smul_of_divisor_eq_single_pow` — the
  payoff: `e_n(σS, σT) = e_n(S, T) ^ χ_n(σ)` with the two `σ`-images supplied as `σ • P = Q`
  instead of as `equation_algEquiv`.  One restatement, to demonstrate that the bridge carries
  load; the raw `equation_algEquiv` forms must keep existing, since the producer lemmas take them.

`σ • 0 = 0` is not restated: it is `smul_zero σ`, from the merged `DistribMulAction` instance.

## What this does *not* close

**`det ρ_{E,2} = χ_2` is not proved and gets no closer to being proved.**  What is removed here is
a *formal* obstruction — before this file the two sides of that identity were literally about
different functions, so the implication could not be started.  The mathematical content still
needs rung 5 (`#418`; discharged over `F̄` by `PullbackPrincipalityTwo`/`Three`, open over a
general field), the alternating property (`#465` deliverable 2) and
non-degeneracy — which is **not** Ward-gated; `WeilPairing`'s scope section is the canonical account
of what it consumes (`#769`).  Divisor-slot bilinearity has come off that list: it is merged
as `WeilPairingAntisymmetric` (`#723`), together with antisymmetry, on `[Field F]` and
`[W.IsElliptic]` alone — all it wants beyond those is the production of
`g_{S ⊕ S'} = g_S · g_{S'} · w`, which ⚠️ is **rung 5 only, never rung 4**, and is produced in
`EllipticCurves.FunctionField.WeilPairingProductRelation` (`#845`).  Nothing here says
anything about the image of `ρ` or of `χ`, and nothing here handles closed points of degree `> 1`:
`pointClosedPoint` covers the rational slice, which is where the pairing's divisors live.

## References

* [J. Silverman, *The arithmetic of elliptic curves*][silverman2009], III.7, III.8.1(e), III.8.3.
-/

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum

namespace WeierstrassCurve.Affine

variable {S F : Type*} [Field S] [Field F] [Algebra S F] {W : Affine S}

namespace CoordinateRing

/-- **The `σ`-image of a nonsingular point is nonsingular.**  The exact `Nonsingular` twin of
`equation_algEquiv`, proved the same way: transport along the injective `(σ : F →+* F)` with
`map_nonsingular`, then undo the base change with `baseChange_map_algEquiv`, which is where the
hypothesis that `σ` is an `S`-algebra map (so fixes the coefficients of `W⁄F`) is used.

The namespace is inherited from `equation_algEquiv`, not from any use of the coordinate ring:
these two are looked up together, and splitting them would hide one from anyone who found the
other. -/
lemma nonsingular_algEquiv (σ : F ≃ₐ[S] F) {x y : F} (h : (W⁄F).Nonsingular x y) :
    (W⁄F).Nonsingular (σ x) (σ y) := by
  have h2 := (WeierstrassCurve.Affine.map_nonsingular (W := W⁄F) (f := (σ : F →+* F))
    (EquivLike.injective σ) x y).mpr h
  rwa [baseChange_map_algEquiv] at h2

end CoordinateRing

namespace Point

open CoordinateRing

variable [DecidableEq F]

/-- **The two Galois actions agree.**  The `DistribMulAction` of `Gal(F/S)` on `(W⁄F).Point` that
`ρ_ℓ` is built from acts on an affine point by applying `σ` to both coordinates — which is the
action every Weil-pairing equivariance statement assumes, phrased there as `equation_algEquiv`.

It is `rfl`: `galois_smul_def` unfolds `σ • P` to `Point.map (σ : F →ₐ[S] F) P`, `Point.map_some`
is `rfl`, and the nonsingularity proof `Point.map` produces is definitionally
`nonsingular_algEquiv σ h` by proof irrelevance. -/
@[simp] lemma galois_smul_some (σ : F ≃ₐ[S] F) {x y : F} (h : (W⁄F).Nonsingular x y) :
    σ • (Point.some x y h) = Point.some (σ x) (σ y) (nonsingular_algEquiv σ h) :=
  rfl

/-- `σ` carries the affine point `(x, y)` to the affine point `(x', y')` exactly when `x' = σ x`
and `y' = σ y`.  This is the form the bridge is consumed in: a hypothesis `σ • P = Q` about
abstract points becomes an equation between coordinates, which is what the `FunctionField` side
speaks. -/
lemma galois_smul_some_eq_some_iff (σ : F ≃ₐ[S] F) {x y x' y' : F}
    (h : (W⁄F).Nonsingular x y) (h' : (W⁄F).Nonsingular x' y') :
    σ • (Point.some x y h) = Point.some x' y' h' ↔ x' = σ x ∧ y' = σ y := by
  rw [galois_smul_some]
  simp only [Point.some.injEq]
  exact ⟨fun ⟨hx, hy⟩ => ⟨hx.symm, hy.symm⟩, fun ⟨hx, hy⟩ => ⟨hx.symm, hy.symm⟩⟩

/-- **Torsion preservation, in coordinates.**  The group-level statement is the merged
`galois_smul_nsmul` (and the `SMul` instance on `(W⁄F).torsion n` it supports); this is the same
fact for a point presented by its coordinates, which is the shape a Weil-pairing consumer needs,
since `weilPairingMu` is indexed by `Equation`s rather than by elements of the point group. -/
lemma mem_torsion_galois_smul_some (σ : F ≃ₐ[S] F) {x y : F} (h : (W⁄F).Nonsingular x y) {n : ℕ}
    (hP : Point.some x y h ∈ (W⁄F).torsion n) :
    Point.some (σ x) (σ y) (nonsingular_algEquiv σ h) ∈ (W⁄F).torsion n := by
  rw [← galois_smul_some σ h, mem_torsion_iff, ← galois_smul_nsmul, mem_torsion_iff.mp hP,
    smul_zero]

end Point

namespace CoordinateRing

open Point

variable [W.IsElliptic] [DecidableEq F]

omit [W.IsElliptic] in
/-- **The closed-point map is `Gal(F/S)`-equivariant for the action `ρ` uses.**  If `σ` carries the
affine point `(x, y)` to `(x', y')`, then `galoisPoint σ` carries the closed point of the first to
the closed point of the second.

This is `galoisPoint_pointClosedPoint` (`#635`) with its `equation_algEquiv` hypothesis replaced by
point data, and it is the form a divisor-level computation of `det ρ` needs: `galoisPoint` is what
acts on `divisor`, and `σ •` is what acts on `E(F)`.

⚠️ **`[W.IsElliptic]` is `omit`ted rather than absent from the section.**  It is on the `variable`
line above because the rest of this section needs it; this theorem does not, and it did not before
either — what changed is that `galoisPoint_pointClosedPoint`
(`EllipticCurves.FunctionField.GaloisClosedPoint`) dropped a dead `[W.IsElliptic]` in `#1272`, so
the instance stopped being reachable through the one step this proof takes and the
`unusedSectionVars` linter began reporting it.  The `omit` is the linter's own suggested repair. -/
theorem galoisPoint_pointClosedPoint_smul (σ : F ≃ₐ[S] F) {x y x' y' : F}
    (h : (W⁄F).Nonsingular x y) (h' : (W⁄F).Nonsingular x' y')
    (hP : σ • (Point.some x y h) = Point.some x' y' h') :
    galoisPoint σ (pointClosedPoint h.1) = pointClosedPoint h'.1 := by
  obtain ⟨rfl, rfl⟩ := (galois_smul_some_eq_some_iff σ h h').mp hP
  exact galoisPoint_pointClosedPoint σ h.1

/-- The `Nonsingular`-indexed form of the previous theorem is not a new statement: by proof
irrelevance `(nonsingular_algEquiv σ h).1` *is* `equation_algEquiv σ h.1`, so it is the merged
`galoisPoint_pointClosedPoint` verbatim, and giving it a second name would be duplication. -/
example (σ : F ≃ₐ[S] F) {x y : F} (h : (W⁄F).Nonsingular x y) :
    galoisPoint σ (pointClosedPoint h.1) = pointClosedPoint (nonsingular_algEquiv σ h).1 :=
  galoisPoint_pointClosedPoint σ h.1

open Classical in
/-- **`e_n(σS, σT) = e_n(S, T) ^ χ_n(σ)`, with the Galois action taken on points.**

`weilPairingMu_galois_of_divisor_eq_single_pow` (`#638`) states this with both `σ`-images written
as `equation_algEquiv`.  Here they arrive instead as `σ • P₂ = P₂'` and `σ • P₃ = P₃'` — the action
`ρ_{E,ℓ}` is built from — so a consumer holding a Galois-equivariance statement about the
representation can feed it to the pairing directly.

One restatement is deliberate: the point is to show the bridge carries load, not to duplicate the
`FunctionField` API.  The `equation_algEquiv` forms stay, since the producer lemmas take them. -/
theorem weilPairingMu_galois_smul_of_divisor_eq_single_pow (σ : F ≃ₐ[S] F)
    {x₂ y₂ x₂' y₂' x₃ y₃ x₃' y₃' : F}
    (h₂ : (W⁄F).Nonsingular x₂ y₂) (h₂' : (W⁄F).Nonsingular x₂' y₂')
    (h₃ : (W⁄F).Nonsingular x₃ y₃) (h₃' : (W⁄F).Nonsingular x₃' y₃')
    (hP₂ : σ • (Point.some x₂ y₂ h₂) = Point.some x₂' y₂' h₂')
    (hP₃ : σ • (Point.some x₃ y₃ h₃) = Point.some x₃' y₃' h₃')
    {g g' : (W⁄F).FunctionField} {m : ℤ} {n : ℕ} [NeZero n]
    (hn : Nat.card { x // x ∈ rootsOfUnity n F } = n) (hg : g ≠ 0) (hg' : g' ≠ 0)
    (hgdiv : divisor (W⁄F) g = Finsupp.single (pointClosedPoint h₃.1) m)
    (hg'div : divisor (W⁄F) g' = Finsupp.single (pointClosedPoint h₃'.1) m)
    (hpow : weilPairingElt h₂.1 g ^ n = 1)
    (hpow' : weilPairingElt h₂'.1 g' ^ n = 1) :
    weilPairingMu h₂'.1 hpow'
      = weilPairingMu h₂.1 hpow ^ ((galoisModularCyclotomicChar S F hn σ : ZMod n)).val := by
  obtain ⟨rfl, rfl⟩ := (galois_smul_some_eq_some_iff σ h₂ h₂').mp hP₂
  obtain ⟨rfl, rfl⟩ := (galois_smul_some_eq_some_iff σ h₃ h₃').mp hP₃
  exact weilPairingMu_galois_of_divisor_eq_single_pow σ h₂.1 h₃.1 hn hg hg' hgdiv hg'div hpow hpow'

end CoordinateRing

end WeierstrassCurve.Affine
