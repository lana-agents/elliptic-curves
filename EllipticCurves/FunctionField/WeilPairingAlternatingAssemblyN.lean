/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import EllipticCurves.Fixtures
import EllipticCurves.FunctionField.MulByNComposition
import EllipticCurves.FunctionField.MulByNXCoordFormula
import EllipticCurves.FunctionField.WeilPairingAlternatingMu
import EllipticCurves.FunctionField.WeilPairingAlternatingWorkhorseN
import EllipticCurves.FunctionField.WeilPairingTelescopeN
import EllipticCurves.Torsion.NsmulSmoothSurjective
import EllipticCurves.Torsion.TwoTorsionOrder

/-!
# The alternating property at general `n`: `e_n(T, T) = 1`, assembled

Silverman *AEC* III.8.1(b).  `EllipticCurves.FunctionField.WeilPairingAlternating{Two,Three}` are
the merged numeral cases; this file is the assembly at an arbitrary `n`, and both of them are
recovered from it, verbatim.

`#1327` split the general-`n` alternating argument into two gates that do not depend on each other.
Both are now merged, and this file is the join:

* **gate A, the divisor telescope** — `f` with `div f = n(T) − n(O)` and
  `∏_{i<n} τ_{[i]T}∗ f = c ∈ F∖{0}`, from `exists_prod_translatePointEndo_eq_algebraMap`
  (`EllipticCurves.FunctionField.WeilPairingTelescopeN`);
* **gate B, the workhorse** — `τ_T∗ g = g` from that product and an `n`-th root `g` of `[n]∗ f`,
  from `translatePointEndo_eq_self_of_prod_eq_of_pow_eq`
  (`EllipticCurves.FunctionField.WeilPairingAlternatingWorkhorseN`).

Between them the argument is the merged `n = 2` proof with three names changed: the `#418` datum
`hprin` produces `g`, `exists_smul_pow_eq_of_nsmul_divisor` turns `n • div g = div ([n]∗ f)` into
`u • gⁿ = [n]∗ f`, `isUnit_iff_exists_eq_algebraMap` says the unit `u` is a nonzero constant, gate B
gives `τ_T∗ g = g`, and `weilPairingElt_self_of_translateEndo_fixed` reads off `e_n(T, T) = 1`.
Every one of those five was already general in `n`; only the two gates were missing.

## ⚠️ The core needs no `[IsAlgClosed F]`, and that is not a technicality

`WeilPairingAlternatingBaseChange`'s docstring establishes that `[IsAlgClosed F]` reaches this front
by **two** independent routes: `hprin`, and the halving point `P` with `[n]P = T`.  At `n = 2` and
`n = 3` the halving point is produced *inside* the assembly, which is why both merged headlines
carry `[IsAlgClosed F]`.

Gate B takes `{P T : W.Point} (hPT : n • P = T)` with `P` **not required to be affine** and no
`[IsAlgClosed F]` anywhere.  So `exists_weilPairingElt_self_eq_one_of_hprin_n` below takes the
halving point as a hypothesis and is stated over an **arbitrary field**, and
`…_of_algClosed` discharges it.  That layering matches
`translateEndo_eq_self_of_mul_algebraMap_sq_eq` (core, arbitrary field, halving point explicit)
against its `_of_baseChange` form, and it is what leaves the base-change descent a separate piece of
work rather than a rewrite of this one.

## ⚠️ Where the `n = 5` gate on the algebraically closed corollary was — it is GONE

Every other `_of_smooth` corollary on this front stops at `n = 5` because the *transcendence*
`Transcendental F (n • 𝒫).xCoord` is only available at `3`-smooth `n`.  **That is not the reason
here.**  Over `F̄` the transcendence is `transcendental_xCoord_nsmul_of_isAlgClosed`, which is
general in `n ≠ 0` and needs no `3`-smoothness and no `(3 : F) ≠ 0`.  The `3`-smoothness enters in
exactly one place, `exists_nsmul_eq_of_smooth` (`EllipticCurves.Torsion.NsmulSmoothSurjective`),
which is what produces the halving point.  A general-`n` surjectivity of `[n]` on `E(F̄)` would
lift this corollary to every `n` with nothing else changing.  ⚠️ **This sentence used to name that
surjectivity as missing, via `#251`'s coordinate formula, and it is not missing**:
`nsmul_surjective_of_two_ne_zero` (`EllipticCurves.Torsion.TwoTorsionOrder`) is `[n]`-surjectivity
on `E(F̄)` at every `n ≠ 0` over a field with `(2 : F) ≠ 0`, off the now-closed `#251`
(`hasXCoordFormula_of_two_ne_zero`, `EllipticCurves.Torsion.NsmulOrder`).

⚠️ **The swap is measured now (`#1549` group 2), and it costs nothing.**
`…_of_algClosed_of_ne_zero` and its `μ` twin below are the `_of_algClosed` pair with `hfac`
deleted and **no index condition put in its place** — no `h3`, no `((n : ℤ) : F) ≠ 0`, no extra
instance.  ⚠️ This is the only place on this front where the general layer is free, precisely
because the transcendence over `F̄` never needed `natDegree_ΨSq`.  The `_of_smooth` forms are kept:
`exists_nsmul_eq_of_smooth` halves by iterated `2`- and `3`-descent and consumes no division
polynomial, while `nsmul_surjective_of_two_ne_zero` runs through the `ΨSq`-root dictionary, so the
two are independent routes and the `example`s below compile the containment.

## ⚠️ The other `n = 5` gate is somewhere else, and one of the two is now GONE

`exists_weilPairingElt_self_eq_one_of_hprin_n_of_smooth` is the arbitrary-field companion of the
corollary above, with the transcendence discharged and the halving point still a hypothesis.  For
*that* statement the unreachable `n = 5` **was** the transcendence — as it was for every other
`_of_smooth` statement on this front.  So the two corollaries below consume `hfac` in *opposite*
places, and a reader who carries the paragraph above across to the `_of_smooth` form will get it
exactly backwards.  Each statement says which is which.

⚠️ **And that half is paid** (`#1549`): `exists_weilPairingElt_self_eq_one_of_hprin_n_of_ne_zero`
below is the arbitrary-field statement at every `n` with `((n : ℤ) : F) ≠ 0`, off
`transcendental_xCoord_nsmul_genericPoint_of_intCast_ne_zero`
(`EllipticCurves.FunctionField.MulByNXCoordFormula`), and the `_of_smooth` form is a corollary of it
— compiled in the `example` beside it, not asserted.

⚠️ **The `_of_algClosed` pair is now paid too, by group 2 of the same issue, and it is a different
payment**: its `hfac` is the *halving point*, and replacing that costs no index hypothesis at all,
whereas replacing the transcendence costs `((n : ℤ) : F) ≠ 0`.  So the two halves of this file come
off `3`-smoothness at **different prices**, and a reader who carries one across to the other will
overstate the arbitrary-field reach.  Each statement says which is which.

## Main results

* **`WeierstrassCurve.Affine.exists_weilPairingElt_self_eq_one_of_hprin_n`** — over an arbitrary
  field, with `hprin` and the halving point as hypotheses;
* **`WeierstrassCurve.Affine.exists_weilPairingElt_self_eq_one_of_hprin_n_of_smooth`** — the same
  over an arbitrary field at `3`-smooth `n ≠ 0`, with the transcendence discharged;
* **`WeierstrassCurve.Affine.exists_weilPairingElt_self_eq_one_of_hprin_n_of_ne_zero`** — the same
  over an arbitrary field at every `n` with `((n : ℤ) : F) ≠ 0` (`#1549`), the transcendence
  coming from `transcendental_xCoord_nsmul_genericPoint_of_intCast_ne_zero`
  (`EllipticCurves.FunctionField.MulByNXCoordFormula`); ⚠️ the `_of_smooth` form above is a
  corollary of it, compiled in the `example` beside them;
* **`WeierstrassCurve.Affine.exists_weilPairingElt_self_eq_one_of_hprin_n_of_algClosed`** — over
  `F̄` at every `3`-smooth `n ≠ 0`, with `hprin` the only hypothesis left; its `hfac` is the halving
  point rather than the transcendence;
* **`WeierstrassCurve.Affine.exists_weilPairingElt_self_eq_one_of_hprin_n_of_algClosed_of_ne_zero`**
  — the same over `F̄` at **every** `n ≠ 0` (`#1549` group 2), the halving point coming from
  `nsmul_surjective_of_two_ne_zero` (`EllipticCurves.Torsion.TwoTorsionOrder`).  ⚠️ Despite the
  `_of_ne_zero` suffix this one takes **no** `((n : ℤ) : F) ≠ 0`: the suffix marks the general layer
  on this front, and here `n ≠ 0` is the whole of it.  The `_of_algClosed` form above is a corollary
  of it, compiled in the `example` beside them;
* **`WeierstrassCurve.Affine.exists_weilPairingMu_self_eq_one_of_hprin_n`**,
  **`…_of_hprin_n_of_algClosed`** and **`…_of_hprin_n_of_algClosed_of_ne_zero`** — the
  `μ_m(F)`-valued twins of the first, fourth and fifth, in the shape
  `exists_weilPairingMu_self_eq_one_of_hprin_two`
  (`EllipticCurves.FunctionField.WeilPairingAlternatingBaseChange`) has at `n = 2`.  ⚠️ Their index
  `m` is arbitrary and **need not equal `n`**: the witness is manufactured from `1 ^ m = 1`, so the
  statement is the group identity of `μ_m(F)` for whichever `m` the caller packaged the value in,
  not a claim that `e_n` lands in `μ_m`.

## Imports, measured rather than preferred

`WeilPairingAlternatingMu` costs **3** further project modules in this file's closure
(`…Mu`, `WeilPairingBilinearMu`, `WeilPairingRootsOfUnity`) and `MulByNComposition` costs **12**
more, all of which `EllipticCurves.FunctionField.WeilPairingAlternatingConsumerN` already builds.
Neither cycles — nothing imports this file.  That is why the `μ` forms and the `_of_smooth`
corollary live here rather than in a sibling module: a split would have bought a smaller closure for
a file that is a leaf, at the price of separating four statements about one theorem.

## ⚠️ `open Classical in`, and why the `[DecidableEq F]` binder is *not* used here

`WeilPairingTelescopeN` found that a general statement mentioning `i • P` should take
`[DecidableEq F]` as an instance **binder** rather than being elaborated `open Classical in`, so
that a certificate over a field with its own `DecidableEq` instance costs no `convert`.  That
finding is right and this file is the first place it does not apply, for two reasons worth stating
so the next author does not re-litigate it:

* gate B is elaborated `open Classical in`, so its `htel` and `hPT` are Classical-fixed.  A binder
  form here would have to transport both across `Subsingleton.elim` at every use — the binder pays
  only once gate B is restated, not before;
* both statements this file must recover are themselves `open Classical in`
  (`WeilPairingAlternatingTwo:276`, `WeilPairingAlternatingThree:311`), and the certificate is over
  `AlgebraicClosure ℚ`, which carries **no** `DecidableEq` instance — so there is no competing
  instance for a binder to be polymorphic over.  The certificate below costs zero `convert`s as it
  stands.

The general lesson is narrower than "prefer the binder": **the binder is right for a *producer*, and
`open Classical in` for a *consumer* of a `Classical`-fixed statement.**  Gate B fixes the instance,
so a binder here does not remove the `convert`s — it moves them under a `Finset.prod` binder, which
is worse.  Retrofitting gate B with the binder would make both free, and that retrofit belongs to
gate B.  The `F̄` reading — *the binder pays exactly when a consumer over a field with a competing
`DecidableEq` instance exists* — is the special case of this that the `AlgebraicClosure ℚ`
certificate below exhibits: there is no competing instance there, so the binder would buy nothing.

⚠️ The `ℚ` certificate at the end of the file is the *other* case, and it is the one that pins the
rule down: `ℚ` does have a competing instance, `instDecidableEqRat`, which wins on priority even
under `open Classical`, so that block pays exactly two `convert`s.  Writing `open Classical in` on
its lemmas is a **no-op** for the same priority reason, and would hide the cost rather than remove
it.

## What is *not* here

* **`hprin`, the `#418` datum** — carried as a hypothesis at both levels, exactly as the merged
  `n = 2` and `n = 3` headlines carry it.  `EllipticCurves.FunctionField.PullbackPrincipalityTwo`
  discharges it at `n = 2` over `F̄`; at general `n` nothing does, and `#962` records the general
  field case.  ⚠️ This is the last real gate on the alternating front — do not read this file as
  "alternating at general `n` is unconditional".
* **The base-change descent**, i.e. dropping the halving-point hypothesis over an arbitrary field
  the way `translateEndo_eq_self_of_mul_algebraMap_sq_eq_of_baseChange` does at `n = 2`.  It needs
  `functionFieldMap_mulByNEndo`, and `EllipticCurves.FunctionField.FunctionFieldBaseChange` has only
  the two numeral forms `functionFieldMap_mulByTwoEndo` and `functionFieldMap_mulByThreeEndo`.  That
  missing intertwiner is the whole of the remaining work and it is a separate piece.
* `n = 5` on the **`_of_algClosed`** corollaries — see above; the obstruction there is the halving
  point, `exists_nsmul_eq_of_smooth`, and nothing here replaces it.  ⚠️ On the arbitrary-field
  corollary `n = 5` **is** reached, by `…_of_hprin_n_of_ne_zero` (`#1549`); that obstruction was the
  transcendence and it is discharged.
* `ωₙ`, `#404`, `#251`, Ward, bilinearity, non-degeneracy.  ⚠️ Of those, `#404` and Ward are
  **closed** — `WeierstrassCurve.Affine.equation_div_of_ψ_ne_zero`
  (`EllipticCurves.Torsion.OmegaCrux`, PR #557) and
  `WeierstrassCurve.Affine.ψ_isEllipticNet` (`EllipticCurves.Torsion.WardHalving`) — so naming
  them here is a statement that this file does not use them, not that they gate anything
  (`#1460`).  ⚠️ **`#251` used to be marked open here and is closed too**
  (`hasXCoordFormula_of_two_ne_zero`, `EllipticCurves.Torsion.NsmulOrder`; `y`-half
  `nsmul_eq_some_omegaY_of_ΨSq_ne_zero`, `EllipticCurves.Torsion.NsmulYPeriodic`, `#1500`), so all
  of the list is an independence claim.  ⚠️ The `μ`-valued statements below are the *value-group
  form of this one theorem* and nothing more; `μ_n`-valuedness of `e_n` in the sense of
  `EllipticCurves.FunctionField.WeilPairingRootsOfUnity` is not re-proved here.

## References

* [J. Silverman, *The arithmetic of elliptic curves*][silverman2009], III.8.1(b).
-/

open Polynomial IsDedekindDomain

namespace WeierstrassCurve.Affine

open CoordinateRing

variable {F : Type*} [Field F] {W : Affine F} [W.IsElliptic]
  [IsDedekindDomain W.CoordinateRing] {xT yT : F}

/-! ### The assembly over an arbitrary field -/

open Classical in
/-- **`e_n(T, T) = 1` at general `n`, over an arbitrary field.**

Given the `#418` datum `hprin` — the principality of the `n`-divisible divisor `div ([n]∗ f_T)`, in
the exact shape `exists_gS_n` takes it — and a point `P` with `[n]P = T`, there are a principal
function `f_T` with `div f_T = n(T) − n(O)` and an `n`-th root `g_T` of `[n]∗ f_T` (up to a unit of
`F[W]`) with `τ_T∗ g_T = g_T`, hence `e_n(T, T) = 1`.

This is `exists_weilPairingElt_self_eq_one_of_algClosed_two`
(`EllipticCurves.FunctionField.WeilPairingAlternatingTwo`) at an arbitrary `n`, with
`[IsAlgClosed F]` traded for the explicit halving point.  ⚠️ `P` is **not** required to be affine
and no interior multiple `[i]P` or `[i]T` is either — that is what
`EllipticCurves.FunctionField.TranslationPointEndomorphism` buys, and it is why the `n = 3`
assembly's auxiliary point `Q` has no analogue in this hypothesis list.

⚠️ `hprin` is a hypothesis, not a conclusion.  It is `#418`, it is open at general `n`, and it is
the last real gate on this front. -/
theorem exists_weilPairingElt_self_eq_one_of_hprin_n {n : ℕ} (hnz : n ≠ 0)
    (hn : Transcendental F (n • genericPoint (W := W)).xCoord)
    (h : W.Nonsingular xT yT) (htors : Point.some xT yT h ∈ W.torsion n)
    {P : W.Point} (hPT : n • P = Point.some xT yT h)
    (hprin : ∀ f : W.FunctionField, f ≠ 0 →
      divisor W f = Finsupp.single (pointClosedPoint h.left) (n : ℤ) →
      ∃ g₀ : W.FunctionField, g₀ ≠ 0 ∧
        n • divisor W g₀ = divisor W (mulByNEndo n hn f)) :
    ∃ f : W.FunctionField, f ≠ 0 ∧
      divisorProj W f = Finsupp.single (some (pointClosedPoint h.left)) (n : ℤ)
          - Finsupp.single (none : ProjPoint W) (n : ℤ) ∧
        ∃ g : W.FunctionField, g ≠ 0 ∧
          (∃ u : W.CoordinateRingˣ, (u : W.CoordinateRing) • g ^ n = mulByNEndo n hn f) ∧
          translateEndo h.left g = g ∧ weilPairingElt h.left g = 1 := by
  obtain ⟨f, hf, hdivproj, c, hc, htel⟩ := exists_prod_translatePointEndo_eq_algebraMap h htors
  obtain ⟨g, hg, hgdiv⟩ :=
    hprin f hf (divisor_eq_single_of_divisorProj_eq_single_sub_single hdivproj)
  have hfne : mulByNEndo n hn f ≠ 0 := fun hz =>
    hf ((mulByNEndo n hn).injective (by rw [hz, map_zero]))
  obtain ⟨u, hu⟩ := exists_smul_pow_eq_of_nsmul_divisor hfne hg hgdiv
  obtain ⟨c₀, hc₀, hueq⟩ := isUnit_iff_exists_eq_algebraMap.mp u.isUnit
  have hpow : algebraMap F W.FunctionField c₀ * g ^ n = mulByNEndo n hn f := by
    rw [← hu, Algebra.smul_def, hueq, ← IsScalarTower.algebraMap_apply]
  have htinv : translateEndo h.left g = g := by
    have key := translatePointEndo_eq_self_of_prod_eq_of_pow_eq hnz hn hPT hg hc hc₀ htel hpow
    rwa [show Point.some xT yT h = torsionPoint h.left from rfl,
      translatePointEndo_torsionPoint] at key
  exact ⟨f, hf, hdivproj, g, hg, ⟨u, hu⟩, htinv,
    weilPairingElt_self_of_translateEndo_fixed h.left hg htinv⟩

open Classical in
/-- **`e_n(T, T) = 1` at general `n` in the value group `μ_m(F)`, over an arbitrary field.**

The `μ`-valued twin of `exists_weilPairingElt_self_eq_one_of_hprin_n`, and the general-`n` form of
`exists_weilPairingMu_self_eq_one_of_hprin_two`
(`EllipticCurves.FunctionField.WeilPairingAlternatingBaseChange`).

`weilPairingMu` is indexed by a proof that the pairing element is an `m`-th root of unity, so the
statement *produces* one rather than taking it; that costs nothing, because the `Elt`-level theorem
already gives `e_n(T, T) = 1` and `1 ^ m = 1`.

⚠️ **The index `m` is arbitrary and need not equal `n`.**  This is the group identity of `μ_m(F)`
for whichever `m` the caller has packaged the value in — it is *not* a claim that `e_n` lands in
`μ_m` for `m ≠ n`.  Both merged `μ`-valued assemblies say the same of themselves, and the reason is
the same: the root-of-unity witness is manufactured from `1 ^ m = 1`, which knows nothing about
`n`. -/
theorem exists_weilPairingMu_self_eq_one_of_hprin_n {n : ℕ} (hnz : n ≠ 0)
    (hn : Transcendental F (n • genericPoint (W := W)).xCoord)
    (h : W.Nonsingular xT yT) (htors : Point.some xT yT h ∈ W.torsion n)
    {P : W.Point} (hPT : n • P = Point.some xT yT h)
    (hprin : ∀ f : W.FunctionField, f ≠ 0 →
      divisor W f = Finsupp.single (pointClosedPoint h.left) (n : ℤ) →
      ∃ g₀ : W.FunctionField, g₀ ≠ 0 ∧
        n • divisor W g₀ = divisor W (mulByNEndo n hn f))
    (m : ℕ) [NeZero m] :
    ∃ f : W.FunctionField, f ≠ 0 ∧
      divisorProj W f = Finsupp.single (some (pointClosedPoint h.left)) (n : ℤ)
          - Finsupp.single (none : ProjPoint W) (n : ℤ) ∧
        ∃ g : W.FunctionField, g ≠ 0 ∧
          (∃ u : W.CoordinateRingˣ, (u : W.CoordinateRing) • g ^ n = mulByNEndo n hn f) ∧
          ∃ hpow : weilPairingElt h.left g ^ m = 1, weilPairingMu h.left hpow = 1 := by
  obtain ⟨f, hf, hdivproj, g, hg, hu, htinv, halt⟩ :=
    exists_weilPairingElt_self_eq_one_of_hprin_n hnz hn h htors hPT hprin
  exact ⟨f, hf, hdivproj, g, hg, hu, by rw [halt, one_pow],
    weilPairingMu_self_of_translateEndo_fixed h.left hg _ htinv⟩

/-! ### The assembly over an arbitrary field at `3`-smooth `n`

One hypothesis of the core is discharged here and two are not: the transcendence comes from
`transcendental_xCoord_nsmul_of_smooth`, and the halving point `hPT` and `hprin` stay.  ⚠️ Read the
placement of the `n = 5` gate carefully — it sits somewhere different here than it does one section
below. -/

open Classical in
/-- **`e_n(T, T) = 1` at every `3`-smooth `n ≠ 0`, over an arbitrary field**, with the halving point
`hPT` and `hprin` the only hypotheses beyond the setting.

The core with `hn` supplied by `transcendental_xCoord_nsmul_of_smooth`
(`EllipticCurves.FunctionField.MulByNComposition`) and nothing else changed.

⚠️ **For this corollary the unreachable `n = 5` is the transcendence**, as for every other
`_of_smooth` statement on this front: the degree tower that supplies
`Transcendental F (n • 𝒫).xCoord` manufactures no new prime.  ⚠️ **That obstruction is discharged
one theorem below** — `…_of_hprin_n_of_ne_zero` is this statement at every `n` with
`((n : ℤ) : F) ≠ 0`, and this one is a corollary of it.  It is kept as an independent route: its
transcendence consumes no division polynomial.

⚠️ Its neighbour `exists_weilPairingElt_self_eq_one_of_hprin_n_of_algClosed` stops at `5` for the
*other* reason — there the transcendence is general in `n ≠ 0` and it is the **halving point** that
needs `3`-smoothness, so nothing here moves it.  The two statements look alike and their `hfac` is
consumed in opposite places; the module docstring records why. -/
theorem exists_weilPairingElt_self_eq_one_of_hprin_n_of_smooth (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0)
    {n : ℕ} (hnz : n ≠ 0) (hfac : ∀ p ∈ n.primeFactors, p = 2 ∨ p = 3)
    (h : W.Nonsingular xT yT) (htors : Point.some xT yT h ∈ W.torsion n)
    {P : W.Point} (hPT : n • P = Point.some xT yT h)
    (hprin : ∀ f : W.FunctionField, f ≠ 0 →
      divisor W f = Finsupp.single (pointClosedPoint h.left) (n : ℤ) →
      ∃ g₀ : W.FunctionField, g₀ ≠ 0 ∧
        n • divisor W g₀
          = divisor W (mulByNEndo n (transcendental_xCoord_nsmul_of_smooth h2 h3 hnz hfac) f)) :
    ∃ f : W.FunctionField, f ≠ 0 ∧
      divisorProj W f = Finsupp.single (some (pointClosedPoint h.left)) (n : ℤ)
          - Finsupp.single (none : ProjPoint W) (n : ℤ) ∧
        ∃ g : W.FunctionField, g ≠ 0 ∧
          (∃ u : W.CoordinateRingˣ, (u : W.CoordinateRing) • g ^ n
            = mulByNEndo n (transcendental_xCoord_nsmul_of_smooth h2 h3 hnz hfac) f) ∧
          translateEndo h.left g = g ∧ weilPairingElt h.left g = 1 :=
  exists_weilPairingElt_self_eq_one_of_hprin_n hnz _ h htors hPT hprin

open Classical in
/-- **`e_n(T, T) = 1` at every `n` with `((n : ℤ) : F) ≠ 0`, over an arbitrary field**, with the
halving point still a hypothesis.

The core with `hn` supplied by `transcendental_xCoord_nsmul_genericPoint_of_intCast_ne_zero`
(`EllipticCurves.FunctionField.MulByNXCoordFormula`) rather than by the `3`-smooth degree tower,
and nothing else changed.

⚠️ **`n = 5` and `n = 10` are here**, and the `example` below derives
`exists_weilPairingElt_self_eq_one_of_hprin_n_of_smooth` from this one verbatim, so the containment
between the two layers is compiled rather than asserted.  The `_of_smooth` form is kept as an
independent route: it consumes no division polynomial.

⚠️ **The halving point is untouched.**  `hPT : n • P = T` is a hypothesis here exactly as it is in
`…_of_smooth`, and it is what the neighbouring `_of_algClosed` statements discharge — those stop at
`3`-smooth `n` for that reason and not for this one, and this theorem moves them not at all. -/
theorem exists_weilPairingElt_self_eq_one_of_hprin_n_of_ne_zero (h2 : (2 : F) ≠ 0)
    {n : ℕ} (hn : ((n : ℤ) : F) ≠ 0)
    (h : W.Nonsingular xT yT) (htors : Point.some xT yT h ∈ W.torsion n)
    {P : W.Point} (hPT : n • P = Point.some xT yT h)
    (hprin : ∀ f : W.FunctionField, f ≠ 0 →
      divisor W f = Finsupp.single (pointClosedPoint h.left) (n : ℤ) →
      ∃ g₀ : W.FunctionField, g₀ ≠ 0 ∧
        n • divisor W g₀
          = divisor W (mulByNEndo n
            (transcendental_xCoord_nsmul_genericPoint_of_intCast_ne_zero h2 hn) f)) :
    ∃ f : W.FunctionField, f ≠ 0 ∧
      divisorProj W f = Finsupp.single (some (pointClosedPoint h.left)) (n : ℤ)
          - Finsupp.single (none : ProjPoint W) (n : ℤ) ∧
        ∃ g : W.FunctionField, g ≠ 0 ∧
          (∃ u : W.CoordinateRingˣ, (u : W.CoordinateRing) • g ^ n
            = mulByNEndo n (transcendental_xCoord_nsmul_genericPoint_of_intCast_ne_zero h2 hn) f) ∧
          translateEndo h.left g = g ∧ weilPairingElt h.left g = 1 :=
  exists_weilPairingElt_self_eq_one_of_hprin_n (by rintro rfl; simp at hn) _ h htors hPT hprin

open Classical in
/-- **`…_of_smooth` is a corollary of `…_of_ne_zero`** — its statement verbatim, proved from the
general layer.  ⚠️ The two `mulByNEndo` terms carry different transcendence proofs and match only by
proof irrelevance, `Transcendental` being a `Prop`. -/
example (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) {n : ℕ} (hnz : n ≠ 0)
    (hfac : ∀ p ∈ n.primeFactors, p = 2 ∨ p = 3)
    (h : W.Nonsingular xT yT) (htors : Point.some xT yT h ∈ W.torsion n)
    {P : W.Point} (hPT : n • P = Point.some xT yT h)
    (hprin : ∀ f : W.FunctionField, f ≠ 0 →
      divisor W f = Finsupp.single (pointClosedPoint h.left) (n : ℤ) →
      ∃ g₀ : W.FunctionField, g₀ ≠ 0 ∧
        n • divisor W g₀
          = divisor W (mulByNEndo n (transcendental_xCoord_nsmul_of_smooth h2 h3 hnz hfac) f)) :
    ∃ f : W.FunctionField, f ≠ 0 ∧
      divisorProj W f = Finsupp.single (some (pointClosedPoint h.left)) (n : ℤ)
          - Finsupp.single (none : ProjPoint W) (n : ℤ) ∧
        ∃ g : W.FunctionField, g ≠ 0 ∧
          (∃ u : W.CoordinateRingˣ, (u : W.CoordinateRing) • g ^ n
            = mulByNEndo n (transcendental_xCoord_nsmul_of_smooth h2 h3 hnz hfac) f) ∧
          translateEndo h.left g = g ∧ weilPairingElt h.left g = 1 :=
  exists_weilPairingElt_self_eq_one_of_hprin_n_of_ne_zero h2
    (Nat.intCast_ne_zero_of_smooth h2 h3 hnz hfac) h htors hPT hprin

/-! ### The assembly over an algebraically closed field -/

section AlgClosed

open Classical in
/-- **`e_n(T, T) = 1` over `F̄` at every `3`-smooth `n ≠ 0`**, with `hprin` the only hypothesis
left.

Both hypotheses the core takes on top of `hprin` are discharged here:

* the transcendence, by `transcendental_xCoord_nsmul_of_isAlgClosed` — general in `n ≠ 0` over `F̄`,
  needing neither `3`-smoothness nor `(3 : F) ≠ 0`;
* the halving point, by `exists_nsmul_eq_of_smooth`
  (`EllipticCurves.Torsion.NsmulSmoothSurjective`).

⚠️ **`hfac` is consumed in the second of those and nowhere else**, so the first index this does not
reach is `n = 5` *for the halving point*, not for the transcendence — unlike every other
`_of_smooth` corollary on this front.  ⚠️ **`#1549` group 1 did not move this one**: it replaced the
transcendence, which is already general here.  Group 2 did, by replacing
`exists_nsmul_eq_of_smooth` — see `…_of_algClosed_of_ne_zero` below, which is this statement with
`hfac` deleted and nothing put in its place.  This one is kept because its halving point is an
independent route. -/
theorem exists_weilPairingElt_self_eq_one_of_hprin_n_of_algClosed [IsAlgClosed F]
    (h2 : (2 : F) ≠ 0) {n : ℕ} (hnz : n ≠ 0) (hfac : ∀ p ∈ n.primeFactors, p = 2 ∨ p = 3)
    (h : W.Nonsingular xT yT) (htors : Point.some xT yT h ∈ W.torsion n)
    (hprin : ∀ f : W.FunctionField, f ≠ 0 →
      divisor W f = Finsupp.single (pointClosedPoint h.left) (n : ℤ) →
      ∃ g₀ : W.FunctionField, g₀ ≠ 0 ∧
        n • divisor W g₀
          = divisor W (mulByNEndo n (transcendental_xCoord_nsmul_of_isAlgClosed h2 hnz) f)) :
    ∃ f : W.FunctionField, f ≠ 0 ∧
      divisorProj W f = Finsupp.single (some (pointClosedPoint h.left)) (n : ℤ)
          - Finsupp.single (none : ProjPoint W) (n : ℤ) ∧
        ∃ g : W.FunctionField, g ≠ 0 ∧
          (∃ u : W.CoordinateRingˣ, (u : W.CoordinateRing) • g ^ n
            = mulByNEndo n (transcendental_xCoord_nsmul_of_isAlgClosed h2 hnz) f) ∧
          translateEndo h.left g = g ∧ weilPairingElt h.left g = 1 :=
  let ⟨_, hP⟩ := exists_nsmul_eq_of_smooth h2 hnz hfac (Point.some xT yT h)
  exists_weilPairingElt_self_eq_one_of_hprin_n hnz _ h htors hP hprin

open Classical in
/-- **`e_n(T, T) = 1` in `μ_m(F̄)` at every `3`-smooth `n ≠ 0`**, with `hprin` the only hypothesis
left.

The `μ`-valued twin of `exists_weilPairingElt_self_eq_one_of_hprin_n_of_algClosed`, standing to it
exactly as `exists_weilPairingMu_self_eq_one_of_hprin_n` stands to the core.  Both hypotheses the
core takes on top of `hprin` are discharged, by the same two lemmas and for the same reasons.

⚠️ As above, `m` is arbitrary and need not equal `n`. -/
theorem exists_weilPairingMu_self_eq_one_of_hprin_n_of_algClosed [IsAlgClosed F]
    (h2 : (2 : F) ≠ 0) {n : ℕ} (hnz : n ≠ 0) (hfac : ∀ p ∈ n.primeFactors, p = 2 ∨ p = 3)
    (h : W.Nonsingular xT yT) (htors : Point.some xT yT h ∈ W.torsion n)
    (hprin : ∀ f : W.FunctionField, f ≠ 0 →
      divisor W f = Finsupp.single (pointClosedPoint h.left) (n : ℤ) →
      ∃ g₀ : W.FunctionField, g₀ ≠ 0 ∧
        n • divisor W g₀
          = divisor W (mulByNEndo n (transcendental_xCoord_nsmul_of_isAlgClosed h2 hnz) f))
    (m : ℕ) [NeZero m] :
    ∃ f : W.FunctionField, f ≠ 0 ∧
      divisorProj W f = Finsupp.single (some (pointClosedPoint h.left)) (n : ℤ)
          - Finsupp.single (none : ProjPoint W) (n : ℤ) ∧
        ∃ g : W.FunctionField, g ≠ 0 ∧
          (∃ u : W.CoordinateRingˣ, (u : W.CoordinateRing) • g ^ n
            = mulByNEndo n (transcendental_xCoord_nsmul_of_isAlgClosed h2 hnz) f) ∧
          ∃ hpow : weilPairingElt h.left g ^ m = 1, weilPairingMu h.left hpow = 1 :=
  let ⟨_, hP⟩ := exists_nsmul_eq_of_smooth h2 hnz hfac (Point.some xT yT h)
  exists_weilPairingMu_self_eq_one_of_hprin_n hnz _ h htors hP hprin m


/-! #### The same at every `n ≠ 0`

The two statements above consume `hfac` in exactly one place, `exists_nsmul_eq_of_smooth`, and
`nsmul_surjective_of_two_ne_zero` (`EllipticCurves.Torsion.TwoTorsionOrder`) is the same conclusion
under the same instances at **every** `n ≠ 0`.  So the two below are the two above with `hfac`
deleted and **nothing put in its place** — no index condition, no `h3`, no extra instance.

⚠️ **This is the only place on this front where the general layer is free.** Everywhere else — the
nine group-1 statements, the `_of_smooth` corollaries over an arbitrary field — dropping `hfac`
costs `((n : ℤ) : F) ≠ 0`, because what is being replaced there is the *transcendence*, and the
route to it runs through `natDegree_ΨSq`.  Here the transcendence is already
`transcendental_xCoord_nsmul_of_isAlgClosed`, general in `n ≠ 0` over `F̄` with no condition on the
characteristic at all, and the only `3`-smooth input left is the halving point.

⚠️ The `_of_smooth` forms are **kept, not deleted**: `exists_nsmul_eq_of_smooth` halves by iterated
`2`- and `3`-descent and consumes no division polynomial, while `nsmul_surjective_of_two_ne_zero`
runs through the `ΨSq`-root dictionary.  They are independent routes to the same halving point, and
the `example`s below compile the containment rather than asserting it. -/

open Classical in
/-- **`e_n(T, T) = 1` over `F̄` at every `n ≠ 0`**, with `hprin` the only hypothesis left.

`exists_weilPairingElt_self_eq_one_of_hprin_n_of_algClosed` with `hfac` removed.  Both hypotheses
the core takes on top of `hprin` are discharged, and neither needs `3`-smoothness:

* the transcendence, by `transcendental_xCoord_nsmul_of_isAlgClosed`;
* the halving point, by `nsmul_surjective_of_two_ne_zero`
  (`EllipticCurves.Torsion.TwoTorsionOrder`), `[n]`-surjectivity on `E(F̄)` at every `n ≠ 0`.

⚠️ `h2` is the *only* condition on the characteristic, and it is not an index condition: `n` may be
divisible by `char F`.  `[n]` is still non-constant there — it is inseparable, not constant — which
is why the `F̄` transcendence never needed `natDegree_ΨSq`. -/
theorem exists_weilPairingElt_self_eq_one_of_hprin_n_of_algClosed_of_ne_zero [IsAlgClosed F]
    (h2 : (2 : F) ≠ 0) {n : ℕ} (hnz : n ≠ 0)
    (h : W.Nonsingular xT yT) (htors : Point.some xT yT h ∈ W.torsion n)
    (hprin : ∀ f : W.FunctionField, f ≠ 0 →
      divisor W f = Finsupp.single (pointClosedPoint h.left) (n : ℤ) →
      ∃ g₀ : W.FunctionField, g₀ ≠ 0 ∧
        n • divisor W g₀
          = divisor W (mulByNEndo n (transcendental_xCoord_nsmul_of_isAlgClosed h2 hnz) f)) :
    ∃ f : W.FunctionField, f ≠ 0 ∧
      divisorProj W f = Finsupp.single (some (pointClosedPoint h.left)) (n : ℤ)
          - Finsupp.single (none : ProjPoint W) (n : ℤ) ∧
        ∃ g : W.FunctionField, g ≠ 0 ∧
          (∃ u : W.CoordinateRingˣ, (u : W.CoordinateRing) • g ^ n
            = mulByNEndo n (transcendental_xCoord_nsmul_of_isAlgClosed h2 hnz) f) ∧
          translateEndo h.left g = g ∧ weilPairingElt h.left g = 1 :=
  let ⟨_, hP⟩ := nsmul_surjective_of_two_ne_zero h2 hnz (Point.some xT yT h)
  exists_weilPairingElt_self_eq_one_of_hprin_n hnz _ h htors hP hprin

open Classical in
/-- **`e_n(T, T) = 1` in `μ_m(F̄)` at every `n ≠ 0`**, with `hprin` the only hypothesis left.

The `μ`-valued twin of `exists_weilPairingElt_self_eq_one_of_hprin_n_of_algClosed_of_ne_zero`.
⚠️ As above, `m` is arbitrary and need not equal `n`. -/
theorem exists_weilPairingMu_self_eq_one_of_hprin_n_of_algClosed_of_ne_zero [IsAlgClosed F]
    (h2 : (2 : F) ≠ 0) {n : ℕ} (hnz : n ≠ 0)
    (h : W.Nonsingular xT yT) (htors : Point.some xT yT h ∈ W.torsion n)
    (hprin : ∀ f : W.FunctionField, f ≠ 0 →
      divisor W f = Finsupp.single (pointClosedPoint h.left) (n : ℤ) →
      ∃ g₀ : W.FunctionField, g₀ ≠ 0 ∧
        n • divisor W g₀
          = divisor W (mulByNEndo n (transcendental_xCoord_nsmul_of_isAlgClosed h2 hnz) f))
    (m : ℕ) [NeZero m] :
    ∃ f : W.FunctionField, f ≠ 0 ∧
      divisorProj W f = Finsupp.single (some (pointClosedPoint h.left)) (n : ℤ)
          - Finsupp.single (none : ProjPoint W) (n : ℤ) ∧
        ∃ g : W.FunctionField, g ≠ 0 ∧
          (∃ u : W.CoordinateRingˣ, (u : W.CoordinateRing) • g ^ n
            = mulByNEndo n (transcendental_xCoord_nsmul_of_isAlgClosed h2 hnz) f) ∧
          ∃ hpow : weilPairingElt h.left g ^ m = 1, weilPairingMu h.left hpow = 1 :=
  let ⟨_, hP⟩ := nsmul_surjective_of_two_ne_zero h2 hnz (Point.some xT yT h)
  exists_weilPairingMu_self_eq_one_of_hprin_n hnz _ h htors hP hprin m

open Classical in
/-- **`…_of_algClosed` is a corollary of `…_of_algClosed_of_ne_zero`** — its statement verbatim,
`hfac` binder and binder *name* included, proved from the general form.  The containment is
compiled, not asserted.

⚠️ The `have _hfac := hfac` line is why the binder can keep its name: `--wfail` rejects an
explicitly bound hypothesis that is never referenced, and renaming it to `_hfac` would leave a
statement that a token-by-token comparison against the theorem no longer matches.  One unused
`have` buys an exactly verbatim restatement, which is the point of the `example`. -/
example [IsAlgClosed F] (h2 : (2 : F) ≠ 0) {n : ℕ} (hnz : n ≠ 0)
    (hfac : ∀ p ∈ n.primeFactors, p = 2 ∨ p = 3)
    (h : W.Nonsingular xT yT) (htors : Point.some xT yT h ∈ W.torsion n)
    (hprin : ∀ f : W.FunctionField, f ≠ 0 →
      divisor W f = Finsupp.single (pointClosedPoint h.left) (n : ℤ) →
      ∃ g₀ : W.FunctionField, g₀ ≠ 0 ∧
        n • divisor W g₀
          = divisor W (mulByNEndo n (transcendental_xCoord_nsmul_of_isAlgClosed h2 hnz) f)) :
    ∃ f : W.FunctionField, f ≠ 0 ∧
      divisorProj W f = Finsupp.single (some (pointClosedPoint h.left)) (n : ℤ)
          - Finsupp.single (none : ProjPoint W) (n : ℤ) ∧
        ∃ g : W.FunctionField, g ≠ 0 ∧
          (∃ u : W.CoordinateRingˣ, (u : W.CoordinateRing) • g ^ n
            = mulByNEndo n (transcendental_xCoord_nsmul_of_isAlgClosed h2 hnz) f) ∧
          translateEndo h.left g = g ∧ weilPairingElt h.left g = 1 :=
  have _hfac := hfac
  exists_weilPairingElt_self_eq_one_of_hprin_n_of_algClosed_of_ne_zero h2 hnz h htors hprin

open Classical in
/-- **`…Mu…_of_algClosed` is a corollary of `…Mu…_of_algClosed_of_ne_zero`**, likewise verbatim,
and likewise with `have _hfac := hfac` keeping the binder name. -/
example [IsAlgClosed F] (h2 : (2 : F) ≠ 0) {n : ℕ} (hnz : n ≠ 0)
    (hfac : ∀ p ∈ n.primeFactors, p = 2 ∨ p = 3)
    (h : W.Nonsingular xT yT) (htors : Point.some xT yT h ∈ W.torsion n)
    (hprin : ∀ f : W.FunctionField, f ≠ 0 →
      divisor W f = Finsupp.single (pointClosedPoint h.left) (n : ℤ) →
      ∃ g₀ : W.FunctionField, g₀ ≠ 0 ∧
        n • divisor W g₀
          = divisor W (mulByNEndo n (transcendental_xCoord_nsmul_of_isAlgClosed h2 hnz) f))
    (m : ℕ) [NeZero m] :
    ∃ f : W.FunctionField, f ≠ 0 ∧
      divisorProj W f = Finsupp.single (some (pointClosedPoint h.left)) (n : ℤ)
          - Finsupp.single (none : ProjPoint W) (n : ℤ) ∧
        ∃ g : W.FunctionField, g ≠ 0 ∧
          (∃ u : W.CoordinateRingˣ, (u : W.CoordinateRing) • g ^ n
            = mulByNEndo n (transcendental_xCoord_nsmul_of_isAlgClosed h2 hnz) f) ∧
          ∃ hpow : weilPairingElt h.left g ^ m = 1, weilPairingMu h.left hpow = 1 :=
  have _hfac := hfac
  exists_weilPairingMu_self_eq_one_of_hprin_n_of_algClosed_of_ne_zero h2 hnz h htors hprin m

end AlgClosed

/-! ### Recovery of the merged `n = 2` and `n = 3` assemblies

`#907`'s rule: a general form is only worth having if the merged statements it replaces come back
out of it unchanged.  Both do, and the two statements below are their signatures character for
character, ambient `variable` line included, `[IsAlgClosed F]` included.  Each is proved *through*
the algebraically closed corollary rather than re-proved.

⚠️ Both are `private`: public copies would duplicate merged names.  Check them against their twins
by the **elaborated-type** comparison (`pp.explicit`, `pp.universes`, `pp.deepTerms`) inside a copy
of this module, not by a source diff — a source comparator cannot see an auto-bound instance binder,
and printed names differ between modules with different `open` lines.

⚠️ The only real content of either is the numeral bridge `mulByNEndo_two` / `mulByNEndo_three`,
which has to be pushed through `hprin` as well as through the conclusion.  Proof irrelevance makes
the transcendence argument of `mulByNEndo` unify on its own; do not try to match it by hand. -/

section Recovery

variable {x₂ y₂ x₃ y₃ : F}

omit [W.IsElliptic] [IsDedekindDomain W.CoordinateRing] in
/-- `3`-smoothness at a prime index: the only prime factor of a prime `p` is `p` itself. -/
private lemma primeFactors_eq_two_or_three_of_prime {p : ℕ} (hp : p.Prime)
    (h : p = 2 ∨ p = 3) : ∀ q ∈ p.primeFactors, q = 2 ∨ q = 3 := fun q hq => by
  rw [Nat.mem_primeFactors] at hq
  rw [(Nat.prime_dvd_prime_iff_eq hq.1 hp).mp hq.2.1]
  exact h

open Classical in
/-- `exists_weilPairingElt_self_eq_one_of_algClosed_two`
(`EllipticCurves.FunctionField.WeilPairingAlternatingTwo`), recovered. -/
private theorem exists_weilPairingElt_self_eq_one_of_algClosed_two_of_general [IsAlgClosed F]
    (h2 : (2 : F) ≠ 0) (h : W.Nonsingular x₂ y₂) (htors : Point.some x₂ y₂ h ∈ W.torsion 2)
    (hprin : ∀ f : W.FunctionField, f ≠ 0 →
      divisor W f = Finsupp.single (pointClosedPoint h.left) (2 : ℤ) →
      ∃ g₀ : W.FunctionField, g₀ ≠ 0 ∧
        2 • divisor W g₀ = divisor W (mulByTwoEndo h2 f)) :
    ∃ f : W.FunctionField, f ≠ 0 ∧
      divisorProj W f = Finsupp.single (some (pointClosedPoint h.left)) (2 : ℤ)
          - Finsupp.single (none : ProjPoint W) (2 : ℤ) ∧
        ∃ g : W.FunctionField, g ≠ 0 ∧
          (∃ u : W.CoordinateRingˣ, (u : W.CoordinateRing) • g ^ 2 = mulByTwoEndo h2 f) ∧
          translateEndo h.left g = g ∧ weilPairingElt h.left g = 1 := by
  have key := exists_weilPairingElt_self_eq_one_of_hprin_n_of_algClosed (n := 2) h2
    (by norm_num) (primeFactors_eq_two_or_three_of_prime Nat.prime_two (Or.inl rfl)) h htors
    (by simpa only [mulByNEndo_two h2, Nat.cast_ofNat] using hprin)
  simpa only [mulByNEndo_two h2, Nat.cast_ofNat] using key

open Classical in
/-- `exists_weilPairingElt_self_eq_one_of_algClosed_three`
(`EllipticCurves.FunctionField.WeilPairingAlternatingThree`), recovered.

⚠️ `h3` is in the statement only because `mulByThreeEndo` is indexed by it; neither discharge in the
corollary above needs it.  Asking the general form for it would have made this recovery carry a
hypothesis the merged statement does not have. -/
private theorem exists_weilPairingElt_self_eq_one_of_algClosed_three_of_general [IsAlgClosed F]
    (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) (h : W.Nonsingular x₃ y₃)
    (htors : Point.some x₃ y₃ h ∈ W.torsion 3)
    (hprin : ∀ f : W.FunctionField, f ≠ 0 →
      divisor W f = Finsupp.single (pointClosedPoint h.left) (3 : ℤ) →
      ∃ g₀ : W.FunctionField, g₀ ≠ 0 ∧
        3 • divisor W g₀ = divisor W (mulByThreeEndo h2 h3 f)) :
    ∃ f : W.FunctionField, f ≠ 0 ∧
      divisorProj W f = Finsupp.single (some (pointClosedPoint h.left)) (3 : ℤ)
          - Finsupp.single (none : ProjPoint W) (3 : ℤ) ∧
        ∃ g : W.FunctionField, g ≠ 0 ∧
          (∃ u : W.CoordinateRingˣ, (u : W.CoordinateRing) • g ^ 3 = mulByThreeEndo h2 h3 f) ∧
          translateEndo h.left g = g ∧ weilPairingElt h.left g = 1 := by
  have key := exists_weilPairingElt_self_eq_one_of_hprin_n_of_algClosed (n := 3) h2
    (by norm_num) (primeFactors_eq_two_or_three_of_prime Nat.prime_three (Or.inr rfl)) h htors
    (by simpa only [mulByNEndo_three h2 h3, Nat.cast_ofNat] using hprin)
  simpa only [mulByNEndo_three h2 h3, Nat.cast_ofNat] using key

end Recovery

/-! ### Non-vacuity over `F̄` at `n = 6`, and at `n = 10` for the general layer

⚠️ **`hprin` is a hypothesis and it is `#418`, so the headline cannot be fully instantiated on any
concrete curve.**  What is certified below is that *every other* hypothesis of the algebraically
closed corollary is simultaneously satisfiable at an index no merged assembly reaches: the elliptic
instance, `(2 : K) ≠ 0`, `n ≠ 0`, `3`-smoothness of `n`, an affine nonsingular `T`, and
`T ∈ torsion n`.  The halving point is not in that list because the corollary produces it — which is
itself part of the claim.  What stays hypothetical is `hprin` and nothing else; a certificate
resting on a hypothesis that is *false* proves nothing (`#916`), so each of the others is proved
here rather than assumed.

⚠️ `n = 6` at a `T` of order **3** is chosen for the order, not the index.  `T` of order strictly
dividing `n` is the configuration no `translateEndo`-indexed statement can express — the interior
factor at `i = 3` translates by `O` — and `WeilPairingTelescopeN`'s certificate exercises the same
one for the same reason.

⚠️ The curve is `y² = x³ + 1`, **not** this subtree's default `y² = x³ − x`: on the default every
affine rational point is `2`-torsion, so there is no point of order `3` on it to exhibit.  That is
the second of **three** independent rediscoveries of one fact about that fixture; the `ℚ` block
below records all three together, and it is the right place to look before choosing a fourth curve.

The base field is `AlgebraicClosure ℚ`, as `[IsAlgClosed F]` requires.  It carries no `DecidableEq`
instance, so `open Classical in` supplies the same one the theorem's statement fixes and the
certificate costs no `convert` — see the module docstring. -/

section Nonvacuity

/-! The certificate curves `y² = x³ + 1` and `y² = x³ + 4x` are the shared
`EllipticCurves.Fixture.y2EqX3AddOne` and `EllipticCurves.Fixture.y2EqX3Add4X`, and the base —
algebraically closed, and of characteristic `0` so that `2 ≠ 0` and `3 ≠ 0` — is
`EllipticCurves.Fixture.AlgClosedQ`, whose single `[CharZero F]` instance also supplies
`IsElliptic` here. -/

open EllipticCurves.Fixture

private lemma exampleTwoNeZero : (2 : AlgClosedQ) ≠ 0 := two_ne_zero

/-- `T = (0, 1)` is a nonsingular point of `y² = x³ + 1`. -/
private lemma exampleNonsingularT : (y2EqX3AddOne AlgClosedQ).Nonsingular 0 1 := by
  rw [nonsingular_iff]
  refine ⟨?_, Or.inr ?_⟩ <;>
    norm_num [y2EqX3AddOne, WeierstrassCurve.Affine.equation_iff, WeierstrassCurve.Affine.negY]

open Classical in
/-- `[2]T = −T`: the tangent at `(0, 1)` is horizontal, and doubling returns `(0, −1)`. -/
private lemma exampleDouble :
    Point.some (0 : AlgClosedQ) 1 exampleNonsingularT
        + Point.some (0 : AlgClosedQ) 1 exampleNonsingularT
      = -Point.some (0 : AlgClosedQ) 1 exampleNonsingularT := by
  have hy : (1 : AlgClosedQ) ≠ (y2EqX3AddOne AlgClosedQ).negY 0 1 := by
    norm_num [y2EqX3AddOne, WeierstrassCurve.Affine.negY]
  rw [Point.add_self_of_Y_ne hy, Point.neg_some, Point.some.injEq]
  constructor <;>
    norm_num [y2EqX3AddOne, WeierstrassCurve.Affine.addX, WeierstrassCurve.Affine.addY,
      WeierstrassCurve.Affine.negAddY, WeierstrassCurve.Affine.negY,
      WeierstrassCurve.Affine.slope]

open Classical in
/-- `T` has order `3`. -/
private lemma exampleThreeTorsion :
    ((3 : ℕ) • Point.some (0 : AlgClosedQ) 1 exampleNonsingularT :
        (y2EqX3AddOne AlgClosedQ).Point) = 0 := by
  rw [show (3 : ℕ) = 2 + 1 from rfl, succ_nsmul, two_nsmul, exampleDouble, neg_add_cancel]

open Classical in
/-- Hence `T` is `6`-torsion, without having order `6`. -/
private lemma exampleSixTorsion :
    Point.some (0 : AlgClosedQ) 1 exampleNonsingularT ∈ (y2EqX3AddOne AlgClosedQ).torsion 6 := by
  rw [mem_torsion_iff, show (6 : ℕ) = 3 + 3 from rfl, add_nsmul, exampleThreeTorsion, add_zero]

/-- `6` is `3`-smooth. -/
private lemma exampleSmooth : ∀ p ∈ (6 : ℕ).primeFactors, p = 2 ∨ p = 3 := by
  intro p hp
  rw [show (6 : ℕ) = 2 * 3 from rfl, Nat.primeFactors_mul (by norm_num) (by norm_num),
    Finset.mem_union, Nat.Prime.primeFactors Nat.prime_two,
    Nat.Prime.primeFactors Nat.prime_three, Finset.mem_singleton, Finset.mem_singleton] at hp
  exact hp

open Classical in
/-- **Every hypothesis but `hprin` is simultaneously satisfiable at `n = 6`.** -/
example
    (hprin : ∀ f : (y2EqX3AddOne AlgClosedQ).FunctionField, f ≠ 0 →
      divisor (y2EqX3AddOne AlgClosedQ) f
          = Finsupp.single (pointClosedPoint exampleNonsingularT.left) ((6 : ℕ) : ℤ) →
        ∃ g₀ : (y2EqX3AddOne AlgClosedQ).FunctionField, g₀ ≠ 0 ∧
          (6 : ℕ) • divisor (y2EqX3AddOne AlgClosedQ) g₀ = divisor (y2EqX3AddOne AlgClosedQ)
            (mulByNEndo 6
              (transcendental_xCoord_nsmul_of_isAlgClosed exampleTwoNeZero (by norm_num)) f)) :
    ∃ f : (y2EqX3AddOne AlgClosedQ).FunctionField, f ≠ 0 ∧
      divisorProj (y2EqX3AddOne AlgClosedQ) f
          = Finsupp.single (some (pointClosedPoint exampleNonsingularT.left)) ((6 : ℕ) : ℤ)
            - Finsupp.single (none : ProjPoint (y2EqX3AddOne AlgClosedQ)) ((6 : ℕ) : ℤ) ∧
        ∃ g : (y2EqX3AddOne AlgClosedQ).FunctionField, g ≠ 0 ∧
          (∃ u : (y2EqX3AddOne AlgClosedQ).CoordinateRingˣ, (u :
              (y2EqX3AddOne AlgClosedQ).CoordinateRing) • g ^ (6 : ℕ)
            = mulByNEndo 6
                (transcendental_xCoord_nsmul_of_isAlgClosed exampleTwoNeZero (by norm_num)) f) ∧
          translateEndo exampleNonsingularT.left g = g ∧
            weilPairingElt exampleNonsingularT.left g = 1 :=
  exists_weilPairingElt_self_eq_one_of_hprin_n_of_algClosed exampleTwoNeZero (by norm_num)
    exampleSmooth exampleNonsingularT exampleSixTorsion hprin


/-! #### And at `n = 10`, which the `_of_smooth` corollary cannot state

⚠️ **`n = 6` cannot falsify the general layer.**  `6 = 2 · 3` is `3`-smooth, so the certificate
above is equally a certificate for `…_of_algClosed`, and a *"general"* wrapper reaching only
`{2, 3}`-indices would pass it unchanged.  `#1549`'s bar asks for an index that is **even and not
`3`-smooth**; `10 = 2 · 5` is the smallest.

⚠️ The witness has to change with the index, not just the numeral: `T = (0, 1)` has order `3` and is
not `10`-torsion.  The other rational point of small order on the same curve is `(−1, 0)`, which is
`2`-torsion (`y = negY y` forces `2y = 0`, and `x³ = −1` forces `x = −1` here), hence `10`-torsion.
⚠️ Write the factorisation as `10 = 2 * 5` and not `5 * 2`: `mul_nsmul` reads
`(m * n) • a = n • m • a`, so the *left* factor is applied first. -/

/-- `(−1, 0)` is a nonsingular point of `y² = x³ + 1`. -/
private lemma exampleNonsingularNegOne : (y2EqX3AddOne AlgClosedQ).Nonsingular (-1) 0 := by
  rw [nonsingular_iff]
  refine ⟨?_, Or.inl ?_⟩ <;>
    norm_num [y2EqX3AddOne, WeierstrassCurve.Affine.equation_iff, WeierstrassCurve.Affine.negY]

open Classical in
/-- `(−1, 0)` is `2`-torsion: it is its own negative. -/
private lemma exampleTwoTorsionNegOne :
    Point.some (-1 : AlgClosedQ) 0 exampleNonsingularNegOne
      ∈ (y2EqX3AddOne AlgClosedQ).torsion 2 := by
  rw [mem_torsion_iff, two_nsmul, Point.add_self_of_Y_eq
    (by norm_num [y2EqX3AddOne, WeierstrassCurve.Affine.negY])]

open Classical in
/-- Hence `(−1, 0)` is `10`-torsion. -/
private lemma exampleTenTorsionNegOne :
    Point.some (-1 : AlgClosedQ) 0 exampleNonsingularNegOne
      ∈ (y2EqX3AddOne AlgClosedQ).torsion 10 := by
  rw [mem_torsion_iff, show (10 : ℕ) = 2 * 5 from rfl, mul_nsmul,
    mem_torsion_iff.mp exampleTwoTorsionNegOne, smul_zero]

open Classical in
/-- **Every hypothesis but `hprin` is simultaneously satisfiable at `n = 10`**, an index
`exists_weilPairingElt_self_eq_one_of_hprin_n_of_algClosed` cannot reach at any hypotheses
(`Nat.ten_not_smooth`). -/
example
    (hprin : ∀ f : (y2EqX3AddOne AlgClosedQ).FunctionField, f ≠ 0 →
      divisor (y2EqX3AddOne AlgClosedQ) f
          = Finsupp.single (pointClosedPoint exampleNonsingularNegOne.left) ((10 : ℕ) : ℤ) →
        ∃ g₀ : (y2EqX3AddOne AlgClosedQ).FunctionField, g₀ ≠ 0 ∧
          (10 : ℕ) • divisor (y2EqX3AddOne AlgClosedQ) g₀ = divisor (y2EqX3AddOne AlgClosedQ)
            (mulByNEndo 10
              (transcendental_xCoord_nsmul_of_isAlgClosed exampleTwoNeZero (by norm_num)) f)) :
    ∃ f : (y2EqX3AddOne AlgClosedQ).FunctionField, f ≠ 0 ∧
      divisorProj (y2EqX3AddOne AlgClosedQ) f
          = Finsupp.single (some (pointClosedPoint exampleNonsingularNegOne.left)) ((10 : ℕ) : ℤ)
            - Finsupp.single (none : ProjPoint (y2EqX3AddOne AlgClosedQ)) ((10 : ℕ) : ℤ) ∧
        ∃ g : (y2EqX3AddOne AlgClosedQ).FunctionField, g ≠ 0 ∧
          (∃ u : (y2EqX3AddOne AlgClosedQ).CoordinateRingˣ, (u :
              (y2EqX3AddOne AlgClosedQ).CoordinateRing) • g ^ (10 : ℕ)
            = mulByNEndo 10
                (transcendental_xCoord_nsmul_of_isAlgClosed exampleTwoNeZero (by norm_num)) f) ∧
          translateEndo exampleNonsingularNegOne.left g = g ∧
            weilPairingElt exampleNonsingularNegOne.left g = 1 :=
  exists_weilPairingElt_self_eq_one_of_hprin_n_of_algClosed_of_ne_zero exampleTwoNeZero
    (by norm_num) exampleNonsingularNegOne exampleTenTorsionNegOne hprin

open Classical in
/-- **The `μ_10`-valued twin at `n = 10` as well**, with `m = n = 10`.  ⚠️ The first compiled
instantiation of any `weilPairingMu` statement of this file outside the `3`-smooth class. -/
example
    (hprin : ∀ f : (y2EqX3AddOne AlgClosedQ).FunctionField, f ≠ 0 →
      divisor (y2EqX3AddOne AlgClosedQ) f
          = Finsupp.single (pointClosedPoint exampleNonsingularNegOne.left) ((10 : ℕ) : ℤ) →
        ∃ g₀ : (y2EqX3AddOne AlgClosedQ).FunctionField, g₀ ≠ 0 ∧
          (10 : ℕ) • divisor (y2EqX3AddOne AlgClosedQ) g₀ = divisor (y2EqX3AddOne AlgClosedQ)
            (mulByNEndo 10
              (transcendental_xCoord_nsmul_of_isAlgClosed exampleTwoNeZero (by norm_num)) f)) :
    ∃ f : (y2EqX3AddOne AlgClosedQ).FunctionField, f ≠ 0 ∧
      divisorProj (y2EqX3AddOne AlgClosedQ) f
          = Finsupp.single (some (pointClosedPoint exampleNonsingularNegOne.left)) ((10 : ℕ) : ℤ)
            - Finsupp.single (none : ProjPoint (y2EqX3AddOne AlgClosedQ)) ((10 : ℕ) : ℤ) ∧
        ∃ g : (y2EqX3AddOne AlgClosedQ).FunctionField, g ≠ 0 ∧
          (∃ u : (y2EqX3AddOne AlgClosedQ).CoordinateRingˣ, (u :
              (y2EqX3AddOne AlgClosedQ).CoordinateRing) • g ^ (10 : ℕ)
            = mulByNEndo 10
                (transcendental_xCoord_nsmul_of_isAlgClosed exampleTwoNeZero (by norm_num)) f) ∧
          ∃ hpow : weilPairingElt exampleNonsingularNegOne.left g ^ (10 : ℕ) = 1,
            weilPairingMu exampleNonsingularNegOne.left hpow = 1 :=
  exists_weilPairingMu_self_eq_one_of_hprin_n_of_algClosed_of_ne_zero exampleTwoNeZero
    (by norm_num) exampleNonsingularNegOne exampleTenTorsionNegOne hprin 10

end Nonvacuity

/-! ### Non-vacuity over `ℚ` at `n = 6`, with the halving *proved*

The section above certifies the algebraically closed corollary, where the halving point is produced
*by the theorem*.  This one certifies the two statements that take it as a hypothesis — the core and
`…_of_hprin_n_of_smooth` — over a field that is **not** algebraically closed, by exhibiting a
concrete `P` with `[6]P = T` on a named curve over `ℚ`.  ⚠️ Without it nothing on this front
exhibits a concrete halving at a composite index over a general field, and a hypothesis that is
never inhabited is a hypothesis that could be false (`#916`).

⚠️ **The index and the curve are both forced, and the arithmetic is the irreplaceable part.**
`[n]P = T` together with `[n]T = O` forces `ord P ∣ n²`, and `T ≠ O` forces `ord P ∤ n`.

* At `n = 4` that leaves `ord P ∈ {8, 16}`, and `ℤ/16` does not occur over `ℚ` — so a rational
  certificate at `n = 4` needs a point of order `8`.
* At `n = 6` it leaves `ord P ∈ {4, 9, 12, 18, 36}`, and **`ord P = 4` works**: then `[6]P = [2]P`,
  which is `2`-torsion, hence `6`-torsion, hence a legal `T`.

So `n = 6` is the cheapest genuinely composite index over `ℚ`, and `6 = 2 · 3` is `3`-smooth, so the
`_of_smooth` form applies.  The curve is `y² = x³ + 4x`, of discriminant `−4096`, with `T = (0, 0)`
of order `2` and a point of order `4` above it, at `x = 2`.

⚠️ **That order argument is a theorem now, not prose, and the block below no longer re-derives it at
this fixture.**  `exists_nsmul_eq_some_of_root_of_mem_torsion_two`
(`EllipticCurves.Torsion.DoublingSurjective`) says: if `T` is `2`-torsion and `Φ₂ − x(T)·Ψ₂Sq` has a
root carrying a point of `W` above it, then `[n]P = T` **and** `P ≠ T` for some `P`, at *every*
`n ≡ 2 (mod 4)`.  The proof is the second bullet above, in general form — `[4]P = [2]([2]P) =
[2]T = O`, hence `[4k + 2]P = [k]([4]P) + [2]P = T` — and the first bullet is why `n = 4` is *not*
reachable by it (`4 % 4 = 0`).  So the only thing this block still has to supply at `n = 6` is one
polynomial identity, `Φ₂(2) = 0 = x(T) · Ψ₂Sq(2)`, plus `6 % 4 = 2` by `norm_num`.

⚠️ **Why a root rather than a tangent line.**  A root of `Φ₂ − x(T)·Ψ₂Sq` and the `2`-torsion of `T`
are statements about explicit polynomials over the base field, so they are the data that survives
base change to a splitting field; a doubling computed through `slope`/`addX`/`addY` at named
coordinates transports to nothing.  That is the form `#962`'s descent will want, and it is the
reason the collapse is a strengthening rather than a shortening.

⚠️ **A fixture note, because this fact has now been rediscovered three times on this front as three
different-looking obstructions.**  `y² = x³ − x` — this subtree's historical default — has rational
torsion `(ℤ/2)²`.  That single fact appeared as *"no two distinct multiples"* (`#1325`), *"no point
of order `3`"* (`#1328`), and *"no point of order `4`"* (here).  It is the wrong fixture at every
index past `3`, and the right reflex is to change curve rather than to weaken the certificate.

⚠️ **No `open Classical in` on any lemma of this block**, unlike every abstract-`F` statement above,
and unlike the `AlgebraicClosure ℚ` block: it would be a *no-op*, because `ℚ` carries
`instDecidableEqRat`, which wins on instance priority whatever is open.  That is exactly why the
final application needs two `convert`s, and writing `open Classical in` here would hide the reason
rather than remove it.  This is the consumer side of the rule the module docstring states: **the
`[DecidableEq F]` binder is right for a producer, `open Classical in` for a consumer of a
`Classical`-fixed statement**, and retrofitting the binder onto gate B — not onto this file — is
what would make both free. -/

section NonvacuityRat

open EllipticCurves.Fixture

private lemma exampleRatTwo : (2 : ℚ) ≠ 0 := by norm_num

private lemma exampleRatThree : (3 : ℚ) ≠ 0 := by norm_num

/-- `P = (2, 4)` is a nonsingular point of `y² = x³ + 4x`. -/
private lemma exampleRatNsP : (y2EqX3Add4X ℚ).Nonsingular 2 4 :=
  (y2EqX3Add4X ℚ).equation_iff_nonsingular.mp (by
    norm_num [y2EqX3Add4X, WeierstrassCurve.Affine.equation_iff])

/-- `T = (0, 0)` is a nonsingular point of `y² = x³ + 4x`; it is the `2`-torsion point cut out by
`x = 0`. -/
private lemma exampleRatNsT : (y2EqX3Add4X ℚ).Nonsingular 0 0 :=
  (y2EqX3Add4X ℚ).equation_iff_nonsingular.mp (by
    norm_num [y2EqX3Add4X, WeierstrassCurve.Affine.equation_iff])

/-- `T = (0, 0)` is `2`-torsion: `ψ₂(T) = 2·0 + 0·0 + 0 = 0`. -/
private lemma exampleRatTorTwoT : Point.some (0 : ℚ) 0 exampleRatNsT ∈ (y2EqX3Add4X ℚ).torsion 2 :=
  (mem_torsion_two_some_iff exampleRatNsT).mpr (by norm_num [y2EqX3Add4X])

/-- **`T + T = O`**, the `W.Point` form of `exampleRatTorTwoT`. -/
private lemma exampleRatDoubleT :
    Point.some (0 : ℚ) 0 exampleRatNsT + Point.some (0 : ℚ) 0 exampleRatNsT = 0 := by
  have h := mem_torsion_iff.mp exampleRatTorTwoT
  rwa [two_nsmul] at h

/-- **`T` is `6`-torsion**, because it is `2`-torsion and `2 ∣ 6`.  ⚠️ Its order is `2`, strictly
dividing `6`: the theorem asks for `n`-torsion and not for order exactly `n`, and this certificate
runs at an index where the two differ — the same configuration the `AlgebraicClosure ℚ` block above
exercises at a `T` of order `3`.

⚠️ `mul_nsmul a m n : (m * n) • a = n • m • a` puts the factors out in the **opposite** order to the
one written, so `6 = 2 * 3` is what produces `3 • (2 • T)` here. -/
private lemma exampleRatTorSixT :
    Point.some (0 : ℚ) 0 exampleRatNsT ∈ (y2EqX3Add4X ℚ).torsion 6 := by
  rw [mem_torsion_iff, show (6 : ℕ) = 2 * 3 from rfl, mul_nsmul, two_nsmul, exampleRatDoubleT,
    smul_zero]

/-- **The root that does the work**: `Φ₂(2) = 0 = x(T) · Ψ₂Sq(2)`.

`y² = x³ + 4x` has `b₂ = 0`, `b₄ = 8`, `b₆ = 0`, `b₈ = −16`, so
`Φ₂ = X⁴ − b₄X² − 2b₆X − b₈ = X⁴ − 8X² + 16 = (X² − 4)²` vanishes at `x = 2`, while `x(T) = 0`.

⚠️ **`Φ₂` is literally the same polynomial as on `⟨0, 5, 0, 4, 0⟩`** — the curve
`EllipticCurves.Torsion.DoublingSurjective` and `…WeilPairingAlternatingTwoRational` run their own
blocks on — because the two share `b₄`, `b₆` and `b₈`.  `Ψ₂Sq` does **not** (`4X³ + 16X` here
against `4X³ + 20X² + 16X` there), so `Ψ₃` and every evaluation differ: copy the proof shape from
those files, recompute the numbers.

⚠️ Routed through `Φ_two_eval` — `Φ₂(x) = x · Ψ₂Sq(x) − Ψ₃(x)`, giving `2 · 64 − 128 = 0` — rather
than by unfolding `W.Φ 2`, whose definition is a recursion. -/
private lemma eval_Φ_two_exampleRatCurve :
    ((y2EqX3Add4X ℚ).Φ 2).eval 2 = (0 : ℚ) * (y2EqX3Add4X ℚ).Ψ₂Sq.eval 2 := by
  rw [Φ_two_eval]
  simp only [WeierstrassCurve.Ψ₂Sq, WeierstrassCurve.Ψ₃, WeierstrassCurve.b₂,
    WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈, y2EqX3Add4X]
  norm_num

/-- **The halving `[6]P = T`, discharged from a polynomial root**, together with the diagonal guard
`P ≠ T`.

This is the hypothesis the general assembly carries and the merged `n = 2` and `n = 3` assemblies do
not, and it is the reason this block exists: here it is *proved*, not assumed.

⚠️ **The order argument in the section docstring above is now a theorem rather than prose.**
`exists_nsmul_eq_some_of_root_of_mem_torsion_two` (`EllipticCurves.Torsion.DoublingSurjective`)
turns one root of `Φ₂ − x(T)·Ψ₂Sq` into `[n]P = T` at **every** `n ≡ 2 (mod 4)`, by way of
`[4]P = [2]([2]P) = [2]T = O`; `6 % 4 = 2` is the whole of what is index-specific here, and it is
discharged by `norm_num`.  Nothing in this block computes a tangent line any more.

⚠️ **The guard is inside the existential, and that is load-bearing.**  `P` is anonymous, so the old
coordinate form `(2, 4) ≠ (0, 0)` is not statable about it; but `P ≠ T` is a *consequence* of
`[2]P = T` when `T` is non-zero `2`-torsion — `P = T` would force `T = [2]T = O` — so the
certificate below binds its `P` from a witness satisfying **both** conjuncts and carries
off-diagonality by construction, even though it binds the second component to `_`.  Do not "clean
up" the unused conjunct.

⚠️ `exampleRatNsP` survives this collapse in a different role: it is no longer the named summand of
a doubling but the `W.Equation` witness above the root, supplied as `exampleRatNsP.left`. -/
private lemma exampleRatExistsSixP :
    ∃ P : (y2EqX3Add4X ℚ).Point,
      (6 : ℕ) • P = Point.some (0 : ℚ) 0 exampleRatNsT ∧
        P ≠ Point.some (0 : ℚ) 0 exampleRatNsT :=
  exists_nsmul_eq_some_of_root_of_mem_torsion_two exampleRatNsT exampleRatTorTwoT
    exampleRatNsP.left eval_Φ_two_exampleRatCurve (by norm_num)

/-- **Every hypothesis but `hprin` is simultaneously satisfiable at `n = 6` over `ℚ`**, on a named
curve, at a named affine `T` whose `6`-torsion is proved and a named affine `P`, distinct from `T`,
whose halving relation `[6]P = T` is proved.

⚠️ `hprin` is the **only** hypothesis left bound, exactly as in the merged `n = 2` and `n = 3`
assemblies over a general field.  It is `#418` and nothing on this board discharges it at any index
over a field that is not algebraically closed. -/
private theorem exampleRatAssemblySix
    (hprin : ∀ f : (y2EqX3Add4X ℚ).FunctionField, f ≠ 0 →
      divisor (y2EqX3Add4X ℚ) f
          = Finsupp.single (pointClosedPoint exampleRatNsT.left) ((6 : ℕ) : ℤ) →
        ∃ g₀ : (y2EqX3Add4X ℚ).FunctionField, g₀ ≠ 0 ∧
          (6 : ℕ) • divisor (y2EqX3Add4X ℚ) g₀ = divisor (y2EqX3Add4X ℚ)
            (mulByNEndo 6 (transcendental_xCoord_nsmul_of_smooth exampleRatTwo exampleRatThree
              (by norm_num) exampleSmooth) f)) :
    ∃ f : (y2EqX3Add4X ℚ).FunctionField, f ≠ 0 ∧
      divisorProj (y2EqX3Add4X ℚ) f
          = Finsupp.single (some (pointClosedPoint exampleRatNsT.left)) ((6 : ℕ) : ℤ)
            - Finsupp.single (none : ProjPoint (y2EqX3Add4X ℚ)) ((6 : ℕ) : ℤ) ∧
        ∃ g : (y2EqX3Add4X ℚ).FunctionField, g ≠ 0 ∧
          (∃ u : (y2EqX3Add4X ℚ).CoordinateRingˣ,
            (u : (y2EqX3Add4X ℚ).CoordinateRing) • g ^ (6 : ℕ)
              = mulByNEndo 6 (transcendental_xCoord_nsmul_of_smooth exampleRatTwo exampleRatThree
                  (by norm_num) exampleSmooth) f) ∧
          translateEndo exampleRatNsT.left g = g ∧ weilPairingElt exampleRatNsT.left g = 1 :=
  -- ⚠️ The two `convert`s are the entire price of the consuming theorem being elaborated
  -- `open Classical in`, and they are bookkeeping rather than mathematics.  `ℚ` has a genuine
  -- `DecidableEq` instance which wins on priority even under `open Classical`, so
  -- `exampleRatTorSixT` and `hP` are indexed by `instDecidableEqRat` while the theorem's copies
  -- carry `Classical.propDecidable`; the two are propositionally but not syntactically equal, and
  -- `convert` closes the gap by `Subsingleton.elim`.  ⚠️ Both lemmas behind `hP` are on the
  -- *producer* side and bind `[DecidableEq F]`, so over `ℚ` they land at `instDecidableEqRat` too:
  -- the count of `convert`s is unchanged at two, which is the prediction this collapse was checked
  -- against.
  let ⟨P, hP, _⟩ := exampleRatExistsSixP
  exists_weilPairingElt_self_eq_one_of_hprin_n_of_smooth exampleRatTwo exampleRatThree
    (n := 6) (by norm_num) exampleSmooth exampleRatNsT (by convert exampleRatTorSixT)
    (P := P) (by convert hP) hprin

end NonvacuityRat

end WeierstrassCurve.Affine
