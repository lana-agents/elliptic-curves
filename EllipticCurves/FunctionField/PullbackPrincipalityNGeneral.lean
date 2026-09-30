/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import EllipticCurves.FunctionField.DivisorBaseChangeRationalPoint
import EllipticCurves.FunctionField.DivisorGaloisDescentNsmul
import EllipticCurves.FunctionField.FunctionFieldBaseChangeN
import EllipticCurves.FunctionField.PullbackPrincipalityNRationalTorsionHprin

/-!
# `[n]∗((S) − (O))` is `n` times a principal divisor, by descent from an ABSTRACT finite Galois `N`

`EllipticCurves.FunctionField.PullbackPrincipalityNRationalTorsionHprin` discharges `hprin` at a
general `n` over an arbitrary field, but only from two rationality hypotheses over the base:
`hcard : #E[n] = n²` and a point `P` with `[n]P = S`.  **This file moves both hypotheses up to a
finite Galois extension `N / F` and brings the conclusion back down.**  It is the general-`n`
analogue of `exists_nsmul_divisor_eq_divisor_mulByThreeEndo_of_galois`
(`EllipticCurves.FunctionField.PullbackPrincipalityThreeGeneral`), and it is rung 3 of `#962`'s
general-`n` ladder.

⚠️ **`N` is ABSTRACT here and no tower is built.**  Constructing the field over which the two
hypotheses become *theorems* — `halvingGaloisField` at `n = 2`, `triplingGaloisField` at `n = 3`,
and an unbounded-depth tower at a general index — is rung 4, and so is the unconditional
`…_general` headline it unlocks.  This file stops at the descent.

⚠️ **Abstracting `N` is a measurement and not a preference**, and it is
`PullbackPrincipalityThreeGeneral`'s own finding re-used rather than re-derived: transcribing the
`n = 2` proof with the tower inlined exceeds the **default** heartbeat limit at `n = 3` already,
because `triplingGaloisField` is a five-layer chain of splitting fields that unification must
unfold.  **This file carries no `set_option maxHeartbeats`**, and at an unbounded tower depth the
argument for keeping `N` abstract is stronger rather than weaker.

## The route, in four steps

1. `algebraMap_ofNat_ne_zero` and `map_intCast` carry `(2 : F) ≠ 0` and `((n : ℤ) : F) ≠ 0` up to
   `N`.
2. `divisor_functionFieldMap_eq_single`
   (`EllipticCurves.FunctionField.DivisorBaseChangeRationalPoint`) carries `div f = n·(S)` up to `N`
   **on the nose** — the fibre over the closed point of a *rational* point is a singleton with
   `e = 1` there.
3. `exists_nsmul_divisor_eq_divisor_mulByNEndo_of_card` over `N` (`#2293`) produces a `g` with
   `n · div g = div ([n]∗ f)` upstairs.
4. `exists_nsmul_divisor_eq_of_functionFieldMap`
   (`EllipticCurves.FunctionField.DivisorGaloisDescentNsmul`) brings the identity back to `F`, by
   Hilbert 90 at the finite level.  ⚠️ The function it returns is **not** the descent of `g`.

⚠️ **The `F̄` route is closed at every index and this is not a matter of taste**: Mathlib's
Hilbert 90 is `[FiniteDimensional]`-only at the pin, so `H¹(Gal(F̄/F), F̄ˣ) = 0` is unavailable and
the finite extension is the route rather than a convenience.

## ⚠️ Seven of the eight inputs were ALREADY general at source, and the two that were not are named

Re-resolved declaration by declaration at `3f9e323`, against the elaborated type and not the
`theorem` line:

| input | index binder at source |
|---|---|
| `algebraMap_ofNat_ne_zero` | `{n : ℕ} [n.AtLeastTwo]` — general |
| `WeierstrassCurve.map_nonsingular` | Mathlib, index-free |
| `divisor_functionFieldMap_eq_single` | `{n : ℤ}`, `[Module.Finite F K]` — general |
| `exists_nsmul_divisor_eq_of_functionFieldMap` | `{n : ℕ} (hn : n ≠ 0)`, finite Galois — general |
| `mulByNEndo` / `mulByNEndo_injective` | `(n : ℕ)` — general |
| `functionFieldMap_mulByNEndo` | `{n : ℕ}` — general |
| `exists_nsmul_divisor_eq_divisor_mulByNEndo_of_card` | `{n : ℕ}` — general, and it is `#2293` |
| ⚠️ the torsion-membership bridge | `n = 3`-specific at source; **replaced, see below** |

**So this rung is assembly.**  ⚠️ **It is not assembly with nothing in it, and the two findings
below are what it cost.**

### ⚠️ FINDING 1 — the general-`n` descent binds ONE hypothesis the numeral forms do not, and it is
the endomorphism's own index

`mulByThreeEndo h2 h3` is indexed by two *numeral* facts, and `algebraMap_ofNat_ne_zero` transports
both to `N` for free — which is why the `n = 3` descent needs no extra binder.  `mulByNEndo n h` is
indexed by `h : Transcendental F (x([n]𝒫))` instead, and ⚠️ **`functionFieldMap_mulByNEndo` takes
the transcendence over `F` *and* over `N` because neither implies the other at that generality**:
its own module docstring
(`EllipticCurves.FunctionField.FunctionFieldBaseChangeN`, `## Two transcendence hypotheses`) says
*"Do not try to transport one into the other"* in terms.  So `h'` over `N` is a **hypothesis** here,
and it is the one place where the general index costs a binder that `n = 2` and `n = 3` do not pay.
⚠️ **A caller with `3`-smooth `n` gets it for free from `transcendental_xCoord_nsmul_of_smooth` over
`N`, which is exactly what the `n = 3` recovery below does; a caller at a general index must supply
it.**

### ⚠️ FINDING 2 — the torsion bridge has no division polynomial at a general `n`, and the
point-level route needed a new brick because `basePointMap` cannot carry a `map_*` lemma

`n = 2` transports `mem_torsion_two_some_iff` through a `congrArg` on the coordinates and `n = 3`
re-derives membership from `Ψ₃.eval x = 0`, which base-changes as a `Polynomial.eval`.  ⚠️ **At a
general `n` there is no such polynomial**, so the only route is the point-level one:
`mem_torsion_iff` (`EllipticCurves.Torsion.Defs`) is already `{n : ℕ}`, so what is needed is that
`n • S = 0` survives base change — one application of `map_nsmul` to an additive map on points.

⚠️⚠️ **`basePointMap` (`EllipticCurves.FunctionField.FunctionFieldBaseChangeN`) is that map and NO
`map_*` lemma can be applied to it in a context carrying `[DecidableEq F]`, which is measured and
not supposed.**  It is declared under `open Classical in`, so the `AddZeroClass W.Point` in its own
arrow type comes from `Classical.decEq F`; synthesising
`AddMonoidHomClass (W.Point →+ (W⁄N).Point) W.Point (W⁄N).Point` then **fails**, because instance
search produces the `[DecidableEq F]`-derived structure instead and the two do not match.  The
failure is the same whether `map_nsmul` is applied as a term or fired by `rw`, and adding
`open Classical in` to the consumer does not fix it.  ⚠️ **The working form is Mathlib's
`Point.map (Algebra.ofId F N)` under the ambient `[DecidableEq F]` and `[DecidableEq N]`** — which
`basePointMap` is a `Classical` wrapper *of* — with the `Point.some` computation left to
definitional unfolding rather than to `Point.map_some`, whose own `(W⁄F).Point` / `W.Point` framing
`rw` will not match either.  That is `mem_torsion_baseChange_of_nsmul_eq_zero` below.

⚠️ **Consequence for the signatures, and it is why the descent step takes its torsion hypothesis
over `N`.**  The bridge binds `[DecidableEq F]`; the descent step does not want to.  Taking
`hS` **over `N`** keeps the `omit [DecidableEq F]` that the `n = 3` form has *and* is a strictly
weaker hypothesis — the `F`-form implies it through the bridge — so the theorem is stronger, not
weaker, for it.  `exists_gS_n_of_galois` takes the `F`-form and pays the bridge, because
`exists_gS_n` binds `[DecidableEq F]` regardless.

## Main statements

Reach clauses below are complete, per `README.md` `## Docstring conventions` option (a), and are
read off the **elaborated type**.

* `WeierstrassCurve.Affine.exists_nsmul_divisor_eq_divisor_mulByNEndo_of_galois` — the descent step.
  ⚠️ **No `[DecidableEq F]`**, matching the `n = 3` form; it binds `[W.IsElliptic]`, which
  `mulByNEndo`'s index forces since `genericPoint` is defined only for an elliptic curve.  Reach:
  `(2 : F) ≠ 0`, `((n : ℤ) : F) ≠ 0`, non-constancy of `x([n]𝒫)` over `F` **and** over `N`,
  `#E[n] = n²` over `N`, an arbitrary finite Galois `N / F` with `[DecidableEq N]`, the
  nonsingularity of the `F`-rational `S = (x, y)`, the `n`-torsion of `S` **over `N`**, a point `P`
  of `E(N)` with `[n]P = S`, and a nonzero `f` with `div f = n·(S)`.
* `WeierstrassCurve.Affine.mem_torsion_baseChange_of_nsmul_eq_zero` — the bridge of FINDING 2:
  `n • S = 0` over `F` gives `S ∈ E(N)[n]` at every `n`.  ⚠️ **It binds `[DecidableEq F]` and
  `[DecidableEq N]` and no `[W.IsElliptic]`** — it is a statement about the group of points and
  about nothing else, and it is the only declaration here that is not assembly.
* `WeierstrassCurve.Affine.exists_gS_n_of_galois` — rung 5 of the Weil pairing over the same data,
  producing the `f` itself.  Reach: the descent step's list with `hS` read over `F` instead of over
  `N`, without the quantified `f`, and ⚠️ **with `[DecidableEq F]` added**, which `exists_gS_n`
  (`EllipticCurves.FunctionField.NthRootOfPullbackN`) binds.

`#print axioms` over all three returns exactly `{propext, Classical.choice, Quot.sound}`; `sorry`
and `sorryAx` are absent.

## Recovery

`#907`'s rule.  The `example` in `## Recovery` restates
`exists_nsmul_divisor_eq_divisor_mulByThreeEndo_of_galois` **verbatim** — same hypothesis list, same
`omit [DecidableEq F]`, same conclusion in terms of `mulByThreeEndo h2 h3` — and proves it from the
general form.  ⚠️ **The `omit` is part of the restatement and not an accident**: the
`FunctionFieldBaseChangeN` rule applies here — "an `example` that quietly keeps an instance its
original omits restates something *weaker* than the theorem it claims to subsume, and the
signatures match either way".  The two `mulByNEndo` indices are interchangeable because
`Transcendental` is a `Prop`, and `mulByNEndo_three`
(`EllipticCurves.FunctionField.MulByNPullback`) is the bridge to the numeral endomorphism.

⚠️ **The `n = 2` `…_of_galois` is NOT recovered, because there is none to recover.**
`PullbackPrincipalityTwoGeneral` inlines its tower and states no abstract-`N` descent step, which
is `PullbackPrincipalityThreeGeneral`'s *"do NOT transpose from `n = 2`"* warning read from the
other side.

## Non-vacuity — STATED and inherited, not re-derived

`#916`'s rule, and `#2295`'s own instruction that a rung which silently drops its predecessor's
vacuity disclosure has un-published it.

⚠️ **`#2293` confines its certificate to `n = 2`**: *"`n = 2` is the only index at which the
`_of_card` hypotheses are certified jointly satisfiable on this board"*, because `hcard` at any
`n ≥ 3` forces `μ_n ⊆ F` and admits no `ℚ` certificate — the obstruction
`PullbackPrincipalityNRationalTorsion`'s `## Non-vacuity` section records.  **That disclosure is
inherited here unchanged and no certificate is claimed at any index.**

⚠️ **One thing does change and it is worth stating, because it is the whole point of the rung:**
this file's `hcard` is over `N` and not over `F`, so the `μ_n ⊆ F` obstruction is no longer an
obstruction to the *hypothesis* — it is what forces `N ≠ F`, and producing such an `N` is rung 4.
**Until rung 4 lands, the only `N` for which this file's hypotheses are certified satisfiable is
`N = F` at `n = 2`**, where the statement collapses to `#2293`'s `exampleRungFiveGeneral` and
certifies nothing new.  ⚠️ **No `example` below asserts otherwise**, and the reason no inhabitation
is exhibited is this and not an oversight.

## ⚠️ What is *not* here

* **The general-`n` Galois tower** and the unconditional `…_general` headline — `#2296`.  The tower
  is three layers at `n = 2` and five at `n = 3`, so its depth at a general index is unbounded.
* **`exists_gS_n_general`** — it instantiates the tower, so it is rung 4's.
* **Any weakening of `hcard` or of `hP`.**  Both are hypotheses here, moved to `N` and not removed.
* **Re-derivation of the seven already-general inputs.**  Each binder was re-resolved once at
  source and then consumed.
* **No degree and no Galois group.**  `[N : F]` is not computed, `Gal(N/F)` is not identified, and
  nothing below says `F ⊊ N`.
* **Nothing about a non-rational `S`.**  Every statement is at an affine point of `W(F)`.

## References

* [J. H. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.8 (the Weil pairing)
  and VIII.2 (Hilbert 90).
-/

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum

namespace WeierstrassCurve.Affine

open CoordinateRing

variable {F : Type*} [Field F] {W : Affine F} [DecidableEq F] [W.IsElliptic]

omit [W.IsElliptic] in
/-- **`n`-torsion of an `F`-rational point survives base change, at every `n`.**  Stated as the
group equation `n • S = 0` downstairs and as `torsion` membership upstairs, which is the pair the
descent step consumes.

⚠️ **This is the general-`n` replacement for the division-polynomial bridges the numeral files
use** (`mem_torsion_two_some_iff` at `n = 2`, `Ψ₃.eval x = 0` at `n = 3`), and it is the one
declaration in this file that is not assembly.  See FINDING 2 in the module docstring for why it
goes through Mathlib's `Point.map` rather than through `basePointMap`, and why no `map_*` lemma
applies to the latter.

⚠️ **No `[W.IsElliptic]`**: it is a statement about the group of points. -/
theorem mem_torsion_baseChange_of_nsmul_eq_zero (N : Type*) [Field N] [Algebra F N]
    [DecidableEq N] {n : ℕ} {x y : F} (hns : W.Nonsingular x y)
    (hS : n • Point.some x y hns = 0) :
    Point.some (algebraMap F N x) (algebraMap F N y)
      ((W.map_nonsingular (algebraMap F N).injective x y).mpr hns) ∈ (W⁄N).torsion n := by
  have key := map_nsmul (Point.map (W' := W) (Algebra.ofId F N)) n (Point.some x y hns)
  rw [hS, map_zero] at key
  exact mem_torsion_iff.mpr key.symm

omit [DecidableEq F] in
/-- **The descent step at a general `n`**, over an arbitrary field `F` with `(2 : F) ≠ 0` and
`((n : ℤ) : F) ≠ 0` and an arbitrary finite Galois extension `N / F` over which `#E[n] = n²` and `S`
is `n` times a point: for a nonsingular `F`-rational `S = (x, y)` that is `n`-torsion over `N` and a
nonzero `f` with `div f = n·(S)`, the pullback `[n]∗ f` is `n` times a principal divisor **over
`F`**.

Steps 1–4 of the route in the module docstring; `N` is a variable here and rung 4 (`#2296`) is what
instantiates it.

⚠️ **`[DecidableEq F]` is NOT bound**, matching the `n = 3` form — the decidability the `torsion`
subgroup needs is `[DecidableEq N]`, upstairs, and the rest is supplied by `classical` inside.
⚠️ **`[W.IsElliptic]` IS bound**, and it is read off the elaborated type rather than off the
`variable` line: `mulByNEndo`'s index mentions `genericPoint`, which exists only for an elliptic
curve, and `(W⁄N).IsElliptic`, which `…_of_card` over `N` wants, is synthesised from it.

⚠️ **`hS` is read over `N` and not over `F`, deliberately.**  The `F`-form implies it through
`mem_torsion_baseChange_of_nsmul_eq_zero`, so this is the weaker hypothesis and the stronger
theorem; taking the `F`-form instead would drag `[DecidableEq F]` into the signature for nothing.

⚠️ **`h'` is the one binder the numeral descents do not pay** — see FINDING 1: `mulByNEndo`'s index
is a transcendence statement and `functionFieldMap_mulByNEndo` needs it over both fields, where
`mulByThreeEndo`'s two numeral indices transport for free.

⚠️ **The `g₀` this returns is not the base change of the `g` obtained over `N`**, and is not claimed
to be: only its divisor identity descends. -/
theorem exists_nsmul_divisor_eq_divisor_mulByNEndo_of_galois (N : Type*) [Field N]
    [Algebra F N] [FiniteDimensional F N] [IsGalois F N] [DecidableEq N]
    {n : ℕ} (h2 : (2 : F) ≠ 0) (hn : ((n : ℤ) : F) ≠ 0)
    (h : Transcendental F (n • genericPoint (W := W)).xCoord)
    (h' : Transcendental N (n • genericPoint (W := W⁄N)).xCoord)
    (hcard : Nat.card ((W⁄N).torsion n) = n ^ 2)
    {x y : F} (hns : W.Nonsingular x y)
    (hS : Point.some (algebraMap F N x) (algebraMap F N y)
      ((W.map_nonsingular (algebraMap F N).injective x y).mpr hns) ∈ (W⁄N).torsion n)
    (hP : ∃ P : (W⁄N).Point, n • P
      = Point.some (algebraMap F N x) (algebraMap F N y)
        ((W.map_nonsingular (algebraMap F N).injective x y).mpr hns))
    {f : W.FunctionField} (hf : f ≠ 0)
    (hfdiv : divisor W f = Finsupp.single (pointClosedPoint hns.left) (n : ℤ)) :
    ∃ g₀ : W.FunctionField, g₀ ≠ 0 ∧
      n • divisor W g₀ = divisor W (mulByNEndo n h f) := by
  classical
  have hn0 : n ≠ 0 := by rintro rfl; simp at hn
  have h2' : (2 : N) ≠ 0 := algebraMap_ofNat_ne_zero h2
  have hnN : ((n : ℤ) : N) ≠ 0 := by
    rw [← map_intCast (algebraMap F N) (n : ℤ), ne_eq, map_eq_zero]
    exact_mod_cast hn
  have hns' : (W⁄N).Nonsingular (algebraMap F N x) (algebraMap F N y) :=
    (W.map_nonsingular (algebraMap F N).injective x y).mpr hns
  obtain ⟨P, hPeq⟩ := hP
  have hf' : functionFieldMap W N f ≠ 0 :=
    (map_ne_zero_iff _ (functionFieldMap_injective W N)).mpr hf
  have hfdiv' : divisor (W⁄N) (functionFieldMap W N f)
      = Finsupp.single (pointClosedPoint hns'.left) (n : ℤ) :=
    divisor_functionFieldMap_eq_single N hns.left hf hfdiv
  obtain ⟨g, hg, hgdiv⟩ :=
    exists_nsmul_divisor_eq_divisor_mulByNEndo_of_card h2' hnN h' hcard hns' hS hPeq hf' hfdiv'
  have hz : mulByNEndo n h f ≠ 0 :=
    (map_ne_zero_iff _ (mulByNEndo_injective n h)).mpr hf
  refine exists_nsmul_divisor_eq_of_functionFieldMap N hn0 hz hg ?_
  rw [hgdiv, functionFieldMap_mulByNEndo h h']
  rfl

/-- **Rung 5 of the Weil pairing at a general `n`, by descent from an abstract finite Galois `N`**:
for a nonsingular `F`-rational `n`-torsion point `S` there are a principal `f_S` with
`div f_S = n·(S)` and a nonzero `g_S` with `u · g_S ^ n = [n]∗ f_S` for a unit `u` of `F[W]`.

`exists_gS_n` (`EllipticCurves.FunctionField.NthRootOfPullbackN`) with its `hprin` discharged by the
descent step above; the general-`n` form of `exists_gS_three_general`
(`EllipticCurves.FunctionField.PullbackPrincipalityThreeGeneral`) with the tower left abstract.

⚠️ **`[DecidableEq F]` IS bound here and is not bound by the descent step** — `exists_gS_n` binds
it, and `hS` is read over `F` rather than over `N` for the same reason: once the instance is present
the bridge is free. -/
theorem exists_gS_n_of_galois (N : Type*) [Field N]
    [Algebra F N] [FiniteDimensional F N] [IsGalois F N] [DecidableEq N]
    {n : ℕ} (h2 : (2 : F) ≠ 0) (hn : ((n : ℤ) : F) ≠ 0)
    (h : Transcendental F (n • genericPoint (W := W)).xCoord)
    (h' : Transcendental N (n • genericPoint (W := W⁄N)).xCoord)
    (hcard : Nat.card ((W⁄N).torsion n) = n ^ 2)
    {x y : F} (hns : W.Nonsingular x y) (hS : Point.some x y hns ∈ W.torsion n)
    (hP : ∃ P : (W⁄N).Point, n • P
      = Point.some (algebraMap F N x) (algebraMap F N y)
        ((W.map_nonsingular (algebraMap F N).injective x y).mpr hns)) :
    ∃ f : W.FunctionField, f ≠ 0 ∧
      divisor W f = Finsupp.single (pointClosedPoint hns.left) (n : ℤ) ∧
      ∃ gS : W.FunctionField, gS ≠ 0 ∧
        ∃ u : W.CoordinateRingˣ, (u : W.CoordinateRing) • gS ^ n = mulByNEndo n h f :=
  exists_gS_n h hns hS fun _ hf hfdiv =>
    exists_nsmul_divisor_eq_divisor_mulByNEndo_of_galois N h2 hn h h' hcard hns
      (mem_torsion_baseChange_of_nsmul_eq_zero N hns (mem_torsion_iff.mp hS)) hP hf hfdiv

/-! ## Recovery -/

section Recovery

omit [DecidableEq F] in
/-- **`exists_nsmul_divisor_eq_divisor_mulByThreeEndo_of_galois`
(`EllipticCurves.FunctionField.PullbackPrincipalityThreeGeneral`) is a corollary** — its statement
verbatim, `omit` included, proved from the general form. -/
example (N : Type*) [Field N] [Algebra F N] [FiniteDimensional F N] [IsGalois F N] [DecidableEq N]
    (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) {x y : F}
    (h : W.Nonsingular x y) (hcard : Nat.card ((W⁄N).torsion 3) = 9)
    (hP : ∃ P : (W⁄N).Point, (3 : ℕ) • P
      = Point.some (algebraMap F N x) (algebraMap F N y)
        ((W.map_nonsingular (algebraMap F N).injective x y).mpr h))
    (hx : W.Ψ₃.eval x = 0)
    {f : W.FunctionField} (hf : f ≠ 0)
    (hfdiv : divisor W f = Finsupp.single (pointClosedPoint h.left) (3 : ℤ)) :
    ∃ g₀ : W.FunctionField, g₀ ≠ 0 ∧
      3 • divisor W g₀ = divisor W (mulByThreeEndo h2 h3 f) := by
  have h2' : (2 : N) ≠ 0 := algebraMap_ofNat_ne_zero h2
  have h3' : (3 : N) ≠ 0 := algebraMap_ofNat_ne_zero h3
  have hx' : (W⁄N).Ψ₃.eval (algebraMap F N x) = 0 := by
    rw [show (W⁄N) = W.map (algebraMap F N) from rfl, WeierstrassCurve.map_Ψ₃,
      Polynomial.eval_map_apply, hx, map_zero]
  have hS : Point.some (algebraMap F N x) (algebraMap F N y)
      ((W.map_nonsingular (algebraMap F N).injective x y).mpr h) ∈ (W⁄N).torsion 3 :=
    mem_torsion_three_some_iff'.mpr hx'
  obtain ⟨g₀, hg₀, hdiv⟩ :=
    exists_nsmul_divisor_eq_divisor_mulByNEndo_of_galois (W := W) (n := 3) N h2
      (by exact_mod_cast h3) (transcendental_xCoord_three_nsmul h2 h3)
      (transcendental_xCoord_three_nsmul h2' h3') (by simpa using hcard) h hS hP hf
      (by exact_mod_cast hfdiv)
  exact ⟨g₀, hg₀, by rwa [mulByNEndo_three h2 h3] at hdiv⟩

end Recovery

end WeierstrassCurve.Affine
