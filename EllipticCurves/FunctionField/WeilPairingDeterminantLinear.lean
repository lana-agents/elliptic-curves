/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import EllipticCurves.FunctionField.WeilPairingDeterminantCharacter

/-!
# `e_3(α x, α y) = e_3(x, y) ^ det α` for an arbitrary `ZMod 3`-linear `α`

Silverman *AEC* III.8.1(e) is usually read as a statement about the Galois representation: the
determinant of `ρ_{E,n}` is the cyclotomic character.  That reading is a **corollary** of a fact
about the pairing alone, in which no Galois group appears:

> an alternating bilinear form on a free module of rank `2` transforms under an endomorphism `α` by
> the `det α`-th power.

This file proves that fact at `n = 3`, for an arbitrary `ZMod 3`-linear endomorphism of `E[3]`:

```
e_3(α x, α y) = e_3(x, y) ^ det α        for all α : E[3] →ₗ[ZMod 3] E[3] and all x y ∈ E[3].
```

## ⚠️ This is optional, and nothing in this development consumes it

`#955` planned `det ρ_{E,3} = χ_3` as three rungs and called this one *"the only rung with real
content"*.  That was wrong: `#958` (`EllipticCurves.FunctionField.WeilPairingDeterminantCharacter`,
merged) proves `galoisDetMod 3 = χ_3` without it, by reducing `LinearEquiv.det` to a `2 × 2` matrix
determinant with `LinearMap.det_toMatrix` and quoting `#951`'s coordinate computation of that
matrix.  ⚠️ **So the statement below is a genuine generalisation with no consumer**, and it is
recorded as such rather than presented as infrastructure.  Its value is prospective: a general-`n`
or `ℓ`-adic treatment wanting the transformation law without a Galois group has to prove exactly
this.

⚠️ The clause this paragraph used to carry — *"`galoisDetMod_three_eq_galoisModularCyclotomicChar`
becomes the special case `α = ρ_{E,3}(σ)` of it"* — is **false**, and it was false when it was
written.  `#958`'s theorem is an identity of *monoid homomorphisms*
`(F ≃ₐ[S] F) →* (ZMod 3)ˣ`; the headline below instantiated at `α = ρ_{E,3}(σ)` is an equation
between two *pairing values*, in which `galoisModularCyclotomicChar` does not occur at all.  Those
are different propositions and no instantiation turns the first into the second.

What the headline actually is: the **Galois-free half** of `#958`.  The other half is
`galoisModularCyclotomicChar_three_eq_det`
(`EllipticCurves.FunctionField.WeilPairingDeterminant`, consumed there by
`exists_smul_eq_zsmul_add_zsmul_and_det_three_eq`), which is where Galois-equivariance of `e_3` and
the definition of `χ_3` are spent; `#958` combines the two.  ⚠️ **Nothing this file adds reaches
that half** — `det_eq_intCast_of_zsmul_add_zsmul` below is the matrix step and nothing more — and
`#958` neither depends on this file nor is an instance of it.

⚠️ The weaker reading a few lines above — that the Galois statement is a **corollary** of a fact
about the pairing alone — is not affected and stays: `det ρ = χ` does follow from the pairing law
*together with* the Galois inputs, and "corollary" does not claim it needs nothing else.  It is
*"special case"* that overreaches.

## The route taken, and why

`#957` offered two routes and asked whichever is taken to be named.

* **Route 1, coordinates — taken.**  Pick a pair `(P, T)` with `e_3(P, T) ≠ 1`, write everything in
  integer coordinates against it, and let `weilPairingThree_zsmul_add_zsmul` (`#951`) do the
  bilinear expansion.  Everything below is then integer algebra: the exponent identity is
  `(ap + cq)(br + ds) − (bp + dq)(ar + cs) = (ad − bc)(ps − qr)`, closed by `ring`.
* **Route 2, `Mathlib.LinearAlgebra.Alternating`** — not taken.  It needs a `ZMod 3`-linear
  isomorphism `Additive (μ_3 F) ≃ₗ[ZMod 3] ZMod 3` to view `e_3` as an `AlternatingMap`, which is a
  second non-canonical choice on top of the basis, and it would buy nothing here: alternation and
  antisymmetry are already consumed, in coordinates, inside `weilPairingThree_zsmul_add_zsmul`.

⚠️ **`#957`'s thread predicted the one real cost of route 1 and the prediction came true.**  Its
2026-08-24 comment says that if `#958` landed the `Module.Basis.ofEquivFun` form of the pairing
basis rather than the `Module.Basis.repr` form, then *"whoever takes this rung inherits the `repr`
computation after all and should re-price accordingly"*.  `#958` did land the `ofEquivFun` form
(`basisTorsionThreeOfPairing` is `Module.Basis.ofEquivFun (torsionThreePairingEquiv …).symm`), and
`basisTorsionThreeOfPairing_repr_of_eq_zsmul_add_zsmul` below is that inherited computation.  It is
five lines, so the re-pricing is small, but it is real and it is the only place this file does
linear algebra rather than integer algebra.

The basis itself is **reused, not rebuilt**: `basisTorsionThreeOfPairing` and its two
characterising lemmas come from `#958`'s file unchanged, which is what `#957` asked for.

## Why `LinearMap` and not `LinearEquiv`

`#957` asked for the statement about `α : E[3] ≃ₗ[ZMod 3] E[3]`.  The proof never inverts `α`, so
the statement is proved for `α : E[3] →ₗ[ZMod 3] E[3]` and the equivalence version is a one-line
corollary through `LinearEquiv.coe_det`.  ⚠️ The endomorphism version is **strictly stronger and not
merely more general**: at a non-invertible `α` it says `e_3(α x, α y) = 1` for all `x`, `y`, i.e.
that a rank-`≤ 1` image is isotropic, which the equivalence version cannot state.

⚠️ Note also that `ZMod 3`-linearity of `α` is not an extra assumption on an additive map: `E[3]` is
a `ZMod 3`-module through `torsionZModModule`, which is `AddCommGroup.zmodModule` and carries no
hypothesis, so every additive endomorphism of `E[3]` is `ZMod 3`-linear.  What `α : E[3] →ₗ …`
buys over `α : E[3] →+ E[3]` is not strength, it is that `LinearMap.det α` can be written down.

## Main results

* `zpow_rootsOfUnity_eq_of_intCast_eq` — a power of a `p`-th root of unity depends on its exponent
  only mod `p`.  Root namespace: no curve, no field, no pairing.
* `basisTorsionThreeOfPairing_repr_of_eq_zsmul_add_zsmul` — the coordinates of `u • P + v • T`
  against the pairing basis `(P, T)` are `(u mod 3, v mod 3)`.
* `weilPairingThree_linearMap_of_zsmul_add_zsmul` — the transformation law with `α`'s matrix carried
  in hypotheses, as four integers.
* `det_eq_intCast_of_zsmul_add_zsmul` — that matrix's determinant **is** `LinearMap.det α`.
* `weilPairingThree_linearMap` — the headline, with nothing assumed about `α`.
* `weilPairingThree_linearEquiv` — the headline for `α : E[3] ≃ₗ[ZMod 3] E[3]`, which is the form
  `#957` asked for and the form Silverman III.8.1(e) is a corollary of.
* `exists_weilPairingThree_linearEquiv_det_ne_one` — the non-vacuity certificate against a
  constantly-`1` pairing.  ⚠️ The `#### On a curve that exists` block additionally rules out an
  empty hypothesis class, which is a different risk; see the `Non-vacuity` section below.
* `not_forall_weilPairingThree_linearMap_of_zsmul_add_zsmul`,
  `not_forall_det_eq_intCast_of_zsmul_add_zsmul` — refutations R1 and R3, as theorems rather than
  as compiler transcripts.

## Scope

* **`n = 3` only.**  ⚠️ The `n = 2` analogue is *not* stated.  This bullet used to say the reason
  was infrastructural rather than mathematical, namely that
  `EllipticCurves.TateModule.DeterminantMod` supplies `finrank_torsion_three` and
  `finite_torsion_three_zmod` and *"has **no `n = 2` counterpart** — a tree-wide grep for
  `finrank_torsion_two`, `basisTorsionTwo` and `finite_torsion_two_zmod` finds no declaration by any
  of those names, in this module or anywhere else — so there is no `ZMod 2`-basis of `E[2]` to run
  the argument against."*  ⚠️ **That grep now returns three hits and the infrastructural reason is
  spent**: `EllipticCurves.TateModule.DeterminantModSmooth` (`#1240`) states
  `finrank_torsion_two`, `finite_torsion_two_zmod` and `basisTorsionTwo` under those exact names.
  ⚠️ **That does not make the `n = 2` analogue available**, and nothing here should be read as
  saying so: the missing basis was one blocker, the argument of this file is the other, and only the
  first has been removed.  ⚠️ It is
  worth recording that the `n = 2` statement would **not** be content-free, contrary to the usual
  reading: `(ZMod 2)ˣ` is trivial, so the *equivalence* version degenerates to "every automorphism
  of `E[2]` preserves `e_2`", but the *endomorphism* version does not, since `LinearMap.det α` can
  be `0` there.
* **General `n` is out of scope** and is not merely unproved here: this development has the Weil
  pairing at `n = 2` and `n = 3` and nowhere else.  ⚠️ The ceiling is the two-slot pairing itself
  at general `n`, and `#938`'s double obstruction at composite `n`.
  ⚠️ **The reason this used to give for general `n` was wrong** — it read *"`#404`'s `ωₙ` crux for
  the pairing itself"*.  `[n]∗` needs no `y`-coordinate division polynomial (`#1165`), and the
  rung-5 root and the whole rung-6 translation slot are now stated at every `n`, with the
  non-constancy side condition discharged at every `3`-smooth `n` (`#1304`, `#1308`).  What general
  `n` waits on here is the **two-slot** pairing itself: `weilPairingN` and `weilPairingNHom` are
  names this tree declares at no index but `2` and `3` (`WeilPairingFunctionTwo`,
  `WeilPairingFunctionThree`, `#922`/`#925`), and the `[IsAlgClosed F]` they carry enters through
  `hprin`, whose only producers are `exists_gS_{two,three}_of_isAlgClosed` (`#791`/`#825`).  ⚠️
  Everything this bullet says about a **second** obstruction is untouched and is still right; only
  the first one is renamed.
* ⚠️ **This does not touch `EllipticCurves.TateModule.Determinant`.**  `galoisDetTwo` there is
  `LinearEquiv.det` on the `2`-adic Tate module, and identifying it with the cyclotomic character
  needs the pairing at every level `E[2 ^ k]`.  Nothing below is a step towards that.

## Non-vacuity (`#916`)

The headline is an equation between two pairing values and would be satisfied by a pairing that was
constantly `1`, so it needs a certificate that the two sides can differ.  ⚠️ The certificate is
`exists_weilPairingThree_linearEquiv_det_ne_one` below, and it is stronger than an existence claim
about `e_3`: it produces a **`P`, a `T` and an `α`** with

* `e_3(P, T) ≠ 1`,
* `det α ≠ 1` in `ZMod 3`, and
* `e_3(α P, α T) ≠ e_3(P, T)`,

so the headline at that `α` is not the trivial statement that `α` preserves the pairing.  The `α`
is the basis swap `P ↔ T`, whose determinant is `−1`; ⚠️ that is precisely the antisymmetry of `e_3`
read as a determinant, so the certificate exhibits the file's own content rather than a side fact.
The only step closed by `decide` is the arithmetic `((0 * 0 − 1 * 1 : ℤ) : ZMod 3) ≠ 1` at the very
end; everything before it consumes `det_eq_intCast_of_zsmul_add_zsmul` and
`weilPairingThree_linearEquiv` (`#957`).

⚠️ **That certificate does not close the other half of `#916`, and an earlier version of this
section read as though it did.**  Every statement in this file carries `[IsAlgClosed F]` and
`[W.IsElliptic]`, and a theorem quantified over an *empty* class of instances is vacuously true no
matter how many inequalities it asserts.  The `#### On a curve that exists` block at the end of the
file rules that out on `#936`'s curve `y² + y = x³` over `AlgebraicClosure ℚ`, by **applying** the
certificate rather than by `rfl`, `decide` or `norm_num`.  ⚠️ The two are independent: the first
rules out a constantly-`1` pairing, the second rules out an empty hypothesis class, and neither
implies the other.

⚠️ **Three refutations.**  R1 and R3 are *proved*, as the two `not_forall_…` theorems below: the
statements really are false without their `hPT`, not merely unproved, so no compiler transcript is
needed to establish that they are load-bearing.  Deletion transcripts are given as well, because
the board asks for them, and they are measured against this file **as committed**.  ⚠️ In each
transcript the `path:line:col:` prefix of every `error:` line is elided and **nothing else is**;
each deletion also cascades into the consumers further down the file, and only the errors belonging
to the theorem under test are shown.

**R1 — delete `hPT` from `weilPairingThree_linearMap_of_zsmul_add_zsmul`.**  Proved false by
`not_forall_weilPairingThree_linearMap_of_zsmul_add_zsmul`.  The deletion transcript opens

```
error: Unknown identifier `hPT`
error: Unknown identifier `hPT`
```

— the two `exists_zsmul_add_zsmul_eq_three` calls that give `x` and `y` their coordinates.  ⚠️ The
rest of R1's transcript is **not quoted and should not be**: with `hPT` gone, `P` and `T` are no
longer determined by unification, so the following `rw`s report goals full of metavariables
(`hx : x = a • ?m.241 • P + c • ?m.123`) and the proof finally hits a `whnf` heartbeat timeout.
That is elaboration noise, not a residual goal, and reading it as one would be exactly the mistake
this board records as *"a type mismatch is never a deletion test"*.  The theorem
`not_forall_…` is the refutation; the transcript only shows where the input was consumed.

**R2 — delete `hT` from `weilPairingThree_linearMap_of_zsmul_add_zsmul`.**  Knowing `α` on `P`
alone does not determine `α`:

```
error: Unknown identifier `hT`
error: Unknown identifier `hT`
```

both inside the `hαx`/`hαy` steps, which is precisely the claim that the second column of the
matrix is used.  ⚠️ No falsity theorem is offered for R2 and one would be misleading: with `hT`
deleted, `q` and `s` become unconstrained universally-quantified integers, so the statement is
false for the boring reason that its conclusion mentions variables its hypotheses no longer touch.
R1 and R3 fail for a substantive reason and R2 for a syntactic one, and the difference is worth
keeping.

**R3 — delete `hPT` from `det_eq_intCast_of_zsmul_add_zsmul`.**  Proved false by
`not_forall_det_eq_intCast_of_zsmul_add_zsmul`.  This is the clean deletion test of the three,
leaving a **goal** and not a type mismatch, with both matrix hypotheses surviving:

```
error: Unknown identifier `hPT`
error: unsolved goals
F : Type u_1
inst✝² : Field F
inst✝¹ : IsAlgClosed F
W : Affine F
inst✝ : WeierstrassCurve.IsElliptic W
h2 : 2 ≠ 0
h3 : 3 ≠ 0
P T : ↥(W.torsion 3)
α : ↥(W.torsion 3) →ₗ[ZMod 3] ↥(W.torsion 3)
p q r s : ℤ
hP : α P = p • P + r • T
hT : α T = q • P + s • T
⊢ LinearMap.det α = ↑(p * s - q * r)
```

The single unknown identifier is the `basisTorsionThreeOfPairing h2 h3 hPT` that
`LinearMap.det_toMatrix` is applied to: without `hPT` there is no basis, which is a different
failure from R1's, where the basis is never mentioned.

## ⚠️ Where alternation is load-bearing, and how that is measured here

`weilPairingThree_self` and `weilPairingThree_swap` — alternation and antisymmetry — are consumed
one file down, inside `weilPairingThree_zsmul_add_zsmul`, so no deletion in *this* file can reach
them.  What this file can measure is their consequence, and
`exists_weilPairingThree_linearEquiv_det_ne_one`'s third clause is exactly it: at the basis swap
`α : P ↔ T` the headline forces `e_3(α P, α T) = e_3(P, T) ^ 2 ≠ e_3(P, T)`.  ⚠️ **A symmetric
pairing would make that clause false**, so the certificate is not decoration: it is the statement
that the form `e_3` is alternating rather than symmetric, read off the determinant `−1` of a
transposition.

## References

* [J. H. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.8.1(e).
* `EllipticCurves.FunctionField.WeilPairingDeterminant` (`#951`) — the bilinear expansion
  `weilPairingThree_zsmul_add_zsmul`, the spanning lemma `exists_zsmul_add_zsmul_eq_three`, and
  `exists_weilPairingThree_ne_one`.
* `EllipticCurves.FunctionField.WeilPairingDeterminantCharacter` (`#958`) — the pairing basis
  `basisTorsionThreeOfPairing` and the Galois specialisation of the headline.
* `EllipticCurves.TateModule.DeterminantMod` (`#956`) — `torsionZModModule` and
  `finrank_torsion_three`.
-/


/-- **A power of a `p`-th root of unity depends on its exponent only mod `p`.**

⚠️ Unlike `orderOf_rootsOfUnity_eq_of_prime`, which needs `ζ ≠ 1` and `p` prime to pin the order at
exactly `p`, this needs neither: `orderOf ζ ∣ p` holds for every element of `rootsOfUnity p M`, and
a divisor is all the congruence needs.  That is why the headline below can be stated for arbitrary
`x` and `y`, including pairs at which `e_3(x, y) = 1`.

Stated at the root namespace over `[CommMonoid M]`: it mentions no curve, no field and no
pairing. -/
theorem zpow_rootsOfUnity_eq_of_intCast_eq {M : Type*} [CommMonoid M] {p : ℕ}
    (ζ : rootsOfUnity p M) {m n : ℤ} (hmn : (m : ZMod p) = (n : ZMod p)) : ζ ^ m = ζ ^ n := by
  have hpow : ζ ^ p = 1 := by
    refine Subtype.ext (Units.ext ?_)
    have hmem := ζ.2
    rw [mem_rootsOfUnity] at hmem
    push_cast
    exact congrArg (Units.val) hmem
  have hdvd : (orderOf ζ : ℤ) ∣ (p : ℤ) :=
    Int.natCast_dvd_natCast.mpr (orderOf_dvd_of_pow_eq_one hpow)
  exact zpow_eq_zpow_iff_modEq.mpr
    (Int.ModEq.of_dvd hdvd ((ZMod.intCast_eq_intCast_iff _ _ p).mp hmn))

namespace WeierstrassCurve.Affine

open CoordinateRing

section LinearDeterminant

variable {F : Type*} [Field F] [IsAlgClosed F] {W : Affine F} [W.IsElliptic]

open Classical in
/-- **The coordinates of `u • P + v • T` against the pairing basis `(P, T)` are `(u, v)` mod `3`.**

⚠️ This is the `Module.Basis.repr` computation that `#957`'s thread predicted would be inherited if
`#958` landed `basisTorsionThreeOfPairing` in its `Module.Basis.ofEquivFun` form.  It did, and this
is the cost: `#951` spans `E[3]` with **integer** coefficients, and `Int.cast_smul_eq_zsmul` is the
only bridge from that `ℤ`-action to the `ZMod 3`-action `Module.Basis.repr` speaks. -/
theorem basisTorsionThreeOfPairing_repr_of_eq_zsmul_add_zsmul (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0)
    {P T : W.torsion 3} (hPT : weilPairingThree h2 h3 P T ≠ 1) {u v : ℤ} {Q : W.torsion 3}
    (hQ : Q = u • P + v • T) :
    (basisTorsionThreeOfPairing h2 h3 hPT).repr Q 0 = (u : ZMod 3) ∧
      (basisTorsionThreeOfPairing h2 h3 hPT).repr Q 1 = (v : ZMod 3) := by
  have hQ' : Q = (u : ZMod 3) • (basisTorsionThreeOfPairing h2 h3 hPT) 0
      + (v : ZMod 3) • (basisTorsionThreeOfPairing h2 h3 hPT) 1 := by
    rw [basisTorsionThreeOfPairing_zero, basisTorsionThreeOfPairing_one,
      Int.cast_smul_eq_zsmul, Int.cast_smul_eq_zsmul]
    exact hQ
  rw [hQ']
  constructor <;> simp

open Classical in
/-- **The transformation law, with `α`'s matrix carried in hypotheses.**

If `e_3(P, T) ≠ 1` and `α P = p • P + r • T`, `α T = q • P + s • T`, then

```
e_3(α x, α y) = e_3(x, y) ^ (p * s − q * r)      for every x, y ∈ E[3].
```

⚠️ **No linear algebra happens here.**  `x` and `y` get integer coordinates from `#951`'s
spanning lemma, `α` is pushed through them by `map_zsmul`, and the whole content is the integer
identity

```
(a * p + c * q) * (b * r + d * s) − (b * p + d * q) * (a * r + c * s)
  = (a * d − b * c) * (p * s − q * r) ,
```

which `ring` closes.  ⚠️ That identity is the *multiplicativity of the `2 × 2` determinant* written
out; the determinant enters this file through it and not through `Matrix.det`.

⚠️ `hPT` is load-bearing and its absence makes the statement false, not merely unproved: at
`P = T = 0` every quadruple satisfies both matrix hypotheses. -/
theorem weilPairingThree_linearMap_of_zsmul_add_zsmul (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0)
    {P T : W.torsion 3} (hPT : weilPairingThree h2 h3 P T ≠ 1)
    (α : W.torsion 3 →ₗ[ZMod 3] W.torsion 3) {p q r s : ℤ}
    (hP : α P = p • P + r • T) (hT : α T = q • P + s • T) (x y : W.torsion 3) :
    weilPairingThree h2 h3 (α x) (α y)
      = weilPairingThree h2 h3 x y ^ (p * s - q * r) := by
  obtain ⟨a, c, hx⟩ := exists_zsmul_add_zsmul_eq_three h2 h3 hPT x
  obtain ⟨b, d, hy⟩ := exists_zsmul_add_zsmul_eq_three h2 h3 hPT y
  have hαx : α x = (a * p + c * q) • P + (a * r + c * s) • T := by
    rw [hx, map_add, map_zsmul, map_zsmul, hP, hT]; module
  have hαy : α y = (b * p + d * q) • P + (b * r + d * s) • T := by
    rw [hy, map_add, map_zsmul, map_zsmul, hP, hT]; module
  rw [hαx, hαy, weilPairingThree_zsmul_add_zsmul, hx, hy, weilPairingThree_zsmul_add_zsmul,
    ← zpow_mul]
  congr 1
  ring

open Classical in
/-- **The matrix in a pairing basis has determinant `LinearMap.det α`.**

This is the only place the file mentions `Matrix`, and it is where `#958`'s basis is spent:
`LinearMap.det_toMatrix` against `basisTorsionThreeOfPairing h2 h3 hPT`, then `Matrix.det_fin_two`,
then the four entries read off by `basisTorsionThreeOfPairing_repr_of_eq_zsmul_add_zsmul`.

⚠️ The entries are transposed relative to the hypotheses, and deliberately so: `LinearMap.toMatrix`
puts `α (b j)`'s coordinates in **column** `j`, so `hP` supplies the first column `(p, r)` and `hT`
the second `(q, s)`.  The determinant `p * s − q * r` is the same either way, which is why the
statement can be read off `hP` and `hT` without the transposition being visible in it. -/
theorem det_eq_intCast_of_zsmul_add_zsmul (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0)
    {P T : W.torsion 3} (hPT : weilPairingThree h2 h3 P T ≠ 1)
    (α : W.torsion 3 →ₗ[ZMod 3] W.torsion 3) {p q r s : ℤ}
    (hP : α P = p • P + r • T) (hT : α T = q • P + s • T) :
    LinearMap.det α = ((p * s - q * r : ℤ) : ZMod 3) := by
  have h0 := basisTorsionThreeOfPairing_zero h2 h3 hPT
  have h1 := basisTorsionThreeOfPairing_one h2 h3 hPT
  rw [← LinearMap.det_toMatrix (basisTorsionThreeOfPairing h2 h3 hPT), Matrix.det_fin_two]
  simp only [LinearMap.toMatrix_apply, h0, h1]
  obtain ⟨hp, hr⟩ := basisTorsionThreeOfPairing_repr_of_eq_zsmul_add_zsmul h2 h3 hPT hP
  obtain ⟨hq, hs⟩ := basisTorsionThreeOfPairing_repr_of_eq_zsmul_add_zsmul h2 h3 hPT hT
  rw [hp, hr, hq, hs]
  push_cast
  ring

open Classical in
/-- **The headline: `e_3(α x, α y) = e_3(x, y) ^ det α`, with nothing assumed about `α`.**

Silverman *AEC* III.8.1(e) with the Galois group removed.  A pairing-nonvanishing pair is produced
inside the proof by `exists_weilPairingThree_ne_one` (`#951`), so no basis, no pair and no matrix
appears in the statement.

⚠️ **The exponent is `(LinearMap.det α).val : ℕ` and not an integer**, because `det α` lives in
`ZMod 3` and only its residue is meaningful: `e_3(x, y)` is a cube root of unity, so
`zpow_rootsOfUnity_eq_of_intCast_eq` makes the two readings agree.

⚠️ **True at non-invertible `α` too**, where it reads `e_3(α x, α y) = 1`: the image of such an `α`
is isotropic for `e_3`.  See the module docstring — the `LinearEquiv` version below cannot state
that. -/
theorem weilPairingThree_linearMap (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0)
    (α : W.torsion 3 →ₗ[ZMod 3] W.torsion 3) (x y : W.torsion 3) :
    weilPairingThree h2 h3 (α x) (α y)
      = weilPairingThree h2 h3 x y ^ (LinearMap.det α).val := by
  obtain ⟨P, T, hPT⟩ := exists_weilPairingThree_ne_one (W := W) h2 h3
  obtain ⟨p, r, hP⟩ := exists_zsmul_add_zsmul_eq_three h2 h3 hPT (α P)
  obtain ⟨q, s, hT⟩ := exists_zsmul_add_zsmul_eq_three h2 h3 hPT (α T)
  rw [weilPairingThree_linearMap_of_zsmul_add_zsmul h2 h3 hPT α hP hT x y, ← zpow_natCast]
  refine zpow_rootsOfUnity_eq_of_intCast_eq _ ?_
  rw [det_eq_intCast_of_zsmul_add_zsmul h2 h3 hPT α hP hT]
  push_cast
  simp [ZMod.natCast_val]

open Classical in
/-- **The headline for a `ZMod 3`-linear automorphism**, which is the statement `#957` asked for.

A one-line corollary of the endomorphism version above: `LinearEquiv.coe_det` says
`(LinearEquiv.det α : ZMod 3)` is `LinearMap.det (α : E[3] →ₗ[ZMod 3] E[3])`, and that version is
stated about exactly that.

⚠️ The clause this docstring used to carry — copy-paste, with the quotation left unemphasised
because it contains emphasis of its own:

> the one Silverman *AEC* III.8.1(e) is the `α = ρ_{E,3}(σ)` case of

is **false** in the direction it asserts, for the reason given in the
module docstring: instantiating this at `α = ρ_{E,3}(σ)` produces an equation between two pairing
values, not `galoisDetMod 3 σ = χ_3 σ`.  This is the **Galois-free half** of
`galoisDetMod_three_eq_galoisModularCyclotomicChar`; the other half is
`galoisModularCyclotomicChar_three_eq_det`, which this file does not touch.

⚠️ That other half used to be described here as *"the half that is **missing**"*, and it was
false when it was written: the theorem is merged, in
`EllipticCurves.FunctionField.WeilPairingDeterminant` (`#951`), which is in this file's own import
closure.  The module docstring above states the same split correctly (*"The other half is …"*), so
one commit wrote both readings into one file and only the declaration docstring got it wrong. -/
theorem weilPairingThree_linearEquiv (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0)
    (α : W.torsion 3 ≃ₗ[ZMod 3] W.torsion 3) (x y : W.torsion 3) :
    weilPairingThree h2 h3 (α x) (α y)
      = weilPairingThree h2 h3 x y ^ ((LinearEquiv.det α : (ZMod 3)ˣ) : ZMod 3).val := by
  have h := weilPairingThree_linearMap h2 h3 (α : W.torsion 3 →ₗ[ZMod 3] W.torsion 3) x y
  rwa [← LinearEquiv.coe_det] at h

end LinearDeterminant

/-! ### Non-vacuity

Two certificates, closing two different risks, and neither replaces the other.

* `exists_weilPairingThree_linearEquiv_det_ne_one` is stated over an **arbitrary** `F` and `W`,
  because nothing here needs a Galois group and so nothing here needs a base field `S` with
  `Gal(F/S)` non-trivial — the reason `#951` and `#958` had to name `S = ℚ`.  It closes the risk
  this file actually runs: the headline is an equation between two pairing values and would also
  hold of a pairing that was constantly `1`.  ⚠️ It restates the headline in full rather than
  projecting out of an `obtain` (`#916`), and adds the two inequalities that make the headline
  non-trivial at that `α`.
* ⚠️ **That is not what `#916` asks for, and an earlier version of this section gave the first
  bullet as the reason no named curve appears.**  A statement quantified over
  `[IsAlgClosed F] [W.IsElliptic]` is vacuous if nothing inhabits those classes, and only a curve
  that exists rules that out.  The `#### On a curve that exists` block below is that curve —
  `y² + y = x³` over `AlgebraicClosure ℚ`, this front's standard certificate curve — and it is a
  *different* fact from the first bullet rather than a weaker restatement of it.

⚠️ **The `open Classical in` on each declaration here is load-bearing and is house style for the
whole `WeilPairing*` family.**  These files carry no `[DecidableEq F]` in their `variable` blocks,
so `weilPairingThree`'s decidability argument is filled by `Classical.propDecidable` and baked into
every statement.  A consumer that *does* have a real `DecidableEq F` in scope gets
`synthesized type class instance is not definitionally equal to expression inferred by typing
rules`; the fix is to mirror the section header rather than to fight it, and the named-curve
block below is the worked example of doing so.
-/

section Nonvacuity

variable {F : Type*} [Field F] [IsAlgClosed F] {W : Affine F} [W.IsElliptic]

open Classical in
/-- **⚠️ THE LOAD-BEARING CERTIFICATE: the headline is not `e_3(α x, α y) = e_3(x, y)` in
disguise.**

There are a `P`, a `T` and a `ZMod 3`-linear automorphism `α` of `E[3]` with `e_3(P, T) ≠ 1`,
`det α ≠ 1`, `e_3(α P, α T) ≠ e_3(P, T)`, and the headline holding at all three.

The `α` is the swap `P ↔ T` in the pairing basis, whose determinant is `−1`; ⚠️ so the certificate
is the antisymmetry of `e_3` read as a determinant, which is the file's own content rather than a
side fact.  The `e_3(α P, α T) ≠ e_3(P, T)` clause is what rules out the degenerate reading — it
says the exponent `det α` is doing work at this `α`, not merely being `1`.

⚠️ Only the final arithmetic step `((0 * 0 − 1 * 1 : ℤ) : ZMod 3) ≠ 1` is closed by `decide`; the
determinant is computed by `det_eq_intCast_of_zsmul_add_zsmul` and the headline instance is
`weilPairingThree_linearEquiv` (`#957`). -/
theorem exists_weilPairingThree_linearEquiv_det_ne_one (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) :
    ∃ (P T : W.torsion 3) (α : W.torsion 3 ≃ₗ[ZMod 3] W.torsion 3),
      weilPairingThree h2 h3 P T ≠ 1 ∧
        ((LinearEquiv.det α : (ZMod 3)ˣ) : ZMod 3) ≠ 1 ∧
        weilPairingThree h2 h3 (α P) (α T) ≠ weilPairingThree h2 h3 P T ∧
        weilPairingThree h2 h3 (α P) (α T)
          = weilPairingThree h2 h3 P T ^ ((LinearEquiv.det α : (ZMod 3)ˣ) : ZMod 3).val := by
  obtain ⟨P, T, hPT⟩ := exists_weilPairingThree_ne_one (W := W) h2 h3
  set bas := basisTorsionThreeOfPairing h2 h3 hPT with hbas
  have hP : bas 0 = P := basisTorsionThreeOfPairing_zero h2 h3 hPT
  have hT : bas 1 = T := basisTorsionThreeOfPairing_one h2 h3 hPT
  set α := bas.equiv bas (Equiv.swap 0 1) with hα
  have hαP : (α : W.torsion 3 →ₗ[ZMod 3] W.torsion 3) P = (0 : ℤ) • P + (1 : ℤ) • T := by
    rw [← hP]; simp [hα, Module.Basis.equiv_apply, hT]
  have hαT : (α : W.torsion 3 →ₗ[ZMod 3] W.torsion 3) T = (1 : ℤ) • P + (0 : ℤ) • T := by
    rw [← hT]; simp [hα, Module.Basis.equiv_apply, hP]
  have hdet : ((LinearEquiv.det α : (ZMod 3)ˣ) : ZMod 3) = ((0 * 0 - 1 * 1 : ℤ) : ZMod 3) := by
    rw [LinearEquiv.coe_det, det_eq_intCast_of_zsmul_add_zsmul h2 h3 hPT _ hαP hαT]
  refine ⟨P, T, α, hPT, by rw [hdet]; decide, ?_, weilPairingThree_linearEquiv h2 h3 α P T⟩
  -- `α P = T` and `α T = P`, so the left side is `e_3(T, P) = e_3(P, T)⁻¹`.
  have hswap : weilPairingThree h2 h3 (α P) (α T) = (weilPairingThree h2 h3 P T)⁻¹ := by
    have hαP' : α P = T := by simpa using hαP
    have hαT' : α T = P := by simpa using hαT
    rw [hαP', hαT', weilPairingThree_swap h2 h3]
  rw [hswap]
  intro hEq
  -- `ζ⁻¹ = ζ` forces `ζ ^ 2 = 1`, hence `3 = orderOf ζ ∣ 2`.
  have hsq : weilPairingThree h2 h3 P T ^ (2 : ℕ) = 1 := by
    rw [pow_two]
    nth_rewrite 1 [← hEq]
    exact inv_mul_cancel _
  have := orderOf_dvd_of_pow_eq_one hsq
  rw [orderOf_rootsOfUnity_eq_of_prime Nat.prime_three hPT] at this
  omega

open Classical in
/-- **⚠️ REFUTATION R1: `hPT` is not removable from
`weilPairingThree_linearMap_of_zsmul_add_zsmul` — without it the statement is FALSE.**

⚠️ This is a *proof* that the hypothesis is load-bearing, not a failed compile.  The witness is the
degenerate pair `P = T = 0`, at which both matrix hypotheses hold for **every** quadruple
`(p, q, r, s)`: take `α = id` and `p = q = r = s = 0`, and the `hPT`-free statement asserts
`e_3(x, y) = e_3(x, y) ^ 0 = 1` for all `x` and `y`, which `exists_weilPairingThree_ne_one`
contradicts.

⚠️ Note where the falsity comes from: it is the *hypotheses* that degenerate, not the conclusion.
That is why weakening `hPT` is not an option either — any pair that fails to span `E[3]` leaves the
quadruple underdetermined. -/
theorem not_forall_weilPairingThree_linearMap_of_zsmul_add_zsmul (h2 : (2 : F) ≠ 0)
    (h3 : (3 : F) ≠ 0) :
    ¬ ∀ (P T : W.torsion 3) (α : W.torsion 3 →ₗ[ZMod 3] W.torsion 3) (p q r s : ℤ),
        α P = p • P + r • T → α T = q • P + s • T →
          ∀ x y : W.torsion 3,
            weilPairingThree h2 h3 (α x) (α y)
              = weilPairingThree h2 h3 x y ^ (p * s - q * r) := by
  intro h
  obtain ⟨x, y, hxy⟩ := exists_weilPairingThree_ne_one (W := W) h2 h3
  exact hxy (by simpa using h 0 0 LinearMap.id 0 0 0 0 (by simp) (by simp) x y)

omit [IsAlgClosed F] [W.IsElliptic] in
open Classical in
/-- **⚠️ REFUTATION R3: `hPT` is not removable from `det_eq_intCast_of_zsmul_add_zsmul` either, and
the reason is different.**

In R1 what fails without `hPT` is that `P` and `T` need not span; here what fails is that
`basisTorsionThreeOfPairing` does not exist, so there is no basis to run `LinearMap.det_toMatrix`
against.  The falsity witness is the same degenerate pair: at `P = T = 0` with `α = id` and
`p = q = r = s = 0` the `hPT`-free statement reads `LinearMap.det id = 0`, i.e. `(1 : ZMod 3) = 0`.

⚠️ **This one needs neither `[IsAlgClosed F]` nor `[W.IsElliptic]`** — the `omit` above is measured,
not guessed; the `unusedSectionVars` linter reported both.  It is a statement about `LinearMap.det`
and a degenerate pair, and it is true over any field. -/
theorem not_forall_det_eq_intCast_of_zsmul_add_zsmul :
    ¬ ∀ (P T : W.torsion 3) (α : W.torsion 3 →ₗ[ZMod 3] W.torsion 3) (p q r s : ℤ),
        α P = p • P + r • T → α T = q • P + s • T →
          LinearMap.det α = ((p * s - q * r : ℤ) : ZMod 3) := by
  intro h
  have hid := h 0 0 LinearMap.id 0 0 0 0 (by simp) (by simp)
  simp at hid

/-! #### On a curve that exists

⚠️ Everything above carries `[IsAlgClosed F]` and `[W.IsElliptic]`, so `ℚ` cannot witness it and the
statements would all be vacuously true if nothing inhabited those classes.  The block below rules
that out on `#936`'s curve `y² + y = x³` base-changed to `AlgebraicClosure ℚ`, the same curve
`EllipticCurves.FunctionField.WeilPairingDeterminant` and
`EllipticCurves.FunctionField.WeilPairingDeterminantCharacter` use.  ⚠️ Those files' copies are
`private`, so this one is a duplicate by necessity rather than by oversight.
-/

/-- The curve `y² + y = x³` over `ℚ`, `#936`'s `n = 3` certificate curve. -/
private noncomputable def exampleCurve : Affine ℚ := ⟨0, 0, 1, 0, 0⟩

/-- An algebraically closed extension of `ℚ`.  ⚠️ Unlike `#951`'s and `#958`'s copies, no base field
`S` is named here: nothing in this file mentions a Galois group, so `Gal(F/S)` never appears. -/
private abbrev exampleField : Type := AlgebraicClosure ℚ

private instance : exampleCurve.IsElliptic := by
  rw [WeierstrassCurve.isElliptic_iff, isUnit_iff_ne_zero]
  norm_num [exampleCurve, WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈]

private lemma exampleTwo : (2 : exampleField) ≠ 0 := by norm_num

private lemma exampleThree : (3 : exampleField) ≠ 0 := by norm_num

open Classical in
/-- **The transformation law on a curve that exists** (`#916`), restated in full rather than
projected out of an `obtain`.

⚠️ This closes a *different* risk from `exists_weilPairingThree_linearEquiv_det_ne_one`: that one
rules out a constantly-`1` pairing, this one rules out an empty hypothesis class.  Neither implies
the other.

⚠️ It closes by **application** of the abstract certificate, not by `rfl`, `decide` or `norm_num`,
so it consumes the theorem it certifies (`#944`).  Its only real content beyond that is that
`exampleCurve⁄exampleField` satisfies `[IsAlgClosed F]` and `[W.IsElliptic]` at all. -/
example :
    ∃ (P T : (exampleCurve⁄exampleField).torsion 3)
      (α : (exampleCurve⁄exampleField).torsion 3 ≃ₗ[ZMod 3]
        (exampleCurve⁄exampleField).torsion 3),
      weilPairingThree exampleTwo exampleThree P T ≠ 1 ∧
        ((LinearEquiv.det α : (ZMod 3)ˣ) : ZMod 3) ≠ 1 ∧
        weilPairingThree exampleTwo exampleThree (α P) (α T)
          ≠ weilPairingThree exampleTwo exampleThree P T ∧
        weilPairingThree exampleTwo exampleThree (α P) (α T)
          = weilPairingThree exampleTwo exampleThree P T
              ^ ((LinearEquiv.det α : (ZMod 3)ˣ) : ZMod 3).val :=
  exists_weilPairingThree_linearEquiv_det_ne_one exampleTwo exampleThree

end Nonvacuity

end WeierstrassCurve.Affine
