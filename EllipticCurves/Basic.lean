/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass
import Mathlib.AlgebraicGeometry.EllipticCurve.Reduction

/-!
# Elliptic curves

The `EllipticCurves` project formalises the arithmetic of elliptic curves over
local and global fields, following Silverman's *The Arithmetic of Elliptic
Curves*. This file is not the library's root module — that is
`EllipticCurves.lean`, the `mk_all` aggregator that imports the whole library.

The project builds on Mathlib's existing theory of Weierstrass and elliptic
curves (`Mathlib.AlgebraicGeometry.EllipticCurve.*`). The two headline targets
are semi-stable reduction and the Néron–Ogg–Shafarevich criterion; neither is
finished, and neither is untouched.

The *good ⇒ unramified* direction of Néron–Ogg–Shafarevich is proved for an
abstract complete DVR `A ⊆ L` with inertia subgroup `A.inertiaSubgroup K`
(`Reduction/NeronOggShafarevich.lean`); that file's `## Scope` section puts two
pieces out of scope, "the *classical local-field* form — a curve `E / K` over a
local field with inertia realised inside `Gal(K^{ur}/K)`" and "the *converse*
direction, unramified ⇒ good reduction". For semi-stable reduction, the
reduction-type trichotomy, the `j`-invariant criteria and the mutual exclusivity
of potential good and potential multiplicative reduction are in place
(`Reduction/`), but the theorem itself is not yet assembled.

Beside those targets the tree carries reduction over a discrete valuation ring
(`Reduction/`); the function field `F(W)`, its places, its divisors and the Weil
pairing (`FunctionField/`); the Weierstrass formal group and `Ê(𝔪)`
(`FormalGroup/`); `n`-torsion and division polynomials, with `E[n] ≅ (ℤ/nℤ)²`
for every `3`-smooth `n` over an algebraically closed field in which `2 ≠ 0` and
`3 ≠ 0` (`Torsion/`, `DivisionPolynomial/`); the Tate module `T_ℓE` and its
ℓ-adic Galois representation (`TateModule/`); the cyclotomic character and other
Galois-theoretic support (`Galois/`); and the Newton-polygon dichotomy for a
Weierstrass equation (`NewtonPolygon.lean`). Many of these carry hypotheses, or
hold only at restricted indices; the module docstring of the file that proves a
result states its own, and `README.md` has the full inventory.

This file re-exports the relevant Mathlib foundations so that downstream files
have a single, stable entry point to import. That is an offer rather than a
description of the tree: no module under `EllipticCurves/` imports it, directly
or transitively — the only importer is the root module `EllipticCurves.lean` —
so the files here name their Mathlib dependencies themselves.
-/
