/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass
import Mathlib.AlgebraicGeometry.EllipticCurve.Reduction

/-!
# Elliptic curves

The `EllipticCurves` project formalises the arithmetic of elliptic curves over local
and global fields, following Silverman's *The Arithmetic of Elliptic Curves*, on top of
Mathlib's existing theory of Weierstrass and elliptic curves
(`Mathlib.AlgebraicGeometry.EllipticCurve.*`).  The two headline targets are
**semi-stable reduction** and the **Néron–Ogg–Shafarevich criterion**.  Neither is
finished and neither is untouched: the *good ⇒ unramified* direction of
Néron–Ogg–Shafarevich is proved for an abstract complete discrete valuation ring in
`EllipticCurves.Reduction.NeronOggShafarevich`, whose own scope section names what is
left (the converse, and the classical local-field packaging with inertia inside
`Gal(Kᵘʳ/K)`); for semi-stable reduction the reduction-type trichotomy, the
`j`-invariant criteria and the potential-good / potential-multiplicative dichotomy are
in `EllipticCurves.Reduction`, but the theorem itself is not assembled.  `README.md`
carries the full inventory.

⚠️ **This is not the root module of the library.**  That is `EllipticCurves.lean`, the
`lake exe mk_all` aggregator, which imports all 360 modules of the project.

## ⚠️ Nothing imports this file

This module re-exports two Mathlib roots, and was written so that downstream files would
have a single stable entry point.  They do not use it.  Measured at `931ed05`:

```
$ grep -rn "import EllipticCurves.Basic" --include=*.lean . | grep -v '^./\.lake'
EllipticCurves.lean:1:import EllipticCurves.Basic
```

One hit, and it is the `mk_all` aggregator, which imports every module by construction.
**Zero of the other 359 modules import this one.**  Each imports the Mathlib modules it
needs directly — `EllipticCurves.Torsion.Defs`, `EllipticCurves.FunctionField.Divisors` and
`EllipticCurves.NewtonPolygon` all import a `Mathlib.AlgebraicGeometry.EllipticCurve.*`
module themselves, and so on down the tree.

⚠️ The `.lake` filter above is not optional: without it the same command also greps the
vendored Mathlib and Batteries sources.  Known-nonzero control for the command, run at
the same commit: `import EllipticCurves.Galois.SubfieldAut` returns three hits, of which
two — `EllipticCurves.FunctionField.MulByNGaloisGroup` and
`EllipticCurves.FunctionField.NegYGaloisGroup` — are real consumers.

The file is kept: a stable entry point costs nothing, and whether an unused re-export
module should exist at all is a design question nobody has argued either way.  What it
must not do is claim a consumption it does not have.
-/
