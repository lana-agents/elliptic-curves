/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass
import Mathlib.AlgebraicGeometry.EllipticCurve.Reduction

/-!
# Elliptic curves

This is the root of the `EllipticCurves` project, whose goal is to formalise the
arithmetic of elliptic curves over local and global fields, following
Silverman's *The Arithmetic of Elliptic Curves*.

The project builds on Mathlib's existing theory of Weierstrass and elliptic
curves (`Mathlib.AlgebraicGeometry.EllipticCurve.*`). Planned developments
include:

* semi-stable reduction of elliptic curves;
* the Néron–Ogg–Shafarevich criterion for good reduction.

This file re-exports the relevant Mathlib foundations so that downstream files
have a single, stable entry point to import.
-/
