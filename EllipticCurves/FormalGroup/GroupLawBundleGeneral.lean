/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import EllipticCurves.FormalGroup.GroupLawBundle
import EllipticCurves.FormalGroup.GenuineLawTransfer
import Mathlib.RingTheory.Localization.FractionRing

/-!
# General-`CommRing` associativity of the Weierstrass formal group law by universality

Associativity of the genuine `(z, w)` Weierstrass formal group law `W.formalGroupZW` is proved over
a `ℚ`-algebra via the formal logarithm (`GroupLawAssoc`, #319, conditional on the log-additivity of
#315).  This file lifts that associativity from `ℚ`-algebras to an **arbitrary `CommRing R`** by the
standard universality argument, and assembles the resulting `FormalGroup R` bundle — the last-mile
of #263.  The `ℚ`-algebra bundle (`formalGroupOfLogAdditivity`, #324) does not suffice over a
char-`p` base, which is exactly what the downstream `Point` `AddCommMonoid` and the
kernel-of-reduction
programme (#243) need.

## Main results

* `WeierstrassCurve.formalGroupZW_assoc_of_ratAlgebra` : the `FormalGroup.assoc`-field-shaped
  associativity of `W.formalGroupZW` over an **arbitrary** `CommRing R`, from the hypothesis `hℚ`
  that associativity holds over every `ℚ`-algebra.
* `WeierstrassCurve.formalGroupOfRatAlgebra` : the `FormalGroup R` bundle over an arbitrary
  `CommRing R`, and `…_isComm` its `IsComm` witness.

## Discharging the hypothesis

The single hypothesis `hℚ` is exactly what the merged, ℚ-algebra-only associativity
`WeierstrassCurve.formalGroupZW_assoc` (#319) provides once #315 lands the unconditional
log-additivity `formalLog_subst_formalGroupZW`.  Concretely, the instant #315 delivers
`formalLog_subst_formalGroupZW [Algebra ℚ C] (V : WeierstrassCurve C)`, the hypothesis is discharged
by
```
fun C _ _ V => V.formalGroupZW_assoc V.formalLog_subst_formalGroupZW
```
turning every result here unconditional over an arbitrary `CommRing R`, closing #263.

## Strategy — universality transfer (Silverman AEC IV.1, Thm 1.1)

The two sides of `assoc` have coefficients that are integral polynomials in the `aᵢ`, so it suffices
to prove the identity over the universal Weierstrass ring `S = MvPolynomial (Fin 5) ℤ` and
specialise (`univ`/`specialize`/`univ_map_specialize`, from
`GenuineLawTransfer`/`UniversalIdentification`).

* **Base change is natural.** For `f : A →+* B`, `MvPowerSeries.map f` slides through the nested
  `subst ![…]` of the `assoc` shape (`MvPowerSeries.map_subst`) and, on `formalGroupZW`, through
  base change (`map_formalGroupZW`, #318).  This gives both the forward transfer `AssocId.map` and,
  when `f` is injective, the descent `AssocId.of_map_injective`.
* **`ℚ`-algebra ⇒ universal ring.** `S` is a char-`0` domain; over `K = FractionRing S` (a
  `ℚ`-algebra) the hypothesis `hℚ` applies, and `algebraMap S K` is injective, so associativity
  descends to `S` (`AssocId.of_map_injective`).
* **Universal ring ⇒ `R`.** Base change along `W.specialize : S →+* R` (with
  `univ.map W.specialize = W`) transports associativity from `univ` to `W` (`AssocId.map`).

## References

* [J. H. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], IV.1, Theorem 1.1.
-/

open MvPowerSeries

namespace WeierstrassCurve

variable {A B : Type*} [CommRing A] [CommRing B]

/-- The `FormalGroup.assoc`-field-shaped associativity identity for `W.formalGroupZW`. -/
private def AssocId {R : Type*} [CommRing R] (W : WeierstrassCurve R) : Prop :=
  W.formalGroupZW.subst ![W.formalGroupZW.subst ![(X 0 : MvPowerSeries (Fin 3) R), X 1], X 2]
    = W.formalGroupZW.subst ![(X 0 : MvPowerSeries (Fin 3) R), W.formalGroupZW.subst ![X 1, X 2]]

/-- `MvPowerSeries.map` of an injective ring hom is injective (in the `Fin 3` grading needed for the
`assoc` shape). -/
private lemma mvPowerSeries_map_injective (f : A →+* B) (hf : Function.Injective f) :
    Function.Injective (MvPowerSeries.map (σ := Fin 3) f) := by
  intro x y hxy
  ext n
  exact hf (by
    have := congrArg (MvPowerSeries.coeff (R := B) n) hxy
    rwa [MvPowerSeries.coeff_map, MvPowerSeries.coeff_map] at this)

/-- Base change slides through a single `formalGroupZW`-substitution `F.subst ![X i, X j]`. -/
private lemma map_formalGroupZW_subst_pair (f : A →+* B) (V : WeierstrassCurve A) (i j : Fin 3) :
    MvPowerSeries.map f (V.formalGroupZW.subst ![X i, X j])
      = (V.map f).formalGroupZW.subst (![X i, X j] : Fin 2 → MvPowerSeries (Fin 3) B) := by
  rw [MvPowerSeries.map_subst MvPowerSeries.HasSubst.X_X, V.map_formalGroupZW f]
  congr 1
  funext k; fin_cases k <;> simp [MvPowerSeries.map_X]

/-- Base change slides through the left-associated triple `assoc` substitution. -/
private lemma map_assoc_lhs (f : A →+* B) (V : WeierstrassCurve A) :
    MvPowerSeries.map f
        (V.formalGroupZW.subst
          ![V.formalGroupZW.subst ![(X 0 : MvPowerSeries (Fin 3) A), X 1], X 2])
      = (V.map f).formalGroupZW.subst
          ![(V.map f).formalGroupZW.subst ![(X 0 : MvPowerSeries (Fin 3) B), X 1], X 2] := by
  rw [MvPowerSeries.map_subst
      (MvPowerSeries.HasSubst.cons_subst_zero_left 0 1 2 V.constantCoeff_formalGroupZW),
    V.map_formalGroupZW f]
  congr 1
  funext i; fin_cases i
  · change MvPowerSeries.map f (V.formalGroupZW.subst ![X 0, X 1])
      = (V.map f).formalGroupZW.subst ![X 0, X 1]
    exact map_formalGroupZW_subst_pair f V 0 1
  · change MvPowerSeries.map f (X 2) = X 2
    exact MvPowerSeries.map_X f 2

/-- Base change slides through the right-associated triple `assoc` substitution. -/
private lemma map_assoc_rhs (f : A →+* B) (V : WeierstrassCurve A) :
    MvPowerSeries.map f
        (V.formalGroupZW.subst
          ![(X 0 : MvPowerSeries (Fin 3) A), V.formalGroupZW.subst ![X 1, X 2]])
      = (V.map f).formalGroupZW.subst
          ![(X 0 : MvPowerSeries (Fin 3) B), (V.map f).formalGroupZW.subst ![X 1, X 2]] := by
  rw [MvPowerSeries.map_subst
      (MvPowerSeries.HasSubst.cons_subst_zero_right 0 1 2 V.constantCoeff_formalGroupZW),
    V.map_formalGroupZW f]
  congr 1
  funext i; fin_cases i
  · change MvPowerSeries.map f (X 0) = X 0
    exact MvPowerSeries.map_X f 0
  · change MvPowerSeries.map f (V.formalGroupZW.subst ![X 1, X 2])
      = (V.map f).formalGroupZW.subst ![X 1, X 2]
    exact map_formalGroupZW_subst_pair f V 1 2

/-- **Forward transfer.** Associativity over `A` transports along any base change `f : A →+* B` to
associativity of the base-changed curve `V.map f`. -/
private lemma AssocId.map (f : A →+* B) {V : WeierstrassCurve A} (hV : AssocId V) :
    AssocId (V.map f) := by
  have := congrArg (MvPowerSeries.map (σ := Fin 3) f) hV
  rwa [map_assoc_lhs, map_assoc_rhs] at this

/-- **Descent.** If `f : A →+* B` is injective, associativity of the base-changed curve `V.map f`
descends to associativity over `A`. -/
private lemma AssocId.of_map_injective (f : A →+* B) (hf : Function.Injective f)
    {V : WeierstrassCurve A} (hVf : AssocId (V.map f)) : AssocId V := by
  apply mvPowerSeries_map_injective f hf
  rw [map_assoc_lhs, map_assoc_rhs]
  exact hVf

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R)

/-- **Associativity of `W.formalGroupZW` over an arbitrary `CommRing R`**, in the exact
`FormalGroup.assoc`-field shape `F(F(X₀, X₁), X₂) = F(X₀, F(X₁, X₂))`, from the hypothesis `hℚ` that
this associativity holds over every `ℚ`-algebra.

The proof is the universality transfer: `hℚ` gives associativity over `K = FractionRing S` for the
universal curve `univ` (`S = MvPolynomial (Fin 5) ℤ`); injectivity of `algebraMap S K` descends it
to `S` (`AssocId.of_map_injective`); and base change along `W.specialize` transports it to `W`
(`AssocId.map`, using `univ.map W.specialize = W`).

`hℚ` is discharged unconditionally the instant #315 lands (see the module docstring), making this
associativity unconditional over any `CommRing R`. -/
theorem formalGroupZW_assoc_of_ratAlgebra
    (hℚ : ∀ (C : Type) [CommRing C] [Algebra ℚ C] (V : WeierstrassCurve C),
      V.formalGroupZW.subst ![V.formalGroupZW.subst ![(X 0 : MvPowerSeries (Fin 3) C), X 1], X 2]
        = V.formalGroupZW.subst
            ![(X 0 : MvPowerSeries (Fin 3) C), V.formalGroupZW.subst ![X 1, X 2]]) :
    W.formalGroupZW.subst ![W.formalGroupZW.subst ![(X 0 : MvPowerSeries (Fin 3) R), X 1], X 2]
      = W.formalGroupZW.subst
          ![(X 0 : MvPowerSeries (Fin 3) R), W.formalGroupZW.subst ![X 1, X 2]] := by
  have hKuniv : AssocId ((univ).map (algebraMap (MvPolynomial (Fin 5) ℤ)
      (FractionRing (MvPolynomial (Fin 5) ℤ)))) :=
    hℚ (FractionRing (MvPolynomial (Fin 5) ℤ)) _
  have hSuniv : AssocId (univ : WeierstrassCurve (MvPolynomial (Fin 5) ℤ)) :=
    hKuniv.of_map_injective _ (IsFractionRing.injective (MvPolynomial (Fin 5) ℤ) _)
  have hR : AssocId ((univ).map W.specialize) := hSuniv.map W.specialize
  rwa [univ_map_specialize] at hR

/-- **The Weierstrass formal group law as a `FormalGroup R` over an arbitrary `CommRing R`**, built
on the genuine `(z, w)` series `W.formalGroupZW`, conditional on the ℚ-algebra associativity
hypothesis `hℚ` (see the module docstring — discharged unconditionally once #315 lands).  The
normalisation fields come from `GenuineLaw.lean`; the `assoc` field is
`formalGroupZW_assoc_of_ratAlgebra`.  Unlike the ℚ-algebra bundle
`formalGroupOfLogAdditivity` (#324), this is available over a char-`p` base. -/
noncomputable def formalGroupOfRatAlgebra
    (hℚ : ∀ (C : Type) [CommRing C] [Algebra ℚ C] (V : WeierstrassCurve C),
      V.formalGroupZW.subst ![V.formalGroupZW.subst ![(X 0 : MvPowerSeries (Fin 3) C), X 1], X 2]
        = V.formalGroupZW.subst
            ![(X 0 : MvPowerSeries (Fin 3) C), V.formalGroupZW.subst ![X 1, X 2]]) :
    FormalGroup R where
  toPowerSeries := W.formalGroupZW
  zero_constantCoeff := W.constantCoeff_formalGroupZW
  lin_coeff_X := W.coeff_single_zero_formalGroupZW
  lin_coeff_Y := W.coeff_single_one_formalGroupZW
  assoc := W.formalGroupZW_assoc_of_ratAlgebra hℚ

@[simp]
theorem formalGroupOfRatAlgebra_toPowerSeries
    (hℚ : ∀ (C : Type) [CommRing C] [Algebra ℚ C] (V : WeierstrassCurve C),
      V.formalGroupZW.subst ![V.formalGroupZW.subst ![(X 0 : MvPowerSeries (Fin 3) C), X 1], X 2]
        = V.formalGroupZW.subst
            ![(X 0 : MvPowerSeries (Fin 3) C), V.formalGroupZW.subst ![X 1, X 2]]) :
    (W.formalGroupOfRatAlgebra hℚ).toPowerSeries = W.formalGroupZW :=
  rfl

/-- **The Weierstrass formal group law over an arbitrary `CommRing R` is commutative.**  The
`FormalGroup.IsComm` witness for `formalGroupOfRatAlgebra`, from the unconditional
`formalGroupZW_subst_swap`. -/
theorem formalGroupOfRatAlgebra_isComm
    (hℚ : ∀ (C : Type) [CommRing C] [Algebra ℚ C] (V : WeierstrassCurve C),
      V.formalGroupZW.subst ![V.formalGroupZW.subst ![(X 0 : MvPowerSeries (Fin 3) C), X 1], X 2]
        = V.formalGroupZW.subst
            ![(X 0 : MvPowerSeries (Fin 3) C), V.formalGroupZW.subst ![X 1, X 2]]) :
    (W.formalGroupOfRatAlgebra hℚ).IsComm :=
  ⟨(W.formalGroupZW_subst_swap).symm⟩

end WeierstrassCurve
