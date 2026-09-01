/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import Mathlib.NumberTheory.EllipticDivisibilitySequence

/-!
# `normEDS` is weighted-homogeneous: the scaling law of a normalised EDS

Mathlib's `normEDS b c d : ℤ → R` is built from three parameters, and this file records that it is
**homogeneous** in them for the weights

```
deg b = 3,   deg c = 8,   deg d = 12,   deg (normEDS b c d n) = n ^ 2 - 1.
```

Concretely, for every `u : R` and every `n`,

```
u * normEDS (u ^ 3 * b) (u ^ 8 * c) (u ^ 12 * d) n = u ^ n ^ 2 * normEDS b c d n
```

(`normEDS_homogeneous`), with the extra factor `u` on the left so that the exponent is `n ^ 2`
rather than `n ^ 2 - 1` and no truncated `ℕ`-subtraction appears in the statement.

⚠️ **The weights are forced, not chosen.** `normEDS 2 = b`, `normEDS 3 = c` and `normEDS 4 = d * b`
give `deg b = 2² - 1 = 3`, `deg c = 3² - 1 = 8` and `deg d = (4² - 1) - 3 = 12`, so this is the
*only* grading under which `normEDS b c d n` can be homogeneous of weight `n ² - 1`. For the
division polynomials `ψₙ` of a Weierstrass curve this is the familiar statement that `ψₙ` has weight
`n² - 1` under the scaling `(x, y) ↦ (u²x, u³y)`; here it is proved for `normEDS` directly, over an
arbitrary `CommRing` and with no curve in sight.

## Why this file exists: Ward's relator is homogeneous, and that constrains its proofs

`IsEllipticNet.rel W p q 1 0` is the `r = 1` Ward relator whose vanishing for `normEDS` is the open
half of Mathlib's `IsEllipticDvdSequence` `TODO` (see `EllipticCurves.Torsion.WardR1Core`, where
what remains is isolated as `WeierstrassCurve.WardGapCore`). The last theorem below,
`IsEllipticNet.rel_normEDS_homogeneous`, says that this relator is homogeneous of weight
`2p² + 2q² + 2`:

```
u ^ 4 * rel (normEDS (u ^ 3 * b) (u ^ 8 * c) (u ^ 12 * d)) p q 1 0
  = u ^ (2 * p.natAbs ^ 2 + 2 * q.natAbs ^ 2 + 2) * rel (normEDS b c d) p q 1 0
```

⚠️ **This is a constraint on what a `linear_combination` proof of Ward's theorem can look
like.** Every relator is homogeneous, so in any identity `M * rel … a b 1 0 = ∑ cᵢ * gᵢ`
between relators the weights must match term by term: each cofactor `cᵢ` is forced to be
homogeneous of weight `deg M + deg (target) - deg (gᵢ)`. Because the weights grow
*quadratically* in the indices, that is a tight constraint, and it is one a degree bound
cannot see — it rules out cofactors of every degree at once rather than up to a search
horizon.

⚠️ **What this file does and does not claim.** It proves the homogeneity. It does **not** claim any
particular certificate does not exist: that is a statement about a search, not a theorem, and it is
not formalised here. Nothing below bears on `WardGapCore`, which is untouched and not weakened.

## Main statements

* `preNormEDSWeight` : the weight of `preNormEDS' B c d n` when `B`, `c`, `d` have weights
  `12`, `8`, `12` — namely `n ^ 2 - 1` for odd `n` and `n ^ 2 - 4` for even `n`.
* `preNormEDS'_homogeneous` : the scaling law for `preNormEDS'`, which is where the induction runs.
* `normEDS_homogeneous_natCast`, `normEDS_homogeneous` : the scaling law for `normEDS`, at a natural
  and at an integer index.
* `not_normEDS_homogeneous_of_b_weight_ne` and its `c`, `d` companions : lowering any one of the
  three weights by `1` makes the scaling law false, so the weights are forced.
* `IsEllipticNet.rel_normEDS_homogeneous` : the `r = 1` Ward relator of `normEDS` is homogeneous of
  weight `2p² + 2q² + 2`.

## References

* M. Ward, *Memoir on elliptic divisibility sequences*, Amer. J. Math. 70 (1948).
* [J. Silverman, *The arithmetic of elliptic curves*][silverman2009], III.4 and VII.
-/

variable {R : Type*} [CommRing R]

/-! ### The weight of `preNormEDS'`, and the arithmetic of its recursion -/

/-- The weight of `preNormEDS' B c d n` when `B`, `c` and `d` carry weights `12`, `8` and `12`:
it is `n ^ 2 - 1` for odd `n` and `n ^ 2 - 4` for even `n`.

⚠️ The two cases differ because `normEDS b c d n = preNormEDS' (b ^ 4) c d n * (b if n is even)`
carries an extra factor `b`, of weight `3`, at even `n`; it is `normEDS` and not `preNormEDS'` whose
weight is the uniform `n ^ 2 - 1`. The `ℕ`-subtraction truncates only at `n = 0`, where
`preNormEDS' B c d 0 = 0` makes every statement below vacuous. -/
def preNormEDSWeight (n : ℕ) : ℕ :=
  (n - (if Even n then 2 else 1)) * (n + (if Even n then 2 else 1))

lemma preNormEDSWeight_odd (k : ℕ) : preNormEDSWeight (2 * k + 1) = 4 * k * (k + 1) := by
  have h : ¬ Even (2 * k + 1) := by simp [parity_simps]
  simp only [preNormEDSWeight, h, if_false]
  have : 2 * k + 1 - 1 = 2 * k := by omega
  rw [this]; ring

lemma preNormEDSWeight_even (k : ℕ) : preNormEDSWeight (2 * (k + 1)) = 4 * k * (k + 2) := by
  simp only [preNormEDSWeight, even_two_mul, if_true]
  have : 2 * (k + 1) - 2 = 2 * k := by omega
  rw [this]; ring

/-- The weight bookkeeping of the first summand of `preNormEDS'_even`. -/
lemma preNormEDSWeight_even_step₁ (m : ℕ) :
    preNormEDSWeight (m + 2) + preNormEDSWeight (m + 2) + preNormEDSWeight (m + 3) +
      preNormEDSWeight (m + 5) = preNormEDSWeight (2 * (m + 3)) := by
  rcases Nat.even_or_odd m with ⟨j, rfl⟩ | ⟨j, rfl⟩
  · rw [show j + j + 2 = 2 * (j + 1) by ring, show j + j + 3 = 2 * (j + 1) + 1 by ring,
      show j + j + 5 = 2 * (j + 2) + 1 by ring, preNormEDSWeight_even, preNormEDSWeight_odd,
      preNormEDSWeight_odd, show 2 * (2 * (j + 1) + 1) = 2 * (2 * j + 2 + 1) by ring,
      preNormEDSWeight_even]
    ring
  · rw [show 2 * j + 1 + 2 = 2 * (j + 1) + 1 by ring, show 2 * j + 1 + 3 = 2 * (j + 2) by ring,
      show 2 * j + 1 + 5 = 2 * (j + 3) by ring, preNormEDSWeight_odd, preNormEDSWeight_even,
      preNormEDSWeight_even, show 2 * (2 * (j + 2)) = 2 * (2 * j + 3 + 1) by ring,
      preNormEDSWeight_even]
    ring

/-- The weight bookkeeping of the second summand of `preNormEDS'_even`. -/
lemma preNormEDSWeight_even_step₂ (m : ℕ) :
    preNormEDSWeight (m + 1) + preNormEDSWeight (m + 3) + preNormEDSWeight (m + 4) +
      preNormEDSWeight (m + 4) = preNormEDSWeight (2 * (m + 3)) := by
  rcases Nat.even_or_odd m with ⟨j, rfl⟩ | ⟨j, rfl⟩
  · rw [show j + j + 1 = 2 * j + 1 by ring, show j + j + 3 = 2 * (j + 1) + 1 by ring,
      show j + j + 4 = 2 * (j + 2) by ring, preNormEDSWeight_odd, preNormEDSWeight_odd,
      preNormEDSWeight_even, show 2 * (2 * (j + 1) + 1) = 2 * (2 * j + 2 + 1) by ring,
      preNormEDSWeight_even]
    ring
  · rw [show 2 * j + 1 + 1 = 2 * (j + 1) by ring, show 2 * j + 1 + 3 = 2 * (j + 2) by ring,
      show 2 * j + 1 + 4 = 2 * (j + 2) + 1 by ring, preNormEDSWeight_even, preNormEDSWeight_even,
      preNormEDSWeight_odd, show 2 * (2 * (j + 2)) = 2 * (2 * j + 3 + 1) by ring,
      preNormEDSWeight_even]
    ring

/-- The weight bookkeeping of the first summand of `preNormEDS'_odd`.  The `12` is the weight of
the parameter `B`, which that summand carries exactly when `m` is even. -/
lemma preNormEDSWeight_odd_step₁ (m : ℕ) :
    preNormEDSWeight (m + 4) + (preNormEDSWeight (m + 2) + preNormEDSWeight (m + 2) +
      preNormEDSWeight (m + 2)) + (if Even m then 12 else 0)
      = preNormEDSWeight (2 * (m + 2) + 1) := by
  rcases Nat.even_or_odd m with ⟨j, rfl⟩ | ⟨j, rfl⟩
  · rw [if_pos ⟨j, rfl⟩, show 2 * (j + j + 2) + 1 = 2 * (2 * j + 2) + 1 by ring,
      preNormEDSWeight_odd, show j + j + 4 = 2 * (j + 2) by ring,
      show j + j + 2 = 2 * (j + 1) by ring, preNormEDSWeight_even, preNormEDSWeight_even]
    ring
  · rw [if_neg (by simp [parity_simps]),
      show 2 * (2 * j + 1 + 2) + 1 = 2 * (2 * j + 3) + 1 by ring, preNormEDSWeight_odd,
      show 2 * j + 1 + 4 = 2 * (j + 2) + 1 by ring, show 2 * j + 1 + 2 = 2 * (j + 1) + 1 by ring,
      preNormEDSWeight_odd, preNormEDSWeight_odd]
    ring

/-- The weight bookkeeping of the second summand of `preNormEDS'_odd`.  The `12` is the weight of
the parameter `B`, which that summand carries exactly when `m` is odd. -/
lemma preNormEDSWeight_odd_step₂ (m : ℕ) :
    preNormEDSWeight (m + 1) + (preNormEDSWeight (m + 3) + preNormEDSWeight (m + 3) +
      preNormEDSWeight (m + 3)) + (if Even m then 0 else 12)
      = preNormEDSWeight (2 * (m + 2) + 1) := by
  rcases Nat.even_or_odd m with ⟨j, rfl⟩ | ⟨j, rfl⟩
  · rw [if_pos ⟨j, rfl⟩, show 2 * (j + j + 2) + 1 = 2 * (2 * j + 2) + 1 by ring,
      preNormEDSWeight_odd, show j + j + 1 = 2 * j + 1 by ring,
      show j + j + 3 = 2 * (j + 1) + 1 by ring, preNormEDSWeight_odd, preNormEDSWeight_odd]
    ring
  · rw [if_neg (by simp [parity_simps]),
      show 2 * (2 * j + 1 + 2) + 1 = 2 * (2 * j + 3) + 1 by ring, preNormEDSWeight_odd,
      show 2 * j + 1 + 1 = 2 * (j + 1) by ring, show 2 * j + 1 + 3 = 2 * (j + 2) by ring,
      preNormEDSWeight_even, preNormEDSWeight_even]
    ring

/-- `1 + preNormEDSWeight n + (3 if n is even)` is `n ^ 2`, for `n ≥ 1`: the passage from the weight
of `preNormEDS'` to the uniform weight `n ^ 2 - 1` of `normEDS`. -/
lemma one_add_preNormEDSWeight_succ (k : ℕ) :
    1 + preNormEDSWeight (k + 1) + (if Even (k + 1) then 3 else 0) = (k + 1) ^ 2 := by
  rcases Nat.even_or_odd (k + 1) with hk | hk
  · obtain ⟨j, hj⟩ := hk
    obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
    rw [if_pos ⟨i + 1, hj⟩, show k + 1 = 2 * (i + 1) from by omega, preNormEDSWeight_even]
    ring
  · obtain ⟨j, hj⟩ := hk
    rw [if_neg (by simp [hj, parity_simps]), hj, preNormEDSWeight_odd]
    ring

/-! ### The scaling law -/

/-- **`preNormEDS'` is weighted-homogeneous** in its three parameters, of weights `12`, `8`, `12`:
scaling them by `u ^ 12`, `u ^ 8`, `u ^ 12` scales `preNormEDS' B c d n` by the factor
`u ^ preNormEDSWeight n`.

Proved by `normEDSRec`, the recursion `preNormEDS'` is defined by; the content is the four weight
identities above, one per summand of `preNormEDS'_even` and `preNormEDS'_odd`. -/
theorem preNormEDS'_homogeneous (u B c d : R) (n : ℕ) :
    preNormEDS' (u ^ 12 * B) (u ^ 8 * c) (u ^ 12 * d) n
      = u ^ preNormEDSWeight n * preNormEDS' B c d n := by
  induction n using normEDSRec with
  | zero => simp
  | one => rw [show preNormEDSWeight 1 = 0 from by decide]; simp
  | two => rw [show preNormEDSWeight 2 = 0 from by decide]; simp
  | three => rw [show preNormEDSWeight 3 = 8 from by decide]; simp
  | four => rw [show preNormEDSWeight 4 = 12 from by decide]; simp
  | even m ih1 ih2 ih3 ih4 ih5 =>
    have e1 := preNormEDSWeight_even_step₁ m
    have e2 := preNormEDSWeight_even_step₂ m
    rw [preNormEDS'_even, preNormEDS'_even, ih1, ih2, ih3, ih4, ih5, mul_sub]
    nth_rewrite 1 [← e1]
    nth_rewrite 1 [← e2]
    ring
  | odd m ih1 ih2 ih3 ih4 =>
    have e1 := preNormEDSWeight_odd_step₁ m
    have e2 := preNormEDSWeight_odd_step₂ m
    rw [preNormEDS'_odd, preNormEDS'_odd, ih1, ih2, ih3, ih4, mul_sub]
    rcases Nat.even_or_odd m with hm | hm
    · simp only [if_pos hm] at e1 e2 ⊢
      nth_rewrite 1 [← e1]
      nth_rewrite 1 [← e2]
      ring
    · simp only [if_neg (Nat.not_even_iff_odd.mpr hm)] at e1 e2 ⊢
      nth_rewrite 1 [← e1]
      nth_rewrite 1 [← e2]
      ring

/-- **`normEDS` is weighted-homogeneous** of weight `n ^ 2 - 1`, for `deg b = 3`, `deg c = 8`,
`deg d = 12`.  At a natural index; see `normEDS_homogeneous` for an integer one.

The factor `u` on the left is what makes the exponent the honest `n ^ 2` instead of a truncated
`n ^ 2 - 1`; at `n = 0` both sides are `0` and the statement says nothing. -/
theorem normEDS_homogeneous_natCast (u b c d : R) (n : ℕ) :
    u * normEDS (u ^ 3 * b) (u ^ 8 * c) (u ^ 12 * d) n = u ^ n ^ 2 * normEDS b c d n := by
  rcases n with _ | k
  · simp
  · have h := one_add_preNormEDSWeight_succ k
    rw [normEDS_ofNat, normEDS_ofNat, show (u ^ 3 * b) ^ 4 = u ^ 12 * b ^ 4 from by ring,
      preNormEDS'_homogeneous, ← h]
    rcases Nat.even_or_odd (k + 1) with hk | hk
    · simp only [if_pos hk]
      ring
    · simp only [if_neg (Nat.not_even_iff_odd.mpr hk)]
      ring

/-- **`normEDS` is weighted-homogeneous** of weight `n ^ 2 - 1`, at an integer index.  Extends
`normEDS_homogeneous_natCast` across the sign by `normEDS_neg`. -/
theorem normEDS_homogeneous (u b c d : R) (n : ℤ) :
    u * normEDS (u ^ 3 * b) (u ^ 8 * c) (u ^ 12 * d) n
      = u ^ n.natAbs ^ 2 * normEDS b c d n := by
  rcases Int.natAbs_eq n with h | h
  · rw [h, normEDS_homogeneous_natCast]; simp [Int.natAbs_abs]
  · rw [h, normEDS_neg, normEDS_neg, mul_neg, normEDS_homogeneous_natCast, mul_neg]
    simp [Int.natAbs_abs]

/-! ### The three weights are forced

Each of `3`, `8`, `12` is pinned by a single value of `normEDS`, and lowering any one of them by
`1` makes `normEDS_homogeneous` false.  These three witnesses are what stop the theorem above
being read as *"some scaling works"*: it is **this** scaling and no other. -/

/-- The weight `3` of `b` is forced: `normEDS b c d 2 = b`. -/
lemma not_normEDS_homogeneous_of_b_weight_ne :
    ¬ ∀ (u b c d n : ℤ),
      u * normEDS (u ^ 2 * b) (u ^ 8 * c) (u ^ 12 * d) n = u ^ n.natAbs ^ 2 * normEDS b c d n := by
  intro h
  have := h 2 1 1 1 2
  norm_num at this

/-- The weight `8` of `c` is forced: `normEDS b c d 3 = c`. -/
lemma not_normEDS_homogeneous_of_c_weight_ne :
    ¬ ∀ (u b c d n : ℤ),
      u * normEDS (u ^ 3 * b) (u ^ 7 * c) (u ^ 12 * d) n = u ^ n.natAbs ^ 2 * normEDS b c d n := by
  intro h
  have := h 2 1 1 1 3
  norm_num at this

/-- The weight `12` of `d` is forced: `normEDS b c d 4 = d * b`. -/
lemma not_normEDS_homogeneous_of_d_weight_ne :
    ¬ ∀ (u b c d n : ℤ),
      u * normEDS (u ^ 3 * b) (u ^ 8 * c) (u ^ 11 * d) n = u ^ n.natAbs ^ 2 * normEDS b c d n := by
  intro h
  have := h 2 1 1 1 4
  norm_num at this

/-! ### Ward's `r = 1` relator is homogeneous -/

namespace IsEllipticNet

/-- A four-fold product scales by the sum of the four weights.  The shape of every summand of
`IsEllipticNet.rel`. -/
private lemma mul_four_homogeneous {u x₁ x₂ x₃ x₄ y₁ y₂ y₃ y₄ : R} {a₁ a₂ a₃ a₄ : ℕ}
    (h₁ : u * x₁ = u ^ a₁ * y₁) (h₂ : u * x₂ = u ^ a₂ * y₂)
    (h₃ : u * x₃ = u ^ a₃ * y₃) (h₄ : u * x₄ = u ^ a₄ * y₄) :
    u ^ 4 * (x₁ * x₂ * x₃ * x₄) = u ^ (a₁ + a₂ + a₃ + a₄) * (y₁ * y₂ * y₃ * y₄) := by
  calc u ^ 4 * (x₁ * x₂ * x₃ * x₄) = (u * x₁) * (u * x₂) * (u * x₃) * (u * x₄) := by ring
    _ = (u ^ a₁ * y₁) * (u ^ a₂ * y₂) * (u ^ a₃ * y₃) * (u ^ a₄ * y₄) := by rw [h₁, h₂, h₃, h₄]
    _ = u ^ (a₁ + a₂ + a₃ + a₄) * (y₁ * y₂ * y₃ * y₄) := by
        rw [pow_add, pow_add, pow_add]; ring

private lemma natAbs_sq_add_sub (p q : ℤ) :
    (p + q).natAbs ^ 2 + (p - q).natAbs ^ 2 + 1 + 1
      = 2 * p.natAbs ^ 2 + 2 * q.natAbs ^ 2 + 2 := by
  have h : ∀ n : ℤ, ((n.natAbs ^ 2 : ℕ) : ℤ) = n ^ 2 := fun n => by
    exact_mod_cast Int.natAbs_sq n
  zify [h]
  ring

private lemma natAbs_sq_shift (p q : ℤ) :
    (p + 1).natAbs ^ 2 + (p - 1).natAbs ^ 2 + q.natAbs ^ 2 + q.natAbs ^ 2
      = 2 * p.natAbs ^ 2 + 2 * q.natAbs ^ 2 + 2 := by
  have h : ∀ n : ℤ, ((n.natAbs ^ 2 : ℕ) : ℤ) = n ^ 2 := fun n => by
    exact_mod_cast Int.natAbs_sq n
  zify [h]
  ring

/-- **Ward's `r = 1` relator of `normEDS` is weighted-homogeneous** of weight
`2 p ² + 2 q ² + 2`, for `deg b = 3`, `deg c = 8`, `deg d = 12`.

⚠️ This is a fact about the relator, not about `WeierstrassCurve.WardGapCore`: it says that any
identity between relators must balance weights term by term, which forces the shape of every
`linear_combination` cofactor in a proof of Ward's theorem.  It proves nothing about whether such a
proof exists. -/
theorem rel_normEDS_homogeneous (u b c d : R) (p q : ℤ) :
    u ^ 4 * rel (normEDS (u ^ 3 * b) (u ^ 8 * c) (u ^ 12 * d)) p q 1 0
      = u ^ (2 * p.natAbs ^ 2 + 2 * q.natAbs ^ 2 + 2) * rel (normEDS b c d) p q 1 0 := by
  have h := normEDS_homogeneous u b c d
  have h1 : ((1 : ℤ)).natAbs ^ 2 = 1 := by decide
  simp only [rel, add_zero]
  have t₁ := mul_four_homogeneous (h (p + q)) (h (p - q)) (h 1) (h 1)
  have t₂ := mul_four_homogeneous (h (p + 1)) (h (p - 1)) (h q) (h q)
  have t₃ := mul_four_homogeneous (h (q + 1)) (h (q - 1)) (h p) (h p)
  rw [h1] at t₁
  rw [natAbs_sq_add_sub] at t₁
  rw [natAbs_sq_shift] at t₂
  rw [natAbs_sq_shift q p,
    show 2 * q.natAbs ^ 2 + 2 * p.natAbs ^ 2 + 2 = 2 * p.natAbs ^ 2 + 2 * q.natAbs ^ 2 + 2
      from by ring] at t₃
  linear_combination t₁ - t₂ + t₃

end IsEllipticNet
