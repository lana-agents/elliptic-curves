/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import EllipticCurves.Torsion.TwoPrimary

/-!
# Compatible bases for the `2`-primary tower

`EllipticCurves.Torsion.TwoPrimary` shows that `E[2^k] ≃+ ZMod (2^k) × ZMod (2^k)` for an elliptic
curve over an algebraically closed field with `2 ≠ 0`. Those isomorphisms are **non-canonical**, and
worse, a family of them chosen level by level need not commute with the transition maps
`E[2^{k+1}] → E[2^k]`, `x ↦ 2 • x`. Any consumer that takes an inverse limit — above all the Tate
module `T₂E = lim_k E[2^k]` — needs a **coherent** system instead. This file builds one:

```
∃ P Q : ℕ → W.Point,
  (∀ k, AddSubgroup.closure {P k, Q k} = W.torsion (2 ^ k)) ∧
  (∀ k, 2 • P (k + 1) = P k) ∧ (∀ k, 2 • Q (k + 1) = Q k)
```

## The mechanism

Two ingredients.

* **Lifting.** `EllipticCurves.Torsion.DoublingSurjective` makes `[2]` surjective on `E(F̄)`, and a
  preimage of an element of `E[2^k]` lies in `E[2^{k+1}]` for free.

* **Arbitrary lifts of a generating pair generate — as soon as `k ≥ 1`.** If
  `closure {P, Q} = E[2^k]` and `2 • P' = P`, `2 • Q' = Q` with `P', Q' ∈ E[2^{k+1}]`, put
  `H := closure {P', Q'}`. Then `E[2^k] = closure {2 • P', 2 • Q'} ≤ H`. Given `x ∈ E[2^{k+1}]` we
  have `2 • x ∈ E[2^k]`, so `2 • x = m • (2 • P') + n • (2 • Q') = 2 • h` for `h := m • P' + n • Q'`
  in `H`; hence `x - h ∈ E[2] ≤ E[2^k] ≤ H` and `x ∈ H`.

  **`k ≥ 1` is essential** and enters at exactly one point: `E[2] ≤ E[2^k]`. At `k = 0` the
  statement is genuinely false — `P = Q = 0` generate `E[1] = ⊥`, but two lifts in `E[2]` need not
  generate `E[2]` (take them equal). So the recursion is started at `k = 1` from a chosen basis of
  `E[2]`, and level `0` is filled in with `P 0 = Q 0 = 0`.

Note that **no element orders, cardinalities or determinants** appear in the inductive step; the
chain of containments `E[2] ≤ E[2^k] ≤ H` does all the work. The step is stated for a general
generating pair (`closure_pair_eq_torsion_succ`), and the same proof works verbatim for any prime
`ℓ` whose `[ℓ]`-surjectivity is established, with `2` replaced by `ℓ`.

## The levelwise isomorphism, in explicit form

`AddCommGroup.equiv_zmod_sq_of_two_gen` concludes `Nonempty (A ≃+ ZMod n × ZMod n)` and so discards
the map. Inverse-limit arguments need the map itself, and in particular need its **injectivity**, so
this file also builds

```
torsionPairEquiv : ZMod (2 ^ k) × ZMod (2 ^ k) ≃+ W.torsion (2 ^ k)
  (a, b) ↦ a.val • P + b.val • Q
```

from a generating pair, together with the two unbundled consequences `exists_zmod_pair_eq`
(surjectivity) and `zmod_pair_eq_zero_iff` (injectivity at `0`). Surjectivity is
`AddSubgroup.mem_closure_pair` plus reduction of the integer coefficients mod `2^k`; injectivity is
then free, because `#(ZMod (2^k))² = 4^k = #E[2^k]` by `card_torsion_two_pow`.

## Main statements

* `WeierstrassCurve.Affine.exists_two_nsmul_eq_of_mem_torsion`: lifting along `[2]` in the tower.
* `WeierstrassCurve.Affine.closure_pair_eq_torsion_succ`: lifts of a generating pair generate.
* `WeierstrassCurve.Affine.exists_compatible_basis`: the coherent system.
* `WeierstrassCurve.Affine.torsionPairEquiv`: the explicit `(ℤ/2^kℤ)² ≃+ E[2^k]`.
* `WeierstrassCurve.Affine.zmod_pair_eq_zero_iff`: uniqueness of the coefficients.
* `WeierstrassCurve.Affine.ne_zero_and_ne_of_closure_pair`: a generating pair is non-degenerate.

## References

* [Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.7.
-/

open scoped AddSubgroup

namespace WeierstrassCurve.Affine

/-! ### Coefficients modulo `n` acting on `n`-torsion elements -/

section Generic

variable {A : Type*} [AddCommGroup A]

/-- Natural numbers with the same residue mod `n` act identically on an element killed by `n`. -/
private lemma nsmul_congr_of_natCast_eq {n : ℕ} {g : A} (hg : n • g = 0) {s t : ℕ}
    (h : (s : ZMod n) = (t : ZMod n)) : s • g = t • g := by
  rw [nsmul_eq_mod_nsmul s hg, nsmul_eq_mod_nsmul t hg,
    (ZMod.natCast_eq_natCast_iff' s t n).mp h]

/-- An integer acts on an element killed by `n` through the canonical representative of its residue
class in `ZMod n`. -/
private lemma zsmul_eq_val_nsmul {n : ℕ} [NeZero n] {g : A} (hg : n • g = 0) (m : ℤ) :
    m • g = ((m : ZMod n)).val • g := by
  obtain ⟨c, hc⟩ : (n : ℤ) ∣ m - (((m : ZMod n)).val : ℤ) := by
    refine (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp ?_
    push_cast [ZMod.natCast_val, ZMod.intCast_cast, ZMod.cast_id]
    ring
  have hm : m = c * (n : ℤ) + (((m : ZMod n)).val : ℤ) := by linarith [hc]
  conv_lhs => rw [hm]
  rw [add_zsmul, mul_zsmul, natCast_zsmul, hg, smul_zero, zero_add, natCast_zsmul]

/-- The additive homomorphism `(ZMod n)² →+ A` attached to a pair of elements of `A` killed by `n`,
namely `(a, b) ↦ a.val • g₁ + b.val • g₂`. -/
private def zmodPairHom {n : ℕ} [NeZero n] {g₁ g₂ : A} (h₁ : n • g₁ = 0) (h₂ : n • g₂ = 0) :
    ZMod n × ZMod n →+ A where
  toFun ab := ab.1.val • g₁ + ab.2.val • g₂
  map_zero' := by simp
  map_add' ab cd := by
    have e₁ : ((ab.1 + cd.1).val : ZMod n) = ((ab.1.val + cd.1.val : ℕ) : ZMod n) := by
      push_cast [ZMod.natCast_val, ZMod.cast_id]
      rfl
    have e₂ : ((ab.2 + cd.2).val : ZMod n) = ((ab.2.val + cd.2.val : ℕ) : ZMod n) := by
      push_cast [ZMod.natCast_val, ZMod.cast_id]
      rfl
    rw [Prod.fst_add, Prod.snd_add, nsmul_congr_of_natCast_eq h₁ e₁,
      nsmul_congr_of_natCast_eq h₂ e₂, add_nsmul, add_nsmul]
    abel

private lemma zmodPairHom_apply {n : ℕ} [NeZero n] {g₁ g₂ : A} (h₁ : n • g₁ = 0) (h₂ : n • g₂ = 0)
    (ab : ZMod n × ZMod n) : zmodPairHom h₁ h₂ ab = ab.1.val • g₁ + ab.2.val • g₂ := rfl

/-- The `ZMod n`-coefficient map onto a pair of generators is surjective onto the subgroup they
generate. -/
private lemma zmodPairHom_surjOn {n : ℕ} [NeZero n] {g₁ g₂ : A} (h₁ : n • g₁ = 0) (h₂ : n • g₂ = 0)
    {x : A} (hx : x ∈ AddSubgroup.closure ({g₁, g₂} : Set A)) :
    ∃ ab : ZMod n × ZMod n, zmodPairHom h₁ h₂ ab = x := by
  obtain ⟨m, l, hml⟩ := AddSubgroup.mem_closure_pair.mp hx
  exact ⟨((m : ZMod n), (l : ZMod n)), by
    rw [zmodPairHom_apply, ← zsmul_eq_val_nsmul h₁ m, ← zsmul_eq_val_nsmul h₂ l, hml]⟩

/-- In `ZMod n × ZMod n` the two standard vectors generate. -/
private lemma closure_pair_zmod_prod (n : ℕ) [NeZero n] :
    AddSubgroup.closure ({((1 : ZMod n), (0 : ZMod n)), ((0 : ZMod n), (1 : ZMod n))} :
      Set (ZMod n × ZMod n)) = ⊤ := by
  have h1 : ((1 : ZMod n), (0 : ZMod n)) ∈ ({((1 : ZMod n), (0 : ZMod n)),
      ((0 : ZMod n), (1 : ZMod n))} : Set (ZMod n × ZMod n)) := Set.mem_insert _ _
  have h2 : ((0 : ZMod n), (1 : ZMod n)) ∈ ({((1 : ZMod n), (0 : ZMod n)),
      ((0 : ZMod n), (1 : ZMod n))} : Set (ZMod n × ZMod n)) := Set.mem_insert_of_mem _ rfl
  rw [eq_top_iff]
  rintro ⟨a, b⟩ -
  have hab : ((a, b) : ZMod n × ZMod n)
      = a.val • ((1 : ZMod n), (0 : ZMod n)) + b.val • ((0 : ZMod n), (1 : ZMod n)) := by
    rw [Prod.smul_mk, Prod.smul_mk, Prod.mk_add_mk, smul_zero, smul_zero, add_zero, zero_add,
      nsmul_eq_mul, nsmul_eq_mul, mul_one, mul_one, ZMod.natCast_rightInverse a,
      ZMod.natCast_rightInverse b]
  rw [hab]
  exact add_mem
    (AddSubgroup.nsmul_mem _ (AddSubgroup.subset_closure h1) _)
    (AddSubgroup.nsmul_mem _ (AddSubgroup.subset_closure h2) _)

end Generic

/-! ### Lifting along multiplication by two inside the tower -/

variable {F : Type*} [Field F] [DecidableEq F] {W : Affine F}

variable [IsAlgClosed F] [W.IsElliptic]

/-- **Lifting inside the `2`-primary tower.** Every element of `E[2^k]` is twice an element of
`E[2^{k+1}]`. Surjectivity of `[2]` on `E(F̄)` supplies a preimage, and the preimage automatically
lands one level up: `2 ^ (k + 1) • x = 2 ^ k • (2 • x) = 0`. -/
theorem exists_two_nsmul_eq_of_mem_torsion (h2 : (2 : F) ≠ 0) {k : ℕ} {y : W.Point}
    (hy : y ∈ W.torsion (2 ^ k)) : ∃ x ∈ W.torsion (2 ^ (k + 1)), 2 • x = y := by
  obtain ⟨x, hx⟩ := nsmul_two_surjective h2 y
  have hx' : 2 • x = y := hx
  refine ⟨x, ?_, hx'⟩
  rw [mem_torsion_iff, pow_succ, mul_smul, hx']
  exact hy

/-! ### Lifts of a generating pair generate one level up -/

omit [IsAlgClosed F] [W.IsElliptic] in
/-- **The inductive step.** If `P`, `Q` generate `E[2^k]` with `k ≥ 1`, then *any* lifts `P'`, `Q'`
of them along multiplication by `2` generate `E[2^{k+1}]`.

The proof uses no element orders, no cardinalities and no determinants. Writing
`H := closure {P', Q'}`, the containment `E[2^k] = closure {2 • P', 2 • Q'} ≤ H` is immediate; for
`x ∈ E[2^{k+1}]` the element `2 • x` lies in `E[2^k]`, hence is `2 • h` for some `h ∈ H`, and then
`x - h ∈ E[2] ≤ E[2^k] ≤ H`.

The hypothesis `1 ≤ k` enters at exactly one place, the containment `E[2] ≤ E[2^k]`, and it cannot
be dropped: at `k = 0` the pair `P = Q = 0` generates `E[1] = ⊥`, but two equal lifts in `E[2]`
generate a group of order `2`, not `4`.

Nothing in this proof is special to the prime `2`: the same argument, with `2` replaced by a prime
`ℓ` for which `[ℓ]` is surjective on `E(F̄)`, gives the corresponding step of the `ℓ`-primary
tower. -/
theorem closure_pair_eq_torsion_succ {k : ℕ} (hk : 1 ≤ k) {P Q P' Q' : W.Point}
    (hP' : P' ∈ W.torsion (2 ^ (k + 1))) (hQ' : Q' ∈ W.torsion (2 ^ (k + 1)))
    (hP : 2 • P' = P) (hQ : 2 • Q' = Q)
    (hgen : AddSubgroup.closure ({P, Q} : Set W.Point) = W.torsion (2 ^ k)) :
    AddSubgroup.closure ({P', Q'} : Set W.Point) = W.torsion (2 ^ (k + 1)) := by
  set H := AddSubgroup.closure ({P', Q'} : Set W.Point) with hH
  have hP'H : P' ∈ H := AddSubgroup.subset_closure (Set.mem_insert _ _)
  have hQ'H : Q' ∈ H := AddSubgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
  -- `E[2^k] ≤ H`, because `E[2^k]` is generated by `2 • P'` and `2 • Q'`.
  have hle : W.torsion (2 ^ k) ≤ H := by
    rw [← hgen, AddSubgroup.closure_le]
    rintro x (rfl | rfl)
    · exact hP ▸ AddSubgroup.nsmul_mem _ hP'H 2
    · exact hQ ▸ AddSubgroup.nsmul_mem _ hQ'H 2
  refine le_antisymm ?_ fun x hx => ?_
  · rw [AddSubgroup.closure_le]
    rintro x (rfl | rfl) <;> assumption
  · -- `2 • x` lies in `E[2^k]`, hence is an integer combination of `2 • P'` and `2 • Q'`.
    have h2x : 2 • x ∈ W.torsion (2 ^ k) := by
      rw [mem_torsion_iff, ← mul_smul, ← pow_succ]
      exact hx
    rw [← hgen] at h2x
    obtain ⟨m, l, hml⟩ := AddSubgroup.mem_closure_pair.mp h2x
    have hhH : m • P' + l • Q' ∈ H :=
      AddSubgroup.add_mem _ (AddSubgroup.zsmul_mem _ hP'H m) (AddSubgroup.zsmul_mem _ hQ'H l)
    -- The difference is killed by `2`, hence lies in `E[2] ≤ E[2^k] ≤ H`.
    have hdiff : x - (m • P' + l • Q') ∈ W.torsion 2 := by
      rw [mem_torsion_iff, smul_sub, sub_eq_zero, smul_add, smul_comm 2 m, smul_comm 2 l, hP, hQ,
        hml]
    have : x - (m • P' + l • Q') ∈ H :=
      hle (torsion_mono (dvd_pow_self 2 (by omega)) hdiff)
    simpa using AddSubgroup.add_mem _ this hhH

/-! ### The base of the tower: a generating pair for `E[2]` -/

/-- `E[2]` has a generating pair: it is isomorphic to `ZMod 2 × ZMod 2`, in which the two standard
vectors generate. -/
theorem exists_closure_pair_eq_torsion_two (h2 : (2 : F) ≠ 0) :
    ∃ P Q : W.Point, P ∈ W.torsion 2 ∧ Q ∈ W.torsion 2 ∧
      AddSubgroup.closure ({P, Q} : Set W.Point) = W.torsion 2 := by
  obtain ⟨e⟩ := nonempty_torsionTwo_addEquiv (W := W) h2
  refine ⟨(e.symm (1, 0) : W.Point), (e.symm (0, 1) : W.Point),
    (e.symm (1, 0)).2, (e.symm (0, 1)).2, ?_⟩
  have htop : AddSubgroup.closure ({e.symm (1, 0), e.symm (0, 1)} : Set (W.torsion 2)) = ⊤ := by
    have himg : (e.symm.toAddMonoidHom) ''
        ({((1 : ZMod 2), (0 : ZMod 2)), ((0 : ZMod 2), (1 : ZMod 2))} : Set (ZMod 2 × ZMod 2))
        = ({e.symm (1, 0), e.symm (0, 1)} : Set (W.torsion 2)) := by
      rw [Set.image_insert_eq, Set.image_singleton]
      rfl
    rw [← himg, ← AddMonoidHom.map_closure, closure_pair_zmod_prod 2,
      AddSubgroup.map_top_of_surjective _ e.symm.surjective]
  have hsub : AddSubgroup.map (W.torsion 2).subtype
      (AddSubgroup.closure ({e.symm (1, 0), e.symm (0, 1)} : Set (W.torsion 2)))
      = AddSubgroup.closure ({(e.symm (1, 0) : W.Point), (e.symm (0, 1) : W.Point)} :
        Set W.Point) := by
    rw [AddMonoidHom.map_closure, Set.image_insert_eq, Set.image_singleton]
    rfl
  rw [← hsub, htop, ← AddMonoidHom.range_eq_map, AddSubgroup.range_subtype]

/-! ### The coherent system -/

/-- **Compatible bases for the `2`-primary tower.** Over an algebraically closed field with
`2 ≠ 0` there is a system of generating pairs of the groups `E[2^k]`, coherent for the transition
maps `x ↦ 2 • x` of the tower:

```
∀ k, AddSubgroup.closure {P k, Q k} = W.torsion (2 ^ k)
∀ k, 2 • P (k + 1) = P k        ∀ k, 2 • Q (k + 1) = Q k
```

The recursion starts at level `1` from a generating pair of `E[2]`
(`exists_closure_pair_eq_torsion_two`) and climbs by `closure_pair_eq_torsion_succ`; level `0` is
filled in with `P 0 = Q 0 = 0`, which generates `E[1] = ⊥`, and the compatibility `2 • P 1 = P 0`
holds because `P 1` is `2`-torsion. The family is *chosen*, so the statement is existential; every
consumer only ever needs one such system. -/
theorem exists_compatible_basis (h2 : (2 : F) ≠ 0) :
    ∃ P Q : ℕ → W.Point,
      (∀ k, AddSubgroup.closure ({P k, Q k} : Set W.Point) = W.torsion (2 ^ k)) ∧
      (∀ k, 2 • P (k + 1) = P k) ∧ (∀ k, 2 • Q (k + 1) = Q k) := by
  classical
  obtain ⟨g₁, g₂, hg₁, hg₂, hg⟩ := exists_closure_pair_eq_torsion_two (W := W) h2
  -- One step of the recursion, made total by a junk value off the invariant.
  have key : ∀ (k : ℕ) (pq : W.Point × W.Point), ∃ pq' : W.Point × W.Point,
      AddSubgroup.closure ({pq.1, pq.2} : Set W.Point) = W.torsion (2 ^ k) →
        AddSubgroup.closure ({pq'.1, pq'.2} : Set W.Point) = W.torsion (2 ^ (k + 1)) ∧
          2 • pq'.1 = pq.1 ∧ 2 • pq'.2 = pq.2 := by
    intro k pq
    by_cases hpq : AddSubgroup.closure ({pq.1, pq.2} : Set W.Point) = W.torsion (2 ^ k)
    · rcases Nat.eq_zero_or_pos k with rfl | hk
      · -- Level `0`: `E[2^0] = E[1] = ⊥`, so the pair is `(0, 0)` and any basis of `E[2]` lifts it.
        have hmem₁ : pq.1 ∈ AddSubgroup.closure ({pq.1, pq.2} : Set W.Point) :=
          AddSubgroup.subset_closure (Set.mem_insert _ _)
        have hmem₂ : pq.2 ∈ AddSubgroup.closure ({pq.1, pq.2} : Set W.Point) :=
          AddSubgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
        rw [hpq, pow_zero, torsion_one, AddSubgroup.mem_bot] at hmem₁ hmem₂
        refine ⟨(g₁, g₂), fun _ => ⟨by simpa using hg, ?_, ?_⟩⟩
        · rw [hmem₁]; exact mem_torsion_iff.mp hg₁
        · rw [hmem₂]; exact mem_torsion_iff.mp hg₂
      · -- Level `k ≥ 1`: lift both generators and apply the inductive step.
        have hp : pq.1 ∈ W.torsion (2 ^ k) :=
          hpq ▸ AddSubgroup.subset_closure (Set.mem_insert _ _)
        have hq : pq.2 ∈ W.torsion (2 ^ k) :=
          hpq ▸ AddSubgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
        obtain ⟨p', hp'mem, hp'⟩ := exists_two_nsmul_eq_of_mem_torsion h2 hp
        obtain ⟨q', hq'mem, hq'⟩ := exists_two_nsmul_eq_of_mem_torsion h2 hq
        exact ⟨(p', q'), fun _ =>
          ⟨closure_pair_eq_torsion_succ hk hp'mem hq'mem hp' hq' hpq, hp', hq'⟩⟩
    · exact ⟨(0, 0), fun h => absurd h hpq⟩
  choose nxt hnxt using key
  obtain ⟨b, hb0, hbs⟩ : ∃ b : ℕ → W.Point × W.Point,
      b 0 = (0, 0) ∧ ∀ k, b (k + 1) = nxt k (b k) :=
    ⟨fun k => Nat.rec ((0 : W.Point), (0 : W.Point)) nxt k, rfl, fun _ => rfl⟩
  have hgen : ∀ k, AddSubgroup.closure ({(b k).1, (b k).2} : Set W.Point) = W.torsion (2 ^ k) := by
    intro k
    induction k with
    | zero =>
      rw [hb0, pow_zero, torsion_one]
      simp
    | succ k ih => rw [hbs]; exact (hnxt k (b k) ih).1
  refine ⟨fun k => (b k).1, fun k => (b k).2, hgen, fun k => ?_, fun k => ?_⟩
  · change 2 • (b (k + 1)).1 = (b k).1
    rw [hbs]
    exact (hnxt k (b k) (hgen k)).2.1
  · change 2 • (b (k + 1)).2 = (b k).2
    rw [hbs]
    exact (hnxt k (b k) (hgen k)).2.2

/-! ### The explicit isomorphism `(ℤ/2^kℤ)² ≃+ E[2^k]` -/

omit [IsAlgClosed F] [W.IsElliptic] in
private lemma mem_closure_fst (P Q : W.Point) :
    P ∈ AddSubgroup.closure ({P, Q} : Set W.Point) :=
  AddSubgroup.subset_closure (Set.mem_insert _ _)

omit [IsAlgClosed F] [W.IsElliptic] in
private lemma mem_closure_snd (P Q : W.Point) :
    Q ∈ AddSubgroup.closure ({P, Q} : Set W.Point) :=
  AddSubgroup.subset_closure (Set.mem_insert_of_mem _ rfl)

omit [IsAlgClosed F] [W.IsElliptic] in
private lemma nsmul_fst_of_closure {k : ℕ} {P Q : W.Point}
    (hgen : AddSubgroup.closure ({P, Q} : Set W.Point) = W.torsion (2 ^ k)) :
    (2 ^ k) • P = 0 :=
  mem_torsion_iff.mp (by rw [← hgen]; exact mem_closure_fst P Q)

omit [IsAlgClosed F] [W.IsElliptic] in
private lemma nsmul_snd_of_closure {k : ℕ} {P Q : W.Point}
    (hgen : AddSubgroup.closure ({P, Q} : Set W.Point) = W.torsion (2 ^ k)) :
    (2 ^ k) • Q = 0 :=
  mem_torsion_iff.mp (by rw [← hgen]; exact mem_closure_snd P Q)

omit [IsAlgClosed F] [W.IsElliptic] in
/-- The additive homomorphism `(ℤ/2^kℤ)² →+ E[2^k]`, `(a, b) ↦ a.val • P + b.val • Q`, attached to
a pair of generators of `E[2^k]`. -/
noncomputable def torsionPairHom {k : ℕ} {P Q : W.Point}
    (hgen : AddSubgroup.closure ({P, Q} : Set W.Point) = W.torsion (2 ^ k)) :
    ZMod (2 ^ k) × ZMod (2 ^ k) →+ W.torsion (2 ^ k) :=
  (zmodPairHom (nsmul_fst_of_closure hgen) (nsmul_snd_of_closure hgen)).codRestrict
    (W.torsion (2 ^ k)) fun ab => by
      rw [← hgen]
      exact AddSubgroup.add_mem _
        (AddSubgroup.nsmul_mem _ (mem_closure_fst P Q) _)
        (AddSubgroup.nsmul_mem _ (mem_closure_snd P Q) _)

omit [IsAlgClosed F] [W.IsElliptic] in
@[simp]
lemma torsionPairHom_apply_coe {k : ℕ} {P Q : W.Point}
    (hgen : AddSubgroup.closure ({P, Q} : Set W.Point) = W.torsion (2 ^ k))
    (ab : ZMod (2 ^ k) × ZMod (2 ^ k)) :
    ((torsionPairHom hgen ab : W.torsion (2 ^ k)) : W.Point) = ab.1.val • P + ab.2.val • Q := rfl

omit [IsAlgClosed F] [W.IsElliptic] in
/-- **Every element of `E[2^k]` is a `ZMod (2^k)`-combination of a generating pair.** This is
`AddSubgroup.mem_closure_pair` together with the reduction of the integer coefficients modulo
`2^k`, which is legitimate because `P` and `Q` are killed by `2^k`. -/
theorem exists_zmod_pair_eq {k : ℕ} {P Q : W.Point}
    (hgen : AddSubgroup.closure ({P, Q} : Set W.Point) = W.torsion (2 ^ k))
    {x : W.Point} (hx : x ∈ W.torsion (2 ^ k)) :
    ∃ a b : ZMod (2 ^ k), a.val • P + b.val • Q = x := by
  obtain ⟨ab, hab⟩ := zmodPairHom_surjOn (nsmul_fst_of_closure hgen) (nsmul_snd_of_closure hgen)
    (by rw [hgen]; exact hx)
  exact ⟨ab.1, ab.2, hab⟩

/-- `torsionPairHom` is bijective: it is surjective by `exists_zmod_pair_eq`, and both sides have
`4 ^ k` elements by `card_torsion_two_pow`. -/
theorem torsionPairHom_bijective (h2 : (2 : F) ≠ 0) {k : ℕ} {P Q : W.Point}
    (hgen : AddSubgroup.closure ({P, Q} : Set W.Point) = W.torsion (2 ^ k)) :
    Function.Bijective (torsionPairHom hgen) := by
  haveI := finite_torsion_two_pow (W := W) h2 k
  refine (Nat.bijective_iff_surjective_and_card _).mpr ⟨fun x => ?_, ?_⟩
  · obtain ⟨a, b, hab⟩ := exists_zmod_pair_eq hgen x.2
    exact ⟨(a, b), Subtype.ext hab⟩
  · rw [Nat.card_prod, Nat.card_zmod, card_torsion_two_pow h2, ← pow_add, ← two_mul, pow_mul]
    norm_num

/-- **The explicit structure isomorphism `(ℤ/2^kℤ)² ≃+ E[2^k]`** attached to a generating pair of
`E[2^k]`.

`AddCommGroup.equiv_zmod_sq_of_two_gen` concludes only `Nonempty`; inverse-limit arguments need the
map itself, and in particular its injectivity, which is what this bundles. -/
noncomputable def torsionPairEquiv (h2 : (2 : F) ≠ 0) {k : ℕ} {P Q : W.Point}
    (hgen : AddSubgroup.closure ({P, Q} : Set W.Point) = W.torsion (2 ^ k)) :
    ZMod (2 ^ k) × ZMod (2 ^ k) ≃+ W.torsion (2 ^ k) :=
  AddEquiv.ofBijective _ (torsionPairHom_bijective h2 hgen)

@[simp]
lemma torsionPairEquiv_apply_coe (h2 : (2 : F) ≠ 0) {k : ℕ} {P Q : W.Point}
    (hgen : AddSubgroup.closure ({P, Q} : Set W.Point) = W.torsion (2 ^ k))
    (ab : ZMod (2 ^ k) × ZMod (2 ^ k)) :
    ((torsionPairEquiv h2 hgen ab : W.torsion (2 ^ k)) : W.Point)
      = ab.1.val • P + ab.2.val • Q := rfl

/-- **Uniqueness of the coefficients**: a `ZMod (2^k)`-combination of a generating pair vanishes
only for zero coefficients. This is the half that `AddCommGroup.equiv_zmod_sq_of_two_gen` discards,
and it is what identifies the inverse limit of the tower. -/
theorem zmod_pair_eq_zero_iff (h2 : (2 : F) ≠ 0) {k : ℕ} {P Q : W.Point}
    (hgen : AddSubgroup.closure ({P, Q} : Set W.Point) = W.torsion (2 ^ k))
    {a b : ZMod (2 ^ k)} : a.val • P + b.val • Q = 0 ↔ a = 0 ∧ b = 0 := by
  constructor
  · intro h
    have : torsionPairHom hgen (a, b) = torsionPairHom hgen (0, 0) := by
      refine Subtype.ext ?_
      rw [torsionPairHom_apply_coe, torsionPairHom_apply_coe, h]
      simp
    exact Prod.mk.injEq .. ▸ (Prod.ext_iff.mp
      ((torsionPairHom_bijective h2 hgen).1 this))
  · rintro ⟨rfl, rfl⟩
    simp

/-- **A generating pair of `E[2^k]` with `k ≥ 1` is non-degenerate**: both members are nonzero and
they are distinct. This is the qualitative content of the injectivity half, and it is what rules out
the degenerate systems that the existential statements would otherwise permit — for instance a
"basis" with `P = Q`, which is exactly the configuration that makes the inductive step fail at
`k = 0`. -/
theorem ne_zero_and_ne_of_closure_pair (h2 : (2 : F) ≠ 0) {k : ℕ} (hk : 1 ≤ k) {P Q : W.Point}
    (hgen : AddSubgroup.closure ({P, Q} : Set W.Point) = W.torsion (2 ^ k)) :
    P ≠ 0 ∧ Q ≠ 0 ∧ P ≠ Q := by
  have h1lt : 1 < 2 ^ k := by
    calc 1 < 2 := one_lt_two
      _ = 2 ^ 1 := (pow_one 2).symm
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
  haveI : Fact (1 < 2 ^ k) := ⟨h1lt⟩
  have hval1 : ((1 : ZMod (2 ^ k))).val = 1 := ZMod.val_one _
  have hval0 : ((0 : ZMod (2 ^ k))).val = 0 := ZMod.val_zero
  have hne10 : (1 : ZMod (2 ^ k)) ≠ 0 := one_ne_zero
  refine ⟨fun h => hne10 ?_, fun h => hne10 ?_, fun h => hne10 ?_⟩
  · exact ((zmod_pair_eq_zero_iff h2 hgen (a := 1) (b := 0)).mp
      (by rw [hval1, hval0, h]; simp)).1
  · exact ((zmod_pair_eq_zero_iff h2 hgen (a := 0) (b := 1)).mp
      (by rw [hval1, hval0, h]; simp)).2
  · have himg : torsionPairHom hgen (1, 0) = torsionPairHom hgen (0, 1) := by
      refine Subtype.ext ?_
      rw [torsionPairHom_apply_coe, torsionPairHom_apply_coe, hval1, hval0, h]
      simp
    exact congrArg Prod.fst ((torsionPairHom_bijective h2 hgen).1 himg)

end WeierstrassCurve.Affine
