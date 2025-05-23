import MyProject.WithOne

/-!
# Idempotence in Finite Semigroups

This file defines properties related to idempotent elements in finite semigroups.

## Main Definitions

* `Semigroup.exists_repeating_pow` - Powers of an element eventually repeat
* `Semigroup.pow_idempotent_unique` - Idempotent powers of an element are equal
* `Semigroup.exists_idempotent_pow` - Every element in a finite semigroup has an idempotent power

## Implementation Notes

This file imports `PnatPow.lean` (and thereby `WithOne.lean`), and is imported by
`GreensRelations.lean`.

## Refrences

The `Idempotence` file predicaten thdefined e Idempotence` file in the `Mathlib`n is i lib.Algebra.Gro
-/

namespace Semigroup

variable {M} [Semigroup M]

/-- If `M` is finite then for any `x : M` there exist
exponents such that the power eventually repeats. -/
lemma exists_repeating_pow [Finite M] (x : M) : ∃ (m n : ℕ+), x ^ m * x ^ n = x ^ m := by
  obtain ⟨o, p, hop, heq⟩ : ∃ o p : ℕ+, o ≠ p ∧ x ^ o = x ^ p := by
    apply Finite.exists_ne_map_eq_of_infinite
  simp_all only [ne_eq, PNat.pow_add]; pnat_to_nat
  rcases (Nat.lt_or_gt_of_ne hop) with (o_lt_p | p_lt_o)
  · use o, p - o; simp_all
  · use p, o - p; simp_all

/-- If two powers of an element `x : M` are idempotent, then they are equal. -/
theorem pow_idempotent_unique {x : M} {m n : ℕ+}
(hm : IsIdempotentElem (x ^ m)) (hn : IsIdempotentElem (x ^ n)) : x ^ m = x ^ n := by
  rw [← PNat.pow_succ_eq n hm, PNat.pow_right_comm, PNat.pow_succ_eq m hn]

/-- In a finite semigroup, for any `x : M` there exists a positive
natural number `m` such that `x ^ m` is idempotent. -/
theorem exists_idempotent_pow [Finite M] (x : M) : ∃ (m : ℕ+), IsIdempotentElem (x ^ m) := by
  -- `n` is the length of the pre-period (tail),
  --`loop_size` is the length of the cycle.
  obtain ⟨n, loop_size, loop_eq⟩ := exists_repeating_pow x
  -- The `loop` lemma formalizes that once powers of `a` enter the cycle,
  -- adding further multiples of `loop_size` to the exponent doesn't change the result.
  have loop : ∀ (loop_count start : ℕ+),
      n < start → x ^ (start + loop_count * loop_size) = x ^ start := by
    intro loop_count
    induction loop_count using PNat.recOn with
    | one =>
      intro start n_lt_start
      obtain ⟨diff, hdiff⟩ := PNat.exists_eq_add_of_lt n_lt_start
      simp_all only [PNat.pow_add, one_mul, ← PNat.pow_add, mul_assoc]
    | succ loop_count' ih =>
      intro start n_lt_start
      obtain ⟨diff, hdiff⟩ := PNat.exists_eq_add_of_lt n_lt_start
      subst hdiff
      specialize ih (diff + n)
      apply ih at n_lt_start
      have h_arith :
        (loop_count' + 1) * loop_size = (loop_count' * loop_size) + loop_size := by ring
      simp_rw [h_arith, ← add_assoc, ← PNat.pow_add] at *
      rw [n_lt_start, mul_assoc, loop_eq]
  -- We choose `2 * n * loop_size` as the exponent for our idempotent element.
  -- This ensures the exponent is beyond the pre-period `n` and is a multiple of `loop_size`.
  use 2 * n * loop_size
  unfold IsIdempotentElem
  specialize loop (2 * n) (2 * n * loop_size)
  simp_all only [PNat.pow_add]
  -- Apply the `loop` lemma. The condition `n < 2 * n * loop_size` is met by `PNat.n_lt_2nm`.
  apply loop
  exact PNat.n_lt_2nm n (loop_size)

end Semigroup
