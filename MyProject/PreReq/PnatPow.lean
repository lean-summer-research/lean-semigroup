import Mathlib

/-!
# Positive Natural Number Exponentiation for Semigroups

This file defines and instantiates an exponentiation operation on semigroups. Exponentiation is
typically defined for natural number exponents, but here we require non-zero natural numbers (`ℕ+`)
because `x^0` is not well defined in a semigroup context.

This file also contains lemmas about the properties of this exponentiation operation and of the
`ℕ+` type.

## Main definitions

Defs and Instances:
* `PNat.pnatPow`
* `PNat.hPow`

Pnat lemmas:
* `PNat.exists_eq_add_of_lt`
* `add_sub_cancel'`
* `n_lt_2nm`

Exponentiation lemmas:
* `PNat.pow_one`
* `PNat.pow_succ`
* `PNat.pow_add`
* `PNat.mul_pow_mul`
* `PNat.pow_mul_comm`
* `PNat.pow_mul_comm'`
* `PNat.pow_mul`
* `PNat.pow_right_comm`
* `PNat.pow_pnat_to_nat`

## Implementation notes

The simp-tagged lemmas collectively normalize power expressions when calling `simp`.
For example, `(a * b) ^ n * (a * b) ^ m * a ^ 1` normalizes to `a * (b * a) ^ (n + m)`.

## References

Analogous definitions and lemmas for exponentiation in monoids can be found in
`Mathlib.Algebra.Group.Defs`.
-/

namespace PNat

/-- If `m < n` for positive naturals, then there exists a positive `k` such that `n = k + m`. -/
lemma exists_eq_add_of_lt {m n : ℕ+} (m_lt_n : m < n) : ∃ (k : ℕ+), n = k + m := by
  use n - m
  pnat_to_nat; omega

/-- For positive naturals, if `m < n` then `m + (n - m) = n`. -/
@[simp] lemma add_sub_cancel' {n m : ℕ+} (m_lt_n : m < n) : m + (n - m) = n := by
  induction m using PNat.recOn <;> (pnat_to_nat; omega)

/-- For positive naturals, `n < 2 * n * m` -/
lemma n_lt_2nm (n m : ℕ+) : n < 2 * n * m := by
  induction m using PNat.recOn with
  | one => pnat_to_nat; omega
  | succ m ih => pnat_to_nat; ring_nf; omega

variable {S} [Semigroup S]

/-- Exponentiation for semigroups over positive naturals -/
def pnatPow (x : S) (n : ℕ+) : S := @PNat.recOn n (fun _ => S) x (fun _ ih => ih * x)

/-- Provides the notation `a ^ n` for `pnatPow a n` -/
instance hPow : Pow S ℕ+ := ⟨pnatPow⟩

variable (x y : S) (n m : ℕ+)

/-- For any element `x` of a semigroup, `x` raised to the power `1` equals `x`. -/
@[simp] lemma pow_one : x ^ (1 : ℕ+) = x := by rfl

/-- Exponentiation satisfies the successor property -/
@[simp] lemma pow_succ : (x ^ n) * x = x ^ (n + 1) := by induction n using PNat.recOn <;> rfl

/-- Power of a sum equals the product of powers -/
@[simp] lemma pow_add : x ^ m * x ^ n = x ^ (m + n) := by
  induction n using PNat.recOn with
  | one => rw [pow_one, pow_succ]
  | succ k ih => simp_rw [← add_assoc, ← pow_succ, ← mul_assoc, ih]

/-- Multiplicative associativity for powers -/
@[simp] lemma mul_pow_mul : (x * y) ^ n * x = x * (y * x) ^ n := by
  induction n using PNat.recOn with
  | one => simp [← mul_assoc]
  | succ n ih => simp only [← pow_succ, ← mul_assoc, ih]

/-- Powers of the same element commute with each other -/
lemma pow_mul_comm : x ^ m * x ^ n = x ^ n * x ^ m := by rw [pow_add, add_comm, pow_add]

/-- For every `x : S` and `n : ℕ+`, the power `x ^ n` commutes with `x` -/
@[simp] lemma pow_mul_comm' : x ^ n * x = x * x ^ n := by
  induction n using PNat.recOn with
  | one    => rfl
  | succ k ih => rw [← pow_succ, ← mul_assoc, ih]

/-- The power of a power equals the power of the product of exponents -/
@[simp] lemma pow_mul : (x ^ n) ^ m = x ^ (m * n) := by
  induction m using PNat.recOn with
  | one    => rw [one_mul, pow_one]
  | succ k ih => simp_rw [← pow_succ, ih, pow_add]; congr; ring

/-- Right-associated powers commute -/
lemma pow_right_comm : (x ^ m) ^ n = (x ^ n) ^ m := by simp only [pow_mul, mul_comm]

/-- Bridge between PNat powers and standard Nat powers in monoids -/
lemma pow_pnat_to_nat {M} [Monoid M] (x : M) (n : ℕ+) :
    x ^ n = x ^ (n : ℕ) := by
  induction n with
  | one => simp [PNat.pnatPow]
  | succ n' ih =>
    rw [PNat.add_coe]; simp
    rw [ ← PNat.pow_succ, ← Nat.succ_eq_add_one, _root_.pow_succ, ih]

end PNat
