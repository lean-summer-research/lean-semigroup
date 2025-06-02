import Mathlib

/-!
# Positive Natural Number Exponentiation for Semigroups

This file defines exponentiation operations for elements of a semigroup using positive natural
numbers (`ℕ+`). It provides the foundational definitions and lemmas for semigroup exponentiation.

## Main definitions

* `PNat.pnatPow` - exponentiation function for semigroups over positive naturals
* `PNat.hPow` - instance providing the notation `a ^ n` for semigroups

## Main statements

* `PNat.pow_add` - power of a sum equals the product of powers: `x ^ m * x ^ n = x ^ (m + n)`
* `PNat.pow_mul` - power of a power: `(x ^ n) ^ m = x ^ (m * n)`
* `PNat.pow_mul_comm'` - powers commute with the base element: `x ^ n * x = x * x ^ n`
* `PNat.pow_pnat_to_nat` - bridge between PNat powers and standard Nat powers in monoids

## Notations

* `a ^ n` - exponentiation for `a : S` and `n : ℕ+` where `S` is a semigroup

## Implementation notes

The simp-tagged lemmas collectively normalize power expressions when calling `simp`.
For example, `(a * b) ^ n * (a * b) ^ m * a ^ 1` normalizes to `a * (b * a) ^ (n + m)`.

This is the base file in the project dependency chain. All other files in MyProject
import Mathlib indirectly through this file.

## References

Analogous definitions and lemmas for exponentiation in monoids can be found in
`Mathlib.Algebra.Group.Defs`.

## TODO

* Should we use a notation like `x ^+ n`  for PNat pow instead of using the hPow instance?
This could be easier becuase it avoids having to deal with the typeclass synthesis which
can sometimes get confused between PNat and Nat pow when `x` is in a Monoid.

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

/-- Multiplicative associativity for powers -/
@[simp] lemma mul_pow_mul : (x * y) ^ n * x = x * (y * x) ^ n := by
  induction n using PNat.recOn with
  | one => simp [← mul_assoc]
  | succ n ih => simp only [← pow_succ, ← mul_assoc, ih]

/-- For every `x : S` and `n : ℕ+`, the power `x ^ n` commutes with `x` -/
@[simp] lemma pow_mul_comm' : x ^ n * x = x * x ^ n := by
  induction n using PNat.recOn with
  | one    => rfl
  | succ k ih => rw [← pow_succ, ← mul_assoc, ih]

/-- Power of a sum equals the product of powers -/
@[simp] lemma pow_add : x ^ m * x ^ n = x ^ (m + n) := by
  induction n using PNat.recOn with
  | one => rw [pow_one, pow_succ]
  | succ k ih => simp_rw [← add_assoc, ← pow_succ, ← mul_assoc, ih]

/-- Powers of the same element commute with each other -/
lemma pow_mul_comm : x ^ m * x ^ n = x ^ n * x ^ m := by rw [pow_add, add_comm, pow_add]

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
