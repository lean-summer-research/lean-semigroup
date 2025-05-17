import Mathlib

/-!
# PnatPow

This file defines exponentiation operations for elements of a semigroup using positive natural
numbers. It also provides lemmas related to the `PNat` type.

## Definitions

PNat Properties:
  * `PNat.exists_eq_add_of_lt` - If `m < n` for positive naturals, then there
  exists a positive `k` such that `n = k + m`
  * `PNat.add_sub_cancel'`
  * `PNat.n_lt_2nm`

Basic Exponentiation:
  * `PNat.pnatPow`
  * `PNat.hPow` - Instance providing the notation `a ^ n` for semigroups
  * `PNat.pow_one`
  * `PNat.pow_succ`

Exponentiation lemmas:
  * `PNat.mul_pow_mul`
  * `PNat.pow_mul_comm'`
  * `PNat.pow_add`
  * `PNat.pow_mul_comm`
  * `PNat.pow_mul`
  * `PNat.pow_right_comm`

Special Properties:
  * `PNat.pow_succ_eq` - Shows that for idempotent elements, all powers equal the element itself

## Implementation notes

The simp-tagged lemmas collectively normalize power expressions whenever you call `simp`.
For example, an expression like `(a*b)^n * (a*b)^m * a^1 ` would be normalized to `a * (b*a)^(n+m)`
by calling `simp` on it.

This is the base file in the project, imported by `WithOne.lean`. All other files in the MyProject
directory import mathlib indirectly through this file.

## Refrences

Analagous definitions and lemmas for exponentiation in Monoids can be found in
`Mathlib.Algebra.Group.Defs`
-/

namespace PNat

/-- If `m < n` for positive naturals, then there exists a positive `k` such that `n = k + m`. -/
lemma exists_eq_add_of_lt {m n : ℕ+} (m_lt_n : m < n) : ∃ (k : ℕ+), n = k + m := by
  use n - m
  pnat_to_nat; omega

/-- For positive naturals, if `m < n` then `m + (n - m) = n`. -/
@[simp] lemma add_sub_cancel' {n m : ℕ+} (m_lt_n : m < n) : m + (n - m) = n := by
  induction m using PNat.recOn <;> (pnat_to_nat; omega)

/-- For positive naturals, if `n < 2 * n * m` then `n < 2 * n * m`. -/
lemma n_lt_2nm (n m : ℕ+) : n < 2 * n * m := by
  induction m using PNat.recOn with
  | one => pnat_to_nat; omega
  | succ m ih => pnat_to_nat; ring_nf; omega

variable {M} [Semigroup M]

/-- Exponentiation for semigroups over positive naturals -/
def pnatPow (x : M) (n : ℕ+) : M := @PNat.recOn n (fun _ => M) x (fun _ ih => ih * x)

/-- Provides the notation `a ^ n` for `pnatPow a n`, analogous to the
`Pow M ℕ` instance for monoids (in  -/
instance hPow : Pow M ℕ+ := ⟨pnatPow⟩

variable (x y : M) (n m : ℕ+)

/-- For any element `x` of a semigroup, `x` raised to the power `1` equals `x`. -/
@[simp] lemma pow_one : x ^ (1 : ℕ+) = x := by rfl

/-- Exponentiation satisfies the successor property -/
@[simp] lemma pow_succ : (x ^ n) * x = x ^ (n + 1) := by induction n using PNat.recOn <;> rfl

/-- Multiplicative associativity property for powers -/
@[simp] lemma mul_pow_mul : (x * y) ^ n * x = x * (y * x) ^ n := by
  induction n using PNat.recOn with
  | one => simp [← mul_assoc]
  | succ n ih => simp only [← pow_succ, ← mul_assoc, ih]

/-- For every `x : M` and `n : ℕ+`, the power `x ^ n` commutes with `x` -/
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

/-- The right-associated powers commute -/
lemma pow_right_comm : (x ^ m) ^ n = (x ^ n) ^ m := by simp only [pow_mul, mul_comm]

/-- If `x` is idempotent, then raising `x` to any positive power yields `x`. -/
lemma pow_succ_eq {x : M} (h_idem : IsIdempotentElem x) : x ^ n = x := by
  induction n using PNat.recOn with
  | one    => rfl
  | succ n' ih => rw [← pow_succ, ih, h_idem]

end PNat
