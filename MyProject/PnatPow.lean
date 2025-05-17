import Mathlib

/-! # Positive Natural Number Exponentiation for Semigroups

This file defines exponentiation operations for elements of a semigroup using
positive natural numbers. It defines `pnatPow` and the `Pow M ℕ+` instance which
allows us to use `x ^ n` notation in semigroups.

The definitions and lemmas in this file are organized into the following sections:

### PNat Properties
* `PNat.exists_eq_add_of_lt` - If `m < n` for positive naturals, then there
  exists a positive `k` such that `n = k + m`
* `PNat.add_sub_cancel'`
* `PNat.n_lt_2nm`

### Basic Exponentiation
* `PNat.pnatPow`
* `PNat.hPow` - Instance providing the notation `a ^ n` for semigroups
* `PNat.pow_one`
* `PNat.pow_succ`

### Exponentiation Properties
* `PNat.mul_pow_mul`
* `PNat.pow_mul_comm'`
* `PNat.pow_add`
* `PNat.pow_mul_comm`
* `PNat.pow_mul`
* `PNat.pow_right_comm`

The simp-tagged lemmas collectively normalize power expressions whenever you
call `simp`. For example, an expression like `(a*b)^n * (a*b)^m * a^1 ` would be
normalized to `a * (b*a)^(n+m)` by calling `simp` on it.

### Special Properties
* `PNat.pow_succ_eq` - Shows that for idempotent elements, all powers equal the
  element itself

This is the base file in the project, imported by `WithOne.lean`. All other
files in the MyProject directory import mathlib indirectly through this file. -/

namespace PNat

/-- If `m < n` for positive naturals,
then there exists a positive `k` such that `n = k + m`. -/
lemma exists_eq_add_of_lt {m n : ℕ+} (m_lt_n : m < n) :
    ∃ (k : ℕ+), n = k + m := by
  use n - m; pnat_to_nat; omega

/-- For positive naturals, if `m < n` then `m + (n - m) = n`. -/
@[simp] lemma add_sub_cancel' {n m : ℕ+} (m_lt_n : m < n) :
    m + (n - m) = n := by
  induction m using PNat.recOn <;> (pnat_to_nat; omega)

/-- For positive naturals, if `n < 2 * n * m` then `n < 2 * n * m`. -/
lemma n_lt_2nm (n m : ℕ+) : n < 2 * n * m := by
  induction m using PNat.recOn with
  | one => pnat_to_nat; omega
  | succ m ih => pnat_to_nat; ring_nf; omega

variable {M} [Semigroup M]

/-- Exponentiation for semigroups over positive naturals -/
def pnatPow (a : M) (n : ℕ+) : M :=
  @PNat.recOn n (fun _ => M) a (fun _ ih => ih * a)

/-- Provides the notation `a ^ n` for `pnatPow a n`, analogous to the
    `Pow M ℕ` instance for monoids (in `Mathlib.Algebra.Group.Defs`) -/
instance hPow : Pow M ℕ+ := ⟨pnatPow⟩

variable (a b : M) (n m : ℕ+)

/-- For any element `a` of a semigroup, `a` raised to the power `1` equals `a`. -/
@[simp] lemma pow_one : a ^ (1 : ℕ+) = a := by rfl

/-- Exponentiation satisfies the successor property -/
@[simp] lemma pow_succ : (a ^ n) * a = a ^ (n + 1) := by
  induction n using PNat.recOn <;> rfl

/-- Multiplicative associativity property for powers -/
@[simp] lemma mul_pow_mul : (a * b) ^ n * a = a * (b * a) ^ n := by
  induction n using PNat.recOn with
  | one => simp only [pow_one, ← mul_assoc]
  | succ n ih => simp_rw [← pow_succ, ← mul_assoc, ih]

/-- For every `a : M` and `n : ℕ+`, the power `a ^ n` commutes with `a` -/
@[simp] lemma pow_mul_comm' : a ^ n * a = a * a ^ n := by
  induction n using PNat.recOn with
  | one    => rfl
  | succ k ih => rw [← pow_succ, ← mul_assoc, ih]

/-- Power of a sum equals the product of powers -/
@[simp] lemma pow_add : a ^ m * a ^ n = a ^ (m + n) := by
  induction n using PNat.recOn with
  | one => rw [pow_one, pow_succ]
  | succ k ih => simp_rw [← add_assoc, ← pow_succ, ← mul_assoc, ih]

/-- Powers of the same element commute with each other -/
lemma pow_mul_comm : a ^ m * a ^ n = a ^ n * a ^ m := by
  rw [pow_add, add_comm, pow_add]

/-- The power of a power equals the power of the product of exponents -/
@[simp] lemma pow_mul : (a ^ n) ^ m = a ^ (m * n) := by
  induction m using PNat.recOn with
  | one    => rw [one_mul, pow_one]
  | succ k ih => simp_rw [← pow_succ, ih, pow_add]; congr; ring

/-- The right-associated powers commute -/
lemma pow_right_comm : (a ^ m) ^ n = (a ^ n) ^ m := by
  simp only [pow_mul, mul_comm]

/-- If `a` is idempotent, then raising `a` to any positive power yields `a`. -/
lemma pow_succ_eq {a : M} (h_idem : IsIdempotentElem a) : a ^ n = a := by
  induction n using PNat.recOn with
  | one    => rfl
  | succ n' ih => rw [← pow_succ, ih, h_idem]

end PNat
