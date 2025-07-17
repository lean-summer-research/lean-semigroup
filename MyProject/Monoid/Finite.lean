import MyProject.Monoid.Defs

/-!
# Finiteness in Semigroups
This file begins by defining an exponentiation operation for semigroups using positive natural numbers.
We then prove statments about idempotent elements in finite semigroups and monoids.
These statments are used in the latter parts of the file to prove the DJ Theorem.

## Main Definitions
- `pnatPow`: Exponentiation for semigroups over positive naturals.

## Main Statements
- `Semigroup.exists_idempotent_pow` - and a version for monoids
- `Semigroup.exists_pow_mul_of_sandwich` - and a version for monoids
- `D_eqv_iff_J_finite`: The DJ Theorem, which states that in finite Monoids,
  the 𝓓-relation equals the 𝓙-relation.
-/

/-
### Positive Natural Number Exponentiation for Semigroups
Exponentiation in monoids is defined for natural number exponents, but here we require non-zero
natural numbers (`ℕ+`) because `x^0` is not well defined in a semigroup context.

We also prove lemmas about the properties of this exponentiation operation and of the `ℕ+` type.

The simp-tagged lemmas collectively normalize power expressions when calling `simp`.
For example, `(a * b) ^ n * (a * b) ^ m * a ^ 1` normalizes to `a * (b * a) ^ (n + m)`.

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
lemma lt_2_mul_mul (n m : ℕ+) : n < 2 * n * m := by
  induction m using PNat.recOn with
  | one => pnat_to_nat; omega
  | succ m ih => pnat_to_nat; ring_nf; omega

variable {S : Type*} [Semigroup S]

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

/-! # Idempotent Elements in Finite Semigroups -/

namespace Semigroup

variable {S : Type*} [Semigroup S]

/-- If `x` is idempotent, then raising `x` to any positive power yields `x`. -/
lemma pow_succ_eq {x : S} (n : ℕ+) (h_idem : IsIdempotentElem x) : x ^ n = x := by
  induction n using PNat.recOn with
  | one    => rfl
  | succ n' ih => rw [← PNat.pow_succ, ih, h_idem]

/-- If `S` is finite then for any `x : S` there exist
exponents such that the power eventually repeats. -/
lemma exists_repeating_pow [Finite S] (x : S) : ∃ (m n : ℕ+), x ^ m * x ^ n = x ^ m := by
  obtain ⟨o, p, hop, heq⟩ : ∃ o p : ℕ+, o ≠ p ∧ x ^ o = x ^ p := by
    apply Finite.exists_ne_map_eq_of_infinite
  simp_all only [ne_eq, PNat.pow_add]; pnat_to_nat
  rcases (Nat.lt_or_gt_of_ne hop) with (o_lt_p | p_lt_o)
  · use o, p - o; simp_all
  · use p, o - p; simp_all

/-- If two powers of an element `x : S` are idempotent, then they are equal. -/
theorem pow_idempotent_unique {x : S} {m n : ℕ+}
(hm : IsIdempotentElem (x ^ m)) (hn : IsIdempotentElem (x ^ n)) : x ^ m = x ^ n := by
  rw [← pow_succ_eq n hm, PNat.pow_right_comm, pow_succ_eq m hn]

/-- In a finite semigroup `S`, the subsemigroup generated by any element contains an idempotent -/
theorem exists_idempotent_pow [Finite S] (x : S) : ∃ (m : ℕ+), IsIdempotentElem (x ^ m) := by
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
  -- Apply the `loop` lemma. The condition `n < 2 * n * loop_size` is met by `PNat.lt_2_mul_mul`.
  apply loop
  exact PNat.lt_2_mul_mul n (loop_size)

lemma exists_pow_mul_of_sandwich [Finite S] (x y z : S) (h : x * y * z = y) :
    ∃ n : ℕ+,  x ^ n * y = y := by
  have loop : ∀ m : ℕ+, x ^ m * y * z ^ m = y := by
    intro m
    induction m using PNat.recOn with
    | one => simp_all
    | succ m ih =>
      simp [← PNat.pow_succ]
      rw [← PNat.pow_mul_comm', ← mul_assoc, mul_assoc (x ^ m), mul_assoc (x ^ m)]
      rw [h, ih]
  -- Apply `loop` to the idempotent power of `x`
  obtain ⟨k, hk⟩ := exists_idempotent_pow x
  use k
  have hLoop := loop k
  rw [← hLoop]
  unfold IsIdempotentElem at hk
  simp_rw [← mul_assoc, hk]

open MulOpposite

-- DUal to above
lemma exists_mul_pow_of_sandwich [Finite S] (x y z : S) (h : x * y * z = y) :
    ∃ n : ℕ+, y * z ^ n = y := by
  have loop : ∀ m : ℕ+, x ^ m * y * z ^ m = y := by
    intro m
    induction m using PNat.recOn with
    | one => simp_all
    | succ m ih =>
      simp [← PNat.pow_succ]
      rw [← PNat.pow_mul_comm', ← mul_assoc, mul_assoc (x ^ m), mul_assoc (x ^ m)]
      rw [h, ih]
  obtain ⟨k, hk⟩ := exists_idempotent_pow z
  use k
  have hLoop := loop k
  rw [← hLoop]
  unfold IsIdempotentElem at hk
  rw [mul_assoc, hk]

end Semigroup

/-! We now give versions of the previous proofs for Finite Monoids -/

namespace Monoid

variable {M : Type*} [Monoid M] [Finite M]

/-- Every element in a finite monoid has a non-zero idempotent power -/
theorem exists_idempotent_pow (x : M) :
    ∃ (n : ℕ), IsIdempotentElem (x ^ n) ∧ n ≠ 0:= by
  obtain ⟨m, hm⟩ := Semigroup.exists_idempotent_pow x
  use m; simp_all only [IsIdempotentElem]
  constructor
  · rwa [← PNat.pow_pnat_to_nat]
  · simp [PNat.ne_zero]

lemma exists_pow_mul_of_sandwich {x y z : M} (h : x * y * z = y) :
    ∃ n : ℕ,  x ^ n * y = y ∧ n ≠ 0 := by
  obtain ⟨n, hn⟩ := Semigroup.exists_pow_mul_of_sandwich x y z h
  use n
  constructor
  · simp_all [← PNat.pow_pnat_to_nat]
  · simp_all [PNat.ne_zero]

-- dual to above
lemma exists_mul_pow_of_sandwich {x y z : M} (h : x * y * z = y) :
    ∃ n : ℕ, y * z ^ n = y ∧ n ≠ 0 := by
  obtain ⟨n, hn⟩ := Semigroup.exists_mul_pow_of_sandwich x y z h
  use n
  constructor
  · simp [← PNat.pow_pnat_to_nat, hn]
  · simp

end Monoid

/-! ### DJ Theorem -/

variable {M : Type*} [Monoid M] {x y z : M}

/-- Every 𝓓-related pair is 𝓙-related. -/
@[simp] theorem JEquiv.of_dEquiv (h : x 𝓓 y): x 𝓙 y := by
  simp_all [DEquiv, JEquiv]
  rcases h with ⟨z, ⟨⟨t, hR₁⟩, ⟨u, hR₂⟩⟩ , ⟨⟨v, hL₁⟩, ⟨w, hL₂⟩⟩⟩
  constructor
  · use v, t
    rw [← hR₁, ← hL₁]
  · use w, u
    rw [← hL₂, ← hR₂, ← mul_assoc]

variable [Finite M]

@[simp] theorem LEquiv.of_le_and_jEquiv (hL : x ≤𝓛 y) (hJ: x 𝓙 y) : x 𝓛 y := by
  simp_all [LEquiv]
  obtain ⟨_, hJ⟩ := hJ
  rcases hL with ⟨z, hz⟩
  obtain ⟨u, v, huv⟩ := hJ
  rw [← hz, ← mul_assoc] at huv
  obtain ⟨n, ⟨hn, hneq⟩⟩ := Monoid.exists_pow_mul_of_sandwich huv
  use (u * z) ^ (n - 1) * u
  rw [← hz, ← mul_assoc, mul_assoc _ u, ← pow_succ]
  have hl : n - 1 + 1 = n := by exact Nat.succ_pred_eq_of_ne_zero hneq
  rw [hl, hn]

-- Dual to above
@[simp] theorem REquiv.of_le_and_jEquiv (hR : x ≤𝓡 y) (hJ: x 𝓙 y) : x 𝓡 y := by
  simp_all [← REquiv.op_iff]

-- corrolary to `LEquiv.of_le_and_jEquiv`
@[simp] lemma LEquiv.mul_of_jEquiv (hJ : x 𝓙 y * x) : x 𝓛 y * x := by
  symm
  apply LEquiv.of_le_and_jEquiv
  · simp
  · symm; exact hJ

-- corrolary to `REquiv.of_le_and_jEquiv`
@[simp] lemma REquiv.mul_of_jEquiv (hJ : x 𝓙 x * y) : x 𝓡 x * y := by
  symm
  apply REquiv.of_le_and_jEquiv
  · simp
  · symm; exact hJ

theorem HEquiv.of_sandwich (h : x = y * x * z ) : x 𝓗 x * z ∧ x 𝓗 y * x := by
  have hLLE : x ≤𝓛 x * z := by
    use y
    rw [← mul_assoc, ← h]
  have hJ₁ : x 𝓙 x * z := by
    simp [JEquiv, hLLE]
  have hRLE : x ≤𝓡 y * x := by
    use z
    rw [← h]
  have hJ₂ : x 𝓙 y * x := by
    simp [JEquiv, hRLE]
  simp [← HEquiv.rEquiv_and_lEquiv_iff]
  clear h -- h breaks `simp all`
  constructor <;> constructor
  · apply REquiv.mul_of_jEquiv hJ₁ -- x 𝓡 x * z
  · apply LEquiv.of_le_and_jEquiv hLLE hJ₁ -- x 𝓛 x * z
  · apply REquiv.of_le_and_jEquiv hRLE hJ₂ -- x 𝓡 y * x
  · apply LEquiv.mul_of_jEquiv hJ₂ -- x 𝓛 y * x

/-- In finite semigroups, Green's 𝓓-relation equals the 𝓙-relation.
The backward implication holds even in infinite semigroups. -/
theorem D_eqv_iff_J_finite : x 𝓙 y ↔ x 𝓓 y := by
  constructor
  · intro hJ
    rcases _ : hJ with ⟨⟨u₁, v₁, huv₁⟩, ⟨u₂, v₂, huv₂⟩⟩
    rw [← huv₂] at huv₁
    simp_rw [← mul_assoc, mul_assoc _ _ v₁] at huv₁
    obtain ⟨n, ⟨hn, hnPos⟩⟩  := Monoid.exists_mul_pow_of_sandwich huv₁
    obtain ⟨k, ⟨hk, hkPos⟩⟩  := Monoid.exists_pow_mul_of_sandwich huv₁
    rw [DEquiv]
    use x * v₂
    constructor
    · simp [REquiv] -- goal: `x ≤𝓡 x * v₂`
      use v₁ * (v₂ * v₁) ^ (n - 1)
      simp [← mul_assoc]
      rw [mul_assoc ↑x ↑v₂ v₁, mul_assoc ↑x (↑v₂ * v₁) _ , ← pow_succ']
      have hTriv : n - 1 + 1 = n := by exact Nat.succ_pred_eq_of_ne_zero hnPos
      rw [hTriv, hn]
    · subst y
      simp [LEquiv] -- goal: `x * v₂ ≤𝓛 y = u₂ * x * v₂`
      apply LLE.mul_right_compat
      use (u₁ * u₂) ^ (k - 1) * u₁
      rw [ ← mul_assoc, mul_assoc _ u₁]
      rw [← pow_succ]
      have hTriv : k - 1 + 1 = k := by exact Nat.succ_pred_eq_of_ne_zero hkPos
      rw [hTriv, hk]
  · intro hD
    simp_all
