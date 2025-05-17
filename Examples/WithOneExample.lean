import MyProject.GreensRelations -- Current project head (imports everything)

/-! # WithOne Example: Idempotent Powers

This file demonstrates how to apply theorems about monoids to semigroups by
using the `WithOne` construction, which adjoins an identity element to a
semigroup. -/

/-- Restates `Semigroup.exists_idempotent_pow` but requires monoid. -/
theorem Monoid.exists_idempotent_pow (M) [Finite M] [Monoid M] (m : M) :
  ∃ (n : ℕ+), IsIdempotentElem (m ^ n) := Semigroup.exists_idempotent_pow m

/-- This theorem demonstrates how to use the Monoid theorem to prove a result about a
semigroup by adjoining an identity element. -/
theorem with_one_exists_idempotent_pow {S} [Semigroup S] [Fintype S] (x : S) :
    ∃ (n : ℕ+), IsIdempotentElem (x ^ n) := by
  -- apply Monoid theorem to S¹
  have H := Monoid.exists_idempotent_pow (S¹)
  specialize H (↑x : S¹); obtain ⟨ n', Hn' ⟩ := H; use n'
  unfold IsIdempotentElem at *
  -- use lemmas from WithOne.lean
  simp_all only [Semigroup.with_one_pow]
  rw [Semigroup.with_one_mul] at Hn'
  -- Coerce back to S
  rwa [← @WithOne.coe_inj S (x ^ n' * x ^ n') (x ^ n')]
