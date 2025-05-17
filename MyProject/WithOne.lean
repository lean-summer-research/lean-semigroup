import MyProject.PnatPow

/-!
# WithOne

This file relates to the `WithOne` construction for adding a unit element to a semigroup, forming a
monoid denoted as `S¹` (typed as `S\^1`). The original semigroup `S` can be considered a subtype of
`S¹` via a type coercion.

## Definitions

Instance Declarations for `S¹`:
  * `Semigroup.with_one_fintype` - When `S` has a finite type instance, so does `S¹`

Lemmas relating properties of `S¹` and `S`:
  * `Semigroup.with_one_pow`
  * `Semigroup.with_one_mul`

## Notations

We define the notation `S¹` for the monoid obtained by adjoining a unit element to the semigroup `S`.

## Implementation notes

This file depends on `PnatPow.lean` for the semigroup exponentiation operations, and is imported by
`Idempotence.lean`. The lemmas are used in `Examples/WithOneExample.lean` to translate idempotence
results from `S¹` to `S`.

## Refrences

The `WithOne` construction is defined in `Mathlib.Algebra.Group.WithOne`
-/

namespace Semigroup

variable {S} [Semigroup S]

/-- Notation `S¹` for the monoid obtained by adjoining a unit element to the semigroup `S`. -/
notation S"¹" => WithOne S

/-- The monoid instance for `S¹`. This instance is inferred automatically,
but we write it out for clarity. -/
instance with_one_monoid : Monoid (S¹) := by infer_instance

/-- When `S` has a finite type instance, so does `S¹`. -/
instance with_one_fintype [Fintype S] : Fintype (S¹) := by unfold WithOne; infer_instance

/-- Taking powers in the monoid `S¹` of an element from the semigroup `S` is
equivalent to taking powers in `S` and then embedding the result into `S¹`. -/
lemma with_one_pow {S} [Semigroup S] (x : S) (n : ℕ+) : (↑x : S¹) ^ n = ↑(x ^ n) := by
  induction n with
  | one => rfl
  | succ n ih => simp_rw [← PNat.pow_succ, PNat.pow_mul_comm', WithOne.coe_mul, ih]

/-- Multiplying two elements from `S` in the monoid `S¹` is equivalent to
multiplying them in `S` and then embedding the result into `S¹`. -/
lemma with_one_mul {S} [Semigroup S] (x : S) : (↑x : S¹) * (↑x : S¹) = ↑ (x * x : S) := by rfl

end Semigroup
