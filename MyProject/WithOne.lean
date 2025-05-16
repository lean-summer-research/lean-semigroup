import MyProject.PnatPow

/-! # WithOne Construction for Semigroups

This file provides operations and properties for the `WithOne` construction.
This construction takes a semigroup `S` and adjoins a unit element to form a
monoid, denoted as `S¹` (typed as `S\^1`). The original semigroup `S` can be
considered a subtype of `S¹` via an explicit coercion.

The file defines two key lemmas:
* `Semigroup.with_one_pow`: Taking powers of an element from `S` within the
  monoid `S¹` is equivalent to taking powers in `S` and then embedding the
  result into `S¹`.
* `Semigroup.with_one_mul`: Multiplying two elements from `S` within `S¹` is
  equivalent to multiplying them in `S` and then embedding the result into `S¹`.
These lemmas are crucial for translating statements about the monoid `S¹` back to
statements about the original semigroup `S`.

An example of how these constructions and lemmas are used can be found in
`Examples/WithOneExample.lean`.

This file depends on `PnatPow.lean` for the semigroup exponentiation operations,
and is imported by `Idempotence.lean` -/

namespace Semigroup

variable {S} [Semigroup S]

/-- Notation `S¹` for the monoid obtained by
adjoining a unit element to the semigroup `S`. -/
notation S"¹" => WithOne S

/-- The monoid instance for `S¹`. This instance is inferred
automatically, but we write it out for clarity. -/
instance with_one_monoid : Monoid (S¹) := by infer_instance

/-- When `S` has a finite type instance, so does `S¹`. -/
instance with_one_fintype [Fintype S] : Fintype (S¹) := by
  unfold WithOne; infer_instance

/-- Taking powers in the monoid `S¹` of an element from the semigroup `S` is
equivalent to taking powers in `S` and then embedding the result into `S¹`. -/
lemma with_one_pow {S} [Semigroup S] (a : S) (n : ℕ+) : (↑a : S¹) ^ n = ↑(a ^ n) := by
  induction n with
  | one => rfl
  | succ n ih => simp_rw [← PNat.pow_succ, PNat.pow_mul_comm', WithOne.coe_mul, ih]

/-- Multiplying two elements from `S` in the monoid `S¹` is equivalent to
multiplying them in `S` and then embedding the result into `S¹`. -/
lemma with_one_mul {S} [Semigroup S] (a : S) :
    (↑a : S¹) * (↑a : S¹) = ↑ (a * a : S) := by rfl

end Semigroup
