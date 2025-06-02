import MyProject.PnatPow

/-!
# WithOne Construction for Semigroups

This file develops the `WithOne` construction for adjoining a unit element to a semigroup,
forming a monoid denoted as `S¹`. The original semigroup `S` embeds into `S¹` via type coercion.

## Main definitions (instances)

* `WithOne.Monoid` - monoid instance for `S¹` when `S` is a semigroup
* `WithOne.Finite`
* `WithOne.Fintype`
* `WithOne.DecidableEq`

## Main statements

* `WithOne.pow_eq` - powers in `S¹` correspond to powers in `S`: `(↑x : S¹) ^ n = ↑(x ^ n)`

## Notations

* `S¹` - the monoid obtained by adjoining a unit element to the semigroup `S` (typed as `S\^1`)

## Implementation notes

This file depends on `PnatPow.lean` for semigroup exponentiation operations.

## References

The `WithOne` construction is defined in `Mathlib.Algebra.Group.WithOne`.

-/

variable {S} [Semigroup S]

/-- Notation `S¹` for the monoid obtained by adjoining a unit element to the semigroup `S`. -/
notation S"¹" => WithOne S

/-- When `S` is a Semigroup, `S¹` is a Monoid. -/
instance WithOne.Monoid : Monoid (S¹) := by infer_instance

/-- When `S` is finite, so is `S¹` -/
instance WithOne.Finite [inst : Finite S] : Finite (S¹) := by
  have H := finite_or_infinite (S¹)
  cases H with
  | inl hfinite => exact hfinite
  | inr hinfinite =>
    exfalso
    unfold WithOne at *
    apply Nat.card_eq_zero_of_infinite at hinfinite
    have H : Nat.card (Option S) = (Nat.card S) + 1 := by
      simp only [Finite.card_option, Nat.add_left_inj]
    rw [hinfinite] at H
    contradiction

/-- This registers a procedure for converting an explicit,
finite list of every element in `S` to a list of every element in `S¹` -/
instance WithOne.Fintype [Fintype S] : Fintype (S¹) := by unfold WithOne; infer_instance

/-- When `S` has Decidable Equality, so does `S¹` -/
instance WithOne.DecidableEq [DecidableEq S] : DecidableEq (S¹) := by unfold WithOne; infer_instance

/-- Taking powers in the monoid `S¹` is equivalent to taking powers in `S`
and then embedding the result into `S¹`. -/
lemma WithOne.pow_eq {S} [Semigroup S] (x : S) (n : ℕ+) : (↑x : S¹) ^ n = ↑(x ^ n) := by
  induction n with
  | one => rfl
  | succ n ih => simp_rw [← PNat.pow_succ, PNat.pow_mul_comm', WithOne.coe_mul, ih]
