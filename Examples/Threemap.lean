import MyProject.GreensRelations

/-!
# Threemap Example: Green's Relations on Functions on `Fin 3`

This file provides a concrete example for studying Green's relations on the monoid of functions
from a three-element set to itself. It demonstrates the use of `#eval` and the `decide` tactic to
compute and characterize Green's relations on this monoid.

## Definitions

* `Threemap` - Type of functions from `Fin 3` to itself
* Specific example functions like `f_id`, `f_120`, `f_112`, etc.
* `form_of_fun` - Returns a function's form (ex. `[a, b, a]`)
* `image_of_fun` - Returns the image of a function as a `Finset`
* `rank_of_fun` - Returns the rank of a function (ex. `2` for `f_112`)

**Correspondence Theorems**
* `r_class_form_correspondence` - R-equivalence corresponds to function form
* `l_class_image_corrospondence` - L-equivalence corresponds to function image
* `h_class_correspondence` - H-equivalence corresponds to both form and image
* `j_class_rank_correspondence` - J-equivalence corresponds to function rank

## Implementation Notes

This file imports `GreensRelations.lean`.

-/

/-- The type of functions from a three-element set to itself, represented as `Fin 3 → Fin 3`. -/
def Threemap : Type := Fin 3 → Fin 3
deriving DecidableEq, Inhabited, Fintype

namespace Threemap

/-- The monoid instance for Threemap, with composition as multiplication. -/
instance : Monoid Threemap where
  mul := fun a b => b ∘ a
  mul_assoc := by intros a b c; rfl
  one := fun a => a
  one_mul := by intros a; rfl
  mul_one := by intros a; rfl
  npow_zero := by intros a; rfl
  npow_succ := by intros a b; rfl

/-- The identity function on `Fin 3`. -/
def f_id : Threemap := ![0, 1, 2]
/-- The cyclic permutation (0 → 1 → 2 → 0). -/
def f_120 : Threemap := ![1, 2, 0]
/-- The function sending 0 and 1 to 1 and 2 to 2. -/
def f_112 : Threemap := ![1, 1, 2]
def f_220 : Threemap := ![2, 2, 0]
def f_212 : Threemap := ![2, 1, 2]
/-- The constant function sending everything to 0. -/
def f_000 : Threemap := ![0, 0, 0]

/-! Compute and print Green's equivalence classes of f_220. -/
#eval ⟦f_220⟧ᵣ
#eval ⟦f_220⟧ₗ
#eval ⟦f_220⟧ⱼ
#eval ⟦f_220⟧ₕ

variable (f g : Threemap)
/-- Example demonstrating that every function is ≤ₕ the identity function. -/
example : (f ≤ₕ f_id) = true := by revert f; decide
/-- Example showing f_112 and f_220 are R-equivalent. -/
example : (f_112 ≡ᵣ f_220) = true := by decide
/-- Example demonstrating the R-class of the constant function f_000. -/
example : ⟦f_000⟧ᵣ = {![0, 0, 0], ![1, 1, 1], ![2, 2, 2]} := by decide

/-- Classifies a function based on its form (pattern of values).
    Returns a value in `Fin 5` representing one of the 5 possible forms. -/
def form_of_fun : Fin 5 :=
  if f 0 = f 1 ∧ f 1 = f 2 then 0 -- [a, a, a]
  else if f 1 = f 2 then 1 -- [b, a, a]
  else if f 0 = f 2 then 2 -- [a, b, a]
  else if f 0 = f 1 then 3 -- [a, a, b]
  else 4 -- [a, b, c]

/-- Two functions are R-equivalent if and only if they have the same form. -/
theorem R_class_form_correspondence : f ≡ᵣ g ↔ form_of_fun f = form_of_fun g := by
  revert f g; decide +native

/-- The image of a function as a Finset, representing which values can be outputs. -/
def image_of_fun : Finset (Fin 3) := Finset.image f Finset.univ

/-- Two functions are L-equivalent if and only if they have the same image. -/
theorem L_class_image_corrospondence : image_of_fun f = image_of_fun g ↔ f ≡ₗ g := by
  revert f g; decide +native

/-- Two functions are H-equivalent if and only if they have both the same form and image. -/
theorem H_class_correspondence :
    f ≡ₕ g ↔ form_of_fun f = form_of_fun g ∧ image_of_fun f = image_of_fun g := by
  revert f g; decide +native

/-- The rank of a function, defined as the cardinality of its image. -/
def rank : Nat := Finset.card (Finset.image f Finset.univ)

/-- The rank of any function in Threemap is either 1, 2, or 3. -/
lemma rank_in_123 : rank f ∈ [1, 2, 3] := by revert f; decide

/-- The rank of a composition of functions cannot exceed the rank of the first function. -/
lemma rank_mul : rank (f * g) ≤ rank f := by revert f g; decide +native

/-- Two functions are J-equivalent if and only if they have the same rank. -/
theorem J_class_rank_correspondence : f ≡ⱼ g ↔ rank f = rank g := by revert f g; decide +native

end Threemap
