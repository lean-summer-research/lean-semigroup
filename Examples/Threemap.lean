import MyProject.GreensRelations.Misc.Decidable

/-!
# Green's Relations on Three-Element Function Maps

This file demonstrates the computational power of Green's relations on a concrete finite monoid:
the monoid of functions from a three-element set to itself (`Fin 3 → Fin 3`). It showcases
the decidability and finiteness features developed in `GreensRelations.Decidable`.

## Computational Demonstrations

**Green's Relations**: Examples of computing `≤𝓡`, `≤𝓛`, `≤𝓙`, `≤𝓗` and `𝓡`, `𝓛`, `𝓙`, `𝓗` `𝓓`
**Quotient Types**: Usage of `R_class`, `L_class`, ect. with decidable equality
**Finset Classes**: Computation of `⟦f⟧𝓡_fin`, `⟦f⟧𝓛_fin`, etc. as explicit finite sets
**ideals**: Examples of finite ideals  `M •fin a`, `a •fin M`, `M ••fin a`
**Correspondence Theorems**: Concrete characterizations of Green's classes proven using `decide`
-/

section THREEMAP

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

/-! ### Sample Functions -/

/-- The identity function on `Fin 3`. -/
def f_id : Threemap := ![0, 1, 2]
/-- The cyclic permutation (0 → 1 → 2 → 0). -/
def f_120 : Threemap := ![1, 2, 0]
/-- The function sending 0 and 1 to 1, and 2 to 2. -/
def f_112 : Threemap := ![1, 1, 2]
def f_221 : Threemap := ![2, 2, 1]
def f_220 : Threemap := ![2, 2, 0]
def f_212 : Threemap := ![2, 1, 2]
/-- The constant function sending everything to 0. -/
def f_000 : Threemap := ![0, 0, 0]
def f_111 : Threemap := ![1, 1, 1]

#eval Fintype.card Threemap  -- 27 = 3³

/-! ### Basic Green's Relations Computations -/

-- Examples of Green's preorders
#eval f_112 ≤𝓡 f_id  -- true
#eval f_000 ≤𝓙 f_112  -- true
#eval f_220 ≤𝓛 f_112  -- false
#eval f_id ≤𝓗 f_120   -- true

-- Examples of Green's equivalences
#eval f_112 𝓡 f_220   -- true
#eval f_id 𝓗 f_120    -- true

-- Automated theorem proving with decide
example : ¬(f_id 𝓛 f_000) := by decide +native
example : f_112 𝓙 f_221 := by decide +native

/-! ### Quotient Types and Fintype Instances -/

-- Computing cardinalities of quotient types
#eval Fintype.card (R_class Threemap)  -- Number of R-classes (5)
#eval Fintype.card (L_class Threemap)  -- Number of L-classes (7)
#eval Fintype.card (J_class Threemap)  -- Number of J-classes (3)
#eval Fintype.card (H_class Threemap)  -- Number of H-classes (13)

-- Enumerating all J-classes (there are exactly 3)
example : ∀ j : J_class Threemap, j = (⟦f_id⟧𝓙) ∨ j = (⟦f_112⟧𝓙) ∨ j = (⟦f_000⟧𝓙) := by
  decide +native

/-! ### Finset-Based Equivalence Classes -/

-- Computing explicit equivalence classes
#eval ⟦f_220⟧𝓡_fin
#eval ⟦f_220⟧𝓛_fin
#eval ⟦f_220⟧𝓙_fin
#eval ⟦f_220⟧𝓗_fin

/-! ### ideal Computations -/

#eval f_000 •fin Threemap¹  -- right ideal of f_000
#eval f_112 •fin Threemap¹  -- right ideal of f_112

#eval Threemap¹ •fin f_000  -- left ideal of f_000
#eval Threemap¹ •fin f_id   -- left ideal of f_id

#eval Threemap¹ ••fin f_000  -- Two-sided ideal of f_000
#eval Threemap¹ ••fin f_112  -- Two-sided ideal of f_112

/-! ### Correspondence Theorems

This section demonstrates how abstract Green's relations
correspond to concrete properties of functions.
-/

/-- Classifies a function based on its form (pattern of values).
    Returns a value in `Fin 5` representing one of the 5 possible forms-/
def form_of_fun (f : Threemap) : Fin 5 :=
  if f 0 = f 1 ∧ f 1 = f 2 then 0 -- [a, a, a]
  else if f 1 = f 2 then 1 -- [b, a, a]
  else if f 0 = f 2 then 2 -- [a, b, a]
  else if f 0 = f 1 then 3 -- [a, a, b]
  else 4 -- [a, b, c]

/-- The image of a function as a Finset, representing which values can be outputs. -/
def image_of_fun (f : Threemap) : Finset (Fin 3) := Finset.image f Finset.univ

/-- The rank of a function, defined as the cardinality of its image. -/
def rank (f : Threemap) : Nat := Finset.card (Finset.image f Finset.univ)

/-- **𝓡 Correspondence**: Two functions are R-equivalent iff they have the same form. -/
theorem R_eqv_form_correspondence (f g : Threemap) :
    f 𝓡 g ↔ form_of_fun f = form_of_fun g := by
  revert f g; decide +native

/-- **𝓛  Correspondence**: Two functions are L-equivalent iff they have the same image. -/
theorem L_eqv_image_correspondence (f g : Threemap) :
    f 𝓛 g ↔ image_of_fun f = image_of_fun g := by
  revert f g; decide +native

/-- **𝓙 Correspondence**: Two functions are J-equivalent iff they have the same rank. -/
theorem J_eqv_rank_correspondence (f g : Threemap) :
    f 𝓙 g ↔ rank f = rank g := by
  revert f g; decide +native

/-- **𝓗 Correspondence**: Two functions are H-equivalent iff
they have both the same form and image. -/
theorem H_eqv_correspondence (f g : Threemap) :
    f 𝓗 g ↔ form_of_fun f = form_of_fun g ∧ image_of_fun f = image_of_fun g := by
  revert f g; decide +native

/-- **𝓓 Correspondence**: Same as the 𝓙 -/
theorem D_eqv_correspondence (f g : Threemap) : f 𝓓 g ↔ f 𝓙 g := by
  revert f g; decide +native

theorem D_class_fin_eq_J (f: Threemap) : ⟦f⟧𝓓_fin = ⟦f⟧𝓙_fin := by
  revert f; decide +native

theorem D_class_eq_iff_J (f g: Threemap) :
    (⟦f⟧𝓓 : D_class Threemap) = (⟦g⟧𝓓 : D_class Threemap) ↔
    (⟦f⟧𝓙 : J_class Threemap) = (⟦g⟧𝓙 : J_class Threemap) := by
  revert f g; decide +native

end Threemap

end THREEMAP
