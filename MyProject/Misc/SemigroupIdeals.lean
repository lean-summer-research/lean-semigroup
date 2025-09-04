import MyProject.GreensRelations.Defs
import Mathlib.Algebra.Group.WithOne.Basic

/-! # Ideals in Semigroups

This file defines the notion of ideals in semigroups and gives a characterization of
Green's relations in terms of these ideals.

We adjoin a unit to the semigroup `S` (denoted `S¹`) so that we can still talk
about `S¹ • a`, `a • S¹`, `S¹ •• a` just like in the monoid case.
-/

section IdealCharacterizations

variable (S) [Semigroup S]

/-- the left ideal `S • a` -/
def left_ideal [Semigroup S] (a : S) : Set S :=
  {x | ∃ y : S, x = y * a ∨ x = a}

/-- the right ideal `a • S` -/
def right_ideal [Semigroup S] (a : S) : Set S :=
  {x | ∃ y : S, x = a * y ∨ x = a}

/-- the two-sided ideal `S •• a` -/
def two_sided_ideal [Semigroup S] (a : S) : Set S :=
  {x | ∃ y z : S, x = y * a * z ∨ x = a}

/-! Ideals of sets (rather than ideals of elements) -/
/- do we need these? -/

/-! Ideal notation, typed \bub -/
notation:65 S " • " a:66 => left_ideal S a
notation:65 a:66 " • " S => right_ideal S a
notation:65 S " •• " a:66  => two_sided_ideal S a

variable (a b : S)

/-- The left ideal of `a * b` is contained in the left ideal of `b`. -/
lemma left_ideal_subset (a b : S): (S • (a * b)) ⊆ (S • b) := by
  simp [left_ideal];
  intro x y hh
  rcases hh with ⟨rfl | rfl⟩
  · use (y * a : S); simp [mul_assoc]
  · use a ;
    rename_i h
    subst h
    simp_all only [true_or]

/-- The right ideal of `a * b` is contained in the right ideal of `a`. -/
lemma right_ideal_subset : ((a * b) • S) ⊆ (a • S) := by
  simp [right_ideal]
  intro x y hh
  rcases hh with ⟨rfl | rfl⟩
  · use (b * y : S); simp [← mul_assoc]
  · use b ;
    rename_i h
    subst h
    simp_all only [true_or]

end IdealCharacterizations

/-! Preorder characterizations from ideals -/
/-
theorem L_preorder_iff_ideal :
    a ≤𝓛 b ↔ (S • a) ⊆ (S • b) := by
  rw [L_preorder_iff_without_one]
  constructor
  · intro h; cases h with
    | inl heq => simp [heq]
    | inr =>
  · intro h
    simp [left_ideal] at h
    specialize h a (1 : S¹)
    simp [← L_preorder_iff_without_one, L_preorder] at h
    exact h

theorem R_preorder_iff_ideal :
    a ≤𝓡 b ↔ (a • S) ⊆ (b • S) := by
  rw [R_preorder_iff_without_one]
  constructor
  · intro h; cases h with
    | inl heq => simp [heq]
    | inr ⟨x, hx⟩ => rw [hx]; apply right_ideal_subset
  · intro h
    simp [right_ideal] at h
    specialize h a (1 : S¹)
    simp [← R_preorder_iff_without_one, R_preorder] at h
    exact h

theorem J_preorder_iff_ideal :
    a ≤𝓙 b ↔ (S¹ •• a) ⊆ (S¹ •• b) := by
  constructor
  · simp [J_preorder, two_sided_ideal]
    rintro x y Hreach z t u rfl
    use (t * x), (y * u); simp [mul_assoc]
  · simp [J_preorder, two_sided_ideal]
    intro H
    specialize H a (1 : S¹) (1 : S¹)
    simp at H
    exact H

/-! Equivalence relation characterizations from ideals -/

theorem L_eqv_iff_ideal : a 𝓛 b ↔ (S¹ • a) = (S¹ • b) := by
  simp [L_eqv_iff, L_preorder_iff_ideal, antisymm_iff]

theorem R_eqv_iff_ideal : a 𝓡 b ↔ (a • S¹) = (b • S¹) := by
  simp [R_eqv_iff, R_preorder_iff_ideal, antisymm_iff]

theorem J_eqv_iff_ideal : a 𝓙 b ↔ (S¹ •• a) = (S¹ •• b) := by
  simp [J_eqv_iff, J_preorder_iff_ideal, antisymm_iff]
--/
