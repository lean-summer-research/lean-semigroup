import MyProject.GreensRelations.Defs
import Mathlib.Algebra.Group.WithOne.Basic

/-! # Ideals in Semigroups

This file defines the notion of ideals in semigroups and gives a characterization of
Green's relations in terms of these ideals.

We adjoin a unit to the semigroup `S` (denoted `S¹`) so that we can still talk
about `S¹ • a``, `a • S¹`, `S¹ •• a` just like in the monoid case.
-/

section IdealCharacterizations

variable {S: Type*} [Semigroup S]

structure IsLeftIdeal (I : Set S) : Prop where
  nonempty : I.Nonempty
  mul_mem_left : ∀ (s : S) {i : S}, i ∈ I → s * i ∈ I

structure IsRightIdeal (I : Set S) : Prop where
  nonempty : I.Nonempty
  mul_mem_right : ∀ (s : S) {i : S}, i ∈ I → i * s ∈ I

structure IsTwoSidedIdeal (I : Set S) : Prop where
(left : IsLeftIdeal I)
(right : IsRightIdeal I)

/-- the left ideal `S • a` -/
def principal_left_ideal [Semigroup S] (a : S) : Set S :=
  {x | ∃ y : S, x = y * a ∨ x = a}
/-- the principal right ideal `a • S` -/
def principal_right_ideal [Semigroup S] (a : S) : Set S :=
  {x | ∃ y : S, x = a * y ∨ x = a}

/-- the principal two-sided ideal `S •• a` -/
def principal_two_sided_ideal (a : S) : Set S :=
  {x | ∃ (y z : WithOne S), y * (a : WithOne S) * z = (x : WithOne S)}

lemma principal_left_ideal_is_left_ideal (a : S) : IsLeftIdeal (principal_left_ideal a) := by
  constructor
  case nonempty =>
    use a
    use a
    exact Or.inr rfl

  case mul_mem_left =>
    intros s i h_i
    rcases h_i with ⟨t, h_cases⟩
    rcases h_cases with h_mul | h_eq

    /- this is if i=t*a, NTS s * (t * a) ∈ (a)-/
    · rw [h_mul]
      use (s * t)
      rw [mul_assoc]
      exact Or.inl rfl
    /-this is if i=a -/
    · rw [h_eq]
      use s
      exact Or.inl rfl
lemma principal_right_ideal_is_right_ideal (a : S) : IsRightIdeal (principal_right_ideal a) := by
  constructor
  case nonempty =>
    use a
    use a
    exact Or.inr rfl
  case mul_mem_right =>
    intros s i h_i
    rcases h_i with ⟨t, h_cases⟩
    rcases h_cases with h_mul | h_eq
    · rw [h_mul]
      use (t * s)
      rw [mul_assoc]
      exact Or.inl rfl
    · rw [h_eq]
      use s
      exact Or.inl rfl
lemma principal_two_sided_ideal_is_two_sided_ideal (a : S) : IsTwoSidedIdeal (principal_two_sided_ideal a) := by
  constructor
  · constructor
    · exact ⟨a, 1, 1, by simp⟩
    · intro s i hi
      rcases hi with ⟨y, z, h⟩
      use (s : WithOne S) * y, z
      calc
        ((s : WithOne S) * y) * (a : WithOne S) * z = (s : WithOne S) * (y * (a : WithOne S) * z) := by simp [mul_assoc]
        _ = (s : WithOne S) * (i : WithOne S) := by rw [h]
        _ = (s * i : WithOne S) := by simp
  · constructor
    · exact ⟨a, 1, 1, by simp⟩
    · intro s i hi
      rcases hi with ⟨y, z, h⟩
      use y, z * (s : WithOne S)
      calc
        y * (a : WithOne S) * (z * (s : WithOne S)) = (y * (a : WithOne S) * z) * (s : WithOne S) := by simp [mul_assoc]
        _ = (i : WithOne S) * (s : WithOne S) := by rw [h]
        _ = (i * s : WithOne S) := by simp


/-! Ideals of sets (rather than ideals of elements) -/
/- do we need these? -/

/-! Ideal notation, typed \bub -/
-- More explicit, robust notation syntax

notation:65 S:66 " • " a:67 => @principal_left_ideal S _ a
notation:65 a:66 " • " S:67 => @principal_right_ideal S _ a
notation:65 S:66 " •• " a:67 => @principal_two_sided_ideal S _ a
variable (a b : S)

/-- The left ideal of `a * b` is contained in the left ideal of `b`. -/
lemma left_ideal_subset (a b : S): (S • (a * b)) ⊆ (S • b) := by
  simp [principal_left_ideal];
  intro x y hh
  rcases hh with ⟨rfl | rfl⟩
  · use (y * a : S); simp [mul_assoc]
  · use a ;
    rename_i h
    subst h
    simp_all only [true_or]

/-- The right ideal of `a * b` is contained in the right ideal of `a`. -/
lemma right_ideal_subset : ((a * b) • S) ⊆ (a • S) := by
  simp [principal_right_ideal]
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
