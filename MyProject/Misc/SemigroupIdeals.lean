import MyProject.GreensRelations.Defs
import Mathlib.Algebra.Group.WithOne.Basic

/-! # Ideals in Semigroups

This file defines the notion of ideals in semigroups and gives a characterization of
Green's relations in terms of these ideals.
-/

section IdealCharacterizations

variable (S) [Semigroup S]

/-- the left ideal `S • a` -/
def principal_left_ideal [Semigroup S] (a : S) : Set S :=
  {x | ∃ y : S, x = y * a ∨ x = a}

/-- the right ideal `a • S` -/
def principal_right_ideal [Semigroup S] (a : S) : Set S :=
  {x | ∃ y : S, x = a * y ∨ x = a}

/-- the two-sided ideal `S •• a` -/
def principal_two_sided_ideal [Semigroup S] (a : S) : Set S :=
  {x | ∃ y z : S, x = y * a * z ∨ x = a}

/-! Principal ideal notation, typed \bub \ ^ P -/
notation:65 S " •ᴾ " a:66 => principal_left_ideal S a
notation:65 a:66 " •ᴾ " S => principal_right_ideal S a
notation:65 S " ••ᴾ " a:66  => principal_two_sided_ideal S a

/-! Ideals of sets (rather than ideals of elements) -/

def left_ideal_set [Semigroup S] (A : Set S) : Set S :=
  {x | ∃ (a : A) (y : S), x = y * a}

def right_ideal_set [Semigroup S] (A : Set S) : Set S :=
  {x | ∃ (a : A) (y : S), x = a * y}

def two_sided_ideal_set [Semigroup S] (A : Set S) : Set S :=
  {x | ∃ (a : A) (y z : S), x = y * a * z}


/-! Ideal notation, typed \bub -/
notation:65 S " • " a:66 => left_ideal_set S a
notation:65 a:66 " • " S => right_ideal_set S a
notation:65 S " •• " a:66  => two_sided_ideal_set S a

variable (a b : S)

/-- The principal left ideal of `a * b` is contained in the left ideal of `b`. -/
@[simp] lemma principal_left_ideal_subset (a b : S): (S •ᴾ (a * b)) ⊆ (S •ᴾ b) := by
  simp [principal_left_ideal];
  intro x y  hh
  rcases hh with ⟨rfl | rfl⟩
  · use (y * a : S); simp [mul_assoc]
  · use a ;
    rename_i h
    subst h
    simp_all only [true_or]

/-- The principal right ideal of `a * b` is contained in the right ideal of `a`. -/
@[simp] lemma principal_right_ideal_subset : ((a * b) •ᴾ S) ⊆ (a •ᴾ S) := by
  simp [principal_right_ideal]
  intro x y hh
  rcases hh with ⟨rfl | rfl⟩
  · use (b * y : S); simp [← mul_assoc]
  · use b ;
    rename_i h
    subst h
    simp_all only [true_or]


end IdealCharacterizations

/-! Preorder characterizations from ideals
variable {S} [Semigroup S] (a b : S)

theorem L_preorder_iff_principal_ideal :
    a ≤𝓛 b ↔ (S •ᴾ a) ⊆ (S •ᴾ b) := by
    apply Iff.intro
    · intro a_1 x h
      simp[principal_left_ideal]
      refine exists_or.mpr ?_
      obtain ⟨y, hy⟩ := a_1
      use (y * x)

    · intro a_1
      sorry

  · intro h; cases h with
    | inl heq => simp [heq]
    | inr =>
  · intro h
    aesop[principal_left_ideal]
    specialize h a (1 : S¹)
    simp [← L_preorder_iff_without_one, L_preorder]
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
