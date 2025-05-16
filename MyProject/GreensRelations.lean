import MyProject.Idempotence

/-! # Green's Relations for Monoids

This file defines Green's relations (𝓡, 𝓛, 𝓙, and 𝓗), which classify elements
based on the principal ideals they generate. It also includes decidability
instances and functions for computing equivalence classes in finite monoids.

## Key Definitions

This file introduces specialized notation:
*   **Preorder Relations Notation**: `a ≤ᵣ b`, `a ≤ₗ b`, `a ≤ⱼ b`
*   **Equivalence Relations Notation**: `a ≡ᵣ b`, `a ≡ₗ b`, `a ≡ⱼ b`, `a ≡ₕ b`
*   **Equivalence Classes Notation**: `⟦a⟧ᵣ`, `⟦a⟧ₗ`, `⟦a⟧ⱼ`, `⟦a⟧ₕ`

The core definitions and supporting structures are:

*   **Preorder Relations**: These define "less than or equal to" style
  relationships between elements based on ideal containment.
    *   `le_R a b`: Defines the right preorder `a ≤ᵣ b`
    *   `le_L a b`: Defines the left preorder `a ≤ₗ b`
    *   `le_J a b`: Defines the two-sided preorder `a ≤ⱼ b`
    *   `le_H a b`: Defines the preorder `a ≤ₕ b`
    *   `le_R_decidable`, `le_L_decidable`, `le_J_decidable`, `le_H_decidable`:
      Instances providing decidability for these preorder relations
      in finite monoids with decidable equality.

*   **Green's Equivalence Relations**: These are defined as mutual preorder
    and instances of `Setoid` structures.
    *   `R_rel a b`: Defines Green's 𝓡-relation `a ≡ᵣ b`
    *   `L_rel a b`: Defines Green's 𝓛-relation `a ≡ₗ b`
    *   `J_rel a b`: Defines Green's 𝒥-relation `a ≡ⱼ b`
    *   `H_rel a b`: Defines Green's 𝓗-relation `a ≡ₕ b`
    *   `R_setoid`, `L_setoid`, `J_setoid`, `H_setoid`:
      Instances establishing `Setoid` structures
    *   `decidableR`, `decidableL`, `decidableJ`, `decidableH`:
      Instances providing decidability for these Setoids
      in finite monoids with decidable equality.

*   **Equivalence Classes**: Functions that compute the equivilance classe
    of a given element, returning a `Finset` of the elements in the class.
    Due to the decidability instances, these are computable with `#eval`
    *   `R_class a`: Returns the 𝓡-class `⟦a⟧ᵣ`
    *   `L_class a`: Returns the 𝓛-class `⟦a⟧ₗ`
    *   `J_class a`: Returns the 𝒥-class `⟦a⟧ⱼ`
    *   `H_class a`: Returns the 𝓗-class `⟦a⟧ₕ`

This file imports `Idempotence.lean` and is imported by the example file
`Threemap.lean`, which demonstrates these relations in a concrete case. -/

section GREENS_RELATIONS

variable {M} [Monoid M]

/-- the "right-ideal" preorder: a ≤ᵣ b iff a M ⊇ b M-/
@[simp] def le_R (a b : M) : Prop := ∃ x, a = b * x
/-- the "left-ideal" preorder: a ≤ₗ b iff M·a ⊇ M·b -/
@[simp] def le_L (a b : M) : Prop := ∃ x, a = x * b
/-- the "two-sided-ideal" preorder: a ≤ⱼ b iff M·a·M ⊇ M·b·M -/
@[simp] def le_J (a b : M) : Prop := ∃ x y, a = x * b * y
/-- the "two-sided-ideal" preorder: a ≤ₕ b iff a M ⊇ b M and M a ⊇ M -/
@[simp] def le_H (a b : M) : Prop := le_R a b ∧ le_L a b

-- 1. Preorder notation: typed \\leq\\_r
notation:50 f " ≤ᵣ " g:50 => le_R f g
notation:50 f " ≤ₗ " g:50 => le_L f g
notation:50 f " ≤ⱼ " g:50 => le_J f g
notation:50 f " ≤ₕ " g:50 => le_H f g

/-- Decidability instance for the right-ideal preorder relation -/
instance le_R_decidable [Fintype M] [DecidableEq M] (a b : M) :
    Decidable (le_R a b) := by simp; infer_instance
/-- Decidability instance for the left-ideal preorder relation -/
instance le_L_decidable [Fintype M] [DecidableEq M] (a b : M) :
    Decidable (le_L a b) := by simp; infer_instance
/-- Decidability instance for the two-sided-ideal preorder relation -/
instance le_J_decidable [Fintype M] [DecidableEq M] (a b : M) :
    Decidable (le_J a b) := by simp; infer_instance
/-- Decidability instance for the H relation -/
instance le_H_decidable [Fintype M] [DecidableEq M] (a b : M) :
    Decidable (le_H a b) := by simp; infer_instance

/-- Green's 𝓡-relation-/
@[simp] def R_rel (a b : M) : Prop := le_R a b ∧ le_R b a
/-- Green's 𝓛-relation -/
@[simp] def L_rel (a b : M) : Prop := le_L a b ∧ le_L b a
/-- Green's 𝒥-relation -/
@[simp] def J_rel (a b : M) : Prop := le_J a b ∧ le_J b a
/-- Green's 𝓗-relation = intersection of L and R -/
@[simp] def H_rel (a b : M) : Prop := L_rel a b ∧ R_rel a b

/-! 1. Equivilance notation: typed \\==\\_r -/
notation:50 f " ≡ᵣ " g:50 => R_rel f g
notation:50 f " ≡ₗ " g:50 => L_rel f g
notation:50 f " ≡ⱼ " g:50 => J_rel f g
notation:50 f " ≡ₕ " g:50 => H_rel f g

/-! # reflexivity, symmetry, and transitivity theorems-/

/-- Green's R-relation is reflexive -/
theorem R_rel.refl (a : M) : R_rel a a := by simp [R_rel, le_R]; use 1; simp
/-- Green's L-relation is reflexive -/
theorem L_rel.refl (a : M) : L_rel a a := by simp [L_rel, le_L]; use 1; simp
/-- Green's J-relation is reflexive -/
theorem J_rel.refl (a : M) : J_rel a a := by
  simp [J_rel, le_J]; use 1, 1; simp
/-- Green's H-relation is reflexive -/
theorem H_rel.refl (a : M) : H_rel a a := by
  simp; apply And.intro <;> use 1; simp; symm; apply mul_one

/-- Green's R-relation is symmetric -/
theorem R_rel.symm {a b : M} (h : R_rel a b) : R_rel b a := by
  simp_all only [R_rel, le_R, and_self]
/-- Green's L-relation is symmetric -/
theorem L_rel.symm {a b : M} (h : L_rel a b) : L_rel b a := by
  simp_all only [L_rel, le_L, and_self]
/-- Green's J-relation is symmetric -/
theorem J_rel.symm {a b : M} (h : J_rel a b) : J_rel b a := by
  simp_all only [J_rel, le_J, and_self]
/-- Green's H-relation is symmetric -/
theorem H_rel.symm {a b : M} (h : H_rel a b) : H_rel b a := by
  cases h; constructor
  · exact L_rel.symm (by assumption)
  · exact R_rel.symm (by assumption)

/-- Green's 𝓡-relation is transitive -/
theorem R_rel.trans {a b c : M} (hab : R_rel a b) (hbc : R_rel b c) :
    R_rel a c := by
  simp_all;
  obtain ⟨⟨x₁, h_x₁a_b⟩, ⟨y₁, h_y₁b_a⟩⟩ := hab
  obtain ⟨⟨x₂, h_x₂b_c⟩, ⟨y₂, h_y₂c_b⟩⟩ := hbc
  subst h_y₁b_a h_y₂c_b; apply And.intro
  · use (x₂ * x₁); rw [← mul_assoc, ← h_x₂b_c, ← h_x₁a_b]
  · use (y₁ * y₂); rw [← mul_assoc]
/-- Green's 𝓛-relation is transitive -/
theorem L_rel.trans {a b c : M} (hab : L_rel a b) (hbc : L_rel b c) :
    L_rel a c := by
  simp_all;
  obtain ⟨⟨x₁, h_ax₁_b⟩, ⟨y₁, h_by₁_a⟩⟩ := hab
  obtain ⟨⟨x₂, h_bx₂_c⟩, ⟨y₂, h_cy₂_b⟩⟩ := hbc
  subst h_by₁_a h_cy₂_b; apply And.intro
  · use (x₁ * x₂); rw [mul_assoc, ← h_bx₂_c, ← h_ax₁_b]
  · use (y₂ * y₁); rw [← mul_assoc]
/-- Green's J-relation is transitive -/
theorem J_rel.trans {a b c : M} (hab : J_rel a b) (hbc : J_rel b c) :
    J_rel a c := by
  simp_all
  obtain ⟨⟨left₁, right₁, h_lab⟩,⟨left₂, right₂, h_rba⟩⟩ := hab
  obtain ⟨⟨left₃, right₃, h_lbc⟩, ⟨left₄, right₄, h_rcb⟩⟩ := hbc
  subst h_rcb h_rba
  apply And.intro
  · use (left₁ * left₃), (right₃ * right₁)
    simp_rw [← mul_assoc] at *
    have helper :
      left₁ * left₃ * left₄ * left₂ * a * right₂ * right₄ * right₃ * right₁ =
      left₁ * (left₃ * left₄ * left₂ * a * right₂ * right₄ * right₃) * right₁ :=
      by simp [mul_assoc]
    simp_rw [helper, ← h_lbc, ← mul_assoc, ← h_lab]
  · use (left₄ * left₂), (right₂ * right₄)
    rw [← mul_assoc, ← mul_assoc, ← mul_assoc]
/-- Green's H-relation is transitive -/
theorem H_rel.trans {a b c : M} (hab : H_rel a b) (hbc : H_rel b c) :
    H_rel a c := by
  cases hab; cases hbc; constructor
  · exact L_rel.trans ‹_› ‹_›
  · exact R_rel.trans ‹_› ‹_›

/-- Setoid instance for Green's R-relation -/
instance R_setoid : Setoid M where
  r     := R_rel
  iseqv := ⟨R_rel.refl, R_rel.symm, R_rel.trans⟩
/-- Setoid instance for Green's L-relation -/
instance L_setoid : Setoid M where
  r     := L_rel
  iseqv := ⟨L_rel.refl, L_rel.symm, L_rel.trans⟩
/-- Setoid instance for Green's J-relation -/
instance J_setoid : Setoid M where
  r     := J_rel
  iseqv := ⟨J_rel.refl, J_rel.symm, J_rel.trans⟩
/-- Setoid instance for Green's H-relation -/
instance H_setoid : Setoid M where
  r     := H_rel
  iseqv := ⟨H_rel.refl, H_rel.symm, H_rel.trans⟩

/-- Decidability instance for Green's R-relation -/
instance decidableR [inst : Monoid M] [Fintype M] [DecidableEq M]:
    DecidableRel (@R_rel M inst) := by
  simp [DecidableRel]; intros a b; exact instDecidableAnd
/-- Decidability instance for Green's L-relation -/
instance decidableL [inst : Monoid M] [Fintype M] [DecidableEq M] :
    DecidableRel (@L_rel M inst) := by
  simp [DecidableRel]; intros a b; exact instDecidableAnd
/-- Decidability instance for Green's H-relation -/
instance decidableH [inst : Monoid M] [Fintype M] [DecidableEq M] :
    DecidableRel (@H_rel M inst) := by
  simp [DecidableRel]; intros a b
  exact instDecidableAnd
/-- Decidability instance for Green's J-relation -/
instance decidableJ [inst : Monoid M] [Fintype M] [DecidableEq M] :
    DecidableRel (@J_rel M inst) := by
  simp [DecidableRel]; intros a b; exact instDecidableAnd

/-- The 𝓡-class of `a` as a `Finset M`. -/
def R_class [inst : Monoid M] [Fintype M] [DecidableEq M] (a : M) : Finset M :=
  Finset.univ.filter (@R_rel M inst a)
/-- The 𝓛-class of `a` as a `Finset M`. -/
def L_class [inst : Monoid M] [Fintype M] [DecidableEq M] (a : M) : Finset M :=
  Finset.univ.filter (@L_rel M inst a)
/-- The 𝓙-class of `a` as a `Finset M`. -/
def J_class [inst : Monoid M] [Fintype M] [DecidableEq M] (a : M) : Finset M :=
  Finset.univ.filter (@J_rel M inst a)
/-- The 𝓗-class of `a` as a `Finset M`. -/
def H_class [inst : Monoid M] [Fintype M] [DecidableEq M] (a : M) : Finset M :=
  Finset.univ.filter (@H_rel M inst a)

/-! R-class notattion: typed \\[[ f \\]]\\_r  -/
notation "⟦" f "⟧ᵣ" => R_class f
notation "⟦" f "⟧ₗ" => L_class f
notation "⟦" f "⟧ⱼ" => J_class f
notation "⟦" f "⟧ₕ" => H_class f

end GREENS_RELATIONS
