import MyProject.GreensRelations

/-!
# Propositions about Green's Relations

This file contains proofs of basic results about Green's Relations.
This includes the compatibility of ≤ᵣ, ≤ₗ, ≤ⱼ/≡ᵣ, ≡ₗ, ≡ⱼ with multiplication,
the commutativity of ≡ᵣ and ≡ₗ, and the definition of 𝓓 = 𝓡𝓛 = 𝓛𝓡.

Names as follows--
* le_R.lmult_compat : left-compatibility of ≤ᵣ with multiplication
* le_L.rmult_compat : right-compatibility of ≤ₗ with multiplication
* R_rel.lmult_compat : left-compatibility of ≡ᵣ with multiplication
* L_rel.rmult_compat : right-compatibility of ≡ₗ with multiplication
* R_L commute : commutativity of  ≡ᵣ and ≡ₗ (incomplete)

## Green's D_Relation
Define Green's 𝓓-relation on a monoid M as 𝓡𝓛.
That is, a ≡ᴰ b if there exists x such that a ≡ᵣ x and x ≡ᵣ b.
We also show this is equivalent to the composition in the other order-- 𝓓 = 𝓛𝓡.

## Definitions

* `D_rel` : The Green's 𝓓 relation
* `D_rel_def` : `a ≡ᴰ b` ↔ ∃ x, a ≡ᵣ x ∧ x ≡ₗ b
* `D_rel_alt` : `a ≡ᴰ b` ↔ ∃ x, a ≡ₗ x ∧ x ≡ᵣ b
-/

variable {M} [Monoid M]

theorem le_R.lmult_compat {a b c : M} (h : a ≤ᵣ b) : c * a ≤ᵣ c * b := by
  obtain ⟨x, hx⟩ := h
  use x
  rw [hx, mul_assoc]

theorem le_L.rmult_compat {a b c : M} (h : a ≤ₗ b) : a * c ≤ₗ b * c := by
  obtain ⟨x, hx⟩ := h
  use x
  rw [← mul_assoc, hx]

theorem R_rel.lmult_compat {a b c : M} (h : a ≡ᵣ b) : c * a ≡ᵣ c * b := by
  constructor
  · exact le_R.lmult_compat h.left
  · rw [R_rel] at h
    apply le_R.lmult_compat h.right

theorem L_rel.rmult_compat {a b c : M} (h : a ≡ₗ b) : a * c ≡ₗ b * c := by
  constructor
  · exact le_L.rmult_compat h.left
  · rw [L_rel] at h
    apply le_L.rmult_compat h.right


def rel_composition {α : Type*} (r s : α → α → Prop) : α → α → Prop :=
  λ a c => ∃ b, r a b ∧ s b c

notation:50 f " ∘ᴿ " g:50 => rel_composition f g

theorem R_L_commute {a b: M}: (R_rel ∘ᴿ L_rel) a b ↔ (L_rel ∘ᴿ R_rel) a b:= by
  sorry


def D_rel (a b : M) : Prop :=
  ∃ x : M, a ≡ᵣ x ∧ x ≡ₗ b

infix:50 " ≡ᴰ " => D_rel

theorem D_rel_def {a b : M} : a ≡ᴰ b ↔ ∃ x : M, a ≡ᵣ x ∧ x ≡ₗ b :=
  Iff.rfl

def D_rel_alt (a b : M) : Prop :=
  ∃ x : M, a ≡ₗ x ∧ x ≡ᵣ b

theorem D_rel_alt_def {a b : M} : a ≡ᴰ b ↔ D_rel_alt a b := by
  unfold D_rel D_rel_alt
  apply Iff.trans
  · apply R_L_commute
  · exact Iff.rfl
