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
* R_L commute : commutativity of  ≡ᵣ and ≡ₗ

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

theorem R_L_commute {a b: M}: (L_rel ∘ᴿ R_rel) a b ↔ (R_rel ∘ᴿ L_rel) a b:= by
  unfold rel_composition
  constructor
  · rintro ⟨c, hr, hl⟩
    obtain ⟨u, hu⟩ := hr.left
    obtain ⟨v, hv⟩ := hl.right
    let x := u * c * v
    use x
    constructor
    have h1 : u * c ≡ᵣ u * b := R_rel.lmult_compat hl
    have hx : x = u * b := calc
      x = u * c * v := rfl
      _ = u * (c * v) := by rw[← mul_assoc]
      _ = u * b := by rw [hv]
    rw[hu, hx]
    exact h1

    have h2 : a * v ≡ₗ c * v := L_rel.rmult_compat hr
    have hx : x = a * v := calc
      x = u * c * v := rfl
      _ = (u * c) * v := by rw[mul_assoc]
      _ = a * v := by rw [hu]
    rw[hv, hx]
    exact h2

  · rintro ⟨c, hl, hr⟩
    obtain ⟨u, hu⟩ := hl.left
    obtain ⟨v, hv⟩ := hr.right
    let x := v * c * u
    use x
    constructor
    have h1 : b * u ≡ₗ c * u := L_rel.rmult_compat hr.symm
    have hx : x = b * u := calc
      x = v * c * u := rfl
      _ = (v * c) * u := by rw [mul_assoc]
      _ = b * u := by rw [hv]
    rw [hu, hx]
    exact h1.symm

    have h2 : v * a  ≡ᵣ v * c := R_rel.lmult_compat hl
    have hx : x = v * a := calc
      x = v * c * u := rfl
      _ = v * (c * u) := by rw [mul_assoc]
      _ = v * a := by rw [hu]
    rw [hv, hx]
    exact h2



def D_rel (a b : M) : Prop :=
  ∃ x : M, a ≡ᵣ x ∧ x ≡ₗ b

infix:50 " ≡ᴰ " => D_rel

theorem D_rel_def {a b : M} : a ≡ᴰ b ↔ ∃ x : M, a ≡ᵣ x ∧ x ≡ₗ b :=
  Iff.rfl

def D_rel_alt (a b : M) : Prop :=
  ∃ x : M, a ≡ₗ x ∧ x ≡ᵣ b

theorem D_rel_alt_def {a b : M} : a ≡ᴰ b ↔ D_rel_alt a b := by
  unfold D_rel D_rel_alt
  constructor
  · rintro ⟨x, ha, hb⟩
    obtain ⟨y, hb1, ha1⟩ := (R_L_commute.mp) ⟨x, hb.symm, ha.symm⟩
    exact ⟨y, ha1.symm, hb1.symm⟩
  · rintro ⟨x, ha, hb⟩
    obtain ⟨y, hb2, ha2⟩ := (R_L_commute.mpr) ⟨x, hb.symm, ha.symm⟩
    exact ⟨y, ha2.symm, hb2.symm⟩
