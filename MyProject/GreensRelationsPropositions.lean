import MyProject.GreensRelations

/-!
# Propositions about Green's Relations

This file contains proofs of basic results related to Green's Relations.
This includes the compatibility of ≤ᵣ, ≤ₗ, ≤ⱼ/≡ᵣ, ≡ₗ, ≡ⱼ with left/right multiplication
and the commutativity of ≡ᵣ and ≡ₗ.

Additionally, we use these to define the relation 𝓓 = 𝓡𝓛 = 𝓛𝓡 and prove
that 𝓓 = 𝓙 in finite semigroups.

Names as follows--
* le_R.lmult_compat : left-compatibility of ≤ᵣ with multiplication
* le_L.rmult_compat : right-compatibility of ≤ₗ with multiplication
* R_rel.lmult_compat : left-compatibility of ≡ᵣ with multiplication
* L_rel.rmult_compat : right-compatibility of ≡ₗ with multiplication
* R_L commute : commutativity of  ≡ᵣ and ≡ₗ
* D_iff_J_finite_semigroup : 𝓓 = 𝓙 in finite semigroups

## Green's D_Relation
Define Green's 𝓓-relation on a monoid M as 𝓡𝓛.
That is, a ≡ᴰ b if there exists x such that a ≡ᵣ x and x ≡ᵣ b.
We also show this is equivalent to the composition in the other order-- 𝓓 = 𝓛𝓡.

## Definitions

* `D_rel` : Green's 𝓓 relation
* `D_rel_def` : `a ≡ᴰ b` ↔ ∃ x, a ≡ᵣ x ∧ x ≡ₗ b
* `D_rel_alt` : `a ≡ᴰ b` ↔ ∃ x, a ≡ₗ x ∧ x ≡ᵣ b

## TODO
- Put the defition of the D relation in GreensRelations.lean
- Rename this file to GreensRelationsBasic.lean
-/

variable {S} [Semigroup S]

theorem le_R.lmult_compat {a b c : S¹} (h : a ≤ᵣ b) : c * a ≤ᵣ c * b := by
  obtain ⟨x, hx⟩ := h
  use x
  rw [hx, mul_assoc]

theorem le_L.rmult_compat {a b c : S¹} (h : a ≤ₗ b) : a * c ≤ₗ b * c := by
  obtain ⟨x, hx⟩ := h
  use x
  rw [← mul_assoc, hx]

theorem R_rel.lmult_compat {a b c : S¹} (h : a ≡ᵣ b) : c * a ≡ᵣ c * b := by
  constructor
  · exact le_R.lmult_compat h.left
  · rw [R_rel] at h
    apply le_R.lmult_compat h.right

theorem L_rel.rmult_compat {a b c : S¹} (h : a ≡ₗ b) : a * c ≡ₗ b * c := by
  constructor
  · exact le_L.rmult_compat h.left
  · rw [L_rel] at h
    apply le_L.rmult_compat h.right


def rel_composition {α : Type*} (r s : α → α → Prop) : α → α → Prop :=
  λ a c => ∃ b, r a b ∧ s b c

notation:50 f " ∘ᴿ " g:50 => rel_composition f g

theorem R_L_commute {a b: S¹}: (L_rel ∘ᴿ R_rel) a b ↔ (R_rel ∘ᴿ L_rel) a b:= by
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
    rw[hu, hx]; exact h1
    have h2 : a * v ≡ₗ c * v := L_rel.rmult_compat hr
    have hx : x = a * v := calc
      x = u * c * v := rfl
      _ = (u * c) * v := by rw[mul_assoc]
      _ = a * v := by rw [hu]
    rw[hv, hx]; exact h2

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
    rw [hu, hx]; exact h1.symm

    have h2 : v * a  ≡ᵣ v * c := R_rel.lmult_compat hl
    have hx : x = v * a := calc
      x = v * c * u := rfl
      _ = v * (c * u) := by rw [mul_assoc]
      _ = v * a := by rw [hu]
    rw [hv, hx]; exact h2


def D_rel (a b : S¹) : Prop :=
  ∃ x : S¹, a ≡ᵣ x ∧ x ≡ₗ b

infix:50 " ≡ᴰ " => D_rel

def D_rel_alt (a b : S¹) : Prop :=
  ∃ x : S¹, a ≡ₗ x ∧ x ≡ᵣ b

theorem D_rel_alt_def {a b : S¹} : a ≡ᴰ b ↔ D_rel_alt a b := by
  unfold D_rel D_rel_alt
  constructor
  · rintro ⟨x, ha, hb⟩
    obtain ⟨y, hb1, ha1⟩ := (R_L_commute.mp) ⟨x, hb.symm, ha.symm⟩
    exact ⟨y, ha1.symm, hb1.symm⟩
  · rintro ⟨x, ha, hb⟩
    obtain ⟨y, hb2, ha2⟩ := (R_L_commute.mpr) ⟨x, hb.symm, ha.symm⟩
    exact ⟨y, ha2.symm, hb2.symm⟩

/- I used fintype instead of finite for S. I originally used finite, but
I needed to use the fact that a finite S implies a finite S¹ to use exists_idempotent_pow, and in our
WithOne file, we only have "instance with_one_fintype" to supply this fact.
Should we create an analogous "instance with_one_finite"
so that this theorem can be in terms of an argument [Finite S]? Or otherwise
rewrite this theorem to make that so?-/

theorem D_iff_J_finite_semigroup [Fintype S] {a b : S¹} : a ≡ᴰ b ↔ a ≡ⱼ b := by
  constructor
  · rintro ⟨x, ⟨⟨r1, hrx⟩, ⟨r2, hxr⟩⟩, ⟨⟨l1, hxl⟩, ⟨l2, hbl⟩⟩⟩
    constructor
    have ha: a ≤ⱼ b := by
      unfold le_J
      have haj : a = l1 * b * r1 := by
        rw [← hxl, ← hrx]
      use l1, r1
    exact ha
    have hb: b ≤ⱼ a := by
      unfold le_J
      have hbj : b = l2 * a * r2 := by
        rw [mul_assoc, ← hxr, hbl]
      use l2, r2
    exact hb
  · rintro ⟨⟨x, y, hab⟩, ⟨u, v, hba⟩⟩
    have h : x * u * a * v * y = a := by
      rw [hba] at hab
      repeat rw[mul_assoc]
      rw[mul_assoc, mul_assoc, mul_assoc] at hab --repeat not working here, nor simp_rw... why?
      exact hab.symm
    have hk: ∀(k : ℕ+), (x * u)^k * a * (v * y)^k = a := by
      intro k
      induction k using PNat.recOn with
      | one =>
        rw[mul_assoc] at h
        simp
        exact h
      | succ k ih =>
        simp_rw[<- PNat.pow_succ, PNat.pow_mul_comm' (x * u), <- mul_assoc, mul_assoc (x * u)]
        rw[ih]
        repeat rw[<-mul_assoc]
        exact h
    have ⟨k, he⟩ := Semigroup.exists_idempotent_pow (x * u)
    have ⟨l, hf⟩ := Semigroup.exists_idempotent_pow (v * y)
    have hua : (u * a) ≡ₗ a := by
     constructor
      · use u
      · sorry
    have hav : (a * v) ≡ᵣ a := by
     constructor
      · use v
      · sorry
    have hl : b ≡ₗ (a * v) := by
      have huav : u * a * v ≡ₗ a * v := L_rel.rmult_compat hua
      rw[hba]
      exact huav
    have hr : D_rel_alt b a := by
     let x := a * v
     exact ⟨(a * v), hl, hav⟩
    have hd: b ≡ᴰ a := by
      rw [<- D_rel_alt_def] at hr
      exact hr
