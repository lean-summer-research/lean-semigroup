import MyProject.GreensRelations.Basic

/-! # Green's D-Relation

This file defines Green's 𝓓 relation.

## Main Definitions

* `rel_comp` - composition of binary relations (notated ∘ᴿ)
* `R_L_comm` - commutativity of Green's R and L relations under composition
* `D_eqv` - Green's 𝓓 relation
-/

/-! ### Green's 𝓓-relation and relation composition

This section introduces relation composition and uses it to define Green's 𝓓-relation.
We establish the commutativity of Green's 𝓡 and 𝓛 relations under composition, which
allows an alternate characterization of the 𝓓-relation.
-/

section DRelation

variable {S} [Semigroup S] {a b: S}

/-! Relation composition and Green's D-relation -/

/-- Composition of binary relations -/
def rel_comp {α : Type*} (r s : α → α → Prop) : α → α → Prop :=
  λ a c => ∃ b, r a b ∧ s b c

notation:50 f " ∘ᴿ " g:50 => rel_comp f g

/-- Green's D-relation, defined as the composition of R and L relations -/
def D_eqv : S → S → Prop := R_eqv ∘ᴿ L_eqv
infix:50 " 𝓓 " => D_eqv

def D_class_set (x : S) : Set S := {a: S | a 𝓓 x}

/-- Straight Definitional lemma of Green's `𝓓` equivalence -/
lemma D_eqv_iff : a 𝓓 b ↔ ∃ x, a 𝓡 x ∧ x 𝓛 b := by simp [D_eqv, rel_comp]

/-- **Green's Commutativity**: R and L relations commute under composition -/
theorem R_L_comm: (L_eqv ∘ᴿ R_eqv) a b ↔ (R_eqv ∘ᴿ L_eqv) a b := by
  unfold rel_comp
  constructor
  · rintro ⟨c, hl, hr⟩
    rcases _ : hl with ⟨hl1, hl2⟩; rcases _ : hr with ⟨hr1, hr2⟩
    rw [L_preorder_iff_without_one] at hl1;
    cases hl1 with
    | inl heq => subst heq; use b; constructor; assumption; apply eqv_of_preorder_refl
    | inr hneq =>
      obtain ⟨u, hu⟩ := hneq; subst hu; use u* b
      rw [R_preorder_iff_without_one] at hr2
      cases hr2 with
      | inl heq => subst heq; constructor; apply eqv_of_preorder_refl; assumption
      | inr hneq =>
        obtain ⟨v, hv⟩ := hneq; subst hv
        constructor
        · apply R_eqv_lmult_compat; assumption
        · rw [← mul_assoc]; apply L_eqv_rmult_compat; assumption
  · rintro ⟨c, hl, hr⟩
    rcases _ : hl with ⟨hl1, hl2⟩; rcases _ : hr with ⟨hr1, hr2⟩
    rw [R_preorder_iff_without_one] at hl1;
    cases hl1 with
    | inl heq => subst heq; use b; constructor; assumption; apply eqv_of_preorder_refl
    | inr hneq =>
      obtain ⟨v, hv⟩ := hneq; subst hv; use b*v
      rw [L_preorder_iff_without_one] at hr2
      cases hr2 with
      | inl heq => subst heq; constructor; apply eqv_of_preorder_refl; assumption
      | inr hneq =>
        obtain ⟨u, hu⟩ := hneq; subst hu
        constructor
        · apply L_eqv_rmult_compat; assumption
        · rw [ mul_assoc]; apply R_eqv_lmult_compat; assumption

/-- Alternate Def of Green's `𝓓` equivalence -/
theorem D_eqv_iff_comm : a 𝓓 b ↔ ∃ x, a 𝓛 x ∧ x 𝓡 b := by
  unfold D_eqv; rw [← R_L_comm]; simp [rel_comp]

@[simp] lemma D_eqv_refl (a : S) : a 𝓓 a := by
  simp [D_eqv_iff]; use a; constructor <;> apply eqv_of_preorder_refl

lemma D_eqv_symm : a 𝓓 b → b 𝓓 a := by
  rw [D_eqv_iff, D_eqv_iff_comm]
  · rintro ⟨x, ⟨hx1, hx2⟩⟩; use x; constructor
    · exact hx2.symm
    · exact hx1.symm

/-- The 𝓓-relation is preserved by 𝓛-equivalent elements on the right.
If `a 𝓓 b` and `b 𝓛 c`, then `a 𝓓 c`. -/
lemma D_eqv_closed_under_L {a b c : S} : a 𝓓 b → b 𝓛 c → a 𝓓 c := by
  simp [D_eqv_iff]; intros x h1 h2 h3; use x; constructor
  · exact h1
  · exact (eqv_of_preorder_trans L_preorder h2 h3)

/-- The 𝓓-relation is preserved by 𝓡-equivalent elements on the right.
If `a 𝓓 b` and `b 𝓡 c`, then `a 𝓓 c`. -/
lemma D_eqv_closed_under_R {a b c : S} : a 𝓓 b → b 𝓡 c → a 𝓓 c := by
  simp [D_eqv_iff_comm]; intros x h1 h2 h3; use x; constructor
  · exact h1
  · exact (eqv_of_preorder_trans R_preorder h2 h3)

/-- The 𝓓-relation is transitive. This is proved using closure under 𝓡 and 𝓛. -/
lemma D_eqv_trans {a b c : S} : a 𝓓 b → b 𝓓 c → a 𝓓 c := by
  intros h1 h2
  obtain ⟨y, ⟨hy1, hy2⟩⟩ := h2
  have hd1 : a 𝓓 y := by apply D_eqv_closed_under_R; exact h1; assumption
  apply D_eqv_closed_under_L hd1 hy2

/-- The 𝓓-relation is an equivalence relation on `S`. This instance combines the
reflexivity, symmetry and transitivity proofs. -/
instance D_eqv_inst : Equivalence (fun a b : S => a 𝓓 b) where
  refl := D_eqv_refl
  symm := D_eqv_symm
  trans := D_eqv_trans

end DRelation
