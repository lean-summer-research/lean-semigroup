import MyProject.GreensRelations.Defs

variable {S} [Semigroup S] (a b e : S)
open MulOpposite
/- (the bult-in notation for MulOpposite S is Sᵐᵒᵖ)-/


/- # Definitions and Instances related to S¹-compatibility with MulOpposite-/

instance MulOpposite.Monoid : Monoid (MulOpposite (S¹)) :=
  by infer_instance

def WithOneMulOppositeEquiv (S : Type*) :
    (Sᵐᵒᵖ)¹ ≃ (S¹)ᵐᵒᵖ :=
  {toFun := λ x =>
    match x with
      | none => op none
      | some a => op (some a.unop),
   invFun := λ x => match unop x with
    | none => none
    | some a => some (op a),
   left_inv := by
      intro x
      cases x
      simp[op, unop]; rfl
      dsimp; rfl
   right_inv := by
      intro x
      refine unop_inj.mp ?_
      simp only [Function.comp_apply]
      simp only [unop, op]
      cases x.unop' with
      | one => simp; rfl
      | coe => rfl
  }

/- # Lemmas establishing basic facts about relationship between Green's relations on S and Sᵐᵒᵖ
(From playing around with examples/trying to use Sᵐᵒᵖ in proofs, to make using this method
efficient, we'd need to write a pretty larger number of such lemmas for basic facts about
finite semigroups.)-/

lemma L_preorder_iff_R_preorder_op (a b : S) :
    a ≤𝓛 b ↔ (op a) ≤𝓡 (op b) := by
  rw[R_preorder_iff_without_one, L_preorder_iff_without_one]
  constructor
  · intro hu
    cases' hu with hp hq
    · exact Or.symm (Or.inr (congr_arg op (hp)))
    . obtain ⟨x, hx⟩ := hq
      refine Or.symm (Or.intro_left (op a = op b) ?_)
      use op x
      exact congr_arg op hx
  · intro hv
    cases' hv with hp hq
    · exact Or.symm (Or.inr (congr_arg unop (hp)))
    · obtain ⟨x, hx⟩ := hq
      refine Or.symm (Or.intro_left (a = b) ?_)
      use unop x
      exact congr_arg unop hx

lemma L_preorder_op_iff_R_preorder (a b : S) :
    (op a) ≤𝓛 (op b) ↔ (a) ≤𝓡 (b) := by
  rw[R_preorder_iff_without_one, L_preorder_iff_without_one]
  constructor
  · intro hu
    cases' hu with hp hq
    · exact Or.symm (Or.inr (congr_arg unop (hp)))
    . obtain ⟨x, hx⟩ := hq
      refine Or.symm (Or.intro_left (a = b) ?_)
      use unop x
      exact congr_arg unop hx
  · intro hv
    cases' hv with hp hq
    · exact Or.symm (Or.inr (congr_arg op (hp)))
    · obtain ⟨x, hx⟩ := hq
      refine Or.symm (Or.intro_left (op a = op b) ?_)
      use op x
      exact congr_arg op hx

lemma L_eqv_iff_R_eqv_op (a b : S) :
    a 𝓛 b ↔ op a 𝓡 op b := by
  unfold L_eqv R_eqv
  simp[L_preorder_iff_R_preorder_op a b, L_preorder_iff_R_preorder_op b a]

lemma L_eqv_op_iff_R_eqv (a b : S) :
    (op a) 𝓛 (op b) ↔ a 𝓡 b := by
  unfold L_eqv R_eqv
  simp[L_preorder_op_iff_R_preorder a b, L_preorder_op_iff_R_preorder b a]

lemma Class_op_RL (x : S): x ∈ R_class_set a  ↔ op x ∈ L_class_set (op a) := by
  unfold R_class_set L_class_set
  simp only [Set.mem_setOf_eq]
  apply Iff.intro
  · intro h
    simp[L_eqv_op_iff_R_eqv]; exact h
  · intro h
    simp[<-L_eqv_op_iff_R_eqv]; exact h

lemma Class_op_LR (x : S): op x ∈ R_class_set (op a)  ↔ x ∈ L_class_set a := by
  unfold R_class_set L_class_set
  simp only [Set.mem_setOf_eq]
  apply Iff.intro
  · intro h
    simp[L_eqv_iff_R_eqv_op]; exact h
  · intro h
    simp[<-L_eqv_iff_R_eqv_op]; exact h

lemma H_eqv_op_iff (x y : S) : (x 𝓗 y) ↔ (op x 𝓗 op y) := by
  rw [H_eqv_iff_L_and_R, H_eqv_iff_L_and_R]
  constructor
  · rintro ⟨hL, hR⟩
    exact ⟨by simp[L_eqv_iff_R_eqv_op] at hR; exact hR,
           by simp[<-L_eqv_op_iff_R_eqv] at hL; exact hL⟩
  · rintro ⟨hL, hR⟩
    exact ⟨by simp[<-L_eqv_op_iff_R_eqv]; exact hR,
           by simp[L_eqv_iff_R_eqv_op]; exact hL⟩


/--# Example of use

Using `le_R_idempotent`-- proved in Basic as follows-- we provide an alternate proof of
`le_L_idempotent`, where we switch to the opposite semigroup Sᵐᵒᵖ and apply `le_R_idempotent`.

I believe most of the work in using this method is always in establishing that the natural analogs
of the hypotheses of the original theorem hold in the opposite semigroup (ex. for `le_L_idempotent`,
showing `h_op`). For more complicated statements, especially when dealing with coercions between S
and S¹ as well as from S to Sᵐᵒᵖ, this was not always easy (for me, at least)-- I tried doing so
for some of the Green's lemma proofs with limited success. --/

/- this is the original `le_R_idempotent`:-/
theorem le_R_idempotent_rehash (h: IsIdempotentElem e) : (a ≤𝓡 e) ↔ (a = e * a) := by
  constructor
  · rintro ⟨u, hru⟩
    unfold IsIdempotentElem at h
    rw [<-WithOne.coe_inj, WithOne.coe_mul] at h ⊢
    rw [hru, ← mul_assoc, h ]
  · intro hl; use a
    rw[<-WithOne.coe_inj] at hl; exact hl

/- an alternate proof of `le_L_idempotent` using `le_R_idempotent` in the opposite semigroup.-/
lemma le_L_idempotent_alt (h : IsIdempotentElem e) : a ≤𝓛 e ↔ a = a * e := by
  have h_op : IsIdempotentElem (op e) := by
    unfold IsIdempotentElem at *
    rw [← op_inj, op_mul] at h; exact h
  have : op a ≤𝓡 op e ↔ op a = op e * op a := le_R_idempotent_rehash (op a) (op e) h_op
  simp[L_preorder_iff_R_preorder_op, this]
  exact ⟨congrArg unop, congrArg op⟩
