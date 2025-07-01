import MyProject.GreensRelations.morphisms

/-!
# Opposite

This file defines properties of Green's relations in the opposite semigroup `Sᵐᵒᵖ`.
The purpose of this is to provide a method for proving dual statments about the 𝓡 and 𝓛 relations.

## Main Definitions

* `WithONeMulOppositeEquiv` - `(Sᵐᵒᵖ)¹` is isomorphic to `(S¹)ᵐᵒᵖ`
   - As well as other instances
* `L_eqv_iff_R_eqv_op` - equivalence between the 𝓛 and 𝓡 relations in `S` and `Sᵐᵒᵖ`
   - and many similar lemmas for the other relations and preorders
* `le_L_idempotent_alt` - an example proof of `le_L_idempotent` using duality in `Sᵐᵒᵖ`

## Notation

* the bult-in notation for `MulOpposite S` is `Sᵐᵒᵖ`
-/

/-! ### Definitions and Instances related to S¹-compatibility with MulOpposite-/

section Instances

variable {S} [Semigroup S]

open MulOpposite

instance MulOpposite_Monoid : Monoid (MulOpposite (S¹)) := by infer_instance

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

instance MulOpposite_Finite [hF : Finite S] : Finite (Sᵐᵒᵖ) := Finite.of_equiv S opEquiv

end Instances

/-! ### Lemmas establishing basic facts about relationship between Green's relations on S and Sᵐᵒᵖ
(From playing around with examples/trying to use Sᵐᵒᵖ in proofs, to make using this method:w
efficient, we'd need to write a pretty larger number of such lemmas for basic facts about
finite semigroups.)-/

section Propositions

open MulOpposite

variable {S} [Semigroup S] (a b c d : S)

/-! Multiplication Duality -/

theorem mul_eq_iff_op : a * b = c ↔ op b * op a = op c := by
  simp [← op_mul]

theorem eq_mul_iff_op : a = b * c ↔ op a = op c * op b := by
  simp [← op_mul]

theorem mul_mul_eq_iff_op : a * b * c = d ↔ op c * op b * op a = op d := by
  simp [← op_mul, ← mul_assoc]

theorem eq_mul_mul_iff_op : a = b * c * d ↔ op a = op d * op c * op b := by
  simp [← op_mul, ← mul_assoc]

/-! Preorder Duality -/

theorem L_preorder_iff_op : a ≤𝓛 b ↔ (op a) ≤𝓡 (op b) := by
  rw[R_preorder_iff_without_one, L_preorder_iff_without_one]
  constructor
  · rintro (heq | ⟨x, hx⟩)
    · left; simpa [op_inj]
    · right; use op x; simpa [← op_mul, op_inj]
  · rintro (heq | ⟨x, hx⟩)
    · left; rwa [← op_inj]
    · right; use unop x; rw [← op_inj]; simpa

theorem R_preorder_iff_op : a ≤𝓡 b ↔ (op a) ≤𝓛 (op b) := by
  rw[L_preorder_iff_without_one, R_preorder_iff_without_one]
  constructor
  · rintro (heq | ⟨x, hx⟩)
    · left; simpa [op_inj]
    · right; use op x; simpa [← op_mul, op_inj]
  · rintro (heq | ⟨x, hx⟩)
    · left; rwa [← op_inj]
    · right; use unop x; rw [← op_inj]; simpa

theorem J_preorder_iff_op : a ≤𝓙 b ↔ (op a) ≤𝓙 (op b) := by
  simp [J_preorder_iff_without_one]
  constructor
  · rintro (heq | hL | hR | ⟨x, y, hxy⟩)
    · subst a; left; rfl
    · right; right; left; rwa [← L_preorder_iff_op a b]
    · right; left; rwa [← R_preorder_iff_op a b]
    · right; right; right; use y, x
      simp_rw [← op_mul, op_inj, ← mul_assoc]
      exact hxy
  · rintro (heq | hL | hR | ⟨x, y, hxy⟩)
    · subst a; left; rfl
    · right; right; left; rwa [R_preorder_iff_op]
    · right; left; rwa [L_preorder_iff_op]
    · right; right; right; use y, x
      simp_rw [← op_mul, op_inj, ← mul_assoc] at hxy
      exact hxy

theorem H_preorder_iff_op : a ≤𝓗 b ↔ (op a) ≤𝓗 (op b) := by
  simp [H_preorder_iff]
  rw [R_preorder_iff_op]
  nth_rw 2 [L_preorder_iff_op]
  simp [and_comm]

/-! Equivalence Duality -/

theorem L_eqv_iff_op : a 𝓛 b ↔ op a 𝓡 op b := by
  simp[L_eqv_iff, R_eqv_iff, L_preorder_iff_op a b, L_preorder_iff_op b a]

theorem R_eqv_iff_op : a 𝓡 b ↔ op a 𝓛 op b := by
  simp [L_eqv_iff, R_eqv_iff, R_preorder_iff_op a b, R_preorder_iff_op b a]

theorem J_eqv_iff_op : a 𝓙 b ↔ op a 𝓙 op b := by
  simp [J_eqv_iff, J_preorder_iff_op a b, J_preorder_iff_op b a]

theorem H_eqv_iff_op : a 𝓗 b ↔ op a 𝓗 op b := by
  simp [H_eqv_iff, H_preorder_iff_op a b, H_preorder_iff_op b a]

theorem D_eqv_iff_op : a 𝓓 b ↔ op a 𝓓 op b := by
  rw [D_eqv_iff, D_eqv_iff_comm]
  simp [R_eqv_iff_op a, L_eqv_iff_op _ b]

/-! Equivalence Classes Duality -/

theorem R_class_iff_op : b ∈ R_class_set a  ↔ op b ∈ L_class_set (op a) := by
  simp [L_class_set, R_class_set, R_eqv_iff_op]

theorem L_class_iff_op : b ∈ L_class_set a ↔ op b ∈ R_class_set (op a) := by
  simp [L_class_set, R_class_set, L_eqv_iff_op]

theorem J_class_iff_op : b ∈ J_class_set a ↔ op b ∈ J_class_set (op a) := by
  simp_rw [J_class_set]; simp; rw [J_eqv_iff_op]

theorem H_class_iff_op : b ∈ H_class_set a ↔ op b ∈ H_class_set (op a) := by
  simp_rw [H_class_set]; simp; rw [H_eqv_iff_op]

theorem D_class_iff_op : b ∈ D_class_set a ↔ op b ∈ D_class_set (op a) := by
  simp_rw [D_class_set]; simp; rw [D_eqv_iff_op]

/-! Idempotent duality -/

theorem idempotent_iff_op : IsIdempotentElem a ↔ IsIdempotentElem (op a) := by
  unfold IsIdempotentElem; rw [mul_eq_iff_op]

end Propositions

/-! ### Example of use

Using `le_R_idempotent`-- proved in Basic as follows-- we provide an alternate proof of
`le_L_idempotent`, where we switch to the opposite semigroup Sᵐᵒᵖ and apply `le_R_idempotent`.

I believe most of the work in using this method is always in establishing that the natural analogs
of the hypotheses of the original theorem hold in the opposite semigroup (ex. for `le_L_idempotent`,
showing `h_op`). For more complicated statements, especially when dealing with coercions between S
and S¹ as well as from S to Sᵐᵒᵖ, this was not always easy (for me, at least)-- I tried doing so
for some of the Green's lemma proofs with limited success. --/

section Examples

open MulOpposite

variable {S} [Semigroup S] {e : S}

/- this is the original `le_R_idempotent`:-/
theorem le_R_idempotent_rehash (a : S) (h: IsIdempotentElem e) : (a ≤𝓡 e) ↔ (a = e * a) := by
  constructor
  · rintro ⟨u, hru⟩
    unfold IsIdempotentElem at h
    rw [<-WithOne.coe_inj, WithOne.coe_mul] at h ⊢
    rw [hru, ← mul_assoc, h ]
  · intro hl; use a
    rw[<-WithOne.coe_inj] at hl; exact hl

/- an alternate proof of `le_L_idempotent` using `le_R_idempotent` in the opposite semigroup.-/
lemma le_L_idempotent_alt (a : S) (h : IsIdempotentElem e) : a ≤𝓛 e ↔ a = a * e := by
  rw [idempotent_iff_op] at h
  rw [L_preorder_iff_op, eq_mul_iff_op]
  apply le_R_idempotent_rehash (op a) h

end Examples
