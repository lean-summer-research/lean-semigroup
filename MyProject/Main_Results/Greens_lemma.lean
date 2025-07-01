import MyProject.Main_Results.DJ_Theorem

/-! # Greens Lemma

This file proves Green's lemma, which is the following:
Let `a 𝓡 b` such that `a = b * u` and `b = a * v`,
then the map `x ↦ x * v` is a bijection from the 𝓛-classes of `a` to the 𝓛-class of `b`
and the map `x ↦ x * u` is its inverse bijection. Additionally, these bijections preserve 𝓗 classes.

We also prove the dual, left translation version of this lemma

## Main Definitions

Let `a 𝓡 b` such that `a = b * u` and `b = a * v`

* `right_translations_inverse` - the right translation by `u` is the inverse of the right
translation by `v` for all elements `x` in the 𝓛 class of `a`.

* `right_translation_bijection` - the right translation by `u` from the 𝓛-class of `a` to
the 𝓛-class of `b` is a bijection.

* `right_translation_preserves_H` - This bijection preserves 𝓗 classes

We also prove the dual, left translation version of these.
-/


section Greens_Lemma

open MulOpposite

variable {S} [Semigroup S] {a b u v x y : S}

/-- If `a 𝓡 b` such that `a = b * u` and `b = a * v`, then right translation by `v * u`
on any element `x` L-equivalent to `a` is the identity. -/
lemma right_translation_id (ha : a = b * u) (hb : b = a * v) (hx : x 𝓛 a) : x * v * u = x := by
  rw [L_eqv_iff, L_preorder_iff_without_one] at hx
  rcases hx with ⟨(heq | ⟨x, hx⟩), _⟩
  · subst heq; rw [← hb, ← ha]
  · subst hx; rw [mul_assoc x, ← hb, mul_assoc, ← ha]

-- Dual version
lemma left_translation_id (ha : a = u * b) (hb : b = v * a) (hx : x 𝓡 a) : u * v * x = x := by
  rw [eq_mul_iff_op, R_eqv_iff_op, mul_mul_eq_iff_op] at *
  apply right_translation_id ha hb hx

-- TODO: is the below lemma ever used?

/-- If `a 𝓡 b` such that `a = b * u` and `b = a * v`,
then `ρᵣ u` inverts `ρᵣ v` on the 𝓛 class of `a` -/
theorem right_translations_inverse (ha : a = b * u) (hb : b = a * v) :
    Set.InvOn (ρᵣ u) (ρᵣ v) (L_class_set a) (L_class_set b) := by
  simp [Set.InvOn, Set.LeftInvOn, L_class_set, R_translation]
  constructor
  /- Becuase `x 𝓛 a`, we have a `y` such that `x = y * a`,
   thus `x * v * u = y * a * v * u = y * a = x` -/
  · intros x hL
    apply right_translation_id ha hb hL
  · intros x hL
    apply right_translation_id hb ha hL

-- Dual Version
theorem left_translations_inverse (ha : a = u * b) (hb : b = v * a) :
    Set.InvOn (ρₗ u) (ρₗ v) (R_class_set a) (R_class_set b) := by
  simp [Set.InvOn, Set.LeftInvOn, R_class_set, L_translation]
  constructor
  · intros x hR; rw [← mul_assoc]
    apply left_translation_id ha hb hR
  · intros x hR; rw [← mul_assoc]
    apply left_translation_id hb ha hR

/-- If `a 𝓡 b` such that `a = b * u`, then `ρᵣ u` is a bijection
from the 𝓛 class of `b` to the 𝓛 class of `a` -/
theorem right_translation_bijection (ha: a = b * u) (hb : b = a * v):
    Set.BijOn (ρᵣ v) (L_class_set a) (L_class_set b) := by
  refine Set.BijOn.mk ?_ ?_ ?_
  · intros x hx
    simp [L_class_set, R_translation] at *
    subst b
    apply L_eqv_rmult_compat; exact hx
  · intro x hx y hy hxy
    simp [L_class_set, R_translation] at *
    have hinvx := right_translation_id ha hb hx
    have hinvy := right_translation_id ha hb hy
    rw [← hinvx, ← hinvy, hxy]
  · intros y hy
    simp [R_translation, L_class_set] at *
    use y * u
    constructor
    · rw [ha]
      apply L_eqv_rmult_compat; exact hy
    · apply right_translation_id hb ha hy

-- Dual version
theorem left_translation_bijection (ha : a = u * b) (hb : b = v * a) :
    Set.BijOn (ρₗ v) (R_class_set a) (R_class_set b) := by
  refine Set.BijOn.mk ?_ ?_ ?_
  · intros x hx
    simp [R_class_set, L_translation] at *
    subst b
    apply R_eqv_lmult_compat; exact hx
  · intro x hx y hy hxy
    simp [R_class_set, L_translation] at *
    have hinvx := left_translation_id ha hb hx
    have hinvy := left_translation_id ha hb hy
    rw [← hinvx, ← hinvy, mul_assoc, hxy, ← mul_assoc]
  · intros y hy
    simp [L_translation, R_class_set] at *
    use u * y
    constructor
    · rw [ha]
      apply R_eqv_lmult_compat; exact hy
    · rw [← mul_assoc]; apply left_translation_id hb ha hy

/-- If `a 𝓡 b` such that `b = a * v`, then the bijection `ρᵣ v` preserves 𝓗 classes -/
theorem right_translation_preserves_H (ha: a = b * u) (hb: b = a * v)
  (hx : x ∈ L_class_set a) (hy : y ∈ L_class_set a) :
    (x 𝓗 y) ↔ (x * v) 𝓗 (y * v) := by
  simp [L_class_set, R_translation, H_eqv_iff_L_and_R] at *
  have hidx : x * v * u = x := right_translation_id ha hb hx
  have hidy : y * v * u = y := right_translation_id ha hb hy
  have hxux : x * v 𝓡 x := by
    simp [R_eqv, R_preorder_iff_without_one]
    right; use u; exact hidx.symm
  have hyuy : y 𝓡 y * v := by
    simp [R_eqv, R_preorder_iff_without_one]
    right; use u; exact hidy.symm
  clear ha hb
  constructor
  · rintro ⟨hr, hl⟩
    constructor
    · apply R_eqv_trans hxux
      apply R_eqv_trans hr
      exact hyuy
    · apply L_eqv_rmult_compat; exact hl
  · rintro ⟨hr, hl⟩
    constructor
    · apply R_eqv_trans hxux.symm
      apply R_eqv_trans hr
      exact hyuy.symm
    · apply L_eqv_trans hx hy.symm

-- Dual version
theorem left_translation_preserves_H (ha : a = u * b) (hb : b = v * a)
  (hx : x ∈ R_class_set a) (hy : y ∈ R_class_set a) :
    (x 𝓗 y) ↔ (v * x) 𝓗 (v * y) := by
  rw [eq_mul_iff_op, R_class_iff_op, H_eqv_iff_op, H_eqv_iff_op (v * x), op_mul, op_mul] at *
  apply right_translation_preserves_H ha hb hx hy


end Greens_Lemma
