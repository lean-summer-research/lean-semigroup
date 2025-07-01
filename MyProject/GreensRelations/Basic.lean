import MyProject.GreensRelations.Defs

/-!
# Basic Properties of Green's Relations

This file establishes fundamental properties of Green's relations in semigroups, particularly
in finite semigroups.

## Main Definitions

* Simp Lemmas for Greens Relations
* `R_eqv_lmult_compat` and `L_eqv_rmult_compat`
* Cancelation properties for 𝓛 and 𝓡
* `R_preorder_implies_J` and `R_eqv_implies_J` and duals
* `le_R_idempotent` and `le_L_idempotent` and `le_H_idempotent`
    - characterizations of elements below idempotents

## Implementation Notes

This file is for defining the basic properties of Green's relations that are necessary
for defining the 𝓓 relation. D_Rel.lean imports this file.
-/

/-! ### Simp Lemmas
This section provides lemmas tagged with @[simp]. For lemmas that take hypothesis
like `h : a ≤𝓡 a * b`, make sure that you call `simp [h]` to use them. -/

section Simp_Lemmas

variable {S} [Semigroup S] (a x y : S)

/-- `a * x` is always `≤𝓡 a` -/
@[simp] lemma mul_right_R_preorder_self : a * x ≤𝓡 a := by
  use x; rw [WithOne.coe_mul]

/-- `x * a` is always `≤𝓛 a` -/
@[simp] lemma mul_left_L_preorder_self : x * a ≤𝓛 a := by
  use x; rw [WithOne.coe_mul]

/-- `x * a * y` is always `≤𝓙 a` -/
@[simp] lemma mul_sandwich_J_preorder_self : x * a * y ≤𝓙 a := by
  use x, y; simp

variable {a x y : S}

/-- `a ≤𝓡 a * x` implies `a 𝓡 a * x` -/
@[simp] lemma R_eqv_of_R_preorder_mul_right (h : a ≤𝓡 a * x) : a 𝓡 a * x := by
  simpa [R_eqv_iff]

/-- `a ≤𝓛 x * a` implies `a 𝓛 b * a` -/
@[simp] lemma L_eqv_of_L_preorder_mul_left (h : a ≤𝓛 x * a) : a 𝓛 x * a := by
  simpa [L_eqv_iff]

/-- `a ≤𝓙 x * a * y` implies `a 𝓙 x * a * y` -/
@[simp] lemma J_eqv_of_J_preorder_mul_sandwich (h : a ≤𝓙 x * a * y) : a 𝓙 x * a * y := by
  simpa [J_eqv_iff]

end Simp_Lemmas

/-! ### Basic Lemmas for 𝓡 and 𝓛 and 𝓙 equivalences (Prop 1.4.3) -/

section RL_Lemmas

variable {S} [Semigroup S] {a b x y : S}

/-! Compatibility of Green's relations with multiplication -/

theorem R_preorder_lmult_compat (h : a ≤𝓡 b) (c) : c * a ≤𝓡 c * b := by
  obtain ⟨x, hx⟩ := h; use x
  simp [mul_assoc, hx]

theorem R_eqv_lmult_compat (h : a 𝓡 b) (c) : c * a 𝓡 c * b := by
  simp_all [R_eqv_iff]
  cases h; constructor <;> (apply R_preorder_lmult_compat; assumption)

theorem L_preorder_rmult_compat (h : a ≤𝓛 b) (c) : a * c ≤𝓛 b * c := by
  obtain ⟨x, hx⟩ := h; use x
  simp [← mul_assoc, hx]

theorem L_eqv_rmult_compat (h : a 𝓛 b) (c) : a * c 𝓛 b * c := by
  simp_all [L_eqv_iff]
  cases h; constructor <;> (apply L_preorder_rmult_compat; assumption)

/-! calcelation lemmas -/

/-- If `a 𝓡 a * x * y`, then `a 𝓡 a * x`. -/
lemma R_eqv_right_cancel (h : a 𝓡 a * x * y) : a 𝓡 a * x := by
  simp_all [R_eqv_iff]
  obtain ⟨⟨u, hu⟩, _⟩ := h
  use y * u; simp_rw [WithOne.coe_mul, ← mul_assoc] at *
  exact hu

/-- If `a 𝓡 a * x * y`, then `a * x 𝓡 a * x * y`.-/
lemma R_eqv_right_extend (h : a 𝓡 a * x * y) : a * x 𝓡 a * x * y := by
  simp_all [R_eqv_iff]
  obtain ⟨⟨u, hu⟩, _⟩ := h
  use u * x; simp_rw [WithOne.coe_mul, ← mul_assoc] at *
  rw [← hu]

/-- If `a 𝓛 y * x * a`, then `a 𝓛 x * a`. -/
theorem L_eqv_left_cancel (h: a 𝓛 y * x * a ) : a 𝓛 x * a := by
  simp_all [L_eqv_iff]
  obtain ⟨u, hu⟩ := h
  use u * y; simp_rw [WithOne.coe_mul, ← mul_assoc] at *
  exact hu

/-- If `a 𝓛 y * x * a`, then `x * a 𝓛 y * x * a`. -/
theorem L_eqv_left_extend (h : a 𝓛 y * x * a) : x * a 𝓛 y * x * a := by
  simp_all [L_eqv_iff]
  constructor
  · obtain ⟨u, hu⟩ := h
    use x * u; simp_rw [WithOne.coe_mul, mul_assoc] at *
    rw [← hu]
  · simp [mul_assoc]


theorem R_preorder_implies_J (h : a ≤𝓡 b) : a ≤𝓙 b := by
  simp_all [J_preorder_iff, R_preorder_iff]
  obtain ⟨x, hx⟩ := h
  use 1, x; simp_all

theorem L_preorder_implies_J (h : a ≤𝓛 b) : a ≤𝓙 b := by
  simp_all [J_preorder_iff, L_preorder_iff]
  obtain ⟨x, hx⟩ := h
  use x, 1; simp_all

theorem R_eqv_implies_J (h : a 𝓡 b) : a 𝓙 b := by
  simp_all [J_eqv_iff, R_eqv_iff, R_preorder_implies_J]

theorem L_eqv_implies_J (h : a 𝓛 b) : a 𝓙 b := by
  simp_all [J_eqv_iff, L_eqv_iff, L_preorder_implies_J]

end RL_Lemmas


/-! ### Idempotent properties (Prop 1.4.1)
This section characterizes elements that are 𝓡- below or 𝓛- below an idempotent. -/

section Idempotent_Props

variable {S} [Semigroup S] {e f: S}

/-- An element `a` is 𝓡-below an idempotent `e` if and only if `a = e * a`. -/
theorem le_R_idempotent (a : S) (h: IsIdempotentElem e) : (a ≤𝓡 e) ↔ (a = e * a) := by
  constructor
  · rintro ⟨u, hru⟩
    unfold IsIdempotentElem at h
    rw [← WithOne.coe_inj, WithOne.coe_mul] at h ⊢
    rw [hru, ← mul_assoc, h ]
  · intro hl; use a
    rw[<-WithOne.coe_inj] at hl; exact hl

/-- An element `a` is 𝓛-below an idempotent `e` if and only if `a = a * e`. -/
theorem le_L_idempotent (a : S) (h: IsIdempotentElem e) : (a ≤𝓛 e) ↔ (a = a * e) := by
  constructor
  · rintro ⟨u, hru⟩
    unfold IsIdempotentElem at h
    rw [← WithOne.coe_inj, WithOne.coe_mul] at h ⊢
    rw [hru, mul_assoc, h ]
  · intro hl; use a
    rw[<-WithOne.coe_inj] at hl; exact hl

theorem le_H_idempotent (a : S) (h : IsIdempotentElem e) : (a ≤𝓗 e) ↔ (a = e * a ∧ a = a * e) := by
  simp [H_preorder_iff, le_R_idempotent a h, le_L_idempotent a h]

theorem le_H_idempotent' (a : S) (he : IsIdempotentElem e) : a ≤𝓗 e ↔ e * a * e = a := by
  rw [le_H_idempotent a he]
  constructor
  · rintro ⟨h₁, h₂⟩; rw [← h₁, ← h₂]
  · intro h; constructor
    · nth_rw 2 [← h]
      simp_rw [← mul_assoc]; rw [he, h]
    · nth_rw 2 [← h]
      rw [mul_assoc, he, h ]

end Idempotent_Props
