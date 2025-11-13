import MyProject.PreReq.Idempotence

/-!
# Green's Relations Definitions

This file defines Green's relations 𝓡, 𝓛, 𝓙, and 𝓗 for semigroups.
It also Provides a set-based implementation of the equivalence classes for these relations.

## Main definitions

* Preorder Relations `≤𝓡`, `≤𝓛`, `≤𝓙`, `≤𝓗` with Reflexivity and transativity
* Equivalence Relations `𝓡`, `𝓛`, `𝓙`, `𝓗` with Refl Trans and Symm
* Alternate characterizations of preorders and equivalences `without_one` and a Monoid version
* Set-based equivalence classes and definitions for translations

## Notation

* Right translations `ρᵣ a`,
* Left translations `ρₗ a`
-/

/-! ### Equivalence relations from preorders

This section establishes a general framework for converting preorders into equivalence
relations by taking the symmetric closure. This construction will be applied to Green's
preorders to obtain the corresponding equivalence relations.
-/

section EquivalenceFromPreorder

variable {α} (p : α → α → Prop) [inst : IsPreorder α p]

@[simp] def eqv_of_preorder (a b : α) : Prop := p a b ∧ p b a

@[refl] lemma eqv_of_preorder_refl (a : α) : eqv_of_preorder p a a := by simp; apply inst.refl

set_option linter.unusedSectionVars false in
@[symm] lemma eqv_of_preorder_symm {a b : α} : eqv_of_preorder p a b → eqv_of_preorder p b a := by aesop

@[trans] lemma eqv_of_preorder_trans {a b c : α} :
    eqv_of_preorder p a b → eqv_of_preorder p b c → eqv_of_preorder p a c:= by
  simp; intros H₁ H₂ H₃ H₄
  constructor
  · exact (inst.trans a b c H₁ H₃)
  · exact (inst.trans c b a H₄ H₂)

-- Equivalence is the unbundled form of Setoid
instance eqv_of_preorder_inst : Equivalence (eqv_of_preorder p) where
  refl := eqv_of_preorder_refl p
  symm := eqv_of_preorder_symm p
  trans := eqv_of_preorder_trans p

end EquivalenceFromPreorder

/-! ### Core Green's relations definitions

This section defines the fundamental Green's preorders and equivalences. We start with the
basic preorder definitions using `WithOne` elements, establish their preorder properties,
and then derive the equivalence relations as symmetric closures.
-/

section CoreDefinitions

variable {S} [Semigroup S]

/-- the 𝓡 preorder: a ≤𝓡 b iff a*S¹ ⊆ b*S¹ -/
def R_preorder (a b : S) : Prop := ∃ x : S¹ , ↑a = ↑b * x
/-- the 𝓛 preorder: a ≤𝓛 b iff S¹*a ⊆ S¹*b -/
def L_preorder (a b : S) : Prop := ∃ x : S¹, ↑a = x * ↑b
/-- the 𝓙 preorder: a ≤𝓙 b iff S¹*a*S¹ ⊆ S¹*b*S¹ -/
def J_preorder (a b : S) : Prop := ∃ x y : S¹, a = x * b * y

/-! Preorder notation, typed \leq\MCR -/
notation:50 f " ≤𝓡 " g:50 => R_preorder f g
notation:50 f " ≤𝓛 " g:50 => L_preorder f g
notation:50 f " ≤𝓙 " g:50 => J_preorder f g

/-- the 𝓗 preorder -/
def H_preorder (a b : S) : Prop := a ≤𝓡 b ∧ a ≤𝓛 b

notation:50 f " ≤𝓗 " g:50 => H_preorder f g

/-! Definitional lemmas -/
theorem R_preorder_iff (a b : S) : a ≤𝓡 b ↔ ∃ x : S¹ , ↑a = ↑b * x := by simp [R_preorder]
theorem L_preorder_iff (a b : S) : a ≤𝓛 b ↔ ∃ x : S¹, ↑a = x * ↑b := by simp [L_preorder]
theorem J_preorder_iff (a b : S) : a ≤𝓙 b ↔ ∃ x y : S¹, a = x * b * y := by simp [J_preorder]
theorem H_preorder_iff (a b : S) : a ≤𝓗 b ↔ a ≤𝓡 b ∧ a ≤𝓛 b := by simp [H_preorder]

/-! Reflexivity lemmas -/
@[simp] lemma R_preorder_refl (x : S) : x ≤𝓡 x := by use 1; simp
@[simp] lemma L_preorder_refl (x : S) : x ≤𝓛 x := by use 1; simp
@[simp] lemma J_preorder_refl (x : S) : x ≤𝓙 x := by use 1, 1; simp
@[simp] lemma H_preorder_refl (x : S) : x ≤𝓗 x := by
  unfold H_preorder; apply And.intro <;> use 1; simp; rw [one_mul]

/-! Transitivity lemmas -/
lemma R_preorder_trans (a b c : S) : a ≤𝓡 b → b ≤𝓡 c → a ≤𝓡 c := by
  simp [R_preorder]; intros h₁ h₂ h₃ h₄
  use (h₃ * h₁)
  rw [← mul_assoc, ← h₄, h₂]
lemma L_preorder_trans (a b c : S) : a ≤𝓛 b → b ≤𝓛 c → a ≤𝓛 c := by
  unfold L_preorder; rintro ⟨x, hx⟩ ⟨y, hy⟩
  use x * y; rw [hx, hy, mul_assoc]
lemma J_preorder_trans (a b c : S) : a ≤𝓙 b → b ≤𝓙 c → a ≤𝓙 c := by
  unfold J_preorder; rintro ⟨x₁, y₁, hx⟩ ⟨x₂, y₂, hy⟩
  use x₁ * x₂, y₂ * y₁; rw [hx, hy]; simp [mul_assoc]
lemma H_preorder_trans (a b c : S) : a ≤𝓗 b → b ≤𝓗 c → a ≤𝓗 c := by
  unfold H_preorder; rintro ⟨h₁, h₂⟩ ⟨h₃, h₄⟩
  constructor
  · apply R_preorder_trans a b c <;> assumption
  · apply L_preorder_trans a b c <;> assumption

/-! Preorder instances -/
instance R_is_preorder : IsPreorder S R_preorder where
  refl := R_preorder_refl
  trans := R_preorder_trans
instance L_is_preorder : IsPreorder S L_preorder where
  refl := L_preorder_refl
  trans := L_preorder_trans
instance J_is_preorder : IsPreorder S J_preorder where
  refl := J_preorder_refl
  trans := J_preorder_trans
instance H_is_preorder : IsPreorder S H_preorder where
  refl := H_preorder_refl
  trans := H_preorder_trans

/-- The equivalence relation `𝓡` -/
def R_eqv : S → S → Prop := eqv_of_preorder R_preorder
/-- The equivalence relation `𝓛` -/
def L_eqv : S → S → Prop := eqv_of_preorder L_preorder
/-- The equivalence relation `𝓙` -/
def J_eqv : S → S → Prop := eqv_of_preorder J_preorder
/-- The equivalence relation `𝓗` -/
def H_eqv : S → S → Prop := eqv_of_preorder H_preorder

/-! Equivalence notation: typed \MCR -/
notation:50 a " 𝓡 " b:50 => R_eqv a b
notation:50 a " 𝓛 " b:50 => L_eqv a b
notation:50 a " 𝓙 " b:50 => J_eqv a b
notation:50 a " 𝓗 " b:50 => H_eqv a b

/-! Definitional lemmas for equivalence relations -/
lemma R_eqv_iff (a b : S) : a 𝓡 b ↔ a ≤𝓡 b ∧ b ≤𝓡 a := by unfold R_eqv; simp
lemma L_eqv_iff (a b : S) : a 𝓛 b ↔ a ≤𝓛 b ∧ b ≤𝓛 a := by unfold L_eqv; simp
lemma J_eqv_iff (a b : S) : a 𝓙 b ↔ a ≤𝓙 b ∧ b ≤𝓙 a := by unfold J_eqv; simp
lemma H_eqv_iff (a b : S) : a 𝓗 b ↔ a ≤𝓗 b ∧ b ≤𝓗 a := by unfold H_eqv; simp

variable {a b c : S}

/-! Reflexivity Lemmas -/
@[simp] lemma R_eqv_refl : a 𝓡 a := by constructor <;> simp
@[simp] lemma L_eqv_refl : a 𝓛 a := by constructor <;> simp
@[simp] lemma J_eqv_refl : a 𝓙 a := by constructor <;> simp
@[simp] lemma H_eqv_refl : a 𝓗 a := by constructor <;> simp

/-! Symmetry Lemmas -/
@[symm]
lemma R_eqv_symm : a 𝓡 b ↔ b 𝓡 a := by
  constructor <;> (intros h; apply eqv_of_preorder_symm; simp_all [R_eqv_iff])
lemma L_eqv_symm : a 𝓛 b ↔ b 𝓛 a := by
  constructor <;> (intros h; apply eqv_of_preorder_symm; simp_all [L_eqv_iff])
lemma J_eqv_symm : a 𝓙 b ↔ b 𝓙 a := by
  constructor <;> (intros h; apply eqv_of_preorder_symm; simp_all [J_eqv_iff])
lemma H_eqv_symm : a 𝓗 b ↔ b 𝓗 a := by
  constructor <;> (intros h; apply eqv_of_preorder_symm; simp_all [H_eqv_iff])

/-! Transitivity Lemmas-/
lemma R_eqv_trans (hab : a 𝓡 b) (hbc : b 𝓡 c) : a 𝓡 c := by
  apply @eqv_of_preorder_trans S R_preorder _ a b c <;> assumption
lemma L_eqv_trans (hab : a 𝓛 b) (hbc : b 𝓛 c) : a 𝓛 c := by
  apply @eqv_of_preorder_trans S L_preorder _ a b c <;> assumption
lemma J_eqv_trans (hab : a 𝓙 b) (hbc : b 𝓙 c) : a 𝓙 c := by
  apply @eqv_of_preorder_trans S J_preorder _ a b c <;> assumption
lemma H_eqv_trans (hab : a 𝓗 b) (hbc : b 𝓗 c) : a 𝓗 c := by
  apply @eqv_of_preorder_trans S H_preorder _ a b c <;> assumption
end CoreDefinitions

/-! ### Alternative characterizations of 𝓗 -/

section AlternativeH

variable {S} [Semigroup S] (a b : S)

/-- The 𝓗 equivalence relation is the intersection of 𝓡 and 𝓛 equivalences. -/
theorem H_eqv_iff_L_and_R : a 𝓗 b ↔ a 𝓡 b ∧ a 𝓛 b := by
  simp [H_eqv, H_preorder_iff]
  rw [@and_comm _ (b ≤𝓛 a), and_assoc, ← @and_assoc _ _ (b ≤𝓡 a)]
  rw [ ← L_eqv_iff, and_comm, and_assoc, @and_comm (b ≤𝓡 a) _, ←  R_eqv_iff, and_comm]

end AlternativeH

/-! ### WithOne-free characterizations of Preorders

This section provides alternative characterizations of Green's preorders that avoid
explicit reference to `WithOne` elements, which can be more convenient for certain proofs.
-/

section WithoutOneCharacterizations

variable {S} [Semigroup S] (a b : S)

theorem R_preorder_iff_without_one : a ≤𝓡 b ↔ a = b ∨ ∃ x, a = b * x := by
  unfold R_preorder; constructor
  · rintro ⟨x, hx⟩; cases x with
    | one => left; simp_all
    | coe y => right; use y; simp [← WithOne.coe_inj, hx]
  · rintro h; cases h with
    | inl h => use (1 : S¹); simp_all
    | inr h => obtain ⟨x, hx⟩ := h; use x; simp [← WithOne.coe_mul, hx]

theorem L_preorder_iff_without_one : a ≤𝓛 b ↔ a = b ∨ ∃ x, a = x * b := by
  unfold L_preorder; constructor
  · rintro ⟨x, hx⟩; cases x with
    | one => left; simp_all
    | coe y => right; use y; simp [← WithOne.coe_inj, hx]
  · rintro h; cases h with
    | inl h => use (1 : S¹); simp_all
    | inr h => obtain ⟨x, hx⟩ := h; use x; simp [← WithOne.coe_mul, hx]

theorem J_preorder_iff_without_one : a ≤𝓙 b ↔ a = b ∨ a ≤𝓛 b ∨ a ≤𝓡 b ∨ ∃ x y, a = x * b * y := by
  constructor
  · intro hJ; obtain ⟨x, y, hxy⟩ := hJ; cases' x with x' <;> cases' y with y'
    · left; simp_all
    · right; right; left; use ↑y'; exact hxy
    · right; left; use ↑x'; exact hxy
    · right; right; right; use x', y'; simp [← WithOne.coe_inj, hxy]
  · rintro (h | h | h | ⟨x, y, hxy⟩)
    · rw [h]; exact J_preorder_refl b
    · obtain ⟨x', hx⟩ := h; use x', 1; simp [hx]
    · obtain ⟨y', hy⟩ := h; use 1, y'; simp [hy]
    · use ↑x, ↑y; simp [hxy, WithOne.coe_mul]

theorem R_eqv_iff_without_one : a 𝓡 b ↔ a = b ∨ (∃ u v, a = b * u ∧ b = a * v) := by
  simp_all [R_eqv_iff, R_preorder_iff_without_one]; aesop

theorem L_eqv_iff_without_one : a 𝓛 b ↔ a = b ∨ (∃ u v, a = u * b ∧ b = v * a) := by
  simp_all [L_eqv_iff, L_preorder_iff_without_one]; aesop

end WithoutOneCharacterizations

/-! ### Monoid-specific characterizations of Preorders

This section provides specialized versions of Green's preorder definitions for monoids,
demonstrating how the `WithOne` construction behaves like the original monoid.
-/

section MonoidCharacterizations

variable {M} [Monoid M] (a b : M)

theorem R_preorder_iff_monoid : a ≤𝓡 b ↔ ∃ x, a = b * x := by
  unfold R_preorder; constructor
  · rintro ⟨x, hx⟩; cases x with
    | one => use 1; simp [← WithOne.coe_inj, hx]
    | coe y => use y; simp [← WithOne.coe_inj, hx]
  · rintro ⟨x, hx⟩; use (↑x : M¹); simp [← WithOne.coe_inj, hx]

theorem L_preorder_iff_monoid : a ≤𝓛 b ↔ ∃ x, a = x * b := by
  unfold L_preorder; constructor
  · rintro ⟨x, hx⟩; cases x with
    | one => use 1; simp [← WithOne.coe_inj, hx]
    | coe y => use y; simp [← WithOne.coe_inj, hx]
  · rintro ⟨x, hx⟩; use (↑x : M¹)
    rw [← WithOne.coe_inj, WithOne.coe_mul] at hx; exact hx

theorem J_preorder_iff_monoid : a ≤𝓙 b ↔ ∃ x y, a = x * b * y := by
  unfold J_preorder; constructor
  · rintro ⟨x, y, hxy⟩; cases' x with x' <;> cases' y with y'
    · use 1, 1; simp_all
    · use 1, y'; simp [← WithOne.coe_inj, hxy]
    · use x', 1; simp [← WithOne.coe_inj, hxy]
    · use x', y'; simp [← WithOne.coe_inj, hxy]
  · rintro ⟨x, y, hxy⟩; use (↑x : M¹), (↑y : M¹); simp [← WithOne.coe_inj, hxy]

end MonoidCharacterizations

/-! ### Translations and Set-defined R/L classes

This section defines translation on semigroups and provides a set (not necessarily finite)
description of R/L classes. These definitions provide foundations for proving Green's Lemma.
-/

section Translations

variable {S} [Semigroup S] {a b: S}

def R_translation (a : S) : S → S := (· * a)
def R_translation_op (a : Sᵐᵒᵖ) : Sᵐᵒᵖ → Sᵐᵒᵖ := (· * a)

notation:50 "ρᵣ" a => R_translation a
infixr:70 " ⋆ρᵣ " => R_translation

def L_translation (a : S) : S → S := (a * ·)
def L_translation_op (a : Sᵐᵒᵖ) : Sᵐᵒᵖ → Sᵐᵒᵖ := (a * ·)

notation:50 "ρₗ" a => L_translation a
infixr:70 " ⋆ρₗ " => L_translation

def R_class_set (x : S) : Set (S) :=
  {a | a 𝓡 x}
def L_class_set (x : S) : Set (S) :=
  { a | a 𝓛 x}
def J_class_set (x : S) : Set (S) :=
  { a | a 𝓙 x}
def H_class_set (x : S) : Set (S) :=
  { a | a 𝓗 x}

@[simp] lemma in_L_implies_in_J (e a : S): e ∈ L_class_set a → (e ∈ J_class_set a) :=
  fun h => by
    simp [L_class_set, J_class_set] at *
    obtain ⟨u, hu⟩ := h
    obtain ⟨v, hv⟩ := u
    obtain ⟨w, hw⟩ := hu
    refine (J_eqv_iff e a).mpr ?_
    constructor
    · use v, 1; simp[hv]
    · use w, 1; simp [hw]

@[simp] lemma in_R_implies_in_J (e a : S): e ∈ R_class_set a → (e ∈ J_class_set a) :=
  fun h => by
    simp [R_class_set, J_class_set] at *
    obtain ⟨u, hu⟩ := h
    obtain ⟨v, hv⟩ := u
    obtain ⟨w, hw⟩ := hu
    refine (J_eqv_iff e a).mpr ?_
    constructor
    · use 1, v; simp[hv]
    · use 1, w; simp [hw]
end Translations
