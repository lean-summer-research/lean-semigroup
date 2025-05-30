import MyProject.Idempotence

/-!
# Green's Relations Definitions

This file defines Green's relations (𝓡, 𝓛, 𝓙, and 𝓗) for semigroups.

## Main Definitions

**Preorder Relations**:
  * `R_preorder a b` - The 𝓡 preorder: a ≤𝓡 b iff a*S¹ ⊆ b*S¹
  * `L_preorder a b` - The 𝓛 preorder: a ≤𝓛 b iff S¹*a ⊆ S¹*b
  * `J_preorder a b` - The 𝓙 preorder: a ≤𝓙 b iff S¹*a*S¹ ⊆ S¹*b*S¹
  * `H_preorder a b` - The 𝓗 preorder: intersection of 𝓡 and 𝓛

**Equivalence Relations**:
  * `R_eqv`, `L_eqv`, `J_eqv`, `H_eqv` - Green's equivalence relations
  * `R_class S`, `L_class S`, etc. - Quotient types for equivalence classes

**Alternative Characterizations**:
  * Coset-based definitions showing equivalences via principal ideals
  * Monoid-specific versions eliminating the need for S¹

## Notation

* **Preorders**: `a ≤𝓡 b`, `a ≤𝓛 b`, `a ≤𝓙 b`, `a ≤𝓗 b`
* **Equivalences**: `a 𝓡 b`, `a 𝓛 b`, `a 𝓙 b`, `a 𝓗 b`
* **Classes**: `⟦a⟧𝓡`, `⟦a⟧𝓛`, `⟦a⟧𝓙`, `⟦a⟧𝓗`
* **Cosets**: `M • a`, `a • M`, `M •• a`

## Implementation Notes

This file imports `Idempotence.lean` and is imported by `Decidable.lean`. It provides the
foundational definitions for Green's relations, with computational instances added in the
`GreensRelations.Decidable.lean`
-/

/-! ### Equivalence of Preorder

This section establishes the general framework for converting any preorder into an equivalence
relation. Given a preorder `p`, we define `eqv_of_preorder p a b` as `p a b ∧ p b a`, and we
instantiate it with the `Equivalence` type-class.
-/

section Equivalence_of_Preorder

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

end Equivalence_of_Preorder

/-! ### Greens Relations Definitions

This section defines the four Green's preorders (𝓡, 𝓛, 𝓙, 𝓗) for semigroups using the monoid
extension S¹. Each preorder is shown to be reflexive and transitive, with corresponding
equivalence relations derived using the framework from the previous section.
-/

section Definitions

variable {S} [Semigroup S]

/-- the 𝓡 preorder: a ≤𝓡 b iff a*S¹ ⊆ b*S¹ -/
def R_preorder (a b : S) : Prop := ∃ x : S¹ , ↑a = ↑b * x
/-- the 𝓛 preorder: a ≤𝓛 b iff S¹*a ⊆ S¹*b -/
def L_preorder (a b : S) : Prop := ∃ x : S¹, ↑a = x * ↑b
/-- the 𝓙 preorder: a ≤𝓙 b iff S¹*a*S¹ ⊆ S¹*b*S¹ -/
def J_preorder (a b : S) : Prop := ∃ x y : S¹, a = x * b * y
/-- the 𝓗 preorder -/
def H_preorder (a b : S) : Prop := R_preorder a b ∧ L_preorder a b

/-! Preorder notation, typed \leq\MCR -/
notation:50 f " ≤𝓡 " g:50 => R_preorder f g
notation:50 f " ≤𝓛 " g:50 => L_preorder f g
notation:50 f " ≤𝓙 " g:50 => J_preorder f g
notation:50 f " ≤𝓗 " g:50 => H_preorder f g

/-! Reflexivity lemmas -/
lemma R_preorder_refl (x : S) : x ≤𝓡 x := by use 1; simp
lemma L_preorder_refl (x : S) : x ≤𝓛 x := by use 1; simp
lemma J_preorder_refl (x : S) : x ≤𝓙 x := by use 1, 1; simp
lemma H_preorder_refl (x : S) : x ≤𝓗 x := by
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

/-! Preorder Instances -/
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

/-! Definitional lemmas for equivilance relations -/
lemma R_eqv_iff (a b : S) : a 𝓡 b ↔ a ≤𝓡 b ∧ b ≤𝓡 a := by unfold R_eqv; simp
lemma L_eqv_iff (a b : S) : a 𝓛 b ↔ a ≤𝓛 b ∧ b ≤𝓛 a := by unfold L_eqv; simp
lemma J_eqv_iff (a b : S) : a 𝓙 b ↔ a ≤𝓙 b ∧ b ≤𝓙 a := by unfold J_eqv; simp
lemma H_eqv_iff (a b : S) : a 𝓗 b ↔ a ≤𝓗 b ∧ b ≤𝓗 a := by unfold H_eqv; simp

end Definitions

section Quot

/-! ### The type of the equivalence classes as a `Quot`

This section constructs quotient types for Green's equivalence classes using Lean's `Quot`
constructor. It provides functions to map elements to their equivalence classes and establishes
the relationship between quotient equality and the underlying equivalence relations.
-/

def R_class (S) [Semigroup S] := Quot (fun a b : S => a 𝓡 b)
def L_class (S) [Semigroup S] := Quot (fun a b : S => a 𝓛 b)
def J_class (S) [Semigroup S] := Quot (fun a b : S => a 𝓙 b)
def H_class (S) [Semigroup S] := Quot (fun a b : S => a 𝓗 b)

variable {S} [Semigroup S]

/-! Functions from elements of `S` to their equivalence classes -/
def get_R_class (a : S) : R_class S := Quot.mk R_eqv a
def get_L_class (a : S) : L_class S := Quot.mk L_eqv a
def get_J_class (a : S) : J_class S := Quot.mk J_eqv a
def get_H_class (a : S) : H_class S := Quot.mk H_eqv a

/-! Notation for the functions returning equivalence classes of `S` -/
notation:50 "⟦"x"⟧𝓡" => get_R_class x
notation:50 "⟦"x"⟧𝓛" => get_L_class x
notation:50 "⟦"x"⟧𝓙" => get_J_class x
notation:50 "⟦"x"⟧𝓗" => get_H_class x

/-! Unlike `Quotient r`, `Quot r` does not require a `Setoid` structure on the binary relation `r`.
In fact, it does not even require that `r` be reflexive, transitive, or symmetric. Instead, it
applies the function `Relation.EqvGen` to `r`, which modifies `r` to relate all elements necessary
to fulfill the setoid conditions. Our relations are already Refl, trans, and symm so this function
does not change them, which we prove here. -/
@[simp] lemma R_EqvGen_eq (a b : S): Relation.EqvGen R_eqv a b ↔ a 𝓡 b :=
  Equivalence.eqvGen_iff (eqv_of_preorder_inst R_preorder)
@[simp] lemma L_EqvGen_eq (a b : S): Relation.EqvGen L_eqv a b ↔ a 𝓛 b :=
  Equivalence.eqvGen_iff (eqv_of_preorder_inst L_preorder)
@[simp] lemma J_EqvGen_eq (a b : S): Relation.EqvGen J_eqv a b ↔ a 𝓙 b :=
  Equivalence.eqvGen_iff (eqv_of_preorder_inst J_preorder)
@[simp] lemma H_EqvGen_eq (a b : S): Relation.EqvGen H_eqv a b ↔ a 𝓗 b :=
  Equivalence.eqvGen_iff (eqv_of_preorder_inst H_preorder)

/-! Definitional lemmas for equivilance classes -/
lemma R_class_iff (a b : S) : (⟦a⟧𝓡 : R_class S) = (⟦b⟧𝓡 : R_class S) ↔ a 𝓡 b := by
  unfold get_R_class
  rw [Quot.eq]; simp --simp finds R_EqvGen_eq
lemma L_class_iff (a b : S) : (⟦a⟧𝓛 : L_class S) = (⟦b⟧𝓛 : L_class S) ↔ a 𝓛 b := by
  unfold get_L_class
  rw [Quot.eq]; simp
lemma J_class_iff (a b : S) : (⟦a⟧𝓙 : J_class S) = (⟦b⟧𝓙 : J_class S) ↔ a 𝓙 b := by
  unfold get_J_class
  rw [Quot.eq]; simp
lemma H_class_iff (a b : S) : (⟦a⟧𝓗 : H_class S) = (⟦b⟧𝓗 : H_class S) ↔ a 𝓗 b := by
  unfold get_H_class
  rw [Quot.eq]; simp

end Quot

/-! ### Alternate Definitions of Preorders

This section provides alternative characterizations of Green's preorders that avoid explicit
use of S¹. It includes simplified definitions for semigroups, specialized versions for monoids,
and coset-based formulations that express the preorders in terms of principal ideal containment.
-/

section WithoutOne

variable {S} [Semigroup S] (a b : S)

theorem R_preorder_iff : a ≤𝓡 b ↔ a = b ∨ ∃ x, a = b * x := by
  unfold R_preorder; constructor
  · rintro ⟨x, hx⟩; cases x with
    | one => left; simp_all
    | coe y => right; use y; simp [← WithOne.coe_inj, hx]
  · rintro h; cases h with
    | inl h => use (1 : S¹); simp_all
    | inr h => obtain ⟨x, hx⟩ := h; use x; simp [← WithOne.coe_mul, hx]

theorem L_preorder_iff  : a ≤𝓛 b ↔ a = b ∨ ∃ x, a = x * b := by
  unfold L_preorder; constructor
  · rintro ⟨x, hx⟩; cases x with
    | one => left; simp_all
    | coe y => right; use y; simp [← WithOne.coe_inj, hx]
  · rintro h; cases h with
    | inl h => use (1 : S¹); simp_all
    | inr h => obtain ⟨x, hx⟩ := h; use x; simp [← WithOne.coe_mul, hx]

theorem J_preorder_iff : a ≤𝓙 b ↔ a = b ∨ a ≤𝓛 b ∨ a ≤𝓡 b ∨ ∃ x y, a = x * b * y := by
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

theorem H_preorder_iff (a b : S) : a ≤𝓗 b ↔ a ≤𝓡 b ∧ a ≤𝓛 b := by simp [H_preorder]

end WithoutOne

/-! Preorder definitions on Monoids, showing how M¹ behaves like M-/

section MonoidPreorders

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

end MonoidPreorders

/-! Cosets as Sets -/

section Cosets

/-- the right coset `M • a` -/
def right_coset (M) [Monoid M] (a : M) : Set (M) := {x | ∃ y, x = y * a}
/-- the right coset `a • M` -/
def left_coset (M) [Monoid M] (a : M) : Set (M) := {x | ∃ y, x = a * y}
/-- the two_sided coset ` M • a • M` -/
def two_sided_coset (M) [Monoid M] (a : M) : Set (M) := {x | ∃ y z, x = y * a * z}

/-! Coset notation, typed \bub -/
notation:65 M " • " a:66 => right_coset M a
notation:65 a:66 " • " M => left_coset M a
notation:65 M " •• " a:66  => two_sided_coset M a

variable {S} [Semigroup S] (a b : S)

/-! Coset lemmas -/
lemma right_coset_subset : (S¹ • (a * b)) ⊆ (S¹ • b) := by
  simp [right_coset]; intro x; use (x * a); simp [mul_assoc]
lemma left_coset_subset : ((a * b) • S¹) ⊆ (a • S¹) := by
  simp [left_coset]; intro x; use (b * x); simp [mul_assoc]

/-! Preorder Defs from Cosets -/

theorem R_preorder_iff_coset : a ≤𝓡 b ↔ (a • S¹) ⊆ (b • S¹) := by
  rw [R_preorder_iff]
  constructor
  · intro h; cases h with
    | inl heq => simp [heq]
    | inr h => obtain ⟨x, hx⟩ := h; rw [hx]; simp [left_coset_subset]
  · intro h; simp_all [left_coset]
    specialize h ↑a 1; simp_all [← R_preorder_iff, R_preorder]

theorem L_preorder_iff_coset : a ≤𝓛 b ↔ (S¹ • a) ⊆ (S¹ • b) := by
  rw [L_preorder_iff]
  constructor
  · intro h; cases h with
    | inl heq => simp [heq]
    | inr h => obtain ⟨x, hx⟩ := h; rw [hx]; simp [right_coset_subset]
  · intro h; simp_all [right_coset]
    specialize h ↑a 1; simp_all [← L_preorder_iff, L_preorder]

theorem J_preorder_iff_coset : a ≤𝓙 b ↔ (S¹ •• a) ⊆ (S¹ •• b) := by
  constructor
  · simp [J_preorder, two_sided_coset]
    rintro x y Hreach z t u Hz; subst Hz
    use (t * x), (y * u); simp_all [mul_assoc]
  · simp [J_preorder, two_sided_coset]
    intros H
    specialize H ↑a 1 1; simp_all

theorem H_preorder_iff_coset : a ≤𝓗 b ↔ (a • S¹) ⊆ (b • S¹) ∧ (S¹ • a) ⊆ (S¹ • b) := by
  simp [H_preorder, R_preorder_iff_coset, L_preorder_iff_coset]

/-! Equiv Relation Defs from Cosets -/

theorem R_eqv_iff_coset : a 𝓡 b ↔ (a • S¹) = (b • S¹) := by
  simp [R_eqv_iff, R_preorder_iff_coset, antisymm_iff]

theorem L_eqv_iff_coset : a 𝓛 b ↔ (S¹ • a) = (S¹ • b) := by
  simp [L_eqv_iff, L_preorder_iff_coset, antisymm_iff]

theorem J_eqv_iff_coset : a 𝓙 b ↔ (S¹ •• a) = (S¹ •• b) := by
  simp [J_eqv_iff, J_preorder_iff_coset, antisymm_iff]

theorem H_eqv_iff_coset : a 𝓗 b ↔ a 𝓡 b ∧ a 𝓛 b := by
  simp [H_eqv, H_preorder_iff]
  rw [@and_comm (b ≤𝓡 a), and_assoc, ← @and_assoc _ _ (b ≤𝓡 a)]
  rw [ ← L_eqv_iff, and_comm, and_assoc, @and_comm (b ≤𝓡 a) _, ←  R_eqv_iff, and_comm]

end Cosets
