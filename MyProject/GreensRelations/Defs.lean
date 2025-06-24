import MyProject.Idempotence

/-!
# Green's Relations Definitions

This file defines Green's relations 𝓡, 𝓛, 𝓙, 𝓗, and 𝓓 for semigroups.

## Main definitions

**Preorder Relations**:
* `R_preorder` - the 𝓡 preorder: `a ≤𝓡 b` iff `a*S¹ ⊆ b*S¹`
* `L_preorder` - the 𝓛 preorder: `a ≤𝓛 b` iff `S¹*a ⊆ S¹*b`
* `J_preorder` - the 𝓙 preorder: `a ≤𝓙 b` iff `S¹*a*S¹ ⊆ S¹*b*S¹`
* `H_preorder` - the 𝓗 preorder: intersection of 𝓡 and 𝓛

**Equivalence Relations**:
* `R_eqv`, `L_eqv`, `J_eqv`, `H_eqv` - Green's equivalence relations
* `D_eqv` - the 𝓓 relation defined as composition of 𝓡 and 𝓛

**Principal Ideals**:
* `left_ideal`, `right_ideal`, `two_sided_ideal` - principal ideal constructions

## Notations

* **Preorders**: `a ≤𝓡 b`, `a ≤𝓛 b`, `a ≤𝓙 b`, `a ≤𝓗 b`
* **Equivalences**: `a 𝓡 b`, `a 𝓛 b`, `a 𝓙 b`, `a 𝓗 b`, `a 𝓓 b`
* **Ideals**: `M • a` (left), `a • M` (right), `M •• a` (two-sided)
* **Relation composition**: `r ∘ᴿ s`

## TODO

* I started writing a 𝓓 preoreder but I had trouble relating the equivilance it generates
through `eqv_of_preorder` to the definitnion as the composition of 𝓛 and 𝓡. I also could
not find anyone talking about a 𝓓 preorder in the literature, and I'm wondering if it is
it even possible to define. It seemed like it was equivilant to the 𝓙 preorder.

* Can the alternate definitions of the preorders in monoids be more generalized? Should we
put that in withone.lean? Do all statments in `S¹` hold in `S` and vice versa if `S` is
already a monoid?

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

variable {a b : S}

/-! Reflexivity Lemmas -/
@[simp] lemma R_eqv_refl : a 𝓡 a := by constructor <;> simp
@[simp] lemma L_eqv_refl : a 𝓛 a := by constructor <;> simp
@[simp] lemma J_eqv_refl : a 𝓙 a := by constructor <;> simp
@[simp] lemma H_eqv_refl : a 𝓗 a := by constructor <;> simp

/-! Symmetry Lemmas -/
lemma R_eqv_symm : a 𝓡 b ↔ b 𝓡 a := by
  constructor <;> (intros h; apply eqv_of_preorder_symm; simp_all [R_eqv_iff])
lemma L_eqv_symm : a 𝓛 b ↔ b 𝓛 a := by
  constructor <;> (intros h; apply eqv_of_preorder_symm; simp_all [L_eqv_iff])
lemma J_eqv_symm : a 𝓙 b ↔ b 𝓙 a := by
  constructor <;> (intros h; apply eqv_of_preorder_symm; simp_all [J_eqv_iff])
lemma H_eqv_symm : a 𝓗 b ↔ b 𝓗 a := by
  constructor <;> (intros h; apply eqv_of_preorder_symm; simp_all [H_eqv_iff])
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

/-! ### Ideal-based characterizations

This section provides an alternative approach to Green's relations through principal ideals.
-/

section IdealCharacterizations

/-- the left ideal `M • a` -/
def left_ideal (M) [Monoid M] (a : M) : Set (M) := {x | ∃ y, x = y * a}

/-- the right ideal `a • M` -/
def right_ideal (M) [Monoid M] (a : M) : Set (M) := {x | ∃ m, x = a * m}

/-- the two_sided ideal ` M •• a` -/
def two_sided_ideal (M) [Monoid M] (a : M) : Set (M) := {x | ∃ y z, x = y * a * z}

/-! Ideals of sets (rather than ideals of elements) -/

def left_ideal_set (M) [Monoid M] (A : Set M) : Set (M) := {x | ∃ (a : A) (y : M), x = y * a}

def right_ideal_set (M) [Monoid M] (A : Set M) : Set (M) := {x | ∃ (a : A) (y : M), x = a * y}

def two_sided_ideal_set (M) [Monoid M] (A : Set M) : Set (M) := {x | ∃ (a : A) (y z : M), x = y * a * z}

/-! Ideal notation, typed \bub -/
notation:65 M " • " a:66 => left_ideal M a
notation:65 a:66 " • " M => right_ideal M a
notation:65 M " •• " a:66  => two_sided_ideal M a

/-! Ideal set notation  -/
notation:65 M " •ˢ " A:66 => left_ideal_set M A
notation:65 A:66 " •ˢ " M => right_ideal_set M A
notation:65 M " ••ˢ " A:66  => two_sided_ideal_set M A

variable {S} [Semigroup S] (a b : S)

/-- The left ideal of `a * b` is contained in the left ideal of `b`. -/
lemma left_ideal_subset : (S¹ • (a * b)) ⊆ (S¹ • b) := by
  simp [left_ideal]; intro x; use (x * a); simp [mul_assoc]

/-- The right ideal of `a * b` is contained in the right ideal of `a`. -/
lemma right_ideal_subset : ((a * b) • S¹) ⊆ (a • S¹) := by
  simp [right_ideal]; intro x; use (b * x); simp [mul_assoc]

/-! Preorder characterizations from ideals -/

theorem L_preorder_iff_ideal : a ≤𝓛 b ↔ (S¹ • a) ⊆ (S¹ • b) := by
  rw [L_preorder_iff_without_one]
  constructor
  · intro h; cases h with
    | inl heq => simp [heq]
    | inr h => obtain ⟨x, hx⟩ := h; rw [hx]; simp [left_ideal_subset]
  · intro h; simp_all [left_ideal]
    specialize h ↑a 1; simp_all [← L_preorder_iff_without_one, L_preorder]

theorem R_preorder_iff_ideal : a ≤𝓡 b ↔ (a • S¹) ⊆ (b • S¹) := by
  rw [R_preorder_iff_without_one]
  constructor
  · intro h; cases h with
    | inl heq => simp [heq]
    | inr h => obtain ⟨x, hx⟩ := h; rw [hx]; simp [right_ideal_subset]
  · intro h; simp_all [right_ideal]
    specialize h ↑a 1; simp_all [← R_preorder_iff_without_one, R_preorder]

theorem J_preorder_iff_ideal : a ≤𝓙 b ↔ (S¹ •• a) ⊆ (S¹ •• b) := by
  constructor
  · simp [J_preorder, two_sided_ideal]
    rintro x y Hreach z t u Hz; subst Hz
    use (t * x), (y * u); simp_all [mul_assoc]
  · simp [J_preorder, two_sided_ideal]
    intros H
    specialize H ↑a 1 1; simp_all

/-! Equivalence relation characterizations from ideals -/

theorem L_eqv_iff_ideal : a 𝓛 b ↔ (S¹ • a) = (S¹ • b) := by
  simp [L_eqv_iff, L_preorder_iff_ideal, antisymm_iff]

theorem R_eqv_iff_ideal : a 𝓡 b ↔ (a • S¹) = (b • S¹) := by
  simp [R_eqv_iff, R_preorder_iff_ideal, antisymm_iff]

theorem J_eqv_iff_ideal : a 𝓙 b ↔ (S¹ •• a) = (S¹ •• b) := by
  simp [J_eqv_iff, J_preorder_iff_ideal, antisymm_iff]

/- Relating one and two sided ideals (should we keep these?) -/

lemma two_sided_ideal_iff : ((S¹ • a) •ˢ S¹) = (S¹ •• a) := by
  simp [two_sided_ideal]
  apply Set.setOf_inj.mpr; ext x
  constructor
  · simp; intro b hb c hc; subst hc
    simp [left_ideal] at hb; obtain ⟨d, hd⟩ := hb; subst hd
    use d, c
  · rintro ⟨y, z, h⟩; subst h; simp
    use y * ↑a; simp [left_ideal]; use y

lemma two_sided_ideal_iff' : (S¹ •ˢ (a • S¹)) = (S¹ •• a) := by
  simp [two_sided_ideal]
  apply Set.setOf_inj.mpr; ext x
  constructor
  · simp; intro b hb c hc; subst hc
    simp [right_ideal] at hb; obtain ⟨d, hd⟩ := hb; subst hd
    use c, d; rw [← mul_assoc]
  · rintro ⟨y, z, h⟩; subst h; simp
    use ↑a * z; simp [right_ideal, ← mul_assoc]; use y

end IdealCharacterizations

/-! ### Green's 𝓓-relation and relation composition

This section introduces relation composition and uses it to define Green's 𝓓-relation.
We establish the commutativity of Green's 𝓡 and 𝓛 relations under composition, which
allows an alternate characterization of the 𝓓-relation.
-/

section DRelation

variable {S} [Semigroup S] {a b: S}

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

/-! Relation composition and Green's D-relation -/

/-- Composition of binary relations -/
def rel_comp {α : Type*} (r s : α → α → Prop) : α → α → Prop :=
  λ a c => ∃ b, r a b ∧ s b c

notation:50 f " ∘ᴿ " g:50 => rel_comp f g

/-- Green's D-relation, defined as the composition of R and L relations -/
def D_eqv : S → S → Prop := R_eqv ∘ᴿ L_eqv
infix:50 " 𝓓 " => D_eqv

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

end Translations
