import MyProject.GreensRelations.Defs

/-! # Ideals

This file defines the notion of ideals in semigroups and gives a characterization of
Green's Relations in terms of these ideals

## Main Definitions

## Implementation notes

I don't think we have any proofs that use these ideals yet, so I moved these definitions out
of `GreensRelations.Defs` to here.
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
