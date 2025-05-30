import MyProject.GreensRelations.Defs

/-!
# Green's Relations Decidability and Finiteness

This file provides computational instances for Green's relations on finite semigroups with
decidable equality. It enables computation of Green's preorders, equivalences,
and equivalence classes, making the abstract definitions from `Defs.lean` computationally
tractable for concrete finite semigroups.

## Main Definitions

**Decidability Instances**:
  * `DecidableRel` instances for all Green's preorders and equivalences
  * `DecidableEq` instances for quotient types of Green's equivalence classes
  * `Fintype` instances for quotient types enabling finite enumeration

**Computational Equivalence Classes**:
  * `R_class_finset`, `L_class_finset`, etc. - Finset-based equivalence classes
  * `right_coset_fin`, `left_coset_fin`, `two_sided_coset_fin` - Finite cosets

**Alternative Characterizations**:
  * Finset-based versions of coset containment theorems

## Notation

* **Finset Classes**: `⟦a⟧𝓡_fin`, `⟦a⟧𝓛_fin`, `⟦a⟧𝓙_fin`, `⟦a⟧𝓗_fin`
* **Finite Cosets**: `M •fin a`, `a •fin M`, `M ••fin a`

## Implementation Notes

This file imports `GreensRelations.Defs` and enables the use of `#eval` to compute Green's
relations and the `decide` tactic for automated proofs about concrete finite semigroups.
The decidability instances are essential for the computational examples in `Examples.Threemap.lean`
-/

/-! ### Decidability and Finiteness -/

section Decidability_and_Finiteness

variable {S} [Semigroup S] [Fintype S] [DecidableEq S]

/-! ### DecidableRel Instances

This section provides `DecidableRel` instances for all Green's preorders and equivalences,
enabling algorithmic decision procedures ford these relations on finite semigroups with decidable
equality.
-/

/-! Preorder Relations -/
instance R_preorder_dec : DecidableRel (fun x y : S =>  x ≤𝓡 y) := by
  intros a b; unfold R_preorder; infer_instance
instance L_preorder_dec : DecidableRel (fun x y : S =>  x ≤𝓛 y) := by
  intros a b; unfold L_preorder; infer_instance
instance J_preorder_dec : DecidableRel (fun x y : S =>  x ≤𝓙 y) := by
  intros a b; unfold J_preorder; infer_instance
instance H_preorder_dec : DecidableRel (fun x y : S =>  x ≤𝓗 y) := by
  intros a b; unfold H_preorder; infer_instance

/-! Equivalence Relations -/
instance R_eqv_dec : DecidableRel (fun a b : S => a 𝓡 b) := by
  unfold DecidableRel; intros a b; simp [R_eqv]; infer_instance
instance L_eqv_dec : DecidableRel (fun a b : S => a 𝓛 b) := by
  unfold DecidableRel; intros a b; simp [L_eqv]; infer_instance
instance J_eqv_dec : DecidableRel (fun a b : S => a 𝓙 b) := by
  unfold DecidableRel; intros a b; simp [J_eqv]; infer_instance
instance H_eqv_dec : DecidableRel (fun a b : S => a 𝓗 b) := by
  unfold DecidableRel; intros a b; simp [H_eqv]; infer_instance


/-! ### Equivalence Classes as Quot Types

This section provides computational support for quotient types representing Green's equivalence
classes. It includes `DecidableEq` instances for testing equality of equivalence classes and
`Fintype` instances for finite enumeration of all equivalence classes.
-/

/-! `DecidableEq` instances for Quot Types -/

instance R_quot_dec: DecidableEq (R_class S) := by
  intros q₁ q₂
  -- Base case
  have helper : ∀ (a b : S), Subsingleton (Decidable ((⟦a⟧𝓡 : R_class S) = (⟦b⟧𝓡 : R_class S))) := by
    infer_instance
  apply @Quot.recOnSubsingleton₂ S S R_eqv R_eqv (fun x y => Decidable (x = y)) helper q₁ q₂
  intro a b -- Now we need to constructivly prove that ∀ a b, ⟦a⟧𝓡 = ⟦b⟧𝓡 ∨ ⟦a⟧𝓡 != ⟦b⟧𝓡
  -- By R_class_iff, this is equivalent to a ≡𝓡 b
  -- And we already have decidability for a ≡𝓡 b via R_eqv_dec
  exact decidable_of_iff (a 𝓡 b) (R_class_iff a b).symm

instance L_quot_dec : DecidableEq (L_class S) := by
  intros q₁ q₂
  have helper : ∀ (a b : S), Subsingleton (Decidable ((⟦a⟧𝓛 : L_class S) = (⟦b⟧𝓛 : L_class S))) := by
    infer_instance
  apply @Quot.recOnSubsingleton₂ S S L_eqv L_eqv (fun x y => Decidable (x = y)) helper q₁ q₂
  intro a b; exact decidable_of_iff (a 𝓛 b) (L_class_iff a b).symm

instance J_quot_dec : DecidableEq (J_class S) := by
  intros q₁ q₂
  have helper : ∀ (a b : S), Subsingleton (Decidable ((⟦a⟧𝓙 : J_class S) = (⟦b⟧𝓙 : J_class S))) := by
    infer_instance
  apply @Quot.recOnSubsingleton₂ S S J_eqv J_eqv (fun x y => Decidable (x = y)) helper q₁ q₂
  intro a b; exact decidable_of_iff (a 𝓙 b) (J_class_iff a b).symm

instance H_quot_dec : DecidableEq (H_class S) := by
  intros q₁ q₂
  have helper : ∀ (a b : S), Subsingleton (Decidable ((⟦a⟧𝓗 : H_class S) = (⟦b⟧𝓗 : H_class S))) := by
    infer_instance
  apply @Quot.recOnSubsingleton₂ S S H_eqv H_eqv (fun x y => Decidable (x = y)) helper q₁ q₂
  intro a b; exact decidable_of_iff (a 𝓗 b) (H_class_iff a b).symm

/-! `Fintype` instances for the quotient types -/

instance R_class_fintype : Fintype (R_class S) :=
  Fintype.ofSurjective (Quot.mk R_eqv) Quot.mk_surjective

instance L_class_fintype : Fintype (L_class S) :=
  Fintype.ofSurjective (Quot.mk L_eqv) Quot.mk_surjective

instance J_class_fintype : Fintype (J_class S) :=
  Fintype.ofSurjective (Quot.mk J_eqv) Quot.mk_surjective

instance H_class_fintype : Fintype (H_class S) :=
  Fintype.ofSurjective (Quot.mk H_eqv) Quot.mk_surjective

/-! ### Eqiv Classes as Finsets

This section defines Green's equivalence classes as `Finset`s, providing a computational
representation of equivalence classes as finite sets of elements.
-/

def R_class_finset (x : S) : Finset S :=
  Finset.univ.filter (fun a => a 𝓡 x)
def L_class_finset (x : S) : Finset S :=
  Finset.univ.filter (fun a => a 𝓛 x)
def J_class_finset (x : S) : Finset S :=
  Finset.univ.filter (fun a => a 𝓙 x)
def H_class_finset [Monoid S] [Fintype S] [DecidableEq S] (x : S) : Finset S :=
  Finset.univ.filter (fun a => a 𝓗 x)

/-! FinCoset notation: typed \[[ f \]]\MCR_fin -/
notation "⟦" f "⟧𝓡_fin" => R_class_finset f
notation "⟦" f "⟧𝓛_fin" => L_class_finset f
notation "⟦" f "⟧𝓙_fin" => J_class_finset f
notation "⟦" f "⟧𝓗_fin" => H_class_finset f

/-! ### Cosets as Finsets

This section provides finite set representations of left, right, and two-sided cosets, along with
computational versions of the coset-based characterizations of Green's preorders and equivalences.
These enable algorithmic verification of Green's relations via coset containment and equality.
-/

section Cosets

variable (M) [Monoid M] [Fintype M] [DecidableEq M] (a : M)

/-- the right coset `M • a` -/
def right_coset_fin (a : M) : Finset (M) := {x | ∃ y, x = y * a}

/-- the left coset `a • M` -/
def left_coset_fin (a : M) : Finset (M) := {x | ∃ y, x = a * y}

/-- the two_sided coset ` M • a • M` -/
def two_sided_coset_fin (a : M) : Finset (M) := {x | ∃ y z, x = y * a * z}

/-! FinCoset notation, typed \bub -/
notation:65 M " •fin " a:66 => right_coset_fin M a
notation:65 a:66 " •fin " M => left_coset_fin M a
notation:65 M " ••fin " a:66 => two_sided_coset_fin M a

end Cosets

variable (a b : S)

/-- The finite right coset of a product is contained in
the finite right coset of the second factor -/
lemma right_coset_fin_subset : (S¹ •fin (a * b)) ⊆ (S¹ •fin b) := by
  simp [right_coset_fin, Finset.subset_iff]; intro x
  use x * ↑a; simp [mul_assoc]

/-- The finite left coset of a product is contained in the finite left coset of the first factor -/
lemma left_coset_fin_subset : ((a * b) •fin S¹) ⊆ (a •fin S¹) := by
  simp [left_coset_fin, Finset.subset_iff]; intro x
  use b * x; simp [mul_assoc]

/-! Alternate Defs of Preorders from Finite cosets -/

theorem R_preorder_iff_coset_fin : a ≤𝓡 b ↔ (a •fin S¹) ⊆ (b •fin S¹) := by
  constructor
  · rw [R_preorder_iff]
    intro h; cases h with
    | inl heq => simp [heq]
    | inr h => obtain ⟨x, hx⟩ := h; rw [hx]; simp [left_coset_fin_subset]
  · intro h; simp_all [left_coset_fin, Finset.subset_iff]
    specialize @h ↑a 1; simp_all [R_preorder]

theorem L_preorder_iff_coset_fin : a ≤𝓛 b ↔ (S¹ •fin a) ⊆ (S¹ •fin b) := by
  constructor
  · rw [L_preorder_iff]
    intro h; cases h with
    | inl heq => simp [heq]
    | inr h => obtain ⟨x, hx⟩ := h; rw [hx]; simp [right_coset_fin_subset]
  · intro h; simp_all [right_coset_fin, Finset.subset_iff]
    specialize @h ↑a 1; simp_all [L_preorder]

theorem J_preorder_iff_coset_fin : a ≤𝓙 b ↔ (S¹ ••fin a) ⊆ (S¹ ••fin b) := by
  constructor
  · simp [J_preorder, two_sided_coset_fin, Finset.subset_iff]
    intros x y hxy z t u htu; subst htu
    use t * x, y * u; simp_all [mul_assoc]
  · simp [J_preorder, two_sided_coset_fin, Finset.subset_iff]
    intros H; specialize @H ↑a 1 1; simp_all


/-! Alternate definitions of equivalences with Finite cosets -/

theorem R_class_iff_coset_fin : a 𝓡 b ↔ (a •fin S¹) = (b •fin S¹) := by
  simp [R_eqv, R_preorder_iff_coset_fin, antisymm_iff]

theorem L_class_iff_coset_fin : a 𝓛 b ↔ (S¹ •fin a) = (S¹ •fin b) := by
  simp [L_eqv, L_preorder_iff_coset_fin, antisymm_iff]

theorem J_class_iff_coset_fin : a 𝓙 b ↔ (S¹ ••fin a) = (S¹ ••fin b) := by
  simp [J_eqv, J_preorder_iff_coset_fin, antisymm_iff]


end Decidability_and_Finiteness
