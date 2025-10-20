import MyProject.Main_Results.Location_alt
import MyProject.Misc.SemigroupIdeals

def ReesMatrix {I : Type} {G : Type} {J : Type} (P : J → I → G) := Option (I × G × J)
def ReesMatrixNonzero {I J G : Type} (P : J → I → G) := I × G × J

namespace ReesMatrix0

variable {G : Type } {I : Type } {J : Type } (P : J → I → G) [Nonempty I] [Nonempty J]
  [GroupWithZero G]

instance ReesMul : Mul (ReesMatrix P) where
  mul a b :=
    match a, b with
    | some (i1, g1, j1), some (i2, g2, j2) =>
      match P j1 i2 with
      | pval => some (i1, g1 * pval * g2, j2)
    | _, _ => none

/-- I needed to define this separately to use it in the proof of associativity
-- otherwise lean complained about the Option wrapper on ReesMatrix-/
def rees_mul (a b : ReesMatrix P) : ReesMatrix P :=
  match a, b with
  | some (i1, g1, j1), some (i2, g2, j2) =>
      match P j1 i2 with
      | pval => some (i1, g1 * pval * g2, j2)
  | _, _ => none

/-
instance {P : J → I → G} : MulZeroClass (ReesMatrix P) where
  zero := none
  mul := Mul.mul
  zero_mul := by
    intro x
    cases x with
    | none => rfl
    | some _ => rfl
  mul_zero := by
    intro x
    cases x with
    | none => rfl
    | some _ => rfl
--/

instance (P : J → I → G) : Semigroup (ReesMatrix P) where
  mul := Mul.mul
  mul_assoc := by
    intros a b c
    cases a with
    | none => rfl
    | some aval =>
      cases b with
      | none => rfl
      | some bval =>
        cases c with
        | none =>
          let h1 := rees_mul P (some aval) (some bval)
          have h2 : rees_mul P h1 none = none := by rfl
          exact h2
        | some cval =>
          let aval' : ReesMatrix P := some aval
          let bval' : ReesMatrix P := some bval
          let cval' : ReesMatrix P := some cval
          rcases aval with ⟨i₁, g₁, j₁⟩
          rcases bval with ⟨i₂, g₂, j₂⟩
          rcases cval with ⟨i₃, g₃, j₃⟩
          let mid₁ := P j₁ i₂
          let mid₂ := P j₂ i₃
          have hab : aval' * bval' = some (i₁, g₁ * mid₁ * g₂, j₂) := by
            rfl
          have hbc : bval' * cval' = some (i₂, g₂ * mid₂ * g₃, j₃) := by
            rfl
          have ha_bc : aval' * (bval' * cval') = some (i₁, g₁ * mid₁ * (g₂ * mid₂ * g₃), j₃) := by
            simp_all only [mid₁, mid₂, aval', bval', cval']
            rfl
          have hab_c : aval' * bval' * cval' = some (i₁, (g₁ * mid₁ * g₂) * mid₂ * g₃, j₃) := by
            simp_all only [cval', aval', mid₂, mid₁, bval']
            rfl
          have heq : (g₁ * mid₁ * g₂) * mid₂ * g₃ = g₁ * mid₁ * (g₂ * mid₂ * g₃) := by
            simp[mul_assoc]
          have hfinal : aval' * bval' * cval' = aval' * (bval' * cval') := by
            simp_all only [ha_bc, hab_c, heq]
          unfold aval' bval' cval' at hfinal
          exact hfinal

end ReesMatrix0

namespace ReesMatrixNonzero

variable {I J G : Type} (P : J → I → G) {Nonempty I} {Nonempty J} [Group G]

instance : Coe (ReesMatrixNonzero P) (ReesMatrix P) :=
  ⟨fun ⟨i, g, j⟩ => some (i, g, j)⟩

instance : Mul (ReesMatrixNonzero P) where
  mul a b :=
    match a, b with
    | (i₁, g₁, j₁), (i₂, g₂, j₂) =>
        (i₁, g₁ * P j₁ i₂ * g₂, j₂)

def rees_mul_nz (a b : ReesMatrixNonzero P) : ReesMatrixNonzero P :=
  match a, b with
  | (i₁, g₁, j₁), (i₂, g₂, j₂) =>
      (i₁, g₁ * P j₁ i₂ * g₂, j₂)

instance : Semigroup (ReesMatrixNonzero P) where
  mul_assoc := by
    intros a' b' c'
    let a : ReesMatrixNonzero P := a'
    let b : ReesMatrixNonzero P:= b'
    let c : ReesMatrixNonzero P := c'
    rcases a' with ⟨i₁, g₁, j₁⟩
    rcases b' with ⟨i₂, g₂, j₂⟩
    rcases c' with ⟨i₃, g₃, j₃⟩
    let mid₁ := P j₁ i₂; let mid₂ := P j₂ i₃
    have hab : a * b = (i₁, g₁ * mid₁ * g₂, j₂) := by rfl
    have hbc : b * c = (i₂, g₂ * mid₂ * g₃, j₃) := by rfl
    have ha_bc : a * (b * c) = (i₁, g₁ * mid₁ * (g₂ * mid₂ * g₃), j₃) := by
      simp_all only [a, b, mid₁, c, mid₂]; rfl
    have hab_c : a * b * c = (i₁, (g₁ * mid₁ * g₂) * mid₂ * g₃, j₃) := by
      simp_all only [a, b, mid₁, c, mid₂]; rfl
    have heq : (g₁ * mid₁ * g₂) * mid₂ * g₃ = g₁ * mid₁ * (g₂ * mid₂ * g₃) := by simp[mul_assoc]
    simp_all only [a, b, mid₁, c, mid₂]

/-- Compatibility: mult in `ReesMatrixNoZero` matches `ReesMatrix` coercion.
To make this work, I need to get the MulOneClass and MulZeroClass multiplication
of the 0 and nonzero containing RMs to align-- rewrite rees_mul in terms of
[Mul G], then assert Group/GroupWithZero where needed?-/

theorem coe_mul (a b : ReesMatrixNonzero P) [GroupWithZero G]:
    (a * b : ReesMatrix P) = ReesMatrix0.rees_mul P (↑a) (↑b) := by
  let a' : ReesMatrixNonzero P := a
  let b' : ReesMatrixNonzero P := b
  rcases a with ⟨i₁, g₁, j₁⟩
  rcases b with ⟨i₂, g₂, j₂⟩
  simp [ReesMatrix0.rees_mul]
  rfl

end ReesMatrixNonzero

section ReesMatrixTheorems
variable {G : Type } {I : Type } {J : Type } (P : J → I → G) [Nonempty I] [Nonempty J]
  [GroupWithZero G]

/- the following are skeletons for proofs of theorems about the Rees matrix semigroup-/

variable {S : Type*} [Semigroup S]

/- Prop 3.1 (about simple/zero simple)-- to delete? may fit better
be covered in SemigroupIdeals file-/

/- helper lemmas -/
lemma Ideal'.nonempty_if_ne_emptyset {S : Type*} [Semigroup S]
  (I : Ideal' S) (hI : I ≠ ∅) : (I : Set S).Nonempty := by
  contrapose! hI
  ext x
  apply Iff.intro
  · intro a
    apply SetLike.mem_of_subset
    on_goal 2 => {exact a}
    · simp_all only [Set.empty_subset]
  · intro a
    apply SetLike.mem_of_subset
    · simp_all only [Set.subset_empty_iff]
      exact hI
    · simp_all only [Set.mem_empty_iff_false]
      exact a

lemma simple_iff_ideals (S : Type*) [Semigroup S] :
  Ideal'.isSimple S ↔ ∀ a : S, Ideal'.principal a = ⊤ := by
  apply Iff.intro
  · intro h a
    have h' := h (Ideal'.principal a)
    cases h' with
    | inl h_empty =>
      have : a ∈ (Ideal'.principal a : Set S) := by
        simp [Ideal'.principal, Ideal'.ofSet_coe]
      simp[h_empty] at *
      cases this
    | inr h_top =>
      exact h_top
  · intro h I
    by_cases hI : I = ∅
    · left; exact hI
    · right
      obtain ⟨x, hx⟩ := Ideal'.nonempty_if_ne_emptyset I hI
      have incl : Ideal'.principal x ≤ I := by
        intro y hy
        simp [Ideal'.principal, Ideal'.ofSet_coe] at hy
        obtain ⟨s, t, h⟩ := hy
        simp_all only [SetLike.mem_coe, Set.mul_singleton, Set.image_univ, Set.mem_range, Set.mem_univ, true_and]
        obtain ⟨w, h_2⟩ := t
        obtain ⟨w_1, h⟩ := h
        subst h h_2
        simp_all only [Ideal'.mul_left_mem, Ideal'.mul_right_mem]
        rename_i h_1
        simp_all only [SetLike.mem_coe, LeftIdeal.ofSet_coe, Set.mul_singleton, Set.image_univ, Set.union_singleton,
          Set.mem_insert_iff, Set.mem_range]
        cases h_1 with
        | inl h_2 =>
          subst h_2
          simp_all only
        | inr h_3 =>
          obtain ⟨w, h_1⟩ := h_3
          subst h_1
          simp_all only [Ideal'.mul_left_mem]
        rename_i h_1
        simp_all only [SetLike.mem_coe, RightIdeal.ofSet_coe, Set.singleton_mul, Set.image_univ, Set.union_singleton,
          Set.mem_insert_iff, Set.mem_range]
        cases h_1 with
        | inl h_2 =>
          subst h_2
          simp_all only
        | inr h_3 =>
          obtain ⟨w, h_1⟩ := h_3
          subst h_1
          simp_all only [Ideal'.mul_right_mem]
      rw [h x] at incl
      apply le_antisymm; exact fun ⦃x⦄ a ↦ trivial
      exact incl


lemma zero_simple_iff_ideals (S : Type*) [SemigroupWithZero S] :
  Ideal'.isZeroSimple S ↔ (∃ a : S, a ≠ 0) ∧ ∀ a : S, a ≠ 0 → Ideal'.principal a = ⊤ := by
    simp_all only [ne_eq]
    apply Iff.intro
    · intro a
      apply And.intro
      · cases a with
        | intro h hI =>
          obtain ⟨x, b⟩ := h
          have hI := hI (Ideal'.principal x)
          cases hI with
          | inl hI =>
            exact Exists.imp' (HMul.hMul x) (fun a a ↦ a) b
          | inr hI => exact Exists.imp' (HMul.hMul x) (fun a a ↦ a) b
      · intro a_1 a_2
        sorry
    · intro a
      obtain ⟨left, right⟩ := a
      obtain ⟨w, h⟩ := left
      sorry

/- notion of regular classes in semigroups-- there are a number of theorems
about these we may or may not need/want to prove. For now just need them to
state Theorem 3.2 --/

def is_regular (a : S) : Prop := ∃ s : S, a * s * a = a

def J_class_regular (x : S) : Prop := ∀ a ∈ J_class_set x, is_regular a

def R_class_regular (x : S) : Prop := ∀ a ∈ R_class_set x, is_regular a

def L_class_regular (x : S) : Prop := ∀ a ∈ L_class_set x, is_regular a

def H_class_regular (x : S) : Prop := ∀ a ∈ H_class_set x, is_regular a

def all_J_classes_regular (S : Type*) [Semigroup S] := ∀ x : S, J_class_regular x

def regular_semigroup (S : Type*) [Semigroup S] := ∀ x : S, is_regular x

lemma regular_iff_J_regular (S : Type*) [Semigroup S] :
  regular_semigroup S ↔ all_J_classes_regular S := by
  apply Iff.intro
  · intro a
    exact fun x a_1 a_2 ↦ a a_1
  · intro h x
    have hx := h x
    unfold J_class_regular at hx
    have : x ∈ J_class_set x := by
      unfold J_class_set
      simp
    exact h x x this

lemma regular_semigroup.of_mul_equiv
  {S T : Type*} [Semigroup S] [Semigroup T]
  (e : S ≃* T) (hS : regular_semigroup S) :
  regular_semigroup T := by
    intro y
    obtain ⟨x, rfl⟩ := e.surjective y
    obtain ⟨s, hs⟩ := hS x
    use e s
    rw [← e.map_mul, ← e.map_mul, hs]

 /- this is Theorem 3.2-/

open ReesMatrixNonzero
attribute [simp] mul_inv_cancel₀ inv_mul_cancel₀

 /- this is (part) of Theorem 3.2-/
 /-Using MulEquiv to indicate "semigroup isomorphism"-- to replace?--/

theorem zero_simple_iff_rees [Finite S] [SemigroupWithZero S] [GroupWithZero G] :
        Ideal'.isZeroSimple S ↔
        ∃ (I J : Type)  (P : J → I → G) (iso : S ≃* ReesMatrix P),
        Nonempty I ∧ Nonempty J ∧ Nonempty G ∧ regular_semigroup S ∧
        (∃ a b : S, a * b ≠ 0) ∧
        (∀ a : S, a ≠ 0 → ∃ (i : I) (g : G) (j : J),
        iso a = (some (i, g, j) : ReesMatrix P)) := by
  simp_all only [ne_eq, exists_and_left]
  apply Iff.intro
  · intro a
    sorry
  · intro ⟨I, neI, J, neJ, neG, regS, hab, P, iso, nzerorep⟩
    refine And.symm ⟨?_, ?_⟩
    · intro I
      by_cases hIempty : I = ∅
      · left; exact hIempty
      · have : ∃ x : S, x ∈ I := by exact Ideal'.exists_mem_of_ne_empty hIempty
        obtain ⟨a, hx⟩ := hab
        have hINZ : a ≠ 0 := by
          simp_all only [ne_eq]
          obtain ⟨w, h⟩ := this
          obtain ⟨w_1, h_1⟩ := hx
          apply Aesop.BuiltinRules.not_intro
          intro a_1
          subst a_1
          simp_all only [zero_mul, not_true_eq_false]
        right; right
        have ha : a≠0 := hINZ
        have hnzideal : ⊤ = Ideal'.ofSet ({iso a}) := by
          obtain ⟨i₁, g₁, j₁, ha⟩ := nzerorep a ha
          let J1 := J_class_set (a)
          have ainJ : a ∈ J1 := by
            simp_all only [ne_eq, J1]
            unfold J_class_set; simp
          have hJ : is_J_class J1 := by
            simp_all only [ne_eq, J1]
            apply Exists.intro
            · rfl
          have hjreg : is_regular_J_class J1 hJ := by
            simp_all only [ne_eq, J1]
            intro a ha
            obtain ⟨s, hs⟩ := regS a
            use s
          have t := (regular_J_class_tfae J1) hJ
          have t1 := t.out 0 2
          have t2 := t.out 0 3
          obtain ⟨x, hx⟩ := t1
          obtain ⟨y, hy⟩ := t2
          have xJ := x hjreg a ainJ ; obtain ⟨e1, hs⟩ := xJ
          have yJ := y hjreg a ainJ ; obtain ⟨e2, ht⟩ := yJ
          have he1 : e1 ≠ 0 := by sorry
          have he2 : e2 ≠ 0 := by sorry
          obtain ⟨i₃, g₃, r, he1⟩ := nzerorep e1 he1
          obtain ⟨s, g₄, j₄, he2⟩ := nzerorep e2 he2
          refine Ideal'.ext fun d ↦ Iff.intro ?h₁ ?h₂
          simp_all only [exists_prop, Set.mem_singleton_iff, Set.mem_setOf_eq]
          · intro _
            by_cases hx0 : d = none
            · subst hx0
              left; left
              simp; use none; simp
              have h1 : ReesMatrix0.rees_mul P (none) (some (i₁, g₁, j₁)) = none := by unfold ReesMatrix0.rees_mul ; simp_all
              have h2: ReesMatrix0.rees_mul P (some (i₁, g₁, j₁)) (none)  = none := by unfold ReesMatrix0.rees_mul ; simp_all
              constructor
              · use none; exact h1
              · use none; exact h2
            · refine SetLike.mem_coe.mp ?_
              have hd0 : iso.symm d ≠ 0 := by
                contrapose! hx0
                have h : iso (iso.symm d) = iso 0 := congrArg iso hx0
                rw [iso.apply_symm_apply] at h
                have iso_symm_none_zero : iso.symm none = 0 := by
                  by_contra hneq
                  obtain ⟨i0, g0, j0, hh⟩ := nzerorep (iso.symm none) hneq
                  rw [iso.apply_symm_apply] at hh
                  cases hh
                have : iso 0 = none := by
                  have := congrArg iso iso_symm_none_zero
                  simp[iso.apply_symm_apply none] at this
                  exact this.symm
                simp[h, this]
              obtain ⟨i₂, g₂, j₂, hd⟩ := nzerorep (iso.symm d) (hd0)
              have P1 : P j₁ s ≠ 0 := by sorry
              have P2 : P r i₁ ≠ 0 := by sorry
              have: g₁ ≠ 0 := by sorry
              let A : ReesMatrix P := some (i₂, g₁⁻¹ * (P r i₁)⁻¹, r)
              let B : ReesMatrix P := some (s, (P j₁ s)⁻¹ * g₂, j₂)
              let mid : ReesMatrix P := some (i₁, g₁ * P j₁ s * ((P j₁ s)⁻¹  * g₂), j₂)
              let mid' : ReesMatrix P := some (i₂, 1, j₁)
              have h1 : (iso a) * B = mid := by rw[ha]; simp[B, mid]; rfl
              have h1' : A * (iso a) = mid' := by
                rw[ha];
                simp[A, mid']
                have : ReesMatrix0.rees_mul P (some (i₂, g₁⁻¹ * (P r i₁)⁻¹, r)) (some (i₁, g₁, j₁)) = some (i₂, 1, j₁) := by
                  unfold ReesMatrix0.rees_mul ; simp_all
                exact this
              have h2 : A * mid = some (i₂, g₂, j₂) := by
                simp[A, mid]
                set lhs := (g₁⁻¹ * (P r i₁)⁻¹) * P r i₁ * (g₁ * P j₁ s * ((P j₁ s)⁻¹ * g₂))
                have lh : lhs = g₂ := by simp_all[lhs, mul_assoc]
                rw [<-lh]; simp[<-mul_assoc]; simp[mul_assoc, mul_inv_cancel₀ P1]
                simp_all only [ne_eq, implies_true, exists_and_left, forall_const, imp_self, isUnit_iff_ne_zero,
                    not_false_eq_true, IsUnit.inv_mul_cancel_right, IsUnit.inv_mul_cancel_left, mid, B, lhs, A, J1]
                have : ReesMatrix0.rees_mul P (some (i₂, g₁⁻¹ * (P r i₁)⁻¹, r)) (some (i₁, g₁ * g₂, j₂)) = some (i₂, g₂, j₂) := by
                    unfold ReesMatrix0.rees_mul ; simp_all
                exact this
              have h2' : mid' * B = some (i₂, g₂, j₂) := by
                simp[A, mid', B]
                have : ReesMatrix0.rees_mul P (some (i₂, 1, j₁)) (some (s, (P j₁ s)⁻¹ * g₂, j₂)) = some (i₂, g₂, j₂) := by
                    unfold ReesMatrix0.rees_mul ; simp_all
                exact this
              have hAB : A * ((iso a) * B) = iso (iso.symm d) := by simp[h1, h2, hd]
              have hAB' : (A * (iso a)) * B = iso (iso.symm d) := by simp[h1', h2', hd]
              have hI : iso (iso.symm d) ∈ Ideal'.ofSet ({iso a}) := by
                simp_all only [ne_eq, implies_true, exists_and_left, forall_const, imp_self]
                unfold Ideal'.ofSet
                left; left; unfold Set.mul
                use mid'
                simp
                have : ReesMatrix0.rees_mul P (some (i₂, g₁⁻¹ * (P r i₁)⁻¹, r)) (some (i₁, g₁, j₁)) = some (i₂, 1, j₁) := by
                    unfold ReesMatrix0.rees_mul ; simp_all
                simp[this, mid']
                obtain ⟨left, right⟩ := hs
                obtain ⟨left_1, right_1⟩ := ht
                apply And.intro
                · apply Exists.intro
                  ·  exact h1'
                · apply Exists.intro
                  · exact h2'
              rw [iso.apply_symm_apply, ha] at hI; exact hI
          intro hdin
          simp_all only [ne_eq, implies_true, exists_and_left, forall_const, imp_self, J1]
          obtain ⟨left, right⟩ := hs
          obtain ⟨left_1, right_1⟩ := ht
          apply SetLike.mem_of_subset
          · simp_all only [Ideal'.ofSet_coe, Set.mul_singleton, Set.image_univ, LeftIdeal.ofSet_coe, Set.union_singleton,
                Set.union_insert, RightIdeal.ofSet_coe, Set.singleton_mul, Set.mem_union, Set.mem_insert_iff, Set.mem_range,
                true_or, Set.insert_eq_of_mem, Ideal'.coe_top, Set.subset_univ, J1]
          · exact hdin
        have : I = ⊤ := by
          apply Ideal'.ext
          intro x
          constructor
          · intro a_1
            simp_all only [ne_eq, not_false_eq_true]
            obtain ⟨w, h⟩ := this
            obtain ⟨w_1, h_1⟩ := hx
            apply SetLike.mem_of_subset
            · simp_all only [Ideal'.coe_top, Set.subset_univ]
            · exact a_1
          · have hx0 : iso x ∈ Ideal'.ofSet {iso a} := by
                rw [←hnzideal]
                trivial
            sorry
        exact this
    exact hab

theorem simple_iff_rees [Semigroup S] [Group G] :
        Ideal'.isSimple S ↔
        ∃ (I J : Type) (P : J → I → G) (iso : S ≃* ReesMatrixNonzero P),
        Nonempty I ∧ Nonempty J ∧ Nonempty G ∧ regular_semigroup S ∧
        (∀ a : S, ∃ (i : I) (g : G) (j : J),
        iso a = ((i, g, j) : ReesMatrixNonzero P)) := by
  simp_all only [exists_and_left]
  apply Iff.intro
  · intro a
    sorry
  · intro a
    sorry

end ReesMatrixTheorems


namespace Example
/-This implements the simple example for a 2-element group G, as given in the typed up 7/17
meeting notes.-/

/--defines a group with two elements--/
inductive G2 | one | α deriving DecidableEq, Repr

open G2

instance : Group G2 where
  mul
    | one, x => x
    | x, one => x
    | α, α => one
  one := one
  inv
    | one => one
    | α => α
  mul_assoc := by
    intro a b c
    cases a <;> cases b <;> cases c <;> rfl
  one_mul := by intro x; cases x <;> rfl
  mul_one := by intro x; cases x <;> rfl
  inv_mul_cancel := by
    intro a
    cases a <;> rfl


abbrev G2WZ := WithZero G2

def one : G2WZ := some 1
def α : G2WZ := some G2.α
instance : BEq G2 := by exact ⟨fun a b => a = b⟩


inductive A | a1 | a2 deriving DecidableEq, Repr
inductive B | b1 | b2 deriving DecidableEq, Repr

open A B

instance : Nonempty A := ⟨a1⟩
instance : Nonempty B := ⟨b1⟩

def P : B → A → G2WZ
| b2, a2 => α
| _, _ => one

abbrev RM := ReesMatrix P

def e1 : ReesMatrix P := some (a1, one, b1)
def e2 : ReesMatrix P := some (a1, one, b2)
def e3 : ReesMatrix P := some (a2, one, b1)
def e4 : ReesMatrix P := some (a2, α, b2)

-- some examples to test the multiplication

#eval e4 * e4 -- this is an idempotent-- result should be e4 = (a2, α, b2)
#eval e1 * e2 -- this should be e2 = (a1, one, b2)
#eval e1 * e3 -- should be e1 = (a1, one, b1)
#eval e2 * e3 -- should be (a1, α, b1)

end Example
