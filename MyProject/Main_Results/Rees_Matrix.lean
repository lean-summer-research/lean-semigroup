import MyProject.Main_Results.Location
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
/-NOTE: the book seems to allow ideals to be the empty set, hence the below defs of
simple/zero simple. If we decide to define ideals as never empty that ideals are nonempty
we should edit these-/
def IsSimpleSemigroup (S : Type*) [Semigroup S] : Prop :=
  ∀ I : Set S, (I = Ideal' S) → (I = ∅) ∨ (I = Set.univ)

def IsZeroSimpleSemigroup (S : Type*) [Semigroup S] [Zero S]: Prop :=
   (∃ a b : S, a * b ≠ 0) ∧
   (∀ I : Set S, (I = Ideal' S) → I = ∅ ∨ I = {0} ∨ I = Set.univ)

/- the following two lemmas encode Prop 3.1-/
lemma simple_iff_ideals (S : Type*) [Semigroup S] :
  IsSimpleSemigroup S ↔ ∀ a : S, (Ideal'.principal a : Set S) = Set.univ := by
  apply Iff.intro
  · intro a a_1
    sorry
  · intro a
    sorry

lemma zero_simple_iff_ideals (S : Type*) [Semigroup S] [SemigroupWithZero S] :
  IsZeroSimpleSemigroup S ↔ (∃ a : S, a ≠ 0) ∧ ∀ a : S, (Ideal'.principal a : Set S) = Set.univ \ {0} := by
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


 /- this is (part) of Theorem 3.2-/
 /-Using MulEquiv to indicate "semigroup isomorphism"-- to replace?--/

theorem zero_simple_iff_rees [SemigroupWithZero S] [GroupWithZero G] :
        IsZeroSimpleSemigroup S ↔
        ∃ (I J : Type)  (P : J → I → G) (iso : S ≃* ReesMatrix P),
        Nonempty I ∧ Nonempty J ∧ Nonempty G ∧ regular_semigroup S ∧
        (∃ a b : S, a * b ≠ 0) ∧
        (∀ a : S, a ≠ 0 → ∃ (i : I) (g : G) (j : J),
        iso a = (some (i, g, j) : ReesMatrix P)) := by
  simp_all only [ne_eq, exists_and_left]
  apply Iff.intro
  · intro a
    sorry
  · intro a
    sorry

theorem simple_iff_rees [Semigroup S] [Group G] :
        IsSimpleSemigroup S ↔
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
