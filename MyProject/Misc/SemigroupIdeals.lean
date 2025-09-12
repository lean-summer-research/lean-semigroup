import MyProject.GreensRelations.Defs
import Mathlib.Algebra.Group.WithOne.Basic

/-!
### Ideal Structure Definitions
The `SetLike` implementation is from the template in the docstring of `Mathlib.Data.Setlike.Basic`.
We define left, right and two-sided ideals in a semigroup as `Structures`, and we also provide
a function from `Set α → Ideal α` which is the smallest ideal containing the set.
Principal ideals are defined as the smallest ideal containing a singleton set.
-/

open Pointwise -- Allows `s * t` notation for pointise set mul

structure LeftIdeal (α : Type*) [Mul α] where
  carrier : Set α
  mul_mem_mem {x: α} (hin : x ∈ carrier) (y : α) : y * x ∈ carrier

namespace LeftIdeal

variable {α : Type*} [Mul α] {x y : α}

instance : EmptyCollection (LeftIdeal α) where
  emptyCollection := {
      carrier := ∅
      mul_mem_mem := by simp}

instance : Top (LeftIdeal α) where
  top := {
      carrier := ∅
      mul_mem_mem := by simp}

/--`SetLike` instance requires we prove that there is an injection from `LeftIdeal → Set`.
It regesters a coersion to `Set` and provides various simp lemmas and instances-/
instance : SetLike (LeftIdeal α) α :=
  ⟨LeftIdeal.carrier, fun p q h ↦ by cases p; cases q; congr!⟩

@[simp] lemma mem_carrier {p : LeftIdeal α} {x : α}: x ∈ p.carrier ↔ x ∈ (p : Set α) := Iff.rfl

/-- This allows us to use the `ext` tactic -/
@[ext] theorem ext {p q : LeftIdeal α} (h : ∀ x, x ∈ p ↔ x ∈ q) : p = q := SetLike.ext h

@[simp] lemma mem {p : LeftIdeal α} (hin : x ∈ p) : y * x ∈ p := by
  have h := p.mul_mem_mem hin y; simp_all

variable {S : Type*} [Semigroup S]

def ofSet (p : Set S) : LeftIdeal S where
  carrier := Set.univ * p ∪ p
  mul_mem_mem := by
    intros x h y
    simp_all [Set.mem_mul]
    left
    rcases h with (⟨w, ⟨v, ⟨hv, heq⟩⟩⟩ | hin)
    · use y * w
      use v
      simp_all [mul_assoc]
    · use y; use x

@[simp] lemma ofSet_coe (p : Set S) : ↑(ofSet p) = Set.univ * p ∪ p := rfl

@[simp] lemma ofSet_coe_prop (p : Set S) {x y : S} (hin : x ∈ ↑(ofSet p)) : y * x ∈ ↑(ofSet p) := by
  simp_all

/-- The `SetLike` instance lets us use `≤` like `⊆` -/
theorem ofSet_minimal {p : LeftIdeal S} {q : Set S} (hin : q ⊆ ↑p) :
    (ofSet q) ≤ p := by
  simp only [ ← SetLike.coe_subset_coe]
  dsimp
  simp_all [Set.subset_def]
  intros x hx
  rcases hx with (⟨y, ⟨hy, ⟨w, ⟨hw, heq⟩⟩ ⟩⟩ | hx)
  · simp_all
    subst x
    apply hin at hw
    simp_all
  · apply hin; exact hx

def principal (x : S) : LeftIdeal S := ofSet {x}

end LeftIdeal

structure RightIdeal (α : Type*) [Mul α] where
  carrier : Set α
  mem_mul_mem {x: α} (hin : x ∈ carrier) (y : α) : x * y ∈ carrier

namespace RightIdeal

variable {α : Type*} [Mul α] {x y : α}

instance : EmptyCollection (RightIdeal α) where
  emptyCollection := {
      carrier := ∅
      mem_mul_mem := by simp}

instance : Top (RightIdeal α) where
  top := {carrier := Set.univ,
          mem_mul_mem := by simp_all}

/--`SetLike` instance requires we prove that there is an injection from `LeftIdeal → Set`.
It regesters a coersion to `Set` and provides various simp lemmas and instances-/
instance : SetLike (RightIdeal α) α :=
  ⟨RightIdeal.carrier, fun p q h ↦ by cases p; cases q; congr!⟩

@[simp] lemma mem_carrier {p : RightIdeal α} {x : α}: x ∈ p.carrier ↔ x ∈ (p : Set α) := Iff.rfl

/-- This allows us to use the `ext` tactic -/
@[ext] theorem ext {p q : RightIdeal α} (h : ∀ x, x ∈ p ↔ x ∈ q) : p = q := SetLike.ext h

@[simp] lemma mem {p : RightIdeal α} (hin : x ∈ p) : x * y ∈ p := by
  have h := p.mem_mul_mem hin y; simp_all

variable {S : Type*} [Semigroup S]

def ofSet (p : Set S) : RightIdeal S where
  carrier := p * Set.univ ∪ p
  mem_mul_mem := by
    intros x hx y
    simp_all [Set.mem_mul]
    left
    rcases hx with (⟨w, ⟨v, ⟨hv, heq⟩⟩⟩ | hin)
    · subst x
      use w; simp_all
      use hv * y
      simp_all [mul_assoc]
    · use x; simp_all

@[simp] lemma ofSet_coe (p : Set S) : ↑(ofSet p) = p * Set.univ ∪ p := rfl

@[simp] lemma ofSet_coe_prop (p : Set S) {x y : S} (hin : x ∈ ↑(ofSet p)) : x * y ∈ ↑(ofSet p) := by
  simp_all

/-- The `SetLike` instance lets us use `≤` like `⊆` -/
theorem ofSet_minimal {p : RightIdeal S} {q : Set S} (hin : q ⊆ ↑p) :
    (ofSet q) ≤ p := by
  simp only [ ← SetLike.coe_subset_coe]
  dsimp
  simp_all [Set.subset_def]
  intros x hx
  rcases hx with (⟨y, ⟨hy, ⟨w, ⟨hw, heq⟩⟩ ⟩⟩ | hx)
  · simp_all
    subst x
    apply hin at hy
    simp_all
  · apply hin; exact hx

def principal (x : S) : RightIdeal S := ofSet {x}

end RightIdeal

structure Ideal' (α : Type*) [Mul α] where
  carrier : Set α
  mem_mul_mem {x: α} (hin : x ∈ carrier) (y : α) : x * y ∈ carrier
  mul_mem_mem {x: α} (hin : x ∈ carrier) (y : α) : y * x ∈ carrier

namespace Ideal'

variable {α : Type*} [Mul α] {x y z : α}

instance : EmptyCollection (Ideal' α) where
  emptyCollection := {
      carrier := ∅
      mem_mul_mem := by simp
      mul_mem_mem := by simp}

instance : Top (Ideal' α) where
  top := {carrier := Set.univ,
          mem_mul_mem := by simp_all,
          mul_mem_mem := by simp_all}

def toLeftIdeal (p : Ideal' α) : LeftIdeal α where
  carrier := p.carrier
  mul_mem_mem := p.mul_mem_mem

def toRightIdeal (p : Ideal' α) : RightIdeal α where
  carrier := p.carrier
  mem_mul_mem := p.mem_mul_mem

/--`SetLike` instance requires we prove that there is an injection from `LeftIdeal → Set`.
It regesters a coersion to `Set` and provides various simp lemmas and instances-/
instance : SetLike (Ideal' α) α :=
  ⟨Ideal'.carrier, fun p q h ↦ by cases p; cases q; congr!⟩

@[simp] lemma mem_carrier {p : Ideal' α} {x : α}: x ∈ p.carrier ↔ x ∈ (p : Set α) := Iff.rfl

/-- This allows us to use the `ext` tactic -/
@[ext] theorem ext {p q : Ideal' α} (h : ∀ x, x ∈ p ↔ x ∈ q) : p = q := SetLike.ext h

@[simp] lemma mem {p : Ideal' α} (hin : x ∈ p) : z * x * y ∈ p := by
  have h := p.mul_mem_mem hin z
  simp_all
  have h₂ := p.mem_mul_mem h y
  simp_all

@[simp] lemma mul_right_mem {p : Ideal' α} (hin : x ∈ p) : x * y ∈ p := by
  have h := p.mem_mul_mem hin y
  simp_all

@[simp] lemma mul_left_mem {p : Ideal' α} (hin : x ∈ p) : y * x ∈ p := by
  have h := p.mul_mem_mem hin y
  simp_all

variable {S : Type*} [Semigroup S]

def ofSet (p : Set S) : Ideal' S where
  carrier := Set.univ * p * Set.univ ∪ LeftIdeal.ofSet p ∪ RightIdeal.ofSet p
  mem_mul_mem := by
    intros x hx y
    simp_all
    rcases hx with ((htwo | (hleft | heq )) | hright | hin)
    · left; left
      rcases htwo with ⟨a, ⟨⟨b, ⟨hb, ⟨c, ⟨hc, heq⟩⟩⟩ ⟩, ⟨d, hd⟩⟩⟩
      simp_all
      subst a x
      use (b * c); simp_all
      constructor
      · use b; simp; use c
      · use d * y; simp [mul_assoc]
    · left; left
      rcases hleft with ⟨a, ⟨ha, ⟨b, ⟨hb, heq⟩⟩⟩⟩
      simp_all
      subst x
      use (a * b); simp_all
      use a; simp; use b
    · right; left
      use x; simp_all
    · right; left
      rcases hright with ⟨a, ⟨ha, ⟨b, ⟨hb, heq⟩⟩⟩⟩
      simp_all
      subst x
      use a; simp_all
      use b * y; simp [mul_assoc]
    · right; left
      use x; simp_all
  mul_mem_mem := by
    intros x hx y
    simp_all
    rcases hx with ((htwo | (hleft | heq )) | hright | hin)
    · left; left
      rcases htwo with ⟨a, ⟨⟨b, ⟨hb, ⟨c, ⟨hc, heq⟩⟩⟩ ⟩, ⟨d, hd⟩⟩⟩
      simp_all
      subst a x
      use (y * b * c); simp_all
      constructor
      · use y * b; simp; use c
      · use d; simp [mul_assoc]
    · left; right; left
      rcases hleft with ⟨a, ⟨ha, ⟨b, ⟨hb, heq⟩⟩⟩⟩
      simp_all
      subst x
      use (y * a); simp_all
      use b; simp_all [mul_assoc]
    · left; right; left
      use y; simp; use x
    · left; left
      rcases hright with ⟨a, ⟨ha, ⟨b, ⟨hb, heq⟩⟩⟩⟩
      simp_all
      subst x
      use y * a; simp_all
      constructor
      · use y; simp; use a
      · use b; simp_all [mul_assoc]
    · left; right; left
      use y; simp_all
      use x


@[simp] lemma ofSet_coe (p : Set S) : ((ofSet p) : Set S) = Set.univ * p * Set.univ ∪ ↑(LeftIdeal.ofSet p) ∪ ↑(RightIdeal.ofSet p) := by rfl


@[simp] lemma ofSet_coe_prop (p : Set S) {x y z : S} (hin : x ∈ ↑(ofSet p)) : z * x * y ∈ ↑(ofSet p) := by
  simp_all

/-- The `SetLike` instance lets us use `≤` like `⊆` -/
theorem ofSet_minimal {p : Ideal' S} {q : Set S} (hin : q ⊆ ↑p) :
    (ofSet q) ≤ p := by
  simp [ ← SetLike.coe_subset_coe]
  simp_all [Set.subset_def]
  constructor; constructor
  · intros x hx
    rcases hx with ⟨y, ⟨⟨z, ⟨hz, ⟨w, ⟨hw, heq⟩⟩⟩⟩, ⟨v, ⟨hv, heq₂⟩⟩⟩⟩
    simp_all
    subst x y
    apply hin at hw
    simp_all
  · intros x hx
    rcases hx with ⟨w, ⟨hw, ⟨b, ⟨hb, heq⟩ ⟩ ⟩ ⟩
    simp_all
    subst x
    apply hin at hb
    simp_all
  · intros x hx
    rcases hx with ⟨w, ⟨hw, ⟨b, ⟨hb, heq⟩ ⟩ ⟩ ⟩
    simp_all
    subst x
    apply hin at hw
    simp_all

def principal (x : S) : Ideal' S := ofSet {x}

end Ideal'

/-! ### Ideal Theorems-/

/-! #### The intersections of ideals are ideals -/

/-! #### Products of ideals are ideals -/

/-! #### Ideals are preserved under surjective morphisms -/

/-! #### Ideals are preserved under inverse morphisms -/



/-! ### (TODO) Quotients by Ideals -/

/-! ### (TODO) Minimal Ideals-/

variable {α : Type*} [Mul α]

namespace Ideal'

def isMinimal (I : Ideal' α) : Prop :=
  I ≠ ∅ ∧ ∀ (J : Ideal' α), J ≠ ∅ → J ≤ I → J = I

def isZeroMinimal [MulZeroClass α] (I : Ideal' α) : Prop :=
  I ≠ ∅ ∧ I.carrier ≠ {0} ∧
    ∀ (J : Ideal' α), J ≠ ∅ → J ≤ I → (J = I ∨ J.carrier = {0})

example : (a b : Set α) : a ⊆ b

/- We prove that a semigroup has at most one minimal ideal
Because`I ∩ J = ∅` and is an ideal contained in both,
minimality implies `I = I ∩ J` and `J = I ∩ J`, so `I = J` -/
theorem minimal_ideal_unique  (I J : Ideal' α) (hI : isMinimal I) (hJ : isMinimal J) :
    I = J := by
  rcases hI with ⟨hI₁, hI₂⟩
  rcases hJ with ⟨hJ₁, hJ₂⟩
  have hIJ := hI₂ J hJ₁
  have hJI := hJ₂ I hI₁
  have h : (I ≤ J) ∨ (J ≤ I) := by sorry
  rcases h with (h₁ | h₂)
  · exact hJI h₁
  · symm; exact hIJ h₂

/- TODO: Lemma; Every finite semigroup has a unique minimal ideal -/

/- Lemma: If `S` has a zero `0`, then `{0}` is a minimal ideal -/
variable {S : Type*} [SemigroupWithZero S]

lemma zero_is_minimal : isMinimal (Ideal'.principal (0 : S)) := by sorry

end Ideal'


/-! ### (TODO) Simple and Zero-Simple semigroups
A Semigroup `S` is simple if its only ideals are `∅ and S`.
If `S` has a zero element, it is zero-simple if its only ideals are `∅, {0}, and S`.
Left/right simple semigroups are defined analogously. -/


def isSimple (S : Type*) [Semigroup S] : Prop := ∀ (I : Ideal' S), I = ∅ ∨ I = ⊤

def isZeroSimple (S : Type*) [SemigroupWithZero S] : Prop :=
  ∀ (I : Ideal' S), I = ∅ ∨ I.carrier = {0} ∨ I = ⊤

/- Lemma: If `S` is 0-simple, then `S² = S`-/

/- Lemma: `S` is simple ↔ `SsS = S` for every `s ∈ S`-/
