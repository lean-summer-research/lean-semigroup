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

/--The intersection of two ideals is an ideal-/
instance : Inter (Ideal' α) where
  inter p q := {
    carrier := p.carrier ∩ q.carrier
    mem_mul_mem := by
      intros x hx y
      rcases hx with ⟨hxp, hxq⟩
      constructor
      . exact p.mem_mul_mem hxp y -- Proof for `x * y ∈ p.carrier`
      . exact q.mem_mul_mem hxq y -- Proof for `x * y ∈ q.carrier`
    mul_mem_mem := by
      intros x hx y
      rcases hx with ⟨hxp, hxq⟩
      constructor
      . exact p.mul_mem_mem hxp y -- Proof for `y * x ∈ p.carrier`
      . exact q.mul_mem_mem hxq y -- Proof for `y * x ∈ q.carrier`
  }
@[simp] lemma inter_coe {p q : Ideal' α} : ↑(p ∩ q) = ↑p ∩ ↑q := rfl



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
@[simp] lemma coe_top : ((⊤ : Ideal' α) : Set α) = Set.univ := rfl
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




/-! ### Quotients by Ideals
- Should we use QUot or Quotient?
- Prove that the quotient is a semigroup `{x : S // x = 0 ∨ ¬(x ∈ I)}`
- Define the Surjective mul hom
-/

section Quotient

variable {S : Type*} [Semigroup S]

/-!
#### Ree's Congruence
We given an `I : Ideal S`, we can form a congruence on `S`, called the Ree's Congruence, where
`a ~ b` if `a = b` or `a, b ∈ I`.
-/

def ReesCon (I : Ideal' S) (x y : S) : Prop := x = y ∨ (x ∈ I ∧ y ∈ I)

lemma ReesCon.refl (I : Ideal' S) (x : S) : ReesCon I x x := Or.inl rfl

lemma ReesCon.symm (I : Ideal' S) {x y : S} (h : ReesCon I x y) : ReesCon I y x := by
  simp_all [ReesCon]
  rcases h with (h | ⟨h₁, h₂⟩)
  · subst x; simp
  · right; exact ⟨h₂, h₁⟩

lemma ReesCon.trans (I : Ideal' S) {x y z : S} (hxy : ReesCon I x y) (hyz : ReesCon I y z) :
    ReesCon I x z := by
  simp_all [ReesCon]
  rcases hxy with (hxy | ⟨hxy₁, hxy₂⟩)
  <;> rcases hyz with (hyz | ⟨hyz₁, hyz₂⟩)
  · subst x; subst y; simp
  · subst y; right; exact ⟨hyz₁, hyz₂⟩
  · subst y; right; exact ⟨hxy₁, hxy₂⟩
  · right; exact ⟨hxy₁, hyz₂⟩

/-- The property that lifts it from setoid to congruence -/
lemma ReesCon.mul' (I : Ideal' S) {w x y z : S} (hwx : ReesCon I w x) (hyz : ReesCon I y z) :
    ReesCon I (w * y) (x * z) := by
  simp_all [ReesCon]
  rcases hwx with (hwx | ⟨hwx₁, hwx₂⟩)
  <;> rcases hyz with (hyz | ⟨hyz₁, hyz₂⟩)
  · subst x; subst y; left; rfl
  · subst w; right; simp_all
  · subst z; right; simp_all
  · right; simp_all

instance ReesCon.equiv (I : Ideal' S) : Equivalence (ReesCon I) where
  refl := ReesCon.refl I
  symm := ReesCon.symm I
  trans := ReesCon.trans I

instance ReesCon.Con (I : Ideal' S) : Con S where
  r := ReesCon I
  iseqv := ReesCon.equiv I
  mul' (hwx) (hyz) := ReesCon.mul' I hwx hyz

@[simp] lemma ReesCon.Con_def (I : Ideal' S) (x y : S) : (ReesCon.Con I) x y ↔ x = y ∨ (x ∈ I ∧ y ∈ I) := by rfl

abbrev ReesCon.Quotient (I : Ideal' S) :=  (ReesCon.Con I).Quotient

instance ReesCon.QuotSemigroup (I : Ideal' S) : Semigroup (ReesCon.Quotient I) :=
  (ReesCon.Con I).semigroup

/-- The semigroup cannonical homomorphism -/
def ReesCon.mulHom (I : Ideal' S) : S →ₙ* (ReesCon.Quotient I) := (ReesCon.Con I).mkMulHom

variable {M : Type*} [Monoid M]

instance ReesCon.QuotMonoid (I : Ideal' M) : Monoid (ReesCon.Quotient I) :=
  (ReesCon.Con I).monoid

/-- The monoid cannonical homomorphism -/
def ReesCon.monoidHom (I : Ideal' M) : M →* (ReesCon.Quotient I) := (ReesCon.Con I).mk'

/-!
#### Structure of quotients by Rees congruence
We prove that, as long as `(I : Ideal S) ≠ ∅`, then the quotient semigroup is a
`SemigroupWithZero`, where the zero element is the class of any element in `I`
-/

/-
instance ReesCon.QuotZeroOfInhabited (I : Ideal' S) [Inhabited I] (hd : ↑(default : I) ∈ I) : Zero (ReesCon.Quotient I) where
  zero := ReesCon.mulHom I ↑(default : I)

lemma ReesCon.zeroDef (I : Ideal' S) [Inhabited I] {x : I} : (0 : Quotient I) = ⟦x⟧  := by
  have hrep := Quotient.exists_rep (0 : Quotient I)
  rcases hrep with ⟨y, hy⟩
  rw [← hy]
  rw [Quotient.eq]
  simp


/- ERror: failed to synthesize
  OfNat (Quotient I) 0
numerals are polymorphic in Lean, but the numeral `0` cannot be used in a context where the expected type is
  Quotient I
due to the absence of the instance above

Additional diagnostic information may be available using the `set_option diagnostics true` command.-/
instance ReesCon.QuotSemigroupWithZero (I : Ideal' S) {x : S} (hx : x ∈ I): SemigroupWithZero (ReesCon.Quotient I) where
  zero := ReesCon.mulHom I x
  zero_mul := by
    intro a
    have h : (Zero.zero : Quotient I) = ReesCon.mulHom I x := by rfl


#check MulEquiv

lemma ReesCon.zeroDef (I : Ideal' S) {x : S} (hx : x ∈ I) : (0 : ReesCon.Quotient I) = ↑x := by sorry
-/
end Quotient



/-! ### (TODO) Minimal Ideals-/

variable {α : Type*} [Mul α]

namespace Ideal'

def isMinimal (I : Ideal' α) : Prop :=
  I ≠ ∅ ∧ ∀ (J : Ideal' α), J ≠ ∅ → J ≤ I → J = I

def isZeroMinimal [MulZeroClass α] (I : Ideal' α) : Prop :=
  I ≠ ∅ ∧ I.carrier ≠ {0} ∧
    ∀ (J : Ideal' α), J ≠ ∅ → J ≤ I → (J = I ∨ J.carrier = {0})


/- We prove that a semigroup has at most one minimal ideal
Because`I ∩ J = ∅` and is an ideal contained in both,
minimality implies `I = I ∩ J` and `J = I ∩ J`, so `I = J` -/
lemma exists_mem_of_ne_empty {I : Ideal' α} (h : I ≠ ∅) : ∃ x, x ∈ I := by
  -- turn `I ≠ ∅` (as an `Ideal'`) into `(I : Set α) ≠ ∅`
  have hset : (I : Set α) ≠ ∅ := by
    intro hh
    -- `hh : (I : Set α) = ∅` gives `I = ∅` by SetLike.coe_injective
    have : I = ∅ := SetLike.coe_injective hh
    exact h this
  -- use the set-lemma to get a witness
  rcases Set.nonempty_iff_ne_empty.mpr hset with ⟨x, hx⟩
  exact ⟨x, hx⟩

theorem minimal_ideal_unique (I J : Ideal' α) (hI : isMinimal I) (hJ : isMinimal J) :
    I = J := by
  rcases hI with ⟨hI_ne, hI_min⟩
  rcases hJ with ⟨hJ_ne, hJ_min⟩

  rcases exists_mem_of_ne_empty hI_ne with ⟨a, ha⟩
  rcases exists_mem_of_ne_empty hJ_ne with ⟨b, hb⟩

  have hab : a * b ∈ (I ∩ J : Set α) := by
    constructor
    · exact I.mul_right_mem ha
    · exact J.mul_left_mem hb

  -- show I ∩ J is nonempty (by contradiction)
  have h_inter_ne : (I ∩ J) ≠ ∅ := by
    intro H
    have hset : (I ∩ J : Set α) = ∅ := congrArg (fun K : Ideal' α => (K : Set α)) H
    rw [hset] at hab
    exact hab

  -- this is a bit terse. we apply minimiality to show I ∩ J is a subset of I, first showing nonempty
  have HI := (hI_min (I ∩ J) h_inter_ne (by intro x hx; exact hx.1)).symm
  have HJ := (hJ_min (I ∩ J) h_inter_ne (by intro x hx; exact hx.2)).symm

  -- compose to get I = J
  exact HI.trans HJ.symm


/- TODO: Lemma; Every finite semigroup has a unique minimal ideal -/

/- Lemma: If `S` has a zero `0`, then `{0}` is a minimal ideal -/
variable {S : Type*} [SemigroupWithZero S]

lemma principal_zero_eq : (principal (0 : S) : Set S) = {0} := by
  ext x -- tactic that reduces to proving `A=B` (as sets) to `x ∈ A ↔ x ∈ B`
  simp only [Set.mem_singleton_iff] -- replaces `x ∈ {0}` with `x=0`
  constructor
  · intro hx -- `x ∈ principal (0 : S) → x = 0`
    simp [principal, ofSet, LeftIdeal.ofSet, RightIdeal.ofSet, Set.mem_union,
          Set.mem_mul, Set.mem_univ, Set.mem_singleton_iff] at hx
    -- `hx` is now a big "or" statement. We check every case.
    rcases hx with (((⟨a, c, rfl⟩ | ⟨a, rfl⟩) | rfl) | ⟨b, rfl⟩) | rfl
    · simp [mul_zero, zero_mul] -- Case `x = a * 0 * c`
    · simp [mul_zero]           -- Case `x = a * 0`
    · rfl                        -- Case `x = 0`
  · intro hx -- `x = 0 → x ∈ principal (0 : S)`
    rw [hx]
    simp only [principal, ofSet, LeftIdeal.ofSet, RightIdeal.ofSet]
    right; left
    use 0
    simp

lemma zero_is_minimal : isMinimal (principal (0 : S)) := by
  constructor
  · -- show `principal 0 ≠ ∅` by contradiction: coerce both sides to `Set` and use `principal_zero_eq`
    intro h
    -- i'm not exactly sure how this magical line works. chatgpt found it
    have hset : ((principal (0 : S) : Set S) = (∅ : Set S)) := congrArg (fun (I : Ideal' S) => (I : Set S)) h
    simp [principal_zero_eq] at hset
  · intro J hJ_ne hJ_le --minimality
    ext x
    constructor
    · intro hx
      exact hJ_le hx
    · intro hx
      have : x ∈ (principal (0 : S) : Set S) := hx
      rw [principal_zero_eq, Set.mem_singleton_iff] at this
      subst x
      rcases exists_mem_of_ne_empty hJ_ne with ⟨y, hy⟩
      have h0 : y * 0 ∈ J := J.mul_right_mem hy -- y * 0 = 0 ∈ J, so 0 ∈ J

      rwa [mul_zero] at h0

def isSimple (S : Type*) [Semigroup S] : Prop := ∀ (I : Ideal' S), I = ∅ ∨ I = ⊤

def isZeroSimple (S : Type*) [SemigroupWithZero S] : Prop :=
  (∃ a b : S, a * b ≠ 0) ∧ ∀ (I : Ideal' S), I = ∅ ∨ (I : Set S) = ({0} : Set S) ∨ I = ⊤
end Ideal'

section zero_simple

variable (S : Type*) [SemigroupWithZero S]

/-- Notation for S² = { a * b | a b ∈ S }. -/
def Ssq : Set S := (Set.univ : Set S) * (Set.univ : Set S)

open Ideal'

/-- 1) `S^2` is a two-sided ideal (placeholder). -/
def Ssq_is_ideal : Ideal' S :=
{ carrier := Ssq S,
  mem_mul_mem := by
    intro x hx y
    -- unpack x ∈ Set.univ * Set.univ as x = a * b with a,b ∈ Set.univ
    rcases Set.mem_mul.1 hx with ⟨a, ⟨ha, ⟨b, ⟨hb, rfl⟩⟩⟩⟩
    -- show x * y ∈ Set.univ * Set.univ by giving witnesses `a` and `b * y`
    use a
    constructor
    · simp [ha]  -- a ∈ Set.univ
    use (b * y)
    constructor
    · simp
    · rw [mul_assoc]

  mul_mem_mem := by
    intro x hx y
    rcases Set.mem_mul.1 hx with ⟨a, ⟨ha, ⟨b, ⟨hb, rfl⟩⟩⟩⟩
    use (y * a)
    constructor; simp
    use b
    constructor; simp
    change (y * a) * b = y * (a * b)
    rw [mul_assoc]}


lemma Ssq_ne_singleton_zero_0simple (h : isZeroSimple S) : (Ssq S : Set S) ≠ ({0} : Set S) := by
  -- extract the existence of non-zero product from 0-simplicity
  rcases h with ⟨⟨a, b, hab_ne⟩, _⟩

  -- show a * b ∈ Ssq S
  have hab_in_Ssq : a * b ∈ (Ssq S) := by
    dsimp [Ssq]
    exact ⟨a, ⟨Set.mem_univ a, ⟨b, ⟨Set.mem_univ b, rfl⟩⟩⟩⟩

  -- if Ssq S = {0}, then a * b = 0, contradicting hab_ne
  intro h_eq
  rw [h_eq, Set.mem_singleton_iff] at hab_in_Ssq
  exact hab_ne hab_in_Ssq


theorem zero_simple_Ssq_eq_univ (h : isZeroSimple S) :
  (Ssq S : Set S) = Set.univ := by
  -- S^2 is an ideal
  let I : Ideal' S := Ssq_is_ideal S

  --  - prod_nonzero : ∃ a b, a * b ≠ 0 (equivalent to `S^2 ≠ {0}`)
  --  - h_prop : ∀ I, I = ∅ ∨ (I : Set S) = {0} ∨ I = ⊤
  rcases h with ⟨prod_nonzero, h_prop⟩
  rcases prod_nonzero with ⟨a, b, hab_ne⟩
  let s := a * b
  have hs_ne : s ≠ (0 : S) := hab_ne -- extract s ∈ S^2, s ≠ 0

  -- apply 0-simplicity to the ideal I
  have hI := h_prop I
  rcases hI with (heq_empty | heq_singleton | heq_top)

  -- Case I = ∅
  ·
    -- push the ideal-equality to sets
    apply_fun (fun (K : Ideal' S) => (K : Set S)) at heq_empty
    have Ssq_eq_empty : (Ssq S) = (∅ : Set S) := (rfl : (I : Set S) = Ssq S).symm.trans heq_empty

    -- show `s * 0 ∈ Ssq S` (Ssq is all products of two elements)
    have s0_in_Ssq : (s * (0 : S)) ∈ (Ssq S) := by
      dsimp [Ssq]
      exact ⟨s, ⟨Set.mem_univ s, ⟨0, ⟨Set.mem_univ (0 : S), rfl⟩⟩⟩⟩

    -- rewrite with `Ssq = ∅` to get contradiction
    rw [Ssq_eq_empty] at s0_in_Ssq
    simp at s0_in_Ssq

  -- Case (I : Set S) = {0}
  ·
    -- reconstruct the isZeroSimple hypothesis
    have h_reconstructed : isZeroSimple S := ⟨⟨a, b, hab_ne⟩, h_prop⟩
    exact False.elim (Ssq_ne_singleton_zero_0simple S h_reconstructed heq_singleton)

  -- Case I = ⊤ (what we want to show)
  ·
    -- push the equality `I = ⊤` to sets
    apply_fun (fun (K : Ideal' S) => (K : Set S)) at heq_top
    have Ssq_eq_univ : Ssq S = Set.univ :=
      (rfl : (I : Set S) = Ssq S).symm.trans (by simp [heq_top])
    exact Ssq_eq_univ




end zero_simple
