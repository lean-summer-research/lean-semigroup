import MyProject.WithOne


/-!
# Green's Relations in Finite Semigroups

This file defines Green's relations in finite semigroups and establishes their basic properties.
Green's relations are the R, L, J and H - preorders and the equivalence relations induced by these orders.

## Main Definitions


## Implementation Notes

The preorders on a semigroup S are defined via equations in the monoid S¹ obtained by adjoining an identity to S; the S¹ construction is defined in tje file `WithOne.lean`.

The associated equivalence relations are obtained by applying a general procedure for passing from a preorder `≤` to the equivalence relation `≅` defined by `a ≅ b` if and only if `a ≤ b` and `b ≤ a`.


This file imports `PnatPow.lean` (and thereby `WithOne.lean`), and is imported by
`GreensRelations.lean`.

## References

The `Idempotence` file uses the `IsIdempotentElem` predicate defined in `Mathlib.Algebra.Group.Idempotent`.
-/



/-

### Defining an equivalence relation from a preorder -/

def equiv_from_preorder {α : Type }(p: Preorder α) (a b :α) :=
  (p.le a b) ∧ (p.le b a)

/-! Establish reflexivity, symmetry and transitivity properties  for the equivalence relation. -/

lemma equiv_from_preorder_refl {α : Type }(p: Preorder α) :
   Reflexive (equiv_from_preorder p) := by
   intro a
   constructor
   · apply  le_refl
   · apply  le_refl



lemma equiv_from_preorder_symm {α : Type }(p: Preorder α) :
  Symmetric  (equiv_from_preorder p ) := by
    intros a b h
    exact  And.intro h.right h.left


lemma equiv_from_preorder_trans {α : Type }(p: Preorder α) :
  Transitive  (equiv_from_preorder p ) := by
  intros a b c h₁ h₂
  constructor
  · exact le_trans h₁.left h₂.left
  · exact le_trans h₂.right h₁.right

/-! A setoid is a structure carrying an equivalence
relation.-/

instance setoid_from_preorder {α : Type } [p : Preorder α] : Setoid α where
  r := equiv_from_preorder p
  iseqv :=  ⟨equiv_from_preorder_refl p, @equiv_from_preorder_symm α p,@equiv_from_preorder_trans α p⟩

/-!

### The 𝓡 preorder -/

/-! Definition of the order, by lifting to `S¹`.-/
@[simp]
def R_le {S : Type} [Semigroup S ](s t : S) :=  (∃ u : S¹, ↑s = ↑ t * u)


lemma R_le_refl {S : Type} [Semigroup S ] (s : S ) : R_le s s := by
  use (1 : S¹)
  rfl

lemma R_le_trans {S : Type} [Semigroup S ](s t u : S) (slet : R_le s t)(tleu :   R_le t u) :   R_le s u  := by
  obtain ⟨v,h₁⟩ := slet
  obtain ⟨w,h₂⟩ := tleu
  use w * v
  rw [h₁,h₂,mul_assoc]



instance ROrder {S : Type} [Semigroup S ]: Preorder S where
  le := R_le
  le_refl := R_le_refl
  le_trans := R_le_trans


/-! Standard notation for the 𝓡 - order.  -/
notation:50 f " ≤ᵣ " g:50 => ROrder.le f g
notation:50 f " <ᵣ " g:50 => ROrder.lt f g

/-! An alternative definition for the 𝓡 order in a finite semigroup does not involve the lifting to S¹ but 'lives in' `S`. This can be useful in calculations. Here we define the alternative and prove equivalence. -/

def R_le_alt {S : Type} [Semigroup S ](s t : S) :=  (∃ u : S, s = t * u) ∨ s = t

/- Proof that the two definitions are equivalent.
-/
lemma R_le_alt_Rle {S : Type} [Semigroup S ](s t : S): s ≤ᵣ t ↔ R_le_alt s t := by
  constructor
  · intro slet_mon
    cases' slet_mon with u rbelow
    by_cases h : u = (1: (WithOne S))
    · have seqt  : s = t := by
        rw [h, mul_one] at rbelow
        exact WithOne.coe_inj.mp rbelow

      exact Or.intro_right _ seqt
    · have rightmultiplier : ∃ v : S, ↑v = u := by
        use WithOne.unone h
        exact WithOne.coe_unone h
      cases' rightmultiplier with v tliftv
      have seqtv : s = t * v := by
        rw [<-tliftv] at rbelow
        exact WithOne.coe_inj.mp rbelow
      exact Or.intro_left _ (Exists.intro v seqtv)

  · intro slet_sg
    cases' slet_sg with neq eq
    · cases' neq with u stu
      use ↑u
      have coestu : WithOne.coe s = WithOne.coe t * WithOne.coe u :=
        calc
          WithOne.coe s = WithOne.coe (t * u) := by rw [stu]
          _ = WithOne.coe t * WithOne.coe u := rfl
      exact coestu
    · rw [eq]

/- A handy immediate consequence: -/
lemma R_le_alt_implies_R_le {S : Type} [Semigroup S ](s t : S)(h : ∃ u : S, s = t * u) : s ≤ᵣ t := by
  apply (R_le_alt_Rle s t).mpr
  exact Or.intro_left _ h





/-! #### A running example

 -/

def Threemap : Type := Fin 3 → Fin 3
deriving DecidableEq, Fintype, Inhabited
/- what does Inhabited do ? -/

namespace Threemap

instance : Semigroup Threemap where
  mul := fun a b => b ∘ a
  mul_assoc := by intros a b c; rfl


def f_id : Threemap := ![0, 1, 2]
def f_120 : Threemap := ![1, 2, 0]
def f_110 : Threemap := ![1, 1, 0]
def f_202 : Threemap := ![2, 0, 2]
def f_121 : Threemap := ![1, 2, 1]
def f_112 : Threemap := ![1, 1, 2]
def f_221 : Threemap := ![2, 2, 1]
def f_220 : Threemap := ![2, 2, 0]
def f_212 : Threemap := ![2, 1, 2]
def f_022 : Threemap := ![0,2, 2]
def f_000 : Threemap := ![0, 0, 0]

#eval f_202 * f_221
#eval f_110 * f_121

lemma Rex1  : f_220 = f_120 * f_022 := by decide
lemma Rex2 : f_220 = f_112 * f_220 := by decide
lemma Rex3 : f_112 = f_220 * f_221 := by decide

example : f_220 ≤ᵣ f_120 := by
  have h : ∃ s : Threemap, f_220 = f_120 * s := by
    use f_022
    exact Rex1
  exact R_le_alt_implies_R_le f_220 f_120 h

lemma Rex4 : f_220 ≤ᵣ f_112 := by
  have h : ∃ s : Threemap, f_220 = f_112 * s := by
    use f_220
    exact Rex2
  exact R_le_alt_implies_R_le f_220 f_112 h

lemma Rex5 : f_112 ≤ᵣ f_220 := by
   have h : ∃ s : Threemap, f_112 = f_220 * s := by
    use f_221
    exact Rex3
   exact R_le_alt_implies_R_le f_112 f_220 h



end Threemap

/-! ### 𝓡 - equivalence

Now define R equivalence using the tool above for constructing equivalence relations from preorders. -/

instance REq  {S : Type}[Semigroup S] : Setoid S :=
  @setoid_from_preorder S ROrder

/-! Notation for the R equivalence relation. -/

notation:50 f " ≡ᵣ " g:50 => REq.r f g

/-! Definition of the 𝓡-class of an element.
This uses the general apparatus in Lean, so
an equivalence class is a type.-/


/-- The 𝓡‑class of `a`  -/

def R_class {S : Type} [Semigroup S](a : S) : @Quot S ⇑REq   := @Quot.mk S REq.r a

/-! R-class notation: typed \[[ f \]]\_r  -/
notation "⟦" f "⟧ᵣ" => R_class f




/-! ### Running example continued -/

namespace Threemap
lemma Rex6 : f_112 ≡ᵣ f_220 := by
  constructor
  · apply Rex5
  · apply Rex4

lemma Rex7 : ⟦f_112⟧ᵣ = ⟦f_220⟧ᵣ := by
  apply Quot.sound Rex6




end Threemap

/-!
### The 𝓛 preorder -/

/-! Definition of the order, by lifting to `S¹`.-/
@[simp]
def L_le {S : Type} [Semigroup S ](s t : S) :=  (∃ u : S¹, ↑s = u * ↑ t )


lemma L_le_refl {S : Type} [Semigroup S ] (s : S ) : L_le s s := by
  use (1 : S¹)
  rfl

lemma L_le_trans {S : Type} [Semigroup S ](s t u : S) (slet : L_le s t)(tleu :   L_le t u) :   L_le s u  := by
  obtain ⟨v,h₁⟩ := slet
  obtain ⟨w,h₂⟩ := tleu
  use v * w
  rw [h₁,h₂,mul_assoc]


/-HS. comment  LOrder as an instance of preorder. Interesting
that this did required explicit definition of the
lt field, which was not needed in the definition of
the 𝓡 order . -/

instance LOrder {S : Type} [Semigroup S ]: Preorder S where
  le := L_le
  le_refl := L_le_refl
  le_trans := L_le_trans
  lt := fun a b => (L_le a b) ∧ ¬(L_le b a)



/-! Standard notation for the 𝓛 - order.  -/
notation:50 f "  ≤ₗ  " g:50 => LOrder.le f g
notation:50 f "  <ₗ  " g:50 => LOrder.lt f g

/-! An alternative definition for the 𝓛 order in a finite semigroup does not involve the lifting to S¹ but 'lives in' `S`. This can be useful in calculations. Here we define the alternative and prove equivalence. -/

def L_le_alt {S : Type} [Semigroup S ](s t : S) :=  (∃ u : S, s = u * t) ∨ s = t

/- Proof that the two definitions are equivalent.
-/
lemma L_le_alt_Lle {S : Type} [Semigroup S ](s t : S): s ≤ₗ t ↔ L_le_alt s t := by
  constructor
  · intro slet_mon
    cases' slet_mon with u lbelow
    by_cases h : u = (1: (WithOne S))
    · have seqt  : s = t := by
        rw [h, one_mul] at lbelow
        exact WithOne.coe_inj.mp lbelow

      exact Or.intro_right _ seqt
    · have leftmultiplier : ∃ v : S, ↑v = u := by
        use WithOne.unone h
        exact WithOne.coe_unone h
      cases' leftmultiplier with v tliftv
      have seqtv : s = v * t := by
        rw [<-tliftv] at lbelow
        exact WithOne.coe_inj.mp lbelow
      exact Or.intro_left _ (Exists.intro v seqtv)

  · intro slet_sg
    cases' slet_sg with neq eq
    · cases' neq with u stu
      use ↑u
      have coestu : WithOne.coe s = WithOne.coe u * WithOne.coe t :=
        calc
          WithOne.coe s = WithOne.coe (u * t) := by rw [stu]
          _ = WithOne.coe u * WithOne.coe t := rfl
      exact coestu
    · rw [eq]

/- A handy immediate consequence: -/
lemma L_le_alt_implies_L_le {S : Type} [Semigroup S ](s t : S)(h : ∃ u : S, s = u * t) : s ≤ₗ t := by
  apply (L_le_alt_Lle s t).mpr
  exact Or.intro_left _ h



/- How do we use decidability? -/



/-! #### A running example continued

 -/


namespace Threemap

lemma Rex8 : f_202 * f_221 = f_121 := by decide
lemma Rex9 : f_110 * f_121 = f_221 := by decide

lemma Rex10 : f_121 ≤ₗ f_221 := by
  apply L_le_alt_implies_L_le
  use f_202
  exact Eq.symm Rex8

lemma Rex11 : f_221 ≤ₗ f_121 := by
  apply L_le_alt_implies_L_le
  use f_110
  exact Eq.symm Rex9


end Threemap

/-! ### 𝓛 - equivalence

Now define L equivalence using the tool above for constructing equivalence relations from preorders. -/

instance LEq  {S : Type}[Semigroup S] : Setoid S :=
  @setoid_from_preorder S LOrder

/-! Notation for the L equivalence relation. -/

notation:50 f " ≡ₗ " g:50 => LEq.r f g

/-! Definition of the 𝓛-class of an element.
This uses the general apparatus in Lean, so
an equivalence class is a type.-/


/-- The 𝓛‑class of `a`  -/

def L_class {S : Type} [Semigroup S](a : S) : @Quot S ⇑LEq   := @Quot.mk S LEq.r a

/-! L-class notation: typed \[[ f \]]\_r  -/
notation "⟦" f "⟧ₗ" => L_class f

namespace Threemap
lemma Rex12 : f_221 ≡ₗ f_121 := by
  constructor
  · apply Rex11
  · apply Rex10

lemma Rex13 : ⟦f_221⟧ₗ = ⟦f_121⟧ₗ := by
  apply Quot.sound Rex12



end Threemap



/-! ### The 𝓙 preorder-/

/-! Definition of the order, by lifting to `S¹`.-/
@[simp]
def J_le {S : Type} [Semigroup S ](s t : S) :=  (∃ u v : S¹, ↑s = u * ↑ t * v)

lemma J_le_refl {S : Type} [Semigroup S ] (s : S ) : J_le s s := by
  use (1 : S¹),(1 : S¹)
  rfl

lemma J_le_trans {S : Type} [Semigroup S ](s t u : S) (slet : J_le s t)(tleu : J_le t u) : J_le s u:= by
   obtain ⟨ x₁,y₁, p₁ ⟩  := slet
   obtain ⟨ x₂, y₂, p₂ ⟩ := tleu
   use x₁ * x₂, y₂ * y₁
   rw [p₁]
   rw [p₂]
   rw [mul_assoc x₂ ↑u y₂]
   rw [<-mul_assoc ]
   rw [<-mul_assoc ]
   rw [<-mul_assoc ]

instance JOrder {S : Type} [Semigroup S ]: Preorder S where
  le := J_le
  le_refl := J_le_refl
  le_trans := J_le_trans
  lt := fun a b => (J_le a b) ∧ ¬(J_le b a)

/-! Standard notation for the 𝓙 - order.  -/
notation:50 f " ≤ⱼ " g:50 => JOrder.le f g
notation:50 f " <ⱼ " g:50 => JOrder.lt f g

/- A couple of useful lemmas linking the 𝓡 and 𝓛 orders to the 𝓙 order -/

lemma R_below_implies_J_below {S : Type} [Semigroup S ](s t : S)(slet : s ≤ᵣ t) : s ≤ⱼ t := by
  obtain ⟨u,p⟩ := slet
  use (1 :WithOne S),u
  rw [one_mul,p]

lemma L_below_implies_J_below {S : Type} [Semigroup S ](s t : S)(slet : s ≤ₗ t) : s ≤ⱼ t := by
  obtain ⟨u,p⟩ := slet
  use u, (1 :WithOne S)
  rw [p,mul_one]

/-! ### 𝓙 - equivalence

Now define J equivalence using the tool above for constructing equivalence relations from preorders. -/

instance JEq  {S : Type}[Semigroup S] : Setoid S :=
  @setoid_from_preorder S JOrder

/-! Notation for the J equivalence relation. -/

notation:50 f " ≡ⱼ " g:50 => JEq.r f g

lemma R_equiv_implies_J_equiv {S : Type} [Semigroup S ](s t : S)(seqvt : s ≡ᵣ t) : s ≡ⱼ t := by
  obtain ⟨slet,tles⟩ := seqvt
  constructor
  · apply R_below_implies_J_below s t slet
  · apply R_below_implies_J_below t s tles


lemma L_equiv_implies_J_equiv {S : Type} [Semigroup S ](s t : S)(seqvt : s ≡ₗ t) : s ≡ⱼ t := by
  obtain ⟨slet,tles⟩ := seqvt
  constructor
  · apply L_below_implies_J_below s t slet
  · apply L_below_implies_J_below t s tles





/-! Definition of the 𝓙-class of an element.
This uses the general apparatus in Lean, so
an equivalence class is a type.-/


/-- The 𝓙‑class of `a`  -/

def J_class {S : Type} [Semigroup S](a : S) : @Quot S ⇑JEq   := @Quot.mk S JEq.r a

/-! J-class notation: typed \[[ f \]]\_r  -/
notation "⟦" f "⟧ⱼ" => J_class f

/-! ### The 𝓗 preorder-/

/-! Definition of the order, by lifting to `S¹`.-/
@[simp]
def H_le {S : Type} [Semigroup S ](s t : S) :=  (s ≤ᵣ t) ∧ (s ≤ₗ t)

lemma H_le_refl {S : Type} [Semigroup S ] (s : S ) : H_le s s := by
  constructor
  · apply R_le_refl
  · apply L_le_refl

lemma H_le_trans {S : Type} [Semigroup S ](s t u : S) (slet : H_le s t)(tleu : H_le t u) : H_le s u:= by
  constructor
  · apply R_le_trans s t u slet.left tleu.left
  · apply L_le_trans s t u slet.right tleu.right

instance HOrder {S : Type} [Semigroup S ]: Preorder S where
  le := H_le
  le_refl := H_le_refl
  le_trans := H_le_trans
  lt := fun a b => (H_le a b) ∧ ¬(H_le b a)

/-! Standard notation for the 𝓙 - order.  -/
notation:50 f " ≤ₕ " g:50 => HOrder.le f g
notation:50 f " <ₕ " g:50 => HOrder.lt f g

/-! ### 𝓗 - equivalence

Now define H equivalence using the tool above for constructing equivalence relations from preorders.

The name HEq introduces a name conflict, so I have HEquiv, but perhaps this should all be done in a namespace -/

instance HEquiv  {S : Type}[Semigroup S] : Setoid S :=
  @setoid_from_preorder S HOrder

/-! Notation for the H equivalence relation. -/

notation:50 f " ≡ₕ " g:50 => HEquiv.r f g

/-!  ### Decidability of Green's relations

Equality is decidable in `T¹` if it is decidable in T. But why do we need the two-step process below? (If we eliminate option_decide and just try to use infer_instance on T¹ directly, it doesn't work!) -/
instance option_decide {T : Type }[DecidableEq  T]:DecidableEq (Option T) := by
  infer_instance

instance {T : Type} [DecidableEq T] : DecidableEq (T¹  ) := option_decide

/- Decidability of the ordering relations, but again,
why does this require a two-step process? -/

instance le_R_decidable_ {S : Type}[Semigroup S][Fintype S] [DecidableEq S] (a b : S) :
    Decidable (R_le a b) := by
      simp
      infer_instance





instance le_R_decidable  {S : Type}[Semigroup S][Fintype S] [DecidableEq S] (a b : S) :
    Decidable (a ≤ᵣ b) := by
      apply le_R_decidable_


instance le_L_decidable_ {S : Type}[Semigroup S][Fintype S] [DecidableEq S] (a b : S) :
    Decidable (L_le a b) := by
      simp
      infer_instance

instance le_L_decidable  {S : Type}[Semigroup S][Fintype S] [DecidableEq S] (a b : S) :
    Decidable (a ≤ₗ b) := by
      apply le_L_decidable_

instance le_J_decidable_ {S : Type}[Semigroup S][Fintype S] [DecidableEq S] (a b : S) :
    Decidable (J_le a b) := by
      simp
      infer_instance

instance le_J_decidable  {S : Type}[Semigroup S][Fintype S] [DecidableEq S] (a b : S) :
    Decidable (a ≤ⱼ b) := by
      apply le_J_decidable_

instance le_H_decidable_ {S : Type}[Semigroup S][Fintype S] [DecidableEq S] (a b : S) :
    Decidable (H_le a b) := by
      simp
      infer_instance

instance le_H_decidable  {S : Type}[Semigroup S][Fintype S] [DecidableEq S] (a b : S) :
    Decidable (a ≤ₕ  b) := by
      apply le_H_decidable_

/- If a preorder is decidable, then the equivalence relation derived from the preorder is decidable.-/
instance equiv_from_preorder_decidable {α : Type }(p: Preorder α)(h: ∀ a b :α, Decidable (p.le a b))(x y: α) : Decidable ((equiv_from_preorder p) x y)  := by
  exact instDecidableAnd

instance eq_R_decidable {S : Type}[Semigroup S][Fintype S] [DecidableEq S] (a b : S) : Decidable (a ≡ᵣ b) := by
  apply equiv_from_preorder_decidable
  apply le_R_decidable

instance eq_L_decidable {S : Type}[Semigroup S][Fintype S] [DecidableEq S] (a b : S) : Decidable (a ≡ₗ  b) := by
  apply equiv_from_preorder_decidable
  apply le_L_decidable

instance eq_J_decidable {S : Type}[Semigroup S][Fintype S] [DecidableEq S] (a b : S) : Decidable (a ≡ⱼ b) := by
  apply equiv_from_preorder_decidable
  apply le_J_decidable

instance eq_H_decidable {S : Type}[Semigroup S][Fintype S] [DecidableEq S] (a b : S) : Decidable (a ≡ₕ b) := by
  apply equiv_from_preorder_decidable
  apply le_H_decidable
