import MyProject.GreensRelations.morphisms

open MulOpposite

/- (the built-in notation for MulOpposite S is Sᵐᵒᵖ)-/

/- ### Basic properties of the reversed semigroup -/

/- Reversal of multiplication.  Where in the definition of
MulOpposite does this occur?  Yet it's there... somehow.-/

section Basic_Properties

variable {S : Type} [Semigroup S]

@[simp] lemma mul_reverse (s t : S) : op (s * t) = op t * op s := rfl


/- The reversed semigroup of a finite semigroup is finite. Must be very simple, but how do I prove it?-/
instance reverse_finite [Finite S] : Finite Sᵐᵒᵖ := by
  sorry

/- op preserves idempotents in a weak sense; see below for
the 'strong' sense-/

@[simp]
lemma op_idem' (e : S) (idem : IsIdempotentElem e) : IsIdempotentElem (op e) := by
  unfold IsIdempotentElem at *
  rw [← mul_reverse, idem]

/- op∘op is an isomorphism-/
def op_op_isom : S ≃* (Sᵐᵒᵖ)ᵐᵒᵖ where
  toFun := op ∘ op
  invFun := unop ∘ unop
  left_inv := by
    unfold Function.LeftInverse
    unfold Function.comp
    simp
  right_inv := by
    intro x
    unfold Function.comp
    simp
  map_mul' := by
    intro s t
    apply mul_reverse


/- op preserves idempotents in the strong sense  -/
@[simp]
lemma op_idem (e : S): IsIdempotentElem e ↔ IsIdempotentElem (op e) := by
  constructor
  · intro idem
    apply op_idem' e idem
  · intro idem
    apply op_idem' (op e) at idem
    rw [idempotent_iso_preserved (@op_op_isom S _) e]
    assumption

end Basic_Properties

/-! ## Duality of 𝓡 and 𝓛 orders

These two lemmas say that the 𝓡 order in a semigroup is the same as the 𝓛 order in the reversed
semigroup, and vice-versa. We use the results above about isomorphisms to derive the second result
in a very direct manner from the first.
-/

section Duality

variable {S : Type} [Semigroup S] (a b : S)

lemma op_op_L : a ≤𝓛 b ↔ op (op a) ≤𝓛 op (op b) := L_order_iso_stable S (Sᵐᵒᵖ)ᵐᵒᵖ op_op_isom a b

lemma op_op_R : a ≤𝓡 b ↔ op (op a) ≤𝓡 op (op b) := R_order_iso_stable S (Sᵐᵒᵖ)ᵐᵒᵖ (op_op_isom) a b

lemma L_preorder_iff_R_preorder_op : a ≤𝓛 b ↔ (op a) ≤𝓡 (op b) := by
  rw [R_preorder_iff_without_one, L_preorder_iff_without_one]
  constructor
  · rintro (heq | ⟨x, hx⟩)
    · left; congr
    · right; use op x; congr
  · rintro (heq | ⟨x, hx⟩)
    · left; rwa [← op_inj]
    · right; use unop x; rw [← op_inj, hx, mul_reverse, op_unop]

lemma R_preorder_iff_L_preorder_op : a ≤𝓡 b ↔ (op a) ≤𝓛 (op b) := by
  simp [op_op_R a b]
  simp [(L_preorder_iff_R_preorder_op (op a) (op b))]

lemma L_equiv_iff_R_equiv_op : a 𝓛 b ↔ (op a) 𝓡 (op b) := by
  simp [R_eqv, L_eqv]
  simp [L_preorder_iff_R_preorder_op]

lemma R_equiv_iff_L_equiv_op :a 𝓡 b ↔ (op a) 𝓛 (op b) := by
  simp [R_eqv, L_eqv]
  simp [R_preorder_iff_L_preorder_op]

end Duality

section Example

variable {S : Type} [Semigroup S] (a e : S)

/- Example of use : Here is a re-proof of
a theorem from Basics.  We will then apply it along with the duality principles established
above to obtain a brief proof of the dual version.-/

theorem le_R_idempotent_rehash (h : IsIdempotentElem e) : (a ≤𝓡 e) ↔ (a = e * a) := by
  rw [R_preorder_iff_without_one]
  constructor
  ·intro h
   cases' h with eq neq
   · rw [eq, h]
   · cases' neq with x h'
     have k : e * a = a := by
      rw [h',<-mul_assoc, h]
     exact Eq.symm k
  · intro aea
    have k' : ∃ x, a = e * x := by use a
    exact Or.intro_right _ k'
variable (S : Type)[Semigroup S]

theorem le_L_idempotent_rehash (h: IsIdempotentElem e) : (a ≤𝓛 e) ↔ (a = a * e) := by
  simp [L_preorder_iff_R_preorder_op]
  rw [le_R_idempotent_rehash, ← mul_reverse a e]
  exact op_inj; exact op_idem' e h

/- Stuff that was not used in the code above.
/- # Definitions and Instances related to S¹-compatibility with MulOpposite-/

instance MulOpposite.Monoid : Monoid (MulOpposite (S¹)) :=
  by infer_instance

/- HS. These next lemmas could be useful.
They basically say that `op` is an
involution ; i.e, that `op (op s) = s`.
However in Lean `op (op s)` lives in
a different type from s, so we have
to state things differently. -/

def is_antihomomorphism {T₁ T₂ : Type} [Semigroup T₁][Semigroup T₂](f : T₁ → T₂):Prop := ∀ t t' : T₁,
f (t * t') = (f t') * (f t)

/- if you compose two antihomomorphisms you get a homomorphism-/

lemma anti_anti {T₁ T₂ T₃: Type} [Semigroup T₁][Semigroup T₂][Semigroup T₃](f : T₁ → T₂)(g : T₂ → T₃)(isantif : is_antihomomorphism f)(isantig : is_antihomomorphism g)(t t': T₁) : f ( g (t * t')) = f (g t) * f (g t') := sorry

lemma op_op (s : S) : unop (unop (op (op s))) = s := by
  have h₁: unop (op (op s)) = op s := rfl
  calc
    unop (unop (op (op s))) = unop (op s) := by rw [h₁]
    _ = s := rfl

lemma op_involution (s t : S):
op (op s) = op (op t) ↔ s = t := by
  constructor
  · intro h
    have h₂: unop (unop (op (op s))) =  unop (unop (op (op t))) := by
      apply congrArg unop
      apply congrArg unop
      exact h
    rw [op_op,op_op] at h₂
    exact h₂
  · intro h
    apply congrArg op
    apply congrArg op
    exact h


/- op op is a homomorphism -/
lemma op_op_morphism (s t : S):
  op (op (s * t)) = op (op s) * (op (op t)) :=
  by
    calc
      op (op (s * t)) = op ((op t) * (op s)) := rfl
      _ = op (op s) * op (op t) := rfl

/- unop unop is a homomorphism -/
lemma unop_unop_morphism (s t : (MulOpposite (MulOpposite S))):
  unop (unop (s * t)) = unop (unop s) * (unop (unop t)) :=
  by
    have h₁: op (op (unop (unop (s * t)))) = s *t :=
    calc
      op (op (unop (unop (s * t)))) = op (unop (s * t)) := rfl
      _ = s * t := rfl
    sorry

def opop_hom : sg_morph S (MulOpposite (MulOpposite S)) :=
{
  f := sorry
  multiplicative := sorry
}

def unopunop_hom : sg_morph  (MulOpposite (MulOpposite S)) S :=
{
  f := sorry
  multiplicative := sorry
}

def opop_iso : sg_isomorph S (MulOpposite (MulOpposite S))
 :=
{
  h := opop_hom
  hinv := unopunop_hom
  rightinv := sorry
  leftinv := sorry

}

/- HS. do we need this next one ? -/
def WithOneMulOppositeEquiv (S : Type*) :
    (Sᵐᵒᵖ)¹ ≃ (S¹)ᵐᵒᵖ :=
  {toFun := λ x =>
    match x with
      | none => op none
      | some a => op (some a.unop),
   invFun := λ x => match unop x with
    | none => none
    | some a => some (op a),
   left_inv := by
      intro x
      cases x
      simp[op, unop]; rfl
      dsimp; rfl
   right_inv := by
      intro x
      refine unop_inj.mp ?_
      simp only [Function.comp_apply]
      simp only [unop, op]
      cases x.unop' with
      | one => simp; rfl
      | coe => rfl
  }

/- # Lemmas establishing basic facts about relationship between Green's relations on S and Sᵐᵒᵖ
(From playing around with examples/trying to use Sᵐᵒᵖ in proofs, to make using this method
efficient, we'd need to write a pretty larger number of such lemmas for basic facts about
finite semigroups.)-/

lemma L_preorder_iff_R_preorder_op (a b : S) :
    a ≤𝓛 b ↔ (op a) ≤𝓡 (op b) := by
  rw[R_preorder_iff_without_one, L_preorder_iff_without_one]
  constructor
  · intro hu
    cases' hu with hp hq
    · exact Or.symm (Or.inr (congrArg op (hp)))
    . obtain ⟨x, hx⟩ := hq
      refine Or.symm (Or.intro_left (op a = op b) ?_)
      use op x
      exact congrArg op hx
  · intro hv
    cases' hv with hp hq
    · exact Or.symm (Or.inr (congrArg unop (hp)))
    · obtain ⟨x, hx⟩ := hq
      refine Or.symm (Or.intro_left (a = b) ?_)
      use unop x
      exact congrArg unop hx

lemma L_preorder_op_iff_R_preorder (a b : S) :
    (op a) ≤𝓛 (op b) ↔ (a) ≤𝓡 (b) := by
  rw[R_preorder_iff_without_one, L_preorder_iff_without_one]
  constructor
  · intro hu
    cases' hu with hp hq
    · exact Or.symm (Or.inr (congrArg unop (hp)))
    . obtain ⟨x, hx⟩ := hq
      refine Or.symm (Or.intro_left (a = b) ?_)
      use unop x
      exact congrArg unop hx
  · intro hv
    cases' hv with hp hq
    · exact Or.symm (Or.inr (congrArg op (hp)))
    · obtain ⟨x, hx⟩ := hq
      refine Or.symm (Or.intro_left (op a = op b) ?_)
      use op x
      exact congrArg op hx

lemma L_eqv_iff_R_eqv_op (a b : S) :
    a 𝓛 b ↔ op a 𝓡 op b := by
  unfold L_eqv R_eqv
  simp[L_preorder_iff_R_preorder_op a b, L_preorder_iff_R_preorder_op b a]

lemma L_eqv_op_iff_R_eqv (a b : S) :
    (op a) 𝓛 (op b) ↔ a 𝓡 b := by
  unfold L_eqv R_eqv
  simp[L_preorder_op_iff_R_preorder a b, L_preorder_op_iff_R_preorder b a]


/--# Example of use

Using `le_R_idempotent`-- proved in Basic as follows-- we provide an alternate proof of
`le_L_idempotent`, where we switch to the opposite semigroup Sᵐᵒᵖ and apply `le_R_idempotent`.

I believe most of the work in using this method is always in establishing that the natural analogs
of the hypotheses of the original theorem hold in the opposite semigroup (ex. for `le_L_idempotent`,
showing `h_op`). For more complicated statements, especially when dealing with coercions between S
and S¹ as well as from S to Sᵐᵒᵖ, this was not always easy (for me, at least)-- I tried doing so
for some of the Green's lemma proofs with limited success. --/

/- this is the original `le_R_idempotent`:-/
theorem le_R_idempotent_rehash (h: IsIdempotentElem e) : (a ≤𝓡 e) ↔ (a = e * a) := by
  constructor
  · rintro ⟨u, hru⟩
    unfold IsIdempotentElem at h
    rw [<-WithOne.coe_inj, WithOne.coe_mul] at h ⊢
    rw [hru, ← mul_assoc, h ]
  · intro hl; use a
    rw[<-WithOne.coe_inj] at hl; exact hl

/- an alternate proof of `le_L_idempotent` using `le_R_idempotent` in the opposite semigroup.-/
lemma le_L_idempotent_alt (h : IsIdempotentElem e) : a ≤𝓛 e ↔ a = a * e := by
  have h_op : IsIdempotentElem (op e) := by
    unfold IsIdempotentElem at *
    rw [← op_inj, op_mul] at h; exact h
  have : op a ≤𝓡 op e ↔ op a = op e * op a := le_R_idempotent_rehash (op a) (op e) h_op
  simp[L_preorder_iff_R_preorder_op, this]
  exact ⟨congrArg unop, congrArg op⟩
-/

/- some baggage about antihomomorphisms
and antiisomorphisms that I did not use-/

/-!
  ## Anti-homomorphism and anti-isomorphism

Try to eliminate this baggage about antihomomorphisms
and cut to the chase. So ignore this section.
-/

/- definition of antihomomorphism-/
structure AntiHom ( S T : Type)[Semigroup S][Semigroup T] where
  toFun : S → T
  map_mul : ∀ s s' : S, toFun (s * s') = (toFun s') * (toFun s)

/-anti homomorphisms preserve idempotents-/
lemma anti_hom_idempotent(S T:Type)[Semigroup S][Semigroup T](h : AntiHom S T)(e : S)(id : IsIdempotentElem e) : IsIdempotentElem (h.toFun e) := by
  unfold IsIdempotentElem at *
  rw [<-h.map_mul e e, id]

/- `op` is an antihomomorphism -/

def op_anti_hom (S : Type ) [Semigroup S] : AntiHom S Sᵐᵒᵖ  where
  toFun := op
  map_mul := by
    intros s s'
    rfl


/- op preserves idempotents in a weak sense (see below for the 'strong' sense)-/
lemma op_idempotent' (S : Type)[Semigroup S]
(e : S)(id : IsIdempotentElem e) : IsIdempotentElem (op e) :=
anti_hom_idempotent S Sᵐᵒᵖ (op_anti_hom S) e id

structure  AntiIso (S T : Type )[Semigroup S][Semigroup T]  extends S ≃ T, AntiHom S T

def op_anti_iso (S : Type) [Semigroup S] : AntiIso S Sᵐᵒᵖ where
  toFun := op
  invFun := unop
  left_inv := by
    unfold Function.LeftInverse
    intro x
    rfl
  right_inv :=  by
    unfold Function.RightInverse
    intro x
    rfl
  map_mul := (op_anti_hom S).map_mul


/- The composition of two antihomormorphisms
is a morphism.-/

def  antihom_comp (S T U : Type )[Semigroup S][Semigroup T][Semigroup U](ahst: AntiHom S T)
(ahtu: AntiHom T U) : S →ₙ* U where
  toFun := ahtu.toFun ∘ ahst.toFun
  map_mul' := by
    intro x y
    calc
      (ahtu.toFun ∘ ahst.toFun) (x * y) =
        ahtu.toFun (ahst.toFun (x * y)) := rfl
      _ = ahtu.toFun ((ahst.toFun y) * (ahst.toFun x)) := by rw [ahst.map_mul ]
      _ = (ahtu.toFun (ahst.toFun x)) * (ahtu.toFun (ahst.toFun y)) := by rw [ahtu.map_mul]
      _ = ((ahtu.toFun ∘ ahst.toFun) x) * ((ahtu.toFun ∘ ahst.toFun) y) := rfl
/-
  The composition of two anti-isomorphisms is an isomorphism -/

def  anti_iso_comp (S T U : Type)[Semigroup S][Semigroup T][Semigroup U](ahst: AntiIso S T)
(ahtu: AntiIso T U) : S ≃* U where
  toFun := ahtu.toFun ∘ ahst.toFun
  invFun := ahst.invFun ∘ ahtu.invFun
  left_inv := by
    unfold Function.LeftInverse
    unfold Function.comp
    simp
  right_inv := by
    intro x
    unfold Function.comp
    simp
  map_mul' := (antihom_comp S T U (AntiIso.toAntiHom ahst) (AntiIso.toAntiHom ahtu)).map_mul'

def op_op_iso (S : Type) [Semigroup S]: S ≃* (Sᵐᵒᵖ)ᵐᵒᵖ := anti_iso_comp S (Sᵐᵒᵖ) ((Sᵐᵒᵖ)ᵐᵒᵖ)  (op_anti_iso S ) (op_anti_iso Sᵐᵒᵖ )

/- op preserves idempotents in a strong sense -/
lemma op_idempotent (S : Type)[Semigroup S]
(e : S): IsIdempotentElem e ↔ IsIdempotentElem (op e) := by
  constructor
  · intro id
    exact op_idempotent' S e id
  · intro idop
    rw [idempotent_iso_preserved (op_op_iso S) e]
    have h : op_op_iso S e = op (op e):= rfl
    rw [h]
    exact op_idempotent' Sᵐᵒᵖ (op e) idop
