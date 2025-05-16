import Mathlib

set_option linter.unusedVariables false

/-!
Questions: Nice notation for S¹?
Nice notation for ≅J, for instance.

arranging imports and namespaces

general associativity tactic--does it exist?  It should because
we have ring which does something more complicated. For instance
we should be able to show

(a * (b * c)) * (d * e) = a * (b * (c * (d * e)))

in a single step.

## Existence of idempotent powers in a finite semigroup

The goal is to prove  that in a finite semigroup S, if x ∈ S then there is
a unique element xⁿ where n > 0 such that x^n is idempotent. Note that it is the element xⁿ  that is unique, not the integer n, since if xⁿ is idempotent, then so is xᵏⁿ  for any positive integer k.

### Sketch of the mathematical proof

Before trying to represent this in Lean, we want to be sure that we understand a standard pencil-and-paper proof: Given x ∈ S, we enumerate the powers

x,x²,x³,

etc. By finiteness, this sequence contains a repeat---that is, integers 0 < i < j such that

xⁱ = xʲ

Thus the values of xⁿ eventually cycle, and the integer j - i is a multiple of the length of the cycle.  (The 'cycle' could have length 1.) It is then easy to show by induction on k that if t ≥ i and k is any natural number,  then x ^ (t + k * (j-i)) = x ^ t. This readily implies that xʳ is idempotent, where

r = i ⬝ (j - i)

Uniqueness of the idempotent power follows from a very simple argument:  If xʳ = xˢ are both idempotent,  then

xʳ = (xʳ)ˢ = xʳˢ = xˢʳ = (xˢ)ʳ = xˢ

### The monoids-first strategy

There were more tools available in Lean for working directly with monoids rather than semigroups, so we first stated and proved the theorem for monoids, then generalized to semigroups by the simple trick of adjoining an identity element to a semigroup in order to obtain a monoid.

### How finiteness is applied-- existence of a loop

The first lemma shows the existence of a repeat in the sequence of powers of x.  The original version, supplied by the students, is commented out below. The notions 'monoid' and 'finite' are built into Lean.  The property of finiteness that was used is the pigeonhole principle, in the line `apply Finite.exists_ne_map_eq_of_infinite` below.

### Proof of the existence of a repeat

At first I made a lot of tweaks to this code supplied by the students, because I didn't understand about typeclass inference, thought that the monoid should be an explicit argument, thought that we should use `Finite` instead of `Fintype` because I wanted `α is finite ` to be a Proposition, etc.  I came back to the original version as I started to understand a bit more about some of the magic that takes place under the hood (although there is much I still don't understand!)

The only change I kept is that the exponent `a` whose existence is proved is a positive integer.
-/



lemma exists_repeat {α : Type*}  [Fintype α] [ Monoid α ] (x : α) : ∃ (a b : ℕ), a < b ∧ x^a = x^b ∧ a > 0 := by
  -- use a mathlib theorem to get a1 ≠ b1
  obtain ⟨a1, b1, a1_neq_b1, xa1_eq_xb1,posa1,posb1 ⟩ : ∃ a1 b1, a1 ≠ b1 ∧ x^a1 = x^b1 ∧ a1 > 0 ∧ b1 > 0 := by
    let f : ℕ → α := fun n => x^(n+1)
    have h: ∃ m n : ℕ ,m ≠ n ∧ x^(m+1) = x^(n+1) := by apply Finite.exists_ne_map_eq_of_infinite
    cases'  h with m  h₁
    cases' h₁ with n h₂
    have succmpos : m + 1 > 0 := Nat.zero_lt_succ m
    have succnpos : n + 1 > 0 := Nat.zero_lt_succ n
    have m_neq_n : m ≠ n := h₂.left
    have succm_neq_succn : m + 1 ≠ n + 1 := (add_ne_add_left 1).mpr m_neq_n
    exact ⟨m+1,n+1,succm_neq_succn,h₂.right,succmpos,succnpos ⟩
  -- Without loss of generality, let a < b
  rcases (Nat.lt_or_gt_of_ne a1_neq_b1) with (a1_lt_b1 | a1_gt_b1)
  {-- Case a1 < b1

      exact ⟨a1 , b1 , a1_lt_b1, xa1_eq_xb1,posa1⟩
  }
  {-- Case a1 > b1
      have xb1_eq_xa1 : x^b1 = x^a1 := by
        simp_all only [ne_eq, gt_iff_lt]
      exact ⟨b1, a1, a1_gt_b1, xb1_eq_xa1,posb1⟩
  }

/- ### Definition of idempotent   -/

def idempotent {α : Type*}   [Monoid α] (e : α) : Prop :=  e^2 = e

/- ### Existence of an idempostnet

 The idea of the proof is this: We use the previous lemma to
extract a pair 0 < a < b such that x^a = x^b. Then b - a is
a positive multiple of the length of the cycle in the powers of
x.  We prove that if t ≥ a and k is any natural number,  then x ^ (t + k * (b-a)) = x ^ t. This is the statement `loop` given below,
and proved by induction.


QUESTION 1: Can we make the proof more concise? The code below contains a gazillion `have`s and long calculational proofs, surely there is a slicker way.

QUESTION 2: (more advanced) Can we write a tactic, analogous to ring for doing calculations in monoids?  Or does such a tactic exist? This should take two expressions involving multiplication, parentheses and exponentiation, and find a proof, if one exists, that they are equivalent.  That is, it will do all necessary applications of the laws of exponents and associativity automatically, like the `ring` tactic but without addition.
-/

theorem exists_idempotent {α : Type*} [Fintype α] [ Monoid α] (x : α):
∃ r:ℕ , r > 0 ∧ (idempotent   (x ^ r)) :=  by
  cases' exists_repeat   x with a h₁
  cases' h₁ with b h₂

  /- `loop` is the basic principle that guides the proof -/
  have loop : ∀ k t : ℕ , t ≥ a → x ^ (t + k * (b-a)) = x ^ t := by
    intro k
    induction' k with k ih
    /- zero case -/
    · intro t
      intro t_geq_a
      have h : t + 0 * (b -a) = t := by ring
      rw [h]

    /- inductive case -/
    · intro t
      intro t_ge_a
      have b_gt_a : b > a := h₂.left
      have b_ge_a : b ≥ a := Nat.le_of_succ_le b_gt_a
      have t_sub_a : (t - a) + a = t := Nat.sub_add_cancel t_ge_a
      have b_sub_a : a + (b -a) = b := Nat.add_sub_of_le b_ge_a
      have rearrange : t + (k + 1) * (b - a) = (t+ k *(b-a) + (b - a))
      := by ring
      have powerstuff : x ^ ((t-a)+a) = x ^ (t - a)* x ^ a := pow_add x (t - a) a
      have powerstuff2 : x^a * x^(b - a) = x ^ (a + (b - a)) := Eq.symm (pow_add x a (b - a))
      calc
        x ^ (t + (k + 1) * (b - a)) = x ^ (t+ k *(b-a) + (b - a)) := by rw [rearrange]
        _       = x ^ (t+ k *(b-a)) * x ^ (b- a) := pow_add x (t + k * (b - a)) (b - a)
        _       = x ^ t * x ^ (b -a) := by rw [ih t t_ge_a]
        _       = x ^ ((t - a) + a) * x ^(b -a) := by rw [t_sub_a]
        _       = x ^ (t - a) * x^a * x^(b - a) := by rw [powerstuff]
        _       = x ^ (t - a) * (x^a * x^(b - a)) := npow_mul_assoc (t - a) a (b - a) x
        _       = x ^ (t - a) * x ^ (a + (b - a)) := by rw [powerstuff2]
        _       = x ^ (t - a) * x ^ b := by rw [b_sub_a]
        _       = x ^ (t - a) * x ^ a := by rw [h₂.right.left]
        _       = x ^ ((t -a) + a) := Eq.symm (pow_add x (t - a) a)
        _       = x ^ t := by rw [t_sub_a]


  /- once we have `loop` we can construct the idempotent -/
  let r := a *(b-a)
  use r
  have apos : a > 0 := h₂.right.right
  have a_lt_b : a < b := h₂.left
  have b_sub_a_pos : b - a ≥ 1 := Nat.zero_lt_sub_of_lt a_lt_b
  have r_ge_a : r ≥ a :=
    calc
      r = a * (b -a) := rfl
      _ ≥ a * 1 :=  Nat.mul_le_mul_left a b_sub_a_pos
      _ = a := by ring

  have two_r : 2 * r = r + r := by ring
  constructor
  · calc
      r ≥ a := r_ge_a
      _ > 0 := apos
  · calc
      (x ^ r) ^ 2 = x ^ (2 *r ) := Eq.symm (pow_mul' x 2 r)
      _           = x ^ (r + r) := by rw [two_r]
      _           = x ^ r := loop a r r_ge_a


/- Now we can do uniqueness of the idempotent.  As the students pointed out, there is a very simple proof of this. We first show that all positive powers of an idempotent are equal.  A question was raised in our meeting about how to
prove something for all positive integers, that is, how to start the induction at 1.  There are several approaches, but the one below works okay: We first prove a version that starts the induction at 0, and then adjust. -/

lemma powers_of_idempotents_1 {α : Type*} [Monoid α] (e : α)(id_e : idempotent   e)(m : ℕ ): e ^ (m + 1) = e := by
  induction' m with m ih
  --case m = 0
  · calc
      e ^ (0 + 1) = e^1  := rfl
      _           = e := pow_one e
  --case m + 1
  · calc
      e ^ (m + 1 + 1) = e^(m + 1)* e^1 := pow_add e (m + 1) 1
      _               = e * e^1 := by rw [ih]
      _               = e * e := by rw [pow_one e]
      _               = e^2 := Eq.symm (pow_two e)
      _               = e := id_e


/- Here is the adjustment, which just consists of applying the fact that
if m is a positive integer, then it is a natural number plus 1.  -/
lemma powers_of_idempotents {α : Type*}  [ Monoid α](e : α)(id_e : idempotent e)(m : ℕ )(mpos: m > 0): e ^ m = e := by
  have msplit : m = (m - 1)+1 := (Nat.sub_eq_iff_eq_add mpos).mp rfl
  rw [msplit]
  exact powers_of_idempotents_1  e id_e (m-1)

/- QUESTION 3: Is there a more elegant way to start a proof by induction to show a property that holds at all natural numbers greater than or equal to some threshold t ? -/

/- ### Proof of Uniqueness of Idempotents -/

/- Here is the assertion that the idempotent power of x is unique. -/

theorem unique_idempotent {α : Type*}  [Monoid α](x :α)
(r s :ℕ)(rpos: r > 0)(spos : s > 0)(id_r: idempotent   (x^r))(id_s: idempotent  (x^s)): x^r =x^s :=
  calc
    x ^ r = (x ^ r)^s := Eq.symm (powers_of_idempotents  (x^r) id_r  s spos)
    _ = x ^ (r * s) := Eq.symm (pow_mul x r s)
    _ = x ^ (s * r) := by rw [mul_comm r s ]
    _ = (x ^ s) ^ r := pow_mul x s r
    _ = x ^ s := powers_of_idempotents  (x^s) id_s  r rpos

/-

QUESTION 4 : (Organization of the project) I would like to break this large file into smaller files, and import the files containing the earlier steps, but this gave me some troubles: It looks like I have to create a compiled version of the .lean files with the extension .olean, but I didn't succeed, even with the instructions in hand!

### Generalizing to semigroups

  It was helpful to work in monoids, but we want these theorems to hold in any finite semigroup.  There is an easy mathematical proof of this:  Given a finite semigroup `S`, adjoin a new element `I` and extend the multiplication in `S` to `S ∪ {I}` by making `I` the identity. `S ∪ {I}` is now a monoid, and any idempotent in `S` now has all the properties of the monoid.  -/

/- powering is not a built-in definition in semigroups (surprisingly).

QUESTION 5 : (Organization of the project) How should we handle the namespaces?-/

namespace Algebra.Semigroup

/- ### Extending the definition of powering to semigroups.-/

def pnatPow {S : Type } [Semigroup S](x : S) (n : ℕ+) := @PNat.recOn n (fun _ => S) x (fun _ ih => ih * x)

/-- Provides the notation `x ^ n` for `pnatPow x n`,
analogous to the `Pow M ℕ` instance for monoids (also in `Mathlib.Algebra.Group.Defs`) -/
instance hPow {S : Type } [Semigroup S]: Pow S ℕ+ := ⟨pnatPow⟩

@[simp]
lemma pow_one {S : Type } [Semigroup S](x : S) : x ^ (1 : ℕ+) = x := by rfl

/-- Exponentiation satisfies the successor property -/
@[simp ←]
lemma pow_succ {S : Type } [Semigroup S](n : ℕ+) (x : S) : x ^ (n + 1) = (x ^ n) * x := by
  induction n using PNat.recOn with
  | one    => rfl
  | succ k ih => rfl

/-

### Extending S to S¹ .

This is the `WithOne`  trick that lets us prove something about semigroups by embedding in a monoid. The lemma below shows that if k is positive, then x^k is the same element whether we consider x as an element of the semigroup S or of the monoid S¹ . That .coe is type coercion of an element of type S to an element of type S¹.

We also need to deal with the type difference between ℕ+ and ℕ . This is what the Subtype.val is doing in the statements below, again coercing the type.

QUESTION 7: (Notation) We can refer to the embedding with the verbose name WithOne.coe.  In the Tactic state in InfoView, the compact notation ↑ is often used, although this could be ambiguous. For instance, in the code below, I get an error message when I try to replace the last occurrence of WithOne.coe by ↑, When can we replace the verbose notation by the more compact version?

QUESTION 8: (Notation) Can we introduce the notation S¹, so that this looks more like the mathematical notation?-/

lemma lift_powers{S : Type } [Semigroup S](x : S) (n : ℕ+) : WithOne.coe (x^n) = (WithOne.coe x)^(PNat.val n) := by

  induction n using PNat.recOn with
  | one    => rfl
  | succ k ih =>
    calc
     ↑ (x ^ (k + 1)) = ↑ (x^k * x) := by rw [pow_succ k x]
     _              = (↑(x^k)) * (↑x) := by rfl
     _              = (↑x)^(PNat.val k )  * (↑ x) := by rw [ih]
     _              = (WithOne.coe x)^(PNat.val k+1) := rfl

/- idempotents in semigroups -/

/- It will be useful to know that an element of S¹ is NOT the lift of an element if and only if it is not the identity. -/

lemma id_is_not_lift {S : Type } [Semigroup S] (m : WithOne S):
(∃ s : S, m = ↑s ) ↔ (m ≠ (1 : WithOne S)) := by
  constructor
  · intro ex
    cases' ex with s lift
    rw [lift]
    by_contra h
    exact WithOne.coe_ne_one h

  · intro mneq1
    use WithOne.unone mneq1
    exact Eq.symm (WithOne.coe_unone mneq1)



def idempotent_sg  {S : Type } [Semigroup S](e : S) : Prop :=  e^ (2 : ℕ+) = e

/-
### Lifting idempotents
An element of the semigroup S is idempotent if and only if it is idempotent
when considered as an element of S¹. In one direction, this is application
of lifting powers. In the other, it is just injectivity of the embedding of
S in S¹. -/

lemma lift_idempotents {S : Type } [Semigroup S](x : S) : idempotent_sg x ↔ idempotent (WithOne.coe x) := by
  constructor
  · intro sgid
    have h : (WithOne.coe x)^2 = WithOne.coe x :=
      calc
        (WithOne.coe x)^2 = WithOne.coe (x^(2:ℕ+)) := lift_powers x 2
        _                 = WithOne.coe (x ) := by rw [sgid]

    exact h
  · intro monid
    have h : x^(2 : ℕ+) = x :=  WithOne.coe_inj.mp monid
    exact h

/- Just a simple combination of the last two lemmas: -/

lemma lift_idempotent_powers {S : Type } [Semigroup S](x : S)(r : ℕ+)(idxr: idempotent_sg (x^r)) : idempotent ((WithOne.coe x)^(PNat.val r)) := by
  have h₁ : idempotent (WithOne.coe (x^r)) := (lift_idempotents (x^r)).mp idxr
  have h₂: WithOne.coe (x ^ r) = (WithOne.coe x) ^ (PNat.val r) := lift_powers x r
  rw [<-h₂]
  exact h₁


/- QUESTION 9: How do we prove this simple thing---that from Fintype S we get
Fintype (WithOne S)?  WithOne S is definitionally equivalent to
Option S, so why won't the proof below work when I replace Option S
by WithOne S ? But it worked when I did it in two steps as below!
The first step is copied from library code, and I don't entirely
understand it.
-/
instance instfintype_option {S : Type } [Semigroup S][Fintype S] : Fintype (Option  S ) where
  elems := Finset.insertNone Finset.univ
  complete := by
    intro a
    simp

instance  {S : Type } [Semigroup S][Fintype S] : Fintype (WithOne  S ):=
  instfintype_option

/- ### Semigroup version of the theorem on existence of idempotents -/
theorem exists_idempotent_sg  {S : Type } [Semigroup S][Fintype S]  (x : S):
∃ r:ℕ+ , (idempotent_sg   (x ^ r)) := by

  obtain ⟨s,spos,idemwithone⟩ : ∃ s : ℕ, (s > 0 ) ∧ (idempotent ((WithOne.coe x)^s)) := exists_idempotent (WithOne.coe x)
  have h : ∃ r : ℕ+, (PNat.val r) = s := CanLift.prf s spos
  cases' h with r sbtp
  use r
  have h₂ : WithOne.coe (x ^ r ) = (WithOne.coe x)^s :=
    calc
      WithOne.coe (x ^ r) = (WithOne.coe x)^(PNat.val r) := lift_powers x r
      _ = (WithOne.coe x)^s := by rw [sbtp]
  have h₃ : idempotent (WithOne.coe (x ^ r)) := by
    rw [Eq.symm h₂] at idemwithone
    exact idemwithone
  exact (lift_idempotents (x ^ r)).mpr h₃



/-
### Uniqueness of idempotents in the semigroup case.

QUESTION 10 : no longer needed
-/


lemma pnat_is_pos (n : ℕ+) : (PNat.val n) > 0 := PNat.pos n


theorem unique_idempotent_sg {S : Type}  [Semigroup S](x : S)
(r s :ℕ+)(id_r: idempotent_sg   (x^r))(id_s: idempotent_sg  (x^s)): x^r =x^s := by
 have rpos : (PNat.val r) > 0 := pnat_is_pos r
 have spos : (PNat.val s) > 0 := pnat_is_pos s
 have idxr : idempotent ((WithOne.coe x)^(PNat.val r)) := lift_idempotent_powers x r id_r
 have idxs : idempotent  ((WithOne.coe x)^(PNat.val s)) := lift_idempotent_powers x s id_s
 have idxreqidxs : ((WithOne.coe x)^(PNat.val r)) = ((WithOne.coe x)^(PNat.val s)) := unique_idempotent (WithOne.coe x) r s rpos spos idxr idxs
 have liftsequal : WithOne.coe (x^r ) = WithOne.coe (x^s) :=
  calc
    WithOne.coe (x^r ) = ((WithOne.coe x)^(PNat.val r)) := lift_powers x r
    _                  = ((WithOne.coe x)^(PNat.val s)) := idxreqidxs
    _                  = WithOne.coe (x^s ) := Eq.symm (lift_powers x s)
 exact WithOne.coe_inj.mp liftsequal


/-!
### Green's Relations in Finite Semigroups

#### Equivalence relations from preorders

Initially, Green's relations  will be defined as preorders, and then the corresponding equivalence relations will be constructed by a standard procedure for passing from a preorder to an equivalence relation.
-/

/- A type with an equivalence relation is an instance of a class
called a Setoid.-/

def equiv_from_preorder {α : Type }(p : Preorder α)(a b :α) :=
  (a ≤ b) ∧ (b ≤  a)

lemma equiv_from_preorder_refl {α : Type }(p :Preorder α) :
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


instance setoid_from_preorder {α : Type } [p : Preorder α] : Setoid α where
  r := equiv_from_preorder p
  iseqv :=  ⟨equiv_from_preorder_refl p, @equiv_from_preorder_symm α p,@equiv_from_preorder_trans α p⟩

/-!

### The R preorder

The mathematical definitions of the preorders are more concise, and their properties (especially transitivity) easier to verify, if we work in the monoid S¹.  So we will use the results about WithOne to define
the R and L orderings, and to prove that they are preorders.

On the other hand, it is useful to have an equivalent definition that 'lives in' semigroups, so we give this as well,and prove that it is
equivalent to the original definition.
 -/

def R_le {S : Type} [Semigroup S ](s t : S) :=  (∃ u : (WithOne S), ↑s = ↑ t * u)

lemma R_le_refl {S : Type} [Semigroup S ] (s : S ) : R_le s s := by
  use (1 : (WithOne S))
  rfl
/- note in the proof below (a) If we did not use WithOne, we would
be faced with multiple cases, and the proof would be much longer. (b) We can
also use the abbreviated notation ↑ for WithOne.coe.  Since this can be ambiguous, it doesn't always work, but it saves typing when it does. -/

lemma R_le_trans {S : Type} [Semigroup S ](s t u : S) (slet : R_le s t)(tleu : R_le t u) : R_le s u := by
  cases' slet with v h₁
  cases' tleu with w h₂
  use w * v
  calc
    ↑s = ↑t * v := h₁
    _ =  (↑u * w) * v := by rw [h₂]
    _ =  ↑u * (w * v) := by apply mul_assoc


instance ROrder {S : Type} [Semigroup S ]: Preorder S where
  le := R_le
  le_refl := R_le_refl
  le_trans := R_le_trans

/- the alternative definition of the R ordering, which lives
entirely in the semigroup domain.-/

def R_le_alt {S : Type} [Semigroup S ](s t : S) :=  (∃ u : S, s = t * u) ∨ s = t

/- Proof that the two definitions are equivalent.
-/
lemma R_le_alt_Rle {S : Type} [Semigroup S ](s t : S): ROrder.le s t ↔ R_le_alt s t := by
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
        sorry

      exact Or.intro_left _ (Exists.intro v seqtv)

  · intro slet_sg
    cases' slet_sg with neq eq
    · sorry
    · sorry

/- ### R equivalence

But how do you now define R equivalence using the general tools for preorder and now the setoid thing? The following gave the correct type correctly, but does it acually work?-/

instance REq  {S : Type}[Semigroup S] : Setoid S :=
  @setoid_from_preorder S ROrder

variable {S : Type}[Semigroup S]
#check (@REq  S).r

/-
### An example to check that all this works

In this example we'll construct the semigroup of all maps from
a three-element set into itself, and construct some elements
of the semigroup.  Then verify some inequalities and equivalences using the R order and R equivalence.

There is an equation (in the sublemma `verify_sublem` below ) that
I am unable to prove, even though it is  just a simple calculation
with finite functions.`

 Here is the type of maps of a 3-element set into itself.-/
def threemaps := (Fin 3) → (Fin 3)

/- Here are a few threemaps -/
def f : threemaps :=
  fun x : Fin 3 => if x = 0 then 0
                   else 2

#check f

#eval f
#check f 1
#eval f 1
/- There's a more convenient notation! -/
def g : threemaps := ![2, 1, 0]

#check g 1
#eval g 2



/- semigroup structure on threemaps-/



def threemaps_prod (a b: threemaps ) := b ∘ a
/- nice that you get associativity just from rfl -/
lemma threemaps_prod_assoc (a b c : threemaps ) :
threemaps_prod (threemaps_prod a b ) c = threemaps_prod a (threemaps_prod b c ) := rfl

def h : threemaps := threemaps_prod f g
#check h
#eval h

#eval threemaps_prod h g
#eval f


instance : Semigroup threemaps where
  mul := threemaps_prod
  mul_assoc := threemaps_prod_assoc

#check threemaps
#check (@ROrder threemaps).le h f

/-verifying an R - inequality -/
lemma ROrder_verify1 : (@ROrder threemaps).le h f := by
  use g
  sorry

lemma verify_sublem: threemaps_prod h g = f := List.ofFn_inj.mp rfl

/- why doesn't the same thing work here?: Note that we haven't quite
finished. Seems to get confused with WithOne. -/
lemma ROrder_verify2 : (@ROrder threemaps).le f h := by
  use g
  /- rfl -/
  sorry


#check ![0,2,2]
example: (@REq ).r h f := by
  constructor
  · exact ROrder_verify1
  · exact ROrder_verify2

/- ### The L preorder

STOP HERE!
I haven't yet handled the L order with the new regime of
embedding into a monoid.

We _could_ get fancy and try to define this as the R-preorder in the reversed semigroup, but that looks like more trouble than it's worth. So we'll just repeat the code above with everything turned around. -/

def L_le {S : Type} [Semigroup S ](s t : S) :=  (∃ u : (WithOne S), ↑s = u * ↑ t )

lemma L_le_refl {S : Type} [Semigroup S ] (s : S ) : L_le s s := by
  use (1 : (WithOne S))
  rfl

/- note in the proof below (a) If we did not do the type coercion, we would
be faced with multiple cases, and the proof would be much longer.  We can
also use the abbreviated notation ↑ for WithOne.coe.  Since this can be ambiguous, it doesn't always work, but it saves typing when it does. -/

lemma L_le_trans {S : Type} [Semigroup S ](s t u : S) (slet : L_le s t)(tleu : L_le t u) : L_le s u := by
  cases' slet with v h₁
  cases' tleu with w h₂
  use v * w
  calc
    ↑s = v * ↑t   := h₁
    _ =  v * ( w * ↑u )  := by rw [h₂]
    _ =  v *  w * ↑u  := by apply (Eq.symm (mul_assoc v w ↑u))

      /- Here we need to explicitly supply the field
      lt, although it seems redundant, and we did not
      need it for the L order. -/
instance LOrder {S : Type} [Semigroup S ]: Preorder S where
  le := L_le
  le_refl := L_le_refl
  le_trans := L_le_trans
  lt := fun a b => (L_le a b) ∧ ¬(L_le b a)
 /-!

 ### The J preorder

 We can either define this as the composition of R and L (in either order)
 or give a 'two-sided' definition.  We'll do the latter.-/

def J_le {S : Type} [Semigroup S ](s t : S) := ∃ u v : (WithOne S), ↑s = u * ↑ t * v

lemma J_le_refl {S : Type} [Semigroup S ] (s : S ) : J_le s s := by
  use (1 : WithOne S) , (1 : WithOne S)
  rfl

lemma J_le_trans {S : Type} [Semigroup S ](s t u : S) (slet : J_le s t)(tleu : J_le t u) : J_le s u := by
/- can we shorten the next four lines of code that extract witnesses? -/
  cases' slet with v h
  cases' h with w h₁
  cases' tleu with v₁ h
  cases' h with w₁ h₂
  use v * v₁, w₁ * w
  calc
    ↑s = v * ↑t * w := h₁
    _ = v * (v₁ * ↑u * w₁) * w := by rw [h₂]
    _ = v * (v₁ * ↑u) * w₁ * w := by rw [mul_assoc v (v₁ * ↑u) w₁]
    _ = v * (v₁ * ↑u) * (w₁ * w) := by rw [mul_assoc (v * (v₁ * ↑ u)) w₁ w]
    _ = v * v₁ * ↑u * (w₁ * w):= by rw [mul_assoc v v₁ ↑u]


instance JOrder  {S : Type} [Semigroup S ]: Preorder S where
  le := J_le
  le_refl := J_le_refl
  le_trans := J_le_trans
  lt := fun a b => (J_le a b) ∧ ¬(J_le b a)

/-!
### The H preorder
-/

def H_le {S : Type} [Semigroup S ](s t : S) := (R_le s t) ∧ (L_le s t)

lemma H_le_refl {S : Type} [Semigroup S ] (s : S ) : H_le s s := by
  constructor
  · apply R_le_refl
  · apply L_le_refl

lemma H_le_trans {S : Type} [Semigroup S ](s t u : S) (slet : H_le s t)(tleu : H_le t u) : H_le s u := by
  constructor
  · exact R_le_trans s t u slet.left tleu.left
  · exact L_le_trans s t u slet.right tleu.right

instance HOrder  {S : Type} [Semigroup S ]: Preorder S where
  le := H_le
  le_refl := H_le_refl
  le_trans := H_le_trans
  lt := fun a b => (H_le a b) ∧ ¬(H_le b a)
end Algebra.Semigroup
