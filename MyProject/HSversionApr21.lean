import Mathlib


/-!

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

Note that the way we said (originally) that α is a finite monoid is through the arguments
{α : Type*} [Monoid α] [Fintype α]
below. Question:  What do the square brackets actually mean?

 -/



/- lemma exists_a_b {α : Type*} [Monoid α] [Fintype α] (x : α) : ∃ (a b : ℕ), a < b ∧ x^a = x^b  := by
  -- use a mathlib theorem to get a1 ≠ b1
  obtain ⟨a1, b1, a1_neq_b1, xa1_eq_xb1⟩ : ∃ a1 b1, a1 ≠ b1 ∧ x^a1 = x^b1  := by
    let f : ℕ → α := fun n => x^n
    apply Finite.exists_ne_map_eq_of_infinite
  -- Without loss of generality, let a < b
  rcases (Nat.lt_or_gt_of_ne a1_neq_b1) with (a1_leq_b1 | a1_geq_b1)
  {-- Case a1 < b1

      exact ⟨a1 , b1 , a1_leq_b1, xa1_eq_xb1⟩
  }
  {-- Case a1 > b1
      have xb1_eq_xa1 : x^b1 = x^a1 := by
        simp_all only [ne_eq, gt_iff_lt]
      exact ⟨b1, a1, a1_geq_b1, xb1_eq_xa1⟩
  } -/


/-I tweaked this in several ways: for purposes later in the proof, I required the values `a1, b1` obtained in the proof above to be positive.  Second, I switched to using `Finite` in place of `Fintype` as a way to say that the type is finite, since `Finite α` gives a proposition. That made it easier for me to work with, since I don't really understand what Fintype is doing!

Question: What is `Fintype` doing?

I also wanted the monoid to be an explicit argument, for use later in the proof. This just involves replaces the thingy in square brackets. (Again, I don't really understand what is going on under the hood in this.) I'm a bit on the fence about this last 'improvement', since it entails carrying around the argument M as extra baggage through every step of the argument, rather than just proving everything with the argument list starting

{α : Type*} [Monoid α] [Finite α]

and then extracting a version with an explicit argument.

So here at last is the proof of the existence of a repeat. -/


lemma exists_repeat {α : Type*}  [Finite α] (M : Monoid α ) (x : α) : ∃ (a b : ℕ), a < b ∧ x^a = x^b ∧ a > 0 := by
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

def idempotent {α : Type*}  [Finite α] (M :Monoid α) (e : α) : Prop :=  e^2 = e

/- The idea of the proof is this: We use the previous lemma to
extract a pair 0 < a < b such that x^a = x^b. Then b - a is
a positive multiple of the length of the cycle in the powers of
x.  We prove that if t ≥ a and k is any natural number,  then x ^ (t + k * (b-a)) = x ^ t. This is the statement `loop` given below,
and proved by induction.

### Existence proof in Lean

-/

theorem exists_idempotent {α : Type*} [Finite α] (M : Monoid α) (x : α):
∃ r:ℕ , r > 0 ∧ (idempotent M (x ^ r)) :=  by
  cases' exists_repeat M x with a h₁
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

lemma powers_of_idempotents_1 {α : Type*} [Finite α](M : Monoid α) (e : α)(id_e : idempotent M e)(m : ℕ ): e ^ (m + 1) = e := by
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
lemma powers_of_idempotents {α : Type*}  [Finite α] (M: Monoid α)(e : α)(id_e : idempotent M e)(m : ℕ )(mpos: m > 0): e ^ m = e := by
  have msplit : m = (m - 1)+1 := (Nat.sub_eq_iff_eq_add mpos).mp rfl
  rw [msplit]
  exact powers_of_idempotents_1 M e id_e (m-1)

/- Question: Is there a more elegant way to start a proof by induction at a value greater than 0?-/

/- Here is the assertion that the idempotent power of x is unique. -/
theorem unique_idempotent {α : Type*}  [Finite α](M :Monoid α)(x :α)
(r s :ℕ)(rpos: r > 0)(spos : s > 0)(id_r: idempotent M (x^r))(id_s: idempotent M (x^s)): x^r =x^s :=
  calc
    x ^ r = (x ^ r)^s := Eq.symm (powers_of_idempotents M (x^r) id_r  s spos)
    _ = x ^ (r * s) := Eq.symm (pow_mul x r s)
    _ = x ^ (s * r) := by rw [mul_comm r s ]
    _ = (x ^ s) ^ r := pow_mul x s r
    _ = x ^ s := powers_of_idempotents M (x^s) id_s  r rpos


/-

### Generalizing to semigroups

  It was helpful to work in monoids, but we want these theorems to hold in any finite semigroup.  There is an easy mathematical proof of this:  Given a finite semigroup `S`, adjoin a new element `I` and extend the multiplication in `S` to `S ∪ {I}` by making `I` the identity. `S ∪ {I}` is now a monoid, and any idempotent in `S` now has all the properties of the monoid.  -/

/- But how do we say this in Lean? -/

/- Given two types α,β we can create their sum type α ⊕ β, which is the disjoint union. To achieve the effect we want, we need to take β to be a type with just one element. The Unit type does this. Here is a proof that if α is finite then so is α ⊕ Unit. This is easy! -/

example (α : Type)(h : Finite α): Finite (α ⊕ Unit ) := by
  exact Finite.instSum



/- We're now ready to define the monoid structure on
α ⊕ Unit.  I tried several different formulations, and relied heavily on the documentation in the Lean Language Manual for information on Sum types. But I still could not prove associativity.  When I get to associativity, the Lean Infoview presents the goal as `⊢ u * v * w = u * (v * w)` But it will not let me write
these expressions without throwing an error. This is where the proof stalled.


-/

instance add_identity {α : Type}(S : Semigroup α) : Monoid (α ⊕ Unit)
  where
    mul f g := by
      by_cases h : Sum.isLeft f
      · by_cases hh: Sum.isLeft g
        · exact Sum.inl (S.mul (f.getLeft h) (g.getLeft hh))
        · exact f
      · by_cases Sum.isLeft g
        · exact g
        · exact Sum.inr Unit.unit
    one := Sum.inr Unit.unit
    one_mul := by
      intro a
      by_cases h : Sum.isLeft a
      · sorry
      · sorry

    mul_one := by
      intro a
      by_cases h : Sum.isLeft a
      · sorry
      · sorry



    mul_assoc := sorry



/- Definition of an idempotent in a semigroup. We don't have the power
notation available in semigroups, so the statement looks slightly different. -/

def idempotent_sg {α : Type*}  [Finite α] (S :Semigroup α) (e : α) : Prop :=  e*e = e

/- Existence of an idempotent power in a semigroup. -/





--------------------------------------------------------------------------- -/
/- I've kept the older code below, but didn't use it. -/
/-
lemma periodic {α : Type*} [Monoid α] [Fintype α] (x : α) (a : ℕ)(b : ℕ) (c : ℕ) (a_lt_b : a < b) (c_eq_ba : c = b-a) (xa_eq_xb : x^a = x^b) :
∀ (n : ℕ), x^(a+n*c) = x^a := by
  have cycle : x^a = x^(a+c) := by
    rw [xa_eq_xb]
    have h1 : (a + (b - a) = b) :=
      Nat.add_sub_cancel' (Nat.le_of_lt a_lt_b)
    rw [c_eq_ba]
    rw [h1]
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    calc
      x^(a + (n+1)*c) = x^(a + n*c + c) := by
        ring_nf
      x^(a + n*c + c) = x^(a + n*c) * x^c := by
        rw [pow_add]
      x^(a + n*c) * x^c = x^a * x^c := by
        rw [ih]
      x^a * x^c = x^(a+c) := by
        rw [pow_add]
      x^(a+c) = x^a := by
        rw [cycle]


theorem idempotence_theorem (α : Type*) [Monoid α] [Fintype α]:
∀ (x: α), ∃ (n : ℕ), x ^ n = x^(2*n) ∧
∀ (m : ℕ), x^m = x^(2*m) → x^n = x^m
:= by
  intro (x: α)

  obtain ⟨a, b, a_lt_b, xa_eq_xb⟩ : ∃ a b, a < b ∧ x^a = x^b := exists_a_b x

  let c := b - a
  have c_eq_ba : c = b - a := by
    simp [c]

  have periodic : ∀ (n  : ℕ), x^(a+n*c) = x^a :=
    periodic x a b c a_lt_b c_eq_ba xa_eq_xb

  have periodic_general : ∀ (n1 n2 : ℕ), (n1 ≥ a) → x^n1 = x^(n1 + n2*c) := by
    sorry -- probably prove by induction
    -- See how this will be used in unique_idempotent

  have idempotent_divides : ∀ (n : ℕ), x^n = x^(2*n) → ∃ (d : ℕ), n = d * c := by
    sorry  -- probably prove by induction
    -- See how this will be used in unique_idempotent
    -- Note: this is only true if c is defined as the cycle length, but we defined it as the difference between some a b where x^a = x^b. This means could be a multiple of the cycle length, so this statmeent would not hold. I think we need to change the definition of C to be the difference between the FIRST two a b such that x^a = x^b not any such a b.

  -- x^(a*c) is idempotent
  have idempotent : x^(a*c) = x^(2*(a*c)) := by
    have h1 : x^a = x^(a*(1+c)) := by
      have h2 : x^a = x^(a + a*c) := by
        rw [periodic]
      have h3 : x^(a + a*c) = x^(a*(1+c)) := by
        sorry
      rw [h2, h3]

    have h4 : x^a * x^(a*c-a) = x^(a*(1+c)) * x^(a*c-a) := by
      sorry -- both sides * x^(a*c-a)

    have h5 : x^a * x^(a*c-a) = x^(a*c) := by
      have h6 : x^a * x^(a*c-a) = x^(a+a*c-a) := by
        sorry
      have h7 : a+a*c-a = a*c := by
        sorry
      rw [h6, h7]

    have h8 : x^(a*(1+c)) * x^(a*c-a) = x^(2*(a*c)) := by
      have h9 : a*(1+c) = a+a*c := by
        sorry
      rw [h9]
      have h10 : x^(a+a*c) * x^(a*c-a) = x^(a+a*c+a*c-a) := by
        sorry --power laws
      rw [h10]
      have h11 : a+a*c+a*c-a = 2*(a*c) := by
        sorry
      rw [h11]

    sorry --apply h5 to left side and h8 to right


  have unique_idem : ∀ m, x^m = x^(2*m) → x^(a*c) = x^m := by
    intros m hm
    obtain ⟨y, m_eq_yc⟩ : ∃ (y : ℕ), m=y*c := by
      sorry -- use idempotent_divides
    have compare_ya : y = a ∨ y > a ∨ y < a := by
      sorry

    rcases compare_ya with (y_eq_a | y_gt_a | y_lt_a)
    { -- Case 1: y = a
      rw [m_eq_yc, y_eq_a]
    }
    {-- Case 2 : y_gt_a
      let diff := y - a
      calc
        x^(a*c) = x^(a*c + c*diff):= by
          sorry -- use generalized periodic
        x^(a*c + c*diff) = x^(a*c + c*(y-a)) := by
            sorry --def of diff
        x^(a*c + c*(y-a)) = x^(a*c + c*y-c*a) := by
          sorry -- distribute c
        x^(a*c + c*y - c*a) = x^(y*c) := by
          sorry -- communitivity and canceling
        x^(y*c) = x^m := by
          rw [m_eq_yc]
    }
    { -- case 3: y_lt_a
      let diff := a - y
      have reverse : x^m = x^(a*c) := by
        calc
          x^m = x^(y*c) := by
            rw [m_eq_yc]
          x^(y*c) = x^(y*c + c*diff):= by
            sorry -- use generalized periodic
          x^(y*c + c*diff) = x^(y*c + c*(a-y)) := by
            sorry --def of diff
          x^(y*c + c*(a-y)) = x^(y*c + c*a-c*y) := by
            sorry -- distribute c
          x^(y*c + c*a - c*y) = x^(a*c) := by
            sorry -- communitivity and canceling
      rw [reverse]
    }

  exact ⟨(a*c), idempotent, unique_idem⟩
-/
