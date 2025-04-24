import Mathlib

universe u

section SyntacticMonoid

def synRel {α} (L : Language α) (u v : (FreeMonoid α) ): Prop :=
  ∀ (x y : FreeMonoid α), (x * u * y) ∈ L ↔ (x * v * y) ∈ L

lemma synRel_refl {α} (L : Language α): ∀ (w : FreeMonoid α), synRel L w w := by
  intro u -- Goal: synRel L u
  unfold synRel
  intros x y
  rfl -- The two sides are identical, so the equivalence is true

lemma synRel_symm {α} (L : Language α) {w v : FreeMonoid α}: synRel L w v → synRel L v w := by
  unfold synRel at * -- Unfold in hypothesis and goal
  intro huv x y -- Goal: x ++ v ++ y ∈ L ↔ x ++ u ++ y ∈ L
  exact (huv x y).symm

lemma synRel_trans {α} (L : Language α) {w v x : FreeMonoid α} :
 synRel L w v → synRel L v x → synRel L w x := by
  unfold synRel at * -- Unfold everywhere
  intros huv hvw x y
  exact Iff.trans (huv x y) (hvw x y)

-- Package the relation and its equivalence proof into a Setoid instance
instance synSetoid {α} (L : Language α): Setoid (FreeMonoid α) where
  r := synRel L
  iseqv := ⟨synRel_refl L, synRel_symm L, synRel_trans L⟩

-- Prove compatibility with multiplication (List concatenation)
lemma synRel_mul_compat {α} (L : Language α) {u₁ v₁ u₂ v₂ : FreeMonoid α} :
 synRel L u₁ v₁ → synRel L u₂ v₂ → (synRel L (u₁ * u₂) (v₁ * v₂)) := by
  intros h1 h2; unfold synRel at *; intros x y
  rw [<- mul_assoc, h2 (x*u₁) y, mul_assoc, h1 x (v₂*y), <- mul_assoc, <-  mul_assoc]


-- Define the Congruence object using the Setoid and the compatibility proof
instance synCong {α} (L : Language α): Con (FreeMonoid α) where
  toSetoid := synSetoid L
  mul' := synRel_mul_compat L


example (α) : Monoid (FreeMonoid α) := by
  infer_instance
-- Below is not necessary
instance FreeMonoid_isMonoid {α} : Monoid (FreeMonoid α) where
  mul x y := FreeMonoid.ofList (FreeMonoid.toList x ++ FreeMonoid.toList y)
  mul_assoc := List.append_assoc
  one := FreeMonoid.ofList []
  one_mul := List.nil_append
  mul_one := List.append_nil
  npow_zero := by intros w; unfold npowRecAuto; rfl;
  npow_succ := by intros m a; unfold npowRecAuto; exact rfl



-- Define the natural homomorphism from the free monoid (words) to the syntactic monoid (classes)
def toSynMonoid {α} (L : Language α) : FreeMonoid α →* Con.Quotient (synCong L) :=
  Con.mk' (synCong L)

-- The Syntactic Monoid M(L) is the quotient of the free monoid (List α) by the syntactic congruence
@[simp]
def SyntacticMonoid {α} (L : Language α) : Type := (synCong L).Quotient

example {α} (L : Language α) : Monoid ((synCong L).Quotient) := by infer_instance

instance synMonoid {α} (L : Language α) : Monoid (SyntacticMonoid L) := by
  simp; infer_instance

instance natural_homomorphism {α} (L : Language α): MonoidHom (FreeMonoid α) (SyntacticMonoid L) where
  toFun := (toSynMonoid L).toFun
  map_one' := by simp only [OneHom.toFun_eq_coe, MonoidHom.toOneHom_coe, map_one]
  map_mul' := by simp only [OneHom.toFun_eq_coe, MonoidHom.toOneHom_coe, map_mul, implies_true]


-- Build in notation:
-- notation "⟦" w "⟧_(" L ")" => toSynMonoid L w

example {α} (L : Language α) (w₁ w₂ : FreeMonoid α)
 : toSynMonoid L (w₁ * w₂) = toSynMonoid L w₁ * toSynMonoid L w₂ := by
  simp only [map_mul]


example {α} {L: Language α} : (1 : SyntacticMonoid L) = toSynMonoid L 1 := by
  -- This is true by definition because `toSynMonoid L` maps identity to identity
  simp only [SyntacticMonoid, map_one]

-- Notation for the quotient element (class of w)
notation "⟦" w "⟧_(" L ")" => toSynMonoid L w

-- Example usage of notation
example {α} (L : Language α) (w₁ w₂ : FreeMonoid α) : ⟦w₁ * w₂⟧_(L) = ⟦w₁⟧_(L) * ⟦w₂⟧_(L) := by
  simp only [map_mul]

example {α} (L : Language α): (1 : SyntacticMonoid L) = ⟦(1 : FreeMonoid α)⟧_(L) := by
  simp only [SyntacticMonoid, map_one]



def IsRegular' {α} (L : Language α) : Prop :=
  Finite (SyntacticMonoid L)

end SyntacticMonoid

namespace PNat

/--
If `m < n` for positive naturals, then there exists a positive `k` such that `n = k + m`.
-/
lemma exists_eq_add_of_lt {m n : ℕ+} (m_lt_n : m < n) :
  ∃ (k : ℕ+), n = k + m := by
  set k := n - m with _h
  use k
  pnat_to_nat; omega

/--
For positive naturals, if `m < n` then `m + (n - m) = n`.
-/
@[simp]
lemma add_sub_cancel' {n m : ℕ+} (m_lt_n : m < n) :
  m + (n - m) = n := by
  induction m using PNat.recOn with
  | one    => pnat_to_nat; omega
  | succ m' ih => pnat_to_nat; omega

end PNat

namespace Algebra.Semigroup

variable {M : Type u} [Semigroup M]

def pnatPow (x : M) (n : ℕ+) : M :=
  @PNat.recOn n (fun _ => M) x (fun _ ih => ih * x)

/--
Provides the notation `x ^ n` for `pnatPow x n`,
analogous to the `Pow M ℕ` instance for monoids (also in `Mathlib.Algebra.Group.Defs`)
-/
instance hPow : Pow M ℕ+ := ⟨pnatPow⟩

@[simp]
lemma pow_one (x : M) :
  x ^ (1 : ℕ+) = x := by
  rfl

/--
Exponentiation satisfies the successor property
-/
@[simp ←]
lemma pow_succ (n : ℕ+) (x : M) :
  x ^ (n + 1) = (x ^ n) * x := by
  induction n using PNat.recOn with
  | one    => rfl
  | succ k ih => rfl

@[simp]
lemma mul_pow_mul (a b : M) (n : ℕ+) :
  (a * b) ^ n * a = a * (b * a) ^ n := by
  induction n using PNat.recOn with
  | one =>
    simp only [pow_one]
    apply mul_assoc
  | succ n ih =>
    simp only [pow_succ]
    rw [← mul_assoc, ih]
    simp only [mul_assoc, ← pow_succ]

/--
For every `a : M` and `n : ℕ+`, the power `a ^ n` commutes with `a`
-/
@[simp]
lemma pow_mul_comm' (a : M) (n : ℕ+) :
  a ^ n * a = a * a ^ n := by
  induction n using PNat.recOn with
  | one    => rfl
  | succ k ih =>
    rw [pow_succ, ← mul_assoc, ih]

@[simp ←]
lemma pow_add (a : M) (n : ℕ+) :
  ∀ m, a ^ (m + n) = a ^ m * a ^ n := by
  induction n using PNat.recOn with
  | one =>
    intros m
    rw [pow_one, pow_succ]
  | succ k ih =>
    intros m
    have h_eq : m + (k + 1) = m + 1 + k := by ring
    rw [h_eq, ih]
    simp_all only [pow_succ, pow_mul_comm']
    rw [← pow_mul_comm', mul_assoc]

lemma pow_mul_comm (a : M) (m n : ℕ+) :
  a ^ m * a ^ n = a ^ n * a ^ m := by
  rw [← pow_add, ← pow_add, add_comm]

@[simp ←]
lemma pow_mul (a : M) (m n : ℕ+) :
  a ^ (m * n) = (a ^ n) ^ m := by
  induction m using PNat.recOn with
  | one    => simp
  | succ k ih =>
    simp_all only [pow_add, pow_one, pow_mul_comm']
    rw [← ih]
    have h_eq : (k + 1) * n = k * n + n := by ring
    simp_all only [pow_add, pow_mul_comm']

/--
The right-associated powers commute
-/
lemma pow_right_comm (a : M) (m n : ℕ+) :
  (a ^ m) ^ n = (a ^ n) ^ m := by
  rw [← pow_mul, mul_comm, pow_mul]

/--
If `a` is idempotent, then raising `a` to any positive power yields `a`.
-/
lemma pow_succ_eq {a : M} (n : ℕ+) (h_idem : IsIdempotentElem a) :
  a ^ n = a := by
  induction n using PNat.recOn with
  | one    => rfl
  | succ n' ih => rw [pow_add, pow_one, ih, h_idem]

/-! .
### Idempotence in Finite Semigroups

If `(x : M)` is a finite semigroup, then the cyclic subsemigroup generated by `x`:
1. Is eventuatly periodic (`exists_repeating_pow`)
2. Has at most one idempotent (`pow_idempotent_unique`)
3. Has an idempotent (`exists_idempotent_pow`)
-/

/--
If `M` is finite then for any `x : M` there exist exponents such that the power eventually repeats.
-/
lemma exists_repeating_pow [Finite M] (x : M) :
  ∃ (m c : ℕ+), x ^ m * x ^ c = x ^ m := by
  obtain ⟨m, n, hmn, heq⟩ : ∃ m n : ℕ+, m ≠ n ∧ x ^ m = x ^ n := by
    let f : ℕ+ → M := fun n => x ^ n
    apply Finite.exists_ne_map_eq_of_infinite
  simp_all
  pnat_to_nat
  rcases (Nat.lt_or_gt_of_ne hmn) with (m_lt_n | n_lt_m)
  · use m, n - m
    simp_all only [PNat.coe_lt_coe, PNat.add_sub_cancel' m_lt_n]
  · use n, m - n
    simp_all only [PNat.coe_lt_coe, PNat.add_sub_cancel' n_lt_m]


/--
If two powers of an element `x : M` are idempotent, then they are equal.
-/
theorem pow_idempotent_unique {x : M} {m n : ℕ+}
  (hm : IsIdempotentElem (x ^ m)) (hn : IsIdempotentElem (x ^ n)) :
  x ^ m = x ^ n := by
  rw [← pow_succ_eq n hm, pow_right_comm, pow_succ_eq m hn]

/--
In a finite semigroup, for any `x : M` there exists a positive natural number `n`
such that `x ^ n` is idempotent.
-/
theorem exists_idempotent_pow [Finite M] (x : M) :
  ∃ (n : ℕ+), IsIdempotentElem (x ^ n) := by
  obtain ⟨m, c, m_c_eq⟩ := exists_repeating_pow x
  /- Because `Semigroup.pow` is defined on ℕ+ rather than ℕ, it is more convenient to prove
     the `loop` lemma for all `m < a` rather than for all `m ≤ a`. This is due to the fact
     that one cannot construct a positive `b` such that `a = b + m` when `m = a`. -/
  have loop : ∀ (k a : ℕ+), m < a → x ^ (a + k * c) = x ^ a := by
    intro k
    induction k using PNat.recOn with
    | one =>
      intro a m_lt_a
      obtain ⟨d, hd⟩ := PNat.exists_eq_add_of_lt m_lt_a
      simp_all only [one_mul, add_assoc, pow_add]
    | succ k ih =>
      intro a m_lt_a
      obtain ⟨d, hd⟩ := PNat.exists_eq_add_of_lt m_lt_a
      specialize ih (a := d + m)
      have h_eq : (k + 1) * c = (k * c) + c := by ring
      simp_all only [pow_add, mul_assoc, forall_const, ← add_assoc]
  use 2 * m * c -- We cannot use `m * c` because, to apply `loop`, we must establish `m < m * c`
  unfold IsIdempotentElem
  specialize loop (k := 2 * m) (a := 2 * m * c)
  have h_m : m < 2 * m * c := by
    induction c using PNat.recOn with
    | one       => pnat_to_nat; omega
    | succ c₀ ih => pnat_to_nat; ring_nf; omega
  simp_all only [← pow_add, forall_const]


end Algebra.Semigroup

def IsAperiodic_semigroup {M} [Semigroup M]: Prop :=
  ∀ s : M, ∃ n : ℕ+, s ^ n = s ^ (n+1)

def IsAperiodic {α} (L : Language α) : Prop :=
  @IsAperiodic_semigroup (SyntacticMonoid L) (@Monoid.toSemigroup (SyntacticMonoid L) (synMonoid L))

def isStarFree {α} (L : Language α) : Prop :=
  IsRegular' L ∧ IsAperiodic L



  /-!
### Idempotent power in a finite semigroup via adjoined identity
-/

theorem Monoid.exists_idempotent_pow (M) [Finite M] [Monoid M] (m : M) :
  ∃ (n : ℕ+), IsIdempotentElem (m ^ n) := Algebra.Semigroup.exists_idempotent_pow m

namespace Semigroup

variable {S} [Semigroup S]

instance with_one_monoid : Monoid (WithOne S) := by infer_instance


instance with_one_fintype [Fintype S] : Fintype (WithOne S) := by unfold WithOne; infer_instance

lemma with_one_pow {S} [Semigroup S] (x : S) (n : ℕ+) : (↑x : WithOne S) ^ n = ↑(x ^ n) := by
  induction n with
  | one => trivial
  | succ n ih => simp [Algebra.Semigroup.pow_succ]; rw [ih]

lemma with_one_mul {S} [Semigroup S] (x : S) : (↑x : WithOne S) * (↑x : WithOne S) = ↑ (x * x : S) := by rfl

theorem with_one_exists_idempotent_pow {S} [Semigroup S] [Fintype S] (x : S) : ∃ (n : ℕ+), IsIdempotentElem (x ^ n) := by
  have H := Monoid.exists_idempotent_pow (WithOne S)
  specialize H (↑x : WithOne S); obtain ⟨ n', Hn' ⟩ := H; use n'
  unfold IsIdempotentElem at *
  simp_all only [with_one_pow]
  rw [with_one_mul] at Hn'
  rwa [← @WithOne.coe_inj S (x ^ n' * x ^ n') (x ^ n')]

end Semigroup
