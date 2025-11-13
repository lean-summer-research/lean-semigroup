import MyProject.Main_Results.Location_alt
import MyProject.Misc.SemigroupIdeals

def ReesMatrix {I : Type} {G : Type} {J : Type} (P : J → I → G) := Option (I × G × J)
def ReesMatrixNonzero {I J G : Type} (P : J → I → G) := I × G × J

namespace ReesMatrix0

variable {G : Type } {I : Type } {J : Type } (P : J → I → G) [Nonempty I] [Nonempty J]
  [GroupWithZero G] [DecidableEq G]


instance ReesMul : Mul (ReesMatrix P) where
  mul a b :=
    match a, b with
    | some (i1, g1, j1), some (i2, g2, j2) =>
      let prod := g1 * P j1 i2 * g2
      if prod = 0 then none else some (i1, g1 * P j1 i2 * g2, j2)
    | _, _ => none

def rees_of (i : I) (g : G) (j : J) : ReesMatrix P :=
  if g = 0 then none else some (i, g, j)

lemma rees_of_zero (i : I) (j : J) : rees_of i 0 j = none := by
  simp [rees_of]

/-- I needed to define this separately to use it in the proof of associativity
-- otherwise lean complained about the Option wrapper on ReesMatrix-/
def rees_mul (a b : ReesMatrix P) : ReesMatrix P :=
  match a, b with
    | some (i1, g1, j1), some (i2, g2, j2) =>
      let prod := g1 * P j1 i2 * g2
      if prod = 0 then none else some (i1, prod, j2)
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

@[simp] lemma rees_mul_none_left (x : ReesMatrix P) :
    rees_mul P none x = none := rfl

@[simp] lemma rees_mul_none_right (x : ReesMatrix P) :
    rees_mul P x none = none := by
  cases x <;> rfl

@[simp] lemma rees_mul_some_some
    {i₁ i₂ : I} {j₁ j₂ : J} {g₁ g₂ : G} {hnz : g₁ ≠ 0 ∧ g₂ ≠ 0 ∧ P j₁ i₂ ≠ 0}:
    rees_mul P (some (i₁, g₁, j₁)) (some (i₂, g₂, j₂))
      = some (i₁, g₁ * P j₁ i₂ * g₂, j₂) := by unfold ReesMatrix0.rees_mul; simp_all

@[simp] lemma rees_mul_eq_mul (a b : ReesMatrix P) :
    rees_mul P a b = a * b := by rfl

lemma mul_eq_rees_mul (a b : ReesMatrix P) :
    a * b = rees_mul P a b := by rfl


@[simp] lemma rees_mul_P_zero
    {i₁ i₂ : I} {j₁ j₂ : J} {g₁ g₂ : G} (h: P j₂ i₁ = 0):
    rees_mul P (some (i₂, g₂, j₂)) (some (i₁, g₁, j₁))  = none := by
      unfold ReesMatrix0.rees_mul
      simp_all
@[simp] lemma mul_mul_eq_zero {a b c : G} :
  a * b * c = 0 ↔ a = 0 ∨ b = 0 ∨ c = 0 := by
  -- associate to `(a*b) * c`
  have h : a * b * c = (a * b) * c := by simp [mul_assoc]
  constructor
  · intro hz
    have hz' : (a * b) * c = 0 := by simpa [h] using hz
    rcases mul_eq_zero.mp hz' with h_ab | h_c
    · rcases mul_eq_zero.mp h_ab with h_a | h_b
      · exact Or.inl h_a
      · exact Or.inr (Or.inl h_b)
    · exact Or.inr (Or.inr h_c)
  · intro hzero
    rcases hzero with h_a | hzero
    · simp [h_a]
    rcases hzero with h_b | h_c
    · have : a * b = 0 := mul_eq_zero.mpr (Or.inr h_b)
      simp [this, mul_assoc]
    · have : (a * b) * c = 0 := mul_eq_zero.mpr (Or.inr h_c)
      simpa [mul_assoc] using this

/-- Criterion for when `rees_mul` of two non-`none` values is `none`. -/
@[simp] lemma rees_mul_some_some_eq_none_iff
    {i₁ i₂ : I} {j₁ j₂ : J} {g₁ g₂ : G} :
    rees_mul P (some (i₁, g₁, j₁)) (some (i₂, g₂, j₂)) = none
      ↔ g₁ = 0 ∨ P j₁ i₂ = 0 ∨ g₂ = 0 := by
  unfold ReesMatrix0.rees_mul
  set prod := g₁ * P j₁ i₂ * g₂
  -- the branch is `none` exactly when `prod = 0`
  have h0 : prod = 0 ↔ g₁ = 0 ∨ P j₁ i₂ = 0 ∨ g₂ = 0 := by
    simpa [prod] using
      (ReesMatrix0.mul_mul_eq_zero (a := g₁) (b := P j₁ i₂) (c := g₂))
  by_cases h : prod = 0
  · simp_all only [mul_eq_zero, ↓reduceIte, prod] --if prod=0
  · simp_all [↓reduceIte, prod] -- if prod≠0

@[simp] lemma rees_mul_some_some_ne_none_iff
    {i₁ i₂ : I} {j₁ j₂ : J} {g₁ g₂ : G} :
    rees_mul P (some (i₁, g₁, j₁)) (some (i₂, g₂, j₂)) ≠ none
      ↔ (g₁ ≠ 0 ∧ P j₁ i₂ ≠ 0 ∧ g₂ ≠ 0) := by
  -- use the previous iff and De Morgan
  have h := rees_mul_some_some_eq_none_iff (P:=P)
            (i₁:=i₁) (i₂:=i₂) (j₁:=j₁) (j₂:=j₂) (g₁:=g₁) (g₂:=g₂)
  constructor
  · intro hne
    have not_disj : ¬ (g₁ = 0 ∨ P j₁ i₂ = 0 ∨ g₂ = 0) := by
      intro disj
      exact hne ((h.mpr) disj)
    refine ⟨?_, ?_, ?_⟩
    · intro hg1; exact not_disj (Or.inl hg1)
    · intro hP;  exact not_disj (Or.inr (Or.inl hP))
    · intro hg2; exact not_disj (Or.inr (Or.inr hg2))
  · intro ⟨hg1, hP, hg2⟩
    -- with all three nonzero, the guard is false, so result is `some …` hence ≠ none
    unfold ReesMatrix0.rees_mul
    set prod := g₁ * P j₁ i₂ * g₂
    have h12 : g₁ * P j₁ i₂ ≠ 0 := mul_ne_zero hg1 hP
    have hprod : prod ≠ 0 := mul_ne_zero h12 hg2
    by_cases hzero : prod = 0
    · exact (hprod hzero).elim
    · simp [prod, hzero]
@[simp] lemma rees_mul_some_left_zero
    {i₁ i₂ : I} {j₁ j₂ : J} {g₂ : G} :
    rees_mul P (some (i₁, 0, j₁)) (some (i₂, g₂, j₂)) = none := by
  simpa using
    (ReesMatrix0.rees_mul_some_some_eq_none_iff (P:=P)
      (i₁:=i₁) (i₂:=i₂) (j₁:=j₁) (j₂:=j₂) (g₁:=0) (g₂:=g₂)).mpr (Or.inl rfl)

@[simp] lemma rees_mul_some_right_zero
    {i₁ i₂ : I} {j₁ j₂ : J} {g₁ : G} :
    rees_mul P (some (i₁, g₁, j₁)) (some (i₂, 0, j₂)) = none := by
  simpa using
    (ReesMatrix0.rees_mul_some_some_eq_none_iff (P:=P)
      (i₁:=i₁) (i₂:=i₂) (j₁:=j₁) (j₂:=j₂) (g₁:=g₁) (g₂:=0)).mpr (Or.inr <| Or.inr rfl)
@[simp] lemma rees_mul_some_some_val_of_ne_zero
    {i₁ i₂ : I} {j₁ j₂ : J} {g₁ g₂ : G}
    (hg₁ : g₁ ≠ 0) (hP : P j₁ i₂ ≠ 0) (hg₂ : g₂ ≠ 0) :
    rees_mul P (some (i₁, g₁, j₁)) (some (i₂, g₂, j₂))
      = some (i₁, g₁ * P j₁ i₂ * g₂, j₂) := by
  -- just unfold once; `simp` kills the `if` using zero-iff lemma
  unfold ReesMatrix0.rees_mul
  have : g₁ * P j₁ i₂ * g₂ ≠ 0 := by
    have := (ReesMatrix0.mul_mul_eq_zero (a:=g₁) (b:=P j₁ i₂) (c:=g₂))
    -- rewrite: ¬(prod=0) using (a=0 ∨ b=0 ∨ c=0) ↔ …
    exact by
      intro h
      have : g₁ = 0 ∨ P j₁ i₂ = 0 ∨ g₂ = 0 := by
        simpa [h] using this.mp h
      rcases this with h1 | hP' | h2
      · exact (hg₁ h1)
      · exact (hP  hP')
      · exact (hg₂ h2)
  simp [this]
@[simp] lemma rees_mul_eq_some_iff
    {i₁ i₂ i : I} {j₁ j₂ j : J} {g₁ g₂ g : G} :
    rees_mul P (some (i₁, g₁, j₁)) (some (i₂, g₂, j₂)) = some (i, g, j)
      ↔ (i = i₁ ∧ j = j₂ ∧ g = g₁ * P j₁ i₂ * g₂ ∧
          g₁ ≠ (0 : G) ∧ P j₁ i₂ ≠ (0 : G) ∧ g₂ ≠ (0 : G)) := by
  classical
  constructor
  · intro h
    -- not-none ⇒ all three factors are nonzero
    have hne :
      rees_mul P (some (i₁, g₁, j₁)) (some (i₂, g₂, j₂)) ≠ none := by
      simp_all only [rees_mul_eq_mul, ne_eq, reduceCtorEq, not_false_eq_true]
    have hnz := (rees_mul_some_some_ne_none_iff (P:=P)
                  (i₁:=i₁) (j₁:=j₁) (i₂:=i₂) (j₂:=j₂) (g₁:=g₁) (g₂:=g₂)).mp hne
    rcases hnz with ⟨hg₁, hPnz, hg₂⟩
    -- if all three factors are nonzero, 'rees_mul' returns the 'some' branch
    have hsome :
      rees_mul P (some (i₁, g₁, j₁)) (some (i₂, g₂, j₂))
        = some (i₁, g₁ * P j₁ i₂ * g₂, j₂) :=
      rees_mul_some_some_val_of_ne_zero (P:=P) hg₁ hPnz hg₂
    -- compare the two `some`'s
    have htrip : (i₁, g₁ * P j₁ i₂ * g₂, j₂) = (i, g, j) :=
      Option.some.inj (Eq.trans (Eq.symm hsome) h)
    -- `(i, g, j)` is `Prod I (Prod G J)`:
    -- first component (I)
    have hi : i₁ = i := congrArg Prod.fst htrip
    -- second component is a pair (G × J)
    have hgj : (g₁ * P j₁ i₂ * g₂, j₂) = (g, j) := congrArg Prod.snd htrip
    have hg : g₁ * P j₁ i₂ * g₂ = g := congrArg Prod.fst hgj
    have hj : j₂ = j := congrArg Prod.snd hgj

    exact ⟨hi.symm, hj.symm, hg.symm, hg₁, hPnz, hg₂⟩
  · rintro ⟨hi, hj, hg, hg₁, hPnz, hg₂⟩
    have hsome :
      rees_mul P (some (i₁, g₁, j₁)) (some (i₂, g₂, j₂))
        = some (i₁, g₁ * P j₁ i₂ * g₂, j₂) :=
      rees_mul_some_some_val_of_ne_zero (P:=P) hg₁ hPnz hg₂
    simpa [hi, hj, hg] using hsome

@[simp] lemma rees_mul_neq_none_iff
    {i₁ i₂ i : I} {j₁ j₂ j : J} {g₁ g₂ g : G} :
    rees_mul P (some (i₁, g₁, j₁)) (some (i₂, g₂, j₂)) ≠ none
      ↔ g₁ ≠ (0 : G) ∧ P j₁ i₂ ≠ (0 : G) ∧ g₂ ≠ (0 : G) := by
      exact rees_mul_some_some_ne_none_iff P



instance (P : J → I → G) : Semigroup (ReesMatrix P) where
  mul := Mul.mul
  mul_assoc := by
    intro a b c
    cases a <;> cases b <;> cases c <;>
      simp [ReesMatrix0.rees_mul, ReesMatrix0.mul_eq_rees_mul, mul_assoc]
    rename_i val val_1 val_2
    simp_all only [or_false]
    obtain ⟨fst, snd⟩ := val
    obtain ⟨fst_1, snd_1⟩ := val_1
    obtain ⟨fst_2, snd_2⟩ := val_2
    obtain ⟨fst_3, snd⟩ := snd
    obtain ⟨fst_4, snd_1⟩ := snd_1
    obtain ⟨fst_5, snd_2⟩ := snd_2
    simp_all only
    split
    next h =>
        cases h with
        | inl h_1 =>
          subst h_1
          simp_all only [true_or, ↓reduceIte, ite_self]
        | inr h_2 =>
          cases h_2 with
          | inl h => simp_all only [or_true, ↓reduceIte, ite_self]
          | inr h_1 =>
            subst h_1
            simp_all only [true_or, ↓reduceIte]
    next h => simp_all only [not_or, false_or, or_self, ↓reduceIte]


end ReesMatrix0

namespace ReesMatrixNonzero

variable {I J G : Type} (P : J → I → G) {Nonempty I} {Nonempty J} [Group G][DecidableEq G]

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

@[simp] lemma coe_mul_as_some (a b : ReesMatrixNonzero P) :
    ((a * b : ReesMatrixNonzero P) : ReesMatrix P)
      = some (a.1, a.2.1 * P a.2.2 b.1 * b.2.1, b.2.2) := by
  cases a <;> cases b <;> rfl
@[simp] lemma fst_mul (x y : ReesMatrixNonzero P) : (x * y).1 = x.1 := by
  cases x <;> cases y <;> rfl

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


lemma R_equiv_iff_same_i {a b : ReesMatrixNonzero P} :
    a 𝓡 b ↔ a.1 = b.1 := by
  apply Iff.intro
  · intro hR
    obtain ⟨ha, hb⟩ := hR
    rcases a with ⟨i₁, g₁, j₁⟩
    rcases b with ⟨i₂, g₂, j₂⟩
    obtain ⟨c, hc⟩ := ha
    cases c <;>
    simp at *
    exact (Prod.mk.inj hc).1
    rename_i a
    rcases a with ⟨i₃, g₃, j₃⟩
    injection hc with h
    simp[ReesMatrix0.rees_mul] at h
    have : rees_mul_nz P (i₂, g₂, j₂) (i₃, g₃, j₃) = (i₂, g₂ * P j₂ i₃ * g₃, j₃) := by
      unfold rees_mul_nz; simp_all
    have : (i₁, g₁, j₁) = (i₂, g₂ * P j₂ i₃ * g₃, j₃) := by simp_all[h]; exact this
    exact (Prod.mk.inj this).1
  · intro a_1
    rcases a with ⟨i₁, g₁, j₁⟩
    rcases b with ⟨i₂, g₂, j₂⟩
    let c : ReesMatrixNonzero P := (i₂, (P j₁ i₂)⁻¹ * g₁⁻¹ * g₂, j₂)
    have hac : rees_mul_nz P (i₁, g₁, j₁)  c = (i₂, g₂, j₂) := by
      unfold rees_mul_nz; simp_all[c, <-mul_assoc]
    let d : ReesMatrixNonzero P := (i₁, (g₂  * P j₂ i₁)⁻¹ * g₁, j₁)
    have had : rees_mul_nz P (i₂, g₂, j₂) d = (i₁, g₁, j₁) := by
      unfold rees_mul_nz; simp_all[d, <-mul_assoc]
    unfold R_eqv; unfold R_preorder
    constructor
    · use (d : _); rw[had.symm]; rfl
    · use (c : _); simp[hac.symm]; rfl

  lemma L_equiv_iff_same_j {a b : ReesMatrixNonzero P} :
    a 𝓛 b ↔ a.2.2 = b.2.2 := by
  apply Iff.intro
  · intro hR
    obtain ⟨ha, hb⟩ := hR
    rcases a with ⟨i₁, g₁, j₁⟩
    rcases b with ⟨i₂, g₂, j₂⟩
    obtain ⟨c, hc⟩ := ha
    cases c <;>
    simp at *
    exact (Prod.mk.inj (Prod.mk.inj hc).2).2
    rename_i a
    rcases a with ⟨i₃, g₃, j₃⟩
    injection hc with h
    simp[ReesMatrix0.rees_mul] at h
    have : rees_mul_nz P (i₃, g₃, j₃) (i₂, g₂, j₂) = (i₃, g₃ * P j₃ i₂ * g₂, j₂) := by
      unfold rees_mul_nz; simp_all
    have : (i₁, g₁, j₁) = (i₃, g₃ * P j₃ i₂ * g₂, j₂) := by simp_all[h]; exact this
    exact (Prod.mk.inj (Prod.mk.inj this).2).2
  · intro a_1
    rcases a with ⟨i₁, g₁, j₁⟩
    rcases b with ⟨i₂, g₂, j₂⟩
    let c : ReesMatrixNonzero P := (i₂, g₂ * (P j₂ i₁ * g₁)⁻¹, j₂)
    have hac : rees_mul_nz P c (i₁, g₁, j₁)  = (i₂, g₂, j₂) := by
      unfold rees_mul_nz; simp_all[c, <-mul_assoc]
    let d : ReesMatrixNonzero P := (i₁, g₁ * (P j₂ i₂ * g₂)⁻¹, j₁)
    have had : rees_mul_nz P d (i₂, g₂, j₂) = (i₁, g₁, j₁) := by
      unfold rees_mul_nz; simp_all[d, <-mul_assoc]
    unfold L_eqv; unfold L_preorder
    constructor
    · use (d : _); rw[had.symm]; rfl
    · use (c : _); simp[hac.symm]; rfl


section withZero
variable {I J G : Type} (P : J → I → G)
  [DecidableEq G] [GroupWithZero G]
@[simp] theorem coe_mul_of_nonzero
    (a b : ReesMatrixNonzero P)
    (hg₁ : a.2.1 ≠ (0 : G)) (hP : P a.2.2 b.1 ≠ (0 : G)) (hg₂ : b.2.1 ≠ (0 : G)) :
    (a * b : ReesMatrix P) = ReesMatrix0.rees_mul P (↑a) (↑b) := by
  classical
  rcases a with ⟨i₁, g₁, j₁⟩
  rcases b with ⟨i₂, g₂, j₂⟩
  simp_all only [ne_eq]; rfl
end withZero
end ReesMatrixNonzero

section ReesMatrixPreamble
variable {G : Type } {I : Type } {J : Type } {S : Type*} (P : J → I → G) [Nonempty I] [Nonempty J]
  [GroupWithZero G][Semigroup S]

/- Prop 3.1 (about simple/zero simple)-- to move? may fit better
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
  Ideal'.isZeroSimple S ↔ (∃ a b : S, a * b ≠ 0) ∧ ∀ a : S, a ≠ 0 → Ideal'.principal a = ⊤ := by
  constructor
  -- forward: isZeroSimple → (∃ a b, a*b ≠ 0) ∧ (∀ nonzero a, principal a = ⊤)
  · intro h
    -- isZeroSimple gives two witnesses with a nonzero product and the "all ideals are ∅, {0}, ⊤" property
    obtain ⟨⟨a, b, hab⟩, h_ideals⟩ := h
    constructor
    · use a, b -- we proved a nonzero product exists
    · intro x hx
      -- we show that (x) generateds the whole semigroup
      -- `cases : Ideal'.principal x = ∅ ∨ ↑(Ideal'.principal x) = {0} ∨ Ideal'.principal x = ⊤`
      have cases := h_ideals (Ideal'.principal x)

      -- first split `I = ∅ ∨ ↑I = {0} ∨ I = ⊤` into two steps
      cases cases with
      | inl h_empty =>
        -- principal x = ∅, contradiction b/c x ∈ principal x
        have x_in : x ∈ (Ideal'.principal x : Set S) := by
          simp [Ideal'.principal, Ideal'.ofSet_coe, LeftIdeal.ofSet_coe, RightIdeal.ofSet_coe]
        -- coerce the Ideal' equality to a Set equality then rewrite
        have set_eq : (Ideal'.principal x : Set S) = ∅ := congrArg (fun (I : Ideal' S) => (I : Set S)) h_empty
        rw [set_eq] at x_in
        simp at x_in

      | inr rest =>
        -- now rest : ↑(Ideal'.principal x) = {0} ∨ Ideal'.principal x = ⊤
        cases rest with
        | inl h_singleton =>
          -- ↑(principal x) = {0}. Again impossible b/c x ≠ 0
          have x_in : x ∈ (Ideal'.principal x : Set S) := by
            simp [Ideal'.principal, Ideal'.ofSet_coe, LeftIdeal.ofSet_coe, RightIdeal.ofSet_coe]
          rw [h_singleton] at x_in
          simp at x_in
          contradiction
        | inr h_top =>
          -- principal x = ⊤, done
          exact h_top


  -- reverse: (∃ a b, a*b ≠ 0) ∧ (∀ nonzero a, principal a = ⊤) → isZeroSimple
  · intro ⟨⟨a, b, hab⟩, h_all_principal⟩
    constructor
    · -- provide the witness ∃ a b, a*b ≠ 0
      use a, b, hab
    · -- show: every ideal I is ∅ or {0} or ⊤
      intro I
      -- if I = ∅, we are done
      by_cases hI : I = ∅
      · left; exact hI

      -- if I ≠ ∅, we can pick x ∈ I
      have ⟨x, hx⟩ := Ideal'.exists_mem_of_ne_empty hI

      -- two cases: x = 0 or x ≠ 0
      by_cases hx_zero : x = 0
      · by_cases h_single : (I : Set S) = {0}
        · right; left; exact h_single -- if I = {0}, we're done
        · -- otherwise, we can pick a nonzero element y
          have : ∃ y, y ∈ I ∧ y ≠ 0 := by
            by_contra H
            -- H : ¬ ∃ y, y ∈ I ∧ y ≠ 0
            -- so ∀ y, y ∈ I → y = 0
            have subset : (I : Set S) ⊆ {0} := by
              intro z hz
              by_contra hzne
              apply H
              use z
              constructor; assumption; exact hzne
            -- show {0} ⊆ I because I is nonempty, so 0 ∈ I (we find a z ∈ I and show z * 0 ∈ I)
            obtain ⟨z, hz⟩ := Ideal'.exists_mem_of_ne_empty hI
            have zero_in : (0 : S) ∈ I := by
              -- z * 0 ∈ I and z * 0 = 0
              have : z * 0 ∈ I := I.mul_right_mem hz
              simpa using this
            have ssubset : {0} ⊆ (I : Set S) := by --this is the reverse inclusion
              intro a ha
              simp [Set.mem_singleton_iff] at ha
              subst a; exact zero_in
            have eq : (I : Set S) = ({0} : Set S) := by
              ext a
              constructor
              · intro ha
                apply subset
                exact ha
              · intro ha
                apply ssubset
                exact ha
            -- contradiction with `h_single : ¬ ((I : Set S) = {0})`
            contradiction
          -- obtain witness and finish: principal y = ⊤ and principal y ≤ I ⇒ I = ⊤
          obtain ⟨y, hy_in, hy_ne⟩ := this
          have hy_top : Ideal'.principal y = ⊤ := h_all_principal y hy_ne
          have : Ideal'.principal y ≤ I := Ideal'.ofSet_minimal (Set.singleton_subset_iff.mpr hy_in)
          subst hx_zero
          simp_all only [ne_eq, not_false_eq_true, false_or]
          ext x : 1
          apply Iff.intro
          · intro a_1
            apply SetLike.mem_of_subset
            · simp_all only [Ideal'.coe_top, Set.subset_univ]
            · exact a_1
          · intro a_1
            apply this
            simp_all only

      · -- subcase x ≠ 0. Then principal x = ⊤ by hypothesis, and sice (x) ≤ I, done
        right; right
        have hx_top : Ideal'.principal x = ⊤ := h_all_principal x hx_zero
        have : Ideal'.principal x ≤ I := Ideal'.ofSet_minimal (Set.singleton_subset_iff.mpr hx)
        simp_all only [ne_eq, not_false_eq_true]
        ext x_1 : 1
        apply Iff.intro
        · intro a_1
          apply SetLike.mem_of_subset
          · simp_all only [Ideal'.coe_top, Set.subset_univ]
          · exact a_1
        · intro a_1
          apply this
          simp_all only





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

@[simp] abbrev zero_regular_semigroup (S : Type*) [SemigroupWithZero S] :=
  regular_semigroup S

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
lemma zero_regular_iff_J_regular (S : Type*) [SemigroupWithZero S] :
  regular_semigroup S ↔ all_J_classes_regular S :=
  regular_iff_J_regular S

lemma regular_semigroup.of_mul_equiv
  {S T : Type*} [Semigroup S] [Semigroup T]
  (e : S ≃* T) (hS : regular_semigroup S) :
  regular_semigroup T := by
    intro y
    obtain ⟨x, rfl⟩ := e.surjective y
    obtain ⟨s, hs⟩ := hS x
    use e s
    rw [← e.map_mul, ← e.map_mul, hs]

lemma zero_regular_semigroup.of_mul_equiv
  {S T : Type*} [SemigroupWithZero S] [SemigroupWithZero T]
  (e : S ≃* T) (hS : regular_semigroup S) :
  regular_semigroup T := by
    intro y
    obtain ⟨x, rfl⟩ := e.surjective y
    obtain ⟨s, hs⟩ := hS x
    use e s
    rw [← e.map_mul, ← e.map_mul, hs]

@[simp] lemma nonzero_J_class_nonzero
  {S : Type*} [SemigroupWithZero S]
  (J1 : Set S) (hJ : is_J_class J1)
  (hne : J1 ≠ {0}) : ∀ e ∈ J1, e ≠ 0 := by
    intro e he
    by_contra h
    subst h
    have : J1 = {0} := by
      simp_all only [ne_eq]
      unfold is_J_class at hJ
      obtain ⟨x, hx⟩ := hJ
      subst hx
      unfold J_class_set at he hne
      simp_all only [Set.mem_setOf_eq]
      unfold J_eqv at he ; unfold eqv_of_preorder at he; unfold J_preorder at he
      obtain ⟨ha, hb⟩ := he
      have : x = 0 := by
        obtain ⟨s, y, hs⟩ := hb
        sorry
      sorry
    contradiction
 /- this is Theorem 3.2-/

open ReesMatrixNonzero
attribute [simp] mul_inv_cancel₀ inv_mul_cancel₀

@[simp] lemma hmul_eq {S : Type*} [SemigroupWithZero S]:
  @HMul.hMul S S S (@instHMul S MulZeroClass.toMul) =
  @HMul.hMul S S S (@instHMul S Semigroup.toMul) :=
by ext; rfl

lemma semigroupWithZero_hmul_eq {S : Type*} [SemigroupWithZero S] :
    @HMul.hMul S S S (@instHMul S SemigroupWithZero.toSemigroup.toMul) =
    @HMul.hMul S S S (@instHMul S SemigroupWithZero.toMulZeroClass.toMul) :=
by ext; rfl

end ReesMatrixPreamble

section ReesMatrixTheorems
set_option maxHeartbeats 400000
variable {G : Type } {I : Type } {J : Type } {S : Type} (P : J → I → G) [Nonempty I] [Nonempty J]
  [DecidableEq G] [GroupWithZero G] [SemigroupWithZero S]


theorem zero_simple_iff_rees [Finite S] :
        Ideal'.isZeroSimple S ↔
        ∃ (I J : Type)  (P : J → I → G) (iso : S ≃* ReesMatrix P),
        Nonempty I ∧ Nonempty J ∧ Nonempty G ∧ (∀ x : S, is_regular x) ∧
        (∃ a b : S, a * b ≠ 0) ∧
        (∀ a : S, a ≠ 0 → ∃ (i : I) (g : G) (j : J),
        iso a = (some (i, g, j) : ReesMatrix P)) := by
  simp_all only [ne_eq, exists_and_left]
  apply Iff.intro
  · intro a
    sorry
  · intro ⟨I, neI, J, neJ, neG, regS, hab, P, iso, nzerorep⟩
    have hr := (zero_simple_iff_ideals S)
    simp[hr]
    constructor
    · exact hab
    · intro a
      have hnzideal : a ≠ 0 → ⊤ = Ideal'.principal (iso a) := by
        intro ha
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
        have t3 := t.out 0 5
        obtain ⟨x, hx⟩ := t1
        obtain ⟨y, hy⟩ := t2
        have xJ := x hjreg a ainJ ; obtain ⟨e1, hs⟩ := xJ
        have yJ := y hjreg a ainJ ; obtain ⟨e2, ht⟩ := yJ
        rename a ≠ 0 => han
        have he1 : e1 ≠ 0 := by
          have := hs.2; apply nonzero_J_class_nonzero J1 _
          simp_all [J1]
          obtain ⟨w, h⟩ := hab
          obtain ⟨w_1, h_1⟩ := hjreg
          obtain ⟨left, right⟩ := ht
          obtain ⟨w_2, h⟩ := h
          obtain ⟨left_1, right_1⟩ := h_1
          obtain ⟨w_3, h_1⟩ := right_1
          obtain ⟨left_2, right_1⟩ := h_1
          apply Aesop.BuiltinRules.not_intro
          intro a_1
          simp_all only [Set.mem_singleton_iff, J1]
          simp_all only [hmul_eq, ne_eq, true_and, implies_true, exists_and_left, true_iff, forall_const, imp_self,
            and_true, in_R_implies_in_J, J1]
          exact hJ
        have he2 : e2 ≠ 0 := by
          have := ht.2;
          apply nonzero_J_class_nonzero J1 _
          simp[ainJ]
          simp_all [J1]
          obtain ⟨w, h⟩ := hab
          obtain ⟨w_1, h_1⟩ := hjreg
          obtain ⟨left, right⟩ := hs
          obtain ⟨w_2, h⟩ := h
          obtain ⟨left_1, right_1⟩ := h_1
          obtain ⟨w_3, h_1⟩ := right_1
          obtain ⟨left_2, right_1⟩ := h_1
          apply Aesop.BuiltinRules.not_intro
          intro a_1
          simp_all only [Set.mem_singleton_iff, J1]
          simp_all only [hmul_eq, ne_eq, true_and, implies_true, exists_and_left, true_iff, forall_const, imp_self,
            and_true, in_L_implies_in_J, J1]
          exact hJ
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
            have iso_symm_none_zero : iso.symm none = 0 := by
                by_contra hn
                obtain ⟨i_0, g_0, h_0, hh⟩ := nzerorep (iso.symm none) hn
                rw [iso.apply_symm_apply] at hh
                cases hh
            have hd0 : iso.symm d ≠ 0 := by
              contrapose! hx0
              have h : iso (iso.symm d) = iso 0 := congrArg iso hx0
              rw [iso.apply_symm_apply] at h
              have : iso 0 = none := by
                have := congrArg iso iso_symm_none_zero
                simp[iso.apply_symm_apply none] at this
                exact this.symm
              simp[h, this]
            obtain ⟨i₂, g₂, j₂, hd⟩ := nzerorep (iso.symm d) (hd0)
            have P1 : P j₁ s ≠ 0 := by
              by_contra h
              have : ReesMatrix0.rees_mul P (some (i₁, g₁, j₁)) (some (s, g₄, j₄)) = none := by
                unfold ReesMatrix0.rees_mul; simp_all only [hmul_eq, implies_true, ne_eq, true_and, exists_and_left,
                  forall_const, imp_self, MulEquiv.apply_symm_apply, mul_zero, zero_mul, ↓reduceIte, J1]
              rw[he2.symm, ha.symm] at this
              have h0 : a * e2 = 0 := by
                have h2 := congrArg iso.symm this
                simp[iso.apply_symm_apply (iso e2)] at h2
                simp[iso_symm_none_zero] at h2; exact h2
              have hn0 : a * e2 ≠ 0 := by
                have:= ht.left
                unfold L_class_set at this
                simp_all
                obtain ⟨⟨z, hz⟩, x,hx⟩ := this
                obtain ⟨b, hb⟩ := regS a
                have httr : e2 * e2 = e2 := by
                  let htr := ht.right
                  unfold IsIdempotentElem at htr
                  exact htr
                have: (a * e2 : WithOne S) = (a : WithOne S) := by
                    calc
                    a * e2 = (x * e2) * e2 := by simp[hx]
                    _ = x * (e2 * e2) := by simp[<-mul_assoc]
                    _ = x * ↑(e2) := by rw[<- WithOne.coe_mul, httr]
                    _ = ↑a := by rw[hx]
                have := WithOne.coe_inj.mp this; simp_all
              exact hn0 h0
            have P2 : P r i₁ ≠ 0 := by
              by_contra h
              have : ReesMatrix0.rees_mul P (some (i₃, g₃, r)) (some (i₁, g₁, j₁)) = none := by
                unfold ReesMatrix0.rees_mul; simp_all[h]
              rw[he1.symm, ha.symm] at this
              have h0 : e1 * a = 0 := by
                have h1 := congrArg iso.symm this
                simp[iso.apply_symm_apply (iso e1)] at h1
                simp[iso_symm_none_zero] at h1; exact h1
              have hn0 : e1 * a ≠ 0 := by
                have:= hs.left
                unfold R_class_set at this
                simp at *
                obtain ⟨⟨z, hz⟩, x,hx⟩ := this
                obtain ⟨b, hb⟩ := regS a
                have httr : e1 * e1 = e1 := by
                  let htr := hs.right
                  unfold IsIdempotentElem at htr
                  exact htr
                have hwo: (e1 * a : WithOne S) = (a : WithOne S) := by
                    calc
                    e1 * a = e1 * (e1 * x) := by simp[hx]
                    _ = (e1 * e1) * x := by simp[<-mul_assoc]
                    _ = ↑(e1) * x := by rw[<- WithOne.coe_mul, httr]
                    _ = ↑a := by rw[hx]
                have := WithOne.coe_inj.mp hwo; subst hd; simp_all only [J1]
              exact hn0 h0
            have: g₁ ≠ 0 := by
              by_contra h
              have : ReesMatrix0.rees_mul P (some (i₃, g₃, r)) (some (i₁, g₁, j₁)) = none := by
                unfold ReesMatrix0.rees_mul;
                subst h
                simp_all only [hmul_eq, implies_true, ne_eq, true_and, exists_and_left, forall_const, imp_self,
                  MulEquiv.apply_symm_apply, mul_zero, ↓reduceIte, J1]
              rw[he1.symm, ha.symm] at this
              have h0 : e1 * a = 0 := by
                have h1 := congrArg iso.symm this
                simp[iso.apply_symm_apply (iso e1)] at h1
                simp[iso_symm_none_zero] at h1; exact h1
              have hn0 : e1 * a ≠ 0 := by
                have:= hs.left
                unfold R_class_set at this
                simp at *
                obtain ⟨⟨z, hz⟩, x,hx⟩ := this
                obtain ⟨b, hb⟩ := regS a
                have httr : e1 * e1 = e1 := by
                  let htr := hs.right
                  unfold IsIdempotentElem at htr
                  exact htr
                have hwo: (e1 * a : WithOne S) = (a : WithOne S) := by
                    calc
                    e1 * a = e1 * (e1 * x) := by simp[hx]
                    _ = (e1 * e1) * x := by simp[<-mul_assoc]
                    _ = ↑(e1) * x := by rw[<- WithOne.coe_mul, httr]
                    _ = ↑a := by rw[hx]
                have := WithOne.coe_inj.mp hwo; subst hd; simp_all only [J1]
              exact hn0 h0
            have: g₂ ≠ 0 := by sorry
            let A : ReesMatrix P := some (i₂, g₁⁻¹ * (P r i₁)⁻¹, r)
            let B : ReesMatrix P := some (s, (P j₁ s)⁻¹ * g₂, j₂)
            let mid : ReesMatrix P := some (i₁, g₁ * P j₁ s * ((P j₁ s)⁻¹  * g₂), j₂)
            let mid' : ReesMatrix P := some (i₂, 1, j₁)
            have h1 : (iso a) * B = mid := by
              rw[ha]; simp[B, mid]
              simp_all
              have : ReesMatrix0.rees_mul P (some (i₁, g₁, j₁)) (some (s, (P j₁ s)⁻¹ * g₂, j₂)) = some (i₁, g₁ * P j₁ s * ((P j₁ s)⁻¹ * g₂), j₂) := by
                 unfold ReesMatrix0.rees_mul ;
                 subst hd
                 simp_all only [hmul_eq, mul_eq_zero, or_self, inv_eq_zero, ↓reduceIte, J1, mid, B]
              exact this
            have h1' : A * (iso a) = mid' := by
              rw[ha];
              simp[A, mid']
              have : ReesMatrix0.rees_mul P (some (i₂, g₁⁻¹ * (P r i₁)⁻¹, r)) (some (i₁, g₁, j₁)) = some (i₂, 1, j₁) := by
                unfold ReesMatrix0.rees_mul ; simp_all only [hmul_eq, implies_true, ne_eq, true_and, exists_and_left,
                  forall_const, imp_self, MulEquiv.apply_symm_apply, isUnit_iff_ne_zero, not_false_eq_true,
                  IsUnit.inv_mul_cancel_right, IsUnit.inv_mul_cancel, one_ne_zero, ↓reduceIte, A, J1, mid, B, mid']
              exact this
            have h2 : A * mid = some (i₂, g₂, j₂) := by
              simp[A, mid]
              set lhs := (g₁⁻¹ * (P r i₁)⁻¹) * P r i₁ * (g₁ * P j₁ s * ((P j₁ s)⁻¹ * g₂))
              have lh : lhs = g₂ := by simp_all[lhs, mul_assoc]
              rw [<-lh]; simp[<-mul_assoc]; simp[mul_assoc, mul_inv_cancel₀ P1]
              simp_all only [ne_eq, implies_true, exists_and_left, forall_const, imp_self, isUnit_iff_ne_zero,
                    not_false_eq_true, IsUnit.inv_mul_cancel_right, IsUnit.inv_mul_cancel_left, mid, B, lhs, A, J1]
              have : ReesMatrix0.rees_mul P (some (i₂, g₁⁻¹ * (P r i₁)⁻¹, r)) (some (i₁, g₁ * g₂, j₂)) = some (i₂, g₂, j₂) := by
                    unfold ReesMatrix0.rees_mul ; simp_all only [hmul_eq, true_and, MulEquiv.apply_symm_apply,
                      isUnit_iff_ne_zero, ne_eq, not_false_eq_true, IsUnit.inv_mul_cancel_right,
                      IsUnit.inv_mul_cancel_left, ↓reduceIte, A, J1, lhs, mid, B, mid']
              exact this
            have h2' : mid' * B = some (i₂, g₂, j₂) := by
              simp_all only [A, mid', B]
              have : ReesMatrix0.rees_mul P (some (i₂, 1, j₁)) (some (s, (P j₁ s)⁻¹ * g₂, j₂)) = some (i₂, g₂, j₂) := by
                    unfold ReesMatrix0.rees_mul ; simp_all [↓reduceIte, A, J1, mid, B, mid']
              exact this
            have hAB : A * ((iso a) * B) = iso (iso.symm d) := by simp[h1, h2, hd]
            have hAB' : (A * (iso a)) * B = iso (iso.symm d) := by simp[h1', h2', hd]
            have hI : iso (iso.symm d) ∈ Ideal'.ofSet ({iso a}) := by
              simp_all only [ne_eq, implies_true, exists_and_left, forall_const, imp_self]
              unfold Ideal'.ofSet
              left; left; unfold Set.mul
              use mid'
              have : ReesMatrix0.rees_mul P (some (i₂, g₁⁻¹ * (P r i₁)⁻¹, r)) (some (i₁, g₁, j₁)) = some (i₂, 1, j₁) := by
                    unfold ReesMatrix0.rees_mul ; simp_all only [hmul_eq, implies_true, ne_eq, true_and, exists_and_left,
                      forall_const, imp_self, MulEquiv.apply_symm_apply, isUnit_iff_ne_zero, not_false_eq_true,
                      IsUnit.inv_mul_cancel_right, IsUnit.inv_mul_cancel, one_ne_zero, ↓reduceIte, A, J1, mid, B, mid']
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
      intro haa
      have : Ideal'.principal (iso a) = ⊤ := by simp_all only [ne_eq, true_and, not_false_eq_true, forall_const]
      ext x
      constructor
      · intro _; trivial
      · intro _
        have hmem : iso x ∈ Ideal'.principal (iso a) := by
          rw [this]; trivial
        simp [Ideal'.principal, Ideal'.ofSet] at hmem
        rcases hmem
        · refine SetLike.mem_coe.mp ?_; unfold Ideal'.principal; simp
          rename_i h1
          simp_all
          cases h1
          · simp_all
          · rename_i h2
            cases h2
            · rename_i h
              left; right; left
              rcases h with ⟨y, hy⟩
              simp_all
              obtain ⟨⟨x1, hx1⟩, ⟨x2, hx2⟩⟩ := hy
              apply_fun iso.symm at hx1
              apply_fun iso.symm at hx2
              simp at hx1; simp at hx2
              use (iso.symm y); simp
              subst hx2
              simp_all only [exists_apply_eq_apply, and_true]
              obtain ⟨w, h⟩ := hab
              obtain ⟨w_1, h⟩ := h
              apply Exists.intro
              · exact hx1
            · rename_i h
              obtain ⟨y, hy⟩ := h
              apply_fun iso.symm at hy; simp at hy
              subst hy
              simp_all only [exists_apply_eq_apply, or_true, true_or]
        · refine SetLike.mem_coe.mp ?_; unfold Ideal'.principal
          refine Or.symm (Or.inl ?_); left
          rename_i h
          rcases h with ⟨y, hy⟩
          apply_fun iso.symm at hy
          simp only [map_mul, MulEquiv.symm_apply_apply, hmul_eq] at hy
          use a
          constructor
          . simp
          use iso.symm y
          have : iso.symm y ∈ Set.univ := by simp
          constructor; exact this
          exact hy


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

instance : DecidableEq G2WZ := by
  intro x y; cases x; cases y
  simp; exact instDecidableTrue
  simp; exact instDecidableFalse
  rename_i a;
  cases y
  simp; exact instDecidableFalse
  rename_i b
  cases decEq a b with
  | isTrue h => exact isTrue (by rw[h])
  | isFalse h => exact isFalse (by intro eq; injection eq with h'; exact h h')



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
