import MyProject.GreensRelations.Decidable

/-!
# Basic Properties of Green's Relations

This file establishes fundamental properties of Green's relations in semigroups, particularly
in finite semigroups.

## Main statements

* `R_eqv_right_cancel`, `L_eqv_left_cancel`: Cancellation properties of 𝓡 and 𝓛 relations
* `exists_pow_sandwich_eq_self`: A key lemma in proofs on Finite Semigroups.
* `D_iff_J_finite`: The D-J theorem for finite semigroups
* `le_R_idempotent`, `le_L_idempotent`: Characterization of elements below idempotents
* `R_eqv_of_J_mul_right`, `L_eqv_of_J_mul_left`: Shows how 𝓙 equivilance "strengthens"
  𝓡 and 𝓛 preorders to equivalences in finite semigroups.

## TODO
* Finish Greens Lemma
-/

/-! ### Simp Lemmas
This section provides lemmas tagged with @[simp]. For lemmas that take hypothesis
like `h : a ≤𝓡 a * b`, make sure that you call `simp [h]` to use them. -/

section Simp_Lemmas

variable {S} [Semigroup S] (a x y : S)

/-- `a * x` is always `≤𝓡 a` -/
@[simp] lemma mul_right_R_preorder_self : a * x ≤𝓡 a := by
  use x; rw [WithOne.coe_mul]

/-- `x * a` is always `≤𝓛 a` -/
@[simp] lemma mul_left_L_preorder_self : x * a ≤𝓛 a := by
  use x; rw [WithOne.coe_mul]

/-- `x * a * y` is always `≤𝓙 a` -/
@[simp] lemma mul_sandwich_J_preorder_self : x * a * y ≤𝓙 a := by
  use x, y; simp

variable {a x y : S}

/-- `a ≤𝓡 a * x` implies `a 𝓡 a * x` -/
@[simp] lemma R_eqv_of_R_preorder_mul_right (h : a ≤𝓡 a * x) : a 𝓡 a * x := by
  simpa [R_eqv_iff]

/-- `a ≤𝓛 x * a` implies `a 𝓛 b * a` -/
@[simp] lemma L_eqv_of_L_preorder_mul_left (h : a ≤𝓛 x * a) : a 𝓛 x * a := by
  simpa [L_eqv_iff]

/-- `a ≤𝓙 x * a * y` implies `a 𝓙 x * a * y` -/
@[simp] lemma J_eqv_of_J_preorder_mul_sandwich (h : a ≤𝓙 x * a * y) : a 𝓙 x * a * y := by
  simpa [J_eqv_iff]

end Simp_Lemmas

/-! ### Lemmas for 𝓡 and 𝓛 equivalences (Prop 1.4.3)
This section establishes cancellation and extension properties for Green's 𝓡 and 𝓛 relations. -/

section RL_Lemmas

variable {S} [Semigroup S] {a x y : S}

/-! Lemmas assuming `a 𝓡 axy` -/

/-- If `a 𝓡 a * x * y`, then `a 𝓡 a * x`. -/
lemma R_eqv_right_cancel (h : a 𝓡 a * x * y) : a 𝓡 a * x := by
  simp_all [R_eqv_iff]
  obtain ⟨⟨u, hu⟩, _⟩ := h
  use y * u; simp_rw [WithOne.coe_mul, ← mul_assoc] at *
  exact hu

/-- If `a 𝓡 a * x * y`, then `a * x 𝓡 a * x * y`.-/
lemma R_eqv_right_extend (h : a 𝓡 a * x * y) : a * x 𝓡 a * x * y := by
  simp_all [R_eqv_iff]
  obtain ⟨⟨u, hu⟩, _⟩ := h
  use u * x; simp_rw [WithOne.coe_mul, ← mul_assoc] at *
  rw [← hu]

/-! Lemmas assuming `a 𝓛 yxa` -/

/-- If `a 𝓛 y * x * a`, then `a 𝓛 x * a`. -/
theorem L_eqv_left_cancel (h: a 𝓛 y * x * a ) : a 𝓛 x * a := by
  simp_all [L_eqv_iff]
  obtain ⟨u, hu⟩ := h
  use u * y; simp_rw [WithOne.coe_mul, ← mul_assoc] at *
  exact hu

/-- If `a 𝓛 y * x * a`, then `x * a 𝓛 y * x * a`. -/
theorem L_eqv_left_extend (h : a 𝓛 y * x * a) : x * a 𝓛 y * x * a := by
  simp_all [L_eqv_iff]
  constructor
  · obtain ⟨u, hu⟩ := h
    use x * u; simp_rw [WithOne.coe_mul, mul_assoc] at *
    rw [← hu]
  · simp [mul_assoc]

end RL_Lemmas

/-! ### Lemmas for Monoids -/

section Monoid_Lemmas

variable {M} [Monoid M] {a x y : M}

/-- In finite monoids, if `a = x * a * y`, then there exist positive integers `n₁` and `n₂`
such that `x ^ n₁ * a = a` and `a * y ^ n₂ = a`. -/
lemma exists_pow_sandwich_eq_self [Finite M] (h : a = x * a * y) :
    ∃ n₁ n₂ : ℕ, n₁ ≠ 0 ∧ n₂ ≠ 0 ∧ x ^ n₁ * a = a ∧ a * y ^ n₂ = a := by
  have loop : ∀ k : ℕ, x ^ k * a * y ^ k = a := by
    intro k; induction k with
    | zero => simp
    | succ n ih =>
      rw [pow_succ, pow_succ']
      rw [← mul_assoc, mul_assoc _ a, mul_assoc _ x, ← mul_assoc x a y, ← h, ih]
  have ⟨n₁, ⟨hn₁, hneq₁⟩⟩ := Monoid.exists_idempotent_pow x
  have ⟨n₂, ⟨hn₂, hneq₂⟩⟩ := Monoid.exists_idempotent_pow y
  use n₁, n₂
  constructor; exact hneq₁; constructor; exact hneq₂; constructor
  · rw [← (loop n₁), ← mul_assoc, ← mul_assoc, hn₁]
  · rw [← (loop n₂), mul_assoc, hn₂]

end Monoid_Lemmas

/-! ### The D-J Theorem for Finite Semigroups -/

section D_J

variable {S} [Semigroup S] {a b : S}

/-- Every 𝓓-related pair is 𝓙-related. -/
lemma D_eqv_if : a 𝓓 b → a 𝓙 b := by
  simp [D_eqv_iff, J_eqv_iff]
  rintro x ⟨⟨c, hc⟩, ⟨d, hd⟩⟩ ⟨⟨f, hf⟩, ⟨g, hg⟩⟩
  constructor
  · use f, c; rw [← hf, ← hc]
  · use g, d; rw [mul_assoc, ← hd, hg]

/-- In finite semigroups, Green's 𝓓-relation equals the 𝓙-relation. The forward direction
always holds, but finiteness is needed for the reverse implication. -/
theorem D_iff_J_finite [Finite S] : a 𝓓 b ↔ a 𝓙 b := by
  constructor
  · apply D_eqv_if
  · intro hJ
    have hJ_copy := hJ; obtain ⟨⟨x, y, ha⟩, ⟨u, v, hb⟩⟩ := hJ_copy
    have hab : ↑a = x * u * a * (v * y) := by
      rw [hb, ← mul_assoc, ← mul_assoc, mul_assoc _ v y] at ha
      exact ha
    obtain ⟨k, l, hene, hfne, heq1, heq2⟩ := exists_pow_sandwich_eq_self hab
    cases v with
    | one =>
      use a; rw [one_mul, mul_one] at *; simp [L_eqv_iff]
      constructor
      · use (x * u)^(k-1) * x
        have hk : k - 1 + 1 = k := by exact Nat.succ_pred_eq_of_ne_zero hene
        rw [hb, ← mul_assoc, mul_assoc _ x u, ← pow_succ, hk, heq1]
      · use u
    | coe v =>
      use a * v
      simp [R_eqv_iff, L_eqv_iff]
      constructor
      · use y * (v * y) ^ (l - 1)
        rw [WithOne.coe_mul, ← mul_assoc, mul_assoc ↑a ↑v y, mul_assoc,  ← pow_succ']
        have hl : l - 1 + 1 = l := by exact Nat.succ_pred_eq_of_ne_zero hfne
        rw [hl, heq2]
      · constructor
        · use (x * u)^(k-1) * x; rw [hb]
          conv => rhs; rw [← mul_assoc, ← mul_assoc, mul_assoc _ x u]
          have hk : k - 1 + 1 = k := by exact Nat.succ_pred_eq_of_ne_zero hene
          rw [WithOne.coe_mul, ← pow_succ, hk, heq1]
        · use u; simp [hb, mul_assoc]

end D_J

/-! ### Idempotent properties (Prop 1.4.1)
This section characterizes elements that are 𝓡- below or 𝓛- below an idempotent. -/

section Idempotent_Props

variable {S} [Semigroup S] (a e : S)

/-- An element `a` is 𝓡-below an idempotent `e` if and only if `a = e * a`. -/
theorem le_R_idempotent (h: IsIdempotentElem e) : (a ≤𝓡 e) ↔ (a = e * a) := by
  constructor
  · rintro ⟨u, hru⟩
    unfold IsIdempotentElem at h
    rw [← WithOne.coe_inj, WithOne.coe_mul] at h ⊢
    rw [hru, ← mul_assoc, h ]
  · intro hl; use a
    rw[<-WithOne.coe_inj] at hl; exact hl

/-- An element `a` is 𝓛-below an idempotent `e` if and only if `a = a * e`. -/
theorem le_L_idempotent (h: IsIdempotentElem e) : (a ≤𝓛 e) ↔ (a = a * e) := by
  constructor
  · rintro ⟨u, hru⟩
    unfold IsIdempotentElem at h
    rw [← WithOne.coe_inj, WithOne.coe_mul] at h ⊢
    rw [hru, mul_assoc, h ]
  · intro hl; use a
    rw[<-WithOne.coe_inj] at hl; exact hl

end Idempotent_Props

/-! ### Properties relating J, L, and R (Proposition 1.4.2 and 1.4.4)
This section shows how 𝓙-equivalence "strengthens"
𝓡 and 𝓛 preorders to equivalences in finite semigroups. -/

section J_R_L_Props

variable {S} [Semigroup S] [Finite S] {a b : S}

/-- In finite semigroups, if `a` is 𝓙-related to `a * b`, then `a` is 𝓡-related to `a * b`. -/
lemma R_eqv_of_J_mul_right (hj : a 𝓙 a * b) : a 𝓡 a * b := by
  obtain ⟨⟨x, y, hxy⟩, _⟩ := hj
  rw [WithOne.coe_mul, ← mul_assoc, mul_assoc] at hxy
  simp [R_eqv_iff]
  obtain ⟨_, n, _, hneq, _, ha ⟩ := exists_pow_sandwich_eq_self hxy
  use y * (↑b * y) ^ (n - 1)
  simp_rw [WithOne.coe_mul, ← mul_assoc, mul_assoc ↑a ↑b y]
  rw [mul_assoc ↑a (↑b * y), ← pow_succ']
  have hl : n - 1 + 1 = n := by exact Nat.succ_pred_eq_of_ne_zero hneq
  rw [hl, ha]

/-- In finite semigroups, if `a` is 𝓡-below `b` and `a 𝓙 b`, then `a 𝓡 b`. -/
theorem R_eqv_of_R_preorder_and_J (hr : a ≤𝓡 b) (hj: a 𝓙 b) : a 𝓡 b := by
  rw [R_preorder_iff_without_one] at hr
  cases hr with
  | inl heq => subst heq; simp
  | inr ha =>
    obtain ⟨u, hru⟩ := ha; subst hru;
    rw [J_eqv_symm, R_eqv_symm] at *
    apply R_eqv_of_J_mul_right; assumption

/-- In finite semigroups, if `a` is 𝓙-related to `b * a`, then `a` is 𝓛-related to `b * a`. -/
lemma L_eqv_of_J_mul_left (hj : a 𝓙 b * a) : a 𝓛 b * a := by
  obtain ⟨⟨x, y, hxy⟩, _⟩ := hj
  rw [WithOne.coe_mul, ← mul_assoc ] at hxy
  simp [L_eqv_iff]
  obtain ⟨ n, _, hneq, _, ha, _ ⟩ := exists_pow_sandwich_eq_self hxy
  use (x * ↑b) ^ (n - 1) * x
  simp_rw [WithOne.coe_mul, ← mul_assoc, mul_assoc _ x, ← pow_succ]
  have hl : n - 1 + 1 = n := by exact Nat.succ_pred_eq_of_ne_zero hneq
  rw [hl, ha]

/-- In finite semigroups, if `a` is 𝓛-below `b` and `a 𝓙 b`, then `a 𝓛 b`. -/
theorem L_eqv_of_L_preorder_and_J (hl : a ≤𝓛 b) (hj: a 𝓙 b) : a 𝓛 b := by
  rw [L_preorder_iff_without_one] at hl
  cases hl with
  | inl heq => subst heq; simp
  | inr ha =>
    obtain ⟨u, hru⟩ := ha; subst hru;
    rw [J_eqv_symm, L_eqv_symm] at *
    apply L_eqv_of_J_mul_left; assumption

end J_R_L_Props


/-!
# Green's Lemma (Prop 1.5)
Some notes about statement of parts of this lemma. Not sure if I've done so in
the best way.
1. (More of a quibble)
We have the hypotheses a𝓡b or a𝓛b, respectively, but we need to call upon
the actual witnesses of these relations in stating the conclusion of the lemma;
hence we need to incorporate hypotheses (h1: b = a * ↑u)(h2: a= b * ↑v). I'm not sure what
the most elegant way to state this is. Technically, we don't need to state the equivalence
relation directly, but omitting feels uncomfortable. Should we remove the
hypotheses h1/h2 and write these instead as implications?
2. We need to define right/left translation on semigroups and set instances of
R/L classes that are not necessarily finite. These should probably be incorporated
into Defs.
3. To what extent should these statements be presented as separate theorems/combined?
Right now it's broken down pretty significantly.
4. Looking at the proof, it does not seem to use any facts about idempotents and
consequently it's not clear to me that S must be finite for Green's Lemma to hold.
Is this true?
5. Would it be more lucid to characterize these theorems in terms of ideals?
-/

section Greens_Lemma

variable {S} [Semigroup S] {a b : S}

/-Necessary definitions-- to be moved-/
def R_translation (a : S) : S → S := (· * a)
notation:50 "ρᵣ" a => R_translation a
infixr:70 " ⋆ρᵣ " => R_translation

def L_translation (a : S) : S → S := (a * ·)
notation:50 "ρₗ" a => L_translation a
infixr:70 " ⋆ρₗ " => L_translation

def R_class_set (x : S) : Set S :=
  fun a => a 𝓡 x
def L_class_set (x : S) : Set S :=
  fun a => a 𝓛 x

/-For right translation:-/
theorem Greens_lemma_R_rel_ab {u v: S} {h: a 𝓡 b} (h1: b = a * ↑u) (h2: a= b * ↑v):
   Set.BijOn (ρᵣ ↑u) (L_class_set a) (L_class_set b) := by
   sorry

theorem Greens_lemma_R_rel_ba {u v : S} {h: a 𝓡 b} (h2: a= b * ↑v) :
   Set.BijOn (ρᵣ ↑v) (L_class_set b) (L_class_set a) := by
   sorry

theorem Greens_lemma_r_trans_preserves_H_ab {u v x y : S} {h: a 𝓡 b}
   (hx : x ∈ L_class_set a) (hy : y ∈ L_class_set a) (h1: b = a * ↑u) :
    (↑x 𝓗 ↑y) ↔ (x ⋆ρᵣ u) 𝓗 (y ⋆ρᵣ u) := by
  sorry

theorem Greens_lemma_r_trans_preserves_H_ba {u v x y : S} {h: a 𝓡 b}
   (hx : x ∈ L_class_set a) (hy : y ∈ L_class_set b) (h1: b = a * ↑u) :
    (↑x 𝓗 ↑y) ↔ (x ⋆ρᵣ v) 𝓗 (y ⋆ρᵣ v) := by
  sorry

theorem Greens_lemma_inverse_bijections_r_trans {u v : S}
    (h: a 𝓡 b) (h1 : a = b * v) (h2 : b = a * u) :
    Function.RightInverse (ρᵣ v) (ρᵣ u) ∧
    Function.LeftInverse (ρᵣ v) (ρᵣ u) :=
  sorry

/-For left translation:-/
theorem Greens_lemma_L_rel_ab {u v: S} {h: a 𝓛 b} (h1: b = ↑u * a) (h2: a= b * ↑v):
   Set.BijOn (ρᵣ ↑u) (R_class_set a) (R_class_set b) := by
   sorry

theorem Greens_lemma_L_rel_ba {u v : S} {h: a 𝓛  b} (h2: a= b * ↑v) :
   Set.BijOn (ρᵣ ↑v) (L_class_set b) (L_class_set a) := by
   sorry

theorem Greens_lemma_l_trans_preserves_H_ab {u v x y : S} {h: a 𝓛 b}
   (hx : x ∈ R_class_set a) (hy : y ∈ R_class_set a) (h1: b = ↑u * a) (h2: a= b * ↑v):
    (↑x 𝓗 ↑y) ↔ (u ⋆ρₗ x) 𝓗 (u ⋆ρₗ y) := by
  sorry

theorem Greens_lemma_l_trans_preserves_H_ba {u v x y : S} {h: a 𝓛 b}
   (hx : x ∈ R_class_set a) (hy : y ∈ R_class_set b) (h1: b = ↑u * a) (h2: a= b * ↑v):
    (↑x 𝓗 ↑y) ↔ (v ⋆ρₗ x) 𝓗 (v ⋆ρₗ y) := by
  sorry

theorem Greens_lemma_inverse_bijections_l_trans {u v : S}
    (h: a 𝓡 b) (h1: b = ↑u * a) (h2: a= b * ↑v) :
    Function.RightInverse (ρₗ v) (ρₗ u) ∧
    Function.LeftInverse (ρₗ v) (ρₗ u) := by
  sorry

end Greens_Lemma
