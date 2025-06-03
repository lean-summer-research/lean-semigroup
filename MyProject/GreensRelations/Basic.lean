import MyProject.GreensRelations.Decidable

/-!
# Basic Properties of Green's Relations

This file establishes basic properties of Green's relations.

## Main statements

* `D_iff_J_finite` - **D-J Theorem**: in finite semigroups, 𝓓 = 𝓙
Prop 1.4:
* `le_R_idempotent` : if e ∈ S idempotent, then e ≤𝓡 a iff a = ea for all a ∈ S
* `le_L_idempotent` : if e ∈ S idempotent, then e ≤𝓛 a iff a = ae for all a ∈ S
* `le_J_rmult_implies_J_R_rel` : if a ≤𝓙 ax then a 𝓙 ax and a 𝓡 ax
* `le_J_lmult_implies_J_L_rel` : if a ≤𝓙 xa then a 𝓙 xa and a 𝓛 xa
* `le_R_double_implies_R_rel` : if a ≤𝓡 axy then a 𝓡 ax 𝓡 axy
* `le_L_double_implies_L_rel` : if a ≤𝓛 yxa then a 𝓛 xa 𝓛 yxa
* `le_R_and_J_rel_implies_R_rel` : if a ≤𝓡 b and a 𝓙 b then a 𝓡 b
* `le_L_and_J_rel_implies_L_rel` : if a ≤𝓛 b and a 𝓙 b then a 𝓛 b

Green's Lemma (1.5):
[Includes some subsidiary definitions/notation at the beginning, should move to Defs]
* `Greens_lemma_R_rel_ab`
* `Greens_lemma_R_rel_ba`
* `Greens_lemma_r_trans_preserves_H_ab`
* `Greens_lemma_r_trans_preserves_H_ba`
* `Greens_lemma_inverse_bijections_r_trans`
* `Greens_lemma_L_rel_ab`
* `Greens_lemma_L_rel_ba`
* `Greens_lemma_l_trans_preserves_H_ab`
* `Greens_lemma_l_trans_preserves_H_ba`
* `Greens_lemma_inverse_bijections_l_trans`

## Implementation notes

-/

/-! ## The D-J Theorem for Finite Semigroups -/

variable {S} [Semigroup S] (a b : S)
/-- Every D-related pair is J-related -/
lemma D_eqv_if : a 𝓓 b → a 𝓙 b := by
  simp [D_eqv, rel_comp, J_eqv_iff]
  rintro x ⟨⟨c, hc⟩, ⟨d, hd⟩⟩ ⟨⟨f, hf⟩, ⟨g, hg⟩⟩
  constructor
  · use f, c; rw [← hf, ← hc]
  · use g, d; rw [mul_assoc, ← hd, hg]

/-- **D-J Theorem**: In finite semigroups, Green's D-relation equals the J-relation -/
theorem D_iff_J_finite [Finite S] : a 𝓓 b ↔ a 𝓙 b := by
  constructor
  · apply D_eqv_if
  · rintro ⟨⟨x, y, ha⟩, ⟨u, v, hb⟩⟩
    have loop : ∀ n : ℕ, (x * u)^n * ↑a * (v * y)^n = a := by
      intros n; induction n with
      | zero => simp
      | succ n ih =>
        conv => lhs; lhs; rw [pow_succ, mul_assoc]
        conv => lhs; rhs; rw [pow_succ']
        have rw_assoc : (x * u)^ n * (x * u * ↑a) * (v * y * (v * y)^ n) =
            (x*u)^ n * (x * (u * a * v) * y) * (v*y)^n := by simp [mul_assoc]
        rw [rw_assoc, ← hb, ← ha, ih]
    have ⟨k, ⟨he, hene⟩⟩ := Monoid.exists_idempotent_pow (x * u)
    have ⟨l, ⟨hf, hfne⟩⟩ := Monoid.exists_idempotent_pow (v * y : S¹)
    have heq1 : (x * u)^ k * a = a := by rw [← (loop k), ← mul_assoc, ← mul_assoc, he]
    have heq2 : a * (v * y)^ l = a := by rw [← (loop l), mul_assoc, hf]
    cases v with
    | one =>
      use a; constructor
      · apply eqv_of_preorder_refl
      · rw [L_eqv_iff]; constructor
        · rw [one_mul, mul_one] at *; use (x * u)^(k-1) * x
          have hk : k - 1 + 1 = k := by exact Nat.succ_pred_eq_of_ne_zero hene
          rw [hb, ← mul_assoc, mul_assoc _ x u, ← pow_succ, hk, heq1]
        · use u; rw [hb, mul_one]
    | coe v =>
      use a * v
      constructor
      · constructor
        · use y * (v * y)^ (l - 1)
          rw [WithOne.coe_mul, ← mul_assoc, mul_assoc ↑a ↑v y, mul_assoc,  ← pow_succ' ]
          have hl : l - 1 + 1 = l := by exact Nat.succ_pred_eq_of_ne_zero hfne
          rw [hl, heq2]
        · use v; simp
      · constructor
        · use (x * u)^(k-1) * x; rw [hb]
          conv => rhs; rw [← mul_assoc, ← mul_assoc, mul_assoc _ x u]
          have hk : k - 1 + 1 = k := by exact Nat.succ_pred_eq_of_ne_zero hene
          rw [WithOne.coe_mul, ← pow_succ, hk, heq1]
        · use u; simp [hb, mul_assoc]

theorem le_R_idempotent {e : S} (h: IsIdempotentElem e) : (a ≤𝓡 e) ↔ (a = e * a) := by
  constructor
  · intro hr
    have he : ↑e = ↑(e * e) := h.symm
    obtain ⟨u, hru⟩ := hr
    rw[<-WithOne.coe_inj]
    calc
      a = ↑e * u := hru
      _ = ↑(e * e) * u := by rw[<-he]
      _ = ↑e * (↑e * u) := by rw[WithOne.coe_mul, mul_assoc]
      _ = ↑e * a := by rw[<-hru]
  · intro hl
    rw[<-WithOne.coe_inj] at hl
    use (↑e * ↑a)
    nth_rw 1[<-mul_assoc, <-WithOne.coe_mul, h]
    exact hl

theorem le_L_idempotent {e : S} (h: IsIdempotentElem e) : (a ≤𝓛 e) ↔ (a = a * e) := by
  constructor
  · intro hr
    have he : ↑e = ↑(e * e) := h.symm
    obtain ⟨u, hru⟩ := hr
    rw[<-WithOne.coe_inj]
    calc
      ↑a = u * ↑e := hru
      _ = u * ↑(e * e) := by rw[<-he]
      _ = (u * ↑e) * ↑e := by rw[WithOne.coe_mul, mul_assoc]
      _ = a * ↑e := by rw[<-hru]
  · intro hl
    rw[<-WithOne.coe_inj] at hl
    use (↑a * ↑e)
    conv => lhs
    rw[mul_assoc, <-WithOne.coe_mul, h]
    exact hl

theorem le_J_rmult_implies_J_R_rel [Finite S] (h: a ≤𝓙 a * b) : (a 𝓙 a * b) ∧ (a 𝓡 a * b) := by
  constructor
  · have h1: a * b ≤𝓙 a := by use 1, b; simp
    exact ⟨h,h1⟩
  · constructor
    · obtain ⟨u, v, hr⟩ := h
      have loop : ∀ n : ℕ, (u)^n * ↑a * (b * v)^n = a := by
        intros n; induction n with
        | zero => simp
        | succ n ih =>
          conv => lhs; lhs; rw [pow_succ, mul_assoc]
          conv => lhs; rhs; rw [pow_succ']
          simp_rw[<-mul_assoc]
          rw[mul_assoc (u ^ n * u * ↑a)]
          nth_rw 2[<-pow_one u]; nth_rw 1[<-pow_one (↑b * v)]
          rw[pow_mul_comm u, mul_assoc, pow_mul_comm (↑b * v)]
          have rw_assoc : u ^ 1 * u ^ n * ↑a * ((↑b * v) ^ n * (↑b * v) ^ 1) =
            u^1 * (u ^ n * ↑a * (↑b * v) ^ n) * (↑b * v) ^ 1 := by simp[mul_assoc]
          simp_rw[rw_assoc, ih, pow_one]
          nth_rw 2[hr]; simp[mul_assoc]
      have ⟨l, hu⟩ := Monoid.exists_idempotent_pow u
      have hul : u^↑l * u^↑l = u^↑l := hu.left
      have hl : u^l * a = a := by
        calc
        u^↑l * a = u^↑l * (u^↑l * a * (b * v)^↑l) := by rw[loop l]
              _ = u^↑l * u^↑l * a * (b * v)^↑l :=by repeat rw[<-mul_assoc]
              _ = u^↑l * a * (b * v)^↑l := by simp_rw[hul]
              _ = a := by rw[loop l]
      have loopl := loop l
      use (v * (b * v)^(l-1))
      repeat rw[<-mul_assoc]
      rw[WithOne.coe_mul]; nth_rw 2[<-hl]
      rw[mul_assoc (u^l * a)]; nth_rw 1[<-pow_one (b * v)]
      have hsub : (↑b * v) ^ 1 * (↑b * v) ^ (↑l - 1) = (↑b * v) ^↑l := by
        rw[<-pow_add (b * v) 1 (↑(l-1))]
        have hpow: (1 + ↑(l - 1)) = l := by
          refine Nat.add_sub_of_le ?_
          exact (Nat.pos_of_ne_zero hu.right)
        have hl : (↑b * v) ^ (1 + ↑(l - 1)) = (↑b * v) ^ ↑l := by
          simp_rw[hpow]
        exact hl
      conv => lhs
      simp_rw[mul_assoc (u^l * ↑a), hsub]; exact loopl.symm
    · use b; rw[WithOne.coe_mul]

theorem le_J_lmult_implies_J_L_rel [Finite S] (h: a ≤𝓙 b * a) : (a 𝓙 b * a) ∧ (a 𝓛 b * a) := by
  constructor
  · have h1: b * a ≤𝓙 a := by use b, 1; simp
    exact ⟨h,h1⟩
  · constructor
    · obtain ⟨u, v, hr⟩ := h
      have loop : ∀ n : ℕ, (u * b)^n * ↑a * (v)^n = a := by
        intros n; induction n with
        | zero => simp
        | succ n ih =>
          conv => lhs; lhs; rw [pow_succ, mul_assoc]
          conv => lhs; rhs; rw [pow_succ']
          simp_rw[<-mul_assoc]
          have rw_assoc :  (u * ↑b) ^ n * u * ↑b * ↑a * v * v ^ n =
            (u * ↑b) ^ n * (u * ↑b)^1 * ↑a * v^1 * v ^ n := by
            rw[mul_assoc ((u * ↑b) ^ n)]
            nth_rw 2[<-pow_one (u * ↑b)]
            nth_rw 1[<-pow_one (v)]
          rw[rw_assoc, pow_mul_comm (u * ↑b), mul_assoc, pow_mul_comm (v)]
          have rw_assoc : (u * ↑b)^ 1 * (u*↑b) ^ n * ↑a * (v^ n * v^ 1) =
            (u * ↑b)^ 1 * ((u*↑b) ^ n * ↑a * v^ n) * v^ 1 := by simp[mul_assoc]
          simp_rw[rw_assoc, ih, pow_one]
          nth_rw 2[hr]; simp[mul_assoc]
      have ⟨l, hv⟩ := Monoid.exists_idempotent_pow v
      have hvl : v^l * v^l = v^l := hv.left
      have hl : a = a * v^l := by
        calc
        a = (u * b)^l * a * v^l := by rw[loop l]
        _ = (u * b)^l * a * (v^l * v^l) := by rw[hvl]
              _ = ((u * b)^l * a * v^l) * v^l := by simp_rw[mul_assoc]
              _ = a * v^l := by rw[loop l]
      have loopl := loop l
      use ((u * b)^(l-1) * u)
      rw[WithOne.coe_mul]; nth_rw 2[hl]; repeat rw[<-mul_assoc]
      have h_assoc : (u * ↑b) ^ (l - 1) * u * ↑b * ↑a * v^l =
        (u * ↑b) ^ (l - 1) * (u * ↑b)^ 1 * ↑a * v^l := by
        simp[mul_assoc]
      rw[h_assoc]
      have hsub : (u * b) ^ (l - 1) * (u * b) ^ 1 = (u * b) ^l := by
        refine pow_sub_mul_pow (u * ↑b) ?_
        exact (Nat.pos_of_ne_zero hv.right)
      rw[hsub]; exact loopl.symm
    · use b; rw[WithOne.coe_mul]

theorem le_R_double_implies_R_rel {x y : S} (h: a ≤𝓡 a * x * y) : (a 𝓡 a * x) ∧ (a * x 𝓡 a * x * y) ∧ (a 𝓡 a * x * y) := by
  have ⟨z, ha⟩:= h
  have haax : a ≤𝓡 a * x := by
    use ↑y * ↑z; simp_rw[WithOne.coe_mul] at ha
    simp_rw[<-mul_assoc, WithOne.coe_mul, <-ha]
  have hxxy : a * x ≤𝓡 a * x * y := by
    use ↑z * ↑x; rw[<-mul_assoc, <-ha, WithOne.coe_mul]
  have hxya : a * x * y ≤𝓡 a := by
    use ↑x * ↑y; simp_rw[<-mul_assoc, WithOne.coe_mul]
  exact ⟨⟨haax, (by use x; rw[WithOne.coe_mul])⟩,
    ⟨hxxy, (by use y; rw[WithOne.coe_mul])⟩, ⟨h, hxya⟩⟩

theorem le_L_double_implies_L_rel {x y : S} (h: a ≤𝓛 y * x * a) : (a 𝓛 x * a) ∧ (x * a 𝓛 y * x * a) ∧ (a 𝓛 y * x * a) := by
  have ⟨z, ha⟩:= h
  simp_rw[WithOne.coe_mul, <-mul_assoc] at ha
  have haxa : a ≤𝓛 x * a := by
    use ↑z * ↑y; rw[ha, WithOne.coe_mul, <-mul_assoc]
  have hxyx : x * a ≤𝓛 y * x * a:= by
    use ↑x * ↑z; simp_rw[WithOne.coe_mul, <-mul_assoc]; nth_rw 1[ha];
    simp_rw[<-mul_assoc]
  exact ⟨⟨haxa, (by use x; rw[WithOne.coe_mul])⟩,
    ⟨hxyx, by use y; simp_rw[WithOne.coe_mul, mul_assoc]⟩,
    ⟨h, (by use (y * x); simp_rw[WithOne.coe_mul])⟩⟩

theorem le_R_and_J_rel_implies_R_rel [Finite S] (h1 : a ≤𝓡 b) (h2: a 𝓙 b) : a 𝓡 b := by
  rw[R_preorder_iff_without_one] at h1
  cases h1 with
  | inl h1.left => rw[h1.left]; exact (R_eqv_iff_ideal b b).mpr rfl
  | inr h1.right =>
      obtain ⟨u, h1⟩ := h1.right
      obtain ⟨h2l, ⟨v, w, h2r⟩⟩ := h2
      have hub : b * u 𝓙 b := by
        constructor
        · use 1, u
          simp
        · use v, w; rw[<-h1, h2r]
      have h: b 𝓙 b * u ∧ b 𝓡 b * u := by
        refine le_J_rmult_implies_J_R_rel b u ?_
        refine (J_preorder_iff b (b * u)).mpr ?_
        exact hub.right
      have hr := h.right
      rw[h1]
      refine (R_eqv_iff (b * u) b).mpr ?_
      have : b * u ≤𝓡 b ∧ b ≤𝓡 b * u := by
        unfold R_eqv at hr
        simp_all
      exact this

theorem le_L_and_J_rel_implies_R_rel [Finite S] (h1 : a ≤𝓛 b) (h2: a 𝓙 b) : a 𝓛 b := by
  rw[L_preorder_iff_without_one] at h1
  cases h1 with
  | inl h1.left => rw[h1.left]; exact (L_eqv_iff_ideal b b).mpr rfl
  | inr h1.right =>
      obtain ⟨u, h1⟩ := h1.right
      obtain ⟨h2l, ⟨v, w, h2r⟩⟩ := h2
      have hub : u * b 𝓙 b := by
        constructor
        · use u, 1
          simp
        · use v, w; rw[<-h1, h2r]
      have h: b 𝓙 u * b ∧ b 𝓛 u * b := by
        refine le_J_lmult_implies_J_L_rel b u ?_
        refine (J_preorder_iff b (u * b)).mpr ?_
        exact hub.right
      have hr := h.right
      rw[h1]
      refine (L_eqv_iff (u * b) b).mpr ?_
      have : u * b ≤𝓛 b ∧ b ≤𝓛 u * b := by
        unfold L_eqv at hr
        simp_all
      exact this


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
