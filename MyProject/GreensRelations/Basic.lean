import MyProject.GreensRelations.Decidable
import MyProject.Opposite

/-!
# Basic Properties of Green's Relations

This file establishes fundamental properties of Green's relations in semigroups, particularly
in finite semigroups.

## Main statements

* `R_eqv_right_cancel`, `L_eqv_left_cancel`: Cancellation properties of 𝓡 and 𝓛 relations
* `exists_pow_sandwich_eq_self`: A key lemma in proofs on Finite Semigroups.
* `D_iff_J_finite`: The D-J theorem for finite semigroups
* `le_R_idempotent`, `le_L_idempotent`: Characterization of elements below idempotents
* `R_eqv_of_J_mul_right`, `L_eqv_of_J_mul_left`: Shows how 𝓙 equivalence "strengthens"
  𝓡 and 𝓛 preorders to equivalences in finite semigroups.
* `Greens_lemma_inverse_r_trans`, `Greens_lemma_inverse_l_trans`:
  If two elements a and b are 𝓡/𝓛 related, then right/left translation between 𝓛-classes/𝓡-classes
  of a and b by certain elements are inverses
* `Greens_lemma_R_rel_bij`, `Greens_lemma_L_rel_bij` : If two elements a and b are 𝓡/𝓛 related,
  right/left translation by specific elements induces a bijection between 𝓛-classes/ 𝓡-classes
  of a and b.
* `Greens_lemma_r_trans_preserves_H`, `Greens_lemma_l_trans_preserves_H`: shows preservation
  of 𝓗-classes for elements in certain 𝓛/𝓡 classes under specific left/right translations


## TODO

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

/-! ### Green's Lemma (Proposition 1.5)
This section demonstrates various results related to Green's theorem. We prove that
that left/right translations induced by witnesses to two 𝓡/𝓛 related elements are
bijections between their L/R classes, respectively, that preserve H classes. -/

section Greens_Lemma
set_option linter.unusedVariables false

variable {S} [Semigroup S] {a b : S}

open MulOpposite

/-Helper lemmas: -/

/-If a 𝓡 b such that b = a * u and a = b * v, then translation by (u * v) on
any x such that x𝓛a is the identity. -/
lemma right_translation_id_ab (u v : S) (h : a 𝓡 b) (hu : b = a * u) (hv : a = b * v) :
    ∀x ∈ (L_class_set a), (v ⋆ρᵣ (u ⋆ρᵣ x)) = x := by
    intros c hc
    have hac : ↑a 𝓛 c := by exact L_eqv_symm.mp hc
    have ht : c = a ∨ ∃ x, c = x * a := by
      refine (L_preorder_iff_without_one c ↑a).mp ?_; exact hac.right
    cases' ht with hl hr
    · rw[hl]
      calc
      (v ⋆ρᵣ ( u⋆ρᵣ a)) = (v ⋆ρᵣ ( u ⋆ρᵣ a)) := by rfl
      _ = a * u * v := by unfold R_translation; rfl
      _ = b * v := by simp_rw[hu]
      _ = a := by simp_rw[hv]
    · obtain ⟨t, ht'⟩ := hr
      calc
      (v ⋆ρᵣ ( u⋆ρᵣ c)) = (v ⋆ρᵣ ( u ⋆ρᵣ c)) := by rfl
      _ = c * u * v := by unfold R_translation; rfl
      _ = t * b * v := by simp_rw[ht', hu, mul_assoc]
      _ = t * a := by rw[hv, mul_assoc]
      _ = c := by rw[ht']

/-If a 𝓡 b such that b = a * u and a = b * v, then translation by (v * u) on
any x such that x𝓛b is the identity. -/
lemma right_translation_id_ba (u v : S) (h : a 𝓡 b) (hu : b = a * u) (hv : a = b * v) :
    ∀x ∈ (L_class_set ↑b), (u ⋆ρᵣ (v ⋆ρᵣ x)) = x := by
    intros c hc
    have hac : ↑b 𝓛 c := by exact L_eqv_symm.mp hc
    have ht : c = b ∨ ∃ x, c = x * b := by
      refine (L_preorder_iff_without_one c b).mp ?_; exact hac.right
    cases' ht with hl hr
    · rw[hl]
      calc
      (u ⋆ρᵣ (v ⋆ρᵣ b)) = (u ⋆ρᵣ (v ⋆ρᵣ b)) := by rfl
      _ = b * v * u := by unfold R_translation; rfl
      _ = a * u := by simp_rw[hv]
      _ = b := by rw[hu]
    · obtain ⟨t, ht'⟩ := hr
      calc
      (u ⋆ρᵣ (v ⋆ρᵣ c)) = (u ⋆ρᵣ (v ⋆ρᵣ c)) := by rfl
      _ = c * v * u := by unfold R_translation; rfl
      _ = t * a * u := by simp_rw[ht', hv, mul_assoc]
      _ = t * b := by rw[hu, mul_assoc]
      _ = c := by rw[ht']

/-If a 𝓛 b such that b = u * a and a = v * b, then translation by (v * u) on
any x such that x 𝓡 a is the identity. -/
lemma left_translation_id_ab (u v : S) (h : a 𝓛 b)
    (hu : b = u * a) (hv : a = v * b) :
    ∀ x ∈ R_class_set a, (v ⋆ρₗ (u ⋆ρₗ x)) = x := by
  have hR : (op a) 𝓡 (op b) := by
    rw [←L_eqv_iff_R_eqv_op]; exact h
  have hu_op : op b = op a * op u := by simp[hu]
  have hv_op : op a = op b * op v := by simp[hv]
  intro x hx
  have hx_op : op x ∈ L_class_set (op a) := by
    unfold L_class_set; simp[L_eqv_op_iff_R_eqv]
    unfold R_class_set at hx; simp at hx; exact hx
  exact congr_arg unop (right_translation_id_ab (op u) (op v) hR hu_op hv_op (op x) hx_op)

/-If a 𝓛 b such that b = u * a and a = v * b, then translation by (u * v) on
any x such that x 𝓡 a is the identity. -/
lemma left_translation_id_ba (u v : S) (h : a 𝓛 b) (hu : b = u * a) (hv : a = v * b) :
    ∀x ∈ (R_class_set b), (u ⋆ρₗ (v ⋆ρₗ x)) = x := by
  have hR : (op a) 𝓡 (op b) := by
    rw [←L_eqv_iff_R_eqv_op]; exact h
  have hu_op : op b = op a * op u := by simp[hu]
  have hv_op : op a = op b * op v := by simp[hv]
  intro x hx
  have hx_op : op x ∈ L_class_set (op b) := by
    unfold L_class_set; simp[L_eqv_op_iff_R_eqv]
    unfold R_class_set at hx; simp at hx; exact hx
  exact congr_arg unop (right_translation_id_ba (op u) (op v) hR hu_op hv_op (op x) hx_op)

/-end of helper lemmas.-/

/--If a 𝓡 b such that b = a * u and a = b * v, then right translation by
(v * u) from the 𝓛-class of a to the 𝓛-class of b
and by (u * v) from the 𝓛-class of b to the 𝓛-class of a are inverses.-/
theorem Greens_lemma_inverse_r_trans {u v : S}
    (h: a 𝓡 b) (hv : a = b * v) (hu : b = a * u) :
    Set.InvOn (ρᵣ v) (ρᵣ u) (L_class_set a) (L_class_set b) := by
    unfold Set.InvOn
    exact ⟨right_translation_id_ab u v h hu hv, right_translation_id_ba u v h hu hv⟩

/--If a 𝓛 b such that b = u * a and a = v * b, then left translation by
(v * u) from the 𝓡-class of a to the 𝓡-class of b
and by (u * v) from the 𝓡-class of b to the 𝓡-class of a are inverses.-/
theorem Greens_lemma_inverse_l_trans {u v : S}
    (h: a 𝓛 b) (hv : a = v * b) (hu : b = u * a) :
    Set.InvOn (ρₗ v) (ρₗ u) (R_class_set a) (R_class_set b) := by
    unfold Set.InvOn
    exact ⟨left_translation_id_ab u v h hu hv, left_translation_id_ba u v h hu hv⟩

/--If a 𝓡 b such that b = a * u, right translation by u from the 𝓛-class of a is a
bijection on the 𝓛-class of b.-/
theorem Greens_lemma_R_rel_bij {u v : S} (h: a 𝓡 b) (hu: b = a * u) (hv : a = b * v):
    (Set.BijOn (ρᵣ u) (L_class_set a) (L_class_set b)) := by
  have h' := h
  unfold R_eqv at h; simp[R_preorder_iff_without_one] at h
  refine Set.BijOn.mk ?_ ?_ ?_
  · intros x hx
    have hxa : x 𝓛 a := hx
    have : x * u 𝓛 a * u := ⟨L_preorder_rmult_compat hxa.left u,
      L_preorder_rmult_compat hxa.right u⟩
    rw [←hu] at this
    exact this
  · intro x hx y hy hxy
    have hinv := by exact fun x a_1 ↦ right_translation_id_ab u v h' hu hv x a_1
    have hinvx := hinv x hx; have hinvy := hinv y hy
    rw[<-hinvx, <-hinvy, hxy]
  · intros y hy
    refine (Set.mem_image (ρᵣ u) (L_class_set ↑a) y).mpr ?_
    let x := y * v
    have hx : x ∈ L_class_set ↑a := by
      have hyb : y 𝓛 b := hy
      have h1 : x 𝓛 b * v := ⟨L_preorder_rmult_compat hyb.left v,
                              L_preorder_rmult_compat hyb.right v⟩
      rw [←hv] at h1; exact h1
    use x, hx
    have hinv : ∀y ∈ (L_class_set ↑b), (u ⋆ρᵣ (v ⋆ρᵣ y)) = y
      := by exact fun y a_1 ↦ right_translation_id_ba u v h' hu hv y a_1
    have hinvx := hinv y hy; unfold R_translation at hinvx
    calc
      x * u = y * v * u := rfl
      _ = y := by rw[hinvx]

theorem Greens_lemma_L_rel_bij {u v : S} (h: a 𝓛 b) (hu: b = u * a) (hv : a = v * b):
    (Set.BijOn (ρₗ u) (R_class_set a) (R_class_set b)) := by
  have hR : (op a) 𝓡 (op b) := by
    rw [←L_eqv_iff_R_eqv_op]; exact h
  have hu_op : op b = op a * op u := by simp[hu]
  have hv_op : op a = op b * op v := by simp[hv]
  have hop := Greens_lemma_R_rel_bij hR hu_op hv_op
  refine Set.BijOn.mk ?_ ?_ ?_
  · intro x hx
    rw [Class_op_RL] at hx
    have h := hop.mapsTo hx
    simp_rw[R_translation, <-op_mul, <-Class_op_RL] at h; exact h
  · intro x hx y hy hxy
    rw [Class_op_RL] at hx hy
    have h := hop.injOn hx hy; specialize h (congrArg op hxy)
    exact op_inj.mp h
  · intro y hy
    rw [Class_op_RL] at hy
    obtain ⟨x', hx', hxy⟩ := hop.surjOn hy; let x := unop x'
    have hx : x ∈ R_class_set a := by
      rw [Class_op_RL]; exact hx'
    have hxyunop : u ⋆ρₗ unop x' = y := by
      have:= congr_arg unop hxy
      simp[R_translation, unop_op] at this; exact this
    have:= Set.mem_image_of_mem (ρₗ u) hx
    simp[x, hxyunop] at *; exact this

/- If a 𝓡 b such that b = a * u, right translation by u preserves 𝓗-classes.-/
theorem Greens_lemma_r_trans_preserves_H {x y u v: S} (h: a 𝓡 b) (h1: b = a * u)
    (h2: a = b * v)
    (hx : x ∈ L_class_set ↑a) (hy : y ∈ L_class_set ↑a):
    (x 𝓗 y) ↔ (u ⋆ρᵣ x) 𝓗 (u ⋆ρᵣ y) := by
  constructor
  · intro hxy
    refine (H_eqv_iff_L_and_R (x * u) (y * u)).mpr ?_
    have := by simp[H_eqv_iff_L_and_R x y] at hxy; exact hxy
    obtain ⟨hxyr, hxyl⟩ := this
    constructor
    · let ⟨⟨r1, hr1⟩, ⟨r2, hr2⟩⟩ := hxyr
      have hu : ∀ x ∈ L_class_set ↑a, x 𝓡 x * u := by
        intro x hx
        have := right_translation_id_ab u v h h1 h2 x hx
        simp_rw[R_eqv, eqv_of_preorder, R_preorder_iff_without_one, R_translation] at *
        constructor
        · right; use v; exact this.symm
        · right; use u
      have hxu := hu x hx; have hyu := hu y hy
      constructor
      · exact R_preorder_trans _ _ _ (R_preorder_trans _ _ _ hxu.right hxyr.left) hyu.left
      · exact R_preorder_trans _ _ _ (R_preorder_trans _ _ _ hyu.right hxyr.right) hxu.left
    · exact L_eqv_rmult_compat hxyl u
  · intro hxyu; unfold R_translation at hxyu
    have hv : ∀ x ∈ L_class_set ↑b, x 𝓡 x * v := by
      simp_rw [R_eqv, eqv_of_preorder, R_preorder_iff_without_one]
      intro x hx
      have := right_translation_id_ba u v h h1 h2 x hx
      constructor
      · right; use u; exact this.symm
      · right; use v
    have hxu :(x * u) ∈ L_class_set ↑b := by
      have : x 𝓛 a := hx; have := L_eqv_rmult_compat this u
      rw[<-h1] at this; exact this
    have hyu :(y * u) ∈ L_class_set ↑b := by
      have : y 𝓛 a := hy; have := L_eqv_rmult_compat this u
      rw[<-h1] at this; exact this
    have hxv := hv (x * u) (hxu : (x * u) ∈ L_class_set ↑b)
    have hxy := hv (y * u) (hyu : (y * u) ∈ L_class_set ↑b)
    have x_eq : (x * u) * v = x := right_translation_id_ab u v h h1 h2 x hx
    have y_eq : (y * u) * v = y := right_translation_id_ab u v h h1 h2 y hy
    have hloopr : x * u * v 𝓡 y * u * v := by
      constructor
      · calc x * u * v ≤𝓡 x * u     := by simp [mul_right_R_preorder_self]
                   _         ≤𝓡 y * u     := hxyu.left.left
                   _         ≤𝓡 y * u * v := by rw [y_eq]; simp [mul_right_R_preorder_self]
      · calc y * u * v ≤𝓡 y * u     := by simp [mul_right_R_preorder_self]
                   _         ≤𝓡 x * u     := hxyu.right.left
                   _         ≤𝓡 x * u * v := by rw [x_eq]; simp [mul_right_R_preorder_self]
    rw[x_eq, y_eq] at hloopr
    have hloopl : x * u * v 𝓛 y * u * v := ⟨L_preorder_rmult_compat hxyu.left.right v,
      L_preorder_rmult_compat hxyu.right.right v⟩
    rw[x_eq, y_eq] at hloopl
    have:= H_eqv_iff_L_and_R x y
    exact (H_eqv_iff_L_and_R x y).mpr ⟨hloopr, hloopl⟩


/- If a 𝓡 b such that b = a * u, right translation by u preserves 𝓗-classes.-/
theorem Greens_lemma_l_trans_preserves_H_alt {x y u v: S} (h: a 𝓛 b) (h1: b = u * a)
    (h2: a = v * b)
    (hx : x ∈ R_class_set ↑a) (hy : y ∈ R_class_set ↑a):
    (x 𝓗 y) ↔ (u ⋆ρₗ x) 𝓗 (u ⋆ρₗ y) := by
  -- Pass to the opposite semigroup
  have hR_op : op a 𝓡 op b := by rw [← L_eqv_iff_R_eqv_op]; exact h
  have h1_op : op b = op a * op u := by simp [h1]
  have h2_op : op a = op b * op v := by simp [h2]
  have hx_op : op x ∈ L_class_set (op a) := by rw [← Class_op_RL]; exact hx
  have hy_op : op y ∈ L_class_set (op a) := by rw [← Class_op_RL]; exact hy
  have := Greens_lemma_r_trans_preserves_H hR_op h1_op h2_op hx_op hy_op
  simp[R_translation] at this
  simp[H_eqv_op_iff x y, L_translation, H_eqv_op_iff (u * x) (u * y)]
  exact this


theorem RL_intersection_contains_ab :
  a * b ∈ (R_class_set a) ∩ (L_class_set b) ↔
    ∃ e : S, e ∈ (R_class_set b) ∩ (L_class_set a) ∧ IsIdempotentElem e := by
  constructor
  · intro hab
    simp only [Set.mem_inter_iff, R_class_set, L_class_set] at hab
    obtain ⟨hR, hL⟩ := hab
    have hRaab : a 𝓡 a * b := by
      simp[R_eqv] at hR
      exact ⟨hR, by unfold R_preorder; use b; simp⟩
    simp[R_eqv, R_preorder_iff_without_one] at hR
    cases' hR with heq hneq
    · have L_eq' : L_class_set a = L_class_set b := by
        apply Set.ext
        intro x; apply Iff.intro
        · intro hxa
          obtain ⟨⟨u, hu⟩, ⟨v, hv⟩⟩ := hxa
          have haLb : a 𝓛 b := by rw [←heq] at hL; exact hL
          obtain ⟨⟨s, hs⟩, ⟨t, ht⟩⟩ := haLb
          have h₁ : ∃ m, (↑x : S¹) = ↑m * ↑b := ⟨u * s, by rw [hu, mul_assoc, <-hs]⟩
          have h₂ : ∃ n, (↑b : S¹) = n * x := ⟨t * v, by rw [ht, mul_assoc, <-hv]⟩
          exact ⟨h₁, h₂⟩
        · intro hxb
          obtain ⟨⟨u, hu⟩, ⟨v, hv⟩⟩ := hxb
          have haLb : a 𝓛 b := by rw [←heq] at hL; exact hL
          obtain ⟨⟨s, hs⟩, ⟨t, ht⟩⟩ := haLb
          have h1 : ∃ m, (↑x : S¹) = m * a := ⟨u * t, by rw [hu, ht, ←Semigroup.mul_assoc]⟩
          have h2 : ∃ n, (↑a : S¹) = n * x := ⟨s * v, by rw [hs, hv, ←Semigroup.mul_assoc]⟩
          exact ⟨h1, h2⟩
      have hbLa : b ∈ L_class_set a := by
        rw [L_eq']; simp [L_class_set]
      cases' hbLa with hu hv
      rw[L_preorder_iff_without_one] at hu hv
      cases' hu with hequ hnequ
      · cases' hv with heqv hneqv
        · rw[heqv] at heq
          have heR : b ∈ R_class_set b := by
            simp [R_class_set, R_preorder_iff_without_one]
          have heL' : b ∈ L_class_set a := by
            simp[L_class_set, L_preorder_iff_without_one]; simp[heqv]
          exact ⟨b, ⟨heR, heL'⟩, heq.symm⟩
        · rw[<-hequ] at heq
          have heR : b ∈ R_class_set b := by
            simp [R_class_set, R_preorder_iff_without_one]
          have heL' : b ∈ L_class_set a := by
            simp[L_class_set, L_preorder_iff_without_one]; simp[hequ]
          exact ⟨b, ⟨heR, heL'⟩, heq.symm⟩
      · cases' hv with heqv hneqv
        · rw[heqv] at heq
          have heR : b ∈ R_class_set b := by
            simp [R_class_set, R_preorder_iff_without_one]
          have heL' : b ∈ L_class_set a := by
            simp[L_class_set, L_preorder_iff_without_one]; simp[heqv]
          exact ⟨b, ⟨heR, heL'⟩, heq.symm⟩
        · rcases hnequ with ⟨s, hs⟩
          have heL : b ∈ L_class_set a := by
            simp [L_class_set]; constructor;
            · simp[hs]
            · unfold L_preorder; use a; exact congr_arg WithOne.coe heq
          have heR : b ∈ R_class_set b := by
            simp [R_class_set, R_preorder_iff_without_one] -- b = t * a
          have bb_eq : b * b = b := by
            calc
            b * b = (s * a) * b := by rw [hs]
            _     = s * (a * b) := by rw[mul_assoc]
            _    = s * a        := by rw [<-heq]
            _     = b           := by rw [hs]
          exact ⟨b, ⟨heR, heL⟩, bb_eq⟩
    · rcases hneq with ⟨v, hv⟩
      have bij := Greens_lemma_R_rel_bij hRaab rfl hv
      simp[L_class_set, L_preorder_iff_without_one] at hL
      rcases hL with ⟨⟨u1, hu1⟩, ⟨v1, hv1⟩⟩
      have hb_in_Lab : b ∈ L_class_set (a * b) := by
        simp [L_class_set, L_preorder_iff_without_one]
        constructor; use v1; use a; simp[WithOne.coe_mul]
      rcases Set.BijOn.surjOn bij hb_in_Lab with ⟨e, heL, he_mul⟩
      unfold R_translation at he_mul
      have heb : e 𝓡 b := by sorry
      have heR : e ∈ R_class_set b := by
        simp [R_class_set, R_preorder_iff_without_one]; constructor;
        · exact heb.left
        · use b; exact congr_arg WithOne.coe he_mul.symm
      have hidem : IsIdempotentElem e := by
        unfold IsIdempotentElem;
        have := heb.left; simp[R_preorder_iff_without_one] at this;
        cases' this with heqs hneqs
        · rw[<-heqs] at he_mul; exact he_mul
        · obtain ⟨s, hs⟩ := hneqs
          calc
            e * e = e * (b * s) := by rw[hs]
            _     = (e * b) * s := by rw[mul_assoc]
            _     = b * s       := by simp[he_mul]
            _     = e         := by rw[hs]
      exact ⟨e, ⟨heR, heL⟩, hidem⟩
  · intro ⟨e, he, heq⟩
    simp only [Set.mem_inter_iff, R_class_set, L_class_set] at he
    have : e 𝓛 a := he.right
    have haleq : a ≤𝓛 e := by simp[this.symm]
    have : e 𝓡 b := he.left
    have hbleq : b ≤𝓡 e := by simp[this.symm]
    have hea : a * e = a := ((le_L_idempotent a e heq).mp haleq).symm
    have heb : e * b = b := ((le_R_idempotent b e heq).mp hbleq).symm
    have hR : a 𝓡 (a * b) := by
      have : (a * e) 𝓡 (a * b) := by exact R_eqv_lmult_compat this a
      rw [hea] at this; exact this
    have hL : b 𝓛 (a * b) := by
      have : (e * b) 𝓛 (a * b) := by (expose_names; exact L_eqv_rmult_compat this_1 b)
      rw [heb] at this; exact this
    have hR' : a * b ∈ R_class_set a := by unfold R_class_set; exact hR.symm
    have hL' : a * b ∈ L_class_set b := by unfold L_class_set; exact hL.symm
    exact ⟨hR', hL'⟩
