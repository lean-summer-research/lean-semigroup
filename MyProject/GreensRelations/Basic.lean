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

variable {S} [Semigroup S] {a b : S}

/-Necessary definitions-- to be moved-/
def R_translation (a : S¹) : S¹ → S¹ := (· * a)
notation:50 "ρᵣ" a => R_translation a
infixr:70 " ⋆ρᵣ " => R_translation

def L_translation (a : S¹) : S¹ → S¹ := (a * ·)
notation:50 "ρₗ" a => L_translation a
infixr:70 " ⋆ρₗ " => L_translation

def R_class_set (x : S¹) : Set (S¹) :=
  {a | a 𝓡 x}
def L_class_set (x : S¹) : Set (S¹) :=
  { a | a 𝓛 x}

/-Helper lemmas: -/

/-If a 𝓡 b such that b = a * u and a = b * v, then translation by (u * v) on
any x such that x𝓛a is the identity. -/
lemma right_translation_id_ab (u v : S¹) (h : a 𝓡 b) (hu : b = a * u) (hv : a = b * v) :
    ∀x ∈ (L_class_set ↑a), (v ⋆ρᵣ (u ⋆ρᵣ x)) = x := by
    intros c hc
    have hac : ↑a 𝓛 c := by exact L_eqv_symm.mp hc
    have ht : ∃ x, c = x * a := by
      refine (L_preorder_iff_monoid c ↑a).mp ?_; exact hac.right
    obtain ⟨t, ht'⟩ := ht
    have : (v ⋆ρᵣ ( u ⋆ρᵣ c)) = c := by
      calc
      (v ⋆ρᵣ ( u⋆ρᵣ c)) = (v ⋆ρᵣ ( u ⋆ρᵣ c)) := by rfl
      _ = c * u * v := by unfold R_translation; rfl
      _ = t * b * v := by simp_rw[ht', hu, mul_assoc]
      _ = t * a := by rw[hv, mul_assoc]
      _ = c := by rw[ht']
    exact this


/-If a 𝓡 b such that b = a * u and a = b * v, then translation by (v * u) on
any x such that x𝓛b is the identity. -/
lemma right_translation_id_ba (u v : S¹) (h : a 𝓡 b) (hu : b = a * u) (hv : a = b * v) :
    ∀x ∈ (L_class_set ↑b), (u ⋆ρᵣ (v ⋆ρᵣ x)) = x := by
    intros c hc
    have hac : ↑b 𝓛 c := by exact L_eqv_symm.mp hc
    have ht : ∃ x, c = x * b := by
      refine (L_preorder_iff_monoid c ↑b).mp ?_; exact hac.right
    obtain ⟨t, ht'⟩ := ht
    have : (u ⋆ρᵣ (v ⋆ρᵣ c)) = c := by
      calc
      (u ⋆ρᵣ (v ⋆ρᵣ c)) = (u ⋆ρᵣ (v ⋆ρᵣ c)) := by rfl
      _ = c * v * u := by unfold R_translation; rfl
      _ = t * a * u := by simp_rw[ht', hv, mul_assoc]
      _ = t * b := by rw[hu, mul_assoc]
      _ = c := by rw[ht']
    exact this

lemma left_translation_id_ab (u v : S¹) (h : a 𝓛 b) (hu : b = u * a) (hv : a = v * b) :
    ∀x ∈ (R_class_set ↑a), (v ⋆ρₗ (u ⋆ρₗ x)) = x := by
    intros c hc
    have hac : ↑a 𝓡 c := by exact R_eqv_symm.mp hc
    have ht : ∃ x, c = a * x := by
      refine (R_preorder_iff_monoid c ↑a).mp ?_; exact hac.right
    obtain ⟨t, ht'⟩ := ht
    have : (v ⋆ρₗ ( u ⋆ρₗ c)) = c := by
      calc
      (v ⋆ρₗ ( u⋆ρₗ c)) = (v ⋆ρₗ ( u ⋆ρₗ c)) := by rfl
      _ = v * u * c := by unfold L_translation; simp[mul_assoc]
      _ = v * b * t := by simp_rw[ht', mul_assoc, hu, <-mul_assoc]
      _ = a * t := by rw[hv, mul_assoc]
      _ = c := by rw[ht']
    exact this

  lemma left_translation_id_ba (u v : S¹) (h : a 𝓛 b) (hu : b = u * a) (hv : a = v * b) :
    ∀x ∈ (R_class_set ↑b), (u ⋆ρₗ (v ⋆ρₗ x)) = x := by
    intros c hc
    have hac : ↑b 𝓡 c := by exact R_eqv_symm.mp hc
    have ht : ∃ x, c = b * x := by
      refine (R_preorder_iff_monoid c ↑b).mp ?_; exact hac.right
    obtain ⟨t, ht'⟩ := ht
    have : (u ⋆ρₗ (v ⋆ρₗ c)) = c := by
      calc
      (u ⋆ρₗ (v ⋆ρₗ c)) = (u ⋆ρₗ (v ⋆ρₗ c)) := by rfl
      _ = u * v * c := by unfold L_translation; simp[mul_assoc]
      _ = u * a * t := by simp_rw[ht', hv, mul_assoc]
      _ = b * t := by rw[hu, mul_assoc]
      _ = c := by rw[ht']
    exact this

/-end of helper lemmas.-/

/--If a 𝓡 b such that b = a * u and a = b * v, then right translation by
(v * u) from the 𝓛-class of a to the 𝓛-class of b
and by (u * v) from the 𝓛-class of b to the 𝓛-class of a are inverses.-/
theorem Greens_lemma_inverse_r_trans {u v : S¹}
    (h: a 𝓡 b) (hv : a = b * v) (hu : b = a * u) :
    Set.InvOn (ρᵣ v) (ρᵣ u) (L_class_set a) (L_class_set b) := by
    unfold Set.InvOn
    exact ⟨right_translation_id_ab u v h hu hv, right_translation_id_ba u v h hu hv⟩

/--If a 𝓛 b such that b = u * a and a = v * b, then left translation by
(v * u) from the 𝓡-class of a to the 𝓡-class of b
and by (u * v) from the 𝓡-class of b to the 𝓡-class of a are inverses.-/
theorem Greens_lemma_inverse_l_trans {u v : S¹}
    (h: a 𝓛 b) (hv : a = v * b) (hu : b = u * a) :
    Set.InvOn (ρₗ v) (ρₗ u) (R_class_set a) (R_class_set b) := by
    unfold Set.InvOn
    exact ⟨left_translation_id_ab u v h hu hv, left_translation_id_ba u v h hu hv⟩

/--If a 𝓡 b such that b = a * u, right translation by u from the 𝓛-class of a is a
bijection on the 𝓛-class of b.-/
theorem Greens_lemma_R_rel_bij {u : S¹} (h: a 𝓡 b) (hu: b = a * u):
    (Set.BijOn (ρᵣ u) (L_class_set a) (L_class_set b)) := by
  have h' := h
  unfold R_eqv at h; unfold eqv_of_preorder at h
  obtain ⟨⟨v, hv⟩, _⟩ := h
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
    have hx : x ∈ L_class_set a := by
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

/--If a 𝓛 b such that b = u * a, left translation by u from the 𝓡-class of a is a
bijection on the 𝓡-class of b.-/
theorem Greens_lemma_L_rel_bij {u : S¹} (h: a 𝓛 b) (hu: b = u * a):
    (Set.BijOn (ρₗ u) (R_class_set a) (R_class_set b)) := by
  have h' := h
  unfold L_eqv at h; unfold eqv_of_preorder at h
  obtain ⟨⟨v, hv⟩, _⟩ := h
  refine Set.BijOn.mk ?_ ?_ ?_
  · intros x hx
    have hxa : x 𝓡 a := hx
    have : u * x 𝓡 u * a := ⟨R_preorder_lmult_compat hxa.left u,
      R_preorder_lmult_compat hxa.right u⟩
    rw [←hu] at this
    exact this
  · intro x hx y hy hxy
    have hinv := by exact fun x a_1 ↦ left_translation_id_ab u v h' hu hv x a_1
    have hinvx := hinv x hx; have hinvy := hinv y hy
    rw[<-hinvx, <-hinvy, hxy]
  · intros y hy
    refine (Set.mem_image (ρₗ u) (R_class_set ↑a) y).mpr ?_
    let x := v * y
    have hx : x ∈ R_class_set a := by
      have hyb : y 𝓡 b := hy
      have h1 : x 𝓡 v * b := ⟨R_preorder_lmult_compat hyb.left v,
                                R_preorder_lmult_compat hyb.right v⟩
      rw [←hv] at h1; exact h1
    use x, hx
    have hinv : ∀y ∈ (R_class_set ↑b), (u ⋆ρₗ (v ⋆ρₗ y)) = y
     := by exact fun y a_1 ↦ left_translation_id_ba u v h' hu hv y a_1
    have hinvx := hinv y hy; unfold L_translation at hinvx
    calc
       u * x = u * (v * y) := by simp[x]
       _ = y := by rw[hinvx]

/- If a 𝓡 b such that b = a * u, right translation by u preserves 𝓗-classes.-/
theorem Greens_lemma_r_trans_preserves_H {x y u v: S¹} (h: a 𝓡 b) (h1: b = a * u)
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
theorem Greens_lemma_l_trans_preserves_H {x y u v: S¹} (h: a 𝓛 b) (h1: b = u * a)
    (h2: a = v * b)
    (hx : x ∈ R_class_set ↑a) (hy : y ∈ R_class_set ↑a):
    (x 𝓗 y) ↔ (u ⋆ρₗ x) 𝓗 (u ⋆ρₗ y) := by
  constructor
  · intro hxy
    refine (H_eqv_iff_L_and_R (u * x) (u * y)).mpr ?_
    have := by simp[H_eqv_iff_L_and_R x y] at hxy; exact hxy
    obtain ⟨hxyr, hxyl⟩ := this
    constructor
    · exact R_eqv_lmult_compat hxyr u
    · let ⟨⟨r1, hr1⟩, ⟨r2, hr2⟩⟩ := hxyr
      have hu : ∀ x ∈ R_class_set ↑a, x 𝓛 u * x := by
        intro x hx
        have := left_translation_id_ab u v h h1 h2 x hx
        simp_rw[L_eqv, eqv_of_preorder, L_preorder_iff_without_one, L_translation] at *
        constructor
        · right; use v; exact this.symm
        · right; use u
      have hxu := hu x hx; have hyu := hu y hy
      constructor
      · exact L_preorder_trans _ _ _ (L_preorder_trans _ _ _ hxu.right hxyl.left) hyu.left
      · exact L_preorder_trans _ _ _ (L_preorder_trans _ _ _ hyu.right hxyl.right) hxu.left
  · intro hxyu; unfold L_translation at hxyu
    have hv : ∀ x ∈ R_class_set ↑b, x 𝓛 v * x := by
      simp_rw [L_eqv, eqv_of_preorder, L_preorder_iff_without_one]
      intro x hx
      have := left_translation_id_ba u v h h1 h2 x hx
      constructor
      · right; use u; exact this.symm
      · right; use v
    have hxu :(u * x) ∈ R_class_set ↑b := by
      have : x 𝓡 a := hx; have := R_eqv_lmult_compat this u
      rw[<-h1] at this; exact this
    have hyu :(u * y) ∈ R_class_set ↑b := by
      have : y 𝓡 a := hy; have := R_eqv_lmult_compat this u
      rw[<-h1] at this; exact this
    have hxv := hv (u * x) (hxu : (u * x) ∈ R_class_set ↑b)
    have hxy := hv (u * y) (hyu : (u * y) ∈ R_class_set ↑b)
    have x_eq : v * (u * x) = x := left_translation_id_ab u v h h1 h2 x hx
    have y_eq : v * (u * y) = y := left_translation_id_ab u v h h1 h2 y hy
    have hloopr : v * (u * x) 𝓛 v * (u * y) := by
      constructor
      · calc  v * (u * x) ≤𝓛 (u * x)     := by simp [mul_left_L_preorder_self]
                   _      ≤𝓛 u * y       := hxyu.left.right
                   _      ≤𝓛 v * (u * y) := by rw [y_eq]; simp [mul_left_L_preorder_self]
      · calc  v * (u * y) ≤𝓛 (u * y)     := by simp [mul_left_L_preorder_self]
                   _      ≤𝓛 u * x       := hxyu.right.right
                   _      ≤𝓛 v * (u * x) := by rw [x_eq]; simp [mul_right_R_preorder_self]
    rw[x_eq, y_eq] at hloopr
    have hloopl : v * (u * x) 𝓡 v * (u * y) := ⟨R_preorder_lmult_compat hxyu.left.left v,
      R_preorder_lmult_compat hxyu.right.left v⟩
    rw[x_eq, y_eq] at hloopl
    have:= H_eqv_iff_L_and_R x y
    exact (H_eqv_iff_L_and_R x y).mpr ⟨hloopl, hloopr⟩
