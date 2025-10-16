import MyProject.Main_Results.Greens_lemma
/-!
## Location Theorem

This file proves the Location Theorem, which states the following:
If `a 𝓓 b`, then the following conditions are equivalent
  1. `a * b ∈ R_class_set a ∩ L_class_set b`
  2. `R_class_set b ∩ L_class_set a` contains an idempotent element.
  3. (TODO) `a⁻¹ * a * b = b` and `a * b * b⁻¹ = a` for some inverses `a⁻¹` of `a` and `b⁻¹` of `b`
If `S` is finite, then these conditions are equivalent to
  4. `a * b 𝓓 a` (Alternativly, `a * b 𝓓 b`)

We also prove the dual version of these statments

This file also contains corrolaries about idempotent-containing H-classes

TODO: have a Group Instance for H-classes containing idempotents
-/

section Equivalence_Basics
/- The first few results are just a general property of equivalence relations: a ~ b if and only if the equivalence class of a is equal to the equivalence class of b. We should be able to invoke a general theorem, but here we will just prove each version piecemeal.-/

variable {S} [Semigroup S] {a b : S}
lemma H_equiv_iff_classes_equal : a 𝓗 b ↔ H_class_set a = H_class_set b := by
  constructor
  · intro ahb
    unfold H_class_set
    apply Set.Subset.antisymm
    · intro a1 a1ha
      exact  H_eqv_trans a1ha  ahb
    · intro a2 a2hb
      exact  H_eqv_trans a2hb  (H_eqv_symm.mpr ahb)

  · intro setsequal
    have ainclass  : a ∈ H_class_set a := H_eqv_refl
    rw [setsequal] at ainclass
    exact ainclass

lemma R_equiv_iff_classes_equal : a 𝓡 b ↔ R_class_set a = R_class_set b := by
  constructor
  · intro ahb
    unfold R_class_set
    apply Set.Subset.antisymm
    · intro a1 a1ha
      exact  R_eqv_trans a1ha  ahb
    · intro a2 a2hb
      exact  R_eqv_trans a2hb  (R_eqv_symm.mpr ahb)
  · intro setsequal
    have ainclass  : a ∈ R_class_set a := R_eqv_refl
    rw [setsequal] at ainclass
    exact ainclass

lemma L_equiv_iff_classes_equal : a 𝓛 b ↔ L_class_set a = L_class_set b := by
  constructor
  · intro ahb
    unfold L_class_set
    apply Set.Subset.antisymm
    · intro a1 a1ha
      exact  L_eqv_trans a1ha  ahb
    · intro a2 a2hb
      exact  L_eqv_trans a2hb  (L_eqv_symm.mpr ahb)
  · intro setsequal
    have ainclass  : a ∈ L_class_set a := L_eqv_refl
    rw [setsequal] at ainclass
    exact ainclass

/- H-equivalence implies both L and R - equivalence; these are just special cases of a basic result proved earlier.-/

lemma H_implies_R : a 𝓗 b → a 𝓡 b := by
  intro hahb
  exact ((H_eqv_iff_L_and_R a b).mp hahb).left

lemma H_implies_L : a 𝓗 b → a 𝓛 b := by
  intro hahb
  exact ((H_eqv_iff_L_and_R a b).mp hahb).right


end Equivalence_Basics

section Location_Theorem

variable {S} [Semigroup S] {a b : S}

theorem finite_location_theorem [Finite S]:
    a * b ∈ (R_class_set a) ∩ (L_class_set b) ↔
    a 𝓓 b ∧ a 𝓓 a * b := by
  simp [R_class_set, L_class_set]
  constructor
  · rintro ⟨hR, hL⟩
    simp [D_eqv_iff_J_finite]
    rw [R_eqv_symm] at hR; apply R_eqv_implies_J at hR
    apply L_eqv_implies_J at hL
    constructor
    · apply J_eqv_trans hR hL
    · assumption
  · rintro ⟨hD₁, hD₂⟩
    have hJ : a 𝓙 b := by rwa [D_eqv_iff_J_finite] at hD₁
    constructor
    · apply R_eqv_of_R_preorder_and_J; simp_all -- goal: `a * b 𝓡 a`
      rw [D_eqv_iff_J_finite] at hD₂; exact hD₂.symm
    · apply L_eqv_of_L_preorder_and_J; simp_all -- goal: `a * b 𝓛 b
      rw [D_eqv_iff_J_finite] at hD₂
      rw [J_eqv_symm] at hD₂
      apply J_eqv_trans hD₂; exact hJ

/-- For a, b in S, (a * b) ∈ R_class_set a ∩ L_class_set b if and only if there is an idempotent
element in R_class_set b ∩ L_class_set a. -/
theorem RL_intersection_contains_mul_iff_contains_idempotent :
    a * b ∈ (R_class_set a) ∩ (L_class_set b) ↔
    ∃ e : S, e ∈ (R_class_set b) ∩ (L_class_set a) ∧ IsIdempotentElem e := by
  simp [R_class_set, L_class_set]
  constructor
  · rintro ⟨hR, hL⟩ -- Forward implication
    have split : a * b = a ∨ a * b ≠ a := by exact eq_or_ne (a * b) a
    -- Case split on if `a = a * b`
    rcases split with (heq | hneq)
    · use b; simp -- Assuming `a = a * b`, `b` is the idempotent
      constructor
      · rwa [heq, L_eqv_symm] at hL
      · have hL₂ := hL.right; rw [L_preorder_iff_without_one] at hL₂
        simp [IsIdempotentElem]
        rcases hL₂ with (heq₂ | ⟨v, hv⟩)
        · nth_rw 1 [heq₂, heq, ← heq₂]
        · nth_rw 1 [hv, ← mul_assoc, mul_assoc v, heq ]
          nth_rw 2 [hv]; rw [mul_assoc]
    · rw [R_eqv_symm] at hR -- Case: a ≠ a * b
      have heq_ab : a * b = a * b := by rfl
      -- Use a `right_translation_bijection` (greens lemma) to prove `ρᵣ b` is a bijection
      have hR₁ := hR --make a copy of hR
      rw [R_eqv_iff_without_one] at hR₁
      rcases hR₁ with (contra | ⟨u, _, hu, _⟩)
      have contra := contra.symm; contradiction
      have hBij := right_translation_bijection hu heq_ab
      have hSurj := hBij.surjOn; clear hBij hu u heq_ab
      simp [L_class_set, R_translation, Set.SurjOn, Set.subset_def] at *
      -- our idempotent will be the preimage of `b` under `ρᵣ b`
      specialize hSurj b
      have hL₂ := hL; rw [L_eqv_symm] at hL₂
      apply hSurj at hL₂
      obtain ⟨x, ⟨hLx, heqx⟩⟩ := hL₂
      use x; clear hSurj -- We need to establish `x ≤𝓡 b`,
      have hR₂ := by rw [R_eqv_iff_without_one] at hR; exact hR
      rcases hR₂ with (contra | ⟨u, _, hu, _⟩); have contra := contra.symm; contradiction
      -- Critical lemma `right_translation_id_ab`
      have heq_ab : a * b = a * b := by rfl
      have hid : x * b * u = x := right_translation_id hu heq_ab hLx
      constructor; constructor
      · simp [R_eqv, R_preorder_iff_without_one] -- Goal: `x 𝓡 b`
        constructor
        · right; use u; rw [← heqx, hid]
        · right; use b; exact heqx.symm
      · exact hLx -- Goal: `x 𝓛 b`
      · simp [IsIdempotentElem] -- Goal: `x` is idempotent
        nth_rw 2 [← hid]; rw [heqx, ← mul_assoc, hid]
  · rintro ⟨e, ⟨hR, hL⟩, hidem⟩ -- Backward implication
    have hb : b = e * b := by
      have hR_below : b ≤𝓡 e := by simp_all [R_eqv_iff]
      rwa [le_R_idempotent b hidem] at hR_below -- crucial lemma. (todo, make vars implicit)
    have ha : a = a * e := by
      have hL_below : a ≤𝓛 e := by simp [L_eqv_iff] at hL; exact hL.right
      rwa [le_L_idempotent a hidem] at hL_below
    constructor
    · nth_rw 2 [ha]
      apply R_eqv_lmult_compat
      exact hR.symm
    · nth_rw 2 [hb]
      apply L_eqv_rmult_compat
      exact hL.symm

/- the Jean-Eric Pin textbook lists this equivalence too -/

def is_weak_inverse (a a': S) : Prop := a' * a * a' = a'

def is_strong_inverse (a a': S) : Prop := is_weak_inverse a a' ∧ a * a' * a = a

lemma idempotent_stong_inverse {e : S} (he : IsIdempotentElem e) : is_strong_inverse e e := by
  simp_all [is_strong_inverse, is_weak_inverse, IsIdempotentElem]

-- todo, this is the wrong requirement of inverse, see textbook
theorem contains_idempotent_implies_exists_inverses :
    (∃ e : S, e ∈ (R_class_set b) ∩ (L_class_set a) ∧ IsIdempotentElem e)
    → ∃ a' b', is_strong_inverse a a' ∧ is_strong_inverse b b' := by
  simp [R_class_set, L_class_set]
  rintro e ⟨hR₁, hR₂⟩ ⟨hL₁, hL₂⟩ hidem
  have heq₁ : b = e * b := by rwa [le_R_idempotent b hidem] at hR₂
  have heq₂ : a = a * e := by rwa [le_L_idempotent a hidem] at hL₂
  have a_inv : ∃ a', is_strong_inverse a a' := by
    rw [L_preorder_iff_without_one] at hL₁
    rcases hL₁ with (triv | ⟨u, hu⟩)
    · subst a; use e; apply idempotent_stong_inverse hidem -- trivial case where a = e
    · use e * u; simp [is_strong_inverse, is_weak_inverse] -- case where a ≠ e
      constructor -- prove `e * u` inverts `a`
      · rw [mul_assoc e, ← hu, ← mul_assoc, hidem, hidem]
      · rw [← mul_assoc, mul_assoc (a * e), ← hu, mul_assoc, hidem, ← heq₂]
  have b_inv : ∃ b', is_strong_inverse b b' := by
    rw [R_preorder_iff_without_one] at hR₁
    rcases hR₁ with (triv | ⟨v, hv⟩)
    · subst b; use e; apply idempotent_stong_inverse hidem -- trivial case where b = e
    · use v * e; simp [is_strong_inverse, is_weak_inverse] -- case where b ≠ e
      constructor -- prove `v * e` inverts `b`
      · simp [IsIdempotentElem] at hidem
        simp_rw [← mul_assoc, mul_assoc (v * e), ← hv, mul_assoc, hidem ]
      · rw [← mul_assoc, ← hv, hidem, ← heq₁]
  exact ⟨a_inv, b_inv⟩

end Location_Theorem

section GroupsInSemigroups

variable {S} [Semigroup S][Finite S] {e x a b : S}
set_option linter.unusedSectionVars false

/-helper lemmas-/
lemma H_equiv_iff_exists (idem: IsIdempotentElem (e)) (h : x 𝓗 e) :
  ∃ u v : S, x = e * u ∧ x = v * e := by
  have h: x 𝓡 e ∧ x 𝓛 e := (H_eqv_iff_L_and_R x e).mp h
  simp only [Set.mem_inter_iff] at h
  obtain ⟨hR, hL⟩ := h
  unfold L_eqv eqv_of_preorder at hL
  unfold R_eqv eqv_of_preorder at hR
  simp[R_preorder_iff_without_one] at hR
  simp[L_preorder_iff_without_one] at hL
  cases' hR.left with heq hneq
  · cases' hL.left with heq' hneq'
    · use e, e; simp [heq];
      have : e * e = e := idem; exact this.symm
    · use e, e; simp [heq];
      have : e * e = e := idem; exact this.symm
  · cases' hL.left with heq' hneq'
    · use e, e; simp [heq'];
      have : e * e = e := idem; exact this.symm
    · obtain ⟨u, hu⟩ := hneq
      obtain ⟨v, hv⟩ := hneq'
      use u, v

lemma idempotent_left_identity (he : IsIdempotentElem e) (ha : a 𝓗 e) :
  e * a = a := by
    rcases H_equiv_iff_exists he ha with ⟨u, v, rfl, he'⟩
    simp [← mul_assoc]
    have : e * e = e := he
    simp_rw[this]

lemma idempotent_right_identity (he : IsIdempotentElem e) (ha : a 𝓗 e) :
  a * e = a := by
    rcases H_equiv_iff_exists he ha with ⟨u, v, he', rfl⟩
    simp [mul_assoc]
    have : e * e = e := he
    simp_rw[this]

/-- The idempotent e in an 𝓗 class functions as an identity for elements in said class.-/
lemma idempotent_identity_H_eqv (he : IsIdempotentElem e) (ha : a 𝓗 e) :
    e * a = a ∧ a * e = a :=
  ⟨idempotent_left_identity he ha, idempotent_right_identity he ha⟩

/-- An 𝓗 class containing an idempotent is closed under multiplication-/
lemma H_mul_closed (he : IsIdempotentElem e)
    (ha : a 𝓗 e) (hb : b 𝓗 e) :
    a * b 𝓗 e := by
  have halr := (H_eqv_iff_L_and_R a e).mp ha
  have hblr := (H_eqv_iff_L_and_R b e).mp hb
  simp only [Set.mem_inter_iff] at *
  obtain ⟨hal, har⟩ := halr
  obtain ⟨hbl, hbr⟩ := hblr
  unfold R_eqv eqv_of_preorder at hal hbl
  unfold L_eqv eqv_of_preorder at har hbr
  simp[R_preorder_iff_without_one] at hal hbl
  simp[L_preorder_iff_without_one] at har hbr
  cases' hal.left with heq halneq
  · cases' hbl.left with heq' hblneq
    · rw [heq, heq'] at *
      have : e * e = e := he
      simp_rw[this]; apply H_eqv_refl
    · rw[heq]; obtain ⟨x, rfl⟩ := hblneq
      rw[<-mul_assoc, he]; exact hb
  · cases' hbl.left with heq' hblneq
    · rw[heq']; obtain ⟨x, rfl⟩ := halneq
      have : (e * x) * e = (e * x) := idempotent_right_identity he ha
      rw[this]; exact ha
    · apply (H_eqv_iff_L_and_R (a * b) e).mpr
      have hee: e ∈ R_class_set b ∩ L_class_set a := by
        rw [R_class_set, L_class_set]
        constructor
        · exact (((H_eqv_iff_L_and_R b e).mp (hb)).left).symm
        · exact (((H_eqv_iff_L_and_R a e).mp (ha)).right).symm
      constructor
      · have hae := ((H_eqv_iff_L_and_R a e).mp ha).left
        have habl : a * b 𝓡 a * e := by
          refine R_eqv_lmult_compat ?_ a
          exact ((H_eqv_iff_L_and_R b e).mp hb).left
        have : a * e = a := by exact idempotent_right_identity he ha
        rw[this] at habl
        unfold R_eqv eqv_of_preorder
        exact ⟨R_preorder_trans (a * b) a e (habl.left) (hae.left),
            R_preorder_trans (e) a (a * b) (hae.right) (habl.right)⟩
      · have hbe := ((H_eqv_iff_L_and_R b e).mp hb).right
        have habl : a * b 𝓛 e * b := by
          refine L_eqv_rmult_compat ?_ b
          exact ((H_eqv_iff_L_and_R a e).mp ha).right
        have : e * b = b := by exact idempotent_left_identity he hb
        rw[this] at habl
        unfold L_eqv eqv_of_preorder
        exact ⟨L_preorder_trans (a * b) b e (habl.left) (hbe.left),
            L_preorder_trans (e) b (a * b) (hbe.right) (habl.right)⟩

/-- An 𝓗 class containing an idempotent is closed under multiplication; a different proof that uses the theorems in the file DJ_Theorem.  Do these actually require finiteness?-/
lemma H_mul_closed' (he : IsIdempotentElem e)
    (ha : a 𝓗 e) (hb : b 𝓗 e) :
    a * b 𝓗 e := by
  obtain ⟨ua,va,hua,hva⟩ := H_equiv_iff_exists he ha
  obtain ⟨ub,vb,hub,hvb⟩ := H_equiv_iff_exists he hb
  have habvavbe : a * b = va * vb * e := by
    calc
      a * b = va * (e * e * ub) := by rw [hva, hub, mul_assoc,mul_assoc]
      _     = va * (e * ub) := by rw [he ]
      _     = va * vb * e := by rw [<-hub, hvb, mul_assoc ]
  have hablle : a * b ≤𝓛 e := by
    simp [L_preorder_iff_without_one]
    have hexleftmul : ∃ x, a * b = x * e := by
      use va * vb
    exact Or.intro_right _ hexleftmul
  have habeuaub : a * b = e * (ua * ub) := by
    calc
      a * b = va * (e * e * ub) := by rw [hva, hub, mul_assoc,mul_assoc]
      _     = va * (e * ub) := by rw [he ]
      _     = e * (ua * ub) := by rw [<-mul_assoc,<-hva,hua,mul_assoc]
  have hablre : a * b ≤𝓡 e := by
    simp [R_preorder_iff_without_one]
    have hexrightmul : ∃ x, a * b = e * x := by
      use ua * ub
    exact Or.intro_right _ hexrightmul
  unfold H_eqv at ha
  simp at ha
  unfold H_preorder R_preorder L_preorder at ha
  unfold H_eqv at hb
  simp at hb
  unfold H_preorder R_preorder L_preorder at hb
  obtain ⟨x,hx⟩ := ha.2.2
  obtain ⟨y,hy⟩ := hb.2.1
  have hexaby : e = x * (a * b) * y :=
    calc
      ↑e = ↑(e * e) := by rw [he]
      _ =  ↑e * ↑e := rfl
      _ =  (x * ↑a) * ↑e := by rw [hx ]
      _ =  (x * ↑a) * (↑b * y) := by rw [hy]
      _ = x * (↑a * ↑b) * y := by rw [mul_assoc,mul_assoc, mul_assoc]
  have heljab : e ≤𝓙 a * b := by
    unfold J_preorder
    use x, y
    exact hexaby
  have helrab : e ≤𝓡 a * b := sorry /-R_preorder_of_R_preorder_and_J_preorder hablre heljab-/
  have hellab : e ≤𝓛 a * b := sorry /-L_preorder_of_L_preorder_and_J_preorder hablle heljab-/
  unfold H_eqv
  simp
  constructor
  · unfold H_preorder
    exact And.intro hablre hablle
  · unfold H_preorder
    exact And.intro helrab hellab




lemma R_eqv_without_one_decomp (h : a 𝓡 b) :
  (a = b) ∨ (∃ c, a = b * c ∧ ∃ d, b = a * d) := by
  simp [R_eqv, R_preorder_iff_without_one] at h
  have ⟨hr, hl⟩ := h
  cases' hr with hxe hex
  constructor
  · exact hxe
  · cases' hl with hex exx
    constructor
    · exact hex.symm
    · obtain ⟨c, hc⟩ := hex
      obtain ⟨d, hd⟩ := exx
      right
      use c; use hc; use d

lemma L_eqv_without_one_decomp (h : a 𝓛 b) :
    (a = b) ∨ (∃ c, a = c * b ∧ ∃ d, b = d * a) := by
  simp [L_eqv, L_preorder_iff_without_one] at h
  have ⟨hr, hl⟩ := h
  cases' hr with hxe hex
  constructor
  · exact hxe
  · cases' hl with hex exx
    constructor
    · exact hex.symm
    · obtain ⟨c, hc⟩ := hex
      obtain ⟨d, hd⟩ := exx
      right
      use c; use hc; use d

lemma rightMul_H_bij_on
    {e x : S} (he : IsIdempotentElem e) (hx : x 𝓗 e) :
    Set.BijOn (ρᵣ x) (H_class_set e) (H_class_set e) := by
  have hX := hx
  rw [H_eqv_iff_L_and_R] at hx
  rcases hx with ⟨hL, hR⟩
  have hr := R_eqv_without_one_decomp hL
  have hl := L_eqv_without_one_decomp hR
  cases' hr with heq hr
  · unfold R_translation H_class_set
    rw[heq]
    refine Set.BijOn.mk ?_ ?_ ?_
    · intro x hx; simp
      refine H_mul_closed he hx ?_
      exact H_eqv_refl
    · intro x hx y hy hxy
      simp at hxy
      simp at hx hy
      rw[idempotent_right_identity he hx, idempotent_right_identity he hy] at hxy
      exact hxy
    · intro y hy
      simp; use y
      constructor
      · simp at hy; exact hy
      · simp [idempotent_right_identity he hy]
  · cases' hl with heq' hl
    · unfold R_translation H_class_set
      rw[heq']
      refine Set.BijOn.mk ?_ ?_ ?_
      · intro x hx; simp
        refine H_mul_closed he hx ?_
        exact H_eqv_refl
      · intro x hx y hy hxy
        simp at hxy
        simp at hx hy
        rw[idempotent_right_identity he hx, idempotent_right_identity he hy] at hxy
        exact hxy
      · intro y hy
        simp; use y
        constructor
        · simp at hy; exact hy
        · simp [idempotent_right_identity he hy]
    · unfold R_translation H_class_set Set.BijOn
      obtain ⟨c, hc, d, hd⟩ := hr
      obtain ⟨c', hc', d', hd'⟩ := hl
      refine Set.BijOn.mk ?_ ?_ ?_
      · intro y hy; simp
        simp at hy
        exact H_mul_closed he hy hX
      · intro a ha b hb hab
        simp at hab
        simp at ha hb
        have hax : a * (x * d) = a := by
          have := idempotent_right_identity he ha
          rw[hd] at this; exact this
        calc
        a = a * (x * d) := hax.symm
        _ = b * (x * d) := by simp[<-mul_assoc, hab]
        _ = b * e := by rw[hd]
        _ = b := idempotent_right_identity he hb
      · intro y hy
        simp at *
        have hY := hy
        rw [H_eqv_iff_L_and_R] at hy
        obtain ⟨hyL, hyR⟩ := hy
        have hyxR : y 𝓡 x := R_eqv_trans hyL hL.symm
        have hyxL : y 𝓛 x := L_eqv_trans hyR hR.symm
        have hxyR := R_eqv_without_one_decomp hyxR
        have hxyL := L_eqv_without_one_decomp hyxL
        cases' hxyR with heq hxyR
        · cases' hxyL with heq' hxyL
          · use e; simp [heq]
            exact (idempotent_identity_H_eqv he hX).left
          · use e; simp [heq]
            exact (idempotent_identity_H_eqv he hX).left
        · cases' hxyL with heq' hxyL
          · use e; simp [heq']
            exact (idempotent_identity_H_eqv he hX).left
          · obtain ⟨f, hf, g, hg⟩ := hxyR
            obtain ⟨f', hf', g', hg'⟩ := hxyL
            use e * f' * e
            constructor
            · have : (e * f' * e) 𝓗 x := by
                rw [H_eqv_iff_L_and_R]
                constructor
                · constructor
                  · use d * f' * e
                    simp[<-mul_assoc, <-WithOne.coe_mul]
                    rw[<-hd]
                  · use x * g
                    have := idempotent_left_identity he hX
                    nth_rw 1[<-this]
                    simp[<-mul_assoc, <-WithOne.coe_mul]
                    have := idempotent_left_identity he hX
                    nth_rw 2[mul_assoc, this]
                    nth_rw 1[hg, hf']
                    simp[<-mul_assoc]
                · constructor
                  · use e * f' * d'
                    simp[mul_assoc, <-WithOne.coe_mul, <-hd']
                  · use g' * y * g'
                    nth_rw 2[hd]; simp[ <-WithOne.coe_mul, <-mul_assoc]; simp[mul_assoc, <-hf']
                    have := idempotent_left_identity he hY
                    simp[<-mul_assoc, this, <-hg', <-hd]
                    exact (idempotent_right_identity he hX).symm
              exact H_eqv_trans this hX
            · have := idempotent_left_identity he hX
              simp[mul_assoc, this, <-hf']
              exact idempotent_left_identity he hY

lemma idempotent_eq_of_H_rel
    {a b : S} (ha : IsIdempotentElem a) (hb : IsIdempotentElem b) (hab : a 𝓗 b) : a = b := by
  have hab' := hab
  rw[H_eqv_iff_L_and_R] at hab
  obtain ⟨hR, hL⟩ := hab
  have := R_eqv_without_one_decomp hR
  cases' this with heq hneq
  · exact heq
  · have := L_eqv_without_one_decomp hL
    cases' this with heq' hneq'
    · exact heq'
    · have h1 := idempotent_left_identity ha (hab').symm
      have h4 := idempotent_right_identity hb hab'
      rw[h1.symm]; nth_rw 1[h4.symm]

lemma H_class_has_inverse {S : Type*} [Finite S][Semigroup S]
    {e x : S} (he : IsIdempotentElem e) (hx : x 𝓗 e) :
    ∃ y : S, x * y = e ∧ y * x = e ∧ y 𝓗 e := by
  rcases H_equiv_iff_exists he hx with ⟨u, v, hu, hv⟩
  have hR := ((H_eqv_iff_L_and_R x e).mp hx).left
  have hL := ((H_eqv_iff_L_and_R e x).mp hx.symm).right
  have hRR := R_eqv_without_one_decomp hR
  have hLL := L_eqv_without_one_decomp hL
  cases' hRR with heq hneqr
  · cases' hLL with heql hneql
    · use e; rw[heq]; simp; exact he
    · use e; rw[heq]; simp; exact he
  · cases' hLL with heql hneql
    · use e; rw[<-heql]; simp; exact he
    · obtain ⟨c, hc, d, hd⟩ := hneqr
      obtain ⟨c', hc', d', hd'⟩ := hneql
      have bijR := right_translation_bijection hc hd
      have bijL := left_translation_bijection hd' hc'
      have hle : (L_class_set x) = (L_class_set e) := by
        refine Eq.symm (Set.ext ?_)
        intro y
        unfold L_class_set; simp
        exact ⟨by intro hye; exact L_eqv_trans hye hL,
          by intro hye; exact L_eqv_trans hye hL.symm⟩
      have hre : (R_class_set x) = (R_class_set e) := by
        refine Eq.symm (Set.ext ?_)
        intro y
        unfold R_class_set; simp
        exact ⟨by intro hye; exact R_eqv_trans hye hR.symm,
          by intro hye; exact R_eqv_trans hye hR⟩
      rw[hle] at bijR; rw[hre] at bijL
      have := rightMul_H_bij_on he hx
      have heH : e ∈ H_class_set e := by
        unfold H_class_set; simp [Set.mem_setOf_eq]
      obtain ⟨y, hyH, hyx⟩ := this.surjOn heH
      unfold R_translation at hyx
      have hy1 : y = e * y := (idempotent_identity_H_eqv he hyH).left.symm
      have hy2 : y = y * e := (idempotent_identity_H_eqv he hyH).right.symm
      use y; constructor
      · have : x * y = (x * y) * (x * y) := by
          calc
          x * y = x * y := by rfl
          _ = x * (e * y) := by rw[hy1.symm]
          _ = x * ((y * x) * y) := by rw[hyx]
          _ = (x * y) * (x * y) := by simp[mul_assoc]
        have hxy_idem : IsIdempotentElem (x * y) := by
          unfold IsIdempotentElem; exact this.symm
        have hxyH : x * y 𝓗 e := H_mul_closed he hx hyH
        have hxy_eq_e : x * y = e := by
          apply (idempotent_eq_of_H_rel he hxy_idem hxyH.symm).symm
        exact hxy_eq_e
      · exact ⟨hyx, hyH⟩

/- If an 𝓗-class contains two elements (which could be identical whose product is in the class, then it contains an idempotent.-/


lemma H_class_product_idempotent (a b : S)(ha : a 𝓗 b)(haab: a 𝓗 a * b) : ∃ e :S , IsIdempotentElem e ∧ (a 𝓗 e) := by
  unfold H_eqv eqv_of_preorder H_preorder at haab

  have harab: a 𝓡 a*b := ((H_eqv_iff_L_and_R a (a*b)).mp haab).left

  have halab: a 𝓛 a * b := ((H_eqv_iff_L_and_R a (a*b)).mp haab).right

  have hbab : b 𝓗 a * b := H_eqv_trans (H_eqv_symm.mp ha) haab

  have hbrab: b 𝓡 a*b := ((H_eqv_iff_L_and_R b (a*b)).mp hbab).left

  have hblab: b 𝓛 a*b := ((H_eqv_iff_L_and_R b (a*b)).mp hbab).right

  have habininter : a * b ∈ (R_class_set a) ∩ (L_class_set b) := by
    constructor
    · unfold R_class_set
      exact R_eqv_symm.mp harab
    · unfold L_class_set
      exact L_eqv_symm.mp hblab

  have hidinter : ∃ e : S, e ∈ (R_class_set b) ∩ (L_class_set a) ∧ IsIdempotentElem e := (RL_intersection_contains_mul_iff_contains_idempotent).mp habininter
  have hrclassesequal : R_class_set a = R_class_set b :=
   R_equiv_iff_classes_equal.mp (H_implies_R ha)

  have hlclassesequal : L_class_set a = L_class_set b := L_equiv_iff_classes_equal.mp (H_implies_L ha)
  rw [ Eq.symm hrclassesequal, hlclassesequal] at hidinter
  cases' hidinter with e phi
  use e
  constructor
  · exact phi.2
  · have hare : a 𝓡 e := by
      have h₁ : e ∈ R_class_set a := Set.mem_of_mem_inter_left phi.1
      exact R_eqv_symm.mp h₁
    have hble : b 𝓛 e := by
      have h₂ : e ∈ L_class_set b := Set.mem_of_mem_inter_right phi.1
      exact L_eqv_symm.mp h₂
    have hale : a 𝓛 e := L_eqv_trans (H_implies_L ha) hble
    exact  (H_eqv_iff_L_and_R a e).mpr (And.intro hare hale)

/- end helper lemmas-/

/-! Definitions and lemmas concerning substructures (i.e., subgroups, submonoids, etc. in semigroups). -/

/- An 𝓗-class containing an idempotent is
a Subsemigroup. (substitutes for instance semigroupOnH in code below) -/

def subsemigroupOnH {e : S}(he : IsIdempotentElem e): Subsemigroup S where
  carrier := (H_class_set e)
  mul_mem' := by
    intros ha hb hae hbe
    exact H_mul_closed he hae hbe

/-! Define the structure a monoid in a semigroup. Should be able to do this by extending the preceding, but had trouble with this.-/
class  monoidInSemigroup (S : Type*) [Semigroup S] where
  /-- The carrier of a subsemigroup. -/
  carrier : Set S
  id : S
  id_in_sub : id ∈ carrier
  /-- The product of two elements of the submonoid
  belongs to the submonoid. -/
  mul_mem': ∀ a b : S,a ∈ carrier → b ∈ carrier → a * b ∈ carrier
  /-- id is an identity for the submonoid -/
  id_right_one : ∀ a : S,  a ∈ carrier → a * id = a
  id_left_one : ∀ a : S, a ∈ carrier → id * a = a



/-! An 𝓗-class containing an idempotent is
a monoid in the semigroup. (substitutes for instance monoidOnH in code below). -/

def submonoidOnH {e : S}(he : IsIdempotentElem e): monoidInSemigroup S where
  carrier := (H_class_set e)
  mul_mem' := by
    intros ha hb hae hbe
    exact H_mul_closed he hae hbe
  id := e
  id_in_sub := by
    unfold H_class_set
    simp
  id_right_one := by
    intro a
    intro hae
    exact idempotent_right_identity he hae
  id_left_one := by
    intro a
    intro hae
    exact idempotent_left_identity he hae

/-! Define the structure a group in a semigroup. Should be able to do this by extending the preceding, but had trouble with this.-/
class  groupInSemigroup (S : Type*) [Semigroup S] where
  /-- The carrier of a subsemigroup. -/
  carrier : Set S
  id : S
  id_in_sub : id ∈ carrier
  /-- The product of two elements of the submonoid
  belongs to the submonoid. -/
  mul_mem': ∀ a b : S,a ∈ carrier → b ∈ carrier → a * b ∈ carrier
  /-- id is an identity for the submonoid -/
  id_right_one : ∀ a : S,  a ∈ carrier → a * id = a
  id_left_one : ∀ a : S, a ∈ carrier → id * a = a
  inv : carrier → carrier
  left_inverse : ∀ a : carrier , a * (inv a) = id
  right_inverse : ∀ a : carrier , (inv a) * a  = id

noncomputable def subgroupOnH {e : S}(he : IsIdempotentElem e): groupInSemigroup S where
  carrier := (H_class_set e)
  mul_mem' := by
    intros ha hb hae hbe
    exact H_mul_closed he hae hbe
  id := e
  id_in_sub := by
    unfold H_class_set
    simp
  id_right_one := by
    intro a
    intro hae
    exact idempotent_right_identity he hae
  id_left_one := by
    intro a
    intro hae
    exact idempotent_left_identity he hae
  inv := fun x =>
    let y := Classical.choose (H_class_has_inverse he x.prop)
    let hy := Classical.choose_spec (H_class_has_inverse he x.prop)
    ⟨y, hy.2.2⟩ /- explain exactly what this does -/
  left_inverse := by
    intro x
    simp
    let y := Classical.choose (H_class_has_inverse he x.prop)
    let hy := Classical.choose_spec (H_class_has_inverse he x.prop)
    exact hy.1

  right_inverse :=  by
    intro x
    simp
    let y := Classical.choose (H_class_has_inverse he x.prop)
    let hy := Classical.choose_spec (H_class_has_inverse he x.prop)
    exact hy.2.1

/-! A group of definitions in the style : is an H-class, is a subsemigroup, etc.  Used for giving standard looking mathematical statement of the main theorem of this section. -/

/- A Proposition that says that a set is a subsemigroup of S. -/
def isSubsemigroup (T : Set S) := ∃ u : (Subsemigroup S), T = u.carrier

/- A subsemigroup of S is itself a semigroup (note that the definition of subsemigroup in Mathlib does not require associativity!!)-/

def subsemigroupIsSemigroup (T: Set S)(is_ssg: isSubsemigroup T): Semigroup T where
  mul := fun x y: T => ⟨ x.val * y.val , (by
  cases' is_ssg with u p
  have hx : x.val ∈ T := Subtype.coe_prop x
  have hy : y.val ∈ T := Subtype.coe_prop y
  simp [p] at *
  apply u.mul_mem' hx hy)⟩
  mul_assoc := by
    intros a b c
    apply Subtype.eq
    exact mul_assoc a.val b.val c.val

/- A Proposition that says that a set is an
𝓗-class of S.  -/

def is_H_class (X : Set S) := ∃ s : S, X = H_class_set s

/- Add something similar for J, R and L classes -/
def is_J_class  (X : Set S) := ∃ s : S, X = J_class_set s





def is_R_class (X : Set S) := ∃ s : S, X = R_class_set s

def is_L_class (X : Set S) := ∃ s : S, X = L_class_set s

/- Another basic property of equivalence relations: If H is an H-class and it contains s then it's the H-class of s -/


lemma is_H_class_of (X : Set S)(t : S)(hast : t ∈ X)(ishclass: is_H_class X) :
X = H_class_set t := by

  unfold is_H_class at ishclass
  cases' ishclass with s p
  unfold H_class_set at *
  have ahs : s 𝓗 t := by
    rw [p] at hast
    exact H_eqv_symm.mp hast
  have classes_equal : H_class_set s = H_class_set t := H_equiv_iff_classes_equal.mp ahs
  unfold H_class_set at classes_equal
  rw [classes_equal] at p
  exact p








/-! A Proposition asserting that a subset of
S is a subgroup.-/

def isSubgroup  (G : Set S) := ∃ u : (groupInSemigroup S), G = u.carrier


/- Any two elements of a subgroup of a semigroup are H-related.-/

lemma subgroup_elements_H_equiv (G : Set S)(a b : S)(hsubgrp : isSubgroup G): a ∈ G → b ∈ G → a 𝓗 b := by
  intro haing hbing
  cases' hsubgrp with u gcarrier

  rw [gcarrier] at haing hbing

  have haeqbc : a = b * (u.inv ⟨b, hbing⟩ ).val * a := calc
    a = u.id * a := Eq.symm (u.id_left_one a haing)
    _ = b * (u.inv ⟨b, hbing⟩ ).val * a := by rw [u.left_inverse ⟨b, hbing⟩]
  have harleb : a ≤𝓡 b := by
    apply (R_preorder_iff_without_one a b).mpr
    apply Or.intro_right
    use (u.inv ⟨b, hbing⟩ ) * a
    rw [<-mul_assoc]
    exact haeqbc
  have hbeqac : b = a * (u.inv ⟨ a,haing⟩) * b := calc
    b = u.id * b := Eq.symm (u.id_left_one b hbing)
    _ = a * (u.inv ⟨a, haing⟩ ).val * b := by rw [u.left_inverse ⟨a, haing⟩]
  have hbrlea : b ≤𝓡 a := by
    apply (R_preorder_iff_without_one b a).mpr
    apply Or.intro_right
    use (u.inv ⟨a, haing⟩ ) * b
    rw [<-mul_assoc]
    exact hbeqac
  have harb : a 𝓡 b := by
    unfold R_eqv eqv_of_preorder
    exact ⟨harleb,hbrlea⟩

  have haeqcb : a = a * (u.inv ⟨b, hbing⟩ ).val * b := calc
    a = a * u.id  := Eq.symm (u.id_right_one a haing)
    _ = a * ((u.inv ⟨b, hbing⟩ ).val * b) := by rw [u.right_inverse ⟨b, hbing⟩]
    _ = a * (u.inv ⟨b, hbing⟩ ).val * b  := by rw [<-mul_assoc]

  have halleb : a ≤𝓛 b := by
    apply (L_preorder_iff_without_one a b).mpr
    apply Or.intro_right
    use a * (u.inv ⟨b, hbing⟩)

  have hbeqca : b = b * (u.inv ⟨ a, haing ⟩) * a :=
    calc
      b =  b * u.id := Eq.symm (u.id_right_one b hbing)
      _ = b * (u.inv ⟨ a,haing⟩) * a := by rw [mul_assoc, u.right_inverse ⟨a, haing⟩]


  have hbllea : b ≤𝓛 a := by
    apply (L_preorder_iff_without_one b a).mpr
    apply Or.intro_right
    use b * (u.inv ⟨ a,haing⟩)

  have halb : a 𝓛 b := by
    unfold L_eqv eqv_of_preorder
    exact ⟨halleb,hbllea⟩
  exact (H_eqv_iff_L_and_R a b).mpr ⟨ harb, halb⟩

/- A restatement of subgroupOnH : An H-class containing an idempotent is a subgroup.-/

lemma H_class_with_idempotent_subgroup (H : Set S)
(hishclass : is_H_class H)(hasid: ∃ e : S, e ∈ H ∧ IsIdempotentElem  e) : isSubgroup H
:= by
  obtain ⟨e, einh, eidem⟩ := hasid
  unfold isSubgroup
  let v := subgroupOnH eidem
  use v
  have h: groupInSemigroup.carrier = H_class_set e := rfl
  rw [h]
  exact is_H_class_of H e einh hishclass



/- A subgroup contains an idempotent. -/
lemma subgroup_has_idempotent (G : Set S)(subgp : isSubgroup G) : ∃ e : S, e ∈ G ∧ IsIdempotentElem e
:= by

  cases' subgp with u p
  use u.id
  rw [p]
  constructor
  · exact groupInSemigroup.id_in_sub
  · unfold IsIdempotentElem
    apply groupInSemigroup.id_right_one
    exact groupInSemigroup.id_in_sub

/- An H-class containing an idempotent is a subgroup
of S.-/
/- A Proposition  asserting that a subset of S is
a maximal subgroup of S.-/

def isMaximalSubgroup (G : Set S) := isSubgroup G ∧ ∀ G' : Set S, G ⊆ G' → isSubgroup G' → G = G'

/- This is Corollary 1.7 in the Pin text -/
theorem H_class_tfae
 (H : Set S)(ish : is_H_class H) : List.TFAE [∃ e : S, e ∈ H ∧ (IsIdempotentElem e), (∃ a b : S, a ∈ H ∧ b ∈ H ∧ a * b ∈ H),isMaximalSubgroup H ] := by
  tfae_have 1 → 2 := by
    intro cond1
    obtain ⟨e, einH, eidem⟩ := cond1
    use e, e
    constructor
    · exact einH
    · constructor
      · exact einH
      · rw [eidem]
        exact einH

  tfae_have 2 → 3 := by
    intro cond2
    obtain ⟨ a, b,aih, binh, abinh ⟩  := cond2
    unfold isMaximalSubgroup
    constructor
    · have hasid: ∃ e : S, e ∈ H ∧ IsIdempotentElem  e := by
        have hclassa : H = H_class_set a := is_H_class_of H a aih ish
        have hclassb : H = H_class_set b := is_H_class_of H b binh ish
        have hclassab : H = H_class_set (a * b) := is_H_class_of H (a * b) abinh ish
        have ha : a 𝓗 b := by
          have h₁ : H_class_set a = H_class_set b :=
            Eq.trans (Eq.symm hclassa) hclassb
          apply H_equiv_iff_classes_equal.mpr h₁
        have  haab: a 𝓗 a * b := by
          have h₁ : H_class_set a = H_class_set (a * b) :=
            Eq.trans (Eq.symm hclassa) hclassab
          apply H_equiv_iff_classes_equal.mpr h₁
        obtain ⟨e,isid,ahe⟩ := H_class_product_idempotent a b ha haab
        use e

        constructor
        · have hclasse : H_class_set a = H_class_set e  := H_equiv_iff_classes_equal.mp ahe
          have hhclasse : H = H_class_set e :=
          Eq.trans  hclassa hclasse
          have heclasse : e ∈ (H_class_set e) := by apply H_eqv_refl
          rw [<-hhclasse]  at heclasse
          exact heclasse
        · exact isid
      exact H_class_with_idempotent_subgroup H ish hasid

    · intro  G subHG issubgp
      have subGH : G ⊆ H := by
        intro g ginG
        have ainG : a ∈ G := subHG aih
        have ahg : a 𝓗 g := subgroup_elements_H_equiv G a g issubgp ainG ginG
        have ginhclass : g ∈ H_class_set a := by
          unfold H_class_set
          exact H_eqv_symm.mp ahg
        have hclassa : H = H_class_set a := is_H_class_of H a aih ish
        rw [hclassa]
        exact ginhclass
      exact Set.Subset.antisymm subHG subGH
  tfae_have 3 → 1 := by
    intro h
    have hh : isSubgroup H := h.left
    obtain ⟨e,p,q⟩ :=  subgroup_has_idempotent H hh
    use e
  tfae_finish

/- These next theorems are devoted to reconciling 'groups in semigroups' with groups as already defined in the Math library.-/
/- Map a subgroup to its underlying
groupInSemigroup object and carrier set.-/

noncomputable def subgroup_groupInSemigroup (G : Set S)(h :isSubgroup G):= Classical.choose h

noncomputable def subgroup_groupInSemigroup_prop (G : Set S)(h :isSubgroup G) := Classical.choose_spec h

#check subgroup_groupInSemigroup_prop

/- A subgroup of a semigroup is closed under multiplication. -/

lemma subgroup_mul_closed (G : Set S)(subgp: isSubgroup G ): a ∈ G → b ∈ G → a * b ∈ G := by
  intro aing bing
  cases'  subgp with u gcarrier
  rw [gcarrier]
  rw [gcarrier] at aing  bing
  exact u.mul_mem' a b aing bing

/- A subgroup of a semigroup is associative -/
lemma subgroup_mul_assoc (G : Set S)(subgp: isSubgroup G )(a b c : G):  (a.val  *  b.val ) * c.val = a.val  * (b.val  * c.val) := by

  cases'  subgp with u gcarrier
  exact mul_assoc a.val  b.val  c.val

/- A map sending a subgroup of a semigroup to its identity element-/

noncomputable def id_of_subgroup( G : Set S)(subgp : isSubgroup G) : G := by
    let u := subgroup_groupInSemigroup G subgp
    have member : u.id ∈ G := by
      have gcarrier : G = u.carrier :=  subgroup_groupInSemigroup_prop G subgp
      rw [gcarrier]
      exact u.id_in_sub
    exact ⟨ u.id , member ⟩

/- A map sending a subgroup and an element to
the inverse of the element -/



noncomputable def inv_of_subgroup( G : Set S)(subgp : isSubgroup G)(g :  G) : G := by
    let u := subgroup_groupInSemigroup G subgp
    let v := u.inv

    have gcarrier : G = u.carrier :=  subgroup_groupInSemigroup_prop G subgp
    have member : ↑ g ∈ u.carrier := by
      rw [<-gcarrier]
      exact Subtype.coe_prop g
    rw [gcarrier]
    exact   v ⟨↑ g, member ⟩




lemma subgroup_left_cancel (G : Set S)
(subgp: isSubgroup G )(a : G):   (inv_of_subgroup G subgp a ) *  a.val= (id_of_subgroup G subgp  ) := by
  let w := (inv_of_subgroup G subgp a)
  let u := subgroup_groupInSemigroup G subgp
  have  h₂ : G = u.carrier := subgroup_groupInSemigroup_prop G subgp
  have member : ↑ a ∈ u.carrier := by
    rw [<-h₂]
    exact Subtype.coe_prop a
  have h₃ : w.val =  u.inv ⟨ ↑a , member ⟩ := by
    sorry --how do we get over this bump?


  have h : w.val  * a.val = u.id := by
   rw [h₃]
   apply u.right_inverse
  exact h

/- The idenity element of a subgroup is a right identity, followed by the dual statement-/
lemma subgroup_one_right (G : Set S)
(subgp: isSubgroup G )(a : G): a.val * (id_of_subgroup G subgp ) = a.val := by
  let u := subgroup_groupInSemigroup G subgp
  have h: a.val  * u.id = a  := by
    apply u.id_right_one
    have h₂ : G = u.carrier := subgroup_groupInSemigroup_prop G subgp
    rw [<-h₂]
    exact Subtype.coe_prop a
  exact h

lemma subgroup_one_left (G : Set S)
(subgp: isSubgroup G )(a : G):   (id_of_subgroup G subgp ) *  a.val= a.val := by
  let u := subgroup_groupInSemigroup G subgp
  have h:  u.id * a.val = a   := by
    apply u.id_left_one
    have h₂ : G = u.carrier := subgroup_groupInSemigroup_prop G subgp
    rw [<-h₂]
    exact Subtype.coe_prop a
  exact h

/- A subgroup of a semigroup is a group! -/

noncomputable def  group_of_subgroup (G : Set S)(subgp : isSubgroup G) : Group G where
  mul :=  λ a b :G => ⟨ a.val * b.val,(by
    have aing : a.val ∈ G := Subtype.coe_prop a
    have bing : b.val ∈ G := Subtype.coe_prop b
    exact subgroup_mul_closed G subgp aing bing)⟩
  mul_assoc := by
    intro a b c
    apply Subtype.eq
    exact  subgroup_mul_assoc G subgp a b c


  one := id_of_subgroup G subgp

  one_mul := by
    intro x
    have h := subgroup_one_left G subgp
    rw [← Subtype.coe_inj]
    exact h x

  mul_one := by
    intro x
    have h := subgroup_one_right G subgp
    rw [← Subtype.coe_inj]
    exact h x

  inv := inv_of_subgroup G subgp
  inv_mul_cancel := by
    intro x
    have h:= subgroup_left_cancel G subgp x
    rw [← Subtype.coe_inj]
    exact h

/- This should contain a tatement of Proposition 1.8, that the
maximal subgroups within a D-class are isomorphic. We know the MulEquiv
instance formulation which can be used to assert that a map is an instance of
an isomorphism.  But how do we state that two groups are isomorphic?

Prop 1.8 here (work on statement)

### Regular semigroups
-/

def is_regular_element (s : S): Prop := ∃ t : S, s * t * s = s

def is_regular_J_class (D : Set S )(isjclass : is_J_class D):Prop := ∀ s:S, s ∈ D → is_regular_element s

/-The theorem below  is Proposition 1.9 from Pin. We need to
prove a couple of preliminary lemmas about regular elements in
R- and L- classes -/

lemma regular_Rclass_idempotent (s : S ) : List.TFAE [
    (∃ e : S, e ∈ R_class_set s ∧ IsIdempotentElem e),
    ((∀ t : S, t ∈ R_class_set s → is_regular_element t)),
     ((∃ t : S, t ∈ R_class_set s ∧  is_regular_element t))] := by
tfae_have 1 → 2 := by
  intro claim1
  obtain ⟨ e, sRe, ideme⟩ := claim1
  intro t sRt
  have eRt : e 𝓡 t := sorry
  have teqet : t = e * t := sorry
  have eeqtu : ∃ u : S, e = t * u := sorry
  obtain ⟨ u, etu ⟩ := eeqtu
  unfold is_regular_element
  use u * e
  calc
    t * (u * e) * t = (t * u) * (e * t) := sorry
    _ = e * e * t := sorry
    _ = t := sorry

tfae_have 2 → 3 := by
  intro claim2
  use s
  constructor
  · unfold R_class_set
    exact  R_equiv_iff_classes_equal.mpr rfl
  · apply claim2
    exact  R_equiv_iff_classes_equal.mpr rfl

tfae_have 3 → 1 := by
  intro claim3
  obtain ⟨t,trs,regt⟩ := claim3
  obtain ⟨ x , txt⟩ := regt
  use t * x
  constructor
  · sorry
  · sorry



tfae_finish




lemma regular_Lclass_idempotent (s : S ) : List.TFAE [(∃ e : S, e ∈ L_class_set s ∧ IsIdempotentElem e),((∀ t : S, t ∈ L_class_set s → is_regular_element t)), ((∃ t : S, t ∈ L_class_set s ∧  is_regular_element t))]  := sorry


theorem regular_J_class_tfae
 (D : Set S)(isj : is_J_class D) : List.TFAE [ is_regular_J_class D isj,
  ∃ s : S, s ∈ D ∧ is_regular_element s,
  (∀ s : S, s ∈ D →  (∃ e: S, e ∈ (R_class_set s)  ∧ IsIdempotentElem e)),
   (∀ s : S, s ∈ D →  (∃ e: S, e ∈ (L_class_set s)  ∧ IsIdempotentElem e)),
  (∃ s : S, s ∈ D ∧ IsIdempotentElem s),
  (∃ x y : S, x ∈ D ∧ y ∈ D ∧ x * y ∈ D)] := by
  tfae_have 1 → 2:= by
    unfold is_regular_J_class
    unfold is_J_class at isj
    cases' isj with s Ds
    intro univ
    use ↑s
    have s_in_D : ↑s ∈ D := by
      unfold J_class_set at Ds
      rw [Ds]
      exact J_eqv_refl
    have sreg : is_regular_element s := univ s s_in_D
    exact ⟨ s_in_D, sreg⟩

  tfae_have 2 → 3:= by
    intro claim2 s Ds
    obtain ⟨ t, Dt, regt⟩ := claim2
    have sjt : s 𝓙 t := by
      sorry
    sorry

  tfae_have 3 → 4:= sorry
  tfae_have 4 → 5:= sorry
  tfae_have 5 → 6:= sorry
  tfae_have 6 → 1:= sorry
  tfae_finish




/- Below this line is Soleil's work on the proposition  giving the equivalent characterizations
of H-classes with idempotents. -/
/-! Define a semigroup instance on a subsemig.
/- TODO -/
instance semigroupOnH {e : S} (he : IsIdempotentElem e) :
    Semigroup (H_class_set e) where
  mul := λ (a b : H_class_set e) => ⟨a.val * b.val, (by
    refine Set.mem_def.mpr ?_
    apply H_mul_closed he ?_
    unfold H_class_set at a b
    · exact b.prop
    · exact a.prop)⟩
  mul_assoc := by
    intros a b c
    apply Subtype.eq
    exact mul_assoc a.val b.val c.val

instance monoidOnH {e : S} (he : IsIdempotentElem e) :
    Monoid (H_class_set e) where
  toSemigroup := semigroupOnH he
  one := ⟨e, by simp [H_class_set, Set.mem_setOf_eq]⟩
  one_mul := by
    intro x
    apply Subtype.eq
    exact idempotent_left_identity he x.prop
  mul_one := by
    intro x
    apply Subtype.eq
    exact idempotent_right_identity he x.prop

instance mulOnH {S : Type*} [Finite S][Semigroup S] (e : S) (he : IsIdempotentElem e):
    Mul (H_class_set e) where
  mul := λ a b => ⟨a.val * b.val, H_mul_closed he a.prop b.prop⟩

noncomputable instance groupOnH {e : S} (he : IsIdempotentElem e) : Group (H_class_set e) where
  toMonoid := monoidOnH he
  inv :=  fun x =>
    let y := Classical.choose (H_class_has_inverse he x.prop)
    let hy := Classical.choose_spec (H_class_has_inverse he x.prop)
    ⟨y, hy.2.2⟩
  inv_mul_cancel := by
    intro x
    let y := Classical.choose (H_class_has_inverse he x.prop)
    let hy := Classical.choose_spec (H_class_has_inverse he x.prop)
    cases' x with x hx
    simp
    apply Subtype.eq
    exact hy.2.1

def H_contains_idempotent (H : Set S) : Prop :=
  ∃ e, (IsIdempotentElem e) ∧ (H = H_class_set e)

def H_has_mul_closure (H : Set S) : Prop :=
  ∃ a b, (a ∈ H) ∧ (b ∈ H) ∧ (a * b ∈ H)

def H_is_maximal_group (H : Set S) : Prop :=
  ∃ (e : S) (he : IsIdempotentElem e),
    H = H_class_set e ∧ ∀ (G : Set S), Group G → H ⊆ G → G = H

theorem H_class_tfae {e : S} (H : Set S) (hH : ∃ e, IsIdempotentElem e ∧ H = H_class_set e):
    List.TFAE [H_contains_idempotent H, H_has_mul_closure H, H_is_maximal_group H] := by
  tfae_have 1 → 2 := by
    intro h
    rcases h with ⟨e, he_idem, heq⟩
    use e, e
    constructor
    · rw[heq]
      exact Set.mem_setOf_eq.mpr H_eqv_refl
    constructor
    · rw[heq]
      exact Set.mem_setOf_eq.mpr H_eqv_refl
    · rw[heq]
      exact H_mul_closed he_idem (Set.mem_setOf_eq.mpr H_eqv_refl) (Set.mem_setOf_eq.mpr H_eqv_refl)
  tfae_have 2 → 3 := by
    intro h
    rcases h with ⟨a, b, ha, hb, hab⟩
    obtain ⟨e, he_idem, heq⟩ := hH
    rw[heq] at ha hb hab
    use e, he_idem
    constructor
    · exact heq
    · intros G hG hsub
      apply Eq.symm
      apply Set.Subset.antisymm hsub
      intro g hg
      have h_𝓗 : g 𝓗 e := by
        sorry
      sorry
  tfae_have 3 → 1 :=   by
    intro h_max_group
    rcases h_max_group with ⟨e, he_idem, heq, hmax⟩
    use e
  tfae_finish
end GroupsInSemigroups
-/
