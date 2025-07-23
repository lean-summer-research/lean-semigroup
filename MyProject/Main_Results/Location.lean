import MyProject.Main_Results.Greens_lemma

/-!
# Location Theorem

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

variable {S} [Semigroup S] {e x a b : S}
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

/-- An 𝓗 class containing an identity is closed under multiplication-/
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
        have hba : a = b := by
          calc
          a = a * (x * d) := hax.symm
          _ = b * (x * d) := by simp[<-mul_assoc, hab]
          _ = b * e := by rw[hd]
          _ = b := idempotent_right_identity he hb
        exact hba
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

lemma H_class_has_inverse {S : Type*} [Semigroup S]
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
      have ⟨hl, hr⟩ := idempotent_identity_H_eqv he hx
      have hee : e * e = e := he
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
      have hy1 : y = e * y := by
        apply (idempotent_identity_H_eqv he hyH).left.symm
      have hy2 : y = y * e := by
        apply (idempotent_identity_H_eqv he hyH).right.symm
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

/- end helper lemmas-/


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

instance mulOnH {S : Type*} [Semigroup S] (e : S) (he : IsIdempotentElem e):
    Mul (H_class_set e) where
  mul := λ a b => ⟨a.val * b.val, H_mul_closed he a.prop b.prop⟩

instance groupOnH {e : S} (he : IsIdempotentElem e) : Group (H_class_set e) where
  toMonoid := monoidOnH he
  inv := λ x => ⟨(H_class_has_inverse he x.prop).choose, (H_class_has_inverse he x.prop).choose_spec.2.2⟩
  inv_mul_cancel := by sorry
end GroupsInSemigroups
