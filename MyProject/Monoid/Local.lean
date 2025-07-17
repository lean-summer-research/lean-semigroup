import MyProject.Monoid.Finite

/-!
# Local Theory

## Main Statments
- Greens Lemma
- Location Theorem
- TODO: Groups in H classes
-/

/-!
### Greens Lemma
Let `x, y : S` and let `x 𝓡 y` such that `↑x * u = ↑y` and `↑y * v = ↑x` for `u, v ∈ S¹`
Then the function `f := z => ↓(↑z * u)` is a bijection from `⟦x⟧𝓛 → ⟦y⟧𝓛`
and `g := z => ↓(v * ↑z)` is its inverse.
Moreover, these bijections preserve the 𝓗 classes.

TODO: We also prove the dual version of this lemma which uses left translations to
form a bijection on the 𝓡 classes.
-/

section Translations

open WithOne

variable {M : Type*} [Monoid M]

@[simp] def rightTranslation (x y : M) := y * x
notation "ρᵣ" => rightTranslation

@[simp] def leftTranslation (x y : M) := x * y
notation "ρₗ" => leftTranslation


@[simp] lemma right_translation_eq_id : ρᵣ (1 : M) = id := by
  unfold rightTranslation id
  simp

@[simp] lemma left_translation_eq_id : ρₗ (1 : M) = id := by
  unfold leftTranslation id
  simp

end Translations

section GreensLemma

variable {M : Type*} [Monoid M] {x y z u v t w : M}

lemma right_id_of_lLE (hId : x * y = x) (hz : z ≤𝓛 x) : z * y = z := by
  rcases hz with ⟨u, hu⟩
  rw [← hu, mul_assoc, hId]

/-- If `x 𝓡 y` such that `x * u = y` and `y * v = x`, then right translation by `u * v`
on any element `z` L-below  `x` is the identity. -/
lemma right_id_of_rEquiv_and_lLE (hu : x * u = y) (hv : y * v = x) (hz : z ≤𝓛 x) :
    z * u * v = z := by
  rcases hz with ⟨z, hz⟩
  rw [← hz, mul_assoc z, hu, mul_assoc, hv]

theorem right_translation_bijection (hu : x * u = y) (hv : x ≤𝓡 y) :
    Set.BijOn (ρᵣ u) ⟦x⟧𝓛 ⟦y⟧𝓛 := by
  obtain ⟨v, hv⟩ := hv
  refine Set.BijOn.mk ?_ ?_ ?_
  · simp [Set.MapsTo]
    intros z hL
    rw [← hu]
    apply LEquiv.mul_right_compat
    exact hL
  · simp [Set.InjOn]
    intros z hLz w hLw hEq
    have h₁ : z * u * v = z := by apply right_id_of_rEquiv_and_lLE hu hv; simp [hLz]
    have h₂ : w * u * v = w := by apply right_id_of_rEquiv_and_lLE hu hv; simp [hLw]
    rw [← h₁, ← h₂, hEq]
  · simp [Set.SurjOn]
    intros z hz
    simp_all
    use z * v
    constructor
    · rw [← hv] -- goal: `z * v 𝓛 x`
      apply LEquiv.mul_right_compat
      exact hz
    · apply right_id_of_rEquiv_and_lLE hv hu -- goal: `z * v * u = x`
      simp [hz]

lemma right_translation_inv (hu : x * u = y) (hv : y * v = x) :
    Set.InvOn (ρᵣ v) (ρᵣ u) ⟦x⟧𝓛 ⟦y⟧𝓛 := by
  simp_all [Set.InvOn]
  constructor
  · simp [Set.LeftInvOn]
    intros z hz
    apply right_id_of_rEquiv_and_lLE hu hv
    simp [hz]
  · simp [Set.RightInvOn, Set.LeftInvOn]
    intros z hz
    apply right_id_of_rEquiv_and_lLE hv hu
    simp [hz]

theorem right_translation_preserves_h (hu : x * u = y) (hv : y * v = x) (ht : t 𝓛 x) (hw : w 𝓛 x) :
    ρᵣ u t 𝓗 ρᵣ u w ↔ t 𝓗 w := by
  simp_all [← HEquiv.rEquiv_and_lEquiv_iff]
  have hx : x * (u * v) = x := by simp [← mul_assoc, hu, hv]
  have ht₂ : t * (u * v) = t := right_id_of_lLE hx ht.le
  have hw₂ : w * (u * v) = w := right_id_of_lLE hx hw.le
  have hRt : t 𝓡 t * u := by
    simp [REquiv]
    use v
    simp [ht₂, mul_assoc]
  have hRw : w 𝓡 w * u := by
    simp [REquiv]
    use v
    simp [hw₂, mul_assoc]
  clear hx hu hv
  constructor
  · rintro ⟨h₁, h₂⟩
    constructor
    · apply REquiv.trans hRt
      apply REquiv.trans h₁ hRw.symm
    · rw [← mul_assoc] at ht₂ hw₂
      rw [← ht₂, ← hw₂]
      apply LEquiv.mul_right_compat
      exact h₂
  · rintro ⟨h₁, h₂⟩
    constructor
    · apply REquiv.trans hRt.symm
      apply REquiv.trans h₁ hRw
    · apply LEquiv.mul_right_compat
      exact h₂

end GreensLemma

/-!
# Location Theorem

This file proves the Location Theorem, which states the following conditions are equivalent
  1. `a * b ∈ R_class_set a ∩ L_class_set b`
  2. `R_class_set b ∩ L_class_set a` contains an idempotent element.
  3. (TODO) ``a * b 𝓓 b`?

We also prove the dual version of these statments (TODO)

This file also contains corrolaries about idempotent-containing H-classes

TODO: have a Group Instance for H-classes containing idempotents
-/

section Location_Theorem

variable {M : Type*} [Monoid M] {x y : M}

theorem RL_intersection_contains_mul_iff_contains_idempotent :
    (∃ e, IsIdempotentElem e ∧ (e 𝓛 x) ∧ (e 𝓡 y)) ↔
    (x * y 𝓡 x) ∧ (x * y 𝓛 y) := by
  constructor
  · rintro ⟨e, ⟨hIdem, hL, hR⟩⟩
    rcases _ : hL with ⟨_, hex⟩
    rcases _ : hR with ⟨_, hey⟩
    rw [RLE.idempotent_iff y e hIdem] at hey
    rw [LLE.idempotent_iff x e hIdem] at hex
    constructor
    · nth_rw 2 [← hex]
      apply REquiv.mul_left_compat x hR.symm
    · nth_rw 2 [← hey]
      apply LEquiv.mul_right_compat y hL.symm
  · rintro ⟨hR, hL⟩
    have hEq : x * y = x * y := by rfl
    have hBij := right_translation_bijection hEq hR.ge
    have hSurj := hBij.surjOn; clear hBij
    simp [Set.SurjOn, Set.subset_def] at hSurj
    specialize hSurj y
    obtain ⟨t, hLt, hRt⟩ := hSurj hL.symm
    use t
    rcases _ : hR with ⟨_, ⟨u, hu⟩⟩
    have ht : t * y * u = t := right_id_of_rEquiv_and_lLE hEq hu hLt.le
    constructor
    · simp [IsIdempotentElem]
      nth_rw 3 [← ht]
      rw [← hRt, mul_assoc, ht]
    · simp_all [REquiv]
      constructor
      · use u
      · use y
