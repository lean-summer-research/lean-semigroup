import MyProject.Monoid.Finite

/-!
# Local Theory

## Main Statments
- Greens Lemma
- Location Theorem
- TODO: Groups in H classes
-/

/-!
### Greens Lemma (Proposition 1.5)
Let `x, y : S` and let `x 𝓡 y` such that `x * u = y` and `y * v = x` for `u, v ∈ M`
Let `ρᵣ u` and `ρᵣ v` be the right translations defined by `(ρᵣ v) z = z * v`
Then these translations induce inverse bijections from `⟦x⟧𝓛` to `⟦y⟧𝓛`
Additionally, these bijections preserve the 𝓗 classes.

TODO: Dual version
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
# Location Theorem (Proposition 1.6)

Let `x, y : M`,
then `x * y` is 𝓡-related to `x` and 𝓛-related to `y` iff
there exists an idmepotetnt that is 𝓛-related to `x` and 𝓡-related to `y`

TODO: Prove Dual version
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

end Location_Theorem

/-!
### Corrollary 1.7

For a given 𝓗-class `⟦x⟧𝓗`, the following conditions are equivalent:
1. `⟦x⟧𝓗` contains an idempotent.
2.  there exist `x, y : M` such that `x * y ∈ ⟦x⟧𝓗`.
3. `⟦x⟧𝓗` is a maximal group in `M`

### Implementation Notes
We create the structures `subsemigroup'`, `submonoid'` and `subgroup'` to represent a
subset `T` of a given semigigroup `S`, implemneted as a set, along with a proof that
this subset is a semigroup, monoid, or group.

We define the canonical morphism from a subsemigroup, submonid,
and subgroup to the original semigroup.

Note that Mathlib's Submonoid requires a monoid, (same with group), but ours only
requires semigroup (could just require mul).

Slight modification to Mathlib's subsemigroup (no setlike and requires semigroup).

-/

variable {α : Type*} [Mul α]

structure Submagma' (carrier : Set α) where
  mul_mem (x y : α) : x ∈ carrier → y ∈ carrier → x * y ∈ carrier


structure Subsemigroup' (carrier : Set α) extends Submagma' carrier where
  mul_assoc (x y z : α) : x ∈ carrier → y ∈ carrier → z ∈ carrier → (x * y) * z = x * (y * z)

namespace Subsemigroup'

instance isSemigroup {s : Set α} (inst : Subsemigroup' s) : Semigroup (↑s) where
  mul (x y : ↑s) := ⟨↑x * ↑y, by
    apply inst.mul_mem ↑x ↑y
    · simp
    · simp ⟩
  mul_assoc (x y z : ↑s) := by
    rw [← Subtype.coe_inj]
    apply inst.mul_assoc ↑x ↑y ↑z
    · simp
    · simp
    · simp

end Subsemigroup'

structure Submonoid' (carrier : Set α) extends Subsemigroup' carrier where
  one : α
  one_mem : one ∈ carrier
  one_mul (x : α) : x ∈ carrier → one * x = x
  mul_one (x : α) : x ∈ carrier → x * one = x

namespace Submonoid'

instance hasOne {s : Set α} (inst : Submonoid' s) : One (↑s) where
  one := ⟨inst.one, inst.one_mem⟩

instance isMonoid {s : Set α} (inst : Submonoid' s) : Monoid (↑s) where
  toSemigroup := inst.isSemigroup
  toOne := inst.hasOne
  one_mul (x : ↑s) := by
    have hOne := hasOne inst
    have hEq : (1 : ↑s) = ⟨inst.one, inst.one_mem⟩ := by sorry
    sorry
  mul_one (x : ↑s) := by sorry

end Submonoid'

structure Subgroup' (carrier : Set α) extends Submonoid' carrier where
  inv (x : α) : x ∈ carrier → α
  inv_mem (x : α) (hx : x ∈ carrier) : inv x hx ∈ carrier
  inv_mul_cancel (x : α) (hx : x ∈ carrier) : (inv x hx) * x = one
  mul_inv_cancel (x : α) (hx : x ∈ carrier) : x * (inv x hx) = one

namespace Subgroup'

instance {s : Set α} (inst : Subgroup' s) : Group (↑s) where
  toMonoid := inst.isMonoid
  inv (x : ↑s) := ⟨inst.inv x.1 x.2, inst.inv_mem x.1 x.2⟩
  inv_mul_cancel (x : ↑s) := by
    have hInv := inst.inv x.1 x.2
    have H := inst.inv_mul_cancel x.1
    sorry

@[simp] def IsMaximal {s : Set α} (_ : Subgroup' s) : Prop :=
  ∀ (t : Set α), Subgroup' t → s ⊆ t → s = t

variable {S : Type*} [Semigroup S] {s : Set S} (instS : Subgroup' s)

lemma idempotent_iff_identity {x : S} (hx : x ∈ s) :
    IsIdempotentElem x ↔ instS.one = x := by
  constructor
  · intro hIdem
    simp_all [IsIdempotentElem]
    have h := instS.inv_mul_cancel x hx
    rw [← h]
    nth_rw 2 [← hIdem]
    rw [← mul_assoc]
    rw [instS.inv_mul_cancel x hx]
    rw [instS.one_mul]
    exact hx
  · intro hEq
    rw [← hEq]
    simp [IsIdempotentElem]
    apply instS.one_mul
    rw [hEq]
    exact hx

lemma eq_one_of_containing_group {t : Set S} (instT : Subgroup' t) (h : s ⊆ t) :
    instS.one = instT.one := by
  have h₁ : IsIdempotentElem (instS.one) := by
    rw [idempotent_iff_identity instS (instS.one_mem)]
  have h₂ : instS.one ∈ t := by apply h; exact instS.one_mem
  have h₃ := idempotent_iff_identity instT h₂
  symm
  rw [← h₃]
  exact h₁

end Subgroup'

variable {M : Type*} [Monoid M]

lemma HEquiv.mul_mem_if_contains_idempotent {e x y: M} (hidem : IsIdempotentElem e)
    (he : x 𝓗 e) (hy : y 𝓗 e) : x * y 𝓗 e := by
  simp [← HEquiv.rEquiv_and_lEquiv_iff] at he hy ⊢
  rcases hy with ⟨hR₁, hR₂⟩
  rcases he with ⟨hL₁, hL₂⟩
  have h : (x * y) 𝓡 x ∧ (x * y) 𝓛 y := by
    apply RL_intersection_contains_mul_iff_contains_idempotent.mp
    use e
    simp_all
  rcases h with ⟨hR₃, hL₃⟩
  constructor
  · apply REquiv.trans hR₃ hL₁
  · apply LEquiv.trans hL₃ hR₂

structure withIdempotent (s : Set M) where
  idem : M
  hidem : IsIdempotentElem idem
  idem_in : idem ∈ s

namespace HClassIdem

variable {x : M} (inst : withIdempotent ⟦x⟧𝓗)

instance isSubmagma' : Submagma' ⟦x⟧𝓗 where
  mul_mem z y hz hy:= by
    simp_all
    have H : x 𝓗 inst.idem := by
      have h₂ := inst.idem_in
      simp at h₂
      exact h₂.symm
    have hz₂ : z 𝓗 inst.idem := by apply HEquiv.trans hz H
    have hy₂ : y 𝓗 inst.idem := by apply HEquiv.trans hy H
    refine HEquiv.trans ?_ H.symm
    apply HEquiv.mul_mem_if_contains_idempotent inst.hidem hz₂ hy₂

instance isSubsemigroup' : Subsemigroup' ⟦x⟧𝓗 where
  toSubmagma' := isSubmagma' inst
  mul_assoc z y w hz hy hw := by apply mul_assoc


instance isSubmonoid' : Submonoid' (HEquiv.set x) where
  toSubsemigroup' := isSubsemigroup' inst
  one := inst.idem
  one_mem := inst.idem_in
  one_mul x hz := by
    rw [← RLE.idempotent_iff]
    simp_all
    have h₁ : z ≤𝓡 x := by simp_all
    have h₂ : x ≤𝓡 inst.idem := by
      have h₃ := inst.idem_in
      simp_all
    apply RLE.trans h₁ h₂
    exact inst.hidem

lemma exists_inverse {y : M} (hy : y ∈ ⟦x⟧𝓗) : ∃ z, z * y = inst.idem ∧ z ∈ ⟦x⟧𝓗 := by
  have hH : inst.idem 𝓗 x := inst.idem_in
  have hL : inst.idem ≤𝓛 y := by
    have hL₁ : inst.idem ≤𝓛 x := by simp_all
    have hL₂ : x ≤𝓛 y := by simp_all
    apply LLE.trans hL₁ hL₂
  obtain ⟨z, hz⟩ := hL
  have hz₂ : z ∈ ⟦x⟧𝓗 := by
    sorry
  exact ⟨z, ⟨hz, hz₂⟩⟩
-- TODO, dual of above

noncomputable instance isSubgroup' : Subgroup' ⟦x⟧𝓗 where
  toSubmonoid' := isSubmonoid' inst
  inv z hz := Classical.choose (exists_inverse inst hz)
  inv_mem z hz := by
    have H := Classical.choose_spec (exists_inverse inst hz)
    apply H.2
  inv_mul_cancel z hz := by
    have H := Classical.choose_spec (exists_inverse inst hz)
    apply H.1
  mul_inv_cancel z hz := by sorry

lemma one_eq_idem {x : M} (inst : withIdempotent ⟦x⟧𝓗) :
    (isSubgroup' inst).one = inst.idem := by rfl

/-- For all subgroups on Monoids, every element of the subgroup is
𝓗-related to the identity -/
lemma subgroup_H_id {s : Set M} (instS : Subgroup' s) {x : M} (hx : x ∈ s) :
    x 𝓗 instS.one := by
  have hIdem := instS.idempotent_iff_identity hx
  simp [← HEquiv.rEquiv_and_lEquiv_iff]
  constructor
  · constructor
    · use x
      apply instS.one_mul x hx
    · use instS.inv x hx
      apply instS.mul_inv_cancel x hx
  · constructor
    · use x
      apply instS.mul_one x hx
    · use instS.inv x hx
      apply instS.inv_mul_cancel x hx

theorem maximal_subgroup : (isSubgroup' inst).IsMaximal := by
  simp_all
  rintro t instT hIn
  ext z
  constructor
  · intro hz
    apply hIn
    exact hz
  · intros hz
    simp_all
    have hin : inst.idem ∈ t := by apply hIn; exact inst.idem_in
    have hH₁ : z 𝓗 inst.idem := by
      have hId₁ : inst.idem = (isSubgroup' inst).one := by rfl
      have hId₂ : (isSubgroup' inst).one = instT.one :=
        Subgroup'.eq_one_of_containing_group (isSubgroup' inst) instT hIn
      rw [hId₁, hId₂]
      apply subgroup_H_id instT hz
    have hH₂ : x 𝓗 inst.idem := inst.idem_in.symm
    apply HEquiv.trans hH₁ hH₂.symm


end HClassIdem
