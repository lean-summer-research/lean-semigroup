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


structure Subgroup' (α : Type*) [Mul α] where
  carrier : Set α
  group : Nonempty (Group ↑carrier)

namespace Subgroup'

variable (α : Type*) [Mul α] {x : α} (s : Set α)

instance : SetLike (Subgroup' α) α where
  coe := Subgroup'.carrier
  coe_injective' := fun l q h => by
    cases l
    cases q
    simp_all

@[simp] lemma mem_carrier {p : Subgroup' α} : x ∈ p ↔ x ∈ p.carrier:= Iff.rfl

@[ext] theorem ext {p q : Subgroup' α} (h : ∀ x, x ∈ p ↔ x ∈ q) : p = q := SetLike.ext h

def IsMaximal (S : Subgroup' α) : Prop :=
  ∀ (T : Subgroup' α), S.carrier ⊆ T.carrier → S = T

end Subgroup'

lemma HEquiv.mul_mem_if_contains_idempotent' {M : Type*} [Monoid M] {e x y: M} (hidem : IsIdempotentElem e)
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

structure HClassIdem (M : Type*) [Monoid M] where
  e : M
  hidem : IsIdempotentElem e

namespace HClassIdem

variable {M : Type*} [Monoid M]

@[simp] def Subtype (s : HClassIdem M) := {val : M // val 𝓗 s.e}

instance mulInstance (s : HClassIdem M) : Mul s.Subtype where
  mul (x y : s.Subtype) := ⟨x.val * y.val, HEquiv.mul_mem_if_contains_idempotent' s.hidem x.prop y.prop⟩

lemma coe_mul {s : HClassIdem M} (x y : s.Subtype) :
    (x * y).val = x.val * y.val := by rfl

instance semigroupInstance (s : HClassIdem M) : Semigroup s.Subtype where
  mul_assoc (x y z : s.Subtype) := by
    simp_all [← Subtype.val_inj]
    rw [coe_mul, coe_mul, coe_mul, coe_mul]
    rw [Semigroup.mul_assoc]

instance oneInstance (s : HClassIdem M): One s.Subtype where
  one := ⟨s.e, by simp⟩

@[simp] lemma coe_one (s : HClassIdem M): (1 : s.Subtype).val = s.e := by rfl

instance monoidInstance (s : HClassIdem M) : Monoid s.Subtype where
  one_mul (x : s.Subtype):= by
    simp [← Subtype.coe_inj]
    rw [coe_mul]
    simp
    rw [← RLE.idempotent_iff]
    · have h := x.prop
      simp_all
    · apply s.hidem
  mul_one (x : s.Subtype) := by
    simp [← Subtype.coe_inj]
    rw [coe_mul]
    simp
    rw [← LLE.idempotent_iff]
    · have h := x.prop
      simp_all
    · apply s.hidem

lemma exists_inverse {s : HClassIdem M} (x : s.Subtype) : ∃ y : s.Subtype, y * x = 1 := by
  have hL : s.e ≤𝓛 x.val := by
    have h := x.prop
    simp [h]
  obtain ⟨z, hz⟩ := hL
  have hH : z 𝓗 s.e := by sorry
  use ⟨z, hH⟩
  simp_all [← Subtype.coe_inj]
  rw [coe_mul]
  simp_all

noncomputable instance groupInstance (s : HClassIdem M) : Group s.Subtype where
  inv (x : s.Subtype) := Classical.choose (exists_inverse x)
  inv_mul_cancel (x : s.Subtype) := by apply Classical.choose_spec (exists_inverse x)


instance subgroupInst (s : HClassIdem M) : Subgroup' M where
  carrier := {val : M | val 𝓗 s.e}
  group := by
    simp_all
    have H : Group s.Subtype := groupInstance s
    rw [Subtype] at H
    exact Nonempty.intro H

theorem is_maximal_subgroup (s : HClassIdem M) : s.subgroupInst.IsMaximal := by
  simp_all [Subgroup'.IsMaximal, subgroupInst]
  intros t hIn
  ext x
  simp
  constructor
  · intro hH
    exact hIn hH
  · intro hT
    sorry
