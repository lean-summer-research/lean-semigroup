import MyProject.GreensRelations.D_Rel

/-!
# Homomorphisms and Isomorphisms of Semigroups

This file introduces homomorphisms and isomorphisms of semigroups, together with associated
notations. In fact, these notions are already defined in mathlib for arbitrary multiplicative
structures, so there is no need to introduce anything new for semigroups, for which the definitions
are the same.

It then proves a number of properties concerning preservation of Green's relations and idempotence
under homomorphisms and isomorphisms.

## Main definitions and notations

**Homomorphisms and Isomorphisms**:

* `S →ₙ* T` (defined in Mathlib.Algebra.Hom.Group) If `S` and `T` are semigroups (or any
multiplicative structures) then `MulHom S T` denotes the type of multiplication-preserving
maps--that is, homomorphisms--from `S` to `T`. This is also denoted `S →ₙ* T`. (A member of this
type is a structure bundling the map and a proof that it is multiplication-preserving, however
some typeclass magic tricks allow us to treat it as the map itself.)

* (defined in Mathlib.Algebra.Hom.Group) `MulEquiv S T` denotes the type of isomorphisms between
`S` and `T`. This is also denoted `S ≃* T`.

**Stable binary relations**

* `hom_stable` -- A family of binary relations `Rel` on semigroups is hom-stable if for every
homomorphism `h` of semigroups, `s Rel s'` implies `(h s) Rel (h s')`.

* `iso-stable` -- A family of binary relations `Rel` on semigroups is iso-stable if for every
isomorphism `h` of semigroups, `s Rel s'` if and only if ` (h s) Rel (h s')`.

## Main statements

* We prove that Green's orders and equivalences are hom-stable and iso-stable.

* `idempotent_preimage` -- In finite semigroups, if `h : S →ₙ* T` and `e ∈ T` is an idempotent in the
image of `h`, then `h⁻¹(e)` contains an idempotent.

## TODO

* This file contains a separate proof that the inverse of an isomorphism is an isomorphism. But
this is also proved in Mathlib.Algebra.Hom.Group, so it would be desirable to apply the version
of this statement as alredy given, rather than redoing this from scratch.
-/

/-!
### Preservations of Green's relations under homomorphisms

This section shows that the 𝓡,𝓛,𝓙 orders and equivalences are preserved under homomorphisms.
-/

section Preservations

variable {S T : Type} [Semigroup S] [Semigroup T] (h : S →ₙ* T) (s₁ s₂ : S)

/-- ≤𝓡 is preserved under homomorphisms -/
lemma R_order_preserved (ord : s₁ ≤𝓡 s₂): (h s₁) ≤𝓡 (h s₂) := by
  rw [R_preorder_iff_without_one] at *
  cases' ord with eq neq
  · left; congr
  · right
    cases' neq with x prod
    use h x
    rw [← map_mul, prod]

/-- ≤𝓛 is preserved under homomorphisms -/
lemma L_order_preserved (ord : s₁ ≤𝓛 s₂) : (h  s₁) ≤𝓛 (h  s₂) := by
  rw [L_preorder_iff_without_one] at *
  cases' ord with eq neq
  · left; congr
  · right
    cases' neq with x prod
    use h x
    rw [← map_mul, prod]

/-- ≤𝓙 is preserved under homomorphisms -/
lemma J_order_preserved (ord : s₁ ≤𝓙 s₂) : (h  s₁) ≤𝓙  (h  s₂) := by
  rw [J_preorder_iff_without_one] at *
  rcases ord with heq | hl | hr | hj
  · left; congr
  · right; left; apply L_order_preserved; assumption
  · right; right; left; apply R_order_preserved; assumption
  · right; right; right
    rcases hj with ⟨x, y, prod⟩
    use h x, h y
    simp [← map_mul]
    congr

end Preservations

/-! ## hom-stable relations

This defines what it means for a family of relations on semigroups to be preserved under
homomorphisms, and shows that the orders and equivalences in Green's relations are preserved.
The results on the preorders are just restatements of the lemmas in the preceding section, but
this is stated in a way that allows us to talk about a family of relations having a given property.

We also show preservation under isomorphisms.
-/

def hom_stable (rel : {T : Type} → [Semigroup T] →  T → T → Prop ) : Prop :=
  ∀ (S₁ S₂ : Type) [Semigroup S₁] [Semigroup S₂] (h : S₁ →ₙ* S₂) (s s' : S₁),
    rel s s' → rel (h s) (h s')

/- The lemmas above can be translated by saying that the various relations are hom_stable. This
one is for the L-order, but the proofs for the other relations are the same. -/

lemma L_order_hom_stable : hom_stable L_preorder := by
  intros S₁ S₂ ins1 ins2 h s s' lord
  apply L_order_preserved
  exact lord

lemma R_order_hom_stable : hom_stable R_preorder := by
  intros S₁ S₂ ins1 ins2 h s s' rord
  apply R_order_preserved
  exact rord

lemma J_order_hom_stable : hom_stable J_preorder := by
  intros S₁ S₂ ins1 ins2 h s s' jord
  apply J_order_preserved
  exact jord

lemma L_equiv_hom_stable: hom_stable L_eqv := by
  intros S₁ S₂ ins1 ins2 h s s' leq
  simp_all [L_eqv_iff]
  rcases leq with ⟨lord₁, lord₂⟩
  apply L_order_preserved h at lord₁
  apply L_order_preserved h at lord₂
  constructor <;> assumption

lemma R_equiv_hom_stable: hom_stable R_eqv := by
  intros S₁ S₂ ins1 ins2 h s s' req
  simp_all [R_eqv_iff]
  rcases req with ⟨rord₁, rord₂⟩
  apply R_order_preserved h at rord₁
  apply R_order_preserved h at rord₂
  constructor <;> assumption

lemma J_equiv_hom_stable: hom_stable J_eqv := by
  intros S₁ S₂ ins1 ins2 h s s' jeq
  simp_all [J_eqv_iff]
  rcases jeq with ⟨jord₁, jord₂⟩
  apply J_order_preserved h at jord₁
  apply J_order_preserved h at jord₂
  constructor <;> assumption

lemma D_eqiv_hom_stable : hom_stable D_eqv := by
  intros S₁ S₂ ins1 ins2 h s s' deq
  simp_all [D_eqv_iff]
  rcases deq with ⟨x, rord, lord⟩
  use h x
  constructor
  · apply R_equiv_hom_stable
    exact rord
  · apply L_equiv_hom_stable
    exact lord

/-! ## iso-stable relations

This section defines what it means for a family of binary relations on semigroups to be stable
under isomorphisms. We prove a very general result that hom-stable relations are iso-stable, and
use it to give short proofs that the Green orders and equivalences are all iso-stable.
-/

/-- Definition of an isomorphism-stable family of relations on semigroups.-/
def iso_stable (rel : {T : Type} → [Semigroup T] → T → T → Prop ) : Prop :=
  ∀ (S₁ S₂ : Type) [Semigroup S₁] [Semigroup S₂] (h : S₁ ≃* S₂) (s s' : S₁),
    rel s s' ↔ rel (h s) (h s')

section Inverse_Isomorphism

variable {S T : Type} [Semigroup S] [Semigroup T] (h : S ≃* T)

/-- An isomorphism composed with its inverse is the identity -/
lemma inv_id (t : T) : t = h (h.invFun t) := by simp

/-- The inverse of an isomorphism is an isomorphism.-/
instance inviso : T ≃* S where
  toFun := h.invFun
  invFun := h.toFun
  left_inv := h.right_inv
  right_inv := h.left_inv
  map_mul' := by
    intros x y
    apply MulEquiv.injective h
    rw [map_mul h, ← inv_id, ← inv_id, ← inv_id]

lemma inviso_invFun : (inviso h) = h.invFun := by
  ext t; simp [inviso]

lemma inviso_comp_id (s : S) : (inviso h) (h s) = s := by
  rw [inviso_invFun]; simp

lemma inviso_comp_id' (t : T) : h ((inviso h) t) = t := by
  rw [inviso_invFun]; simp

end Inverse_Isomorphism

/- A relation that is stable under homomorphisms is stable under isomorphisms.-/

lemma hom_stable_iso_stable (rel : {T : Type} → [Semigroup T] → T → T → Prop) (hs : hom_stable rel) : iso_stable rel := by
  unfold hom_stable at hs
  unfold iso_stable
  simp
  intros S₁ S₂ ins1 ins2 h s s'
  constructor
  · intro rs₁s₂
    exact hs S₁ S₂ h s s' rs₁s₂
  · intro rhs₁hs₂
    have k: rel ((inviso h) (h s)) ((inviso h) (h s')) :=  hs S₂ S₁ (inviso h) (h s) (h s') rhs₁hs₂
    simp_rw [inviso_comp_id] at k
    exact k

lemma L_order_iso_stable :  iso_stable @L_preorder := by
  apply hom_stable_iso_stable
  exact L_order_hom_stable

lemma R_order_iso_stable :  iso_stable @R_preorder := by
  apply hom_stable_iso_stable
  exact R_order_hom_stable

lemma J_order_iso_stable :  iso_stable @J_preorder := by
  apply hom_stable_iso_stable
  exact J_order_hom_stable

lemma L_equiv_iso_stable :  iso_stable @L_eqv := by
  apply hom_stable_iso_stable
  exact L_equiv_hom_stable

lemma R_equiv_iso_stable :  iso_stable @R_eqv := by
  apply hom_stable_iso_stable
  exact R_equiv_hom_stable

lemma J_equiv_iso_stable :  iso_stable @J_eqv := by
  apply hom_stable_iso_stable
  exact J_equiv_hom_stable

lemma D_eqiv_iso_stable :  iso_stable @D_eqv := by
  apply hom_stable_iso_stable
  exact D_eqiv_hom_stable

/-! ### Powers and Idempotents

This section shows that powering is preserved under homomorphisms, and that idempotents are
preserved under homomorphisms and isomorphisms.  It also shows that in the finite case, every
idempotent in the image of a homomorphism has an idempotent preimage.
-/

section Powers_Idempotents

variable {S T : Type} [Semigroup S] [Semigroup T] (h : S →ₙ* T) (i : S ≃* T) (n : ℕ+)

/-- Homomorphisms preserve powers of elements. -/
lemma hom_powers (s : S) : h (s ^ n) = (h s) ^ n := by
  induction n using PNat.recOn with
  | one => rfl
  | succ n' ih => simp_rw [← PNat.pow_succ, map_mul h, ih]

/-- Homomorphisms preserve idempotents (forward direction) -/
lemma idempotent_hom_preserved (e : S) (id : IsIdempotentElem e) : IsIdempotentElem (h e) := by
  unfold IsIdempotentElem at *
  rw [← map_mul h, id]


/-- Isomorphisms preserve idempotents (both directions) -/
lemma idempotent_iso_preserved (e : S) : IsIdempotentElem e ↔ IsIdempotentElem (i e) := by
  constructor
  · intro id
    apply idempotent_hom_preserved i.toMulHom
    exact id
  · intro hid
    rw [← inviso_comp_id i e]
    apply idempotent_hom_preserved (inviso i).toMulHom
    assumption

/- For finite `S`: If `h : S →ₙ* T` and `e ∈ T` is an idempotent in the image of `h`,
then `h⁻¹(e)` contains an idempotent.-/
lemma idempotent_preimage [Finite S] (e : T) (id : IsIdempotentElem e) (inimage : ∃ g : S, h g = e) : ∃ f : S, (IsIdempotentElem f) ∧ (h f = e) := by
  cases' inimage with g hge
  subst hge
  have idpower : ∃ k : ℕ+, (IsIdempotentElem (g^k)) := Semigroup.exists_idempotent_pow g
  cases' idpower with k gkid
  use (g^k)
  constructor
  · exact gkid
  · rw [hom_powers]
    apply Semigroup.pow_succ_eq
    exact id

end Powers_Idempotents
