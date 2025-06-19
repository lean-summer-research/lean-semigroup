import MyProject.GreensRelations.Defs


/-!
# Homomorphisms and Isomorphisms of Semigroups

This file introduces homomorphisms and isomorphisms of semigroups, together with associated notations.
In fact, these notions are already defined in mathlib for arbitrary multiplicative structures, so there is no need to introduce anything new for semigroups, for which the definitions are the same.

It then proves a number of properties concerning preservation of Green's relations and idempotence under homomorphisms and isomorphisms.

## Main definitions and notations

**Homomorphisms and Isomorphisms**:

* `S →ₙ* T` (defined in Mathlib.Algebra.Hom.Group) If `S` and `T` are semigroups (or any multiplicative structures) then `MulHom S T` denotes the type of multiplication-preserving maps--that is, homomorphisms--from `S` to `T`. This is also denoted `S →ₙ* T`. (A member of this type is a structure bundling the map and a proof that it is multiplication-preserving, however some typeclass magic tricks allow us to treat it as the map itself.)

* (defined in Mathlib.Algebra.Hom.Group) `MulEquiv S T` denotes the type of isomorphisms between `S` and `T`. This is also denoted `S ≃* T`.

**Stable binary relations**

* `hom_stable` -- A family of binary relations `Rel` on semigroups is hom-stable if for every homomorphism `h` of semigroups, `s Rel s'` implies
`(h s) Rel (h s')`.

* `iso-stable` -- A family of binary relations `Rel` on semigroups is iso-stable if for every isomorphism `h` of semigroups, `s Rel s'` if and only if ` (h s) Rel (h s')`.

## Main statements


## TODO

* Fill in Main statements above!
* This file contains a separate proof that the inverse of an isomorphism is an isomorphism. But this is also proved in Mathlib.Algebra.Hom.Group, so it would be desirable to apply the version of this statement as alredy given, rather than redoing this from scratch.
-/

/-!
## Preservations of Green's relations under homomorphisms

This section shows that the 𝓡,𝓛,𝓙 orders and equivalences are preserved under homomorphisms.

-/
lemma R_order_preserved (S T: Type)[Semigroup S]
[Semigroup T](h : S →ₙ* T)(s₁ s₂: S)(ord : s₁ ≤𝓡 s₂) : (h  s₁) ≤𝓡 (h  s₂) := by
  rw [R_preorder_iff_without_one] at *
  cases' ord with eq neq
  · apply congrArg h  at eq
    exact Or.intro_left _ eq
  · cases' neq with x prod
    have hprod : ∃ u: T, (h  s₁) = (h  s₂) * u := by
      use h  x
      apply congrArg h  at prod
      rw [map_mul h] at prod
      exact prod
    exact Or.intro_right _ hprod

/- The L-order is preserved under morphisms.-/

lemma L_order_preserved (S T: Type)[Semigroup S]
[Semigroup T](h : S →ₙ* T)(s₁ s₂: S)(ord : s₁ ≤𝓛 s₂) : (h  s₁) ≤𝓛 (h  s₂) := by
  rw [L_preorder_iff_without_one] at *
  cases' ord with eq neq
  · apply congrArg h  at eq
    exact Or.intro_left _ eq
  · cases' neq with x prod
    have hprod : ∃ u: T, (h  s₁) = u * (h  s₂)  := by
      use h  x
      apply congrArg h  at prod
      rw [map_mul h ] at prod
      exact prod
    exact Or.intro_right _ hprod


lemma J_order_preserved (S T: Type)[Semigroup S]
[Semigroup T](h : S →ₙ* T)(s₁ s₂: S)(ord : s₁ ≤𝓙 s₂) : (h  s₁) ≤𝓙  (h  s₂) := by
  rw [J_preorder_iff_without_one] at *
  cases' ord with eq neq
  · apply congrArg h  at eq
    exact Or.intro_left _ eq
  · cases' neq with l rj
    · have lord : h s₁ ≤𝓛 h s₂ :=  L_order_preserved S T  h s₁ s₂ l
      tauto
    · cases' rj with r j
      · have rord : h s₁ ≤𝓡 h s₂ :=  R_order_preserved S T  h s₁ s₂ r
        tauto
      · obtain ⟨ x, y, prod ⟩ := j
        have hprod : ∃ u v: T, (h  s₁) = u * (h  s₂) * v  := by
          use h x
          use h y
          apply congrArg h  at prod
          rw [map_mul h, map_mul h] at prod
          exact prod
        tauto

/-! ## hom-stable relations

This defines what it means for a family of relations on semigroups to be preserved under homomorphisms, and shows that the orders and equivalences in Green's relations are  preserved. The results on the preorders are just restatements of the lemmas in the preceding section, but this is stated in a way that allows us to talk about a family of relations having a given property.

We also show preservation under isomorphisms.

-/

def hom_stable (rel :(T : Type)→ [Semigroup T] →  T → T → Prop ) : Prop := ∀ (S₁  S₂ : Type)[Semigroup S₁][Semigroup S₂](h : S₁ →ₙ* S₂)(s s' : S₁), rel S₁ s s' → rel S₂ (h s) (h s')

/- The lemmas above can be translated by saying that the various relations are hom_stable.  This
one is for the L-order, but the proofs for the other relations are the same. -/

lemma L_order_hom_stable : hom_stable @L_preorder := by
  intros S₁ S₂ ins1 ins2 h s s' lord
  apply L_order_preserved
  exact lord

lemma R_order_hom_stable : hom_stable @R_preorder := by
  intros S₁ S₂ ins1 ins2 h s s' rord
  apply R_order_preserved
  exact rord

lemma J_order_hom_stable : hom_stable @J_preorder := by
  intros S₁ S₂ ins1 ins2 h s s' jord
  apply J_order_preserved
  exact jord

lemma L_equiv_hom_stable: hom_stable @L_eqv := by
  intros S₁ S₂ ins1 ins2 h s s' leq
  unfold L_eqv at leq
  constructor
  · have sls': s ≤𝓛 s' := leq.left
    apply L_order_hom_stable
    exact sls'
  · have s'ls : s' ≤𝓛 s := leq.right
    apply L_order_hom_stable
    exact s'ls

lemma R_equiv_hom_stable: hom_stable @R_eqv := by
  intros S₁ S₂ ins1 ins2 h s s' req
  unfold R_eqv at req
  constructor
  · have srs': s ≤𝓡 s' := req.left
    apply R_order_hom_stable
    exact srs'
  · have s'rs : s' ≤𝓡 s := req.right
    apply R_order_hom_stable
    exact s'rs

lemma J_equiv_hom_stable: hom_stable @J_eqv := by
  intros S₁ S₂ ins1 ins2 h s s' jeq
  unfold J_eqv at jeq
  constructor
  · have sjs': s ≤𝓙 s' := jeq.left
    apply J_order_hom_stable
    exact sjs'
  · have s'js : s' ≤𝓙 s := jeq.right
    apply J_order_hom_stable
    exact s'js

/-! ## iso-stable relations

This section defines what it means for a family of binary relations on semigroups to be stable under isomorphisms. We prove a very general result that hom-stable relations are iso-stable, and use it to give short proofs that the Green orders and equivalences are all iso-stable.

-/

/- The inverse of an isomorphism is an isomorphism.-/

lemma inv1 {S}{T}[Semigroup S][Semigroup T](hs : S ≃* T) (t: T): t = hs (hs.invFun t)  := (MulEquiv.symm_apply_eq hs).mp rfl


instance inviso {S}{T}[Semigroup S][Semigroup T](hs : S ≃* T) : T ≃* S where
  toFun := hs.invFun
  invFun := hs.toFun
  left_inv := hs.right_inv
  right_inv := hs.left_inv
  map_mul' := by
    intros x y
    have u: hs (hs.invFun (x * y)) = hs ((hs.invFun x)* (hs.invFun y)) := by rw [<-inv1, map_mul hs, <-inv1 ,<-inv1]
    exact MulEquiv.injective hs u


/- Definition of an isomorphism-stable family of relations.-/

def iso_stable (rel :(T : Type)→ [Semigroup T] →  T → T → Prop ) : Prop := ∀ (S₁  S₂ : Type)[Semigroup S₁][Semigroup S₂](h : S₁ ≃* S₂)(s s' : S₁), rel S₁ s s' ↔ rel S₂ (h s) (h s')

/- A relation that is stable under homomorphisms is stable under isomorphisms.-/

lemma hom_stable_iso_stable (rel :(T : Type)→ [Semigroup T] →  T → T → Prop ) (hs : hom_stable rel) : iso_stable rel := by
  unfold hom_stable at hs
  unfold iso_stable
  intros S₁ S₂ ins1 ins2 h s s'
  constructor
  · intro rs₁s₂
    exact hs S₁ S₂  h s s' rs₁s₂
  · intro rhs₁hs₂
    have k: rel S₁ ((inviso h) (h s)) ((inviso h) (h s')) :=  hs S₂ S₁ (inviso h) (h s) (h s') rhs₁hs₂
    have k₂: ((inviso h) (h s)) = s := (MulEquiv.eq_symm_apply (inviso h)).mp rfl
    have k₃: ((inviso h) (h s')) = s' := (MulEquiv.eq_symm_apply (inviso h)).mp rfl
    rw [k₂,k₃] at k
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

/-!

## Powers and Idempotents

This section shows that powering is preserved under homomorphisms, and that idempotents are preserved under homomorphisms and isomorphisms.  It also shows that in the finite case, every idempotent in the image of a homomorphism has an idempotent preimage. -/

/- lemma pow_succ_eq {x : S} (n : ℕ+) (h_idem : IsIdempotentElem x) : x ^ n = x := by
  induction n using PNat.recOn with
  | one    => rfl
  | succ n' ih => rw [← PNat.pow_succ, ih, h_idem]
-/

lemma hom_powers {S T}[Semigroup S][Semigroup T](n : ℕ+)(h : S →ₙ* T)( s : S): h (s^n) = (h s)^n := by
  induction n using PNat.recOn with
  | one => rfl
  | succ n' ih =>  rw [<-PNat.pow_succ,map_mul h,<-PNat.pow_succ,ih]



lemma idempotent_hom_preserved {S}{T}[Semigroup S][Semigroup T](h : S →ₙ* T) (e : S)(id : IsIdempotentElem e) : IsIdempotentElem (h e) := by
  unfold IsIdempotentElem at *
  rw [<-map_mul h,id ]

lemma idempotent_iso_preserved {S}{T}[Semigroup S][Semigroup T](h : S ≃* T) (e : S): IsIdempotentElem e ↔ IsIdempotentElem (h e) := by
  constructor
  · intro id
    exact @idempotent_hom_preserved S T _ _ h e id
  · intro hid
    have k : IsIdempotentElem ((inviso h) (h e)) :=
    @idempotent_hom_preserved T S _ _ (inviso h) (h e) hid
    have k₂ : inviso h (h e) = e := by exact (MulEquiv.eq_symm_apply (inviso h)).mp rfl
    rw [k₂] at k
    exact k

/- For finite `S`: If `h : S →ₙ* T` and `e ∈ T` is an idempotent in the image of `h`, then `h⁻¹(e)` contains an idempotent.-/

lemma idempotent_preimage {S}{T}[Semigroup S][Semigroup T][Finite S](h : S →ₙ* T) (e : T) (id : IsIdempotentElem e)(inimage : ∃ g : S, h g = e) : ∃ f : S, (IsIdempotentElem f) ∧ (h f = e) := by
  cases' inimage with g hge
  have idpower : ∃ k : ℕ+, (IsIdempotentElem (g^k)) := Semigroup.exists_idempotent_pow g
  cases' idpower with k gkid
  use (g^k)
  constructor
  · exact gkid
  · calc
      h (g ^ k) = (h g)^k := hom_powers k h g
      _ = e^k := by rw [hge]
      _ = e := Semigroup.pow_succ_eq k id
