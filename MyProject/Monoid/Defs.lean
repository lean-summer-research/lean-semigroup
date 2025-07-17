import Mathlib

/-!
# Green's Relations Definitions
This file defines Greens Preorders and Equivalences.
We also prove basic properties and `simp` lemmas.
For all Equivalences and preroders, we provide `iff` style duality lemmas.
We define Equivalence classes with the notation `⟦x⟧𝓩`

## Main Definitions
Greens Preorders (infix notation): `≤𝓡`, `≤𝓛`, `≤𝓙`, `≤𝓗`
Greens Relations (infix notation): `𝓡`, `𝓛`, `𝓙`, `𝓗`, `𝓓`
Equivalence classes: `⟦x⟧𝓛`, `⟦x⟧𝓡`, `⟦x⟧𝓙`, `⟦x⟧𝓗`, `⟦x⟧𝓓`

## Main Statments
TODO

## Notation
Greens Preorders (infix notation): `≤𝓡`, `≤𝓛`, `≤𝓙`, `≤𝓗`
Greens Relations (infix notation): `𝓡`, `𝓛`, `𝓙`, `𝓗`, `𝓓`
Equivalence classes: `⟦x⟧𝓛`, `⟦x⟧𝓡`, `⟦x⟧𝓙`, `⟦x⟧𝓗`, `⟦x⟧𝓓`
-/

/-!
### Preorders
This section defines preorders `≤𝓡`, `≤𝓛`, `≤𝓙 `, and `≤𝓗`.
We also provide `isPreorder` instances.
-/

section Preorders

variable {M : Type*} [Monoid M] (x y : M)

def RLE : Prop := ∃ z, y * z = x
notation:50 x" ≤𝓡 "y:50 => RLE x y

def LLE : Prop := ∃ z, z * y = x
notation:50 x" ≤𝓛 "y:50 => LLE x y

def JLE : Prop := ∃ u v, u * y * v = x
notation:50 x" ≤𝓙 "y:50 => JLE x y

def HLE : Prop := x ≤𝓡 y ∧ x ≤𝓛 y
notation:50 x" ≤𝓗 "y:50 => HLE x y

@[simp] lemma RLE.refl (x : M) : x ≤𝓡 x := by use 1; simp
@[simp] lemma LLE.refl (x : M) : x ≤𝓛 x := by use 1; simp
@[simp] lemma JLE.refl (x : M) : x ≤𝓙 x := by use 1, 1; simp
@[simp] lemma HLE.refl (x : M) : x ≤𝓗 x := by simp [HLE]

lemma RLE.trans {x y z : M} (h₁ : x ≤𝓡 y) (h₂ : y ≤𝓡 z) : x ≤𝓡 z := by
  rcases h₂ with ⟨u, hu⟩
  rcases h₁ with ⟨v, hv⟩
  use u * v
  simp [hu, hv, ← mul_assoc]

lemma LLE.trans {x y z : M} (h₁ : x ≤𝓛 y) (h₂ : y ≤𝓛 z) : x ≤𝓛 z := by
  rcases h₁ with ⟨u, hu⟩
  rcases h₂ with ⟨v, hv⟩
  use u * v
  simp [hu, hv, mul_assoc]

lemma JLE.trans {x y z : M} (h₁ : x ≤𝓙 y) (h₂ : y ≤𝓙 z) : x ≤𝓙 z := by
  rcases h₁ with ⟨u₁, v₁, h₁⟩
  rcases h₂ with ⟨u₂, v₂, h₂⟩
  use u₁ * u₂, v₂ * v₁
  rw [← mul_assoc, mul_assoc u₁, mul_assoc u₁]
  rw [h₂, h₁]

lemma HLE.trans {x y z : M} (h₁ : x ≤𝓗 y) (h₂ : y ≤𝓗 z) : x ≤𝓗 z := by
  rcases h₁ with ⟨h₁R, h₁L⟩
  rcases h₂ with ⟨h₂R, h₂L⟩
  constructor
  · apply RLE.trans h₁R h₂R
  · apply LLE.trans h₁L h₂L

instance RLE.isPreorder : IsPreorder M RLE where
  refl := RLE.refl
  trans := by intros x y z h₁ h₂; apply RLE.trans h₁ h₂
instance LLE.isPreorder : IsPreorder M LLE where
  refl := LLE.refl
  trans := by intros x y z h₁ h₂; apply LLE.trans h₁ h₂
instance JLE.isPreorder : IsPreorder M JLE where
  refl := JLE.refl
  trans := by intros x y z h₁ h₂; apply JLE.trans h₁ h₂
instance HLE.isPreorder : IsPreorder M HLE where
  refl := HLE.refl
  trans := by intros x y z h₁ h₂; apply HLE.trans h₁ h₂

end Preorders

/-!
### Equivalence relations from preorders
We define a general method for converting preorders into equivalence relations.
-/

section EquivOfLE

variable {α : Type*} (p : α → α → Prop) [hInst : IsPreorder α p]

@[simp] def EquivOfLE (x y : α) : Prop := p x y ∧ p y x

-- Equivalence is the unbundled form of Setoid
instance EquivOfLE.isEquiv : Equivalence (EquivOfLE p) where
  refl := by
    simp
    apply hInst.refl
  symm := by aesop
  trans := by
    simp_all
    rintro x y z h₁ h₂ h₃ h₄
    constructor
    · apply (hInst.trans x y z ) <;> assumption
    · apply (hInst.trans z y x ) <;> assumption

end EquivOfLE

/-! ### Green's Equivalence Relations -/

section Equivalences

variable {M : Type*} [Monoid M]

/-- The equivalence relation `𝓡` -/
def REquiv : M → M → Prop := EquivOfLE RLE
notation:50 x " 𝓡 " y:50 => REquiv x y

/-- The equivalence relation `𝓛` -/
def LEquiv : M → M → Prop := EquivOfLE LLE
notation:50 x " 𝓛 " y:50 => LEquiv x y

/-- The equivalence relation `𝓙` -/
def JEquiv : M → M → Prop := EquivOfLE JLE
notation:50 x " 𝓙 " y:50 => JEquiv x y

/-- The equivalence relation `𝓗` -/
def HEquiv : M → M → Prop := EquivOfLE HLE
notation:50 x " 𝓗 " y:50 => HEquiv x y


/-! Equivalence typeclass instances -/
instance REquiv.isEquiv : Equivalence (fun x y : M => x 𝓡 y) := by
  unfold REquiv
  exact @EquivOfLE.isEquiv M RLE _
instance LEquiv.isEquiv : Equivalence (fun x y : M => x 𝓛 y) := by
  unfold LEquiv
  exact @EquivOfLE.isEquiv M LLE _
instance JEquiv.isEquiv : Equivalence (fun x y : M => x 𝓙 y) := by
  unfold JEquiv
  exact @EquivOfLE.isEquiv M JLE _
instance HEquiv.isEquiv : Equivalence (fun x y : M => x 𝓗 y) := by
  unfold HEquiv
  exact @EquivOfLE.isEquiv M HLE _

/-! reflexivity proofs for Green's Equivalences-/

variable (x : M)

@[simp] theorem REquiv.refl : x 𝓡 x := by
  have hEquiv := @REquiv.isEquiv M _
  apply hEquiv.refl
@[simp] theorem LEquiv.refl: x 𝓛 x := by
  have hEquiv := @LEquiv.isEquiv M _
  apply hEquiv.refl
@[simp] theorem JEquiv.refl : x 𝓙 x := by
  have hEquiv := @JEquiv.isEquiv M _
  apply hEquiv.refl
@[simp] theorem HEquiv.refl : x 𝓗 x := by
  have hEquiv := @HEquiv.isEquiv M _
  apply hEquiv.refl

/-! transivitity proofs for Green's Equivalences-/

variable {x y z : M}

theorem REquiv.trans (h₁ : x 𝓡 y) (h₂ : y 𝓡 z) : x 𝓡 z := by
  have hEquiv := @REquiv.isEquiv M _
  apply hEquiv.trans h₁ h₂
theorem LEquiv.trans (h₁ : x 𝓛 y) (h₂ : y 𝓛 z) : x 𝓛 z := by
  have hEquiv := @LEquiv.isEquiv M _
  apply hEquiv.trans h₁ h₂
theorem JEquiv.trans (h₁ : x 𝓙 y) (h₂ : y 𝓙 z) : x 𝓙 z := by
  have hEquiv := @JEquiv.isEquiv M _
  apply hEquiv.trans h₁ h₂
theorem HEquiv.trans (h₁ : x 𝓗 y) (h₂ : y 𝓗 z) : x 𝓗 z := by
  have hEquiv := @HEquiv.isEquiv M _
  apply hEquiv.trans h₁ h₂

/-! Symmetry proofs for Greens Equivalences -/

-- The `symm` attribute lets the `symm` tactic reverse goals by these lemmas
@[simp, symm] theorem REquiv.symm (h : x 𝓡 y) : y 𝓡 x := by
  have hEquiv := @REquiv.isEquiv M _
  apply (@hEquiv.symm) h
@[simp, symm] theorem LEquiv.symm (h : x 𝓛 y) : y 𝓛 x := by
  have hEquiv := @LEquiv.isEquiv M _
  apply (@hEquiv.symm) h
@[simp, symm] theorem JEquiv.symm (h : x 𝓙 y) : y 𝓙 x := by
  have hEquiv := @JEquiv.isEquiv M _
  apply (@hEquiv.symm) h
@[simp, symm] theorem HEquiv.symm (h : x 𝓗 y) : y 𝓗 x := by
  have hEquiv := @HEquiv.isEquiv M _
  apply (@hEquiv.symm) h

end Equivalences

/-! ### Basic lemmas -/

section Basic

variable {M : Type*} [Monoid M] {x y z u v : M}

/-- We connect out definition based on `≤𝓗` to one based on `𝓡 ∧ 𝓛` -/
theorem HEquiv.rEquiv_and_lEquiv_iff : x 𝓡 y ∧ x 𝓛 y ↔ x 𝓗 y := by
  simp [HEquiv, REquiv, LEquiv, HLE]
  aesop

/-- `x * y` is always `≤𝓡 x` -/
@[simp] lemma RLE.mul_right_self (x y : M) : x * y ≤𝓡 x := by use y

/-- `y * x` is always `≤𝓛 x` -/
@[simp] lemma LLE.mul_left_self : y * x ≤𝓛 x := by use y

/-- `u * x * v` is always `≤𝓙 x` -/
@[simp] lemma JLE.mul_sandwich_self : u * x * v ≤𝓙 x := by use u, v

lemma JLE.left_cancel {x y z : M} (h : x ≤𝓙 y * z) : x ≤𝓙 z := by
  obtain ⟨u, v, huv⟩ := h
  use u * y, v
  simp_all [← mul_assoc]

lemma JLE.right_cancel {x y z : M} (h : x ≤𝓙 y * z) : x ≤𝓙 y := by
  obtain ⟨u, v, huv⟩ := h
  use u , z * v
  simp_all [← mul_assoc]

lemma RLE.right_cancel {x y z : M} (h : x ≤𝓡 y * z) : x ≤𝓡 y := by
  rcases h with ⟨u, hu⟩
  use z * u
  simp_all [← mul_assoc]

lemma LLE.left_cancel {x y z : M} (h : x ≤𝓛 y * z) : x ≤𝓛 z := by
  rcases h with ⟨u, hu⟩
  use u * y
  simp_all [← mul_assoc]

/-! Idempotent properties -/

lemma RLE.idempotent_iff (x e : M) (h : IsIdempotentElem e) : x ≤𝓡 e ↔ e * x = x := by
  constructor
  · rintro ⟨u, hu⟩
    rw [← hu, ← mul_assoc, h]
  · intro h
    use x

lemma LLE.idempotent_iff (x e : M) (h : IsIdempotentElem e) : x ≤𝓛 e ↔ x * e = x := by
  constructor
  · rintro ⟨u, hu⟩
    rw [← hu, mul_assoc, h]
  · intro h
    use x

/-! Definitional lemmas for the simplifier -/

@[simp] lemma REquiv.of_le (h₁ : x ≤𝓡 y) (h₂ : y ≤𝓡 x) : x 𝓡 y := by simp_all [REquiv]
@[simp] lemma LEquiv.of_le (h₁ : x ≤𝓛 y) (h₂ : y ≤𝓛 x) : x 𝓛 y := by simp_all [LEquiv]
@[simp] lemma JEquiv.of_le (h₁ : x ≤𝓙 y) (h₂ : y ≤𝓙 x) : x 𝓙 y := by simp_all [JEquiv]
@[simp] lemma HEquiv.of_le (h₁ : x ≤𝓗 y) (h₂ : y ≤𝓗 x) : x 𝓗 y := by simp_all [HEquiv]

@[simp] theorem HEquiv.of_rEquiv_and_lEquiv {x y : M} (h₁ : x 𝓡 y) (h₂ : x 𝓛 y) : x 𝓗 y := by
  simp_all [← HEquiv.rEquiv_and_lEquiv_iff, h₁, h₂]

/-! `to` lemmas -/

@[simp] theorem RLE.to_jLE (h : x ≤𝓡 y) : x ≤𝓙 y := by
  simp_all [RLE, JLE]
  obtain ⟨x, hx⟩ := h
  use 1, x
  simp_all

@[simp] theorem LLE.to_jLE (h : x ≤𝓛 y) : x ≤𝓙 y := by
  simp_all [RLE, JLE]
  obtain ⟨x, hx⟩ := h
  use x, 1
  simp_all

@[simp] theorem REquiv.le (hR : x 𝓡 y) : x ≤𝓡 y := by simp_all [REquiv]
@[simp] theorem LEquiv.le (hL : x 𝓛 y) : x ≤𝓛 y := by simp_all [LEquiv]
@[simp] theorem JEquiv.le (hJ : x 𝓙 y) : x ≤𝓙 y := by simp_all [JEquiv]
@[simp] theorem HEquiv.le (hH : x 𝓗 y) : x ≤𝓗 y := by simp_all [HEquiv]

@[simp] theorem REquiv.ge (hR : x 𝓡 y) : y ≤𝓡 x := by simp_all [REquiv]
@[simp] theorem LEquiv.ge (hL : x 𝓛 y) : y ≤𝓛 x := by simp_all [LEquiv]
@[simp] theorem JEquiv.ge (hJ : x 𝓙 y) : y ≤𝓙 x := by simp_all [JEquiv]
@[simp] theorem HEquiv.ge (hH : x 𝓗 y) : y ≤𝓗 x := by simp_all [HEquiv]

@[simp] theorem REquiv.to_jEquiv (h : x 𝓡 y) : x 𝓙 y := by simp_all [REquiv, JEquiv]
@[simp] theorem LEquiv.to_jEquiv (h : x 𝓛 y) : x 𝓙 y := by simp_all [LEquiv, JEquiv]

@[simp] lemma HEquiv.to_rEquiv {x y : M} (h : x 𝓗 y) : x 𝓡 y := by
  simp_all [← HEquiv.rEquiv_and_lEquiv_iff]

@[simp] lemma HEquiv.to_lEquiv {x y : M} (h : x 𝓗 y) : x 𝓛 y := by
  simp_all [← HEquiv.rEquiv_and_lEquiv_iff]

end Basic

/-! ### Duality -/

section Duality

open MulOpposite

variable {M : Type*} [Monoid M] (x y z u v : M)

instance MulOppositeFinite [hF : Finite M] : Finite (Mᵐᵒᵖ) := Finite.of_equiv M opEquiv

/-! Multiplication Duality -/

@[simp] theorem mul_eq_op_iff : op x * op y = op z ↔ y * x = z := by simp [← op_mul]

-- Same lemmas as above, but for `z = x * y` instead of `x * y = z`
@[simp] theorem op_eq_mul_iff : op x = op y * op z ↔ x = z * y := by simp [← op_mul]

@[simp] theorem mul_mul_eq_op_iff : op x * op y * op z = op u ↔ z * y * x = u := by
  simp [← op_mul, ← mul_assoc]

@[simp] theorem op_eq_mul_mul_iff : op x = op y * op z * op u ↔ x = u * z * y := by
  simp [← op_mul, ← mul_assoc]

/-! Preorder Duality -/
@[simp] lemma RLE.op_iff : op x ≤𝓛 op y ↔ x ≤𝓡 y := by simp [LLE, RLE]
@[simp] lemma  LLE.op_iff : op x ≤𝓡 op y ↔ x ≤𝓛 y := by simp [RLE, LLE]
@[simp] lemma JLE.op_iff : op x ≤𝓙 op y ↔ x ≤𝓙 y := by simp [JLE]; aesop
@[simp] lemma HLE.op_iff : op x ≤𝓗 op y ↔ x ≤𝓗 y := by simp [HLE, and_comm, RLE.op_iff, LLE.op_iff]

/-! Equivalence Duality -/
@[simp] theorem REquiv.op_iff : op x 𝓛 op y ↔ x 𝓡 y := by simp [LEquiv, REquiv, RLE.op_iff]
@[simp] theorem LEquiv.op_iff : op x 𝓡 op y ↔ x 𝓛 y := by simp [REquiv, LEquiv, LLE.op_iff]
@[simp] theorem JEquiv.op_iff : op x 𝓙 op y ↔ x 𝓙 y := by simp [JEquiv]
@[simp] theorem HEquiv.op_iff : op x 𝓗 op y ↔ x 𝓗 y := by simp [HEquiv]

-- Note, DEquiv.op_iff is proven later

/-- Idempotent duality -/
theorem idempotent_op_iff (e : M) : IsIdempotentElem (op e) ↔ IsIdempotentElem e := by
  unfold IsIdempotentElem
  rw [mul_eq_op_iff]

end Duality

/-!
### Statements about 𝓡 and 𝓛
We prove that 𝓡 and 𝓛 are compatable with left/right multiplication, respectivly.
We also prove that 𝓡 and 𝓛 commute under composition, and this is also true of their preorders.
These lemmas are essential for proving that 𝓓 is an equivalence.
-/

section REquivLEquiv

open MulOpposite

variable {M : Type*} [Monoid M] {x y z : M}

/-- `≤𝓡` is compatable with left multiplication -/
@[simp] lemma RLE.mul_left_compat (z : M) (h : x ≤𝓡 y) : z * x ≤𝓡 z * y := by
  obtain ⟨u, hu⟩ := h
  use u
  simp [mul_assoc, hu]

/-- `≤𝓛` is compatable with right multiplication -/
@[simp] lemma LLE.mul_right_compat (z : M) (h : x ≤𝓛 y) : x * z ≤𝓛 y * z := by
  obtain ⟨u, hu⟩ := h
  use u
  simp [← mul_assoc, hu]

/-- `𝓡` is compatable with left multiplication -/
@[simp] lemma REquiv.mul_left_compat (z : M) (h : x 𝓡 y) : z * x 𝓡 z * y := by simp_all [REquiv]

/-- `𝓛` is compatable with right multiplication -/
@[simp] lemma LEquiv.mul_right_compat (z : M) (h : x 𝓛 y) : x * z 𝓛 y * z := by simp_all [LEquiv]

-- Note: is this the same as the J relation?
lemma rLE_lLE_of_comm (hL : x ≤𝓛 z) (hR : z ≤𝓡 y) : ∃ u, x ≤𝓡 u ∧ u ≤𝓛 y := by
  rcases _ : hL with ⟨v, hv⟩
  rcases _ : hR with ⟨w, hw⟩
  use v * y
  simp [← hv, hR]

-- Dual to above
lemma lLE_rLE_of_comm (hR : x ≤𝓡 z) (hL : z ≤𝓛 y) : ∃ u, x ≤𝓛 u ∧ u ≤𝓡 y := by
  rcases _ : hL with ⟨v, hv⟩
  rcases _ : hR with ⟨w, hw⟩
  use y * w
  simp [← hw, hL]

theorem rLE_lLE_comm (x y : M) : (∃ z, x ≤𝓛 z ∧ z ≤𝓡 y) ↔ ∃ z, x ≤𝓡 z ∧ z ≤𝓛 y := by
  constructor
  · rintro ⟨u, hL, hR⟩
    apply rLE_lLE_of_comm hL hR
  · rintro ⟨u, hL, hR⟩
    apply lLE_rLE_of_comm hL hR

lemma rEquiv_lEquiv_of_comm (hL : x 𝓛 z) (hR : z 𝓡 y) : ∃ u, x 𝓡 u ∧ u 𝓛 y := by
  rcases _ : hL with ⟨hL₁, hL₂⟩ -- the `_ : hL` syntax preserves the original hL
  rcases _ : hR with ⟨hR₁, hR₂⟩
  obtain ⟨t, ht⟩ := hL₁
  use t * y
  subst x
  constructor
  · simp [hR] -- proof `t * z 𝓡 t * y`
  · simp [LEquiv] --  proof `t * y 𝓛 y`
    obtain ⟨w, hw⟩ := hR₂
    rw [← hw, ← mul_assoc]
    simp [hL₂]

-- Dual of above
lemma lEquiv_rEquiv_of_comm (hR : x 𝓡 z) (hL : z 𝓛 y) : ∃ u, x 𝓛 u ∧ u 𝓡 y := by
  rw [← REquiv.op_iff] at hR
  rw [← LEquiv.op_iff] at hL
  obtain ⟨u, hu⟩ := rEquiv_lEquiv_of_comm hR hL
  use unop u
  have hEq : u = op (unop u) := by simp
  rw [hEq, LEquiv.op_iff, REquiv.op_iff] at hu
  exact hu

/-- **Green's Commutativity**: R and L relations commute under composition -/
theorem rEquiv_lEquiv_comm: (∃ z, x 𝓛 z ∧ z 𝓡 y) ↔ ∃ z, x 𝓡 z ∧ z 𝓛 y := by
  constructor
  · rintro ⟨z, hL, hR⟩
    apply rEquiv_lEquiv_of_comm hL hR
  · rintro ⟨z, hL, hR⟩
    apply lEquiv_rEquiv_of_comm hL hR

end REquivLEquiv

/-! ### 𝓓 Relation -/

section DEquiv

variable {M : Type*} [Monoid M]

def DEquiv (x y : M) : Prop := ∃ z, x 𝓡 z ∧ z 𝓛 y
notation:50 x " 𝓓 " y:50 => DEquiv x y

/-- Alternate Def of `𝓓`, equivalent by 𝓡-𝓛 communitivity -/
theorem DEquiv.comm {x y : M} : (∃ z, x 𝓛 z ∧ z 𝓡 y) ↔ x 𝓓 y := by
  simp [DEquiv, rEquiv_lEquiv_comm]

open MulOpposite in
/-- Duality statment for 𝓓 -/
@[simp] lemma DEquiv.op_iff {x y : M} : op x 𝓓 op y ↔ x 𝓓 y := by
  simp [DEquiv]
  rw [rEquiv_lEquiv_comm]

@[simp] lemma DEquiv.refl (x : M) : x 𝓓 x := by use x; simp_all

variable {x y z : M}

@[symm] lemma DEquiv.symm (h : x 𝓓 y) : y 𝓓 x := by
  simp_all [DEquiv]
  rw [← rEquiv_lEquiv_comm]
  obtain ⟨z, ⟨hR, hL⟩⟩ := h
  use z
  exact ⟨hL.symm, hR.symm⟩

/-- The 𝓓-relation is preserved by 𝓛-equivalent elements on the right.
If `a 𝓓 b` and `b 𝓛 c`, then `a 𝓓 c`. -/
lemma DEquiv.closed_under_lEquiv (hD : x 𝓓 y) (hL : y 𝓛 z) : x 𝓓 z := by
  simp_all [DEquiv]
  obtain ⟨u, ⟨hR, hL₂⟩⟩ := hD
  use u
  simp_all
  apply LEquiv.trans hL₂ hL

-- Dual to above
lemma DEquiv.closed_under_rEquiv (hD : x 𝓓 y) (hR : y 𝓡 z) : x 𝓓 z := by
  rw [← DEquiv.op_iff] at hD ⊢
  rw [← REquiv.op_iff] at hR
  apply DEquiv.closed_under_lEquiv hD hR

/-- The 𝓓-relation is transitive. This is proved using closure under 𝓡 and 𝓛. -/
lemma DEquiv.trans (h₁ : x 𝓓 y) (h₂ : y 𝓓 z) : x 𝓓 z := by
  obtain ⟨u, ⟨hy1, hy2⟩⟩ := h₂
  have hd1 : x 𝓓 u := DEquiv.closed_under_rEquiv h₁ hy1
  apply DEquiv.closed_under_lEquiv hd1 hy2

/-- The 𝓓-relation is an equivalence relation on `M`. -/
instance DEquiv.isEquiv: Equivalence (fun a b : M => a 𝓓 b) where
  refl := DEquiv.refl
  symm := DEquiv.symm
  trans := DEquiv.trans

/-- `to` style lemmas -/
@[simp] lemma REquiv.to_dEquiv (h : x 𝓡 y) : x 𝓓 y := by use y; simp_all
@[simp] lemma LEquiv.to_dEquiv (h : x 𝓛 y) : x 𝓓 y := by use x; simp_all

end DEquiv

/-! ### Equivalence classes as Sets -/

section EquivalenceClasses

variable {M : Type*} [Monoid M] (x : M)

@[simp] def REquiv.set : Set M := {y | y 𝓡 x}
@[simp] def LEquiv.set : Set M := {y | y 𝓛 x}
@[simp] def JEquiv.set : Set M := {y | y 𝓙 x}
@[simp] def HEquiv.set : Set M := {y | y 𝓗 x}
@[simp] def DEquiv.set : Set M := {y | y 𝓓 x}

notation "⟦" x "⟧𝓡" => REquiv.set x
notation "⟦" x "⟧𝓛" => LEquiv.set x
notation "⟦" x "⟧𝓙" => JEquiv.set x
notation "⟦" x "⟧𝓗" => HEquiv.set x
notation "⟦" x "⟧𝓓" => DEquiv.set x

/-! Equivalence Classes Duality -/

open MulOpposite

variable {x y : M}

@[simp] theorem REquiv.op_mem_set_iff : op x ∈ ⟦op y⟧𝓛 ↔ x ∈ ⟦y⟧𝓡 := by simp
@[simp] theorem LEquiv.op_mem_set_iff : op x ∈ ⟦op y⟧𝓡 ↔ x ∈ ⟦y⟧𝓛 := by simp
@[simp] theorem JEquiv.op_mem_set_iff : op x ∈ ⟦op y⟧𝓙 ↔ x ∈ ⟦y⟧𝓙 := by simp
@[simp] theorem HEquiv.op_mem_set_iff : op x ∈ ⟦op y⟧𝓗 ↔ x ∈ ⟦y⟧𝓗 := by simp
@[simp] theorem DEquiv.op_mem_set_iff : op x ∈ ⟦op y⟧𝓓 ↔ x ∈ ⟦y⟧𝓓 := by simp

end EquivalenceClasses
