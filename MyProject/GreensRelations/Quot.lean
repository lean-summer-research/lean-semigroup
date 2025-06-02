import MyProject.GreensRelations.Defs

/-!
# Green's Relations Quotient Types

This file constructs quotient types for Green's equivalence classes using Lean's `Quot`
constructor.

## Main definitions

* `R_class`, `L_class`, `J_class`, `H_class` `D_class`
- quotient types for Green's equivalence classes
* `get_R_class`, `get_L_class`, `get_J_class`, `get_H_class`, `get_D_class`
- functions mapping elements to their equivalence classes

## Main statements

* `R_class_iff`, `L_class_iff`, `J_class_iff`, `H_class_iff` `D_class_iff`
- quotient equality characterizations

## Notations

* `⟦a⟧𝓡`, `⟦a⟧𝓛`, `⟦a⟧𝓙`, `⟦a⟧𝓗`, `⟦a⟧𝓓` - equivalence class notation for elements

## Implementation notes

Unlike `Quotient r`, `Quot r` does not require a `Setoid` structure on the binary relation `r`.
Instead, it applies `Relation.EqvGen` to `r` to generate the minimal equivalence relation containing `r`.
Since Green's relations are already equivalence relations, this generation process is the identity.

This file serves as the foundation for `Decidable.lean`, which adds computational instances,
and provides the quotient structure needed for finite enumeration of equivalence classes.
-/

/-! ### Quotient type definitions

We define the quotient types for each of Green's relations using Lean's `Quot` constructor.
-/

section QuotientTypes

def R_class (S) [Semigroup S] := Quot (fun a b : S => a 𝓡 b)
def L_class (S) [Semigroup S] := Quot (fun a b : S => a 𝓛 b)
def J_class (S) [Semigroup S] := Quot (fun a b : S => a 𝓙 b)
def H_class (S) [Semigroup S] := Quot (fun a b : S => a 𝓗 b)
def D_class (S) [Semigroup S] := Quot (fun a b : S => a 𝓓 b)

end QuotientTypes

variable {S} [Semigroup S]

/-! ### Equivalence class accessor functions -/

section AccessorFunctions

def get_R_class (a : S) : R_class S := Quot.mk R_eqv a
def get_L_class (a : S) : L_class S := Quot.mk L_eqv a
def get_J_class (a : S) : J_class S := Quot.mk J_eqv a
def get_H_class (a : S) : H_class S := Quot.mk H_eqv a
def get_D_class (a : S) : D_class S := Quot.mk D_eqv a

/-! Notation for equivalence classes of elements in `S` -/
notation:50 "⟦"x"⟧𝓡" => get_R_class x
notation:50 "⟦"x"⟧𝓛" => get_L_class x
notation:50 "⟦"x"⟧𝓙" => get_J_class x
notation:50 "⟦"x"⟧𝓗" => get_H_class x
notation:50 "⟦"x"⟧𝓓" => get_D_class x

end AccessorFunctions

/-! ### Quotient characterizations -/

section QuotientCharacterizations

@[simp] lemma R_EqvGen_eq (a b : S): Relation.EqvGen R_eqv a b ↔ a 𝓡 b :=
  Equivalence.eqvGen_iff (eqv_of_preorder_inst R_preorder)
@[simp] lemma L_EqvGen_eq (a b : S): Relation.EqvGen L_eqv a b ↔ a 𝓛 b :=
  Equivalence.eqvGen_iff (eqv_of_preorder_inst L_preorder)
@[simp] lemma J_EqvGen_eq (a b : S): Relation.EqvGen J_eqv a b ↔ a 𝓙 b :=
  Equivalence.eqvGen_iff (eqv_of_preorder_inst J_preorder)
@[simp] lemma H_EqvGen_eq (a b : S): Relation.EqvGen H_eqv a b ↔ a 𝓗 b :=
  Equivalence.eqvGen_iff (eqv_of_preorder_inst H_preorder)
@[simp] lemma D_EqvGen_eq (a b : S): Relation.EqvGen D_eqv a b ↔ a 𝓓 b := by
  apply Equivalence.eqvGen_iff (D_eqv_inst)


/-! Definitional lemmas for equivalence classes -/
lemma R_class_iff (a b : S) : (⟦a⟧𝓡 : R_class S) = (⟦b⟧𝓡 : R_class S) ↔ a 𝓡 b := by
  unfold get_R_class
  rw [Quot.eq]; simp --simp finds R_EqvGen_eq
lemma L_class_iff (a b : S) : (⟦a⟧𝓛 : L_class S) = (⟦b⟧𝓛 : L_class S) ↔ a 𝓛 b := by
  unfold get_L_class
  rw [Quot.eq]; simp
lemma J_class_iff (a b : S) : (⟦a⟧𝓙 : J_class S) = (⟦b⟧𝓙 : J_class S) ↔ a 𝓙 b := by
  unfold get_J_class
  rw [Quot.eq]; simp
lemma H_class_iff (a b : S) : (⟦a⟧𝓗 : H_class S) = (⟦b⟧𝓗 : H_class S) ↔ a 𝓗 b := by
  unfold get_H_class
  rw [Quot.eq]; simp
lemma D_class_iff (a b : S) : (⟦a⟧𝓓 : D_class S) = (⟦b⟧𝓓 : D_class S) ↔ a 𝓓 b := by
  unfold get_D_class
  rw [Quot.eq]; simp

end QuotientCharacterizations
