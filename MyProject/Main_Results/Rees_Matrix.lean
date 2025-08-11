import MyProject.Main_Results.Location

def ReesMatrix (I : Type) (G : Type) (J : Type) := Option (I × G × J)

namespace ReesMatrix

variable {G : Type } {I : Type } {J : Type } (P : J → I → Option G) [Nonempty I] [Nonempty J]
  [Group G] [BEq G]

instance ReesMul : Mul (ReesMatrix I G J) where
  mul a b :=
    match a, b with
    | some (i1, g1, j1), some (i2, g2, j2) =>
        match P j1 i2 with
        | some pval => some (i1, g1 * pval * g2, j2)
        | none => none
    | _, _ => none

def rees_mul (a b : ReesMatrix I G J) : ReesMatrix I G J :=
  match a, b with
  | some (i1, g1, j1), some (i2, g2, j2) =>
      match P j1 i2 with
      | some pval => some (i1, g1 * pval * g2, j2)
      | none => none
  | _, _ => none


instance {P : J → I → Option G} : MulZeroClass (ReesMatrix I G J) where
  zero := none
  mul := rees_mul P
  zero_mul := by
    intro x
    cases x with
    | none => rfl
    | some _ => rfl
  mul_zero := by
    intro x
    cases x with
    | none => rfl
    | some _ => rfl


instance (P : J → I → Option G) : Semigroup (ReesMatrix I G J) where
  mul := rees_mul P
  mul_assoc := by
    intros a b c
    cases a with
    | none => rfl
    | some aval =>
      cases b with
      | none => rfl
      | some bval =>
        cases c with
        | none =>
          let h1 := rees_mul P (some aval) (some bval)
          have h2 : rees_mul P h1 none = none := by simp
          exact h2
        | some cval =>
          rcases aval with ⟨i₁, g₁, j₁⟩
          rcases bval with ⟨i₂, g₂, j₂⟩
          rcases cval with ⟨i₃, g₃, j₃⟩
          let mid₁ := P j₁ i₂
          let mid₂ := P j₂ i₃
          cases mid₁ with
          | none =>
            cases mid₂ with
            | none => sorry
            | some => sorry
          | some val₁ =>
            cases mid₂ with
            | none => sorry
            | some val₂ =>
              let left := rees_mul P (some (i₁, g₁ * val₁ * g₂, j₂)) (some (i₃, g₃, j₃))
              simp only [rees_mul] at left
              let right := rees_mul P (some (i₁, g₁, j₁)) (some (i₂, g₂ * val₂ * g₃, j₃))
              simp only [rees_mul] at right
              sorry
end ReesMatrix
