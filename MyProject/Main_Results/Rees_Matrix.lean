import MyProject.Main_Results.Location

def ReesMatrix {I : Type} {G : Type} {J : Type} (P : J → I → G) := Option (I × G × J)

namespace ReesMatrix

variable {G : Type } {I : Type } {J : Type } (P : J → I → G) [Nonempty I] [Nonempty J]
  [GroupWithZero G] [BEq G]

instance ReesMul : Mul (ReesMatrix P) where
  mul a b :=
    match a, b with
    | some (i1, g1, j1), some (i2, g2, j2) =>
        match P j1 i2 with
        | pval => some (i1, g1 * pval * g2, j2)
    | _, _ => none

def rees_mul (a b : ReesMatrix P) : ReesMatrix P :=
  match a, b with
  | some (i1, g1, j1), some (i2, g2, j2) =>
      match P j1 i2 with
      | pval => some (i1, g1 * pval * g2, j2)
  | _, _ => none


instance {P : J → I → G} : MulZeroClass (ReesMatrix P) where
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


instance (P : J → I → G) : Semigroup (ReesMatrix P) where
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
          have h2 : rees_mul P h1 none = none := by rfl
          exact h2
        | some cval =>
          let aval' : ReesMatrix P := some aval
          let bval' : ReesMatrix P := some bval
          let cval' : ReesMatrix P := some cval
          rcases aval with ⟨i₁, g₁, j₁⟩
          rcases bval with ⟨i₂, g₂, j₂⟩
          rcases cval with ⟨i₃, g₃, j₃⟩
          let mid₁ := P j₁ i₂
          let mid₂ := P j₂ i₃
          have hab : aval' * bval' = some (i₁, g₁ * mid₁ * g₂, j₂) := by
            rfl
          have hbc : bval' * cval' = some (i₂, g₂ * mid₂ * g₃, j₃) := by
            rfl
          have ha_bc : aval' * (bval' * cval') = some (i₁, g₁ * mid₁ * (g₂ * mid₂ * g₃), j₃) := by
            simp_all only [mid₁, mid₂, aval', bval', cval']
            rfl
          have hab_c : aval' * bval' * cval' = some (i₁, (g₁ * mid₁ * g₂) * mid₂ * g₃, j₃) := by
            simp_all only [cval', aval', mid₂, mid₁, bval']
            rfl
          have heq : (g₁ * mid₁ * g₂) * mid₂ * g₃ = g₁ * mid₁ * (g₂ * mid₂ * g₃) := by
            simp[mul_assoc]
          have hfinal : aval' * bval' * cval' = aval' * (bval' * cval') := by
            simp_all only [ha_bc, hab_c, heq]
          unfold aval' bval' cval' at hfinal
          exact hfinal

end ReesMatrix
