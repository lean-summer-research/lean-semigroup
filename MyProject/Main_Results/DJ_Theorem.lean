import MyProject.GreensRelations.Opposite

/-! # DJ Theorem

This file proves that, in finite semigroups, the following properties hold:
  1. `D_iff_J_finite` - The 𝓙 and 𝓓 relations are equivalent
  2. `R_eqv_of_J_mul_right` - If `s 𝓙 s * x`, then `s 𝓡 s * x`
  3. `L_eqv_of_J_mul_left` If `s 𝓙 x * s`, then `s 𝓛 x * s`
  4. `R_eqv_of_R_preorder_and_J` - If `s 𝓙 t` and `s ≤𝓡 t`, then `s 𝓡 t`
  5. `L_eqv_of_L_preorder_and_J` - If `s 𝓙 t` and `s ≤𝓛 t`, then `s 𝓛 t`
  6. `H_eqv_of_eq` -  If `s = u * s * v` for some `u v ∈ S¹`, then `s 𝓗 u * s 𝓗 s * v`

## Implementation Notes

This file is a good example of some of the Duality lemmas
-/

/-! ### The D-J Theorem for Finite Semigroups -/

section D_J

variable {S} [Semigroup S] {a b : S}

/-- Every 𝓓-related pair is 𝓙-related. -/
lemma D_eqv_if : a 𝓓 b → a 𝓙 b := by
  simp [D_eqv_iff, J_eqv_iff]
  rintro x ⟨⟨c, hc⟩, ⟨d, hd⟩⟩ ⟨⟨f, hf⟩, ⟨g, hg⟩⟩
  constructor
  · use f, c; rw [← hf, ← hc]
  · use g, d; rw [mul_assoc, ← hd, hg]

/-- In finite semigroups, Green's 𝓓-relation equals the 𝓙-relation. The forward direction
always holds, but finiteness is needed for the reverse implication. -/
theorem D_eqv_iff_J_finite [Finite S] : a 𝓓 b ↔ a 𝓙 b := by
  constructor
  · apply D_eqv_if
  · intro hJ
    have hJ_copy := hJ; obtain ⟨⟨x, y, ha⟩, ⟨u, v, hb⟩⟩ := hJ_copy
    have hab : ↑a = x * u * a * (v * y) := by
      rw [hb, ← mul_assoc, ← mul_assoc, mul_assoc _ v y] at ha
      exact ha
    obtain ⟨k, l, hene, hfne, heq1, heq2⟩ := Monoid.exists_pow_sandwich_eq_self hab
    cases v with
    | one =>
      use a; rw [one_mul, mul_one] at *; simp [L_eqv_iff]
      constructor
      · use (x * u)^(k-1) * x
        have hk : k - 1 + 1 = k := by exact Nat.succ_pred_eq_of_ne_zero hene
        rw [hb, ← mul_assoc, mul_assoc _ x u, ← pow_succ, hk, heq1]
      · use u
    | coe v =>
      use a * v
      simp [R_eqv_iff, L_eqv_iff]
      constructor
      · use y * (v * y) ^ (l - 1)
        rw [WithOne.coe_mul, ← mul_assoc, mul_assoc ↑a ↑v y, mul_assoc,  ← pow_succ']
        have hl : l - 1 + 1 = l := by exact Nat.succ_pred_eq_of_ne_zero hfne
        rw [hl, heq2]
      · constructor
        · use (x * u)^(k-1) * x; rw [hb]
          conv => rhs; rw [← mul_assoc, ← mul_assoc, mul_assoc _ x u]
          have hk : k - 1 + 1 = k := by exact Nat.succ_pred_eq_of_ne_zero hene
          rw [WithOne.coe_mul, ← pow_succ, hk, heq1]
        · use u; simp [hb, mul_assoc]

end D_J

/-! ### Properties relating J, L, and R (Proposition 1.4.2 and 1.4.4)
This section shows how 𝓙-equivalence "strengthens"
𝓡 and 𝓛 preorders to equivalences in finite semigroups. -/

section J_R_L_Props

open MulOpposite

variable {S} [Semigroup S] [Finite S] {a b : S}

/-- In finite semigroups, if `a` is 𝓙-related to `a * b`, then `a` is 𝓡-related to `a * b`. -/
lemma R_eqv_of_J_mul_right (hj : a 𝓙 a * b) : a 𝓡 a * b := by
  obtain ⟨⟨x, y, hxy⟩, _⟩ := hj
  rw [WithOne.coe_mul, ← mul_assoc, mul_assoc] at hxy
  simp [R_eqv_iff]
  obtain ⟨_, n, _, hneq, _, ha ⟩ := Monoid.exists_pow_sandwich_eq_self hxy
  use y * (↑b * y) ^ (n - 1)
  simp_rw [WithOne.coe_mul, ← mul_assoc, mul_assoc ↑a ↑b y]
  rw [mul_assoc ↑a (↑b * y), ← pow_succ']
  have hl : n - 1 + 1 = n := by exact Nat.succ_pred_eq_of_ne_zero hneq
  rw [hl, ha]

-- Dual version of above
/-- In finite semigroups, if `a` is 𝓙-related to `b * a`, then `a` is 𝓛-related to `b * a`. -/
lemma L_eqv_of_J_mul_left (hj : a 𝓙 b * a) : a 𝓛 b * a := by
  rw [J_eqv_iff_op, L_eqv_iff_op, op_mul] at *
  apply R_eqv_of_J_mul_right hj

/-- In finite semigroups, if `a` is 𝓡-below `b` and `a 𝓙 b`, then `a 𝓡 b`. -/
theorem R_eqv_of_R_preorder_and_J (hr : a ≤𝓡 b) (hj: a 𝓙 b) : a 𝓡 b := by
  rw [R_preorder_iff_without_one] at hr
  cases hr with
  | inl heq => subst heq; simp
  | inr ha =>
    obtain ⟨u, hru⟩ := ha; subst hru;
    rw [J_eqv_symm, R_eqv_symm] at *
    apply R_eqv_of_J_mul_right; assumption

-- Dual version of above
/-- In finite semigroups, if `a` is 𝓛-below `b` and `a 𝓙 b`, then `a 𝓛 b`. -/
theorem L_eqv_of_L_preorder_and_J (hl : a ≤𝓛 b) (hj: a 𝓙 b) : a 𝓛 b := by
  rw [L_preorder_iff_op, J_eqv_iff_op, L_eqv_iff_op] at *
  apply R_eqv_of_R_preorder_and_J hl hj

end J_R_L_Props

/-! ### Properties of the 𝓗 relation -/

section H_Props

variable {S} [Semigroup S] [Finite S] {a u v : S}

theorem H_eqv_of_eq_right (h : a = u * a * v ) : a 𝓗 a * v ∧ a 𝓗 u * a:= by
  have hJ : a 𝓙 a * v := by
    simp [J_eqv_iff, J_preorder_iff]; constructor
    · use ↑u, 1; simp_rw [mul_one, ← WithOne.coe_mul, WithOne.coe_inj, ← mul_assoc]; exact h
    · use 1, ↑v; simp
  have hJ₂ : a 𝓙 u * a := by
    simp [J_eqv_iff, J_preorder_iff]; constructor
    · use 1, ↑v; simp_rw [one_mul, ← WithOne.coe_mul, WithOne.coe_inj]; exact h
    · use u, 1; simp
  have hR : a 𝓡 a * v := R_eqv_of_J_mul_right hJ
  have hL : a 𝓛 u * a := L_eqv_of_J_mul_left hJ₂
  have hR₂ : a 𝓡 u * a := by
    apply R_eqv_of_R_preorder_and_J
    · use v; rw [← WithOne.coe_mul, WithOne.coe_inj]; exact h
    · exact hJ₂
  have hL₂ : a 𝓛 a * v := by
    apply L_eqv_of_L_preorder_and_J
    · use u; rw [← WithOne.coe_mul u (a * v), WithOne.coe_inj, ← mul_assoc]; exact h
    · exact hJ
  simp [H_eqv_iff_L_and_R, hR, hL, hR₂, hL₂]

end H_Props
