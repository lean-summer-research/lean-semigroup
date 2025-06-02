import MyProject.GreensRelations.Decidable

/-!
# Basic Properties of Green's Relations

This file establishes basic properties of Green's relations.

## Main statements

* `D_iff_J_finite` - **D-J Theorem**: in finite semigroups, 𝓓 = 𝓙

## Implementation notes

-/

/-! ## The D-J Theorem for Finite Semigroups -/

variable {S} [Semigroup S] (a b : S)
/-- Every D-related pair is J-related -/
lemma D_eqv_if : a 𝓓 b → a 𝓙 b := by
  simp [D_eqv, rel_comp, J_eqv_iff]
  rintro x ⟨⟨c, hc⟩, ⟨d, hd⟩⟩ ⟨⟨f, hf⟩, ⟨g, hg⟩⟩
  constructor
  · use f, c; rw [← hf, ← hc]
  · use g, d; rw [mul_assoc, ← hd, hg]

/-- **D-J Theorem**: In finite semigroups, Green's D-relation equals the J-relation -/
theorem D_iff_J_finite [Finite S] : a 𝓓 b ↔ a 𝓙 b := by
  constructor
  · apply D_eqv_if
  · rintro ⟨⟨x, y, ha⟩, ⟨u, v, hb⟩⟩
    have loop : ∀ n : ℕ, (x * u)^n * ↑a * (v * y)^n = a := by
      intros n; induction n with
      | zero => simp
      | succ n ih =>
        conv => lhs; lhs; rw [pow_succ, mul_assoc]
        conv => lhs; rhs; rw [pow_succ']
        have rw_assoc : (x * u)^ n * (x * u * ↑a) * (v * y * (v * y)^ n) =
            (x*u)^ n * (x * (u * a * v) * y) * (v*y)^n := by simp [mul_assoc]
        rw [rw_assoc, ← hb, ← ha, ih]
    have ⟨k, ⟨he, hene⟩⟩ := Monoid.exists_idempotent_pow (x * u)
    have ⟨l, ⟨hf, hfne⟩⟩ := Monoid.exists_idempotent_pow (v * y : S¹)
    have heq1 : (x * u)^ k * a = a := by rw [← (loop k), ← mul_assoc, ← mul_assoc, he]
    have heq2 : a * (v * y)^ l = a := by rw [← (loop l), mul_assoc, hf]
    cases v with
    | one =>
      use a; constructor
      · apply eqv_of_preorder_refl
      · rw [L_eqv_iff]; constructor
        · rw [one_mul, mul_one] at *; use (x * u)^(k-1) * x
          have hk : k - 1 + 1 = k := by exact Nat.succ_pred_eq_of_ne_zero hene
          rw [hb, ← mul_assoc, mul_assoc _ x u, ← pow_succ, hk, heq1]
        · use u; rw [hb, mul_one]
    | coe v =>
      use a * v
      constructor
      · constructor
        · use y * (v * y)^ (l - 1)
          rw [WithOne.coe_mul, ← mul_assoc, mul_assoc ↑a ↑v y, mul_assoc,  ← pow_succ' ]
          have hl : l - 1 + 1 = l := by exact Nat.succ_pred_eq_of_ne_zero hfne
          rw [hl, heq2]
        · use v; simp
      · constructor
        · use (x * u)^(k-1) * x; rw [hb]
          conv => rhs; rw [← mul_assoc, ← mul_assoc, mul_assoc _ x u]
          have hk : k - 1 + 1 = k := by exact Nat.succ_pred_eq_of_ne_zero hene
          rw [WithOne.coe_mul, ← pow_succ, hk, heq1]
        · use u; simp [hb, mul_assoc]
