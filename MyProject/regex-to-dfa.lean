import Mathlib

universe u v

open Finset Computability List

/-- A constructive ε‐NFA using Finset σ instead of Set σ. -/
structure εNFA' (α : Type u) (σ : Type v) where
  step   : σ → Option α → Finset σ
  start  : Finset σ
  accept : Finset σ

namespace εNFA'

variable {α : Type u} {σ : Type v} [DecidableEq σ]

instance : Inhabited (εNFA' α σ) := ⟨εNFA'.mk (fun _ _ => ∅) ∅ ∅⟩

/-- The εClosure of a set is the set of states which can be reached by taking a finite string of
ε-transitions from an element of the set. -/
@[simp] def εClosure (M : εNFA' α σ) [Fintype σ] : Finset σ → Finset σ
| S =>
  let S' := S ∪ S.biUnion (fun s => M.step s none)
  if S' = S then S else εClosure M S'
termination_by S => Fintype.card σ - S.card
decreasing_by
  have h_ssub : S ⊂ S' :=
    Finset.ssubset_iff_subset_ne.mpr ⟨subset_union_left, by simp_all only [union_eq_left,
      biUnion_subset_iff_forall_subset, not_forall, Classical.not_imp, ne_eq, left_eq_union, S', S]⟩
  have h_card_lt : S.card < S'.card := Finset.card_lt_card h_ssub
  have h_le : S'.card ≤ Fintype.card σ := Finset.card_le_univ _
  simp_all only [union_eq_left, biUnion_subset_iff_forall_subset, not_forall, Classical.not_imp,
    gt_iff_lt, S', S]; omega

@[simp] theorem εClosure_empty (M : εNFA' α σ) [Fintype σ] : M.εClosure ∅ = ∅ := by
  simp only [εClosure, biUnion_empty, union_idempotent, ↓reduceIte]

@[simp] theorem εClosure_univ (M : εNFA' α σ) [Fintype σ]
 : M.εClosure (univ : Finset σ) = univ := by
  simp only [εClosure, union_eq_left, subset_univ, ↓reduceIte]

/-- One symbol step: take all a‐transitions then ε‐close each target. -/
def stepSet (M : εNFA' α σ) [Fintype σ] (S : Finset σ) (a : α) : Finset σ :=
  (S.biUnion fun s => M.step s (some a)).biUnion fun s => M.εClosure {s}

@[simp] theorem stepSet_empty (M : εNFA' α σ) [Fintype σ] (a : α)
 : M.stepSet ∅ a = ∅ := by dsimp only [stepSet, biUnion_empty]

/-- x ∈ stepSet M S a iff there is t ∈ S and u ∈ M.step t (some a)
with x ∈ εClosure M {u}. -/
theorem mem_stepSet (M : εNFA' α σ) [Fintype σ] {x : σ} {S : Finset σ} {a : α} :
    x ∈ M.stepSet S a ↔ ∃ t ∈ S, ∃ u ∈ M.step t (some a), x ∈ M.εClosure {u} := by
  dsimp only [stepSet]
  constructor
  · intro h
    rcases Finset.mem_biUnion.1 h with ⟨u, hu_in, hx_in⟩
    rcases Finset.mem_biUnion.1 hu_in with ⟨t, htS, hu_step⟩
    exact ⟨t, htS, u, hu_step, hx_in⟩
  · rintro ⟨t, htS, u, hu_step, hx_in⟩
    have hu : u ∈ S.biUnion fun s => M.step s (some a) :=
      Finset.mem_biUnion.2 ⟨t, htS, hu_step⟩
    exact Finset.mem_biUnion.2 ⟨u, hu, hx_in⟩

/-- Evaluate from an arbitrary set of start states. -/
def evalFrom (M : εNFA' α σ) [Fintype σ]  (start : Finset σ) : List α → Finset σ :=
  List.foldl (fun S a => M.stepSet S a) (M.εClosure start)

@[simp] theorem evalFrom_nil (M : εNFA' α σ) [Fintype σ] (start : Finset σ) :
  M.evalFrom start [] = M.εClosure start := rfl

@[simp] theorem evalFrom_singleton (M : εNFA' α σ) [Fintype σ] (start : Finset σ) (a : α)
 : M.evalFrom start [a] = M.stepSet (M.εClosure start) a := rfl

@[simp]
theorem evalFrom_append_singleton (M : εNFA' α σ) [Fintype σ] (start : Finset σ) (xs : List α)
 (a : α) : M.evalFrom start (xs ++ [a]) = M.stepSet (M.evalFrom start xs) a := by
 simp only [evalFrom, foldl_append, foldl_cons, foldl_nil]

/-- Evaluate on input x starting from M.start. -/
def eval (M : εNFA' α σ) [Fintype σ] (x : List α) : Finset σ := M.evalFrom M.start x

@[simp] theorem eval_nil (M : εNFA' α σ) [Fintype σ] : M.eval [] = M.εClosure M.start := rfl

@[simp] theorem eval_singleton (M : εNFA' α σ) [Fintype σ] (a : α)
 : M.eval [a] = M.stepSet (M.εClosure M.start) a := rfl

@[simp] theorem eval_append_singleton (M : εNFA' α σ) [Fintype σ] (xs : List α) (a : α) :
    M.eval (xs ++ [a]) = M.stepSet (M.eval xs) a := by simp only [eval, evalFrom_append_singleton]

/-- The language accepted by the ε‐NFA: some accept‐state is reached. -/
def accepts (M : εNFA' α σ) [Fintype σ] : Language α := { x | ∃ t ∈ M.accept, t ∈ M.eval x }

theorem mem_accepts (M : εNFA' α σ) [Fintype σ] {x : List α} :
 x ∈ M.accepts ↔ ∃ t ∈ M.accept, t ∈ M.eval x := Iff.rfl

end εNFA'

/-- A NFA with Finset σ states. -/
structure NFA' (α : Type u) (σ : Type v) where
  step   : σ → α → Finset σ
  start  : Finset σ
  accept : Finset σ

namespace NFA'

variable {α : Type u} {σ : Type v}  [DecidableEq σ] (M : NFA' α σ)

instance : Inhabited (NFA' α σ) := ⟨NFA'.mk (fun _ _ => ∅) ∅ ∅⟩

/-- One‐symbol step: from each state in S follow an a‐transition. -/
def stepSet (S : Finset σ) (a : α) : Finset σ := S.biUnion fun s => M.step s a

@[simp] theorem stepSet_empty (a : α) : M.stepSet ∅ a = ∅ := by dsimp only [stepSet, biUnion_empty]

/-- s ∈ stepSet M S a iff there is some t ∈ S with s ∈ M.step t a. -/
theorem mem_stepSet (M : NFA' α σ) {s : σ} {S : Finset σ} {a : α}
 : s ∈ M.stepSet S a ↔ ∃ t ∈ S, s ∈ M.step t a := by dsimp only [stepSet]; exact Finset.mem_biUnion

/-- Evaluate the NFA from an arbitrary set of start states. -/
def evalFrom (S : Finset σ) : List α → Finset σ := foldl M.stepSet S

@[simp] theorem evalFrom_nil (S : Finset σ) : M.evalFrom S [] = S := rfl

@[simp] theorem evalFrom_singleton (M : NFA' α σ) (start : Finset σ) (a : α)
 : M.evalFrom start [a] = M.stepSet start a := rfl

@[simp] theorem evalFrom_append_singleton (M : NFA' α σ) [Fintype σ] (start : Finset σ)
 (xs : List α) (a : α) : M.evalFrom start (xs ++ [a]) = M.stepSet (M.evalFrom start xs) a := by
 simp only [evalFrom, foldl_append, foldl_cons, foldl_nil]

/-- Evaluate on input x from the designated start. -/
def eval (M : NFA' α σ) (x : List α) : Finset σ := M.evalFrom M.start x

@[simp] theorem eval_nil (M : NFA' α σ) : M.eval [] = M.start := rfl

@[simp] theorem eval_singleton (M : NFA' α σ) (a : α) : M.eval [a] = M.stepSet M.start a := by
  dsimp only [eval, evalFrom_singleton]

@[simp] theorem eval_append_singleton (M : NFA' α σ) [Fintype σ] (xs : List α) (a : α)
 : M.eval (xs ++ [a]) = M.stepSet (M.eval xs) a := by
  simp only [eval, evalFrom, foldl_append, foldl_cons, foldl_nil]

/-- The language accepted by the NFA: some accept‐state is reached. -/
def accepts (M : NFA' α σ) : Language α := { x | ∃ t ∈ M.accept, t ∈ M.eval x }

@[simp] theorem mem_accepts (M : NFA' α σ) {x : List α}
 : x ∈ M.accepts ↔ ∃ t ∈ M.accept, t ∈ M.eval x := Iff.rfl

end NFA'

structure DFA' (α : Type u) (σ : Type v) where
  step : σ → α → σ
  start : σ
  accept : Finset σ


namespace DFA'

variable {α : Type u} {σ : Type v} (M : DFA' α σ)

instance [Inhabited σ] : Inhabited (DFA' α σ) := ⟨DFA'.mk (fun _ _ => default) default ∅⟩

/-- M.evalFrom s x evaluates M with input x starting from the state s. -/
def evalFrom (s : σ) : List α → σ := List.foldl M.step s

@[simp] theorem evalFrom_nil (s : σ) : M.evalFrom s [] = s := rfl

@[simp] theorem evalFrom_singleton (s : σ) (a : α) : M.evalFrom s [a] = M.step s a := rfl

@[simp] theorem evalFrom_append_singleton (s : σ) (x : List α) (a : α)
 : M.evalFrom s (x ++ [a]) = M.step (M.evalFrom s x) a := by
  simp only [evalFrom, List.foldl_append, List.foldl_cons, List.foldl_nil]

/-- M.eval x evaluates M with input x starting from the state M.start. -/
def eval : List α → σ := M.evalFrom M.start

@[simp] theorem eval_nil : M.eval [] = M.start := rfl

@[simp] theorem eval_singleton (a : α) : M.eval [a] = M.step M.start a := rfl

@[simp] theorem eval_append_singleton (x : List α) (a : α)
 : M.eval (x ++ [a]) = M.step (M.eval x) a := evalFrom_append_singleton _ _ _ _

theorem evalFrom_of_append (start : σ) (x y : List α)
 : M.evalFrom start (x ++ y) = M.evalFrom (M.evalFrom start x) y := List.foldl_append

/-- M.acceptsFrom s is the language of x such that M.evalFrom s x is an accept state. -/
def acceptsFrom (s : σ) : Language α := {x | M.evalFrom s x ∈ M.accept}

theorem mem_acceptsFrom {s : σ} {x : List α}
 : x ∈ M.acceptsFrom s ↔ M.evalFrom s x ∈ M.accept := by rfl

/-- M.accepts is the language of x such that M.eval x is an accept state. -/
def accepts : Language α := M.acceptsFrom M.start

theorem mem_accepts {x : List α} : x ∈ M.accepts ↔ M.eval x ∈ M.accept := by rfl

/-- M.rmatch x is true iff the DFA M accepts x. -/
@[simp]
def rmatch (M : DFA' α σ) (x : List α) [DecidableEq σ]: Bool :=
  if M.eval x ∈ M.accept then true else false

/-- rmatch_iff_accepts connects the boolean test to the Language definition. -/
theorem rmatch_iff_accepts [DecidableEq σ] {M : DFA' α σ} {x : List α}
 : M.rmatch x = true ↔ x ∈ M.accepts := by
  simp only [rmatch, Bool.if_false_right, Bool.and_true, decide_eq_true_eq]; rfl

end DFA'

/-! ### Conversions -/

namespace εNFA'  -- εNFA' → NFA

variable {α : Type u} {σ : Type v} (M : εNFA' α σ) [DecidableEq σ] [Fintype σ]

/-- M.toNFA is an NFA constructed from an εNFA M. -/
def toNFA' : NFA' α σ where
  step := fun s a => M.εClosure (M.step s (some a))
  start := M.εClosure M.start
  accept := M.accept

/-- The core fact: doing one stepSet in the subset‑NFA coincides
   with your original M.stepSet. -/
@[simp]
theorem stepSet_eq (S : Finset σ) (a : α) :
    M.toNFA'.stepSet S a = M.stepSet S a := by

  -- Unfold both definitions of stepSet
  dsimp [toNFA', εNFA'.stepSet, NFA'.stepSet]
  -- Reassociate the two biUnions using the built‑in lemma
  rw [Finset.biUnion_biUnion]
  /- Goal : ⊢ (S.biUnion fun s => M.εClosure (M.step s (some a))) =
  S.biUnion fun a_1 => (M.step a_1 (some a)).biUnion fun s => M.εClosure {s}-/

  sorry

/--
For every input list xs, running the NFA built from M starting
in M.εClosure M.start equals running the original ε‑NFA from M.start.
-/
@[simp]
theorem toNFA'_evalFrom (xs : List α) :
    M.toNFA'.evalFrom M.toNFA'.start xs = M.evalFrom M.start xs := by
  induction xs with
  | nil =>
    -- foldl _ _ [] = _ definitionally
    rfl
  | cons a xs ih =>
    -- Peel off one step of the fold on both sides
    dsimp only [NFA'.evalFrom, evalFrom, List.foldl_cons]
    sorry
    -- Now the goal is


/-- The languages accepted by M and by M.toNFA' coincide. -/
@[simp]
theorem toNFA'_correct :
    M.toNFA'.accepts = M.accepts := by
  simp only [εNFA'.accepts, NFA'.accepts, NFA'.eval, toNFA'_evalFrom]
  rfl

end εNFA'



namespace NFA' -- NFA' → DFA'

variable {α : Type u} {σ : Type v} (M : NFA' α σ) [DecidableEq σ] [Fintype σ]

/-- M.toDFA is a DFA constructed from an NFA M using the subset construction. The
  states is the type of Sets of M.state and the step function is M.stepSet. -/
def toDFA' : DFA' α (Finset σ) where
  step := M.stepSet
  start := M.start
  accept := { S | ∃ s ∈ S, s ∈ M.accept }

theorem toDFA'_eval_mem (xs : List α) :
    M.toDFA'.evalFrom M.toDFA'.start xs ∈ M.toDFA'.accept
  ↔ ∃ t ∈ M.accept, t ∈ M.eval xs := by
  dsimp [toDFA', DFA'.step, DFA'.acceptsFrom, NFA'.accepts, DFA'.eval]
  simp only [Finset.mem_filter, Finset.mem_univ, exists_prop, exists_and_left]
  simp_all only [true_and]
  apply Iff.intro
  · intro a
    obtain ⟨w, h⟩ := a
    obtain ⟨left, right⟩ := h
    apply Exists.intro
    · apply And.intro
      on_goal 2 => {exact left}
      · simp_all only
  · intro a
    obtain ⟨w, h⟩ := a
    obtain ⟨left, right⟩ := h
    apply Exists.intro
    · apply And.intro
      · exact right
      · exact left


@[simp]
theorem toDFA'_correct : M.toDFA'.accepts = M.accepts := by
  ext xs
  simp only [mem_accepts, DFA'.accepts, DFA'.acceptsFrom]
  rw [Set.mem_setOf]
  apply toDFA'_eval_mem

end NFA'


namespace RegularExpression -- This section implements Regex → εNFA' → NFA' → DFA'

open Computability Set Fin

variable {α : Type u} {σ : Type v}

@[simp]
def εNFA_size : RegularExpression α → ℕ
  | 0 => 2
  | 1 => 2
  | char _ => 2
  | P + Q => εNFA_size P + Q.εNFA_size + 2
  | P * Q => P.εNFA_size + Q.εNFA_size
  | star P => P.εNFA_size + 2

lemma εNFA_size_ge_two (reg : RegularExpression α) : 2 ≤ reg.εNFA_size := by
  induction reg <;> simp; omega

def toεNFA [DecidableEq α] (reg : RegularExpression α) : εNFA' α (Fin (reg.εNFA_size)) :=
  match h_reg : reg with
  | 0 =>  /-   (0)       (1)  -/
    let start : Fin (εNFA_size 0) := Fin.mk 0 (by simp only [εNFA_size, Nat.ofNat_pos])
    let accept : Fin (εNFA_size 0) := Fin.mk 1 (by simp only [εNFA_size, Nat.one_lt_ofNat])
    let step (_ : Fin (εNFA_size 0)) (_ : Option α) : Finset (Fin (εNFA_size 0)) := {}
    ⟨step, {start}, {accept}⟩
  | 1 =>  /- (0)    none →   (1)  -/
      let start : Fin (εNFA_size 1) := Fin.mk 0 (by simp only [εNFA_size, Nat.ofNat_pos])
      let accept : Fin (εNFA_size 1) := Fin.mk 1 (by simp only [εNFA_size, Nat.one_lt_ofNat])
      let step (n : Fin (εNFA_size 1)) (a? : Option α) : Finset (Fin (εNFA_size 1)) :=
        if n = start then match a? with
          | none => {accept}
          | some _ => {}
        else {}
      ⟨step, {start}, {accept}⟩
  | char b =>  /- (0)     b →    (1)  -/
      let start : Fin (char b).εNFA_size := Fin.mk 0 (by simp only [εNFA_size, Nat.ofNat_pos])
      let accept : Fin (char b).εNFA_size := Fin.mk 1 (by simp only [εNFA_size, Nat.one_lt_ofNat])
      let step (n : Fin (char b).εNFA_size) (a? : Option α) : Finset (Fin (char b).εNFA_size) :=
        if n = start then match a? with
          | none => {}
          | some a => if a=b then {accept} else {}
        else {}
      ⟨step, {start}, {accept}⟩
  | P + Q =>  /-     none →     { (1) ...  (last of P) }       none →
                (0)                                                     (accept_state)
                     none →  { (first of Q) ... (last of Q) }  none →      -/
    let P_nfa : εNFA' α (Fin P.εNFA_size) := P.toεNFA
    let Q_nfa : εNFA' α (Fin Q.εNFA_size) := Q.toεNFA
    have h_size : (P + Q).εNFA_size = P.εNFA_size + Q.εNFA_size + 2 := by
      simp only [εNFA_size, Nat.add_left_inj]
    let start : Fin (P + Q).εNFA_size := ⟨0, by simp only [εNFA_size, lt_add_iff_pos_left,
      add_pos_iff, Nat.ofNat_pos, or_true]⟩
    let acceptState : Fin (P + Q).εNFA_size := ⟨P.εNFA_size + Q.εNFA_size + 1, by omega⟩
    let mapP (s : Fin P.εNFA_size) : Fin (P + Q).εNFA_size := ⟨s.val + 1, by omega⟩
    let mapQ (s : Fin Q.εNFA_size) : Fin (P + Q).εNFA_size := ⟨s.val + P.εNFA_size + 1, by omega⟩

    let step (n : Fin (P + Q).εNFA_size) (a? : Option α) : Finset (Fin (P + Q).εNFA_size) :=
      (if h₁ : 1 ≤ n.val ∧ n.val < 1 + P.εNFA_size then -- Base transitions within P and Q
         let n_p : Fin P.εNFA_size := ⟨n.val - 1, by omega⟩
         Finset.image mapP (P_nfa.step n_p a?)
       else {})
      ∪
      (if h₂ : 1 + P.εNFA_size ≤ n.val ∧ n.val < 1 + P.εNFA_size + Q.εNFA_size then
         let n_q : Fin Q.εNFA_size := ⟨n.val - (1 + P.εNFA_size), by omega⟩
         Finset.image mapQ (Q_nfa.step n_q a?)
       else {})
      ∪ -- Union with Epsilon transitions
      (if a? = none then
         (if n = start then Finset.image mapP P_nfa.start ∪ Finset.image mapQ Q_nfa.start else {}) -- From new start state
         ∪
         (if h₁ : 1 ≤ n.val ∧ n.val < 1 + P.εNFA_size then   -- From P's accept states to new accept state
           let n_p : Fin P.εNFA_size := ⟨n.val - 1, by omega⟩
           if n_p.val = P.εNFA_size - 1 then {acceptState} else {}
          else {})
         ∪
         (if h₂ : 1 + P.εNFA_size ≤ n.val ∧ n.val < 1 + P.εNFA_size + Q.εNFA_size then -- From Q's accept states to new accept state
            let n_q : Fin Q.εNFA_size := ⟨n.val - (1 + P.εNFA_size), by omega⟩
            if n_q = (Q.εNFA_size + P.εNFA_size) then {acceptState} else {}
          else {})
       else {})
    ⟨step, {start}, {acceptState}⟩
  | P * Q =>  /- (first of P)  ... (last of P) none→ (first of Q) ... (last of Q)
                   (start)                                              (accept) -/
    let P_nfa : εNFA' α (Fin P.εNFA_size) := P.toεNFA
    let Q_nfa : εNFA' α (Fin Q.εNFA_size) := Q.toεNFA
    have h_size : (P * Q).εNFA_size = P.εNFA_size + Q.εNFA_size := by
      simp only [εNFA_size, Nat.add_left_inj]
    have P_le_PQ : P.εNFA_size < (P * Q).εNFA_size := by let h := εNFA_size_ge_two Q; omega;
    have Q_le_PQ : Q.εNFA_size < (P * Q).εNFA_size := by let h := εNFA_size_ge_two P; omega;
    let mapP (s : Fin P.εNFA_size) : Fin (P * Q).εNFA_size := ⟨s.val, by omega⟩
    let mapQ (s : Fin Q.εNFA_size) : Fin (P * Q).εNFA_size := ⟨s.val + P.εNFA_size, by omega⟩
    let step (n : Fin (P * Q).εNFA_size) (a? : Option α) : Finset (Fin (P * Q).εNFA_size) :=
      (if h₁ : n < P.εNFA_size then -- Base transitions
         let n_p : Fin P.εNFA_size := ⟨n.val, h₁⟩
         Finset.image mapP (P_nfa.step n_p a?)
       else if h₂ : P.εNFA_size - 1 < n then
         let n_q : Fin Q.εNFA_size := ⟨n.val - (P.εNFA_size + 1), by omega⟩
         Finset.image mapQ (Q_nfa.step n_q a?)
        else {})
      ∪ -- Union with Epsilon transitions
      (if a? = none then -- From P's accept state to Q's start state
         if h₁ : n = P.εNFA_size - 1 then {⟨↑n + 1, by omega⟩} else {}
       else {})
    ⟨step, {⟨0, by omega⟩}, {⟨P.εNFA_size + Q.εNFA_size - 1, by omega⟩}⟩
  | star P => /-           <--------- none
                          none →    { (First of P) ... (Last of P) }    none →
                       (0)                                                  (accept)
                            none ------------------------------------------->     -/
    let P_nfa : εNFA' α (Fin P.εNFA_size) := P.toεNFA
    have h_size : P.star.εNFA_size = P.εNFA_size + 2 := by simp only [εNFA_size, Nat.add_left_inj]
    have P_le_PQ : P.εNFA_size < P.star.εNFA_size := by let h := εNFA_size_ge_two P; omega;
    let mapP (s : Fin P.εNFA_size) : Fin P.star.εNFA_size := ⟨s.val + 1, by omega⟩
    let step (n : Fin P.star.εNFA_size) (a? : Option α) : Finset (Fin P.star.εNFA_size) :=
      (if h₁ : 1 ≤ n.val ∧ n.val < 1 + P.εNFA_size then -- Base transitions within P
         let n_p : Fin P.εNFA_size := ⟨n.val - 1, by omega⟩
         Finset.image mapP (P_nfa.step n_p a?)
       else {})
      ∪ -- Union with Epsilon transitions
      (if a? = none then
         (if ↑n = 0 then {⟨P.εNFA_size + 1, by omega⟩, ⟨1, by omega⟩} -- From new start state
         else if h₁ : ↑n = P.εNFA_size then {⟨P.εNFA_size + 1, by simp⟩, ⟨1, by simp⟩} else {} )
       else {})
    ⟨step, {⟨0, by simp⟩}, {⟨P.εNFA_size + 1, by simp⟩}⟩

-- TODO, add a correctness proof for the regex → εNFA
-- TODO, implement regex → DFA and correctness lemma (using functions defined earlier) and
-- connect the regex decidable predicate to the one we defined for DFAs
end RegularExpression



-- TODO, add example eval comands that demonstrats the equivilant representations of the language as a regex, enfa, nfa, and dfa.

-- Example usage:

def MyState := Fin 3
instance : DecidableEq (Fin 3) := inferInstance
instance : Fintype (Fin 3) := Fin.fintype 3

inductive MyInput | x | y deriving DecidableEq, Repr

def myEnfa : εNFA' MyInput (Fin 3) where
  step s oi := match s.val, oi with
    | 0, none            => {1}
    | 1, some MyInput.x  => {2}
    | _, _               => ∅
  start  := {0}
  accept := {2}

def myNfa : NFA' MyInput (Fin 3) := myEnfa.toNFA'
/-9 of 19
invalid field 'to_NFA'', the environment does not contain 'εNFA'.to_NFA''
  myEnfa
has type
  εNFA' MyInput (Fin 3)Lean -/

-- now fully #eval‑able:
#eval εNFA'.εClosure myEnfa {0}           -- => {0, 1}
#eval εNFA'.εClosure myEnfa {1}           -- => {1}
#eval myEnfa.step 1 MyInput.x
#eval myNfa.step 0 MyInput.x               -- => ∅
#eval myNfa.step 1 MyInput.x               -- => {2}
#eval myNfa.start                          -- => {0, 1}


instance {n} [Repr (Fin n)] : Repr (Finset (Fin n)) where  -- TODO: determine if this Is this necessary?
  reprPrec s prec :=
    -- 1. List all possible Fin n in canonical order
    let xs : List (Fin n) := List.finRange n
    -- 2. Keep only those actually in the finset
    let fs := xs.filter (· ∈ s)
    -- 3. Build a reversed list of formats
    let fmtsRev := fs.foldl (fun acc a => reprPrec a prec :: acc) []
    -- 4. Reverse to recover original order
    let fmts := fmtsRev.reverse
    -- 5. Join with commas and line‑breaks
    Std.Format.bracket "{" (Std.Format.joinSep fmts ("," ++ Std.Format.line)) "}"
