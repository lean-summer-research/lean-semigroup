import Mathlib

/-!
# Style Guidelines

This file is an assembly of the most relevant content in these documents:
- Lean Community website: https://leanprover-community.github.io/index.html
- Library Style Guidlines: https://leanprover-community.github.io/contribute/style.html

## Summary

- Code structure and formatting guidelines for definitions, theorems, and proofs
- Proper use of anonymous functions and tactic blocks
- Whitespace conventions and use of delimiters
- Use of operators like `<|` and `|>` to improve readability
- A discussion of Normal Forms

## TODO

- Implement a Normal Form for greens Relations (dont write theorems in terms of set membership)

### Line Length

- Lines should not be longer than 100 characters.

### Structuring definitions and theorems

- All declarations (e.g., def, lemma, theorem, class, structure, inductive, instance, etc.)
and commands (e.g., variable, open, section, namespace, notation, etc.) are considered
top-level and these words should appear flush-left in the document. In particular, opening
a namespace or section does not result in indenting the contents of that namespace or section.
(Note: within VS Code, hovering over any declaration such as def Foo ... will show the
fully qualified name, like MyNamespace Foo if Foo is declared while the namespace MyNamespace
is open.)

- Use spaces on both sides of ":", ":=" or infix operators. Put them
before a line break rather than at the beginning of the next line.

- After stating the theorem, we indent the lines in the subsequent proof by 2 spaces. -/

open Nat

theorem nat_case {P : Nat → Prop} (n : Nat) (H1 : P 0) (H2 : ∀ m, P (succ m)) : P n :=
  Nat.recOn n H1 (fun m _ ↦ H2 m)

/-! If the theorem statement requires multiple lines, indent the subsequent lines by 4 spaces.
The proof is still indented only 2 spaces (not 6 = 4 + 2). When providing a proof in tactic
mode, the by is placed on the line prior to the first tactic; however, by should not be placed
on a line by itself. In practice this means you will often see := by at the end of a theorem
statement. -/

theorem le_induction {P : Nat → Prop} {m}
    (h0 : P m) (h1 : ∀ n, m ≤ n → P n → P (n + 1)) :
    ∀ n, m ≤ n → P n := by
  apply Nat.le.rec
  · exact h0
  · exact h1 _

/-! When a proof term takes multiple arguments, it is sometimes clearer, and often necessary,
to put some of the arguments on subsequent lines. In that case, indent each argument.
This rule, i.e., indent an additional two spaces, applies more generally whenever
a term spans multiple lines. -/

axiom zero_or_succ (n : Nat) : n = zero ∨ n = succ (pred n)

theorem nat_discriminate {B : Prop} {n : Nat} (H1: n = 0 → B) (H2 : ∀ m, n = succ m → B) : B :=
  Or.elim (zero_or_succ n)
    (fun H3 : n = zero ↦ H1 H3)
    (fun H3 : n = succ (pred n) ↦ H2 (pred n) H3)

/-! A short declaration can be written on a single line: -/

theorem succ_pos : ∀ n : Nat, 0 < succ n := zero_lt_succ

def square (x : Nat) : Nat := x * x

/-!
- A have can be put on a single line when the justification is short.

```c
example (n k : Nat) (h : n < k) : ... :=
  have h1 : n ≠ k := ne_of_lt h
```

-  When the justification is too long, you should put it on the next line,
indented by an additional two spaces.

```c
example (n k : Nat) (h : n < k) : ... :=
  have h1 : n ≠ k := by
    apply ne_of_lt
```
-/
/-! When the arguments themselves are long enough to require line breaks, use an additional
indent for every line after the first, as in the following example: -/

theorem Nat.add_right_inj' {n m k : Nat} : n + m = n + k → m = k :=
  Nat.recOn n
    (fun H : 0 + m = 0 + k ↦ calc
      m = 0 + m := Eq.symm (zero_add m)
      _ = 0 + k := H
      _ = k     := zero_add _)
    (fun (n : Nat) (IH : n + m = n + k → m = k)
         (H : succ n + m = succ n + k) ↦
      have H2 : succ (n + m) = succ (n + k) := calc
        succ (n + m) = succ n + m := Eq.symm (succ_add n m)
        _ = succ n + k         := H
        _ = succ (n + k)       := succ_add n k
      have H3 : n + m = n + k := succ.inj H2
      IH H3)

/-! In a `class` or `structure` definition, fields are indented 2 spaces, and moreover each
field should have a `docstring`, as in: -/

class Module' (R : Type u) (M : Type v) [Semiring R] [AddCommMonoid M] extends
    DistribMulAction R M where
  /-- Scalar multiplication distributes over addition from the right. -/
  protected add_smul : ∀ (r s : R) (x : M), (r + s) • x = r • x + s • x
  /-- Scalar multiplication by zero gives zero. -/
  protected zero_smul : ∀ x : M, (0 : R) • x = 0

/-! When using a constructor taking several arguments in a definition,
arguments line up, as in: -/

theorem Ordinal.sub_eq_zero_iff_le' {a b : Ordinal} : a - b = 0 ↔ a ≤ b :=
  ⟨fun h => by simpa only [h, add_zero] using le_add_sub a b,
   fun h => by rwa [← Ordinal.le_zero, sub_le, add_zero]⟩

/-! We generally use a blank line to separate `theorems` and `definitions`,
but this can be omitted, for example, to group together a number of short `definitions`,
or to group together a definition and `notation`.

### Instances

- When providing terms of structures or instances of classes, the `where` syntax
should be used to avoid the need for enclosing braces, as in: -/

instance instOrderBot : OrderBot ℕ where
  bot := 0
  bot_le := Nat.zero_le

/-! If there is already an instance instBot, then one can write

```c
instance instOrderBot : OrderBot ℕ where
  __ := instBot
  bot_le := Nat.zero_le
```

### Hypotheses Left of Colon

Generally, having arguments to the left of the colon is preferred over having arguments in
universal quantifiers or implications, if the proof starts by introducing these variables.
For instance:  -/

example (n : ℝ) (h : 1 < n) : 0 < n := by linarith

/-! is preferred over -/

example (n : ℝ) : 1 < n → 0 < n := fun h ↦ by linarith

/-!
### `Anonymous functions`

`Lean` has several nice syntax options for declaring anonymous functions. For very simple
functions, one can use the centered dot as the function argument, as in `(· ^ 2)` to represent
the squaring function. However, sometimes it is necessary to refer to the arguments by name
(e.g., if they appear in multiple places in the function body). The `Lean` default for this is
`fun x => x * x`, but the `↦` arrow (inserted with `\mapsto`) is also valid. In `mathlib` the
pretty printer displays `↦`, and we slightly prefer this in the source as well.

### Tactic Mode

- As we have already mentioned, when opening a tactic block, `by` is placed at the end of the
line preceding the start of the tactic block, but not on its own line. Everything within the
tactic block is indented.

- When new goals arise as side conditions or steps, they are indented and preceded by a focusing
dot `·` (inserted with `\.`); the dot is not indented:

- Certain tactics, such as `refine`, can create named subgoals which can be proven in whichever
order is desired using `case`. This feature is also useful in aiding readability. However, it is
not required to use this instead of the focusing dot `·`. -/

example {p q : Prop} (h₁ : p → q) (h₂ : q → p) : p ↔ q := by
  refine ⟨?imp, ?converse⟩
  case converse => exact h₂
  case imp => exact h₁

/-! Often `t0 <;> t1` is used to execute `t0` and then `t1` on all new goals. Either write the
tactics in one line, or indent the following tactic.

```c
  cases x <;>
    simp [a, b, c, d]
```

- For single line tactic proofs (or short tactic proofs embedded in a term), it is acceptable to use
`by tac1; tac2; tac3` with semicolons instead of a new line with indentation.

- In general, you should put a single tactic invocation per line, unless you are closing a goal with
a proof that fits entirely on a single line. Short sequences of tactics that correspond to a single
mathematical idea can also be put on a single line, separated by semicolons as in
`cases bla; clear h` or `induction n; simp` or `rw [foo]; simp_rw [bar]`, but even in these
scenarios, newlines are preferred.

```c
example : ... := by
  by_cases h : x = 0
  · rw [h]; exact hzero ha
  · rw [h]
    have h' : ... := H ha
    simp_rw [h', hb]
    ...
```
- Very short goals can be closed right away using `swap` or `pick_goal` if needed, to avoid
additional indentation in the rest of the proof.

```c
example : ... := by
  rw [h]
  swap; exact h'
  ...
```

### Squeezing `simp` calls

- Unless performance is particularly poor or the proof breaks otherwise, terminal `simp` calls (a
`simp` call is terminal if it closes the current goal or is only followed by flexible tactics such
as `ring`, `field_simp`, `aesop`) should not be squeezed (replaced by the output of `simp?`).

There are two main reasons for this:

1. A squeezed `simp` call might be several lines longer than the corresponding unsqueezed one,
   and therefore drown the useful information of what key lemmas were added to the unsqueezed
   `simp` call to close the goal in a sea of basic `simp` lemmas.
2. A squeezed `simp` call refers to many lemmas by name, meaning that it will break when one such
   lemma gets renamed. Lemma renamings happen often enough for this to matter on a maintenance level.

- When using the tactics `rw` or `simp` there should be a space after the left arrow `←`.
For instance `rw [← add_comm a b]` or `simp [← and_or_left]`. (There should also be a space
between the tactic name and its arguments, as in `rw [h]`.)

- Empty lines inside declarations are discouraged and there is a linter that enforces that they are
not present. This helps maintaining a uniform code style throughout all of `mathlib`.

### Whitespace and Delimiters

- Lean is whitespace-sensitive, and in general we opt for a style which avoids delimiting code.
For instance, when writing tactics, it is possible to write them as tac1; tac2; tac3,
separated by ;, in order to override the default whitespace sensitivity. However, as mentioned
above, we generally try to avoid this except in a few special cases.

- Similarly, sometimes parentheses can be avoided by judicious use of the <| operator (or its
cousin |>). Note: while $ is a synonym for <|, its use in mathlib is disallowed in favor of
<| for consistency as well as because of the symmetry with |>. These operators have the effect
of parenthesizing everything to the right of <| (note that ( is curved the same direction as <)
or to the left of |> (and ) curves the same way as >).

- A common example of the usage of |> occurs with dot notation when the term preceding the . is a
function applied to some arguments. For instance, ((foo a).bar b).baz can be rewritten as
`foo a |>.bar b |>.baz`

- A common example of the usage of <| is when the user provides a term which is a function applied
to multiple arguments whose last argument is a proof in tactic mode, especially one that spans
multiple lines. In that case, it is natural to use <| by ... instead of (by ...), as in: -/

example {x y : ℝ} (hxy : x ≤ y) (h : ∀ ε > 0, y - ε ≤ x) : x = y :=
  le_antisymm hxy <| le_of_forall_pos_le_add <| by
    intro ε hε
    have := h ε hε
    linarith

/-!
### Normal forms

Some statements are equivalent. For instance, there are several equivalent ways to require that a
subset `s` of a type is nonempty. For another example, given `a : α`, the corresponding element of
`Option α` can be equivalently written as `Some a` or `(a : Option α)`. In general, we try to
settle on one standard form, called the normal form, and use it both in statements and conclusions
of theorems. In the above examples, this would be `s.Nonempty` (which gives access to dot notation)
and `(a : Option α)`. Often, `simp` lemmas will be registered to convert the other equivalent forms
to the normal form.

Iff theorems should be notated such that the more normalized version of the statment is on the right
side of the iff. This allows you to use them with `rw` and `simp` without prepending `←`. This also
is the way that `simp` will try to automatically apply the tactic if you tag it @[simp].
-/
