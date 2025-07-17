import MyProject.Monoid.Local

/-!
# Style Guidelines

This file is an assembly of the most relevant content in these documents:
- Lean Community website: https://leanprover-community.github.io/index.html
- Library Style Guidlines: https://leanprover-community.github.io/contribute/style.html

I also inserted some examples from our codebase.
-/

namespace Example

/-!
### Line Length
Lines must not be longer than 100 characters.

### Structuring definitions and theorems
All declarations (e.g., def, lemma, theorem, class, structure, inductive, instance, etc.)
and commands (e.g., variable, open, section, namespace, notation, etc.) are considered
top-level and these words should appear flush-left in the document.

Use spaces on both sides of ":", ":=" or infix operators. Put them
before a line break rather than at the beginning of the next line.

When providing a proof in tactic mode, the by is placed on the line prior to the first tactic;
however, by should not be placed on a line by itself. In practice this means you will often
see `:= by` at the end of a theorem statement.

After stating the theorem, we indent the lines in the subsequent proof by 2 spaces.
If the theorem statement requires multiple lines, indent the subsequent lines by 4 spaces.
The proof is still indented only 2 spaces (not 6 = 4 + 2).

Examples of **Good Structure** : -/

@[simp]
lemma RLE.mul_left_compat {M : Type*} [Monoid M]
    {x y : M} (z : M) (h : x ≤𝓡 y) :
    z * x ≤𝓡 z * y := by
  obtain ⟨u, hu⟩ := h
  use u
  simp [mul_assoc, hu]

@[simp] lemma RLE.mul_left_compat' {M : Type*} [Monoid M]
    {x y : M} (z : M) (h : x ≤𝓡 y) : z * x ≤𝓡 z * y := by
  obtain ⟨u, hu⟩ := h
  use u
  simp [mul_assoc, hu]

/-! A short declaration can be written on a single line: -/

variable {M : Type*} [Monoid M]

@[simp] lemma RLE.mul_right_self (x y : M): x * y ≤𝓡 x := by use y

/-!
### `have` syntax
A have can be put on a single line when the justification is short:
```c
example (n k : Nat) (h : n < k) : ... :=
  have h1 : n ≠ k := ne_of_lt h
```

When the justification is too long, you should put it on the next line,
indented by an additional two spaces:
```c
example (n k : Nat) (h : n < k) : ... :=
  have h1 : n ≠ k := by
    apply ne_of_lt
```
### Grouping definitions

We generally use a blank line to separate theorems and definitions,
but this can be omitted, for example, to group together a number of short definitions,
or to group together a definition and notation.
-/

@[simp] lemma RLE.refl (x : M) : x ≤𝓡 x := by use 1; simp
@[simp] lemma LLE.refl (x : M) : x ≤𝓛 x := by use 1; simp
@[simp] lemma JLE.refl (x : M) : x ≤𝓙 x := by use 1, 1; simp
@[simp] lemma HLE.refl (x : M) : x ≤𝓗 x := by simp [HLE]

/-!
### Instances

When providing terms of structures or instances of classes, the `where` syntax
should be used to avoid the need for enclosing braces, as in: -/

instance RLE.isPreorder : IsPreorder M RLE where
  refl := RLE.refl
  trans := by intros x y z h₁ h₂; apply RLE.trans h₁ h₂

/-!
### Hypotheses Left of Colon

Generally, having arguments to the left of the colon is preferred over having arguments in
universal quantifiers or implications, if the proof starts by introducing these variables.
For instance:  -/

example (n : ℝ) (h : 1 < n) : 0 < n := by linarith

/-! is preferred over -/

example (n : ℝ) : 1 < n → 0 < n := fun h ↦ by linarith

/-!
### Anonymous functions

Lean has several nice syntax options for declaring anonymous functions. For very simple
functions, one can use the centered dot as the function argument, as in `(· ^ 2)` to represent
the squaring function. However, sometimes it is necessary to refer to the arguments by name
(e.g., if they appear in multiple places in the function body). The `Lean` default for this is
`fun x => x * x`, but the `↦` arrow (inserted with `\mapsto`) is also valid. In `mathlib` the
pretty printer displays `↦`, and we slightly prefer this in the source as well.

Example: -/

instance REquiv.isEquiv : Equivalence (fun x y : M => x 𝓡 y) := by
  unfold REquiv
  exact @EquivOfLE.isEquiv M RLE _

/-!
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

Iff theorems should be notated such that the more normalized version of the statement is on the right
side of the iff. This allows you to use them with `rw` and `simp` without prepending `←`. This also
is the way that `simp` will try to automatically apply the tactic if you tag it @[simp].
-/
