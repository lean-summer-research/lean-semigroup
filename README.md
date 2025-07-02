

# Style Guidelines
Sources:
1. Style Guidlines - https://leanprover-community.github.io/contribute/style.html
2. Naming Conventions - https://leanprover-community.github.io/contribute/naming.html

## Case (capitalization) conventions

- TODO: add examples from codebase
  
There are 3 types of case styles used in Lean4:
1. `snake_case`
2. `UpperCamelCase`
3. `lowerCamelCase`

### `snake_case`
- Use for terms of type `Prop` (e.g. proofs, theorem names)
  
### `UpperCamelCase`
 - Use for file names
 - Use for `Prop`s and `Type`s (e.g. inductive types, structures, and classes)

### `lowerCamelCase`
- All ofther terms of `Types` (basically anything else)

### Special Cases

Functions are named the same way as their return values (e.g. a function of type A → B → C is named as though it is a term of type C). 

Acronyms like LE are written upper-/lowercase as a group, depending on what the first character would be. An exception is `Ne` and `Eq` for not equal and equal.

## Naming Theorems
When naming theorems, translate the statement of the theorem into words using the following dictionary. 

### Logic naming Dictionary

symbol 	shortcut 	 name 	          notes
∨ 	    \or 	     or 	
∧ 	    \and       and 	
→ 	    \r 	       of / imp 	      the conclusion is stated first and the hypotheses are often omitted
↔ 	    \iff       iff 	            sometimes omitted along with the right hand side of the iff
¬ 	    \n 	       not 	
∃ 	    \ex 	     exists      
∀ 	    \fo 	     all / forall   	
= 	  	eq 	       often omitted
≠ 	    \ne 	     ne 	
∘ 	    \o 	       comp 	


### Set naming Dictionary

symbol 	shortcut 	name 	notes
∈ 	    \in 	mem 	
∉ 	    \notin 	notMem 	
∪ 	    \cup 	union 	
∩ 	     \cap 	inter 	
⋃ 	\bigcup 	iUnion / biUnion 	i for "indexed", bi for "bounded indexed"
⋂ 	\bigcap 	iInter / biInter 	i for "indexed", bi for "bounded indexed"
⋃₀ 	\bigcup\0 	sUnion 	s for "set"
⋂₀ 	\bigcap\0 	sInter 	s for "set"
\ 	\\ 	sdiff 	
ᶜ 	\^c 	compl 	
{x | p x} 		setOf 	
{x} 		singleton 	
{x, y} 		pair 	
Algebra
symbol 	shortcut 	name 	notes
0 		zero 	
+ 		add 	
- 		neg / sub 	neg for the unary function, sub for the binary function
1 		one 	
* 		mul 	
^ 		pow 	
/ 		div 	
• 	\bu 	smul 	
⁻¹ 	\-1 	inv 	
⅟ 	\frac1 	invOf 	
∣ 	\| 	dvd 	
∑ 	\sum 	sum 	
∏ 	\prod 	prod 	





## Variable naming conventions
    u, v, w, ... for universes
    α, β, γ, ... for generic types
    a, b, c, ... for propositions
    x, y, z, ... for elements of a generic type
    h, h₁, ... for assumptions
    p, q, r, ... for predicates and relations
    s, t, ... for lists
    s, t, ... for sets
    m, n, k, ... for natural numbers
    i, j, k, ... for integers
    
We also use `S` `M` and `G` for semigroups, monoids, and groups, respectivly.
TODO: Fix code for this, replace `s` with `x` for elemnets of semigroups.

## Line Length
Lines should not be longer than 100 characters.

## Module Docstrings
Every file should have a module docstring after the imports (delimited with /-! and -/)

It should contain:
- a title of the file,
- a summary of the contents (the main definitions and theorems, proof techniques, etc…)
- notation that has been used in the file (if any)
- Implementation Notes and TODOs (if any)
- references to the literature (if any)

## Structuring definitions and theorems

All declarations (e.g., def, lemma, theorem, class, structure, inductive, instance, etc.) and commands (e.g., variable, open, section, namespace, notation, etc.) are considered top-level and these words should appear flush-left in the document. In particular, opening a namespace or section does not result in indenting the contents of that namespace or section. (Note: within VS Code, hovering over any declaration such as def Foo ... will show the fully qualified name, like MyNamespace Foo if Foo is declared while the namespace MyNamespace is open.)

Use spaces on both sides of ":", ":=" or infix operators. Put them before a line break rather than at the beginning of the next line.

After stating the theorem, we indent the lines in the subsequent proof by 2 spaces.
```
open Nat
theorem nat_case {P : Nat → Prop} (n : Nat) (H1 : P 0) (H2 : ∀ m, P (succ m)) : P n :=
  Nat.recOn n H1 (fun m IH ↦ H2 m)
```

If the theorem statement requires multiple lines, indent the subsequent lines by 4 spaces. The proof is still indented only 2 spaces (not 6 = 4 + 2). When providing a proof in tactic mode, the by is placed on the line prior to the first tactic; however, by should not be placed on a line by itself. In practice this means you will often see := by at the end of a theorem statement.

```
theorem le_induction {P : Nat → Prop} {m}
    (h0 : P m) (h1 : ∀ n, m ≤ n → P n → P (n + 1)) :
    ∀ n, m ≤ n → P n := by
  apply Nat.le.rec
  · exact h0
  · exact h1 _
```

When a proof term takes multiple arguments, it is sometimes clearer, and often necessary, to put some of the arguments on subsequent lines. In that case, indent each argument. This rule, i.e., indent an additional two spaces, applies more generally whenever a term spans multiple lines.

```
theorem nat_discriminate {B : Prop} {n : Nat} (H1: n = 0 → B) (H2 : ∀ m, n = succ m → B) : B :=
  Or.elim (zero_or_succ n)
    (fun H3 : n = zero ↦ H1 H3)
    (fun H3 : n = succ (pred n) ↦ H2 (pred n) H3)
```

A short declaration can be written on a single line:

```
theorem succ_pos : ∀ n : Nat, 0 < succ n := zero_lt_succ

def square (x : Nat) : Nat := x * x
```
A have can be put on a single line when the justification is short.

```
example (n k : Nat) (h : n < k) : ... :=
  have h1 : n ≠ k := ne_of_lt h
  ...
```

When the justification is too long, you should put it on the next line, indented by an additional two spaces.

```
example (n k : Nat) (h : n < k) : ... :=
  have h1 : n ≠ k := by
    apply ne_of_lt
    exact h
```

When the arguments themselves are long enough to require line breaks, use an additional indent for every line after the first, as in the following example:

```
theorem Nat.add_right_inj {n m k : Nat} : n + m = n + k → m = k :=
  Nat.recOn n
    (fun H : 0 + m = 0 + k ↦ calc
      m = 0 + m := Eq.symm (zero_add m)
      _ = 0 + k := H
      _ = k     := zero_add _)
    (fun (n : Nat) (IH : n + m = n + k → m = k) (H : succ n + m = succ n + k) ↦
      have H2 : succ (n + m) = succ (n + k) := calc
        succ (n + m) = succ n + m   := Eq.symm (succ_add n m)
        _            = succ n + k   := H
        _            = succ (n + k) := succ_add n k
      have H3 : n + m = n + k := succ.inj H2
      IH H3)
```

In a class or structure definition, fields are indented 2 spaces, and moreover each field should have a docstring, as in:

```
class Module (R : Type u) (M : Type v) [Semiring R] [AddCommMonoid M] extends
    DistribMulAction R M where
  /-- Scalar multiplication distributes over addition from the right. -/
  protected add_smul : ∀ (r s : R) (x : M), (r + s) • x = r • x + s • x
  /-- Scalar multiplication by zero gives zero. -/
  protected zero_smul : ∀ x : M, (0 : R) • x = 0
```
When using a constructor taking several arguments in a definition, arguments line up, as in:

```
theorem Ordinal.sub_eq_zero_iff_le {a b : Ordinal} : a - b = 0 ↔ a ≤ b :=
  ⟨fun h => by simpa only [h, add_zero] using le_add_sub a b,
   fun h => by rwa [← Ordinal.le_zero, sub_le, add_zero]⟩
```


We generally use a blank line to separate theorems and definitions, but this can be omitted, for example, to group together a number of short definitions, or to group together a definition and notation.

## Instances

When providing terms of structures or instances of classes, the where syntax should be used to avoid the need for enclosing braces, as in:

```
instance instOrderBot : OrderBot ℕ where
  bot := 0
  bot_le := Nat.zero_le
```

If there is already an instance instBot, then one can write

```
instance instOrderBot : OrderBot ℕ where
  __ := instBot
  bot_le := Nat.zero_le
```
## Hypotheses Left of Colon

Generally, having arguments to the left of the colon is preferred over having arguments in universal quantifiers or implications, if the proof starts by introducing these variables. For instance:

```
example (n : ℝ) (h : 1 < n) : 0 < n := by linarith
```

is preferred over

```
example (n : ℝ) : 1 < n → 0 < n := fun h ↦ by linarith
```

## Anonymous functions

Lean has several nice syntax options for declaring anonymous functions. For very simple functions, one can use the centered dot as the function argument, as in (· ^ 2) to represent the squaring function. However, sometimes it is necessary to refer to the arguments by name (e.g., if they appear in multiple places in the function body). The Lean default for this is fun x => x * x, but the ↦ arrow (inserted with \mapsto) is also valid. In mathlib the pretty printer displays ↦, and we slightly prefer this in the source as well. 

## Tactic Mode
As we have already mentioned, when opening a tactic block, by is placed at the end of the line preceding the start of the tactic block, but not on its own line. Everything within the tactic block is indented.

When new goals arise as side conditions or steps, they are indented and preceded by a focusing dot · (inserted as \.); the dot is not indented:

```
theorem exists_npow_eq_one_of_zpow_eq_one' [Group G] {n : ℤ} (hn : n ≠ 0) {x : G} (h : x ^ n = 1) :
    ∃ n : ℕ, 0 < n ∧ x ^ n = 1 := by
  cases n
  · simp only [Int.ofNat_eq_coe] at h
    rw [zpow_ofNat] at h
    refine ⟨_, Nat.pos_of_ne_zero fun n0 ↦ hn ?_, h⟩
    rw [n0]
    rfl
  · rw [zpow_negSucc, inv_eq_one] at h
    refine ⟨_ + 1, Nat.succ_pos _, h⟩
```

Certain tactics, such as refine, can create named subgoals which can be proven in whichever order is desired using case. This feature is also useful in aiding readability. However, it is not required to use this instead of the focusing dot (·).

```
example {p q : Prop} (h₁ : p → q) (h₂ : q → p) : p ↔ q := by
  refine ⟨?imp, ?converse⟩
  case converse => exact h₂
  case imp => exact h₁
```

Often t0 <;> t1 is used to execute t0 and then t1 on all new goals. Either write the tactics in one line, or indent the following tactic.

```
  cases x <;>
    simp [a, b, c, d]
```

For single line tactic proofs (or short tactic proofs embedded in a term), it is acceptable to use by tac1; tac2; tac3 with semicolons instead of a new line with indentation.

In general, you should put a single tactic invocation per line, unless you are closing a goal with a proof that fits entirely on a single line. Short sequences of tactics that correspond to a single mathematical idea can also be put on a single line, separated by semicolons as in cases bla; clear h or induction n; simp or rw [foo]; simp_rw [bar], but even in these scenarios, newlines are preferred.

```
example : ... := by
  by_cases h : x = 0
  · rw [h]; exact hzero ha
  · rw [h]
    have h' : ... := H ha
    simp_rw [h', hb]
    ...
```

Very short goals can be closed right away using swap or pick_goal if needed, to avoid additional indentation in the rest of the proof.

```
example : ... := by
  rw [h]
  swap; exact h'
  ...
```

## Squeezing simp calls

Unless performance is particularly poor or the proof breaks otherwise, terminal simp calls (a simp call is terminal if it closes the current goal or is only followed by flexible tactics such as ring, field_simp, aesop) should not be squeezed (replaced by the output of simp?).

There are two main reasons for this:

1. A squeezed simp call might be several lines longer than the corresponding unsqueezed one, and therefore drown the useful information of what key lemmas were added to the unsqueezed simp call to close the goal in a sea of basic simp lemmas.
2. A squeezed simp call refers to many lemmas by name, meaning that it will break when one such lemma gets renamed. Lemma renamings happen often enough for this to matter on a maintenance level.

## Whitespace and delimiters

Lean is whitespace-sensitive, and in general we opt for a style which avoids delimiting code. For instance, when writing tactics, it is possible to write them as tac1; tac2; tac3, separated by ;, in order to override the default whitespace sensitivity. However, as mentioned above, we generally try to avoid this except in a few special cases.

Similarly, sometimes parentheses can be avoided by judicious use of the <| operator (or its cousin |>). Note: while $ is a synonym for <|, its use in mathlib is disallowed in favor of <| for consistency as well as because of the symmetry with |>. These operators have the effect of parenthesizing everything to the right of <| (note that ( is curved the same direction as <) or to the left of |> (and ) curves the same way as >).

A common example of the usage of |> occurs with dot notation when the term preceding the . is a function applied to some arguments. For instance, `((foo a).bar b).baz` can be rewritten as `foo a |>.bar b |>.baz`

A common example of the usage of <| is when the user provides a term which is a function applied to multiple arguments whose last argument is a proof in tactic mode, especially one that spans multiple lines. In that case, it is natural to use <| by ... instead of (by ...), as in:

```
example {x y : ℝ} (hxy : x ≤ y) (h : ∀ ε > 0, y - ε ≤ x) : x = y :=
  le_antisymm hxy <| le_of_forall_pos_le_add <| by
    intro ε hε
    have := h ε hε
    linarith
```

When using the tactics rw or simp there should be a space after the left arrow ←. For instance `rw [← add_comm a b]` or `simp [← and_or_left]`. (There should also be a space between the tactic name and its arguments, as in `rw [h]`.) 

Empty lines inside declarations are discouraged and there is a linter that enforces that they are not present. This helps maintaining a uniform code style throughout all of mathlib.

## Comments
Use module doc delimiters /-! -/ to provide section headers and separators since these get incorporated into the auto-generated docs, and use /- -/ for more technical comments (e.g. TODOs and implementation notes) or for comments in proofs. Use -- for short or in-line comments.

Documentation strings for declarations are delimited with /-- -/. When a documentation string for a declaration spans multiple lines, do not indent subsequent lines.


# TODO

- "Least monoid containing a semigroup" implementation in WithOne.lean
- Relate Ideal definition to Closure definition rather than generators
- Duality of L and R through "Reverse Semigroup"
  - Reverse Semigroup S^rev - The same elements but multiplication is reversed
    - This means we have two semigroups defined on the same type (does it have to be unbundled?)
    
## Explain Normal forms
Normal forms #

Some statements are equivalent. For instance, there are several equivalent ways to require that a subset s of a type is nonempty. For another example, given a : α, the corresponding element of Option α can be equivalently written as Some a or (a : Option α). In general, we try to settle on one standard form, called the normal form, and use it both in statements and conclusions of theorems. In the above examples, this would be s.Nonempty (which gives access to dot notation) and (a : Option α). Often, simp lemmas will be registered to convert the other equivalent forms to the normal form.

# Project Structure

## Files and Organization

### Main Project Files (`MyProject` folder)
- **PnatPow.lean**: Defines exponentiation for semigroups using positive natural numbers
- **WithOne.lean**: Implements the `S¹` construction for turning semigroups into monoids
- **Idempotence.lean**: Proves theorems about idempotent elements in finite semigroups

#### `MyProject/GreensRelations` folder
- **Defs.lean**: Formalizes Green's relations (R, L, J, H, and D). This file contains Definitions and alternative definitions based on Ideals, anlong with other characterizatoins of Greens Relations
- **Quot.lean**: This file deals with the representation of equivilance classes of Greens Equivalences as a `Quot` type.
- **Decidable.lean**: This contains things related to Decidability and Fintype instances for working with Greens relations on concrete examples of Semigroups.
- **Basic.lean**: This contains lemmas that build upon the foundation defined in earlier files.

### Examples (`Examples` folder)
- **Threemap.lean**: Defines the monoid of functions on {0,1,2} under composition and characterizes Greens relations on it. Demonstrates stuff from `MyProject.GreensRelations.Decidable.lean`
- **HSversion.lean**: Unchanged
- **GreensRelationsHS.lean**: Unchanged

## Import Structure
```
Mathlib
  ↓
PnatPow.lean
  ↓
WithOne.lean
  ↓
Idempotence.lean
  ↓
GreensRelations.Defs.lean
  ↓
GreensRelations.Quot.lean
  ↓
GreensRelations.Decidable.lean
  ↓
GreensRelations.Basic.lean
```

# Using Github Codespaces

There are two ways to use this repository:

1. Clone the repository and use it normally, ignoring the `.devcontainer` folder.
2. (also easy) Use GitHub Codespaces, which gives you a pre-configured development environment in your browser (explained below).

When you open this repo in a codespace, you'll see a VS Code interface in your browser. It's automatically set up with the LEAN4 vscode extention, correct lean version, and mathlib cache. It all runs on github's infra, so you don't have to worry about any of your local Lean, Elan, or VScode installations.

## First Time Setup:
1. Click the green "<> Code" button at the top of this GitHub page
2. Select "Codespaces" tab
3. Click "Create codespace"
4. Wait about 5-10 minutes for initial setup

## Basic Git Commands:
  First you have to open the integrated terminal (Mac: `Cmd+(backtick)`, Windows: `Ctrl+(backtick)`)

```bash
# Download latest changes
git pull

# Save your changes
# Stage all changes in the current working directory (make sure you are in the directory you want to save)
git add .

# Save changes locally
git commit -m "example"

# Upload changes to GitHub
git push
```

## Returning Later:
Go back to the repository's "<> Code" button, select "Codespaces" tab, and click your existing codespace (starts a lot faster than the initial build).

## How It Works (and how to do it locally)

The `.devcontainer` folder contains configuration files for a "dev container," which is like a small virtual machine. It sets up everything needed, like the operating system and software such as VSCode and Lean. GitHub Codespaces uses these files to create a development environment in the cloud, using Docker to manage the setup.

Docker is a tool that runs dev containers on your local computer. If you prefer not to use GitHub's cloud, you can run the same dev container locally instead of using Codespaces:

1. Install Docker Desktop from docker.com
2. In VS Code, install the "Dev Containers" extension
3. Clone this repository
4. Open the folder in VS Code
5. Click "Reopen in Container" when prompted

This will give you the same environment as Codespaces but running on your local machine. The VScode extension should automatically reopen the same container when you reopen the folder so you only have to build the container once.
