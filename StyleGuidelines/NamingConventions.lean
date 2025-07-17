import MyProject.Monoid.Local

/-!
# Project Naming Conventions

This file is an assembly of the most relevant content in these documents:
- Lean Community website: https://leanprover-community.github.io/index.html
- Mathlib naming conventions: https://leanprover-community.github.io/contribute/naming.html

## Summary

- Variable naming conventions
- Case style guidelines (`snake_case`, `UpperCamelCase`, and `lowerCamelCase`)
- Namespaces, Dot notation, and "axiomatic" naming
- General naming standards and a dictionary for naming common operations

### Variable Naming Conventions

`x`, `y`, `z`, `u`, `v`, `w` ... for elements of a generic type
  (including elements of Semigroups and Monoids!)
`e` ... for idempotent elements
`s`, `t`, ... for sets and lists
`p`, `q`, `r`, ... for predicates and relations (excluding greens relations)
`m`, `n`, `k`, ... for natural numbers
`i`, `j`, `k`, ... for integers
`a`, `b`, `c`, ... for propositions
`S`, `T` ... for semigroups
`M` ... for monoids
`G` ... for groups
`α`, `β`, `γ`, ... for generic types
`u`, `v`, `w`, ... for universes
`h`, `h₁`, ... for assumptions

### snake_case vs. UpperCamelCase vs lowerCamelCase

- Use `snake_case` for terms of type `Prop` (e.g. proofs, theorem names)

- Use `UpperCamelCase` for:
  1. File Names
  2.`Prop`s and `Type`s (e.g. inductive types, structures, and classes)
    i.e. `REquiv`, `RLE`, `REquiv.isEquiv`

- Use `lowerCamelCase` for all other terms of `Types` (basically anything else)
  i.e. `REquiv.set`

#### Special Cases

- Functions are named the same way as their return values.
For example, a function of type `A → B → C` is named as though it is a term of type `C`.

- Acronyms like `LE` are written upper or lowercase as a group, depending on what the
first character would be. An exception is `Ne` and `Eq`.

- When appearing in the names of theorems, `UpperCamelCase` types get `lowerCamelCase`d.
   i.e. `HEquiv.to_rEquiv`


- When referring to a namespaced definition in a lemma name not in the same namespace,
the definition should have its namespace removed. If the definition name is unambiguous
without its namespace, it can be used as is. Else, the namespace is prepended back to it
in `lowerCamelCase`. This is to ensure that _-separated strings in a lemma name correspond
to a definition name or connective.

(Note: within VS Code, hovering over any declaration such as def Foo ... will show the
fully qualified name, like `MyNamespace.Foo` if `Foo` is declared while the
namespace `MyNamespace` is open.)

### Naming Theorems Descriptively

- Definitions and theorem's names should describe their conclusion. There are some standard
names for various operations that may be in that conclusion.

#### Logic naming Dictionary

symbol 	shortcut 	 name 	          notes
∨ 	    `\or` 	     `or`
∧ 	    `\and`       `and`
→ 	    `\r` 	     `of` / `imp`  the conclusion is stated first and the hypotheses are often omitted
↔ 	    `\iff`       `iff` 	        sometimes omitted along with the right hand side of the iff
¬ 	    `\n` 	     `not`
∃ 	    `\ex` 	     `exists`
∀ 	    `\fo` 	     `all` / `forall`
= 	  	             `eq` 	        often omitted
≠ 	    `\ne` 	     `ne`
∘ 	    `\o` 	     `comp`

#### Algebra naming Dictionary

symbol    shortcut     name             notes
0                     `zero`
+                     `add`
-                     `neg` / `sub`     `neg` for the unary function, `sub` for the binary function
1                     `one`
*                     `mul`
^                     `pow`
/                     `div`
•         `\bu`       `smul`
⁻¹        `\-1`       `inv`
⅟         `\frac1`    `invOf`
∣         `\|`        `dvd`
∑         `\sum`      `sum`
∏         `\prod`     `prod`

#### Set naming Dictionary

symbol    shortcut     name               notes
∈         `\in`       `mem`
∉         `\notin`    `notMem`
∪         `\cup`      `union`
∩         `\cap`      `inter`
⋃         `\bigcup`   `iUnion` / `biUnion`   i for "indexed", bi for "bounded indexed"
⋂         `\bigcap`   `iInter` / `biInter`   i for "indexed", bi for "bounded indexed"
\         `\\`        `sdiff`
ᶜ         `\^c`       `compl`
{x | p x}             `setOf`
{x}                   `singleton`
{x, y}                `pair`


#### Lattice naming Dictionary

symbol    shortcut     name
< 		               `lt` / `gt`
≤ 	        `\le` 	   `le` / `ge`

- The symbols ≤ and < have a special naming convention. In mathlib,
we almost always use ≤ and < instead of ≥ and >, so we can use both `le`/`lt`
and `ge`/`gt` for naming ≤ and <. There are a few reasons to use `ge`/`gt`:

1. We use `ge`/`gt` if the arguments to ≤ or < appear in different orders.
  We use `le`/`lt` for the first occurrence of ≤/< in the theorem name,
  and then `ge`/`gt` indicates that the arguments are swapped.

2. We use `ge`/`gt` to match the argument order of another relation, such as = or ≠.

3. We use `ge`/`gt` to describe the ≤ or < relation with its arguments swapped.

4. We use `ge`/`gt` if the second argument to ≤ or < is 'more variable'.

```c
-- follows rule 1
theorem lt_iff_le_not_ge [Preorder α] {a b : α} : a < b ↔ a ≤ b ∧ ¬b ≤ a := sorry
theorem not_le_of_gt [Preorder α] {a b : α} (h : a < b) : ¬b ≤ a := sorry
theorem LT.lt.not_ge [Preorder α] {a b : α} (h : a < b) : ¬b ≤ a := sorry

-- follows rule 2
theorem Eq.ge [Preorder α] {a b : α} (h : a = b) : b ≤ a := sorry
theorem ne_of_gt [Preorder α] {a b : α} (h : b < a) : a ≠ b := sorry

-- follows rule 3
theorem ge_trans [Preorder α] {a b : α} : b ≤ a → c ≤ b → c ≤ a := sorry

-- follows rule 4
theorem le_of_forall_gt [LinearOrder α] {a b : α} (H : ∀ (c : α), a < c → b < c) : b ≤ a := sorry
``` -/
#check REquiv.ge
#check REquiv.le

/-!
#### Referring to Hypothesis with `of`

Sometimes, to disambiguate the name of theorem or better convey the intended
reference, it is necessary to describe some of the hypotheses.
The word "of" is used to separate these hypotheses: -/

#check HEquiv.of_rEquiv_and_lEquiv

--Mathlib examples:
open Nat
#check lt_of_succ_le
#check lt_of_not_ge
#check lt_of_le_of_ne
#check add_lt_add_of_lt_of_le

/-! - The hypotheses are listed in the order they appear, not reverse order.
For example, the theorem `A → B → C` would be named `C_of_A_of_B`. -/

/-
### Namespaces and Local Hypothesis
If you put a function that accepts `(h : x 𝓡 y)` in the namespace `REquiv`,
you can then apply it to local hypothesis while writing proofs.
-/

#check REquiv.symm
#check REquiv.le
#check REquiv.ge
#check REquiv.to_dEquiv

variable {M : Type*} [Monoid M]

example (x y : M) (h : x 𝓡 y) : y 𝓡 x := by exact h.symm
example (x y : M) (h : x 𝓡 y) : x ≤𝓡 y := by exact h.le
example (x y : M) (h : x 𝓡 y) : y ≤𝓡 x := by exact h.ge
example (x y : M) (h : x 𝓡 y) : y 𝓓 x := by exact h.to_dEquiv.symm

/-!
### Naming Theorems Axiomatically

- We adopt the following naming guidelines to make it easier for
users to guess the name of a theorem or find it using tab completion.

- Generally, the name of a definition or theorem should be a description
of its conclusion. However, some theorems are better described using axiomatic names.

- Common "axiomatic" properties of an operation like introduction and elimination
are put in a namespace that begins with the name of the operation. In particular,
this includes `intro` and `elim` operations for logical connectives, and properties of relations:

Places where projection (dot) notation is useful, for example: -/

-- Our examples:
#check REquiv.trans
#check HEquiv.to_rEquiv
#check LLE.to_jLE
#check REquiv.op_iff
#check JEquiv.isEquiv

-- Mathlib examples:
#check And.comm
#check And.intro
#check And.elim
#check Or.comm
#check Or.intro_left
#check Or.intro_right
#check Or.resolve_left
#check Or.resolve_right
#check Eq.trans
#check HEq.trans
#check Iff.refl


/-!  Here are some common axiomatic Desciptions:
    `def` (for unfolding a definition)
    `assoc`
    `refl`
    `symm`
    `trans`
    `irrefl`
    `antisymm`
    `asymm`
    `congr`
    `comm`
    `left_comm`
    `right_comm`
    `mul_left_cancel`
    `mul_right_cancel`
    `inj` (injective)

- When an operation is written as infix, the theorem names follow suit.
For example, we write `neg_mul_neg` rather than `mul_neg_neg` to describe the pattern `-a * -b`.

#### Extensionality

- A lemma of the form `(∀ x, f x = g x) → f = g` should be named `.ext`, and labelled with the
`@[ext]` attribute.

- A lemma of the form `f = g ↔ ∀ x, f x = g x` should be named `.ext_iff`.

#### Injectivity

Where possible, injectivity lemmas should be written in terms of an `Function.Injective f`
conclusion which uses the full word injective, typically as `f_injective`.

In addition to these, a variant should usually be provided as a bidirectional implication,
e.g. as `f x = f y ↔ x = y`, which can be obtained from `Function.Injective.eq_iff`.
Such lemmas should be named `f_inj` (although if they are in an appropriate namespace
`.inj` is good too). Bidirectional injectivity lemmas are often good candidates for @[simp].

An injectivity lemma that uses "left" or "right" should refer to the argument that "changes".
For example, a lemma with the statement `a - b = a - c ↔ b = c` could be called `sub_right_inj`.

#### Predicates as Suffixes

Most predicates should be added as prefixes. Eg `IsClosed (Icc a b)`
should be called `isClosed_Icc`, not `Icc_isClosed`.

Some widely used predicates don't follow this rule. Those are the predicates that are analogous
to an atom already suffixed by the naming convention. Here is a non-exhaustive list:

- We use `_inj` for `f a = f b ↔ a = b`, so we also use `_injective` for `Injective f`,
`_surjective` for `Surjective f`, `_bijective` for `Bijective f`...

+- We use `_mono` for `a ≤ b → f a ≤ f b` and `_anti` for `a ≤ b → f b ≤ f a`,
+so we also use `_monotone` for `Monotone f`, `_antitone` for `Antitone f`,
`_strictMono` for `StrictMono f`, `_strictAnti` for `StrictAnti f`, etc...
-/
