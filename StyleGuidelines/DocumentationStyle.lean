import Mathlib

/-!
# Documentation style

This file is an assembly of the most relevant content in these documents:
- Documentation Style: https://leanprover-community.github.io/contribute/naming.html

## Summary

- Module docstrings guide
- Documentation strings guide (using `/--` and `-/`)
- LaTeX and Markdown formatting in documentation
- File structure with sectioning comments
- Examples of good documentation style

### Comments

Use module doc delimiters `/-! -/` to provide section headers and separators since these
get incorporated into the auto-generated docs, and use `/- -/` for more technical comments
(e.g. TODOs and implementation notes) or for comments in proofs. Use `--` for short or
in-line comments.

Documentation strings for declarations are delimited with `/-- -/`. When a documentation
string for a declaration spans multiple lines, do not indent subsequent lines.

### Module Docstrings (Header Comments)

- Each mathlib file should start with a module docstring containing
general documentation, written using Markdown and LaTeX.

- The open and close delimiters `/-!` and `-/` should appear on their own lines.

- The mandatory title of the file is a first level header.
It is followed by a summary of the content of the file.

- The other sections, with second level headers are (in this order):
  1. Main definitions (optional, can be covered in the summary)
  2. Main statements (optional, can be covered in the summary)
  3. Notations (omitted only if no notation is introduced in this file)
  4. Implementation notes (description of important design decisions or interface features,
      including use of type classes and `simp` canonical form for new definitions)
  5. References (references to textbooks or papers, or Wikipedia pages)

- The following code block is an example of a file header.

/-! (BEGIN EXAMPLE)
# p-adic norm

This file defines the `p`-adic norm on `ℚ`.

The `p`-adic valuation on `ℚ` is the difference of the multiplicities of `p` in the numerator and
denominator of `q`. This function obeys the standard properties of a valuation, with the appropriate
assumptions on `p`.

The valuation induces a norm on `ℚ`. This norm is a nonarchimedean absolute value.
It takes values in {0} ∪ {1/p^k | k ∈ ℤ}.

## Implementation notes

Much, but not all, of this file assumes that `p` is prime. This assumption is inferred automatically
by taking `[Fact p.Prime]` as a type class argument.

## References

* <https://en.wikipedia.org/wiki/P-adic_number>
-/
(END EXAMPLE)

### Doc strings

- Every definition and major theorem is required to have a doc string. (Doc strings on lemmas
are also encouraged, particularly if the lemma has any mathematical content or might be useful
in another file.) These are introduced using `/--` and closed by `-/` above the definition,
with either newlines or single spaces between the markers and the text. Subsequent lines in a
doc-string should not be indented. They can contain Markdown and LaTeX as well: see the next
section. If a doc string is a complete sentence, then it should end in a period. Named theorems,
such as the mean value theorem should be bold faced (i.e., with two asterisks before and after).

- Doc strings should convey the mathematical meaning of the definition.
They are allowed to lie slightly about the actual implementation.
The following is a doc string example: -/

/-- If `q ≠ 0`, the `p`-adic norm of a rational `q` is `p ^ (-padicValRat p q)`.
If `q = 0`, the `p`-adic norm of `q` is `0`. -/
def padicNorm' (p : ℕ) (q : ℚ) : ℚ :=
  if q = 0 then 0 else (p : ℚ) ^ (-padicValRat p q)

/-! - An example that is slightly lying but still describes the mathematical content would be: -/

/-- `padicValRat` defines the valuation of a rational `q` to be the valuation of `q.num` minus the
valuation of `q.den`. If `q = 0` or `p = 1`, then `padicValRat p q` defaults to `0`. -/
def padicValRat' (p : ℕ) (q : ℚ) : ℤ :=
  padicValInt p q.num - padicValNat p q.den

/-!
### LaTeX and Markdown

- We generally put references to Lean declarations or variables in between backticks.
Writing the fully-qualified name (e.g. `finset.card_pos` instead of just `card_pos`) will
turn the name into a link on our online docs.

- Raw URLs should be enclosed in angle brackets `<...>` to ensure that they will be clickable online.

- When talking about mathematical symbols instead, it may be preferable to use LaTeX.
LaTeX can be included in doc strings in three ways:

  1. using single dollar signs `$ ... $` to render math inline,
  2. using double dollar signs `$$ ... $$` to render math in "display mode", or
  3. using environments `\begin{*} ... \end{*}` (without dollar signs).

### File Structure

- It is common to structure a file in sections, where each section contains related declarations.
By describing the sections with module documentation `/-! ... -/` at the beginning,
these sections can be seen in the documentation.

- While these sectioning comments will often correspond to `section` or `namespace` commands,
this is not required. You can use sectioning comments inside of a section or namespace,
and you can have multiple sections or namespaces following one sectioning comment.

- Sectioning comments are for display and readability only. They have no semantic meaning.

- Third-level headers `###` should be used for titles inside sectioning comments.

- If the comment is more than one line long, the delimiters `/-!` and `-/`
should appear on their own lines.

### Examples

- The following files are maintained as examples of good documentation style:

    `Mathlib.NumberTheory.Padics.PadicNorm`
    `Mathlib.Topology.Basic`
    `Analysis.Calculus.ContDiff.Basic`
-/
