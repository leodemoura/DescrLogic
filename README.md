# DescrLogic

A deep embedding of the ALC description logic in [Lean 4](https://lean-lang.org), with formal semantics, custom notation, and computable finite interpretations.

The point: Lean is both a theorem prover and a programming language. This project uses both sides — you can **prove** metatheorems about ALC and **execute** knowledge base queries in the same language, with the same definitions.

## What's here

**Syntax** — ALC concepts as an inductive type with notation:

```lean
concept Person
concept Female

role hasChild

-- Concepts compose with ⊓ (and), ⊔ (or), ~ (not), ∀ᵣ, ∃ᵣ
def Mother := Female ⊓ (∃ᵣ hasChild, .top)
```

**Semantics** — Standard set-theoretic interpretation (`Concept.eval`):

```lean
def Concept.eval (I : Interp α) : Concept → α → Prop
  | .top, _       => True
  | .bot, _       => False
  | .atom name, a => I.concept name a
  | .neg C, a     => ¬ C.eval I a
  | .conj C D, a  => C.eval I a ∧ D.eval I a
  | .disj C D, a  => C.eval I a ∨ D.eval I a
  | .all r C, a   => ∀ b, I.role r a b → C.eval I b
  | .ex r C, a    => ∃ b, I.role r a b ∧ C.eval I b
```

**Metatheory** — Proved against the semantics (no sorry):

```lean
theorem de_morgan_conj (I : Interp α) (C D : Concept) :
    equiv I (~ (C ⊓ D)) (~ C ⊔ ~ D) := ...

theorem neg_neg (I : Interp α) (C : Concept) :
    equiv I (~ (~ C)) C := ...
```

**Computable finite interpretations** — `FinInterp n` evaluates concepts over `Fin n` using `Bool`, so everything runs:

```lean
knowledge family where
  Alice   : Person, Female, Parent
  Bob     : Person, Male, Parent
  Charlie : Person, Male
  Diana   : Person, Female
  Alice hasChild Charlie
  Bob hasChild Diana

#eval family.extensionNames (∃ᵣ hasChild, Female)
-- ["Bob"]

#eval family.subsumes Mother Parent
-- true

#eval family.satisfiable (Male ⊓ Female)
-- false
```

**TBox reasoning:**

```lean
def familyTBox : TBox := [
  Parent ⊑ Person,
  (∃ᵣ hasChild, .top) ⊑ Parent
]

#eval family.satisfiesTBox familyTBox  -- true
```

## Project structure

| File | Contents |
|------|----------|
| `Basic.lean` | `Concept` inductive, `Interp`, `Concept.eval`, notation, metatheorems |
| `Finite.lean` | `FinInterp n` with `Bool`-valued evaluation, extension/subsumption/satisfiability |
| `KB.lean` | `KB` structure (named individuals + fact lists), compiles to `FinInterp` |
| `Syntax.lean` | `concept`, `role`, and `knowledge` command macros |
| `Demo.lean` | Family ontology example with executable queries |

## Building

Requires [Lean 4](https://lean-lang.org/lean4/doc/setup.html) (v4.28.0).

```
lake build
lake exe descrlogic
```
