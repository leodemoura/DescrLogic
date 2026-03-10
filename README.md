# DescrLogic

A deep embedding of the ALC description logic in [Lean 4](https://lean-lang.org), with formal semantics, custom notation, and computable finite interpretations.

The point: Lean is both a theorem prover and a programming language. This project uses both sides — you can **prove** metatheorems about ALC and **execute** knowledge base queries in the same language, with the same definitions.

## Custom notation

None of the DL-specific syntax below is built into Lean. It's all defined in the project using Lean's macro system (about 70 lines in [`Syntax.lean`](DescrLogic/Syntax.lean) and [`Basic.lean`](DescrLogic/Basic.lean)).

**Concept declarations** — the `concept` and `role` commands are custom:

```lean
concept Person      -- declares an atomic concept
concept Female
role hasChild       -- declares a role name
```

**Concept expressions** — standard DL connectives, defined as custom infix/prefix operators:

| Notation | Meaning | Standard DL |
|----------|---------|-------------|
| `C ⊓ D` | conjunction | C ⊓ D |
| `C ⊔ D` | disjunction | C ⊔ D |
| `~ C` | negation | ¬C |
| `∀ᵣ r, C` | universal restriction | ∀r.C |
| `∃ᵣ r, C` | existential restriction | ∃r.C |
| `C ⊑ D` | concept inclusion (TBox) | C ⊑ D |

So you can write concept expressions that read like textbook DL:

```lean
def Mother := Female ⊓ (∃ᵣ hasChild, .top)
```

**Knowledge base declarations** — the `knowledge` command is a custom macro that parses a block of concept membership and role assertions, collects the individual names automatically, and generates the internal data structure:

```lean
knowledge family where
  Alice   : Person, Female, Parent
  Bob     : Person, Male, Parent
  Charlie : Person, Male
  Diana   : Person, Female
  Alice hasChild Charlie
  Bob hasChild Diana
```

## Semantics

Standard set-theoretic interpretation, defined as a recursive function from concepts to predicates over a domain:

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

This is both the formal specification (used in proofs) and the basis for the computable evaluator.

## Proofs

Metatheorems proved directly against the semantics (no axioms, no `sorry`):

```lean
theorem de_morgan_conj (I : Interp α) (C D : Concept) :
    equiv I (~ (C ⊓ D)) (~ C ⊔ ~ D) := ...

theorem neg_neg (I : Interp α) (C : Concept) :
    equiv I (~ (~ C)) C := ...
```

## Executable queries

`#eval` runs queries at compile time — Lean computes the answers:

```lean
#eval family.extensionNames (∃ᵣ hasChild, Female)
-- ["Bob"]

#eval family.subsumes Mother Parent
-- true

#eval family.satisfiable (Male ⊓ Female)
-- false
```

TBox satisfaction checking:

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
| [`Basic.lean`](DescrLogic/Basic.lean) | `Concept` inductive type, `Interp`, semantic evaluation, operator notation, metatheorems |
| [`Finite.lean`](DescrLogic/Finite.lean) | `FinInterp n` — computable `Bool`-valued evaluation over finite domains |
| [`KB.lean`](DescrLogic/KB.lean) | `KB` — named individuals + fact lists, compiles to `FinInterp` |
| [`Syntax.lean`](DescrLogic/Syntax.lean) | `concept`, `role`, and `knowledge` command macros |
| [`Demo.lean`](DescrLogic/Demo.lean) | Family ontology example with executable queries |

## Building

Requires [Lean 4](https://lean-lang.org/lean4/doc/setup.html) (v4.28.0).

```
lake build
lake exe descrlogic
```
