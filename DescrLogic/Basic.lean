namespace DescrLogic

/-- Atomic concept and role names. -/
abbrev CName := String
abbrev RName := String

/-- ALC concept expressions. -/
inductive Concept where
  | top    : Concept
  | bot    : Concept
  | atom   : CName → Concept
  | neg    : Concept → Concept
  | conj   : Concept → Concept → Concept
  | disj   : Concept → Concept → Concept
  | all    : RName → Concept → Concept
  | ex     : RName → Concept → Concept
  deriving Repr, BEq, Hashable, Inhabited

namespace Concept

/-! ## Notation -/

scoped prefix:90 "~" => Concept.neg
scoped infixl:70 " ⊓ " => Concept.conj
scoped infixl:65 " ⊔ " => Concept.disj
/-- `∀ᵣ r, C` — universal restriction. -/
scoped notation:25 "∀ᵣ " r ", " C => Concept.all r C
/-- `∃ᵣ r, C` — existential restriction. -/
scoped notation:25 "∃ᵣ " r ", " C => Concept.ex r C

end Concept

/-! ## Set-theoretic semantics -/

/-- An interpretation over domain `α`. -/
structure Interp (α : Type) where
  /-- Interpretation of atomic concepts as predicates. -/
  concept : CName → α → Prop
  /-- Interpretation of roles as binary relations. -/
  role : RName → α → α → Prop

/-- Semantic evaluation of a concept in an interpretation. -/
def Concept.eval (I : Interp α) : Concept → α → Prop
  | .top, _       => True
  | .bot, _       => False
  | .atom name, a => I.concept name a
  | .neg C, a     => ¬ C.eval I a
  | .conj C D, a  => C.eval I a ∧ D.eval I a
  | .disj C D, a  => C.eval I a ∨ D.eval I a
  | .all r C, a   => ∀ b, I.role r a b → C.eval I b
  | .ex r C, a    => ∃ b, I.role r a b ∧ C.eval I b

/-- `C` is subsumed by `D` in interpretation `I`. -/
def subsumes (I : Interp α) (C D : Concept) : Prop :=
  ∀ a, C.eval I a → D.eval I a

/-- `C ≡ D` in interpretation `I`. -/
def equiv (I : Interp α) (C D : Concept) : Prop :=
  ∀ a, C.eval I a ↔ D.eval I a

/-- `C ⊑ D` is valid (all interpretations, all domains). -/
def validSubsumes (C D : Concept) : Prop :=
  ∀ (α : Type) (I : Interp α), subsumes I C D

/-- `C` is satisfiable. -/
def satisfiable (C : Concept) : Prop :=
  ∃ (α : Type) (I : Interp α) (a : α), C.eval I a

/-! ## Basic metatheory -/

open Concept in
theorem conj_sub_left (I : Interp α) (C D : Concept) : subsumes I (C ⊓ D) C :=
  fun _ h => h.1

open Concept in
theorem conj_sub_right (I : Interp α) (C D : Concept) : subsumes I (C ⊓ D) D :=
  fun _ h => h.2

open Concept in
theorem disj_super_left (I : Interp α) (C D : Concept) : subsumes I C (C ⊔ D) :=
  fun _ h => Or.inl h

open Concept in
theorem disj_super_right (I : Interp α) (C D : Concept) : subsumes I D (C ⊔ D) :=
  fun _ h => Or.inr h

open Concept in
theorem neg_neg (I : Interp α) (C : Concept) : equiv I (~ (~ C)) C :=
  fun _ => ⟨fun h => Classical.byContradiction (fun hn => h hn), fun h hn => hn h⟩

open Concept in
theorem de_morgan_conj (I : Interp α) (C D : Concept) :
    equiv I (~ (C ⊓ D)) (~ C ⊔ ~ D) :=
  fun _ => Classical.not_and_iff_not_or_not

open Concept in
theorem de_morgan_disj (I : Interp α) (C D : Concept) :
    equiv I (~ (C ⊔ D)) (~ C ⊓ ~ D) :=
  fun _ => not_or

end DescrLogic