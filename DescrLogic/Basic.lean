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

/-! ## Subsumption-unsatisfiability reduction

The foundational result in DL reasoning: checking C ⊑ D reduces to
checking that C ⊓ ¬D is unsatisfiable. All tableau-based DL reasoners
rely on this. -/

open Concept in
theorem valid_subsumes_iff_unsat (C D : Concept) :
    validSubsumes C D ↔ ¬ satisfiable (C ⊓ ~ D) := by
  constructor
  · intro h ⟨α, I, a, hC, hD⟩
    exact hD (h α I a hC)
  · intro h α I a hC
    exact Classical.byContradiction fun hD => h ⟨α, I, a, hC, hD⟩

/-! ## Modal duality

ALC is multi-modal K. These are the duality laws between
universal and existential restrictions — the DL analogues of
the □/◇ duality in modal logic. -/

open Concept in
theorem exist_neg_dual (I : Interp α) (r : RName) (C : Concept) :
    equiv I (~ (∃ᵣ r, C)) (∀ᵣ r, ~ C) :=
  fun _ =>
    ⟨fun h b hr hc => h ⟨b, hr, hc⟩,
     fun h ⟨b, hr, hc⟩ => h b hr hc⟩

open Concept in
theorem all_neg_dual (I : Interp α) (r : RName) (C : Concept) :
    equiv I (~ (∀ᵣ r, C)) (∃ᵣ r, ~ C) :=
  fun _ =>
    ⟨fun h => Classical.byContradiction fun hne =>
       h fun b hr => Classical.byContradiction fun hc => hne ⟨b, hr, hc⟩,
     fun ⟨b, hr, hc⟩ h => hc (h b hr)⟩

/-! ## Monotonicity of restrictions

If C ⊑ D in an interpretation, then ∃r.C ⊑ ∃r.D and ∀r.C ⊑ ∀r.D. -/

open Concept in
theorem exist_mono (I : Interp α) (r : RName) (C D : Concept)
    (h : subsumes I C D) : subsumes I (∃ᵣ r, C) (∃ᵣ r, D) :=
  fun _ ⟨b, hr, hc⟩ => ⟨b, hr, h b hc⟩

open Concept in
theorem all_mono (I : Interp α) (r : RName) (C D : Concept)
    (h : subsumes I C D) : subsumes I (∀ᵣ r, C) (∀ᵣ r, D) :=
  fun _ ha b hr => h b (ha b hr)

/-! ## Distributivity

∀r distributes over ⊓, and ∃r distributes over ⊔.
The converses (∃r over ⊓, ∀r over ⊔) only hold in one direction. -/

open Concept in
theorem all_conj_distrib (I : Interp α) (r : RName) (C D : Concept) :
    equiv I (∀ᵣ r, C ⊓ D) ((∀ᵣ r, C) ⊓ (∀ᵣ r, D)) :=
  fun _ =>
    ⟨fun h => ⟨fun b hr => (h b hr).1, fun b hr => (h b hr).2⟩,
     fun ⟨hc, hd⟩ b hr => ⟨hc b hr, hd b hr⟩⟩

open Concept in
theorem exist_disj_distrib (I : Interp α) (r : RName) (C D : Concept) :
    equiv I (∃ᵣ r, C ⊔ D) ((∃ᵣ r, C) ⊔ (∃ᵣ r, D)) :=
  fun _ =>
    ⟨fun ⟨b, hr, hcd⟩ => hcd.elim (fun hc => Or.inl ⟨b, hr, hc⟩)
                                     (fun hd => Or.inr ⟨b, hr, hd⟩),
     fun h => h.elim (fun ⟨b, hr, hc⟩ => ⟨b, hr, Or.inl hc⟩)
                     (fun ⟨b, hr, hd⟩ => ⟨b, hr, Or.inr hd⟩)⟩

open Concept in
/-- ∃r does NOT distribute over ⊓ — only one direction holds. -/
theorem exist_conj_sub (I : Interp α) (r : RName) (C D : Concept) :
    subsumes I (∃ᵣ r, C ⊓ D) ((∃ᵣ r, C) ⊓ (∃ᵣ r, D)) :=
  fun _ ⟨b, hr, hc, hd⟩ => ⟨⟨b, hr, hc⟩, ⟨b, hr, hd⟩⟩

open Concept in
/-- ∀r does NOT distribute over ⊔ — only one direction holds. -/
theorem all_disj_super (I : Interp α) (r : RName) (C D : Concept) :
    subsumes I ((∀ᵣ r, C) ⊔ (∀ᵣ r, D)) (∀ᵣ r, C ⊔ D) :=
  fun _ h b hr => h.elim (fun hc => Or.inl (hc b hr)) (fun hd => Or.inr (hd b hr))

end DescrLogic