import DescrLogic.Basic

namespace DescrLogic

/-- A finite interpretation: domain is `Fin n`, concepts and roles are decidable. -/
structure FinInterp (n : Nat) where
  /-- Interpretation of atomic concepts: which domain elements satisfy each concept. -/
  concept : CName → Fin n → Bool
  /-- Interpretation of roles: which pairs are related. -/
  role : RName → Fin n → Fin n → Bool

namespace FinInterp

variable {n : Nat} (I : FinInterp n)

/-- Evaluate a concept at a domain element. Fully computable. -/
def eval : Concept → Fin n → Bool
  | .top, _       => true
  | .bot, _       => false
  | .atom name, a => I.concept name a
  | .neg C, a     => !eval C a
  | .conj C D, a  => eval C a && eval D a
  | .disj C D, a  => eval C a || eval D a
  | .all r C, a   => (List.finRange n).all fun b => !I.role r a b || eval C b
  | .ex r C, a    => (List.finRange n).any fun b => I.role r a b && eval C b

/-- Extension of a concept: list of all domain elements satisfying it. -/
def extension (C : Concept) : List (Fin n) :=
  (List.finRange n).filter (I.eval C)

/-- Check if `C ⊑ D` holds in this interpretation. -/
def subsumes (C D : Concept) : Bool :=
  (List.finRange n).all fun a => !I.eval C a || I.eval D a

/-- Check if `C ≡ D` holds in this interpretation. -/
def equiv (C D : Concept) : Bool :=
  (List.finRange n).all fun a => I.eval C a == I.eval D a

/-- Check if `C` is satisfiable in this interpretation. -/
def satisfiable (C : Concept) : Bool :=
  (List.finRange n).any (I.eval C)

end FinInterp

/-! ## TBox and ABox -/

/-- A TBox axiom: concept inclusion. -/
structure TBoxAxiom where
  lhs : Concept
  rhs : Concept
  deriving Repr

/-- Notation: `C ⊑ D`. -/
scoped infix:50 " ⊑ " => TBoxAxiom.mk

/-- A TBox is a list of axioms. -/
abbrev TBox := List TBoxAxiom

/-- An ABox assertion. -/
inductive ABoxAssert where
  | conceptAssert : Fin n → Concept → ABoxAssert
  | roleAssert : Fin n → Fin n → RName → ABoxAssert
  deriving Repr

/-- Check if a finite interpretation satisfies a TBox. -/
def FinInterp.satisfiesTBox (I : FinInterp n) (T : TBox) : Bool :=
  T.all fun ax => I.subsumes ax.lhs ax.rhs

/-- Check if a finite interpretation satisfies an ABox concept assertion. -/
def FinInterp.satisfiesConceptAssert (I : FinInterp n) (a : Fin n) (C : Concept) : Bool :=
  I.eval C a

/-- Check if a finite interpretation satisfies an ABox role assertion. -/
def FinInterp.satisfiesRoleAssert (I : FinInterp n) (a b : Fin n) (r : RName) : Bool :=
  I.role r a b

end DescrLogic
