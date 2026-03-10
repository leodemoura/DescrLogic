import DescrLogic.Finite

namespace DescrLogic

/-- Individual name. -/
abbrev IName := String

/-- A knowledge base with named individuals and fact lists. -/
structure KB where
  individuals : Array IName
  conceptFacts : List (IName × CName)  -- (individual, concept)
  roleFacts : List (IName × RName × IName)  -- (source, role, target)

namespace KB

def size (kb : KB) : Nat := kb.individuals.size

/-- Resolve an individual name to its index. -/
def resolve (kb : KB) (name : IName) : Option (Fin kb.size) :=
  kb.individuals.findIdx? (· == name) |>.bind fun idx =>
    if h : idx < kb.size then some ⟨idx, h⟩ else none

/-- Compile the knowledge base into a `FinInterp`. -/
def toFinInterp (kb : KB) : FinInterp kb.size where
  concept cname i :=
    kb.conceptFacts.any fun (iname, cn) =>
      cn == cname && kb.resolve iname == some i
  role rname i j :=
    kb.roleFacts.any fun (src, rn, tgt) =>
      rn == rname && kb.resolve src == some i && kb.resolve tgt == some j

/-- Look up the name of a domain element. -/
def nameOf (kb : KB) (i : Fin kb.size) : IName :=
  kb.individuals[i.val]'(by simp [size] at i; exact i.isLt)

/-- Named extension: returns individual names instead of indices. -/
def extensionNames (kb : KB) (C : Concept) : List IName :=
  (kb.toFinInterp.extension C).map kb.nameOf

/-- Check subsumption. -/
def subsumes (kb : KB) (C D : Concept) : Bool :=
  kb.toFinInterp.subsumes C D

/-- Check equivalence. -/
def equiv (kb : KB) (C D : Concept) : Bool :=
  kb.toFinInterp.equiv C D

/-- Check satisfiability. -/
def satisfiable (kb : KB) (C : Concept) : Bool :=
  kb.toFinInterp.satisfiable C

/-- Check TBox satisfaction. -/
def satisfiesTBox (kb : KB) (T : TBox) : Bool :=
  kb.toFinInterp.satisfiesTBox T

end KB

end DescrLogic
