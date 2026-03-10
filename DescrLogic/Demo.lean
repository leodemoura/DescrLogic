import DescrLogic.Syntax

namespace DescrLogic

open Concept

/-! ## A simple family ontology -/

concept Person
concept Parent
concept Female
concept Male

role hasChild

knowledge family where
  Alice   : Person, Female, Parent
  Bob     : Person, Male, Parent
  Charlie : Person, Male
  Diana   : Person, Female
  Alice hasChild Charlie
  Bob hasChild Diana

/-! ## Queries that compute -/

#eval family.extensionNames Person
-- ["Alice", "Bob", "Charlie", "Diana"]

#eval family.extensionNames Female
-- ["Alice", "Diana"]

#eval family.extensionNames (Female ⊓ Parent)
-- ["Alice"]

#eval family.extensionNames (Male ⊔ Female)
-- ["Alice", "Bob", "Charlie", "Diana"]

-- Who has a female child?
#eval family.extensionNames (∃ᵣ hasChild, Female)
-- ["Bob"]

-- Who has only male children?
#eval family.extensionNames (∀ᵣ hasChild, Male)
-- ["Alice", "Charlie", "Diana"]

#eval family.extensionNames (~ Parent)
-- ["Charlie", "Diana"]

/-! ## Subsumption checks -/

#eval family.subsumes (Female ⊓ Parent) Parent   -- true
#eval family.subsumes Parent Female               -- false
#eval family.satisfiable (Male ⊓ Female)          -- false
#eval family.satisfiable (Parent ⊓ ~ Female)      -- true (Bob)

/-! ## TBox reasoning -/

def familyTBox : TBox := [
  Parent ⊑ Person,
  (∃ᵣ hasChild, .top) ⊑ Parent
]

#eval family.satisfiesTBox familyTBox  -- true

/-! ## Defined concepts -/

def Mother := Female ⊓ (∃ᵣ hasChild, .top)
def Father := Male ⊓ (∃ᵣ hasChild, .top)

#eval family.extensionNames Mother  -- ["Alice"]
#eval family.extensionNames Father  -- ["Bob"]

#eval family.subsumes Mother Parent              -- true
#eval family.equiv Mother (Female ⊓ Parent)      -- true

end DescrLogic
