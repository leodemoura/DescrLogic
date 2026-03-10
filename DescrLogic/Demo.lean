import DescrLogic.KB

namespace DescrLogic

open Concept

/-! ## A simple family ontology -/

/-- Shorthand for atomic concepts. -/
def c (name : String) : Concept := .atom name

def Person := c "Person"
def Parent := c "Parent"
def Female := c "Female"
def Male   := c "Male"

def hasChild : RName := "hasChild"

/-- Our family knowledge base. -/
def family : KB where
  individuals := #["Alice", "Bob", "Charlie", "Diana"]
  conceptFacts := [
    ("Alice",   "Person"), ("Alice",   "Female"), ("Alice",   "Parent"),
    ("Bob",     "Person"), ("Bob",     "Male"),   ("Bob",     "Parent"),
    ("Charlie", "Person"), ("Charlie", "Male"),
    ("Diana",   "Person"), ("Diana",   "Female")
  ]
  roleFacts := [
    ("Alice", "hasChild", "Charlie"),
    ("Bob",   "hasChild", "Diana")
  ]

/-! ## Queries that compute -/

-- Who is a Person?
#eval family.extensionNames Person
-- expected: ["Alice", "Bob", "Charlie", "Diana"]

-- Who is Female?
#eval family.extensionNames Female
-- expected: ["Alice", "Diana"]

-- Who is a Female Parent?
#eval family.extensionNames (Female ⊓ Parent)
-- expected: ["Alice"]

-- Who is Male or Female?
#eval family.extensionNames (Male ⊔ Female)
-- expected: ["Alice", "Bob", "Charlie", "Diana"]

-- Who has a female child? (∃ hasChild. Female)
#eval family.extensionNames (∃ᵣ hasChild, Female)
-- expected: ["Bob"]

-- Who has only male children? (∀ hasChild. Male)
#eval family.extensionNames (∀ᵣ hasChild, Male)
-- expected: ["Alice", "Charlie", "Diana"]

-- Who is not a Parent?
#eval family.extensionNames (~ Parent)
-- expected: ["Charlie", "Diana"]

/-! ## Subsumption checks -/

-- Female ⊓ Parent ⊑ Parent?
#eval family.subsumes (Female ⊓ Parent) Parent
-- expected: true

-- Parent ⊑ Female?
#eval family.subsumes Parent Female
-- expected: false

-- Does Male ⊓ Female have instances?
#eval family.satisfiable (Male ⊓ Female)
-- expected: false

-- Does Parent ⊓ ~ Female have instances?
#eval family.satisfiable (Parent ⊓ ~ Female)
-- expected: true (Bob)

/-! ## TBox reasoning -/

def familyTBox : TBox := [
  Parent ⊑ Person,
  (∃ᵣ hasChild, .top) ⊑ Parent
]

#eval family.satisfiesTBox familyTBox
-- expected: true

/-! ## Defined concepts -/

def Mother := Female ⊓ (∃ᵣ hasChild, .top)
def Father := Male ⊓ (∃ᵣ hasChild, .top)

#eval family.extensionNames Mother
-- expected: ["Alice"]

#eval family.extensionNames Father
-- expected: ["Bob"]

#eval family.subsumes Mother Parent
-- expected: true

#eval family.equiv Mother (Female ⊓ Parent)
-- expected: true

end DescrLogic
