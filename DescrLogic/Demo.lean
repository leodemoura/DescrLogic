import DescrLogic.Finite

namespace DescrLogic

open Concept

/-! ## A simple family ontology

Domain: `Fin 4` representing {Alice=0, Bob=1, Charlie=2, Diana=3}

Concepts: Person, Parent, Female, Male
Roles: hasChild
-/

/-- Shorthand for atomic concepts. -/
def c (name : String) : Concept := .atom name

def Person := c "Person"
def Parent := c "Parent"
def Female := c "Female"
def Male   := c "Male"

def hasChild : RName := "hasChild"

/-- Our family interpretation over 4 individuals. -/
def familyInterp : FinInterp 4 where
  concept name i := match name, i.val with
    | "Person", _ => true       -- everyone is a person
    | "Female", 0 => true       -- Alice is female
    | "Female", 3 => true       -- Diana is female
    | "Male",   1 => true       -- Bob is male
    | "Male",   2 => true       -- Charlie is male
    | "Parent", 0 => true       -- Alice is a parent
    | "Parent", 1 => true       -- Bob is a parent
    | _, _ => false
  role name i j := match name, i.val, j.val with
    | "hasChild", 0, 2 => true  -- Alice hasChild Charlie
    | "hasChild", 1, 3 => true  -- Bob hasChild Diana
    | _, _, _ => false

/-! ## Queries that compute -/

-- Who is a Person?
#eval familyInterp.extension Person
-- expected: [0, 1, 2, 3]

-- Who is Female?
#eval familyInterp.extension Female
-- expected: [0, 3]

-- Who is a Female Parent?
#eval familyInterp.extension (Female ⊓ Parent)
-- expected: [0]  (Alice)

-- Who is Male or Female?
#eval familyInterp.extension (Male ⊔ Female)
-- expected: [0, 1, 2, 3]

-- Who has a female child? (∃ hasChild. Female)
#eval familyInterp.extension (∃ᵣ hasChild, Female)
-- expected: [1]  (Bob, since Diana is female)

-- Who has only male children? (∀ hasChild. Male)
#eval familyInterp.extension (∀ᵣ hasChild, Male)
-- expected: [0, 2, 3]  (Alice's child Charlie is male; Charlie and Diana have no children, so vacuously true)

-- Who is not a Parent?
#eval familyInterp.extension (~ Parent)
-- expected: [2, 3]

/-! ## Subsumption checks -/

-- Female ⊓ Parent ⊑ Parent?
#eval familyInterp.subsumes (Female ⊓ Parent) Parent
-- expected: true

-- Parent ⊑ Female?
#eval familyInterp.subsumes Parent Female
-- expected: false (Bob is a Parent but not Female)

-- Does the concept (Male ⊓ Female) have instances?
#eval familyInterp.satisfiable (Male ⊓ Female)
-- expected: false

-- Does (Parent ⊓ ~ Female) have instances?
#eval familyInterp.satisfiable (Parent ⊓ ~ Female)
-- expected: true (Bob)

/-! ## TBox reasoning -/

def familyTBox : TBox := [
  Parent ⊑ Person,                       -- Parents are Persons
  (∃ᵣ hasChild, .top) ⊑ Parent           -- Having a child makes you a Parent
]

-- Does our interpretation satisfy the TBox?
#eval familyInterp.satisfiesTBox familyTBox
-- expected: true

/-! ## A richer concept: Mother = Female ⊓ ∃ hasChild. ⊤ -/

def Mother := Female ⊓ (∃ᵣ hasChild, .top)

#eval familyInterp.extension Mother
-- expected: [0]  (Alice)

def Father := Male ⊓ (∃ᵣ hasChild, .top)

#eval familyInterp.extension Father
-- expected: [1]  (Bob)

-- Mother ⊑ Parent?
#eval familyInterp.subsumes Mother Parent
-- expected: true

-- Mother ≡ Female ⊓ Parent?
#eval familyInterp.equiv Mother (Female ⊓ Parent)
-- expected: true (in this interpretation)

end DescrLogic
