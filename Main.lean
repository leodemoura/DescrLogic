import DescrLogic

open DescrLogic
open Concept

def main : IO Unit := do
  IO.println "=== Description Logic (ALC) Demo ==="
  IO.println ""
  IO.println s!"Person extension:        {familyInterp.extension Person}"
  IO.println s!"Female extension:        {familyInterp.extension Female}"
  IO.println s!"Female ⊓ Parent:         {familyInterp.extension (Female ⊓ Parent)}"
  IO.println s!"∃ hasChild. Female:      {familyInterp.extension (∃ᵣ hasChild, Female)}"
  IO.println s!"∀ hasChild. Male:        {familyInterp.extension (∀ᵣ hasChild, Male)}"
  IO.println s!"Mother (Female ⊓ ∃ hasChild. ⊤): {familyInterp.extension Mother}"
  IO.println s!"Father (Male ⊓ ∃ hasChild. ⊤):   {familyInterp.extension Father}"
  IO.println ""
  IO.println s!"Female ⊓ Parent ⊑ Parent: {familyInterp.subsumes (Female ⊓ Parent) Parent}"
  IO.println s!"Parent ⊑ Female:          {familyInterp.subsumes Parent Female}"
  IO.println s!"Mother ⊑ Parent:          {familyInterp.subsumes Mother Parent}"
  IO.println s!"Male ⊓ Female satisfiable: {familyInterp.satisfiable (Male ⊓ Female)}"
  IO.println ""
  IO.println s!"TBox satisfied: {familyInterp.satisfiesTBox familyTBox}"
