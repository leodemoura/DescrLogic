import DescrLogic

open DescrLogic
open Concept

def main : IO Unit := do
  IO.println "=== Description Logic (ALC) Demo ==="
  IO.println ""
  IO.println s!"Person:              {family.extensionNames Person}"
  IO.println s!"Female:              {family.extensionNames Female}"
  IO.println s!"Female ⊓ Parent:     {family.extensionNames (Female ⊓ Parent)}"
  IO.println s!"∃ hasChild. Female:  {family.extensionNames (∃ᵣ hasChild, Female)}"
  IO.println s!"∀ hasChild. Male:    {family.extensionNames (∀ᵣ hasChild, Male)}"
  IO.println s!"Mother:              {family.extensionNames Mother}"
  IO.println s!"Father:              {family.extensionNames Father}"
  IO.println ""
  IO.println s!"Female ⊓ Parent ⊑ Parent: {family.subsumes (Female ⊓ Parent) Parent}"
  IO.println s!"Parent ⊑ Female:          {family.subsumes Parent Female}"
  IO.println s!"Mother ⊑ Parent:          {family.subsumes Mother Parent}"
  IO.println s!"Male ⊓ Female satisfiable: {family.satisfiable (Male ⊓ Female)}"
  IO.println s!"TBox satisfied:            {family.satisfiesTBox familyTBox}"
