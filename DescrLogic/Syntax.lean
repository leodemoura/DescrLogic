import Lean
import DescrLogic.KB

namespace DescrLogic

open Lean

/-- `concept Person` expands to `def Person : Concept := .atom "Person"` -/
scoped syntax "concept " ident : command

macro_rules
  | `(concept $n:ident) =>
    let s := quote n.getId.toString
    `(def $n : Concept := .atom $s)

/-- `role hasChild` expands to `def hasChild : RName := "hasChild"` -/
scoped syntax "role " ident : command

macro_rules
  | `(role $n:ident) =>
    let s := quote n.getId.toString
    `(def $n : RName := $s)

/-- Knowledge base entry: concept membership or role assertion. -/
declare_syntax_cat kbEntry
syntax ident " : " ident,+ : kbEntry           -- Alice : Person, Female, Parent
syntax ident ident ident : kbEntry              -- Alice hasChild Charlie

/--
Declare a knowledge base:
```
knowledge family where
  Alice : Person, Female, Parent
  Bob : Person, Male
  Alice hasChild Charlie
```
Individuals are collected automatically from all entries.
-/
scoped syntax "knowledge " ident " where " kbEntry* : command

macro_rules
  | `(knowledge $name:ident where $entries:kbEntry*) => do
    let mut individuals : Array String := #[]
    let mut conceptFacts : Array (TSyntax `term) := #[]
    let mut roleFacts : Array (TSyntax `term) := #[]
    let addInd (arr : Array String) (s : String) : Array String :=
      if arr.contains s then arr else arr.push s
    for entry in entries do
      match entry with
      | `(kbEntry| $ind:ident : $[$concepts:ident],*) =>
        let indName := ind.getId.toString
        individuals := addInd individuals indName
        for c in concepts do
          let cName := c.getId.toString
          conceptFacts := conceptFacts.push (← `(($(quote indName), $(quote cName))))
      | `(kbEntry| $a:ident $r:ident $b:ident) =>
        let aName := a.getId.toString
        let rName := r.getId.toString
        let bName := b.getId.toString
        individuals := addInd individuals aName
        individuals := addInd individuals bName
        roleFacts := roleFacts.push (← `(($(quote aName), $(quote rName), $(quote bName))))
      | _ => Macro.throwError "invalid knowledge base entry"
    let indStxs := individuals.map (quote (k := `term) ·)
    `(def $name : KB where
        individuals := #[$[$indStxs],*]
        conceptFacts := [$[$conceptFacts],*]
        roleFacts := [$[$roleFacts],*])

end DescrLogic
