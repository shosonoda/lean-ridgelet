import VersoManual
import VersoBlueprint
import LeanRidgeletBlueprint.Chapters.L1
import LeanRidgeletBlueprint.Chapters.OverviewL1
import LeanRidgeletBlueprint.Chapters.L1Theory

open Verso.Doc
open Verso.Genre

namespace LeanRidgeletBlueprint.Parts.L1

set_option compiler.extract_closed false

attribute [local irreducible]
  LeanRidgeletBlueprint.Chapters.L1.«the canonical document object name»
  LeanRidgeletBlueprint.Chapters.OverviewL1.«the canonical document object name»
  LeanRidgeletBlueprint.Chapters.L1Theory.«the canonical document object name»

/-- The cached L1 subtree of the Blueprint. -/
opaque part : Part Manual :=
  { (%doc LeanRidgeletBlueprint.Chapters.L1) with
    subParts := #[
      (%doc LeanRidgeletBlueprint.Chapters.OverviewL1),
      (%doc LeanRidgeletBlueprint.Chapters.L1Theory)
    ] }

end LeanRidgeletBlueprint.Parts.L1

