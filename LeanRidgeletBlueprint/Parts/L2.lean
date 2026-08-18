import VersoManual
import VersoBlueprint
import LeanRidgeletBlueprint.Chapters.L2
import LeanRidgeletBlueprint.Chapters.OverviewL2
import LeanRidgeletBlueprint.Chapters.Foundations
import LeanRidgeletBlueprint.Chapters.FourierDilation
import LeanRidgeletBlueprint.Chapters.Operators
import LeanRidgeletBlueprint.Chapters.GeneralSolution
import LeanRidgeletBlueprint.Chapters.Activations
import LeanRidgeletBlueprint.Chapters.FurtherResults

open Verso.Doc
open Verso.Genre

namespace LeanRidgeletBlueprint.Parts.L2

set_option compiler.extract_closed false

attribute [local irreducible]
  LeanRidgeletBlueprint.Chapters.L2.«the canonical document object name»
  LeanRidgeletBlueprint.Chapters.OverviewL2.«the canonical document object name»
  LeanRidgeletBlueprint.Chapters.Foundations.«the canonical document object name»
  LeanRidgeletBlueprint.Chapters.FourierDilation.«the canonical document object name»
  LeanRidgeletBlueprint.Chapters.Operators.«the canonical document object name»
  LeanRidgeletBlueprint.Chapters.GeneralSolution.«the canonical document object name»
  LeanRidgeletBlueprint.Chapters.Activations.«the canonical document object name»
  LeanRidgeletBlueprint.Chapters.FurtherResults.«the canonical document object name»

/-- The cached L2 subtree of the Blueprint. -/
opaque part : Part Manual :=
  { (%doc LeanRidgeletBlueprint.Chapters.L2) with
    subParts := #[
      (%doc LeanRidgeletBlueprint.Chapters.OverviewL2),
      (%doc LeanRidgeletBlueprint.Chapters.Foundations),
      (%doc LeanRidgeletBlueprint.Chapters.FourierDilation),
      (%doc LeanRidgeletBlueprint.Chapters.Operators),
      (%doc LeanRidgeletBlueprint.Chapters.GeneralSolution),
      (%doc LeanRidgeletBlueprint.Chapters.Activations),
      (%doc LeanRidgeletBlueprint.Chapters.FurtherResults)
    ] }

end LeanRidgeletBlueprint.Parts.L2

