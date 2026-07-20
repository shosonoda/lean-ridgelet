import VersoManual
import VersoBlueprint
import LeanRidgeletBlueprint.Blueprint
import LeanRidgeletBlueprint.Chapters.OverviewL2
import LeanRidgeletBlueprint.Chapters.Foundations
import LeanRidgeletBlueprint.Chapters.FourierDilation
import LeanRidgeletBlueprint.Chapters.Operators
import LeanRidgeletBlueprint.Chapters.GeneralSolution
import LeanRidgeletBlueprint.Chapters.Activations
import LeanRidgeletBlueprint.Chapters.FurtherResults

open Verso.Doc
open Verso.Genre

namespace LeanRidgeletBlueprint

set_option compiler.extract_closed false

attribute [local irreducible]
  LeanRidgeletBlueprint.Blueprint.«the canonical document object name»
  LeanRidgeletBlueprint.Chapters.OverviewL2.«the canonical document object name»
  LeanRidgeletBlueprint.Chapters.Foundations.«the canonical document object name»
  LeanRidgeletBlueprint.Chapters.FourierDilation.«the canonical document object name»
  LeanRidgeletBlueprint.Chapters.Operators.«the canonical document object name»
  LeanRidgeletBlueprint.Chapters.GeneralSolution.«the canonical document object name»
  LeanRidgeletBlueprint.Chapters.Activations.«the canonical document object name»
  LeanRidgeletBlueprint.Chapters.FurtherResults.«the canonical document object name»

private opaque overviewL2Part : Part Manual :=
  (%doc LeanRidgeletBlueprint.Chapters.OverviewL2)

private opaque foundationsPart : Part Manual :=
  (%doc LeanRidgeletBlueprint.Chapters.Foundations)

private opaque fourierDilationPart : Part Manual :=
  (%doc LeanRidgeletBlueprint.Chapters.FourierDilation)

private opaque operatorsPart : Part Manual :=
  (%doc LeanRidgeletBlueprint.Chapters.Operators)

private opaque generalSolutionPart : Part Manual :=
  (%doc LeanRidgeletBlueprint.Chapters.GeneralSolution)

private opaque activationsPart : Part Manual :=
  (%doc LeanRidgeletBlueprint.Chapters.Activations)

private opaque furtherResultsPart : Part Manual :=
  (%doc LeanRidgeletBlueprint.Chapters.FurtherResults)

/-- The seven-chapter Verso document tree used for public Blueprint output. -/
opaque assembledPublicBlueprint : Part Manual :=
  { (%doc LeanRidgeletBlueprint.Blueprint) with
    subParts := #[overviewL2Part, foundationsPart, fourierDilationPart, operatorsPart,
      generalSolutionPart, activationsPart, furtherResultsPart] }

end LeanRidgeletBlueprint
