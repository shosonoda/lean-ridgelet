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
import LeanRidgeletBlueprint.Chapters.OverviewL1
import LeanRidgeletBlueprint.Chapters.L1Theory
import LeanRidgeletBlueprint.Chapters.ToMathlib
import LeanRidgeletBlueprint.Generated

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
  LeanRidgeletBlueprint.Chapters.OverviewL1.«the canonical document object name»
  LeanRidgeletBlueprint.Chapters.L1Theory.«the canonical document object name»
  LeanRidgeletBlueprint.Chapters.ToMathlib.«the canonical document object name»
  LeanRidgeletBlueprint.Generated.«the canonical document object name»

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

private opaque overviewL1Part : Part Manual :=
  (%doc LeanRidgeletBlueprint.Chapters.OverviewL1)

private opaque l1TheoryPart : Part Manual :=
  (%doc LeanRidgeletBlueprint.Chapters.L1Theory)

private opaque toMathlibPart : Part Manual :=
  (%doc LeanRidgeletBlueprint.Chapters.ToMathlib)

/--
The *Dependency Graph* and *Blueprint Summary* chapters, which `{blueprint_graph}` and
`{blueprint_summary}` build from the node registry in `LeanRidgeletBlueprint.Generated`. That
module exists only to carry the two commands: they must be elaborated somewhere that imports every
chapter, and putting them in `Blueprint.lean` itself makes the build pathologically slow, as its
module docstring records. Only the subparts are used; the wrapper title is discarded.
-/
private opaque generatedParts : Array (Part Manual) :=
  (%doc LeanRidgeletBlueprint.Generated).subParts

/-- The standard Verso document tree used for multi-page Blueprint output. -/
opaque assembledBlueprint : Part Manual :=
  { (%doc LeanRidgeletBlueprint.Blueprint) with
    subParts := #[overviewL2Part, foundationsPart, fourierDilationPart, operatorsPart,
      generalSolutionPart, activationsPart, furtherResultsPart, overviewL1Part,
      l1TheoryPart, toMathlibPart] ++ generatedParts }

end LeanRidgeletBlueprint
