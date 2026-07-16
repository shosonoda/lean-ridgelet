import VersoManual
import VersoBlueprint.PreviewManifest
import LeanRidgeletBlueprint.Chapters.Overview
import LeanRidgeletBlueprint.Chapters.Foundations
import LeanRidgeletBlueprint.Chapters.FourierDilation
import LeanRidgeletBlueprint.Chapters.Operators
import LeanRidgeletBlueprint.Chapters.GeneralSolution
import LeanRidgeletBlueprint.Chapters.Activations
import LeanRidgeletBlueprint.Chapters.FurtherResults

open Verso Doc
open Verso.Genre Manual

private def overviewMain (args : List String) : IO UInt32 :=
  Informal.PreviewManifest.blueprintMainWithPreviewData
    (%doc LeanRidgeletBlueprint.Chapters.Overview)
    args
    (extensionImpls := by exact extension_impls%)

private def foundationsMain (args : List String) : IO UInt32 :=
  Informal.PreviewManifest.blueprintMainWithPreviewData
    (%doc LeanRidgeletBlueprint.Chapters.Foundations)
    args
    (extensionImpls := by exact extension_impls%)

private def fourierDilationMain (args : List String) : IO UInt32 :=
  Informal.PreviewManifest.blueprintMainWithPreviewData
    (%doc LeanRidgeletBlueprint.Chapters.FourierDilation)
    args
    (extensionImpls := by exact extension_impls%)

private def operatorsMain (args : List String) : IO UInt32 :=
  Informal.PreviewManifest.blueprintMainWithPreviewData
    (%doc LeanRidgeletBlueprint.Chapters.Operators)
    args
    (extensionImpls := by exact extension_impls%)

private def generalSolutionMain (args : List String) : IO UInt32 :=
  Informal.PreviewManifest.blueprintMainWithPreviewData
    (%doc LeanRidgeletBlueprint.Chapters.GeneralSolution)
    args
    (extensionImpls := by exact extension_impls%)

private def activationsMain (args : List String) : IO UInt32 :=
  Informal.PreviewManifest.blueprintMainWithPreviewData
    (%doc LeanRidgeletBlueprint.Chapters.Activations)
    args
    (extensionImpls := by exact extension_impls%)

private def furtherResultsMain (args : List String) : IO UInt32 :=
  Informal.PreviewManifest.blueprintMainWithPreviewData
    (%doc LeanRidgeletBlueprint.Chapters.FurtherResults)
    args
    (extensionImpls := by exact extension_impls%)

def main (args : List String) : IO UInt32 :=
  match args with
  | "overview" :: rest => overviewMain rest
  | "foundations" :: rest => foundationsMain rest
  | "fourier-dilation" :: rest => fourierDilationMain rest
  | "operators" :: rest => operatorsMain rest
  | "general-solution" :: rest => generalSolutionMain rest
  | "activations" :: rest => activationsMain rest
  | "further-results" :: rest => furtherResultsMain rest
  | chapter :: _ => do
      IO.eprintln s!"unknown Blueprint chapter: {chapter}"
      return 1
  | [] => do
      IO.eprintln "a Blueprint chapter name is required"
      return 1
