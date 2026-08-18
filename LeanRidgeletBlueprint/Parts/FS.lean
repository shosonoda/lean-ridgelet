import VersoManual
import VersoBlueprint
import LeanRidgeletBlueprint.Chapters.FS
import LeanRidgeletBlueprint.Chapters.OverviewFS
import LeanRidgeletBlueprint.Chapters.FSTheory

open Verso.Doc
open Verso.Genre

namespace LeanRidgeletBlueprint.Parts.FS

set_option compiler.extract_closed false

attribute [local irreducible]
  LeanRidgeletBlueprint.Chapters.FS.«the canonical document object name»
  LeanRidgeletBlueprint.Chapters.OverviewFS.«the canonical document object name»
  LeanRidgeletBlueprint.Chapters.FSTheory.«the canonical document object name»

/-- The cached Fourier-slice subtree of the Blueprint. -/
opaque part : Part Manual :=
  { (%doc LeanRidgeletBlueprint.Chapters.FS) with
    subParts := #[
      (%doc LeanRidgeletBlueprint.Chapters.OverviewFS),
      (%doc LeanRidgeletBlueprint.Chapters.FSTheory)
    ] }

end LeanRidgeletBlueprint.Parts.FS

