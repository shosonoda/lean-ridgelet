import VersoManual
import VersoBlueprint
import LeanRidgeletBlueprint.Blueprint
import LeanRidgeletBlueprint.Parts.L2
import LeanRidgeletBlueprint.Parts.L1
import LeanRidgeletBlueprint.Parts.FS
import LeanRidgeletBlueprint.Parts.ToMathlib
import LeanRidgeletBlueprint.PublicGenerated

open Verso.Doc
open Verso.Genre

namespace LeanRidgeletBlueprint

set_option compiler.extract_closed false

attribute [local irreducible]
  LeanRidgeletBlueprint.Blueprint.«the canonical document object name»
  LeanRidgeletBlueprint.PublicGenerated.«the canonical document object name»

/--
The *Dependency Graph* and *Blueprint Summary* generated from the public node registry. Only the
subparts are used; the carrier's wrapper title is discarded.
-/
private opaque generatedParts : Array (Part Manual) :=
  (%doc LeanRidgeletBlueprint.PublicGenerated).subParts

/-- The hierarchical public Blueprint; the development-only harmonic-analysis subtree is absent. -/
opaque assembledPublicBlueprint : Part Manual :=
  { (%doc LeanRidgeletBlueprint.Blueprint) with
    subParts := #[
      LeanRidgeletBlueprint.Parts.L2.part,
      LeanRidgeletBlueprint.Parts.L1.part,
      LeanRidgeletBlueprint.Parts.FS.part,
      LeanRidgeletBlueprint.Parts.ToMathlib.part
    ] ++ generatedParts }

end LeanRidgeletBlueprint
