import VersoManual
import VersoBlueprint
import LeanRidgeletBlueprint.Blueprint
import LeanRidgeletBlueprint.Parts.L2
import LeanRidgeletBlueprint.Parts.L1
import LeanRidgeletBlueprint.Parts.FS
import LeanRidgeletBlueprint.Parts.HA
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

/--
The hierarchical public Blueprint. No theory subtree is development-only at present: the
harmonic-analysis subtree joined the published ones on 2026-08-19, as the Fourier-slice subtree did
on 2026-08-11 and the L1 subtree on 2026-08-05, so this assembly and
`LeanRidgeletBlueprint.assembledBlueprint` currently carry the same parts.  The two are kept apart
all the same: they are the mechanism by which the next unstable subtree stays out of the public
document, and collapsing them would have to be undone the moment one is added.
-/
opaque assembledPublicBlueprint : Part Manual :=
  { (%doc LeanRidgeletBlueprint.Blueprint) with
    subParts := #[
      LeanRidgeletBlueprint.Parts.L2.part,
      LeanRidgeletBlueprint.Parts.L1.part,
      LeanRidgeletBlueprint.Parts.FS.part,
      LeanRidgeletBlueprint.Parts.HA.part,
      LeanRidgeletBlueprint.Parts.ToMathlib.part
    ] ++ generatedParts }

end LeanRidgeletBlueprint
