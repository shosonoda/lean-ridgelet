import Verso
import VersoManual
import VersoBlueprint
import VersoBlueprint.Commands.Graph
import VersoBlueprint.Commands.Summary
import LeanRidgeletBlueprint.Parts.L2
import LeanRidgeletBlueprint.Parts.L1
import LeanRidgeletBlueprint.Parts.FS
import LeanRidgeletBlueprint.Parts.ToMathlib

open Verso.Genre
open Verso.Genre.Manual
open Informal

set_option linter.hashCommand false
set_option maxRecDepth 100000

/-!
Public counterpart of `LeanRidgeletBlueprint.Generated`.

`{blueprint_graph}` and `{blueprint_summary}` read the Blueprint node registry out of the
environment, so what they draw is decided by what this module imports. This one imports the
published theory subtrees only; that is the whole reason it exists, and it is why the public graph
and summary cannot show the development-only harmonic-analysis nodes.

Keep the import list in step with `LeanRidgeletBlueprint.PublicAssembly`. The graph options and
the module-name caveat are as in `LeanRidgeletBlueprint.Generated`.
-/

#doc (Manual) "Generated chapters" =>

{blueprint_graph (direction := LR) (pack := true)}
{blueprint_summary}
