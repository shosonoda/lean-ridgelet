import Verso
import VersoManual
import VersoBlueprint
import VersoBlueprint.Commands.Graph
import VersoBlueprint.Commands.Summary
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
import LeanRidgeletBlueprint.Chapters.ToMathlibLieGroup
import LeanRidgeletBlueprint.Chapters.OverviewFS
import LeanRidgeletBlueprint.Chapters.FSTheory

open Verso.Genre
open Verso.Genre.Manual
open Informal

set_option linter.hashCommand false
set_option maxRecDepth 100000

/-!
Public counterpart of `LeanRidgeletBlueprint.Generated`.

`{blueprint_graph}` and `{blueprint_summary}` read the Blueprint node registry out of the
environment, so what they draw is decided by what this module imports. This one imports the
published chapters only; that is the whole reason it exists, and it is why the public graph and
summary cannot show a development-only node. At present nothing is development-only, so it imports
the same chapters as `LeanRidgeletBlueprint.Generated`.

Keep the import list in step with `LeanRidgeletBlueprint.PublicAssembly`. The graph options and
the module-name caveat are as in `LeanRidgeletBlueprint.Generated`.
-/

#doc (Manual) "Generated chapters" =>

{blueprint_graph (direction := LR) (pack := true)}
{blueprint_summary}
