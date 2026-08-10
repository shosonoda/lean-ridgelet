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
Carrier module for the two generated chapters, *Dependency Graph* and *Blueprint Summary*.

`{blueprint_graph}` and `{blueprint_summary}` read the Blueprint node registry out of the
environment, so they have to be elaborated somewhere that imports every chapter. They live here
rather than at the end of `LeanRidgeletBlueprint.Blueprint` because putting them in the module
named `LeanRidgeletBlueprint.Blueprint` specifically makes the build pathologically slow: the same
bytes under any other module name build in about ten seconds, while that one had not finished
after 28 minutes and 36 GB. Keep the two commands in this carrier module; if the build ever hangs
here again, renaming this module is the first thing to try.

`LeanRidgeletBlueprint.Assembly` takes only the subparts of this document, so the wrapper title and
this comment never reach the rendered output.

This carrier is the *development* one: it imports every chapter, whether published or not. The
public build has its own carrier, `LeanRidgeletBlueprint.PublicGenerated`, importing only the
published ones. The registry is read out of the environment, so a shared carrier would put a
development-only node into the public graph and summary. At present nothing is development-only and
the two carriers import the same chapters.

The graph options are chosen for this project's shape. Its 140 nodes fall into many small
components, so the default `TB` without packing lays them out in one row: a 11540 by 724 box, an
unreadable 16:1 sliver once it is scaled into the page canvas. `pack := true` alone gives 2.5:1 and
`direction := LR` with it gives 2654 by 2582, near square. Both stay adjustable at read time under
*Graph options*.
-/

#doc (Manual) "Generated chapters" =>

{blueprint_graph (direction := LR) (pack := true)}
{blueprint_summary}
