import VersoManual
import VersoBlueprint.PreviewManifest
import LeanRidgeletBlueprint.Assembly

open Verso Doc
open Verso.Genre Manual

def main (args : List String) : IO UInt32 :=
  Informal.PreviewManifest.blueprintMainWithPreviewData
    LeanRidgeletBlueprint.assembledBlueprint
    args
    (extensionImpls := by exact extension_impls%)
