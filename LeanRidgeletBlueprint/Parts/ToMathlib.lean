import VersoManual
import VersoBlueprint
import LeanRidgeletBlueprint.Chapters.ToMathlib
import LeanRidgeletBlueprint.Chapters.ToMathlibMeasureLp
import LeanRidgeletBlueprint.Chapters.ToMathlibRadonFourier
import LeanRidgeletBlueprint.Chapters.ToMathlibIntegralFourierTools
import LeanRidgeletBlueprint.Chapters.ToMathlibSchwartzConvolution
import LeanRidgeletBlueprint.Chapters.ToMathlibFiniteEuclidean
import LeanRidgeletBlueprint.Chapters.ToMathlibRepresentations
import LeanRidgeletBlueprint.Chapters.ToMathlibInvariantGeometry
import LeanRidgeletBlueprint.Chapters.ToMathlibSymmetricSpaces

open Verso.Doc
open Verso.Genre

namespace LeanRidgeletBlueprint.Parts.ToMathlib

set_option compiler.extract_closed false

attribute [local irreducible]
  LeanRidgeletBlueprint.Chapters.ToMathlib.«the canonical document object name»
  LeanRidgeletBlueprint.Chapters.ToMathlibMeasureLp.«the canonical document object name»
  LeanRidgeletBlueprint.Chapters.ToMathlibRadonFourier.«the canonical document object name»
  LeanRidgeletBlueprint.Chapters.ToMathlibIntegralFourierTools.«the canonical document object name»
  LeanRidgeletBlueprint.Chapters.ToMathlibSchwartzConvolution.«the canonical document object name»
  LeanRidgeletBlueprint.Chapters.ToMathlibFiniteEuclidean.«the canonical document object name»
  LeanRidgeletBlueprint.Chapters.ToMathlibRepresentations.«the canonical document object name»
  LeanRidgeletBlueprint.Chapters.ToMathlibInvariantGeometry.«the canonical document object name»
  LeanRidgeletBlueprint.Chapters.ToMathlibSymmetricSpaces.«the canonical document object name»

/-- The cached Mathlib-upstream subtree of the Blueprint. -/
opaque part : Part Manual :=
  { (%doc LeanRidgeletBlueprint.Chapters.ToMathlib) with
    subParts := #[
      (%doc LeanRidgeletBlueprint.Chapters.ToMathlibMeasureLp),
      (%doc LeanRidgeletBlueprint.Chapters.ToMathlibRadonFourier),
      (%doc LeanRidgeletBlueprint.Chapters.ToMathlibIntegralFourierTools),
      (%doc LeanRidgeletBlueprint.Chapters.ToMathlibSchwartzConvolution),
      (%doc LeanRidgeletBlueprint.Chapters.ToMathlibFiniteEuclidean),
      (%doc LeanRidgeletBlueprint.Chapters.ToMathlibRepresentations),
      (%doc LeanRidgeletBlueprint.Chapters.ToMathlibInvariantGeometry),
      (%doc LeanRidgeletBlueprint.Chapters.ToMathlibSymmetricSpaces)
    ] }

end LeanRidgeletBlueprint.Parts.ToMathlib

