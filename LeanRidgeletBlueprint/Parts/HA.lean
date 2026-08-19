import VersoManual
import VersoBlueprint
import LeanRidgeletBlueprint.Chapters.HA
import LeanRidgeletBlueprint.Chapters.OverviewHA
import LeanRidgeletBlueprint.Chapters.HARepresentations
import LeanRidgeletBlueprint.Chapters.HAAffine
import LeanRidgeletBlueprint.Chapters.HAArchitectures
import LeanRidgeletBlueprint.Chapters.HAQuadratic

open Verso.Doc
open Verso.Genre

namespace LeanRidgeletBlueprint.Parts.HA

set_option compiler.extract_closed false

attribute [local irreducible]
  LeanRidgeletBlueprint.Chapters.HA.«the canonical document object name»
  LeanRidgeletBlueprint.Chapters.OverviewHA.«the canonical document object name»
  LeanRidgeletBlueprint.Chapters.HARepresentations.«the canonical document object name»
  LeanRidgeletBlueprint.Chapters.HAAffine.«the canonical document object name»
  LeanRidgeletBlueprint.Chapters.HAArchitectures.«the canonical document object name»
  LeanRidgeletBlueprint.Chapters.HAQuadratic.«the canonical document object name»

/-- The cached harmonic-analysis subtree of the Blueprint, published since 2026-08-19. -/
opaque part : Part Manual :=
  { (%doc LeanRidgeletBlueprint.Chapters.HA) with
    subParts := #[
      (%doc LeanRidgeletBlueprint.Chapters.OverviewHA),
      (%doc LeanRidgeletBlueprint.Chapters.HARepresentations),
      (%doc LeanRidgeletBlueprint.Chapters.HAAffine),
      (%doc LeanRidgeletBlueprint.Chapters.HAArchitectures),
      (%doc LeanRidgeletBlueprint.Chapters.HAQuadratic)
    ] }

end LeanRidgeletBlueprint.Parts.HA

