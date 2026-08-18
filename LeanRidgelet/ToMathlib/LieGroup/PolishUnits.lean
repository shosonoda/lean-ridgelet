/-
Copyright (c) 2026 Sho Sonoda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sho Sonoda, OpenAI Codex
-/
module

public import Mathlib.Analysis.Normed.Ring.Units
public import Mathlib.Topology.MetricSpace.Polish

/-!
# Polish topology on unit groups

The units of a normed ring with summable geometric series form an open subspace of the ring.
Consequently the unit group is Polish whenever the ring is Polish.  This is the topology already
carried by `Rˣ`; no new topology is installed.
-/

@[expose] public section

noncomputable section

open Topology

namespace Units

variable {R : Type*} [NormedRing R] [HasSummableGeomSeries R]

/-- The unit group of a Polish normed ring with summable geometric series is Polish. -/
noncomputable instance instPolishSpaceOfNormedRing [PolishSpace R] : PolishSpace Rˣ := by
  letI : PolishSpace (Set.range (Units.val : Rˣ → R)) :=
    Units.isOpenEmbedding_val.isOpen_range.polishSpace
  exact Units.isOpenEmbedding_val.isEmbedding.toHomeomorph.isClosedEmbedding.polishSpace

end Units
