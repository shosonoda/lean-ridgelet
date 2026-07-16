import Verso
import VersoManual
import VersoBlueprint

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Lean Ridgelet Blueprint" =>

This Blueprint connects the mathematical development of integral-representation neural networks
and ridgelet transforms with the declarations in `LeanRidgelet`. The chapters follow the dependency
structure of the Lean development rather than the publication order of the source manuscript.

1. [Fourier conventions and Hilbert spaces](../chapters/foundations/html-multi/index.html)
2. [Fourier--dilation coordinates](../chapters/fourier-dilation/html-multi/index.html)
3. [Synthesis, ridgelets, and reconstruction](../chapters/operators/html-multi/index.html)
4. [Null space and the general solution](../chapters/general-solution/html-multi/index.html)
5. [Standard activation functions](../chapters/activations/html-multi/index.html)
6. [Further results from the source manuscript](../chapters/further-results/html-multi/index.html)

Each chapter is rendered separately so that strict Lean declaration resolution and previews remain
fast enough for routine local development. A node without an associated Lean declaration records
work that remains to be formalized; it does not introduce an assumption into the Lean development.

The generated [doc-gen4 API documentation](../../../docbuild/.lake/build/doc/index.html) provides
the complementary module and declaration index for the complete `LeanRidgelet` library.
