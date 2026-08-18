import LeanRidgeletBlueprint.Chapters.ToMathlibRadonFourier
import LeanRidgelet.ToMathlib.CyclicFourier
import LeanRidgelet.ToMathlib.DPlaneTransform
import LeanRidgelet.ToMathlib.DiagonalScaling
import LeanRidgelet.ToMathlib.IteratedFubini
import Verso
import VersoManual
import VersoBlueprint

open Verso.Genre
open Verso.Genre.Manual
open Informal

set_option linter.hashCommand false
-- Verso directive headers and display mathematics must stay on one physical line.
set_option linter.style.longLine false
set_option verso.blueprint.externalCode.strictResolve true

#doc (Manual) "Mathlib candidates: finite Fourier and Euclidean geometry" =>
%%%
file := "finite-euclidean"
%%%

Finite Fourier inversion, the higher-codimension `d`-plane transform, diagonal changes of variables, and a triple-integral Fubini bridge.

*Finite Fourier analysis*

:::theorem "mathlib_cyclic_fourier" (lean := "AddChar.map_finsetSum, ZMod.sum_stdAddChar_mul, ZMod.norm_stdAddChar, ZMod.conj_stdAddChar, ZMod.sum_dft_mul_dft_mul_stdAddChar, ZMod.piDFT, ZMod.piDFT_apply_zero, ZMod.sum_stdAddChar_dotProduct, ZMod.sum_stdAddChar_smul_piDFT, ZMod.piDFT_inversion")
*The discrete Fourier transform on a product of cyclic groups.* Mathlib's `ZMod.dft` covers a single cyclic group `ZMod N` together with its inversion formula, but neither the transform on $`\iota\to\mathbb Z/N\mathbb Z` with the dot-product pairing, which is what one needs whenever $`(\mathbb Z/N\mathbb Z)^m` stands in for a discretized Euclidean space, nor a convolution theorem for the one-dimensional transform. Both are proved here. Everything rests on orthogonality of characters on a product,
$$`\sum_{\xi}\mathrm e(\xi\cdot t)=\begin{cases}N^{|\iota|}&t=0\\0&t\neq0,\end{cases}`
which follows by factoring the character of a dot product over the coordinates — an additive character carries a finite sum to a finite product, the first declaration — and reducing to the one-dimensional statement, itself the public form of a computation Mathlib currently performs inline inside a private proof. Inversion is stated as $`\sum_\xi\mathrm e(\xi\cdot x)\widehat f(\xi)=N^{|\iota|}f(x)`, avoiding division. The convolution theorem takes the matching form $`\sum_\omega\widehat u(\omega)\widehat v(\omega)\mathrm e(\omega t)=N\sum_bu(b)v(t-b)`. Along the way the standard character is recorded as unimodular, so that conjugating it negates its argument.
:::

:::theorem "mathlib_dplane_transform" (lean := "MeasureTheory.planeOrthogonalSplit, MeasureTheory.measurePreserving_planeOrthogonalSplit, MeasureTheory.inner_planeOrthogonalSplit, MeasureTheory.dPlaneTransform, MeasureTheory.integrable_comp_planeOrthogonalSplit, MeasureTheory.ae_integrable_dPlaneTransform_section, MeasureTheory.integrable_dPlaneTransform, MeasureTheory.integral_dPlaneTransform, MeasureTheory.fourier_slice_dPlaneTransform, MeasureTheory.frameVectorCodimOne, MeasureTheory.norm_frameVectorCodimOne, MeasureTheory.eq_smul_single_fin_one, MeasureTheory.apply_eq_smul_frameVectorCodimOne, MeasureTheory.range_eq_span_frameVectorCodimOne, MeasureTheory.dPlaneTransform_codimOne, MeasureTheory.norm_eq_abs_apply_fin_one, MeasureTheory.frameOfUnitVector, MeasureTheory.frameOfUnitVector_apply, MeasureTheory.frameVectorCodimOne_frameOfUnitVector, MeasureTheory.frameOfUnitVector_frameVectorCodimOne, MeasureTheory.unitVectorFinOne, MeasureTheory.coe_unitVectorFinOne, MeasureTheory.integral_euclideanSpace_fin_one") (uses := "mathlib_radon_transform, mathlib_fourier_slice")
*The `d`-plane transform and its Fourier slice theorem.* The `d`-plane transform integrates over a `d`-dimensional affine subspace, parametrized by an orthonormal `k`-frame presented as a linear isometry $`L:\mathbb R^k\to E` with $`k=m-d`:
$$`P_d[f](L,\boldsymbol b)=\int_{(\operatorname{range}L)^\perp}f(L\boldsymbol b+y)\,\mathrm dy.`
At $`k=1` it *is* the Radon transform above — a codimension-one frame is a unit vector, its range is the line through that vector, and the last declaration is the resulting identity `dPlaneTransform f L b = radonTransform f (L e₀) (b 0)` — and at $`k=m-1` it is the X-ray transform; Mathlib has neither it nor its slice theorem in any codimension. Both are proved here exactly as in the $`k=1` case: the parametrization $`(\boldsymbol b,y)\mapsto L\boldsymbol b+y` of `E` by the range of the frame and its orthogonal complement is a linear isometry equivalence, hence measure preserving, and the rest is Fubini. The `L¹` theory and the Fubini corollary $`\int P_d[f](L,\boldsymbol b)\,\mathrm d\boldsymbol b=\int f` come with it, and the *Fourier slice theorem* reads
$$`\mathcal Ff(L\boldsymbol\omega)=\mathcal F\bigl(P_d[f](L,\cdot)\bigr)(\boldsymbol\omega).`
It needs no measure on the space of frames, being a statement at a fixed frame; an invariant measure on the Stiefel manifold is needed only for the inversion formula.
:::

The identification at $`k=1` is recorded in both directions: a codimension-one frame is a unit vector, and a unit vector is the frame $`\boldsymbol b\mapsto b_0\boldsymbol u` that scales it. So the Stiefel manifold $`V_{m,1}` *is* the sphere $`\mathbb S^{m-1}` as a set; that it is the sphere as a measure space is `mathlib_stiefel_codim_one`. The bias space of a codimension-one frame is $`\mathbb R^1`, and integration over it is integration over $`\mathbb R` — the only coordinate is a measure-preserving equivalence, obtained by composing Mathlib's identification of $`\mathbb R^1` with $`\iota\to\mathbb R` at $`|\iota|=1` with the projection out of a singleton product.

:::theorem "mathlib_diagonal_scaling" (lean := "MeasureTheory.diagScale, MeasureTheory.diagScale_apply, MeasureTheory.det_diagScale, MeasureTheory.diagScaleEquiv, MeasureTheory.diagScaleMeasurableEquiv, MeasureTheory.coe_diagScaleMeasurableEquiv, MeasureTheory.integral_comp_diagScale")
*Coordinatewise scaling of $`\mathbb R^k`.* Mathlib has the one-dimensional change of variables $`x\mapsto cx` and, at the level of measures, the rescaling of an additive Haar measure by an arbitrary linear map; what is missing is the integral form of the change of variables in all `k` coordinates at once,
$$`\int_{\mathbb R^k}G(w_1d_1,\ldots,w_kd_k)\,\mathrm d\boldsymbol d=\Bigl(\prod_i|w_i|\Bigr)^{-1}\int_{\mathbb R^k}G(\boldsymbol y)\,\mathrm d\boldsymbol y.`
That is what a `k`-fold scale parameter produces — the diagonal factor of a singular value decomposition, where the `k` singular values are traded against the `k` coordinates of a frequency. The proof composes the two facts above: the diagonal map is a linear equivalence when no entry vanishes, its determinant is $`\prod_iw_i`, and the Haar rescaling transports the integral. There is no hypothesis on the integrand, the substitution being along a measurable equivalence.
:::

:::lemma_ "mathlib_iterated_fubini" (lean := "MeasureTheory.integral_integral_integral_swap_left, MeasureTheory.integral_integral_integral_swap_right")
*Fubini for triple iterated integrals.* Mathlib's `integral_integral_swap` exchanges the two integrals of a doubly iterated Bochner integral; nothing there covers the triply iterated case, where the outer variable has to pass both inner ones at once. Both directions are proved here from the two-variable statement, by treating the two inner variables as a single variable of the product and unfolding again on each side. The hypothesis is integrability of the whole integrand against the triple product measure, which is what Fubini needs and what a statement of this kind has to carry.
:::
