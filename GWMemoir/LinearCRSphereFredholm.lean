import GWMemoir.CokernelSphereDense
import GWMemoir.EllipticEstimateSphere

/-!
# The linearized Cauchy–Riemann operator at a constant map from the sphere is Fredholm

HWZ, *Applications of Polyfold Theory I*, Memoirs AMS 248, no. 1179, §4 and Appendix 5.3, at a
constant map `u ≡ q` from the sphere with three marked points (`sphere3`) and a constant complex
structure: the operator `D = ∂̄` from the section space `H^{3,δ₀}` to the fibre `H^{2,δ₀}` of
`(0,1)`-forms is Fredholm, surjective, with kernel the constants, of index `dim E`.  No named
proposition is assumed: the elliptic estimate is `ellipticEstimate_sphere3`, the vanishing of the
cokernel follows from it and the density of the range (`cokernelVanishes_of_ellipticEstimate`).
-/

set_option maxSynthPendingDepth 3
set_option linter.unusedSectionVars false

open scoped Manifold ContDiff
open Polyfold Polyfold.CylinderSobolev ContinuousLinearMap

namespace GWMemoir

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {Q : Type} [TopologicalSpace Q] [ChartedSpace E Q] [IsManifold 𝓘(ℝ, E) ∞ Q]
variable (J : AlmostComplexStructure E Q) {q : Q} {A : SectionAtlas (E := E) sphere3 (fun _ => q)}
  (G : GlueData A) (δ : ℕ → ℝ) (h0 : 0 ≤ δ 0) (hmono : StrictMono δ)

/-- **The cokernel of `D` vanishes on `sphere3`**, with no hypothesis beyond a positive weight. -/
theorem cokernelVanishes_sphere3_of_pos (hδ : 0 < δ 0) : CokernelVanishes J G δ h0 hmono :=
  cokernelVanishes_of_ellipticEstimate J G δ h0 hmono hδ (ellipticEstimate_sphere3 J G δ h0 hmono hδ)

/-- **`D` is Fredholm of index `dim E` at a constant map from `sphere3`** (Memoir §4, at a constant
map), with a positive weight `δ₀`. -/
theorem linCR_isFredholm_sphere3 (hδ : 0 < δ 0) :
    IsFredholm (linCR3 J G δ h0 hmono) ∧
      fredholmIndex (linCR3 J G δ h0 hmono) = Module.finrank ℝ E :=
  ⟨linCR_isFredholm J G δ h0 hmono (cokernelVanishes_sphere3_of_pos J G δ h0 hmono hδ),
    linCR_index J G δ h0 hmono (cokernelVanishes_sphere3_of_pos J G δ h0 hmono hδ)⟩

end GWMemoir
