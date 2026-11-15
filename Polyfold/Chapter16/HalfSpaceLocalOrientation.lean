import Polyfold.Chapter16.HalfSpaceOrientedSection
import Polyfold.Chapter14.LocalOrientationFunctorHalfSpace
import Polyfold.Chapter12.LocalOrientationComparisonOrbit

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part I, §6.6,
Definitions 6.6.14–6.6.16 (p. 274), and Chapter 12, Definition 12.5.4 (p. 594), for the local
orientation sets.

# An orientation of the graph section over the half-space, for the local orientation sets

## The text, paraphrased

(Definition 6.6.14) `f` is orientable if `Γ_f([φ])` depends only on the end points of `φ`;
(Definition 6.6.16) an orientation is a map `y ↦ o_y` which near every smooth point is a
continuous orientation; (Definition 12.5.4) over an ep-groupoid it is moreover invariant under
the morphisms.

## What is formalized (namespace `Polyfold.HalfSpaceBundle`)

The bundle is `H × ℝᵏ → H` over the trivial ep-groupoid of `H = [0, ∞) × ℝᵐ` (`halfSEP m k`),
with `∂H ≠ ∅` and fibres `ℝᵏ`; `F` is the graph section of a `C^∞` map `φ`.  The orientation
sets are the local ones (`OrxLoc`, sc⁺-sections over open subsets of chart domains).

* `isOrientableSectionLoc_halfSpace`: `F` is orientable (Definition 6.6.14), since any two
  sc-smooth paths of `H` with the same end points are homotopic (`PathCat.hom_eq_halfSpace`).
* `halfOrientationLoc`: the image of the orientation `halfOrientation` under `orxLocEquiv`;
  `isSectionOrientationLoc_halfOrientationLoc` (Definition 6.6.16) and
  `definition_12_5_4_loc_halfOrientationLoc` (Definition 12.5.4 for the local objects).
* `halfOrientationLoc_witness`: the same together with `∂H ≠ ∅` and non-zero fibres.
-/

set_option maxSynthPendingDepth 3

open Set

open scoped ContDiff

noncomputable section

namespace Polyfold

namespace HalfSpaceBundle

variable {m k : ℕ} {φ : Pm m → (Fin k → ℝ)}

/-- **Definition 6.6.14 for the local orientation sets on the half-space bundle**: the graph
section of a `C^∞` map is orientable, because the path category of `H` has at most one
morphism between two points. -/
theorem isOrientableSectionLoc_halfSpace (hφ : ContDiff ℝ ∞ φ) :
    IsOrientableSectionLoc (isTame_halfSEP m k) (isScFredholmSectionTame_graphSection_halfSEP hφ) :=
  isOrientableSectionLoc_of_hom_eq _ _ fun a b => PathCat.hom_eq_halfSpace (m := m) a b

/-- **An orientation of the graph section for the local orientation sets**: the image of
`halfOrientation` under `orxLocEquiv`. -/
def halfOrientationLoc (hφ : ContDiff ℝ ∞ φ) : ∀ a (hs : a ∈ (halfSEP m k).X.PObj.smoothSet),
    OrxLoc (isScFredholmSectionTame_graphSection_halfSEP hφ) a hs := fun a hs =>
  orxLocEquiv (isScFredholmSectionTame_graphSection_halfSEP hφ)
    (hasScPlusSectionsThrough_halfSEP m k) a hs (halfOrientation hφ a hs)

/-- **`halfOrientationLoc` is an orientation in the sense of Definition 6.6.16** for the local
orientation sets. -/
theorem isSectionOrientationLoc_halfOrientationLoc (hφ : ContDiff ℝ ∞ φ) :
    IsSectionOrientationLoc (isTame_halfSEP m k)
      (isScFredholmSectionTame_graphSection_halfSEP hφ) (halfOrientationLoc hφ) := by
  have := paracompactSpace_rn_prod (halfSEP m k).X.PObj
  have := paracompactSpace_rn_pullback (halfSEP m k).B
  have := paracompactSpace_rn_rn_prod (halfSEP m k).X.PObj
  have := paracompactSpace_rn_rn_pullback (halfSEP m k).B
  refine (isSectionOrientation_iff_loc (isTame_halfSEP m k) (admitsBumpFunctions_halfSEP m k)
    (isScFredholmSectionTame_graphSection_halfSEP hφ) (hasScPlusSectionsThrough_halfSEP m k)
    (halfOrientation hφ)).1 ?_
  exact (isSectionOrientation_iff_continuous (isTame_halfSEP m k)
    (admitsBumpFunctions_halfSEP m k) (isScFredholmSectionTame_graphSection_halfSEP hφ)
    (hasScPlusSectionsThrough_halfSEP m k) _).2
      (exists_continuous_orSec_graphSection_halfSEP hφ).choose_spec

/-- **`halfOrientationLoc` is an orientation in the sense of Definition 12.5.4** for the local
objects: continuous for the topology of Theorem 12.5.3 on the orientation space of the local
orientation sets, and invariant under the morphisms. -/
theorem definition_12_5_4_loc_halfOrientationLoc (hφ : ContDiff ℝ ∞ φ) :
    (halfSEP m k).E.definition_12_5_4_loc (isTame_halfSEP m k)
      (isScFredholmSectionFunctor_graphSection_halfSEP hφ)
      (isScFredholmSectionTame_graphSection_halfSEP hφ) (halfOrientationLoc hφ) := by
  have := paracompactSpace_rn_prod (halfSEP m k).X.PObj
  have := paracompactSpace_rn_pullback (halfSEP m k).B
  have := paracompactSpace_rn_rn_prod (halfSEP m k).X.PObj
  have := paracompactSpace_rn_rn_pullback (halfSEP m k).B
  exact ((halfSEP m k).E.definition_12_5_4_iff_loc
    (isScFredholmSectionFunctor_graphSection_halfSEP hφ)
    (isScFredholmSectionTame_graphSection_halfSEP hφ) (hasScPlusSectionsThrough_halfSEP m k)
    (isTame_halfSEP m k) (admitsBumpFunctions_halfSEP m k) (halfOrientation hφ)).1
      (definition_12_5_4_halfOrientation hφ)

/-- **Witness for §12.5 with the local orientation sets, with boundary and non-zero fibres**:
over `H = [0, ∞) × ℝᵐ` (`∂H ≠ ∅`) with fibres `ℝᵏ`, `k ≥ 1`, the graph section of a `C^∞`
map is orientable (Definition 6.6.14) and `halfOrientationLoc` is an orientation in the sense
of Definitions 6.6.16 and 12.5.4. -/
theorem halfOrientationLoc_witness [NeZero k] (hφ : ContDiff ℝ ∞ φ) :
    (halfSEP m k).X.PObj.boundary.Nonempty ∧
    (∀ y : (halfSEP m k).Obj, Nontrivial ((halfSEP m k).P ⁻¹' {y})) ∧
    IsOrientableSectionLoc (isTame_halfSEP m k)
      (isScFredholmSectionTame_graphSection_halfSEP hφ) ∧
    IsSectionOrientationLoc (isTame_halfSEP m k)
      (isScFredholmSectionTame_graphSection_halfSEP hφ) (halfOrientationLoc hφ) ∧
    (halfSEP m k).E.definition_12_5_4_loc (isTame_halfSEP m k)
      (isScFredholmSectionFunctor_graphSection_halfSEP hφ)
      (isScFredholmSectionTame_graphSection_halfSEP hφ) (halfOrientationLoc hφ) :=
  ⟨⟨_, zero_mem_boundary_halfSEP m k⟩, nontrivial_fibre_halfSEP m k,
    isOrientableSectionLoc_halfSpace hφ, isSectionOrientationLoc_halfOrientationLoc hφ,
    definition_12_5_4_loc_halfOrientationLoc hφ⟩

end HalfSpaceBundle

end Polyfold
