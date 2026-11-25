import Polyfold.Examples.OrbifoldSquareSign
import Polyfold.Chapter15.LinearizationFunctor
import Polyfold.Chapter14.LocalScPlus

/-!
# Examples for the linearization of Theorem 15.1.1 and the sections `f − s`

Examples for the rows V15.2 (Theorem 15.1.1) and V15.10 (local sc⁺-sections and `f − s` on
`W|_O`) of Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), §§15.1–15.2, on
the worked example `X5 = ℤ/5 ⋉ ℂ` with the section `f(z) = z²`.

* `lvl1`: a point of `ℂ ≅ ℝ²` as a level-1 point of `X5`.
* `theorem_15_1_1_functor_sq`: for the five-branch sc⁺-multisection `Λ5 c` the linearization
  `T(f, Λ5 c)` satisfies `T(f, Λ)(g · z) = (g, z)_* T(f, Λ)(z)` for every morphism `(g, z)` of
  `X5`, including the isotropy morphisms `(g, 0)`, `g ≠ 1`, at the origin.
* `isScFredholmSectionTame_subRestrict_sq`: `f − s` for the constant sc⁺-section `s = (z, −b)` is
  an sc-Fredholm section of `W|_O` with tame germ data, `O = ℂ`.
-/

set_option maxSynthPendingDepth 3

open Set Function Topology

noncomputable section

namespace Polyfold.Examples.Path

open Polyfold OrbifoldSquare TrivialBundle EpGroupoid EpGroupoid.Examples StrongBundle MPolyfold
  SBLocalization Linearization15

/-- A point of `ℝ²` as a level-1 point of the object M-polyfold of `X5`. -/
def lvl1 (z : Fin 2 → ℝ) : A5.X.PObj.Level 1 :=
  A5.X.PObj.levelMk 1 z (by have h := mem_smoothSet_A5 z; exact mem_iInter.1 h 1)

/-- Row V15.2, Theorem 15.1.1 (pp. 684–687): the functor property of the linearization
`T(f, Λ)` of `f(z) = z²` and the five-branch sc⁺-multisection `Λ5 c` along any morphism `(g, z)` of
`X5 = ℤ/5 ⋉ ℂ`, among them the non-unit isotropy morphisms `(g, 0)` at the origin. -/
theorem theorem_15_1_1_functor_sq (c : ℂ) (g : G5) (z : Fin 2 → ℝ) :
    linearization sqSection (Λ5 c) (lvl1 (g • z)) =
      grfPush (A := A5) ((g, z) : G5 × (Fin 2 → ℝ))
        (mem_levelSet_one_of_src (x := lvl1 z) rfl) rfl rfl
        (linearization sqSection (Λ5 c) (lvl1 z)) :=
  theorem_15_1_1_functor isScFredholmSectionFunctor_sqSection (isScPlusMultisection_Λ5 c)
    ((g, z) : G5 × (Fin 2 → ℝ)) rfl rfl

/-- Row V15.2: the isotropy morphism `(g, 0)` of `X5` at the origin is not a unit for `g ≠ 1`, so
`theorem_15_1_1_functor_sq` is tested on morphisms that are not units. -/
theorem isotropy_ne_one_sq {g : G5} (hg : g ≠ 1) :
    (⟨((g, (0 : Fin 2 → ℝ)) : G5 × (Fin 2 → ℝ)), rfl, smul_zero5 g⟩ :
      X5.Isotropy (0 : Fin 2 → ℝ)) ≠ 1 := by
  intro h
  have h' := congrArg isotropyZeroEquiv h
  rw [map_one] at h'
  exact hg h'

/-- `univ ⊆ ℝ²` is nonempty. -/
theorem nonempty_univ_A5 : Nonempty (univ : Set A5.Obj) := ⟨⟨(0 : Fin 2 → ℝ), mem_univ _⟩⟩

/-- `univ ⊆ ℝ²` is paracompact. -/
theorem paracompactSpace_univ_A5 : ParacompactSpace (univ : Set A5.Obj) := by
  change ParacompactSpace (univ : Set (Fin 2 → ℝ))
  infer_instance

/-- The pull-back of `W` to `univ ⊆ ℝ²` is paracompact. -/
theorem paracompactSpace_pullback_univ_A5 :
    ParacompactSpace (pullbackSpace A5.P (Subtype.val : ↥(univ : Set A5.Obj) → A5.Obj)) := by
  change ParacompactSpace (pullbackSpace (proj 2 2)
    (Subtype.val : ↥(univ : Set (Fin 2 → ℝ)) → (Fin 2 → ℝ)))
  infer_instance

attribute [local instance] nonempty_univ_A5 paracompactSpace_univ_A5
  paracompactSpace_pullback_univ_A5

/-- Row V15.10, local sc⁺-sections and `f − s` on `W|_O` (p. 689): for `f(z) = z²` on the worked
example and the constant sc⁺-section `s(z) = (z, −b)`, the section `f − s` of `W|_ℂ` is
sc-Fredholm with tame germ data. -/
theorem isScFredholmSectionTame_subRestrict_sq (b : Fin 2 → ℝ) :
    (A5.B.restrictOpen (isOpen_univ : IsOpen (univ : Set A5.Obj))).IsScFredholmSectionTame
      (subRestrict (O := univ) sqSection (negConst b)
        isScFredholmSectionTame_sqSection.isScSmooth.1) :=
  isScFredholmSectionTame_subRestrict isOpen_univ isScFredholmSectionTame_sqSection
    (IsScPlusSectionOn.of_isScPlusSection (isScPlusSection_negConst b) isOpen_univ)

end Polyfold.Examples.Path
