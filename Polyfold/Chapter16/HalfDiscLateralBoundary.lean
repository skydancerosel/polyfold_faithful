import Polyfold.Chapter16.HalfDiscFaceStructureInstance
import Polyfold.Chapter9.IntervalLateralBoundary

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Remark 6.6.19 and the
proof of Theorem 6.7.1 (pp. 276–278), on the half-disc example of
`HalfDiscIntervalCobordism.lean`.

# The signed boundary formula without faces on the half-disc

`H = [0, ∞) × ℝ` (`∂H ≠ ∅`), the bundle `H × ℝ → H` (fibres `ℝ`),
`f(a, y) = ((a, y), a² + y² − 1)` with the orientation `halfDiscOrientation` (index `1`), and
`S = 0`.  Both ends of `S_F = [0, 1] × S_f` contain the boundary point `(0, 1)`
(`topPoint_mem_ends_halfDisc`).

* **`theorem_6_6_18_boundaryIntegral_interval_lateral_halfDisc`**:
  `theorem_6_6_18_boundaryIntegral_interval_lateral` with every hypothesis discharged (the
  face-structuredness of `H` is not used): the corner structures, the orientations of
  Theorem 6.6.18, and for every `α` and all cut-offs `χₘ`,
  `∫_{∂S_F} (χₘ ∘ t) ω → ∫_{∂S_F} ω − (∫_{S_{F_1}} α − ∫_{S_{F_0}} α)`.
-/

set_option maxSynthPendingDepth 3

noncomputable section

namespace Polyfold

namespace HalfSpaceBundle

open SBLocalization StrongBundle StrongRetr UnitCube MPolyfold

local instance instParacompactIvHL : ParacompactSpace ((Fin 1 → unitInterval) × H 1) :=
  MPolyfold.paracompactSpace_prod (cubePolyfold 1) (basePoly 1)

local instance instParacompactIvPullbackL :
    ParacompactSpace (pullbackSpace (proj 1 1) (Prod.snd : (Fin 1 → unitInterval) × H 1 → H 1)) :=
  paracompactSpace_pullbackSpace (f := (Prod.snd : (Fin 1 → unitInterval) × H 1 → H 1))
    ((cubePolyfold 1).prod (basePoly 1)) (bundle 1 1)

local instance instParacompactSFL : ParacompactSpace (solutionSet (pullbackProj (proj 1 1)
    Prod.snd) (sectionAdd (pullbackProj (proj 1 1) Prod.snd) (cubeLift (n := 1)
      (graphSection halfDiscMap) isScFredholmSectionTame_halfDisc.isScSmooth.1)
      halfDiscZeroLift)) :=
  ((cubePolyfold 1).prod (basePoly 1)).paracompactSpace_subtype _

local instance instParacompactSEL (b : Bool) : ParacompactSpace (solutionSet (proj 1 1)
    (sectionAdd (proj 1 1) (graphSection halfDiscMap) (prodSlice halfDiscZeroLift (ivEnd b)))) :=
  (basePoly 1).paracompactSpace_subtype _

/-- **`theorem_6_6_18_boundaryIntegral_interval_lateral` on the half-disc** (`S = 0`, index `1`):
every hypothesis is discharged.  The statement is that of the general theorem for
`X = H`, `f(a, y) = a² + y² − 1`, `o = halfDiscOrientation`, `S = 0`. -/
theorem theorem_6_6_18_boundaryIntegral_interval_lateral_halfDisc :
    type_of% (theorem_6_6_18_boundaryIntegral_interval_lateral isTame_basePoly_one
      admitsBumpFunctions_basePoly_one isScFredholmSectionTame_halfDisc halfDiscOrientation
      halfDiscZeroLift_spec.1 halfDiscZeroLift_spec.2.1 halfDiscZeroLift_spec.2.2.1
      (k := 1) (fun x _ => isIndexAt_halfDisc x)) :=
  theorem_6_6_18_boundaryIntegral_interval_lateral isTame_basePoly_one
    admitsBumpFunctions_basePoly_one isScFredholmSectionTame_halfDisc halfDiscOrientation
    halfDiscZeroLift_spec.1 halfDiscZeroLift_spec.2.1 halfDiscZeroLift_spec.2.2.1
    (k := 1) (fun x _ => isIndexAt_halfDisc x)

end HalfSpaceBundle

end Polyfold
