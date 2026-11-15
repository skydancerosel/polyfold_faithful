import Polyfold.Chapter15.CylinderCanonicalOrientation
import Polyfold.Chapter16.CanonicalOrientationWitness

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), §15.4, p. 703, and §6.6,
p. 276 (**Remark 6.6.19**): the orientation "`[0, 1]` first, then `o`" of `f̃` on `[0, 1] × X`, on
an example.

# The orientation `õ = e ∧ o` on the cylinder over the half-plane

## What is formalized (namespace `Polyfold.HalfSpaceBundle`)

The example is the half-disc section `f(a, y) = a² + y² − 1` of the trivial bundle with fibre
`ℝ` over the half-plane `H = [0, ∞) × ℝ` (`halfSEP 1 1`), oriented by `halfOrientation`.

* **`cubeOrientation_halfSEP`**: `∂H ≠ ∅`, the fibres are non-zero, `f` has index `1` at every
  point, and on the cylinder `[0, 1] × H`: `õ = e ∧ o` is an orientation of `f̃` (Definition
  6.6.16), it is invariant under the morphisms of the cylinder (the second clause of Definition
  12.5.4), and `f̃` has index `2` at every smooth point.

## Reading

`H` has a boundary, so `d_H ≢ 0` and Corollary 15.4.4 does not apply to this example; the
statement shows that the hypotheses on `õ` used for the cobordism (`ho`, `hinvC`, the index)
hold in an example with boundary and non-zero fibres.  The morphisms of the example are units.
-/

set_option maxSynthPendingDepth 3
set_option linter.unusedSectionVars false

open Set Function Topology Filter Module
open scoped ContDiff

noncomputable section

namespace Polyfold

namespace HalfSpaceBundle

open SBLocalization StrongBundle StrongRetr MPolyfold EpGroupoid Linearization15 SEP

/-- **The orientation `õ = e ∧ o` on the cylinder over the half-plane** (2021 p. 703, Remark
6.6.19): for the half-disc section `f` of `halfSEP 1 1` with its orientation `o`, the base has
non-empty boundary, the fibres are non-zero, and on `[0, 1] × H` the family `õ = e ∧ o` is an
orientation of `f̃`, invariant under the morphisms, and `f̃` has index `2` at every smooth
point. -/
theorem cubeOrientation_halfSEP :
    (halfSEP 1 1).X.PObj.boundary.Nonempty ∧
    (∀ y : (halfSEP 1 1).Obj, Nontrivial ((halfSEP 1 1).P ⁻¹' {y})) ∧
    (haveI := paracompactSpace_rn_prod ((halfSEP 1 1).cubeSEP 1).X.PObj
     haveI := paracompactSpace_rn_pullback ((halfSEP 1 1).cubeSEP 1).B
     IsSectionOrientation (cubeLiftEp (n := 1) halfDiscSection
        (isScFredholmSectionFunctor_graphSection_halfSEP (k := 1) contDiff_halfDiscMap).1.1.1)
      (isScFredholmSectionFunctor_cubeLiftEp (n := 1)
        (isScFredholmSectionFunctor_graphSection_halfSEP (k := 1) contDiff_halfDiscMap)
        (isScFredholmSectionTame_graphSection_halfSEP (k := 1) contDiff_halfDiscMap)).2
      (cubeOrientation
        (isScFredholmSectionFunctor_graphSection_halfSEP (k := 1) contDiff_halfDiscMap)
        (isScFredholmSectionTame_graphSection_halfSEP (k := 1) contDiff_halfDiscMap)
        (hasScPlusSectionsThrough_halfSEP 1 1) (halfOrientation contDiff_halfDiscMap))) ∧
    (∀ hsec' : ((halfSEP 1 1).cubeSEP 1).B.HasScPlusSectionsThrough,
      ((halfSEP 1 1).cubeSEP 1).E.IsOrInvariant
        (isScFredholmSectionFunctor_cubeLiftEp (n := 1)
          (isScFredholmSectionFunctor_graphSection_halfSEP (k := 1) contDiff_halfDiscMap)
          (isScFredholmSectionTame_graphSection_halfSEP (k := 1) contDiff_halfDiscMap)) hsec'
        (cubeOrientation
          (isScFredholmSectionFunctor_graphSection_halfSEP (k := 1) contDiff_halfDiscMap)
          (isScFredholmSectionTame_graphSection_halfSEP (k := 1) contDiff_halfDiscMap)
          (hasScPlusSectionsThrough_halfSEP 1 1) (halfOrientation contDiff_halfDiscMap))) ∧
    ∀ (t : Fin 1 → unitInterval) (x : (halfSEP 1 1).Obj), x ∈ (halfSEP 1 1).X.PObj.smoothSet →
      ((halfSEP 1 1).cubeSEP 1).B.IsIndexAt (cubeLiftEp (n := 1) halfDiscSection
        (isScFredholmSectionFunctor_graphSection_halfSEP (k := 1) contDiff_halfDiscMap).1.1.1)
        (t, x) ((1 + 1 : ℕ) : ℤ) := by
  obtain ⟨hbd, hfib, -, hX, hbump, -, -, -, -, -, ho, -, -⟩ := theorem_15_4_1_hypotheses_halfSEP
  refine ⟨hbd, hfib, ?_, fun hsec' => ?_, fun t x hxs => ?_⟩
  · exact isSectionOrientation_cubeOrientation hX hbump
      (isScFredholmSectionFunctor_graphSection_halfSEP (k := 1) contDiff_halfDiscMap)
      (isScFredholmSectionTame_graphSection_halfSEP (k := 1) contDiff_halfDiscMap) ho
  · exact isOrInvariant_cubeOrientation_of_forall_unit _ _ _ hsec' _ fun _ => rfl
  · exact isIndexAt_cubeLiftEp
      (isScFredholmSectionFunctor_graphSection_halfSEP (k := 1) contDiff_halfDiscMap)
      (isScFredholmSectionTame_graphSection_halfSEP (k := 1) contDiff_halfDiscMap)
      (hasScPlusSectionsThrough_halfSEP 1 1) hxs (isIndexAt_halfDisc x) t

end HalfSpaceBundle

end Polyfold
