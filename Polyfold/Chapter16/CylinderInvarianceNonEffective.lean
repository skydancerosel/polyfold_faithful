import Polyfold.Chapter15.CylinderOrientationInvariance
import Polyfold.Chapter16.OrientationNonEffectiveWitness

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), §15.4, p. 703
(Corollary 15.4.4), with Definition 12.5.4 (p. 594) and Remark 6.6.19: the orientation
"`[0, 1]` first, then `o`" of `f̃` on `[0, 1] × X` in an example with non-trivial morphisms.

# The orientation `õ = e ∧ o` on the cylinder over `ℤ/3 × ℝ ⇉ ℝ`

## What is formalized (namespace `Polyfold.StrongBundleLocalizationExamples`)

The example is `W = ℝ × ℝᵏ → ℝ` over `ℤ/3 × ℝ ⇉ ℝ` with the trivial actions (`z3SEP k`),
`f` the graph section of a `C^∞` map `φ : ℝ → ℝᵏ`, oriented by `z3Orientation`
(Definition 12.5.4).

* `ne_unit_z3SEP`, `ne_unit_cubeSEP_z3SEP`: `X` and `[0, 1] × X` have morphisms that are not
  units.
* **`isOrInvariant_cubeOrientation_z3`**: `d_X ≡ 0`, the fibres are non-zero for `k ≥ 1`, there
  are morphisms of `[0, 1] × X` that are not units, `õ = e ∧ o` is an orientation of `f̃`
  (Definition 6.6.16), and `(t, g)_* õ = õ` for all morphisms of `[0, 1] × X`.

## Reading

The base is `ℝ`, so `f` has index `1 − k ≤ 0` for `k ≥ 1`: this is an instance of the
invariance of `õ` (`isOrInvariant_cubeOrientation`) with isotropy, not of Corollary 15.4.4
with sheets of positive dimension.
-/

set_option maxSynthPendingDepth 3
set_option linter.unusedSectionVars false

open Set Function Topology Module

open scoped ContDiff

noncomputable section

namespace Polyfold

namespace StrongBundleLocalizationExamples

open SBLocalization StrongBundleEquivalenceExamples TrivialBundle EpStrongBundle
open LocalizationLRBundleBaseExamples EpGroupoid.Examples SEP MPolyfold

variable {k : ℕ} {φ : (Fin 1 → ℝ) → (Fin k → ℝ)}

/-- `ℤ/3 × ℝ ⇉ ℝ` has a morphism that is not a unit. -/
theorem ne_unit_z3SEP (k : ℕ) :
    ∃ σ : (z3SEP k).Mor, σ ≠ (z3SEP k).X.unit ((z3SEP k).X.src σ) :=
  ⟨(Multiplicative.ofAdd (1 : ZMod 3), 0), fun h => by
    have h1 : Multiplicative.ofAdd (1 : ZMod 3) = 1 := congrArg Prod.fst h
    exact absurd h1 (by decide)⟩

/-- `[0, 1] × (ℤ/3 × ℝ ⇉ ℝ)` has a morphism that is not a unit. -/
theorem ne_unit_cubeSEP_z3SEP (k : ℕ) :
    ∃ σ : ((z3SEP k).cubeSEP 1).Mor,
      σ ≠ ((z3SEP k).cubeSEP 1).X.unit (((z3SEP k).cubeSEP 1).X.src σ) := by
  obtain ⟨σ, hσ⟩ := ne_unit_z3SEP k
  exact ⟨((fun _ => 0 : Fin 1 → unitInterval), σ), fun h => hσ (congrArg Prod.snd h)⟩

/-- **The orientation `õ = e ∧ o` on the cylinder over `ℤ/3 × ℝ ⇉ ℝ` is invariant under the
morphisms** (Definition 12.5.4 for `õ`; 2021 p. 703): for the graph section `f` of a `C^∞` map
`φ : ℝ → ℝᵏ`, `k ≥ 1`, with the orientation `o = z3Orientation`, the base has `d_X ≡ 0`, the
fibres are non-zero, `[0, 1] × X` has morphisms that are not units, `õ` is an orientation of
`f̃` (Definition 6.6.16) and `(t, g)_* õ_{(t, x)} = õ_{(t, x)}` for all morphisms `(t, (g, x))`
of `[0, 1] × X`. -/
theorem isOrInvariant_cubeOrientation_z3 [NeZero k] (hφ : ContDiff ℝ ∞ φ) :
    (∀ x, (z3SEP k).X.PObj.degIndex x = 0) ∧
    (∀ y : (z3SEP k).Obj, Nontrivial ((z3SEP k).P ⁻¹' {y})) ∧
    (∃ σ : ((z3SEP k).cubeSEP 1).Mor,
      σ ≠ ((z3SEP k).cubeSEP 1).X.unit (((z3SEP k).cubeSEP 1).X.src σ)) ∧
    (haveI := paracompactSpace_rn_prod ((z3SEP k).cubeSEP 1).X.PObj
     haveI := paracompactSpace_rn_pullback ((z3SEP k).cubeSEP 1).B
     IsSectionOrientation (cubeLiftEp (A := z3SEP k) (n := 1) (graphSection φ)
        (isScFredholmSectionFunctor_graphSection_z3 (k := k) hφ).1.1.1)
      (isScFredholmSectionFunctor_cubeLiftEp (A := z3SEP k) (n := 1)
        (isScFredholmSectionFunctor_graphSection_z3 (k := k) hφ)
        (isScFredholmSectionTame_graphSection_z3 hφ)).2
      (cubeOrientation (A := z3SEP k) (isScFredholmSectionFunctor_graphSection_z3 (k := k) hφ)
        (isScFredholmSectionTame_graphSection_z3 hφ) (hasScPlusSectionsThrough_z3SEP k)
        (z3Orientation hφ))) ∧
    ∀ hsec' : ((z3SEP k).cubeSEP 1).B.HasScPlusSectionsThrough,
      ((z3SEP k).cubeSEP 1).E.IsOrInvariant
        (isScFredholmSectionFunctor_cubeLiftEp (A := z3SEP k) (n := 1)
          (isScFredholmSectionFunctor_graphSection_z3 (k := k) hφ)
          (isScFredholmSectionTame_graphSection_z3 hφ)) hsec'
        (cubeOrientation (A := z3SEP k) (isScFredholmSectionFunctor_graphSection_z3 (k := k) hφ)
          (isScFredholmSectionTame_graphSection_z3 hφ) (hasScPlusSectionsThrough_z3SEP k)
          (z3Orientation hφ)) := by
  have := paracompactSpace_rn_prod (z3SEP k).X.PObj
  have := paracompactSpace_rn_pullback (z3SEP k).B
  have := paracompactSpace_rn_rn_prod (z3SEP k).X.PObj
  have := paracompactSpace_rn_rn_pullback (z3SEP k).B
  have hdef := definition_12_5_4_z3Orientation (k := k) hφ
  have ho : IsSectionOrientation (B := (z3SEP k).B) (graphSection φ)
      (isScFredholmSectionFunctor_graphSection_z3 hφ).2 (z3Orientation hφ) :=
    (isSectionOrientation_iff_continuous (isTame_z3SEP k) (admitsBumpFunctions_z3SEP k)
      (isScFredholmSectionTame_graphSection_z3 hφ) (hasScPlusSectionsThrough_z3SEP k) _).2 hdef.1
  refine ⟨fun x => MPolyfold.degIndex_rn x, fun y => nontrivial_fibre_z3SEP y,
    ne_unit_cubeSEP_z3SEP k, ?_, fun hsec' => ?_⟩
  · exact isSectionOrientation_cubeOrientation (isTame_z3SEP k) (admitsBumpFunctions_z3SEP k)
      (isScFredholmSectionFunctor_graphSection_z3 hφ)
      (isScFredholmSectionTame_graphSection_z3 hφ) ho
  · exact isOrInvariant_cubeOrientation _ _ _ hsec' _ hdef.2

end StrongBundleLocalizationExamples

end Polyfold
