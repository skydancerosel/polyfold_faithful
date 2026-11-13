import Polyfold.Chapter6.ProductSectionOrientation2021f
import Polyfold.Chapter6.InvariantCobordism2021

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), §6.7, p. 278 (proof of
**Theorem 6.7.1**; preprint Theorem 6.43) and **Remark 6.6.19**, p. 276: the orientation of the
cobordism `S_F`, `F = f̃₀ + Ŝ`, given by the orientation `e ∧ o₀` of `F`.

# The orientation of the cobordism

## What is formalized

* `cobOr`: the tangent orientation of the index-`(k+1)` part `S_F^{k+1}` given by the orientation
  `SectionOrientation.prodFirst o₀` of `F` (Theorem 6.6.18 for the open part,
  `solOrOpen`); `isContinuous_cobOr`: it is continuous.
* `cobordismOrientation_of_ends`: 4b's `CobordismOrientation` holds as soon as `cobOr` is the
  product orientation `e ∧ o_{S_i}` on the two ends (`ProductEnd.IsEndProductOrientation`).

## Continued in later files

The value of `cobOr` on the two ends (the hypotheses of `cobordismOrientation_of_ends`) is
`isEndProductOrientation_cobOr`, and `CobordismOrientationHyp` is `cobordismOrientationHyp`
(`CobordismOrientationEnds2021d`); Theorem 6.7.1 is `theorem_6_7_1` (`Theorem671Final2021`).
-/

open Set Filter Topology Manifold Module MeasureTheory

noncomputable section

namespace Polyfold

universe u v

local notation "𝓠" => modelWithCornersEuclideanQuadrant

local notation3 "∞" => ((⊤ : ℕ∞) : WithTop ℕ∞)

section CobOr

open MPolyfold StrongBundle

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle PX P}
  [ParacompactSpace ((Fin 1 → ℝ) × X)]
  [ParacompactSpace (pullbackSpace P (Prod.snd : (Fin 1 → ℝ) × X → X))]
  (hX : PX.IsTame) (hbump : PX.AdmitsBumpFunctions)
  {f₀ : X → Y} (hf₀ : B.IsScFredholmSectionTame f₀) {N₀ : B.One → ℝ} {U₀ : Set X} {s₀ : X → Y}
  (hs₀ : B.IsAdmissible f₀ N₀ U₀ s₀) (o₀ : SectionOrientation f₀ hf₀.toIsScFredholmSection)
  {f₁ : X → Y} (hf₁ : B.IsScFredholmSectionTame f₁) {N₁ : B.One → ℝ} {U₁ : Set X} {s₁ : X → Y}
  (hs₁ : B.IsAdmissible f₁ N₁ U₁ s₁) (o₁ : SectionOrientation f₁ hf₁.toIsScFredholmSection)
  {σ₁ : X → Y} {Ŝ : (Fin 1 → ℝ) × X → pullbackSpace P (Prod.snd : (Fin 1 → ℝ) × X → X)}
  (hC : B.IsCobordismData f₀ hf₀.isScSmooth.1 s₀ σ₁ Ŝ)
  (h₁ : sectionAdd P f₀ σ₁ = sectionAdd P f₁ s₁) (k : ℕ)

/-- **The orientation of the cobordism `S_F^{k+1}`** (2021 Remark 6.6.19, p. 276; proof of
Theorem 6.7.1, p. 278): at `z`, the orientation of `T_zS_F = ker F'(z)` given by the orientation
`e ∧ o₀` of `F = f̃₀ + Ŝ` (`SectionOrientation.prodFirst`; `solOrOpen` on the open part
`cobIndexNbhd`). -/
def cobOr :
    letI := cobChartedSpace hX hf₀ hC k
    TangentOrientation (𝓠 (k + 1)) ↥(cobPart hf₀ Ŝ k) (k + 1) :=
  letI := cobChartedSpace hX hf₀ hC k
  haveI : Fact (IsOpen (cobIndexNbhd hf₀ Ŝ k)) := ⟨isOpen_cobIndexNbhd hf₀ hC k⟩
  haveI : ParacompactSpace ↥(solutionSet (pullbackProj P Prod.snd)
      (sectionAdd (pullbackProj P Prod.snd) (paramLift (n := 1) f₀ hf₀.isScSmooth.1) Ŝ) ∩
        cobIndexNbhd hf₀ Ŝ k) := ((rnPolyfold 1).prod PX).paracompactSpace_subtype _
  fun x => modelOrToTangent x (solOrOpen (Ω := cobIndexNbhd hf₀ Ŝ k)
    (theorem_3_1_18_tame hf₀.param hC.isScPlusSection)
    (SectionOrientation.prodFirst hX hbump hf₀ o₀ hC.isScPlusSection)
    (fun z hz => hC.gp z hz.1) (fun z hz => cobIndexNbhd_isLinOfIndex hf₀ hC k z hz.2 hz.1)
    (hasCornerStructureOfDim_cobPart hX hf₀ hC k) x)

/-- **The orientation of the cobordism is continuous** (`isContinuous_solOr_open` over the tame
`ℝ¹ × X` with its bump functions). -/
theorem isContinuous_cobOr :
    letI := cobChartedSpace hX hf₀ hC k
    (cobOr hX hbump hf₀ o₀ hC k).IsContinuous (𝓠 (k + 1)) ∞ :=
  letI := cobChartedSpace hX hf₀ hC k
  haveI : Fact (IsOpen (cobIndexNbhd hf₀ Ŝ k)) := ⟨isOpen_cobIndexNbhd hf₀ hC k⟩
  haveI : ParacompactSpace ↥(solutionSet (pullbackProj P Prod.snd)
      (sectionAdd (pullbackProj P Prod.snd) (paramLift (n := 1) f₀ hf₀.isScSmooth.1) Ŝ) ∩
        cobIndexNbhd hf₀ Ŝ k) := ((rnPolyfold 1).prod PX).paracompactSpace_subtype _
  isContinuous_solOr_open (Ω := cobIndexNbhd hf₀ Ŝ k) (inst := cobChartedSpace hX hf₀ hC k)
    (theorem_3_1_18_tame hf₀.param hC.isScPlusSection)
    (SectionOrientation.prodFirst hX hbump hf₀ o₀ hC.isScPlusSection)
    (fun z hz => hC.gp z hz.1) (fun z hz => cobIndexNbhd_isLinOfIndex hf₀ hC k z hz.2 hz.1)
    (hasCornerStructureOfDim_cobPart hX hf₀ hC k) (prod_rn_isTame hX)
    (MPolyfold.admitsBumpFunctions_prod_rn hbump) rfl

/-- **`CobordismOrientation` from the values of `cobOr` on the ends**: 4b's
`CobordismOrientation` holds if the orientation `cobOr` of `S_F^{k+1}` given by `e ∧ o₀` is the
product orientation `e ∧ o_{S_i}` on the ends `(0, 1/8) × S₀` and `(7/8, 1) × S₁`. -/
theorem cobordismOrientation_of_ends
    (hL : letI := solPartChartedSpace hX hf₀ hs₀ k
      letI := cobChartedSpace hX hf₀ hC k
      ∀ x₀ : ↥(B.solPart f₀ s₀ k),
        (cobEndLeft hX hf₀ hs₀ hC k x₀).IsEndProductOrientation (cobOr hX hbump hf₀ o₀ hC k)
          (solPartOr hX hf₀ hs₀ o₀ k))
    (hR : letI := solPartChartedSpace hX hf₁ hs₁ k
      letI := cobChartedSpace hX hf₀ hC k
      ∀ x₀ : ↥(B.solPart f₁ s₁ k),
        (cobEndRight hX hf₀ hf₁ hs₁ hC h₁ k x₀).IsEndProductOrientation
          (cobOr hX hbump hf₀ o₀ hC k) (solPartOr hX hf₁ hs₁ o₁ k)) :
    CobordismOrientation hX hf₀ hs₀ o₀ hf₁ hs₁ o₁ hC h₁ k :=
  ⟨cobOr hX hbump hf₀ o₀ hC k, isContinuous_cobOr hX hbump hf₀ o₀ hC k, hL, hR⟩

end CobOr

end Polyfold
