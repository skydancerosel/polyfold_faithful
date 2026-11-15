import Polyfold.Chapter15.BoundaryExtensionIndependence
import Polyfold.Chapter15.CylinderCobordismReduced

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), §15.3–15.4:
**Corollary 15.3.10 (3)**, p. 699, and **Corollary 15.4.4**, p. 703, with Theorem 15.3.9 on
`[0, 1] × X` proved.

# Corollaries of the Transversal Extension Theorem on the cylinder

## What is formalized (namespace `Polyfold.SBLocalization`)

* **`corollary_15_3_10_3_of_onto`**: Corollary 15.3.10 (3) for two structurable regular
  perturbations `Λ⁰`, `Λ¹`: a regular perturbation over `[0, 1] × X` which agrees with `Λⁱ` over
  `{i} × X`.  Theorem 15.3.9 on the cylinder is `theorem_15_3_9`, and the glued boundary data are
  structurable (`cubeLiftFace_holds`).  Added hypotheses: sc-smooth partitions of unity on `X`
  and the face condition of the glued data (`hbonto`).
* **`corollary_15_4_4_of_onto_or`**, `corollary_15_4_4_eff_of_onto_or`: Corollary 15.4.4 along
  the text's argument and its effective version, given the face condition of the glued data
  (`honto`) and step (c) (`hor`).
-/

set_option maxSynthPendingDepth 3
set_option linter.unusedSectionVars false

open Set Function Topology Filter

noncomputable section

namespace Polyfold

universe u

namespace SBLocalization

open StrongBundle StrongRetr MPolyfold EpGroupoid SEP OrientedRegularPerturbation

variable {A : SEP.{u}}

/-- **Corollary 15.3.10 (3), p. 699, for two structurable regular perturbations**: for `d_X ≡ 0`,
paracompact `|X|`, sc-smooth partitions of unity, `f` sc-Fredholm (with tame germ data) with
compact `|S_f|` and regular perturbations `(Nᵢ, Uᵢ, Λⁱ)`, `i = 0, 1`, whose glued boundary data
satisfy the face condition (`hbonto`), there is a regular perturbation over `[0, 1] × X` which
agrees with `Λⁱ` over `{i} × X`, and its solution set is a compact branched ep⁺-subgroupoid. -/
theorem corollary_15_3_10_3_of_onto
    (hd : ∀ x, A.X.PObj.degIndex x = 0) (hpara : A.X.HasParacompactOrbitSpace)
    (hPU : A.X.PObj.AdmitsScPartitionsOfUnity) {f : A.Obj → A.W}
    (hf : A.E.IsScFredholmSectionFunctor f) (hft : A.B.IsScFredholmSectionTame f)
    (hS : A.E.HasCompactSolutionSetEp f) {N₀ N₁ : A.B.One → ℝ} {U₀ U₁ : Set A.Obj}
    {Λ₀ Λ₁ : A.W → ℚ≥0} (hr₀ : IsRegularPerturbation A f N₀ U₀ Λ₀)
    (hr₁ : IsRegularPerturbation A f N₁ U₁ Λ₁)
    (hbonto : IsBoundaryFaceOnto (cubeLiftEp (n := 1) f hf.1.1.1) (cubeGlue Λ₀ Λ₁)) :
    ∃ Λ' : (A.cubeSEP 1).W → ℚ≥0,
      IsRegularPerturbation (A.cubeSEP 1) (cubeLiftEp (n := 1) f hf.1.1.1)
        (interpAuxNorm A N₀ N₁) (interpSet A U₀ U₁) Λ' ∧
      (∀ w, ((cubeVal w).1.1 0 : ℝ) = 0 → Λ' w = Λ₀ (cubeVal w).2) ∧
      (∀ w, ((cubeVal w).1.1 0 : ℝ) = 1 → Λ' w = Λ₁ (cubeVal w).2) ∧
      (A.cubeSEP 1).X.IsBranchedEpSubgroupoid
        (fun z => (Λ' (cubeLiftEp (n := 1) f hf.1.1.1 z) : ℚ)) ∧
      (A.cubeSEP 1).X.IsCompactBranched
        (fun z => (Λ' (cubeLiftEp (n := 1) f hf.1.1.1 z) : ℚ)) :=
  corollary_15_3_10_3_of_rel_onto theorem_15_3_7_relative hd hpara hPU hf hft hS hr₀ hr₁ hbonto

/-- **Corollary 15.4.4 (2017: Corollary 15.2), p. 703, along the text's argument, with
Theorem 15.3.9 on `[0, 1] × X` proved**: `corollary_15_4_4_of_rel_onto` with the relative step
`theorem_15_3_7_relative`.  Left: the face condition of the glued data of any two
`Can`-perturbations (`honto`) and step (c) (`hor`). -/
theorem corollary_15_4_4_of_onto_or
    (hd : ∀ x, A.X.PObj.degIndex x = 0) (hpara : A.X.HasParacompactOrbitSpace)
    (hPUX : A.X.PObj.AdmitsScPartitionsOfUnity)
    {f : A.Obj → A.W} (hf : A.E.IsScFredholmSectionFunctor f)
    (hft : A.B.IsScFredholmSectionTame f) (hS : A.E.HasCompactSolutionSetEp f) {m : ℕ}
    (Can : OrientedRegularPerturbation A f m → Prop)
    (honto : ∀ P₀ P₁, Can P₀ → Can P₁ →
      IsBoundaryFaceOnto (cubeLiftEp (n := 1) f hf.1.1.1) (cubeGlue P₀.Λ P₁.Λ))
    (hor : ∀ P₀ P₁, Can P₀ → Can P₁ → CylinderOrientationStatement hf.1.1.1 P₀ P₁) :
    corollary_15_4_4_statement A f m Can :=
  corollary_15_4_4_of_rel_onto theorem_15_3_7_relative hd hpara hPUX hf hft hS Can honto hor

/-- **Corollary 15.4.4, effective version, p. 703, with Theorem 15.3.9 on `[0, 1] × X` proved**:
`corollary_15_4_4_eff_of_rel_onto` with the relative step `theorem_15_3_7_relative`. -/
theorem corollary_15_4_4_eff_of_onto_or
    (hd : ∀ x, A.X.PObj.degIndex x = 0) (hpara : A.X.HasParacompactOrbitSpace)
    (hPUX : A.X.PObj.AdmitsScPartitionsOfUnity) (hLUC : A.X.IsLUC)
    {f : A.Obj → A.W} (hf : A.E.IsScFredholmSectionFunctor f)
    (hft : A.B.IsScFredholmSectionTame f) (hS : A.E.HasCompactSolutionSetEp f) {m : ℕ}
    (Can : OrientedRegularPerturbation A f m → Prop)
    (honto : ∀ P₀ P₁, Can P₀ → Can P₁ →
      IsBoundaryFaceOnto (cubeLiftEp (n := 1) f hf.1.1.1) (cubeGlue P₀.Λ P₁.Λ))
    (hor : ∀ P₀ P₁, Can P₀ → Can P₁ →
      CylinderOrientationEffStatement hf.1.1.1 hLUC (isLUC_cubeSEP hLUC) P₀ P₁) :
    corollary_15_4_4_eff_statement A f m hLUC Can :=
  corollary_15_4_4_eff_of_rel_onto theorem_15_3_7_relative hd hpara hPUX hLUC hf hft hS Can
    honto hor

end SBLocalization

end Polyfold
