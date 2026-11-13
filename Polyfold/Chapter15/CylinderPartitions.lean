import Polyfold.Chapter5.CubePartitions
import Polyfold.Chapter15.CylinderGlue

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), §15.3, proof of
**Corollary 15.3.10 (3)**, p. 699: sc-smooth partitions of unity on `[0, 1] × X` (gap TY-3).

# Partitions of unity on the cylinder

## The text, paraphrased

The proof of (3) applies Theorem 15.3.9 on `[0, 1] × X`.  Theorem 15.3.9 asks for sc-smooth
partitions of unity; the text does not say why `[0, 1] × X` has them.

## What is formalized (namespace `Polyfold.SBLocalization`)

* `admitsScPartitionsOfUnity_cubeSEP`: the M-polyfold of objects of `[0, 1]ⁿ × X` admits sc-smooth
  partitions of unity if that of `X` does (`admitsScPartitionsOfUnity_cubeProd`).
* **`corollary_15_3_10_3_pu_w5`** and **`corollary_15_3_10_3_glue_w5`**: TY's
  `corollary_15_3_10_3_ty` and `corollary_15_3_10_3_glue_hyp` with the hypothesis `hPUC` on
  `[0, 1] × X` replaced by sc-smooth partitions of unity on `X`.
-/

set_option maxSynthPendingDepth 3
set_option linter.unusedSectionVars false

open Set Function Topology Filter

noncomputable section

namespace Polyfold

universe u

namespace SBLocalization

open StrongBundle StrongRetr MPolyfold EpGroupoid SEP

variable {A : SEP.{u}}

/-- **`[0, 1]ⁿ × X` admits sc-smooth partitions of unity if `X` does** (the M-polyfold of objects
of `SEP.cubeSEP`). -/
theorem admitsScPartitionsOfUnity_cubeSEP (n : ℕ) (hPU : A.X.PObj.AdmitsScPartitionsOfUnity) :
    (A.cubeSEP n).X.PObj.AdmitsScPartitionsOfUnity := by
  have := MPolyfold.paracompactSpace_prod (cubePolyfold n) A.X.PObj
  change ((cubePolyfold n).prod A.X.PObj).AdmitsScPartitionsOfUnity
  exact admitsScPartitionsOfUnity_cubeProd hPU

/-- **Corollary 15.3.10 (3), p. 699, reduced to Theorem 15.3.9 on `[0, 1] × X`**, with sc-smooth
partitions of unity on `X` in place of TY's `hPUC` on `[0, 1] × X`; the other hypotheses as in
`corollary_15_3_10_3_ty`. -/
theorem corollary_15_3_10_3_pu_w5 (h159 : theorem_15_3_9_statement (A.cubeSEP 1))
    (hd : ∀ x, A.X.PObj.degIndex x = 0) (hpara : A.X.HasParacompactOrbitSpace)
    (hPU : A.X.PObj.AdmitsScPartitionsOfUnity) {f : A.Obj → A.W}
    (hf : A.E.IsScFredholmSectionFunctor f) (hft : A.B.IsScFredholmSectionTame f)
    (hS : A.E.HasCompactSolutionSetEp f) {N₀ N₁ : A.B.One → ℝ} {U₀ U₁ : Set A.Obj}
    (h₀ : ControlsCompactness A f N₀ U₀) (h₁ : ControlsCompactness A f N₁ U₁)
    {Λ₀ Λ₁ : A.W → ℚ≥0} (Λb : (A.cubeSEP 1).W → ℚ≥0)
    (hb₀ : ∀ w, ((cubeVal w).1.1 0 : ℝ) = 0 → Λb w = Λ₀ (cubeVal w).2)
    (hb₁ : ∀ w, ((cubeVal w).1.1 0 : ℝ) = 1 → Λb w = Λ₁ (cubeVal w).2)
    (hbs : IsBoundaryStructurable (A.cubeSEP 1) Λb)
    (hbdom : boundaryDomSupp Λb ⊆ interpSet A U₀ U₁)
    (hbN : ∀ z ∈ (A.cubeSEP 1).X.PObj.boundary, pointwiseNorm (interpAuxNorm A N₀ N₁) Λb z < 1)
    (hbonto : IsBoundaryFaceOnto (cubeLiftEp (n := 1) f hf.1.1.1) Λb) :
    ∃ Λ' : (A.cubeSEP 1).W → ℚ≥0,
      IsRegularPerturbation (A.cubeSEP 1) (cubeLiftEp (n := 1) f hf.1.1.1)
        (interpAuxNorm A N₀ N₁) (interpSet A U₀ U₁) Λ' ∧
      (∀ w, ((cubeVal w).1.1 0 : ℝ) = 0 → Λ' w = Λ₀ (cubeVal w).2) ∧
      (∀ w, ((cubeVal w).1.1 0 : ℝ) = 1 → Λ' w = Λ₁ (cubeVal w).2) ∧
      (A.cubeSEP 1).X.IsBranchedEpSubgroupoid
        (fun z => (Λ' (cubeLiftEp (n := 1) f hf.1.1.1 z) : ℚ)) ∧
      (A.cubeSEP 1).X.IsCompactBranched
        (fun z => (Λ' (cubeLiftEp (n := 1) f hf.1.1.1 z) : ℚ)) :=
  corollary_15_3_10_3_ty h159 hd hpara (admitsScPartitionsOfUnity_cubeSEP 1 hPU) hf hft hS h₀ h₁
    Λb hb₀ hb₁ hbs hbdom hbN hbonto

/-- **Corollary 15.3.10 (3), p. 699, for two structurable regular perturbations**, with sc-smooth
partitions of unity on `X` in place of TY's `hPUC` on `[0, 1] × X`: TY's
`corollary_15_3_10_3_glue_hyp`, whose remaining added hypotheses are the structurability `hbs`
and the face condition `hbonto` of the glued data. -/
theorem corollary_15_3_10_3_glue_w5 (h159 : theorem_15_3_9_statement (A.cubeSEP 1))
    (hd : ∀ x, A.X.PObj.degIndex x = 0) (hpara : A.X.HasParacompactOrbitSpace)
    (hPU : A.X.PObj.AdmitsScPartitionsOfUnity) {f : A.Obj → A.W}
    (hf : A.E.IsScFredholmSectionFunctor f) (hft : A.B.IsScFredholmSectionTame f)
    (hS : A.E.HasCompactSolutionSetEp f) {N₀ N₁ : A.B.One → ℝ} {U₀ U₁ : Set A.Obj}
    {Λ₀ Λ₁ : A.W → ℚ≥0} (hr₀ : IsRegularPerturbation A f N₀ U₀ Λ₀)
    (hr₁ : IsRegularPerturbation A f N₁ U₁ Λ₁)
    (hbs : IsBoundaryStructurable (A.cubeSEP 1) (cubeGlue Λ₀ Λ₁))
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
  corollary_15_3_10_3_glue_hyp h159 hd hpara (admitsScPartitionsOfUnity_cubeSEP 1 hPU) hf hft hS
    hr₀ hr₁ hbs hbonto

end SBLocalization

end Polyfold
