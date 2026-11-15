import Polyfold.Chapter6.KernelBundleInterval
import Polyfold.Chapter6.CubeManifold

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), §6.6, **Lemma 6.6.5**
(p. 265; preprint Lemma 6.30, p. 222): **`L` is a smooth vector bundle over `[0, 1]ⁿ`**.
Gap G.65, row V6.34.

# The bundle `L` over the manifold with corners `[0, 1]ⁿ`

## The text, paraphrased

(Lemma 6.6.5) Along the family `t ↦ (t, φ(t), 0)`, `t ∈ [0, 1]`, the kernels `L_t` form a smooth
vector bundle `L` over `[0, 1]`; the same is used for families on `[0, 1]ⁿ` (homotopies, §6.6).

## What is formalized

`lemma_6_6_5_smoothBundle` (`SmoothKernelFrames.lean`) gives `L` over an open connected
`V ⊇ [0, 1]ⁿ` in `ℝⁿ`.  With the smooth structure of the cube (`CubeManifold.lean`: the model
`cubeModel n`, the product of `n` copies of `𝓡∂ 1`, and the `C^∞` inclusion
`cubeToOpens : [0, 1]ⁿ → V`):

* **`lemma_6_6_5_smoothBundle_cube`** (Lemma 6.6.5 over `[0, 1]ⁿ` itself, every `n`): there is a
  smooth family of subspaces over the manifold with corners `[0, 1]ⁿ` whose fibre at `t` is
  `L_t = ker F'(0, (t, z_t)) ∩ {dt = 0}`; it is a Mathlib `C^∞` vector bundle over `[0, 1]ⁿ`
  (`ContMDiffVectorBundle ∞ … (cubeModel n)`).
-/

open Set Filter Topology Function Bundle
open scoped ContDiff Manifold

noncomputable section

namespace Polyfold

universe u v

section Lemma665

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle PX P}
  {f : X → Y} {n k : ℕ}
  [ParacompactSpace ((Fin n → ℝ) × X)]
  [ParacompactSpace (pullbackSpace P (Prod.snd : (Fin n → ℝ) × X → X))]
  [ParacompactSpace ((Fin k → ℝ) × ((Fin n → ℝ) × X))]
  [ParacompactSpace (pullbackSpace (pullbackProj P (Prod.snd : (Fin n → ℝ) × X → X))
    (Prod.snd : (Fin k → ℝ) × ((Fin n → ℝ) × X) → (Fin n → ℝ) × X))]

/-- **2021 Lemma 6.6.5, p. 265, over `[0, 1]ⁿ` itself: `L` is a smooth vector bundle over the
manifold with corners `[0, 1]ⁿ`** (preprint Lemma 6.30).  In the setting of
`lemma_6_6_5_smoothBundle`, there is a smooth family of subspaces over the cube `[0, 1]ⁿ` (model
`cubeModel n`, the product of `n` copies of `𝓡∂ 1`) whose fibre at `t` is
`L_t = ker F'(0, (t, z_t)) ∩ {dt = 0}` in the product chart; it is a `C^∞` vector bundle over
`[0, 1]ⁿ`.  For `n = 1` this is `lemma_6_6_5_smoothBundle_interval` up to `[0, 1] ≃ [0, 1]¹`. -/
theorem lemma_6_6_5_smoothBundle_cube (hf : B.IsScFredholmSectionTame f)
    {Φ : (Fin n → ℝ) → X} (hΦ : (rnPolyfold n).IsScSmoothMap PX Φ)
    {c : StrongBundleChart PX P} (hc : B.IsChart c)
    (hΦc : ∀ q ∈ Icc (0 : Fin n → ℝ) 1, Φ q ∈ c.φ.source)
    {S : (Fin n → ℝ) × X → pullbackSpace P (Prod.snd : (Fin n → ℝ) × X → X)}
    (hS : (B.pullback (MPolyfold.isScSmoothMap_snd (rnPolyfold n) PX)).IsScPlusSection S)
    (hz : ∀ᶠ q in 𝓝ˢ (Icc (0 : Fin n → ℝ) 1), IsZeroAt (pullbackProj P Prod.snd)
      (sectionAdd (pullbackProj P Prod.snd) (paramLift f hf.isScSmooth.1) S) (q, Φ q))
    {s : Fin k → (Fin n → ℝ) × X → pullbackSpace P (Prod.snd : (Fin n → ℝ) × X → X)}
    (hs : ∀ i, (B.pullback (MPolyfold.isScSmoothMap_snd (rnPolyfold n) PX)).IsScPlusSection (s i))
    (hP : ∀ᶠ q in 𝓝ˢ (Icc (0 : Fin n → ℝ) 1),
      ((B.pullback (MPolyfold.isScSmoothMap_snd (rnPolyfold n) PX)).pullback
        (MPolyfold.isScSmoothMap_snd (rnPolyfold k)
          ((rnPolyfold n).prod PX))).IsGeneralPositionGerm
        (paramSection (sectionAdd (pullbackProj P Prod.snd) (paramLift f hf.isScSmooth.1) S)
          ((isSection_pullbackLift _).sectionAdd hS.1) s fun i => (hs i).1) (0, (q, Φ q)))
    (q₀ : pullbackSpace P (Prod.snd : (Fin n → ℝ) × X → X))
    (q₁ : pullbackSpace (pullbackProj P (Prod.snd : (Fin n → ℝ) × X → X))
      (Prod.snd : (Fin k → ℝ) × ((Fin n → ℝ) × X) → (Fin n → ℝ) × X))
    (z : (Fin n → ℝ) → c.φ.model.E 1)
    (hzy : ∀ q, Φ q ∈ c.φ.source → c.φ.model.E.toBase 1 (z q) = c.φ (Φ q)) :
    ∃ Λ : SmoothSubspaceFamily (cubeModel n) (Fin n → unitInterval)
          (((PullbackChartData.ofProd ((PullbackChartData.ofProd c 0).toChart q₀) 0).toChart
            q₁).φ.model.E 0),
        (∀ t : Fin n → unitInterval, Λ.L t =
          ((PullbackChartData.ofProd ((PullbackChartData.ofProd c 0).toChart q₀) 0).toChart
            q₁).linKer
            (paramSection (sectionAdd (pullbackProj P Prod.snd) (paramLift f hf.isScSmooth.1) S)
              ((isSection_pullbackLift _).sectionAdd hS.1) s fun i => (hs i).1)
            ((0, ((fun i => (t i : ℝ)), z fun i => (t i : ℝ))) : ((PullbackChartData.ofProd
              ((PullbackChartData.ofProd c 0).toChart q₀) 0).toChart q₁).φ.model.E 1) ⊓
          LinearMap.ker (sliceProj k n (c.φ.model.E 0)).toLinearMap) ∧
        ContMDiffVectorBundle ∞ (Fin Λ.n → ℝ) Λ.Fiber (cubeModel n) := by
  obtain ⟨V, hIccV, -, Λ, hΛ, -⟩ :=
    lemma_6_6_5_smoothBundle hf hΦ hc hΦc hS hz hs hP q₀ q₁ z hzy
  set Λ' := Λ.comp (cubeToOpens V hIccV) (contMDiff_cubeToOpens V hIccV)
  exact ⟨Λ', fun t => hΛ _, inferInstance⟩

end Lemma665

end Polyfold
