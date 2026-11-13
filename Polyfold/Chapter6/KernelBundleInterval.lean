import Polyfold.Chapter6.SmoothKernelFrames
import Mathlib.Geometry.Manifold.Instances.Icc

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), §6.6, **Lemma 6.6.5**
(p. 265; preprint Lemma 6.30, p. 222): **`L` is a smooth vector bundle over `[0, 1]`**.
Gap G.65, row V6.34.

# The bundle `L` over the manifold with boundary `[0, 1]`

## The text, paraphrased

(Lemma 6.6.5) Along the family `t ↦ (t, φ(t), 0)`, `t ∈ [0, 1]`, the kernels `L_t` form a smooth
vector bundle `L` over `[0, 1]`.

## What is formalized

`lemma_6_6_5_smoothBundle` (`SmoothKernelFrames.lean`) gives `L` over an open connected
`V ⊇ [0, 1]ⁿ` in `ℝⁿ`.  Here:

* `SmoothSubspaceFamily.comp`: a smooth family of subspaces pulls back along a `C^∞` map of
  manifolds (with corners): `L ∘ g`, with the frames `e ∘ g`.
* `contMDiff_unitIntervalToOpens`: the inclusion `[0, 1] → V`, `t ↦ (t)`, is `C^∞` from Mathlib's
  manifold with boundary `[0, 1]` (model `𝓡∂ 1`) to the open subset `V` of `ℝ¹`.
* **`lemma_6_6_5_smoothBundle_interval`** (Lemma 6.6.5 over `[0, 1]` itself, `n = 1`): in the
  setting of `lemma_6_6_5_smoothBundle` for `n = 1`, there is a smooth family of subspaces over
  the manifold with boundary `[0, 1]` whose fibre at `t` is `L_t = ker F'(0, (t, z_t)) ∩ {dt = 0}`;
  it is a Mathlib `C^∞` vector bundle over `[0, 1]` (`ContMDiffVectorBundle ∞ … (𝓡∂ 1)`).

For `n ≥ 2` Mathlib has no smooth structure on the cube `[0, 1]ⁿ` (manifold with corners); the
same pull-back applies once one is available.
-/

open Set Filter Topology Function Bundle
open scoped ContDiff Manifold

noncomputable section

namespace Polyfold

universe u v

section Pullback

variable {EB : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB] {HB : Type*}
  [TopologicalSpace HB] {IB : ModelWithCorners ℝ EB HB} {B : Type*} [TopologicalSpace B]
  [ChartedSpace HB B] {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  {EB' : Type*} [NormedAddCommGroup EB'] [NormedSpace ℝ EB'] {HB' : Type*}
  [TopologicalSpace HB'] {IB' : ModelWithCorners ℝ EB' HB'} {B' : Type*} [TopologicalSpace B']
  [ChartedSpace HB' B']

/-- **The pull-back of a smooth family of subspaces along a `C^∞` map** `g : B' → B`:
`b' ↦ L(g(b'))`, with the frames `e ∘ g`. -/
def SmoothSubspaceFamily.comp (Λ : SmoothSubspaceFamily IB B W) (g : B' → B)
    (hg : ContMDiff IB' IB ∞ g) : SmoothSubspaceFamily IB' B' W where
  L b := Λ.L (g b)
  n := Λ.n
  finiteDimensional b := Λ.finiteDimensional (g b)
  finrank_eq b := Λ.finrank_eq (g b)
  exists_frame b₀ := by
    obtain ⟨U, hU, hb₀, e, he, h⟩ := Λ.exists_frame (g b₀)
    exact ⟨g ⁻¹' U, hU.preimage hg.continuous, hb₀, fun i => e i ∘ g,
      fun i => (he i).comp hg.contMDiffOn fun _ hb => hb, fun b hb => h (g b) hb⟩

theorem SmoothSubspaceFamily.comp_L (Λ : SmoothSubspaceFamily IB B W) (g : B' → B)
    (hg : ContMDiff IB' IB ∞ g) (b : B') : (Λ.comp g hg).L b = Λ.L (g b) := rfl

end Pullback

section Inclusion

/-- The inclusion `[0, 1] → V` into an open `V ⊇ [0, 1]` of `ℝ¹`. -/
def unitIntervalToOpens (V : TopologicalSpace.Opens (Fin 1 → ℝ))
    (hV : Icc (0 : Fin 1 → ℝ) 1 ⊆ V) (t : unitInterval) : V :=
  ⟨pt1 (t : ℝ), hV ⟨fun _ => t.2.1, fun _ => t.2.2⟩⟩

/-- **The inclusion `[0, 1] → V` is `C^∞`** from Mathlib's manifold with boundary `[0, 1]`
(model `𝓡∂ 1`) to the open subset `V` of `ℝ¹`. -/
theorem contMDiff_unitIntervalToOpens (V : TopologicalSpace.Opens (Fin 1 → ℝ))
    (hV : Icc (0 : Fin 1 → ℝ) 1 ⊆ V) :
    ContMDiff (𝓡∂ 1) 𝓘(ℝ, Fin 1 → ℝ) ∞ (unitIntervalToOpens V hV) := by
  refine (ContMDiff.subtypeVal_comp_iff V _).1 ?_
  have h1 : ContMDiff (𝓡∂ 1) 𝓘(ℝ) ∞ fun z : Icc (0 : ℝ) 1 => (z : ℝ) := contMDiff_subtypeVal_Icc
  have h2 : ContMDiff 𝓘(ℝ) 𝓘(ℝ, Fin 1 → ℝ) ∞ fun s : ℝ => pt1 s :=
    (contDiff_pi.2 fun _ => contDiff_id).contMDiff
  exact h2.comp h1

end Inclusion

/-! ### Lemma 6.6.5 over `[0, 1]` -/

section Lemma665

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle PX P}
  {f : X → Y} {k : ℕ}
  [ParacompactSpace ((Fin 1 → ℝ) × X)]
  [ParacompactSpace (pullbackSpace P (Prod.snd : (Fin 1 → ℝ) × X → X))]
  [ParacompactSpace ((Fin k → ℝ) × ((Fin 1 → ℝ) × X))]
  [ParacompactSpace (pullbackSpace (pullbackProj P (Prod.snd : (Fin 1 → ℝ) × X → X))
    (Prod.snd : (Fin k → ℝ) × ((Fin 1 → ℝ) × X) → (Fin 1 → ℝ) × X))]

/-- **2021 Lemma 6.6.5, p. 265, over `[0, 1]` itself: `L` is a smooth vector bundle over the
manifold with boundary `[0, 1]`** (preprint Lemma 6.30).  In the setting of
`lemma_6_6_5_smoothBundle` for a path (`n = 1`), there is a smooth family of subspaces over
`[0, 1]` (Mathlib's model `𝓡∂ 1`) whose fibre at `t` is
`L_t = ker F'(0, (t, z_t)) ∩ {dt = 0}` in the product chart; it is a `C^∞` vector bundle over
`[0, 1]`. -/
theorem lemma_6_6_5_smoothBundle_interval (hf : B.IsScFredholmSectionTame f)
    {Φ : (Fin 1 → ℝ) → X} (hΦ : (rnPolyfold 1).IsScSmoothMap PX Φ)
    {c : StrongBundleChart PX P} (hc : B.IsChart c)
    (hΦc : ∀ q ∈ Icc (0 : Fin 1 → ℝ) 1, Φ q ∈ c.φ.source)
    {S : (Fin 1 → ℝ) × X → pullbackSpace P (Prod.snd : (Fin 1 → ℝ) × X → X)}
    (hS : (B.pullback (MPolyfold.isScSmoothMap_snd (rnPolyfold 1) PX)).IsScPlusSection S)
    (hz : ∀ᶠ q in 𝓝ˢ (Icc (0 : Fin 1 → ℝ) 1), IsZeroAt (pullbackProj P Prod.snd)
      (sectionAdd (pullbackProj P Prod.snd) (paramLift f hf.isScSmooth.1) S) (q, Φ q))
    {s : Fin k → (Fin 1 → ℝ) × X → pullbackSpace P (Prod.snd : (Fin 1 → ℝ) × X → X)}
    (hs : ∀ i, (B.pullback (MPolyfold.isScSmoothMap_snd (rnPolyfold 1) PX)).IsScPlusSection (s i))
    (hP : ∀ᶠ q in 𝓝ˢ (Icc (0 : Fin 1 → ℝ) 1),
      ((B.pullback (MPolyfold.isScSmoothMap_snd (rnPolyfold 1) PX)).pullback
        (MPolyfold.isScSmoothMap_snd (rnPolyfold k)
          ((rnPolyfold 1).prod PX))).IsGeneralPositionGerm
        (paramSection (sectionAdd (pullbackProj P Prod.snd) (paramLift f hf.isScSmooth.1) S)
          ((isSection_pullbackLift _).sectionAdd hS.1) s fun i => (hs i).1) (0, (q, Φ q)))
    (q₀ : pullbackSpace P (Prod.snd : (Fin 1 → ℝ) × X → X))
    (q₁ : pullbackSpace (pullbackProj P (Prod.snd : (Fin 1 → ℝ) × X → X))
      (Prod.snd : (Fin k → ℝ) × ((Fin 1 → ℝ) × X) → (Fin 1 → ℝ) × X))
    (z : (Fin 1 → ℝ) → c.φ.model.E 1)
    (hzy : ∀ q, Φ q ∈ c.φ.source → c.φ.model.E.toBase 1 (z q) = c.φ (Φ q)) :
    ∃ Λ : SmoothSubspaceFamily (𝓡∂ 1) unitInterval
          (((PullbackChartData.ofProd ((PullbackChartData.ofProd c 0).toChart q₀) 0).toChart
            q₁).φ.model.E 0),
        (∀ t : unitInterval, Λ.L t =
          ((PullbackChartData.ofProd ((PullbackChartData.ofProd c 0).toChart q₀) 0).toChart
            q₁).linKer
            (paramSection (sectionAdd (pullbackProj P Prod.snd) (paramLift f hf.isScSmooth.1) S)
              ((isSection_pullbackLift _).sectionAdd hS.1) s fun i => (hs i).1)
            ((0, (pt1 (t : ℝ), z (pt1 (t : ℝ)))) : ((PullbackChartData.ofProd
              ((PullbackChartData.ofProd c 0).toChart q₀) 0).toChart q₁).φ.model.E 1) ⊓
          LinearMap.ker (sliceProj k 1 (c.φ.model.E 0)).toLinearMap) ∧
        ContMDiffVectorBundle ∞ (Fin Λ.n → ℝ) Λ.Fiber (𝓡∂ 1) := by
  obtain ⟨V, hIccV, -, Λ, hΛ, -⟩ :=
    lemma_6_6_5_smoothBundle hf hΦ hc hΦc hS hz hs hP q₀ q₁ z hzy
  set Λ' := Λ.comp (unitIntervalToOpens V hIccV) (contMDiff_unitIntervalToOpens V hIccV)
  exact ⟨Λ', fun t => hΛ _, inferInstance⟩

end Lemma665

end Polyfold
