import Polyfold.Chapter5.Compactness
import Polyfold.Chapter2.TangentMap

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part I, §2.3, the
paragraph after Definition 2.3.8 and Theorem 2.3.10: **sc-smooth maps are continuous on every
level `X_m` and on `X_∞`**.  Used for Theorem 12.5.7 (the homeomorphism `|O_f| → |O_{f'}|`).

# Sc-smooth maps on the levels

The text uses without comment that an sc-smooth map `f : X → Y` restricts to continuous maps
`X_m → Y_m` (it is sc⁰ in charts) and hence to a continuous map `X_∞ → Y_∞`.

* `continuousAt_levelLift`: `x ↦ φ(x) ∈ E_m` is continuous on the chart domain in `X_m`.
* `MPolyfold.IsScSmoothOn.continuousOn_level_comp`: for `f` sc-smooth on an open `U`, maps `u`
  into `X_m` and `v` into `Y_m` with `v = f ∘ u` (on the underlying points) and `u` continuous,
  `v` is continuous.
* `MPolyfold.IsScSmoothOn.continuousOn_smoothLevel`: the map `X_∞ ∩ U → Y_∞` of `f` is
  continuous (topology of Theorem 2.3.10).
-/

set_option maxSynthPendingDepth 3

open Set Function Topology Filter

noncomputable section

namespace Polyfold

namespace MPolyfold

universe u v w

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {P : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {Q : MPolyfold Y}

/-- **`x ↦ φ(x) ∈ E_m` is continuous on the chart domain in `X_m`** (the generating sets of the
topology of `X_m`). -/
theorem continuousAt_levelLift {φ : MChart X} (hφ : P.IsChart φ) {m : ℕ} {x₀ : P.Level m}
    (hx₀ : P.levelVal m x₀ ∈ φ.source) :
    ContinuousAt (fun x : P.Level m => levelLift φ m (P.levelVal m x)) x₀ := by
  intro W hW
  obtain ⟨W', hW'W, hW'o, hW'⟩ := mem_nhds_iff.1 hW
  exact mem_map.2 (mem_of_superset ((isOpen_level_basic hφ hW'o).mem_nhds ⟨hx₀, hW'⟩)
    fun x hx => hW'W hx.2)

/-- **An sc-smooth map is continuous on level `m`**, in the form: if `u : Z → X_m` is continuous
on `s`, takes values in `U ∩ X_m`, and `v : Z → Y_m` is `f ∘ u` on the underlying points, then
`v` is continuous on `s`.  In charts `φ`, `ψ`, `ψ(v z) = (ψ ∘ f ∘ φ⁻¹)(φ(u z))` and the coordinate
representation is sc⁰. -/
theorem IsScSmoothOn.continuousOn_level_comp {f : X → Y} {U : Set X} (hf : P.IsScSmoothOn Q f U)
    {m : ℕ} {Z : Type w} [TopologicalSpace Z] {s : Set Z} {u : Z → P.Level m} {v : Z → Q.Level m}
    (hu : ContinuousOn u s) (huU : ∀ z ∈ s, P.levelVal m (u z) ∈ U)
    (hv : ∀ z ∈ s, Q.levelVal m (v z) = f (P.levelVal m (u z))) : ContinuousOn v s := by
  intro z₀ hz₀
  refine (@TopologicalSpace.tendsto_nhds_generateFrom_iff Z (Q.levelSet m) (fun z => v z)
    (𝓝[s] z₀) (Q.levelBasis m) (v z₀)).2 ?_
  rintro _ ⟨ψ, hψ, W, hWo, rfl⟩ ⟨hz₀ψ, hz₀W⟩
  set x₀ := P.levelVal m (u z₀)
  obtain ⟨φ, hφ, hx₀φ⟩ := P.exists_isChart_mem_source x₀
  have hfx₀ : f x₀ ∈ ψ.source := hv z₀ hz₀ ▸ hz₀ψ
  set V := U ∩ φ.source ∩ f ⁻¹' ψ.source with hV
  have hVo : IsOpen V :=
    (hf.continuousOn.mono inter_subset_left).isOpen_inter_preimage
      (hf.isOpen.inter φ.isOpen_source) ψ.isOpen_source
  have hx₀V : x₀ ∈ V := ⟨⟨huU z₀ hz₀, hx₀φ⟩, hfx₀⟩
  have hVφ : V ⊆ φ.source := fun y hy => hy.1.2
  have hsm := hf.smooth φ ψ hφ hψ V hVo (fun y hy => hy.1) fun y hy => hy.2
  have hret := φ.isScRetract_image hVφ hVo
  have hsc0 := hsm.isSc0 hret
  set g := ψ ∘ f ∘ φ.symm with hg
  -- the lift of `u` to `E_m` lies in `(φ(V))_m`
  have hmem : ∀ z, P.levelVal m (u z) ∈ V →
      levelLift φ m (P.levelVal m (u z)) ∈ φ.model.E.lvlSet (φ '' V) m := fun z hz => by
    rw [ScBanach.mem_lvlSet, P.toBase_levelLift hφ (hVφ hz) (P.levelVal_mem (u z))]
    exact ⟨_, hz, rfl⟩
  -- `ψ(v z) = g(φ(u z))` in `E'_m`
  have hkey : ∀ z ∈ s, P.levelVal m (u z) ∈ V →
      levelLift ψ m (Q.levelVal m (v z)) = levelMap g m (levelLift φ m (P.levelVal m (u z))) := by
    intro z hz hzV
    apply ψ.model.E.toBase_injective m
    have hvψ : Q.levelVal m (v z) ∈ ψ.source := by rw [hv z hz]; exact hzV.2
    rw [hsc0.toBase_levelMap (hmem z hzV), P.toBase_levelLift hφ (hVφ hzV) (P.levelVal_mem _),
      Q.toBase_levelLift hψ hvψ (Q.levelVal_mem (v z))]
    simp only [hg, Function.comp_apply, φ.symm_apply_apply (hVφ hzV)]
    rw [hv z hz]
  -- continuity of the chart expression
  have hc1 : ContinuousWithinAt (fun z => levelLift φ m (P.levelVal m (u z))) s z₀ :=
    (continuousAt_levelLift hφ hx₀φ).comp_continuousWithinAt (hu z₀ hz₀)
  have hc2 : ContinuousWithinAt (levelMap g m) (φ.model.E.lvlSet (φ '' V) m)
      (levelLift φ m x₀) := hsc0.continuousOn m _ (hmem z₀ hx₀V)
  have hNV : ∀ᶠ z in 𝓝[s] z₀, P.levelVal m (u z) ∈ V :=
    (hu z₀ hz₀).preimage_mem_nhdsWithin
      ((hVo.preimage (P.continuous_levelVal m)).mem_nhds hx₀V)
  have hc3 : Tendsto (fun z => levelMap g m (levelLift φ m (P.levelVal m (u z)))) (𝓝[s] z₀)
      (𝓝 (levelMap g m (levelLift φ m x₀))) :=
    hc2.tendsto.comp (tendsto_nhdsWithin_iff.2 ⟨hc1.tendsto, hNV.mono fun z hz => hmem z hz⟩)
  have hW0 : levelMap g m (levelLift φ m x₀) ∈ W := by
    rw [← hkey z₀ hz₀ hx₀V]; exact hz₀W
  filter_upwards [hc3 (hWo.mem_nhds hW0), hNV, self_mem_nhdsWithin] with z hzW hzV hzs
  refine ⟨show Q.levelVal m (v z) ∈ ψ.source by rw [hv z hzs]; exact hzV.2, ?_⟩
  change levelLift ψ m (Q.levelVal m (v z)) ∈ W
  rw [hkey z hzs hzV]
  exact hzW

/-- **An sc-smooth map is continuous on `X_∞`** (topology of Theorem 2.3.10): if `f` is sc-smooth
on the open `U` and `g : X_∞ → Y_∞` is `f` on the points of `U`, then `g` is continuous on
`U ∩ X_∞`. -/
theorem IsScSmoothOn.continuousOn_smoothLevel {f : X → Y} {U : Set X} (hf : P.IsScSmoothOn Q f U)
    {g : P.SmoothLevel → Q.SmoothLevel}
    (hg : ∀ y, P.smoothVal y ∈ U → Q.smoothVal (g y) = f (P.smoothVal y)) :
    ContinuousOn g (P.smoothVal ⁻¹' U) := by
  rw [continuousOn_iff_continuous_domRestrict,
    (Topology.IsInducing.induced Q.smoothIncl).continuous_iff, continuous_pi_iff]
  intro m
  have h := hf.continuousOn_level_comp (s := P.smoothVal ⁻¹' U)
    (u := fun y => P.smoothIncl y m) (v := fun y => Q.smoothIncl (g y) m)
    (P.continuous_smoothIncl m).continuousOn (fun y hy => hy) fun y hy => hg y hy
  rw [continuousOn_iff_continuous_domRestrict] at h
  exact h

/-- **An sc-smooth map `X → Y` is continuous `X_∞ → Y_∞`.** -/
theorem IsScSmoothMap.continuous_smoothLevel {f : X → Y} (hf : P.IsScSmoothMap Q f)
    {g : P.SmoothLevel → Q.SmoothLevel} (hg : ∀ y, Q.smoothVal (g y) = f (P.smoothVal y)) :
    Continuous g := by
  have h := IsScSmoothOn.continuousOn_smoothLevel hf (g := g) fun y _ => hg y
  rw [preimage_univ] at h
  exact continuousOn_univ.1 h

end MPolyfold

end Polyfold
