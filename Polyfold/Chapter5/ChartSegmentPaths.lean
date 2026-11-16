import Polyfold.Chapter5.OrientableNbhd
import Polyfold.Chapter5.SmoothSetMaps

/-!
# Segment paths in charts

The segment path `chartSegPath` in a chart, its sc-smoothness and the continuity lemmas it uses. The
orientation space is in `Chapter6/OrientationSpace.lean`.
-/

set_option maxSynthPendingDepth 3
open Set Filter Topology Function
open scoped ContDiff
noncomputable section
namespace Polyfold
universe u v
variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle PX P}
  {f : X → Y}

/-- The chart `rnChart n 0` is modelled on the constant sc-structure: `ι_m = id`. -/
lemma rnChart_toBase {n : ℕ} (m : ℕ) (t : Fin n → ℝ) : (rnChart n 0).model.E.toBase m t = t :=
  ScBanach.const_toBase (Fin n → ℝ) m t

/-- The level-`m` coordinates `t ↦ φ(Γ(t)) ∈ E_m` of an sc-smooth map `Γ : ℝⁿ → X` in a chart
are continuous. -/
theorem continuousOn_levelLift_comp {n : ℕ} {Γ : (Fin n → ℝ) → X}
    (hΓ : (rnPolyfold n).IsScSmoothMap PX Γ) {φ : MChart X} (hφ : PX.IsChart φ) (m : ℕ) :
    ContinuousOn (fun t => MPolyfold.levelLift φ m (Γ t)) (Γ ⁻¹' φ.source) := by
  have hΓc : Continuous Γ := continuousOn_univ.1 hΓ.continuousOn
  set V := Γ ⁻¹' φ.source with hV
  have hVo : IsOpen V := φ.isOpen_source.preimage hΓc
  have hsm := hΓ.smooth (rnChart n 0) φ (isChart_rnChart 0) hφ V hVo
    (fun t _ => ⟨mem_univ _, mem_univ _⟩) (fun t ht => ht)
  have hret := (rnChart n 0).isScRetract_image (subset_univ V) hVo
  have hsc0 := hsm.isSc0 hret
  have hcont := hsc0.continuousOn m
  have himg : ∀ t ∈ V, t ∈ (rnChart n 0) '' V := fun t ht =>
    ⟨t, ht, show t - 0 = t from sub_zero t⟩
  have hmem : ∀ t ∈ V, (show (rnChart n 0).model.E m from t) ∈
      (rnChart n 0).model.E.lvlSet ((rnChart n 0) '' V) m := fun t ht => by
    rw [ScBanach.mem_lvlSet]
    simp only [rnChart_toBase]
    exact himg t ht
  have hkey : ∀ t ∈ V, MPolyfold.levelLift φ m (Γ t) =
      levelMap (φ ∘ Γ ∘ (rnChart n 0).symm) m (show (rnChart n 0).model.E m from t) := by
    intro t ht
    apply φ.model.E.toBase_injective m
    rw [hsc0.toBase_levelMap (hmem t ht), PX.toBase_levelLift hφ ht
      (mem_iInter.1 (mem_smoothSet_of_isScSmoothMap hΓ t) m)]
    simp only [rnChart_toBase]
    change φ (Γ t) = φ (Γ (t + 0))
    rw [add_zero]
  refine ContinuousOn.congr (f := fun t => levelMap (φ ∘ Γ ∘ (rnChart n 0).symm) m
    (show (rnChart n 0).model.E m from t)) ?_ hkey
  exact hcont.comp (continuous_id.continuousOn) hmem

/-- **An sc-smooth map `ℝⁿ → X` is continuous into `X_∞`** (topology of Theorem 2.3.10); for
`n = 1`: an sc-smooth path is a continuous path in `X_∞`. -/
theorem continuous_smoothMk_comp {n : ℕ} {Γ : (Fin n → ℝ) → X}
    (hΓ : (rnPolyfold n).IsScSmoothMap PX Γ) :
    Continuous fun t => PX.smoothMk (Γ t) (mem_smoothSet_of_isScSmoothMap hΓ t) := by
  have hΓc : Continuous Γ := continuousOn_univ.1 hΓ.continuousOn
  refine continuous_induced_rng.2 (continuous_pi fun m => ?_)
  change @Continuous _ _ _ (TopologicalSpace.generateFrom (PX.levelBasis m))
    fun t => (⟨Γ t, mem_iInter.1 (mem_smoothSet_of_isScSmoothMap hΓ t) m⟩ : PX.levelSet m)
  rw [continuous_generateFrom_iff]
  rintro s ⟨φ, hφ, W, hW, rfl⟩
  exact (continuousOn_levelLift_comp hΓ hφ m).isOpen_inter_preimage
    (φ.isOpen_source.preimage hΓc) hW

/-- The segment from `u₀` towards `u₁` in a local model, reparametrized by the smooth transition
function, retracted by `R` and read through the chart `φ` (as in `exists_nhds_scPath`). -/
def chartSegPath (φ : MChart X) (R : ScRetraction φ.model.E φ.model.C) (u₀ u₁ : φ.model.E 0) :
    (Fin 1 → ℝ) → X :=
  fun p => φ.symm (R (u₀ + Real.smoothTransition (p 0) • (u₁ - u₀)))

/-- `chartSegPath` is sc-smooth when the segment lies in the domain of the retraction and its
end points are smooth. -/
theorem isScSmoothMap_chartSegPath {φ : MChart X} (hφ : PX.IsChart φ)
    {R : ScRetraction φ.model.E φ.model.C} (hR : R.retract = φ.model.O) {u₀ u₁ : φ.model.E 0}
    (h₀ : u₀ ∈ φ.model.E.smooth) (h₁ : u₁ ∈ φ.model.E.smooth)
    (hU : ∀ p : Fin 1 → ℝ, u₀ + Real.smoothTransition (p 0) • (u₁ - u₀) ∈ R.U) :
    (rnPolyfold 1).IsScSmoothMap PX (chartSegPath φ R u₀ u₁) := by
  have hU1 := isScDomain_univ (rnSc 1)
  have hc₀ : IsScSmooth (E := rnSc 1) (F := φ.model.E) univ fun _ => u₀ :=
    isScSmooth_const_of_mem_smooth hU1 h₀
  have hc₁ : IsScSmooth (E := rnSc 1) (F := φ.model.E) univ fun _ => u₁ - u₀ :=
    isScSmooth_const_of_mem_smooth hU1 (sub_mem h₁ h₀)
  have hρ : IsScSmooth (E := rnSc 1) (F := ScBanach.const ℝ) univ
      fun p : Fin 1 → ℝ => Real.smoothTransition (p 0) :=
    IsScSmooth.of_contDiffOn_finiteDimensional (V := ℝ) hU1
      ((Real.smoothTransition.contDiff.comp (contDiff_apply ℝ ℝ (0 : Fin 1))).contDiffOn)
  have hG : IsScSmooth (E := rnSc 1) (F := φ.model.E) univ
      fun p => u₀ + Real.smoothTransition (p 0) • (u₁ - u₀) :=
    hc₀.add hU1 (hρ.smul hU1 hc₁)
  have hrG : IsScSmooth (E := rnSc 1) (F := φ.model.E) univ
      fun p => R (u₀ + Real.smoothTransition (p 0) • (u₁ - u₀)) :=
    IsScSmooth.comp hU1 R.isScDomain R.isScSmooth hG fun p _ => hU p
  exact isScSmoothMap_rn_chart_symm hφ hrG fun p => hR ▸ R.apply_mem_retract (hU p)

end Polyfold
end
