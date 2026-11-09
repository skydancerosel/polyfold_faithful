import Polyfold.Chapter6.OrientationFunctor
import Polyfold.Chapter5.Compactness

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Chapter 6, §6.6 "Local
Orientation Propagation": **Theorem 6.6.17**, p. 275 (new in the 2021 edition; the 2017 text has the
orientations of Definition 6.13 but no topology on `O_f`), and the orientation space `O_f`
defined just before it (pp. 274–275).

# The orientation space `O_f`

## The text, paraphrased

(pp. 274–275) Let `f` be an sc-Fredholm section of a strong bundle `P : Y → X` over a tame
M-polyfold, and give `X_∞` its natural metrizable topology.  The orientation space `O_f` consists
of the pairs `(x, o)` with `x ∈ X_∞` and `o` an orientation of `DET(f, x)`; over each `x` there are
exactly two, `(x, ±o)`; `π_f : O_f → X_∞` is `(x, o) ↦ x`.

(Theorem 6.6.17, p. 275) There is a uniquely defined Hausdorff topology on `O_f` characterized by:
(1) `π_f` is a local homeomorphism; (2) every `x ∈ X_∞` has an open neighbourhood `U` in `X` such
that `O_f` has precisely two continuous sections over `U ∩ X_∞`; (3) for an sc-smooth path
`φ : [0, 1] → X`, a continuous section `t ↦ (φ(t), o_t)` of the pull-back `φ*O_f → [0, 1]` has,
for every `t₀` and all `t` close to `t₀`, `o_t` equal to the local propagation of `o_{t₀}`.  The
text leaves the proof to the reader, in view of Proposition 6.6.3 and Theorem 6.6.11.  (After the
theorem) `π_f` is the orientation bundle of `f`; `f` is orientable iff `π_f` has a global
continuous section; `ℤ₂` acts on `O_f`, and `det_f = ℝ ⊗_{ℤ₂} O_f`.

## What is formalized

* `OrSpace` (`O_f`, a sigma type over `MPolyfold.SmoothLevel`, the space `X_∞` with the topology
  of Theorem 2.3.10, `theorem_2_3_10`), `orProj` (`π_f`), `OrPullback` (`φ*O_f`), and the three
  properties: `IsLocalHomeomorph` (1), `HasTwoContSections` (2), `IsPropagationContinuous` (3);
  `IsOrientationTopology` collects them with `T2Space`.
* `orTopology L` for local transport data `L` (`LocalTransport`, `PathTransport.lean`): `W` is open
  iff `{y ∈ U_∞ | (y, o_y) ∈ W}` is open in `X_∞` for every continuous orientation `o` over an
  open `U` (`IsContOrOn`: `o` is carried along by the transport along every sc-smooth path in
  `U`).  For every `L`: `isOpen_orBasic`, `orChartHomeo` (the local description: `π_f` restricted
  to `{(y, o_y) | y ∈ U_∞}` is a homeomorphism onto `U_∞`), `isLocalHomeomorph_orProj` (1) and
  `t2Space_orTopology` (Hausdorff).
* With `L = orLocalTransport` (the data of `Γ_f`, Theorem 6.6.13, `orFunctor`):
  `isPropagationContinuous_orTopology` (3); `eq_orTopology_of`: **every topology with (1) and
  (3) is `orTopology`** (uniqueness; neither Hausdorffness nor (2) is used);
  `existsUnique_orientationTopology` (exactly one Hausdorff topology with (1) and (3), no
  further hypothesis); `theorem_6_6_17_hyp` (the theorem with (1)–(3), under
  `MPolyfold.HasConnectedSmoothNbhds`).
* Two facts on `X_∞` used for uniqueness: `continuous_smoothMk_comp` (an sc-smooth map `ℝⁿ → X`
  is continuous into `X_∞`) and `eventually_exists_scPath_smoothLevel` (points of `X_∞` close to
  `x` are joined to `x` by sc-smooth paths staying in a given neighbourhood of `x` in `X_∞`).
* `hasTwoContSections_orTopology` (2) under `MPolyfold.HasConnectedSmoothNbhds`, with the
  witnesses `rnPolyfold_hasConnectedSmoothNbhds` (`ℝⁿ`) and
  `MPolyfold.hasConnectedSmoothNbhds_of_subsingleton`.

## What the text leaves implicit, and the choices made

* Paths are the sc-smooth maps `ℝ → X` of Chapter 6 restricted to `[0, 1]`; their values are
  smooth points (`mem_smoothSet_of_isScSmoothMap`), so `φ*O_f` makes sense; it is the subspace
  `{(t, p) | φ(t) = π_f(p)}` of `[0, 1] × O_f`.
* "`o_t` is the local propagation of `o_{t₀}`": for `t` near `t₀` there is an open set `U` with
  the local propagation property in some chart (`IsPropagationNbhd`) containing `φ([t₀, t])`, and
  the push-forward `orPush` along the segment `φ|[t₀, t]` (`segPath`) maps `o_{t₀}` to `o_t`; the
  push-forward does not depend on `U` (`orPush_compat`).
* A continuous section over `U ∩ X_∞` is a continuous `σ : U_∞ → O_f` with `π_f ∘ σ = id`, `U_∞`
  carrying the subspace topology of `X_∞`.
* The hypotheses are those under which the repository constructs `Γ_f` (`orFunctor`): `X` tame
  with bump functions, `f` an sc-Fredholm section with tame germs, sc⁺-sections through every
  point (which give the two orientations over each point), and the paracompactness instances of
  the products with `ℝⁿ`.

## Items not formalized

* Property (2) is proved under `MPolyfold.HasConnectedSmoothNbhds`: every smooth point has
  arbitrarily small open neighbourhoods `U` in `X` whose smooth part `U ∩ X_∞` is connected in
  `X_∞`.  Every continuous section over `U_∞` is locally one of the two continuous orientations,
  so (2) needs a neighbourhood `U` with connected `U_∞`; `exists_nhds_scPath` only joins smooth
  points of a small `V` by paths in a larger `U`.  We have not found this fact in the text; it
  holds for `ℝⁿ` and is open in general (proposed gap).
* The remarks after the theorem (orientation bundle, orientability iff a global continuous
  section, the `ℤ₂`-action, `det_f`) are not formalized.
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

/-! ### Sc-smooth paths in `X_∞` -/

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

/-- **Small sc-smooth paths in `X_∞`**: for a neighbourhood `N` of `x` in `X_∞` (topology of
Theorem 2.3.10), every `y ∈ X_∞` close to `x` is joined to `x` by an sc-smooth path all of whose
points lie in `N`. -/
theorem eventually_exists_scPath_smoothLevel (x : PX.SmoothLevel) {N : Set PX.SmoothLevel}
    (hN : N ∈ 𝓝 x) :
    ∀ᶠ y in 𝓝 x, ∃ (γ : (Fin 1 → ℝ) → X) (hγ : (rnPolyfold 1).IsScSmoothMap PX γ),
      γ (pt1 0) = PX.smoothVal x ∧ γ (pt1 1) = PX.smoothVal y ∧
      ∀ t, PX.smoothMk (γ t) (mem_smoothSet_of_isScSmoothMap hγ t) ∈ N := by
  classical
  obtain ⟨φ, hφ, hxφ⟩ := PX.exists_isChart_mem_source (PX.smoothVal x)
  obtain ⟨R, hR⟩ := φ.model.isScRetract
  set u₀ := φ (PX.smoothVal x) with hu₀def
  have hOR : ∀ {u}, u ∈ φ.model.O → u ∈ R.retract := fun hu => hR ▸ hu
  have hu₀R : u₀ ∈ R.retract := hOR (φ.mapsTo_model _ hxφ)
  have hu₀U : u₀ ∈ R.U := R.retract_subset hu₀R
  have hRu₀ : R u₀ = u₀ := R.apply_eq_self_of_mem_retract hu₀R
  obtain ⟨O', hO'o, hO'⟩ := R.relOpen.relOpen
  have hUC : R.U ⊆ φ.model.C := by rw [hO']; exact inter_subset_right
  have hCconv : Convex ℝ φ.model.C := R.relOpen.isPartialQuadrant.convex
  obtain ⟨δ, hδ, hδO'⟩ := Metric.isOpen_iff.1 hO'o u₀ (by
    have := hu₀U
    rw [hO'] at this
    exact this.1)
  have hsm : ∀ {y}, y ∈ φ.source → y ∈ PX.smoothSet → φ y ∈ φ.model.E.smooth := fun hy hys =>
    φ.model.E.mem_smooth_iff.2 fun m => (PX.mem_levelSet_iff hφ hy).1 (mem_iInter.1 hys m)
  have hκ : ∀ p : Fin 1 → ℝ, Real.smoothTransition (p 0) ∈ Icc (0 : ℝ) 1 := fun p =>
    ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩
  -- the segment lies in `U`
  have hseg : ∀ {u}, u ∈ φ.model.O → u ∈ Metric.ball u₀ δ → ∀ p : Fin 1 → ℝ,
      u₀ + Real.smoothTransition (p 0) • (u - u₀) ∈ R.U := fun hu hub p => by
    rw [hO']
    exact ⟨hδO' ((convex_ball u₀ δ).add_smul_sub_mem (Metric.mem_ball_self hδ) hub (hκ p)),
      hCconv.add_smul_sub_mem (hUC hu₀U) (hUC (R.retract_subset (hOR hu))) (hκ p)⟩
  -- level `0`: eventually `y` is in the chart and `φ(y)` is close to `u₀`
  have hφc : ContinuousAt (fun y : PX.SmoothLevel => φ (PX.smoothVal y)) x :=
    (φ.continuousOn_toFun.continuousAt (φ.isOpen_source.mem_nhds hxφ)).comp
      PX.continuous_smoothVal.continuousAt
  have hAo : IsOpen {y : PX.SmoothLevel | PX.smoothVal y ∈ φ.source} :=
    φ.isOpen_source.preimage PX.continuous_smoothVal
  have hev0 : ∀ᶠ y in 𝓝 x, PX.smoothVal y ∈ φ.source ∧ φ (PX.smoothVal y) ∈ Metric.ball u₀ δ := by
    filter_upwards [hAo.mem_nhds hxφ, hφc (Metric.ball_mem_nhds _ hδ)] with y h1 h2
    exact ⟨h1, h2⟩
  -- the paths
  set γ : PX.SmoothLevel → (Fin 1 → ℝ) → X := fun y => chartSegPath φ R u₀ (φ (PX.smoothVal y))
  have hγO : ∀ y, PX.smoothVal y ∈ φ.source → φ (PX.smoothVal y) ∈ Metric.ball u₀ δ →
      ∀ p : Fin 1 → ℝ,
        R (u₀ + Real.smoothTransition (p 0) • (φ (PX.smoothVal y) - u₀)) ∈ φ.model.O :=
    fun y h1 h2 p => hR ▸ R.apply_mem_retract (hseg (φ.mapsTo_model _ h1) h2 p)
  -- reduce `N` to finitely many levels
  rw [nhds_induced, nhds_pi, Filter.mem_comap] at hN
  obtain ⟨T, hT, hTN⟩ := hN
  obtain ⟨I, hI, V, hV, hIV⟩ := Filter.mem_pi.1 hT
  have hlev : ∀ m ∈ I, ∀ᶠ y in 𝓝 x, ∀ p, ∀ z : PX.Level m, PX.levelVal m z = γ y p →
      z ∈ V m := by
    intro m _
    have hemb := PX.isEmbedding_levelLift hφ m
    set S := (PX.levelVal m ⁻¹' φ.source : Set (PX.Level m)) with hS
    have hVm : (Subtype.val ⁻¹' V m : Set S) ∈ 𝓝 (⟨PX.smoothIncl x m, hxφ⟩ : S) :=
      continuous_subtype_val.continuousAt.preimage_mem_nhds (hV m)
    rw [hemb.isInducing.nhds_eq_comap, Filter.mem_comap] at hVm
    obtain ⟨G, hG, hGV⟩ := hVm
    set u₀m := MPolyfold.levelLift φ m (PX.smoothVal x) with hu₀mdef
    have hu₀m : φ.model.E.toBase m u₀m = u₀ :=
      PX.toBase_levelLift hφ hxφ (mem_iInter.1 (PX.smoothVal_mem x) m)
    have hu₀mU : u₀m ∈ φ.model.E.lvlSet R.U m := by
      rw [ScBanach.mem_lvlSet, hu₀m]; exact hu₀U
    have hRm : levelMap R m u₀m = u₀m := levelMap_eq_of_toBase_eq (by rw [hu₀m, hRu₀])
    have hcont := (R.isSc1.isSc0.continuousOn m) u₀m hu₀mU
    have hG' : G ∈ 𝓝 (levelMap R m u₀m) := by rw [hRm]; exact hG
    obtain ⟨ζ, hζ, hζG⟩ := Metric.mem_nhdsWithin_iff.1 (hcont hG')
    -- continuity of `y ↦ φ(y)` on level `m`
    have hcA : ContinuousOn (fun y : PX.SmoothLevel => MPolyfold.levelLift φ m (PX.smoothVal y))
        {y : PX.SmoothLevel | PX.smoothVal y ∈ φ.source} := by
      rw [continuousOn_iff_continuous_domRestrict]
      exact hemb.continuous.comp (((PX.continuous_smoothIncl m).comp
        continuous_subtype_val).subtype_mk fun y => y.2)
    have hFc := (hcA.continuousAt (hAo.mem_nhds hxφ)) (Metric.ball_mem_nhds u₀m hζ)
    filter_upwards [hAo.mem_nhds hxφ, hFc, hev0] with y hyφ hyζ hy0 p z hz
    set ym := MPolyfold.levelLift φ m (PX.smoothVal y) with hymdef
    have hym : φ.model.E.toBase m ym = φ (PX.smoothVal y) :=
      PX.toBase_levelLift hφ hyφ (mem_iInter.1 (PX.smoothVal_mem y) m)
    set v := u₀m + Real.smoothTransition (p 0) • (ym - u₀m) with hvdef
    have hv : φ.model.E.toBase m v =
        u₀ + Real.smoothTransition (p 0) • (φ (PX.smoothVal y) - u₀) := by
      rw [hvdef, map_add, map_smul, map_sub, hu₀m, hym]
    have hvU : v ∈ φ.model.E.lvlSet R.U m := by
      rw [ScBanach.mem_lvlSet, hv]
      exact hseg (φ.mapsTo_model _ hyφ) hy0.2 p
    have hvball : v ∈ Metric.ball u₀m ζ :=
      (convex_ball u₀m ζ).add_smul_sub_mem (Metric.mem_ball_self hζ) hyζ (hκ p)
    have hRv : levelMap R m v ∈ G := hζG ⟨hvball, hvU⟩
    have hzO := hγO y hy0.1 hy0.2 p
    have hzφ : PX.levelVal m z ∈ φ.source := by
      rw [hz]; exact φ.symm_mapsTo hzO
    have hlift : MPolyfold.levelLift φ m (PX.levelVal m z) = levelMap R m v := by
      apply φ.model.E.toBase_injective m
      rw [PX.toBase_levelLift hφ hzφ (PX.levelVal_mem z), R.isSc1.isSc0.toBase_levelMap hvU, hv,
        hz]
      exact φ.apply_symm_apply hzO
    exact @hGV ⟨z, hzφ⟩ (show MPolyfold.levelLift φ m (PX.levelVal m z) ∈ G by
      rw [hlift]; exact hRv)
  filter_upwards [hev0, (Filter.eventually_all_finite hI).2 hlev] with y hy0 hyl
  have hy1O : φ (PX.smoothVal y) ∈ φ.model.O := φ.mapsTo_model _ hy0.1
  have hγs : (rnPolyfold 1).IsScSmoothMap PX (γ y) :=
    isScSmoothMap_chartSegPath hφ hR (hsm hxφ (PX.smoothVal_mem x))
      (hsm hy0.1 (PX.smoothVal_mem y)) (hseg hy1O hy0.2)
  refine ⟨γ y, hγs, ?_, ?_, fun t => hTN (hIV fun m hm => hyl m hm t
    (PX.smoothIncl (PX.smoothMk _ (mem_smoothSet_of_isScSmoothMap hγs t)) m) rfl)⟩
  · change φ.symm (R (u₀ + Real.smoothTransition ((pt1 0 : Fin 1 → ℝ) 0) •
      (φ (PX.smoothVal y) - u₀))) = PX.smoothVal x
    rw [pt1_apply, Real.smoothTransition.zero, zero_smul, add_zero, hRu₀, hu₀def,
      φ.symm_apply_apply hxφ]
  · change φ.symm (R (u₀ + Real.smoothTransition ((pt1 1 : Fin 1 → ℝ) 0) •
      (φ (PX.smoothVal y) - u₀))) = PX.smoothVal y
    rw [pt1_apply, Real.smoothTransition.one, one_smul, add_sub_cancel,
      R.apply_eq_self_of_mem_retract (hOR hy1O), φ.symm_apply_apply hy0.1]

/-! ### The orientation space -/

variable (f) in
/-- **The orientation space `O_f`** (2021, pp. 274–275, before Theorem 6.6.17): the pairs
`(x, o)` of a smooth point `x ∈ X_∞` and an orientation `o` of `DET(f, x)`, i.e. `o ∈ Or_x^f`. -/
def OrSpace (hf : B.IsScFredholmSection f) : Type _ :=
  Σ x : PX.SmoothLevel, Orx f hf (PX.smoothVal x) (PX.smoothVal_mem x)

variable (f) in
/-- **The projection `π_f : O_f → X_∞`**, `(x, o) ↦ x`. -/
def orProj (hf : B.IsScFredholmSection f) : OrSpace f hf → PX.SmoothLevel := Sigma.fst

/-- The segment `s ↦ φ(a + s (b − a))` of a path `φ`, from `φ(a)` to `φ(b)`. -/
def segPath (φ : (Fin 1 → ℝ) → X) (a b : ℝ) : (Fin 1 → ℝ) → X :=
  fun s => φ (pt1 (a + s 0 * (b - a)))

/-- A segment of an sc-smooth path is sc-smooth. -/
theorem isScSmoothMap_segPath {φ : (Fin 1 → ℝ) → X} (hφ : (rnPolyfold 1).IsScSmoothMap PX φ)
    (a b : ℝ) : (rnPolyfold 1).IsScSmoothMap PX (segPath φ a b) :=
  isScSmoothMap_reparam hφ (κ := fun s => a + s * (b - a))
    (contDiff_const.add (contDiff_id.mul contDiff_const))

omit [TopologicalSpace X] [T2Space X] [ParacompactSpace X] in
/-- The segment starts at `φ(a)`. -/
@[simp] lemma segPath_zero (φ : (Fin 1 → ℝ) → X) (a b : ℝ) : segPath φ a b (pt1 0) = φ (pt1 a) := by
  simp [segPath]

omit [TopologicalSpace X] [T2Space X] [ParacompactSpace X] in
/-- The segment ends at `φ(b)`. -/
@[simp] lemma segPath_one (φ : (Fin 1 → ℝ) → X) (a b : ℝ) : segPath φ a b (pt1 1) = φ (pt1 b) := by
  simp [segPath]

variable (f) in
/-- **The pull-back `φ*O_f`** along a path `φ`: the pairs `(t, p) ∈ [0, 1] × O_f` with
`φ(t) = π_f(p)`. -/
def OrPullback (hf : B.IsScFredholmSection f) (φ : (Fin 1 → ℝ) → X) :
    Set (unitInterval × OrSpace f hf) :=
  {q | φ (pt1 (q.1 : ℝ)) = PX.smoothVal q.2.1}

variable (f) in
/-- A **continuous section of `O_f` over `U ∩ X_∞`** for a topology `t` on `O_f`. -/
def IsContSectionOver (hf : B.IsScFredholmSection f) (t : TopologicalSpace (OrSpace f hf))
    (U : Set X) (σ : PX.smoothVal ⁻¹' U → OrSpace f hf) : Prop :=
  @Continuous _ _ _ t σ ∧ ∀ y, (σ y).1 = y

section Statement

variable [∀ n : ℕ, ParacompactSpace ((Fin n → ℝ) × X)]
  [∀ n : ℕ, ParacompactSpace (pullbackSpace P (Prod.snd : (Fin n → ℝ) × X → X))]

variable (f) in
/-- **Property (3)** of 2021 Theorem 6.6.17 for a topology `t` on `O_f`: for an sc-smooth path
`φ` and a continuous section `α(t) = (t, (φ(t), o_t))` of `φ*O_f`, for `t` near `t₀` the
orientation `o_t` is the push-forward of `o_{t₀}` along `φ|[t₀, t]` in a propagation
neighbourhood. -/
def IsPropagationContinuous (hf : B.IsScFredholmSection f) (t : TopologicalSpace (OrSpace f hf)) :
    Prop :=
  letI := t
  ∀ (φ : (Fin 1 → ℝ) → X) (hφ : (rnPolyfold 1).IsScSmoothMap PX φ)
    (α : unitInterval → OrPullback f hf φ), Continuous α → (∀ s, (α s).1.1 = s) →
    ∀ t₀ : unitInterval, ∀ᶠ t : unitInterval in 𝓝 t₀, ∃ (U : Set X)
      (hU : IsPropagationNbhd f hf U) (hseg : ∀ s ∈ Icc (0 : ℝ) 1, segPath φ t₀ t (pt1 s) ∈ U)
      (h₀ : segPath φ t₀ t (pt1 0) = PX.smoothVal (α t₀).1.2.1)
      (h₁ : segPath φ t₀ t (pt1 1) = PX.smoothVal (α t).1.2.1),
      orPush hU (segPath φ t₀ t) (isScSmoothMap_segPath hφ t₀ t) hseg h₀ h₁
        (PX.smoothVal_mem _) (PX.smoothVal_mem _) (α t₀).1.2.2 = (α t).1.2.2

variable (f) in
/-- **Property (2)** of 2021 Theorem 6.6.17 for a topology `t` on `O_f`: every `x ∈ X_∞` has an
open neighbourhood `U` in `X` over whose smooth part `O_f` has precisely two continuous sections. -/
def HasTwoContSections (hf : B.IsScFredholmSection f) (t : TopologicalSpace (OrSpace f hf)) :
    Prop :=
  ∀ x : PX.SmoothLevel, ∃ U : Set X, IsOpen U ∧ PX.smoothVal x ∈ U ∧
    ∃ σ₁ σ₂ : PX.smoothVal ⁻¹' U → OrSpace f hf, IsContSectionOver f hf t U σ₁ ∧
      IsContSectionOver f hf t U σ₂ ∧ σ₁ ≠ σ₂ ∧
      ∀ σ, IsContSectionOver f hf t U σ → σ = σ₁ ∨ σ = σ₂

variable (f) in
/-- **The properties of 2021 Theorem 6.6.17** of a topology on `O_f`: Hausdorff, (1) `π_f` is a
local homeomorphism, (2) and (3). -/
structure IsOrientationTopology (hf : B.IsScFredholmSection f)
    (t : TopologicalSpace (OrSpace f hf)) : Prop where
  t2Space : @T2Space _ t
  isLocalHomeomorph : @IsLocalHomeomorph _ _ t _ (orProj f hf)
  twoSections : HasTwoContSections f hf t
  propagation : IsPropagationContinuous f hf t

end Statement

/-! ### The topology -/

section Topology

variable {hf : B.IsScFredholmSection f} (L : LocalTransport PX fun x hs => Orx f hf x hs)

/-- A **continuous orientation over an open set `U`**: `o` carried along by the transport along
every sc-smooth path in `U`. -/
def IsContOrOn (U : Set X) (o : ∀ y (hy : y ∈ PX.smoothSet), Orx f hf y hy) : Prop :=
  IsOpen U ∧ ∀ (γ : (Fin 1 → ℝ) → X) (hγ : (rnPolyfold 1).IsScSmoothMap PX γ),
    (∀ s ∈ Icc (0 : ℝ) 1, γ (pt1 s) ∈ U) → ∀ {x₀ x₁ : X} (h₀ : γ (pt1 0) = x₀)
      (h₁ : γ (pt1 1) = x₁) (hs₀ : x₀ ∈ PX.smoothSet) (hs₁ : x₁ ∈ PX.smoothSet),
      L.transport γ hγ h₀ h₁ hs₀ hs₁ (o x₀ hs₀) = o x₁ hs₁

/-- The section `y ↦ (y, o_y)`. -/
def orSec (o : ∀ y (hy : y ∈ PX.smoothSet), Orx f hf y hy) (y : PX.SmoothLevel) :
    OrSpace f hf :=
  ⟨y, o (PX.smoothVal y) (PX.smoothVal_mem y)⟩

/-- The image `{(y, o_y) | y ∈ U_∞}` of a section. -/
def orBasic (U : Set X) (o : ∀ y (hy : y ∈ PX.smoothSet), Orx f hf y hy) : Set (OrSpace f hf) :=
  {p | PX.smoothVal p.1 ∈ U ∧ p.2 = o (PX.smoothVal p.1) (PX.smoothVal_mem p.1)}

/-- **The topology of `O_f`**: `W` is open iff `{y ∈ U_∞ | (y, o_y) ∈ W}` is open in `X_∞` for
every continuous orientation `o` over an open `U`. -/
@[instance_reducible] def orTopology : TopologicalSpace (OrSpace f hf) where
  IsOpen W := ∀ U o, IsContOrOn L U o →
    IsOpen {y : PX.SmoothLevel | PX.smoothVal y ∈ U ∧ orSec o y ∈ W}
  isOpen_univ U o h := by
    simp only [mem_univ, and_true]
    exact h.1.preimage PX.continuous_smoothVal
  isOpen_inter W₁ W₂ h₁ h₂ U o h := by
    convert (h₁ U o h).inter (h₂ U o h) using 1
    ext y
    exact ⟨fun ⟨a, b, c⟩ => ⟨⟨a, b⟩, a, c⟩, fun ⟨⟨a, b⟩, _, c⟩ => ⟨a, b, c⟩⟩
  isOpen_sUnion S hS U o h := by
    have : {y : PX.SmoothLevel | PX.smoothVal y ∈ U ∧ orSec o y ∈ ⋃₀ S} =
        ⋃ W ∈ S, {y | PX.smoothVal y ∈ U ∧ orSec o y ∈ W} := by
      ext y
      simp only [mem_iUnion, exists_prop]
      exact ⟨fun ⟨a, W, hW, b⟩ => ⟨W, hW, a, b⟩, fun ⟨W, hW, a, b⟩ => ⟨a, W, hW, b⟩⟩
    rw [this]
    exact isOpen_biUnion fun W hW => hS W hW U o h

variable {L}

/-! ### Paths in an open set -/

/-- **Smooth points near `x` are joined by sc-smooth paths in an open `W ∋ x`**
(`exists_nhds_scPath` in a chart of the strong bundle at `x`). -/
theorem exists_nhds_scPath_of_isOpen (B : StrongBundle PX P) {W : Set X} (hW : IsOpen W) {x : X}
    (hx : x ∈ W) :
    ∃ V : Set X, IsOpen V ∧ x ∈ V ∧ V ⊆ W ∧ ∀ y₁ ∈ V, ∀ y₂ ∈ V, y₁ ∈ PX.smoothSet →
      y₂ ∈ PX.smoothSet → ∃ γ : (Fin 1 → ℝ) → X, (rnPolyfold 1).IsScSmoothMap PX γ ∧
        γ (pt1 0) = y₁ ∧ γ (pt1 1) = y₂ ∧ ∀ t, γ t ∈ W := by
  obtain ⟨c, hcB, hxc⟩ := B.exists_chart_mem x
  obtain ⟨V, hVo, hxV, hVW, hpath⟩ := exists_nhds_scPath (B.isChart_of_mem hcB)
    (hW.inter c.φ.isOpen_source) inter_subset_right ⟨hx, hxc⟩
  refine ⟨V, hVo, hxV, fun y hy => (hVW hy).1, fun y₁ hy₁ y₂ hy₂ hs₁ hs₂ => ?_⟩
  obtain ⟨γ, hγ, h₀, h₁, hγW⟩ := hpath y₁ hy₁ y₂ hy₂ hs₁ hs₂
  exact ⟨γ, hγ, h₀, h₁, fun t => (hγW t).1⟩

/-- **Two continuous orientations agree near a point iff they agree at it.** -/
theorem IsContOrOn.eventually_iff {U U' : Set X} {o o' : ∀ y (hy : y ∈ PX.smoothSet), Orx f hf y hy}
    (h : IsContOrOn L U o) (h' : IsContOrOn L U' o') {x : PX.SmoothLevel}
    (hx : PX.smoothVal x ∈ U) (hx' : PX.smoothVal x ∈ U') :
    ∀ᶠ y in 𝓝 x, PX.smoothVal y ∈ U ∧ PX.smoothVal y ∈ U' ∧
      (o (PX.smoothVal y) (PX.smoothVal_mem y) = o' (PX.smoothVal y) (PX.smoothVal_mem y) ↔
        o (PX.smoothVal x) (PX.smoothVal_mem x) = o' (PX.smoothVal x) (PX.smoothVal_mem x)) := by
  obtain ⟨V, hVo, hxV, hVW, hpath⟩ := exists_nhds_scPath_of_isOpen B (h.1.inter h'.1) ⟨hx, hx'⟩
  filter_upwards [(hVo.preimage PX.continuous_smoothVal).mem_nhds hxV] with y hy
  obtain ⟨γ, hγ, h₀, h₁, hγW⟩ := hpath _ hxV _ hy (PX.smoothVal_mem x) (PX.smoothVal_mem y)
  refine ⟨(hVW hy).1, (hVW hy).2, ?_⟩
  rw [← h.2 γ hγ (fun s _ => (hγW _).1) h₀ h₁ (PX.smoothVal_mem x) (PX.smoothVal_mem y),
    ← h'.2 γ hγ (fun s _ => (hγW _).2) h₀ h₁ (PX.smoothVal_mem x) (PX.smoothVal_mem y)]
  exact (L.transport γ hγ h₀ h₁ _ _).apply_eq_iff_eq

/-! ### The local description -/

/-- The sets `{(y, o_y) | y ∈ U_∞}` of continuous orientations are open. -/
theorem isOpen_orBasic {U : Set X} {o : ∀ y (hy : y ∈ PX.smoothSet), Orx f hf y hy}
    (h : IsContOrOn L U o) : IsOpen[orTopology L] (orBasic U o) := by
  intro U' o' h'
  refine isOpen_iff_mem_nhds.2 fun y hy => ?_
  filter_upwards [h'.eventually_iff h hy.1 hy.2.1] with z hz
  exact ⟨hz.1, hz.2.1, hz.2.2.2 hy.2.2⟩

/-- A continuous orientation is a continuous section over `U_∞`. -/
theorem continuousOn_orSec {U : Set X} {o : ∀ y (hy : y ∈ PX.smoothSet), Orx f hf y hy}
    (h : IsContOrOn L U o) :
    @ContinuousOn _ _ _ (orTopology L) (orSec o) (PX.smoothVal ⁻¹' U) := by
  let := orTopology L
  exact (continuousOn_open_iff (h.1.preimage PX.continuous_smoothVal)).2 fun W hW => hW U o h

variable (L) in
/-- `π_f` is continuous. -/
theorem continuous_orProj : @Continuous _ _ (orTopology L) _ (orProj f hf) := by
  let := orTopology L
  exact continuous_def.2 fun G hG U o h => (h.1.preimage PX.continuous_smoothVal).inter hG

/-- A point of `{(y, o_y) | y ∈ U_∞}` is `(π_f(p), o_{π_f(p)})`. -/
theorem eq_orSec_of_mem_orBasic {U : Set X} {o : ∀ y (hy : y ∈ PX.smoothSet), Orx f hf y hy}
    {p : OrSpace f hf} (hp : p ∈ orBasic U o) : p = orSec o p.1 :=
  Sigma.ext rfl (heq_of_eq hp.2)

/-- `(y, o_y) ∈ {(y, o_y) | y ∈ U_∞}` for `y ∈ U`. -/
theorem orSec_mem_orBasic {U : Set X} {o : ∀ y (hy : y ∈ PX.smoothSet), Orx f hf y hy}
    {y : PX.SmoothLevel} (hy : PX.smoothVal y ∈ U) : orSec o y ∈ orBasic U o :=
  ⟨hy, rfl⟩

variable (L) in
/-- **Every point of `O_f` lies on a continuous orientation** over an open set contained in a good
set of `L` (`exists_nhds_scPath`, and push-forwards along paths from the point). -/
theorem exists_isContOrOn (p : OrSpace f hf) :
    ∃ (U : Set X) (o : ∀ y (hy : y ∈ PX.smoothSet), Orx f hf y hy), IsContOrOn L U o ∧
      (∃ U', L.Good U' ∧ U ⊆ U') ∧ p ∈ orBasic U o := by
  classical
  obtain ⟨x, a⟩ := p
  obtain ⟨U', hU', hxU'⟩ := L.exists_good _ (PX.smoothVal_mem x)
  obtain ⟨V, hVo, hxV, hVU', hpath⟩ := exists_nhds_scPath_of_isOpen B (L.isOpen hU') hxU'
  choose γ hγs hγ0 hγ1 hγU using fun y (hy : y ∈ V) (hys : y ∈ PX.smoothSet) =>
    hpath _ hxV y hy (PX.smoothVal_mem x) hys
  let o : ∀ y (hy : y ∈ PX.smoothSet), Orx f hf y hy := fun y hys =>
    if hy : y ∈ V then
      L.push hU' (γ y hy hys) (hγs y hy hys) (fun s _ => hγU y hy hys _) (hγ0 y hy hys)
        (hγ1 y hy hys) (PX.smoothVal_mem x) hys a
    else (L.nonempty _ (PX.smoothVal_mem x) y hys).some a
  have ho : ∀ y (hy : y ∈ V) (hys : y ∈ PX.smoothSet), o y hys =
      L.push hU' (γ y hy hys) (hγs y hy hys) (fun s _ => hγU y hy hys _) (hγ0 y hy hys)
        (hγ1 y hy hys) (PX.smoothVal_mem x) hys a := fun y hy hys => dif_pos hy
  refine ⟨V, o, ⟨hVo, fun δ hδ hδV x₀ x₁ h₀ h₁ hs₀ hs₁ => ?_⟩, ⟨U', hU', hVU'⟩, hxV, ?_⟩
  · have hx₀ : x₀ ∈ V := h₀ ▸ hδV 0 ⟨le_rfl, zero_le_one⟩
    have hx₁ : x₁ ∈ V := h₁ ▸ hδV 1 ⟨zero_le_one, le_rfl⟩
    rw [L.transport_eq_push hU' hδ (fun s hs => hVU' (hδV s hs)) h₀ h₁ hs₀ hs₁, ho _ hx₀,
      ho _ hx₁, L.push_trans hU' (hγs x₁ hx₁ hs₁) (hγs x₀ hx₀ hs₀) hδ (fun s _ => hγU _ _ _ _)
        (fun s _ => hγU _ _ _ _) (fun s hs => hVU' (hδV s hs)) (hγ0 _ _ _) (hγ1 _ _ _)
        (hγ0 _ _ _) (hγ1 _ _ _) h₀ h₁ (PX.smoothVal_mem x) hs₀ hs₁, Equiv.trans_apply]
  · change a = o _ _
    rw [ho _ hxV, L.push_eq_refl hU' _ _ (hγ0 _ _ _) (hγ1 _ _ _)]
    rfl

/-- **The local homeomorphism** of a continuous orientation: `π_f` restricted to
`{(y, o_y) | y ∈ U_∞}`, with inverse `y ↦ (y, o_y)` on `U_∞`. -/
def orChartHomeo {U : Set X} {o : ∀ y (hy : y ∈ PX.smoothSet), Orx f hf y hy}
    (h : IsContOrOn L U o) :
    @OpenPartialHomeomorph (OrSpace f hf) PX.SmoothLevel (orTopology L) _ :=
  let := orTopology L
  { toFun := orProj f hf
    invFun := orSec o
    source := orBasic U o
    target := PX.smoothVal ⁻¹' U
    map_source' := fun _ hp => hp.1
    map_target' := fun _ hy => ⟨hy, rfl⟩
    left_inv' := fun _ hp => (eq_orSec_of_mem_orBasic hp).symm
    right_inv' := fun _ _ => rfl
    open_source := isOpen_orBasic h
    open_target := h.1.preimage PX.continuous_smoothVal
    continuousOn_toFun := (continuous_orProj L).continuousOn
    continuousOn_invFun := continuousOn_orSec h }

variable (L) in
/-- **Property (1)** (2021 Theorem 6.6.17): `π_f` is a local homeomorphism. -/
theorem isLocalHomeomorph_orProj : @IsLocalHomeomorph _ _ (orTopology L) _ (orProj f hf) :=
  fun p =>
    let ⟨_, _, h, _, hp⟩ := exists_isContOrOn L p
    ⟨orChartHomeo h, hp, rfl⟩

variable (L) in
/-- **The topology of `O_f` is Hausdorff.** -/
theorem t2Space_orTopology : @T2Space _ (orTopology L) := by
  let := orTopology L
  have := PX.metrizableSpace_smoothLevel
  refine ⟨fun p q hpq => ?_⟩
  by_cases h : p.1 = q.1
  · obtain ⟨U, o, ho, -, hp⟩ := exists_isContOrOn L p
    obtain ⟨U', o', ho', -, hq⟩ := exists_isContOrOn L q
    obtain ⟨x, a⟩ := p
    obtain ⟨x', b⟩ := q
    dsimp only at h
    subst h
    have hab : a ≠ b := fun e => hpq (by rw [e])
    obtain ⟨N, hN, hNo, hxN⟩ := mem_nhds_iff.1 (ho.eventually_iff ho' hp.1 hq.1)
    refine ⟨orBasic U o ∩ orProj f hf ⁻¹' N, orBasic U' o' ∩ orProj f hf ⁻¹' N,
      (isOpen_orBasic ho).inter (hNo.preimage (continuous_orProj L)),
      (isOpen_orBasic ho').inter (hNo.preimage (continuous_orProj L)), ⟨hp, hxN⟩, ⟨hq, hxN⟩, ?_⟩
    rw [Set.disjoint_left]
    rintro r ⟨hr, hrN⟩ ⟨hr', -⟩
    exact hab (hp.2.trans (((hN hrN).2.2.1 (hr.2.symm.trans hr'.2)).trans hq.2.symm))
  · obtain ⟨G₁, G₂, h₁, h₂, hp, hq, hG⟩ := t2_separation h
    exact ⟨_, _, h₁.preimage (continuous_orProj L), h₂.preimage (continuous_orProj L), hp, hq,
      hG.preimage _⟩

/-- A point over `y` is `(y, o_y)` or `(y, o'_y)` when `o'_y` is the other orientation. -/
theorem eq_orSec_or_eq_orSec {o o' : ∀ y (hy : y ∈ PX.smoothSet), Orx f hf y hy}
    (hother : ∀ y hy (c : Orx f hf y hy), c ≠ o y hy → c = o' y hy) {p : OrSpace f hf}
    {y : PX.SmoothLevel} (hp : p.1 = y) : p = orSec o y ∨ p = orSec o' y := by
  obtain ⟨z, c⟩ := p
  dsimp only at hp
  subst hp
  by_cases hc : c = o (PX.smoothVal z) (PX.smoothVal_mem z)
  · left
    rw [hc]
    rfl
  · right
    rw [hother _ _ _ hc]
    rfl

end Topology

/-- **Connected smooth parts of small neighbourhoods** (the hypothesis under which property (2)
of 2021 Theorem 6.6.17 is proved): every smooth point has arbitrarily small open neighbourhoods
`U` in `X` with `U ∩ X_∞` preconnected in `X_∞` (topology of Theorem 2.3.10). -/
def MPolyfold.HasConnectedSmoothNbhds (PX : MPolyfold X) : Prop :=
  ∀ (x : PX.SmoothLevel) (W : Set X), IsOpen W → PX.smoothVal x ∈ W →
    ∃ U : Set X, IsOpen U ∧ PX.smoothVal x ∈ U ∧ U ⊆ W ∧ IsPreconnected (PX.smoothVal ⁻¹' U)

/-- **Witness**: an M-polyfold on a subsingleton has `HasConnectedSmoothNbhds`. -/
theorem MPolyfold.hasConnectedSmoothNbhds_of_subsingleton [Subsingleton X] (PX : MPolyfold X) :
    PX.HasConnectedSmoothNbhds := by
  have : Subsingleton PX.SmoothLevel := ⟨fun a b => Subtype.ext (Subsingleton.elim a.1 b.1)⟩
  exact fun _ W hW hx => ⟨W, hW, hx, subset_rfl, Set.subsingleton_of_subsingleton.isPreconnected⟩

/-- **Witness**: `ℝⁿ` has `HasConnectedSmoothNbhds` (balls are convex, and `y ↦ y ∈ X_∞` is
continuous by `continuous_smoothMk_comp` for the identity). -/
theorem rnPolyfold_hasConnectedSmoothNbhds (n : ℕ) : (rnPolyfold n).HasConnectedSmoothNbhds := by
  intro x W hW hxW
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hW _ hxW
  refine ⟨Metric.ball ((rnPolyfold n).smoothVal x) ε, Metric.isOpen_ball,
    Metric.mem_ball_self hε, hball, ?_⟩
  have hid := (rnPolyfold n).isScSmoothMap_id
  have himg : (rnPolyfold n).smoothVal ⁻¹' Metric.ball ((rnPolyfold n).smoothVal x) ε =
      (fun y => (rnPolyfold n).smoothMk (id y) (mem_smoothSet_of_isScSmoothMap hid y)) ''
        Metric.ball ((rnPolyfold n).smoothVal x) ε := by
    ext z
    exact ⟨fun hz => ⟨_, hz, rfl⟩, fun ⟨y, hy, hyz⟩ => hyz ▸ hy⟩
  rw [himg]
  exact (convex_ball _ _).isPreconnected.image _ (continuous_smoothMk_comp hid).continuousOn

section Two

variable {hf : B.IsScFredholmSection f} {L : LocalTransport PX fun x hs => Orx f hf x hs}

variable (L) in
/-- **Property (2)** (2021 Theorem 6.6.17) for the topology of `O_f`, from
`HasConnectedSmoothNbhds`, when every
`Or_y^f` has exactly two elements. -/
theorem hasTwoContSections_orTopology
    (htwo : ∀ y (hy : y ∈ PX.smoothSet), ∃ a b : Orx f hf y hy, a ≠ b ∧ ∀ c, c = a ∨ c = b)
    (hC : PX.HasConnectedSmoothNbhds) : HasTwoContSections f hf (orTopology L) := by
  classical
  let := orTopology L
  intro x
  obtain ⟨a, -, -, -⟩ := htwo _ (PX.smoothVal_mem x)
  obtain ⟨V, o, ho, -, hp⟩ := exists_isContOrOn L ⟨x, a⟩
  obtain ⟨U, hUo, hxU, hUV, hconn⟩ := hC x V ho.1 hp.1
  have hne : ∀ y (hy : y ∈ PX.smoothSet), ∃ c : Orx f hf y hy, c ≠ o y hy := fun y hy =>
    let ⟨a₁, a₂, ha, _⟩ := htwo y hy
    if h : o y hy = a₁ then ⟨a₂, h ▸ ha.symm⟩ else ⟨a₁, Ne.symm h⟩
  choose o' ho' using hne
  have hother : ∀ y hy (c : Orx f hf y hy), c ≠ o y hy → c = o' y hy := fun y hy c hc =>
    let ⟨_, _, _, hall⟩ := htwo y hy
    eq_of_ne_of_ne_of_two hall hc (ho' y hy)
  have hco' : IsContOrOn L V o' := ⟨ho.1, fun γ hγ hγV x₀ x₁ h₀ h₁ hs₀ hs₁ =>
    hother _ _ _ fun e => ho' x₀ hs₀ ((L.transport γ hγ h₀ h₁ hs₀ hs₁).injective
      (e.trans (ho.2 γ hγ hγV h₀ h₁ hs₀ hs₁).symm))⟩
  have hUV' : PX.smoothVal ⁻¹' U ⊆ PX.smoothVal ⁻¹' V := fun y hy => hUV hy
  have hcont : ∀ {o'' : ∀ y (hy : y ∈ PX.smoothSet), Orx f hf y hy}, IsContOrOn L V o'' →
      Continuous fun y : PX.smoothVal ⁻¹' U => orSec o'' (y : PX.SmoothLevel) := fun h =>
    continuousOn_iff_continuous_domRestrict.1 ((continuousOn_orSec h).mono hUV')
  have hoo' : ∀ y : PX.SmoothLevel, orSec o y ≠ orSec o' y := fun y e =>
    ho' _ _ (eq_of_heq (Sigma.mk.inj_iff.1 e).2).symm
  refine ⟨U, hUo, hxU, fun y => orSec o y, fun y => orSec o' y, ⟨hcont ho, fun _ => rfl⟩,
    ⟨hcont hco', fun _ => rfl⟩, fun e => hoo' x (congrFun e ⟨x, hxU⟩), ?_⟩
  rintro σ ⟨hσc, hσ⟩
  -- the set where `σ` is the first section is open and closed
  have hev : ∀ {o'' : ∀ y (hy : y ∈ PX.smoothSet), Orx f hf y hy}, IsContOrOn L V o'' →
      IsOpen {y : PX.smoothVal ⁻¹' U | σ y = orSec o'' y} := fun {o''} h =>
    isOpen_iff_mem_nhds.2 fun y hy => by
      have hmem : σ y ∈ orBasic V o'' := by
        rw [show σ y = orSec o'' y from hy]
        exact orSec_mem_orBasic (hUV y.2)
      filter_upwards [hσc.continuousAt.preimage_mem_nhds ((isOpen_orBasic h).mem_nhds hmem)]
        with z hz
      exact (eq_orSec_of_mem_orBasic hz).trans (by rw [hσ z])
  have hA : IsClopen {y : PX.smoothVal ⁻¹' U | σ y = orSec o y} := by
    refine ⟨isOpen_compl_iff.1 ?_, hev ho⟩
    convert hev hco' using 1
    ext y
    change ¬ (σ y = orSec o y) ↔ σ y = orSec o' y
    rcases eq_orSec_or_eq_orSec hother (hσ y) with h | h
    · rw [h]
      exact ⟨fun h' => (h' rfl).elim, fun e => (hoo' _ e).elim⟩
    · rw [h]
      exact ⟨fun _ => rfl, fun _ e => hoo' _ e.symm⟩
  have : PreconnectedSpace (PX.smoothVal ⁻¹' U) := Subtype.preconnectedSpace hconn
  rcases isClopen_iff.1 hA with h | h
  · right
    funext y
    have hy : y ∉ {y : PX.smoothVal ⁻¹' U | σ y = orSec o y} := by rw [h]; exact fun e => e
    exact (eq_orSec_or_eq_orSec hother (hσ y)).resolve_left hy
  · left
    funext y
    have hy : y ∈ {y : PX.smoothVal ⁻¹' U | σ y = orSec o y} := by rw [h]; exact mem_univ y
    exact hy

end Two

/-! ### Property (3), uniqueness and the theorem -/

/-- The point of `X_∞` with value `a = y` is `y`. -/
lemma MPolyfold.smoothMk_eq {a : X} {h : a ∈ PX.smoothSet} {y : PX.SmoothLevel}
    (e : a = PX.smoothVal y) : PX.smoothMk a h = y := by
  subst e; rfl

/-- `t ↦ pt1 t` is continuous. -/
lemma continuous_pt1 : Continuous (pt1 : ℝ → Fin 1 → ℝ) := continuous_pi fun _ => continuous_id

omit [T2Space X] [ParacompactSpace X] in
/-- Near `t₀`, the segments `φ|[t₀, t]` of a continuous path stay in an open set containing
`φ(t₀)`. -/
lemma eventually_segPath_mem {φ : (Fin 1 → ℝ) → X} (hφc : Continuous φ) {U : Set X}
    (hU : IsOpen U) {t₀ : unitInterval} (h : φ (pt1 (t₀ : ℝ)) ∈ U) :
    ∀ᶠ t : unitInterval in 𝓝 t₀, ∀ s ∈ Icc (0 : ℝ) 1, segPath φ t₀ t (pt1 s) ∈ U := by
  have hO : IsOpen {r : ℝ | φ (pt1 r) ∈ U} := hU.preimage (hφc.comp continuous_pt1)
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hO _ h
  refine Metric.eventually_nhds_iff.2 ⟨ε, hε, fun t ht s hs => hball ?_⟩
  rw [Subtype.dist_eq, Real.dist_eq] at ht
  rw [Metric.mem_ball, Real.dist_eq]
  change |(t₀ : ℝ) + s * ((t : ℝ) - t₀) - t₀| < ε
  rw [add_sub_cancel_left, abs_mul, abs_of_nonneg hs.1]
  exact lt_of_le_of_lt (mul_le_of_le_one_left (abs_nonneg _) hs.2) ht

/-- `p = (y, o_y)` iff `p.2 = o_{p.1}`, for `p` over `y`. -/
lemma eq_orSec_iff {hf : B.IsScFredholmSection f} {o : ∀ y (hy : y ∈ PX.smoothSet), Orx f hf y hy}
    {p : OrSpace f hf} {y : PX.SmoothLevel} (hp : p.1 = y) :
    p = orSec o y ↔ p.2 = o (PX.smoothVal p.1) (PX.smoothVal_mem p.1) := by
  obtain ⟨z, c⟩ := p
  dsimp only at hp ⊢
  subst hp
  exact ⟨fun h => eq_of_heq (Sigma.mk.inj_iff.1 h).2, fun h => by rw [h]; rfl⟩

section Existence

variable [∀ n : ℕ, ParacompactSpace ((Fin n → ℝ) × X)]
  [∀ n : ℕ, ParacompactSpace (pullbackSpace P (Prod.snd : (Fin n → ℝ) × X → X))]
  [∀ k n : ℕ, ParacompactSpace ((Fin k → ℝ) × ((Fin n → ℝ) × X))]
  [∀ k n : ℕ, ParacompactSpace (pullbackSpace (pullbackProj P (Prod.snd : (Fin n → ℝ) × X → X))
    (Prod.snd : (Fin k → ℝ) × ((Fin n → ℝ) × X) → (Fin n → ℝ) × X))]

variable (hX : PX.IsTame) (hbump : PX.AdmitsBumpFunctions) (hf : B.IsScFredholmSectionTame f)
  (hsec : B.HasScPlusSectionsThrough)

include hX hbump hf hsec

/-- **Property (3)** (2021 Theorem 6.6.17) for the topology of `O_f`: near `t₀`, a continuous
section of `φ*O_f` stays in one set `{(y, o_y)}` of a continuous orientation `o`, which is carried
along the segments of `φ` by the transport. -/
theorem isPropagationContinuous_orTopology :
    IsPropagationContinuous f hf.toIsScFredholmSection
      (orTopology (orLocalTransport hX hbump hf hsec)) := by
  set L := orLocalTransport hX hbump hf hsec with hL
  let _ : TopologicalSpace (OrSpace f hf.toIsScFredholmSection) := orTopology L
  intro φ hφ α hα hαs t₀
  obtain ⟨U, o, ho, ⟨U', hU', hUU'⟩, hp⟩ := exists_isContOrOn L (α t₀).1.2
  have hφc : Continuous φ := continuousOn_univ.1 hφ.continuousOn
  have hev1 : ∀ᶠ t in 𝓝 t₀, (α t).1.2 ∈ orBasic U o :=
    (continuous_snd.comp (continuous_subtype_val.comp hα)).continuousAt
      ((isOpen_orBasic ho).mem_nhds hp)
  have hαφ : ∀ t : unitInterval, φ (pt1 (t : ℝ)) = PX.smoothVal (α t).1.2.1 := fun t => by
    have := (α t).2
    change φ (pt1 (((α t).1.1 : unitInterval) : ℝ)) = PX.smoothVal (α t).1.2.1 at this
    rw [hαs] at this
    exact this
  have hφt₀ : φ (pt1 (t₀ : ℝ)) ∈ U := by rw [hαφ]; exact hp.1
  filter_upwards [hev1, eventually_segPath_mem hφc ho.1 hφt₀] with t ht hseg
  have h₀ : segPath φ t₀ t (pt1 0) = PX.smoothVal (α t₀).1.2.1 := by rw [segPath_zero, hαφ]
  have h₁ : segPath φ t₀ t (pt1 1) = PX.smoothVal (α t).1.2.1 := by rw [segPath_one, hαφ]
  refine ⟨U', hU', fun s hs => hUU' (hseg s hs), h₀, h₁, ?_⟩
  have hT := ho.2 _ (isScSmoothMap_segPath hφ t₀ t) hseg h₀ h₁ (PX.smoothVal_mem _)
    (PX.smoothVal_mem _)
  calc _ = L.transport _ (isScSmoothMap_segPath hφ t₀ t) h₀ h₁ (PX.smoothVal_mem _)
        (PX.smoothVal_mem _) (α t₀).1.2.2 := by
          rw [L.transport_eq_push hU' _ (fun s hs => hUU' (hseg s hs))]
          rfl
    _ = (α t).1.2.2 := by rw [hp.2, hT, ← ht.2]

/-- **Continuous local sections are the continuous orientations** (the core of uniqueness): for a
topology with property (3), a continuous section `s` over an open `N ⊆ X_∞` which agrees with a
continuous orientation `o` at `y₀` agrees with it near `y₀` (paths of
`eventually_exists_scPath_smoothLevel`, `continuous_smoothMk_comp`, and connectedness of
`[0, 1]`). -/
theorem eventually_eq_orSec_of_continuousOn
    {t : TopologicalSpace (OrSpace f hf.toIsScFredholmSection)}
    (h3 : IsPropagationContinuous f hf.toIsScFredholmSection t) {U : Set X}
    {o : ∀ y (hy : y ∈ PX.smoothSet), Orx f hf.toIsScFredholmSection y hy}
    (ho : IsContOrOn (orLocalTransport hX hbump hf hsec) U o) {N : Set PX.SmoothLevel}
    (hNo : IsOpen N) {s : PX.SmoothLevel → OrSpace f hf.toIsScFredholmSection}
    (hs : @ContinuousOn _ _ _ t s N) (hs1 : ∀ y ∈ N, (s y).1 = y) {y₀ : PX.SmoothLevel}
    (hy₀ : y₀ ∈ N) (hy₀U : PX.smoothVal y₀ ∈ U) (hsy₀ : s y₀ = orSec o y₀) :
    ∀ᶠ y in 𝓝 y₀, s y = orSec o y := by
  set L := orLocalTransport hX hbump hf hsec with hL
  let := t
  have hN : N ∩ PX.smoothVal ⁻¹' U ∈ 𝓝 y₀ :=
    (hNo.inter (ho.1.preimage PX.continuous_smoothVal)).mem_nhds ⟨hy₀, hy₀U⟩
  filter_upwards [eventually_exists_scPath_smoothLevel y₀ hN] with y ⟨γ, hγ, hγ0, hγ1, hγN⟩
  set γ' : unitInterval → PX.SmoothLevel := fun τ =>
    PX.smoothMk (γ (pt1 (τ : ℝ))) (mem_smoothSet_of_isScSmoothMap hγ _) with hγ'def
  have hγ'c : Continuous γ' :=
    (continuous_smoothMk_comp hγ).comp (continuous_pt1.comp continuous_subtype_val)
  have hγ'N : ∀ τ, γ' τ ∈ N ∩ PX.smoothVal ⁻¹' U := fun τ => hγN _
  let α : unitInterval → OrPullback f hf.toIsScFredholmSection γ := fun τ =>
    ⟨(τ, s (γ' τ)), by
      change γ (pt1 (τ : ℝ)) = PX.smoothVal (s (γ' τ)).1
      rw [hs1 _ (hγ'N τ).1]
      rfl⟩
  have hαc : Continuous α :=
    (continuous_id.prodMk (hs.comp_continuous hγ'c fun τ => (hγ'N τ).1)).subtype_mk _
  have h3' := h3 γ hγ α hαc fun _ => rfl
  have hQiff : ∀ τ, s (γ' τ) = orSec o (γ' τ) ↔ (α τ).1.2.2 =
      o (PX.smoothVal (α τ).1.2.1) (PX.smoothVal_mem _) := fun τ =>
    eq_orSec_iff (hs1 _ (hγ'N τ).1)
  have hQ : ∀ τ₀, ∀ᶠ τ in 𝓝 τ₀,
      (s (γ' τ) = orSec o (γ' τ) ↔ s (γ' τ₀) = orSec o (γ' τ₀)) := by
    intro τ₀
    filter_upwards [h3' τ₀] with τ ⟨U'', hU'', hseg, h₀, h₁, hpush⟩
    have hsegU : ∀ r ∈ Icc (0 : ℝ) 1, segPath γ τ₀ τ (pt1 r) ∈ U := fun r _ => (hγN _).2
    have hT := ho.2 _ (isScSmoothMap_segPath hγ τ₀ τ) hsegU h₀ h₁ (PX.smoothVal_mem _)
      (PX.smoothVal_mem _)
    have hP : L.transport _ (isScSmoothMap_segPath hγ τ₀ τ) h₀ h₁ (PX.smoothVal_mem _)
        (PX.smoothVal_mem _) (α τ₀).1.2.2 = (α τ).1.2.2 := by
      rw [L.transport_eq_push hU'' _ hseg]
      exact hpush
    rw [hQiff τ, hQiff τ₀, ← hP, ← hT]
    exact (L.transport _ _ h₀ h₁ _ _).apply_eq_iff_eq
  have hopen : IsOpen {τ | s (γ' τ) = orSec o (γ' τ)} :=
    isOpen_iff_mem_nhds.2 fun τ₀ hτ₀ => (hQ τ₀).mono fun τ h => h.2 hτ₀
  have hclosed : IsOpen {τ | s (γ' τ) = orSec o (γ' τ)}ᶜ :=
    isOpen_iff_mem_nhds.2 fun τ₀ hτ₀ => (hQ τ₀).mono fun τ h hτ => hτ₀ (h.1 hτ)
  have hγ'0 : γ' 0 = y₀ := MPolyfold.smoothMk_eq hγ0
  have hγ'1 : γ' 1 = y := MPolyfold.smoothMk_eq hγ1
  have h0 : (0 : unitInterval) ∈ {τ | s (γ' τ) = orSec o (γ' τ)} := by
    change s (γ' 0) = orSec o (γ' 0)
    rw [hγ'0]; exact hsy₀
  rcases isClopen_iff.1 ⟨isOpen_compl_iff.1 hclosed, hopen⟩ with h | h
  · exact absurd (h ▸ h0) (notMem_empty _)
  · have h1 : (1 : unitInterval) ∈ {τ | s (γ' τ) = orSec o (γ' τ)} := by rw [h]; exact mem_univ _
    change s (γ' 1) = orSec o (γ' 1) at h1
    rwa [hγ'1] at h1

/-- **Uniqueness in 2021 Theorem 6.6.17**: a topology on `O_f` with properties (1) and (3) is the
topology `orTopology` (Hausdorffness and property (2) are not needed). -/
theorem eq_orTopology_of {t : TopologicalSpace (OrSpace f hf.toIsScFredholmSection)}
    (h1 : @IsLocalHomeomorph _ _ t _ (orProj f hf.toIsScFredholmSection))
    (h3 : IsPropagationContinuous f hf.toIsScFredholmSection t) :
    t = orTopology (orLocalTransport hX hbump hf hsec) := by
  set L := orLocalTransport hX hbump hf hsec with hL
  have hsec' : ∀ (e : @OpenPartialHomeomorph _ _ t _), orProj f hf.toIsScFredholmSection = e →
      ∀ z ∈ e.target, (e.symm z).1 = z := fun e he z hz =>
    (congrFun he (e.symm z)).trans (e.right_inv hz)
  refine TopologicalSpace.ext (funext fun G => propext ⟨fun hG => ?_, fun hG => ?_⟩)
  · -- `t`-open sets are open
    intro U o ho
    refine isOpen_iff_mem_nhds.2 fun y hy => ?_
    obtain ⟨e, hpe, he⟩ := h1 (orSec o y)
    have hey : e (orSec o y) = y := (congrFun he _).symm
    have hyt : y ∈ e.target := hey ▸ e.map_source hpe
    have hsy : e.symm y = orSec o y := by
      conv_lhs => rw [← hey]
      exact e.left_inv hpe
    have hev := eventually_eq_orSec_of_continuousOn hX hbump hf hsec h3 ho e.open_target
      e.continuousOn_symm (hsec' e he) hyt hy.1 hsy
    have hev2 : ∀ᶠ z in 𝓝 y, e.symm z ∈ G :=
      (e.continuousOn_symm.continuousAt (e.open_target.mem_nhds hyt))
        (@IsOpen.mem_nhds _ t _ _ hG (hsy ▸ hy.2))
    filter_upwards [hev, hev2, (ho.1.preimage PX.continuous_smoothVal).mem_nhds hy.1]
      with z hz1 hz2 hz3
    exact ⟨hz3, hz1 ▸ hz2⟩
  · -- open sets are `t`-open
    let := t
    refine isOpen_iff_mem_nhds.2 fun p hp => ?_
    obtain ⟨e, hpe, he⟩ := h1 p
    obtain ⟨U, o, ho, -, hpo⟩ := exists_isContOrOn L p
    have hep : e p = p.1 := (congrFun he p).symm
    have hp1 : p.1 ∈ e.target := hep ▸ e.map_source hpe
    have hsp : e.symm p.1 = orSec o p.1 := by
      conv_lhs => rw [← hep]
      exact (e.left_inv hpe).trans (eq_orSec_of_mem_orBasic hpo)
    have hev := eventually_eq_orSec_of_continuousOn hX hbump hf hsec h3 ho e.open_target
      e.continuousOn_symm (hsec' e he) hp1 hpo.1 hsp
    have hmem : p.1 ∈ {y : PX.SmoothLevel | PX.smoothVal y ∈ U ∧ orSec o y ∈ G} :=
      ⟨hpo.1, (eq_orSec_of_mem_orBasic hpo) ▸ hp⟩
    obtain ⟨M, hMsub, hMo, hpM⟩ := mem_nhds_iff.1
      ((hev.and ((hG U o ho).mem_nhds hmem)).and (e.open_target.mem_nhds hp1))
    refine mem_nhds_iff.2 ⟨e.source ∩ e ⁻¹' M, fun q ⟨hq, hqM⟩ => ?_,
      e.isOpen_inter_preimage hMo, hpe, show e p ∈ M by rw [hep]; exact hpM⟩
    have h := hMsub hqM
    rw [← e.left_inv hq, h.1.1]
    exact h.1.2.2

/-- **2021 Theorem 6.6.17 without property (2)**: there is exactly one Hausdorff topology on `O_f`
with properties (1) and (3) (by `eq_orTopology_of`, even exactly one with (1) and (3)). -/
theorem existsUnique_orientationTopology :
    ∃! t : TopologicalSpace (OrSpace f hf.toIsScFredholmSection), @T2Space _ t ∧
      @IsLocalHomeomorph _ _ t _ (orProj f hf.toIsScFredholmSection) ∧
      IsPropagationContinuous f hf.toIsScFredholmSection t :=
  ⟨orTopology (orLocalTransport hX hbump hf hsec),
    ⟨t2Space_orTopology _, isLocalHomeomorph_orProj _,
      isPropagationContinuous_orTopology hX hbump hf hsec⟩,
    fun _ ht => eq_orTopology_of hX hbump hf hsec ht.2.1 ht.2.2⟩

/-- **2021 Theorem 6.6.17**, p. 275 (new in the 2021 edition; the 2017 text has no topology on
`O_f`): there is exactly one topology on `O_f` which is Hausdorff and has properties
(1), (2) and (3); under the hypothesis `HasConnectedSmoothNbhds` (used for (2) only). -/
theorem theorem_6_6_17_hyp (hC : PX.HasConnectedSmoothNbhds) :
    ∃! t : TopologicalSpace (OrSpace f hf.toIsScFredholmSection),
      IsOrientationTopology f hf.toIsScFredholmSection t :=
  ⟨orTopology (orLocalTransport hX hbump hf hsec),
    ⟨t2Space_orTopology _, isLocalHomeomorph_orProj _,
      hasTwoContSections_orTopology _ (fun _ hy => exists_two_orx _ hy hsec) hC,
      isPropagationContinuous_orTopology hX hbump hf hsec⟩,
    fun _ ht => eq_orTopology_of hX hbump hf hsec ht.isLocalHomeomorph ht.propagation⟩

end Existence

end Polyfold
