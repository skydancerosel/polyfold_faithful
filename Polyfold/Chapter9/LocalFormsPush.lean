import Polyfold.Chapter11.MultiChartSheetsEquivalence
import Polyfold.Chapter11.BoundarySheetsDiffeo
import Polyfold.Chapter11.FormEvalPullbackEquivalence

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021; 2017 arXiv 1707.08941),
Part II, Chapter 9, §9.5, **Remark 9.5.19, 2021 p. 451** (2017: Remark 9.8), point G.153.
Numbers and pages are the 2021 text's.

# Forms on an open part of an ep-groupoid, with values on all tangent vectors

The integrals of §9.5 use the values of a form on the tangent spaces of the sheets
(`EpGroupoid.FormEval`).  For an sc-diffeomorphism `f : W → W'` from an open subset of the object
space of `X` onto an open subset of the object space of `Y`, a continuous cut-off `χ` on `X`,
constant on the orbits and with support in `W`, and forms `Ω` with values on `Y`, the values
`χ(y) · ω(Tf α₁, …, Tf αₙ)` (and `0` off `W`) are values on `X`.

* `MPolyfold.chartVec_transportChart_symm`: the chart vector of `Tf α` in the chart `φ ∘ f⁻¹`
  is the chart vector of `α` in `φ`.
* `EpGroupoid.FormEval.pushCut`: the evaluation `χ · (ω ∘ Tf)` on `X`.
* `EpGroupoid.FormEval.evCompatOn_pushCut`, `evCompatOn_symm_pushCut`: where `χ = 1` the values
  are those of `ω`, in both directions of `EvCompatOn`.
* `EpGroupoid.boundaryStratum_image_of_isScDiffeoOn`: `∂₁(f(M)) = f(∂₁M)` (as
  `boundaryStratum_image_cross`, with no orientation of `M`).
-/

set_option maxSynthPendingDepth 3

open Set Function Filter Topology

noncomputable section

namespace Polyfold

universe u

namespace MPolyfold

variable {X Y : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {P : MPolyfold X}
  [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {Q : MPolyfold Y}
  {f : X → Y} {g : Y → X} {U : Set X} {U' : Set Y}

/-- The chart vector of `Tf(α)` in the chart `φ ∘ f⁻¹` of `Y` is the chart vector of `α` in the
chart `φ` of `X`. -/
theorem chartVec_transportChart_symm (hf : P.IsScDiffeoOn Q f g U U') {φ : MChart X}
    (hφ : P.IsChart φ) {α : P.TangentSpace}
    (hαU : P.levelVal 1 (P.tangentProj α) ∈ U ∩ φ.source) :
    chartVec (transportChart_isChart hf.symm hφ) (tangentMapOn hf.isScSmoothOn α) =
      chartVec hφ α := by
  have hα : α ∈ P.tangentPreimage U := hαU.1
  have h1 := chartVec_tangentMapOn_of_isScDiffeoOn hf.symm hφ
    (α := tangentMapOn hf.isScSmoothOn α) (by
      rw [levelVal_tangentProj_tangentMapOn hf.isScSmoothOn hα]
      exact ⟨hf.mapsTo hαU.1, by rw [mem_preimage, hf.left_inv _ hαU.1]; exact hαU.2⟩)
  rw [← h1]
  exact congrArg _ (hf.tangent.left_inv _ hα)

/-- `Tf` maps `T_yN` into `T_{f(y)} f(N ∩ U)`. -/
theorem tangentMapOn_mem_submanifoldTangent_image (hf : P.IsScDiffeoOn Q f g U U') {N : Set X}
    (hN : P.IsSmoothSubmanifold N) {y : X} (hyU : y ∈ U) {α : P.TangentSpace}
    (hα : α ∈ P.submanifoldTangent N y) :
    tangentMapOn hf.isScSmoothOn α ∈ Q.submanifoldTangent (f '' (N ∩ U)) (f y) := by
  have hy : y ∈ N := mem_of_mem_submanifoldTangent hα
  have hU := hf.isScSmoothOn.isOpen
  rw [submanifoldTangent_image_of_isScDiffeoOn hf (hN.inter_isOpen hU) inter_subset_right
    ⟨hy, hyU⟩]
  exact ⟨α, by rw [submanifoldTangent_inter_isOpen hU hyU]; exact hα, rfl⟩

variable (P) in
/-- The base point of the first vector of a tuple of tangent vectors. -/
def tupleBase {n : ℕ} (hn : 0 < n) (α : Fin n → P.TangentSpace) : X :=
  P.levelVal 1 (P.tangentProj (α ⟨0, hn⟩))

theorem tupleBase_eq {n : ℕ} (hn : 0 < n) {α : Fin n → P.TangentSpace} {N : Set X} {y : X}
    (hα : ∀ i, α i ∈ P.submanifoldTangent N y) : P.tupleBase hn α = y :=
  levelVal_tangentProj_of_mem (hα _)

end MPolyfold

namespace EpGroupoid

open MPolyfold

variable {Obj Mor Obj' Mor' : Type u} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor]
  [TopologicalSpace Obj'] [T2Space Obj'] [ParacompactSpace Obj']
  [TopologicalSpace Mor'] [T2Space Mor'] [ParacompactSpace Mor']
  {X : EpGroupoid Obj Mor} {Y : EpGroupoid Obj' Mor'} {n : ℕ}
  {Ω : Type*} [AddCommGroup Ω] [Module ℝ Ω]
  {f : Obj → Obj'} {g : Obj' → Obj} {W : Set Obj} {W' : Set Obj'}

/-- **`∂₁(f(M)) = f(∂₁M)`** for an sc-diffeomorphism `f : W → W'` between open subsets of the
object spaces of two ep-groupoids and a smooth submanifold `M ⊆ W`. -/
theorem boundaryStratum_image_of_isScDiffeoOn (hf : X.PObj.IsScDiffeoOn Y.PObj f g W W')
    {M : Set Obj} (hM : X.PObj.IsSmoothSubmanifold M) (hMW : M ⊆ W) :
    Y.PObj.boundaryStratum (f '' M) = f '' X.PObj.boundaryStratum M := by
  have key : ∀ y ∈ M, (f y ∈ Y.PObj.boundaryStratum (f '' M) ↔ y ∈ X.PObj.boundaryStratum M) :=
    fun y hy => by
      have h := hasReducedCodim_map_tangentMapOn_iff hf (hMW hy) (ℓ := 1)
        (o := ⟨0, X.PObj.submanifoldTangent M y, ∅⟩)
        (fun α hα => levelVal_tangentProj_of_mem hα)
      have e : (OrTangent.map (tangentMapOn hf.isScSmoothOn)
          (⟨0, X.PObj.submanifoldTangent M y, ∅⟩ : OrTangent X.PObj)).carrier =
          Y.PObj.submanifoldTangent (f '' M) (f y) :=
        (submanifoldTangent_image_of_isScDiffeoOn hf hM hMW hy).symm
      constructor
      · intro h1
        refine ⟨hy, h.1 fun c => ?_⟩
        rw [e]
        exact h1.2 c
      · intro h1
        refine ⟨mem_image_of_mem f hy, fun c => ?_⟩
        have h2 := h.2 h1.2 c
        rwa [e] at h2
  ext z
  constructor
  · rintro hz
    obtain ⟨y, hy, rfl⟩ := hz.1
    exact ⟨y, (key y hy).1 hz, rfl⟩
  · rintro ⟨y, hy, rfl⟩
    exact (key y hy.1).2 hy

namespace FormEval

/-- The values `χ(y) · ω(Tf α₁, …, Tf αₙ)`. -/
def pushCutEv (FY : Y.FormEval n Ω) (hn : 0 < n) (hf : X.PObj.IsScDiffeoOn Y.PObj f g W W')
    (χ : Obj → ℝ) (ω : Ω) (α : Fin n → X.PObj.TangentSpace) : ℝ :=
  χ (X.PObj.tupleBase hn α) * FY.ev ω (fun i => tangentMapOn hf.isScSmoothOn (α i))

variable (FY : Y.FormEval n Ω) (hn : 0 < n) (hf : X.PObj.IsScDiffeoOn Y.PObj f g W W')
  {χ : Obj → ℝ}

theorem pushCutEv_eq (ω : Ω) {α : Fin n → X.PObj.TangentSpace} {N : Set Obj} {y : Obj}
    (hα : ∀ i, α i ∈ X.PObj.submanifoldTangent N y) :
    pushCutEv FY hn hf χ ω α =
      χ y * FY.ev ω (fun i => tangentMapOn hf.isScSmoothOn (α i)) := by
  rw [pushCutEv, tupleBase_eq hn hα]

theorem pushCutEv_det (hχW : tsupport χ ⊆ W) (ω : Ω) {N : Set Obj}
    (hN : X.PObj.IsSmoothSubmanifold N) {y : Obj} (hy : y ∈ N) {φ : MChart Obj}
    (hφ : X.PObj.IsChart φ) (hyφ : y ∈ φ.source) (α β : Fin n → X.PObj.TangentSpace)
    (hα : ∀ i, α i ∈ X.PObj.submanifoldTangent N y)
    (hβ : ∀ i, β i ∈ X.PObj.submanifoldTangent N y) (M : Matrix (Fin n) (Fin n) ℝ)
    (hM : ∀ j, chartVec hφ (β j) = ∑ i, M i j • chartVec hφ (α i)) :
    pushCutEv FY hn hf χ ω β = M.det * pushCutEv FY hn hf χ ω α := by
  rw [pushCutEv_eq FY hn hf ω hα, pushCutEv_eq FY hn hf ω hβ]
  by_cases hyW : y ∈ W
  · have hWo := hf.isScSmoothOn.isOpen
    have hcv : ∀ {γ : X.PObj.TangentSpace}, γ ∈ X.PObj.submanifoldTangent N y →
        chartVec (transportChart_isChart hf.symm hφ) (tangentMapOn hf.isScSmoothOn γ) =
          chartVec hφ γ := fun hγ =>
      chartVec_transportChart_symm hf hφ (by
        rw [levelVal_tangentProj_of_mem hγ]; exact ⟨hyW, hyφ⟩)
    rw [FY.ev_det ω ((hN.inter_isOpen hWo).image_of_isScDiffeoOn hf inter_subset_right)
      (y := f y) ⟨y, ⟨hy, hyW⟩, rfl⟩ (transportChart_isChart hf.symm hφ)
      ⟨hf.mapsTo hyW, by rw [mem_preimage, hf.left_inv y hyW]; exact hyφ⟩
      (fun i => tangentMapOn hf.isScSmoothOn (α i)) (fun i => tangentMapOn hf.isScSmoothOn (β i))
      (fun i => tangentMapOn_mem_submanifoldTangent_image hf hN hyW (hα i))
      (fun i => tangentMapOn_mem_submanifoldTangent_image hf hN hyW (hβ i)) M
      (fun j => by
        rw [hcv (hβ j), hM j]
        exact Finset.sum_congr rfl fun i _ => by rw [hcv (hα i)]; rfl)]
    ring
  · rw [image_eq_zero_of_notMem_tsupport fun h => hyW (hχW h)]
    ring

theorem pushCutEv_mor (hχW : tsupport χ ⊆ W)
    (hχinv : ∀ ψ : Mor, χ (X.src ψ) = χ (X.tgt ψ))
    (hmor : ∀ ψ : Mor, X.src ψ ∈ W → ∃ ψ' : Mor', Y.src ψ' = f (X.src ψ) ∧
      ∀ a : X.PObj.TangentSpace, X.PObj.levelVal 1 (X.PObj.tangentProj a) = X.src ψ →
        tangentMapOn hf.isScSmoothOn (X.tangentMor ψ a) =
          Y.tangentMor ψ' (tangentMapOn hf.isScSmoothOn a))
    (ω : Ω) {N : Set Obj} (hN : X.PObj.IsSmoothSubmanifold N) {y : Obj} (hy : y ∈ N)
    (ψ : Mor) (hψ : X.src ψ = y) (α : Fin n → X.PObj.TangentSpace)
    (hα : ∀ i, α i ∈ X.PObj.submanifoldTangent N y) :
    pushCutEv FY hn hf χ ω (fun i => X.tangentMor ψ (α i)) = pushCutEv FY hn hf χ ω α := by
  subst hψ
  have hbα : ∀ i, X.PObj.levelVal 1 (X.PObj.tangentProj (α i)) = X.src ψ := fun i =>
    levelVal_tangentProj_of_mem (hα i)
  have hψ1 : ψ ∈ X.PMor.levelSet 1 := (X.mem_levelSet_src_iff ψ 1).1 (by
    rw [← hbα ⟨0, hn⟩]; exact X.PObj.levelVal_mem _)
  have hbt : X.PObj.tupleBase hn (fun i => X.tangentMor ψ (α i)) = X.tgt ψ :=
    X.levelVal_tangentProj_tangentMor hψ1 (hbα _)
  rw [pushCutEv_eq FY hn hf ω hα, pushCutEv, hbt, ← hχinv ψ]
  by_cases hW : X.src ψ ∈ W
  · obtain ⟨ψ', hsrc, hT⟩ := hmor ψ hW
    have hWo := hf.isScSmoothOn.isOpen
    congr 1
    have e : (fun i => tangentMapOn hf.isScSmoothOn (X.tangentMor ψ (α i))) =
        fun i => Y.tangentMor ψ' (tangentMapOn hf.isScSmoothOn (α i)) :=
      funext fun i => hT _ (hbα i)
    rw [e]
    exact FY.ev_mor ω ((hN.inter_isOpen hWo).image_of_isScDiffeoOn hf inter_subset_right)
      (y := f (X.src ψ)) ⟨_, ⟨hy, hW⟩, rfl⟩ ψ' hsrc _
      (fun i => tangentMapOn_mem_submanifoldTangent_image hf hN hW (hα i))
  · rw [image_eq_zero_of_notMem_tsupport fun h => hW (hχW h)]
    ring

theorem pushCutEv_continuousOn (hχ : Continuous χ) (hχW : tsupport χ ⊆ W) (ω : Ω)
    {N : Set Obj} (hN : X.PObj.IsSmoothSubmanifold N) {φ : MChart Obj}
    (hφ : X.PObj.IsChart φ) {K : Set Obj} (hK : K ⊆ N ∩ φ.source)
    (e : Obj → Fin n → X.PObj.TangentSpace)
    (he : ∀ z ∈ K, ∀ i, e z i ∈ X.PObj.submanifoldTangent N z)
    (hc : ContinuousOn (fun z i => chartVec hφ (e z i)) K) :
    ContinuousOn (fun z => pushCutEv FY hn hf χ ω (e z)) K := by
  have hWo := hf.isScSmoothOn.isOpen
  have hval : ∀ z ∈ K, pushCutEv FY hn hf χ ω (e z) =
      χ z * FY.ev ω (fun i => tangentMapOn hf.isScSmoothOn (e z i)) := fun z hz =>
    pushCutEv_eq FY hn hf ω (he z hz)
  intro z0 hz0
  by_cases hzW : z0 ∈ W
  · have hφ' := transportChart_isChart hf.symm hφ
    set K' := f '' (K ∩ W) with hK'def
    set e' : Obj' → Fin n → Y.PObj.TangentSpace :=
      fun w i => tangentMapOn hf.isScSmoothOn (e (g w) i) with he'def
    have hK' : K' ⊆ f '' (N ∩ W) ∩ (transportChart hf.symm φ).source := by
      rintro _ ⟨z, ⟨hzK, hzW⟩, rfl⟩
      exact ⟨⟨z, ⟨(hK hzK).1, hzW⟩, rfl⟩, hf.mapsTo hzW, by
        rw [mem_preimage, hf.left_inv z hzW]; exact (hK hzK).2⟩
    have he' : ∀ w ∈ K', ∀ i, e' w i ∈ Y.PObj.submanifoldTangent (f '' (N ∩ W)) w := by
      rintro _ ⟨z, ⟨hzK, hzW⟩, rfl⟩ i
      simp only [he'def, hf.left_inv z hzW]
      exact tangentMapOn_mem_submanifoldTangent_image hf hN hzW (he z hzK i)
    have hc' : ContinuousOn (fun w i => chartVec hφ' (e' w i)) K' := by
      have hmaps : MapsTo g K' K := by
        rintro _ ⟨z, ⟨hzK, hzW⟩, rfl⟩
        rw [hf.left_inv z hzW]; exact hzK
      have hKW' : K' ⊆ W' := by
        rintro _ ⟨z, ⟨-, hzW⟩, rfl⟩
        exact hf.mapsTo hzW
      have h1 := hc.comp (hf.isScSmoothOn_inv.continuousOn.mono hKW') hmaps
      refine h1.congr fun w hw => ?_
      obtain ⟨z, ⟨hzK, hzW⟩, rfl⟩ := hw
      funext i
      simp only [he'def, Function.comp, hf.left_inv z hzW]
      exact chartVec_transportChart_symm hf hφ (by
        rw [levelVal_tangentProj_of_mem (he z hzK i)]; exact ⟨hzW, (hK hzK).2⟩)
    have hcont := FY.ev_continuousOn ω
      ((hN.inter_isOpen hWo).image_of_isScDiffeoOn hf inter_subset_right) hφ' hK' e' he' hc'
    have h2 : ContinuousOn (fun z => χ z * FY.ev ω (e' (f z))) (K ∩ W) :=
      hχ.continuousOn.mul (hcont.comp (hf.isScSmoothOn.continuousOn.mono inter_subset_right)
        (mapsTo_image f _))
    have h4 : ContinuousWithinAt (fun z => χ z * FY.ev ω (e' (f z))) K z0 :=
      (continuousWithinAt_inter (hWo.mem_nhds hzW)).1 (h2 z0 ⟨hz0, hzW⟩)
    have hpt : ∀ z ∈ K ∩ W, pushCutEv FY hn hf χ ω (e z) = χ z * FY.ev ω (e' (f z)) :=
      fun z hz => by
        rw [hval z hz.1]
        simp only [he'def, hf.left_inv z hz.2]
    refine h4.congr_of_eventuallyEq ?_ (hpt z0 ⟨hz0, hzW⟩)
    filter_upwards [inter_mem_nhdsWithin K (hWo.mem_nhds hzW)] with z hz
    exact hpt z hz
  · have hz0' : z0 ∉ tsupport χ := fun h => hzW (hχW h)
    have hpt : ∀ z ∈ K ∩ (tsupport χ)ᶜ, pushCutEv FY hn hf χ ω (e z) = 0 := fun z hz => by
      rw [hval z hz.1, image_eq_zero_of_notMem_tsupport hz.2, zero_mul]
    refine (continuousWithinAt_const (b := (0 : ℝ))).congr_of_eventuallyEq ?_
      (hpt z0 ⟨hz0, hz0'⟩)
    filter_upwards [inter_mem_nhdsWithin K ((isClosed_tsupport χ).isOpen_compl.mem_nhds hz0')]
      with z hz
    exact hpt z hz

/-- **The values `χ · (ω ∘ Tf)` on `X`** of the forms with values on `Y`, for an
sc-diffeomorphism `f : W → W'` between open subsets of the object spaces, a continuous cut-off
`χ` constant on the orbits with support in `W`, and `f` compatible with the tangent maps of the
morphisms starting in `W`. -/
def pushCut (hχ : Continuous χ) (hχW : tsupport χ ⊆ W)
    (hχinv : ∀ ψ : Mor, χ (X.src ψ) = χ (X.tgt ψ))
    (hmor : ∀ ψ : Mor, X.src ψ ∈ W → ∃ ψ' : Mor', Y.src ψ' = f (X.src ψ) ∧
      ∀ a : X.PObj.TangentSpace, X.PObj.levelVal 1 (X.PObj.tangentProj a) = X.src ψ →
        tangentMapOn hf.isScSmoothOn (X.tangentMor ψ a) =
          Y.tangentMor ψ' (tangentMapOn hf.isScSmoothOn a)) : X.FormEval n Ω where
  ev := pushCutEv FY hn hf χ
  ev_add ω τ α := by simp only [pushCutEv, FY.ev_add]; ring
  ev_smul c ω α := by simp only [pushCutEv, FY.ev_smul]; ring
  ev_det ω _ hN _ hy _ hφ hyφ α β hα hβ M hM :=
    pushCutEv_det FY hn hf hχW ω hN hy hφ hyφ α β hα hβ M hM
  ev_mor ω _ hN _ hy ψ hψ α hα := pushCutEv_mor FY hn hf hχW hχinv hmor ω hN hy ψ hψ α hα
  ev_continuousOn ω _ hN _ hφ _ hK e he hc :=
    pushCutEv_continuousOn FY hn hf hχ hχW ω hN hφ hK e he hc

variable (hχ : Continuous χ) (hχW : tsupport χ ⊆ W)
  (hχinv : ∀ ψ : Mor, χ (X.src ψ) = χ (X.tgt ψ))
  (hmor : ∀ ψ : Mor, X.src ψ ∈ W → ∃ ψ' : Mor', Y.src ψ' = f (X.src ψ) ∧
    ∀ a : X.PObj.TangentSpace, X.PObj.levelVal 1 (X.PObj.tangentProj a) = X.src ψ →
      tangentMapOn hf.isScSmoothOn (X.tangentMor ψ a) =
        Y.tangentMor ψ' (tangentMapOn hf.isScSmoothOn a))

theorem pushCut_ev (ω : Ω) {α : Fin n → X.PObj.TangentSpace} {N : Set Obj} {y : Obj}
    (hα : ∀ i, α i ∈ X.PObj.submanifoldTangent N y) :
    (pushCut FY hn hf hχ hχW hχinv hmor).ev ω α =
      χ y * FY.ev ω (fun i => tangentMapOn hf.isScSmoothOn (α i)) :=
  pushCutEv_eq FY hn hf ω hα

/-- Where `χ = 1`, the values of `ω` at `Tf α` are the values `χ · (ω ∘ Tf)` at `α`. -/
theorem evCompatOn_pushCut {N : Set Obj} (h1 : ∀ y ∈ N, χ y = 1) (ω : Ω) :
    EvCompatOn (pushCut FY hn hf hχ hχW hχinv hmor) FY hf N ω ω := fun y hy β hβ => by
  rw [pushCut_ev FY hn hf hχ hχW hχinv hmor ω hβ, h1 y hy, one_mul]

/-- Where `χ = 1`, the values `χ · (ω ∘ Tf)` at `Tf⁻¹ β` are the values of `ω` at `β`. -/
theorem evCompatOn_symm_pushCut {N' : Set Obj'} (hN' : N' ⊆ W') (h1 : ∀ z ∈ N', χ (g z) = 1)
    (ω : Ω) : EvCompatOn FY (pushCut FY hn hf hχ hχW hχinv hmor) hf.symm N' ω ω :=
  fun z hz β hβ => by
    have hbase : ∀ i, Y.PObj.levelVal 1 (Y.PObj.tangentProj (β i)) = z := fun i =>
      levelVal_tangentProj_of_mem (hβ i)
    have hβW : ∀ i, β i ∈ Y.PObj.tangentPreimage W' := fun i => by
      change _ ∈ W'; rw [hbase i]; exact hN' hz
    change pushCutEv FY hn hf χ ω _ = _
    have hb : X.PObj.tupleBase hn (fun i => tangentMapOn hf.symm.isScSmoothOn (β i)) = g z := by
      change X.PObj.levelVal 1 (X.PObj.tangentProj (tangentMapOn hf.isScSmoothOn_inv _)) = _
      rw [levelVal_tangentProj_tangentMapOn hf.isScSmoothOn_inv (hβW _), hbase]
    rw [pushCutEv, hb, h1 z hz, one_mul]
    congr 1
    funext i
    exact hf.tangent.right_inv _ (hβW i)

end FormEval

end EpGroupoid

end Polyfold
