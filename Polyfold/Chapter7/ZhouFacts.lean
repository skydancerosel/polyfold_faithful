import Polyfold.Chapter7.ZhouLevels
import Polyfold.Chapter7.SmoothPointsDense
import Polyfold.Chapter2.TangentProjOpen

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021; 2017 arXiv 1707.08941),
Part II, §7.4 "Regularity Assumptions and the Zhou Condition" (pp. 328–340, new in the 2021
edition): two of the Part I facts used in the proofs of **Lemma 7.4.6** (p. 331) and
**Propositions 7.4.8** (p. 332) and **7.4.22** (p. 338), proved for every M-polyfold, and the
§7.4 results restated without them.  Numbers and pages are the 2021 text's.

# Smooth tangent vectors are dense; tangents are determined near smooth points

## The text, paraphrased

(Proof of Lemma 7.4.6, p. 331) From `Tg = id` on `(T_xX)_∞` the text passes to `Tg = id` on
`T_xX`; this uses that the smooth tangent vectors `(T_xX)_∞` are dense in `T_xX` at a smooth
point `x`.  (Proofs of Propositions 7.4.8 and 7.4.22) Two sc-smooth maps that agree near a smooth
point `y` in `X_∞` have the same tangent map on `T_yX`.  The text uses both facts without proof;
they come from Part I: `X_∞` is dense in every `X_m` (2021 p. 289), the tangent space
`T_oO = Dr(o)E` of a retract (2021 p. 38, before Remark 2.3.13; 2014 preprint, the remark after
Definition 2.17), and the definition of sc¹ maps, whose derivative is unique on a partial
quadrant (2021 Definition 1.1.15; 2014 preprint Definition 1.14).

## What is formalized

* Local lemmas: `ScBanach.exists_toLevelOne` (the inclusion `E_{N+1} → E₁`),
  `ScBanach.denseRange_toBase` (`E_k` is dense in `E₀`), `ScRetraction.apply_mem_smooth`
  (`r` preserves `E_∞`), `IsRelOpenInQuadrant.eq_of_eq_smooth` (two continuous maps agreeing at the
  smooth points of `A ∩ U_k`, `A` open in `E_k`, agree on `A ∩ U_k`), and
  `IsSc1.scDeriv_eq_of_eqOn_level`: if two sc¹ maps agree on a neighbourhood of `o` in `U_k`
  (in the topology of `E_k`), their derivatives at `o` agree on all of `E₀`.  The derivatives
  of `G ∘ ι_k` at `o` within `U_k` are unique, they are `DG(o) ∘ ι_k`, and `E_k` is dense in `E₀`.
* **`MPolyfold.denseSmoothTangent`**: `(T_xX)_∞` is dense in `T_xX` for every smooth `x`, i.e.
  Chapter 7's hypothesis `DenseSmoothTangent` holds for every M-polyfold.  In a chart,
  `T_xX ≅ T_oO = Dr(o)E₀`, and `(o, Dr(o)k)` with `k ∈ E_∞` is a smooth vector of `TO`
  (`Tr` is sc⁰, so it maps `(TE)_m` into `(TE)_m`); these are dense since `E_∞` is dense in `E₀`
  and `Dr(o)` is continuous.
* **`MPolyfold.tangentDeterminedSmooth`**: Chapter 7's hypothesis `TangentDeterminedSmooth` holds
  for every M-polyfold.  An `X_∞`-neighbourhood of `y` contains `O' ∩ X_∞` with `O'` open in some
  `X_{N+1}` (`exists_level_nhds_smooth`); in a chart, density of `E_∞` and continuity give
  `f₁ = f₂` on a neighbourhood of `o = φ(y)` in `U_{N+1}`, and `IsSc1.scDeriv_eq_of_eqOn_level`
  gives `Df₁(o) = Df₂(o)`.
* `MPolyfold.smoothRegular_of_smoothConnected`, `MPolyfold.smoothRegular_iff_smoothConnected`:
  with `denseSmooth` (`SmoothPointsDense.lean`), `isOpenMap_tangentProj`
  (`Chapter2/TangentProjOpen.lean`) and the two theorems above, the bundle `SmoothRegular` is
  equivalent to its field `SmoothConnected`.
* The §7.4 results without the discharged hypotheses: `EpGroupoid.lemma_7_4_6_2021_of_isZhou`
  (no `DenseSmoothTangent`), `EpGroupoid.isZhou_of_isZhou'_of_smoothConnected`,
  `EpGroupoid.proposition_7_4_8_2021_of_smoothConnected`,
  `EpGroupoid.proposition_7_4_10_2021_of_smoothConnected`,
  `EpGroupoid.proposition_7_4_22_2021_of_smoothConnected`, and for all lifts
  `EP.proposition_7_4_9_2021_of_smoothConnected`, `EP.corollary_7_4_11_all_2021_of_smoothConnected`,
  `EP.theorem_7_4_13_all_2021_of_smoothConnected`, `EP.theorem_7_4_24_all_2021_of_smoothConnected`.
  In each, `SmoothRegular` is replaced by `SmoothConnected` and `DenseSmoothTangent` is dropped.

These close top-ten item #5 of the triage plan: two of the five Part I facts of G.85 / V7.86
(`DenseSmoothTangent` and `TangentDeterminedSmooth`) are proved.  `SmoothConnected` stays a
hypothesis here.

## What the text leaves implicit, and the choices made

* `(T_xX)_∞` is read, as in Chapter 7, as `T_xX ∩ (TX)_∞` for the M-polyfold `TX`
  (`tangentPolyfold`).
* The derivative comparison is done at level `N + 1 ≥ 1` with the composite inclusion
  `E_{N+1} → E₁`.  The shifted M-polyfold `X^{N+1}` is not needed.
-/

set_option maxSynthPendingDepth 3

open Set Function Topology Filter

noncomputable section

namespace Polyfold

universe u

variable {E E' : ScBanach}

/-! ### Local lemmas -/

/-- The composite inclusion `E_{N+1} → E₁`, compatible with the inclusions into `E₀`. -/
theorem ScBanach.exists_toLevelOne (E : ScBanach) (N : ℕ) :
    ∃ J : E (N + 1) →L[ℝ] E 1, ∀ x, E.toBase 1 (J x) = E.toBase (N + 1) x := by
  induction N with
  | zero => exact ⟨ContinuousLinearMap.id ℝ _, fun _ => rfl⟩
  | succ N ih =>
    obtain ⟨J, hJ⟩ := ih
    exact ⟨J.comp (E.incl (N + 1)), fun x => hJ (E.incl (N + 1) x)⟩

/-- `E_k` is dense in `E₀` (it contains `E_∞`). -/
theorem ScBanach.denseRange_toBase (E : ScBanach) (k : ℕ) : DenseRange (E.toBase k) :=
  (E.dense_smooth 0).mono fun x hx => E.mem_smooth_iff.1 (show x ∈ E.smooth from hx) k

/-- An sc-smooth retraction maps smooth points to smooth points. -/
theorem ScRetraction.apply_mem_smooth {C : Set (E 0)} (R : ScRetraction E C) {u : E 0}
    (hu : u ∈ R.U) (hs : u ∈ E.smooth) : R u ∈ E.smooth := by
  refine E.mem_smooth_iff.2 fun j => ?_
  obtain ⟨y, hy⟩ := E.mem_smooth_iff.1 hs j
  have hyU : y ∈ E.lvlSet R.U j := by rw [ScBanach.mem_lvlSet, hy]; exact hu
  have := R.isSc1.isSc0.mem_range j y hyU
  rw [hy] at this
  exact this

/-- For `U` relatively open in a partial quadrant and `A` open in `E_k`, two maps continuous on
`U` that agree at the smooth points of `A ∩ U_k` agree on `A ∩ U_k`. -/
theorem IsRelOpenInQuadrant.eq_of_eq_smooth {C U : Set (E 0)} (hU : IsRelOpenInQuadrant E C U)
    {G₁ G₂ : E 0 → E' 0} (hc₁ : ContinuousOn G₁ U) (hc₂ : ContinuousOn G₂ U) {k : ℕ}
    {A : Set (E k)} (hA : IsOpen A)
    (heq : ∀ u ∈ A ∩ E.lvlSet U k, u ∈ E.smoothLvl k → G₁ (E.toBase k u) = G₂ (E.toBase k u)) :
    ∀ u ∈ A ∩ E.lvlSet U k, G₁ (E.toBase k u) = G₂ (E.toBase k u) := by
  have hc : ∀ {G : E 0 → E' 0}, ContinuousOn G U →
      ContinuousOn (G ∘ E.toBase k) (A ∩ E.lvlSet U k) := fun hG =>
    (hG.comp (E.toBase k).continuous.continuousOn fun _ hu => hu).mono inter_subset_right
  have hEq : EqOn (G₁ ∘ E.toBase k) (G₂ ∘ E.toBase k) (A ∩ E.lvlSet U k ∩ E.smoothLvl k) :=
    fun u hu => heq u hu.1 hu.2
  have hcl : A ∩ E.lvlSet U k ⊆ closure (A ∩ E.lvlSet U k ∩ E.smoothLvl k) := by
    rintro u ⟨huA, huU⟩
    have := hA.inter_closure ⟨huA, hU.lvlSet_subset_closure_smooth k huU⟩
    rwa [← inter_assoc] at this
  exact fun u hu => hEq.of_subset_closure (hc hc₁) (hc hc₂) inter_subset_left hcl hu

/-- **Derivatives are determined on a higher level.**  Let `G₁, G₂` be sc¹ on an sc-domain `U`,
`k ≥ 1` with `J : E_k → E₁` the inclusion, and `o ∈ U_k`.  If `G₁ = G₂` on `A ∩ U_k` for a
neighbourhood `A` of `o` in `E_k`, then `DG₁(o) = DG₂(o)` on `E₀`. -/
theorem IsSc1.scDeriv_eq_of_eqOn_level {U : Set (E 0)} (hU : IsScDomain E U)
    {G₁ G₂ : E 0 → E' 0} (h₁ : IsSc1 U G₁) (h₂ : IsSc1 U G₂) {k : ℕ} (J : E k →L[ℝ] E 1)
    (hJ : ∀ x, E.toBase 1 (J x) = E.toBase k x) {o : E k} (ho : o ∈ E.lvlSet U k)
    {A : Set (E k)} (hA : A ∈ 𝓝 o)
    (heq : ∀ u ∈ A ∩ E.lvlSet U k, G₁ (E.toBase k u) = G₂ (E.toBase k u)) :
    scDeriv U G₁ (J o) = scDeriv U G₂ (J o) := by
  have hJU : MapsTo J (E.lvlSet U k) (E.lvlSet U 1) := fun u hu => by
    rw [ScBanach.mem_lvlSet, hJ]; exact hu
  have hd : ∀ {G : E 0 → E' 0}, IsSc1 U G → HasFDerivWithinAt (G ∘ E.toBase k)
      ((scDeriv U G (J o)).comp (E.toBase k)) (E.lvlSet U k) o := by
    intro G hG
    have h1 := (hG.isSc1With_scDeriv.hasFDerivWithinAt (J o) (hJU ho)).comp o
      J.hasFDerivWithinAt hJU
    have e1 : (G ∘ E.toBase 1) ∘ J = G ∘ E.toBase k := funext fun x => by
      simp only [Function.comp_apply, hJ]
    have e2 : ((scDeriv U G (J o)).comp (E.toBase 1)).comp J =
        (scDeriv U G (J o)).comp (E.toBase k) := by
      ext x; simp only [ContinuousLinearMap.comp_apply, hJ]
    rwa [e1, e2] at h1
  have hu : UniqueDiffWithinAt ℝ (E.lvlSet U k ∩ A) o := (hU.uniqueDiffWithinAt k o ho).inter hA
  have h1 := (hd h₁).mono (inter_subset_left (s := E.lvlSet U k) (t := A))
  have h2 := (hd h₂).mono (inter_subset_left (s := E.lvlSet U k) (t := A))
  have h1' : HasFDerivWithinAt (G₂ ∘ E.toBase k) ((scDeriv U G₁ (J o)).comp (E.toBase k))
      (E.lvlSet U k ∩ A) o :=
    h1.congr (fun u hu => (heq u ⟨hu.2, hu.1⟩).symm) (heq o ⟨mem_of_mem_nhds hA, ho⟩).symm
  have hc := hu.eq h1' h2
  have hd' : Dense (Submodule.span ℝ (range (E.toBase k)) : Set (E 0)) :=
    (E.denseRange_toBase k).mono Submodule.subset_span
  refine ContinuousLinearMap.ext_on hd' ?_
  rintro _ ⟨y, rfl⟩
  exact congrArg (fun L : E k →L[ℝ] E' 0 => L y) hc

/-! ### The two Part I facts for every M-polyfold -/

namespace MPolyfold

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] (P : MPolyfold X)

/-- **`(T_xX)_∞` is dense in `T_xX` for every smooth `x`** (the fact used in the proof of 2021
Lemma 7.4.6, p. 331): Chapter 7's hypothesis `DenseSmoothTangent` holds for every M-polyfold. -/
theorem denseSmoothTangent : P.DenseSmoothTangent := by
  intro y v hv
  have hv' : P.tangentProj v = P.smoothIncl y 1 := hv
  set x₀ := P.smoothVal y with hx₀
  obtain ⟨φ, hφ, hx₀φ⟩ := P.exists_isChart_mem_source x₀
  obtain ⟨R, hR⟩ := φ.model.isScRetract
  have hTO : retractTangent φ.model.E φ.model.C φ.model.O = R.tangent := by
    rw [← hR, retractTangent_eq]
  have hvφ : v ∈ tangentChartSet (P := P) φ := by
    change P.levelVal 1 (P.tangentProj v) ∈ φ.source
    rw [hv']; exact hx₀φ
  have hx₀1 : x₀ ∈ P.levelSet 1 := mem_iInter.1 (P.smoothVal_mem y) 1
  have hsm : φ x₀ ∈ φ.model.E.smooth :=
    φ.model.E.mem_smooth_iff.2 fun j => (P.mem_levelSet_iff hφ hx₀φ).1
      (mem_iInter.1 (P.smoothVal_mem y) j)
  set a := tangentChartMap hφ v with ha
  have haT : a ∈ R.tangent := hTO ▸ tangentChartMap_mem hφ hvφ
  have ho : a.1 ∈ φ.model.E.lvlSet R.retract 1 := R.fst_mem_of_mem_tangent haT
  have hoφ : φ.model.E.toBase 1 a.1 = φ x₀ := by
    rw [ha, tangentChartMap_fst hφ hvφ, hv']
    exact P.toBase_levelLift hφ hx₀φ hx₀1
  have hDh : scDeriv R.U R a.1 a.2 = a.2 := (R.mem_tangent_iff_of_mem ho).1 haT
  -- the vectors `(o, Dr(o) k)`, `k ∈ E_∞`
  set L : φ.model.E 0 → φ.model.E.tangent 0 := fun k => (a.1, scDeriv R.U R a.1 k) with hL
  have hLc : Continuous L := continuous_const.prodMk (scDeriv R.U R a.1).continuous
  have hLa : L a.2 = a := Prod.ext rfl hDh
  have hLT : MapsTo L (φ.model.E.smoothLvl 0) R.tangent := fun k _ =>
    (R.mem_tangent_iff_mem_range ho).2 ⟨k, rfl⟩
  have haL : a ∈ closure (L '' φ.model.E.smoothLvl 0) := by
    have := mem_closure_image hLc.continuousAt (φ.model.E.dense_smooth 0 a.2)
    rwa [hLa] at this
  -- transport by `(Tφ)⁻¹`
  have hinv : ContinuousOn (tangentChartInv hφ v) R.tangent := by
    rw [← hTO]; exact (tangentChart hφ v).continuousOn_invFun
  have hva : tangentChartInv hφ v a = v := by
    rw [tangentChartInv_of_mem hφ v (tangentChartMap_mem hφ hvφ)]
    exact mk_ofVec_tangentChartMap hφ hvφ
  have h2 := ((hinv a haT).mono hLT.image_subset).mem_closure_image haL
  rw [hva] at h2
  refine closure_mono ?_ h2
  rintro _ ⟨_, ⟨k, hk, rfl⟩, rfl⟩
  have hkT : L k ∈ retractTangent φ.model.E φ.model.C φ.model.O := hTO ▸ hLT hk
  rw [tangentChartInv_of_mem hφ v hkT]
  refine ⟨level_ext ?_, mem_iInter.2 fun m => ?_⟩
  · rw [tangentProj_mk, TangentPre.ofVec_x]
    change φ.symm (φ.model.E.toBase 1 a.1) = x₀
    rw [hoφ, φ.symm_apply_apply hx₀φ]
  · rw [P.tangentPolyfold.mem_levelSet_iff (P.tangentPolyfold_isChart hφ v)
      (TangentPre.ofVec hφ hkT).mem_source, tangentChart_apply, tangentChartMap_mk_ofVec hφ hkT]
    obtain ⟨z₁, hz₁⟩ := φ.model.E.mem_smooth_iff.1 hsm (m + 1)
    obtain ⟨zk, hzk⟩ := φ.model.E.mem_smooth_iff.1 (show k ∈ φ.model.E.smooth from hk) m
    have hp : ((z₁, zk) : φ.model.E.tangent m) ∈
        φ.model.E.tangent.lvlSet (φ.model.E.tangentSet R.U) m := by
      rw [ScBanach.mem_lvlSet_tangentSet, ScBanach.mem_lvlSet]
      change φ.model.E.toBase (m + 1) z₁ ∈ R.U
      rw [hz₁]
      exact R.retract_subset (hR ▸ φ.mapsTo_model x₀ hx₀φ)
    have hbase : φ.model.E.tangent.toBase m ((z₁, zk) : φ.model.E.tangent m) = (a.1, k) := by
      rw [ScBanach.tangent_toBase]
      refine Prod.ext (φ.model.E.toBase_injective 1 ?_) hzk
      change φ.model.E.toBase 1 (φ.model.E.shift.toBase m z₁) = φ.model.E.toBase 1 a.1
      rw [← ScBanach.shift_toBase, hz₁, hoφ]
    have := R.isSc1.tangentMap_isSc0.mem_range m _ hp
    rw [hbase] at this
    change (levelMap R 1 a.1, scDeriv R.U R a.1 k) ∈ _ at this
    rwa [R.levelMap_one_eq_self ho] at this

/-- **Tangents are determined near smooth points** (the fact used in the proofs of 2021
Propositions 7.4.8, p. 332, and 7.4.22, p. 338): two maps sc-smooth on open sets that agree near a
smooth point `y` in `X_∞` have the same tangent map on `T_yX`.  Chapter 7's hypothesis
`TangentDeterminedSmooth` holds for every M-polyfold. -/
theorem tangentDeterminedSmooth : P.TangentDeterminedSmooth := by
  intro f₁ f₂ U₁ U₂ hf₁ hf₂ y hy₁ hy₂ hev v hv
  have hv' : P.tangentProj v = P.smoothIncl y 1 := hv
  set x₀ := P.smoothVal y with hx₀
  -- a level neighbourhood of `y` on which `f₁ = f₂` at smooth points
  obtain ⟨T, hTsub, hTo, hyT⟩ := mem_nhds_iff.1 hev
  obtain ⟨N, O', hO', hyO', hO'T⟩ := P.exists_level_nhds_smooth hTo hyT
  have hfeq : ∀ z : P.SmoothLevel, P.smoothIncl z (N + 1) ∈ O' →
      f₁ (P.smoothVal z) = f₂ (P.smoothVal z) := fun z hz => hTsub (hO'T z hz)
  have hfx₀ : f₁ x₀ = f₂ x₀ := hfeq y hyO'
  -- charts and a common domain `U₀`
  obtain ⟨φ, hφ, hx₀φ⟩ := P.exists_isChart_mem_source x₀
  obtain ⟨ψ, hψ, hfx₀ψ⟩ := P.exists_isChart_mem_source (f₁ x₀)
  set U₀ := U₁ ∩ U₂ ∩ φ.source ∩ f₁ ⁻¹' ψ.source ∩ f₂ ⁻¹' ψ.source with hU₀
  have hU₀o : IsOpen U₀ := by
    have h1 : IsOpen (U₁ ∩ U₂ ∩ φ.source ∩ f₁ ⁻¹' ψ.source) :=
      (hf₁.continuousOn.mono fun z hz => hz.1.1).isOpen_inter_preimage
        ((hf₁.isOpen.inter hf₂.isOpen).inter φ.isOpen_source) ψ.isOpen_source
    exact (hf₂.continuousOn.mono fun z hz => hz.1.1.2).isOpen_inter_preimage h1 ψ.isOpen_source
  have hx₀U₀ : x₀ ∈ U₀ :=
    ⟨⟨⟨⟨hy₁, hy₂⟩, hx₀φ⟩, hfx₀ψ⟩, show f₂ x₀ ∈ ψ.source by rw [← hfx₀]; exact hfx₀ψ⟩
  have hU₀₁ : U₀ ⊆ U₁ := fun z hz => hz.1.1.1.1
  have hU₀₂ : U₀ ⊆ U₂ := fun z hz => hz.1.1.1.2
  have hU₀φ : U₀ ⊆ φ.source := fun z hz => hz.1.1.2
  have hU₀ψ₁ : MapsTo f₁ U₀ ψ.source := fun z hz => hz.1.2
  have hU₀ψ₂ : MapsTo f₂ U₀ ψ.source := fun z hz => hz.2
  have hvU₀ : v ∈ P.tangentPreimage U₀ := by
    change P.levelVal 1 (P.tangentProj v) ∈ U₀
    rw [hv']; exact hx₀U₀
  rw [← tangentMapOn_mono hf₁ hU₀o hU₀₁ hvU₀, ← tangentMapOn_mono hf₂ hU₀o hU₀₂ hvU₀]
  -- compare in the chart `ψ`
  refine tangentChartMap_injOn hψ (tangentMapOn_mapsTo _ hU₀ψ₁ hvU₀)
    (tangentMapOn_mapsTo _ hU₀ψ₂ hvU₀) ?_
  have hfd : ∀ {f : X → X}, MapsTo f U₀ ψ.source → TangentPre.fdomOn U₀ φ f ψ = U₀ := fun hf =>
    Subset.antisymm (fun z hz => hz.1.1) fun z hz => ⟨⟨hz, hU₀φ hz⟩, hf hz⟩
  have hvfd : ∀ {f : X → X}, MapsTo f U₀ ψ.source →
      v ∈ P.tangentPreimage (TangentPre.fdomOn U₀ φ f ψ) := fun hf => by
    rw [hfd hf]; exact hvU₀
  rw [tangentChartMap_tangentMapOn _ hφ hψ (hvfd hU₀ψ₁),
    tangentChartMap_tangentMapOn _ hφ hψ (hvfd hU₀ψ₂), hfd hU₀ψ₁, hfd hU₀ψ₂]
  -- the retract `φ(U₀)` and the coordinate representatives `ψ ∘ fᵢ ∘ φ⁻¹`
  obtain ⟨R₀, hR₀⟩ := φ.isScRetract_image hU₀φ hU₀o
  have hF₁ := hf₁.smooth φ ψ hφ hψ U₀ hU₀o (fun z hz => ⟨hU₀₁ hz, hU₀φ hz⟩) hU₀ψ₁
  have hF₂ := hf₂.smooth φ ψ hφ hψ U₀ hU₀o (fun z hz => ⟨hU₀₂ hz, hU₀φ hz⟩) hU₀ψ₂
  have hvφ : v ∈ tangentChartSet (P := P) φ := hU₀φ hvU₀
  have hx₀1 : x₀ ∈ P.levelSet 1 := mem_iInter.1 (P.smoothVal_mem y) 1
  set a := tangentChartMap hφ v with ha
  have hoφ : φ.model.E.toBase 1 a.1 = φ x₀ := by
    rw [ha, tangentChartMap_fst hφ hvφ, hv']
    exact P.toBase_levelLift hφ hx₀φ hx₀1
  have haU₀ : a ∈ retractTangent φ.model.E φ.model.C (φ '' U₀) :=
    (TangentPre.mem_retractTangent_image_iff hU₀φ hU₀o (by rw [hoφ]; exact ⟨x₀, hx₀U₀, rfl⟩)).2
      (tangentChartMap_mem hφ hvφ)
  rw [retractTangentMap_apply hF₁ R₀ hR₀ haU₀, retractTangentMap_apply hF₂ R₀ hR₀ haU₀]
  have hφx₀O : φ x₀ ∈ R₀.retract := hR₀ ▸ ⟨x₀, hx₀U₀, rfl⟩
  have hφx₀R : R₀ (φ x₀) = φ x₀ := R₀.apply_eq_self_of_mem_retract hφx₀O
  rw [Prod.mk.injEq]
  refine ⟨?_, ?_⟩
  · -- the base points
    have hval : ((ψ ∘ f₁ ∘ φ.symm) ∘ R₀) (φ.model.E.toBase 1 a.1) =
        ((ψ ∘ f₂ ∘ φ.symm) ∘ R₀) (φ.model.E.toBase 1 a.1) := by
      simp only [Function.comp_apply]
      rw [hoφ, hφx₀R, φ.symm_apply_apply hx₀φ, hfx₀]
    unfold levelMap
    rw [hval]
  -- the derivatives, compared on level `N + 1`
  obtain ⟨J, hJ⟩ := φ.model.E.exists_toLevelOne N
  have hx₀N : x₀ ∈ P.levelSet (N + 1) := mem_iInter.1 (P.smoothVal_mem y) (N + 1)
  set o := levelLift φ (N + 1) x₀ with ho
  have hoφ' : φ.model.E.toBase (N + 1) o = φ x₀ := P.toBase_levelLift hφ hx₀φ hx₀N
  have hJo : J o = a.1 := φ.model.E.toBase_injective 1 (by rw [hJ, hoφ', hoφ])
  have hoU : o ∈ φ.model.E.lvlSet R₀.U (N + 1) := by
    rw [ScBanach.mem_lvlSet, hoφ']; exact R₀.retract_subset hφx₀O
  -- the open set `W ⊆ E_{N+1}` corresponding to `O'`
  have hemb := P.isEmbedding_levelLift hφ (N + 1)
  obtain ⟨W, hW, hWeq⟩ := hemb.isInducing.isOpen_iff.1
    (hO'.preimage (continuous_subtype_val
      (p := fun z : P.Level (N + 1) => z ∈ P.levelVal (N + 1) ⁻¹' φ.source)))
  have hW' : ∀ (z : P.Level (N + 1)) (hz : P.levelVal (N + 1) z ∈ φ.source),
      levelLift φ (N + 1) (P.levelVal (N + 1) z) ∈ W → z ∈ O' := by
    intro z hz hzW
    have : (⟨z, hz⟩ : (P.levelVal (N + 1) ⁻¹' φ.source : Set (P.Level (N + 1)))) ∈
        (fun x : (P.levelVal (N + 1) ⁻¹' φ.source : Set (P.Level (N + 1))) =>
          levelLift φ (N + 1) (P.levelVal (N + 1) x)) ⁻¹' W := hzW
    rw [hWeq] at this
    exact this
  have hoW : o ∈ W := by
    have : (⟨P.smoothIncl y (N + 1), hx₀φ⟩ :
        (P.levelVal (N + 1) ⁻¹' φ.source : Set (P.Level (N + 1)))) ∈
        (Subtype.val ⁻¹' O' : Set (P.levelVal (N + 1) ⁻¹' φ.source : Set (P.Level (N + 1)))) :=
      hyO'
    rw [← hWeq] at this
    exact this
  -- the relatively open set of `U_{N+1}` mapped into `W` by `r₀`
  obtain ⟨A, hA, hAeq⟩ := (continuousOn_iff'.1 (R₀.isSc1.isSc0.continuousOn (N + 1))) W hW
  have hRo : levelMap R₀ (N + 1) o = o :=
    levelMap_eq_of_toBase_eq (by rw [hoφ', hφx₀R])
  have hoA : o ∈ A := by
    have : o ∈ levelMap R₀ (N + 1) ⁻¹' W ∩ φ.model.E.lvlSet R₀.U (N + 1) :=
      ⟨by rw [mem_preimage, hRo]; exact hoW, hoU⟩
    rw [hAeq] at this
    exact this.1
  have hG₁ := hF₁.comp_isScSmooth R₀ hR₀
  have hG₂ := hF₂.comp_isScSmooth R₀ hR₀
  have key := IsSc1.scDeriv_eq_of_eqOn_level R₀.isScDomain hG₁.isSc1 hG₂.isSc1 J hJ hoU
    (hA.mem_nhds hoA) (R₀.relOpen.eq_of_eq_smooth hG₁.isSc1.isSc0.continuousOn_base
      hG₂.isSc1.isSc0.continuousOn_base hA ?_)
  · rw [hJo] at key
    rw [key]
  -- equality at the smooth points
  rintro u ⟨huA, huU⟩ hus
  have hw : levelMap R₀ (N + 1) u ∈ W := by
    have : u ∈ A ∩ φ.model.E.lvlSet R₀.U (N + 1) := ⟨huA, huU⟩
    rw [← hAeq] at this
    exact this.1
  have hRu : φ.model.E.toBase (N + 1) (levelMap R₀ (N + 1) u) =
      R₀ (φ.model.E.toBase (N + 1) u) := R₀.isSc1.isSc0.toBase_levelMap huU
  obtain ⟨x, hxU₀, hxeq⟩ : R₀ (φ.model.E.toBase (N + 1) u) ∈ φ '' U₀ :=
    hR₀ ▸ R₀.apply_mem_retract huU
  have hxφ : x ∈ φ.source := hU₀φ hxU₀
  have hxs : x ∈ P.smoothSet :=
    mem_smoothSet_of_chart hφ hxφ (by rw [hxeq]; exact R₀.apply_mem_smooth huU hus)
  have hxN : x ∈ P.levelSet (N + 1) := mem_iInter.1 hxs (N + 1)
  have hlift : levelLift φ (N + 1) x = levelMap R₀ (N + 1) u :=
    φ.model.E.toBase_injective (N + 1) (by rw [P.toBase_levelLift hφ hxφ hxN, hRu, hxeq])
  have hxO' : P.smoothIncl (P.smoothMk x hxs) (N + 1) ∈ O' :=
    hW' _ hxφ (by change levelLift φ (N + 1) x ∈ W; rw [hlift]; exact hw)
  have hfx : f₁ x = f₂ x := hfeq _ hxO'
  change ψ (f₁ (φ.symm (R₀ (φ.model.E.toBase (N + 1) u)))) =
    ψ (f₂ (φ.symm (R₀ (φ.model.E.toBase (N + 1) u))))
  rw [← hxeq, φ.symm_apply_apply hxφ, hfx]

variable {P}

/-- With `denseSmooth`, `isOpenMap_tangentProj`, `tangentDeterminedSmooth`, the bundle
`SmoothRegular` of Part I facts reduces to `SmoothConnected`. -/
theorem smoothRegular_of_smoothConnected (hc : P.SmoothConnected) : P.SmoothRegular :=
  ⟨P.denseSmooth, hc, P.isOpenMap_tangentProj, P.tangentDeterminedSmooth⟩

/-- `SmoothRegular ⟺ SmoothConnected` for every M-polyfold. -/
theorem smoothRegular_iff_smoothConnected : P.SmoothRegular ↔ P.SmoothConnected :=
  ⟨fun h => h.smoothConnected, smoothRegular_of_smoothConnected⟩

end MPolyfold

/-! ### The §7.4 results without the discharged hypotheses -/

namespace EpGroupoid

variable {Obj Mor : Type u} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] (X : EpGroupoid Obj Mor)

/-- **2021 Lemma 7.4.6, p. 331**: (ZHOU) ⇒ (ZHOU'), with no hypothesis beyond (ZHOU)
(`DenseSmoothTangent` is `MPolyfold.denseSmoothTangent`). -/
theorem lemma_7_4_6_2021_of_isZhou (hZ : X.IsZhou) : X.IsZhou' :=
  X.lemma_7_4_6_2021 hZ X.PObj.denseSmoothTangent

/-- **2021 Proposition 7.4.8, (ZHOU') ⇒ (ZHOU)**, with `SmoothConnected` in place of
`SmoothRegular`. -/
theorem isZhou_of_isZhou'_of_smoothConnected (hc : X.PObj.SmoothConnected) (hZ : X.IsZhou') :
    X.IsZhou :=
  X.isZhou_of_isZhou' (MPolyfold.smoothRegular_of_smoothConnected hc) hZ

/-- **2021 Proposition 7.4.8, p. 332**: (ZHOU) ⇔ (ZHOU'), given only `SmoothConnected`
(`DenseSmoothTangent`, `IsOpenMap tangentProj`, `TangentDeterminedSmooth`, `DenseSmooth` are
proved). -/
theorem proposition_7_4_8_2021_of_smoothConnected (hc : X.PObj.SmoothConnected) :
    X.IsZhou ↔ X.IsZhou' :=
  X.proposition_7_4_8_2021 (MPolyfold.smoothRegular_of_smoothConnected hc)
    X.PObj.denseSmoothTangent

/-- **2021 Proposition 7.4.10, p. 333**: (ZHOU) ⇒ (LUC), given only `SmoothConnected`. -/
theorem proposition_7_4_10_2021_of_smoothConnected (hc : X.PObj.SmoothConnected)
    (hZ : X.IsZhou) : X.IsLUC :=
  X.proposition_7_4_10_2021 (MPolyfold.smoothRegular_of_smoothConnected hc) hZ

/-- **2021 Proposition 7.4.22, p. 338**: (ZHOU) ⇒ (LR), given only `SmoothConnected`. -/
theorem proposition_7_4_22_2021_of_smoothConnected (hc : X.PObj.SmoothConnected)
    (hZ : X.IsZhou) : X.IsLR :=
  X.proposition_7_4_22_2021 (MPolyfold.smoothRegular_of_smoothConnected hc) hZ

end EpGroupoid

namespace EP

/-- **2021 Proposition 7.4.9, p. 333**: (ZHOU) for `X` gives (ZHOU) for every `X^i`, given only
`SmoothConnected` for every `X^i`. -/
theorem proposition_7_4_9_2021_of_smoothConnected (A : EP.{u}) (hZ : A.X.IsZhou)
    (hc : ∀ i, (A.lift i).X.PObj.SmoothConnected) (i : ℕ) : (A.lift i).X.IsZhou :=
  A.proposition_7_4_9_2021 hZ A.X.PObj.denseSmoothTangent
    (fun j => MPolyfold.smoothRegular_of_smoothConnected (hc j)) i

/-- **2021 Corollary 7.4.11, p. 334**: under (ZHOU) every `X^i` has (LUC), given only
`SmoothConnected` for every `X^i`. -/
theorem corollary_7_4_11_all_2021_of_smoothConnected (A : EP.{u}) (hZ : A.X.IsZhou)
    (hc : ∀ i, (A.lift i).X.PObj.SmoothConnected) (i : ℕ) : (A.lift i).X.IsLUC :=
  A.corollary_7_4_11_all_2021 hZ A.X.PObj.denseSmoothTangent
    (fun j => MPolyfold.smoothRegular_of_smoothConnected (hc j)) i

/-- **2021 Theorem 7.4.13, p. 334**: (ZHOU) ⇒ (SLUC), given only `SmoothConnected` for every
`X^i`. -/
theorem theorem_7_4_13_all_2021_of_smoothConnected (A : EP.{u}) (hZ : A.X.IsZhou)
    (hc : ∀ i, (A.lift i).X.PObj.SmoothConnected) : A.IsSLUC :=
  A.theorem_7_4_13_all_2021 hZ A.X.PObj.denseSmoothTangent
    (fun j => MPolyfold.smoothRegular_of_smoothConnected (hc j))

/-- **2021 Theorem 7.4.24, p. 340**: (ZHOU) ⇒ (SLR), given only `SmoothConnected` for every
`X^i`. -/
theorem theorem_7_4_24_all_2021_of_smoothConnected (A : EP.{u}) (hZ : A.X.IsZhou)
    (hc : ∀ i, (A.lift i).X.PObj.SmoothConnected) : A.IsSLR :=
  A.theorem_7_4_24_all_2021 hZ A.X.PObj.denseSmoothTangent
    (fun j => MPolyfold.smoothRegular_of_smoothConnected (hc j))

end EP

end Polyfold
