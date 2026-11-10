import Polyfold.Chapter6.InvariantProductEnds2021
import Polyfold.Chapter6.SolutionSetOpen2021
import Polyfold.Chapter9.MathlibFormsBridge2021
import Polyfold.Chapter9.SolutionFaceForms2021

/-!
# The product ends of `S_F` as charted spaces (2021 Theorem 6.7.1, independence)

Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021): the ends of the
cobordism in the proof of Theorem 6.7.1 (pp. 277–278; preprint Theorem 6.43).  Over
`t ∈ (a, b)`, where every slice of the section `G` of `π*P → ℝ¹ × X` is `g`, the solution set
`S_G` is `(a, b) × S_g`.  `InvariantProductEnds2021` proves the end computations for an abstract
`ProductEnd`; this file builds the `ProductEnd` for the actual solution sets with their corner
charted spaces (`cornerChartedSpace`, `solChartedSpaceOpen`).

* `MChart.transport`: an M-polyfold chart carried along a partial homeomorphism; compatibility is
  preserved (`MChart.Compatible.transport`).
* `MPolyfold.isChart_of_forall_compatible`: a chart compatible near each of its points with a
  chart of the structure is a chart of the structure.
* `timeChart a b`: the chart `t ↦ t` of `(a, b) ⊆ ℝ` modelled on `ℝ¹`.
* `endPH`: the identification `{p ∈ A' | t(p) ∈ (a, b)} ≅ (a, b) × A` for sub-M-polyfolds
  `A ⊆ X`, `A' ⊆ ℝ¹ × X` with `A' = (a, b) × A` over `(a, b)`.
* `prodEndChart χ`: the product chart `(t, x) ↦ (t, χ(x))` of a chart `χ` of `A`, a chart of the
  sub-M-polyfold structure of `A'` (`isChart_prodEndChart`): on the sub-charts of `A'` built on
  the product charts `id × ψ` of `ℝ¹ × X` its transition maps are the identity.
* `MPolyfold.CornerCoords.prodRn κ`: corner coordinates of dimension `k + 1` on `A'` from corner
  coordinates `κ` of dimension `k` on `A`, the time coordinate first and shifted by `−a`.
* `productEndOfSub`: the `ProductEnd` of `A'` over `A` for the corner charted spaces of any corner
  structures; `endChart_eqOnSource`: its product charts are the charts of `CornerCoords.prodRn`.
* `solProductEnd`, `StrongBundle.IsCobordismData.productEndLeft`/`productEndRight`: the ends of
  `S_G ∩ V'` and of `S_F ∩ V'` over `S_g ∩ V`, `S_{f+σ₀} ∩ V`, `S_{f+σ₁} ∩ V`.
* `isLinOfIndex_end_iff`: the index of `G` at `(t, x)` is the index of `g` at `x` plus one; so
  the index-`(k+1)` part of `S_F` ends on the index-`k` parts of `S_{f+σᵢ}` (`hVend_left`).
* `ProductEnd.IsEndPullback Ω ω`: `Ω` reads as `tail^*ω` in the product charts;
  `ProductEnd.chartForm_extDeriv_smulFun_stdFrame`: then `d(g(t) Ω)` has the coefficient
  `g′(t) ω`, the hypothesis `hprod` of `ProductEnd.integral_end_fubini`.
* `isEndPullback_formsInftyRestrict_snd`: the restriction to `A'` of `p₁^*ω` (`ω ∈ Ωᵏ_∞(X)`,
  `formsInftyPullback`, `formsInftyRestrict`) and `ω|_A` satisfy `IsEndPullback`, from the tangent
  map identity `tangentMap_prodRn_fiberMap`; `chartForm_extDeriv_smulFun_formsInftyRestrict_snd`
  is the resulting `hprod`.

Not built here: the face-form version (`solFaceForm` of `p₁^*τ` on `∂S_F` read as the pull-back of
`solFaceForm τ` on `∂S_i`, and an extension `g′ dt ∧ p₁^*β` of it for
`ProductEnd.faceIntegral_end_sign`).
-/

open Set Filter Topology Manifold Module

local notation3 "∞" => ((⊤ : ℕ∞) : WithTop ℕ∞)

/-- Mathlib's model with corners `[0,∞)ⁿ ⊆ ℝⁿ`. -/
local notation "𝓠" => modelWithCornersEuclideanQuadrant

noncomputable section

namespace Polyfold

universe u

/-! ### Charts transported along a partial homeomorphism -/

namespace MChart

variable {W : Type*} {Z : Type*} [TopologicalSpace W] [TopologicalSpace Z]

/-- **A chart transported along a partial homeomorphism** `Φ : W → Z`: for a chart `ζ` of `Z`
with domain in `Φ(W)`, the chart `ζ ∘ Φ` of `W`, with the model of `ζ`. -/
def transport (ζ : MChart Z) (Φ : OpenPartialHomeomorph W Z) (h : ζ.source ⊆ Φ.target) :
    MChart W where
  model := ζ.model
  toPartialEquiv := Φ.toPartialEquiv.trans ζ.toPartialEquiv
  isOpen_source := Φ.isOpen_inter_preimage ζ.isOpen_source
  target_eq := by
    ext z
    rw [PartialEquiv.trans_target, ← ζ.target_eq]
    exact ⟨fun hz => hz.1, fun hz => ⟨hz, h (ζ.toPartialEquiv.map_target hz)⟩⟩
  continuousOn_toFun := ζ.continuousOn_toFun.comp (Φ.continuousOn.mono inter_subset_left)
    fun _ hx => hx.2
  continuousOn_invFun := Φ.continuousOn_symm.comp ζ.continuousOn_invFun
    fun _ hz => h (ζ.symm_mapsTo hz)

variable (ζ ζ' : MChart Z) (Φ : OpenPartialHomeomorph W Z) (h : ζ.source ⊆ Φ.target)
  (h' : ζ'.source ⊆ Φ.target)

@[simp] lemma transport_apply (p : W) : ζ.transport Φ h p = ζ (Φ p) := rfl

lemma transport_source : (ζ.transport Φ h).source = Φ.source ∩ Φ ⁻¹' ζ.source := rfl

lemma transport_symm_apply (z : ζ.model.E 0) : (ζ.transport Φ h).symm z = Φ.symm (ζ.symm z) :=
  rfl

/-- The overlap of two transported charts is the overlap of the charts. -/
lemma overlap_transport : (ζ.transport Φ h).overlap (ζ'.transport Φ h') = ζ.overlap ζ' := by
  ext z
  constructor
  · rintro ⟨p, ⟨⟨-, hp1⟩, -, hp2⟩, rfl⟩
    exact ⟨Φ p, ⟨hp1, hp2⟩, rfl⟩
  · rintro ⟨x, ⟨hx, hx'⟩, rfl⟩
    have hxt := h hx
    refine ⟨Φ.symm x, ⟨⟨Φ.map_target hxt, ?_⟩, Φ.map_target hxt, ?_⟩, ?_⟩
    · change Φ (Φ.symm x) ∈ ζ.source; rw [Φ.right_inv hxt]; exact hx
    · change Φ (Φ.symm x) ∈ ζ'.source; rw [Φ.right_inv hxt]; exact hx'
    · change ζ (Φ (Φ.symm x)) = ζ x
      rw [Φ.right_inv hxt]

lemma transition_transport {z : ζ.model.E 0} (hz : z ∈ ζ.overlap ζ') :
    (ζ.transport Φ h).transition (ζ'.transport Φ h') z = ζ.transition ζ' z := by
  obtain ⟨x, ⟨hx, -⟩, rfl⟩ := hz
  change ζ' (Φ (Φ.symm (ζ.symm (ζ x)))) = ζ' (ζ.symm (ζ x))
  rw [ζ.symm_apply_apply hx, Φ.right_inv (h hx)]

variable {ζ ζ'} in
/-- **Transport preserves compatibility**: the transition maps are those of the charts. -/
theorem Compatible.transport (hc : ζ.Compatible ζ') :
    (ζ.transport Φ h).Compatible (ζ'.transport Φ h') := by
  constructor
  · rw [overlap_transport, overlap_transport]
    exact hc.1.congr fun z hz => (transition_transport ζ ζ' Φ h h' hz).symm
  · rw [overlap_transport, overlap_transport]
    exact hc.2.congr fun z hz => (transition_transport ζ' ζ Φ h' h hz).symm

end MChart

/-- **Charts of a structure from compatible neighbours**: a chart which near each point of its
domain is compatible with some chart of the M-polyfold structure is a chart of the structure
(locality of compatibility, `MChart.compatible_of_locally`). -/
theorem MPolyfold.isChart_of_forall_compatible {X : Type u} [TopologicalSpace X] [T2Space X]
    [ParacompactSpace X] (P : MPolyfold X) {χ : MChart X}
    (h : ∀ x ∈ χ.source, ∃ σ : MChart X, P.IsChart σ ∧ x ∈ σ.source ∧ χ.Compatible σ) :
    P.IsChart χ := fun ψ hψ =>
  MChart.compatible_of_locally χ ψ {σ | P.IsChart σ ∧ χ.Compatible σ} (fun _ hσ => hσ.2)
    (fun _ hσ => hσ.1 ψ hψ) fun x hx => by
      obtain ⟨σ, h1, h2, h3⟩ := h x hx.1
      exact ⟨σ, ⟨h1, h3⟩, h2⟩

/-! ### The time chart -/

/-- The time interval `(a, b)` as a relatively open subset of the quadrant `ℝ¹` of `ℝ¹`. -/
theorem relOpen_time (a b : ℝ) :
    IsRelOpenInQuadrant (rnSc 1) univ {r : Fin 1 → ℝ | r 0 ∈ Ioo a b} :=
  ⟨isPartialQuadrant_univ _, {r | r 0 ∈ Ioo a b}, isOpen_Ioo.preimage (continuous_apply 0),
    (inter_univ _).symm⟩

/-- **The time chart** `t ↦ (t)` of `(a, b) ⊆ ℝ`, modelled on `{r ∈ ℝ¹ | r₀ ∈ (a, b)}` with the
constant structure of `ℝ¹`. -/
def timeChart (a b : ℝ) : MChart ℝ where
  model := LocalModel.ofRelOpen (relOpen_time a b)
  toPartialEquiv :=
    { toFun := fun t => (fun _ => t : Fin 1 → ℝ)
      invFun := fun r => r 0
      source := Ioo a b
      target := {r : Fin 1 → ℝ | r 0 ∈ Ioo a b}
      map_source' := fun _ ht => ht
      map_target' := fun _ hr => hr
      left_inv' := fun _ _ => rfl
      right_inv' := fun r _ => funext fun i => by rw [Subsingleton.elim i 0] }
  isOpen_source := isOpen_Ioo
  target_eq := rfl
  continuousOn_toFun := (continuous_pi fun _ => continuous_id).continuousOn
  continuousOn_invFun := (continuous_apply 0).continuousOn

@[simp] lemma timeChart_apply (a b t : ℝ) : timeChart a b t = fun _ => t := rfl

lemma timeChart_source (a b : ℝ) : (timeChart a b).source = Ioo a b := rfl

/-! ### The identification of an end with `(a, b) × A` -/

section EndPH

variable {X : Type u} [TopologicalSpace X] {A : Set X} {A' : Set ((Fin 1 → ℝ) × X)} {a b : ℝ}

/-- The time `t` if `t ∈ (a, b)`, the midpoint of `(a, b)` otherwise. -/
def clampTime (a b t : ℝ) : ℝ := if t ∈ Ioo a b then t else (a + b) / 2

theorem clampTime_mem (hab : a < b) (t : ℝ) : clampTime a b t ∈ Ioo a b := by
  unfold clampTime
  split_ifs with h
  · exact h
  · constructor <;> linarith

theorem clampTime_of_mem {t : ℝ} (ht : t ∈ Ioo a b) : clampTime a b t = t := if_pos ht

variable (A) in
open scoped Classical in
/-- The `X`-component of a point of `A'`, as a point of `A` (junk value `x₀` off `A`). -/
def endProj (x₀ : A) (p : A') : A := if h : p.1.2 ∈ A then ⟨p.1.2, h⟩ else x₀

omit [TopologicalSpace X] in
lemma endProj_val (x₀ : A) {p : A'} (hp : p.1.2 ∈ A) : (endProj A x₀ p).1 = p.1.2 := by
  rw [endProj, dif_pos hp]

variable (hab : a < b) (hend : ∀ z : (Fin 1 → ℝ) × X, z.1 0 ∈ Ioo a b → (z ∈ A' ↔ z.2 ∈ A))
  (x₀ : A)

omit [TopologicalSpace X] in
include hend in
lemma endProj_val_of_mem {p : A'} (hp : p.1.1 0 ∈ Ioo a b) : (endProj A x₀ p).1 = p.1.2 :=
  endProj_val x₀ ((hend p.1 hp).1 p.2)

omit [TopologicalSpace X] in
include hend in
/-- No point of `A'` lies over `(a, b)` when `A` is empty. -/
theorem not_mem_Ioo_of_isEmpty (hA0 : IsEmpty A) (p : A') : p.1.1 0 ∉ Ioo a b := fun hp =>
  hA0.false ⟨_, (hend p.1 hp).1 p.2⟩

/-- **The identification of the end of `A'` with `(a, b) × A`**: `p ↦ (t(p), x(p))` on
`{p ∈ A' | t(p) ∈ (a, b)}`, for `A' = (a, b) × A` over `(a, b)` (`hend`). -/
def endPH : OpenPartialHomeomorph A' (ℝ × A) where
  toFun p := (p.1.1 0, endProj A x₀ p)
  invFun q := ⟨(fun _ => clampTime a b q.1, q.2.1), (hend _ (clampTime_mem hab q.1)).2 q.2.2⟩
  source := {p | p.1.1 0 ∈ Ioo a b}
  target := Ioo a b ×ˢ univ
  map_source' _ hp := ⟨hp, mem_univ _⟩
  map_target' q _ := clampTime_mem hab q.1
  left_inv' p hp := by
    apply Subtype.ext
    change ((fun _ => clampTime a b (p.1.1 0), (endProj A x₀ p).1) : (Fin 1 → ℝ) × X) = p.1
    rw [clampTime_of_mem hp, endProj_val_of_mem hend x₀ hp]
    exact Prod.ext (funext fun i => by rw [Subsingleton.elim i 0]) rfl
  right_inv' q hq := by
    refine Prod.ext (clampTime_of_mem hq.1) (Subtype.ext ?_)
    exact endProj_val x₀ q.2.2
  open_source :=
    isOpen_Ioo.preimage ((continuous_apply 0).comp (continuous_fst.comp continuous_subtype_val))
  open_target := isOpen_Ioo.prod isOpen_univ
  continuousOn_toFun := by
    refine ContinuousOn.prodMk ((continuous_apply 0).comp
      (continuous_fst.comp continuous_subtype_val)).continuousOn ?_
    refine Topology.IsInducing.subtypeVal.continuousOn_iff.2 ?_
    refine (continuous_snd.comp continuous_subtype_val).continuousOn.congr fun p hp => ?_
    exact endProj_val_of_mem hend x₀ hp
  continuousOn_invFun := by
    refine Topology.IsInducing.subtypeVal.continuousOn_iff.2 ?_
    have hc : Continuous fun q : ℝ × A => ((fun _ => q.1 : Fin 1 → ℝ), q.2.1) :=
      (continuous_pi fun _ => continuous_fst).prodMk (continuous_subtype_val.comp continuous_snd)
    refine hc.continuousOn.congr fun q hq => ?_
    change ((fun _ => clampTime a b q.1, q.2.1) : (Fin 1 → ℝ) × X) = ((fun _ => q.1), q.2.1)
    rw [clampTime_of_mem hq.1]

lemma endPH_source : (endPH hab hend x₀).source = {p | p.1.1 0 ∈ Ioo a b} := rfl

lemma endPH_target : (endPH hab hend x₀).target = Ioo a b ×ˢ univ := rfl

lemma endPH_apply (p : A') : endPH hab hend x₀ p = (p.1.1 0, endProj A x₀ p) := rfl

lemma endPH_symm_apply_val {q : ℝ × A} (hq : q.1 ∈ Ioo a b) :
    ((endPH hab hend x₀).symm q).1 = ((fun _ => q.1 : Fin 1 → ℝ), q.2.1) := by
  change ((fun _ => clampTime a b q.1, q.2.1) : (Fin 1 → ℝ) × X) = _
  rw [clampTime_of_mem hq]

/-- The product chart `(t, x) ↦ (t, χ(x))` of the end of `A'`. -/
def prodEndChart (χ : MChart A) : MChart A' :=
  ((timeChart a b).prod χ).transport (endPH hab hend x₀) fun _ hq => ⟨hq.1, mem_univ _⟩

lemma prodEndChart_apply (χ : MChart A) (p : A') :
    prodEndChart hab hend x₀ χ p = ((fun _ => p.1.1 0 : Fin 1 → ℝ), χ (endProj A x₀ p)) := rfl

lemma mem_prodEndChart_source {χ : MChart A} {p : A'} :
    p ∈ (prodEndChart hab hend x₀ χ).source ↔
      p.1.1 0 ∈ Ioo a b ∧ endProj A x₀ p ∈ χ.source :=
  ⟨fun hp => ⟨hp.1, hp.2.2⟩, fun hp => ⟨hp.1, hp.1, hp.2⟩⟩

/-- The model of the product chart of a corner chart is relatively open in its quadrant. -/
theorem relOpen_prodEndChart {χ : MChart A} (hc : χ.IsCornerChart) :
    IsRelOpenInQuadrant (prodEndChart hab hend x₀ χ).model.E
      (prodEndChart hab hend x₀ χ).model.C (prodEndChart hab hend x₀ χ).model.O :=
  (relOpen_time a b).prod hc.isRelOpenInQuadrant

/-- The model space of the product chart of a corner chart is finite-dimensional. -/
theorem finiteDimensional_prodEndChart {χ : MChart A} (hc : χ.IsCornerChart) :
    FiniteDimensional ℝ ((prodEndChart hab hend x₀ χ).model.E 0) := by
  have := hc.finiteDimensional
  exact (inferInstance : FiniteDimensional ℝ ((Fin 1 → ℝ) × χ.model.E 0))

theorem relOpen_prodEndChart_const {χ : MChart A} (hc : χ.IsCornerChart) :
    haveI := finiteDimensional_prodEndChart hab hend x₀ hc
    IsRelOpenInQuadrant (ScBanach.const ((prodEndChart hab hend x₀ χ).model.E 0))
      (prodEndChart hab hend x₀ χ).model.C
      ((id : (ScBanach.const ((prodEndChart hab hend x₀ χ).model.E 0)) 0 → _) ''
        (prodEndChart hab hend x₀ χ).model.O) := by
  have := finiteDimensional_prodEndChart hab hend x₀ hc
  rw [image_id]
  exact (relOpen_prodEndChart hab hend x₀ hc).toConst

/-- **The product corner chart**: the product chart `prodEndChart` with the constant sc-structure
on its finite-dimensional model (`MChart.compDiffeo` with the identity), a corner chart. -/
def cornerEndChart {χ : MChart A} (hc : χ.IsCornerChart) : MChart A' :=
  haveI := finiteDimensional_prodEndChart hab hend x₀ hc
  (prodEndChart hab hend x₀ χ).compDiffeo
    (relOpen_prodEndChart hab hend x₀ hc).isScDiffeoQuadrant_toConst subset_rfl
    (relOpen_prodEndChart_const hab hend x₀ hc).isScRetract

lemma cornerEndChart_apply {χ : MChart A} (hc : χ.IsCornerChart) (p : A') :
    cornerEndChart hab hend x₀ hc p = ((fun _ => p.1.1 0 : Fin 1 → ℝ), χ (endProj A x₀ p)) := rfl

lemma cornerEndChart_source {χ : MChart A} (hc : χ.IsCornerChart) :
    (cornerEndChart hab hend x₀ hc).source = (prodEndChart hab hend x₀ χ).source := rfl

theorem isCornerChart_cornerEndChart {χ : MChart A} (hc : χ.IsCornerChart) :
    (cornerEndChart hab hend x₀ hc).IsCornerChart := by
  have := finiteDimensional_prodEndChart hab hend x₀ hc
  exact ⟨_, inferInstance, inferInstance, inferInstance, _, _,
    relOpen_prodEndChart_const hab hend x₀ hc, rfl⟩

end EndPH

/-! ### The product charts are charts of the sub-M-polyfold `A'` -/

section ProdChart

open MPolyfold

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  [ParacompactSpace ((Fin 1 → ℝ) × X)] {A : Set X} [ParacompactSpace A]
  (hA : PX.IsSubMPolyfold A) {A' : Set ((Fin 1 → ℝ) × X)} [ParacompactSpace A']
  (hA' : ((rnPolyfold 1).prod PX).IsSubMPolyfold A') {a b : ℝ} (hab : a < b)
  (hend : ∀ z : (Fin 1 → ℝ) × X, z.1 0 ∈ Ioo a b → (z ∈ A' ↔ z.2 ∈ A)) (x₀ : A)

omit [ParacompactSpace A] in
/-- **The product chart of a sub-chart of `A` is a chart of `A'`**: on the sub-charts of `A'`
built on the product chart `(r ↦ r) × ψ` of `ℝ¹ × X`, the transition maps of
`(t, x) ↦ (t, ψ(x))` are the identity. -/
theorem isChart_prodEndChart_subChart (d : PX.SubData A) {ψ : MChart X} (hψ : PX.IsChart ψ)
    (y₀ : A) : (subPolyfold hA').IsChart (prodEndChart hab hend x₀ (subChart d hψ y₀)) := by
  set σ := prodEndChart hab hend x₀ (subChart d hψ y₀) with hσ
  have hφ : ((rnPolyfold 1).prod PX).IsChart ((rnChart 1 0).prod ψ) :=
    MPolyfold.IsChart.prod (isChart_rnChart 0) hψ
  have hsrcA : ∀ p ∈ σ.source, p.1.2 ∈ d.shrink ψ := fun p hp => by
    have h2 := ((mem_prodEndChart_source hab hend x₀).1 hp).2
    rw [subChart_source, mem_ofPred_eq, endProj_val_of_mem hend x₀ hp.1] at h2
    exact h2
  refine isChart_subPolyfold_of_compatible hA' hφ
    (fun p hp => ⟨mem_univ _, d.shrink_subset_source ψ (hsrcA p hp)⟩) fun d' b₀ => ?_
  set τ := subChart d' hφ b₀ with hτ
  have heq : ∀ p ∈ σ.source, σ p = τ p := fun p hp => by
    change (((fun _ => p.1.1 0 : Fin 1 → ℝ), ψ (endProj A x₀ p).1) : (Fin 1 → ℝ) × ψ.model.E 0) =
      (rnChart 1 0 p.1.1, ψ p.1.2)
    rw [endProj_val_of_mem hend x₀ hp.1]
    refine Prod.ext (funext fun i => ?_) rfl
    rw [Subsingleton.elim i 0, rnChart_apply, sub_zero]
  have hov : σ.overlap τ = τ.overlap σ := by
    change σ '' (σ.source ∩ τ.source) = τ '' (τ.source ∩ σ.source)
    rw [inter_comm τ.source]
    exact image_congr fun p hp => heq p hp.1
  have htr : ∀ z ∈ σ.overlap τ, σ.transition τ z = z := by
    rintro _ ⟨p, hp, rfl⟩
    rw [σ.transition_apply τ hp.1, heq p hp.1]
  have htr' : ∀ z ∈ τ.overlap σ, τ.transition σ z = z := by
    rintro _ ⟨p, hp, rfl⟩
    rw [τ.transition_apply σ hp.1, heq p hp.2]
  refine ⟨?_, ?_⟩
  · rw [← hov]
    exact (isScSmoothRetractMap_id _).congr fun z hz => (htr z hz).symm
  · rw [hov]
    exact (isScSmoothRetractMap_id _).congr fun z hz => (htr' z hz).symm

/-- **The product chart `(t, x) ↦ (t, χ(x))` of a chart `χ` of `A` is a chart of `A'`**: near each
point it is compatible with the product chart of a sub-chart of `A`
(`isChart_prodEndChart_subChart`), the transition maps being `id × (χ ∘ τ⁻¹)` and its inverse. -/
theorem isChart_prodEndChart {χ : MChart A} (hχ : (subPolyfold hA).IsChart χ) :
    (subPolyfold hA').IsChart (prodEndChart hab hend x₀ χ) := by
  refine isChart_of_forall_compatible _ fun p hp => ?_
  set y := endProj A x₀ p
  obtain ⟨ψ, hψ, hyψ⟩ := PX.exists_isChart_mem_source y.1
  set d := hA.data y.2
  refine ⟨prodEndChart hab hend x₀ (subChart d hψ y),
    isChart_prodEndChart_subChart hA' hab hend x₀ d hψ y,
    (mem_prodEndChart_source hab hend x₀).2
      ⟨hp.1, d.mem_shrink ψ y.2 (hA.mem_data_V y.2) hyψ⟩, ?_⟩
  exact MChart.Compatible.transport _ _ _
    ((MChart.compatible_self _).prod (IsChart.compatible _ hχ (subPolyfold_isChart hA d hψ y)))

include hA in
theorem isChart_cornerEndChart {χ : MChart A} (hχ : (subPolyfold hA).IsChart χ)
    (hc : χ.IsCornerChart) : (subPolyfold hA').IsChart (cornerEndChart hab hend x₀ hc) :=
  have := finiteDimensional_prodEndChart hab hend x₀ hc
  MChart.compDiffeo_isChart (isChart_prodEndChart hA hA' hab hend x₀ hχ) _ _ _

end ProdChart

/-! ### Corner coordinates on the end and the `ProductEnd` -/

section CornerCoordsEnd

open MPolyfold

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  [ParacompactSpace ((Fin 1 → ℝ) × X)] {A : Set X} [ParacompactSpace A]
  {hA : PX.IsSubMPolyfold A} {A' : Set ((Fin 1 → ℝ) × X)} [ParacompactSpace A']
  (hA' : ((rnPolyfold 1).prod PX).IsSubMPolyfold A') {a b : ℝ} (hab : a < b)
  (hend : ∀ z : (Fin 1 → ℝ) × X, z.1 0 ∈ Ioo a b → (z ∈ A' ↔ z.2 ∈ A)) (x₀ : A) {k : ℕ}

namespace MPolyfold.CornerCoords

/-- **Corner coordinates on the end** `(a, b) × A` of `A'` (proof of 2021 Theorem 6.7.1, p. 278):
from corner coordinates `κ = (χ, s, Ψ, c, W)` of dimension `k` on `A`, the corner coordinates
`(t, x) ↦ (t − a, Ψ χ(x) + c)` of dimension `k + 1` on `A'`, on the piece `(a, b) × s`, with
`W' = {y | y₀ ∈ (0, b − a), (y₁, …, y_k) ∈ W}`. -/
def prodRn (κ : CornerCoords (subPolyfold hA) k) : CornerCoords (subPolyfold hA') (k + 1) where
  χ := cornerEndChart hab hend x₀ κ.isCornerChart
  isChart := isChart_cornerEndChart hA hA' hab hend x₀ κ.isChart κ.isCornerChart
  isCornerChart := isCornerChart_cornerEndChart hab hend x₀ κ.isCornerChart
  s := (endPH hab hend x₀).source ∩ endPH hab hend x₀ ⁻¹' (univ ×ˢ κ.s)
  isOpen_s := (endPH hab hend x₀).isOpen_inter_preimage (isOpen_univ.prod κ.isOpen_s)
  s_subset _ hp := (mem_prodEndChart_source hab hend x₀).2 ⟨hp.1, κ.s_subset hp.2.2⟩
  Ψ := ((ContinuousLinearEquiv.funUnique (Fin 1) ℝ ℝ).prodCongr κ.Ψ).trans
    (Fin.consEquivL ℝ fun _ : Fin (k + 1) => ℝ)
  c := Fin.cons (-a) κ.c
  W := {y | y 0 ∈ Ioo 0 (b - a) ∧ Fin.tail y ∈ κ.W}
  isOpen_W := (isOpen_Ioo.preimage (continuous_apply 0)).inter
    (κ.isOpen_W.preimage (continuous_pi fun i => continuous_apply i.succ))
  image_s := by
    have key : ∀ p : A', ((ContinuousLinearEquiv.funUnique (Fin 1) ℝ ℝ).prodCongr κ.Ψ).trans
        (Fin.consEquivL ℝ fun _ : Fin (k + 1) => ℝ) (cornerEndChart hab hend x₀ κ.isCornerChart p) +
          Fin.cons (-a) κ.c = Fin.cons (p.1.1 0 - a) (κ.coord (endProj A x₀ p)) := fun p => by
      funext i
      refine Fin.cases ?_ (fun j => rfl) i
      exact (sub_eq_add_neg _ _).symm
    rw [image_image]
    refine (image_congr fun p _ => key p).trans ?_
    ext y
    constructor
    · rintro ⟨p, hp, rfl⟩
      have ht : p.1.1 0 - a ∈ Ioo 0 (b - a) := ⟨by linarith [hp.1.1], by linarith [hp.1.2]⟩
      refine ⟨⟨ht, κ.coord_mem_W hp.2.2⟩, fun i => Fin.cases ht.1.le ?_ i⟩
      exact fun j => κ.coord_nonneg hp.2.2 j
    · rintro ⟨⟨hy0, hyW⟩, hy⟩
      obtain ⟨x, hx, hxy⟩ := κ.exists_coord_eq hyW fun i => hy i.succ
      have ht : y 0 + a ∈ Ioo a b := ⟨by linarith [hy0.1], by linarith [hy0.2]⟩
      set p : A' := ⟨((fun _ => y 0 + a), x.1), (hend _ ht).2 x.2⟩
      have hpx : endProj A x₀ p = x := Subtype.ext (endProj_val x₀ x.2)
      refine ⟨p, ⟨ht, mem_univ _, ?_⟩, ?_⟩
      · change endProj A x₀ p ∈ κ.s
        rw [hpx]; exact hx
      · change Fin.cons (p.1.1 0 - a) (κ.coord (endProj A x₀ p)) = y
        rw [hpx, hxy]
        change Fin.cons (y 0 + a - a) (Fin.tail y) = y
        rw [add_sub_cancel_right, Fin.cons_self_tail]

variable (κ : CornerCoords (subPolyfold hA) k)

lemma prodRn_s : (κ.prodRn hA' hab hend x₀).s =
    (endPH hab hend x₀).source ∩ endPH hab hend x₀ ⁻¹' (univ ×ˢ κ.s) := rfl

lemma mem_prodRn_s {p : A'} :
    p ∈ (κ.prodRn hA' hab hend x₀).s ↔ p.1.1 0 ∈ Ioo a b ∧ endProj A x₀ p ∈ κ.s :=
  ⟨fun hp => ⟨hp.1, hp.2.2⟩, fun hp => ⟨hp.1, mem_univ _, hp.2⟩⟩

/-- The coordinates of `CornerCoords.prodRn`: `(t, x) ↦ (t − a, κ(x))`. -/
theorem prodRn_coord (p : A') :
    (κ.prodRn hA' hab hend x₀).coord p = Fin.cons (p.1.1 0 - a) (κ.coord (endProj A x₀ p)) := by
  funext i
  refine Fin.cases ?_ (fun j => rfl) i
  exact (sub_eq_add_neg _ _).symm

end MPolyfold.CornerCoords

open MPolyfold.CornerCoords in
/-- **The product charts of the end are the charts of `CornerCoords.prodRn`**: the Mathlib chart
`p ↦ (t − a, κ(x))` (`endChart` of `endPH`) agrees on its domain with the chart of the corner
coordinates `κ.prodRn`. -/
theorem endChart_eqOnSource (κ : CornerCoords (subPolyfold hA) k) :
    endChart (endPH hab hend x₀) a b κ.toQuadrantChart ≈
      (κ.prodRn hA' hab hend x₀).toQuadrantChart := by
  have hsrc : (endChart (endPH hab hend x₀) a b κ.toQuadrantChart).source =
      (κ.prodRn hA' hab hend x₀).s := by
    ext p
    simp only [endChart, OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.prod_source,
      OpenPartialHomeomorph.refl_source, mem_inter_iff, mem_preimage, mem_prod, mem_univ,
      true_and, consQuad_source, OpenPartialHomeomorph.trans_apply,
      OpenPartialHomeomorph.prod_apply, OpenPartialHomeomorph.refl_apply, id, and_true,
      toQuadrantChart_source, mem_prodRn_s, endPH_apply, endPH_source, mem_ofPred_eq]
    tauto
  refine ⟨hsrc, fun p hp => ?_⟩
  rw [hsrc, mem_prodRn_s] at hp
  apply Subtype.ext
  simp only [endChart, OpenPartialHomeomorph.trans_apply, OpenPartialHomeomorph.prod_apply,
    OpenPartialHomeomorph.refl_apply, id, endPH_apply]
  rw [consQuad_apply hp.1.1]
  change consE (p.1.1 0 - a) ((𝓠 k) (κ.toQuadrantChart (endProj A x₀ p))) =
    (𝓠 (k + 1)) ((κ.prodRn hA' hab hend x₀).toQuadrantChart p)
  rw [toQuadrantChart_apply, toQuadrantChart_apply,
    quadrant_right_inv fun i => κ.coord_nonneg hp.2 i,
    quadrant_right_inv fun i => (κ.prodRn hA' hab hend x₀).coord_nonneg
      ((mem_prodRn_s hA' hab hend x₀ κ).2 hp) i, prodRn_coord]
  rfl

variable (hcs : (subPolyfold hA).HasCornerStructureOfDim k)
  (hcs' : (subPolyfold hA').HasCornerStructureOfDim (k + 1))
  [instA : ChartedSpace (EuclideanQuadrant k) A]
  (hchA : instA = (subPolyfold hA).cornerChartedSpace hcs)
  [instA' : ChartedSpace (EuclideanQuadrant (k + 1)) A']
  (hchA' : instA' = (subPolyfold hA').cornerChartedSpace hcs')

/-- **The end `(a, b) × A` of `A'` as a `ProductEnd`** (proof of 2021 Theorem 6.7.1, p. 278;
preprint Theorem 6.43): for sub-M-polyfolds `A ⊆ X` and `A' ⊆ ℝ¹ × X` with `A' = (a, b) × A` over
`(a, b)` and corner structures of dimensions `k` and `k + 1`, the identification `endPH` with the
charted spaces `cornerChartedSpace`: its product charts are the charts of the corner coordinates
`CornerCoords.prodRn` (`endChart_eqOnSource`), hence in the maximal atlas. The point `x₀ ∈ A`
only fixes junk values; for `A = ∅` the end is empty (`not_mem_Ioo_of_isEmpty`). -/
def productEndOfSub : ProductEnd k A A' a b where
  φ := endPH hab hend x₀
  target_eq := rfl
  chart_mem x := by
    have := isManifold_of_eq hcs' hchA'
    rw [chartAt_eq_of_eq hcs hchA x]
    exact StructureGroupoid.mem_maximalAtlas_of_eqOnSource (endChart_eqOnSource hA' hab hend x₀ _)
      (mem_maximalAtlas_of_eq hcs' hchA' _)

@[simp] lemma productEndOfSub_φ :
    (productEndOfSub hA' hab hend x₀ hcs hcs' hchA hchA').φ = endPH hab hend x₀ := rfl

end CornerCoordsEnd

/-! ### The ends of the solution sets -/

section SolutionEnd

open MPolyfold

universe v

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle PX P}
  [ParacompactSpace ((Fin 1 → ℝ) × X)]
  [ParacompactSpace (pullbackSpace P (Prod.snd : (Fin 1 → ℝ) × X → X))]
  {g : X → Y} {G : (Fin 1 → ℝ) × X → pullbackSpace P (Prod.snd : (Fin 1 → ℝ) × X → X)}
  {V : Set X} {V' : Set ((Fin 1 → ℝ) × X)} {a b : ℝ}

omit [TopologicalSpace X] [T2Space X] [ParacompactSpace X] [TopologicalSpace Y] [T2Space Y]
  [ParacompactSpace Y] [∀ x, Module ℝ (P ⁻¹' {x})] [ParacompactSpace ((Fin 1 → ℝ) × X)]
  [ParacompactSpace (pullbackSpace P (Prod.snd : (Fin 1 → ℝ) × X → X))] in
/-- **Over `(a, b)` the part `S_G ∩ V'` is `(a, b) × (S_g ∩ V)`** when the slices of `G` over
`(a, b)` are `g` and `V'` is `ℝ¹ × V` on the zeros over `(a, b)` (`hVend`). -/
theorem solutionSet_end_iff (hG : IsSection (pullbackProj P Prod.snd) G)
    (hslice : ∀ t : Fin 1 → ℝ, t 0 ∈ Ioo a b → pullbackSlice G t = g)
    (hVend : ∀ z ∈ solutionSet (pullbackProj P Prod.snd) G, z.1 0 ∈ Ioo a b → (z ∈ V' ↔ z.2 ∈ V))
    (z : (Fin 1 → ℝ) × X) (hz : z.1 0 ∈ Ioo a b) :
    z ∈ solutionSet (pullbackProj P Prod.snd) G ∩ V' ↔ z.2 ∈ solutionSet P g ∩ V := by
  have h := Set.ext_iff.1 (solutionSet_inter_fst_preimage_eq_prod hG
    (A := {t : Fin 1 → ℝ | t 0 ∈ Ioo a b}) hslice) z
  simp only [mem_inter_iff, mem_preimage, mem_prod, mem_ofPred_eq] at h
  have hS : z ∈ solutionSet (pullbackProj P Prod.snd) G ↔ z.2 ∈ solutionSet P g :=
    ⟨fun h1 => (h.1 ⟨h1, hz⟩).2, fun h2 => (h.2 ⟨hz, h2⟩).1⟩
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨hS.1 h1, (hVend z h1 hz).1 h2⟩
  · rintro ⟨h1, h2⟩; exact ⟨hS.2 h1, (hVend z (hS.2 h1) hz).2 h2⟩

variable (hX : PX.IsTame) (hX' : ((rnPolyfold 1).prod PX).IsTame)
  (hft : B.IsScFredholmSectionTame g)
  (hftG : (B.pullback (MPolyfold.isScSmoothMap_snd (rnPolyfold 1) PX)).IsScFredholmSectionTame G)
  (hV : IsOpen V) (hV' : IsOpen V')
  (hgp : ∀ x ∈ V, IsZeroAt P g x → B.IsGeneralPositionGerm g x)
  (hgp' : ∀ z ∈ V', IsZeroAt (pullbackProj P Prod.snd) G z →
    (B.pullback (MPolyfold.isScSmoothMap_snd (rnPolyfold 1) PX)).IsGeneralPositionGerm G z)
  {k : ℕ} (hidx : ∀ y ∈ V, IsZeroAt P g y → B.IsLinOfIndex g y k)
  (hidx' : ∀ z ∈ V', IsZeroAt (pullbackProj P Prod.snd) G z →
    (B.pullback (MPolyfold.isScSmoothMap_snd (rnPolyfold 1) PX)).IsLinOfIndex G z (k + 1 : ℕ))

/-- **The end `(a, b) × (S_g ∩ V)` of `S_G ∩ V'` as a `ProductEnd`** (proof of 2021 Theorem 6.7.1,
p. 278; preprint Theorem 6.43): for a section `G` of `π*P → ℝ¹ × X` whose slices over `(a, b)`
are `g`, with the charted spaces `solChartedSpaceOpen` of `S_g ∩ V` (dimension `k`) and of
`S_G ∩ V'` (dimension `k + 1`), those of `theorem_6_6_18_oriented_open`. -/
def solProductEnd (hab : a < b)
    (hslice : ∀ t : Fin 1 → ℝ, t 0 ∈ Ioo a b → pullbackSlice G t = g)
    (hVend : ∀ z ∈ solutionSet (pullbackProj P Prod.snd) G, z.1 0 ∈ Ioo a b → (z ∈ V' ↔ z.2 ∈ V))
    (x₀ : ↥(solutionSet P g ∩ V)) :
    letI := solChartedSpaceOpen hX hft hV hgp hidx
    letI := solChartedSpaceOpen hX' hftG hV' hgp' hidx'
    ProductEnd k ↥(solutionSet P g ∩ V) ↥(solutionSet (pullbackProj P Prod.snd) G ∩ V') a b :=
  letI := solChartedSpaceOpen hX hft hV hgp hidx
  letI := solChartedSpaceOpen hX' hftG hV' hgp' hidx'
  letI := PX.paracompactSpace_subtype (solutionSet P g ∩ V)
  letI := ((rnPolyfold 1).prod PX).paracompactSpace_subtype
    (solutionSet (pullbackProj P Prod.snd) G ∩ V')
  productEndOfSub (isSubmanifoldOfDim_inter_open hftG hV' hgp' hidx').1.isSubMPolyfold hab
    (solutionSet_end_iff hftG.isScSmooth.1 hslice hVend) x₀
    ((isSubmanifoldOfDim_inter_open hft hV hgp hidx).hasCornerStructureOfDim_of_tame hX
      (isGoodPositionAt_inter_open hX hft hV hgp))
    ((isSubmanifoldOfDim_inter_open hftG hV' hgp' hidx').hasCornerStructureOfDim_of_tame hX'
      (isGoodPositionAt_inter_open hX' hftG hV' hgp')) rfl rfl

/-- The identification of `solProductEnd`: `z ↦ (t, x)`. -/
theorem solProductEnd_φ_apply (hab : a < b)
    (hslice : ∀ t : Fin 1 → ℝ, t 0 ∈ Ioo a b → pullbackSlice G t = g)
    (hVend : ∀ z ∈ solutionSet (pullbackProj P Prod.snd) G, z.1 0 ∈ Ioo a b → (z ∈ V' ↔ z.2 ∈ V))
    (x₀ : ↥(solutionSet P g ∩ V)) (z : ↥(solutionSet (pullbackProj P Prod.snd) G ∩ V')) :
    letI := solChartedSpaceOpen hX hft hV hgp hidx
    letI := solChartedSpaceOpen hX' hftG hV' hgp' hidx'
    ((solProductEnd hX hX' hft hftG hV hV' hgp hgp' hidx hidx' hab hslice hVend x₀).φ z).1 =
      z.1.1 0 := rfl

theorem solProductEnd_φ_apply_snd (hab : a < b)
    (hslice : ∀ t : Fin 1 → ℝ, t 0 ∈ Ioo a b → pullbackSlice G t = g)
    (hVend : ∀ z ∈ solutionSet (pullbackProj P Prod.snd) G, z.1 0 ∈ Ioo a b → (z ∈ V' ↔ z.2 ∈ V))
    (x₀ : ↥(solutionSet P g ∩ V)) (z : ↥(solutionSet (pullbackProj P Prod.snd) G ∩ V'))
    (hz : z.1.1 0 ∈ Ioo a b) :
    letI := solChartedSpaceOpen hX hft hV hgp hidx
    letI := solChartedSpaceOpen hX' hftG hV' hgp' hidx'
    ((solProductEnd hX hX' hft hftG hV hV' hgp hgp' hidx hidx' hab hslice hVend x₀).φ z).2.1 =
      z.1.2 :=
  endProj_val_of_mem (solutionSet_end_iff hftG.isScSmooth.1 hslice hVend) x₀ hz

theorem solProductEnd_φ_source (hab : a < b)
    (hslice : ∀ t : Fin 1 → ℝ, t 0 ∈ Ioo a b → pullbackSlice G t = g)
    (hVend : ∀ z ∈ solutionSet (pullbackProj P Prod.snd) G, z.1 0 ∈ Ioo a b → (z ∈ V' ↔ z.2 ∈ V))
    (x₀ : ↥(solutionSet P g ∩ V)) :
    letI := solChartedSpaceOpen hX hft hV hgp hidx
    letI := solChartedSpaceOpen hX' hftG hV' hgp' hidx'
    (solProductEnd hX hX' hft hftG hV hV' hgp hgp' hidx hidx' hab hslice hVend x₀).φ.source =
      {z | z.1.1 0 ∈ Ioo a b} := rfl

end SolutionEnd

/-! ### The index on the ends -/

section IndexEnd

universe v

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle PX P}
  [ParacompactSpace ((Fin 1 → ℝ) × X)]
  [ParacompactSpace (pullbackSpace P (Prod.snd : (Fin 1 → ℝ) × X → X))]
  {g : X → Y} {G : (Fin 1 → ℝ) × X → pullbackSpace P (Prod.snd : (Fin 1 → ℝ) × X → X)}
  {V : Set X} {V' : Set ((Fin 1 → ℝ) × X)} {a b : ℝ}

/-- **The index on the end** (proof of 2021 Theorem 6.7.1, p. 278: the index-`(k+1)` part of
`S_F` ends in the index-`k` parts of `S_{f+sᵢ}`): for an sc-Fredholm section `G` of `π*P → ℝ¹ × X`
(tame germ data) whose slice at `t` is the sc-Fredholm section `g`, and a zero `x` of `g` at which
`G` is in general position, `G'(t, x)` has index `k + 1` exactly when `g'(x)` has index `k`.
One direction is the slice relation `isLinOfIndex_pullbackSlice_of_isLinOfIndex`
(`fredholmIndex_eq_of_param`, `linIndex_snd`); the other adds that `G'(t, x)` has an index
(`theorem_3_6_8_index_locally_constant`) and that it is unique (`IsLinOfIndex.unique`). -/
theorem isLinOfIndex_end_iff
    (hftG : (B.pullback (MPolyfold.isScSmoothMap_snd (rnPolyfold 1) PX)).IsScFredholmSectionTame G)
    (hft : B.IsScFredholmSection g) {t : Fin 1 → ℝ} (hslice : pullbackSlice G t = g) {x : X}
    (hx : IsZeroAt P g x)
    (hgp : (B.pullback (MPolyfold.isScSmoothMap_snd (rnPolyfold 1) PX)).IsGeneralPositionGerm G
      (t, x)) {k : ℤ} :
    (B.pullback (MPolyfold.isScSmoothMap_snd (rnPolyfold 1) PX)).IsLinOfIndex G (t, x) (k + 1) ↔
      B.IsLinOfIndex g x k := by
  subst hslice
  have hz : IsZeroAt (pullbackProj P Prod.snd) G (t, x) :=
    (isZeroAt_pullback_iff_pullbackSlice hftG.isScSmooth.1 t x).2 hx
  have hsl : ∀ {i : ℤ}, (B.pullback (MPolyfold.isScSmoothMap_snd (rnPolyfold 1) PX)).IsLinOfIndex
      G (t, x) i → B.IsLinOfIndex (pullbackSlice G t) x (i - 1) := fun hi => by
    have := StrongBundle.isLinOfIndex_pullbackSlice_of_isLinOfIndex hftG.toIsScFredholmSection hft
      hx hi
    rwa [Nat.cast_one] at this
  refine ⟨fun h => by simpa using hsl h, fun h => ?_⟩
  obtain ⟨Vx, d, -, hzV, hind⟩ := theorem_3_6_8_index_locally_constant hftG
    (hgp.isGoodPositionGermTame hftG hz) hz
  have hd := (hind _ hzV hz).isLinOfIndex
  have := StrongBundle.IsLinOfIndex.unique hft hx (hsl hd) h
  rwa [show (k + 1 : ℤ) = d by omega]

omit [TopologicalSpace X] [T2Space X] [ParacompactSpace X] [TopologicalSpace Y] [T2Space Y]
  [ParacompactSpace Y] [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})]
  [ParacompactSpace ((Fin 1 → ℝ) × X)]
  [ParacompactSpace (pullbackSpace P (Prod.snd : (Fin 1 → ℝ) × X → X))] in
/-- An open set cutting out the index part, pointwise: from `S ∩ V = {x ∈ S | Q x}`. -/
theorem mem_iff_of_inter_eq {Z : Type*} {S U : Set Z} {Q : Z → Prop}
    (h : S ∩ U = {x ∈ S | Q x}) {x : Z} (hx : x ∈ S) : x ∈ U ↔ Q x := by
  have := Set.ext_iff.1 h x
  simp only [mem_inter_iff, mem_ofPred_eq] at this
  tauto

/-- **The index parts on the end**: if `V'` cuts out the index-`(k+1)` part of `S_G` over `(a, b)`
and `V` the index-`k` part of `S_g`, then `V'` is `ℝ¹ × V` on the zeros of `G` over `(a, b)` (the
hypothesis `hVend` of `solProductEnd`), by `isLinOfIndex_end_iff`. -/
theorem index_end_hVend
    (hftG : (B.pullback (MPolyfold.isScSmoothMap_snd (rnPolyfold 1) PX)).IsScFredholmSectionTame G)
    (hft : B.IsScFredholmSection g)
    (hslice : ∀ t : Fin 1 → ℝ, t 0 ∈ Ioo a b → pullbackSlice G t = g)
    (hgp : ∀ z, IsZeroAt (pullbackProj P Prod.snd) G z →
      (B.pullback (MPolyfold.isScSmoothMap_snd (rnPolyfold 1) PX)).IsGeneralPositionGerm G z)
    {k : ℕ} (hVk : ∀ x ∈ solutionSet P g, x ∈ V ↔ B.IsLinOfIndex g x k)
    (hV'k : ∀ z ∈ solutionSet (pullbackProj P Prod.snd) G, z.1 0 ∈ Ioo a b →
      (z ∈ V' ↔ (B.pullback (MPolyfold.isScSmoothMap_snd (rnPolyfold 1) PX)).IsLinOfIndex G z
        (k + 1 : ℕ))) :
    ∀ z ∈ solutionSet (pullbackProj P Prod.snd) G, z.1 0 ∈ Ioo a b → (z ∈ V' ↔ z.2 ∈ V) := by
  rintro ⟨t, x⟩ hz ht
  have hx : IsZeroAt P g x := by
    have := (isZeroAt_pullback_iff_pullbackSlice hftG.isScSmooth.1 t x).1 hz
    rwa [hslice t ht] at this
  rw [hV'k _ hz ht, hVk x hx, Nat.cast_add, Nat.cast_one]
  exact isLinOfIndex_end_iff hftG hft (hslice t ht) hx (hgp _ hz)

end IndexEnd

/-! ### The two ends of the cobordism -/

section CobordismEnds

universe v

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle PX P}
  [ParacompactSpace ((Fin 1 → ℝ) × X)]
  [ParacompactSpace (pullbackSpace P (Prod.snd : (Fin 1 → ℝ) × X → X))]
  {f : X → Y} {hf : IsSection P f} {σ₀ σ₁ : X → Y}
  {Ŝ : (Fin 1 → ℝ) × X → pullbackSpace P (Prod.snd : (Fin 1 → ℝ) × X → X)}
  {V : Set X} {V' : Set ((Fin 1 → ℝ) × X)} {a b : ℝ}

namespace StrongBundle.IsCobordismData

/-- `F = f̃ + Ŝ` is an sc-Fredholm section of `π*P` with tame germ data (Theorem 3.1.18 and
`IsScFredholmSectionTame.param`). -/
theorem isScFredholmSectionTame_homotopySection (hC : B.IsCobordismData f hf σ₀ σ₁ Ŝ)
    (hft : B.IsScFredholmSectionTame f) :
    (B.pullback (MPolyfold.isScSmoothMap_snd (rnPolyfold 1) PX)).IsScFredholmSectionTame
      (homotopySection f hf Ŝ) :=
  theorem_3_1_18_tame hft.param hC.isScPlusSection

omit [ParacompactSpace ((Fin 1 → ℝ) × X)]
  [ParacompactSpace (pullbackSpace P (Prod.snd : (Fin 1 → ℝ) × X → X))] in
theorem isScFredholmSectionTame_left (hC : B.IsCobordismData f hf σ₀ σ₁ Ŝ)
    (hft : B.IsScFredholmSectionTame f) : B.IsScFredholmSectionTame (sectionAdd P f σ₀) :=
  theorem_3_1_18_tame hft hC.isScPlusSection_left

omit [ParacompactSpace ((Fin 1 → ℝ) × X)]
  [ParacompactSpace (pullbackSpace P (Prod.snd : (Fin 1 → ℝ) × X → X))] in
theorem isScFredholmSectionTame_right (hC : B.IsCobordismData f hf σ₀ σ₁ Ŝ)
    (hft : B.IsScFredholmSectionTame f) : B.IsScFredholmSectionTame (sectionAdd P f σ₁) :=
  theorem_3_1_18_tame hft hC.isScPlusSection_right

omit [ParacompactSpace ((Fin 1 → ℝ) × X)]
  [ParacompactSpace (pullbackSpace P (Prod.snd : (Fin 1 → ℝ) × X → X))] in
theorem slice_left_Ioo (hC : B.IsCobordismData f hf σ₀ σ₁ Ŝ) (hb : b ≤ 1 / 8) :
    ∀ t : Fin 1 → ℝ, t 0 ∈ Ioo a b → pullbackSlice (homotopySection f hf Ŝ) t = sectionAdd P f σ₀ :=
  fun _ ht => hC.pullbackSlice_le (ht.2.le.trans hb)

omit [ParacompactSpace ((Fin 1 → ℝ) × X)]
  [ParacompactSpace (pullbackSpace P (Prod.snd : (Fin 1 → ℝ) × X → X))] in
theorem slice_right_Ioo (hC : B.IsCobordismData f hf σ₀ σ₁ Ŝ) (ha : 7 / 8 ≤ a) :
    ∀ t : Fin 1 → ℝ, t 0 ∈ Ioo a b → pullbackSlice (homotopySection f hf Ŝ) t = sectionAdd P f σ₁ :=
  fun _ ht => hC.pullbackSlice_ge (ha.trans ht.1.le)

/-- **The index on the left end** (proof of 2021 Theorem 6.7.1, p. 278): at a zero `x` of
`f + σ₀` and `t ≤ 1/8`, `F'(t, x)` has index `k + 1` exactly when `(f + σ₀)'(x)` has index `k`. -/
theorem isLinOfIndex_left_iff (hC : B.IsCobordismData f hf σ₀ σ₁ Ŝ)
    (hft : B.IsScFredholmSectionTame f) {t : Fin 1 → ℝ} (ht : t 0 ≤ 1 / 8) {x : X}
    (hx : IsZeroAt P (sectionAdd P f σ₀) x) {k : ℤ} :
    (B.pullback (MPolyfold.isScSmoothMap_snd (rnPolyfold 1) PX)).IsLinOfIndex
        (homotopySection f hf Ŝ) (t, x) (k + 1) ↔ B.IsLinOfIndex (sectionAdd P f σ₀) x k :=
  isLinOfIndex_end_iff (hC.isScFredholmSectionTame_homotopySection hft)
    (hC.isScFredholmSectionTame_left hft).toIsScFredholmSection (hC.pullbackSlice_le ht) hx
    (hC.gp _ ((isZeroAt_pullback_iff_pullbackSlice
      (hC.isScFredholmSectionTame_homotopySection hft).isScSmooth.1 t x).2
        (by rw [hC.pullbackSlice_le ht]; exact hx)))

/-- **The index on the right end**: at a zero `x` of `f + σ₁` and `t ≥ 7/8`, `F'(t, x)` has index
`k + 1` exactly when `(f + σ₁)'(x)` has index `k`. -/
theorem isLinOfIndex_right_iff (hC : B.IsCobordismData f hf σ₀ σ₁ Ŝ)
    (hft : B.IsScFredholmSectionTame f) {t : Fin 1 → ℝ} (ht : 7 / 8 ≤ t 0) {x : X}
    (hx : IsZeroAt P (sectionAdd P f σ₁) x) {k : ℤ} :
    (B.pullback (MPolyfold.isScSmoothMap_snd (rnPolyfold 1) PX)).IsLinOfIndex
        (homotopySection f hf Ŝ) (t, x) (k + 1) ↔ B.IsLinOfIndex (sectionAdd P f σ₁) x k :=
  isLinOfIndex_end_iff (hC.isScFredholmSectionTame_homotopySection hft)
    (hC.isScFredholmSectionTame_right hft).toIsScFredholmSection (hC.pullbackSlice_ge ht) hx
    (hC.gp _ ((isZeroAt_pullback_iff_pullbackSlice
      (hC.isScFredholmSectionTame_homotopySection hft).isScSmooth.1 t x).2
        (by rw [hC.pullbackSlice_ge ht]; exact hx)))

/-- `hVend` for the index parts on the left end (`index_end_hVend`). -/
theorem hVend_left (hC : B.IsCobordismData f hf σ₀ σ₁ Ŝ) (hft : B.IsScFredholmSectionTame f)
    (hb : b ≤ 1 / 8) {k : ℕ}
    (hVk : ∀ x ∈ solutionSet P (sectionAdd P f σ₀), x ∈ V ↔ B.IsLinOfIndex (sectionAdd P f σ₀) x k)
    (hV'k : ∀ z ∈ solutionSet (pullbackProj P Prod.snd) (homotopySection f hf Ŝ), z.1 0 ∈ Ioo a b →
      (z ∈ V' ↔ (B.pullback (MPolyfold.isScSmoothMap_snd (rnPolyfold 1) PX)).IsLinOfIndex
        (homotopySection f hf Ŝ) z (k + 1 : ℕ))) :
    ∀ z ∈ solutionSet (pullbackProj P Prod.snd) (homotopySection f hf Ŝ), z.1 0 ∈ Ioo a b →
      (z ∈ V' ↔ z.2 ∈ V) :=
  index_end_hVend (hC.isScFredholmSectionTame_homotopySection hft)
    (hC.isScFredholmSectionTame_left hft).toIsScFredholmSection (hC.slice_left_Ioo hb)
    (fun z hz => hC.gp z hz) hVk hV'k

/-- `hVend` for the index parts on the right end. -/
theorem hVend_right (hC : B.IsCobordismData f hf σ₀ σ₁ Ŝ) (hft : B.IsScFredholmSectionTame f)
    (ha : 7 / 8 ≤ a) {k : ℕ}
    (hVk : ∀ x ∈ solutionSet P (sectionAdd P f σ₁), x ∈ V ↔ B.IsLinOfIndex (sectionAdd P f σ₁) x k)
    (hV'k : ∀ z ∈ solutionSet (pullbackProj P Prod.snd) (homotopySection f hf Ŝ), z.1 0 ∈ Ioo a b →
      (z ∈ V' ↔ (B.pullback (MPolyfold.isScSmoothMap_snd (rnPolyfold 1) PX)).IsLinOfIndex
        (homotopySection f hf Ŝ) z (k + 1 : ℕ))) :
    ∀ z ∈ solutionSet (pullbackProj P Prod.snd) (homotopySection f hf Ŝ), z.1 0 ∈ Ioo a b →
      (z ∈ V' ↔ z.2 ∈ V) :=
  index_end_hVend (hC.isScFredholmSectionTame_homotopySection hft)
    (hC.isScFredholmSectionTame_right hft).toIsScFredholmSection (hC.slice_right_Ioo ha)
    (fun z hz => hC.gp z hz) hVk hV'k

variable (hX : PX.IsTame) (hft : B.IsScFredholmSectionTame f) (hV : IsOpen V) (hV' : IsOpen V')
  {k : ℕ}

/-- **The left end of `S_F ∩ V'`** (proof of 2021 Theorem 6.7.1, p. 278; preprint Theorem 6.43):
for `a < b ≤ 1/8`, the part of `S_F ∩ V'` over `(a, b)` is `(a, b) × (S_{f+σ₀} ∩ V)` as a
`ProductEnd`, with the charted spaces `solChartedSpaceOpen` of `theorem_6_6_18_oriented_open`
(`solProductEnd`). For the index parts, `hVend` is `hVend_left`. -/
def productEndLeft (hC : B.IsCobordismData f hf σ₀ σ₁ Ŝ)
    (hidx : ∀ y ∈ V, IsZeroAt P (sectionAdd P f σ₀) y → B.IsLinOfIndex (sectionAdd P f σ₀) y k)
    (hidx' : ∀ z ∈ V', IsZeroAt (pullbackProj P Prod.snd) (homotopySection f hf Ŝ) z →
      (B.pullback (MPolyfold.isScSmoothMap_snd (rnPolyfold 1) PX)).IsLinOfIndex
        (homotopySection f hf Ŝ) z (k + 1 : ℕ))
    (hab : a < b) (hb : b ≤ 1 / 8)
    (hVend : ∀ z ∈ solutionSet (pullbackProj P Prod.snd) (homotopySection f hf Ŝ),
      z.1 0 ∈ Ioo a b → (z ∈ V' ↔ z.2 ∈ V))
    (x₀ : ↥(solutionSet P (sectionAdd P f σ₀) ∩ V)) :
    letI := solChartedSpaceOpen hX (hC.isScFredholmSectionTame_left hft) hV
      (fun x _ hx => hC.gp_left x hx) hidx
    letI := solChartedSpaceOpen (prod_rn_isTame hX) (hC.isScFredholmSectionTame_homotopySection hft)
      hV' (fun z _ hz => hC.gp z hz) hidx'
    ProductEnd k ↥(solutionSet P (sectionAdd P f σ₀) ∩ V)
      ↥(solutionSet (pullbackProj P Prod.snd) (homotopySection f hf Ŝ) ∩ V') a b :=
  solProductEnd hX (prod_rn_isTame hX) _ _ hV hV' _ _ hidx hidx' hab (hC.slice_left_Ioo hb) hVend x₀

/-- **The right end of `S_F ∩ V'`**: for `7/8 ≤ a < b`, the part over `(a, b)` is
`(a, b) × (S_{f+σ₁} ∩ V)` as a `ProductEnd`. For the index parts, `hVend` is `hVend_right`. -/
def productEndRight (hC : B.IsCobordismData f hf σ₀ σ₁ Ŝ)
    (hidx : ∀ y ∈ V, IsZeroAt P (sectionAdd P f σ₁) y → B.IsLinOfIndex (sectionAdd P f σ₁) y k)
    (hidx' : ∀ z ∈ V', IsZeroAt (pullbackProj P Prod.snd) (homotopySection f hf Ŝ) z →
      (B.pullback (MPolyfold.isScSmoothMap_snd (rnPolyfold 1) PX)).IsLinOfIndex
        (homotopySection f hf Ŝ) z (k + 1 : ℕ))
    (hab : a < b) (ha : 7 / 8 ≤ a)
    (hVend : ∀ z ∈ solutionSet (pullbackProj P Prod.snd) (homotopySection f hf Ŝ),
      z.1 0 ∈ Ioo a b → (z ∈ V' ↔ z.2 ∈ V))
    (x₀ : ↥(solutionSet P (sectionAdd P f σ₁) ∩ V)) :
    letI := solChartedSpaceOpen hX (hC.isScFredholmSectionTame_right hft) hV
      (fun x _ hx => hC.gp_right x hx) hidx
    letI := solChartedSpaceOpen (prod_rn_isTame hX) (hC.isScFredholmSectionTame_homotopySection hft)
      hV' (fun z _ hz => hC.gp z hz) hidx'
    ProductEnd k ↥(solutionSet P (sectionAdd P f σ₁) ∩ V)
      ↥(solutionSet (pullbackProj P Prod.snd) (homotopySection f hf Ŝ) ∩ V') a b :=
  solProductEnd hX (prod_rn_isTame hX) _ _ hV hV' _ _ hidx hidx' hab (hC.slice_right_Ioo ha) hVend
    x₀

end StrongBundle.IsCobordismData

end CobordismEnds

/-! ### Pull-backs along the end projection, in coordinates -/

section TailPull

variable {k m : ℕ}

/-- **`tail^*η`**: the pull-back of an `m`-form `η` on `ℝ^k` along `y ↦ (y₁, …, y_k)`. -/
abbrev tailPull (η : EuclideanSpace ℝ (Fin k) [⋀^Fin m]→L[ℝ] ℝ) :
    EuclideanSpace ℝ (Fin (k + 1)) [⋀^Fin m]→L[ℝ] ℝ :=
  η.compContinuousLinearMap (tailCLM k)

theorem tailPull_apply (η : EuclideanSpace ℝ (Fin k) [⋀^Fin m]→L[ℝ] ℝ)
    (w : Fin m → EuclideanSpace ℝ (Fin (k + 1))) : tailPull η w = η (fun j => tailE (w j)) :=
  rfl

/-- **`d(h(t) · tail^*G) = h′(t) dt ∧ tail^*G`** in the top degree, in coordinates: if
`F = h(t + a) · tail^*G` near `y` (on a set `s` with unique derivatives mapped into `T` by the
projection), with `h` differentiable and `G` differentiable within `T`, then the coefficient of
`dF` is `h′` times the coefficient of `G` (the term `h · tail^*dG` is a `(k+1)`-form pulled back
from `ℝ^k`, so it vanishes). -/
theorem extDerivWithin_smul_tailPull_stdFrame {s : Set (EuclideanSpace ℝ (Fin (k + 1)))}
    {T : Set (EuclideanSpace ℝ (Fin k))}
    {F : EuclideanSpace ℝ (Fin (k + 1)) → EuclideanSpace ℝ (Fin (k + 1)) [⋀^Fin k]→L[ℝ] ℝ}
    {G : EuclideanSpace ℝ (Fin k) → EuclideanSpace ℝ (Fin k) [⋀^Fin k]→L[ℝ] ℝ}
    {h : ℝ → ℝ} {a : ℝ} {y : EuclideanSpace ℝ (Fin (k + 1))} (hy : y ∈ s)
    (hs : UniqueDiffWithinAt ℝ s y) (hsT : MapsTo tailE s T)
    (hF : ∀ z ∈ s, F z = h (z 0 + a) • tailPull (G (tailE z)))
    (hh : DifferentiableAt ℝ h (y 0 + a)) (hG : DifferentiableWithinAt ℝ G T (tailE y)) :
    extDerivWithin F s y (stdFrame (k + 1)) = deriv h (y 0 + a) * G (tailE y) (stdFrame k) := by
  set G' := fderivWithin ℝ G T (tailE y)
  set c' : EuclideanSpace ℝ (Fin (k + 1)) →L[ℝ] ℝ :=
    deriv h (y 0 + a) • EuclideanSpace.proj (0 : Fin (k + 1))
  have hc : HasFDerivAt (fun z : EuclideanSpace ℝ (Fin (k + 1)) => h (z 0 + a)) c' y := by
    have h1 : HasFDerivAt (fun z : EuclideanSpace ℝ (Fin (k + 1)) => z 0 + a)
        (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin (k + 1)) :
          EuclideanSpace ℝ (Fin (k + 1)) →L[ℝ] ℝ) y :=
      ((EuclideanSpace.proj (0 : Fin (k + 1)) :
        EuclideanSpace ℝ (Fin (k + 1)) →L[ℝ] ℝ).hasFDerivAt (x := y)).add_const a
    exact hh.hasDerivAt.comp_hasFDerivAt y h1
  set P := ContinuousAlternatingMap.compContinuousLinearMapCLM (ι := Fin k) (F := ℝ) (tailCLM k)
  have hf : HasFDerivWithinAt (fun z => tailPull (G (tailE z))) (P.comp (G'.comp (tailCLM k)))
      s y :=
    P.hasFDerivAt.comp_hasFDerivWithinAt y
      (hG.hasFDerivWithinAt.comp y (tailCLM k).hasFDerivWithinAt hsT)
  have hL : HasFDerivWithinAt (fun z => h (z 0 + a) • tailPull (G (tailE z))) _ s y :=
    hc.hasFDerivWithinAt.smul hf
  rw [extDerivWithin_congr' (ω₂ := fun z => h (z 0 + a) • tailPull (G (tailE z))) hF hy,
    extDerivWithin, hL.fderivWithin hs, ContinuousAlternatingMap.alternatizeUncurryFin_apply,
    Fin.sum_univ_succ]
  have hzero : ∀ i : Fin k, (h (y 0 + a) • (P.comp (G'.comp (tailCLM k))) +
      c'.smulRight (tailPull (G (tailE y))))
        (stdFrame (k + 1) i.succ) (Fin.removeNth i.succ (stdFrame (k + 1))) = 0 := fun i => by
    have hp : c' (stdFrame (k + 1) i.succ) = 0 := by
      simp only [c', smul_apply, smul_eq_mul]
      rw [show (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin (k + 1)))
        (stdFrame (k + 1) i.succ) = 0 from stdFrame_succ_apply_zero i, mul_zero]
    have hi0 : (i.succ).succAbove ⟨0, i.pos⟩ = 0 := by
      rw [Fin.succAbove_of_castSucc_lt _ _ (by simp [Fin.lt_def])]; rfl
    simp only [add_apply, smul_apply, ContinuousLinearMap.smulRight_apply, hp, zero_smul, add_zero,
      ContinuousAlternatingMap.smul_apply, ContinuousLinearMap.coe_comp, Function.comp_apply, P,
      ContinuousAlternatingMap.compContinuousLinearMapCLM_apply,
      ContinuousAlternatingMap.compContinuousLinearMap_apply]
    rw [ContinuousAlternatingMap.map_coord_zero _ ⟨0, i.pos⟩ (by
      simp only [Function.comp_apply, Fin.removeNth_apply, hi0, tailCLM_apply]
      exact tailE_stdFrame_zero), smul_zero]
  rw [Finset.sum_eq_zero fun i _ => by rw [hzero i, smul_zero], add_zero]
  have hp0 : c' (stdFrame (k + 1) 0) = deriv h (y 0 + a) := by
    simp only [c', smul_apply, smul_eq_mul]
    rw [show (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin (k + 1)))
      (stdFrame (k + 1) 0) = 1 from stdFrame_apply_zero_zero, mul_one]
  have hstd : (fun j => tailE (Fin.removeNth 0 (stdFrame (k + 1)) j)) = stdFrame k :=
    funext fun j => by rw [Fin.removeNth_zero]; exact tailE_stdFrame_succ j
  simp only [add_apply, smul_apply, ContinuousLinearMap.smulRight_apply, hp0,
    ContinuousAlternatingMap.smul_apply, ContinuousLinearMap.coe_comp, Function.comp_apply, P,
    tailCLM_apply, tailE_stdFrame_zero, map_zero, smul_zero, zero_add, Fin.val_zero, pow_zero,
    one_smul, smul_eq_mul, tailPull_apply, hstd]

end TailPull

/-! ### Forms pulled back along the end projection -/

section EndPullback

open ManifoldForm

variable {k : ℕ} {N : Type*} [TopologicalSpace N] [ChartedSpace (EuclideanQuadrant k) N]
  {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanQuadrant (k + 1)) M] {a b : ℝ}
  (E : ProductEnd k N M a b)

/-- **`Ω` reads as the pull-back of `ω` along the end projection** (the form `p₁^*ω` on the end
`(a, b) × S_i` of `S_F`, proof of 2021 Theorem 6.7.1, p. 278): in every product chart
`ê = E.chart (chartAt y₀)`, the expression of `Ω` at `y` is `tail^*` of the expression of `ω` in
`chartAt y₀` at `(y₁, …, y_k)`. -/
def ProductEnd.IsEndPullback {m : ℕ} (Ω : ManifoldForm (𝓠 (k + 1)) M m)
    (ω : ManifoldForm (𝓠 k) N m) : Prop :=
  ∀ y₀ : N, ∀ y ∈ ((E.chart (chartAt (EuclideanQuadrant k) y₀)).extend (𝓠 (k + 1))).target,
    chartForm (𝓠 (k + 1)) (E.chart (chartAt (EuclideanQuadrant k) y₀)) Ω y =
      tailPull (chartForm (𝓠 k) (chartAt (EuclideanQuadrant k) y₀) ω (tailE y))

/-- `IsEndPullback` holds for `0` and `0`; the forms of the cobordism argument satisfy it by
`isEndPullback_formsInftyRestrict_snd`. -/
theorem ProductEnd.isEndPullback_zero {m : ℕ} :
    E.IsEndPullback (0 : ManifoldForm (𝓠 (k + 1)) M m) (0 : ManifoldForm (𝓠 k) N m) :=
  fun _ _ _ => by ext v; rfl

/-- On the end, `f Ω` reads as `g(t) · tail^*ω` when `f = g ∘ t` there and `Ω` is a pull-back. -/
theorem ProductEnd.chartForm_smulFun_of_isEndPullback {m : ℕ} {Ω : ManifoldForm (𝓠 (k + 1)) M m}
    {ω : ManifoldForm (𝓠 k) N m} (hpull : E.IsEndPullback Ω ω) {f : M → ℝ} {g : ℝ → ℝ}
    (hf : ∀ p ∈ E.φ.source, f p = g (E.φ p).1) (y₀ : N) {y : EuclideanSpace ℝ (Fin (k + 1))}
    (hy : y ∈ ((E.chart (chartAt (EuclideanQuadrant k) y₀)).extend (𝓠 (k + 1))).target) :
    chartForm (𝓠 (k + 1)) (E.chart (chartAt (EuclideanQuadrant k) y₀)) (smulFun f Ω) y =
      g (y 0 + a) • tailPull (chartForm (𝓠 k) (chartAt (EuclideanQuadrant k) y₀) ω (tailE y)) := by
  obtain ⟨h1, h2⟩ := E.pt_mem hy
  rw [chartForm_smulFun, hpull y₀ y hy, E.chart_extend_symm hy,
    hf _ (E.mem_chart_source.1 h1).1, h2]

variable [IsManifold (𝓠 k) ∞ N] [IsManifold (𝓠 (k + 1)) ∞ M]

/-- **The product chart form of `d(g(t) Ω)` on the end** (the hypothesis `hprod` of
`ProductEnd.integral_end_fubini` with `h = g′`; proof of 2021 Theorem 6.7.1, p. 278: on the
ends, `d(gΩ) = g′(t) dt ∧ p₁^*ω`): if `Ω` is the pull-back of the `C¹` top-degree form `ω`
(`IsEndPullback`), `f = g ∘ t` on the end with `g` differentiable, and `f Ω` is `C¹`, then in the
product charts the coefficient of `d(f Ω)` is `g′(t)` times the coefficient of `ω`. -/
theorem ProductEnd.chartForm_extDeriv_smulFun_stdFrame {Ω : ManifoldForm (𝓠 (k + 1)) M k}
    {ω : ManifoldForm (𝓠 k) N k} (hω : ContMDiffForm (𝓠 k) 1 ω) (hpull : E.IsEndPullback Ω ω)
    {f : M → ℝ} {g : ℝ → ℝ} (hg : Differentiable ℝ g) (hf : ∀ p ∈ E.φ.source, f p = g (E.φ p).1)
    (hβ : ContMDiffForm (𝓠 (k + 1)) 1 (smulFun f Ω)) (y₀ : N) {y : EuclideanSpace ℝ (Fin (k + 1))}
    (hy : y ∈ ((E.chart (chartAt (EuclideanQuadrant k) y₀)).extend (𝓠 (k + 1))).target) :
    chartForm (𝓠 (k + 1)) (E.chart (chartAt (EuclideanQuadrant k) y₀)) (extDeriv (smulFun f Ω)) y
        (stdFrame (k + 1)) =
      deriv g (y 0 + a) * chartForm (𝓠 k) (chartAt (EuclideanQuadrant k) y₀) ω (tailE y)
        (stdFrame k) := by
  have hT : MapsTo tailE ((E.chart (chartAt (EuclideanQuadrant k) y₀)).extend (𝓠 (k + 1))).target
      ((chartAt (EuclideanQuadrant k) y₀).extend (𝓠 k)).target :=
    fun z hz => (E.mem_chart_extend_target.1 hz).2
  have hG : DifferentiableWithinAt ℝ (chartForm (𝓠 k) (chartAt (EuclideanQuadrant k) y₀) ω)
      ((chartAt (EuclideanQuadrant k) y₀).extend (𝓠 k)).target (tailE y) :=
    (hω.contDiffOn_chartForm (by simp) (IsManifold.chart_mem_maximalAtlas y₀)).differentiableOn
      one_ne_zero _ (hT hy)
  rw [chartForm_extDeriv_of_mem_target (E.chart_mem y₀) hβ hy]
  exact extDerivWithin_smul_tailPull_stdFrame hy (uniqueDiffOn_extend_target _ _ hy) hT
    (fun z hz => E.chartForm_smulFun_of_isEndPullback hpull hf y₀ hz) (hg _) hG

end EndPullback

/-! ### The forms `p₁^*ω` on the end (`IsEndPullback` for `formsAlong`) -/

section FormsEnd

universe v

open MPolyfold

/-- The image under a corner chart of an open subset of its source is relatively open in the
quadrant. -/
theorem relOpen_image_fdom {Y : Type*} [TopologicalSpace Y] {σ : MChart Y} (hc : σ.IsCornerChart)
    {s : Set Y} (hs : s ⊆ σ.source) (hso : IsOpen s) :
    IsRelOpenInQuadrant σ.model.E σ.model.C (σ '' s) := by
  obtain ⟨W, hW, hWs⟩ := σ.exists_isOpen_image_eq hs hso
  rw [hWs]
  exact hc.isRelOpenInQuadrant.inter_isOpen hW

namespace ManifoldForm

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M] [ChartedSpace H M] {m : ℕ}

omit [ChartedSpace H M] in
/-- Charts that agree on their common source have the same inverse on the extended target. -/
theorem extend_symm_eq_of_eqOnSource {e e' : OpenPartialHomeomorph M H} (h : e ≈ e') {y : E}
    (hy : y ∈ (e.extend I).target) : (e.extend I).symm y = (e'.extend I).symm y := by
  rw [OpenPartialHomeomorph.extend_target] at hy
  simp only [OpenPartialHomeomorph.extend_coe_symm, Function.comp_apply]
  exact h.symm'.eqOn (by rw [OpenPartialHomeomorph.symm_source]; exact hy.1)

omit [ChartedSpace H M] in
/-- The chart change derivative depends on the chart only up to `EqOnSource`. -/
theorem chartChangeDeriv_eq_of_eqOnSource {e e' : OpenPartialHomeomorph M H} (h : e ≈ e')
    (c : OpenPartialHomeomorph M H) {x : M} (hx : x ∈ e.source) :
    chartChangeDeriv I e c x = chartChangeDeriv I e' c x := by
  have hex : e.extend I x = e'.extend I x := by
    simp only [OpenPartialHomeomorph.extend_coe, Function.comp_apply, h.eqOn hx]
  have hz : e.extend I x ∈ (e.extend I).target :=
    (e.extend I).map_source (by rwa [e.extend_source])
  unfold chartChangeDeriv
  rw [← hex]
  refine Filter.EventuallyEq.fderivWithin_eq ?_ ?_
  · filter_upwards [e.extend_target_mem_nhdsWithin (I := I) hx] with z hz
    simp only [ModelWithCorners.extendCoordChange, PartialEquiv.coe_trans, Function.comp_apply,
      extend_symm_eq_of_eqOnSource h hz]
  · simp only [ModelWithCorners.extendCoordChange, PartialEquiv.coe_trans, Function.comp_apply,
      extend_symm_eq_of_eqOnSource h hz]

/-- **The expression of a form in a chart depends on the chart only up to `EqOnSource`.** -/
theorem chartForm_eq_of_eqOnSource {e e' : OpenPartialHomeomorph M H} (h : e ≈ e')
    (ω : ManifoldForm I M m) {y : E} (hy : y ∈ (e.extend I).target) :
    chartForm I e ω y = chartForm I e' ω y := by
  have hx : (e.extend I).symm y ∈ e.source := by
    rw [← e.extend_source (I := I)]; exact (e.extend I).map_target hy
  ext v
  rw [chartForm_apply, chartForm_apply, chartChangeDeriv_eq_of_eqOnSource h _ hx,
    extend_symm_eq_of_eqOnSource h hy]

end ManifoldForm

namespace MPolyfold

/-! #### Functions of the time are smooth -/

/-- **An sc-smooth function on a finite-dimensional corner M-polyfold is `C^∞`** on the Mathlib
manifold (`cornerChartedSpace`): in the corner coordinates `κ`, `u ∘ κ⁻¹ = (u ∘ χ⁻¹) ∘ aff` with
`u ∘ χ⁻¹` sc-smooth on a finite-dimensional sc-domain (`contDiffOn_of_finiteDim`). -/
theorem contMDiff_of_isScSmoothMap_real {M : Type*} [TopologicalSpace M] [T2Space M]
    [ParacompactSpace M] {Q : MPolyfold M} {n : ℕ} (hcs : Q.HasCornerStructureOfDim n)
    [inst : ChartedSpace (EuclideanQuadrant n) M] (hch : inst = Q.cornerChartedSpace hcs)
    {u : M → ℝ} (hu : Q.IsScSmoothMap realPolyfold u) : ContMDiff (𝓠 n) 𝓘(ℝ) ∞ u := by
  intro x
  set κ := hcs.coords x
  have hc : extChartAt (𝓠 n) x = κ.toQuadrantChart.extend (𝓠 n) := by
    rw [extChartAt, chartAt_eq_of_eq hcs hch x]
    rfl
  rw [contMDiffAt_iff]
  refine ⟨(hu.continuousOn.mono (subset_univ _)).continuousAt univ_mem, ?_⟩
  simp only [extChartAt_model_space_eq_id, PartialEquiv.refl_coe, Function.id_comp, hc]
  have := κ.isCornerChart.finiteDimensional
  have hso := TangentPre.isOpen_fdom hu κ.χ realChart
  have hU := relOpen_image_fdom κ.isCornerChart inter_subset_left hso
  have hsc : IsScSmooth (κ.χ '' TangentPre.fdom κ.χ u realChart) (realChart ∘ u ∘ κ.χ.symm) :=
    (TangentPre.isScSmoothRetractMap_coord hu κ.isChart isChart_realChart subset_rfl
      hso).comp_isScSmooth (ScRetraction.id hU) (image_id _)
  have hcd := contDiffOn_of_finiteDim hU.isScDomain hsc
  have haff : ContDiff ℝ ∞ κ.aff := by
    have : κ.aff = fun y => κ.lin y + κ.aff 0 := funext κ.aff_eq
    rw [this]; exact κ.lin.contDiff.add contDiff_const
  have hon : ContDiffOn ℝ ∞ (u ∘ (κ.toQuadrantChart.extend (𝓠 n)).symm)
      (κ.toQuadrantChart.extend (𝓠 n)).target := by
    refine (hcd.comp haff.contDiffOn fun y hy => ?_).congr fun y hy => ?_
    · obtain ⟨h1, h2⟩ := κ.symm_mem_and_aff_eq hy
      exact h2 ▸ ⟨_, ⟨κ.s_subset h1, mem_univ _⟩, rfl⟩
    · obtain ⟨h1, h2⟩ := κ.symm_mem_and_aff_eq hy
      change u _ = u (κ.χ.symm (κ.aff y))
      rw [h2, κ.χ.symm_apply_apply (κ.s_subset h1)]
  have hx : x ∈ κ.toQuadrantChart.source := hcs.mem_coords x
  have hmem := (κ.toQuadrantChart.extend (𝓠 n)).map_source
    (by rwa [κ.toQuadrantChart.extend_source])
  exact (hon _ hmem).mono_of_mem_nhdsWithin (κ.toQuadrantChart.extend_target_mem_nhdsWithin hx)

/-- **A function of the time `t` is `C^∞` on `A' ⊆ ℝ¹ × X`**: for `g : ℝ → ℝ` of class `C^∞`,
`p ↦ g(t(p))` on the Mathlib manifold `A'` (`cornerChartedSpace`), e.g. the cut-off `g(t)` of the
proof of 2021 Theorem 6.7.1, p. 278 (preprint Theorem 6.43). -/
theorem contMDiff_comp_time {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X]
    {PX : MPolyfold X} [ParacompactSpace ((Fin 1 → ℝ) × X)] {A' : Set ((Fin 1 → ℝ) × X)}
    [ParacompactSpace A'] {hA' : ((rnPolyfold 1).prod PX).IsSubMPolyfold A'} {n : ℕ}
    (hcs' : (subPolyfold hA').HasCornerStructureOfDim n)
    [inst : ChartedSpace (EuclideanQuadrant n) A']
    (hch : inst = (subPolyfold hA').cornerChartedSpace hcs') {g : ℝ → ℝ} (hg : ContDiff ℝ ∞ g) :
    ContMDiff (𝓠 n) 𝓘(ℝ) ∞ (fun p : A' => g (p.1.1 0)) :=
  contMDiff_of_isScSmoothMap_real hcs' hch
    (((isScSmoothMap_rn_real_of_contDiff (n := 1) (g := fun r => g (r 0))
      (hg.comp (contDiff_apply ℝ ℝ (0 : Fin 1)))).comp
      (MPolyfold.isScSmoothMap_fst (rnPolyfold 1) PX)).comp (subPolyfold_inclusion_isScSmooth hA'))

section TangentEnd

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  [ParacompactSpace ((Fin 1 → ℝ) × X)] {A : Set X} [ParacompactSpace A]
  {hA : PX.IsSubMPolyfold A} {A' : Set ((Fin 1 → ℝ) × X)} [ParacompactSpace A']
  (hA' : ((rnPolyfold 1).prod PX).IsSubMPolyfold A') {a b : ℝ} (hab : a < b)
  (hend : ∀ z : (Fin 1 → ℝ) × X, z.1 0 ∈ Ioo a b → (z ∈ A' ↔ z.2 ∈ A)) (x₀ : A) {k : ℕ}

/-- The vector `D(ψ ∘ G ∘ χ⁻¹)(χ(x)) v` of the tangent map of `G` in charts, at a point of `χ`. -/
theorem tangentChartMap_tangentMap_eq_scDeriv {Y Z : Type*} [TopologicalSpace Y] [T2Space Y]
    [ParacompactSpace Y] [TopologicalSpace Z] [T2Space Z] [ParacompactSpace Z]
    {P : MPolyfold Y} {B : MPolyfold Z} {G : Y → Z} (hG : P.IsScSmoothMap B G)
    {χ : MChart Y} (hχ : P.IsChart χ) (hc : χ.IsCornerChart) {ψ : MChart Z} (hψ : B.IsChart ψ)
    {α : P.TangentSpace} {x : P.Level 1} (hαx : α ∈ P.tangentFiber x)
    (hx : P.levelVal 1 x ∈ χ.source) (hGx : G (P.levelVal 1 x) ∈ ψ.source) :
    (tangentChartMap hψ (tangentMap hG α)).2 =
      scDeriv (χ '' TangentPre.fdom χ G ψ) (ψ ∘ G ∘ χ.symm) (tangentChartMap hχ α).1
        (tangentChartMap hχ α).2 := by
  have hα : α ∈ tangentChartSet χ := mem_tangentChartSet_of_mem_fiber hx hαx
  have hfα : G (P.levelVal 1 (P.tangentProj α)) ∈ ψ.source := by
    rw [tangentProj_eq_of_mem_fiber hαx]; exact hGx
  have hso := TangentPre.isOpen_fdom hG χ ψ
  have hU := relOpen_image_fdom hc inter_subset_left hso
  have hmem : tangentChartMap hχ α ∈ retractTangent χ.model.E χ.model.C
      (χ '' TangentPre.fdom χ G ψ) := by
    refine (TangentPre.mem_retractTangent_image_iff inter_subset_left hso ?_).2
      (tangentChartMap_mem hχ hα)
    rw [tangentChartMap_fst_of_mem_fiber hχ hx hαx, P.toBase_levelLift hχ hx (levelVal_mem x)]
    exact ⟨_, ⟨hx, hGx⟩, rfl⟩
  rw [tangentChartMap_tangentMap hG hχ hψ hα hfα]
  exact congrArg Prod.snd (retractTangentMap_apply
    (TangentPre.isScSmoothRetractMap_coord hG hχ hψ subset_rfl hso) (ScRetraction.id hU)
    (image_id _) hmem)

/-- **The tangent map in charts is the derivative of the coordinate map**: for a corner chart
`χ`, `T(ψ ∘ G ∘ χ⁻¹)` at `χ(x)` is any derivative `D` of `ψ ∘ G ∘ χ⁻¹` on `χ(V ∩ G⁻¹V')`. -/
theorem tangentChartMap_tangentMap_eq_of_hasFDerivWithinAt {Y Z : Type*} [TopologicalSpace Y]
    [T2Space Y] [ParacompactSpace Y] [TopologicalSpace Z] [T2Space Z] [ParacompactSpace Z]
    {P : MPolyfold Y} {B : MPolyfold Z} {G : Y → Z} (hG : P.IsScSmoothMap B G)
    {χ : MChart Y} (hχ : P.IsChart χ) (hc : χ.IsCornerChart) {ψ : MChart Z} (hψ : B.IsChart ψ)
    {α : P.TangentSpace} {x : P.Level 1} (hαx : α ∈ P.tangentFiber x)
    (hx : P.levelVal 1 x ∈ χ.source) (hGx : G (P.levelVal 1 x) ∈ ψ.source)
    {D : χ.model.E 0 →L[ℝ] ψ.model.E 0}
    (hD : HasFDerivWithinAt (ψ ∘ G ∘ χ.symm) D (χ '' TangentPre.fdom χ G ψ) (χ (P.levelVal 1 x))) :
    (tangentChartMap hψ (tangentMap hG α)).2 = D (tangentChartMap hχ α).2 := by
  have := hc.finiteDimensional
  have hso := TangentPre.isOpen_fdom hG χ ψ
  have hU := relOpen_image_fdom hc inter_subset_left hso
  rw [tangentChartMap_tangentMap_eq_scDeriv hG hχ hc hψ hαx hx hGx]
  have hbase : χ.model.E.toBase 1 (tangentChartMap hχ α).1 = χ (P.levelVal 1 x) := by
    rw [tangentChartMap_fst_of_mem_fiber hχ hx hαx, P.toBase_levelLift hχ hx (levelVal_mem x)]
  have hmem : χ (P.levelVal 1 x) ∈ χ '' TangentPre.fdom χ G ψ := ⟨_, ⟨hx, hGx⟩, rfl⟩
  have hsc : IsSc1 (χ '' TangentPre.fdom χ G ψ) (ψ ∘ G ∘ χ.symm) :=
    ((TangentPre.isScSmoothRetractMap_coord hG hχ hψ subset_rfl hso).comp_isScSmooth
      (ScRetraction.id hU) (image_id _)).isSc1
  have hD0 := hsc.hasFDerivWithinAt_of_finiteDimensional (x := (tangentChartMap hχ α).1)
    (by rw [hbase]; exact hmem)
  rw [hbase] at hD0
  rw [(hU.isScDomain.uniqueDiffWithinAt 0 _ hmem).eq hD0 hD]

/-- The coordinate map `ψ ∘ G ∘ χ⁻¹` of an sc-smooth map from a corner chart is differentiable at
`χ(x)` on `χ(V ∩ G⁻¹V')`. -/
theorem exists_hasFDerivWithinAt_coord {Y Z : Type*} [TopologicalSpace Y]
    [T2Space Y] [ParacompactSpace Y] [TopologicalSpace Z] [T2Space Z] [ParacompactSpace Z]
    {P : MPolyfold Y} {B : MPolyfold Z} {G : Y → Z} (hG : P.IsScSmoothMap B G)
    {χ : MChart Y} (hχ : P.IsChart χ) (hc : χ.IsCornerChart) {ψ : MChart Z} (hψ : B.IsChart ψ)
    {x : P.Level 1} (hx : P.levelVal 1 x ∈ χ.source) (hGx : G (P.levelVal 1 x) ∈ ψ.source) :
    ∃ D : χ.model.E 0 →L[ℝ] ψ.model.E 0,
      HasFDerivWithinAt (ψ ∘ G ∘ χ.symm) D (χ '' TangentPre.fdom χ G ψ) (χ (P.levelVal 1 x)) := by
  have := hc.finiteDimensional
  have hso := TangentPre.isOpen_fdom hG χ ψ
  have hU := relOpen_image_fdom hc inter_subset_left hso
  have hbase := P.toBase_levelLift hχ hx (levelVal_mem x)
  have hsc : IsSc1 (χ '' TangentPre.fdom χ G ψ) (ψ ∘ G ∘ χ.symm) :=
    ((TangentPre.isScSmoothRetractMap_coord hG hχ hψ subset_rfl hso).comp_isScSmooth
      (ScRetraction.id hU) (image_id _)).isSc1
  have hD0 := hsc.hasFDerivWithinAt_of_finiteDimensional (x := levelLift χ 1 (P.levelVal 1 x))
    (by rw [hbase]; exact ⟨_, ⟨hx, hGx⟩, rfl⟩)
  rw [hbase] at hD0
  exact ⟨_, hD0⟩

/-- **The tangent map along the end projection** (proof of 2021 Theorem 6.7.1, p. 278; preprint
Theorem 6.43; the text uses `T(p₁) = (0, id)` on `(a, b) × S_i` implicitly): if `G' = G ∘ pr` on
the end `(a, b) × A` of `A'`, then `TG'` of the corner vector `w` of `κ.prodRn` is `TG` of the
corner vector `tail w` of `κ`. -/
theorem tangentMap_prodRn_fiberMap {Z : Type*} [TopologicalSpace Z] [T2Space Z]
    [ParacompactSpace Z] {B : MPolyfold Z} {G : A → Z} (hG : (subPolyfold hA).IsScSmoothMap B G)
    {G' : A' → Z} (hG' : (subPolyfold hA').IsScSmoothMap B G')
    (hGG' : ∀ p : A', p.1.1 0 ∈ Ioo a b → G' p = G (endProj A x₀ p))
    (κ : CornerCoords (subPolyfold hA) k) {p : (subPolyfold hA').Level 1}
    (hp : (subPolyfold hA').levelVal 1 p ∈ (κ.prodRn hA' hab hend x₀).χ.source)
    {x : (subPolyfold hA).Level 1} (hxκ : (subPolyfold hA).levelVal 1 x ∈ κ.χ.source)
    (hx : (subPolyfold hA).levelVal 1 x = endProj A x₀ ((subPolyfold hA').levelVal 1 p))
    (w : EuclideanSpace ℝ (Fin (k + 1))) :
    tangentMap hG' ((κ.prodRn hA' hab hend x₀).fiberMap hp w).1 =
      tangentMap hG (κ.fiberMap hxκ (tailE w)).1 := by
  set κ' := κ.prodRn hA' hab hend x₀
  have hpt := ((mem_prodEndChart_source hab hend x₀).1 hp).1
  have hGp : G' ((subPolyfold hA').levelVal 1 p) = G ((subPolyfold hA).levelVal 1 x) := by
    rw [hGG' _ hpt, hx]
  set y := liftLevelOneMap hG x
  have hy : B.levelVal 1 y = G ((subPolyfold hA).levelVal 1 x) := levelVal_liftLevelOneMap hG x
  obtain ⟨ψ, hψ, hyψ⟩ := B.exists_isChart_mem_source (B.levelVal 1 y)
  have hL' := tangentMap_mapsTo_fiber hG' p y (hGp.trans hy.symm) (κ'.fiberMap hp w).2
  have hL := tangentMap_mapsTo_fiber hG x y hy.symm (κ.fiberMap hxκ (tailE w)).2
  refine tangentChartMap_injOn hψ (mem_tangentChartSet_of_mem_fiber hyψ hL')
    (mem_tangentChartSet_of_mem_fiber hyψ hL) (Prod.ext ?_ ?_)
  · rw [tangentChartMap_fst_of_mem_fiber hψ hyψ hL', tangentChartMap_fst_of_mem_fiber hψ hyψ hL]
  have hGψ : G ((subPolyfold hA).levelVal 1 x) ∈ ψ.source := hy ▸ hyψ
  have hGψ' : G' ((subPolyfold hA').levelVal 1 p) ∈ ψ.source := hGp ▸ hGψ
  obtain ⟨D, hD⟩ := exists_hasFDerivWithinAt_coord hG κ.isChart κ.isCornerChart hψ hxκ hGψ
  rw [tangentChartMap_tangentMap_eq_of_hasFDerivWithinAt hG κ.isChart κ.isCornerChart hψ
    (κ.fiberMap hxκ (tailE w)).2 hxκ hGψ hD, κ.tangentChartMap_fiberMap hxκ (tailE w)]
  have hχ' : ∀ q : A', κ'.χ q = ((fun _ => q.1.1 0 : Fin 1 → ℝ), κ.χ (endProj A x₀ q)) :=
    fun _ => rfl
  have hmaps : MapsTo Prod.snd (κ'.χ '' TangentPre.fdom κ'.χ G' ψ)
      (κ.χ '' TangentPre.fdom κ.χ G ψ) := by
    rintro _ ⟨q, ⟨hq, hGq⟩, rfl⟩
    obtain ⟨hqt, hqs⟩ := (mem_prodEndChart_source hab hend x₀).1 hq
    refine ⟨endProj A x₀ q, ⟨hqs, ?_⟩, by rw [hχ']⟩
    rw [mem_preimage, ← hGG' q hqt]; exact hGq
  have heq : EqOn (ψ ∘ G' ∘ κ'.χ.symm) ((ψ ∘ G ∘ κ.χ.symm) ∘ Prod.snd)
      (κ'.χ '' TangentPre.fdom κ'.χ G' ψ) := by
    rintro _ ⟨q, ⟨hq, hGq⟩, rfl⟩
    obtain ⟨hqt, hqs⟩ := (mem_prodEndChart_source hab hend x₀).1 hq
    change ψ (G' (κ'.χ.symm (κ'.χ q))) = ψ (G (κ.χ.symm (κ.χ (endProj A x₀ q))))
    rw [κ'.χ.symm_apply_apply hq, κ.χ.symm_apply_apply hqs, hGG' q hqt]
  have hmem' : κ'.χ ((subPolyfold hA').levelVal 1 p) ∈ κ'.χ '' TangentPre.fdom κ'.χ G' ψ :=
    ⟨_, ⟨hp, hGψ'⟩, rfl⟩
  have hz : (κ'.χ ((subPolyfold hA').levelVal 1 p)).2 = κ.χ ((subPolyfold hA).levelVal 1 x) := by
    rw [hχ', hx]
  rw [← hz] at hD
  have hD' := (hD.comp _ hasFDerivAt_snd.hasFDerivWithinAt hmaps).congr heq (heq hmem')
  rw [tangentChartMap_tangentMap_eq_of_hasFDerivWithinAt hG' κ'.isChart κ'.isCornerChart hψ
    (κ'.fiberMap hp w).2 hp hGψ' hD', κ'.tangentChartMap_fiberMap hp w]
  rfl

end TangentEnd

section FormsAlongEnd

open ManifoldForm

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  [ParacompactSpace ((Fin 1 → ℝ) × X)] {A : Set X} [ParacompactSpace A]
  {hA : PX.IsSubMPolyfold A} {A' : Set ((Fin 1 → ℝ) × X)} [ParacompactSpace A']
  (hA' : ((rnPolyfold 1).prod PX).IsSubMPolyfold A') {a b : ℝ} (hab : a < b)
  (hend : ∀ z : (Fin 1 → ℝ) × X, z.1 0 ∈ Ioo a b → (z ∈ A' ↔ z.2 ∈ A)) (x₀ : A) {k : ℕ}
  (hcs : (subPolyfold hA).HasCornerStructureOfDim k)
  (hcs' : (subPolyfold hA').HasCornerStructureOfDim (k + 1))
  [instA : ChartedSpace (EuclideanQuadrant k) A]
  (hchA : instA = (subPolyfold hA).cornerChartedSpace hcs)
  [instA' : ChartedSpace (EuclideanQuadrant (k + 1)) A']
  (hchA' : instA' = (subPolyfold hA').cornerChartedSpace hcs')

/-- **The pull-back of a form along the end projection** (proof of 2021 Theorem 6.7.1, p. 278;
preprint Theorem 6.43; implicit in the text):
for sc-smooth maps `g : A → Y`, `g' : A' → Y` with `g' = g ∘ pr` on the end `(a, b) × A`, the
Mathlib forms `g'^*ω` on `A'` and `g^*ω` on `A` (`formsAlong`) satisfy `IsEndPullback` for
`productEndOfSub`. -/
theorem isEndPullback_formsAlong {Bd : BundledMPolyfold.{v}} (g : ScMap (subPolyfold hA) Bd.P)
    (g' : ScMap (subPolyfold hA') Bd.P)
    (hgg' : ∀ p : A', p.1.1 0 ∈ Ioo a b → g' p = g (endProj A x₀ p)) {m : ℕ} (i : ℕ)
    (ω : Bd.forms m i) :
    (productEndOfSub hA' hab hend x₀ hcs hcs' hchA hchA').IsEndPullback
      (formsAlong hcs' g' i ω) (formsAlong hcs g i ω) := by
  intro y₀ y hy
  set E := productEndOfSub hA' hab hend x₀ hcs hcs' hchA hchA'
  set κ := hcs.coords y₀
  set κ' := κ.prodRn hA' hab hend x₀
  have hc : chartAt (EuclideanQuadrant k) y₀ = κ.toQuadrantChart := chartAt_eq_of_eq hcs hchA y₀
  rw [hc] at hy ⊢
  have heqv : E.chart κ.toQuadrantChart ≈ κ'.toQuadrantChart :=
    endChart_eqOnSource hA' hab hend x₀ κ
  have hy' : y ∈ (κ'.toQuadrantChart.extend (𝓠 (k + 1))).target := by
    rw [OpenPartialHomeomorph.extend_target] at hy ⊢
    rwa [← heqv.target_eq]
  have htail : tailE y ∈ (κ.toQuadrantChart.extend (𝓠 k)).target :=
    (E.mem_chart_extend_target.1 hy).2
  have hsymm : (κ'.toQuadrantChart.extend (𝓠 (k + 1))).symm y = E.pt κ.toQuadrantChart y := by
    rw [← extend_symm_eq_of_eqOnSource heqv hy, E.chart_extend_symm hy]
  obtain ⟨hpt, hφpt⟩ := E.pt_mem hy
  rw [chartForm_eq_of_eqOnSource heqv _ hy]
  ext v
  rw [tailPull_apply, formsAlong_apply, formsAlong_apply,
    chartForm_cornerForm_fiberMap hcs' hchA' κ' _ hy' v,
    chartForm_cornerForm_fiberMap hcs hchA κ _ htail]
  set q' := (κ'.toQuadrantChart.extend (𝓠 (k + 1))).symm y
  set q := (κ.toQuadrantChart.extend (𝓠 k)).symm (tailE y)
  have hq : endProj A x₀ q' = q := by
    have h2 : (endPH hab hend x₀ q').2 = q := by rw [hsymm]; exact congrArg Prod.snd hφpt
    exact h2
  have hqt : q'.1.1 0 ∈ Ioo a b := by
    have h1 := (E.mem_chart_source.1 hpt).1
    rw [← hsymm] at h1
    exact h1
  have hGG : ∀ p : A', p.1.1 0 ∈ Ioo a b →
      alongLift hcs' g' i p = alongLift hcs g i (endProj A x₀ p) := fun p hp =>
    Bd.incl_injective i (by rw [incl_alongLift, incl_alongLift]; exact hgg' p hp)
  refine (formPullback_eq _ _ _ (y := liftLevelOneMap (alongLift hcs g i).isScSmoothMap
    (hcs.levelOne q)) ?_ _ fun j => ?_).trans (formPullback_apply _ _ _ _).symm
  · rw [levelVal_liftLevelOneMap]
    change alongLift hcs' g' i q' = alongLift hcs g i q
    rw [← hq]
    exact hGG q' hqt
  exact (tangentMap_prodRn_fiberMap hA' hab hend x₀ (alongLift hcs g i).isScSmoothMap
    (alongLift hcs' g' i).isScSmoothMap hGG κ (p := hcs'.levelOne q') (x := hcs.levelOne q) _ _
    hq.symm (v j)).trans
    (coe_tangentFiberMap_apply _ _).symm

omit [T2Space X] in
variable (PX) in
/-- The projection `p₁ : ℝ¹ × X → X`, `(t, x) ↦ x`, as an `ScMap` (`isScSmoothMap_snd`). -/
abbrev prXScMap :
    ScMap (BundledMPolyfold.of ((rnPolyfold 1).prod PX)).P (BundledMPolyfold.of PX).P :=
  ⟨Prod.snd, MPolyfold.isScSmoothMap_snd (rnPolyfold 1) PX⟩

/-- **`IsEndPullback` on `Ωᵐ_∞`** (proof of 2021 Theorem 6.7.1, p. 278; preprint Theorem 6.43;
`formsInftyAlong`): the version of `isEndPullback_formsAlong` for classes in the direct limit. -/
theorem isEndPullback_formsInftyAlong {Bd : BundledMPolyfold.{v}}
    (g : ScMap (subPolyfold hA) Bd.P) (g' : ScMap (subPolyfold hA') Bd.P)
    (hgg' : ∀ p : A', p.1.1 0 ∈ Ioo a b → g' p = g (endProj A x₀ p)) {m : ℕ}
    (ω : Bd.formsInfty m) :
    (productEndOfSub hA' hab hend x₀ hcs hcs' hchA hchA').IsEndPullback
      (formsInftyAlong m hcs' g' ω) (formsInftyAlong m hcs g ω) := by
  induction ω using Module.DirectLimit.induction_on with
  | ih i ω =>
    rw [formsInftyAlong_of, formsInftyAlong_of]
    exact isEndPullback_formsAlong hA' hab hend x₀ hcs hcs' hchA hchA' g g' hgg' i ω

/-- **`p₁^*ω` on the end** (proof of 2021 Theorem 6.7.1, p. 278; preprint Theorem 6.43): for
`ω ∈ Ωᵐ_∞(X)`, the restriction to `A' ⊆ ℝ¹ × X` of the pull-back of `ω` along `(t, x) ↦ x`
reads on the end `(a, b) × A` as the pull-back of the restriction `ω|_A` (`IsEndPullback`). -/
theorem isEndPullback_formsInftyRestrict_snd {m : ℕ}
    (ω : (BundledMPolyfold.of PX).formsInfty m) :
    (productEndOfSub hA' hab hend x₀ hcs hcs' hchA hchA').IsEndPullback
      (formsInftyRestrict m hcs' (BundledMPolyfold.formsInftyPullback (prXScMap PX) m ω))
      (formsInftyRestrict m hcs ω) := by
  have h := LinearMap.congr_fun (formsInftyAlong_comp_formsInftyPullback (k := m) hcs'
    (A := BundledMPolyfold.of ((rnPolyfold 1).prod PX)) (subInclScMap hA')
    (B := BundledMPolyfold.of PX) (prXScMap PX)) ω
  rw [LinearMap.comp_apply] at h
  refine (congrArg (fun Ω => (productEndOfSub hA' hab hend x₀ hcs hcs' hchA hchA').IsEndPullback Ω
    (formsInftyRestrict m hcs ω)) h).mpr ?_
  exact isEndPullback_formsInftyAlong hA' hab hend x₀ hcs hcs' hchA hchA' _ _
    (fun p hp => (endProj_val_of_mem hend x₀ hp).symm) ω

/-- **`hprod` of `integral_end_fubini` for `d(f · p₁^*ω)`** (proof of 2021 Theorem 6.7.1, p. 278;
preprint Theorem 6.43): for `ω ∈ Ωᵏ_∞(X)` and a smooth `f` on `A'` with `f = g ∘ t` on the end,
the coefficient of `d(f · (p₁^*ω)|_{A'})` in the product charts is `g′(t)` times that of `ω|_A`. -/
theorem chartForm_extDeriv_smulFun_formsInftyRestrict_snd
    (ω : (BundledMPolyfold.of PX).formsInfty k) {f : A' → ℝ}
    (hf : ContMDiff (𝓠 (k + 1)) 𝓘(ℝ) ∞ f) {g : ℝ → ℝ} (hg : Differentiable ℝ g)
    (hfg : ∀ p ∈ (productEndOfSub hA' hab hend x₀ hcs hcs' hchA hchA').φ.source,
      f p = g ((productEndOfSub hA' hab hend x₀ hcs hcs' hchA hchA').φ p).1)
    (y₀ : A) {y : EuclideanSpace ℝ (Fin (k + 1))}
    (hy : y ∈ (((productEndOfSub hA' hab hend x₀ hcs hcs' hchA hchA').chart
      (chartAt (EuclideanQuadrant k) y₀)).extend (𝓠 (k + 1))).target) :
    ManifoldForm.chartForm (𝓠 (k + 1)) ((productEndOfSub hA' hab hend x₀ hcs hcs' hchA hchA').chart
        (chartAt (EuclideanQuadrant k) y₀))
        (ManifoldForm.extDeriv (ManifoldForm.smulFun f (formsInftyRestrict k hcs'
          (BundledMPolyfold.formsInftyPullback (prXScMap PX) k ω)))) y
        (stdFrame (k + 1)) =
      deriv g (y 0 + a) * ManifoldForm.chartForm (𝓠 k) (chartAt (EuclideanQuadrant k) y₀)
        (formsInftyRestrict k hcs ω) (tailE y) (stdFrame k) := by
  have := isManifold_of_eq hcs hchA
  have := isManifold_of_eq hcs' hchA'
  exact (productEndOfSub hA' hab hend x₀ hcs hcs' hchA hchA').chartForm_extDeriv_smulFun_stdFrame
    ((contMDiffForm_formsInftyRestrict hchA ω).of_le (by exact_mod_cast le_top))
    (isEndPullback_formsInftyRestrict_snd hA' hab hend x₀ hcs hcs' hchA hchA' ω) hg hfg
    ((ContMDiffForm.smulFun le_rfl hf (contMDiffForm_formsInftyRestrict hchA' _)).of_le
      (by exact_mod_cast le_top)) y₀ hy

/-- **`hprod` for the cut-off** (proof of 2021 Theorem 6.7.1, p. 278; preprint Theorem 6.43): for
`ω ∈ Ωᵏ_∞(X)` and a `C^∞` function `g` of the time, the coefficient of
`d(g(t) · (p₁^*ω)|_{A'})` in the product charts of the end is `g′(t)` times that of `ω|_A`: the
hypothesis `hprod` of `ProductEnd.integral_end_fubini` with `h = g′`. -/
theorem chartForm_extDeriv_cutoff_formsInftyRestrict_snd
    (ω : (BundledMPolyfold.of PX).formsInfty k) {g : ℝ → ℝ} (hg : ContDiff ℝ ∞ g)
    (y₀ : A) {y : EuclideanSpace ℝ (Fin (k + 1))}
    (hy : y ∈ (((productEndOfSub hA' hab hend x₀ hcs hcs' hchA hchA').chart
      (chartAt (EuclideanQuadrant k) y₀)).extend (𝓠 (k + 1))).target) :
    ManifoldForm.chartForm (𝓠 (k + 1)) ((productEndOfSub hA' hab hend x₀ hcs hcs' hchA hchA').chart
        (chartAt (EuclideanQuadrant k) y₀))
        (ManifoldForm.extDeriv (ManifoldForm.smulFun (fun p : A' => g (p.1.1 0))
          (formsInftyRestrict k hcs' (BundledMPolyfold.formsInftyPullback (prXScMap PX) k ω)))) y
        (stdFrame (k + 1)) =
      deriv g (y 0 + a) * ManifoldForm.chartForm (𝓠 k) (chartAt (EuclideanQuadrant k) y₀)
        (formsInftyRestrict k hcs ω) (tailE y) (stdFrame k) :=
  chartForm_extDeriv_smulFun_formsInftyRestrict_snd hA' hab hend x₀ hcs hcs' hchA hchA' ω
    (contMDiff_comp_time hcs' hchA' hg) (hg.differentiable (by simp)) (fun _ _ => rfl) y₀ hy

end FormsAlongEnd

end MPolyfold

end FormsEnd

end Polyfold
