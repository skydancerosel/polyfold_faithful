import Polyfold.Chapter9.SphereRadialRetraction
import Polyfold.Chapter9.BoundaryMeasure
import Polyfold.Chapter2.TameSub

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021; 2017 arXiv 1707.08941),
Part II, Chapter 9, §9.5, Theorems 9.5.17 and 9.5.18 (Stokes), the witness of their hypotheses:
the sheet.  Numbers and pages are the 2021 text's.

# The closed upper hemisphere as a tame `2`-dimensional submanifold of `[0, ∞) × ℝ²`

`X = [0, ∞) × ℝ²` is the M-polyfold `quadrantPolyfold 1 ℝ²` (`Ph`), with boundary `{t = 0}`.
The hemisphere `hemi = {p ∈ X | |p| = 1}` is compact, and:

* it is a smooth finite-dimensional submanifold (Definition 4.2.1): the image of the
  sc⁺-retraction `p ↦ p / |p|` of the open set `X ∖ {0}` (`hemiData`); in the identity chart
  its tangent space at `a` is `a^⊥` (`tangentSpace_hemi`), so it is `2`-dimensional
  (`isSubmanifoldOfDim_hemi`);
* it is a tame sub-M-polyfold (2021 Definition 2.5.19, `isTameSubMPolyfold_hemi`): the
  retraction keeps `d_X` (it multiplies by a positive number), and `ℝa ⊆ T^R_aX` is an
  sc-complement of `T_a hemi = a^⊥` (`hasReducedComplementAt_hemi`); so its induced structure is
  tame (`hasTameInducedStructure_hemi`);
* its boundary `∂ hemi` and its stratum `∂₁ hemi = {d = 1}` are the equator `{t = 0}`
  (`boundaryStratum_hemi`): at an equator point `e_t ∈ T_a hemi` is not reduced.
-/

set_option maxSynthPendingDepth 3

open Set Function Filter Topology Module Submodule
open scoped ContDiff

noncomputable section

namespace Polyfold

open MPolyfold

namespace E8W

/-! ### The half-space M-polyfold -/

/-- The sc-Banach space `ℝ²` with the constant structure. -/
abbrev Wq : ScBanach := ScBanach.const (Fin 2 → ℝ)

/-- The model sc-Banach space `ℝ ⊕ ℝ²`. -/
abbrev E3 : ScBanach := (ScBanach.const (Fin 1 → ℝ)).prod Wq

/-- The half-space `[0, ∞) × ℝ²`. -/
abbrev Q3 : Set (E3 0) := quadrant 1 Wq 0

/-- **The half-space `X = [0, ∞) × ℝ²` as an M-polyfold**, with boundary `{t = 0}`. -/
abbrev Ph : MPolyfold Q3 := quadrantPolyfold 1 Wq

theorem relOpen_Q3 : IsRelOpenInQuadrant E3 Q3 Q3 := isRelOpenInQuadrant_quadrant 1 Wq

/-- The chart `id` of `X`. -/
abbrev chartQ : MChart Q3 :=
  (LocalModel.ofRelOpen relOpen_Q3).selfChart (quadrant_nonempty 1 Wq)

theorem isChart_chartQ : Ph.IsChart chartQ :=
  relOpen_Q3.selfChart_isChart (quadrant_nonempty 1 Wq)

theorem chartQ_apply (p : Q3) : chartQ p = p.1 := rfl

theorem chartQ_symm_val {v : E3 0} (hv : v ∈ Q3) : ((chartQ.symm v : Q3) : E3 0) = v :=
  chartQ.toPartialEquiv.right_inv hv

theorem bijective_toBase_E3 (m : ℕ) : Bijective (E3.toBase m) :=
  bijective_toBase_prod (bijective_toBase_const _) (bijective_toBase_const _) m

/-- A vector of `ℝ ⊕ ℝ²` read on level `1`. -/
def lev1 (v : V3) : E3 1 := v

theorem toBase_lev1 (v : V3) : E3.toBase 1 (lev1 v) = v := by
  rw [ScBanach.prod_toBase]
  exact Prod.ext (ScBanach.const_toBase _ 1 _) (ScBanach.const_toBase _ 1 _)

theorem mem_smooth_E3 (v : E3 0) : v ∈ E3.smooth :=
  E3.mem_smooth_iff.2 fun j => (bijective_toBase_E3 j).2 v

/-- `X` has a corner structure (Definition 4.1; its chart `id` has a corner chart with the same
domain). -/
theorem Ph_hasCornerStructure : Ph.HasCornerStructure := by
  refine hasCornerStructure_iff.2 fun x => ?_
  have hfin : FiniteDimensional ℝ (E3 0) := by
    change FiniteDimensional ℝ ((Fin 1 → ℝ) × (Fin 2 → ℝ)); infer_instance
  obtain ⟨χ', hχ', hsrc, hc, -⟩ := MChart.exists_isCornerChart_of_finiteDimensional isChart_chartQ
    relOpen_Q3 hfin
  exact ⟨χ', hχ', hsrc ▸ mem_univ x, hc⟩

theorem Ph_mem_smoothSet (p : Q3) : p ∈ Ph.smoothSet :=
  (mem_smoothSet_iff_of_isChart isChart_chartQ (mem_univ p)).2 (mem_smooth_E3 _)

theorem Ph_mem_levelSet (m : ℕ) (p : Q3) : p ∈ Ph.levelSet m :=
  Ph.smoothSet_subset_levelSet m (Ph_mem_smoothSet p)

theorem Ph_isScSmoothMap_toLevelOne (x₀ : Ph.Level 1) :
    Ph.IsScSmoothMap Ph.shift (Ph.toLevelOne x₀) := by
  have hc := hasCornerStructure_iff.1 Ph_hasCornerStructure
  refine (isScSmoothMap_toLevelOne_of_cover x₀ fun x => ?_).2
  obtain ⟨χ, hχ, hx, hcorner⟩ := hc x
  exact ⟨χ, hχ, hx, hcorner.isScPlusRetract⟩

/-- `d_X(p)` is the number of vanishing `t`-coordinates of `p`. -/
theorem Ph_degIndex (p : Q3) :
    Ph.degIndex p = (Finset.univ.filter fun i : Fin 1 => p.1.1 i = 0).card := by
  rw [show Ph.degIndex p = TameBoundaryExample.dq 1 Wq p from rfl, TameBoundaryExample.dq_eq]
  rfl

theorem Ph_degIndex_le (p : Q3) : Ph.degIndex p ≤ 1 := by
  rw [Ph_degIndex]
  exact (Finset.card_filter_le _ _).trans (by simp)

theorem Ph_mem_boundary_iff (p : Q3) : p ∈ Ph.boundary ↔ p.1.1 0 = 0 := by
  change 1 ≤ Ph.degIndex p ↔ _
  rw [Ph_degIndex, Nat.one_le_iff_ne_zero, Ne, Finset.card_eq_zero,
    Finset.filter_eq_empty_iff]
  simp

/-! ### Sc-smooth maps of `X` from `C^∞` maps -/

/-- **A `C^∞` map `f` on an open `G ⊆ ℝ³` mapping `X` into `X` is sc-smooth on `X ∩ G`.** -/
theorem isScSmoothOn_of_contDiffOn {G : Set V3} (hG : IsOpen G) {f : V3 → V3}
    (hf : ContDiffOn ℝ ∞ f G) (hQ : ∀ v ∈ Q3, f v ∈ Q3) :
    Ph.IsScSmoothOn Ph (fun p : Q3 => (⟨f p.1, hQ p.1 p.2⟩ : Q3)) {p | p.1 ∈ G} := by
  have hGo : IsOpen {p : Q3 | p.1 ∈ G} := hG.preimage continuous_subtype_val
  have hU : IsRelOpenInQuadrant E3 Q3 (G ∩ Q3) :=
    ⟨relOpen_Q3.isPartialQuadrant, G, hG, rfl⟩
  have hcont : ContinuousOn (fun p : Q3 => f p.1) {p | p.1 ∈ G} :=
    hf.continuousOn.comp continuous_subtype_val.continuousOn fun _ hp => hp
  refine IsScSmoothOn.of_exists_charts hGo (Topology.IsInducing.subtypeVal.continuousOn_iff.2 hcont)
    fun x hx => ⟨chartQ, chartQ, {p | p.1 ∈ G}, isChart_chartQ, isChart_chartQ, hGo, hx,
      fun p hp => ⟨hp, mem_univ _⟩, fun _ _ => mem_univ _, ?_⟩
  have himg : chartQ '' {p : Q3 | p.1 ∈ G} = G ∩ Q3 := by
    ext v
    constructor
    · rintro ⟨p, hp, rfl⟩; exact ⟨hp, p.2⟩
    · intro hv; exact ⟨⟨v, hv.2⟩, hv.1, rfl⟩
  have hval : ∀ u ∈ G ∩ Q3,
      (chartQ ∘ (fun p : Q3 => (⟨f p.1, hQ p.1 p.2⟩ : Q3)) ∘ chartQ.symm) u = f u := by
    intro u hu
    change f ((chartQ.symm u : Q3) : E3 0) = f u
    rw [chartQ_symm_val hu.2]
  rw [himg]
  refine (isScSmoothRetractMap_iff_exists hU.isScRetract).2
    ⟨fun u hu => ?_, ScRetraction.id hU, image_id _, ?_⟩
  · rw [hval u hu]; exact hQ u hu.2
  · refine (isScSmooth_of_bijective_toBase bijective_toBase_E3 bijective_toBase_E3
      hU.isScDomain (f := f) (hf.mono inter_subset_left)).congr hU.isScDomain fun u hu => ?_
    exact (hval u hu).symm

/-! ### The hemisphere and its retraction -/

theorem rho_mem_Q3 {v : E3 0} (hv : v ∈ Q3) : rho v ∈ Q3 := fun i => by
  rw [Subsingleton.elim i 0]
  change 0 ≤ (√(nsq v))⁻¹ * v.1 0
  exact mul_nonneg (inv_nonneg.2 (Real.sqrt_nonneg _)) (hv 0)

/-- **The closed upper hemisphere** `{p ∈ [0, ∞) × ℝ² | |p| = 1}`. -/
def hemi : Set Q3 := {p | nsq p.1 = 1}

/-- The open set `X ∖ {0}`. -/
def Vh : Set Q3 := {p | p.1 ∈ punct3}

theorem isOpen_Vh : IsOpen Vh := isOpen_punct3.preimage continuous_subtype_val

theorem hemi_subset_Vh : hemi ⊆ Vh := fun _ hp => sphere3_subset_punct3 hp

theorem isClosed_hemi : IsClosed hemi := isClosed_sphere3.preimage continuous_subtype_val

/-- The radial retraction of `X`. -/
def sQ (p : Q3) : Q3 := ⟨rho p.1, rho_mem_Q3 p.2⟩

theorem sQ_mem_hemi {p : Q3} (hp : p ∈ Vh) : sQ p ∈ hemi := rho_mem_sphere3 hp

theorem sQ_eq_self {p : Q3} (hp : p ∈ hemi) : sQ p = p := Subtype.ext (rho_eq_self hp)

theorem sQ_image : sQ '' Vh = hemi ∩ Vh := by
  refine Subset.antisymm ?_ fun p hp => ⟨p, hp.2, sQ_eq_self hp.1⟩
  rintro _ ⟨p, hp, rfl⟩
  exact ⟨sQ_mem_hemi hp, hemi_subset_Vh (sQ_mem_hemi hp)⟩

/-- **The radial retraction is an sc⁺-retraction of `X` on `X ∖ {0}`** (Definition 4.1.4). -/
theorem sQ_isScPlusRetractionOn : Ph.IsScPlusRetractionOn sQ Vh where
  isScSmoothOn := isScSmoothOn_of_contDiffOn isOpen_punct3 contDiffOn_rho fun _ hv => rho_mem_Q3 hv
  mapsTo _ hp := hemi_subset_Vh (sQ_mem_hemi hp)
  idem _ hp := sQ_eq_self (sQ_mem_hemi hp)
  mem_levelSet _ _ := Ph_mem_levelSet 1 _
  isScSmoothOn_one x₀ := IsScSmoothOn.comp (Ph_isScSmoothMap_toLevelOne x₀)
    (isScSmoothOn_of_contDiffOn isOpen_punct3 contDiffOn_rho fun _ hv => rho_mem_Q3 hv)
    (mapsTo_univ _ _)

/-- The data `(X ∖ {0}, p ↦ p/|p|)` of the hemisphere (Definition 4.2.1). -/
def hemiData : Ph.SubmanifoldData hemi :=
  ⟨Vh, sQ, isOpen_Vh, sQ_isScPlusRetractionOn, sQ_image⟩

/-- **The hemisphere is a smooth finite-dimensional submanifold of `X`** (Definition 4.2.1). -/
theorem isSmoothSubmanifold_hemi : Ph.IsSmoothSubmanifold hemi := fun _ ha =>
  ⟨Vh, isOpen_Vh, hemi_subset_Vh ha, sQ, sQ_isScPlusRetractionOn, sQ_image⟩

/-! ### The tangent spaces -/

/-- The radial retraction in the chart `id`, as an sc-smooth retraction of `ℝ ⊕ ℝ²`. -/
def rhoRet : ScRetraction E3 Q3 where
  U := punct3 ∩ Q3
  toFun := rho
  relOpen := ⟨relOpen_Q3.isPartialQuadrant, punct3, isOpen_punct3, rfl⟩
  mapsTo _ hv := ⟨sphere3_subset_punct3 (rho_mem_sphere3 hv.1), rho_mem_Q3 hv.2⟩
  isScSmooth := isScSmooth_of_bijective_toBase bijective_toBase_E3 bijective_toBase_E3
    (IsRelOpenInQuadrant.isScDomain ⟨relOpen_Q3.isPartialQuadrant, punct3, isOpen_punct3, rfl⟩)
    (contDiffOn_rho.mono inter_subset_left)
  idem _ hv := rho_idem hv.1

theorem rhoRet_retract : rhoRet.retract = sphere3 ∩ Q3 := by
  refine Subset.antisymm ?_ fun v hv => ⟨v, ⟨sphere3_subset_punct3 hv.1, hv.2⟩, rho_eq_self hv.1⟩
  rintro _ ⟨v, hv, rfl⟩
  exact ⟨rho_mem_sphere3 hv.1, rho_mem_Q3 hv.2⟩

/-- The chart image of a piece `W ∩ hemi` with `W ⊆ X ∖ {0}`, `hemi ⊆ W`. -/
theorem chartQ_image_hemi {W : Set Q3} (hW : hemi ⊆ W) : chartQ '' (W ∩ hemi) = rhoRet.retract := by
  rw [rhoRet_retract, inter_eq_right.2 hW]
  ext v
  constructor
  · rintro ⟨p, hp, rfl⟩; exact ⟨hp, p.2⟩
  · intro hv; exact ⟨⟨v, hv.2⟩, hv.1, rfl⟩

theorem shrink_hemiData : hemiData.toSubData.shrink chartQ = Vh := by
  refine Subset.antisymm (fun p hp => hp.1.1) fun p hp =>
    ⟨⟨hp, mem_univ _⟩, hemi_subset_Vh (sQ_mem_hemi hp), mem_univ _⟩

theorem chartQ_image_shrink : chartQ '' (hemiData.toSubData.shrink chartQ ∩ hemi) =
    rhoRet.retract := by
  rw [shrink_hemiData]; exact chartQ_image_hemi hemi_subset_Vh

/-- **The tangent space of the hemisphere** at `a`, in the chart `id`: `a^⊥`. -/
theorem tangentSpace_hemi {a : V3} (ha : a ∈ sphere3 ∩ Q3) :
    tangentSpace E3 Q3 rhoRet.retract (lev1 a) =
      (LinearMap.ker (ell a : V3 →ₗ[ℝ] ℝ) : Set V3) := by
  have hz : lev1 a ∈ E3.lvlSet rhoRet.retract 1 := by
    rw [ScBanach.mem_lvlSet, toBase_lev1, rhoRet_retract]; exact ha
  have hD : scDeriv rhoRet.U rhoRet (lev1 a) = rhoDeriv a := by
    refine scDeriv_eq_of_hasFDerivAt rhoRet.relOpen rhoRet.isSc1
      (by rw [ScBanach.mem_lvlSet] at hz ⊢; exact rhoRet.retract_subset hz) ?_
    rw [toBase_lev1]; exact hasFDerivAt_rho ha.1
  rw [tangentSpace_eq_coe_submodule rhoRet hz, hD]
  exact congrArg _ (range_rhoDeriv ha.1)

/-- **The hemisphere is a `2`-dimensional submanifold of `X`** (Remark 9.1.1). -/
theorem isSubmanifoldOfDim_hemi : Ph.IsSubmanifoldOfDim hemi 2 := by
  refine ⟨isSmoothSubmanifold_hemi, fun a ha => ?_⟩
  have hQ : IsScRetract chartQ.model.E chartQ.model.C (chartQ '' (Vh ∩ hemi)) := by
    rw [chartQ_image_hemi hemi_subset_Vh]; exact rhoRet.isScRetract
  refine hasDimAt_of_finrank isSmoothSubmanifold_hemi ha isChart_chartQ isOpen_Vh
    (subset_univ _) hQ (hemi_subset_Vh ha) (z := lev1 a.1) (toBase_lev1 a.1) ?_
  erw [chartQ_image_hemi hemi_subset_Vh, tangentSpace_hemi ⟨ha, a.2⟩, span_eq]
  exact finrank_ker_ell ha

/-! ### Tameness -/

/-- The projection `h ↦ h − ⟨a, h⟩a` as an sc-operator of `ℝ ⊕ ℝ²`. -/
def projOp (a : V3) : ScOperator E3 E3 where
  lvl _ := rhoDeriv a
  incl_comm _ _ := rfl

/-- **2021 Definition 2.5.19 (3) for the hemisphere**: in the chart `id`, `T_a hemi = a^⊥` has
the sc-complement `ℝa` in `T_aX = ℝ³`, and `ℝa ⊆ T^R_aX` (if `t(a) = 0`, every multiple of `a`
has `t = 0`). -/
theorem hasReducedComplementAt_hemi {a : V3} (ha : a ∈ sphere3 ∩ Q3) :
    HasReducedComplementAt Q3 Q3 rhoRet.retract (ScIso.refl E3) (lev1 a) := by
  have hU := relOpen_Q3
  have hidem : ∀ h, projOp a 0 (projOp a 0 h) = projOp a 0 h := rhoDeriv_idem ha.1
  have hS := ScBanach.isScSplitting_of_idem (projOp a) hidem
  have hzU : lev1 a ∈ E3.lvlSet Q3 1 := by rw [ScBanach.mem_lvlSet, toBase_lev1]; exact ha.2
  refine ⟨LinearMap.range (projOp a 0 : E3 0 →ₗ[ℝ] E3 0), ⊤,
    LinearMap.ker (projOp a 0 : E3 0 →ₗ[ℝ] E3 0), ?_, ?_, ?_, hS.2.1, fun m => ?_⟩
  · rw [tangentSpace_hemi ha]
    exact congrArg (fun S : Submodule ℝ V3 => (S : Set V3)) (range_rhoDeriv ha.1)
  · have hret : (ScRetraction.id hU).retract = Q3 := image_id _
    have hz0 : lev1 a ∈ E3.lvlSet (ScRetraction.id hU).retract 1 := by rw [hret]; exact hzU
    have h := tangentSpace_eq_coe_submodule (ScRetraction.id hU) hz0
    rw [hret] at h
    have hD : scDeriv (ScRetraction.id hU).U (ScRetraction.id hU) (lev1 a) =
        ContinuousLinearMap.id ℝ (E3 0) :=
      IsSc1.scDeriv_eqOn (isSc1With_id _) (hU.isScDomain.uniqueDiffWithinAt 1) hzU
    have hrange : LinearMap.range (scDeriv (ScRetraction.id hU).U (ScRetraction.id hU)
        (lev1 a) : E3 0 →ₗ[ℝ] E3 0) = ⊤ := by
      rw [hD]; exact LinearMap.range_id
    rw [h, hrange]
  · intro v hv
    have hv' : rhoDeriv a v = 0 := hv
    refine ⟨Submodule.mem_top, (mem_minimalSubspaceWith _).2 fun i hi => ?_⟩
    rw [Subsingleton.elim i 0] at hi ⊢
    have hi' : a.1 0 = 0 := by
      have := hi; rw [toBase_lev1] at this; exact this
    change v.1 0 = 0
    rw [ker_rhoDeriv hv']
    change inner3 a v * a.1 0 = 0
    rw [hi', mul_zero]
  · have hc := hS.2.2 m
    refine ⟨hc.disjoint, ?_⟩
    rw [hc.sup_eq_top]
    exact (Submodule.comap_top _).symm

/-- The data of 2021 Definition 2.5.19 for the hemisphere: the radial retraction keeps `d_X`. -/
def hemiTameData : Ph.TameSubData hemi :=
  { hemiData.toSubData with
    degIndex_apply := fun p hp => by
      change Ph.degIndex (sQ p) = Ph.degIndex p
      rw [Ph_degIndex, Ph_degIndex]
      congr 1
      refine Finset.filter_congr fun i _ => ?_
      rw [Subsingleton.elim i 0]
      change (√(nsq p.1))⁻¹ * p.1.1 0 = 0 ↔ p.1.1 0 = 0
      exact ⟨fun h => (mul_eq_zero.1 h).resolve_left (inv_sqrt_pos hp).ne',
        fun h => by rw [h, mul_zero]⟩
    complement := fun y hy _ => ⟨chartQ, 1, Wq, ScIso.refl _, lev1 y.1, isChart_chartQ,
      mem_univ _, by ext; rfl, toBase_lev1 _, by
        change HasReducedComplementAt Q3 Q3
          (chartQ '' (hemiData.toSubData.shrink chartQ ∩ hemi)) (ScIso.refl E3) (lev1 y.1)
        erw [chartQ_image_shrink]
        exact hasReducedComplementAt_hemi ⟨hy.1, y.2⟩⟩ }

/-- **The hemisphere is a tame sub-M-polyfold of `X`** (2021 Definition 2.5.19). -/
theorem isTameSubMPolyfold_hemi : Ph.IsTameSubMPolyfold hemi :=
  ⟨quadrantPolyfold_isTame 1 Wq, fun _ hy => ⟨hemiTameData, hemi_subset_Vh hy⟩⟩

/-- **The structure induced on the hemisphere is tame** (2021 Definition 2.5.18). -/
theorem hasTameInducedStructure_hemi : Ph.HasTameInducedStructure hemi :=
  isTameSubMPolyfold_hemi.hasTameInducedStructure

/-! ### The boundary: the equator -/

/-- At an equator point `e_t ∈ T_a hemi` is not in `T^R_aX`. -/
theorem not_isTangentReducedAt_hemi {p : Q3} (hp : p ∈ hemi) (h0 : p.1.1 0 = 0) :
    ¬ Ph.IsTangentReducedAt hemi p := by
  intro h
  have hred := h.isReducedChart hemiData isChart_chartQ (ScIso.refl _) (by ext; rfl)
    (hemi_subset_Vh hp) (mem_univ _) (toBase_lev1 p.1)
  have hv : mk3 1 0 0 ∈ tangentSpace E3 Q3
      (chartQ '' (hemiData.toSubData.shrink chartQ ∩ hemi)) (lev1 p.1) := by
    erw [chartQ_image_shrink, tangentSpace_hemi ⟨hp, p.2⟩]
    change ell p.1 (mk3 1 0 0) = 0
    simp [inner3, h0]
  have h1 := (mem_minimalSubspaceWith _).1 (hred hv) 0 (by
    change (E3.toBase 1 (lev1 p.1)).1 0 = 0
    rw [toBase_lev1]; exact h0)
  exact one_ne_zero h1

theorem mem_submanifoldBoundary_hemi {p : Q3} (hp : p ∈ hemi) (h0 : p.1.1 0 = 0) :
    p ∈ Ph.submanifoldBoundary hemi :=
  (mem_submanifoldBoundary_iff isSmoothSubmanifold_hemi).2
    ⟨hp, (Ph_mem_boundary_iff p).2 h0, not_isTangentReducedAt_hemi hp h0⟩

/-- The equator `{p ∈ hemi | t(p) = 0}`. -/
def equator : Set Q3 := {p | p ∈ hemi ∧ p.1.1 0 = 0}

/-- **The stratum `∂₁ hemi = {d = 1}` is the equator.** -/
theorem boundaryStratum_hemi : Ph.boundaryStratum hemi = equator := by
  ext p
  constructor
  · intro hb
    have hb' := (mem_boundaryStratum_iff_subDegIndex isSmoothSubmanifold_hemi
      hasTameInducedStructure_hemi hb.1).1 hb
    refine ⟨hb.1, (Ph_mem_boundary_iff p).1 ?_⟩
    have := subDegIndex_le isSmoothSubmanifold_hemi.isSubMPolyfold ⟨p, hb.1⟩
    rw [hb'] at this
    exact this
  · rintro ⟨hp, h0⟩
    refine (mem_boundaryStratum_iff_subDegIndex isSmoothSubmanifold_hemi
      hasTameInducedStructure_hemi hp).2 ?_
    have h1 := (mem_submanifoldBoundary_iff_subDegIndex isSmoothSubmanifold_hemi hp).1
      (mem_submanifoldBoundary_hemi hp h0)
    have h2 := (subDegIndex_le isSmoothSubmanifold_hemi.isSubMPolyfold ⟨p, hp⟩).trans
      (Ph_degIndex_le p)
    omega

/-! ### Compactness -/

theorem abs_le_one_of_mem_sphere3 {v : V3} (hv : v ∈ sphere3) :
    |v.1 0| ≤ 1 ∧ |v.2 0| ≤ 1 ∧ |v.2 1| ≤ 1 := by
  have hq : v.1 0 ^ 2 + v.2 0 ^ 2 + v.2 1 ^ 2 = 1 := by rw [← nsq_eq]; exact hv
  refine ⟨?_, ?_, ?_⟩ <;> rw [← sq_le_one_iff_abs_le_one] <;>
    nlinarith [sq_nonneg (v.1 0), sq_nonneg (v.2 0), sq_nonneg (v.2 1)]

theorem isCompact_sphere3 : IsCompact sphere3 := by
  refine Metric.isCompact_of_isClosed_isBounded isClosed_sphere3
    (isBounded_iff_forall_norm_le.2 ⟨1, fun v hv => ?_⟩)
  obtain ⟨h0, h1, h2⟩ := abs_le_one_of_mem_sphere3 hv
  refine norm_prod_le_iff.2 ⟨(pi_norm_le_iff_of_nonneg zero_le_one).2 fun i => ?_,
    (pi_norm_le_iff_of_nonneg zero_le_one).2 fun i => ?_⟩
  · rw [Subsingleton.elim i 0, Real.norm_eq_abs]; exact h0
  · fin_cases i
    · rw [Real.norm_eq_abs]; exact h1
    · rw [Real.norm_eq_abs]; exact h2

theorem image_val_hemi : Subtype.val '' hemi = sphere3 ∩ Q3 := by
  ext v
  constructor
  · rintro ⟨p, hp, rfl⟩; exact ⟨hp, p.2⟩
  · intro hv; exact ⟨⟨v, hv.2⟩, hv.1, rfl⟩

/-- **The hemisphere is compact.** -/
theorem isCompact_hemi : IsCompact hemi := by
  rw [Topology.IsEmbedding.subtypeVal.isCompact_iff, image_val_hemi]
  exact isCompact_sphere3.inter_right (quadrant_isClosed 1 Wq 0)

theorem isClosed_equator : IsClosed equator :=
  isClosed_hemi.inter (isClosed_eq ((continuous_apply 0).comp
    (continuous_fst.comp continuous_subtype_val)) continuous_const)

/-- **The equator is compact.** -/
theorem isCompact_equator : IsCompact equator :=
  isCompact_hemi.of_isClosed_subset isClosed_equator fun _ hp => hp.1

/-- The point `(0, 1, 0)` of the equator. -/
def pt0 : Q3 := ⟨mk3 0 1 0, fun i => by rw [Subsingleton.elim i 0]; exact le_rfl⟩

theorem pt0_mem_equator : pt0 ∈ equator :=
  ⟨by change nsq (mk3 0 1 0) = 1; rw [nsq_eq]; simp, rfl⟩

theorem equator_nonempty : equator.Nonempty := ⟨pt0, pt0_mem_equator⟩

end E8W

end Polyfold
