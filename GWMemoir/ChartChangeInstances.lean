import GWMemoir.ChartChange
import GWMemoir.PullbackBounded
import GWMemoir.CompletenessForms

/-!
# The change of atlas on the constant maps from `sphere3`

HWZ, *Applications of Polyfold Theory I*, Memoirs AMS 248, no. 1179, §1.2 (p. 7) and §2.4
(p. 51): for two atlases `A`, `B` of one map, `ξ ↦ ξ` is bounded between the fibre spaces.

* `ChartsOnto X`: the charts of `X` are onto `ℝ²` (`sphere3`: `S2_target`).  Then the disc maps
  `p ↦ discPt z ε p` are smooth on the whole strip, and the transitions
  `dtrans z ε z' ε' = placeInv' ∘ (chart_{z'} ∘ chart_z⁻¹) ∘ place` are smooth, injective, with
  invertible derivative, on the open set where they are defined.
* `chartPiece`: for a smooth `ρ` on `S` with `tsupport ρ` in the disc of `(z', ε')`, the
  coefficient `discCut · (ρ ∘ discPt) / (discCut ∘ dtrans) · (T_{z,z'} e_d)_{d'}` is smooth with
  compact support, and `dtrans` agrees on its support with a globally smooth map: a
  `ChartChange` of `GWMemoir.ChartChange`.
* **`pullbackBounded_refl_const`**: on a surface without nodes whose charts are onto `ℝ²`, for a
  constant map and any two atlases `A`, `B`, `PullbackBounded J δs h0 hmono A B (Iso.refl _)`.
  The operator: a smooth partition of unity `ρ_j` on `S` subordinate to the discs of `B`, and
  `(Rv)_{i,d,k} = ∑_{j,d'} a_{ijdd'} · (v_{j,d',k} ∘ trans_{ij})`, bounded on `H^{2,δ₀}` by
  `ChartChange.op`.
* `sphere3_pullbackBounded`: the instance on the constant maps from `sphere3`.
-/

set_option maxSynthPendingDepth 3
set_option linter.unusedSectionVars false

open scoped Manifold ContDiff Topology
open Set Function Filter MeasureTheory
open Polyfold Polyfold.CylinderSobolev

noncomputable section

namespace GWMemoir

/-! ## 1. Smooth transitions between disc charts -/

section Transition

variable {m : ℕ} {X : NodalSurface m}

variable (X) in
/-- The charts of `X` are onto `ℝ²`. -/
def ChartsOnto : Prop := ∀ z : X.S, (extChartAt 𝓘(ℝ, E2) z).target = univ

theorem sphere3_chartsOnto : ChartsOnto sphere3 := S2_target

variable (hT : ChartsOnto X)

lemma contDiff_single2 (d : Fin 2) : ContDiff ℝ ∞ fun a : ℝ => EuclideanSpace.single d a := by
  have : (fun a : ℝ => EuclideanSpace.single d a) = fun a => a • EuclideanSpace.single d (1 : ℝ) :=
    funext fun a => single_eq_smul d a
  rw [this]; fun_prop

lemma contDiff_place (z : X.S) (ε : ℝ) : ContDiff ℝ ∞ (X.place z ε) := by
  unfold NodalSurface.place
  have h0 := contDiff_single2 0
  have h1 := contDiff_single2 1
  exact contDiff_const.add (((h0.comp contDiff_fst).add
    (h1.comp (contDiff_snd.sub contDiff_const))).const_smul ε)

lemma contDiff_placeInv (z : X.S) (ε : ℝ) : ContDiff ℝ ∞ (placeInv (X := X) z ε) := by
  unfold placeInv
  have hp : ∀ j : Fin 2, ContDiff ℝ ∞ fun w : E2 => w j := fun j =>
    (EuclideanSpace.proj j : E2 →L[ℝ] ℝ).contDiff
  have hs : ContDiff ℝ ∞ fun w : E2 => ε⁻¹ • (w - extChartAt 𝓘(ℝ, E2) z z) :=
    (contDiff_id.sub contDiff_const).const_smul ε⁻¹
  exact ((hp 0).comp hs).prodMk (((hp 1).comp hs).add contDiff_const)

include hT in
lemma mem_target (z : X.S) (w : E2) : w ∈ (extChartAt 𝓘(ℝ, E2) z).target := by
  rw [hT z]; trivial

include hT in
lemma discPt_mem_source (z : X.S) (ε : ℝ) (p : ℝ × ℝ) :
    X.discPt z ε p ∈ (extChartAt 𝓘(ℝ, E2) z).source :=
  (extChartAt 𝓘(ℝ, E2) z).map_target (mem_target hT z _)

include hT in
lemma extChartAt_discPt (z : X.S) (ε : ℝ) (p : ℝ × ℝ) :
    extChartAt 𝓘(ℝ, E2) z (X.discPt z ε p) = X.place z ε p :=
  (extChartAt 𝓘(ℝ, E2) z).right_inv (mem_target hT z _)

include hT in
lemma contMDiff_extChartAt_symm (z : X.S) :
    ContMDiff 𝓘(ℝ, E2) 𝓘(ℝ, E2) ∞ (extChartAt 𝓘(ℝ, E2) z).symm := by
  have h := contMDiffOn_extChartAt_symm (I := 𝓘(ℝ, E2)) (n := ∞) z
  rw [hT z] at h
  exact contMDiffOn_univ.1 h

include hT in
lemma contMDiff_discPt (z : X.S) (ε : ℝ) :
    ContMDiff 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E2) ∞ (X.discPt z ε) :=
  (contMDiff_extChartAt_symm hT z).comp (contMDiff_iff_contDiff.2 (contDiff_place z ε))

include hT in
lemma continuous_discPt (z : X.S) (ε : ℝ) : Continuous (X.discPt z ε) :=
  (contMDiff_discPt hT z ε).continuous

include hT in
lemma contDiff_comp_discPt (ρ : C^∞⟮𝓘(ℝ, E2), X.S; 𝓘(ℝ), ℝ⟯) (z : X.S) (ε : ℝ) :
    ContDiff ℝ ∞ fun p => ρ (X.discPt z ε p) :=
  contMDiff_iff_contDiff.1 (ρ.contMDiff.comp (contMDiff_discPt hT z ε))

/-- The coordinate change `chart_{z'} ∘ chart_z⁻¹`. -/
def chartCC (z z' : X.S) : E2 → E2 := extChartAt 𝓘(ℝ, E2) z' ∘ (extChartAt 𝓘(ℝ, E2) z).symm

/-- Its domain. -/
def chartCCDom (z z' : X.S) : Set E2 :=
  {w | (extChartAt 𝓘(ℝ, E2) z).symm w ∈ (extChartAt 𝓘(ℝ, E2) z').source}

include hT in
lemma isOpen_ccDom (z z' : X.S) : IsOpen (chartCCDom z z') :=
  (isOpen_extChartAt_source z').preimage (contMDiff_extChartAt_symm hT z).continuous

include hT in
lemma contDiffOn_cc (z z' : X.S) : ContDiffOn ℝ ∞ (chartCC z z') (chartCCDom z z') := by
  have h := contDiffOn_ext_coord_change (I := 𝓘(ℝ, E2)) (n := ∞) z' z
  rw [PartialEquiv.trans_source, PartialEquiv.symm_source, hT z, univ_inter] at h
  exact h

/-- The transition from the strip coordinates of `(z, ε)` to those of `(z', ε')`. -/
def dtrans (z : X.S) (ε : ℝ) (z' : X.S) (ε' : ℝ) (p : ℝ × ℝ) : ℝ × ℝ :=
  placeInv z' ε' (chartCC z z' (X.place z ε p))

/-- Its domain: the points whose disc point lies in the chart at `z'`. -/
def dtDom (z : X.S) (ε : ℝ) (z' : X.S) : Set (ℝ × ℝ) :=
  {p | X.discPt z ε p ∈ (extChartAt 𝓘(ℝ, E2) z').source}

include hT in
lemma isOpen_dtDom (z : X.S) (ε : ℝ) (z' : X.S) : IsOpen (dtDom z ε z') :=
  (isOpen_extChartAt_source z').preimage (continuous_discPt hT z ε)

lemma dtrans_eq (z : X.S) (ε : ℝ) (z' : X.S) (ε' : ℝ) (p : ℝ × ℝ) :
    dtrans z ε z' ε' p = placeInv z' ε' (extChartAt 𝓘(ℝ, E2) z' (X.discPt z ε p)) := rfl

include hT in
lemma contDiffOn_trans (z : X.S) (ε : ℝ) (z' : X.S) (ε' : ℝ) :
    ContDiffOn ℝ ∞ (dtrans z ε z' ε') (dtDom z ε z') :=
  (contDiff_placeInv z' ε').comp_contDiffOn
    ((contDiffOn_cc hT z z').comp (contDiff_place z ε).contDiffOn fun _ hp => hp)

lemma discPt_trans {z : X.S} {ε : ℝ} {z' : X.S} {ε' : ℝ} (hε' : ε' ≠ 0) {p : ℝ × ℝ}
    (hp : p ∈ dtDom z ε z') : X.discPt z' ε' (dtrans z ε z' ε' p) = X.discPt z ε p := by
  rw [dtrans_eq, NodalSurface.discPt, place_placeInv z' hε']
  exact (extChartAt 𝓘(ℝ, E2) z').left_inv hp

include hT in
lemma trans_trans {z : X.S} {ε : ℝ} {z' : X.S} {ε' : ℝ} (hε : ε ≠ 0) (hε' : ε' ≠ 0)
    {p : ℝ × ℝ} (hp : p ∈ dtDom z ε z') : dtrans z' ε' z ε (dtrans z ε z' ε' p) = p := by
  rw [dtrans_eq z' ε' z ε, discPt_trans hε' hp, extChartAt_discPt hT, placeInv_place z hε]

include hT in
lemma trans_mem_tDom {z : X.S} {ε : ℝ} {z' : X.S} {ε' : ℝ} (hε' : ε' ≠ 0) {p : ℝ × ℝ}
    (hp : p ∈ dtDom z ε z') : dtrans z ε z' ε' p ∈ dtDom z' ε' z := by
  change X.discPt z' ε' _ ∈ (extChartAt 𝓘(ℝ, E2) z).source
  rw [discPt_trans hε' hp]; exact discPt_mem_source hT z ε p

include hT in
lemma injOn_trans {z : X.S} {ε : ℝ} {z' : X.S} {ε' : ℝ} (hε : ε ≠ 0) (hε' : ε' ≠ 0) :
    InjOn (dtrans z ε z' ε') (dtDom z ε z') := fun p hp p' hp' h => by
  rw [← trans_trans hT hε hε' hp, ← trans_trans hT hε hε' hp', h]

include hT in
/-- The derivative of a transition is invertible. -/
lemma det_trans_ne {z : X.S} {ε : ℝ} {z' : X.S} {ε' : ℝ} (hε : ε ≠ 0) (hε' : ε' ≠ 0)
    {p : ℝ × ℝ} (hp : p ∈ dtDom z ε z') : (fderiv ℝ (dtrans z ε z' ε') p).det ≠ 0 := by
  have hd1 : DifferentiableAt ℝ (dtrans z ε z' ε') p :=
    ((contDiffOn_trans hT z ε z' ε').contDiffAt
      ((isOpen_dtDom hT z ε z').mem_nhds hp)).differentiableAt
      (by simp)
  have hq := trans_mem_tDom hT hε' hp
  have hd2 : DifferentiableAt ℝ (dtrans z' ε' z ε) (dtrans z ε z' ε' p) :=
    ((contDiffOn_trans hT z' ε' z ε).contDiffAt
      ((isOpen_dtDom hT z' ε' z).mem_nhds hq)).differentiableAt (by simp)
  have hev : (dtrans z' ε' z ε ∘ dtrans z ε z' ε') =ᶠ[𝓝 p] id := by
    filter_upwards [(isOpen_dtDom hT z ε z').mem_nhds hp] with p' hp'
    exact trans_trans hT hε hε' hp'
  have hc := fderiv_comp p hd2 hd1
  rw [hev.fderiv_eq, fderiv_id] at hc
  set M := fderiv ℝ (dtrans z' ε' z ε) (dtrans z ε z' ε' p)
  set N := fderiv ℝ (dtrans z ε z' ε') p
  have h1 : LinearMap.det ((M : (ℝ × ℝ) →ₗ[ℝ] ℝ × ℝ) ∘ₗ (N : (ℝ × ℝ) →ₗ[ℝ] ℝ × ℝ)) = 1 := by
    have e : ((M : (ℝ × ℝ) →ₗ[ℝ] ℝ × ℝ) ∘ₗ (N : (ℝ × ℝ) →ₗ[ℝ] ℝ × ℝ)) = LinearMap.id :=
      LinearMap.ext fun v => (congrArg (fun T : (ℝ × ℝ) →L[ℝ] ℝ × ℝ => T v) hc).symm
    rw [e, LinearMap.det_id]
  rw [LinearMap.det_comp] at h1
  intro h0
  change LinearMap.det (N : (ℝ × ℝ) →ₗ[ℝ] ℝ × ℝ) = 0 at h0
  rw [h0, mul_zero] at h1
  exact zero_ne_one h1

include hT in
/-- The tangent coordinate change of `S` is the derivative of the coordinate change. -/
lemma tcc_eq (z z' : X.S) (ε : ℝ) (p : ℝ × ℝ) :
    tangentCoordChange 𝓘(ℝ, E2) z z' (X.discPt z ε p) =
      fderiv ℝ (chartCC z z') (X.place z ε p) := by
  rw [tangentCoordChange_def, extChartAt_discPt hT, modelWithCornersSelf_coe, range_id,
    fderivWithin_univ]
  rfl

end Transition

/-! ## 2. The pieces of a change of atlas -/

section Piece

variable {m : ℕ} {X : NodalSurface m} (hT : ChartsOnto X)

lemma contDiff_of_open_cover {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : ℝ × ℝ → F} {V W : Set (ℝ × ℝ)} (hV : IsOpen V) (hW : IsOpen W) (hVW : ∀ x, x ∈ V ∨ x ∈ W)
    (hf : ContDiffOn ℝ ∞ f V) (h0 : ∀ x ∈ W, f x = 0) : ContDiff ℝ ∞ f := by
  refine contDiff_iff_contDiffAt.2 fun x => ?_
  rcases hVW x with hx | hx
  · exact hf.contDiffAt (hV.mem_nhds hx)
  · refine (contDiffAt_const (c := (0 : F))).congr_of_eventuallyEq ?_
    filter_upwards [hW.mem_nhds hx] with y hy using h0 y hy

lemma contDiff_discCut : ContDiff ℝ ∞ discCut := by
  unfold discCut; exact Real.smoothTransition.contDiff.comp (by fun_prop)

/-- The closed disc `r² ≤ 1/8` of the strip. -/
def closedDisc : Set (ℝ × ℝ) := {p | p.1 ^ 2 + (p.2 - 1 / 2) ^ 2 ≤ 1 / 8}

lemma isCompact_closedDisc : IsCompact closedDisc := by
  refine (isCompact_Icc.prod isCompact_Icc : IsCompact (Icc (-1 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 2))
    |>.of_isClosed_subset (isClosed_le (by fun_prop) continuous_const) fun p hp => ?_
  simp only [closedDisc, mem_ofPred_eq] at hp
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> nlinarith [sq_nonneg p.1, sq_nonneg (p.2 - 1 / 2)]

lemma closedDisc_sub : closedDisc ⊆ openStrip := by
  intro p hp
  simp only [closedDisc, mem_ofPred_eq] at hp
  refine ⟨mem_univ _, ?_, ?_⟩ <;> nlinarith [sq_nonneg p.1, sq_nonneg (p.2 - 1 / 2)]

lemma discD_sub_closedDisc : discD ⊆ closedDisc := fun p hp => by
  simp only [discD, closedDisc, mem_ofPred_eq] at hp ⊢; linarith

lemma discCut_eq_zero {p : ℝ × ℝ} (hp : p ∉ closedDisc) : discCut p = 0 := by
  by_contra h; exact hp (discD_sub_closedDisc (discD_of_discCut_ne h))

/-- The disc of `(z', ε')` in `S`: the points whose strip coordinate lies in `r² < 1/8`. -/
def discSet (z' : X.S) (ε' : ℝ) : Set X.S :=
  (extChartAt 𝓘(ℝ, E2) z').source ∩
    (fun y => placeInv z' ε' (extChartAt 𝓘(ℝ, E2) z' y)) ⁻¹' discD

lemma isOpen_discSet (z' : X.S) (ε' : ℝ) : IsOpen (discSet z' ε') :=
  ((continuous_placeInv z' ε').comp_continuousOn (continuousOn_extChartAt z')).isOpen_inter_preimage
    (isOpen_extChartAt_source z') isOpen_discD

/-- The open set of the strip of `(z, ε)` mapped into the disc of `(z', ε')`. -/
def pieceDom (z : X.S) (ε : ℝ) (z' : X.S) (ε' : ℝ) : Set (ℝ × ℝ) :=
  X.discPt z ε ⁻¹' discSet z' ε'

include hT in
lemma isOpen_pieceDom (z : X.S) (ε : ℝ) (z' : X.S) (ε' : ℝ) : IsOpen (pieceDom z ε z' ε') :=
  (isOpen_discSet z' ε').preimage (continuous_discPt hT z ε)

lemma pieceDom_sub {z : X.S} {ε : ℝ} {z' : X.S} {ε' : ℝ} {p : ℝ × ℝ}
    (hp : p ∈ pieceDom z ε z' ε') : p ∈ dtDom z ε z' ∧ dtrans z ε z' ε' p ∈ discD := hp

/-- The coefficient of the piece `(d, d')`:
`discCut · (ρ ∘ discPt) / (discCut ∘ dtrans) · (T_{z,z'} e_d)_{d'}`. -/
def coef (ρ : X.S → ℝ) (z : X.S) (ε : ℝ) (z' : X.S) (ε' : ℝ) (d d' : Fin 2) (p : ℝ × ℝ) : ℝ :=
  discCut p * ρ (X.discPt z ε p) / discCut (dtrans z ε z' ε' p) *
    (fderiv ℝ (chartCC z z') (X.place z ε p) (EuclideanSpace.single d 1)) d'

/-- The compact set of the piece. -/
def pieceK (ρ : X.S → ℝ) (z : X.S) (ε : ℝ) : Set (ℝ × ℝ) :=
  closedDisc ∩ X.discPt z ε ⁻¹' tsupport ρ

include hT in
lemma isCompact_pieceK (ρ : X.S → ℝ) (z : X.S) (ε : ℝ) : IsCompact (pieceK ρ z ε) :=
  isCompact_closedDisc.inter_right ((isClosed_tsupport ρ).preimage (continuous_discPt hT z ε))

lemma pieceK_sub {ρ : X.S → ℝ} {z : X.S} {ε : ℝ} {z' : X.S} {ε' : ℝ}
    (hρ : tsupport ρ ⊆ discSet z' ε') : pieceK ρ z ε ⊆ pieceDom z ε z' ε' :=
  fun _ hp => hρ hp.2

include hT in
lemma tsupport_coef_sub (ρ : X.S → ℝ) (z : X.S) (ε : ℝ) (z' : X.S) (ε' : ℝ) (d d' : Fin 2) :
    tsupport (coef ρ z ε z' ε' d d') ⊆ pieceK ρ z ε := by
  refine closure_minimal (fun p hp => ?_) (isCompact_pieceK hT ρ z ε).isClosed
  refine ⟨by_contra fun h => hp ?_, by_contra fun h => hp ?_⟩
  · simp [coef, discCut_eq_zero h]
  · simp [coef, image_eq_zero_of_notMem_tsupport h]

include hT in
lemma contDiff_coef (ρ : C^∞⟮𝓘(ℝ, E2), X.S; 𝓘(ℝ), ℝ⟯) (z : X.S) (ε : ℝ) (z' : X.S) (ε' : ℝ)
    (hρ : tsupport ρ ⊆ discSet z' ε') (d d' : Fin 2) : ContDiff ℝ ∞ (coef ρ z ε z' ε' d d') := by
  set V := pieceDom z ε z' ε'
  have hVo : IsOpen V := isOpen_pieceDom hT z ε z' ε'
  have hW : IsOpen (X.discPt z ε ⁻¹' tsupport ρ)ᶜ :=
    ((isClosed_tsupport ρ).preimage (continuous_discPt hT z ε)).isOpen_compl
  refine contDiff_of_open_cover hVo hW (fun p => ?_) ?_ ?_
  · by_cases h : X.discPt z ε p ∈ tsupport ρ
    · exact Or.inl (hρ h)
    · exact Or.inr h
  · have hdt : ContDiffOn ℝ ∞ (dtrans z ε z' ε') V :=
      (contDiffOn_trans hT z ε z' ε').mono fun p hp => (pieceDom_sub hp).1
    have hcut : ContDiffOn ℝ ∞ (fun p => discCut (dtrans z ε z' ε' p)) V :=
      contDiff_discCut.comp_contDiffOn hdt
    have hne : ∀ p ∈ V, discCut (dtrans z ε z' ε' p) ≠ 0 := fun p hp =>
      (discCut_pos (pieceDom_sub hp).2).ne'
    have hF : ContDiffOn ℝ ∞ (fderiv ℝ (chartCC z z')) (chartCCDom z z') :=
      (contDiffOn_cc hT z z').fderiv_of_isOpen (isOpen_ccDom hT z z') (by simp)
    have hF' : ContDiffOn ℝ ∞ (fun p => (fderiv ℝ (chartCC z z') (X.place z ε p)
        (EuclideanSpace.single d 1)) d') V := by
      have h1 : ContDiffOn ℝ ∞ (fun p => fderiv ℝ (chartCC z z') (X.place z ε p)) V :=
        hF.comp (contDiff_place z ε).contDiffOn fun p hp => (pieceDom_sub hp).1
      exact (EuclideanSpace.proj d' : E2 →L[ℝ] ℝ).contDiff.comp_contDiffOn
        (h1.clm_apply contDiffOn_const)
    exact ((contDiff_discCut.contDiffOn.mul (contDiff_comp_discPt hT ρ z ε).contDiffOn).div
      hcut hne).mul hF'
  · intro p hp
    simp [coef, image_eq_zero_of_notMem_tsupport hp]

include hT in
/-- **A piece of the change of atlas is a `ChartChange`**: `dtrans` agrees on `pieceK` with a
globally smooth map. -/
theorem exists_chartChange {ρ : X.S → ℝ} {z : X.S} {ε : ℝ} {z' : X.S} {ε' : ℝ} (hε : ε ≠ 0)
    (hε' : ε' ≠ 0) (hρ : tsupport ρ ⊆ discSet z' ε') :
    ∃ D : ChartChange, D.K = pieceK ρ z ε ∧ ∀ p ∈ D.K, D.ψ p = dtrans z ε z' ε' p := by
  set V := pieceDom z ε z' ε'
  set K := pieceK ρ z ε
  have hVo : IsOpen V := isOpen_pieceDom hT z ε z' ε'
  have hKc : IsCompact K := isCompact_pieceK hT ρ z ε
  have hKV : K ⊆ V := pieceK_sub hρ
  obtain ⟨χ, h0, h1, -⟩ := exists_contMDiffMap_zero_one_nhds_of_isClosed 𝓘(ℝ, ℝ × ℝ) (n := ⊤)
    hVo.isClosed_compl hKc.isClosed (disjoint_compl_left_iff_subset.2 hKV)
  obtain ⟨O, hOo, hVO, hO⟩ := eventually_nhdsSet_iff_exists.1 h0
  obtain ⟨O', hO'o, hKO', hO'⟩ := eventually_nhdsSet_iff_exists.1 h1
  have hχ : ContDiff ℝ ∞ (χ : ℝ × ℝ → ℝ) := contMDiff_iff_contDiff.1 χ.contMDiff
  set ψ : ℝ × ℝ → ℝ × ℝ := fun p => χ p • dtrans z ε z' ε' p
  have hψ : ContDiff ℝ ∞ ψ := by
    refine contDiff_of_open_cover hVo hOo (fun p => ?_) ?_ fun p hp => by simp [ψ, hO p hp]
    · by_cases h : p ∈ V
      · exact Or.inl h
      · exact Or.inr (hVO h)
    · exact hχ.contDiffOn.smul
        ((contDiffOn_trans hT z ε z' ε').mono fun p hp => (pieceDom_sub hp).1)
  have hψeq : ∀ p ∈ O', ψ p = dtrans z ε z' ε' p := fun p hp => by simp [ψ, hO' p hp]
  have hev : ∀ p ∈ K, ψ =ᶠ[𝓝 p] dtrans z ε z' ε' := fun p hp => by
    filter_upwards [hO'o.mem_nhds (hKO' hp)] with p' hp' using hψeq p' hp'
  refine ⟨{
    K := K
    ψ := ψ
    isCompact := hKc
    sub := fun p hp => closedDisc_sub hp.1
    smooth := hψ
    injOn := fun p hp p' hp' h => by
      rw [hψeq p (hKO' hp), hψeq p' (hKO' hp')] at h
      exact injOn_trans hT hε hε' (pieceDom_sub (hKV hp)).1 (pieceDom_sub (hKV hp')).1 h
    det_ne := fun p hp => by
      rw [(hev p hp).fderiv_eq]
      exact det_trans_ne hT hε hε' (pieceDom_sub (hKV hp)).1
    mapsTo := fun p hp => by
      rw [hψeq p (hKO' hp)]
      exact discD_sub (pieceDom_sub (hKV hp)).2 }, rfl, fun p hp => hψeq p (hKO' hp)⟩

end Piece

/-! ## 3. Two atlases of a constant map -/

section Atlases

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {Q : Type} [TopologicalSpace Q] [ChartedSpace E Q] [IsManifold 𝓘(ℝ, E) ∞ Q]
variable {m : ℕ} {X : NodalSurface m} (hX : X.nodes = ∅) (hT : ChartsOnto X)
  {q : Q} {u : X.S → Q} (hu : ∀ x, u x = q)

include hu in
lemma formAt_of_const (z : X.S) (ξ : Form E X) (y : X.S) :
    formAt u z ξ y = (ξ y).comp (tangentCoordChange 𝓘(ℝ, E2) z y y) := by
  ext v
  simp only [formAt, ContinuousLinearMap.comp_apply, hu]
  exact tangentCoordChange_self (mem_extChartAt_source q)

include hX hT in
/-- A smooth partition of unity on `S` subordinate to the discs of an atlas. -/
theorem exists_partition (B : SectionAtlas (E := E) X u) :
    ∃ ρ : SmoothPartitionOfUnity (Fin B.nd) 𝓘(ℝ, E2) X.S univ,
      ρ.IsSubordinate fun j => discSet (B.center j) (B.ε j) := by
  refine SmoothPartitionOfUnity.exists_isSubordinate _ isClosed_univ _
    (fun j => isOpen_discSet _ _) fun y _ => ?_
  rcases B.cover y with ⟨j, p, hp, rfl⟩ | ⟨j, -⟩
  · refine mem_iUnion.2 ⟨j, discPt_mem_source hT _ _ p, ?_⟩
    change placeInv _ _ (extChartAt 𝓘(ℝ, E2) _ (X.discPt _ _ p)) ∈ discD
    rw [extChartAt_discPt hT, placeInv_place _ (B.ε_pos j).ne']
    exact mem_discD_of_core hp
  · obtain ⟨a, ha, -⟩ := B.node_nodal j
    rw [hX] at ha; exact absurd ha (notMem_empty a)

lemma sum_fin2_coord (w : E2) (L : E2 →L[ℝ] ℝ) :
    ∑ d' : Fin 2, w d' * L (EuclideanSpace.single d' 1) = L w := by
  conv_rhs => rw [← single_add_single_eq w, single_eq_smul 0 (w 0), single_eq_smul 1 (w 1)]
  rw [Fin.sum_univ_two, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]

variable {A B : SectionAtlas (E := E) X u}

include hu hT in
/-- One piece of the change of atlas, pointwise. -/
lemma piece_eq {i : Fin A.nd} {j : Fin B.nd} {ρ : X.S → ℝ}
    (hρ : tsupport ρ ⊆ discSet (B.center j) (B.ε j)) {D : ChartChange}
    (hDK : D.K = pieceK ρ (A.center i) (A.ε i))
    (hDψ : ∀ p ∈ D.K, D.ψ p = dtrans (A.center i) (A.ε i) (B.center j) (B.ε j) p)
    (d d' : Fin 2) (k : Fin (Module.finrank ℝ E)) (ξ : Form E X) (p : ℝ × ℝ) :
    coef ρ (A.center i) (A.ε i) (B.center j) (B.ε j) d d' p *
        formDiscRep B j d' k ξ (D.ψ p) =
      discCut p * ρ (X.discPt (A.center i) (A.ε i) p) *
        ((tangentCoordChange 𝓘(ℝ, E2) (A.center i) (B.center j)
          (X.discPt (A.center i) (A.ε i) p) (EuclideanSpace.single d 1)) d' *
        crd k (ξ (X.discPt (A.center i) (A.ε i) p) (tangentCoordChange 𝓘(ℝ, E2) (B.center j)
          (X.discPt (A.center i) (A.ε i) p) (X.discPt (A.center i) (A.ε i) p)
          (EuclideanSpace.single d' 1)))) := by
  by_cases hp : p ∈ pieceK ρ (A.center i) (A.ε i)
  · have hpD : p ∈ pieceDom (A.center i) (A.ε i) (B.center j) (B.ε j) := pieceK_sub hρ hp
    rw [hDψ p (hDK ▸ hp)]
    have hy := discPt_trans (B.ε_pos j).ne' (pieceDom_sub hpD).1
    have hne := (discCut_pos (pieceDom_sub hpD).2).ne'
    simp only [formDiscRep, coef, hy, formAt_of_const hu, ContinuousLinearMap.comp_apply]
    rw [tcc_eq hT (A.center i) (B.center j) (A.ε i) p]
    field_simp
  · have h0 : coef ρ (A.center i) (A.ε i) (B.center j) (B.ε j) d d' p = 0 :=
      image_eq_zero_of_notMem_tsupport fun h => hp (tsupport_coef_sub hT _ _ _ _ _ _ _ h)
    rw [h0, zero_mul]
    by_cases hc : p ∈ closedDisc
    · have : ρ (X.discPt (A.center i) (A.ε i) p) = 0 :=
        image_eq_zero_of_notMem_tsupport fun h => hp ⟨hc, h⟩
      rw [this]; ring
    · rw [discCut_eq_zero hc]; ring

include hu hT in
/-- The pieces of one `j`, summed over the directions `d'`. -/
lemma piece_sum_eq {i : Fin A.nd} {j : Fin B.nd} {ρ : X.S → ℝ}
    (hρ : tsupport ρ ⊆ discSet (B.center j) (B.ε j)) {D : ChartChange}
    (hDK : D.K = pieceK ρ (A.center i) (A.ε i))
    (hDψ : ∀ p ∈ D.K, D.ψ p = dtrans (A.center i) (A.ε i) (B.center j) (B.ε j) p)
    (d : Fin 2) (k : Fin (Module.finrank ℝ E)) (ξ : Form E X) (p : ℝ × ℝ) :
    ∑ d' : Fin 2, coef ρ (A.center i) (A.ε i) (B.center j) (B.ε j) d d' p *
        formDiscRep B j d' k ξ (D.ψ p) =
      ρ (X.discPt (A.center i) (A.ε i) p) * formDiscRep A i d k ξ p := by
  rw [Finset.sum_congr rfl fun d' _ => piece_eq hT hu hρ hDK hDψ d d' k ξ p]
  by_cases hy : ρ (X.discPt (A.center i) (A.ε i) p) = 0
  · simp [hy]
  have hys : X.discPt (A.center i) (A.ε i) p ∈ (extChartAt 𝓘(ℝ, E2) (B.center j)).source :=
    (hρ (subset_tsupport ρ hy)).1
  rw [← Finset.mul_sum]
  have e := sum_fin2_coord (tangentCoordChange 𝓘(ℝ, E2) (A.center i) (B.center j)
    (X.discPt (A.center i) (A.ε i) p) (EuclideanSpace.single d 1))
    ((crd k).toContinuousLinearMap.comp ((ξ (X.discPt (A.center i) (A.ε i) p)).comp
      (tangentCoordChange 𝓘(ℝ, E2) (B.center j) (X.discPt (A.center i) (A.ε i) p)
        (X.discPt (A.center i) (A.ε i) p))))
  simp only [ContinuousLinearMap.comp_apply, LinearMap.coe_toContinuousLinearMap'] at e
  rw [e, tangentCoordChange_comp ⟨⟨discPt_mem_source hT (A.center i) (A.ε i) p, hys⟩,
    mem_extChartAt_source _⟩]
  simp only [formDiscRep, formAt_of_const hu, ContinuousLinearMap.comp_apply]
  ring

end Atlases

/-! ## 4. `PullbackBounded` for two atlases of a constant map -/

section Main

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {Q : Type} [TopologicalSpace Q] [ChartedSpace E Q] [IsManifold 𝓘(ℝ, E) ∞ Q]
variable (J : AlmostComplexStructure E Q) {om : SymplecticForm E Q} {m k : ℕ} {δ : ℝ}
  {δs : ℕ → ℝ} {h0 : 0 ≤ δs 0} {hmono : StrictMono δs}

lemma coeFn_sum_sum {ι ι' : Type} [Fintype ι] [Fintype ι'] (F : ι → ι' → Lp ℝ 2 cyl) :
    (⇑(∑ j, ∑ d', F j d') : ℝ × ℝ → ℝ) =ᵐ[cyl] fun x => ∑ j, ∑ d', F j d' x := by
  filter_upwards [Lp.coeFn_fun_finsetSum Finset.univ fun j => ∑ d', F j d',
    ae_all_iff.2 fun j => Lp.coeFn_fun_finsetSum Finset.univ (F j)] with x h1 h2
  rw [h1]
  exact Finset.sum_congr rfl fun j _ => h2 j

/-- **The change of atlas on the fibres of a constant map**: on a surface without nodes whose
charts are onto `ℝ²`, for a constant map and any two atlases `A`, `B`, the identity is bounded
between the fibre spaces in `A` and `B` (`PullbackBounded` for `Iso.refl`). -/
theorem pullbackBounded_refl_const {α : StableMap om m k δ} (hX : α.dom.nodes = ∅)
    (hT : ChartsOnto α.dom) {q : Q} (hu : ∀ x, α.u x = q)
    (A B : SectionAtlas (E := E) α.dom α.u) :
    PullbackBounded J δs h0 hmono A B (StableMap.Iso.refl α) := by
  obtain ⟨ρ, hρ⟩ := exists_partition hX hT B
  have hρ' : ∀ j, tsupport (ρ j) ⊆ discSet (B.center j) (B.ε j) := hρ
  choose D hDK hDψ using fun (i : Fin A.nd) (j : Fin B.nd) =>
    exists_chartChange hT (ρ := ρ j) (A.ε_pos i).ne' (B.ε_pos j).ne' (hρ' j)
  have hδ := Neck.δ_nonneg δs h0 hmono 0
  have hc : ∀ i j d d', ContDiff ℝ ∞
      (coef (ρ j) (A.center i) (A.ε i) (B.center j) (B.ε j) d d') :=
    fun i j d d' => contDiff_coef hT (ρ j) _ _ _ _ (hρ' j) d d'
  have hs : ∀ i j d d', tsupport (coef (ρ j) (A.center i) (A.ε i) (B.center j) (B.ε j) d d') ⊆
      (D i j).K := fun i j d d' => (hDK i j).symm ▸ tsupport_coef_sub hT _ _ _ _ _ d d'
  let Op : ∀ (i : Fin A.nd) (j : Fin B.nd) (d d' : Fin 2), H 2 hδ →L[ℝ] H 2 hδ :=
    fun i j d d' => (D i j).op 2 hδ (hc i j d d') (hs i j d d') hδ
  let P : ∀ (j : Fin B.nd) (d' : Fin 2) (kk : Fin (Module.finrank ℝ E)),
      (fibreBlocks B δs h0 hmono) 0 →L[ℝ] H 2 hδ :=
    fun j d' kk => (ContinuousLinearMap.proj (j, d', kk)).comp (ContinuousLinearMap.fst ℝ _ _)
  let R : (fibreBlocks B δs h0 hmono) 0 →L[ℝ] (fibreBlocks A δs h0 hmono) 0 :=
    (ContinuousLinearMap.pi fun idk : Fin A.nd × Fin 2 × Fin (Module.finrank ℝ E) =>
      ∑ j, ∑ d', (Op idk.1 j idk.2.1 d').comp (P j d' idk.2.2)).prod 0
  refine pullbackBounded_of_blockMap J (StableMap.Iso.refl α) R fun ξ v _ hv => ?_
  rw [NodalSurface.Iso.pullbackForm_of_eq_id _ fun _ => rfl]
  refine ⟨fun i d kk => ?_, fun j => ?_⟩
  · have e : H.val (fDiscBlock (R v) i d kk) =
        ∑ j, ∑ d', H.val (Op i j d d' (fDiscBlock v j d' kk)) := by
      have e0 : fDiscBlock (R v) i d kk = ∑ j, ∑ d', Op i j d d' (fDiscBlock v j d' kk) := by
        have e1 : fDiscBlock (R v) i d kk = (∑ j, ∑ d', (Op i j d d').comp (P j d' kk)) v := rfl
        rw [e1, _root_.sum_apply]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [_root_.sum_apply]
        rfl
      rw [e0]
      exact (map_sum (valCLM 2 hδ) _ _).trans (Finset.sum_congr rfl fun j _ =>
        map_sum (valCLM 2 hδ) _ _)
    rw [e]
    have h1 : ∀ᵐ x ∂cyl, ∀ j d', (H.val (Op i j d d' (fDiscBlock v j d' kk)) : ℝ × ℝ → ℝ) x =
        coef (ρ j) (A.center i) (A.ε i) (B.center j) (B.ε j) d d' x *
          formDiscRep B j d' kk ξ ((D i j).ψ x) :=
      ae_all_iff.2 fun j => ae_all_iff.2 fun d' =>
        ((D i j).coeFn_op (hc i j d d') (hs i j d d') hδ _).trans
          (ChartChange.comp_congr (hs i j d d') (hv.1 j d' kk))
    filter_upwards [coeFn_sum_sum fun j d' => H.val (Op i j d d' (fDiscBlock v j d' kk)), h1]
      with x hx1 hx2
    rw [hx1]
    simp only [hx2]
    rw [Finset.sum_congr rfl fun j _ => piece_sum_eq hT hu (hρ' j) (hDK i j) (hDψ i j) d kk ξ x,
      ← Finset.sum_mul]
    have h := ρ.sum_eq_one (x := α.dom.discPt (A.center i) (A.ε i) x) (mem_univ _)
    rw [finsum_eq_sum_of_fintype] at h
    rw [h, one_mul]
  · obtain ⟨a, ha, -⟩ := A.node_nodal j
    rw [hX] at ha; exact absurd ha (notMem_empty a)

/-- **Instance**: the constant maps from the three-pointed sphere, any two atlases. -/
theorem sphere3_pullbackBounded (q : Q) (A B : SectionAtlas (E := E)
    (constStableMap om q k δ).dom (constStableMap om q k δ).u) :
    PullbackBounded J δs h0 hmono A B (StableMap.Iso.refl (constStableMap om q k δ)) :=
  pullbackBounded_refl_const J rfl sphere3_chartsOnto (q := q) (fun _ => rfl) A B

end Main

end GWMemoir
