import GWMemoir.LinearCR
import GWMemoir.SphereStability

/-!
# The linearized Cauchy–Riemann operator at a constant map: range and kernel

HWZ, *Applications of Polyfold Theory I*, Memoirs AMS 248, no. 1179, §4.  Continuation of
`GWMemoir.LinearCR`: on a surface without nodes whose charts are onto `ℝ²`, for the constant map
`u ≡ q`, any almost complex structure `J` on `Q` and any atlas,

* **`isFormRep_rOp`**: for the representative `v` of a section `η` of class `(3, δ₀)`, `η` is
  differentiable (`H³ ⊂ C¹`, `exists_C1_rep`) and `R v` is the representative of the form `dη`;
* **`isFormRep_linOp`**: `D v` is the representative of `½ (dη + J(q) ∘ dη ∘ j)`, which is
  anti-linear, so **`linCR`**: `D` is a bounded operator from `H^{3,δ₀}_c(S, u*TQ)` to the fibre
  `H^{2,δ₀}` of `W` over `u` (`GWMemoir.Fibres`);
* `D v = 0` makes `η` holomorphic, `dη ∘ j = J(q) ∘ dη` (`holo_of_linOp_eq_zero`);
* on `sphere3`, **Liouville** in the stereographic chart `σ₁` (`const_of_CR`) gives
  **`linCR_ker_sphere3`**: the kernel of `D` is the constants, and **`linCR_ker_uSpace`**: on
  `E_u` it is the constants in `⋂ H_{u(z)}`; with the three constraints `H = 0` at the marked
  points it is `0` (`linCR_ker_three_points`).
-/

set_option maxSynthPendingDepth 3
set_option linter.unusedSectionVars false

open scoped Manifold ContDiff Topology
open Set Function Filter MeasureTheory
open Polyfold Polyfold.CylinderSobolev

noncomputable section

namespace GWMemoir

/-! ## 1. The circle `r² = 1/8` is null -/

section Null

/-- The exterior of the disc of the cut-off, `r² > 1/8`. -/
def extD : Set (ℝ × ℝ) := {p | 1 / 8 < p.1 ^ 2 + (p.2 - 1 / 2) ^ 2}

lemma isOpen_extD : IsOpen extD := isOpen_lt continuous_const (by fun_prop)

lemma ae_openStrip : ∀ᵐ x ∂cyl, x ∈ openStrip := by
  rw [ae_iff]
  have e : {a : ℝ × ℝ | ¬ a ∈ openStrip} = univ ×ˢ (Ioo (0 : ℝ) 1)ᶜ := by
    ext a; simp [openStrip]
  rw [e, cyl, Measure.prod_prod, Measure.restrict_apply measurableSet_Ioo.compl]
  have e2 : (Ioo (0 : ℝ) 1)ᶜ ∩ Ioc 0 1 = {1} := by
    ext t
    simp only [mem_inter_iff, mem_compl_iff, mem_Ioo, mem_Ioc, mem_singleton_iff]
    constructor
    · rintro ⟨h1, h2, h3⟩; by_contra h; exact h1 ⟨h2, lt_of_le_of_ne h3 h⟩
    · rintro rfl; norm_num
  rw [e2, Real.volume_singleton, mul_zero]

lemma ae_ne_circle : ∀ᵐ x ∂cyl, x.1 ^ 2 + (x.2 - 1 / 2) ^ 2 ≠ 1 / 8 := by
  rw [ae_iff]
  have hm : MeasurableSet {a : ℝ × ℝ | ¬ a.1 ^ 2 + (a.2 - 1 / 2) ^ 2 ≠ 1 / 8} := by
    simp only [ne_eq, not_not]
    exact (isClosed_eq (by fun_prop) continuous_const).measurableSet
  rw [cyl, Measure.measure_prod_null hm]
  refine Eventually.of_forall fun s => ?_
  set c := 1 / 8 - s ^ 2
  have hsub : Prod.mk s ⁻¹' {a : ℝ × ℝ | ¬ a.1 ^ 2 + (a.2 - 1 / 2) ^ 2 ≠ 1 / 8} ⊆
      {1 / 2 + √c, 1 / 2 - √c} := by
    intro t ht
    simp only [mem_preimage, ne_eq, not_not, mem_ofPred_eq] at ht
    have h1 : (t - 1 / 2) ^ 2 = c := by simp only [c]; linarith
    have hc : 0 ≤ c := h1 ▸ sq_nonneg _
    have h2 : |t - 1 / 2| = √c := by rw [← Real.sqrt_sq_eq_abs, h1]
    rcases abs_eq (Real.sqrt_nonneg c) |>.1 h2 with h | h
    · left; linarith
    · right; change t = _; linarith
  have hfin : ({1 / 2 + √c, 1 / 2 - √c} : Set ℝ).Finite := toFinite _
  exact nonpos_iff_eq_zero.1 ((Measure.restrict_apply_le _ _).trans
    ((measure_mono hsub).trans (hfin.measure_zero volume).le))

/-- Almost every point of the cylinder lies in the open strip, inside or outside the circle. -/
lemma ae_disc_or_ext : ∀ᵐ x ∂cyl, x ∈ openStrip ∧ (x ∈ discD ∨ x ∈ extD) := by
  filter_upwards [ae_openStrip, ae_ne_circle] with x hx1 hx2
  refine ⟨hx1, ?_⟩
  rcases lt_trichotomy (x.1 ^ 2 + (x.2 - 1 / 2) ^ 2) (1 / 8) with h | h | h
  · exact Or.inl h
  · exact absurd h hx2
  · exact Or.inr h

lemma not_mem_closedDisc_of_extD {x : ℝ × ℝ} (hx : x ∈ extD) : x ∉ closedDisc := fun h => by
  simp only [extD, closedDisc, mem_ofPred_eq] at hx h; linarith

lemma eqOn_strip_of_ae {f g : ℝ × ℝ → ℝ} (hf : Continuous f) (hg : Continuous g)
    (h : f =ᵐ[cyl] g) : EqOn f g openStrip := by
  rw [cyl_eq_vol_restrict] at h
  exact Measure.eqOn_open_of_ae_eq (ae_restrict_of_ae_restrict_of_subset openStrip_sub h)
    isOpen_openStrip hf.continuousOn hg.continuousOn

end Null

/-! ## 2. Derivatives read in a disc chart -/

section Chart

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {m : ℕ} {X : NodalSurface m} (hT : ChartsOnto X)

include hT in
lemma mfderiv_extChartAt_symm_eq (z : X.S) (w : E2) :
    mfderiv 𝓘(ℝ, E2) 𝓘(ℝ, E2) (extChartAt 𝓘(ℝ, E2) z).symm w =
      tangentCoordChange 𝓘(ℝ, E2) z ((extChartAt 𝓘(ℝ, E2) z).symm w)
        ((extChartAt 𝓘(ℝ, E2) z).symm w) := by
  have hd : MDifferentiableAt 𝓘(ℝ, E2) 𝓘(ℝ, E2) (extChartAt 𝓘(ℝ, E2) z).symm w :=
    ((contMDiff_extChartAt_symm hT z) w).mdifferentiableAt (by simp)
  rw [hd.mfderiv, tangentCoordChange_def, (extChartAt 𝓘(ℝ, E2) z).right_inv
    (mem_target hT z w)]
  simp only [writtenInExtChartAt, extChartAt_model_space_eq_id, PartialEquiv.refl_symm,
    PartialEquiv.refl_coe, Function.comp_id, id_eq]
  rfl

lemma hasFDerivAt_place (z : X.S) (ε : ℝ) (p : ℝ × ℝ) :
    HasFDerivAt (X.place z ε) (ε • ((ContinuousLinearMap.fst ℝ ℝ ℝ).smulRight
      (EuclideanSpace.single (0 : Fin 2) (1 : ℝ)) + (ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight
        (EuclideanSpace.single (1 : Fin 2) (1 : ℝ)))) p := by
  have e : X.place z ε = fun p => extChartAt 𝓘(ℝ, E2) z z + ε • (p.1 • EuclideanSpace.single 0 1 +
      (p.2 - 1 / 2) • EuclideanSpace.single 1 (1 : ℝ)) := by
    funext p; unfold NodalSurface.place; rw [← single_eq_smul, ← single_eq_smul]
  rw [e]
  exact ((((hasFDerivAt_fst).smul_const _).add
    (((hasFDerivAt_snd).sub_const (1 / 2)).smul_const _)).const_smul ε).const_add _

lemma fderiv_place_dir (z : X.S) (ε : ℝ) (p : ℝ × ℝ) (d : Fin 2) :
    fderiv ℝ (X.place z ε) p (dir2 d) = ε • EuclideanSpace.single d (1 : ℝ) := by
  rw [(hasFDerivAt_place z ε p).fderiv]
  fin_cases d <;> simp [dir2]

include hT in
/-- **A map differentiable in a disc chart is differentiable**, and its derivative on the chart
vectors is `ε⁻¹` times the derivative in the strip coordinates. -/
theorem mfderiv_of_disc {f : X.S → E} {z : X.S} {ε : ℝ} (hε : ε ≠ 0) {p : ℝ × ℝ}
    (hf : DifferentiableAt ℝ (fun p => f (X.discPt z ε p)) p) :
    MDifferentiableAt 𝓘(ℝ, E2) 𝓘(ℝ, E) f (X.discPt z ε p) ∧ ∀ d : Fin 2,
      mfderiv 𝓘(ℝ, E2) 𝓘(ℝ, E) f (X.discPt z ε p) (tangentCoordChange 𝓘(ℝ, E2) z
        (X.discPt z ε p) (X.discPt z ε p) (EuclideanSpace.single d 1)) =
          ε⁻¹ • fderiv ℝ (fun p => f (X.discPt z ε p)) p (dir2 d) := by
  set y := X.discPt z ε p
  have hy : y ∈ (extChartAt 𝓘(ℝ, E2) z).source := discPt_mem_source hT z ε p
  have hstrip : ∀ y' ∈ (extChartAt 𝓘(ℝ, E2) z).source, X.discPt z ε (stripPt z ε y') = y' := by
    intro y' hy'
    rw [stripPt, NodalSurface.discPt, place_placeInv z hε]
    exact (extChartAt 𝓘(ℝ, E2) z).left_inv hy'
  have hpy : stripPt z ε y = p := by
    rw [stripPt, extChartAt_discPt hT, placeInv_place z hε]
  have hsm : MDifferentiableAt 𝓘(ℝ, E2) 𝓘(ℝ, ℝ × ℝ) (stripPt (X := X) z ε) y := by
    have h1 : MDifferentiableAt 𝓘(ℝ, E2) 𝓘(ℝ, E2) (extChartAt 𝓘(ℝ, E2) z) y :=
      mdifferentiableAt_extChartAt (by rwa [← extChartAt_source (I := 𝓘(ℝ, E2))])
    have h2 : MDifferentiableAt 𝓘(ℝ, E2) 𝓘(ℝ, ℝ × ℝ) (placeInv (X := X) z ε)
        (extChartAt 𝓘(ℝ, E2) z y) :=
      ((contDiff_placeInv z ε).differentiable (by simp) _).mdifferentiableAt
    exact h2.comp y h1
  have hev : (fun p => f (X.discPt z ε p)) ∘ stripPt z ε =ᶠ[𝓝 y] f := by
    filter_upwards [extChartAt_source_mem_nhds' hy] with y' hy'
    simp only [Function.comp_apply, hstrip y' hy']
  have hfd : MDifferentiableAt 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E) (fun p => f (X.discPt z ε p))
      (stripPt z ε y) := by
    rw [hpy]; exact hf.mdifferentiableAt
  have hmd : MDifferentiableAt 𝓘(ℝ, E2) 𝓘(ℝ, E) f y :=
    (hfd.comp y hsm).congr_of_eventuallyEq hev.symm
  refine ⟨hmd, fun d => ?_⟩
  have hdisc : MDifferentiableAt 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E2) (X.discPt z ε) p :=
    (contMDiff_discPt hT z ε p).mdifferentiableAt (by simp)
  have hchain := mfderiv_comp p hmd hdisc
  have hsymm : MDifferentiableAt 𝓘(ℝ, E2) 𝓘(ℝ, E2) (extChartAt 𝓘(ℝ, E2) z).symm
      (X.place z ε p) := ((contMDiff_extChartAt_symm hT z) _).mdifferentiableAt (by simp)
  have hpl : MDifferentiableAt 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E2) (X.place z ε) p :=
    (hasFDerivAt_place z ε p).differentiableAt.mdifferentiableAt
  have hchain2 : mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E2) (X.discPt z ε) p =
      (mfderiv 𝓘(ℝ, E2) 𝓘(ℝ, E2) (extChartAt 𝓘(ℝ, E2) z).symm (X.place z ε p)).comp
        (mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E2) (X.place z ε) p) :=
    mfderiv_comp (f := X.place z ε) (g := (extChartAt 𝓘(ℝ, E2) z).symm) p hsymm hpl
  have hD : mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E2) (X.discPt z ε) p (dir2 d) =
      ε • tangentCoordChange 𝓘(ℝ, E2) z y y (EuclideanSpace.single d 1) := by
    rw [hchain2]
    erw [ContinuousLinearMap.comp_apply, mfderiv_eq_fderiv, fderiv_place_dir,
      ContinuousLinearMap.map_smul, mfderiv_extChartAt_symm_eq hT]
    rfl
  have key : fderiv ℝ (fun p => f (X.discPt z ε p)) p (dir2 d) =
      mfderiv 𝓘(ℝ, E2) 𝓘(ℝ, E) f y (mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E2) (X.discPt z ε) p (dir2 d)) := by
    rw [← mfderiv_eq_fderiv]
    exact congrArg (fun L => L (dir2 d)) hchain
  rw [key, hD]
  erw [ContinuousLinearMap.map_smul]
  exact (inv_smul_smul₀ hε _).symm

end Chart

/-! ## 3. The representative of `R v` -/

section Rep

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {Q : Type} [TopologicalSpace Q] [ChartedSpace E Q] [IsManifold 𝓘(ℝ, E) ∞ Q]
variable {m : ℕ} {X : NodalSurface m} (hX : X.nodes = ∅) (hT : ChartsOnto X) {q : Q}
  {u : X.S → Q} (hu : ∀ x, u x = q) {A : SectionAtlas (E := E) X u} (G : GlueData A)
  {δ : ℕ → ℝ} {h0 : 0 ≤ δ 0} {hmono : StrictMono δ}

include hu in
lemma continuous_of_isContSection {η : Section E X} (h : IsContSection u η) : Continuous η := by
  refine continuous_iff_continuousAt.2 fun x => ?_
  have e : (fun y => tangentCoordChange 𝓘(ℝ, E) (u y) (u x) (u y) (η y)) = η := by
    funext y
    simp only [hu]
    exact tangentCoordChange_self (mem_extChartAt_source q)
  have h1 := h x
  rw [e] at h1
  exact h1

/-- The `k`-th coordinate of `η` read in the disc `i`. -/
def ek (A : SectionAtlas (E := E) X u) (i : Fin A.nd) (k : Fin (Module.finrank ℝ E))
    (η : Section E X) (p : ℝ × ℝ) : ℝ := crd k (η (X.discPt (A.center i) (A.ε i) p))

/-- The coordinate functional as a continuous linear map. -/
def crdL (k : Fin (Module.finrank ℝ E)) : E →L[ℝ] ℝ := LinearMap.toContinuousLinearMap (crd k)

lemma crdL_apply (k : Fin (Module.finrank ℝ E)) (w : E) : crdL k w = crd k w := rfl

include hT in
lemma continuous_ek {η : Section E X} (hc : Continuous η) (i : Fin A.nd)
    (k : Fin (Module.finrank ℝ E)) : Continuous (ek A i k η) :=
  (crdL k).continuous.comp (hc.comp (continuous_discPt hT _ _))

/-- The data of a section of class `(3, δ₀)` in the disc `i`, coordinate `k`: a continuous
representative `g` of the block, `C¹` on the strip, its partial derivatives `gd`, and
`g = β · η_k` on the strip. -/
structure DiscC1 (A : SectionAtlas (E := E) X u) (δ : ℕ → ℝ) (h0 : 0 ≤ δ 0)
    (hmono : StrictMono δ) (v : (blocks A δ h0 hmono) 0) (η : Section E X) (i : Fin A.nd)
    (k : Fin (Module.finrank ℝ E)) where
  g : ℝ × ℝ → ℝ
  gd : Fin 2 → ℝ × ℝ → ℝ
  cont_gd : ∀ d, Continuous (gd d)
  ae_gd : ∀ d, (H.val (dH δ h0 hmono d (v.1 (i, k))) : ℝ × ℝ → ℝ) =ᵐ[cyl] gd d
  deriv : ∀ x ∈ openStrip, HasFDerivAt g
    (gd 0 x • ContinuousLinearMap.fst ℝ ℝ ℝ + gd 1 x • ContinuousLinearMap.snd ℝ ℝ ℝ) x
  eq : EqOn g (fun p => discCut p * ek A i k η p) openStrip

include hT hu in
lemma exists_discC1 {η : Section E X} (hc : Continuous η) {v : (blocks A δ h0 hmono) 0}
    (hr : IsRep η v) (i : Fin A.nd) (k : Fin (Module.finrank ℝ E)) :
    Nonempty (DiscC1 A δ h0 hmono v η i k) := by
  obtain ⟨g, gs, gt, hg, hgs, hgt, hwg, hwgs, hwgt, hder⟩ := exists_C1_rep (v.1 (i, k))
  refine ⟨⟨g, ![gs, gt], fun d => ?_, fun d => ?_, hder, ?_⟩⟩
  · fin_cases d; exacts [hgs, hgt]
  · fin_cases d; exacts [hwgs, hwgt]
  · refine eqOn_strip_of_ae hg (continuous_discCut.mul (continuous_ek hT hc i k)) ?_
    refine hwg.symm.trans ((hr.1 i k).trans (Eventually.of_forall fun p => ?_))
    rw [discRep_const hu]; rfl

lemma apply_dir2 (a b : ℝ) (d : Fin 2) :
    (a • ContinuousLinearMap.fst ℝ ℝ ℝ + b • ContinuousLinearMap.snd ℝ ℝ ℝ) (dir2 d) =
      ![a, b] d := by
  fin_cases d <;> simp [dir2]

variable {v : (blocks A δ h0 hmono) 0} {η : Section E X}

/-- On the disc `r² < 1/8` the coordinate `η_k` is differentiable, with
`∂_d g = β ∂_d η_k + ∂_d β · η_k`. -/
lemma DiscC1.ek_deriv {i k} (D : DiscC1 A δ h0 hmono v η i k) {p : ℝ × ℝ}
    (hp : p ∈ discD) : DifferentiableAt ℝ (ek A i k η) p ∧ ∀ d,
      D.gd d p = discCut p * fderiv ℝ (ek A i k η) p (dir2 d) + dCut d p * ek A i k η p := by
  have hpS : p ∈ openStrip := discD_sub hp
  have hne : discCut p ≠ 0 := (discCut_pos hp).ne'
  have hcut : DifferentiableAt ℝ discCut p := contDiff_discCut.differentiable (by simp) p
  have hev : (fun p => D.g p * (discCut p)⁻¹) =ᶠ[𝓝 p] ek A i k η := by
    filter_upwards [isOpen_discD.mem_nhds hp] with p' hp'
    rw [D.eq (discD_sub hp'), mul_comm, ← mul_assoc, inv_mul_cancel₀ (discCut_pos hp').ne',
      one_mul]
  have hdiff : DifferentiableAt ℝ (ek A i k η) p :=
    ((D.deriv p hpS).differentiableAt.mul (hcut.inv hne)).congr_of_eventuallyEq hev.symm
  refine ⟨hdiff, fun d => ?_⟩
  have hev2 : (fun p => discCut p * ek A i k η p) =ᶠ[𝓝 p] D.g := by
    filter_upwards [isOpen_openStrip.mem_nhds hpS] with p' hp' using (D.eq hp').symm
  have h1 := (hcut.hasFDerivAt.mul hdiff.hasFDerivAt).congr_of_eventuallyEq hev2.symm
  have h2 := (D.deriv p hpS).unique h1
  have h3 : ![D.gd 0 p, D.gd 1 p] d = (discCut p • fderiv ℝ (ek A i k η) p +
      ek A i k η p • fderiv ℝ discCut p) (dir2 d) := by rw [← apply_dir2, h2]
  simp only [_root_.add_apply, _root_.smul_apply, smul_eq_mul] at h3
  have e : D.gd d p = ![D.gd 0 p, D.gd 1 p] d := by fin_cases d <;> rfl
  rw [e, h3, dCut]
  ring

include hT in
/-- Outside the disc the partial derivatives of `g` vanish. -/
lemma DiscC1.gd_eq_zero {i k} (D : DiscC1 A δ h0 hmono v η i k) {p : ℝ × ℝ} (hpS : p ∈ openStrip)
    (hp : p ∈ extD) (d : Fin 2) : D.gd d p = 0 := by
  have hev : (fun _ => (0 : ℝ)) =ᶠ[𝓝 p] D.g := by
    filter_upwards [(isOpen_openStrip.inter isOpen_extD).mem_nhds ⟨hpS, hp⟩] with p' hp'
    rw [D.eq hp'.1]
    dsimp only
    rw [discCut_eq_zero (not_mem_closedDisc_of_extD hp'.2), zero_mul]
  have h1 := ((hasFDerivAt_const (𝕜 := ℝ) (0 : ℝ) p).congr_of_eventuallyEq hev.symm)
  have h2 : ![D.gd 0 p, D.gd 1 p] d = (0 : ℝ × ℝ →L[ℝ] ℝ) (dir2 d) := by
    rw [← apply_dir2, (D.deriv p hpS).unique h1]
  simp only [_root_.zero_apply] at h2
  have e : D.gd d p = ![D.gd 0 p, D.gd 1 p] d := by fin_cases d <;> rfl
  rw [e, h2]

/-- The form `dη`. -/
def dForm (η : Section E X) : Form E X := fun y => mfderiv 𝓘(ℝ, E2) 𝓘(ℝ, E) η y

lemma crd_fderiv_secDisc {i : Fin A.nd} {p : ℝ × ℝ}
    (h : ∀ k, DifferentiableAt ℝ (ek A i k η) p) (w : ℝ × ℝ) :
    DifferentiableAt ℝ (fun p => η (X.discPt (A.center i) (A.ε i) p)) p ∧ ∀ k,
      crd k (fderiv ℝ (fun p => η (X.discPt (A.center i) (A.ε i) p)) p w) =
        fderiv ℝ (ek A i k η) p w := by
  set b := Module.finBasis ℝ E
  set F : ℝ × ℝ → (Fin (Module.finrank ℝ E) → ℝ) := fun p k => ek A i k η p
  have hF : DifferentiableAt ℝ F p := differentiableAt_pi.2 h
  set e : (Fin (Module.finrank ℝ E) → ℝ) →L[ℝ] E :=
    LinearMap.toContinuousLinearMap b.equivFun.symm.toLinearMap
  have heq : (fun p => η (X.discPt (A.center i) (A.ε i) p)) = e ∘ F := by
    funext p
    simp only [Function.comp_apply, e, F, ek, LinearMap.coe_toContinuousLinearMap',
      LinearEquiv.coe_coe]
    exact (b.equivFun.symm_apply_apply _).symm.trans (by rfl)
  have hd : DifferentiableAt ℝ (fun p => η (X.discPt (A.center i) (A.ε i) p)) p := by
    rw [heq]; exact e.differentiableAt.comp p hF
  refine ⟨hd, fun k => ?_⟩
  have hk : ek A i k η = crdL k ∘ fun p => η (X.discPt (A.center i) (A.ε i) p) := rfl
  rw [hk, fderiv_comp p (crdL k).differentiableAt hd, (crdL k).fderiv]
  rfl

include hT hu in
/-- **The representative of `dη` in the disc `i`**: on `r² < 1/8`, `η` is differentiable at the
point of the disc and `β (dη)_{d,k} = ε⁻¹ (∂_d g - ∂_d β · η_k)`. -/
lemma formDiscRep_dForm (D : ∀ k, DiscC1 A δ h0 hmono v η i k) {p : ℝ × ℝ} (hp : p ∈ discD) :
    MDifferentiableAt 𝓘(ℝ, E2) 𝓘(ℝ, E) η (X.discPt (A.center i) (A.ε i) p) ∧ ∀ d k,
      formDiscRep A i d k (dForm η) p =
        (A.ε i)⁻¹ * ((D k).gd d p - dCut d p * ek A i k η p) := by
  have hdk := fun k => ((D k).ek_deriv hp)
  obtain ⟨hdv, -⟩ := crd_fderiv_secDisc (fun k => (hdk k).1) (0, 0)
  obtain ⟨hmd, hmf⟩ := mfderiv_of_disc hT (A.ε_pos i).ne' hdv
  refine ⟨hmd, fun d k => ?_⟩
  have hck := (crd_fderiv_secDisc (fun k => (hdk k).1) (dir2 d)).2 k
  have hne : discCut p ≠ 0 := (discCut_pos hp).ne'
  rw [formDiscRep, formAt_of_const hu, ContinuousLinearMap.comp_apply]
  change discCut p * crd k (mfderiv 𝓘(ℝ, E2) 𝓘(ℝ, E) η _ _) = _
  rw [hmf d, map_smul, smul_eq_mul, hck, (hdk k).2 d]
  field_simp
  ring

include hX hT hu in
/-- **`R v` is the representative of `dη`** for the representative `v` of a section `η` of class
`(3, δ₀)` (continuous, with representatives in the blocks). -/
theorem isFormRep_rOp (hc : IsContSection u η) (hr : IsRep η v) :
    IsFormRep (dForm η) (rOp hT G δ h0 hmono v) := by
  have hηc := continuous_of_isContSection hu hc
  have hnn := isEmpty_neck_of_nodes_empty hX A
  refine ⟨fun i d k => ?_, fun j => (hnn.false j).elim⟩
  have D := fun k => (exists_discC1 hT hu hηc hr i k).some
  have hZ : ∀ᵐ x ∂cyl, ∀ j, coefZ d (G.ρ j) (A.center i) (A.ε i) (A.center j) (A.ε j) x *
      H.val (v.1 (j, k)) ((G.D i j).ψ x) =
        coefZ d (G.ρ j) (A.center i) (A.ε i) (A.center j) (A.ε j) x *
          discRep A j k η ((G.D i j).ψ x) :=
    ae_all_iff.2 fun j => ChartChange.comp_congr (G.hsZ hT d i j) (hr.1 j k)
  filter_upwards [coeFn_rBlock hT G δ h0 hmono v (i, d, k), (D k).ae_gd d, hZ, ae_disc_or_ext]
    with x h1 h2 h3 h4
  change H.val (rBlock hT G δ h0 hmono (i, d, k) v) x = _
  rw [h1]
  rw [Finset.sum_congr rfl fun j _ => h3 j, sumZ_rep_eq hT G hu d i k η x, h2]
  rcases h4 with ⟨hxS, hxD | hxE⟩
  · rw [(formDiscRep_dForm hT hu D hxD).2 d k]; rfl
  · have hcl := not_mem_closedDisc_of_extD hxE
    rw [(D k).gd_eq_zero hT hxS hxE d, dCut_eq_zero d hcl, formDiscRep, discCut_eq_zero hcl]
    ring

include hX hT hu in
/-- **`D v` is the representative of `½ (dη + J₀ ∘ dη ∘ j)`.** -/
theorem isFormRep_linOp (hc : IsContSection u η) (hr : IsRep η v) (J₀ : E →L[ℝ] E) :
    IsFormRep (projF J₀ (dForm η)) (linOp hT G δ h0 hmono J₀ v) := by
  have h1 := isFormRep_rOp hX hT hu G hc hr
  have h2 := P_rep hT hu (isEmpty_neck_of_nodes_empty hX A) J₀
    (fun _ _ => contDiff_aP hT J₀ _ _ _ _ _ _) (fun _ _ => tsupport_aP J₀ _ _ _ _ _ _) h1
  exact (h1.add h2).smul (1 / 2 : ℝ)

include hu in
lemma continuous_u : Continuous u := continuous_const.congr fun x => (hu x).symm

include hX hT hu in
/-- `D` maps `H^{3,δ₀}_c(S, u*TQ)` into the fibre `H^{2,δ₀}` of `W` over `u`. -/
theorem linOp_mem (J : AlmostComplexStructure E Q) {w : (blocks A δ h0 hmono) 0}
    (hw : w ∈ sectionSpace A δ h0 hmono) :
    linOp hT G δ h0 hmono (J.J q) w ∈ fibreSpace J A δ h0 hmono := by
  rw [sectionSpace_eq_of_nodes_empty (continuous_u hu) hX A δ h0 hmono] at hw
  obtain ⟨η, hc, -, hr⟩ := hw
  refine formsSub_le J A δ h0 hmono ⟨projF (J.J q) (dForm η), fun x _ => ?_,
    isFormRep_linOp hX hT hu G hc hr _⟩
  rw [hu x]; exact projF_mem J q _ x

/-- **The linearization of `∂̄_J` at the constant map `u ≡ q`** (Memoir Prop 4.7, p. 102; the
spaces of p. 66 and p. 7), as a bounded operator `H^{3,δ₀}_c(S, u*TQ) → H^{2,δ₀}`:
`D = ½ (R + P R)`. -/
def linCR (J : AlmostComplexStructure E Q) :
    sectionSpace A δ h0 hmono →L[ℝ] fibreSpace J A δ h0 hmono :=
  ((linOp hT G δ h0 hmono (J.J q)).comp (sectionSpace A δ h0 hmono).subtypeL).codRestrict _
    fun w => linOp_mem hX hT hu G J w.2

lemma linCR_apply (J : AlmostComplexStructure E Q) (w : sectionSpace A δ h0 hmono) :
    (linCR hX hT hu G J w : (fibreBlocks A δ h0 hmono) 0) = linOp hT G δ h0 hmono (J.J q) w :=
  rfl

include hT hu in
/-- On the disc `i`, the representative of `projF J₀ dη` is continuous on `r² < 1/8`. -/
lemma continuousAt_formDiscRep_projF (D : ∀ k, DiscC1 A δ h0 hmono v η i k) (hc : Continuous η)
    (J₀ : E →L[ℝ] E) {p₀ : ℝ × ℝ} (hp₀ : p₀ ∈ discD) (d : Fin 2)
    (k : Fin (Module.finrank ℝ E)) :
    ContinuousAt (formDiscRep A i d k (projF J₀ (dForm η))) p₀ := by
  have hcont : ∀ d k, ContinuousAt (formDiscRep A i d k (dForm η)) p₀ := by
    intro d k
    have hev : (fun p => (A.ε i)⁻¹ * ((D k).gd d p - dCut d p * ek A i k η p)) =ᶠ[𝓝 p₀]
        formDiscRep A i d k (dForm η) := by
      filter_upwards [isOpen_discD.mem_nhds hp₀] with p hp
      exact ((formDiscRep_dForm hT hu D hp).2 d k).symm
    refine ContinuousAt.congr ?_ hev
    exact (continuous_const.mul (((D k).cont_gd d).sub
      ((contDiff_dCut d).continuous.mul (continuous_ek hT hc i k)))).continuousAt
  have e : formDiscRep A i d k (projF J₀ (dForm η)) = fun x => (1 / 2 : ℝ) *
      (formDiscRep A i d k (dForm η) x + ∑ t : Fin 2 × Fin (Module.finrank ℝ E),
        aP J₀ (A.center i) (A.ε i) d t.1 k t.2 x * formDiscRep A i t.1 t.2 (dForm η) x) := by
    funext x
    rw [projF, formDiscRep_smul, formDiscRep_add, Pi.smul_apply, Pi.add_apply,
      formDiscRep_twist hT hu A, smul_eq_mul]
  rw [e]
  refine continuousAt_const.mul ((hcont d k).add ?_)
  exact tendsto_finsetSum _ fun t _ =>
    ((contDiff_aP hT J₀ _ _ _ _ _ _).continuous.continuousAt.mul (hcont t.1 t.2))

include hX hT hu in
/-- **`D v = 0` makes `η` differentiable with `projF J₀ dη = 0`.** -/
theorem projF_eq_zero_of_linOp (hc : IsContSection u η) (hr : IsRep η v) (J₀ : E →L[ℝ] E)
    (h : linOp hT G δ h0 hmono J₀ v = 0) :
    MDifferentiable 𝓘(ℝ, E2) 𝓘(ℝ, E) η ∧ projF J₀ (dForm η) = 0 := by
  have hηc := continuous_of_isContSection hu hc
  have hnn := isEmpty_neck_of_nodes_empty hX A
  have hrep := isFormRep_linOp hX hT hu G hc hr J₀
  rw [h] at hrep
  have key : ∀ y, MDifferentiableAt 𝓘(ℝ, E2) 𝓘(ℝ, E) η y ∧ projF J₀ (dForm η) y = 0 := by
    intro y
    rcases A.cover y with ⟨i, p₀, hp₀, rfl⟩ | ⟨j, -⟩
    swap
    · exact (hnn.false j).elim
    have hp₀D : p₀ ∈ discD := mem_discD_of_core hp₀
    have D := fun k => (exists_discC1 hT hu hηc hr i k).some
    refine ⟨(formDiscRep_dForm hT hu D hp₀D).1, ?_⟩
    have hp2 : 1 / 4 ≤ p₀.2 ∧ p₀.2 ≤ 3 / 4 := by
      constructor <;> nlinarith [sq_nonneg p₀.1, sq_nonneg (p₀.2 - 1 / 4),
        sq_nonneg (p₀.2 - 3 / 4)]
    have hzero : formAt u (A.center i) (projF J₀ (dForm η))
        (X.discPt (A.center i) (A.ε i) p₀) = 0 := by
      refine E2_ext fun d => ?_
      refine (Module.finBasis ℝ E).ext_elem fun k => ?_
      have hae : formDiscRep A i d k (projF J₀ (dForm η)) =ᵐ[cyl] 0 :=
        (hrep.1 i d k).symm.trans (val_zero_ae (k := 2) (hd := Neck.δ_nonneg δ h0 hmono 0))
      have := eq_zero_of_ae_of_continuousAt (by linarith) (by linarith)
        (continuousAt_formDiscRep_projF hT hu D hηc J₀ hp₀D d k) hae
      rw [formDiscRep, discCut_eq_one hp₀, one_mul] at this
      simpa using this
    refine eq_zero_of_formAt (discPt_mem_source hT _ _ _) ?_ hzero
    rw [hu, hu]; exact mem_extChartAt_source q
  exact ⟨fun y => (key y).1, funext fun y => (key y).2⟩

/-- `projF J(q) ξ = 0` is the Cauchy–Riemann equation `ξ ∘ j = J(q) ∘ ξ`. -/
lemma holo_of_projF {J : AlmostComplexStructure E Q} {ξ : Form E X} {y : X.S}
    (h : projF (J.J q) ξ y = 0) (w : E2) : ξ y (X.j.J y w) = J.J q (ξ y w) := by
  have h1 := congrArg (fun L : E2 →L[ℝ] E => J.J q (L w)) h
  simp only [projF, twist, Pi.smul_apply, Pi.add_apply, _root_.smul_apply,
    _root_.add_apply, ContinuousLinearMap.comp_apply, map_smul, map_add, J.J_J,
    _root_.zero_apply, map_zero] at h1
  have h2 : J.J q (ξ y w) - ξ y (X.j.J y w) = 0 := by
    have := congrArg (fun x => (2 : ℝ) • x) h1
    simp only [smul_zero, smul_smul] at this
    norm_num at this
    rw [sub_eq_add_neg]; exact this
  exact (sub_eq_zero.1 h2).symm

end Rep

end GWMemoir
