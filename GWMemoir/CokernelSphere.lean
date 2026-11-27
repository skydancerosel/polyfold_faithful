import GWMemoir.CauchyTransform
import GWMemoir.LinearCRFredholm

/-!
# `∂̄ξ = η` on the three-pointed sphere, and the range of `D`

HWZ, *Applications of Polyfold Theory I*, Memoirs AMS 248, no. 1179, §4 (Props 4.7, 4.23, 4.25
near the constant maps): the vanishing of the cokernel of `D = linCR3` (`H^{0,1}(P¹, ℂⁿ) = 0`).

* `DsigS`, `DtauS`: the derivatives of the holomorphic charts `σ_s`, `s = ±1`, and their
  inverses; `DtauS_I`: `σ_s⁻¹` is holomorphic.
* `chartCoef s η z = η(σ_s⁻¹ z)(Dσ_s⁻¹(z) 1)`, the coefficient of a form in the chart `σ_s`.
  `IsSphereSmooth η`: both coefficients are smooth on `ℂ`.  **`chartCoef_neg_eq`**: for an
  anti-linear form, `coef₋(w) = -(w̄²)⁻¹ coef₊(1/w)` (the change of charts `w = 1/z`).
* **`exists_sphere_solution`**: for a smooth anti-linear form `η` there is a smooth section
  `ξ : S² → E` with `½ (dξ + J₀ dξ j) = η` (the Cauchy transform in both charts,
  `exists_dbar_sphere`).
-/

set_option maxSynthPendingDepth 3
set_option linter.unusedSectionVars false

open scoped Manifold ContDiff Topology
open Set Function Filter MeasureTheory
open Polyfold Polyfold.CylinderSobolev

noncomputable section

namespace GWMemoir

/-! ## 1. The holomorphic charts `σ_s`, `s = ±1` -/

section Charts

variable (s : ℝ) (hs : s ^ 2 = 1)

/-- `Dσ_s(y)`. -/
def DsigS (y : S2) : E2 →L[ℝ] ℂ := mfderiv 𝓘(ℝ, E2) 𝓘(ℝ, ℂ) (holChart s hs) y

/-- `Dσ_s⁻¹(z)`. -/
def DtauS (z : ℂ) : ℂ →L[ℝ] E2 := mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E2) (holChart s hs).symm z

lemma holChart_symm_mem (z : ℂ) : (holChart s hs).symm z ∈ (holChart s hs).source :=
  (holChart s hs).map_target (mem_univ z)

lemma holChart_holChart_symm (z : ℂ) : holChart s hs ((holChart s hs).symm z) = z :=
  (holChart s hs).right_inv (mem_univ z)

theorem DsigS_DtauS (z v : ℂ) : DsigS s hs ((holChart s hs).symm z) (DtauS s hs z v) = v := by
  have h : (mfderiv 𝓘(ℝ, E2) 𝓘(ℝ, ℂ) (holChart s hs) ((holChart s hs).symm z)).comp
      (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E2) (holChart s hs).symm z) = ContinuousLinearMap.id ℝ ℂ := by
    have hσ := (holChart_holo s hs _ (holChart_symm_mem s hs z)).1
    rw [← mfderiv_comp z hσ (mdifferentiable_holChart_symm s hs z)]
    have : (holChart s hs ∘ (holChart s hs).symm) = id := funext (holChart_holChart_symm s hs)
    rw [this, mfderiv_id]
    rfl
  exact congrArg (fun L => L v) h

theorem injective_DsigS (z : ℂ) : Injective (DsigS s hs ((holChart s hs).symm z)) := by
  have hsurj : Surjective (DsigS s hs ((holChart s hs).symm z)) := fun v =>
    ⟨DtauS s hs z v, DsigS_DtauS s hs z v⟩
  have hfin : Module.finrank ℝ E2 = Module.finrank ℝ ℂ := by
    simp [Complex.finrank_real_complex]
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hfin
    (f := ((DsigS s hs ((holChart s hs).symm z) : E2 →L[ℝ] ℂ) : E2 →ₗ[ℝ] ℂ))).2 hsurj

theorem DtauS_DsigS (z : ℂ) (v : E2) :
    DtauS s hs z (DsigS s hs ((holChart s hs).symm z) v) = v :=
  injective_DsigS s hs z (DsigS_DtauS s hs z _)

theorem DsigS_j (y : S2) (hy : y ∈ (holChart s hs).source) (u : E2) :
    DsigS s hs y (jStdMap y u) = Complex.I * DsigS s hs y u :=
  (holChart_holo s hs y hy).2 u

/-- `σ_s⁻¹` is holomorphic: `Dσ_s⁻¹(z)(i v) = j Dσ_s⁻¹(z) v`. -/
theorem DtauS_I (z v : ℂ) :
    DtauS s hs z (Complex.I * v) = jStdMap ((holChart s hs).symm z) (DtauS s hs z v) := by
  apply injective_DsigS s hs z
  rw [DsigS_DtauS, DsigS_j s hs _ (holChart_symm_mem s hs z), DsigS_DtauS]

/-- `σ_s` is smooth on its source. -/
theorem contMDiffAt_holChart {y : S2} (hy : y ∈ (holChart s hs).source) :
    ContMDiffAt 𝓘(ℝ, E2) 𝓘(ℝ, ℂ) ∞ (holChart s hs) y := by
  have hd : 1 - s * (y : E3) 2 ≠ 0 := sub_ne_zero.2 (Ne.symm hy)
  have hcoe : (holChart s hs : S2 → ℂ) = stereoC s ∘ Subtype.val := rfl
  have hst : ContDiffAt ℝ ∞ (stereoC s) (y : E3) := by
    unfold stereoC
    have hinv : ContDiffAt ℝ ∞ (fun x : E3 => (1 - s * x 2)⁻¹) (y : E3) :=
      (contDiffAt_const.sub (contDiffAt_const.mul
        ((EuclideanSpace.proj (2 : Fin 3) : E3 →L[ℝ] ℝ).contDiff.contDiffAt))).inv hd
    have hN : ContDiff ℝ ∞ fun x : E3 => ((x 0 : ℂ) - s * Complex.I * (x 1 : ℂ)) := by
      have h0 : ContDiff ℝ ∞ fun x : E3 => ((x 0 : ℝ) : ℂ) :=
        Complex.ofRealCLM.contDiff.comp (EuclideanSpace.proj (0 : Fin 3) : E3 →L[ℝ] ℝ).contDiff
      have h1 : ContDiff ℝ ∞ fun x : E3 => ((x 1 : ℝ) : ℂ) :=
        Complex.ofRealCLM.contDiff.comp (EuclideanSpace.proj (1 : Fin 3) : E3 →L[ℝ] ℝ).contDiff
      exact h0.sub (contDiff_const.mul h1)
    exact hN.contDiffAt.mul (Complex.ofRealCLM.contDiff.contDiffAt.comp _ hinv)
  rw [hcoe]
  exact hst.contMDiffAt.comp y (contMDiff_coe_sphere (n := 2) y)

end Charts

lemma tau_neg_eq {w : ℂ} (hw : w ≠ 0) : (holChart (-1) (by norm_num)).symm w = sig.symm w⁻¹ := by
  rw [← holChart_neg_symm_inv w⁻¹ (inv_ne_zero hw), inv_inv]

/-- `Dσ₋₁⁻¹(w) v = Dσ₁⁻¹(1/w)(-v/w²)`. -/
lemma DtauS_neg {w : ℂ} (hw : w ≠ 0) (v : ℂ) :
    DtauS (-1) (by norm_num) w v = DtauS 1 (by norm_num) w⁻¹ (-(w ^ 2)⁻¹ * v) := by
  have hev : (holChart (-1) (by norm_num)).symm =ᶠ[𝓝 w] (sig.symm ∘ fun z : ℂ => z⁻¹) := by
    filter_upwards [isOpen_ne.mem_nhds hw] with z hz
    exact tau_neg_eq hz
  have hinv : MDifferentiableAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (fun z : ℂ => z⁻¹) w :=
    (hasFDerivAt_inv_real hw).differentiableAt.mdifferentiableAt
  have h := mfderiv_comp w (mdifferentiable_holChart_symm 1 (by norm_num) w⁻¹) hinv
  rw [DtauS, hev.mfderiv_eq, h, mfderiv_eq_fderiv, (hasFDerivAt_inv_real hw).fderiv]
  rfl

/-! ## 2. Forms in the charts -/

section Coef

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {J₀ : E →L[ℝ] E}

/-- The coefficient of a form in the chart `σ_s`: `η(σ_s⁻¹ z)(Dσ_s⁻¹(z) 1)`. -/
def chartCoef (s : ℝ) (hs : s ^ 2 = 1) (η : S2 → E2 →L[ℝ] E) (z : ℂ) : E :=
  η ((holChart s hs).symm z) (DtauS s hs z 1)

variable (J₀) in
/-- `η` is anti-linear for `(j, J₀)`: `J₀ η(v) = -η(j v)`. -/
def IsAntiJ (η : S2 → E2 →L[ℝ] E) : Prop := ∀ y v, J₀ (η y v) = -η y (jStdMap y v)

/-- A form is **smooth on the sphere** if its coefficients in both holomorphic charts are smooth. -/
def IsSphereSmooth (η : S2 → E2 →L[ℝ] E) : Prop :=
  ContDiff ℝ ∞ (chartCoef 1 (by norm_num) η) ∧ ContDiff ℝ ∞ (chartCoef (-1) (by norm_num) η)

lemma eta_DtauS {s : ℝ} (hs : s ^ 2 = 1) {η : S2 → E2 →L[ℝ] E} (hη : IsAntiJ J₀ η) (z c : ℂ) :
    η ((holChart s hs).symm z) (DtauS s hs z c) =
      cmulL J₀ ((starRingEnd ℂ) c) (chartCoef s hs η z) := by
  have hc : c = c.re • (1 : ℂ) + c.im • (Complex.I * 1) := by apply Complex.ext <;> simp
  have hj : η ((holChart s hs).symm z) (DtauS s hs z (Complex.I * 1)) =
      -J₀ (chartCoef s hs η z) := by
    rw [DtauS_I, chartCoef, hη, neg_neg]
  rw [hc, map_add, map_smul, map_smul, map_add, map_smul, map_smul, hj, cmulL_apply]
  simp only [map_add, Complex.conj_re, Complex.conj_im, Complex.add_re, Complex.add_im,
    Complex.smul_re, Complex.smul_im, Complex.one_re, Complex.one_im, Complex.mul_re,
    Complex.mul_im, Complex.I_re, Complex.I_im, chartCoef]
  module

/-- **The change of charts**: for an anti-linear form, `coef₋(w) = -(w̄²)⁻¹ coef₊(1/w)`. -/
theorem chartCoef_neg_eq {η : S2 → E2 →L[ℝ] E} (hη : IsAntiJ J₀ η) {w : ℂ} (hw : w ≠ 0) :
    chartCoef (-1) (by norm_num) η w =
      cmulL J₀ (-((starRingEnd ℂ) w ^ 2)⁻¹) (chartCoef 1 (by norm_num) η w⁻¹) := by
  rw [chartCoef, DtauS_neg hw, mul_one]
  have e := eta_DtauS (s := 1) (by norm_num) hη w⁻¹ (-(w ^ 2)⁻¹)
  rw [tau_neg_eq hw]
  convert e using 2
  simp [map_neg, map_inv₀, map_pow]

/-! ## 3. The solution on the sphere -/

/-- In the chart `σ_s`: if `ξ ∘ σ_s⁻¹ = F` and `∂̄F(z) = coef_s η (z)`, then
`½ (dξ + J₀ dξ j) = η` at `σ_s⁻¹ z`. -/
theorem projF_dForm_eq (hJ : ∀ v, J₀ (J₀ v) = -v) {s : ℝ} (hs : s ^ 2 = 1)
    {η : S2 → E2 →L[ℝ] E} (hη : IsAntiJ J₀ η) {ξ : S2 → E}
    (hξ : MDifferentiable 𝓘(ℝ, E2) 𝓘(ℝ, E) ξ) {F : ℂ → E}
    (hcomp : ξ ∘ (holChart s hs).symm = F) (z : ℂ)
    (hdbar : dbar J₀ F z = chartCoef s hs η z) :
    projF (X := sphere3) J₀ (dForm (X := sphere3) ξ) ((holChart s hs).symm z) =
      η ((holChart s hs).symm z) := by
  set y := (holChart s hs).symm z
  have hD : ∀ c : ℂ, dForm (X := sphere3) ξ y (DtauS s hs z c) = fderiv ℝ F z c := by
    intro c
    have h := mfderiv_comp z (hξ y) (mdifferentiable_holChart_symm s hs z)
    rw [hcomp, mfderiv_eq_fderiv] at h
    exact (congrArg (fun L => L c) h).symm
  ext v
  rw [← DtauS_DsigS s hs z v]
  set c := DsigS s hs y v
  have hj : sphere3.j.J y (DtauS s hs z c) = DtauS s hs z (Complex.I * c) := (DtauS_I s hs z c).symm
  have hL : projF (X := sphere3) J₀ (dForm (X := sphere3) ξ) y (DtauS s hs z c) =
      (1 / 2 : ℝ) • (fderiv ℝ F z c + J₀ (fderiv ℝ F z (Complex.I * c))) := by
    change (1 / 2 : ℝ) • (dForm (X := sphere3) ξ y (DtauS s hs z c) +
      J₀ (dForm (X := sphere3) ξ y (sphere3.j.J y (DtauS s hs z c)))) = _
    rw [hj, hD, hD]
  rw [hL, eta_DtauS hs hη, ← hdbar, dbar_eq_dbarL, ← dbarL_comp_mul hJ]
  simp only [dbarL, ContinuousLinearMap.comp_apply, ContinuousLinearMap.mul_apply', mul_one,
    mul_comm c Complex.I]

/-- **`∂̄ξ = η` on the sphere**: for a smooth anti-linear form `η` there is a smooth section
`ξ : S² → E` with `½ (dξ + J₀ dξ j) = η`. -/
theorem exists_sphere_solution (hJ : ∀ v, J₀ (J₀ v) = -v) {η : S2 → E2 →L[ℝ] E}
    (hη : IsAntiJ J₀ η) (hsm : IsSphereSmooth η) :
    ∃ ξ : S2 → E, ContMDiff 𝓘(ℝ, E2) 𝓘(ℝ, E) ∞ ξ ∧
      ∀ y, projF (X := sphere3) J₀ (dForm (X := sphere3) ξ) y = η y := by
  obtain ⟨F, F', hF, hF', hdF, hdF', hFF'⟩ :=
    exists_dbar_sphere hJ hsm.1 hsm.2 fun w hw => chartCoef_neg_eq hη hw
  set τ' := (holChart (-1) (by norm_num : (-1 : ℝ) ^ 2 = 1)).symm
  let ξ : S2 → E := fun y => if y = pt 2 then F' 0 else F (sig y)
  have hξ1 : ∀ z, ξ (sig.symm z) = F z := fun z => by
    have h : sig.symm z ≠ pt 2 := (mem_sig_source_iff _).1 (sig_symm_mem z)
    simp only [ξ, if_neg h, sig_sig_symm]
  have hξ2 : ∀ w, ξ (τ' w) = F' w := fun w => by
    by_cases hw : w = 0
    · subst hw; simp only [ξ, τ', holChart_neg_symm_zero, if_pos rfl]
    · rw [show τ' w = sig.symm w⁻¹ from tau_neg_eq hw, hξ1, hFF' w hw]
  have hsrc : pt 2 ∈ (holChart (-1) (by norm_num : (-1 : ℝ) ^ 2 = 1)).source := by
    change (-1) * (pt 2 : E3) 2 ≠ 1
    simp [pt]; norm_num
  have hsm' : ContMDiff 𝓘(ℝ, E2) 𝓘(ℝ, E) ∞ ξ := by
    intro y
    by_cases hy : y = pt 2
    · subst hy
      refine (hF'.contMDiff.contMDiffAt.comp _
        (contMDiffAt_holChart (-1) (by norm_num) hsrc)).congr_of_eventuallyEq ?_
      filter_upwards [(holChart (-1) (by norm_num : (-1 : ℝ) ^ 2 = 1)).open_source.mem_nhds hsrc]
        with y' hy'
      change ξ y' = F' (holChart (-1) (by norm_num) y')
      rw [← hξ2, (holChart (-1) (by norm_num : (-1 : ℝ) ^ 2 = 1)).left_inv hy']
    · have hys : y ∈ sig.source := (mem_sig_source_iff y).2 hy
      refine (hF.contMDiff.contMDiffAt.comp _
        (contMDiffAt_holChart 1 (by norm_num) hys)).congr_of_eventuallyEq ?_
      filter_upwards [sig.open_source.mem_nhds hys] with y' hy'
      change ξ y' = F (sig y')
      rw [← hξ1, sig.left_inv hy']
  have hmd : MDifferentiable 𝓘(ℝ, E2) 𝓘(ℝ, E) ξ := hsm'.mdifferentiable (by simp)
  refine ⟨ξ, hsm', fun y => ?_⟩
  by_cases hy : y = pt 2
  · subst hy
    rw [← holChart_neg_symm_zero]
    exact projF_dForm_eq hJ (by norm_num) hη hmd (funext hξ2) 0 (hdF' 0)
  · rw [← sig.left_inv ((mem_sig_source_iff y).2 hy)]
    exact projF_dForm_eq hJ (by norm_num) hη hmd (funext hξ1) _ (hdF _)

end Coef

/-! ## 4. Smooth sections in the blocks -/

section Blocks

/-- The `tsupport` of `∂_s^a ∂_t^b F` lies in that of `F`. -/
lemma tsupport_pD_subset (F : ℝ × ℝ → ℝ) (a b : ℕ) : tsupport (pD a b F) ⊆ tsupport F := by
  have ht : ∀ b, tsupport (Dt^[b] F) ⊆ tsupport F := by
    intro b
    induction b with
    | zero => exact subset_rfl
    | succ b ih =>
      rw [Function.iterate_succ_apply']
      exact (ChartChange.tsupport_dir_subset _ _).trans ih
  induction a with
  | zero => exact ht b
  | succ a ih => rw [← ChartChange.Ds_pD]; exact (ChartChange.tsupport_dir_subset _ _).trans ih

instance : IsFiniteMeasureOnCompacts cyl :=
  ⟨fun K hK => (Measure.le_iff'.1 cyl_le_vol K).trans_lt hK.measure_lt_top⟩

variable {F : ℝ × ℝ → ℝ} (hF : ContDiff ℝ ∞ F) (hFK : tsupport F ⊆ closedDisc)

include hFK in
lemma hasCompactSupport_of_closedDisc : HasCompactSupport F :=
  isCompact_closedDisc.of_isClosed_subset (isClosed_tsupport F) hFK

include hF hFK in
lemma memLp_of_closedDisc : MemLp F 2 cyl :=
  hF.continuous.memLp_of_hasCompactSupport (hasCompactSupport_of_closedDisc hFK)

include hF hFK in
lemma memH_of_closedDisc (m : ℕ) (δ : ℝ) {hδ : 0 ≤ δ} :
    (memLp_of_closedDisc hF hFK).toLp F ∈ Hsub m hδ := fun a b _ =>
  ⟨pD a b F, (ChartChange.hasWeakDeriv_of_supp isCompact_closedDisc closedDisc_sub hF hFK a b)
    |>.congr_ae (memLp_of_closedDisc hF hFK).coeFn_toLp.symm (ae_eq_refl _),
    ((continuous_wt δ).mul (contDiff_pD hF a b).continuous).memLp_of_hasCompactSupport
      (HasCompactSupport.mul_left (isCompact_closedDisc.of_isClosed_subset (isClosed_tsupport _)
        ((tsupport_pD_subset F a b).trans hFK)))⟩

/-- A smooth function supported in the closed disc, as an element of `H^{m,δ}`. -/
def toHdisc (m : ℕ) {δ : ℝ} (hδ : 0 ≤ δ) : H m hδ :=
  (⟨(memLp_of_closedDisc hF hFK).toLp F, memH_of_closedDisc hF hFK m δ⟩ : Hsub m hδ)

lemma val_toHdisc (m : ℕ) {δ : ℝ} (hδ : 0 ≤ δ) :
    (H.val (toHdisc hF hFK m hδ) : ℝ × ℝ → ℝ) =ᵐ[cyl] F :=
  (memLp_of_closedDisc hF hFK).coeFn_toLp

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {Q : Type} [TopologicalSpace Q] [ChartedSpace E Q] [IsManifold 𝓘(ℝ, E) ∞ Q]
  {q : Q} (A : SectionAtlas (E := E) sphere3 (fun _ => q))
  (δ : ℕ → ℝ) (h0 : 0 ≤ δ 0) (hmono : StrictMono δ)

variable {ξ : S2 → E} (hξ : ContMDiff 𝓘(ℝ, E2) 𝓘(ℝ, E) ∞ ξ)

/-- The disc representative `β · e_k*(ξ ∘ discPt)` of a smooth section. -/
def secDisc (ξ : S2 → E) (i : Fin A.nd) (k : Fin (Module.finrank ℝ E)) (p : ℝ × ℝ) : ℝ :=
  discCut p * crd k (ξ (sphere3.discPt (A.center i) (A.ε i) p))

include hξ in
lemma contDiff_secDisc (i : Fin A.nd) (k : Fin (Module.finrank ℝ E)) :
    ContDiff ℝ ∞ (secDisc A ξ i k) :=
  contDiff_discCut.mul ((crdL k).contDiff.comp (contMDiff_iff_contDiff.1
    (hξ.comp (contMDiff_discPt sphere3_chartsOnto _ _))))

lemma tsupport_secDisc (i : Fin A.nd) (k : Fin (Module.finrank ℝ E)) :
    tsupport (secDisc A ξ i k) ⊆ closedDisc :=
  (tsupport_mul_subset_left).trans tsupport_discCut

/-- The level-`0` blocks of a smooth section. -/
def smoothBlocks (hξ : ContMDiff 𝓘(ℝ, E2) 𝓘(ℝ, E) ∞ ξ) : (blocks A δ h0 hmono) 0 :=
  (fun ik => toHdisc (contDiff_secDisc A hξ ik.1 ik.2) (tsupport_secDisc A ik.1 ik.2) (3 + 0)
      (Neck.δ_nonneg δ h0 hmono 0),
    fun jk => (isEmpty_neck_of_nodes_empty rfl A).elim jk.1)

theorem isRep_smoothBlocks : IsRep ξ (smoothBlocks A δ h0 hmono hξ) := by
  refine ⟨fun i k => ?_, fun j => (isEmpty_neck_of_nodes_empty rfl A).elim j⟩
  refine (val_toHdisc (contDiff_secDisc A hξ i k) (tsupport_secDisc A i k) _ _).trans
    (Eventually.of_forall fun p => ?_)
  exact (discRep_const (X := sphere3) (fun _ => rfl) A i k ξ p).symm

theorem smoothBlocks_mem : smoothBlocks A δ h0 hmono hξ ∈ sectionSpace A δ h0 hmono := by
  refine Submodule.le_topologicalClosure _ ⟨ξ, fun x => ?_, fun x y h => ?_,
    isRep_smoothBlocks A δ h0 hmono hξ⟩
  · simp only [tangentCoordChange_self (mem_extChartAt_source q)]
    exact hξ.continuous.continuousAt
  · exact absurd h (notMem_empty _)

end Blocks

/-! ## 5. The range of `D` and the vanishing of the cokernel -/

section Range

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {Q : Type} [TopologicalSpace Q] [ChartedSpace E Q] [IsManifold 𝓘(ℝ, E) ∞ Q]
variable (J : AlmostComplexStructure E Q) {q : Q} {A : SectionAtlas (E := E) sphere3 (fun _ => q)}
  (G : GlueData A) (δ : ℕ → ℝ) (h0 : 0 ≤ δ 0) (hmono : StrictMono δ)

lemma acs_sq (x : Q) (v : E) : J.J x (J.J x v) = -v := by
  simpa using congrArg (fun L => L v) (J.sq x)

lemma isAntiJ_iff {η : Form E sphere3} :
    IsAntiJ (J.J q) η ↔ IsAntiOff J sphere3 (fun _ => q) η := by
  constructor
  · intro h x _
    exact (NodalSurface.mem_antiLinearForms J sphere3).2 fun v => h x v
  · intro h y v
    exact (NodalSurface.mem_antiLinearForms J sphere3).1
      (h y fun p hp => absurd hp (notMem_empty p)) v

/-- **`D` hits the representative of every smooth anti-linear form**: for `η` anti-linear for
`(j, J(q))` with smooth coefficients in both holomorphic charts, and `y` its representative,
`y = D w` for a section `w ∈ H^{3,δ₀}_c(S², u*TQ)` (the Cauchy transform). -/
theorem linCR3_hits {η : Form E sphere3} (hη : IsAntiJ (J.J q) η) (hsm : IsSphereSmooth η)
    {y : (fibreBlocks A δ h0 hmono) 0} (hy : IsFormRep η y) :
    ∃ w : sectionSpace A δ h0 hmono,
      (linCR3 J G δ h0 hmono w : (fibreBlocks A δ h0 hmono) 0) = y := by
  obtain ⟨ξ, hξ, hξη⟩ := exists_sphere_solution (acs_sq J q) hη hsm
  have hc : IsContSection (X := sphere3) (fun _ => q) ξ := fun x => by
    simp only [tangentCoordChange_self (mem_extChartAt_source q)]
    exact hξ.continuous.continuousAt
  have hr := isRep_smoothBlocks A δ h0 hmono hξ
  have h := isFormRep_linOp (X := sphere3) rfl sphere3_chartsOnto (fun _ => rfl) G hc hr (J.J q)
  have he : projF (X := sphere3) (J.J q) (dForm (X := sphere3) ξ) = η := funext hξη
  rw [he] at h
  exact ⟨⟨smoothBlocks A δ h0 hmono hξ, smoothBlocks_mem A δ h0 hmono hξ⟩,
    (linCR_apply rfl sphere3_chartsOnto (fun _ => rfl) G J _).trans (h.unique hy)⟩

/-- The representatives of the smooth anti-linear forms, in the fibre. -/
def smoothFormReps : Set (fibreSpace J A δ h0 hmono) :=
  {y | ∃ η : Form E sphere3, IsAntiJ (J.J q) η ∧ IsSphereSmooth η ∧
    IsFormRep η (y : (fibreBlocks A δ h0 hmono) 0)}

/-- **The density of the smooth anti-linear forms in the fibre** (the classical input which
`FormsDensity` gives for the forms built from test functions in the disc charts). -/
def SmoothFormsDense : Prop := Dense (smoothFormReps J δ h0 hmono (A := A))

theorem smoothFormReps_subset_range :
    smoothFormReps J δ h0 hmono (A := A) ⊆ range (linCR3 J G δ h0 hmono) := by
  rintro y ⟨η, hη, hsm, hy⟩
  obtain ⟨w, hw⟩ := linCR3_hits J G δ h0 hmono hη hsm hy
  exact ⟨w, Subtype.ext hw⟩

/-- **The range of `D` is dense**, given the density of the smooth forms. -/
theorem denseRange_linCR3 (h : SmoothFormsDense J δ h0 hmono (A := A)) :
    DenseRange (linCR3 J G δ h0 hmono) :=
  h.mono (smoothFormReps_subset_range J G δ h0 hmono)

/-- **Closed and dense range: `CokernelVanishes`.** -/
theorem cokernelVanishes_of_denseRange (hδ : 0 < δ 0) (hE : EllipticEstimate J G δ h0 hmono hδ)
    (hd : DenseRange (linCR3 J G δ h0 hmono)) : CokernelVanishes J G δ h0 hmono := by
  have hc := linCR_isClosed_range J G δ h0 hmono hδ hE
  have hr : ((linCR3 J G δ h0 hmono).range : Set (fibreSpace J A δ h0 hmono)) =
      range (linCR3 J G δ h0 hmono) := LinearMap.coe_range _
  rw [hr] at hc
  intro y
  have : y ∈ closure (range (linCR3 J G δ h0 hmono)) := hd.closure_eq ▸ mem_univ y
  rwa [hc.closure_eq] at this

/-- **`CokernelVanishes`** from the elliptic estimate and the density of the smooth forms:
`D` is onto, so Fredholm of index `dim E` (`linCR_isFredholm`, `linCR_index`). -/
theorem cokernelVanishes_sphere3 (hδ : 0 < δ 0) (hE : EllipticEstimate J G δ h0 hmono hδ)
    (h : SmoothFormsDense J δ h0 hmono (A := A)) : CokernelVanishes J G δ h0 hmono :=
  cokernelVanishes_of_denseRange J G δ h0 hmono hδ hE (denseRange_linCR3 J G δ h0 hmono h)

end Range

end GWMemoir
