import GWMemoir.CokernelNodesNeck

/-!
# Sections at a constant map from two spheres joined at a node

HWZ, *Applications of Polyfold Theory I*, Memoirs AMS 248, no. 1179, §3.1 (pp. 66–68) and §4
(Props 4.7, 4.23, pp. 102–118), at the constant map `u ≡ q` from `twoSpheres` (two round spheres
joined at the nodal pair `{e₂, e₂}`), with an atlas whose neck charts are `σ₋₁`
(`IsStdNeck`, witness `exists_stdNeck_atlas` in `GWMemoir.CokernelNodesNeck`).

* **`neckRep_decay`**: for a smooth section `ξ`, the neck representative
  `β(s) (ξ(σ(s + s₀, t)) - ξ(x))` and all its derivatives are `O(e^{-2πs})`.
* **`smoothNeckRep_mem`**: for `0 ≤ δ₀ < 2π`, a smooth section with matching values at the node
  has its representatives in the blocks, so it lies in `H^{3,δ₀}_c` (`sectionSpace`).
* **`exists_twoSpheres_solution`**: for a smooth anti-linear form `η` there is an element of
  `sectionSpace` represented by a smooth section `ξ` with `½ (dξ + J₀ dξ j) = η` (the Cauchy
  transform on each sphere, `exists_sphere_solution`, and a constant added on the second sphere
  to match the values at the node).
* **`not_mem_sectionSpace_of_two_pi_le`** (the example of §4): for `δ₀ ≥ 2π`, the smooth section
  `ξ = c + χ(z) z·e` (`z = σ₋₁` on the first sphere, `z·e = Re z e + Im z J₀ e`, `χ` a cut-off
  equal to `1` near the node; `contMDiff_exSection`, `exSection_cont_matching`) has no tuple of
  representatives in the blocks: in the polar coordinates, `ξ ∘ σ - c = e^{-2π(s+it)}·e`, which is
  not in `L²(e^{2δ₀ s})`.
-/

set_option maxSynthPendingDepth 3
set_option linter.unusedSectionVars false

open scoped Manifold ContDiff Topology
open Set Function Filter MeasureTheory
open Polyfold Polyfold.CylinderSobolev

noncomputable section

namespace GWMemoir

/-! ## 1. The neck representatives of smooth sections -/

section SmoothNeck

/-- The cut-off `β(s)` read in the coordinate `w = e^{-2π((s+s₀)+it)}`:
`β(-log|w|/(2π) - s₀)`. -/
def cutW (s₀ : ℝ) (w : ℂ) : ℝ := Real.smoothTransition (-Real.log ‖w‖ / (2 * Real.pi) - s₀)

lemma cutW_ePol (s₀ : ℝ) (p : ℝ × ℝ) : cutW s₀ (ePol s₀ p) = Real.smoothTransition p.1 := by
  rw [cutW, norm_ePol, Real.log_exp]
  congr 1
  field_simp
  ring

lemma cutW_eq_one {s₀ : ℝ} {w : ℂ} (hw0 : w ≠ 0)
    (hw : ‖w‖ < Real.exp (-2 * Real.pi * (s₀ + 1))) : cutW s₀ w = 1 := by
  refine Real.smoothTransition.one_of_one_le ?_
  have hl : Real.log ‖w‖ < -2 * Real.pi * (s₀ + 1) :=
    (Real.log_lt_iff_lt_exp (norm_pos_iff.2 hw0)).2 hw
  rw [le_sub_iff_add_le, le_div_iff₀ (by positivity)]
  linarith

lemma cutW_eq_zero {s₀ : ℝ} {w : ℂ} (hw : Real.exp (-2 * Real.pi * s₀) < ‖w‖) :
    cutW s₀ w = 0 := by
  refine Real.smoothTransition.zero_of_nonpos ?_
  have hl : -2 * Real.pi * s₀ < Real.log ‖w‖ :=
    (Real.lt_log_iff_exp_lt ((Real.exp_pos _).trans hw)).2 hw
  rw [sub_nonpos, div_le_iff₀ (by positivity)]
  linarith

lemma contDiffAt_cutW (s₀ : ℝ) {w : ℂ} (hw : w ≠ 0) : ContDiffAt ℝ ∞ (cutW s₀) w := by
  have hl : ContDiffAt ℝ ∞ (fun w : ℂ => Real.log ‖w‖) w :=
    (Real.contDiffAt_log.2 (norm_ne_zero_iff.2 hw)).comp w (contDiffAt_norm ℝ hw)
  exact Real.smoothTransition.contDiff.contDiffAt.comp w
    (((hl.neg).div_const _).sub contDiffAt_const)

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {Q : Type} [TopologicalSpace Q] [ChartedSpace E Q] [IsManifold 𝓘(ℝ, E) ∞ Q]

/-- The neck function of `g : S² → E` at `e₂`, coordinate `k`, in the coordinate `w` of `σ₋₁`:
`β · (e_k*(g(σ₋₁⁻¹ w)) - e_k*(g(e₂)))`. -/
def neckFn (g : S2 → E) (k : Fin (Module.finrank ℝ E)) (s₀ : ℝ) (w : ℂ) : ℝ :=
  cutW s₀ w * (crd k (g ((holChart (-1) (by norm_num)).symm w)) - crd k (g (pt 2)))

theorem neckCls_neckFn {g : S2 → E} (hg : ContMDiff 𝓘(ℝ, E2) 𝓘(ℝ, E) ∞ g)
    (k : Fin (Module.finrank ℝ E)) (s₀ : ℝ) :
    NeckCls (Real.exp (-2 * Real.pi * s₀)) (neckFn g k s₀) := by
  set τ := (holChart (-1) (by norm_num : (-1 : ℝ) ^ 2 = 1)).symm
  have hgh : ContDiff ℝ ∞ fun w => crd k (g (τ w)) - crd k (g (pt 2)) :=
    ((crdL k).contDiff.comp (contMDiff_iff_contDiff.1
      (hg.comp (contMDiff_holChart_symm (-1) (by norm_num))))).sub contDiff_const
  have h0 : crd k (g (τ 0)) - crd k (g (pt 2)) = 0 := by
    simp only [τ, holChart_neg_symm_zero, sub_self]
  refine ⟨contDiff_iff_contDiffAt.2 fun w => ?_, ?_, fun w hw => ?_⟩
  · by_cases hw : w = 0
    · subst hw
      refine hgh.contDiffAt.congr_of_eventuallyEq ?_
      filter_upwards [Metric.ball_mem_nhds (0 : ℂ) (Real.exp_pos (-2 * Real.pi * (s₀ + 1)))]
        with w hw'
      by_cases hw0 : w = 0
      · subst hw0; simp only [neckFn]; rw [show τ = _ from rfl] at h0; rw [h0, mul_zero]
      · rw [neckFn, cutW_eq_one hw0 (mem_ball_zero_iff.1 hw'), one_mul]
    · exact (contDiffAt_cutW s₀ hw).mul hgh.contDiffAt
  · simp only [neckFn]; rw [show τ = _ from rfl] at h0; rw [h0, mul_zero]
  · rw [neckFn, cutW_eq_zero hw, zero_mul]

variable {q : Q} {A : SectionAtlas (E := E) twoSpheres (fun _ => q)}

lemma tcc_const_q (v : E) : tangentCoordChange 𝓘(ℝ, E) q q q v = v :=
  tangentCoordChange_self (mem_extChartAt_source q)

/-- In the standard neck charts, the neck representative of `ξ` at `inl e₂` is
`neckFn (ξ ∘ inl) ∘ ePol s₀`. -/
lemma neckRep_eq_inl (hA : IsStdNeck A) {j : Fin A.nn} (hj : A.node j = Sum.inl (pt 2))
    (k : Fin (Module.finrank ℝ E)) (ξ : Section E twoSpheres) :
    neckRep A j k ξ = neckFn (fun y => ξ (Sum.inl y)) k (A.s0 j) ∘ ePol (A.s0 j) := by
  funext p
  simp only [neckRep, neckConst, hA j, hj, polar_nodeChart_inl, tcc_const_q, comp_apply, neckFn,
    cutW_ePol]
  rfl

lemma neckRep_eq_inr (hA : IsStdNeck A) {j : Fin A.nn} (hj : A.node j = Sum.inr (pt 2))
    (k : Fin (Module.finrank ℝ E)) (ξ : Section E twoSpheres) :
    neckRep A j k ξ = neckFn (fun y => ξ (Sum.inr y)) k (A.s0 j) ∘ ePol (A.s0 j) := by
  funext p
  simp only [neckRep, neckConst, hA j, hj, polar_nodeChart_inr, tcc_const_q, comp_apply, neckFn,
    cutW_ePol]
  rfl

variable {ξ : Section E twoSpheres} (hξ : ContMDiff 𝓘(ℝ, E2) 𝓘(ℝ, E) ∞ ξ)

include hξ in
lemma exists_neckCls_neckRep (hA : IsStdNeck A) (j : Fin A.nn) (k : Fin (Module.finrank ℝ E)) :
    ∃ H, NeckCls (Real.exp (-2 * Real.pi * A.s0 j)) H ∧ neckRep A j k ξ = H ∘ ePol (A.s0 j) := by
  rcases A.node_cases j with hj | hj
  · exact ⟨_, neckCls_neckFn (hξ.comp ContMDiff.inl) k _, neckRep_eq_inl hA hj k ξ⟩
  · exact ⟨_, neckCls_neckFn (hξ.comp ContMDiff.inr) k _, neckRep_eq_inr hA hj k ξ⟩

/-- For `s ≥ 1` the neck representative is `v⁺(s + s₀, t) - c = ξ(σ(s + s₀, t)) - ξ(x)`. -/
lemma neckRep_of_one_le (j : Fin A.nn) (k : Fin (Module.finrank ℝ E)) (ξ : Section E twoSpheres)
    {p : ℝ × ℝ} (hp : 1 ≤ p.1) :
    neckRep A j k ξ p = crd k (ξ (twoSpheres.polar (A.hol j) (p.1 + A.s0 j, p.2))) -
      crd k (ξ (A.node j)) := by
  simp only [neckRep, neckConst, tcc_const_q, Real.smoothTransition.one_of_one_le hp, one_mul]

include hξ in
/-- **Decay at the node**: for a smooth section `ξ`, the neck representative
`β(s) (ξ(σ(s + s₀, t)) - ξ(x))` and all its derivatives are `O(e^{-2πs})`. -/
theorem neckRep_decay (hA : IsStdNeck A) (j : Fin A.nn) (k : Fin (Module.finrank ℝ E))
    (a b : ℕ) : ∃ C, ∀ p : ℝ × ℝ,
      |pD a b (neckRep A j k ξ) p| ≤ C * Real.exp (-2 * Real.pi * p.1) := by
  obtain ⟨H, hH, e⟩ := exists_neckCls_neckRep hξ hA j k
  obtain ⟨G, hG, e'⟩ := pD_comp_ePol hH (A.s0 j) a b
  obtain ⟨M, hM⟩ := hG.bound
  refine ⟨M * Real.exp (-2 * Real.pi * A.s0 j), fun p => ?_⟩
  rw [e, e', comp_apply]
  refine (hM _).trans (le_of_eq ?_)
  rw [norm_ePol, mul_assoc M, ← Real.exp_add]
  congr 2
  ring

include hξ in
theorem memH_neckRep (hA : IsStdNeck A) (j : Fin A.nn) (k : Fin (Module.finrank ℝ E)) (k' : ℕ)
    {δ₀ : ℝ} (hδ : δ₀ < 2 * Real.pi) : MemH k' δ₀ (neckRep A j k ξ) := by
  obtain ⟨H, hH, e⟩ := exists_neckCls_neckRep hξ hA j k
  rw [e]; exact memH_comp_ePol hH k' hδ

include hξ in
theorem memLp_neckRep (hA : IsStdNeck A) (j : Fin A.nn) (k : Fin (Module.finrank ℝ E)) :
    MemLp (neckRep A j k ξ) 2 cyl := by
  obtain ⟨H, hH, e⟩ := exists_neckCls_neckRep hξ hA j k
  rw [e]; exact memLp_comp_ePol hH

end SmoothNeck

/-! ## 2. Smooth sections in `H^{3,δ₀}_c` for `δ₀ < 2π` -/

section Blocks

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {Q : Type} [TopologicalSpace Q] [ChartedSpace E Q] [IsManifold 𝓘(ℝ, E) ∞ Q]
  {q : Q} (A : SectionAtlas (E := E) twoSpheres (fun _ => q))
  (δ : ℕ → ℝ) (h0 : 0 ≤ δ 0) (hmono : StrictMono δ)

lemma mem_Hsub_toLp {k : ℕ} {d : ℝ} (hd : 0 ≤ d) {F : ℝ × ℝ → ℝ} (hF : MemLp F 2 cyl)
    (h : MemH k d F) : hF.toLp F ∈ Hsub k hd := fun a b hab => by
  obtain ⟨g, hg, hgw⟩ := h a b hab
  exact ⟨g, hg.congr_ae hF.coeFn_toLp.symm (ae_eq_refl _), hgw⟩

/-- The disc representative `β · e_k*(ξ ∘ discPt)` of a section of `twoSpheres`. -/
def secDisc2 (ξ : Section E twoSpheres) (i : Fin A.nd) (k : Fin (Module.finrank ℝ E))
    (p : ℝ × ℝ) : ℝ :=
  discCut p * crd k (ξ (twoSpheres.discPt (A.center i) (A.ε i) p))

variable {A} {ξ : Section E twoSpheres} (hξ : ContMDiff 𝓘(ℝ, E2) 𝓘(ℝ, E) ∞ ξ)

include hξ in
lemma contDiff_secDisc2 (i : Fin A.nd) (k : Fin (Module.finrank ℝ E)) :
    ContDiff ℝ ∞ (secDisc2 A ξ i k) :=
  contDiff_discCut.mul ((crdL k).contDiff.comp (contMDiff_iff_contDiff.1
    (hξ.comp (contMDiff_discPt twoSpheres_target _ _))))

lemma tsupport_secDisc2 (i : Fin A.nd) (k : Fin (Module.finrank ℝ E)) :
    tsupport (secDisc2 A ξ i k) ⊆ closedDisc :=
  (tsupport_mul_subset_left).trans tsupport_discCut

variable (hA : IsStdNeck A) (hδ : δ 0 < 2 * Real.pi)

/-- The neck block `β (v⁺ - c) ∈ H^{3,δ₀}` of a smooth section, for `δ₀ < 2π`. -/
def neckH (j : Fin A.nn) (k : Fin (Module.finrank ℝ E)) : H 3 (Neck.δ_nonneg δ h0 hmono 0) :=
  (⟨(memLp_neckRep hξ hA j k).toLp _,
    mem_Hsub_toLp _ (memLp_neckRep hξ hA j k) (memH_neckRep hξ hA j k 3 hδ)⟩ : Hsub 3 _)

/-- The level-`0` blocks of a smooth section of `twoSpheres`, for `δ₀ < 2π`. -/
def smoothBlocks2 : (blocks A δ h0 hmono) 0 :=
  (fun ik => toHdisc (contDiff_secDisc2 hξ ik.1 ik.2) (tsupport_secDisc2 ik.1 ik.2) (3 + 0)
      (Neck.δ_nonneg δ h0 hmono 0),
    fun jk => (crd jk.2 (ξ (A.node jk.1)), neckH δ h0 hmono hξ hA hδ jk.1 jk.2))

theorem isRep_smoothBlocks2 : IsRep ξ (smoothBlocks2 δ h0 hmono hξ hA hδ) := by
  refine ⟨fun i k => ?_, fun j k => ⟨rfl, ?_⟩⟩
  · refine (val_toHdisc (contDiff_secDisc2 hξ i k) (tsupport_secDisc2 i k) _ _).trans
      (Eventually.of_forall fun p => ?_)
    exact (discRep_const (X := twoSpheres) (fun _ => rfl) A i k ξ p).symm
  · exact (memLp_neckRep hξ hA j k).coeFn_toLp

lemma isMatchingSection_twoSpheres {η : Section E twoSpheres}
    (hm : η (Sum.inl (pt 2)) = η (Sum.inr (pt 2))) : IsMatchingSection twoSpheres η := by
  intro x y hxy
  obtain h | h := Sym2.eq_iff.1 (show s(x, y) = s(Sum.inl (pt 2), Sum.inr (pt 2)) from hxy)
  · rw [h.1, h.2]; exact hm
  · rw [h.1, h.2]; exact hm.symm

include hξ in
/-- **Smooth sections lie in `H^{3,δ₀}_c` for `0 ≤ δ₀ < 2π`** (Memoir p. 66, at the node): a
smooth section of `u*TQ = E` over `twoSpheres` with matching values at the node has its local
representatives in the blocks, the neck blocks by `neckRep_decay` (`O(e^{-2πs})` is in
`L²(e^{2δ₀ s})` for `δ₀ < 2π`). -/
theorem smoothNeckRep_mem (hm : ξ (Sum.inl (pt 2)) = ξ (Sum.inr (pt 2))) :
    smoothBlocks2 δ h0 hmono hξ hA hδ ∈ sectionSpace A δ h0 hmono :=
  Submodule.le_topologicalClosure _ ⟨ξ, isContSection_of_const (fun _ => rfl) hξ.continuous,
    isMatchingSection_twoSpheres hm, isRep_smoothBlocks2 δ h0 hmono hξ hA hδ⟩

end Blocks

/-! ## 3. `∂̄ξ = η` on two spheres joined at a node -/

section Solution

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {J₀ : E →L[ℝ] E}

lemma projF_apply {m : ℕ} {X : NodalSurface m} (F : Form E X) (x : X.S) :
    projF (X := X) J₀ F x = (1 / 2 : ℝ) • (F x + J₀.comp ((F x).comp (X.j.J x))) := rfl

lemma projF_dForm_inl (ξ : Section E twoSpheres) (y : S2) :
    projF (X := twoSpheres) J₀ (dForm (X := twoSpheres) ξ) (Sum.inl y) =
      projF (X := sphere3) J₀ (dForm (X := sphere3) fun y => ξ (Sum.inl y)) y := by
  have e : dForm (X := twoSpheres) ξ (Sum.inl y) =
      dForm (X := sphere3) (fun y => ξ (Sum.inl y)) y :=
    by exact mfderiv_inl (I := 𝓘(ℝ, E2)) (I' := 𝓘(ℝ, E)) _ y
  exact congrArg (fun F : E2 →L[ℝ] E => (1 / 2 : ℝ) • (F + J₀.comp (F.comp (jStdMap y)))) e

lemma projF_dForm_inr (ξ : Section E twoSpheres) (y : S2) :
    projF (X := twoSpheres) J₀ (dForm (X := twoSpheres) ξ) (Sum.inr y) =
      projF (X := sphere3) J₀ (dForm (X := sphere3) fun y => ξ (Sum.inr y)) y := by
  have e : dForm (X := twoSpheres) ξ (Sum.inr y) =
      dForm (X := sphere3) (fun y => ξ (Sum.inr y)) y :=
    by exact mfderiv_inr (I := 𝓘(ℝ, E2)) (I' := 𝓘(ℝ, E)) _ y
  exact congrArg (fun F : E2 →L[ℝ] E => (1 / 2 : ℝ) • (F + J₀.comp (F.comp (jStdMap y)))) e

lemma mfderiv_add_const' {ξ : S2 → E} (hξ : MDifferentiable 𝓘(ℝ, E2) 𝓘(ℝ, E) ξ) (c : E)
    (y : S2) : (mfderiv 𝓘(ℝ, E2) 𝓘(ℝ, E) (fun y => ξ y + c) y : E2 →L[ℝ] E) =
      mfderiv 𝓘(ℝ, E2) 𝓘(ℝ, E) ξ y := by
  have h := mfderiv_add (I := 𝓘(ℝ, E2)) (hξ y) (mdifferentiableAt_const (c := c))
  simp only [mfderiv_const] at h
  exact h.trans (add_zero (mfderiv 𝓘(ℝ, E2) 𝓘(ℝ, E) ξ y : E2 →L[ℝ] E))

lemma dForm_add_const {ξ : S2 → E} (hξ : MDifferentiable 𝓘(ℝ, E2) 𝓘(ℝ, E) ξ) (c : E) :
    dForm (X := sphere3) (fun y => ξ y + c) = dForm (X := sphere3) ξ :=
  funext fun y => mfderiv_add_const' hξ c y

/-- **`∂̄ξ = η` on `twoSpheres`**: for a smooth anti-linear form `η` (anti-linear for `(j, J₀)`,
smooth coefficients in both holomorphic charts of each sphere) there is a smooth section `ξ`
with matching values at the node and `½ (dξ + J₀ dξ j) = η`: solve on each sphere
(`exists_sphere_solution`) and add a constant to the second solution. -/
theorem exists_twoSpheres_smooth_solution (hJ : ∀ v, J₀ (J₀ v) = -v) {η : Form E twoSpheres}
    (hη₁ : IsAntiJ J₀ fun y => η (Sum.inl y)) (hη₂ : IsAntiJ J₀ fun y => η (Sum.inr y))
    (hs₁ : IsSphereSmooth fun y => η (Sum.inl y)) (hs₂ : IsSphereSmooth fun y => η (Sum.inr y)) :
    ∃ ξ : Section E twoSpheres, ContMDiff 𝓘(ℝ, E2) 𝓘(ℝ, E) ∞ ξ ∧
      ξ (Sum.inl (pt 2)) = ξ (Sum.inr (pt 2)) ∧
      ∀ x, projF (X := twoSpheres) J₀ (dForm (X := twoSpheres) ξ) x = η x := by
  obtain ⟨ξ₁, hξ₁, h₁⟩ := exists_sphere_solution hJ hη₁ hs₁
  obtain ⟨ξ₂, hξ₂, h₂⟩ := exists_sphere_solution hJ hη₂ hs₂
  set c := ξ₁ (pt 2) - ξ₂ (pt 2)
  refine ⟨Sum.elim ξ₁ fun y => ξ₂ y + c, hξ₁.sumElim (hξ₂.add contMDiff_const), ?_, ?_⟩
  · change ξ₁ (pt 2) = ξ₂ (pt 2) + (ξ₁ (pt 2) - ξ₂ (pt 2)); abel
  · rintro (y | y)
    · exact (projF_dForm_inl _ y).trans (h₁ y)
    · refine (projF_dForm_inr _ y).trans ?_
      change projF (X := sphere3) J₀ (dForm (X := sphere3) fun y => ξ₂ y + c) y = _
      rw [dForm_add_const (hξ₂.mdifferentiable (by simp)) c]
      exact h₂ y

variable {Q : Type} [TopologicalSpace Q] [ChartedSpace E Q] [IsManifold 𝓘(ℝ, E) ∞ Q]
  {q : Q} {A : SectionAtlas (E := E) twoSpheres (fun _ => q)}
  (δ : ℕ → ℝ) (h0 : 0 ≤ δ 0) (hmono : StrictMono δ)

/-- **`∂̄ξ = η` with `ξ ∈ H^{3,δ₀}_c`** (§3d of the plan of Prop 4.23 at a constant map with a
node), for `0 ≤ δ₀ < 2π` and the standard neck charts: for a smooth anti-linear form `η` there is
an element of `sectionSpace` represented by a smooth section `ξ` with `½ (dξ + J₀ dξ j) = η`.
No vanishing of `η` near the node is needed for this. -/
theorem exists_twoSpheres_solution (hA : IsStdNeck A) (hδ : δ 0 < 2 * Real.pi)
    (hJ : ∀ v, J₀ (J₀ v) = -v) {η : Form E twoSpheres}
    (hη₁ : IsAntiJ J₀ fun y => η (Sum.inl y)) (hη₂ : IsAntiJ J₀ fun y => η (Sum.inr y))
    (hs₁ : IsSphereSmooth fun y => η (Sum.inl y)) (hs₂ : IsSphereSmooth fun y => η (Sum.inr y)) :
    ∃ ξ : Section E twoSpheres, ∃ v ∈ sectionSpace A δ h0 hmono, IsRep ξ v ∧
      ∀ x, projF (X := twoSpheres) J₀ (dForm (X := twoSpheres) ξ) x = η x := by
  obtain ⟨ξ, hξ, hm, h⟩ := exists_twoSpheres_smooth_solution hJ hη₁ hη₂ hs₁ hs₂
  exact ⟨ξ, smoothBlocks2 δ h0 hmono hξ hA hδ, smoothNeckRep_mem δ h0 hmono hξ hA hδ hm,
    isRep_smoothBlocks2 δ h0 hmono hξ hA hδ, h⟩

end Solution

/-! ## 4. The example of §4: `δ₀ ≥ 2π` -/

section Example

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {Q : Type} [TopologicalSpace Q] [ChartedSpace E Q] [IsManifold 𝓘(ℝ, E) ∞ Q]
  {q : Q} {A : SectionAtlas (E := E) twoSpheres (fun _ => q)}
  {δ : ℕ → ℝ} {h0 : 0 ≤ δ 0} {hmono : StrictMono δ} {J₀ : E →L[ℝ] E}

/-- The cut-off `χ(w) = β(2 - |w|²)`: `1` for `|w| ≤ 1`, `0` for `|w|² ≥ 2`. -/
def chiC (w : ℂ) : ℝ := Real.smoothTransition (2 - ‖w‖ ^ 2)

lemma chiC_eq_one {w : ℂ} (hw : ‖w‖ ≤ 1) : chiC w = 1 :=
  Real.smoothTransition.one_of_one_le (by nlinarith [norm_nonneg w])

variable (J₀) in
/-- The section of §4: `c + χ(z) z·e` on the first sphere (`z = σ₋₁`, centred at the nodal point
`e₂`; `z·e = Re z e + Im z J₀ e`), and `c` on the second. -/
def exSection (c e : E) : Section E twoSpheres :=
  Sum.elim (fun y => c + chiC (holChart (-1) (by norm_num) y) •
    cmulL J₀ (holChart (-1) (by norm_num) y) e) fun _ => c

/-- `σ₋₁` takes the value `0` at the point it misses (Lean's `0⁻¹ = 0`). -/
lemma holChart_neg_of_not_mem {y : S2} (hy : y ∉ (holChart (-1) (by norm_num)).source) :
    holChart (-1) (by norm_num) y = 0 := by
  have h : -1 * (y : E3) 2 = 1 := not_not.1 hy
  change stereoC (-1) y = 0
  rw [stereoC, show (1 : ℝ) - -1 * (y : E3) 2 = 0 by linarith]
  simp

/-- At the point `σ₋₁` misses, `σ₁ = 0`. -/
lemma sig_of_not_mem {y : S2} (hy : y ∉ (holChart (-1) (by norm_num)).source) : sig y = 0 := by
  have h : -1 * (y : E3) 2 = 1 := not_not.1 hy
  have hs := S2_sq y
  have h0 : (y : E3) 0 = 0 := by nlinarith
  have h1 : (y : E3) 1 = 0 := by nlinarith
  change stereoC 1 y = 0
  rw [stereoC, h0, h1]
  simp

/-- `σ₋₁ = 1/σ₁` where both are defined. -/
lemma holChart_neg_eq_inv {y : S2} (hy : y ∈ sig.source) (h0 : sig y ≠ 0) :
    holChart (-1) (by norm_num) y = (sig y)⁻¹ := by
  have e := holChart_neg_symm_inv (sig y) h0
  rw [sig.left_inv hy] at e
  conv_lhs => rw [← e]
  exact holChart_holChart_symm _ _ _

lemma contDiff_chiC : ContDiff ℝ ∞ chiC :=
  Real.smoothTransition.contDiff.comp (contDiff_const.sub (contDiff_norm_sq ℝ))

lemma chiC_eq_zero {w : ℂ} (hw : 2 ≤ ‖w‖ ^ 2) : chiC w = 0 :=
  Real.smoothTransition.zero_of_nonpos (by linarith)

/-- **The section of §4 is smooth**: near the point missed by `z`, `χ(z) = 0`. -/
theorem contMDiff_exSection (c e : E) :
    ContMDiff 𝓘(ℝ, E2) 𝓘(ℝ, E) ∞ (exSection J₀ c e) := by
  set z := holChart (-1) (by norm_num : (-1 : ℝ) ^ 2 = 1)
  have hF : ContDiff ℝ ∞ fun w : ℂ => chiC w • cmulL J₀ w e :=
    contDiff_chiC.smul ((cmulL J₀).contDiff.clm_apply contDiff_const)
  have hF0 : ∀ w : ℂ, w = 0 ∨ 2 < ‖w‖ → chiC w • cmulL J₀ w e = 0 := by
    rintro w (rfl | hw)
    · simp
    · rw [chiC_eq_zero (by nlinarith), zero_smul]
  refine ContMDiff.sumElim (fun y => ?_) contMDiff_const
  by_cases hy : y ∈ z.source
  · exact contMDiffAt_const.add ((hF.contMDiff.contMDiffAt).comp y (contMDiffAt_holChart _ _ hy))
  · refine (contMDiffAt_const (c := c)).congr_of_eventuallyEq ?_
    have hys : y ∈ sig.source :=
      (mem_sig_source_iff y).2 fun h => hy (h ▸ pt2_mem_holChart_neg_source)
    have hsc : ContinuousAt sig y := sig.continuousAt hys
    have hsy : sig y = 0 := sig_of_not_mem hy
    filter_upwards [sig.open_source.mem_nhds hys,
      hsc.preimage_mem_nhds (Metric.ball_mem_nhds (sig y) (by norm_num : (0 : ℝ) < 1 / 2))]
      with y' hy's hy'b
    rw [mem_preimage, hsy, mem_ball_zero_iff] at hy'b
    change c + chiC (z y') • cmulL J₀ (z y') e = c
    by_cases hy'z : y' ∈ z.source
    · have hne : sig y' ≠ 0 := fun h0 => hy (by
        rw [← show y' = y from (sig.left_inv hy's).symm.trans
          ((congrArg sig.symm (h0.trans hsy.symm)).trans (sig.left_inv hys))]
        exact hy'z)
      rw [holChart_neg_eq_inv hy's hne, hF0 _ (Or.inr ?_), add_zero]
      rw [norm_inv]
      have hp : 0 < ‖sig y'‖ := norm_pos_iff.2 hne
      rw [lt_inv_comm₀ (by norm_num) hp]
      linarith
    · rw [holChart_neg_of_not_mem hy'z, hF0 _ (Or.inl rfl), add_zero]

/-- The section of §4 is continuous with matching values at the node, so it lies in `sectionsSub`
exactly when its local representatives lie in the blocks. -/
theorem exSection_cont_matching (c e : E) :
    IsContSection (X := twoSpheres) (fun _ => q) (exSection J₀ c e) ∧
      IsMatchingSection twoSpheres (exSection J₀ c e) := by
  refine ⟨isContSection_of_const (fun _ => rfl) (contMDiff_exSection c e).continuous,
    isMatchingSection_twoSpheres ?_⟩
  simp [exSection, holChart_neg_pt2]

/-- Its neck representative at `inl e₂`: `β(s) e_k*(χ(w) w·e)`, `w = e^{-2π((s+s₀)+it)}`. -/
lemma neckRep_exSection (hA : IsStdNeck A) {j : Fin A.nn} (hj : A.node j = Sum.inl (pt 2))
    (k : Fin (Module.finrank ℝ E)) (c e : E) (p : ℝ × ℝ) :
    neckRep A j k (exSection J₀ c e) p = Real.smoothTransition p.1 *
      crd k (chiC (ePol (A.s0 j) p) • cmulL J₀ (ePol (A.s0 j) p) e) := by
  rw [neckRep_eq_inl hA hj, comp_apply, neckFn, cutW_ePol]
  congr 1
  simp only [exSection, Sum.elim_inl, holChart_holChart_symm, holChart_neg_pt2, map_zero,
    zero_apply, smul_zero, add_zero, map_add, add_sub_cancel_left]

/-- `|z·e| ≥ κ |z|` for `e ≠ 0` (`J₀² = -1`). -/
lemma exists_norm_cmulL_ge (hJ : ∀ v, J₀ (J₀ v) = -v) {e : E} (he : e ≠ 0) :
    ∃ κ > 0, ∀ w : ℂ, κ * ‖w‖ ≤ ‖cmulL J₀ w e‖ := by
  set L := ‖cmulL J₀‖
  have hL : 0 ≤ L := norm_nonneg _
  refine ⟨‖e‖ / (L + 1), div_pos (norm_pos_iff.2 he) (by linarith), fun w => ?_⟩
  by_cases hw : w = 0
  · simp [hw]
  have h1 : e = cmulL J₀ w⁻¹ (cmulL J₀ w e) := by
    rw [← cmulL_mul hJ, inv_mul_cancel₀ hw, cmulL_one]
  have h2 : ‖e‖ ≤ L * ‖w‖⁻¹ * ‖cmulL J₀ w e‖ := by
    calc ‖e‖ = ‖cmulL J₀ w⁻¹ (cmulL J₀ w e)‖ := by rw [← h1]
      _ ≤ ‖cmulL J₀ w⁻¹‖ * ‖cmulL J₀ w e‖ := (cmulL J₀ w⁻¹).le_opNorm _
      _ ≤ L * ‖w‖⁻¹ * ‖cmulL J₀ w e‖ := by
          refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
          rw [← norm_inv]; exact (cmulL J₀).le_opNorm _
  have hwp : 0 < ‖w‖ := norm_pos_iff.2 hw
  rw [div_mul_eq_mul_div, div_le_iff₀ (by linarith)]
  have h3 : ‖e‖ * ‖w‖ ≤ L * ‖cmulL J₀ w e‖ := by
    have := mul_le_mul_of_nonneg_right h2 hwp.le
    rwa [show L * ‖w‖⁻¹ * ‖cmulL J₀ w e‖ * ‖w‖ = L * ‖cmulL J₀ w e‖ by field_simp] at this
  nlinarith [norm_nonneg (cmulL J₀ w e)]

lemma cyl_Ici_prod (T : ℝ) : cyl (Ici T ×ˢ (univ : Set ℝ)) = ⊤ := by
  rw [cyl, Measure.prod_prod, Real.volume_Ici, Measure.restrict_apply_univ, Real.volume_Ioc]
  exact ENNReal.top_mul (by norm_num)

/-- The elements of `H^{3,δ₀}`, weighted by `e^{δ₀|s|}`, are in `L²`. -/
lemma memLp_wt_of_ae_eq {d : ℝ} {hd : 0 ≤ d} (w : H 3 hd) {F : ℝ × ℝ → ℝ}
    (hw : (H.val w : ℝ × ℝ → ℝ) =ᵐ[cyl] F) : MemLp (fun x => wt d x * F x) 2 cyl := by
  refine (dv_spec (H.toSub w) (idx0 3)).2.ae_eq ?_
  filter_upwards [dv_idx0 (H.toSub w), hw] with x h1 h2
  rw [h1]
  exact congrArg _ h2

/-- **The example of §4, for `δ₀ ≥ 2π`**: the section `ξ = c + χ(z) z·e` (`e ≠ 0`) has no tuple
of local representatives in the blocks: in the polar coordinates at the nodal point,
`ξ ∘ σ - c = e^{-2π((s+s₀)+it)}·e` for large `s`, and `e^{δ₀ s} e^{-2πs}` is not in `L²`. -/
theorem not_isRep_exSection (hA : IsStdNeck A) (hδ : 2 * Real.pi ≤ δ 0)
    (hJ : ∀ v, J₀ (J₀ v) = -v) (c : E) {e : E} (he : e ≠ 0) (v : (blocks A δ h0 hmono) 0) :
    ¬ IsRep (exSection J₀ c e) v := by
  intro hv
  obtain ⟨j, hj⟩ := A.exists_node_inl
  set s₀ := A.s0 j
  set Y : ℝ × ℝ → E := fun p => (wt (δ 0) p * Real.smoothTransition p.1) •
    (chiC (ePol s₀ p) • cmulL J₀ (ePol s₀ p) e)
  -- each coordinate of `Y` is in `L²`
  have hk : ∀ k, MemLp (fun p => crd k (Y p) • Module.finBasis ℝ E k) 2 cyl := fun k => by
    have h := memLp_wt_of_ae_eq _ (hv.2 j k).2
    have e1 : (fun x => wt (δ 0) x * neckRep A j k (exSection J₀ c e) x) =
        fun p => crd k (Y p) := by
      funext p
      rw [neckRep_exSection hA hj]
      simp only [Y, map_smul, smul_eq_mul]
      ring
    rw [e1] at h
    exact (ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) (Module.finBasis ℝ E k)).comp_memLp' h
  have hY : MemLp Y 2 cyl := by
    have := memLp_finsetSum' Finset.univ fun k _ => hk k
    refine this.ae_eq (Eventually.of_forall fun p => ?_)
    simp only [Finset.sum_apply]
    exact crd_basis_sum (Y p)
  -- the lower bound `|Y| ≥ ε₀` on `s ≥ T`
  obtain ⟨κ, hκ, hκw⟩ := exists_norm_cmulL_ge hJ he
  set ε₀ := κ * Real.exp (-2 * Real.pi * s₀)
  have hε₀ : 0 < ε₀ := mul_pos hκ (Real.exp_pos _)
  set T := max 1 (-s₀)
  have hlow : ∀ p : ℝ × ℝ, T ≤ p.1 → ε₀ ≤ ‖Y p‖ := by
    intro p hp
    have h1 : 1 ≤ p.1 := (le_max_left _ _).trans hp
    have h2 : 0 ≤ p.1 + s₀ := by linarith [(le_max_right 1 (-s₀)).trans hp]
    have hn : ‖ePol s₀ p‖ ≤ 1 := by
      rw [norm_ePol, Real.exp_le_one_iff]; nlinarith [Real.pi_pos]
    simp only [Y, Real.smoothTransition.one_of_one_le h1, mul_one, chiC_eq_one hn, one_smul,
      norm_smul, Real.norm_eq_abs, abs_of_pos (wt_pos _ _)]
    have hw : Real.exp (2 * Real.pi * p.1) ≤ wt (δ 0) p := by
      rw [wt, abs_of_nonneg (by linarith), Real.exp_le_exp]
      exact mul_le_mul_of_nonneg_right hδ (by linarith)
    calc ε₀ = Real.exp (2 * Real.pi * p.1) * (κ * ‖ePol s₀ p‖) := by
          rw [norm_ePol]; simp only [ε₀]
          rw [mul_left_comm, ← Real.exp_add]; congr 2; ring
      _ ≤ wt (δ 0) p * ‖cmulL J₀ (ePol s₀ p) e‖ :=
          mul_le_mul hw (hκw _) (by positivity) (wt_pos _ _).le
  -- a contradiction with `Y ∈ L²`
  have hint := hY.norm.integrable_sq
  have hfin := hint.measure_norm_ge_lt_top (ε := ε₀ ^ 2) (by positivity)
  refine absurd (measure_mono (μ := cyl) (show Ici T ×ˢ (univ : Set ℝ) ⊆
    {x | ε₀ ^ 2 ≤ ‖‖Y x‖ ^ 2‖} from ?_)) ?_
  · rintro ⟨s, t⟩ ⟨hs, -⟩
    simp only [mem_ofPred_eq, norm_pow, norm_norm]
    exact pow_le_pow_left₀ hε₀.le (hlow (s, t) hs) 2
  · rw [cyl_Ici_prod]
    exact not_le.2 hfin

/-- **`ξ ∉ H^{3,δ₀}_c` for `δ₀ ≥ 2π`** (the example of §4): no element of `sectionSpace` is
represented by `ξ = c + χ(z) z·e`.  Together with `smoothNeckRep_mem`, the smooth sections lie in
`H^{3,δ₀}_c` exactly in the range `δ₀ < 2π`; the statement of p. 49 with `δ₀ ≥ 2π` does not hold
as we read it. -/
theorem not_mem_sectionSpace_of_two_pi_le (hA : IsStdNeck A) (hδ : 2 * Real.pi ≤ δ 0)
    (hJ : ∀ v, J₀ (J₀ v) = -v) (c : E) {e : E} (he : e ≠ 0) :
    ¬ ∃ v ∈ sectionSpace A δ h0 hmono, IsRep (exSection J₀ c e) v :=
  fun ⟨v, _, hv⟩ => not_isRep_exSection hA hδ hJ c he v hv

end Example

end GWMemoir
