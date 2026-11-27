import GWMemoir.CokernelSphere

/-!
# The smooth anti-linear forms are dense in the fibre over a constant map from `sphere3`

HWZ, *Applications of Polyfold Theory I*, Memoirs AMS 248, no. 1179, §4.  The forms of
`GWMemoir.FormsDensity` built from test functions in the disc charts,
`projF J(q) (∑_j ρ_j · testForm φ j)`, have smooth coefficients in both holomorphic charts
(`isSphereSmooth_testForms`); their representatives are dense in the fibre
(**`smoothFormsDense_sphere3`**).  With `GWMemoir.CokernelSphere` this gives
**`cokernelVanishes_of_ellipticEstimate`**: the elliptic estimate alone gives `CokernelVanishes`.
-/

set_option maxSynthPendingDepth 3
set_option linter.unusedSectionVars false

open scoped Manifold ContDiff Topology
open Set Function Filter MeasureTheory
open Polyfold Polyfold.CylinderSobolev

noncomputable section

namespace GWMemoir

section Smooth

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {Q : Type} [TopologicalSpace Q] [ChartedSpace E Q] [IsManifold 𝓘(ℝ, E) ∞ Q]
  {q : Q} (A : SectionAtlas (E := E) sphere3 (fun _ => q))

/-- The derivative of a map `ℂ → S²` read in the chart of `S²` at `c`. -/
lemma tcc_mfderiv {τ : ℂ → S2} (hτ : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, E2) ∞ τ) (c : S2) {z : ℂ}
    (hz : τ z ∈ (chartAt E2 c).source) (w : ℂ) :
    tangentCoordChange 𝓘(ℝ, E2) (τ z) c (τ z) (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E2) τ z w) =
      fderiv ℝ (fun z => chartAt E2 c (τ z)) z w := by
  have hc : MDifferentiableAt 𝓘(ℝ, E2) 𝓘(ℝ, E2) (chartAt E2 c) (τ z) :=
    mdifferentiableAt_atlas (ChartedSpace.chart_mem_atlas _) hz
  have h := mfderiv_comp z hc ((hτ z).mdifferentiableAt (by simp))
  rw [mfderiv_eq_fderiv, mfderiv_chartAt_eq_tangentCoordChange hz] at h
  exact (congrArg (fun L => L w) h).symm

/-- The value of a test form on a tangent vector. -/
lemma testForm_apply (φ : Ix A → ℝ × ℝ → ℝ) (j : Fin A.nd) (y : S2) (v : E2) :
    testForm (X := sphere3) A φ j y v =
      (discCut (stripPt (X := sphere3) (A.center j) (A.ε j) y))⁻¹ •
        (Module.finBasis ℝ E).equivFun.symm fun k => ∑ d' : Fin 2,
          φ (j, d', k) (stripPt (X := sphere3) (A.center j) (A.ε j) y) *
            (tangentCoordChange 𝓘(ℝ, E2) y (A.center j) y v) d' := by
  simp only [testForm, ContinuousLinearMap.comp_apply, smul_apply,
    LinearMap.coe_toContinuousLinearMap', LinearEquiv.coe_coe]
  congr 2

/-- **One term of the test forms, read along a smooth map `τ : ℂ → S²`, is smooth.** -/
theorem contDiff_testTerm {τ : ℂ → S2} (hτ : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, E2) ∞ τ)
    (φ : Ix A → ℝ × ℝ → ℝ) (hφ : ∀ o, ContDiff ℝ ∞ (φ o)) (j : Fin A.nd)
    {ρ : S2 → ℝ} (hρs : ContMDiff 𝓘(ℝ, E2) 𝓘(ℝ) ∞ ρ)
    (hρ : tsupport ρ ⊆ discSet (A.center j) (A.ε j)) (w : ℂ) :
    ContDiff ℝ ∞ fun z => ρ (τ z) • testForm (X := sphere3) A φ j (τ z)
      (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E2) τ z w) := by
  let c : S2 := A.center j
  let ε := A.ε j
  let V : Set ℂ := τ ⁻¹' discSet (X := sphere3) c ε
  have hVo : IsOpen V := (isOpen_discSet (X := sphere3) c ε).preimage hτ.continuous
  have hVs : ∀ z ∈ V, τ z ∈ (chartAt E2 c).source := fun z hz => by
    have := hz.1; rwa [extChartAt_source] at this
  let ψ : ℂ → E2 := fun z => chartAt E2 c (τ z)
  have hψ : ContDiffOn ℝ ∞ ψ V := fun z hz => by
    have h1 := (contMDiffAt_extChartAt' (I := 𝓘(ℝ, E2)) (n := ∞) (M := S2) (x := c)
      (hVs z hz)).comp z (hτ z)
    exact (contMDiffAt_iff_contDiffAt.1 h1).contDiffWithinAt
  have hψ' : ContDiffOn ℝ ∞ (fun z => fderiv ℝ ψ z w) V :=
    ((hψ.fderiv_of_isOpen hVo (by simp)).clm_apply contDiffOn_const)
  rw [contDiff_iff_contDiffAt]
  intro z₀
  by_cases h₀ : τ z₀ ∈ tsupport ρ
  swap
  · have hopen : IsOpen {z | τ z ∉ tsupport ρ} :=
      (isClosed_tsupport ρ).isOpen_compl.preimage hτ.continuous
    refine contDiffAt_const (c := (0 : E)).congr_of_eventuallyEq ?_
    filter_upwards [hopen.mem_nhds h₀] with z hz
    rw [image_eq_zero_of_notMem_tsupport hz, zero_smul]
  have hz₀ : z₀ ∈ V := hρ h₀
  have hV : V ∈ 𝓝 z₀ := hVo.mem_nhds hz₀
  have hρc : ContDiff ℝ ∞ fun z => ρ (τ z) := contMDiff_iff_contDiff.1 (hρs.comp hτ)
  have hpl : ContDiffAt ℝ ∞ (fun z => placeInv (X := sphere3) c ε (ψ z)) z₀ :=
    (contDiff_placeInv (X := sphere3) c ε).contDiffAt.comp z₀ (hψ.contDiffAt hV)
  have hcut : discCut (placeInv (X := sphere3) c ε (ψ z₀)) ≠ 0 := by
    have h : placeInv (X := sphere3) c ε (ψ z₀) ∈ discD := hz₀.2
    exact (discCut_pos h).ne'
  have hsum : ContDiffAt ℝ ∞ (fun z => (Module.finBasis ℝ E).equivFun.symm fun k =>
      ∑ d' : Fin 2, φ (j, d', k) (placeInv (X := sphere3) c ε (ψ z)) *
        (fderiv ℝ ψ z w) d') z₀ := by
    refine (LinearMap.toContinuousLinearMap
      (Module.finBasis ℝ E).equivFun.symm.toLinearMap).contDiff.contDiffAt.comp z₀ ?_
    refine contDiffAt_pi.2 fun k => ContDiffAt.sum fun d' _ => ?_
    exact ((hφ _).contDiffAt.comp z₀ hpl).mul
      ((EuclideanSpace.proj d' : E2 →L[ℝ] ℝ).contDiff.contDiffAt.comp z₀
        (hψ'.contDiffAt hV))
  have hmain : ContDiffAt ℝ ∞ (fun z => ρ (τ z) •
      ((discCut (placeInv (X := sphere3) c ε (ψ z)))⁻¹ •
        (Module.finBasis ℝ E).equivFun.symm fun k =>
          ∑ d' : Fin 2, φ (j, d', k) (placeInv (X := sphere3) c ε (ψ z)) *
            (fderiv ℝ ψ z w) d')) z₀ :=
    hρc.contDiffAt.smul (((contDiff_discCut.contDiffAt.comp z₀ hpl).inv hcut).smul hsum)
  refine hmain.congr_of_eventuallyEq ?_
  filter_upwards [hV] with z hz
  refine congrArg (ρ (τ z) • ·) ((testForm_apply A φ j (τ z) _).trans ?_)
  erw [tcc_mfderiv hτ (A.center j) (hVs z hz) w]
  rfl

variable (J₀ : E →L[ℝ] E)

/-- **The test forms are smooth on the sphere**: for smooth `ρ_j` supported in the discs and smooth
`φ`, the form `projF J₀ (∑_j ρ_j · testForm φ j)` has smooth coefficients in both holomorphic
charts. -/
theorem isSphereSmooth_testForms (ρ : Fin A.nd → S2 → ℝ)
    (hρs : ∀ j, ContMDiff 𝓘(ℝ, E2) 𝓘(ℝ) ∞ (ρ j))
    (hρ : ∀ j, tsupport (ρ j) ⊆ discSet (A.center j) (A.ε j))
    (φ : Ix A → ℝ × ℝ → ℝ) (hφ : ∀ o, ContDiff ℝ ∞ (φ o)) :
    IsSphereSmooth (projF (X := sphere3) J₀
      (fun y => ∑ j, ρ j y • testForm (X := sphere3) A φ j y)) := by
  have key : ∀ (s : ℝ) (hs : s ^ 2 = 1), ContDiff ℝ ∞ (chartCoef s hs (projF (X := sphere3) J₀
      (fun y => ∑ j, ρ j y • testForm (X := sphere3) A φ j y))) := by
    intro s hs
    have hτ := contMDiff_holChart_symm s hs
    have hζ : ∀ w : ℂ, ContDiff ℝ ∞ fun z => ∑ j, ρ j ((holChart s hs).symm z) •
        testForm (X := sphere3) A φ j ((holChart s hs).symm z) (DtauS s hs z w) := fun w =>
      ContDiff.sum fun j _ => contDiff_testTerm A hτ φ hφ j (hρs j) (hρ j) w
    have he : chartCoef s hs (projF (X := sphere3) J₀
        (fun y => ∑ j, ρ j y • testForm (X := sphere3) A φ j y)) = fun z => (1 / 2 : ℝ) •
          ((∑ j, ρ j ((holChart s hs).symm z) •
            testForm (X := sphere3) A φ j ((holChart s hs).symm z) (DtauS s hs z 1)) +
          J₀ (∑ j, ρ j ((holChart s hs).symm z) •
            testForm (X := sphere3) A φ j ((holChart s hs).symm z)
              (DtauS s hs z Complex.I))) := by
      funext z
      have hj : sphere3.j.J ((holChart s hs).symm z) (DtauS s hs z 1) =
          DtauS s hs z Complex.I := by
        rw [← mul_one Complex.I]; exact (DtauS_I s hs z 1).symm
      change (1 / 2 : ℝ) • ((∑ j, ρ j ((holChart s hs).symm z) •
          testForm (X := sphere3) A φ j ((holChart s hs).symm z)) (DtauS s hs z 1) +
        J₀ ((∑ j, ρ j ((holChart s hs).symm z) •
          testForm (X := sphere3) A φ j ((holChart s hs).symm z))
            (sphere3.j.J ((holChart s hs).symm z) (DtauS s hs z 1)))) = _
      rw [hj]
      simp only [FunLike.coe_sum, Finset.sum_apply, smul_apply]
    rw [he]
    exact ((hζ 1).add (J₀.contDiff.comp (hζ Complex.I))).const_smul _
  exact ⟨key 1 _, key (-1) _⟩

end Smooth

/-! ## The density of the smooth forms and the vanishing of the cokernel -/

section Dense

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {Q : Type} [TopologicalSpace Q] [ChartedSpace E Q] [IsManifold 𝓘(ℝ, E) ∞ Q]
variable (J : AlmostComplexStructure E Q) {q : Q} {A : SectionAtlas (E := E) sphere3 (fun _ => q)}
  (G : GlueData A) (δ : ℕ → ℝ) (h0 : 0 ≤ δ 0) (hmono : StrictMono δ)

/-- **The smooth anti-linear forms are dense in the fibre** over a constant map from `sphere3`
(Memoir p. 51): the operator `Φ = ½ (G + P G)` of `formsDense_const` maps the tuples of test
functions, a dense set, to representatives of the forms `projF J(q) (∑_j ρ_j · testForm φ j)`,
which are smooth on the sphere (`isSphereSmooth_testForms`); `Φ` is the identity on the fibre. -/
theorem smoothFormsDense_sphere3 : SmoothFormsDense J δ h0 hmono (A := A) := by
  have hX : sphere3.nodes = ∅ := rfl
  have hT := sphere3_chartsOnto
  have hu : ∀ x : sphere3.S, (fun _ => q) x = q := fun _ => rfl
  obtain ⟨ρ, hρ⟩ := exists_partition hX hT A
  have hρ' : ∀ j, tsupport (ρ j) ⊆ discSet (A.center j) (A.ε j) := hρ
  choose D hDK hDψ using fun i j : Fin A.nd =>
    exists_chartChange hT (ρ := ρ j) (z := A.center i) (A.ε_pos i).ne' (A.ε_pos j).ne' (hρ' j)
  have hcG : ∀ o t, ContDiff ℝ ∞ (aG A (fun j => ρ j) o t) :=
    fun o t => contDiff_coef hT (ρ t.1) _ _ _ _ (hρ' t.1) _ _
  have hsG : ∀ o t, tsupport (aG A (fun j => ρ j) o t) ⊆ (D o.1 t.1).K :=
    fun o t => by
      rw [hDK o.1 t.1]
      exact tsupport_coef_sub hT _ _ _ _ _ _ _
  have hcP : ∀ o t, ContDiff ℝ ∞ (aPI A (J.J q) o t) := fun o t => contDiff_aP hT _ _ _ _ _ _ _
  have hsP : ∀ o t, tsupport (aPI A (J.J q) o t) ⊆ ((fun _ _ => idCC) o t : ChartChange).K :=
    fun o t => tsupport_aP _ _ _ _ _ _ _
  have hnn := isEmpty_neck_of_nodes_empty hX A
  set Gf := fOp δ h0 hmono (fun o t => D o.1 t.1) (aG A (fun j => ρ j)) hcG hsG (srcG A) with hG
  set P := fOp δ h0 hmono (fun _ _ => idCC) (aPI A (J.J q)) hcP hsP (srcP A) with hP
  set Φ : (fibreBlocks A δ h0 hmono) 0 →L[ℝ] (fibreBlocks A δ h0 hmono) 0 :=
    (1 / 2 : ℝ) • (Gf 0 + (P 0).comp (Gf 0)) with hΦ
  have hGrep : ∀ ξ v, IsFormRep ξ v → IsFormRep ξ (Gf 0 v) := by
    intro ξ v hv
    refine ⟨fun i d k => ?_, fun j => isEmptyElim j⟩
    refine (G_ae hT hu hρ' hDK hDψ hcG hsG (fun _ => ξ)
      (fun o t => ChartChange.comp_congr (hsG o t) (hv.1 t.1 t.2 o.2.2)) (i, d, k)).trans
      (Eventually.of_forall fun x => ?_)
    change ∑ j, ρ j _ * _ = _
    rw [← Finset.sum_mul]
    have h := ρ.sum_eq_one (x := sphere3.discPt (A.center i) (A.ε i) x) (mem_univ _)
    rw [finsum_eq_sum_of_fintype] at h
    rw [h, one_mul]
  have hrep : ∀ ξ v, IsFormRep ξ (Gf 0 v) → IsFormRep (projF (J.J q) ξ) (Φ v) := fun ξ v hv =>
    (hv.add (P_rep hT hu hnn (J.J q) hcP hsP hv)).smul (1 / 2 : ℝ)
  have hfix : ∀ v ∈ formsSub J A δ h0 hmono, Φ v = v := by
    rintro v ⟨ξ, ha, hv⟩
    have hp : projF (J.J q) ξ = ξ := funext fun y => projF_of_mem (ha y (by rw [hX]; simp))
    have h := hrep ξ v (hGrep ξ v hv)
    rw [hp] at h
    exact h.unique hv
  have hfixF : ∀ v ∈ (fibreSpace J A δ h0 hmono : Set ((fibreBlocks A δ h0 hmono) 0)),
      Φ v = v := by
    intro v hv
    rw [fibreSpace, Submodule.topologicalClosure_coe] at hv
    exact (show EqOn Φ id (formsSub J A δ h0 hmono : Set _) from fun v hv => hfix v hv).closure
      Φ.continuous continuous_id hv
  -- the image of a tuple of test functions
  have htest : ∀ w : (fibreBlocks A δ h0 hmono) 0,
      (∀ o, ∃ φ, ∃ hφ : IsTest φ, w.1 o = toH (2 + 0) (Neck.δ_nonneg δ h0 hmono 0) hφ) →
        ∃ y ∈ smoothFormReps J δ h0 hmono (A := A), (y : (fibreBlocks A δ h0 hmono) 0) = Φ w := by
    intro w hw
    choose φ hφ hwφ using hw
    have hG' : IsFormRep (fun y => ∑ j, ρ j y • testForm A φ j y) (Gf 0 w) := by
      refine ⟨fun i d k => ?_, fun j => isEmptyElim j⟩
      refine (G_ae hT hu hρ' hDK hDψ hcG hsG (fun j => testForm A φ j) (fun o t => ?_)
        (i, d, k)).trans (Eventually.of_forall fun x =>
          (formDiscRep_sum hu A (fun j => ρ j) _ i d k x).symm)
      refine (ChartChange.comp_congr (hsG o t) (f' := φ (srcG A o t)) (by
        rw [hwφ (srcG A o t)]; exact MemLp.coeFn_toLp ((hφ _).memLp 2))).trans
        (Eventually.of_forall fun x => ?_)
      change aG A (fun j => ρ j) o t x * φ (srcG A o t) ((D o.1 t.1).ψ x) =
        aG A (fun j => ρ j) o t x * formDiscRep A t.1 t.2 o.2.2 (testForm A φ t.1) ((D o.1 t.1).ψ x)
      by_cases hx : aG A (fun j => ρ j) o t x = 0
      · rw [hx, zero_mul, zero_mul]
      have hxK : x ∈ pieceK (ρ t.1) (A.center o.1) (A.ε o.1) :=
        tsupport_coef_sub hT _ _ _ _ _ _ _ (subset_tsupport _ hx)
      have hxD := pieceK_sub (hρ' t.1) hxK
      rw [hDψ o.1 t.1 x ((hDK o.1 t.1).symm ▸ hxK),
        formDiscRep_testForm hT hu A φ t.1 t.2 o.2.2 (discCut_pos (pieceDom_sub hxD).2).ne']
      rfl
    have hmemS : Φ w ∈ formsSub J A δ h0 hmono :=
      ⟨projF (J.J q) _, fun y _ => projF_mem J q _ y, hrep _ w hG'⟩
    refine ⟨⟨Φ w, formsSub_le J A δ h0 hmono hmemS⟩, ⟨projF (J.J q) _, fun y v =>
      (NodalSurface.mem_antiLinearForms J sphere3).1 (projF_mem J q _ y) v,
      isSphereSmooth_testForms A (J.J q) (fun j => ρ j) (fun j => (ρ j).contMDiff) hρ'
        φ (fun o => (hφ o).smooth), hrep _ w hG'⟩, rfl⟩
  -- density
  let T : Set ((fibreBlocks A δ h0 hmono) 0) :=
    (univ.pi fun _ => {g : (Neck.scCylOff 2 δ h0 hmono) 0 |
      ∃ φ, ∃ hφ : IsTest φ, g = toH (2 + 0) (Neck.δ_nonneg δ h0 hmono 0) hφ}) ×ˢ univ
  have hd : Dense T :=
    (dense_pi univ fun _ _ => dense_test (2 + 0) (Neck.δ_nonneg δ h0 hmono 0)).prod dense_univ
  have hsub : Φ '' T ⊆ (↑) '' smoothFormReps J δ h0 hmono (A := A) := by
    rintro _ ⟨w, hw, rfl⟩
    obtain ⟨y, hy, hyw⟩ := htest w fun o => hw.1 o (mem_univ _)
    exact ⟨y, hy, hyw⟩
  refine Subtype.dense_iff.2 fun v hv => ?_
  rw [← hfixF v hv]
  exact closure_mono hsub (image_closure_subset_closure_image Φ.continuous
    ⟨v, hd v, rfl⟩)

/-- **`CokernelVanishes` from the elliptic estimate**: for `D = ∂̄` at a constant map from
`sphere3`, every form of the fibre is `D ξ` for a section `ξ`. -/
theorem cokernelVanishes_of_ellipticEstimate (hδ : 0 < δ 0)
    (hE : EllipticEstimate J G δ h0 hmono hδ) : CokernelVanishes J G δ h0 hmono :=
  cokernelVanishes_sphere3 J G δ h0 hmono hδ hE (smoothFormsDense_sphere3 J δ h0 hmono)

/-- **The range of `D` is dense** (no estimate needed). -/
theorem denseRange_linCR3_sphere3 : DenseRange (linCR3 J G δ h0 hmono) :=
  denseRange_linCR3 J G δ h0 hmono (smoothFormsDense_sphere3 J δ h0 hmono)

end Dense

end GWMemoir
