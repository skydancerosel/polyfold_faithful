import GWMemoir.CokernelNodes
import GWMemoir.GlueDataNodes
import GWMemoir.CokernelSphereDense
import GWMemoir.LinearCRNodesDenseRep

/-!
# The range of the linearized Cauchy–Riemann operator at a node is dense

HWZ, *Applications of Polyfold Theory I*, Memoirs AMS 248, no. 1179, §4 (Proposition 4.23,
p. 118, level `0`, `a = 0`), at the constant map `u ≡ q` from two spheres joined at a node
(`twoSpheres`), with `0 ≤ δ₀ < 2π` and the standard neck charts (`IsStdNeck`), as for `sphere3`
in `GWMemoir.CokernelSphere`.

* `smoothFormRepsN`: the representatives, in the fibre, of the anti-linear forms with smooth
  coefficients in both holomorphic charts of each sphere; `SmoothFormsDenseN`: they are dense.
* **`linCRN_hits`**: `D` hits each of them: `exists_twoSpheres_smooth_solution` gives a smooth
  section `ξ` with matching values at the node and `∂̄ξ = η`; `smoothNeckRep_mem` puts it in
  `H^{3,δ₀}_c` (this is where `δ₀ < 2π` enters) and `isFormRep_linOpN` identifies `D ξ`.
* **`denseRange_linCRN_of_smoothFormsDenseN`**: the range of `D` is dense, given
  `SmoothFormsDenseN`; **`surjective_linCRN_of_isClosed`**: closed and dense range give `D` onto.
* **`smoothFormsDenseN_of_phiN`**: the operator `Φ` of `GWMemoir.LinearCRNodesDenseOp` is the
  identity on the fibre (`phiN_eq_self_fibre`; the polar coordinates of the standard neck charts
  avoid the nodal points, `twoSpheres_polar_offNode`), so `SmoothFormsDenseN` holds once `Φ` maps
  the tuples of test functions (`testTuplesN`, dense) to representatives of smooth forms.
* `NeckTestForms`: the forms on the necks with prescribed representatives `γ_j` for
  `s ≥ s₀ + ½`, anti-linear there, whose glued anti-linear part is smooth on both spheres;
  **`smoothFormsDenseN_of_neckTestForms`**, **`denseRange_linCRN_of_neckTestForms`**: they give
  the density of the smooth forms and of the range of `D` (`isFormRep_phiN` reads `Φ` of a test
  tuple as `projF J(q) (∑ ρ_i · testForm φ i + ∑ χ_j ξN_j)`).
* `exists_glueAtlas_twoSpheres`: an atlas with all the hypotheses above except `NeckTestForms`.
-/

set_option maxSynthPendingDepth 3
set_option linter.unusedSectionVars false

open scoped Manifold ContDiff Topology
open Set Function Filter MeasureTheory
open Polyfold Polyfold.CylinderSobolev

noncomputable section

namespace GWMemoir

/-! ## 1. `D` hits the smooth forms -/

section Range

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {Q : Type} [TopologicalSpace Q] [ChartedSpace E Q] [IsManifold 𝓘(ℝ, E) ∞ Q]
variable (J : AlmostComplexStructure E Q) {q : Q}
  {A : SectionAtlas (E := E) twoSpheres (fun _ => q)} (hsm : NeckSmooth A) (G : GlueDataN A)
  (δ : ℕ → ℝ) (h0 : 0 ≤ δ 0) (hmono : StrictMono δ)

/-- The representatives, in the fibre over the constant map from `twoSpheres`, of the forms
anti-linear for `(j, J(q))` with smooth coefficients in both holomorphic charts of each sphere. -/
def smoothFormRepsN : Set (fibreSpace J A δ h0 hmono) :=
  {y | ∃ η : Form E twoSpheres, IsAntiJ (J.J q) (fun z => η (Sum.inl z)) ∧
    IsAntiJ (J.J q) (fun z => η (Sum.inr z)) ∧ IsSphereSmooth (fun z => η (Sum.inl z)) ∧
    IsSphereSmooth (fun z => η (Sum.inr z)) ∧
    IsFormRep η (y : (fibreBlocks A δ h0 hmono) 0)}

/-- **The density of the smooth anti-linear forms in the fibre** over the constant map from
`twoSpheres` (as `SmoothFormsDense` for `sphere3`). -/
def SmoothFormsDenseN : Prop := Dense (smoothFormRepsN J δ h0 hmono (A := A))

variable {J δ h0 hmono}

/-- **`D` hits the representative of every smooth anti-linear form** (`0 ≤ δ₀ < 2π`): for `η`
anti-linear with smooth coefficients on both spheres and `y` its representative, `y = D w` for a
section `w ∈ H^{3,δ₀}_c` represented by a smooth section. -/
theorem linCRN_hits (hA : IsStdNeck A) (hδ : δ 0 < 2 * Real.pi) {η : Form E twoSpheres}
    (hη₁ : IsAntiJ (J.J q) fun z => η (Sum.inl z)) (hη₂ : IsAntiJ (J.J q) fun z => η (Sum.inr z))
    (hs₁ : IsSphereSmooth fun z => η (Sum.inl z)) (hs₂ : IsSphereSmooth fun z => η (Sum.inr z))
    {y : (fibreBlocks A δ h0 hmono) 0} (hy : IsFormRep η y) :
    ∃ w : sectionSpace A δ h0 hmono,
      (linCRN twoSpheres_chartsOnto hsm G δ h0 hmono J w : (fibreBlocks A δ h0 hmono) 0) = y := by
  obtain ⟨ξ, hξ, hm, h⟩ := exists_twoSpheres_smooth_solution (acs_sq J q) hη₁ hη₂ hs₁ hs₂
  have hc : IsContSection (fun _ => q) ξ := isContSection_of_const (fun _ => rfl) hξ.continuous
  have hr := isRep_smoothBlocks2 δ h0 hmono hξ hA hδ
  have hD := isFormRep_linOpN twoSpheres_chartsOnto hsm G hc hr (J.J q)
  have he : projF (X := twoSpheres) (J.J q) (dForm (X := twoSpheres) ξ) = η := funext h
  rw [he] at hD
  exact ⟨⟨smoothBlocks2 δ h0 hmono hξ hA hδ, smoothNeckRep_mem δ h0 hmono hξ hA hδ hm⟩,
    (linCRN_apply twoSpheres_chartsOnto hsm G J _).trans (hD.unique hy)⟩

theorem smoothFormRepsN_subset_range (hA : IsStdNeck A) (hδ : δ 0 < 2 * Real.pi) :
    smoothFormRepsN J δ h0 hmono (A := A) ⊆
      range (linCRN twoSpheres_chartsOnto hsm G δ h0 hmono J) := by
  rintro y ⟨η, hη₁, hη₂, hs₁, hs₂, hy⟩
  obtain ⟨w, hw⟩ := linCRN_hits hsm G hA hδ hη₁ hη₂ hs₁ hs₂ hy
  exact ⟨w, Subtype.ext hw⟩

/-- **The range of `D` is dense**, given the density of the smooth forms (`0 ≤ δ₀ < 2π`). -/
theorem denseRange_linCRN_of_smoothFormsDenseN (hA : IsStdNeck A) (hδ : δ 0 < 2 * Real.pi)
    (h : SmoothFormsDenseN J δ h0 hmono (A := A)) :
    DenseRange (linCRN twoSpheres_chartsOnto hsm G δ h0 hmono J) :=
  h.mono (smoothFormRepsN_subset_range hsm G hA hδ)

/-- **Closed and dense range: `D` is onto.** -/
theorem surjective_linCRN_of_isClosed
    (hc : IsClosed (range (linCRN twoSpheres_chartsOnto hsm G δ h0 hmono J)))
    (hd : DenseRange (linCRN twoSpheres_chartsOnto hsm G δ h0 hmono J)) :
    Surjective (linCRN twoSpheres_chartsOnto hsm G δ h0 hmono J) := by
  intro y
  have : y ∈ closure (range (linCRN twoSpheres_chartsOnto hsm G δ h0 hmono J)) :=
    hd.closure_eq ▸ mem_univ y
  rwa [hc.closure_eq] at this

end Range

/-! ## 2. Density of the smooth forms, from the neck test forms -/

section Dense

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {Q : Type} [TopologicalSpace Q] [ChartedSpace E Q] [IsManifold 𝓘(ℝ, E) ∞ Q]
variable (J : AlmostComplexStructure E Q) {q : Q}
  {A : SectionAtlas (E := E) twoSpheres (fun _ => q)}
  (δ : ℕ → ℝ) (h0 : 0 ≤ δ 0) (hmono : StrictMono δ)

/-- In the standard neck charts the polar coordinates avoid the nodal points. -/
theorem twoSpheres_polar_offNode (hA : IsStdNeck A) (hG : GlueCharts A) (j : Fin A.nn)
    (x : ℝ × ℝ) : ∀ p ∈ twoSpheres.nodes, twoSpheres.polar (A.hol j) x ∉ p := by
  have ht : expPolar x ∈ (A.hol j).target := by rw [hG.target j]; trivial
  have hy : A.hol j (twoSpheres.polar (A.hol j) x) = expPolar x := by
    rw [NodalSurface.polar_eq]; exact (A.hol j).right_inv ht
  have hne : twoSpheres.polar (A.hol j) x ≠ A.node j := fun h =>
    expPolar_ne_zero x (by rw [← hy, h]; exact (A.isHol j).2.1)
  have hs : twoSpheres.polar (A.hol j) x ∈ (A.hol j).source := twoSpheres.polar_mem_source ht
  refine (twoSpheres_offNode_iff _).2 ?_
  rcases A.node_cases j with h | h
  · rw [hA j, h] at hs
    obtain ⟨y', -, hy'⟩ := hs
    refine ⟨h ▸ hne, fun hc => ?_⟩
    rw [hA j, h] at hc
    exact Sum.inl_ne_inr (hy'.trans hc)
  · rw [hA j, h] at hs
    obtain ⟨y', -, hy'⟩ := hs
    refine ⟨fun hc => ?_, h ▸ hne⟩
    rw [hA j, h] at hc
    exact Sum.inr_ne_inl (hy'.trans hc)

/-- The tuples of test functions, in all the blocks. -/
def testTuplesN : Set ((fibreBlocks A δ h0 hmono) 0) :=
  (univ.pi fun _ => {g : (Neck.scCylOff 2 δ h0 hmono) 0 |
      ∃ φ, ∃ hφ : IsTest φ, g = toH (2 + 0) (Neck.δ_nonneg δ h0 hmono 0) hφ}) ×ˢ
    (univ.pi fun _ => {g : (Neck.scCylOff 2 δ h0 hmono) 0 |
      ∃ φ, ∃ hφ : IsTest φ, g = toH (2 + 0) (Neck.δ_nonneg δ h0 hmono 0) hφ})

lemma dense_testTuplesN : Dense (testTuplesN δ h0 hmono (A := A)) :=
  (dense_pi univ fun _ _ => dense_test (2 + 0) (Neck.δ_nonneg δ h0 hmono 0)).prod
    (dense_pi univ fun _ _ => dense_test (2 + 0) (Neck.δ_nonneg δ h0 hmono 0))

variable {J δ h0 hmono}

/-- **Density from `Φ`**: if `Φ` maps the tuples of test functions to representatives of smooth
anti-linear forms, these are dense in the fibre (`Φ` is the identity on the fibre,
`phiN_eq_self_fibre`). -/
theorem smoothFormsDenseN_of_phiN (hA : IsStdNeck A) (hG : GlueCharts A) (F : FormGlueN A)
    (htest : ∀ w ∈ testTuplesN δ h0 hmono (A := A), ∃ y ∈ smoothFormRepsN J δ h0 hmono (A := A),
      (y : (fibreBlocks A δ h0 hmono) 0) =
        phiN twoSpheres_chartsOnto hG F (J.J q) δ h0 hmono w) :
    SmoothFormsDenseN J δ h0 hmono (A := A) := by
  have hsub : phiN twoSpheres_chartsOnto hG F (J.J q) δ h0 hmono '' testTuplesN δ h0 hmono ⊆
      (↑) '' smoothFormRepsN J δ h0 hmono (A := A) := by
    rintro _ ⟨w, hw, rfl⟩
    obtain ⟨y, hy, hyw⟩ := htest w hw
    exact ⟨y, hy, hyw⟩
  refine Subtype.dense_iff.2 fun v hv => ?_
  rw [← phiN_eq_self_fibre twoSpheres_chartsOnto hG F J (twoSpheres_polar_offNode hA hG) hv]
  exact closure_mono hsub (image_closure_subset_closure_image
    (phiN twoSpheres_chartsOnto hG F (J.J q) δ h0 hmono).continuous
    ⟨v, dense_testTuplesN δ h0 hmono v, rfl⟩)

variable (J) in
/-- **The neck test forms** (the remaining input): for tuples `φ` of test functions in the
disc blocks and `γ` in the neck blocks, forms `ξN_j` whose neck representatives are `γ_j` for
`s ≥ s₀ + ½`, anti-linear there, such that the anti-linear part of the glued form
`∑ ρ_i · testForm φ i + ∑ χ_j ξN_j` has smooth coefficients in both holomorphic charts of each
sphere. -/
def NeckTestForms (F : FormGlueN A) : Prop :=
  ∀ φ : Ix A → ℝ × ℝ → ℝ, (∀ o, IsTest (φ o)) →
    ∀ γ : Fin A.nn × Fin (Module.finrank ℝ E) → ℝ × ℝ → ℝ, (∀ jk, IsTest (γ jk)) →
      ∃ ξN : Fin A.nn → Form E twoSpheres,
        (∀ j k (x : ℝ × ℝ), A.s0 j + 1 / 2 ≤ x.1 → γ (j, k) x = formNeckRep A j k (ξN j) x) ∧
        (∀ j (x : ℝ × ℝ), A.s0 j + 1 / 2 ≤ x.1 → ξN j (twoSpheres.polar (A.hol j) x) ∈
          twoSpheres.antiLinearForms J q (twoSpheres.polar (A.hol j) x)) ∧
        IsSphereSmooth (fun z => projF (J.J q) (glueForm F (testForm A φ) ξN) (Sum.inl z)) ∧
        IsSphereSmooth (fun z => projF (J.J q) (glueForm F (testForm A φ) ξN) (Sum.inr z))

/-- **The smooth forms are dense in the fibre**, given the neck test forms. -/
theorem smoothFormsDenseN_of_neckTestForms (hA : IsStdNeck A) (hG : GlueCharts A)
    (F : FormGlueN A) (h : NeckTestForms J F) : SmoothFormsDenseN J δ h0 hmono (A := A) := by
  refine smoothFormsDenseN_of_phiN hA hG F fun w hw => ?_
  choose φ hφ hwφ using fun o => hw.1 o (mem_univ _)
  choose γ hγ hwγ using fun jk => hw.2 jk (mem_univ _)
  obtain ⟨ξN, h1, h2, h3, h4⟩ := h φ hφ γ hγ
  have hg : IsGlueRep J w (testForm A φ) ξN :=
    ⟨fun i d k => ⟨φ (i, d, k), by rw [hwφ (i, d, k)]; exact MemLp.coeFn_toLp ((hφ _).memLp 2),
        fun p hp => (formDiscRep_testForm twoSpheres_chartsOnto (fun _ => rfl) A φ i d k hp).symm⟩,
      fun j k => ⟨γ (j, k), by rw [hwγ (j, k)]; exact MemLp.coeFn_toLp ((hγ _).memLp 2),
        h1 j k⟩, h2⟩
  have hrep : IsFormRep (projF (J.J q) (glueForm F (testForm A φ) ξN))
      (phiN twoSpheres_chartsOnto hG F (J.J q) δ h0 hmono w) :=
    isFormRep_phiN twoSpheres_chartsOnto hG F J hg
  have hmemS : phiN twoSpheres_chartsOnto hG F (J.J q) δ h0 hmono w ∈ formsSub J A δ h0 hmono :=
    ⟨projF (J.J q) (glueForm F (testForm A φ) ξN), fun y _ => projF_mem J q _ y, hrep⟩
  have ha1 : IsAntiJ (J.J q)
      fun z => projF (J.J q) (glueForm F (testForm A φ) ξN) (Sum.inl z) := by
    intro y v
    have := (NodalSurface.mem_antiLinearForms J twoSpheres).1
      (projF_mem J q (glueForm F (testForm A φ) ξN) (Sum.inl y)) v
    rw [twoSpheres_j_inl] at this
    exact this
  have ha2 : IsAntiJ (J.J q)
      fun z => projF (J.J q) (glueForm F (testForm A φ) ξN) (Sum.inr z) := by
    intro y v
    have := (NodalSurface.mem_antiLinearForms J twoSpheres).1
      (projF_mem J q (glueForm F (testForm A φ) ξN) (Sum.inr y)) v
    rw [twoSpheres_j_inr] at this
    exact this
  refine ⟨⟨phiN twoSpheres_chartsOnto hG F (J.J q) δ h0 hmono w,
    formsSub_le J A δ h0 hmono hmemS⟩, ?_, rfl⟩
  exact ⟨projF (J.J q) (glueForm F (testForm A φ) ξN), ha1, ha2, h3, h4, hrep⟩

/-- **The range of `D` is dense** (`0 ≤ δ₀ < 2π`), given the neck test forms. -/
theorem denseRange_linCRN_of_neckTestForms (hsm : NeckSmooth A) (G : GlueDataN A)
    (hA : IsStdNeck A) (hδ : δ 0 < 2 * Real.pi) (hG : GlueCharts A) (F : FormGlueN A)
    (h : NeckTestForms J F) :
    DenseRange (linCRN twoSpheres_chartsOnto hsm G δ h0 hmono J) :=
  denseRange_linCRN_of_smoothFormsDenseN hsm G hA hδ
    (smoothFormsDenseN_of_neckTestForms hA hG F h)

variable (q) in
/-- **Witness**: the constant map from `twoSpheres` has an atlas with the standard neck charts
satisfying `GlueCharts`, with the gluing data of the sections and of the forms. -/
theorem exists_glueAtlas_twoSpheres :
    ∃ A : SectionAtlas (E := E) twoSpheres (fun _ => q), IsStdNeck A ∧ GlueCharts A ∧
      NeckSmooth A ∧ Nonempty (GlueDataN A) ∧ Nonempty (FormGlueN A) := by
  obtain ⟨A, hA, hinj, hav⟩ := exists_sectionAtlas_glue (E := E) twoSpheres (fun _ => q)
    continuous_const nodeChart isHolChart_nodeChart
  have hG := glueCharts_of_isStdNeck hA hinj hav
  exact ⟨A, hA, hG, neckSmooth_of_isStdNeck hA, nonempty_glueDataN hG twoSpheres_chartsOnto,
    nonempty_formGlueN hG twoSpheres_chartsOnto⟩

end Dense

end GWMemoir
