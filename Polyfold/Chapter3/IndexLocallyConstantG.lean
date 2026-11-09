import Polyfold.Chapter3.IndexLocallyConstant
import Polyfold.Chapter3.LinearizationChartsScG
import Polyfold.Chapter3.ParamPerturbationG

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory I* (2014 preprint), Part I, §3.6 and §6
(Theorem 3.6.8 (preprint 3.54) and the proof of Proposition 6.2.2 (preprint 6.2), p. 240 (preprint p. 201)): **the Fredholm index of the linearization
is locally constant along the zero set of an sc-Fredholm section**, **in the text's germ reading of
Definition 3.1.11 (preprint 3.11)** (phase 2; round-trip item V3.98 (b)).

# The index along the zero set, germ reading

## The text, paraphrased

See `IndexLocallyConstant.lean`: the text's device for Proposition 6.2.2 (preprint 6.2) adds finitely many
sc⁺-sections with parameters `λ`, applies the implicit function theorem to
`F(λ, y) = f(y) + Σ λᵢ sᵢ(y)`, and reads off the index from the solution manifold of `F`.  The
germs of Definition 3.1.11 (preprint 3.11) are germs (the filling and the sc⁺-section are sc-smooth on germs of
neighbourhoods whose levels may shrink).

## What is formalized

* `Polyfold.StrongBundle.isLinOfIndex_of_conjugationData`: the index of `f'(y)` (in every
  chart, `IsLinOfIndex`) is `dim Pn − dim Q` for every germ datum of Definition 3.1.11 (preprint 3.11) at `y` in the
  germ reading (`linAt_index_of_conjugationData`).
* `Polyfold.StrongBundle.isLinOfIndex_of_paramSection_isLinOfIndex`: if `F` has index `d` at
  `(0, y)`, then `f` has index `d − k` at the zero `y`, for `f` sc-Fredholm in the germ reading
  (`theorem_3_1_21_preprint`, `linAt_paramSection_zero`, `linAt_isScFredholm`).
* Local copies of the Chapter 5 steps, germ reading: `Polyfold.exists_spanning_sections_germ`,
  `Polyfold.isLinSurjAt_paramSection_zero_of_spanning_germ`,
  `Polyfold.spanning_of_isLinSurjAt_germ`,
  `Polyfold.exists_sections_isParamGP_germ` (sections with (i)–(ii) of the proof of Theorem 5.3.10 (preprint 5.18) at
  a zero), and `Polyfold.isGoodPositionGermTame_paramSection_of_isParamGP` ((i)–(ii) give **good
  position** of `F` at `(0, y)` in a tame chart, germ reading).
* **The index is locally constant along the zero set**:
  `Polyfold.index_locally_constant_of_admitsBumpFunctions` (level `0`) and
  `Polyfold.theorem_3_6_8_index_locally_constant_general` (sc form), with the hypotheses
  `PX.AdmitsBumpFunctions` and `IsScFredholmSectionTame`.

## What the text leaves implicit, and the choices made

* As in `IndexLocallyConstant.lean`.  The germ inputs: Proposition 3.6.5 (preprint 3.52) for germs (the index in the
  chart of the germ datum, carried to every chart; the closed range of finite codimension of
  `Lin(0)` for the spanning sections), Theorem 3.1.21 (preprint 3.18) for germs, the linearization of `F` in the
  product chart (about the whole-chart maps `f̂ ∘ r` and `ŝᵢ`), Theorem 3.6.8 (preprint 3.54) (1) and the dimension
  count in the germ reading (`theorem_3_6_8_index_locally_constant`).
* **Good position, not general position.**  The old proof went through the general position of
  `F` at `(0, x₀)` (Definition 5.3.9 (preprint 5.17), `isGeneralPositionGerm_paramSection_of_isParamGP`) and Lemma
  5.26.  The general position needs `ker F'(0, y) = T_{(0, y)}S̃`
  (`exists_isGeneralPositionGerm_iff`,
  `exists_tangentSpace_eq_linKer`, Chapter 5), which is not redone here; the index statement only
  uses the good position, which is the first half of that proof
  (`isGoodPositionGermTame_paramSection_of_isParamGP`).
* The Chapter 5 copies live in this Chapter 3 file because `IndexLocallyConstant.lean` already
  imports `Chapter5.GeneralPosition`; in the switch of Definition 3.1.11 (preprint 3.11) to the germ reading (stage
  2) the Chapter 5 originals can take these proofs.
-/

open Set Filter Topology Function Module ContinuousLinearMap

noncomputable section

namespace Polyfold

universe u v

section Bundle

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle PX P}
  {f : X → Y}

open StrongRetr

/-- **The index of `f'(y)` is `dim Pn − dim Q` for every germ datum at `y`, germ reading** (phase
2; the germ form of `StrongBundle.isLinOfIndex_of_conjugationData_wholeChart`): for a datum of Definition 3.1.11 (preprint 3.11)
at the zero `y` in the germ reading (a chart `c` centred at `y`, a filling germ `g`, an sc⁺-germ
`s` with `s(0) = g(0)`, conjugation data `dc` of `g − s` to a basic germ), `f'(y)` is Fredholm of
index `dim dc.Pn − dim dc.Q` in every chart (`linAt_index_of_conjugationData`, with the
derivative family `scDerivGerm` of `g` on the germ of `IsFillingGerm.germ`). -/
theorem StrongBundle.isLinOfIndex_of_conjugationData (hf : B.IsScSmoothSection f) {y : X}
    (hy0 : IsZeroAt P f y) {c : StrongBundleChart PX P} (hc : B.IsChart c)
    (hyV : y ∈ c.φ.source) (hφ0 : c.φ y = 0) (h0 : (0 : c.φ.model.E 0) ∈ c.U)
    {g : c.φ.model.E 0 → c.F 0} {s : c.φ.model.E 0 → c.F 1}
    (hfill : IsFillingGerm c.relOpen c.isRetraction h0 (c.principal f) g)
    (hs : IsScPlusGerm c.φ.model.C c.U s) (hs0 : c.F.toBase 1 (s 0) = g 0)
    (dc : ConjugationData c.U fun u => g u - c.F.toBase 1 (s u)) :
    B.IsLinOfIndex f y (finrank ℝ dc.Pn - finrank ℝ dc.Q) := by
  obtain ⟨G, hG, hgsm, -⟩ := hfill.germ
  have hg := (hgsm 1).1.isSc1GermWith_scDerivGerm
  intro _ hc' hyV' _ hz' hzU' L' hL'
  obtain ⟨hF, hind, -⟩ := StrongBundle.linAt_index_of_conjugationData hf hy0 hc hyV hφ0 h0
    hfill hG hg hs hs0 dc hc' hyV' hz' hzU' L' hL'
  exact ⟨hF, hind⟩

set_option maxHeartbeats 400000 in
-- the product chart `(r ↦ r) × φ₁` and its tangent space are unfolded through `PullbackChartData`
/-- **The index of `f` at a zero from the index of the parametrized section, germ reading** (phase
2; the germ form of `StrongBundle.isLinOfIndex_of_paramSection_isLinOfIndex_wholeChart`; the step of the proof
of Proposition 6.2.2 (preprint 6.2) "the index of `F'(0, y)` is `k + ind f'(y)`"): let `f` be an sc-Fredholm section
in the germ reading, `s₁, …, s_k` sc⁺-sections, `y` a zero of `f`, and suppose
`F(λ, y) = f(y) + Σ λᵢ sᵢ(y)` is Fredholm of index `d` at its zero `(0, y)` in every chart of `π*P`.
Then `f'(y)` is Fredholm of index `d − k` in every chart.  Proof: in the product chart over the
chart `c₁` of the germ datum at `y`, `Lin_F(0)(δa, δu) = Lin_f(0) δu + Σ δaᵢ ŝᵢ(0)`
(`linAt_paramSection_zero`), so `d = ind Lin_F(0) = ind Lin_f(0) + k`
(`fredholmIndex_eq_of_param`), and the index of `f'(y)` in every chart is that in `c₁`
(`isLinOfIndex_of_conjugationData`). -/
theorem StrongBundle.isLinOfIndex_of_paramSection_isLinOfIndex {k : ℕ}
    [ParacompactSpace ((Fin k → ℝ) × X)]
    [ParacompactSpace (pullbackSpace P (Prod.snd : (Fin k → ℝ) × X → X))]
    (hf : B.IsScFredholmSection f) {s : Fin k → X → Y} (hs : ∀ i, B.IsScPlusSection (s i))
    {y : X} (hy0 : IsZeroAt P f y) {d : ℤ}
    (hF : (B.pullback (MPolyfold.isScSmoothMap_snd (rnPolyfold k) PX)).IsLinOfIndex
      (paramSection f hf.isScSmooth.1 s fun i => (hs i).1) (0, y) d) :
    B.IsLinOfIndex f y (d - k) := by
  classical
  set F := paramSection f hf.isScSmooth.1 s (fun i => (hs i).1) with hFdef
  have hFF : (B.pullback (MPolyfold.isScSmoothMap_snd (rnPolyfold k) PX)).IsScFredholmSection F :=
    theorem_3_1_21_preprint hf hs
  have hFs : IsSection (pullbackProj P Prod.snd) F := hFF.isScSmooth.1
  have hz0 : IsZeroAt (pullbackProj P Prod.snd) F (0, y) := by
    rw [hFdef, isZeroAt_paramSection_iff]
    change IsZeroAt P (paramSlice f hf.isScSmooth.1 s (fun i => (hs i).1) 0) y
    rw [paramSlice_zero]; exact hy0
  -- the chart of the germ datum at `y`
  have hys : y ∈ PX.smoothSet := hf.mem_smoothSet_of_isZeroAt hy0
  obtain ⟨-, c₁, hc₁, hyV₁, hφ₁, h0₁, g₁, s₁, hfill₁, hs₁, hs0₁, hconj₁⟩ := hf.germ y hys
  obtain ⟨d₁⟩ := isConjugateToBasicGerm_iff_nonempty.1 hconj₁
  have hidx₁ := StrongBundle.isLinOfIndex_of_conjugationData hf.isScSmooth hy0 hc₁ hyV₁ hφ₁
    h0₁ hfill₁ hs₁ hs0₁ d₁
  suffices hsuff : (finrank ℝ d₁.Pn - finrank ℝ d₁.Q : ℤ) = d - k by rw [← hsuff]; exact hidx₁
  -- `L₁ = Lin_f(0) : T₀O₁ → K₁` in `c₁`
  have h0O₁ : (0 : c₁.φ.model.E 0) ∈ c₁.φ.model.O := by
    rw [← hφ₁]; exact c₁.φ.mapsTo_model y hyV₁
  have h0O₁' : (0 : c₁.φ.model.E 0) ∈ r c₁.R '' c₁.U := c₁.r_image ▸ h0O₁
  have hz₁ : c₁.φ.model.E.toBase 1 (0 : c₁.φ.model.E 1) = c₁.φ y := by rw [map_zero, hφ₁]
  have hzU₁ : c₁.φ.model.E.toBase 1 (0 : c₁.φ.model.E 1) ∈ c₁.U := by rw [map_zero]; exact h0₁
  have hzO₁ : c₁.φ.model.E.toBase 1 (0 : c₁.φ.model.E 1) ∈ r c₁.R '' c₁.U := by
    rw [map_zero]; exact h0O₁'
  have hfr₁ : IsSc1 c₁.U (c₁.principal f ∘ r c₁.R) := hf.isScSmooth.isSc1_principal_comp_r hc₁
  have hfK₁ : ∀ x ∈ r c₁.R '' c₁.U, (x, c₁.principal f x) ∈ c₁.R '' (c₁.U ×ˢ univ) :=
    fun x hx => c₁.principal_mem_K hf.isScSmooth.1 (c₁.r_image ▸ hx)
  have hfz₁ : c₁.principal f (c₁.φ.model.E.toBase 1 (0 : c₁.φ.model.E 1)) = 0 := by
    rw [hz₁]; exact (c₁.isZeroAt_iff hf.isScSmooth.1 hyV₁).1 hy0
  have hmem₁ : ∀ x : ↥(rangeS (scDeriv c₁.U (r c₁.R) (0 : c₁.φ.model.E 1))),
      linAt c₁.U c₁.R (c₁.principal f) 0 x ∈ rangeS (ρCLM c₁.isRetraction hzU₁) := fun x =>
    ⟨_, rho_scDeriv_comp_r c₁.relOpen c₁.isRetraction hfr₁ hfK₁ hzO₁ hfz₁ x⟩
  set L₁ := (linAt c₁.U c₁.R (c₁.principal f) 0).codRestrict _ hmem₁ with hL₁
  obtain ⟨hL₁F, hL₁ind⟩ := hidx₁ c₁ hc₁ hyV₁ 0 hz₁ hzU₁ L₁ fun _ => rfl
  -- the product chart `(r ↦ r) × φ₁` at `(0, y)` and `L_F = Lin_F(0)`
  set q₀ := F (0, y) with hq₀
  set pc := (PullbackChartData.ofProd c₁ 0).toChart q₀ with hpc
  have hpcc : (B.pullback (MPolyfold.isScSmoothMap_snd (rnPolyfold k) PX)).IsChart pc :=
    (PullbackChartData.ofProd c₁ 0).isChart_toChart B _ hc₁ q₀
  have hzV : (0, y) ∈ pc.φ.source := ⟨mem_univ _, hyV₁⟩
  have hpc0 : pc.φ (0, y) = 0 := ofProd_apply_eq_zero c₁ 0 q₀ hφ₁
  have hzF : pc.φ.model.E.toBase 1 (0 : pc.φ.model.E 1) = pc.φ (0, y) := by
    rw [map_zero, hpc0]
  have hzUF : pc.φ.model.E.toBase 1 (0 : pc.φ.model.E 1) ∈ pc.U := by
    rw [map_zero]; exact ⟨mem_univ _, h0₁⟩
  have hzOF : pc.φ.model.E.toBase 1 (0 : pc.φ.model.E 1) ∈ r pc.R '' pc.U := by
    rw [pc.r_image, hzF]; exact pc.φ.mapsTo_model (0, y) hzV
  have hfrF : IsSc1 pc.U (pc.principal F ∘ r pc.R) := hFF.isScSmooth.isSc1_principal_comp_r hpcc
  have hfKF : ∀ x ∈ r pc.R '' pc.U, (x, pc.principal F x) ∈ pc.R '' (pc.U ×ˢ univ) :=
    fun x hx => pc.principal_mem_K hFs (pc.r_image ▸ hx)
  have hfzF : pc.principal F (pc.φ.model.E.toBase 1 (0 : pc.φ.model.E 1)) = 0 := by
    rw [hzF]; exact (pc.isZeroAt_iff hFs hzV).1 hz0
  have hmemF : ∀ x : ↥(rangeS (scDeriv pc.U (r pc.R) (0 : pc.φ.model.E 1))),
      linAt pc.U pc.R (pc.principal F) 0 x ∈ rangeS (ρCLM pc.isRetraction hzUF) := fun x =>
    ⟨_, rho_scDeriv_comp_r pc.relOpen pc.isRetraction hfrF hfKF hzOF hfzF x⟩
  set LF := (linAt pc.U pc.R (pc.principal F) 0).codRestrict _ hmemF with hLF
  obtain ⟨hLFF, hLFind⟩ := hF pc hpcc hzV 0 hzF hzUF LF fun _ => rfl
  -- the fibres `K_{F,0}` and `K₁` agree
  have hKeq : ∀ k' : pc.F 0, k' ∈ rangeS (ρCLM pc.isRetraction hzUF) ↔
      k' ∈ rangeS (ρCLM c₁.isRetraction hzU₁) := by
    intro k'
    refine (mem_rangeS_ρCLM_iff pc.isRetraction hzOF hzUF).trans ?_
    refine Iff.trans ?_ (mem_rangeS_ρCLM_iff c₁.isRetraction hzO₁ hzU₁).symm
    rw [map_zero, map_zero]
    exact mem_K_ofProd_zero_iff c₁ 0 q₀ h0O₁ k'
  -- `T₀(ℝᵏ × O₁) = ℝᵏ × T₀O₁`
  have hTmem : ∀ (a : Fin k → ℝ) (u : ↥(rangeS (scDeriv c₁.U (r c₁.R) (0 : c₁.φ.model.E 1)))),
      ((a, (u : c₁.φ.model.E 0)) : (Fin k → ℝ) × c₁.φ.model.E 0) ∈
        rangeS (scDeriv pc.U (r pc.R) (0 : pc.φ.model.E 1)) := by
    intro a u
    obtain ⟨u₀, hu₀⟩ := u.2
    exact ⟨(a, u₀), (PullbackChartData.ofProd_scDeriv_r c₁ 0 q₀ h0₁ (a, u₀)).trans
      (Prod.ext rfl hu₀)⟩
  -- completeness of the four spaces
  obtain ⟨-, hT₁, hK₁, -, -, -, -⟩ :=
    StrongBundle.linAt_isScFredholm hf hy0 hc₁ hyV₁ hz₁ hzU₁
  obtain ⟨-, hTF, hKF, -, -, -, -⟩ :=
    StrongBundle.linAt_isScFredholm hFF hz0 hpcc hzV hzF hzUF
  have : CompleteSpace ↥(rangeS (scDeriv c₁.U (r c₁.R) (0 : c₁.φ.model.E 1))) :=
    hT₁.isClosed.completeSpace_coe
  have : CompleteSpace ↥(rangeS (ρCLM c₁.isRetraction hzU₁)) := hK₁.isClosed.completeSpace_coe
  have : CompleteSpace ↥(rangeS (scDeriv pc.U (r pc.R) (0 : pc.φ.model.E 1))) :=
    hTF.isClosed.completeSpace_coe
  have : CompleteSpace ↥(rangeS (ρCLM pc.isRetraction hzUF)) := hKF.isClosed.completeSpace_coe
  -- the isomorphisms `ℝᵏ × T₀O₁ ≃ T₀(ℝᵏ × O₁)` and `K₁ ≃ K_{F,0}`
  set eT : ((Fin k → ℝ) × ↥(rangeS (scDeriv c₁.U (r c₁.R) (0 : c₁.φ.model.E 1)))) ≃L[ℝ]
      ↥(rangeS (scDeriv pc.U (r pc.R) (0 : pc.φ.model.E 1))) :=
    ContinuousLinearEquiv.equivOfInverse
      (((ContinuousLinearMap.id ℝ (Fin k → ℝ)).prodMap
        (rangeS (scDeriv c₁.U (r c₁.R) (0 : c₁.φ.model.E 1))).subtypeL).codRestrict _
          fun p => hTmem p.1 p.2)
      (((ContinuousLinearMap.fst ℝ (Fin k → ℝ) (c₁.φ.model.E 0)).comp
          (rangeS (scDeriv pc.U (r pc.R) (0 : pc.φ.model.E 1))).subtypeL).prod
        (((ContinuousLinearMap.snd ℝ (Fin k → ℝ) (c₁.φ.model.E 0)).comp
          (rangeS (scDeriv pc.U (r pc.R) (0 : pc.φ.model.E 1))).subtypeL).codRestrict _
            fun w => PullbackChartData.ofProd_mem_tangent c₁ 0 q₀ h0₁ w.2))
      (fun p => Prod.ext rfl (Subtype.ext rfl)) (fun w => Subtype.ext (Prod.ext rfl rfl))
    with heT
  set eK : ↥(rangeS (ρCLM c₁.isRetraction hzU₁)) ≃L[ℝ] ↥(rangeS (ρCLM pc.isRetraction hzUF)) :=
    restrictEquiv _ _ (ContinuousLinearMap.id ℝ (c₁.F 0)) (ContinuousLinearMap.id ℝ (c₁.F 0))
      (fun x hx => (hKeq x).2 hx) (fun x hx => (hKeq x).1 hx) (fun _ _ => rfl) (fun _ _ => rfl)
    with heK
  -- the finite-rank part `a ↦ Σ aᵢ ŝᵢ(0)`
  have hsmem : ∀ i, c₁.principal (s i) 0 ∈ rangeS (ρCLM c₁.isRetraction hzU₁) := fun i => by
    rw [mem_rangeS_ρCLM_iff c₁.isRetraction hzO₁ hzU₁, map_zero]
    exact c₁.principal_mem_K (hs i).1 h0O₁
  set Ef : (Fin k → ℝ) →L[ℝ] ↥(rangeS (ρCLM c₁.isRetraction hzU₁)) :=
    ∑ i, (ContinuousLinearMap.proj i).smulRight
      (⟨c₁.principal (s i) 0, hsmem i⟩ : ↥(rangeS (ρCLM c₁.isRetraction hzU₁))) with hEf
  set M := L₁.comp (ContinuousLinearMap.snd ℝ (Fin k → ℝ) _) +
    Ef.comp (ContinuousLinearMap.fst ℝ (Fin k → ℝ) _) with hM
  -- the conjugation `L_F ∘ eT = eK ∘ M`
  have hconj : ∀ p, LF (eT p) = eK (M p) := by
    intro p
    apply Subtype.ext
    change linAt pc.U pc.R (pc.principal F) 0 (eT p) = ((M p : _) : c₁.F 0)
    rw [linAt_paramSection_zero hf hs hc₁ h0O₁ q₀ (eT p).2]
    change linAt c₁.U c₁.R (c₁.principal f) 0 ⟨p.2.1, _⟩ + ∑ i, p.1 i • c₁.principal (s i) 0 =
      (L₁ p.2 : c₁.F 0) + (Ef p.1 : c₁.F 0)
    rw [hEf]
    simp only [FunLike.coe_sum, Finset.sum_apply, Submodule.coe_sum,
      ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.proj_apply, Submodule.coe_smul]
    rfl
  obtain ⟨hiff, hind⟩ := isFredholm_iff_of_conj hconj
  have hMF : M.IsFredholm := hiff.2 hLFF
  have hMind : fredholmIndex M = fredholmIndex L₁ + k := fredholmIndex_eq_of_param hL₁F Ef hM hMF
  have h1 := hind hMF
  rw [hLFind] at h1
  rw [← hL₁ind]
  omega

end Bundle

/-! ### The parametrized section at a zero: the Chapter 5 steps, germ reading

Local copies (germ reading, phase 2) of the Chapter 5 lemmas that the proof of
`index_locally_constant_of_admitsBumpFunctions_wholeChart` uses, with the hypotheses `IsScFredholmSection`,
`IsScFredholmSectionTame` in place of `IsScFredholmSectionWholeChart(Tame)`.  The proofs are those of
`Chapter5/Transversality.lean` and `Chapter5/GeneralPosition.lean`; the germ inputs are
Proposition 3.6.5 (preprint 3.52) for germs (`proposition_3_6_5_preprint`, for the closed range of finite codimension of
`Lin(0)`), the linearization of the parametrized section (`linAt_paramSection_zero`),
Theorem 3.1.21 (preprint 3.18) for germs (`theorem_3_1_21_preprint`, `theorem_3_1_21_tame`) and the assembly of good
position from a non-centred chart (`isGoodPositionGerm_of_linAt_surj`,
`IsGoodPositionGerm.toTame`).
Only the **good position** of the parametrized section is derived (not the general position of
Definition 5.3.9 (preprint 5.17), whose proof goes through `exists_isGeneralPositionGerm_iff`); it is what the index
statement needs. -/

section SpanningGerm

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle PX P}

open StrongRetr

/-- **Spanning sc⁺-sections at a zero, germ reading** (phase 2; the germ form of
`exists_spanning_sections`, Chapter 5): let `X` admit sc-smooth bump functions, `N` be an auxiliary
norm, `g` an sc-Fredholm section in the germ reading, `y` a zero of `g` and `U ∋ y` open.  Then
there are finitely many allowable sc⁺-sections `s₁, …, s_k` supported in `U` and a strong bundle
chart `c` centred at `y` in which `Lin(0)(T₀O) + span{ŝᵢ(0)} = K₀`.  The proof is the old one, with
`Lin(0) = Tf̃(0)` Fredholm by Proposition 3.6.5 (preprint 3.52) for germs (`proposition_3_6_5_preprint`,
`IsFillingGerm.fillerRestrict_eq_linAt`). -/
theorem exists_spanning_sections_germ (hbump : PX.AdmitsBumpFunctions) {N : B.One → ℝ}
    (hN : B.IsAuxNorm N) {g : X → Y} (hg : B.IsScFredholmSection g) {y : X}
    (hy0 : IsZeroAt P g y) {U : Set X} (hU : IsOpen U) (hyU : y ∈ U) :
    ∃ (k : ℕ) (s : Fin k → X → Y), (∀ i, B.IsScPlusSection (s i)) ∧
      (∀ i, sectionSupport P (s i) ⊆ U) ∧
      (∀ i x (hx : s i x ∈ B.oneSet), N (B.oneMk (s i x) hx) ≤ 1) ∧
      ∃ (c : StrongBundleChart PX P) (_ : B.IsChart c) (_ : y ∈ c.φ.source) (_ : c.φ y = 0),
        ∀ k', ((0 : c.φ.model.E 0), k') ∈ c.K →
          ∃ (u : ↥(rangeS (scDeriv c.U (r c.R) 0))) (a : Fin k → ℝ),
            linAt c.U c.R (c.principal g) 0 u + ∑ i, a i • c.principal (s i) 0 = k' := by
  classical
  have hgs : IsSection P g := hg.isScSmooth.1
  have hys : y ∈ PX.smoothSet := hg.mem_smoothSet_of_isZeroAt hy0
  obtain ⟨c, hc, hyV, hφ0, h0U, gf, hfill, G, -, -, Dg, hDg, h1, n, Nn, -, -, hFred, -⟩ :=
    proposition_3_6_5_preprint hgs (hg.germ y hys) hy0
  have h0O : (0 : c.φ.model.E 0) ∈ r c.R '' c.U := by
    rw [c.r_image, ← hφ0]; exact c.φ.mapsTo_model y hyV
  have hfr : IsSc1 c.U (c.principal g ∘ r c.R) := hg.isScSmooth.isSc1_principal_comp_r hc
  set L := fillerRestrict (scDeriv c.U (r c.R) 0) (ρCLM c.isRetraction h0U) (Dg 0) h1
    with hLdef
  have hL : ∀ x, (L x : c.F 0) = linAt c.U c.R (c.principal g) 0 x := fun x =>
    hfill.fillerRestrict_eq_linAt c.relOpen c.isRetraction h0O hfr hDg h1 x
  have : CompleteSpace ↥(rangeS (ρCLM c.isRetraction h0U)) :=
    (isClosed_range_of_idem _ fun k => ρ_ρ c.isRetraction h0O k).completeSpace_coe
  -- the smooth vectors of `K₀` are dense
  have hρsm : ∀ h ∈ c.F.smooth, ρCLM c.isRetraction h0U h ∈ c.F.smooth := by
    intro h hh
    refine c.F.mem_smooth_iff.2 fun m => ?_
    obtain ⟨h', hh'⟩ := c.F.mem_smooth_iff.1 hh m
    exact (c.isRetraction.preserves_filtration m m (Nat.le_succ m) 0 h0U ⟨0, map_zero _⟩ h
      ⟨h', hh'⟩).2
  set D : Submodule ℝ ↥(rangeS (ρCLM c.isRetraction h0U)) :=
    c.F.smooth.comap (rangeS (ρCLM c.isRetraction h0U)).subtype with hDdef
  have hD : Dense (D : Set ↥(rangeS (ρCLM c.isRetraction h0U))) := by
    set ρ' : c.F 0 → ↥(rangeS (ρCLM c.isRetraction h0U)) :=
      fun h => ⟨ρCLM c.isRetraction h0U h, ⟨h, rfl⟩⟩ with hρ'
    have hcont : Continuous ρ' := (ρCLM c.isRetraction h0U).continuous.subtype_mk _
    have hdr : DenseRange ρ' := by
      refine Function.Surjective.denseRange ?_
      rintro ⟨k, k', hk'⟩
      exact ⟨k', Subtype.ext hk'⟩
    have hsm : Dense (c.F.smooth : Set (c.F 0)) := c.F.dense_smooth 0
    refine (hdr.dense_image hcont hsm).mono ?_
    rintro _ ⟨h, hh, rfl⟩
    exact hρsm h hh
  obtain ⟨k, d, hdD, hspan⟩ := exists_fin_mem_of_dense_of_closedComplemented
    hFred.closedComplemented_range hFred.finite_coker hD
  -- the vectors `eᵢ = dᵢ ∈ K₀ ∩ F_∞` as smooth points of `Y`
  have hdK : ∀ i, ((0 : c.φ.model.E 0), (d i : c.F 0)) ∈ c.K := fun i =>
    (mem_rangeS_ρCLM_iff c.isRetraction h0O h0U).1 (d i).2
  have hdsm : ∀ i, (d i : c.F 0) ∈ c.F.smooth := fun i => hdD i
  have hφsymm0 : c.φ.symm 0 = y := by rw [← hφ0]; exact c.φ.symm_apply_apply hyV
  set e : Fin k → Y := fun i => c.toPartialEquiv.symm (0, (d i : c.F 0)) with hedef
  have hPe : ∀ i, P (e i) = y := fun i => by
    change P (c.toPartialEquiv.symm (0, (d i : c.F 0))) = y
    rw [c.proj_symm (hdK i)]; exact hφsymm0
  have hesm : ∀ i, e i ∈ B.toMPolyfold0.smoothSet := fun i =>
    mem_smoothSet_toMPolyfold0_of_chart hc (hdK i) c.φ.model.E.smooth.zero_mem (hdsm i)
  -- Lemma 5.3.3 (preprint 5.11) at each `eᵢ`
  have hsec : ∀ i, ∃ he1 : e i ∈ B.oneSet, ∃ s : X → Y, B.IsScPlusSection s ∧ s y = e i ∧
      sectionSupport P s ⊆ U ∧
      ∀ x (hx : s x ∈ B.oneSet), N (B.oneMk (s x) hx) < N (B.oneMk (e i) he1) + 1 :=
    fun i => lemma_5_3_3 hbump hN hys (hesm i) (hPe i) one_pos hU hyU
  choose he1 s hs hsy hssupp hsN using hsec
  -- rescale by `1/Mᵢ`, `Mᵢ = N(eᵢ) + 1`
  set M : Fin k → ℝ := fun i => N (B.oneMk (e i) (he1 i)) + 1 with hMdef
  have hMpos : ∀ i, 0 < M i := fun i => by
    have := hN.nonneg (B.oneMk (e i) (he1 i))
    simp only [hMdef]; linarith
  set s' : Fin k → X → Y := fun i => sectionSmul P (fun _ => (M i)⁻¹) (s i) with hs'def
  refine ⟨k, s', fun i => (hs i).smul_left (isScSmoothMap_real_const _),
    fun i => (sectionSupport_sectionSmul_const_subset (hs i).1 _).trans (hssupp i),
    fun i x hx => ?_, c, hc, hyV, hφ0, fun k' hk' => ?_⟩
  · rw [hN.oneMk_sectionSmul_const (hs i) _ x hx, abs_of_pos (inv_pos.2 (hMpos i))]
    have := hsN i x ((hs i).mem_oneSet x)
    calc (M i)⁻¹ * N (B.oneMk (s i x) ((hs i).mem_oneSet x)) ≤ (M i)⁻¹ * M i :=
          mul_le_mul_of_nonneg_left this.le (inv_pos.2 (hMpos i)).le
      _ = 1 := inv_mul_cancel₀ (hMpos i).ne'
  · -- the spanning
    have hk'K : k' ∈ rangeS (ρCLM c.isRetraction h0U) :=
      (mem_rangeS_ρCLM_iff c.isRetraction h0O h0U).2 hk'
    obtain ⟨rr, hrr, a, hk'eq⟩ := hspan ⟨k', hk'K⟩
    obtain ⟨u, hu⟩ := LinearMap.mem_range.1 hrr
    refine ⟨u, fun i => a i * M i, ?_⟩
    have h0O' : (0 : c.φ.model.E 0) ∈ c.φ.model.O := by
      rw [← hφ0]; exact c.φ.mapsTo_model y hyV
    have hprin : ∀ i, c.principal (s' i) 0 = (M i)⁻¹ • (d i : c.F 0) := fun i => by
      change c.principal (sectionSmul P (fun _ => (M i)⁻¹) (s i)) 0 = _
      rw [principal_sectionSmul_const c (hs i).1 _ h0O']
      unfold StrongBundleChart.principal
      rw [hφsymm0, hsy i]
      change (M i)⁻¹ • (c (c.toPartialEquiv.symm (0, (d i : c.F 0)))).2 = _
      rw [c.apply_symm (hdK i)]
    have hval : k' = (rr : c.F 0) + ∑ i, a i • (d i : c.F 0) := by
      have := congrArg Subtype.val hk'eq
      simpa using this
    have hu' : (rr : c.F 0) = linAt c.U c.R (c.principal g) 0 u := by
      rw [← hu]; exact hL u
    rw [hval, hu']
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hprin i, smul_smul, mul_assoc, mul_inv_cancel₀ (hMpos i).ne', mul_one]


end SpanningGerm

section ParamChartGerm

variable {m : ℕ} {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X]
  {PX : MPolyfold X} {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y]
  {P : Y → X} [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})]
  [ParacompactSpace ((Fin m → ℝ) × X)]
  [ParacompactSpace (pullbackSpace P (Prod.snd : (Fin m → ℝ) × X → X))]
  {B : StrongBundle PX P} {g : X → Y} {t : Fin m → X → Y}

open StrongRetr

/-- **Transversality of `F` at `(0, y)` from spanning sections at `y`, germ reading** (phase 2;
the germ form of `isLinSurjAt_paramSection_zero_of_spanning`, Chapter 5): if in a chart `c`
centred at the zero `y` of `g` the range of `Lin_g(0)` and the vectors `t̂ᵢ(0)` span `K₀`, then
the linearization of `F(λ, y) = g(y) + Σ λᵢ tᵢ(y)` at `(0, y)` is onto
(`linAt_paramSection_zero`). -/
theorem isLinSurjAt_paramSection_zero_of_spanning_germ (hgF : B.IsScFredholmSection g)
    (htp : ∀ i, B.IsScPlusSection (t i)) {c : StrongBundleChart PX P} (hc : B.IsChart c) {y : X}
    (hyV : y ∈ c.φ.source) (hφ0 : c.φ y = 0)
    (q₀ : pullbackSpace P (Prod.snd : (Fin m → ℝ) × X → X))
    (hspan : ∀ k', ((0 : c.φ.model.E 0), k') ∈ c.K →
      ∃ (u : ↥(rangeS (scDeriv c.U (r c.R) 0))) (a : Fin m → ℝ),
        linAt c.U c.R (c.principal g) 0 u + ∑ i, a i • c.principal (t i) 0 = k') :
    (B.pullback (MPolyfold.isScSmoothMap_snd (rnPolyfold m) PX)).IsLinSurjAt
      (paramSection g hgF.isScSmooth.1 t fun i => (htp i).1) (0, y) := by
  have hχc : (B.pullback (MPolyfold.isScSmoothMap_snd (rnPolyfold m) PX)).IsChart
      ((PullbackChartData.ofProd c 0).toChart q₀) :=
    (PullbackChartData.ofProd c 0).isChart_toChart B _ hc q₀
  have h0O : (0 : c.φ.model.E 0) ∈ c.φ.model.O := by
    rw [← hφ0]; exact c.φ.mapsTo_model y hyV
  have h0U : (0 : c.φ.model.E 0) ∈ c.U :=
    mem_U_of_mem_O c.isRetraction (c.r_image ▸ h0O)
  have hzV' : (0, y) ∈ ((PullbackChartData.ofProd c 0).toChart q₀).φ.source :=
    ⟨mem_univ _, hyV⟩
  have hχ0 : ((PullbackChartData.ofProd c 0).toChart q₀).φ (0, y) = 0 :=
    ofProd_apply_eq_zero c 0 q₀ hφ0
  refine ⟨_, hχc, hzV', 0, by rw [map_zero, hχ0], fun k hk => ?_⟩
  rw [hχ0] at hk
  obtain ⟨u, a, hua⟩ := hspan k ((mem_K_ofProd_zero_iff c 0 q₀ h0O k).1 hk)
  obtain ⟨u₀, hu₀⟩ := u.2
  have hw : ((a, (u : c.φ.model.E 0)) : (Fin m → ℝ) × c.φ.model.E 0) ∈
      rangeS (scDeriv ((PullbackChartData.ofProd c 0).toChart q₀).U
        (r ((PullbackChartData.ofProd c 0).toChart q₀).R) 0) := by
    refine ⟨(a, u₀), ?_⟩
    exact (PullbackChartData.ofProd_scDeriv_r c 0 q₀ h0U (a, u₀)).trans (Prod.ext rfl hu₀)
  refine ⟨⟨_, hw⟩, ?_⟩
  rw [linAt_paramSection_zero hgF htp hc h0O q₀ hw]
  exact hua


end ParamChartGerm

section ConstructionGerm

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle PX P}
  {g : X → Y}

open StrongRetr

/-- The spanning condition (i) read in a chart `c` centred at `y`, from the surjectivity of
`F'(0, y)`, germ reading (phase 2; the germ form of `spanning_of_isLinSurjAt`, Chapter 5). -/
theorem spanning_of_isLinSurjAt_germ {m : ℕ} [ParacompactSpace ((Fin m → ℝ) × X)]
    [ParacompactSpace (pullbackSpace P (Prod.snd : (Fin m → ℝ) × X → X))]
    (hgF : B.IsScFredholmSection g) {t : Fin m → X → Y} (htp : ∀ i, B.IsScPlusSection (t i))
    {y : X} (hy0 : IsZeroAt P g y) {c : StrongBundleChart PX P} (hc : B.IsChart c)
    (hyV : y ∈ c.φ.source) (hφ0 : c.φ y = 0)
    (hsurj : (B.pullback (MPolyfold.isScSmoothMap_snd (rnPolyfold m) PX)).IsLinSurjAt
      (paramSection g hgF.isScSmooth.1 t fun i => (htp i).1) (0, y)) :
    ∀ k', ((0 : c.φ.model.E 0), k') ∈ c.K →
      ∃ (u : ↥(rangeS (scDeriv c.U (r c.R) 0))) (a : Fin m → ℝ),
        linAt c.U c.R (c.principal g) 0 u + ∑ i, a i • c.principal (t i) 0 = k' := by
  have hFsm := (theorem_3_1_21_preprint hgF htp).isScSmooth
  have hz0 : IsZeroAt (pullbackProj P Prod.snd)
      (paramSection g hgF.isScSmooth.1 t fun i => (htp i).1) (0, y) := by
    rw [isZeroAt_paramSection_iff]
    change IsZeroAt P (paramSlice g hgF.isScSmooth.1 t (fun i => (htp i).1) 0) y
    rw [paramSlice_zero]; exact hy0
  set q₀ := paramSection g hgF.isScSmooth.1 t (fun i => (htp i).1) (0, y) with hq₀
  have hc'B : (B.pullback (MPolyfold.isScSmoothMap_snd (rnPolyfold m) PX)).IsChart
      (pc0 c q₀) :=
    (PullbackChartData.ofProd c 0).isChart_toChart B _ hc q₀
  have hyV' : ((0 : Fin m → ℝ), y) ∈ (pc0 c q₀).φ.source :=
    ⟨mem_univ _, hyV⟩
  have hc'0 : (pc0 c q₀).φ (0, y) = 0 :=
    ofProd_apply_eq_zero c 0 q₀ hφ0
  have hz' : (pc0 c q₀).φ.model.E.toBase 1
      (0 : (pc0 c q₀).φ.model.E 1) =
      (pc0 c q₀).φ (0, y) := by rw [map_zero, hc'0]
  have h0O : (0 : c.φ.model.E 0) ∈ c.φ.model.O := hφ0 ▸ c.φ.mapsTo_model y hyV
  have hsurj' := hsurj.linAt_surjective hFsm hz0 hc'B hyV' hz'
  intro k' hk'
  have hkχ : ((pc0 c q₀).φ (0, y), k') ∈
      (pc0 c q₀).K := by
    rw [hc'0]; exact (mem_K_ofProd_zero_iff c 0 q₀ h0O k').2 hk'
  obtain ⟨⟨v, hv⟩, hvk⟩ := hsurj' k' hkχ
  rw [linAt_paramSection_zero hgF htp hc h0O q₀ hv] at hvk
  exact ⟨_, v.1, hvk⟩

set_option maxHeartbeats 3200000 in
-- the coordinates of the tame chart and Lemma 5.3.3 (preprint 5.11) at finitely many points
/-- **Sections with (i)–(ii) at a zero, germ reading** (phase 2; the germ form of
`exists_sections_isParamGP`, Chapter 5): let `X` admit sc-smooth bump functions, `N` be an
auxiliary norm, `g` an sc-Fredholm section with tame germ data in the germ reading, `x` a zero of
`g`, `c` a tame chart centred at `x` (presentation `T`) and `U ∋ x` open.  Then there are
finitely many allowable sc⁺-sections supported in `U` with (i)–(ii) at `(0, x)` in `c`
(`IsParamGP`).  The proof is the old one with `exists_spanning_sections_germ`,
`isLinSurjAt_paramSection_zero_of_spanning_germ` and `spanning_of_isLinSurjAt_germ`; the
construction of the tilting sections uses only that `g` is sc-smooth. -/
theorem exists_sections_isParamGP_germ (hbump : PX.AdmitsBumpFunctions) {N : B.One → ℝ}
    (hN : B.IsAuxNorm N) (hgFt : B.IsScFredholmSectionTame g) {x : X} (hx0 : IsZeroAt P g x)
    {c : StrongBundleChart PX P} (hc : B.IsTameChart c) (hxV : x ∈ c.φ.source)
    (hφ0 : c.φ x = 0) {n : ℕ} {Wq : ScBanach}
    (T : ScIso c.φ.model.E ((ScBanach.const (Fin n → ℝ)).prod Wq))
    (hT : c.φ.model.C = T 0 ⁻¹' quadrant n Wq 0) {U : Set X} (hU : IsOpen U) (hxU : x ∈ U) :
    ∃ (k : ℕ) (s : Fin k → X → Y) (_ : ∀ i, B.IsScPlusSection (s i)),
      (∀ i, sectionSupport P (s i) ⊆ U) ∧
      (∀ i y (hy : s i y ∈ B.oneSet), N (B.oneMk (s i y) hy) ≤ 1) ∧ c.IsParamGP g s T := by
  classical
  have hgF := hgFt.toIsScFredholmSection
  have hxs : x ∈ PX.smoothSet := hgF.mem_smoothSet_of_isZeroAt hx0
  -- (i): the spanning sections, read in `c`
  obtain ⟨k₁, s₁, hs₁, hs₁supp, hs₁N, c₁, hc₁, hxV₁, hφ₁, hspan₁⟩ :=
    exists_spanning_sections_germ hbump hN hgF hx0 hU hxU
  have := MPolyfold.paracompactSpace_prod (rnPolyfold k₁) PX
  have := paracompactSpace_pullbackSpace (f := (Prod.snd : (Fin k₁ → ℝ) × X → X))
    ((rnPolyfold k₁).prod PX) B
  have hsurj₁ := isLinSurjAt_paramSection_zero_of_spanning_germ hgF hs₁ hc₁ hxV₁ hφ₁
    (paramSection g hgF.isScSmooth.1 s₁ (fun i => (hs₁ i).1) (0, x)) hspan₁
  have hspan := spanning_of_isLinSurjAt_germ hgF hs₁ hx0 hc.1 hxV hφ0 hsurj₁
  -- (ii): the coordinates of the tame chart
  set R := c.isRetraction.baseRetraction c.relOpen with hRdef
  have hRT : R.IsTameWith T := hc.2 n Wq T hT
  have h0O : (0 : c.φ.model.E 0) ∈ c.φ.model.O := hφ0 ▸ c.φ.mapsTo_model x hxV
  have h0O' : (0 : c.φ.model.E 0) ∈ r c.R '' c.U := c.r_image ▸ h0O
  have h0U : (0 : c.φ.model.E 0) ∈ c.U := mem_U_of_mem_O c.isRetraction h0O'
  have hz : c.φ.model.E.toBase 1 (0 : c.φ.model.E 1) = c.φ x := by rw [map_zero, hφ0]
  have hzR : (0 : c.φ.model.E 1) ∈ c.φ.model.E.lvlSet R.retract 1 := by
    rw [ScBanach.mem_lvlSet, c.base_retract, hz]; exact c.φ.mapsTo_model x hxV
  have hzs : (0 : c.φ.model.E 1) ∈ c.φ.model.E.smoothLvl 1 := by
    change c.φ.model.E.toBase 1 0 ∈ c.φ.model.E.smooth
    rw [map_zero]; exact c.φ.model.E.smooth.zero_mem
  set e := c.φ.model.E.toBase 1 (0 : c.φ.model.E 1) with he
  have he0 : e = 0 := map_zero _
  set M := LinearMap.range (scDeriv R.U R 0 : c.φ.model.E 0 →ₗ[ℝ] c.φ.model.E 0) with hMdef
  set I := {i : Fin n // (T 0 e).1 i = 0} with hIdef
  set f : M →ₗ[ℝ] (I → ℝ) := (coordMapL T e : c.φ.model.E 0 →ₗ[ℝ] (I → ℝ)) ∘ₗ M.subtype
    with hf
  have hker : LinearMap.ker f = (reducedTangentSpaceWith R T 0).comap M.subtype := by
    ext ⟨v, hv⟩
    simp only [hf, LinearMap.mem_ker, LinearMap.comp_apply, Submodule.coe_subtype,
      Submodule.mem_comap, reducedTangentSpaceWith, Submodule.mem_inf]
    exact ⟨fun h => ⟨hv, h⟩, fun h => h.2⟩
  have hq := quotDim_reducedTangentSpaceWith_eq hRT hzR hzs
  rw [quotDim, ← hker] at hq
  have hrange : LinearMap.range f = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    rw [← (LinearMap.quotKerEquivRange f).finrank_eq, hq, Module.finrank_fintype_fun_eq_card,
      Fintype.card_subtype]
    rfl
  -- smooth preimages
  obtain ⟨hMsc, -, -⟩ := proposition_2_5_6_partialCone hT hRT hzR hzs
  set D : Submodule ℝ (c.φ.model.E 0) := M ⊓ c.φ.model.E.smooth with hD
  set S : Submodule ℝ (I → ℝ) := D.map (coordMapL T e : c.φ.model.E 0 →ₗ[ℝ] (I → ℝ)) with hS
  have hSclosed : IsClosed (S : Set (I → ℝ)) := S.closed_of_finiteDimensional
  have hpre : ∀ v : I → ℝ, ∃ l ∈ D, coordMapL T e l = v := by
    intro v
    have hv : v ∈ LinearMap.range f := by rw [hrange]; exact Submodule.mem_top
    obtain ⟨⟨w, hwM⟩, hwv⟩ := hv
    have hwcl : w ∈ closure ((M : Set (c.φ.model.E 0)) ∩ c.φ.model.E.smoothLvl 0) := by
      have := hMsc.2 0 (show w ∈ c.φ.model.E.levelSub M 0 by
        rw [ScBanach.levelSub_zero]; exact hwM)
      rwa [ScBanach.levelSub_zero] at this
    have hvS : v ∈ S := by
      have h1 : coordMapL T e w ∈ closure ((coordMapL T e) ''
          ((M : Set (c.φ.model.E 0)) ∩ c.φ.model.E.smoothLvl 0)) :=
        image_closure_subset_closure_image (coordMapL T e).continuous ⟨w, hwcl, rfl⟩
      have h2 : closure ((coordMapL T e) ''
          ((M : Set (c.φ.model.E 0)) ∩ c.φ.model.E.smoothLvl 0)) ⊆ (S : Set (I → ℝ)) := by
        refine closure_minimal ?_ hSclosed
        rintro _ ⟨l, ⟨hlM, hls⟩, rfl⟩
        exact ⟨l, ⟨hlM, hls⟩, rfl⟩
      have h3 := h2 h1
      rwa [← hwv]
    obtain ⟨l, hlD, hl⟩ := hvS
    exact ⟨l, hlD, hl⟩
  choose l hlD hlv using fun i : I => hpre (Pi.single i 1)
  -- the smooth fibre points `Φ⁻¹(0, Lin_g(0) lᵢ)`
  have hgr : IsScSmooth c.U (c.principal g ∘ r c.R) :=
    (((hgF.isScSmooth.isScSmoothRetractMap hc.1).comp_isScSmooth
      (c.isRetraction.baseRetraction c.relOpen) c.base_retract).snd c.relOpen.isScDomain).congr
      c.relOpen.isScDomain fun _ _ => rfl
  have hz1U : (0 : c.φ.model.E 1) ∈ c.φ.model.E.lvlSet c.U 1 := by
    rw [ScBanach.mem_lvlSet, map_zero]; exact h0U
  have hop := hgr.isSc1.isSc1With_scDeriv.scOperator_deriv hz1U hzs
  set d : I → c.F 0 := fun i => linAt c.U c.R (c.principal g) 0 ⟨l i, (hlD i).1⟩ with hd
  have hdK : ∀ i, ((0 : c.φ.model.E 0), d i) ∈ c.K := fun i => by
    have hzO : c.φ.model.E.toBase 1 (0 : c.φ.model.E 1) ∈ r c.R '' c.U := by
      rw [map_zero]; exact h0O'
    have hmem := rho_scDeriv_comp_r c.relOpen c.isRetraction
      (hgF.isScSmooth.isSc1_principal_comp_r hc.1)
      (fun x hx => c.principal_mem_K hgF.isScSmooth.1 (c.r_image ▸ hx)) hzO
      (by rw [map_zero, ← hφ0]; exact (c.isZeroAt_iff hgF.isScSmooth.1 hxV).1 hx0) (l i)
    have hzU : c.φ.model.E.toBase 1 (0 : c.φ.model.E 1) ∈ c.U := by rw [map_zero]; exact h0U
    have : d i ∈ rangeS (ρCLM c.isRetraction hzU) := ⟨_, hmem⟩
    have h2 := (mem_rangeS_ρCLM_iff c.isRetraction hzO hzU).1 this
    rwa [map_zero] at h2
  have hdsm : ∀ i, d i ∈ c.F.smooth := fun i => by
    refine c.F.mem_smooth_iff.2 fun j => ?_
    obtain ⟨Tj, hTj⟩ := hop j
    obtain ⟨lj, hlj⟩ := c.φ.model.E.mem_smooth_iff.1 (hlD i).2 j
    exact ⟨Tj lj, by rw [hTj, hlj]; rfl⟩
  have hφsymm0 : c.φ.symm 0 = x := by rw [← hφ0]; exact c.φ.symm_apply_apply hxV
  set ef : I → Y := fun i => c.toPartialEquiv.symm (0, d i) with hefdef
  have hPe : ∀ i, P (ef i) = x := fun i => by
    change P (c.toPartialEquiv.symm (0, d i)) = x
    rw [c.proj_symm (hdK i)]; exact hφsymm0
  have hesm : ∀ i, ef i ∈ B.toMPolyfold0.smoothSet := fun i =>
    mem_smoothSet_toMPolyfold0_of_chart hc.1 (hdK i) c.φ.model.E.smooth.zero_mem (hdsm i)
  -- Lemma 5.3.3 (preprint 5.11) at each point, rescaled
  have hsec : ∀ i, ∃ he1 : ef i ∈ B.oneSet, ∃ s : X → Y, B.IsScPlusSection s ∧ s x = ef i ∧
      sectionSupport P s ⊆ U ∧
      ∀ y (hy : s y ∈ B.oneSet), N (B.oneMk (s y) hy) < N (B.oneMk (ef i) he1) + 1 :=
    fun i => lemma_5_3_3 hbump hN hxs (hesm i) (hPe i) one_pos hU hxU
  choose he1 s₂ hs₂ hs₂x hs₂supp hs₂N using hsec
  set Mi : I → ℝ := fun i => N (B.oneMk (ef i) (he1 i)) + 1 with hMidef
  have hMpos : ∀ i, 0 < Mi i := fun i => by
    have := hN.nonneg (B.oneMk (ef i) (he1 i))
    simp only [hMidef]; linarith
  set s₂' : I → X → Y := fun i => sectionSmul P (fun _ => (Mi i)⁻¹) (s₂ i) with hs₂'def
  have hs₂'p : ∀ i, B.IsScPlusSection (s₂' i) := fun i =>
    (hs₂ i).smul_left (isScSmoothMap_real_const _)
  have hprin : ∀ i, c.principal (s₂' i) 0 = (Mi i)⁻¹ • d i := fun i => by
    change c.principal (sectionSmul P (fun _ => (Mi i)⁻¹) (s₂ i)) 0 = _
    rw [principal_sectionSmul_const c (hs₂ i).1 _ h0O]
    unfold StrongBundleChart.principal
    rw [hφsymm0, hs₂x i]
    change (Mi i)⁻¹ • (c (c.toPartialEquiv.symm (0, d i))).2 = _
    rw [c.apply_symm (hdK i)]
  -- the united family on `Fin (k₁ + k₂)`
  set k₂ := Fintype.card I with hk₂
  set eI := Fintype.equivFin I with heI
  set s : Fin (k₁ + k₂) → X → Y := Fin.append s₁ (fun j => s₂' (eI.symm j)) with hsdef
  have hsl : ∀ i, s (Fin.castAdd k₂ i) = s₁ i := fun i => Fin.append_left _ _ i
  have hsr : ∀ j, s (Fin.natAdd k₁ (eI j)) = s₂' j := fun j => by
    rw [hsdef, Fin.append_right, Equiv.symm_apply_apply]
  have hsp : ∀ i, B.IsScPlusSection (s i) := by
    refine Fin.addCases (fun i => ?_) (fun j => ?_)
    · rw [hsl]; exact hs₁ i
    · rw [show Fin.natAdd k₁ j = Fin.natAdd k₁ (eI (eI.symm j)) by rw [Equiv.apply_symm_apply],
        hsr]
      exact hs₂'p _
  refine ⟨k₁ + k₂, s, hsp, ?_, ?_, ?_, ?_⟩
  · refine Fin.addCases (fun i => ?_) (fun j => ?_)
    · rw [hsl]; exact hs₁supp i
    · rw [show Fin.natAdd k₁ j = Fin.natAdd k₁ (eI (eI.symm j)) by rw [Equiv.apply_symm_apply],
        hsr]
      exact (sectionSupport_sectionSmul_const_subset (hs₂ _).1 _).trans (hs₂supp _)
  · refine Fin.addCases (fun i y hy => ?_) (fun j y hy => ?_)
    · revert hy; rw [hsl]; exact hs₁N i y
    · revert hy
      rw [show Fin.natAdd k₁ j = Fin.natAdd k₁ (eI (eI.symm j)) by rw [Equiv.apply_symm_apply],
        hsr]
      intro hy
      set i := eI.symm j
      rw [hN.oneMk_sectionSmul_const (hs₂ i) _ y hy, abs_of_pos (inv_pos.2 (hMpos i))]
      have := hs₂N i y ((hs₂ i).mem_oneSet y)
      calc (Mi i)⁻¹ * N (B.oneMk (s₂ i y) ((hs₂ i).mem_oneSet y)) ≤ (Mi i)⁻¹ * Mi i :=
            mul_le_mul_of_nonneg_left this.le (inv_pos.2 (hMpos i)).le
        _ = 1 := inv_mul_cancel₀ (hMpos i).ne'
  · -- (i)
    intro k' hk'
    obtain ⟨u, a, hua⟩ := hspan k' hk'
    obtain ⟨a', ha'⟩ := exists_sum_comp_eq (Fin.castAdd k₂) a fun j => c.principal (s j) 0
    refine ⟨u, a', ?_⟩
    rw [ha', ← hua]
    congr 1
    exact Finset.sum_congr rfl fun i _ => by rw [hsl]
  · -- (ii)
    intro w
    set cw : I → ℝ := coordMapL T e w with hcw
    have hlM : ∀ i, l i ∈ M := fun i => (hlD i).1
    set u : ↥(rangeS (scDeriv c.U (r c.R) 0)) :=
      ⟨∑ i, cw i • l i, M.sum_mem fun i _ => M.smul_mem _ (hlM i)⟩ with hu
    have hLu : linAt c.U c.R (c.principal g) 0 u = ∑ i, cw i • d i := by
      have : u = ∑ i, cw i • (⟨l i, hlM i⟩ : ↥(rangeS (scDeriv c.U (r c.R) 0))) := by
        apply Subtype.ext; simp [hu]
      rw [this, map_sum]
      simp only [map_smul]
      rfl
    have hcoord : coordMapL T e (∑ i, cw i • l i) = cw := by
      rw [map_sum]
      simp only [map_smul, hlv]
      ext i
      simp only [Finset.sum_apply, Pi.smul_apply, Pi.single_apply, smul_eq_mul, mul_ite,
        mul_one, mul_zero]
      rw [Finset.sum_eq_single i (fun b _ hb => if_neg (Ne.symm hb))
        (fun h => absurd (Finset.mem_univ i) h), if_pos rfl]
    obtain ⟨a', ha'⟩ := exists_sum_comp_eq (fun i => Fin.natAdd k₁ (eI i))
      (fun i => -(cw i * Mi i)) fun j => c.principal (s j) 0
    refine ⟨u, a', ?_, ?_⟩
    · rw [ha', hLu]
      simp only [hsr, hprin, smul_smul, neg_mul, neg_smul, Finset.sum_neg_distrib]
      rw [← sub_eq_add_neg, sub_eq_zero]
      exact Finset.sum_congr rfl fun i _ => by
        rw [mul_assoc, mul_inv_cancel₀ (hMpos i).ne', mul_one]
    · have hc0 : coordMapL T e ((w : c.φ.model.E 0) - (u : c.φ.model.E 0)) = 0 := by
        rw [map_sub]
        change cw - coordMapL T e (∑ i, cw i • l i) = 0
        rw [hcoord, sub_self]
      rw [← he0, mem_minimalSubspaceWith]
      intro i hi
      have := congrFun hc0 ⟨i, hi⟩
      rwa [coordMapL_apply] at this


end ConstructionGerm

section ParamGPGerm

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle PX P}
  {g : X → Y} {m : ℕ} [ParacompactSpace ((Fin m → ℝ) × X)]
  [ParacompactSpace (pullbackSpace P (Prod.snd : (Fin m → ℝ) × X → X))]

open StrongRetr

set_option maxHeartbeats 3200000 in
-- the product chart and the reduced tangent space of the product quadrant
/-- **(i)–(ii) give good position of the parametrized section, germ reading** (phase 2; the part
of `isGeneralPositionGerm_paramSection_of_isParamGP` (Chapter 5) up to the good position): if
(i)–(ii) hold in a tame chart `c` centred at the zero `y` of `g` (sc-Fredholm with tame germ data
in the germ reading), the parametrized section `F(λ, y) = g(y) + Σ λᵢ tᵢ(y)` is in good position
in a tame chart at `(0, y)` in the germ reading (`IsGoodPositionGermTame`).  (i) gives `F'(0, y)`
onto in the tame product chart; (ii) gives `ker F'(0, y) + T^R = T(ℝᵐ × O)`, so `ker F'(0, y)` has
an algebraic complement inside `T^R` and is in good position to the partial cone
(`isInGoodPositionIn_of_scComplement_le_reduced`); `isGoodPositionGerm_of_linAt_surj` assembles
Definition 3.6.6 (preprint 3.53) in the chart of the germ data of `F` at `(0, y)` (Theorem 3.1.21 (preprint 3.18) for germs) and
`IsGoodPositionGerm.toTame` reads it in the tame chart. -/
theorem isGoodPositionGermTame_paramSection_of_isParamGP (hgFt : B.IsScFredholmSectionTame g)
    {t : Fin m → X → Y} (htp : ∀ i, B.IsScPlusSection (t i)) {y : X} (hy0 : IsZeroAt P g y)
    {c : StrongBundleChart PX P} (hc : B.IsTameChart c) (hyV : y ∈ c.φ.source)
    (hφ0 : c.φ y = 0) {n : ℕ} {Wq : ScBanach}
    (T : ScIso c.φ.model.E ((ScBanach.const (Fin n → ℝ)).prod Wq))
    (hT : c.φ.model.C = T 0 ⁻¹' quadrant n Wq 0) (h : c.IsParamGP g t T) :
    (B.pullback (MPolyfold.isScSmoothMap_snd (rnPolyfold m) PX)).IsGoodPositionGermTame
      (paramSection g hgFt.isScSmooth.1 t fun i => (htp i).1) (0, y) := by
  classical
  have hgF := hgFt.toIsScFredholmSection
  have hFt := theorem_3_1_21_tame hgFt htp
  have hz0 : IsZeroAt (pullbackProj P Prod.snd)
      (paramSection g hgFt.isScSmooth.1 t fun i => (htp i).1) (0, y) := by
    rw [isZeroAt_paramSection_iff]
    change IsZeroAt P (paramSlice g hgFt.isScSmooth.1 t (fun i => (htp i).1) 0) y
    rw [paramSlice_zero]; exact hy0
  set q₀ := paramSection g hgFt.isScSmooth.1 t (fun i => (htp i).1) (0, y) with hq₀
  have hc'B : (B.pullback (MPolyfold.isScSmoothMap_snd (rnPolyfold m) PX)).IsChart (pc0 c q₀) :=
    (PullbackChartData.ofProd c 0).isChart_toChart B _ hc.1 q₀
  have hc'T : (B.pullback (MPolyfold.isScSmoothMap_snd (rnPolyfold m) PX)).IsTameChart (pc0 c q₀) :=
    ⟨hc'B, PullbackChartData.ofProd_isTame c 0 q₀ hc.2⟩
  have hyV' : ((0 : Fin m → ℝ), y) ∈ (pc0 c q₀).φ.source := ⟨mem_univ _, hyV⟩
  have hc'0 : (pc0 c q₀).φ (0, y) = 0 := ofProd_apply_eq_zero c 0 q₀ hφ0
  have hz' : (pc0 c q₀).φ.model.E.toBase 1 (0 : (pc0 c q₀).φ.model.E 1) = (pc0 c q₀).φ (0, y) := by
    rw [map_zero, hc'0]
  have h0O : (0 : c.φ.model.E 0) ∈ c.φ.model.O := hφ0 ▸ c.φ.mapsTo_model y hyV
  have h0U : (0 : c.φ.model.E 0) ∈ c.U := mem_U_of_mem_O c.isRetraction (c.r_image ▸ h0O)
  -- (i): surjectivity
  have hsurjF := isLinSurjAt_paramSection_zero_of_spanning_germ hgF htp hc.1 hyV hφ0 q₀ h.1
  have hsurj' := hsurjF.linAt_surjective hFt.isScSmooth hz0 hc'B hyV' hz'
  -- the presentation of the product quadrant and `E_0 = ℝᵐ × E_0`
  have hT' : (pc0 c q₀).φ.model.C = (prodPresentation (rnPres m) T) 0 ⁻¹'
      quadrant (0 + n) ((ScBanach.const (Fin m → ℝ)).prod Wq) 0 :=
    prod_eq_prodPresentation (rnPres m) T (rnPres_eq (m := m)) hT
  have hmin : minimalSubspaceWith (prodPresentation (rnPres m) T)
      (0 : ((rnSc m).prod c.φ.model.E) 0) =
      (⊤ : Submodule ℝ (Fin m → ℝ)).prod (minimalSubspaceWith T 0) := by
    rw [minimalSubspaceWith_prodPresentation]
    simp only [Prod.fst_zero, Prod.snd_zero, minimalSubspaceWith_rnPres]
  have hb0 : ((rnSc m).prod c.φ.model.E).toBase 1 (0 : ((rnSc m).prod c.φ.model.E) 1) = 0 :=
    map_zero _
  set R' := (pc0 c q₀).isRetraction.baseRetraction (pc0 c q₀).relOpen with hR'
  have hzR : (0 : (pc0 c q₀).φ.model.E 1) ∈ (pc0 c q₀).φ.model.E.lvlSet R'.retract 1 := by
    rw [ScBanach.mem_lvlSet, (pc0 c q₀).base_retract, hz']; exact (pc0 c q₀).φ.mapsTo_model _ hyV'
  have hzs : (0 : (pc0 c q₀).φ.model.E 1) ∈ (pc0 c q₀).φ.model.E.smoothLvl 1 := by
    change (pc0 c q₀).φ.model.E.toBase 1 0 ∈ (pc0 c q₀).φ.model.E.smooth
    rw [map_zero]; exact (pc0 c q₀).φ.model.E.smooth.zero_mem
  -- (ii): `ker F'(0, y) + T^R = T₀(ℝᵐ × O)`
  have hsup : (pc0 c q₀).linKer (paramSection g hgFt.isScSmooth.1 t fun i => (htp i).1) 0 ⊔
      reducedTangentSpaceWith R' (prodPresentation (rnPres m) T) 0 =
        LinearMap.range (scDeriv R'.U R' 0 :
        (pc0 c q₀).φ.model.E 0 →ₗ[ℝ] (pc0 c q₀).φ.model.E 0) := by
    refine le_antisymm (sup_le ((pc0 c q₀).linKer_le _ 0) inf_le_left) fun v hv => ?_
    have hv2 : v.2 ∈ rangeS (scDeriv c.U (r c.R) 0) :=
      PullbackChartData.ofProd_mem_tangent c 0 q₀ h0U hv
    obtain ⟨u, a, hua, hwu⟩ := h.2 ⟨v.2, hv2⟩
    have hk : ((a, (u : c.φ.model.E 0)) : (Fin m → ℝ) × c.φ.model.E 0) ∈
        rangeS (scDeriv (pc0 c q₀).U (r (pc0 c q₀).R) 0) := ofProd_mem_rangeS c q₀ h0U u.2
    have hkK : ((a, (u : c.φ.model.E 0)) : (Fin m → ℝ) × c.φ.model.E 0) ∈
        (pc0 c q₀).linKer (paramSection g hgFt.isScSmooth.1 t fun i => (htp i).1) 0 := by
      refine ((pc0 c q₀).mem_linKer_iff _ 0 _).2 ⟨hk, ?_⟩
      rw [linAt_paramSection_zero hgF htp hc.1 h0O q₀ hk]
      exact hua
    let k : (pc0 c q₀).φ.model.E 0 :=
      ((a, (u : c.φ.model.E 0)) : (Fin m → ℝ) × c.φ.model.E 0)
    have hrest : v - k ∈ reducedTangentSpaceWith R' (prodPresentation (rnPres m) T) 0 := by
      refine ⟨Submodule.sub_mem _ hv hk, ?_⟩
      have hb0' : (pc0 c q₀).φ.model.E.toBase 1
          (0 : (pc0 c q₀).φ.model.E 1) = 0 := map_zero _
      rw [hb0']
      change v - k ∈ minimalSubspaceWith (prodPresentation (rnPres m) T)
        (0 : ((rnSc m).prod c.φ.model.E) 0)
      rw [hmin]
      exact ⟨Submodule.mem_top, hwu⟩
    have : v = k + (v - k) := by abel
    rw [this]
    exact Submodule.add_mem_sup hkK hrest
  -- good position of `(F, (0, y))`
  obtain ⟨B'', hB''T, hKB, hKBM⟩ := exists_compl_le_of_sup_eq le_rfl ((pc0 c q₀).linKer_le _ 0)
    le_rfl inf_le_left hsup
  have hR'T : R'.IsTameWith (prodPresentation (rnPres m) T) :=
    hc'T.2 _ _ (prodPresentation (rnPres m) T) hT'
  have hker := isInGoodPositionIn_of_scComplement_le_reduced (prodPresentation (rnPres m) T) hR'T
    hzR hzs hB''T hKB hKBM
  have hpt : (pc0 c q₀).φ (0, y) =
      ((ScBanach.prodScale (ScBanach.constScale (Fin m → ℝ)) c.φ.model.E.toScScale).toBase 1)
        0 := by
    rw [hc'0]; exact (map_zero _).symm
  have hker' : IsInGoodPositionIn (pc0 c q₀).φ.model.E
      (rangeS (scDeriv (pc0 c q₀).U
        (r (pc0 c q₀).R) 0))
      (partialQuadrantAtWith (prodPresentation (rnPres m) T)
        ((pc0 c q₀).φ (0, y)))
      ((LinearMap.ker (linAt (pc0 c q₀).U
        (pc0 c q₀).R
        ((pc0 c q₀).principal
          (paramSection g hgFt.isScSmooth.1 t fun i => (htp i).1)) 0 :
        ↥(rangeS (scDeriv (pc0 c q₀).U
          (r (pc0 c q₀).R) 0)) →ₗ[ℝ]
          (pc0 c q₀).F 0)).map
        (rangeS (scDeriv (pc0 c q₀).U
          (r (pc0 c q₀).R) 0)).subtype) := by
    rw [hpt]; exact hker
  have hFs : ((0 : Fin m → ℝ), y) ∈ ((rnPolyfold m).prod PX).smoothSet :=
    hFt.mem_smoothSet_of_isZeroAt hz0
  exact (StrongBundle.isGoodPositionGerm_of_linAt_surj hFt.isScSmooth
    (hFt.germ _ hFs) hz0 hc'B hyV' hz' (prodPresentation (rnPres m) T) hT' hsurj' hker').toTame
    hFt.isScSmooth
    (hFt.germTame _ hFs) hz0

end ParamGPGerm

/-! ### The index is locally constant along the zero set, germ reading -/

section IndexGerm

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle PX P}
  {f : X → Y}

open StrongRetr

/-- **The Fredholm index of the linearization is locally constant along the zero set, germ
reading** (phase 2; the germ form of `index_locally_constant_of_admitsBumpFunctions_wholeChart`; round-trip
item V3.98 (b), Theorem 3.6.8 (preprint 3.54) and the proof of Proposition 6.2.2 (preprint 6.2) along the solution set, without good
position or surjectivity at `x₀`): let `X` admit sc-smooth bump functions and `f` be an sc-Fredholm
section with tame germ data in the germ reading (`IsScFredholmSectionTame`), `f(x₀) = 0`.  Then
there are an open `V ∋ x₀` and `i ∈ ℤ` such that at every zero `y ∈ V` `f'(y)` is Fredholm of index
`i` in every strong bundle chart (`IsLinOfIndex`).  Proof as before: sc⁺-sections put the
parametrized section `F` of Theorem 3.1.21 (preprint 3.18) (germ reading) into good position at `(0, x₀)`
(`exists_sections_isParamGP_germ`, `isGoodPositionGermTame_paramSection_of_isParamGP`), its index
is constant along its solution set near `(0, x₀)` (`theorem_3_6_8_index_locally_constant`),
and at `(0, y)` it is `k + ind f'(y)` (`isLinOfIndex_of_paramSection_isLinOfIndex`). -/
theorem index_locally_constant_of_admitsBumpFunctions (hbump : PX.AdmitsBumpFunctions)
    (hf : B.IsScFredholmSectionTame f) {x₀ : X} (hx₀ : IsZeroAt P f x₀) :
    ∃ (V : Set X) (i : ℤ), IsOpen V ∧ x₀ ∈ V ∧ ∀ y ∈ V, IsZeroAt P f y → B.IsLinOfIndex f y i := by
  classical
  obtain ⟨N, hN⟩ := proposition_5_1_3_exists (B := B)
  have hfF := hf.toIsScFredholmSection
  have hxs : x₀ ∈ PX.smoothSet := hfF.mem_smoothSet_of_isZeroAt hx₀
  obtain ⟨-, c, hc, hxV, hφ0, -⟩ := hf.germTame x₀ hxs
  obtain ⟨n, Wq, T, hT⟩ := c.φ.model.isPartialQuadrant
  obtain ⟨k, s, hsp, -, -, hgp⟩ := exists_sections_isParamGP_germ hbump hN hf hx₀ hc hxV hφ0 T hT
    isOpen_univ (mem_univ _)
  have := MPolyfold.paracompactSpace_prod (rnPolyfold k) PX
  have := paracompactSpace_pullbackSpace (f := (Prod.snd : (Fin k → ℝ) × X → X))
    ((rnPolyfold k).prod PX) B
  have hFt := theorem_3_1_21_tame hf hsp
  set F := paramSection f hf.isScSmooth.1 s (fun i => (hsp i).1) with hFdef
  have hz0 : ∀ y, IsZeroAt P f y → IsZeroAt (pullbackProj P Prod.snd) F (0, y) := fun y hy => by
    rw [hFdef, isZeroAt_paramSection_iff]
    change IsZeroAt P (paramSlice f hf.isScSmooth.1 s (fun i => (hsp i).1) 0) y
    rw [paramSlice_zero]; exact hy
  have hgood := isGoodPositionGermTame_paramSection_of_isParamGP hf hsp hx₀ hc hxV hφ0 T hT hgp
  obtain ⟨Vx, d, hVo, hxVx, hall⟩ :=
    theorem_3_6_8_index_locally_constant hFt hgood (hz0 x₀ hx₀)
  refine ⟨Prod.mk (0 : Fin k → ℝ) ⁻¹' Vx, (d : ℤ) - k,
    hVo.preimage (continuous_const.prodMk continuous_id), hxVx, fun y hy hy0 => ?_⟩
  exact StrongBundle.isLinOfIndex_of_paramSection_isLinOfIndex hfF hsp hy0
    (hall (0, y) hy (hz0 y hy0)).isLinOfIndex

/-- **The index is locally constant along the zero set, sc form, germ reading** (phase 2; the germ
form of `theorem_3_6_8_index_locally_constant_general_wholeChart`; round-trip item V3.98 (b)): with the
hypotheses of `index_locally_constant_of_admitsBumpFunctions`, there are an open `V ∋ x₀` and
`i ∈ ℤ` such that at every zero `y ∈ V`, in **every** strong bundle chart `c` of `P` around `y`, at
the level-`1` point `z` over `φ(y)`, `Lin(z) : T_zO → K_z` is an sc-Fredholm operator, Fredholm of
index `i` on every level (`linAt_isScFredholm` and
`index_locally_constant_of_admitsBumpFunctions`). -/
theorem theorem_3_6_8_index_locally_constant_general (hbump : PX.AdmitsBumpFunctions)
    (hf : B.IsScFredholmSectionTame f) {x₀ : X} (hx₀ : IsZeroAt P f x₀) :
    ∃ (V : Set X) (i : ℤ), IsOpen V ∧ x₀ ∈ V ∧
      ∀ y ∈ V, IsZeroAt P f y → ∀ (c : StrongBundleChart PX P) (_ : B.IsChart c)
        (_ : y ∈ c.φ.source) (z : c.φ.model.E 1) (_ : c.φ.model.E.toBase 1 z = c.φ y)
        (hzU : c.φ.model.E.toBase 1 z ∈ c.U),
        ∃ (hD : IsScOperator (scDeriv c.U (c.principal f ∘ r c.R) z))
          (hT : c.φ.model.E.IsScSubspace (rangeS (scDeriv c.U (r c.R) z)))
          (hK : c.F.IsScSubspace (rangeS (ρCLM c.isRetraction hzU)))
          (hTK : ∀ x ∈ rangeS (scDeriv c.U (r c.R) z),
            hD.toScOperator 0 x ∈ rangeS (ρCLM c.isRetraction hzU)),
          (∀ x : (c.φ.model.E.ofSubspace hT) 0,
            ((hD.toScOperator.restrict hT hK hTK 0 x).1 : c.F 0) =
              linAt c.U c.R (c.principal f) z ⟨x.1, x.2⟩) ∧
          IsScFredholm (hD.toScOperator.restrict hT hK hTK) ∧
          ∀ m, ((hD.toScOperator.restrict hT hK hTK) m).IsFredholm ∧
            fredholmIndex ((hD.toScOperator.restrict hT hK hTK) m) = i := by
  obtain ⟨V, i, hVo, hxV, hall⟩ := index_locally_constant_of_admitsBumpFunctions hbump hf hx₀
  refine ⟨V, i, hVo, hxV, fun y hy hy0 c hc hyV z hz hzU => ?_⟩
  obtain ⟨hD, hT, hK, hTK, happ, hsc, hlvl⟩ :=
    StrongBundle.linAt_isScFredholm hf.toIsScFredholmSection hy0 hc hyV hz hzU
  have hmem : ∀ x : ↥(rangeS (scDeriv c.U (r c.R) z)),
      linAt c.U c.R (c.principal f) z x ∈ rangeS (ρCLM c.isRetraction hzU) := fun x => by
    have := hTK x x.2
    rwa [hD.toScOperator_zero] at this
  obtain ⟨hLF, hLind⟩ := hall y hy hy0 c hc hyV z hz hzU
    ((linAt c.U c.R (c.principal f) z).codRestrict _ hmem) fun _ => rfl
  obtain ⟨-, hind0⟩ := hD.toScOperator.isFredholm_restrict_zero hT hK hTK
    (L := (linAt c.U c.R (c.principal f) z).codRestrict _ hmem)
    (fun x => by rw [hD.toScOperator_zero]; rfl) hLF
  refine ⟨hD, hT, hK, hTK, happ, hsc, fun m => ⟨(hlvl m).1, ?_⟩⟩
  rw [(hlvl m).2.1, hind0, hLind]

end IndexGerm

end Polyfold
