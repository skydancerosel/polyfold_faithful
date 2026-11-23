import Polyfold.Chapter15.CanonicalLiftContinuityLocalKer

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part III, §15.4,
pp. 701–702 (**Theorem 15.4.1**), and Part I, §6.6, p. 275 (**Theorem 6.6.18**).

# The frames `o_{i,y}` read in a domain

## The text, paraphrased

(pp. 701–702) Near a point of `supp(Λ ∘ f)` the sheets are `Mᵢ = {f = sᵢ}` for the local
sc⁺-sections `sᵢ` of a local sc⁺-section structure, and `o_y` orients `ker (f − sᵢ)'(y)`.
(Theorem 6.6.18) The solution set of a section with onto linearizations is oriented by the
orientation of the section.

## What is formalized (namespace `Polyfold.SBLocalization`)

Let `W` be a domain (`StrongBundle.Dom`: an open subset of the base domain of a chart of the
atlas) inside the domain `O` of the local sc⁺-sections of a structure described by kernels.
Over `W` the local section `sᵢ` is an sc⁺-section of `P|W` (`KernelBranching.secD`), so
`f|W − sᵢ|W` is an sc-Fredholm section of `P|W`.  No sc⁺-section over all of the base enters.

* `StrongBundle.Dom.chart`, `StrongBundle.Dom.model`: a chart of `P|W` read as a chart of `P`,
  with the same model.
* `KernelBranching.frames_eq_pt`: the frames `o_{i,z}` read in any chart point with base domain
  in `O`.
* **`KernelBranching.mem_frames_iff_tangentOr_dom`**: at `z ∈ Mᵢ ∩ W` and in every strong
  bundle chart `c` of `P|W` at `z`: `z` is a zero of `f|W − sᵢ|W` with onto linearization, the
  chart vectors of `T_zMᵢ` lie in its kernel, which has dimension `dᵢ`, and a frame of `T_zMᵢ`
  is in `o_{i,z}` iff the wedge of its chart vectors spans Part I's tangent orientation of
  `f|W − sᵢ|W` for the orientation `o_z` read in `W` (`StrongBundle.Dom.toGlobal`).
-/

set_option maxSynthPendingDepth 3

open Set Function Topology Filter Module

noncomputable section

namespace Polyfold

universe u v

/-! ### A chart of the restriction to a domain as a chart of the bundle -/

namespace StrongBundle.Dom

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle PX P}
  (D : B.Dom)

/-- **A chart of `P|W` read as a chart of `P`** (the chart carried along the inclusion). -/
abbrev chart (c : StrongBundleChart (PX.restrictOpen D.isOpen)
    (pullbackProj P (Subtype.val : D.carrier → X))) : StrongBundleChart PX P :=
  (B.restrictIso D.isOpen).symm.transportChart c (subset_univ _)

theorem isChart_chart {c : StrongBundleChart (PX.restrictOpen D.isOpen)
    (pullbackProj P (Subtype.val : D.carrier → X))} (hc : D.bundle.IsChart c) :
    B.IsChart (D.chart c) :=
  (B.restrictIso D.isOpen).symm.isChart_transportChart c (subset_univ _) hc

theorem chart_source_subset (c : StrongBundleChart (PX.restrictOpen D.isOpen)
    (pullbackProj P (Subtype.val : D.carrier → X))) : (D.chart c).φ.source ⊆ D.carrier :=
  fun _ hy => hy.1

theorem mem_chart_source {c : StrongBundleChart (PX.restrictOpen D.isOpen)
    (pullbackProj P (Subtype.val : D.carrier → X))} {z : X} (hz : z ∈ D.carrier)
    (hzc : (⟨z, hz⟩ : D.carrier) ∈ c.φ.source) : z ∈ (D.chart c).φ.source := by
  refine ⟨hz, ?_⟩
  change (B.restrictIso D.isOpen).g z ∈ c.φ.source
  rw [B.restrictIso_g_of_mem D.isOpen hz]
  exact hzc

theorem mk_mem_of_mem_chart_source {c : StrongBundleChart (PX.restrictOpen D.isOpen)
    (pullbackProj P (Subtype.val : D.carrier → X))} {z : X}
    (hz : z ∈ (D.chart c).φ.source) : (⟨z, hz.1⟩ : D.carrier) ∈ c.φ.source := by
  have h : (B.restrictIso D.isOpen).g z ∈ c.φ.source := hz.2
  rwa [B.restrictIso_g_of_mem D.isOpen hz.1] at h

/-- **The model of a chart of `P|W` is the model of the chart read in `P`.** -/
def model (c : StrongBundleChart (PX.restrictOpen D.isOpen)
    (pullbackProj P (Subtype.val : D.carrier → X))) :
    c.φ.model.E 0 ≃L[ℝ] (D.chart c).φ.model.E 0 :=
  ContinuousLinearEquiv.refl ℝ (c.φ.model.E 0)

end StrongBundle.Dom

namespace SBLocalization

open StrongBundle StrongRetr MPolyfold Linearization15 EpGroupoid

variable {A : SEP.{u}} {f : A.Obj → A.W} {Λ : A.W → ℚ≥0} {x : A.Obj}

namespace KernelBranching

variable (K : KernelBranching A f Λ x)

/-! ### The frames in a chart point -/

theorem surj_pt (hf : A.B.IsScFredholmSection f) {i : K.ι} {z : A.Obj} (hz : z ∈ K.M i)
    (p : ChartPoint A.B z) (hsub : p.c.φ.source ⊆ K.O) :
    Surjective (subOp hf.isScSmooth (K.isScPlus i) p hsub (K.eq_of_mem hz)) :=
  (surjective_subOp_iff hf.isScSmooth (K.isScPlus i) p hsub (K.eq_of_mem hz)).2
    (K.onto i z hz p.c p.isChart hsub p.mem_source p.z p.toBase_z)

theorem ker_eq_pt {i : K.ι} {z : A.Obj} (hz : z ∈ K.M i) (p : ChartPoint A.B z)
    (hsub : p.c.φ.source ⊆ K.O) :
    chartVec p.c.isChart '' A.X.PObj.submanifoldTangent (K.M i) z =
      kerSet p.c f (K.s i) p.z :=
  K.tangent_eq i z hz p.c p.isChart hsub p.mem_source p.z p.toBase_z

theorem finrank_ker_pt (hf : A.B.IsScFredholmSection f) {i : K.ι} {z : A.Obj}
    (hz : z ∈ K.M i) (p : ChartPoint A.B z) (hsub : p.c.φ.source ⊆ K.O) :
    finrank ℝ ↥((LinearMap.ker ((subOp hf.isScSmooth (K.isScPlus i) p hsub (K.eq_of_mem hz) :
        ↥p.T →L[ℝ] ↥p.K) : ↥p.T →ₗ[ℝ] ↥p.K)).map
      (p.T.subtypeL : ↥p.T →ₗ[ℝ] p.c.φ.model.E 0)) = K.dim i := by
  obtain ⟨N', hN', -, hn⟩ := exists_submodule_chartVec_image p.c.isChart
    (K.isSubmanifoldOfDim i).1 ((K.isSubmanifoldOfDim i).2 z hz) p.mem_source
  have h := (kerSet_eq_coe_map_ker hf.isScSmooth (K.isScPlus i) p hsub
    (K.eq_of_mem hz)).symm.trans ((K.ker_eq_pt hz p hsub).symm.trans hN'.symm)
  rw [SetLike.coe_injective h]
  exact hn

/-- **The frames `o_{i,z}` read in any chart point** with base domain in `O`: the frames of
`T_zMᵢ` whose chart vectors are a basis of `ker (f − sᵢ)'(z)` positive for the orientation
induced by `o_z`, read in the chart point. -/
theorem frames_eq_pt (hf : A.B.IsScFredholmSection f) (hsec : A.B.HasScPlusSectionsThrough)
    (o : ∀ y (hy : y ∈ A.X.PObj.smoothSet), Orx f hf y hy) {i : K.ι} {z : A.Obj}
    (hz : z ∈ K.M i) (p : ChartPoint A.B z) (hsub : p.c.φ.source ⊆ K.O) :
    K.frames hf hsec o i z =
      kerFrames hf K.isOpen_O (K.isScPlus i) p hsub (K.eq_of_mem hz) (K.smooth i z hz) hsec
        (K.surj_pt hf hz p hsub)
        ((orxPt A.B z (K.smooth i z hz)).orTransfer p hf (K.smooth i z hz)
          (o z (K.smooth i z hz)))
        (A.X.PObj.submanifoldTangent (K.M i) z) (K.finrank_ker_pt hf hz p hsub) := by
  rw [K.frames_eq hf hsec o hz]
  have h := kerFrames_orTransfer hf K.isOpen_O (K.isScPlus i)
    (K.pt (K.mem_O hz) (K.smooth i z hz)) p (K.chart_subset z) hsub (K.eq_of_mem hz)
    (K.smooth i z hz) hsec (K.surj hf hz) (K.surj_pt hf hz p hsub)
    (toChartOr hf (K.smooth i z hz) (K.chart z) (K.isChart_chart z) (K.mem_chart (K.mem_O hz))
      (o z (K.smooth i z hz))) (fun α hα => hα.1) (K.ker_eq hz) (K.finrank_ker hf hz)
    (K.finrank_ker_pt hf hz p hsub)
  have e : (K.pt (K.mem_O hz) (K.smooth i z hz)).orTransfer p hf (K.smooth i z hz)
      (toChartOr hf (K.smooth i z hz) (K.chart z) (K.isChart_chart z)
        (K.mem_chart (K.mem_O hz)) (o z (K.smooth i z hz))) =
      (orxPt A.B z (K.smooth i z hz)).orTransfer p hf (K.smooth i z hz)
        (o z (K.smooth i z hz)) :=
    DFunLike.congr_fun (ChartPoint.orTransfer_trans (orxPt A.B z (K.smooth i z hz))
      (K.pt (K.mem_O hz) (K.smooth i z hz)) p hf (K.smooth i z hz)) (o z (K.smooth i z hz))
  rw [← e]
  exact h.symm

/-! ### The local section over a domain -/

variable (D : A.B.Dom) (i : K.ι)

/-- **The local sc⁺-section `sᵢ` over a domain `W`**, a section of `P|W`. -/
def secD : D.carrier → pullbackSpace A.P (Subtype.val : D.carrier → A.Obj) :=
  D.sec (extendZero K.O (K.s i)) (isSection_extendZero K.O (K.s i))

variable {D} in
/-- Over a domain inside `O`, `sᵢ` is an sc⁺-section of `P|W`. -/
theorem isScPlusSection_secD (hDO : D.carrier ⊆ K.O) : D.bundle.IsScPlusSection (K.secD D i) :=
  IsScPlusSectionOn.restrictOpen D.isOpen (((K.isScPlus i).extendZero).mono D.isOpen hDO)
    (isSection_extendZero K.O (K.s i))

/-- **The sc⁺-section `−sᵢ|W`.** -/
abbrev negSecD : D.carrier → pullbackSpace A.P (Subtype.val : D.carrier → A.Obj) :=
  sectionSmul (pullbackProj A.P (Subtype.val : D.carrier → A.Obj)) (fun _ => (-1 : ℝ))
    (K.secD D i)

variable {D} in
theorem isScPlusSection_negSecD (hDO : D.carrier ⊆ K.O) :
    D.bundle.IsScPlusSection (K.negSecD D i) :=
  (K.isScPlusSection_secD i hDO).smul_left (isScSmoothMap_real_const (-1))

/-- **The section `f|W − sᵢ|W` of `P|W`.** -/
abbrev subD (hfs : IsSection A.P f) :
    D.carrier → pullbackSpace A.P (Subtype.val : D.carrier → A.Obj) :=
  sectionAdd (pullbackProj A.P (Subtype.val : D.carrier → A.Obj)) (D.sec f hfs) (K.negSecD D i)

/-! ### The frames and the tangent orientation of `f|W − sᵢ|W` -/

/-- **The frames `o_{i,z}` in terms of Part I's tangent orientation of `f|W − sᵢ|W`**, for a
domain `W ⊆ O`, read in any strong bundle chart `c` of `P|W` at `z ∈ Mᵢ ∩ W`: `z` is a zero of
`f|W − sᵢ|W` with onto linearization, the chart vectors of `T_zMᵢ` lie in
`ker (f|W − sᵢ|W)'(z)`, of dimension `dᵢ`, and a frame `v` of `T_zMᵢ` is in `o_{i,z}` iff the
wedge of its chart vectors spans the tangent orientation of `f|W − sᵢ|W` at `z` for the
orientation inherited from `o_z` read in `W`. -/
theorem mem_frames_iff_tangentOr_dom (hft : A.B.IsScFredholmSectionTame f)
    (hsec : A.B.HasScPlusSectionsThrough)
    (o : ∀ y (hy : y ∈ A.X.PObj.smoothSet), Orx f hft.toIsScFredholmSection y hy)
    (hDO : D.carrier ⊆ K.O) {i : K.ι} {z : A.Obj} (hz : z ∈ K.M i) (hzD : z ∈ D.carrier)
    {c : StrongBundleChart (A.X.PObj.restrictOpen D.isOpen)
      (pullbackProj A.P (Subtype.val : D.carrier → A.Obj))} (hc : D.bundle.IsChart c)
    (hzc : (⟨z, hzD⟩ : D.carrier) ∈ c.φ.source) :
    ∃ (hZ : IsZeroAt (pullbackProj A.P (Subtype.val : D.carrier → A.Obj))
        (K.subD D i hft.isScSmooth.1) ⟨z, hzD⟩)
      (hLs : D.bundle.IsLinSurjAt (K.subD D i hft.isScSmooth.1) ⟨z, hzD⟩)
      (hnk : finrank ℝ (c.linKer (K.subD D i hft.isScSmooth.1)
        (chartPtOf c hc hzc (StrongBundle.Dom.mem_smoothSet hzD (K.smooth i z hz))).z) =
          K.dim i),
      (∀ α ∈ A.X.PObj.submanifoldTangent (K.M i) z,
        (D.model c).symm (chartVec (D.chart c).isChart α) ∈
          c.linKer (K.subD D i hft.isScSmooth.1)
            (chartPtOf c hc hzc (StrongBundle.Dom.mem_smoothSet hzD (K.smooth i z hz))).z) ∧
      ∀ v : Fin (K.dim i) → A.X.PObj.TangentSpace,
        v ∈ K.frames hft.toIsScFredholmSection hsec o i z ↔
          (∀ j, v j ∈ A.X.PObj.submanifoldTangent (K.M i) z) ∧
          ∃ (hmem : ∀ j, (D.model c).symm (chartVec (D.chart c).isChart (v j)) ∈
              c.linKer (K.subD D i hft.isScSmooth.1)
                (chartPtOf c hc hzc
                  (StrongBundle.Dom.mem_smoothSet hzD (K.smooth i z hz))).z)
            (hne : wedge (fun j =>
              (⟨(D.model c).symm (chartVec (D.chart c).isChart (v j)), hmem j⟩ :
                c.linKer (K.subD D i hft.isScSmooth.1)
                  (chartPtOf c hc hzc
                    (StrongBundle.Dom.mem_smoothSet hzD (K.smooth i z hz))).z)) hnk.symm ≠ 0),
            (chartPtOf c hc hzc
                (StrongBundle.Dom.mem_smoothSet hzD (K.smooth i z hz))).tangentOr
                (theorem_3_1_18_preprint (D.isFredholm hft).toIsScFredholmSection
                  (K.isScPlusSection_negSecD i hDO)) hZ hLs
                ((chartPtOf c hc hzc
                    (StrongBundle.Dom.mem_smoothSet hzD (K.smooth i z hz))).orSectionAdd
                  (D.isFredholm hft).toIsScFredholmSection (K.isScPlusSection_negSecD i hDO)
                  (toChartOr (D.isFredholm hft).toIsScFredholmSection
                    (StrongBundle.Dom.mem_smoothSet hzD (K.smooth i z hz)) c hc hzc
                    (D.toGlobal hft hsec z hzD (K.smooth i z hz) (o z (K.smooth i z hz))))) =
              rayOfNeZero ℝ _ hne := by
  classical
  have hf := hft.toIsScFredholmSection
  have hfsec : IsSection A.P f := hft.isScSmooth.1
  have hzs := K.smooth i z hz
  have hzsD : (⟨z, hzD⟩ : D.carrier) ∈ (A.X.PObj.restrictOpen D.isOpen).smoothSet :=
    StrongBundle.Dom.mem_smoothSet hzD hzs
  have hfs : f z = K.s i z := K.eq_of_mem hz
  have hfD := (D.isFredholm hft).toIsScFredholmSection
  have htD := K.isScPlusSection_negSecD i hDO
  have hgD := theorem_3_1_18_preprint hfD htD
  let L := (A.B.restrictIso D.isOpen).symm
  have hg : L.ϕ z = ⟨z, hzD⟩ := A.B.restrictIso_g_of_mem D.isOpen hzD
  let q : ChartPoint D.bundle (⟨z, hzD⟩ : D.carrier) := chartPtOf c hc hzc hzsD
  let pA : ChartPoint A.B z := L.mpullPt q (subset_univ _) hzD hg
  have hsub : pA.c.φ.source ⊆ K.O := fun y hy => hDO hy.1
  -- the sections of `P` and of `P|W`
  have hfL : EqOn f (L.Ψ ∘ D.sec f hfsec ∘ L.ϕ) D.carrier :=
    (A.B.restrictIso D.isOpen).eqOn_symm hfsec
      (A.B.restrictSection_eqOn_restrictIso D.isOpen hfsec)
  have hsL : EqOn (extendZero K.O (K.s i)) (L.Ψ ∘ K.secD D i ∘ L.ϕ) D.carrier :=
    (A.B.restrictIso D.isOpen).eqOn_symm (isSection_extendZero K.O (K.s i))
      (A.B.restrictSection_eqOn_restrictIso D.isOpen (isSection_extendZero K.O (K.s i)))
  have hext : extendZero K.O (K.s i) z = K.s i z :=
    (extendZero_eqOn (K.isScPlus i).1 (K.mem_O hz)).symm
  have hZ : IsZeroAt (pullbackProj A.P (Subtype.val : D.carrier → A.Obj))
      (K.subD D i hfsec) ⟨z, hzD⟩ :=
    (isZeroAt_sectionAdd_neg_iff (isSection_restrictSection hfsec)
      (isSection_restrictSection (isSection_extendZero K.O (K.s i))) _).2
      (Subtype.ext (Prod.ext rfl (hfs.trans hext.symm)))
  -- the two operators
  let S : ↥q.T →L[ℝ] ↥q.K := q.linZero hgD hZ
  let S' : ↥pA.T →L[ℝ] ↥pA.K := subOp hf.isScSmooth (K.isScPlus i) pA hsub hfs
  let AT : ↥q.T ≃L[ℝ] ↥pA.T := L.mcastT q (subset_univ _) hzD hg
  let AK : ↥q.K ≃L[ℝ] ↥pA.K := L.mcastK q (subset_univ _) hzD hg
  have hconj : ∀ v, S' (AT v) = AK (S v) := fun v => by
    apply Subtype.ext
    have hA : (S' (AT v)).1 = scDeriv c.U
        ((fun y => pA.c.principal f y - pA.c.principal (K.s i) y) ∘ r c.R) q.z v.1 := rfl
    have hB : (AK (S v)).1 = scDeriv c.U
        (c.principal (K.subD D i hfsec) ∘ r c.R) q.z v.1 := rfl
    refine hA.trans (Eq.trans ?_ hB.symm)
    refine congrArg (fun M : c.φ.model.E 0 →L[ℝ] c.F 0 => M v.1) ?_
    have h1A : IsSc1 c.U ((fun y => pA.c.principal f y - pA.c.principal (K.s i) y) ∘ r c.R) :=
      isSc1_sub_comp_r hf.isScSmooth (K.isScPlus i) pA.isChart hsub
    have h1D : IsSc1 c.U (c.principal (K.subD D i hfsec) ∘ r c.R) :=
      hgD.isScSmooth.isSc1_principal_comp_r hc
    refine scDeriv_eq_of_eqOn_relOpen c.relOpen h1A h1D subset_rfl subset_rfl (fun u hu => ?_)
      q.mem_U
    have hO : r c.R u ∈ c.φ.model.O := c.r_mem_O hu
    have hO' : r c.R u ∈ pA.c.φ.model.O := pA.c.r_mem_O hu
    have e1 : pA.c.principal f (r c.R u) = c.principal (D.sec f hfsec) (r c.R u) :=
      L.principal_transportChart c (subset_univ _) hfL (isSection_restrictSection hfsec) hO
    have e2 : pA.c.principal (extendZero K.O (K.s i)) (r c.R u) =
        c.principal (K.secD D i) (r c.R u) :=
      L.principal_transportChart c (subset_univ _) hsL
        (isSection_restrictSection (isSection_extendZero K.O (K.s i))) hO
    have e3 : pA.c.principal (K.s i) (r c.R u) =
        pA.c.principal (extendZero K.O (K.s i)) (r c.R u) :=
      congrArg (fun w : A.W => (pA.c w).2)
        (extendZero_eqOn (K.isScPlus i).1 (hsub (pA.c.φ.symm_mapsTo hO')))
    have e4 : c.principal (K.subD D i hfsec) (r c.R u) =
        c.principal (D.sec f hfsec) (r c.R u) + c.principal (K.negSecD D i) (r c.R u) :=
      c.principal_sectionAdd (isSection_restrictSection hfsec)
        (isSection_restrictSection (isSection_extendZero K.O (K.s i))).sectionSmul hO
    have e5 : c.principal (K.negSecD D i) (r c.R u) =
        (-1 : ℝ) • c.principal (K.secD D i) (r c.R u) :=
      principal_sectionSmul_const c
        (isSection_restrictSection (isSection_extendZero K.O (K.s i))) (-1) hO
    refine (congrArg₂ (fun a b : c.F 0 => a - b) e1 (e3.trans e2)).trans ?_
    change _ = c.principal (K.subD D i hfsec) (r c.R u)
    rw [e4, e5, neg_one_smul, sub_eq_add_neg]
  have hsurj' : Surjective S' := K.surj_pt hf hz pA hsub
  have hsurj : Surjective S := fun k => by
    obtain ⟨w, hw⟩ := hsurj' (AK k)
    exact ⟨AT.symm w, AK.injective (by rw [← hconj, AT.apply_symm_apply, hw])⟩
  have hLs : D.bundle.IsLinSurjAt (K.subD D i hfsec) ⟨z, hzD⟩ := by
    refine ⟨q.c, q.isChart, q.mem_source, q.z, q.toBase_z, fun k hk => ?_⟩
    have hkK : k ∈ q.K := by
      refine (mem_rangeS_ρCLM_iff q.c.isRetraction q.mem_O q.mem_U).2 ?_
      rwa [q.toBase_z]
    obtain ⟨v, hv⟩ := hsurj ⟨k, hkK⟩
    exact ⟨v, congrArg Subtype.val hv⟩
  have hSmem : S ∈ q.linSet (D.sec f hfsec) := q.linZero_mem_linSet_of_sectionAdd hfD htD hZ
  have hS'mem : S' ∈ pA.linSet f :=
    subOp_mem_linSet hf K.isOpen_O (K.isScPlus i) pA hsub hfs hzs hsec
  have hlin : pA.linSet f = q.linSet (D.sec f hfsec) :=
    StrongBundle.LocalIso.linSet_mpullPt hf hfD hfL hsec D.hasSections hzs hzsD
  have hn₀ := K.finrank_ker_pt hf hz pA hsub
  have hN := q.map_ker_linZero hgD hZ
  let κ := conjKerEquivOfMap AT AK hconj q.T.subtypeL Subtype.val_injective hN pA.T.subtypeL
    Subtype.val_injective rfl
  have hκ := ChartPoint.coe_conjKerEquivOfMap_eq q pA AT AK (D.model c) (fun _ => rfl) hconj hN
    rfl
  have hnk : finrank ℝ (c.linKer (K.subD D i hfsec) q.z) = K.dim i := κ.finrank_eq.trans hn₀
  -- the orientation
  let oq := toChartOr hfD hzsD c hc hzc (D.toGlobal hft hsec z hzD hzs (o z hzs))
  have hor : (orxPt A.B z hzs).orTransfer pA hf hzs (o z hzs) =
      oq.conj (hC' := pA.isFredholm_of_mem_linSet hf) AT AK
        (StrongBundle.LocalIso.mcastT_mem hlin) := by
    have h1 := L.orTransfer_mpullPt_orxViaAt hf hfD hfL hsec D.hasSections hzD hzs hg q
      (subset_univ _) (D.toGlobal hft hsec z hzD hzs (o z hzs))
    have h2 : L.orxViaAt hf hfD hfL hsec D.hasSections hzD hzs hg
        (D.toGlobal hft hsec z hzD hzs (o z hzs)) = o z hzs := by
      have h3 := (A.B.restrictIso D.isOpen).orxViaAt_symm hfD hf
        (A.B.restrictSection_eqOn_restrictIso D.isOpen hfsec) hfL D.hasSections hsec
        (a := (⟨z, hzD⟩ : D.carrier)) (mem_univ _) hzsD rfl hg
      exact (DFunLike.congr_fun h3 _).trans (Equiv.symm_apply_apply _ _)
    exact (congrArg ((orxPt A.B z hzs).orTransfer pA hf hzs) h2).symm.trans h1
  refine ⟨hZ, hLs, hnk, fun α hα => ?_, fun v => ?_⟩
  · have h1 : chartVec pA.c.isChart α ∈ (LinearMap.ker ((S' : ↥pA.T →L[ℝ] ↥pA.K) :
        ↥pA.T →ₗ[ℝ] ↥pA.K)).map (pA.T.subtypeL : ↥pA.T →ₗ[ℝ] pA.c.φ.model.E 0) := by
      rw [← SetLike.mem_coe, ← kerSet_eq_coe_map_ker hf.isScSmooth (K.isScPlus i) pA hsub hfs,
        ← K.ker_eq_pt hz pA hsub]
      exact mem_image_of_mem _ hα
    have h2 := hκ (κ.symm ⟨_, h1⟩)
    rw [κ.apply_symm_apply] at h2
    have h3 : (D.model c).symm (chartVec pA.c.isChart α) = (κ.symm ⟨_, h1⟩).1 :=
      (D.model c).symm_apply_eq.2 h2
    exact (congrArg (· ∈ c.linKer (K.subD D i hfsec) q.z) h3).mpr (κ.symm ⟨_, h1⟩).2
  · have hfr : K.frames hf hsec o i z = kerFrames hf K.isOpen_O (K.isScPlus i) pA hsub hfs hzs
        hsec hsurj' (oq.conj (hC' := pA.isFredholm_of_mem_linSet hf) AT AK
          (StrongBundle.LocalIso.mcastT_mem hlin))
        (A.X.PObj.submanifoldTangent (K.M i) z) hn₀ :=
      (K.frames_eq_pt hf hsec o hz pA hsub).trans (congrArg (fun o' => kerFrames hf K.isOpen_O
        (K.isScPlus i) pA hsub hfs hzs hsec hsurj' o' (A.X.PObj.submanifoldTangent (K.M i) z)
        hn₀) hor)
    have e1 : q.tangentOr hgD hZ hLs (q.orSectionAdd hfD htD oq) =
        q.orKer oq hSmem (q.linZero_surjective hgD hZ hLs) hN :=
      q.tangentOr_orSectionAdd_eq_orKer hfD htD hZ hLs oq
    have key : ∀ r : Module.Ray ℝ (maxPow (c.linKer (K.subD D i hfsec) q.z)),
        r = q.orKer oq hSmem (q.linZero_surjective hgD hZ hLs) hN →
        ((∃ (hm : ∀ j, (D.model c).symm (chartVec pA.c.isChart (v j)) ∈
              c.linKer (K.subD D i hfsec) q.z)
            (hne : wedge (fun j => (⟨(D.model c).symm (chartVec pA.c.isChart (v j)), hm j⟩ :
              c.linKer (K.subD D i hfsec) q.z)) hnk.symm ≠ 0),
            q.orKer oq hSmem (q.linZero_surjective hgD hZ hLs) hN = rayOfNeZero ℝ _ hne) ↔
          ∃ (hm : ∀ j, (D.model c).symm (chartVec pA.c.isChart (v j)) ∈
              c.linKer (K.subD D i hfsec) q.z)
            (hne : wedge (fun j => (⟨(D.model c).symm (chartVec pA.c.isChart (v j)), hm j⟩ :
              c.linKer (K.subD D i hfsec) q.z)) hnk.symm ≠ 0),
            r = rayOfNeZero ℝ _ hne) := by
      rintro _ rfl
      exact Iff.rfl
    refine (Set.ext_iff.1 hfr v).trans ((mem_kerFrames_iff hf K.isOpen_O (K.isScPlus i) pA hsub
      hfs hzs hsec hsurj' _ _ hn₀ rfl hS'mem hsurj' rfl hn₀ v).trans
      (and_congr_right fun _ => ?_))
    exact (q.exists_ray_orKer_conj_iff pA hfD hf AT AK (D.model c) (D.model c).injective
      (fun _ => rfl) (StrongBundle.LocalIso.mcastT_mem hlin) oq hSmem hS'mem hconj
      (q.linZero_surjective hgD hZ hLs) hsurj' hN rfl hnk.symm hn₀.symm
      (fun j => (D.model c).symm (chartVec pA.c.isChart (v j)))
      (fun j => chartVec pA.c.isChart (v j))
      (fun j => ((D.model c).apply_symm_apply _).symm)).trans (key _ e1)

end KernelBranching

end SBLocalization

end Polyfold
