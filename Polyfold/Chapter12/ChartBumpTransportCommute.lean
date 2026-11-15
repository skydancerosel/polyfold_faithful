import Polyfold.Chapter12.ChartTransportCommute

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Chapter 12, §12.5,
p. 594: the last sentence of **Theorem 12.5.3**, with Part I, §6.6, **Theorem 6.6.11** (p. 272)
and the proof of Theorem 6.6.13 (pp. 273–274).

# The transport commutes with an isomorphism from a bundle with a chart over its base

## The text, paraphrased

The orientations of the linearizations of an sc-Fredholm section are propagated along sc-smooth
paths (Theorem 6.6.11), and this propagation is compatible with local strong bundle
isomorphisms (the last sentence of Theorem 12.5.3).  The linearizations are those of `f − s`
for sc⁺-sections `s`, which may be defined near a point only or on all of the base.

## What is formalized

`P : Y → X` is a strong bundle with a chart of the atlas over the whole base, `P' : Y' → X'` a
strong bundle over a tame M-polyfold with sc-smooth bump functions, `f`, `f'` sc-Fredholm
sections with tame germ data, `L : Y → Y'|U'` a local strong bundle isomorphism over
`ϕ : X → U'` defined on all of `X` with `U'` inside the base domain of a chart of the atlas of
`Y'`, and `f = Ψ ∘ f' ∘ ϕ`.  The transport of `f` is `orLocalTransportOfChart` (made with the
sc⁺-sections written in the chart over `X`), that of `f'` is `orLocalTransport` (made with
sc-smooth bump functions).  This is the situation of the restriction of a bundle to an open
subset of a chart domain and its inclusion.

* `LocalIso.orxVia_comm_local_chart_bump`: every smooth `a₀` has an open neighbourhood `V`
  such that for sc-smooth paths `γ` in `V` the transport of `f` along `γ` after `orxVia` is
  `orxVia` after the transport of `f'` along `ϕ ∘ γ`.
* `LocalIso.orxVia_comm_chart_bump`: the same along every sc-smooth path.
-/

set_option maxSynthPendingDepth 3

open Set Function Topology Filter

noncomputable section

namespace Polyfold

open StrongRetr

universe u v u' v'

section Comm

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle PX P}
  {X' : Type u'} [TopologicalSpace X'] [T2Space X'] [ParacompactSpace X'] {PX' : MPolyfold X'}
  {Y' : Type v'} [TopologicalSpace Y'] [T2Space Y'] [ParacompactSpace Y'] {P' : Y' → X'}
  [∀ x, AddCommGroup (P' ⁻¹' {x})] [∀ x, Module ℝ (P' ⁻¹' {x})] {B' : StrongBundle PX' P'}
  {f : X → Y} {f' : X' → Y'}

namespace StrongBundle.LocalIso

variable {U' : Set X'} (L : LocalIso B B' univ U')

variable [∀ n : ℕ, ParacompactSpace ((Fin n → ℝ) × X)]
  [∀ n : ℕ, ParacompactSpace ((Fin n → ℝ) × X')]
  [∀ n : ℕ, ParacompactSpace (pullbackSpace P (Prod.snd : (Fin n → ℝ) × X → X))]
  [∀ n : ℕ, ParacompactSpace (pullbackSpace P' (Prod.snd : (Fin n → ℝ) × X' → X'))]
  [∀ k n : ℕ, ParacompactSpace ((Fin k → ℝ) × ((Fin n → ℝ) × X))]
  [∀ k n : ℕ, ParacompactSpace (pullbackSpace (pullbackProj P (Prod.snd : (Fin n → ℝ) × X → X))
    (Prod.snd : (Fin k → ℝ) × ((Fin n → ℝ) × X) → (Fin n → ℝ) × X))]
  [∀ k n : ℕ, ParacompactSpace ((Fin k → ℝ) × ((Fin n → ℝ) × X'))]
  [∀ k n : ℕ, ParacompactSpace (pullbackSpace
    (pullbackProj P' (Prod.snd : (Fin n → ℝ) × X' → X'))
    (Prod.snd : (Fin k → ℝ) × ((Fin n → ℝ) × X') → (Fin n → ℝ) × X'))]

variable (hX : PX.IsTame) (hch : ∃ c ∈ B.atlas.charts, c.φ.source = univ)
  (hf : B.IsScFredholmSectionTame f) (hsec : B.HasScPlusSectionsThrough) (hX' : PX'.IsTame)
  (hbump' : PX'.AdmitsBumpFunctions) (hcg : ∃ cg ∈ B'.atlas.charts, U' ⊆ cg.φ.source)
  (hf' : B'.IsScFredholmSectionTame f')
  (hsec' : B'.HasScPlusSectionsThrough) (hfL : EqOn f (L.Ψ ∘ f' ∘ L.ϕ) univ)

include hcg in
/-- **The transport commutes with `L` on short paths; a chart over the whole base of `Y`, bump
functions on `X'`** (the local half of the last sentence of Theorem 12.5.3, p. 594): every
smooth `a₀` has an open neighbourhood `V` such that for every sc-smooth path `γ` with
`γ([0, 1]) ⊆ V`, `orxVia` followed by the transport of `f` along `γ` is the transport of `f'`
along `ϕ ∘ γ` followed by `orxVia`.  The sc⁺-sections of a push-forward of `f'` are carried to
`X` in the transported chart of a chart of `Y'` whose base domain contains `U'`, restricted to
`U'`; its base domain is `X`, so that no cut-off is needed. -/
theorem orxVia_comm_local_chart_bump {a₀ : X} (has₀ : a₀ ∈ PX.smoothSet) :
    ∃ V : Set X, IsOpen V ∧ a₀ ∈ V ∧ ∀ (γ : (Fin 1 → ℝ) → X)
      (hγ : (rnPolyfold 1).IsScSmoothMap PX γ),
      (∀ t ∈ Icc (0 : ℝ) 1, γ (pt1 t) ∈ V) → ∀ {x₀ x₁ : X} (h₀ : γ (pt1 0) = x₀)
        (h₁ : γ (pt1 1) = x₁) (hs₀ : x₀ ∈ PX.smoothSet) (hs₁ : x₁ ∈ PX.smoothSet),
        (L.orxVia hf.toIsScFredholmSection hf'.toIsScFredholmSection hfL hsec hsec'
          (mem_univ x₀) hs₀).trans
          ((orLocalTransportOfChart hX hch hf hsec).transport γ hγ h₀ h₁ hs₀ hs₁) =
        ((orLocalTransport hX' hbump' hf' hsec').transport (fun q => L.ϕ (γ q))
          (L.isScSmoothMap_comp_or hγ fun _ => mem_univ _) (congrArg L.ϕ h₀) (congrArg L.ϕ h₁)
          ((L.mem_smoothSet_iff (mem_univ x₀)).1 hs₀)
          ((L.mem_smoothSet_iff (mem_univ x₁)).1 hs₁)).trans
          (L.orxVia hf.toIsScFredholmSection hf'.toIsScFredholmSection hfL hsec hsec'
            (mem_univ x₁) hs₁) := by
  obtain ⟨c', hc', V', hV'o, hxV', hLP'⟩ :=
    theorem_6_6_11 hX' hbump' hf' ((L.mem_smoothSet_iff (mem_univ a₀)).1 has₀)
  obtain ⟨cB, hcB, VB, hVBo, haVB, hLP⟩ := theorem_6_6_11_of_chart hX hch hf has₀
  obtain ⟨cg, hcgA, hcgs⟩ := hcg
  have hcg : B'.IsChart cg := B'.isChart_of_mem hcgA
  refine ⟨(univ ∩ L.ϕ ⁻¹' V') ∩ VB,
    (L.base.isScSmoothOn.continuousOn.isOpen_inter_preimage isOpen_univ hV'o).inter hVBo,
    ⟨⟨mem_univ _, hxV'⟩, haVB⟩, ?_⟩
  intro γ hγ hγV x₀ x₁ h₀ h₁ hs₀ hs₁
  subst h₀ h₁
  have hγV' := forall_mem_of_forall_pt1_mem hγV
  have hγc : Continuous γ := continuousOn_univ.1 hγ.continuousOn
  have hγU : ∀ q, γ q ∈ (univ : Set X) := fun _ => mem_univ _
  have hϕγ := L.isScSmoothMap_comp_or hγ hγU
  have hs₀' := (L.mem_smoothSet_iff (mem_univ (γ (pt1 0)))).1 hs₀
  have hs₁' := (L.mem_smoothSet_iff (mem_univ (γ (pt1 1)))).1 hs₁
  have hc₀ : B'.IsChart (cg.restrictInter L.isOpen_U') := hcg.restrictInter L.isOpen_U'
  have hsub₀ : (cg.restrictInter L.isOpen_U').φ.source ⊆ U' := fun _ hy => hy.2
  have hW : IsOpen (univ : Set X') := isOpen_univ
  -- the transported chart has base domain `X`
  have hT : ∀ x : X, x ∈ (L.transportChart
      ((cg.restrictInter L.isOpen_U').restrictInter hW) fun _ hy => hsub₀ hy.1).φ.source :=
    fun x => ⟨mem_univ x, ⟨hcgs (L.base.mapsTo (mem_univ x)), L.base.mapsTo (mem_univ x)⟩,
      mem_univ _⟩
  have hβ : PX.IsScSmoothMap realPolyfold (fun _ : X => (1 : ℝ)) := isScSmoothMap_real_const 1
  have hβs : tsupport (fun _ : X => (1 : ℝ)) ⊆ (L.transportChart _ hsub₀).φ.source :=
    fun x _ => ⟨mem_univ x, hcgs (L.base.mapsTo (mem_univ x)), L.base.mapsTo (mem_univ x)⟩
  have hγT : ∀ q ∈ Icc (0 : Fin 1 → ℝ) 1, γ q ∈ (L.transportChart
      ((cg.restrictInter L.isOpen_U').restrictInter hW) fun _ hy => hsub₀ hy.1).φ.source :=
    fun q _ => hT (γ q)
  -- the push-forwards
  have hϕγV' : ∀ q ∈ Icc (0 : Fin 1 → ℝ) 1, L.ϕ (γ q) ∈ V' := fun q hq => (hγV' q hq).1.2
  have hγB : ∀ q ∈ Icc (0 : Fin 1 → ℝ) 1, γ q ∈ VB := fun q hq => (hγV' q hq).2
  have m0 := pt1_mem_Icc (left_mem_Icc.2 (zero_le_one : (0 : ℝ) ≤ 1))
  have m1 := pt1_mem_Icc (right_mem_Icc.2 (zero_le_one : (0 : ℝ) ≤ 1))
  obtain ⟨e', he'⟩ := hLP'.exists_isPush (fun q => L.ϕ (γ q)) hϕγ hϕγV' rfl rfl
    (hLP'.subset (hϕγV' _ m0)) (hLP'.subset (hϕγV' _ m1)) hs₀' hs₁'
  have he'W := IsPush.transfer hc' (hc₀.restrictInter hW) hϕγ
    (fun q hq => hLP'.subset (hϕγV' q hq)) (fun q hq => (hγT q hq).2) rfl rfl
    (hLP'.subset (hϕγV' _ m0)) (hLP'.subset (hϕγV' _ m1)) (hγT _ m0).2 (hγT _ m1).2 hs₀' hs₁'
    he'
  have heT := L.isPush_mpull hf.toIsScFredholmSection hf'.toIsScFredholmSection hfL hsec hsec'
    hc₀ hsub₀ hW hβ hβs (fun _ _ => rfl) hγc hγT hs₀ hs₁ hs₀' hs₁' he'W
  have heB := IsPush.transfer (L.isChart_transportChart _ _ (hc₀.restrictInter hW)) hcB hγ hγT
    (fun q hq => hLP.subset (hγB q hq)) rfl rfl (hγT _ m0) (hγT _ m1)
    (hLP.subset (hγB _ m0)) (hLP.subset (hγB _ m1)) hs₀ hs₁ heT
  rw [orLocalTransportOfChart_transport_eq hX hch hf hsec hLP hVBo hγ hγB rfl rfl hs₀ hs₁
      (hLP.subset (hγB _ m0)) (hLP.subset (hγB _ m1)) heB,
    orLocalTransport_transport_eq hX' hbump' hf' hsec' hLP' hV'o hϕγ hϕγV' rfl
      rfl hs₀' hs₁' (hLP'.subset (hϕγV' _ m0)) (hLP'.subset (hϕγV' _ m1)) he',
    L.orxVia_eq_morVia _ _ hfL hsec hsec' (mem_univ _) hs₀
      (chartPtOf ((cg.restrictInter L.isOpen_U').restrictInter hW) (hc₀.restrictInter hW)
        (hγT _ m0).2 hs₀') (fun _ hy => hsub₀ hy.1),
    L.orxVia_eq_morVia _ _ hfL hsec hsec' (mem_univ _) hs₁
      (chartPtOf ((cg.restrictInter L.isOpen_U').restrictInter hW) (hc₀.restrictInter hW)
        (hγT _ m1).2 hs₁') (fun _ hy => hsub₀ hy.1)]
  exact equiv_comm_square_or _ _ _ _ _ _ (ChartPoint.orTransfer_trans _ _ _ _ _)
    (ChartPoint.orTransfer_trans _ _ _ _ _) _ _ _ _ _ _ _ _
    (ChartPoint.orTransfer_trans _ _ _ _ _) (ChartPoint.orTransfer_trans _ _ _ _ _) _

include hcg in
/-- **The transport commutes with `L` along every path; a chart over the whole base of `Y`,
bump functions on `X'`** (the last sentence of Theorem 12.5.3, p. 594, for paths): for an
sc-smooth path `γ` in `X`, `orxVia` followed by the transport of `f` along `γ` is the transport
of `f'` along `ϕ ∘ γ` followed by `orxVia` (`orxVia_comm_local_chart_bump` on the dyadic pieces,
`scPath_induction_or`). -/
theorem orxVia_comm_chart_bump {γ : (Fin 1 → ℝ) → X} (hγ : (rnPolyfold 1).IsScSmoothMap PX γ)
    {x₀ x₁ : X} (h₀ : γ (pt1 0) = x₀) (h₁ : γ (pt1 1) = x₁)
    (hs₀ : x₀ ∈ PX.smoothSet) (hs₁ : x₁ ∈ PX.smoothSet) :
    (L.orxVia hf.toIsScFredholmSection hf'.toIsScFredholmSection hfL hsec hsec'
      (mem_univ x₀) hs₀).trans
      ((orLocalTransportOfChart hX hch hf hsec).transport γ hγ h₀ h₁ hs₀ hs₁) =
    ((orLocalTransport hX' hbump' hf' hsec').transport (fun q => L.ϕ (γ q))
      (L.isScSmoothMap_comp_or hγ fun _ => mem_univ _) (congrArg L.ϕ h₀) (congrArg L.ϕ h₁)
      ((L.mem_smoothSet_iff (mem_univ x₀)).1 hs₀)
      ((L.mem_smoothSet_iff (mem_univ x₁)).1 hs₁)).trans
      (L.orxVia hf.toIsScFredholmSection hf'.toIsScFredholmSection hfL hsec hsec'
        (mem_univ x₁) hs₁) := by
  refine scPath_induction_or (fun _ => True) (fun γ => ∀
      (hγ : (rnPolyfold 1).IsScSmoothMap PX γ) {x₀ x₁ : X}
      (h₀ : γ (pt1 0) = x₀) (h₁ : γ (pt1 1) = x₁)
      (hs₀ : x₀ ∈ PX.smoothSet) (hs₁ : x₁ ∈ PX.smoothSet),
      (L.orxVia hf.toIsScFredholmSection hf'.toIsScFredholmSection hfL hsec hsec'
        (mem_univ x₀) hs₀).trans
        ((orLocalTransportOfChart hX hch hf hsec).transport γ hγ h₀ h₁ hs₀ hs₁) =
      ((orLocalTransport hX' hbump' hf' hsec').transport (fun q => L.ϕ (γ q))
        (L.isScSmoothMap_comp_or hγ fun _ => mem_univ _) (congrArg L.ϕ h₀) (congrArg L.ϕ h₁)
        ((L.mem_smoothSet_iff (mem_univ x₀)).1 hs₀)
        ((L.mem_smoothSet_iff (mem_univ x₁)).1 hs₁)).trans
        (L.orxVia hf.toIsScFredholmSection hf'.toIsScFredholmSection hfL hsec hsec'
          (mem_univ x₁) hs₁))
    (fun _ _ _ => trivial) (fun _ _ _ => trivial) ?_ ?_ hγ trivial hγ h₀ h₁ hs₀ hs₁
  · intro γ _ _ hl hr hγ x₀ x₁ h₀ h₁ hs₀ hs₁
    have hxm : γ (pt1 (1 / 2)) ∈ (univ : Set X) := mem_univ _
    have hsm := mem_smoothSet_of_isScSmoothMap hγ (pt1 (1 / 2))
    have Hl := hl (isScSmoothMap_leftHalf hγ) (leftHalf_zero.trans h₀)
      (leftHalf_one.trans rfl) hs₀ hsm
    have Hr := hr (isScSmoothMap_rightHalf hγ) (rightHalf_zero.trans rfl)
      (rightHalf_one.trans h₁) hsm hs₁
    rw [(orLocalTransportOfChart hX hch hf hsec).transport_halves hγ h₀ h₁ rfl hs₀ hs₁ hsm,
      (orLocalTransport hX' hbump' hf' hsec').transport_halves
        (L.isScSmoothMap_comp_or hγ fun _ => mem_univ _)
        (congrArg L.ϕ h₀) (congrArg L.ϕ h₁) rfl ((L.mem_smoothSet_iff (mem_univ x₀)).1 hs₀)
        ((L.mem_smoothSet_iff (mem_univ x₁)).1 hs₁) ((L.mem_smoothSet_iff hxm).1 hsm),
      ← Equiv.trans_assoc, Hl, Equiv.trans_assoc, Hr, ← Equiv.trans_assoc]
    rfl
  · intro γ hγ _ t _
    obtain ⟨V, hVo, haV, hV⟩ := L.orxVia_comm_local_chart_bump hX hch hf hsec hX' hbump' hcg hf'
      hsec' hfL (mem_smoothSet_of_isScSmoothMap hγ (pt1 t))
    exact ⟨V, hVo, haV, fun γ' _ _ hγ'V hγ'' _ _ h₀ h₁ hs₀ hs₁ =>
      hV γ' hγ'' hγ'V h₀ h₁ hs₀ hs₁⟩

end StrongBundle.LocalIso

end Comm

end Polyfold
