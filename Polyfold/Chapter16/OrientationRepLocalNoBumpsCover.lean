import Polyfold.Chapter12.ChartBumpTransportCommute

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part I, §6.6,
**Theorem 6.6.11** (p. 272), **Theorem 6.6.13** (pp. 273–274), and Chapter 12, §12.5, p. 594:
the last sentence of **Theorem 12.5.3**.

# The transport of a base covered by propagation neighbourhoods

## The text, paraphrased

Theorem 6.6.11: every smooth point has a neighbourhood in which the orientations of the
linearizations are propagated along sc-smooth paths, independently of the path.  Theorem 6.6.13
makes the functor `Γ_f` from these local propagations.

## What is formalized

The local transport data of `f` on an M-polyfold whose smooth points are covered by open sets
with the local propagation property (`IsPropagationNbhd`); the covering is a hypothesis, so that
no sc-smooth bump functions are used.

* `orLocalTransportOfCover`: the local transport data; the good sets are the propagation
  neighbourhoods, the push-forwards are `orPush`.
* `orLocalTransportOfCover_transport_eq`: property (∗).
* `LocalIso.orxVia_comm_local_chart_cover`, `LocalIso.orxVia_comm_chart_cover`: for a local
  strong bundle isomorphism `L : Y → Y'|U'` defined on all of the base of `Y`, where `Y` has a
  chart of its atlas over its whole base and `U'` lies in the base domain of a chart of `Y'`,
  the transport of `f = Ψ ∘ f' ∘ ϕ` (made in the chart) and the transport of `f'` (made from the
  covering) commute with `orxVia`.
-/

set_option maxSynthPendingDepth 3

open Set Function Topology Filter

noncomputable section

namespace Polyfold

open StrongRetr

universe u v u' v'

section Cover

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle PX P}
  {f : X → Y}

variable [∀ n : ℕ, ParacompactSpace ((Fin n → ℝ) × X)]
  [∀ n : ℕ, ParacompactSpace (pullbackSpace P (Prod.snd : (Fin n → ℝ) × X → X))]

variable (hf : B.IsScFredholmSection f) (hsec : B.HasScPlusSectionsThrough)
  (hcov : ∀ x ∈ PX.smoothSet, ∃ U, IsPropagationNbhd f hf U ∧ x ∈ U)

/-- **The local transport data of `f` when the smooth points are covered by propagation
neighbourhoods** (the proof of Theorem 6.6.13): the good sets are the open sets with the local
propagation property in some chart, the push-forwards are `orPush`; any two `Or_x^f` are in
bijection (two elements each). -/
def orLocalTransportOfCover : LocalTransport PX (fun x hs => Orx f hf x hs) where
  Good := IsPropagationNbhd f hf
  isOpen hU := hU.choose_spec.choose_spec.1
  exists_good x hx := hcov x hx
  nonempty _ hs₀ _ hs₁ :=
    let ⟨_, _, ha, ha'⟩ := exists_two_orx hf hs₀ hsec
    let ⟨_, _, hb, hb'⟩ := exists_two_orx hf hs₁ hsec
    nonempty_equiv_of_two ha ha' hb hb'
  push hU γ hγs hγU _ _ h₀ h₁ hs₀ hs₁ := orPush hU γ hγs hγU h₀ h₁ hs₀ hs₁
  push_trans hU _ _ _ hγ hγ₁ hγ₂ hγU hγ₁U hγ₂U _ _ _ h₀ h₂ h₁₀ h₁₁ h₂₀ h₂₁ hs₀ hs₁ hs₂ :=
    orPush_trans hU hγ hγ₁ hγ₂ hγU hγ₁U hγ₂U h₀ h₂ h₁₀ h₁₁ h₂₀ h₂₁ hs₀ hs₁ hs₂
  push_compat hU hU' _ hγ hγU hγU' _ _ h₀ h₁ hs₀ hs₁ :=
    orPush_compat hU hU' hγ hγU hγU' h₀ h₁ hs₀ hs₁

/-- **Property (∗) for the transport along a path**: on an sc-smooth path in an open `U` with the
local propagation property in a chart `c`, the transport is every push-forward `e` along the path
in `c`, read in the chosen charts. -/
theorem orLocalTransportOfCover_transport_eq {c : StrongBundleChart PX P} {hc : B.IsChart c}
    {U : Set X} (hU : HasLocalPropagation f hf c hc U) (hUo : IsOpen U)
    {γ : (Fin 1 → ℝ) → X} (hγs : (rnPolyfold 1).IsScSmoothMap PX γ)
    (hγU : ∀ q ∈ Icc (0 : Fin 1 → ℝ) 1, γ q ∈ U) {x₀ x₁ : X} (h₀ : γ (pt1 0) = x₀)
    (h₁ : γ (pt1 1) = x₁) (hs₀ : x₀ ∈ PX.smoothSet) (hs₁ : x₁ ∈ PX.smoothSet)
    (hx₀ : x₀ ∈ c.φ.source) (hx₁ : x₁ ∈ c.φ.source)
    {e : (chartPtOf c hc hx₀ hs₀).Or f hf ≃ (chartPtOf c hc hx₁ hs₁).Or f hf}
    (he : IsPush f hf c hc γ (fun q hq => hU.subset (hγU q hq)) h₀ h₁ hx₀ hx₁ hs₀ hs₁ e) :
    (orLocalTransportOfCover hf hsec hcov).transport γ hγs h₀ h₁ hs₀ hs₁ =
      (toChartOr hf hs₀ c hc hx₀).trans (e.trans (toChartOr hf hs₁ c hc hx₁).symm) :=
  ((orLocalTransportOfCover hf hsec hcov).transport_eq_push (U := U) ⟨c, hc, hUo, hU⟩ hγs
    (fun _ ht => hγU _ (pt1_mem_Icc ht)) h₀ h₁ hs₀ hs₁).trans
    (orPush_eq _ hγs (fun _ ht => hγU _ (pt1_mem_Icc ht)) h₀ h₁ hs₀ hs₁ hU hγU hx₀ hx₁ he)

end Cover

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

variable (hX : PX.IsTame) (hch : ∃ c ∈ B.atlas.charts, c.φ.source = univ)
  (hf : B.IsScFredholmSectionTame f) (hsec : B.HasScPlusSectionsThrough)
  (hcg : ∃ cg ∈ B'.atlas.charts, U' ⊆ cg.φ.source)
  (hf' : B'.IsScFredholmSection f')
  (hsec' : B'.HasScPlusSectionsThrough)
  (hcov' : ∀ x ∈ PX'.smoothSet, ∃ U, IsPropagationNbhd f' hf' U ∧ x ∈ U)
  (hfL : EqOn f (L.Ψ ∘ f' ∘ L.ϕ) univ)

include hcg in
/-- **The transport commutes with `L` on short paths; a chart over the whole base of `Y`, a
covering of `X'` by propagation neighbourhoods** (the local half of the last sentence of
Theorem 12.5.3, p. 594): every smooth `a₀` has an open neighbourhood `V` such that for every
sc-smooth path `γ` with `γ([0, 1]) ⊆ V`, `orxVia` followed by the transport of `f` along `γ` is
the transport of `f'` along `ϕ ∘ γ` followed by `orxVia`.  The sc⁺-sections of a push-forward of
`f'` are carried to `X` in the transported chart of a chart of `Y'` whose base domain contains
`U'`, restricted to `U'`; its base domain is `X`, so that no cut-off is needed. -/
theorem orxVia_comm_local_chart_cover {a₀ : X} (has₀ : a₀ ∈ PX.smoothSet) :
    ∃ V : Set X, IsOpen V ∧ a₀ ∈ V ∧ ∀ (γ : (Fin 1 → ℝ) → X)
      (hγ : (rnPolyfold 1).IsScSmoothMap PX γ),
      (∀ t ∈ Icc (0 : ℝ) 1, γ (pt1 t) ∈ V) → ∀ {x₀ x₁ : X} (h₀ : γ (pt1 0) = x₀)
        (h₁ : γ (pt1 1) = x₁) (hs₀ : x₀ ∈ PX.smoothSet) (hs₁ : x₁ ∈ PX.smoothSet),
        (L.orxVia hf.toIsScFredholmSection hf' hfL hsec hsec'
          (mem_univ x₀) hs₀).trans
          ((orLocalTransportOfChart hX hch hf hsec).transport γ hγ h₀ h₁ hs₀ hs₁) =
        ((orLocalTransportOfCover hf' hsec' hcov').transport (fun q => L.ϕ (γ q))
          (L.isScSmoothMap_comp_or hγ fun _ => mem_univ _) (congrArg L.ϕ h₀) (congrArg L.ϕ h₁)
          ((L.mem_smoothSet_iff (mem_univ x₀)).1 hs₀)
          ((L.mem_smoothSet_iff (mem_univ x₁)).1 hs₁)).trans
          (L.orxVia hf.toIsScFredholmSection hf' hfL hsec hsec'
            (mem_univ x₁) hs₁) := by
  obtain ⟨V', ⟨c', hc', hV'o, hLP'⟩, hxV'⟩ :=
    hcov' _ ((L.mem_smoothSet_iff (mem_univ a₀)).1 has₀)
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
  have heT := L.isPush_mpull hf.toIsScFredholmSection hf' hfL hsec hsec'
    hc₀ hsub₀ hW hβ hβs (fun _ _ => rfl) hγc hγT hs₀ hs₁ hs₀' hs₁' he'W
  have heB := IsPush.transfer (L.isChart_transportChart _ _ (hc₀.restrictInter hW)) hcB hγ hγT
    (fun q hq => hLP.subset (hγB q hq)) rfl rfl (hγT _ m0) (hγT _ m1)
    (hLP.subset (hγB _ m0)) (hLP.subset (hγB _ m1)) hs₀ hs₁ heT
  rw [orLocalTransportOfChart_transport_eq hX hch hf hsec hLP hVBo hγ hγB rfl rfl hs₀ hs₁
      (hLP.subset (hγB _ m0)) (hLP.subset (hγB _ m1)) heB,
    orLocalTransportOfCover_transport_eq hf' hsec' hcov' hLP' hV'o hϕγ hϕγV' rfl
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
/-- **The transport commutes with `L` along every path; a chart over the whole base of `Y`, a
covering of `X'` by propagation neighbourhoods** (the last sentence of Theorem 12.5.3, p. 594,
for paths): for an sc-smooth path `γ` in `X`, `orxVia` followed by the transport of `f` along
`γ` is the transport of `f'` along `ϕ ∘ γ` followed by `orxVia`
(`orxVia_comm_local_chart_cover` on the dyadic pieces, `scPath_induction_or`). -/
theorem orxVia_comm_chart_cover {γ : (Fin 1 → ℝ) → X} (hγ : (rnPolyfold 1).IsScSmoothMap PX γ)
    {x₀ x₁ : X} (h₀ : γ (pt1 0) = x₀) (h₁ : γ (pt1 1) = x₁)
    (hs₀ : x₀ ∈ PX.smoothSet) (hs₁ : x₁ ∈ PX.smoothSet) :
    (L.orxVia hf.toIsScFredholmSection hf' hfL hsec hsec'
      (mem_univ x₀) hs₀).trans
      ((orLocalTransportOfChart hX hch hf hsec).transport γ hγ h₀ h₁ hs₀ hs₁) =
    ((orLocalTransportOfCover hf' hsec' hcov').transport (fun q => L.ϕ (γ q))
      (L.isScSmoothMap_comp_or hγ fun _ => mem_univ _) (congrArg L.ϕ h₀) (congrArg L.ϕ h₁)
      ((L.mem_smoothSet_iff (mem_univ x₀)).1 hs₀)
      ((L.mem_smoothSet_iff (mem_univ x₁)).1 hs₁)).trans
      (L.orxVia hf.toIsScFredholmSection hf' hfL hsec hsec'
        (mem_univ x₁) hs₁) := by
  refine scPath_induction_or (fun _ => True) (fun γ => ∀
      (hγ : (rnPolyfold 1).IsScSmoothMap PX γ) {x₀ x₁ : X}
      (h₀ : γ (pt1 0) = x₀) (h₁ : γ (pt1 1) = x₁)
      (hs₀ : x₀ ∈ PX.smoothSet) (hs₁ : x₁ ∈ PX.smoothSet),
      (L.orxVia hf.toIsScFredholmSection hf' hfL hsec hsec'
        (mem_univ x₀) hs₀).trans
        ((orLocalTransportOfChart hX hch hf hsec).transport γ hγ h₀ h₁ hs₀ hs₁) =
      ((orLocalTransportOfCover hf' hsec' hcov').transport (fun q => L.ϕ (γ q))
        (L.isScSmoothMap_comp_or hγ fun _ => mem_univ _) (congrArg L.ϕ h₀) (congrArg L.ϕ h₁)
        ((L.mem_smoothSet_iff (mem_univ x₀)).1 hs₀)
        ((L.mem_smoothSet_iff (mem_univ x₁)).1 hs₁)).trans
        (L.orxVia hf.toIsScFredholmSection hf' hfL hsec hsec'
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
      (orLocalTransportOfCover hf' hsec' hcov').transport_halves
        (L.isScSmoothMap_comp_or hγ fun _ => mem_univ _)
        (congrArg L.ϕ h₀) (congrArg L.ϕ h₁) rfl ((L.mem_smoothSet_iff (mem_univ x₀)).1 hs₀)
        ((L.mem_smoothSet_iff (mem_univ x₁)).1 hs₁) ((L.mem_smoothSet_iff hxm).1 hsm),
      ← Equiv.trans_assoc, Hl, Equiv.trans_assoc, Hr, ← Equiv.trans_assoc]
    rfl
  · intro γ hγ _ t _
    obtain ⟨V, hVo, haV, hV⟩ := L.orxVia_comm_local_chart_cover hX hch hf hsec hcg hf'
      hsec' hcov' hfL (mem_smoothSet_of_isScSmoothMap hγ (pt1 t))
    exact ⟨V, hVo, haV, fun γ' _ _ hγ'V hγ'' _ _ h₀ h₁ hs₀ hs₁ =>
      hV γ' hγ'' hγ'V h₀ h₁ hs₀ hs₁⟩

end StrongBundle.LocalIso

end Comm

end Polyfold
