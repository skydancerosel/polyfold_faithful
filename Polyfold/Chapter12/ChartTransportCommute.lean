import Polyfold.Chapter12.OrientationEquivalenceContinuity
import Polyfold.Chapter6.ChartOrientationSpace

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Chapter 12, §12.5,
p. 594: the last sentence of **Theorem 12.5.3** (2017: Theorem 12.11), with Part I, §6.6,
**Theorem 6.6.11** (pp. 223–224), for strong bundles with a chart over the whole base.

# The transport of orientations commutes with a strong bundle isomorphism defined on the base

The text, paraphrased: the orientations of the linearizations of an sc-Fredholm section are
propagated along sc-smooth paths (Theorem 6.6.11), and this propagation is compatible with the
local strong bundle isomorphisms given by the morphisms (the last sentence of Theorem 12.5.3).

What is formalized: let `P : Y → X` and `P' : Y' → X'` be strong bundles which each have a chart
of the atlas over the whole base, `X` and `X'` tame, `f`, `f'` sc-Fredholm sections with tame germ
data, `L : Y → Y'|U'` a local strong bundle isomorphism over `ϕ : X → U'` defined on all of `X`,
and `f = Ψ ∘ f' ∘ ϕ`.  The transports are those of `orLocalTransportOfChart` (Part I's transport
made without sc-smooth bump functions).

* `LocalIso.orxVia_comm_local_of_chart`: every smooth `a₀` has an open neighbourhood `V` such
  that for sc-smooth paths `γ` in `V` the transport of `f` along `γ` after `orxVia` is `orxVia`
  after the transport of `f'` along `ϕ ∘ γ`.  The sc⁺-sections of the push-forward data of `f'`
  are carried to `X` without a cut-off, because the isomorphism is defined over the whole base:
  in `LocalIso.isPush_mpull` the chart `c₀` is the chart of `Y'` over `X'` restricted to `U'`,
  whose transported chart has base domain `X`, and the function `β` is the constant `1`.
* `LocalIso.orxVia_comm_of_chart`: the same along every sc-smooth path (`scPath_induction_or`).
* `LocalIso.isContOrOn_pullOrx_of_chart`: a continuous orientation `o'` of `f'` over an open `V'`
  is carried to a continuous orientation of `f` over `ϕ⁻¹(V')`.
* `LocalIso.isContOrOn_of_pullOrx_of_chart`: conversely, if the carried section is a continuous
  orientation over `ϕ⁻¹(V')`, then `o'` is one over `U' ∩ V'`.
* `LocalIso.pullOrx_apply_univ`: the carried section at a point.
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

/-- **The carried section at a point**, for an isomorphism defined on all of the base:
`pullOrx o' a = orxVia (o'_{ϕ(a)})`. -/
theorem pullOrx_apply_univ (hf : B.IsScFredholmSection f) (hf' : B'.IsScFredholmSection f')
    (hfL : EqOn f (L.Ψ ∘ f' ∘ L.ϕ) univ) (hsec : B.HasScPlusSectionsThrough)
    (hsec' : B'.HasScPlusSectionsThrough) (o' : ∀ y (hy : y ∈ PX'.smoothSet), Orx f' hf' y hy)
    (a : X) (has : a ∈ PX.smoothSet) :
    L.pullOrx hf hf' hfL hsec hsec' o' a has =
      L.orxVia hf hf' hfL hsec hsec' (mem_univ a) has
        (o' (L.ϕ a) ((L.mem_smoothSet_iff (mem_univ a)).1 has)) := by
  rw [pullOrx, dif_pos (mem_univ a)]

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
  (hch' : ∃ c ∈ B'.atlas.charts, c.φ.source = univ) (hf' : B'.IsScFredholmSectionTame f')
  (hsec' : B'.HasScPlusSectionsThrough) (hfL : EqOn f (L.Ψ ∘ f' ∘ L.ϕ) univ)

/-- **The transport commutes with `L` on short paths, chart over the whole base** (the local half
of the last sentence of Theorem 12.5.3, p. 594): every smooth `a₀` has an open neighbourhood `V`
such that for every sc-smooth path `γ` with `γ([0, 1]) ⊆ V`, `orxVia` followed by the transport
of `f` along `γ` is the transport of `f'` along `ϕ ∘ γ` followed by `orxVia`.  The sc⁺-sections
of a push-forward of `f'` are carried to `X` in the transported chart of the chart of `Y'` over
`X'`, restricted to `U'`; its base domain is `X`, so that no cut-off is needed. -/
theorem orxVia_comm_local_of_chart {a₀ : X} (has₀ : a₀ ∈ PX.smoothSet) :
    ∃ V : Set X, IsOpen V ∧ a₀ ∈ V ∧ ∀ (γ : (Fin 1 → ℝ) → X)
      (hγ : (rnPolyfold 1).IsScSmoothMap PX γ),
      (∀ t ∈ Icc (0 : ℝ) 1, γ (pt1 t) ∈ V) → ∀ {x₀ x₁ : X} (h₀ : γ (pt1 0) = x₀)
        (h₁ : γ (pt1 1) = x₁) (hs₀ : x₀ ∈ PX.smoothSet) (hs₁ : x₁ ∈ PX.smoothSet),
        (L.orxVia hf.toIsScFredholmSection hf'.toIsScFredholmSection hfL hsec hsec'
          (mem_univ x₀) hs₀).trans
          ((orLocalTransportOfChart hX hch hf hsec).transport γ hγ h₀ h₁ hs₀ hs₁) =
        ((orLocalTransportOfChart hX' hch' hf' hsec').transport (fun q => L.ϕ (γ q))
          (L.isScSmoothMap_comp_or hγ fun _ => mem_univ _) (congrArg L.ϕ h₀) (congrArg L.ϕ h₁)
          ((L.mem_smoothSet_iff (mem_univ x₀)).1 hs₀)
          ((L.mem_smoothSet_iff (mem_univ x₁)).1 hs₁)).trans
          (L.orxVia hf.toIsScFredholmSection hf'.toIsScFredholmSection hfL hsec hsec'
            (mem_univ x₁) hs₁) := by
  obtain ⟨c', hc', V', hV'o, hxV', hLP'⟩ :=
    theorem_6_6_11_of_chart hX' hch' hf' ((L.mem_smoothSet_iff (mem_univ a₀)).1 has₀)
  obtain ⟨cB, hcB, VB, hVBo, haVB, hLP⟩ := theorem_6_6_11_of_chart hX hch hf has₀
  obtain ⟨cg, hcgA, hcgs⟩ := hch'
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
    fun x => ⟨mem_univ x, ⟨hcgs ▸ mem_univ _, L.base.mapsTo (mem_univ x)⟩, mem_univ _⟩
  have hβ : PX.IsScSmoothMap realPolyfold (fun _ : X => (1 : ℝ)) := isScSmoothMap_real_const 1
  have hβs : tsupport (fun _ : X => (1 : ℝ)) ⊆ (L.transportChart _ hsub₀).φ.source :=
    fun x _ => ⟨mem_univ x, hcgs ▸ mem_univ _, L.base.mapsTo (mem_univ x)⟩
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
    orLocalTransportOfChart_transport_eq hX' ⟨cg, hcgA, hcgs⟩ hf' hsec' hLP' hV'o hϕγ hϕγV' rfl
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

/-- **The transport commutes with `L` along every path, chart over the whole base** (the last
sentence of Theorem 12.5.3, p. 594, for paths): for an sc-smooth path `γ` in `X`, `orxVia`
followed by the transport of `f` along `γ` is the transport of `f'` along `ϕ ∘ γ` followed by
`orxVia` (`orxVia_comm_local_of_chart` on the dyadic pieces, `scPath_induction_or`). -/
theorem orxVia_comm_of_chart {γ : (Fin 1 → ℝ) → X} (hγ : (rnPolyfold 1).IsScSmoothMap PX γ)
    {x₀ x₁ : X} (h₀ : γ (pt1 0) = x₀) (h₁ : γ (pt1 1) = x₁)
    (hs₀ : x₀ ∈ PX.smoothSet) (hs₁ : x₁ ∈ PX.smoothSet) :
    (L.orxVia hf.toIsScFredholmSection hf'.toIsScFredholmSection hfL hsec hsec'
      (mem_univ x₀) hs₀).trans
      ((orLocalTransportOfChart hX hch hf hsec).transport γ hγ h₀ h₁ hs₀ hs₁) =
    ((orLocalTransportOfChart hX' hch' hf' hsec').transport (fun q => L.ϕ (γ q))
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
      ((orLocalTransportOfChart hX' hch' hf' hsec').transport (fun q => L.ϕ (γ q))
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
      (orLocalTransportOfChart hX' hch' hf' hsec').transport_halves
        (L.isScSmoothMap_comp_or hγ fun _ => mem_univ _)
        (congrArg L.ϕ h₀) (congrArg L.ϕ h₁) rfl ((L.mem_smoothSet_iff (mem_univ x₀)).1 hs₀)
        ((L.mem_smoothSet_iff (mem_univ x₁)).1 hs₁) ((L.mem_smoothSet_iff hxm).1 hsm),
      ← Equiv.trans_assoc, Hl, Equiv.trans_assoc, Hr, ← Equiv.trans_assoc]
    rfl
  · intro γ hγ _ t _
    obtain ⟨V, hVo, haV, hV⟩ := L.orxVia_comm_local_of_chart hX hch hf hsec hX' hch' hf' hsec'
      hfL (mem_smoothSet_of_isScSmoothMap hγ (pt1 t))
    exact ⟨V, hVo, haV, fun γ' _ _ hγ'V hγ'' _ _ h₀ h₁ hs₀ hs₁ =>
      hV γ' hγ'' hγ'V h₀ h₁ hs₀ hs₁⟩

/-- **The continuity statement, chart over the whole base** (the last sentence of
Theorem 12.5.3, p. 594): a continuous orientation `o'` of `f'` over an open `V'` (`IsContOrOn`
for the transport `orLocalTransportOfChart`) is carried by `L⁻¹` to a continuous orientation of
`f` over `ϕ⁻¹(V')`, `a ↦ orxVia (o'_{ϕ(a)})`. -/
theorem isContOrOn_pullOrx_of_chart {V' : Set X'}
    {o' : ∀ y (hy : y ∈ PX'.smoothSet), Orx f' hf'.toIsScFredholmSection y hy}
    (h : IsContOrOn (orLocalTransportOfChart hX' hch' hf' hsec') V' o') :
    IsContOrOn (orLocalTransportOfChart hX hch hf hsec) (L.ϕ ⁻¹' V')
      (L.pullOrx hf.toIsScFredholmSection hf'.toIsScFredholmSection hfL hsec hsec' o') := by
  refine ⟨?_, ?_⟩
  · have := L.base.isScSmoothOn.continuousOn.isOpen_inter_preimage isOpen_univ h.1
    rwa [univ_inter] at this
  intro γ hγ hγV x₀ x₁ h₀ h₁ hs₀ hs₁
  have hc := DFunLike.congr_fun (L.orxVia_comm_of_chart hX hch hf hsec hX' hch' hf' hsec' hfL hγ
    h₀ h₁ hs₀ hs₁) (o' (L.ϕ x₀) ((L.mem_smoothSet_iff (mem_univ x₀)).1 hs₀))
  simp only [Equiv.trans_apply] at hc
  rw [L.pullOrx_apply_univ, L.pullOrx_apply_univ]
  refine hc.trans (congrArg _ ?_)
  exact h.2 (fun q => L.ϕ (γ q)) (L.isScSmoothMap_comp_or hγ fun _ => mem_univ _)
    (fun t ht => hγV t ht) (congrArg L.ϕ h₀) (congrArg L.ϕ h₁) _ _

/-- **A section is continuous where the section it carries is, chart over the whole base** (the
converse of `isContOrOn_pullOrx_of_chart`): if `a ↦ orxVia (o'_{ϕ(a)})` is a continuous
orientation of `f` over `ϕ⁻¹(V')`, then `o'` is a continuous orientation of `f'` over
`U' ∩ V'`.  Paths in `U' ∩ V'` are first reparametrized by the smooth transition function, so
that they take all their values in `U'`, and then carried back by `ϕ⁻¹`. -/
theorem isContOrOn_of_pullOrx_of_chart {V' : Set X'} (hV' : IsOpen V')
    {o' : ∀ y (hy : y ∈ PX'.smoothSet), Orx f' hf'.toIsScFredholmSection y hy}
    (h : IsContOrOn (orLocalTransportOfChart hX hch hf hsec) (L.ϕ ⁻¹' V')
      (L.pullOrx hf.toIsScFredholmSection hf'.toIsScFredholmSection hfL hsec hsec' o')) :
    IsContOrOn (orLocalTransportOfChart hX' hch' hf' hsec') (U' ∩ V') o' := by
  refine ⟨L.isOpen_U'.inter hV', ?_⟩
  intro γ' hγ' hγ'V x₀' x₁' h₀' h₁' hs₀' hs₁'
  have hx₀' : x₀' ∈ U' := h₀' ▸ (hγ'V 0 (left_mem_Icc.2 zero_le_one)).1
  have hx₁' : x₁' ∈ U' := h₁' ▸ (hγ'V 1 (right_mem_Icc.2 zero_le_one)).1
  obtain ⟨x₀, rfl⟩ : ∃ x₀, L.ϕ x₀ = x₀' := ⟨L.g x₀', L.base.right_inv _ hx₀'⟩
  obtain ⟨x₁, rfl⟩ : ∃ x₁, L.ϕ x₁ = x₁' := ⟨L.g x₁', L.base.right_inv _ hx₁'⟩
  have hs₀ : x₀ ∈ PX.smoothSet := (L.mem_smoothSet_iff (mem_univ x₀)).2 hs₀'
  have hs₁ : x₁ ∈ PX.smoothSet := (L.mem_smoothSet_iff (mem_univ x₁)).2 hs₁'
  have hγ'' := isScSmoothMap_smoothTransPath_or hγ'
  have hγ''U : ∀ q, smoothTransPath_or γ' q ∈ U' ∩ V' := smoothTransPath_or_mem hγ'V
  set γ : (Fin 1 → ℝ) → X := fun q => L.g (smoothTransPath_or γ' q) with hγdef
  have hγ : (rnPolyfold 1).IsScSmoothMap PX γ :=
    L.base.isScSmoothOn_inv.comp hγ'' fun q _ => (hγ''U q).1
  have hγU : ∀ q, γ q ∈ (univ : Set X) := fun _ => mem_univ _
  have hϕγ : ∀ q, L.ϕ (γ q) = smoothTransPath_or γ' q := fun q =>
    L.base.right_inv _ (hγ''U q).1
  have h₀'' : smoothTransPath_or γ' (pt1 0) = L.ϕ x₀ :=
    (congrArg (fun t => γ' (pt1 t)) Real.smoothTransition.zero).trans h₀'
  have h₁'' : smoothTransPath_or γ' (pt1 1) = L.ϕ x₁ :=
    (congrArg (fun t => γ' (pt1 t)) Real.smoothTransition.one).trans h₁'
  have h₀ : γ (pt1 0) = x₀ := by
    change L.g (smoothTransPath_or γ' (pt1 0)) = x₀
    rw [h₀'', L.base.left_inv _ (mem_univ x₀)]
  have h₁ : γ (pt1 1) = x₁ := by
    change L.g (smoothTransPath_or γ' (pt1 1)) = x₁
    rw [h₁'', L.base.left_inv _ (mem_univ x₁)]
  have e1 := (orLocalTransportOfChart hX' hch' hf' hsec').transport_reparam hγ'
    Real.smoothTransition.contDiff Real.smoothTransition.zero Real.smoothTransition.one h₀' h₁'
    hs₀' hs₁'
  have e2 := (orLocalTransportOfChart hX' hch' hf' hsec').transport_congr
    (γ := fun s => γ' (pt1 (Real.smoothTransition (s 0)))) (γ' := fun q => L.ϕ (γ q))
    (fun t _ => (hϕγ (pt1 t)).symm) (isScSmoothMap_reparam hγ' Real.smoothTransition.contDiff)
    (L.isScSmoothMap_comp_or hγ hγU) h₀'' h₁'' (congrArg L.ϕ h₀) (congrArg L.ϕ h₁) hs₀' hs₁'
  rw [← e1, e2]
  have hc := DFunLike.congr_fun (L.orxVia_comm_of_chart hX hch hf hsec hX' hch' hf' hsec' hfL hγ
    h₀ h₁ hs₀ hs₁) (o' (L.ϕ x₀) hs₀')
  simp only [Equiv.trans_apply] at hc
  have hcont := h.2 γ hγ (fun t _ => by rw [mem_preimage, hϕγ]; exact (hγ''U _).2)
    h₀ h₁ hs₀ hs₁
  rw [L.pullOrx_apply_univ, L.pullOrx_apply_univ] at hcont
  exact (L.orxVia hf.toIsScFredholmSection hf'.toIsScFredholmSection hfL hsec hsec'
    (mem_univ x₁) hs₁).injective (hc.symm.trans hcont)

end StrongBundle.LocalIso

end Comm

end Polyfold
