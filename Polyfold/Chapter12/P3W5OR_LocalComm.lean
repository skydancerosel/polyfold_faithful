import Polyfold.Chapter12.P3W3O_PushPull
import Polyfold.Chapter12.P3W5OR_PathInduction

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Chapter 12, §12.5,
p. 594: the proof of the last sentence of **Theorem 12.5.3** (2017: Theorem 12.11), first part.

# The transport of orientations commutes with a local strong bundle isomorphism

Let `L : Y|U → Y'|U'` be a local strong bundle isomorphism over `ϕ : U → U'` and `f = Ψ ∘ f' ∘ ϕ`
on `U`.  At a smooth `a ∈ U` the map `L.orxVia : Or^{f'}_{ϕ(a)} ≃ Or^f_a` reads `L⁻¹` on
orientations in the chosen charts (P3F's `morVia`, through a chart point at `ϕ(a)` inside `U'`).

* `LocalIso.orxVia`, `orxVia_eq_morVia` (any intermediate chart point inside `U'` gives it).
* `LocalIso.orxVia_comm_local`: every smooth `a₀ ∈ U` has an open neighbourhood `V` such that for
  every sc-smooth path `γ` in `U` with `γ([0, 1]) ⊆ V`, Part I's transport along `γ` (for `f`)
  after `orxVia` is `orxVia` after the transport along `ϕ ∘ γ` (for `f'`).  The proof: a
  propagation set of `f'` at `ϕ(a₀)` in a chart `c'` and one of `f` at `a₀` in a chart `c_B`
  (Theorem 6.6.11); a push-forward `e'` along `ϕ ∘ γ` in `c'`; its transfer to `c'|U' ∩ W`
  (`IsPush.transfer`), with `W = g⁻¹(N)` for an open `N ⊇ γ([0, 1])` on which a cut-off `β` is
  `1` (`exists_isScSmoothMap_eq_one_nhdsSet`); the carried push-forward of `f` in the transported
  chart (`LocalIso.isPush_mpull`, P3W3O); its transfer to `c_B`; property (∗)
  (`orLocalTransport_transport_eq`) on both sides; and the cocycle identities of `orTransfer`.
-/

set_option maxSynthPendingDepth 3

open Set Function Topology Filter

noncomputable section

namespace Polyfold

open StrongRetr

universe u v u' v'

/-- **Regrouping for the commutation square** (composition from left to right): the bijections
are those of the proof of `orxVia_comm_local`, related by the two cocycle identities. -/
theorem equiv_comm_square_or {A₀ A₁ C₀ C₁ W₀ W₁ T₀ T₁ Q₀ Q₁ B₀ B₁ : Sort*}
    (tc₀ : A₀ ≃ C₀) (tc₁ : A₁ ≃ C₁) (tw₀ : C₀ ≃ W₀) (tw₁ : C₁ ≃ W₁) (v₀ : A₀ ≃ W₀)
    (v₁ : A₁ ≃ W₁) (hv₀ : tc₀.trans tw₀ = v₀) (hv₁ : tc₁.trans tw₁ = v₁) (m₀ : W₀ ≃ T₀)
    (m₁ : W₁ ≃ T₁) (u₀ : T₀ ≃ Q₀) (u₁ : T₁ ≃ Q₁) (tq₀ : Q₀ ≃ B₀) (tq₁ : Q₁ ≃ B₁) (r₀ : T₀ ≃ B₀)
    (r₁ : T₁ ≃ B₁) (hr₀ : u₀.trans tq₀ = r₀) (hr₁ : u₁.trans tq₁ = r₁) (e' : C₀ ≃ C₁) :
    (v₀.trans (m₀.trans u₀)).trans (tq₀.trans ((((r₀.symm.trans
      ((m₀.symm.trans ((tw₀.symm.trans e').trans tw₁)).trans m₁)).trans r₁)).trans tq₁.symm)) =
      (tc₀.trans (e'.trans tc₁.symm)).trans (v₁.trans (m₁.trans u₁)) := by
  subst hv₀ hv₁ hr₀ hr₁
  ext a
  simp only [Equiv.trans_apply, Equiv.symm_trans_apply, Equiv.symm_apply_apply,
    Equiv.apply_symm_apply]

section Comm

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle PX P}
  {X' : Type u'} [TopologicalSpace X'] [T2Space X'] [ParacompactSpace X'] {PX' : MPolyfold X'}
  {Y' : Type v'} [TopologicalSpace Y'] [T2Space Y'] [ParacompactSpace Y'] {P' : Y' → X'}
  [∀ x, AddCommGroup (P' ⁻¹' {x})] [∀ x, Module ℝ (P' ⁻¹' {x})] {B' : StrongBundle PX' P'}
  {f : X → Y} {f' : X' → Y'}

namespace StrongBundle.LocalIso

variable {U : Set X} {U' : Set X'} (L : LocalIso B B' U U')

/-- **A chart point at `x ∈ U'` inside `U'`**: the chosen chart at `x` restricted to `U'`. -/
def innerPt (x : X') (hx : x ∈ U') (hs : x ∈ PX'.smoothSet) : ChartPoint B' x :=
  chartPtOf ((orChart B' x).restrictInter L.isOpen_U')
    ((isChart_orChart x).restrictInter L.isOpen_U') ⟨mem_orChart x, hx⟩ hs

theorem innerPt_sub (x : X') (hx : x ∈ U') (hs : x ∈ PX'.smoothSet) :
    (L.innerPt x hx hs).c.φ.source ⊆ U' := fun _ hy => hy.2

/-- **`L⁻¹` on orientations in the chosen charts**: `Or^{f'}_{ϕ(a)} ≃ Or^f_a` for a smooth
`a ∈ U` (P3F's `morVia` through `innerPt`). -/
def orxVia (hf : B.IsScFredholmSection f) (hf' : B'.IsScFredholmSection f')
    (hfL : EqOn f (L.Ψ ∘ f' ∘ L.ϕ) U) (hsec : B.HasScPlusSectionsThrough)
    (hsec' : B'.HasScPlusSectionsThrough) {a : X} (ha : a ∈ U) (has : a ∈ PX.smoothSet) :
    Orx f' hf' (L.ϕ a) ((L.mem_smoothSet_iff ha).1 has) ≃ Orx f hf a has :=
  L.morVia hf hf' _ _ (L.innerPt (L.ϕ a) (L.base.mapsTo ha) ((L.mem_smoothSet_iff ha).1 has))
    (L.innerPt_sub _ _ _) ha rfl (linSet_mpullPt hf hf' hfL hsec hsec' has
      ((L.mem_smoothSet_iff ha).1 has))
    ((L.mem_smoothSet_iff ha).1 has) has

/-- **`orxVia` through any chart point inside `U'`** (`morVia_eq`). -/
theorem orxVia_eq_morVia (hf : B.IsScFredholmSection f) (hf' : B'.IsScFredholmSection f')
    (hfL : EqOn f (L.Ψ ∘ f' ∘ L.ϕ) U) (hsec : B.HasScPlusSectionsThrough)
    (hsec' : B'.HasScPlusSectionsThrough) {a : X} (ha : a ∈ U) (has : a ∈ PX.smoothSet)
    (p : ChartPoint B' (L.ϕ a)) (hp : p.c.φ.source ⊆ U') :
    L.orxVia hf hf' hfL hsec hsec' ha has =
      L.morVia hf hf' _ _ p hp ha rfl (linSet_mpullPt hf hf' hfL hsec hsec' has
      ((L.mem_smoothSet_iff ha).1 has))
        ((L.mem_smoothSet_iff ha).1 has) has :=
  L.morVia_eq hf hf' _ _ _ hp ha rfl _ _ _ has

open scoped Classical in
/-- **A section of `Or^{f'}` carried along `L⁻¹`**: `a ↦ orxVia (o'_{ϕ(a)})` on `U`, a chosen
orientation outside `U`. -/
def pullOrx (hf : B.IsScFredholmSection f) (hf' : B'.IsScFredholmSection f')
    (hfL : EqOn f (L.Ψ ∘ f' ∘ L.ϕ) U) (hsec : B.HasScPlusSectionsThrough)
    (hsec' : B'.HasScPlusSectionsThrough) (o' : ∀ y (hy : y ∈ PX'.smoothSet), Orx f' hf' y hy)
    (a : X) (has : a ∈ PX.smoothSet) : Orx f hf a has :=
  if ha : a ∈ U then L.orxVia hf hf' hfL hsec hsec' ha has (o' (L.ϕ a) _)
  else (exists_two_orx hf has hsec).choose

/-- `ϕ ∘ γ` is sc-smooth for an sc-smooth path `γ` in `U`. -/
theorem isScSmoothMap_comp_or {γ : (Fin 1 → ℝ) → X} (hγ : (rnPolyfold 1).IsScSmoothMap PX γ)
    (hγU : ∀ q, γ q ∈ U) : (rnPolyfold 1).IsScSmoothMap PX' (fun q => L.ϕ (γ q)) :=
  L.base.isScSmoothOn.comp hγ fun q _ => hγU q

section Local

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

variable (hX : PX.IsTame) (hbump : PX.AdmitsBumpFunctions) (hf : B.IsScFredholmSectionTame f)
  (hsec : B.HasScPlusSectionsThrough) (hX' : PX'.IsTame) (hbump' : PX'.AdmitsBumpFunctions)
  (hf' : B'.IsScFredholmSectionTame f') (hsec' : B'.HasScPlusSectionsThrough)
  (hfL : EqOn f (L.Ψ ∘ f' ∘ L.ϕ) U)

/-- **The transport commutes with `L` on short paths** (the local half of the last sentence of
Theorem 12.5.3, p. 594): every smooth `a₀ ∈ U` has an open neighbourhood `V` such that for every
sc-smooth path `γ` in `U` with `γ([0, 1]) ⊆ V`, `orxVia` followed by the transport of `f` along
`γ` is the transport of `f'` along `ϕ ∘ γ` followed by `orxVia`. -/
theorem orxVia_comm_local {a₀ : X} (ha₀ : a₀ ∈ U) (has₀ : a₀ ∈ PX.smoothSet) :
    ∃ V : Set X, IsOpen V ∧ a₀ ∈ V ∧ ∀ (γ : (Fin 1 → ℝ) → X)
      (hγ : (rnPolyfold 1).IsScSmoothMap PX γ) (hγU : ∀ q, γ q ∈ U),
      (∀ t ∈ Icc (0 : ℝ) 1, γ (pt1 t) ∈ V) → ∀ {x₀ x₁ : X} (h₀ : γ (pt1 0) = x₀)
        (h₁ : γ (pt1 1) = x₁) (hx₀ : x₀ ∈ U) (hx₁ : x₁ ∈ U) (hs₀ : x₀ ∈ PX.smoothSet)
        (hs₁ : x₁ ∈ PX.smoothSet),
        (L.orxVia hf.toIsScFredholmSection hf'.toIsScFredholmSection hfL hsec hsec' hx₀
          hs₀).trans ((orLocalTransport hX hbump hf hsec).transport γ hγ h₀ h₁ hs₀ hs₁) =
        ((orLocalTransport hX' hbump' hf' hsec').transport (fun q => L.ϕ (γ q))
          (L.isScSmoothMap_comp_or hγ hγU) (congrArg L.ϕ h₀) (congrArg L.ϕ h₁)
          ((L.mem_smoothSet_iff hx₀).1 hs₀) ((L.mem_smoothSet_iff hx₁).1 hs₁)).trans
          (L.orxVia hf.toIsScFredholmSection hf'.toIsScFredholmSection hfL hsec hsec' hx₁
            hs₁) := by
  obtain ⟨c', hc', V', hV'o, hxV', hLP'⟩ :=
    theorem_6_6_11 hX' hbump' hf' ((L.mem_smoothSet_iff ha₀).1 has₀)
  obtain ⟨cB, hcB, VB, hVBo, haVB, hLP⟩ := theorem_6_6_11 hX hbump hf has₀
  refine ⟨(U ∩ L.ϕ ⁻¹' (V' ∩ U')) ∩ VB,
    (L.base.isScSmoothOn.continuousOn.isOpen_inter_preimage L.isOpen_U
      (hV'o.inter L.isOpen_U')).inter hVBo, ⟨⟨ha₀, hxV', L.base.mapsTo ha₀⟩, haVB⟩, ?_⟩
  intro γ hγ hγU hγV x₀ x₁ h₀ h₁ hx₀ hx₁ hs₀ hs₁
  subst h₀ h₁
  have hγV' := forall_mem_of_forall_pt1_mem hγV
  have hγc : Continuous γ := continuousOn_univ.1 hγ.continuousOn
  have hϕγ := L.isScSmoothMap_comp_or hγ hγU
  have hs₀' := (L.mem_smoothSet_iff hx₀).1 hs₀
  have hs₁' := (L.mem_smoothSet_iff hx₁).1 hs₁
  have hc₀ : B'.IsChart (c'.restrictInter L.isOpen_U') := hc'.restrictInter L.isOpen_U'
  have hsub₀ : (c'.restrictInter L.isOpen_U').φ.source ⊆ U' := fun _ hy => hy.2
  -- the cut-off `β`, equal to `1` on an open `N ⊇ γ([0, 1])`
  have hK : IsCompact (γ '' Icc (0 : Fin 1 → ℝ) 1) := isCompact_Icc.image hγc
  have hKT : γ '' Icc (0 : Fin 1 → ℝ) 1 ⊆ (L.transportChart _ hsub₀).φ.source := by
    rintro _ ⟨q, hq, rfl⟩
    exact ⟨(hγV' q hq).1.1, hLP'.subset (hγV' q hq).1.2.1, (hγV' q hq).1.2.2⟩
  obtain ⟨β, hβ, hβs, hβ1⟩ := exists_isScSmoothMap_eq_one_nhdsSet hbump hK
    (L.transportChart _ hsub₀).φ.isOpen_source hKT
  obtain ⟨N, hNo, hKN, hNβ⟩ := mem_nhdsSet_iff_exists.1 hβ1
  have hW : IsOpen (U' ∩ L.g ⁻¹' N) :=
    L.base.isScSmoothOn_inv.continuousOn.isOpen_inter_preimage L.isOpen_U' hNo
  have hβ1' : ∀ x ∈ (L.transportChart ((c'.restrictInter L.isOpen_U').restrictInter hW)
      fun _ hy => hsub₀ hy.1).φ.source, β x = 1 := by
    intro x hx
    have h : L.g (L.ϕ x) ∈ N := hx.2.2.2
    rw [L.base.left_inv x hx.1] at h
    exact hNβ h
  have hγT : ∀ q ∈ Icc (0 : Fin 1 → ℝ) 1, γ q ∈ (L.transportChart
      ((c'.restrictInter L.isOpen_U').restrictInter hW) fun _ hy => hsub₀ hy.1).φ.source := by
    intro q hq
    have h : L.g (L.ϕ (γ q)) ∈ N := by
      rw [L.base.left_inv _ (hγU q)]
      exact hKN ⟨q, hq, rfl⟩
    exact ⟨(hγV' q hq).1.1, ⟨hLP'.subset (hγV' q hq).1.2.1, (hγV' q hq).1.2.2⟩,
      (hγV' q hq).1.2.2, h⟩
  -- the push-forwards
  have hϕγV' : ∀ q ∈ Icc (0 : Fin 1 → ℝ) 1, L.ϕ (γ q) ∈ V' := fun q hq => (hγV' q hq).1.2.1
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
    hc₀ hsub₀ hW hβ hβs hβ1' hγc hγT hs₀ hs₁ hs₀' hs₁' he'W
  have heB := IsPush.transfer (L.isChart_transportChart _ _ (hc₀.restrictInter hW)) hcB hγ hγT
    (fun q hq => hLP.subset (hγB q hq)) rfl rfl (hγT _ m0) (hγT _ m1)
    (hLP.subset (hγB _ m0)) (hLP.subset (hγB _ m1)) hs₀ hs₁ heT
  rw [orLocalTransport_transport_eq hX hbump hf hsec hLP hVBo hγ hγB rfl rfl hs₀ hs₁
      (hLP.subset (hγB _ m0)) (hLP.subset (hγB _ m1)) heB,
    orLocalTransport_transport_eq hX' hbump' hf' hsec' hLP' hV'o hϕγ hϕγV' rfl rfl hs₀' hs₁'
      (hLP'.subset (hϕγV' _ m0)) (hLP'.subset (hϕγV' _ m1)) he',
    L.orxVia_eq_morVia _ _ hfL hsec hsec' hx₀ hs₀
      (chartPtOf ((c'.restrictInter L.isOpen_U').restrictInter hW) (hc₀.restrictInter hW)
        (hγT _ m0).2 hs₀') (fun _ hy => hsub₀ hy.1),
    L.orxVia_eq_morVia _ _ hfL hsec hsec' hx₁ hs₁
      (chartPtOf ((c'.restrictInter L.isOpen_U').restrictInter hW) (hc₀.restrictInter hW)
        (hγT _ m1).2 hs₁') (fun _ hy => hsub₀ hy.1)]
  exact equiv_comm_square_or _ _ _ _ _ _ (ChartPoint.orTransfer_trans _ _ _ _ _)
    (ChartPoint.orTransfer_trans _ _ _ _ _) _ _ _ _ _ _ _ _
    (ChartPoint.orTransfer_trans _ _ _ _ _) (ChartPoint.orTransfer_trans _ _ _ _ _) _

/-- **The transport commutes with `L` along every path in `U`** (the last sentence of
Theorem 12.5.3, p. 594, for paths): for an sc-smooth path `γ` with values in `U`, `orxVia`
followed by the transport of `f` along `γ` is the transport of `f'` along `ϕ ∘ γ` followed by
`orxVia` (`orxVia_comm_local` on the dyadic pieces, `scPath_induction_or`). -/
theorem orxVia_comm {γ : (Fin 1 → ℝ) → X} (hγ : (rnPolyfold 1).IsScSmoothMap PX γ)
    (hγU : ∀ q, γ q ∈ U) {x₀ x₁ : X} (h₀ : γ (pt1 0) = x₀) (h₁ : γ (pt1 1) = x₁)
    (hx₀ : x₀ ∈ U) (hx₁ : x₁ ∈ U) (hs₀ : x₀ ∈ PX.smoothSet) (hs₁ : x₁ ∈ PX.smoothSet) :
    (L.orxVia hf.toIsScFredholmSection hf'.toIsScFredholmSection hfL hsec hsec' hx₀
      hs₀).trans ((orLocalTransport hX hbump hf hsec).transport γ hγ h₀ h₁ hs₀ hs₁) =
    ((orLocalTransport hX' hbump' hf' hsec').transport (fun q => L.ϕ (γ q))
      (L.isScSmoothMap_comp_or hγ hγU) (congrArg L.ϕ h₀) (congrArg L.ϕ h₁)
      ((L.mem_smoothSet_iff hx₀).1 hs₀) ((L.mem_smoothSet_iff hx₁).1 hs₁)).trans
      (L.orxVia hf.toIsScFredholmSection hf'.toIsScFredholmSection hfL hsec hsec' hx₁ hs₁) := by
  refine scPath_induction_or (fun γ => ∀ q, γ q ∈ U) (fun γ => ∀
      (hγ : (rnPolyfold 1).IsScSmoothMap PX γ) (hγU : ∀ q, γ q ∈ U) {x₀ x₁ : X}
      (h₀ : γ (pt1 0) = x₀) (h₁ : γ (pt1 1) = x₁) (hx₀ : x₀ ∈ U) (hx₁ : x₁ ∈ U)
      (hs₀ : x₀ ∈ PX.smoothSet) (hs₁ : x₁ ∈ PX.smoothSet),
      (L.orxVia hf.toIsScFredholmSection hf'.toIsScFredholmSection hfL hsec hsec' hx₀
        hs₀).trans ((orLocalTransport hX hbump hf hsec).transport γ hγ h₀ h₁ hs₀ hs₁) =
      ((orLocalTransport hX' hbump' hf' hsec').transport (fun q => L.ϕ (γ q))
        (L.isScSmoothMap_comp_or hγ hγU) (congrArg L.ϕ h₀) (congrArg L.ϕ h₁)
        ((L.mem_smoothSet_iff hx₀).1 hs₀) ((L.mem_smoothSet_iff hx₁).1 hs₁)).trans
        (L.orxVia hf.toIsScFredholmSection hf'.toIsScFredholmSection hfL hsec hsec' hx₁ hs₁))
    (fun γ _ hQ q => hQ _) (fun γ _ hQ q => hQ _) ?_ ?_ hγ hγU hγ hγU h₀ h₁ hx₀ hx₁ hs₀ hs₁
  · intro γ _ hQ hl hr hγ hγU x₀ x₁ h₀ h₁ hx₀ hx₁ hs₀ hs₁
    have hxm : γ (pt1 (1 / 2)) ∈ U := hQ _
    have hsm := mem_smoothSet_of_isScSmoothMap hγ (pt1 (1 / 2))
    have Hl := hl (isScSmoothMap_leftHalf hγ) (fun q => hQ _) (leftHalf_zero.trans h₀)
      (leftHalf_one.trans rfl) hx₀ hxm hs₀ hsm
    have Hr := hr (isScSmoothMap_rightHalf hγ) (fun q => hQ _) (rightHalf_zero.trans rfl)
      (rightHalf_one.trans h₁) hxm hx₁ hsm hs₁
    rw [(orLocalTransport hX hbump hf hsec).transport_halves hγ h₀ h₁ rfl hs₀ hs₁ hsm,
      (orLocalTransport hX' hbump' hf' hsec').transport_halves (L.isScSmoothMap_comp_or hγ hγU)
        (congrArg L.ϕ h₀) (congrArg L.ϕ h₁) rfl ((L.mem_smoothSet_iff hx₀).1 hs₀)
        ((L.mem_smoothSet_iff hx₁).1 hs₁) ((L.mem_smoothSet_iff hxm).1 hsm),
      ← Equiv.trans_assoc, Hl, Equiv.trans_assoc, Hr, ← Equiv.trans_assoc]
    rfl
  · intro γ hγ hQ t _
    obtain ⟨V, hVo, haV, hV⟩ := L.orxVia_comm_local hX hbump hf hsec hX' hbump' hf' hsec' hfL
      (hQ (pt1 t)) (mem_smoothSet_of_isScSmoothMap hγ (pt1 t))
    exact ⟨V, hVo, haV, fun γ' _ _ hγ'V hγ'' hQ'' _ _ h₀ h₁ hx₀ hx₁ hs₀ hs₁ =>
      hV γ' hγ'' hQ'' hγ'V h₀ h₁ hx₀ hx₁ hs₀ hs₁⟩

/-- **The continuity statement** (the last sentence of Theorem 12.5.3, p. 594, for a local strong
bundle isomorphism between two bundles): a continuous orientation `o'` of `f'` over an open `V'`
(`IsContOrOn` for Part I's transport) is carried by `L⁻¹` to a continuous orientation of `f`
over `U ∩ ϕ⁻¹(V')`, `a ↦ orxVia (o'_{ϕ(a)})`.  Paths in `U ∩ ϕ⁻¹(V')` are first reparametrized
by the smooth transition function, so that they take all their values in `U`. -/
theorem isContOrOn_pullOrx {V' : Set X'}
    {o' : ∀ y (hy : y ∈ PX'.smoothSet), Orx f' hf'.toIsScFredholmSection y hy}
    (h : IsContOrOn (orLocalTransport hX' hbump' hf' hsec') V' o') :
    IsContOrOn (orLocalTransport hX hbump hf hsec) (U ∩ L.ϕ ⁻¹' V')
      (L.pullOrx hf.toIsScFredholmSection hf'.toIsScFredholmSection hfL hsec hsec' o') := by
  refine ⟨L.base.isScSmoothOn.continuousOn.isOpen_inter_preimage L.isOpen_U h.1, ?_⟩
  intro γ hγ hγV x₀ x₁ h₀ h₁ hs₀ hs₁
  have hx₀ : x₀ ∈ U := h₀ ▸ (hγV 0 (left_mem_Icc.2 zero_le_one)).1
  have hx₁ : x₁ ∈ U := h₁ ▸ (hγV 1 (right_mem_Icc.2 zero_le_one)).1
  have hγ' := isScSmoothMap_smoothTransPath_or hγ
  have hγU : ∀ q, smoothTransPath_or γ q ∈ U := smoothTransPath_or_mem fun t ht => (hγV t ht).1
  have h₀' : smoothTransPath_or γ (pt1 0) = x₀ :=
    (congrArg (fun t => γ (pt1 t)) Real.smoothTransition.zero).trans h₀
  have h₁' : smoothTransPath_or γ (pt1 1) = x₁ :=
    (congrArg (fun t => γ (pt1 t)) Real.smoothTransition.one).trans h₁
  rw [← (orLocalTransport hX hbump hf hsec).transport_reparam hγ Real.smoothTransition.contDiff
    Real.smoothTransition.zero Real.smoothTransition.one h₀ h₁ hs₀ hs₁]
  have hc := DFunLike.congr_fun (L.orxVia_comm hX hbump hf hsec hX' hbump' hf' hsec' hfL hγ' hγU
    h₀' h₁' hx₀ hx₁ hs₀ hs₁) (o' (L.ϕ x₀) ((L.mem_smoothSet_iff hx₀).1 hs₀))
  simp only [Equiv.trans_apply] at hc
  rw [pullOrx, pullOrx, dif_pos hx₀, dif_pos hx₁]
  refine hc.trans (congrArg _ ?_)
  exact h.2 (fun q => L.ϕ (smoothTransPath_or γ q)) (L.isScSmoothMap_comp_or hγ' hγU)
    (fun t ht => (hγV _ ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩).2)
    (congrArg L.ϕ h₀') (congrArg L.ϕ h₁') _ _

end Local

end StrongBundle.LocalIso

end Comm

end Polyfold
