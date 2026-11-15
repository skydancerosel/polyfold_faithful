import Polyfold.Chapter12.LocalOrientationIso

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Chapter 12, §12.5,
Theorem 12.5.3, last sentence (p. 594), and the proof of Theorem 12.5.7 (pp. 596–597), for the
linearizations made with local sc⁺-sections.

# Local strong bundle isomorphisms commute with the propagation of orientations

## The text, paraphrased

A local sc-diffeomorphism covered by a local strong bundle isomorphism `Φ` with `f = Φ^* f'`
maps a continuous section of the orientation bundle of `f'` to a continuous section of the
orientation bundle of `f` (Theorem 12.5.3 for the isomorphisms `Φ̂` of morphisms; the proof of
Theorem 12.5.7 for strong bundle equivalences).  Continuity is tested along sc-smooth paths,
along which orientations are propagated (Theorems 6.6.11, 6.6.13).

## What is formalized

For `L : LocalIso B B' U U'` with `f = Ψ ∘ f' ∘ ϕ` on `U`, tame bases and tame germ data, and
the maps `L.orLoc : Or_{ϕ(a)}^{f'} ≃ Or_a^f` on the local orientation sets:

* `orLoc_comm_of_dom`: for an sc-smooth path in a domain `D ⊆ U` which `ϕ` maps into a domain
  `D'`, `orLoc` at the ends intertwines the transports along `γ` and along `ϕ ∘ γ`.
* `orLoc_comm`: **the same for every sc-smooth path in `U`**.
* `pullLoc o'`: the family `a ↦ orLoc (o'_{ϕ(a)})` carried by `L` from a family `o'` of
  orientations of `f'`.
* `isContOn_pullLoc`: if `o'` is continuous over an open `V'`, the carried family is continuous
  over `U ∩ ϕ⁻¹(V')`.
* `isContOn_of_pullLoc`: conversely, if the carried family is continuous over `U ∩ ϕ⁻¹(V')`,
  then `o'` is continuous over `U' ∩ V'`.

"Continuous over an open set" is `LocalTransport.IsContOn` for `orLocalTransportLoc`: carried
along by the transport along all sc-smooth paths in the set.
-/

set_option maxSynthPendingDepth 3

open Set Function Topology

noncomputable section

namespace Polyfold

universe u v u' v'

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle PX P}
  {X' : Type u'} [TopologicalSpace X'] [T2Space X'] [ParacompactSpace X'] {PX' : MPolyfold X'}
  {Y' : Type v'} [TopologicalSpace Y'] [T2Space Y'] [ParacompactSpace Y'] {P' : Y' → X'}
  [∀ x, AddCommGroup (P' ⁻¹' {x})] [∀ x, Module ℝ (P' ⁻¹' {x})] {B' : StrongBundle PX' P'}
  {f : X → Y} {f' : X' → Y'}

/-- If `t₀' ≫ d₀ = A₀ ≫ t₀`, `t₁' ≫ d₁ = A₁ ≫ t₁` and `d₀ ≫ T = T' ≫ d₁`, then the conjugates
of `T` and `T'` are intertwined by `A₀`, `A₁`. -/
private theorem conj_comm_of_comm {α β γ δ α' β' γ' δ' : Sort*} {A₀ : α' ≃ α} {A₁ : β' ≃ β}
    {t₀ : α ≃ γ} {t₁ : β ≃ δ} {t₀' : α' ≃ γ'} {t₁' : β' ≃ δ'} {d₀ : γ' ≃ γ} {d₁ : δ' ≃ δ}
    {T : γ ≃ δ} {T' : γ' ≃ δ'} (h₀ : t₀'.trans d₀ = A₀.trans t₀)
    (h₁ : t₁'.trans d₁ = A₁.trans t₁) (hc : d₀.trans T = T'.trans d₁) :
    A₀.trans (t₀.trans (T.trans t₁.symm)) = (t₀'.trans (T'.trans t₁'.symm)).trans A₁ := by
  refine Equiv.ext fun o => ?_
  have e₀ := DFunLike.congr_fun h₀ o
  have e₁ := DFunLike.congr_fun h₁ (t₁'.symm (T' (t₀' o)))
  have ec := DFunLike.congr_fun hc (t₀' o)
  simp only [Equiv.trans_apply, Equiv.apply_symm_apply] at e₀ e₁ ec ⊢
  rw [← e₀, ec, e₁, Equiv.symm_apply_apply]

private theorem trans_congr_left {α β γ : Sort*} {e e' : α ≃ β} (h : e = e') (g : β ≃ γ) :
    e.trans g = e'.trans g := h ▸ rfl

private theorem trans_congr_right {α β γ : Sort*} (g : α ≃ β) {e e' : β ≃ γ} (h : e = e') :
    g.trans e = g.trans e' := h ▸ rfl

namespace StrongBundle.LocalIso

variable {U : Set X} {U' : Set X'} (L : LocalIso B B' U U')

/-! ### Paths in a domain -/

/-- **The maps of orientations commute with the propagation along paths in a domain**: for a
domain `D ⊆ U` which `ϕ` maps into a domain `D'` and an sc-smooth path `γ` in `D` from `x₀` to
`x₁`, `orLoc` at `x₀` followed by the transport of `f` along `γ` is the transport of `f'` along
`ϕ ∘ γ` followed by `orLoc` at `x₁`. -/
theorem orLoc_comm_of_dom (hX : PX.IsTame) (hX' : PX'.IsTame)
    (hf : B.IsScFredholmSectionTame f) (hf' : B'.IsScFredholmSectionTame f')
    (hfL : EqOn f (L.Ψ ∘ f' ∘ L.ϕ) U) (D : B.Dom) (D' : B'.Dom) (hDU : D.carrier ⊆ U)
    (hD' : ∀ y ∈ D.carrier, L.ϕ y ∈ D'.carrier) {γ : (Fin 1 → ℝ) → X}
    (hγ : (rnPolyfold 1).IsScSmoothMap PX γ) (hγD : ∀ q, γ q ∈ D.carrier) {x₀ x₁ : X}
    (h₀ : γ (pt1 0) = x₀) (h₁ : γ (pt1 1) = x₁) (hx₀ : x₀ ∈ U) (hx₁ : x₁ ∈ U)
    (hs₀ : x₀ ∈ PX.smoothSet) (hs₁ : x₁ ∈ PX.smoothSet) (hs₀' : L.ϕ x₀ ∈ PX'.smoothSet)
    (hs₁' : L.ϕ x₁ ∈ PX'.smoothSet) :
    (L.orLoc hf hf' hfL hx₀ rfl hs₀ hs₀').trans
        ((orLocalTransportLoc hX hf).transport γ hγ h₀ h₁ hs₀ hs₁) =
      ((orLocalTransportLoc hX' hf').transport (fun q => L.ϕ (γ q))
        (L.isScSmoothMap_comp_or hγ fun q => hDU (hγD q)) (congrArg L.ϕ h₀) (congrArg L.ϕ h₁)
        hs₀' hs₁').trans (L.orLoc hf hf' hfL hx₁ rfl hs₁ hs₁') := by
  have hxD₀ : x₀ ∈ D.carrier := h₀ ▸ hγD _
  have hxD₁ : x₁ ∈ D.carrier := h₁ ▸ hγD _
  have hγU : ∀ q, γ q ∈ U := fun q => hDU (hγD q)
  have hγD' : ∀ q, L.ϕ (γ q) ∈ D'.carrier := fun q => hD' _ (hγD q)
  have hϕγ := L.isScSmoothMap_comp_or hγ hγU
  have hmem : ∀ w : D.carrier, w ∈ L.domSet D D' := fun w => ⟨hDU w.2, hD' _ w.2⟩
  have hdom : L.domSet D D' = univ := eq_univ_of_forall hmem
  set M := (L.domIso D D').ofEq hdom rfl with hM
  have hfD := L.sec_eqOn_domIso hf.isScSmooth.1 hf'.isScSmooth.1 hfL D D'
  have hfM : EqOn (D.sec f hf.isScSmooth.1) (M.Ψ ∘ D'.sec f' hf'.isScSmooth.1 ∘ M.ϕ) univ :=
    fun w _ => hfD (hmem w)
  -- the statement for `M`, with general endpoints and a general path in `D'`
  have key : ∀ (γ' : (Fin 1 → ℝ) → D'.carrier) (_ : γ' = fun q => M.ϕ (D.liftPath γ hγD q))
      (hγ' : (rnPolyfold 1).IsScSmoothMap (PX'.restrictOpen D'.isOpen) γ')
      (a₀ a₁ : D.carrier) (k₀ : D.liftPath γ hγD (pt1 0) = a₀)
      (k₁ : D.liftPath γ hγD (pt1 1) = a₁)
      (has₀ : a₀ ∈ (PX.restrictOpen D.isOpen).smoothSet)
      (has₁ : a₁ ∈ (PX.restrictOpen D.isOpen).smoothSet)
      (y₀ y₁ : D'.carrier) (e₀ : M.ϕ a₀ = y₀) (e₁ : M.ϕ a₁ = y₁)
      (k₀' : γ' (pt1 0) = y₀) (k₁' : γ' (pt1 1) = y₁)
      (hy₀ : y₀ ∈ (PX'.restrictOpen D'.isOpen).smoothSet)
      (hy₁ : y₁ ∈ (PX'.restrictOpen D'.isOpen).smoothSet),
      (M.orxViaAt (D.isFredholm hf).toIsScFredholmSection
        (D'.isFredholm hf').toIsScFredholmSection hfM D.hasSections D'.hasSections
        (mem_univ a₀) has₀ e₀).trans ((D.transport hX hf).transport (D.liftPath γ hγD)
          (D.isScSmoothMap_liftPath hγ hγD) k₀ k₁ has₀ has₁) =
      ((D'.transport hX' hf').transport γ' hγ' k₀' k₁' hy₀ hy₁).trans
        (M.orxViaAt (D.isFredholm hf).toIsScFredholmSection
          (D'.isFredholm hf').toIsScFredholmSection hfM D.hasSections D'.hasSections
          (mem_univ a₁) has₁ e₁) := by
    rintro γ' rfl hγ' a₀ a₁ k₀ k₁ has₀ has₁ y₀ y₁ rfl rfl k₀' k₁' hy₀ hy₁
    exact M.orxVia_comm_of_chart (D.isTame hX) D.exists_chart_univ (D.isFredholm hf)
      D.hasSections (D'.isTame hX') D'.exists_chart_univ (D'.isFredholm hf') D'.hasSections hfM
      (D.isScSmoothMap_liftPath hγ hγD) k₀ k₁ has₀ has₁
  have hpath : D'.liftPath (fun q => L.ϕ (γ q)) hγD' = fun q => M.ϕ (D.liftPath γ hγD q) :=
    funext fun q => (domIso_ϕ_of_mem (hmem (D.liftPath γ hγD q))).symm
  have hc := key _ hpath (D'.isScSmoothMap_liftPath hϕγ hγD') ⟨x₀, hxD₀⟩ ⟨x₁, hxD₁⟩
    (Subtype.ext h₀) (Subtype.ext h₁) (StrongBundle.Dom.mem_smoothSet hxD₀ hs₀)
    (StrongBundle.Dom.mem_smoothSet hxD₁ hs₁) ⟨L.ϕ x₀, hD' _ hxD₀⟩ ⟨L.ϕ x₁, hD' _ hxD₁⟩
    (L.domIso_ϕ_mk hx₀ rfl hxD₀ (hD' _ hxD₀)) (L.domIso_ϕ_mk hx₁ rfl hxD₁ (hD' _ hxD₁))
    (Subtype.ext (congrArg L.ϕ h₀)) (Subtype.ext (congrArg L.ϕ h₁))
    (StrongBundle.Dom.mem_smoothSet (hD' _ hxD₀) hs₀')
    (StrongBundle.Dom.mem_smoothSet (hD' _ hxD₁) hs₁')
  have hG : ∀ a : D.carrier, GermEq (L.domIso D D') M a := fun a =>
    ⟨⟨univ, isOpen_univ, mem_univ a, fun w _ => hmem w, subset_rfl, fun _ _ => rfl,
      fun _ _ => rfl⟩⟩
  have eG₀ : L.orDom hf hf' hfL D D' hx₀ rfl hxD₀ (hD' _ hxD₀) hs₀ hs₀' =
      M.orxViaAt (D.isFredholm hf).toIsScFredholmSection
        (D'.isFredholm hf').toIsScFredholmSection hfM D.hasSections D'.hasSections
        (mem_univ (⟨x₀, hxD₀⟩ : D.carrier)) (StrongBundle.Dom.mem_smoothSet hxD₀ hs₀)
        (L.domIso_ϕ_mk hx₀ rfl hxD₀ (hD' _ hxD₀)) :=
    orxViaAt_germ _ _ _ _ _ _ _ _ _ _ _ (hG _)
  have eG₁ : L.orDom hf hf' hfL D D' hx₁ rfl hxD₁ (hD' _ hxD₁) hs₁ hs₁' =
      M.orxViaAt (D.isFredholm hf).toIsScFredholmSection
        (D'.isFredholm hf').toIsScFredholmSection hfM D.hasSections D'.hasSections
        (mem_univ (⟨x₁, hxD₁⟩ : D.carrier)) (StrongBundle.Dom.mem_smoothSet hxD₁ hs₁)
        (L.domIso_ϕ_mk hx₁ rfl hxD₁ (hD' _ hxD₁)) :=
    orxViaAt_germ _ _ _ _ _ _ _ _ _ _ _ (hG _)
  have hc' := (trans_congr_left eG₀ _).trans (hc.trans (trans_congr_right _ eG₁.symm))
  have eT := orLocalTransportLoc_transport_eq hX hf D hγ hγD h₀ h₁ hs₀ hs₁
  have eT' := orLocalTransportLoc_transport_eq hX' hf' D' hϕγ hγD' (congrArg L.ϕ h₀)
    (congrArg L.ϕ h₁) hs₀' hs₁'
  have t₀ := L.orDom_toLoc hf hf' hfL D D' hx₀ rfl hxD₀ (hD' _ hxD₀) hs₀ hs₀'
  have t₁ := L.orDom_toLoc hf hf' hfL D D' hx₁ rfl hxD₁ (hD' _ hxD₁) hs₁ hs₁'
  exact (trans_congr_right _ eT).trans ((conj_comm_of_comm t₀ t₁ hc').trans
    (trans_congr_left eT'.symm _))

/-! ### All paths -/

/-- **The maps of orientations of a local strong bundle isomorphism commute with the
propagation of orientations** (Theorem 12.5.3, last sentence, for paths): for an sc-smooth path
`γ` in `U` from `x₀` to `x₁`, `orLoc` at `x₀` followed by the transport of `f` along `γ` is the
transport of `f'` along `ϕ ∘ γ` followed by `orLoc` at `x₁`. -/
theorem orLoc_comm (hX : PX.IsTame) (hX' : PX'.IsTame) (hf : B.IsScFredholmSectionTame f)
    (hf' : B'.IsScFredholmSectionTame f') (hfL : EqOn f (L.Ψ ∘ f' ∘ L.ϕ) U)
    {γ : (Fin 1 → ℝ) → X} (hγ : (rnPolyfold 1).IsScSmoothMap PX γ) (hγU : ∀ q, γ q ∈ U)
    {x₀ x₁ : X} (h₀ : γ (pt1 0) = x₀) (h₁ : γ (pt1 1) = x₁) (hx₀ : x₀ ∈ U) (hx₁ : x₁ ∈ U)
    (hs₀ : x₀ ∈ PX.smoothSet) (hs₁ : x₁ ∈ PX.smoothSet) (hs₀' : L.ϕ x₀ ∈ PX'.smoothSet)
    (hs₁' : L.ϕ x₁ ∈ PX'.smoothSet) :
    (L.orLoc hf hf' hfL hx₀ rfl hs₀ hs₀').trans
        ((orLocalTransportLoc hX hf).transport γ hγ h₀ h₁ hs₀ hs₁) =
      ((orLocalTransportLoc hX' hf').transport (fun q => L.ϕ (γ q))
        (L.isScSmoothMap_comp_or hγ hγU) (congrArg L.ϕ h₀) (congrArg L.ϕ h₁) hs₀' hs₁').trans
        (L.orLoc hf hf' hfL hx₁ rfl hs₁ hs₁') := by
  refine LocalTransport.scPath_induction (PX := PX) (fun γ => ∀ q, γ q ∈ U)
    (fun γ => ∀ (hγ : (rnPolyfold 1).IsScSmoothMap PX γ) (hγU : ∀ q, γ q ∈ U) {x₀ x₁ : X}
      (h₀ : γ (pt1 0) = x₀) (h₁ : γ (pt1 1) = x₁) (hx₀ : x₀ ∈ U) (hx₁ : x₁ ∈ U)
      (hs₀ : x₀ ∈ PX.smoothSet) (hs₁ : x₁ ∈ PX.smoothSet) (hs₀' : L.ϕ x₀ ∈ PX'.smoothSet)
      (hs₁' : L.ϕ x₁ ∈ PX'.smoothSet),
      (L.orLoc hf hf' hfL hx₀ rfl hs₀ hs₀').trans
          ((orLocalTransportLoc hX hf).transport γ hγ h₀ h₁ hs₀ hs₁) =
        ((orLocalTransportLoc hX' hf').transport (fun q => L.ϕ (γ q))
          (L.isScSmoothMap_comp_or hγ hγU) (congrArg L.ϕ h₀) (congrArg L.ϕ h₁) hs₀'
          hs₁').trans (L.orLoc hf hf' hfL hx₁ rfl hs₁ hs₁'))
    (fun γ _ hQ q => hQ _) (fun γ _ hQ q => hQ _) ?_ ?_ hγ hγU hγ hγU h₀ h₁ hx₀ hx₁ hs₀ hs₁
    hs₀' hs₁'
  · intro γ _ _ hl hr hγ hγU x₀ x₁ h₀ h₁ hx₀ hx₁ hs₀ hs₁ hs₀' hs₁'
    have hxm : γ (pt1 (1 / 2)) ∈ U := hγU _
    have hsm := mem_smoothSet_of_isScSmoothMap hγ (pt1 (1 / 2))
    have hsm' : L.ϕ (γ (pt1 (1 / 2))) ∈ PX'.smoothSet := (L.mem_smoothSet_iff hxm).1 hsm
    have Hl := hl (isScSmoothMap_leftHalf hγ) (fun _ => hγU _) (leftHalf_zero.trans h₀)
      (leftHalf_one.trans rfl) hx₀ hxm hs₀ hsm hs₀' hsm'
    have Hr := hr (isScSmoothMap_rightHalf hγ) (fun _ => hγU _) (rightHalf_zero.trans rfl)
      (rightHalf_one.trans h₁) hxm hx₁ hsm hs₁ hsm' hs₁'
    rw [(orLocalTransportLoc hX hf).transport_halves hγ h₀ h₁ rfl hs₀ hs₁ hsm,
      (orLocalTransportLoc hX' hf').transport_halves (L.isScSmoothMap_comp_or hγ hγU)
        (congrArg L.ϕ h₀) (congrArg L.ϕ h₁) rfl hs₀' hs₁' hsm',
      ← Equiv.trans_assoc, Hl, Equiv.trans_assoc, Hr, ← Equiv.trans_assoc]
    rfl
  · intro γ hγ hQ t _
    have ha : γ (pt1 t) ∈ U := hQ _
    have hW : IsOpen (U ∩ L.ϕ ⁻¹' (B'.domAt (L.ϕ (γ (pt1 t)))).carrier) :=
      L.base.isScSmoothOn.continuousOn.isOpen_inter_preimage L.isOpen_U
        (B'.domAt (L.ϕ (γ (pt1 t)))).isOpen
    set D := (B.domAt (γ (pt1 t))).restrict hW
      ⟨γ (pt1 t), B.mem_domAt _, ha, B'.mem_domAt _⟩ with hD
    refine ⟨D.carrier, D.isOpen, ⟨B.mem_domAt _, ha, B'.mem_domAt _⟩, ?_⟩
    intro γ' _ _ hγ'V hγ' hγ'U x₀ x₁ h₀ h₁ hx₀ hx₁ hs₀ hs₁ hs₀' hs₁'
    have e1 := (orLocalTransportLoc hX hf).transport_reparam hγ' Real.smoothTransition.contDiff
      Real.smoothTransition.zero Real.smoothTransition.one h₀ h₁ hs₀ hs₁
    have e2 := (orLocalTransportLoc hX' hf').transport_reparam
      (L.isScSmoothMap_comp_or hγ' hγ'U) Real.smoothTransition.contDiff
      Real.smoothTransition.zero Real.smoothTransition.one (congrArg L.ϕ h₀) (congrArg L.ϕ h₁)
      hs₀' hs₁'
    have hc := L.orLoc_comm_of_dom hX hX' hf hf' hfL D (B'.domAt (L.ϕ (γ (pt1 t))))
      (fun y hy => hy.2.1) (fun y hy => hy.2.2) (isScSmoothMap_smoothTransPath_or hγ')
      (smoothTransPath_or_mem hγ'V)
      ((congrArg (fun t => γ' (pt1 t)) Real.smoothTransition.zero).trans h₀)
      ((congrArg (fun t => γ' (pt1 t)) Real.smoothTransition.one).trans h₁) hx₀ hx₁ hs₀ hs₁
      hs₀' hs₁'
    exact (trans_congr_right _ e1.symm).trans (hc.trans (trans_congr_left e2 _))

/-! ### Continuous families of orientations -/

open Classical in
/-- **The family of orientations carried by a local strong bundle isomorphism**: for a family
`o'` of orientations of `f'`, the family `a ↦ orLoc (o'_{ϕ(a)})` over `U` (outside `U` an
arbitrary value). -/
def pullLoc (hf : B.IsScFredholmSectionTame f) (hf' : B'.IsScFredholmSectionTame f')
    (hfL : EqOn f (L.Ψ ∘ f' ∘ L.ϕ) U) (o' : ∀ y (hy : y ∈ PX'.smoothSet), OrxLoc hf' y hy)
    (a : X) (has : a ∈ PX.smoothSet) : OrxLoc hf a has :=
  if ha : a ∈ U then
    L.orLoc hf hf' hfL ha rfl has ((L.mem_smoothSet_iff ha).1 has)
      (o' (L.ϕ a) ((L.mem_smoothSet_iff ha).1 has))
  else (exists_two_orxLoc hf has).choose

theorem pullLoc_of_mem (hf : B.IsScFredholmSectionTame f) (hf' : B'.IsScFredholmSectionTame f')
    (hfL : EqOn f (L.Ψ ∘ f' ∘ L.ϕ) U) (o' : ∀ y (hy : y ∈ PX'.smoothSet), OrxLoc hf' y hy)
    {a : X} (ha : a ∈ U) (has : a ∈ PX.smoothSet) (has' : L.ϕ a ∈ PX'.smoothSet) :
    L.pullLoc hf hf' hfL o' a has = L.orLoc hf hf' hfL ha rfl has has' (o' (L.ϕ a) has') := by
  rw [pullLoc, dif_pos ha]

/-- **The family carried from a continuous family is continuous** (Theorem 12.5.3, last
sentence): if `o'` is a continuous family of orientations of `f'` over an open `V'`, then
`a ↦ orLoc (o'_{ϕ(a)})` is a continuous family of orientations of `f` over `U ∩ ϕ⁻¹(V')`. -/
theorem isContOn_pullLoc (hX : PX.IsTame) (hX' : PX'.IsTame)
    (hf : B.IsScFredholmSectionTame f) (hf' : B'.IsScFredholmSectionTame f')
    (hfL : EqOn f (L.Ψ ∘ f' ∘ L.ϕ) U) {V' : Set X'}
    {o' : ∀ y (hy : y ∈ PX'.smoothSet), OrxLoc hf' y hy}
    (h : (orLocalTransportLoc hX' hf').IsContOn V' o') :
    (orLocalTransportLoc hX hf).IsContOn (U ∩ L.ϕ ⁻¹' V') (L.pullLoc hf hf' hfL o') := by
  refine ⟨L.base.isScSmoothOn.continuousOn.isOpen_inter_preimage L.isOpen_U h.1, ?_⟩
  intro γ hγ hγV x₀ x₁ h₀ h₁ hs₀ hs₁
  have hγ' := isScSmoothMap_smoothTransPath_or hγ
  have hγ'V : ∀ q, smoothTransPath_or γ q ∈ U ∩ L.ϕ ⁻¹' V' := smoothTransPath_or_mem hγV
  have hγ'U : ∀ q, smoothTransPath_or γ q ∈ U := fun q => (hγ'V q).1
  have h₀' : smoothTransPath_or γ (pt1 0) = x₀ :=
    (congrArg (fun t => γ (pt1 t)) Real.smoothTransition.zero).trans h₀
  have h₁' : smoothTransPath_or γ (pt1 1) = x₁ :=
    (congrArg (fun t => γ (pt1 t)) Real.smoothTransition.one).trans h₁
  have hx₀ : x₀ ∈ U := h₀' ▸ hγ'U _
  have hx₁ : x₁ ∈ U := h₁' ▸ hγ'U _
  have hs₀' := (L.mem_smoothSet_iff hx₀).1 hs₀
  have hs₁' := (L.mem_smoothSet_iff hx₁).1 hs₁
  have er := (orLocalTransportLoc hX hf).transport_reparam hγ Real.smoothTransition.contDiff
    Real.smoothTransition.zero Real.smoothTransition.one h₀ h₁ hs₀ hs₁
  have hc := DFunLike.congr_fun (L.orLoc_comm hX hX' hf hf' hfL hγ' hγ'U h₀' h₁' hx₀ hx₁ hs₀
    hs₁ hs₀' hs₁') (o' (L.ϕ x₀) hs₀')
  simp only [Equiv.trans_apply] at hc
  have hcont := h.2 (fun q => L.ϕ (smoothTransPath_or γ q)) (L.isScSmoothMap_comp_or hγ' hγ'U)
    (fun t _ => (hγ'V _).2) (congrArg L.ϕ h₀') (congrArg L.ϕ h₁') hs₀' hs₁'
  rw [L.pullLoc_of_mem hf hf' hfL o' hx₀ hs₀ hs₀', L.pullLoc_of_mem hf hf' hfL o' hx₁ hs₁ hs₁']
  exact (DFunLike.congr_fun er.symm _).trans (hc.trans (congrArg _ hcont))

/-- **A family is continuous where the family it carries is**: if `a ↦ orLoc (o'_{ϕ(a)})` is a
continuous family of orientations of `f` over `U ∩ ϕ⁻¹(V')`, then `o'` is a continuous family
of orientations of `f'` over `U' ∩ V'`.  Paths in `U' ∩ V'` are first reparametrized so that
they take all their values in `U'`, and then carried back by `ϕ⁻¹`. -/
theorem isContOn_of_pullLoc (hX : PX.IsTame) (hX' : PX'.IsTame)
    (hf : B.IsScFredholmSectionTame f) (hf' : B'.IsScFredholmSectionTame f')
    (hfL : EqOn f (L.Ψ ∘ f' ∘ L.ϕ) U) {V' : Set X'} (hV' : IsOpen V')
    {o' : ∀ y (hy : y ∈ PX'.smoothSet), OrxLoc hf' y hy}
    (h : (orLocalTransportLoc hX hf).IsContOn (U ∩ L.ϕ ⁻¹' V') (L.pullLoc hf hf' hfL o')) :
    (orLocalTransportLoc hX' hf').IsContOn (U' ∩ V') o' := by
  refine ⟨L.isOpen_U'.inter hV', ?_⟩
  intro γ' hγ' hγ'V x₀' x₁' h₀' h₁' hs₀' hs₁'
  have hx₀' : x₀' ∈ U' := h₀' ▸ (hγ'V 0 (left_mem_Icc.2 zero_le_one)).1
  have hx₁' : x₁' ∈ U' := h₁' ▸ (hγ'V 1 (right_mem_Icc.2 zero_le_one)).1
  obtain ⟨x₀, rfl⟩ : ∃ x₀, L.ϕ x₀ = x₀' := ⟨L.g x₀', L.base.right_inv _ hx₀'⟩
  obtain ⟨x₁, rfl⟩ : ∃ x₁, L.ϕ x₁ = x₁' := ⟨L.g x₁', L.base.right_inv _ hx₁'⟩
  have hγ'' := isScSmoothMap_smoothTransPath_or hγ'
  have hγ''U : ∀ q, smoothTransPath_or γ' q ∈ U' ∩ V' := smoothTransPath_or_mem hγ'V
  set γ : (Fin 1 → ℝ) → X := fun q => L.g (smoothTransPath_or γ' q) with hγdef
  have hγ : (rnPolyfold 1).IsScSmoothMap PX γ :=
    L.base.isScSmoothOn_inv.comp hγ'' fun q _ => (hγ''U q).1
  have hγU : ∀ q, γ q ∈ U := fun q => L.base.mapsTo_inv (hγ''U q).1
  have hϕγ : ∀ q, L.ϕ (γ q) = smoothTransPath_or γ' q := fun q =>
    L.base.right_inv _ (hγ''U q).1
  have h₀'' : smoothTransPath_or γ' (pt1 0) = L.ϕ x₀ :=
    (congrArg (fun t => γ' (pt1 t)) Real.smoothTransition.zero).trans h₀'
  have h₁'' : smoothTransPath_or γ' (pt1 1) = L.ϕ x₁ :=
    (congrArg (fun t => γ' (pt1 t)) Real.smoothTransition.one).trans h₁'
  -- the endpoints of `γ`; they are carried to the endpoints of `γ'`
  set y₀ : X := γ (pt1 0) with hy₀
  set y₁ : X := γ (pt1 1) with hy₁
  have hy₀U : y₀ ∈ U := hγU _
  have hy₁U : y₁ ∈ U := hγU _
  have ey₀ : L.ϕ y₀ = L.ϕ x₀ := (hϕγ _).trans h₀''
  have ey₁ : L.ϕ y₁ = L.ϕ x₁ := (hϕγ _).trans h₁''
  have hsy₀' : L.ϕ y₀ ∈ PX'.smoothSet := ey₀ ▸ hs₀'
  have hsy₁' : L.ϕ y₁ ∈ PX'.smoothSet := ey₁ ▸ hs₁'
  have hsy₀ : y₀ ∈ PX.smoothSet := (L.mem_smoothSet_iff hy₀U).2 hsy₀'
  have hsy₁ : y₁ ∈ PX.smoothSet := (L.mem_smoothSet_iff hy₁U).2 hsy₁'
  have e1 := (orLocalTransportLoc hX' hf').transport_reparam hγ'
    Real.smoothTransition.contDiff Real.smoothTransition.zero Real.smoothTransition.one h₀' h₁'
    hs₀' hs₁'
  have e2 := (orLocalTransportLoc hX' hf').transport_congr
    (γ := fun s => γ' (pt1 (Real.smoothTransition (s 0)))) (γ' := fun q => L.ϕ (γ q))
    (fun t _ => (hϕγ (pt1 t)).symm) (isScSmoothMap_reparam hγ' Real.smoothTransition.contDiff)
    (L.isScSmoothMap_comp_or hγ hγU) h₀'' h₁'' (ey₀.symm ▸ rfl : L.ϕ (γ (pt1 0)) = L.ϕ x₀)
    (ey₁.symm ▸ rfl : L.ϕ (γ (pt1 1)) = L.ϕ x₁) hs₀' hs₁'
  -- the statement with the endpoints `ϕ(y₀)`, `ϕ(y₁)` generalized
  have key : ∀ (z₀ z₁ : X') (k₀ : L.ϕ y₀ = z₀) (k₁ : L.ϕ y₁ = z₁) (hz₀ : z₀ ∈ PX'.smoothSet)
      (hz₁ : z₁ ∈ PX'.smoothSet),
      (orLocalTransportLoc hX' hf').transport (fun q => L.ϕ (γ q))
        (L.isScSmoothMap_comp_or hγ hγU) k₀ k₁ hz₀ hz₁ (o' z₀ hz₀) = o' z₁ hz₁ := by
    rintro z₀ z₁ rfl rfl hz₀ hz₁
    have hc := DFunLike.congr_fun (L.orLoc_comm hX hX' hf hf' hfL hγ hγU rfl rfl hy₀U hy₁U
      hsy₀ hsy₁ hz₀ hz₁) (o' (L.ϕ y₀) hz₀)
    simp only [Equiv.trans_apply] at hc
    have hcont := h.2 γ hγ (fun t _ => ⟨hγU _, by rw [mem_preimage, hϕγ]; exact (hγ''U _).2⟩)
      rfl rfl hsy₀ hsy₁
    rw [L.pullLoc_of_mem hf hf' hfL o' hy₀U hsy₀ hz₀,
      L.pullLoc_of_mem hf hf' hfL o' hy₁U hsy₁ hz₁] at hcont
    exact (L.orLoc hf hf' hfL hy₁U rfl hsy₁ hz₁).injective (hc.symm.trans hcont)
  rw [← e1, e2]
  exact key _ _ _ _ hs₀' hs₁'

end StrongBundle.LocalIso

end Polyfold
