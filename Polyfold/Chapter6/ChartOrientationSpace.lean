import Polyfold.Chapter6.ChartOrientationFunctor
import Polyfold.Chapter6.OrientationMainClean

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part I, §6.6,
pp. 227–230: **Theorem 6.6.13** (the functor `Γ_f`) and **Theorem 6.6.17** (the topology of the
orientation space `O_f`) for a strong bundle with a chart over the whole base, without sc-smooth
bump functions.

# The orientation space in a chart over the whole base

## The text, paraphrased

(Theorem 6.6.17) The set `O_f = ⋃ₓ Or_x^f` over the smooth points has exactly one Hausdorff
topology for which (1) the projection `π_f : O_f → X_∞` is a local homeomorphism, (2) every smooth
point has an open neighbourhood over whose smooth part there are precisely two continuous
sections, and (3) the local propagation along sc-smooth paths is continuous.  The proofs of
§6.6 use the local sc⁺-sections of Proposition 6.6.3, written in a chart "assuming `X = U`".

## What is formalized

With `hch : ∃ c ∈ B.atlas.charts, c.φ.source = univ` (a chart of the atlas over the whole base)
in place of sc-smooth bump functions:

* `isPropagationContinuous_orTopology_of_chart`, `eventually_eq_orSec_of_continuousOn_of_chart`,
  `eq_orTopology_of_of_chart`, `existsUnique_orientationTopology_of_chart`,
  `theorem_6_6_17_hyp_of_chart`: the section `Existence` of `OrientationSpace.lean` for the
  transport data `orLocalTransportOfChart`.
* `theorem_6_6_13_of_chart`: **Theorem 6.6.13**, existence and uniqueness of the functor `Γ_f`
  with property (∗).
* `theorem_6_6_17_of_chart`: **Theorem 6.6.17**, exactly one topology on `O_f` is Hausdorff with
  (1), (2), (3).

The hypothesis `hch` holds for the restriction of every strong bundle to the base domain of a
chart of its atlas (`ChartDomainOrientation.lean`).
-/

set_option maxSynthPendingDepth 3

open Set Filter Topology Function CategoryTheory
open scoped ContDiff

noncomputable section

namespace Polyfold

universe u v

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle PX P}
  {f : X → Y}

/-! ### The topology of `O_f` -/

section Existence

variable [∀ n : ℕ, ParacompactSpace ((Fin n → ℝ) × X)]
  [∀ n : ℕ, ParacompactSpace (pullbackSpace P (Prod.snd : (Fin n → ℝ) × X → X))]
  [∀ k n : ℕ, ParacompactSpace ((Fin k → ℝ) × ((Fin n → ℝ) × X))]
  [∀ k n : ℕ, ParacompactSpace (pullbackSpace (pullbackProj P (Prod.snd : (Fin n → ℝ) × X → X))
    (Prod.snd : (Fin k → ℝ) × ((Fin n → ℝ) × X) → (Fin n → ℝ) × X))]

variable (hX : PX.IsTame) (hch : ∃ c ∈ B.atlas.charts, c.φ.source = univ)
  (hf : B.IsScFredholmSectionTame f)
  (hsec : B.HasScPlusSectionsThrough)

include hX hch hf hsec

/-- **Property (3)** (2021 Theorem 6.6.17) for the topology of `O_f`: near `t₀`, a continuous
section of `φ*O_f` stays in one set `{(y, o_y)}` of a continuous orientation `o`, which is carried
along the segments of `φ` by the transport. -/
theorem isPropagationContinuous_orTopology_of_chart :
    IsPropagationContinuous f hf.toIsScFredholmSection
      (orTopology (orLocalTransportOfChart hX hch hf hsec)) := by
  set L := orLocalTransportOfChart hX hch hf hsec with hL
  let _ : TopologicalSpace (OrSpace f hf.toIsScFredholmSection) := orTopology L
  intro φ hφ α hα hαs t₀
  obtain ⟨U, o, ho, ⟨U', hU', hUU'⟩, hp⟩ := exists_isContOrOn L (α t₀).1.2
  have hφc : Continuous φ := continuousOn_univ.1 hφ.continuousOn
  have hev1 : ∀ᶠ t in 𝓝 t₀, (α t).1.2 ∈ orBasic U o :=
    (continuous_snd.comp (continuous_subtype_val.comp hα)).continuousAt
      ((isOpen_orBasic ho).mem_nhds hp)
  have hαφ : ∀ t : unitInterval, φ (pt1 (t : ℝ)) = PX.smoothVal (α t).1.2.1 := fun t => by
    have := (α t).2
    change φ (pt1 (((α t).1.1 : unitInterval) : ℝ)) = PX.smoothVal (α t).1.2.1 at this
    rw [hαs] at this
    exact this
  have hφt₀ : φ (pt1 (t₀ : ℝ)) ∈ U := by rw [hαφ]; exact hp.1
  filter_upwards [hev1, eventually_segPath_mem hφc ho.1 hφt₀] with t ht hseg
  have h₀ : segPath φ t₀ t (pt1 0) = PX.smoothVal (α t₀).1.2.1 := by rw [segPath_zero, hαφ]
  have h₁ : segPath φ t₀ t (pt1 1) = PX.smoothVal (α t).1.2.1 := by rw [segPath_one, hαφ]
  refine ⟨U', hU', fun s hs => hUU' (hseg s hs), h₀, h₁, ?_⟩
  have hT := ho.2 _ (isScSmoothMap_segPath hφ t₀ t) hseg h₀ h₁ (PX.smoothVal_mem _)
    (PX.smoothVal_mem _)
  calc _ = L.transport _ (isScSmoothMap_segPath hφ t₀ t) h₀ h₁ (PX.smoothVal_mem _)
        (PX.smoothVal_mem _) (α t₀).1.2.2 := by
          rw [L.transport_eq_push hU' _ (fun s hs => hUU' (hseg s hs))]
          rfl
    _ = (α t).1.2.2 := by rw [hp.2, hT, ← ht.2]

/-- **Continuous local sections are the continuous orientations** (the core of uniqueness): for a
topology with property (3), a continuous section `s` over an open `N ⊆ X_∞` which agrees with a
continuous orientation `o` at `y₀` agrees with it near `y₀` (paths of
`eventually_exists_scPath_smoothLevel`, `continuous_smoothMk_comp`, and connectedness of
`[0, 1]`). -/
theorem eventually_eq_orSec_of_continuousOn_of_chart
    {t : TopologicalSpace (OrSpace f hf.toIsScFredholmSection)}
    (h3 : IsPropagationContinuous f hf.toIsScFredholmSection t) {U : Set X}
    {o : ∀ y (hy : y ∈ PX.smoothSet), Orx f hf.toIsScFredholmSection y hy}
    (ho : IsContOrOn (orLocalTransportOfChart hX hch hf hsec) U o) {N : Set PX.SmoothLevel}
    (hNo : IsOpen N) {s : PX.SmoothLevel → OrSpace f hf.toIsScFredholmSection}
    (hs : @ContinuousOn _ _ _ t s N) (hs1 : ∀ y ∈ N, (s y).1 = y) {y₀ : PX.SmoothLevel}
    (hy₀ : y₀ ∈ N) (hy₀U : PX.smoothVal y₀ ∈ U) (hsy₀ : s y₀ = orSec o y₀) :
    ∀ᶠ y in 𝓝 y₀, s y = orSec o y := by
  set L := orLocalTransportOfChart hX hch hf hsec with hL
  let := t
  have hN : N ∩ PX.smoothVal ⁻¹' U ∈ 𝓝 y₀ :=
    (hNo.inter (ho.1.preimage PX.continuous_smoothVal)).mem_nhds ⟨hy₀, hy₀U⟩
  filter_upwards [eventually_exists_scPath_smoothLevel y₀ hN] with y ⟨γ, hγ, hγ0, hγ1, hγN⟩
  set γ' : unitInterval → PX.SmoothLevel := fun τ =>
    PX.smoothMk (γ (pt1 (τ : ℝ))) (mem_smoothSet_of_isScSmoothMap hγ _) with hγ'def
  have hγ'c : Continuous γ' :=
    (continuous_smoothMk_comp hγ).comp (continuous_pt1.comp continuous_subtype_val)
  have hγ'N : ∀ τ, γ' τ ∈ N ∩ PX.smoothVal ⁻¹' U := fun τ => hγN _
  let α : unitInterval → OrPullback f hf.toIsScFredholmSection γ := fun τ =>
    ⟨(τ, s (γ' τ)), by
      change γ (pt1 (τ : ℝ)) = PX.smoothVal (s (γ' τ)).1
      rw [hs1 _ (hγ'N τ).1]
      rfl⟩
  have hαc : Continuous α :=
    (continuous_id.prodMk (hs.comp_continuous hγ'c fun τ => (hγ'N τ).1)).subtype_mk _
  have h3' := h3 γ hγ α hαc fun _ => rfl
  have hQiff : ∀ τ, s (γ' τ) = orSec o (γ' τ) ↔ (α τ).1.2.2 =
      o (PX.smoothVal (α τ).1.2.1) (PX.smoothVal_mem _) := fun τ =>
    eq_orSec_iff (hs1 _ (hγ'N τ).1)
  have hQ : ∀ τ₀, ∀ᶠ τ in 𝓝 τ₀,
      (s (γ' τ) = orSec o (γ' τ) ↔ s (γ' τ₀) = orSec o (γ' τ₀)) := by
    intro τ₀
    filter_upwards [h3' τ₀] with τ ⟨U'', hU'', hseg, h₀, h₁, hpush⟩
    have hsegU : ∀ r ∈ Icc (0 : ℝ) 1, segPath γ τ₀ τ (pt1 r) ∈ U := fun r _ => (hγN _).2
    have hT := ho.2 _ (isScSmoothMap_segPath hγ τ₀ τ) hsegU h₀ h₁ (PX.smoothVal_mem _)
      (PX.smoothVal_mem _)
    have hP : L.transport _ (isScSmoothMap_segPath hγ τ₀ τ) h₀ h₁ (PX.smoothVal_mem _)
        (PX.smoothVal_mem _) (α τ₀).1.2.2 = (α τ).1.2.2 := by
      rw [L.transport_eq_push hU'' _ hseg]
      exact hpush
    rw [hQiff τ, hQiff τ₀, ← hP, ← hT]
    exact (L.transport _ _ h₀ h₁ _ _).apply_eq_iff_eq
  have hopen : IsOpen {τ | s (γ' τ) = orSec o (γ' τ)} :=
    isOpen_iff_mem_nhds.2 fun τ₀ hτ₀ => (hQ τ₀).mono fun τ h => h.2 hτ₀
  have hclosed : IsOpen {τ | s (γ' τ) = orSec o (γ' τ)}ᶜ :=
    isOpen_iff_mem_nhds.2 fun τ₀ hτ₀ => (hQ τ₀).mono fun τ h hτ => hτ₀ (h.1 hτ)
  have hγ'0 : γ' 0 = y₀ := MPolyfold.smoothMk_eq hγ0
  have hγ'1 : γ' 1 = y := MPolyfold.smoothMk_eq hγ1
  have h0 : (0 : unitInterval) ∈ {τ | s (γ' τ) = orSec o (γ' τ)} := by
    change s (γ' 0) = orSec o (γ' 0)
    rw [hγ'0]; exact hsy₀
  rcases isClopen_iff.1 ⟨isOpen_compl_iff.1 hclosed, hopen⟩ with h | h
  · exact absurd (h ▸ h0) (notMem_empty _)
  · have h1 : (1 : unitInterval) ∈ {τ | s (γ' τ) = orSec o (γ' τ)} := by rw [h]; exact mem_univ _
    change s (γ' 1) = orSec o (γ' 1) at h1
    rwa [hγ'1] at h1

/-- **Uniqueness in 2021 Theorem 6.6.17**: a topology on `O_f` with properties (1) and (3) is the
topology `orTopology` (Hausdorffness and property (2) are not needed). -/
theorem eq_orTopology_of_of_chart {t : TopologicalSpace (OrSpace f hf.toIsScFredholmSection)}
    (h1 : @IsLocalHomeomorph _ _ t _ (orProj f hf.toIsScFredholmSection))
    (h3 : IsPropagationContinuous f hf.toIsScFredholmSection t) :
    t = orTopology (orLocalTransportOfChart hX hch hf hsec) := by
  set L := orLocalTransportOfChart hX hch hf hsec with hL
  have hsec' : ∀ (e : @OpenPartialHomeomorph _ _ t _), orProj f hf.toIsScFredholmSection = e →
      ∀ z ∈ e.target, (e.symm z).1 = z := fun e he z hz =>
    (congrFun he (e.symm z)).trans (e.right_inv hz)
  refine TopologicalSpace.ext (funext fun G => propext ⟨fun hG => ?_, fun hG => ?_⟩)
  · -- `t`-open sets are open
    intro U o ho
    refine isOpen_iff_mem_nhds.2 fun y hy => ?_
    obtain ⟨e, hpe, he⟩ := h1 (orSec o y)
    have hey : e (orSec o y) = y := (congrFun he _).symm
    have hyt : y ∈ e.target := hey ▸ e.map_source hpe
    have hsy : e.symm y = orSec o y := by
      conv_lhs => rw [← hey]
      exact e.left_inv hpe
    have hev := eventually_eq_orSec_of_continuousOn_of_chart hX hch hf hsec h3 ho e.open_target
      e.continuousOn_symm (hsec' e he) hyt hy.1 hsy
    have hev2 : ∀ᶠ z in 𝓝 y, e.symm z ∈ G :=
      (e.continuousOn_symm.continuousAt (e.open_target.mem_nhds hyt))
        (@IsOpen.mem_nhds _ t _ _ hG (hsy ▸ hy.2))
    filter_upwards [hev, hev2, (ho.1.preimage PX.continuous_smoothVal).mem_nhds hy.1]
      with z hz1 hz2 hz3
    exact ⟨hz3, hz1 ▸ hz2⟩
  · -- open sets are `t`-open
    let := t
    refine isOpen_iff_mem_nhds.2 fun p hp => ?_
    obtain ⟨e, hpe, he⟩ := h1 p
    obtain ⟨U, o, ho, -, hpo⟩ := exists_isContOrOn L p
    have hep : e p = p.1 := (congrFun he p).symm
    have hp1 : p.1 ∈ e.target := hep ▸ e.map_source hpe
    have hsp : e.symm p.1 = orSec o p.1 := by
      conv_lhs => rw [← hep]
      exact (e.left_inv hpe).trans (eq_orSec_of_mem_orBasic hpo)
    have hev := eventually_eq_orSec_of_continuousOn_of_chart hX hch hf hsec h3 ho e.open_target
      e.continuousOn_symm (hsec' e he) hp1 hpo.1 hsp
    have hmem : p.1 ∈ {y : PX.SmoothLevel | PX.smoothVal y ∈ U ∧ orSec o y ∈ G} :=
      ⟨hpo.1, (eq_orSec_of_mem_orBasic hpo) ▸ hp⟩
    obtain ⟨M, hMsub, hMo, hpM⟩ := mem_nhds_iff.1
      ((hev.and ((hG U o ho).mem_nhds hmem)).and (e.open_target.mem_nhds hp1))
    refine mem_nhds_iff.2 ⟨e.source ∩ e ⁻¹' M, fun q ⟨hq, hqM⟩ => ?_,
      e.isOpen_inter_preimage hMo, hpe, show e p ∈ M by rw [hep]; exact hpM⟩
    have h := hMsub hqM
    rw [← e.left_inv hq, h.1.1]
    exact h.1.2.2

/-- **2021 Theorem 6.6.17 without property (2)**: there is exactly one Hausdorff topology on `O_f`
with properties (1) and (3) (by `eq_orTopology_of_of_chart`, even exactly one with (1) and (3)). -/
theorem existsUnique_orientationTopology_of_chart :
    ∃! t : TopologicalSpace (OrSpace f hf.toIsScFredholmSection), @T2Space _ t ∧
      @IsLocalHomeomorph _ _ t _ (orProj f hf.toIsScFredholmSection) ∧
      IsPropagationContinuous f hf.toIsScFredholmSection t :=
  ⟨orTopology (orLocalTransportOfChart hX hch hf hsec),
    ⟨t2Space_orTopology _, isLocalHomeomorph_orProj _,
      isPropagationContinuous_orTopology_of_chart hX hch hf hsec⟩,
    fun _ ht => eq_orTopology_of_of_chart hX hch hf hsec ht.2.1 ht.2.2⟩

/-- **2021 Theorem 6.6.17**, p. 275 (new in the 2021 edition; the 2017 text has no topology on
`O_f`): there is exactly one topology on `O_f` which is Hausdorff and has properties
(1), (2) and (3); under the hypothesis `HasConnectedSmoothNbhds` (used for (2) only). -/
theorem theorem_6_6_17_hyp_of_chart (hC : PX.HasConnectedSmoothNbhds) :
    ∃! t : TopologicalSpace (OrSpace f hf.toIsScFredholmSection),
      IsOrientationTopology f hf.toIsScFredholmSection t :=
  ⟨orTopology (orLocalTransportOfChart hX hch hf hsec),
    ⟨t2Space_orTopology _, isLocalHomeomorph_orProj _,
      hasTwoContSections_orTopology _ (fun _ hy => exists_two_orx _ hy hsec) hC,
      isPropagationContinuous_orTopology_of_chart hX hch hf hsec⟩,
    fun _ ht => eq_orTopology_of_of_chart hX hch hf hsec ht.isLocalHomeomorph ht.propagation⟩

end Existence

/-! ### Theorems 6.6.13 and 6.6.17 -/

/-- **Theorem 6.6.13, chart over the whole base**: for an sc-Fredholm section `f` with tame germ
data of a strong bundle over a tame M-polyfold, with a chart of the atlas over the whole base,
there is a unique family of maps `Γ_f([φ]) : Or_x^f ≃ Or_y^f` on the morphisms `[φ] : x ⟶ y` of
`PX` which is a functor and has property (∗). -/
theorem theorem_6_6_13_of_chart (hX : PX.IsTame)
    (hch : ∃ c ∈ B.atlas.charts, c.φ.source = univ) (hf : B.IsScFredholmSectionTame f) :
    haveI := paracompactSpace_rn_prod PX
    haveI := paracompactSpace_rn_pullback B
    ∃! G : ∀ x y : PathCat PX, (x ⟶ y) →
        (Orx f hf.toIsScFredholmSection x.pt x.smooth ≃
          Orx f hf.toIsScFredholmSection y.pt y.smooth),
      (∀ x, G x x (𝟙 x) = Equiv.refl _) ∧
      (∀ (x y z : PathCat PX) (a : x ⟶ y) (b : y ⟶ z),
        G x z (a ≫ b) = (G x y a).trans (G y z b)) ∧
      IsStarProperty f hf.toIsScFredholmSection G := by
  have := paracompactSpace_rn_prod PX
  have := paracompactSpace_rn_pullback B
  have := paracompactSpace_rn_rn_prod PX
  have := paracompactSpace_rn_rn_pullback B
  exact theorem_6_6_13_hyp_of_chart hX hch hf
    (hch.elim fun _ h => StrongBundle.hasScPlusSectionsThrough_of_chart h.1 h.2)

/-- **Theorem 6.6.17, chart over the whole base**: for an sc-Fredholm section `f` with tame germ
data of a strong bundle over a tame M-polyfold, with a chart of the atlas over the whole base,
there is exactly one topology on `O_f` which is Hausdorff and has properties (1), (2) and (3). -/
theorem theorem_6_6_17_of_chart (hX : PX.IsTame)
    (hch : ∃ c ∈ B.atlas.charts, c.φ.source = univ) (hf : B.IsScFredholmSectionTame f) :
    haveI := paracompactSpace_rn_prod PX
    haveI := paracompactSpace_rn_pullback B
    ∃! t : TopologicalSpace (OrSpace f hf.toIsScFredholmSection),
      IsOrientationTopology f hf.toIsScFredholmSection t := by
  have := paracompactSpace_rn_prod PX
  have := paracompactSpace_rn_pullback B
  have := paracompactSpace_rn_rn_prod PX
  have := paracompactSpace_rn_rn_pullback B
  exact theorem_6_6_17_hyp_of_chart hX hch hf
    (hch.elim fun _ h => StrongBundle.hasScPlusSectionsThrough_of_chart h.1 h.2)
    PX.hasConnectedSmoothNbhds

end Polyfold
