import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V3_5

/-! Round trip for V3_5 (Definition 3.3: sc-smooth section germs).  Refreshed 2026-11-02 (HEAD,
germ reading).

`A` is the conjunction of the types of the listed theorems
`Polyfold.StrongBundle.IsScSmoothSection.isScSmoothSectionGerm` (an sc-smooth section is an
sc-smooth section germ at every smooth point with a centred chart),
`Polyfold.StrongBundle.isChart_congr` (the compatible strong bundle charts depend only on the
equivalence class of the atlas) and `Polyfold.exists_isScSmoothGerm_not_isScSmooth` (an sc-smooth
germ on shrinking levels which is sc-smooth on no open neighbourhood), universes instantiated at
`0` (B lives in `Type`).  `StrongBundle.IsScSmoothSectionGerm`, `StrongBundle.IsChart`,
`StrongBundleChart.principal` are definitions (vocabulary).

* The definitions now agree.  Since 2026-11-02 the project's `IsScSmoothSectionGerm` asks
  `f̂ ∘ r` to be sc-smooth on SOME sc-germ of neighbourhoods `G` with `G₀ ⊆ U` (the text's germ
  reading), exactly as B does.  The remaining difference is that B (the text) also asks `f` to be a
  continuous section on an open `V ∋ x₀` containing `φ⁻¹(r(G₀))`; this is automatic:
  - project ⇒ text (`proj_to_B`): `f̂ ∘ r` is continuous on `G₀` (level `0` of the germ), hence
    `f̂` on `O ∩ G₀` (`r = id` on `O`), hence `f = Φ⁻¹(φ, f̂ ∘ φ)` on the open
    `V = φ⁻¹(G₀) ∩ dom φ`; the germ is shrunk to `G' = {u ∈ G | r(u) ∈ G}`
    (`ScNbhdGerm.preimage` along the sc⁰-germ `r`), so that `φ⁻¹(r(G'₀)) ⊆ V`, and sc-smoothness
    passes to `G'` (`IsScSmoothGerm.mono`).
  - text ⇒ project (`B_to_proj`): forget `V` and the continuity; `0 ∈ U` from `0 ∈ G₀ ⊆ U`.
  So `B` (the `↔` for sections) is proved outright, and `A → B` holds without using `A`.
* `B → A` is proved outright (A is re-proved from non-banned project lemmas; B is not used): the
  regularity bridge as in the project, `isChart_congr` from `isChart_iff_exists_equiv`, and the
  example from `GermVsChart`. -/

namespace RoundTrip.V3_5
open Polyfold Set

/-- The project's statement (universes at `0`). -/
def A : Prop :=
  (type_of% @Polyfold.StrongBundle.IsScSmoothSection.isScSmoothSectionGerm.{0, 0}) ∧
  (type_of% @Polyfold.StrongBundle.isChart_congr.{0, 0}) ∧
  (type_of% @Polyfold.exists_isScSmoothGerm_not_isScSmooth)

theorem A_holds : A :=
  ⟨@Polyfold.StrongBundle.IsScSmoothSection.isScSmoothSectionGerm.{0, 0},
    @Polyfold.StrongBundle.isChart_congr.{0, 0}, Polyfold.exists_isScSmoothGerm_not_isScSmooth⟩

section
variable {X : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})]

/-- Half of B: the project's section germs are germs in the text's sense. -/
theorem proj_to_B (Bd : StrongBundle PX P) (f : X → Y) (x₀ : X)
    (h : Bd.IsScSmoothSectionGerm f x₀) : IsScSmoothSectionGermB Bd f x₀ := by
  obtain ⟨hsec, hsm, c, hc, hx, h0, h0U, G, hGU, hG⟩ := h
  have hR := c.isRetraction
  -- `r` is an sc⁰-germ on `G`
  have hr0 : IsSc0 _ _ c.U (StrongRetr.r c.R) := (hR.baseRetraction c.relOpen).isScSmooth 0
  have hGsub : ∀ m, G.U m ⊆ (ScNbhdGerm.ofSet c.relOpen.relOpen h0U).U m := fun m x hx =>
    hGU (G.toBase_mem hx)
  have hrG : IsSc0Germ G (StrongRetr.r c.R) :=
    (IsSc0.isSc0Germ c.relOpen.relOpen h0U hr0).mono hGsub
  have h0O : (0 : c.φ.model.E 0) ∈ StrongRetr.r c.R '' c.U := by
    rw [c.r_image, ← h0]; exact c.φ.mapsTo_model x₀ hx
  have hr00 : StrongRetr.r c.R 0 = 0 := StrongRetr.r_eq_self hR h0O
  have hUC : c.U ⊆ c.φ.model.C := by
    obtain ⟨O, _, hO⟩ := c.relOpen.relOpen
    rw [hO]; exact inter_subset_right
  have hrC : MapsTo (StrongRetr.r c.R) (G.U 0) c.φ.model.C := fun u hu =>
    hUC (StrongRetr.r_mem hR (hGU hu))
  let G' := G.preimage G hrG hr00 hrC
  -- the open set `V = φ⁻¹(G₀) ∩ dom φ`
  obtain ⟨O', hO', hGO'⟩ := G.relOpen 0
  have hG0 : G.U 0 = O' ∩ c.φ.model.C := hGO'
  have hOC : c.φ.model.O ⊆ c.φ.model.C := fun z hz => by
    rw [← c.r_image] at hz
    exact hUC (StrongRetr.mem_U_of_mem_O hR hz)
  have hφ : ContinuousOn c.φ c.φ.source := c.φ.continuousOn_toFun
  let V : Set X := c.φ.source ∩ c.φ ⁻¹' O'
  have hVo : IsOpen V := hφ.isOpen_inter_preimage c.φ.isOpen_source hO'
  have hVG : ∀ x ∈ V, c.φ x ∈ c.φ.model.O ∩ G.U 0 := fun x hxV => by
    have hxO := c.φ.mapsTo_model x hxV.1
    exact ⟨hxO, by rw [hG0]; exact ⟨hxV.2, hOC hxO⟩⟩
  -- continuity of `f̂` on `O ∩ G₀`
  have hc0 : ContinuousOn (c.principal f ∘ StrongRetr.r c.R) (G.U 0) :=
    IsSc0Germ.continuousOn_base (isSckGerm_zero_iff.1 (hG 0))
  have hcO : ContinuousOn (c.principal f) (c.φ.model.O ∩ G.U 0) := by
    refine (hc0.mono inter_subset_right).congr fun z hz => ?_
    have hz' : z ∈ StrongRetr.r c.R '' c.U := by rw [c.r_image]; exact hz.1
    simp only [Function.comp_apply, StrongRetr.r_eq_self hR hz']
  -- continuity of `f` on `V`
  have hcont : ContinuousOn f V := by
    have h1 : ContinuousOn (fun x => c.toPartialEquiv.symm (c.φ x, c.principal f (c.φ x))) V := by
      refine c.continuousOn_invFun.comp ((hφ.mono inter_subset_left).prodMk
        (hcO.comp (hφ.mono inter_subset_left) hVG)) fun x hx => ?_
      have := c.toPartialEquiv.map_source (c.mem_source_of_proj (by rw [hsec x]; exact hx.1))
      rwa [← c.apply_section' hsec hx.1]
    refine h1.congr fun x hx => ?_
    simp only
    rw [← c.apply_section' hsec hx.1]
    exact (c.toPartialEquiv.left_inv (c.mem_source_of_proj (by rw [hsec x]; exact hx.1))).symm
  refine ⟨hsm, V, hVo, ⟨hx, ?_⟩, fun x _ => hsec x, hcont, c, hc, hx, h0, G', ?_, ?_⟩
  · show c.φ x₀ ∈ O'
    rw [h0]
    have := G.zero_mem 0
    rw [hG0] at this
    exact this.1
  · intro u hu
    have hu0 : u ∈ G.U 0 := hu.1
    have hru : StrongRetr.r c.R u ∈ G.U 0 := by
      have := hu.2
      rwa [levelMap_zero] at this
    have hrO : StrongRetr.r c.R u ∈ c.φ.model.O := c.r_mem_O (hGU hu0)
    refine ⟨hGU hu0, c.φ.symm_mapsTo hrO, ?_⟩
    show c.φ (c.φ.symm (baseB c u)) ∈ O'
    change c.φ (c.φ.symm (StrongRetr.r c.R u)) ∈ O'
    rw [c.φ.apply_symm_apply hrO]
    rw [hG0] at hru
    exact hru.1
  · exact hG.mono c.isQuadrantLike (ScNbhdGerm.preimage_subset _ _ _ _ _)

/-- The other half of B: the text's section germs are the project's (for a section). -/
theorem B_to_proj (Bd : StrongBundle PX P) (f : X → Y) (x₀ : X) (hf : ∀ x, P (f x) = x)
    (h : IsScSmoothSectionGermB Bd f x₀) : Bd.IsScSmoothSectionGerm f x₀ := by
  obtain ⟨hsm, _V, _hVo, _hxV, _hsV, _hcV, c, hc, hx, h0, G, hGU, hG⟩ := h
  exact ⟨hf, hsm, c, hc, hx, h0, (hGU 0 (G.zero_mem 0)).1, G, fun u hu => (hGU u hu).1, hG⟩

end

/-- B holds outright: the project's Definition 3.3 is the text's. -/
theorem B_holds : B := by
  intro X _ _ _ PX Y _ _ _ P _ _ Bd f x₀ hf
  exact ⟨proj_to_B Bd f x₀, B_to_proj Bd f x₀ hf⟩

theorem A_to_B : A → B := fun _ => B_holds

/-- A, re-proved from non-banned lemmas (the project's proofs). -/
theorem A_reproved : A := by
  refine ⟨?_, ?_, ?_⟩
  · intro X _ _ _ PX Y _ _ _ P _ _ B f hf x₀ hx₀ c hc hx h0
    refine ⟨hf.1, hx₀, c, hc, hx, h0, c.zero_mem_U hx h0, ?_⟩
    have h1 := (hf.isScSmoothRetractMap hc).comp_isScSmooth
      (c.isRetraction.baseRetraction c.relOpen) c.base_retract
    have h2 : IsScSmooth c.U (c.principal f ∘ StrongRetr.r c.R) :=
      (h1.snd c.relOpen.isScDomain).congr c.relOpen.isScDomain fun _ _ => rfl
    exact ⟨ScNbhdGerm.ofSet c.relOpen.relOpen (c.zero_mem_U hx h0), fun _ hu => hu,
      h2.isScSmoothGerm c.isQuadrantLike c.relOpen.relOpen _⟩
  · intro X _ _ _ PX Y _ _ _ P _ _ B B' h c
    rw [StrongBundle.isChart_iff_exists_equiv, StrongBundle.isChart_iff_exists_equiv]
    constructor
    · rintro ⟨A, hA, hcA⟩
      exact ⟨A, hA.trans h, hcA⟩
    · rintro ⟨A, hA, hcA⟩
      exact ⟨A, hA.trans h.symm, hcA⟩
  · exact ⟨GermVsChart.Gex, GermVsChart.f, GermVsChart.isScSmoothGerm_f,
      fun _ hU h0 => GermVsChart.not_isScSmooth_f hU h0⟩

theorem B_to_A : B → A := fun _ => A_reproved

#rt_check RoundTrip.V3_5.A_to_B [Polyfold.StrongBundle.IsScSmoothSection.isScSmoothSectionGerm,
  Polyfold.StrongBundle.isChart_congr, Polyfold.exists_isScSmoothGerm_not_isScSmooth]
#rt_check RoundTrip.V3_5.B_to_A [Polyfold.StrongBundle.IsScSmoothSection.isScSmoothSectionGerm,
  Polyfold.StrongBundle.isChart_congr, Polyfold.exists_isScSmoothGerm_not_isScSmooth]
#rt_overlap RoundTrip.V3_5.B_to_A [Polyfold.StrongBundle.IsScSmoothSection.isScSmoothSectionGerm,
  Polyfold.StrongBundle.isChart_congr, Polyfold.exists_isScSmoothGerm_not_isScSmooth]

end RoundTrip.V3_5
