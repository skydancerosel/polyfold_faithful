import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V2_13

/-! Round trip for V2_13 (Definition 2.14: sc-smooth maps between M-polyfolds).

`A` is the conjunction of the types of `Polyfold.MPolyfold.IsScSmoothOn.of_exists_charts`,
`Polyfold.MPolyfold.isScSmoothMap_id`, `Polyfold.MPolyfold.IsScSmoothOn.comp` and
`Polyfold.MPolyfold.IsScSmoothMap.comp`, universes instantiated at `0` (B lives in `Type`).
`MPolyfold.IsScSmoothOn` and `MPolyfold.IsScSmoothMap` are definitions (vocabulary).

`A → B`: the project's `IsScSmoothMap` (continuity + every pair of charts, every open `V` with
`f(V) ⊆ V'`) gives B's existential condition by restricting a chart around `x` to
`dom φ ∩ f⁻¹(dom ψ)` (`IsChart.restrict`, item V2_12) and converting "every retraction" to "some
retraction" (`isScSmoothRetractMap_iff_exists`, item V2_6).  Conversely B's existential condition
implies continuity (`f = ψ⁻¹ ∘ (ψ ∘ f ∘ φ⁻¹) ∘ φ` near `x`) and then `IsScSmoothMap` by A's
`of_exists_charts` with `U = univ`; the independence of the charts follows.

`B → A`: `isScSmoothMap_id` follows from B (one chart `φ = ψ` around each point).
`of_exists_charts` for `U = univ` also follows from B (`of_exists_charts_univ_of_B`, restricting
`φ` to `V`), but A states it for every open `U`, and `IsScSmoothOn.comp` /
`IsScSmoothMap.comp` (composition, Theorem 2.8 on M-polyfolds) are not in the text's Definition
2.14 nor in B: these are re-proved directly with the project's arguments, without B. -/

namespace RoundTrip.V2_13
open Polyfold Set

/-- The project's statement, universes instantiated at `0`. -/
def A : Prop :=
  (type_of% @Polyfold.MPolyfold.IsScSmoothOn.of_exists_charts.{0, 0}) ∧
    (type_of% @Polyfold.MPolyfold.isScSmoothMap_id.{0}) ∧
    (type_of% @Polyfold.MPolyfold.IsScSmoothOn.comp.{0, 0, 0}) ∧
    (type_of% @Polyfold.MPolyfold.IsScSmoothMap.comp.{0, 0, 0})

theorem A_holds : A :=
  ⟨@Polyfold.MPolyfold.IsScSmoothOn.of_exists_charts.{0, 0},
    @Polyfold.MPolyfold.isScSmoothMap_id.{0}, @Polyfold.MPolyfold.IsScSmoothOn.comp.{0, 0, 0},
    @Polyfold.MPolyfold.IsScSmoothMap.comp.{0, 0, 0}⟩

section Glue

variable {E E' : ScBanach} {C O : Set (E 0)} {C' O' : Set (E' 0)} {g : E 0 → E' 0}

theorem toB (h : IsScSmoothRetractMap E C O E' C' O' g) (hO : IsScRetract E C O) :
    IsScSmoothRetractMapB E C O E' O' g := (isScSmoothRetractMap_iff_exists hO).1 h

theorem ofB (h : IsScSmoothRetractMapB E C O E' O' g) (hO : IsScRetract E C O) :
    IsScSmoothRetractMap E C O E' C' O' g := (isScSmoothRetractMap_iff_exists hO).2 h

variable {X : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X]
  {Y : Type} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y]
  {P : MPolyfold X} {Q : MPolyfold Y} {f : X → Y}

/-- A project sc-smooth map has sc-smooth representatives in all charts with `f(V) ⊆ V'`. -/
theorem rep_of_smoothMap (h : P.IsScSmoothMap Q f) {φ : MChart X} {ψ : MChart Y}
    (hφ : P.IsChart φ) (hψ : Q.IsChart ψ) (hmaps : MapsTo f φ.source ψ.source) :
    RepScSmoothB f φ ψ := by
  have := h.smooth φ ψ hφ hψ φ.source φ.isOpen_source (fun y hy => ⟨mem_univ _, hy⟩) hmaps
  rw [φ.image_source] at this
  exact toB this φ.model.isScRetract

theorem smoothMap_to_B (h : P.IsScSmoothMap Q f) : IsScSmoothB P Q f := by
  intro x
  obtain ⟨φ, hφ, hx⟩ := P.exists_isChart_mem_source x
  obtain ⟨ψ, hψ, hfx⟩ := Q.exists_isChart_mem_source (f x)
  have hcont : Continuous f := continuousOn_univ.1 h.continuousOn
  have hso : IsOpen (φ.source ∩ f ⁻¹' ψ.source) :=
    φ.isOpen_source.inter (ψ.isOpen_source.preimage hcont)
  let φ' := φ.restrict (s := φ.source ∩ f ⁻¹' ψ.source) inter_subset_left hso
  have hφ' : P.IsChart φ' := MPolyfold.IsChart.restrict P hφ inter_subset_left hso
  have hmaps : MapsTo f φ'.source ψ.source := fun y hy => hy.2
  exact ⟨φ', ψ, hφ', hψ, ⟨hx, hfx⟩, hmaps, rep_of_smoothMap h hφ' hψ hmaps⟩

/-- B's existential condition implies continuity. -/
theorem continuous_of_B (h : IsScSmoothB P Q f) : Continuous f := by
  refine continuous_iff_continuousAt.2 fun x => ?_
  obtain ⟨φ, ψ, -, -, hx, hmaps, hrep⟩ := h x
  have hsm := ofB (C' := ψ.model.C) hrep φ.model.isScRetract
  have h1 : ContinuousOn (ψ.symm ∘ (ψ.toPartialEquiv ∘ f ∘ φ.symm) ∘ φ.toPartialEquiv)
      φ.source := by
    refine ψ.continuousOn_invFun.comp ((hsm.continuousOn φ.model.isScRetract).comp
      φ.continuousOn_toFun fun y hy => φ.mapsTo_model y hy) ?_
    intro y hy
    exact hsm.mapsTo (φ.mapsTo_model y hy)
  have h2 : EqOn (ψ.symm ∘ (ψ.toPartialEquiv ∘ f ∘ φ.symm) ∘ φ.toPartialEquiv) f φ.source := by
    intro y hy
    simp only [Function.comp_apply]
    rw [φ.symm_apply_apply hy, ψ.symm_apply_apply (hmaps hy)]
  exact ((h1.congr h2.symm).continuousAt (φ.isOpen_source.mem_nhds hx))

end Glue

theorem A_to_B : A → B := by
  rintro ⟨hex, -, -, -⟩ X _ _ _ Y _ _ _ P Q f
  have hBA : IsScSmoothB P Q f → P.IsScSmoothMap Q f := by
    intro h
    refine hex isOpen_univ (continuous_of_B h).continuousOn fun x _ => ?_
    obtain ⟨φ, ψ, hφ, hψ, hx, hmaps, hrep⟩ := h x
    refine ⟨φ, ψ, φ.source, hφ, hψ, φ.isOpen_source, hx, fun y hy => ⟨mem_univ _, hy⟩, hmaps,
      ?_⟩
    rw [φ.image_source]
    exact ofB hrep φ.model.isScRetract
  refine ⟨⟨smoothMap_to_B, hBA⟩, fun h x φ ψ hφ hψ _ hmaps => ?_⟩
  exact rep_of_smoothMap (hBA h) hφ hψ hmaps

/-! ### `B → A` -/

section Direct

variable {X : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X]
  {Y : Type} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y]
  {Z : Type} [TopologicalSpace Z] [T2Space Z] [ParacompactSpace Z]
  {P : MPolyfold X} {Q : MPolyfold Y} {S : MPolyfold Z}

/-- The identity is sc-smooth, from B. -/
theorem id_of_B (hB : B) : P.IsScSmoothMap P id := by
  refine ((hB X X P P id).1).2 fun x => ?_
  obtain ⟨φ, hφ, hx⟩ := P.exists_isChart_mem_source x
  refine ⟨φ, φ, hφ, hφ, hx, fun y hy => hy, ?_⟩
  refine toB ((isScSmoothRetractMap_id (C := φ.model.C) φ.model.O).congr ?_) φ.model.isScRetract
  intro z hz
  change z = φ (φ.symm z)
  rw [φ.apply_symm_apply hz]

/-- `of_exists_charts` for `U = univ`, from B (not used below: A states it for every open `U`). -/
theorem of_exists_charts_univ_of_B (hB : B) {f : X → Y} (hf : ContinuousOn f univ)
    (h : ∀ x ∈ univ, ∃ (φ : MChart X) (ψ : MChart Y) (V : Set X), P.IsChart φ ∧ Q.IsChart ψ ∧
      IsOpen V ∧ x ∈ V ∧ V ⊆ univ ∩ φ.source ∧ MapsTo f V ψ.source ∧
      IsScSmoothRetractMap φ.model.E φ.model.C (φ '' V) ψ.model.E ψ.model.C ψ.model.O
        (ψ ∘ f ∘ φ.symm)) :
    P.IsScSmoothOn Q f univ := by
  have _ := hf
  refine ((hB X Y P Q f).1).2 fun x => ?_
  obtain ⟨φ, ψ, V, hφ, hψ, hVo, hxV, hVφ, hmaps, hsm⟩ := h x (mem_univ x)
  have hVs : V ⊆ φ.source := fun y hy => (hVφ hy).2
  refine ⟨φ.restrict hVs hVo, ψ, MPolyfold.IsChart.restrict P hφ hVs hVo, hψ, hxV, hmaps, ?_⟩
  exact toB hsm (φ.isScRetract_image hVs hVo)

/-- `of_exists_charts` (the project's argument, re-proved directly). -/
theorem of_exists_charts' {f : X → Y} {U : Set X} (hU : IsOpen U)
    (hf : ContinuousOn f U)
    (h : ∀ x ∈ U, ∃ (φ : MChart X) (ψ : MChart Y) (V : Set X), P.IsChart φ ∧ Q.IsChart ψ ∧
      IsOpen V ∧ x ∈ V ∧ V ⊆ U ∩ φ.source ∧ MapsTo f V ψ.source ∧
      IsScSmoothRetractMap φ.model.E φ.model.C (φ '' V) ψ.model.E ψ.model.C ψ.model.O
        (ψ ∘ f ∘ φ.symm)) :
    P.IsScSmoothOn Q f U where
  isOpen := hU
  continuousOn := hf
  smooth φ' ψ' hφ' hψ' V' hV' hV'U hfV' := by
    have hV'φ : V' ⊆ φ'.source := fun x hx => (hV'U hx).2
    refine IsScSmoothRetractMap.of_locally ?_ ?_
    · rintro _ ⟨x, hx, rfl⟩
      change ψ' (f (φ'.symm (φ' x))) ∈ ψ'.model.O
      rw [φ'.symm_apply_apply (hV'φ hx)]
      exact ψ'.mapsTo_model _ (hfV' hx)
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨φ, ψ, V, hφ, hψ, hVo, hxV, hVU, hfV, hsm⟩ := h x (hV'U hx).1
    set V₀ := V ∩ V' with hV₀
    have hV₀o : IsOpen V₀ := hVo.inter hV'
    have hV₀φ' : V₀ ⊆ φ'.source := fun y hy => hV'φ hy.2
    have hV₀φ : V₀ ⊆ φ.source := fun y hy => (hVU hy.1).2
    obtain ⟨W, hW, hWeq⟩ := φ'.exists_isOpen_image_eq hV₀φ' hV₀o
    refine ⟨W, hW, ?_, ?_⟩
    · have : φ' x ∈ φ' '' V₀ := ⟨x, ⟨hxV, hx⟩, rfl⟩
      rw [hWeq] at this; exact this.2
    have hover : φ' '' V' ∩ W = φ' '' V₀ := by
      rw [hWeq]
      exact inter_eq_inter_of_subset (φ'.image_subset_model hV'φ)
        (hWeq ▸ image_mono inter_subset_right)
    rw [hover]
    have h1 : IsScSmoothRetractMap φ'.model.E φ'.model.C (φ' '' V₀) φ.model.E φ.model.C (φ '' V₀)
        (φ'.transition φ) := by
      obtain ⟨W', hW', hW'eq⟩ := φ'.exists_isOpen_image_eq hV₀φ' hV₀o
      have := (hφ'.compatible hφ (P := P)).1.restrict (φ'.isScRetract_overlap φ) (W := W')
      have hover' : φ'.overlap φ ∩ W' = φ' '' V₀ := by
        rw [hW'eq]
        exact inter_eq_inter_of_subset (φ'.overlap_subset φ)
          (hW'eq ▸ image_mono fun y hy => ⟨hV₀φ' hy, hV₀φ hy⟩)
      rw [hover'] at this
      refine this.mono_target ?_
      rintro _ ⟨y, hy, rfl⟩
      rw [φ'.transition_apply φ (hV₀φ' hy)]
      exact ⟨y, hy, rfl⟩
    have h2 : IsScSmoothRetractMap φ.model.E φ.model.C (φ '' V₀) ψ.model.E ψ.model.C
        (ψ.overlap ψ') (ψ ∘ f ∘ φ.symm) := by
      obtain ⟨W', hW', hW'eq⟩ := φ.exists_isOpen_image_eq hV₀φ hV₀o
      have := hsm.restrict (φ.isScRetract_image (fun y hy => (hVU hy).2) hVo) (W := W')
      have hover' : φ '' V ∩ W' = φ '' V₀ := by
        rw [hW'eq]
        exact inter_eq_inter_of_subset (φ.image_subset_model fun y hy => (hVU hy).2)
          (hW'eq ▸ image_mono inter_subset_left)
      rw [hover'] at this
      refine this.mono_target ?_
      rintro _ ⟨y, hy, rfl⟩
      change ψ (f (φ.symm (φ y))) ∈ ψ.overlap ψ'
      rw [φ.symm_apply_apply (hV₀φ hy)]
      exact ⟨f y, ⟨hfV hy.1, hfV' hy.2⟩, rfl⟩
    have h3 : IsScSmoothRetractMap ψ.model.E ψ.model.C (ψ.overlap ψ') ψ'.model.E ψ'.model.C
        ψ'.model.O (ψ.transition ψ') :=
      (hψ.compatible hψ' (P := Q)).1.mono_target fun _ hz => (ψ'.overlap_subset ψ)
        (ψ.transition_mapsTo ψ' hz)
    have hφV₀ : IsScRetract φ.model.E φ.model.C (φ '' V₀) := φ.isScRetract_image hV₀φ hV₀o
    refine ((h3.comp h2 (ψ.isScRetract_overlap ψ')).comp h1 hφV₀).congr ?_
    rintro _ ⟨y, hy, rfl⟩
    simp only [Function.comp_apply, φ'.transition_apply φ (hV₀φ' hy),
      φ'.symm_apply_apply (hV₀φ' hy), φ.symm_apply_apply (hV₀φ hy),
      ψ.transition_apply ψ' (hfV hy.1)]

/-- `IsScSmoothOn.comp` (the project's argument, re-proved directly). -/
theorem comp' {f : X → Y} {g : Y → Z} {U : Set X} {U' : Set Y}
    (hg : Q.IsScSmoothOn S g U') (hf : P.IsScSmoothOn Q f U) (hfU : MapsTo f U U') :
    P.IsScSmoothOn S (g ∘ f) U where
  isOpen := hf.isOpen
  continuousOn := hg.continuousOn.comp hf.continuousOn hfU
  smooth φ χ hφ hχ V hV hVU hgfV := by
    have hVφ : V ⊆ φ.source := fun x hx => (hVU hx).2
    have hVU' : V ⊆ U := fun x hx => (hVU hx).1
    refine IsScSmoothRetractMap.of_locally ?_ ?_
    · rintro _ ⟨x, hx, rfl⟩
      change χ (g (f (φ.symm (φ x)))) ∈ χ.model.O
      rw [φ.symm_apply_apply (hVφ hx)]
      exact χ.mapsTo_model _ (hgfV hx)
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨ψ, hψ, hfxψ⟩ := Q.exists_isChart_mem_source (f x)
    set V' := U' ∩ ψ.source ∩ g ⁻¹' χ.source with hV'
    have hV'o : IsOpen V' := by
      have : ContinuousOn g (U' ∩ ψ.source) := hg.continuousOn.mono inter_subset_left
      exact this.isOpen_inter_preimage (hg.isOpen.inter ψ.isOpen_source) χ.isOpen_source
    set V₀ := V ∩ f ⁻¹' V' with hV₀
    have hV₀o : IsOpen V₀ :=
      (hf.continuousOn.mono hVU').isOpen_inter_preimage hV hV'o
    have hxV₀ : x ∈ V₀ := ⟨hx, ⟨hfU (hVU' hx), hfxψ⟩, hgfV hx⟩
    have hV₀V : V₀ ⊆ V := inter_subset_left
    obtain ⟨W, hW, hWeq⟩ := φ.exists_isOpen_image_eq (hV₀V.trans hVφ) hV₀o
    refine ⟨W, hW, ?_, ?_⟩
    · have : φ x ∈ φ '' V₀ := ⟨x, hxV₀, rfl⟩
      rw [hWeq] at this; exact this.2
    · have hover : φ '' V ∩ W = φ '' V₀ := by
        rw [hWeq]
        ext z
        constructor
        · rintro ⟨hz, hzW⟩
          exact ⟨φ.image_subset_model hVφ hz, hzW⟩
        · rintro ⟨hz, hzW⟩
          refine ⟨?_, hzW⟩
          have : z ∈ φ '' V₀ := by rw [hWeq]; exact ⟨hz, hzW⟩
          exact image_mono hV₀V this
      rw [hover]
      have h1 : IsScSmoothRetractMap φ.model.E φ.model.C (φ '' V₀) ψ.model.E ψ.model.C (ψ '' V')
          (ψ ∘ f ∘ φ.symm) := by
        refine (hf.smooth φ ψ hφ hψ V₀ hV₀o (fun y hy => ⟨hVU' (hV₀V hy), hVφ (hV₀V hy)⟩)
          fun y hy => hy.2.1.2).mono_target ?_
        rintro _ ⟨y, hy, rfl⟩
        change ψ (f (φ.symm (φ y))) ∈ ψ '' V'
        rw [φ.symm_apply_apply (hVφ (hV₀V hy))]
        exact ⟨f y, hy.2, rfl⟩
      have h2 : IsScSmoothRetractMap ψ.model.E ψ.model.C (ψ '' V') χ.model.E χ.model.C χ.model.O
          (χ ∘ g ∘ ψ.symm) :=
        hg.smooth ψ χ hψ hχ V' hV'o (fun y hy => ⟨hy.1.1, hy.1.2⟩) fun y hy => hy.2
      have hψV' : IsScRetract ψ.model.E ψ.model.C (ψ '' V') :=
        ψ.isScRetract_image (fun y hy => hy.1.2) hV'o
      refine (h2.comp h1 hψV').congr ?_
      rintro _ ⟨y, hy, rfl⟩
      simp only [Function.comp_apply, φ.symm_apply_apply (hVφ (hV₀V hy)),
        ψ.symm_apply_apply hy.2.1.2]

end Direct

theorem B_to_A : B → A := by
  intro hB
  refine ⟨?_, ?_, ?_, ?_⟩
  · intros
    exact of_exists_charts' ‹_› ‹_› ‹_›
  · intros
    exact id_of_B hB
  · intros
    exact comp' ‹_› ‹_› ‹_›
  · intros
    exact comp' ‹_› ‹_› (mapsTo_univ _ _)

#rt_check RoundTrip.V2_13.A_to_B [Polyfold.MPolyfold.IsScSmoothOn.of_exists_charts,
  Polyfold.MPolyfold.isScSmoothMap_id, Polyfold.MPolyfold.IsScSmoothOn.comp,
  Polyfold.MPolyfold.IsScSmoothMap.comp]
#rt_check RoundTrip.V2_13.B_to_A [Polyfold.MPolyfold.IsScSmoothOn.of_exists_charts,
  Polyfold.MPolyfold.isScSmoothMap_id, Polyfold.MPolyfold.IsScSmoothOn.comp,
  Polyfold.MPolyfold.IsScSmoothMap.comp]
#rt_overlap RoundTrip.V2_13.B_to_A [Polyfold.MPolyfold.IsScSmoothOn.of_exists_charts,
  Polyfold.MPolyfold.isScSmoothMap_id, Polyfold.MPolyfold.IsScSmoothOn.comp,
  Polyfold.MPolyfold.IsScSmoothMap.comp]

end RoundTrip.V2_13
