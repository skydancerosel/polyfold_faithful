import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V2_36

/-! Round trip for V2_36 (before Theorem 2.31: a retract is an M-polyfold, and
`d_O(x) = min d_{C'}(φ(x))` over germs of sc-diffeomorphisms `φ : (O, x) → (O', φ(x))`).

`A` is the conjunction of the types of the theorems listed for the item:
`IsRelOpenInQuadrant.selfChart_isChart` (no universe) and `MChart.Compatible.isDiffeoGerm`
(universe `0`).  `LocalModel.selfChart`, `LocalModel.toMPolyfold`,
`IsRelOpenInQuadrant.toMPolyfold` are vocabulary.

A says little about B: its first theorem is about the M-polyfold `X_U` of a relatively open
subset `U` of a partial quadrant (not a general retract), the second turns two compatible charts
into a germ of sc¹ diffeomorphisms between restricted retractions.  The text's claims are carried
by the definitions: "a retract is an M-polyfold" is the definition `LocalModel.toMPolyfold` (the
atlas `{id}`), and "`d_O(x) = min …` over germs" is NOT stated by the project; it holds for
`(toMPolyfold).degIndex` (an `sInf` over the charts compatible with `id`), which is proved here.

* `A → B`, proved outright (A unused):
  (1) `toMPolyfold` (or the empty atlas when `O = ∅`) has `id` as a chart;
  (2) `IsLeast`: a chart `ψ` realizing `d_O(x)` gives the germ `ψ ∘ id⁻¹` on the overlap
  `O ∩ V` (`chartToGerm`); conversely every germ `f : (O ∩ V, x) → (O' ∩ V', f(x))` with inverse
  `g` gives a chart `z ↦ f z` on `{z ∈ O | z ∈ V}` modelled on the retract `O' ∩ V'`, compatible
  with `id` (`germChart`), so `d_O(x) ≤ d_{C'}(f(x))`.
* `B → A`, proved outright (B unused): `selfChart_isChart` is membership in the atlas `{id}`;
  `Compatible.isDiffeoGerm` is re-proved (the project's ten-line argument). -/

namespace RoundTrip.V2_36
open Polyfold Set

/-- The project's statement. -/
def A : Prop :=
  (type_of% @Polyfold.IsRelOpenInQuadrant.selfChart_isChart) ∧
  (type_of% @Polyfold.MChart.Compatible.isDiffeoGerm.{0})

theorem A_holds : A :=
  ⟨@Polyfold.IsRelOpenInQuadrant.selfChart_isChart, @Polyfold.MChart.Compatible.isDiffeoGerm.{0}⟩

section Glue

variable {E : ScBanach} {C O : Set (E.lvl 0)} (hO : IsScRetract E C O)

open Classical in
lemma selfChart_symm_apply (hne : O.Nonempty) {z : E.lvl 0} (hz : z ∈ O) :
    ((LocalModel.mk E C O hO).selfChart hne).symm z = ⟨z, hz⟩ := by
  change (if h : z ∈ O then (⟨z, h⟩ : O) else ⟨hne.some, hne.some_mem⟩) = _
  rw [dif_pos hz]

/-- The overlap of the identity chart with a chart `ψ`, seen in `E`. -/
lemma selfChart_overlap (hne : O.Nonempty) (ψ : MChart O) :
    ((LocalModel.mk E C O hO).selfChart hne).overlap ψ = Subtype.val '' ψ.source := by
  change Subtype.val '' (univ ∩ ψ.source) = _
  rw [univ_inter]

open Classical in
/-- The chart of `↥O` defined by a germ `f : (O ∩ V, x) → (O' ∩ V', f x)` with inverse `g`. -/
noncomputable def germChart {E' : ScBanach} {C' O' : Set (E'.lvl 0)} (hO' : IsScRetract E' C' O')
    (x : O) (f : E.lvl 0 → E'.lvl 0) (g : E'.lvl 0 → E.lvl 0) (V : Set (E.lvl 0))
    (V' : Set (E'.lvl 0)) (h : IsGermDiffeoB C O C' O' x f g V V') : MChart O where
  model := ⟨E', C', O' ∩ V', proposition_2_10_1 hO' h.2.1⟩
  toPartialEquiv :=
    { toFun := fun z => f z.1
      invFun := fun w => if hw : g w ∈ O then ⟨g w, hw⟩ else x
      source := Subtype.val ⁻¹' V
      target := O' ∩ V'
      map_source' := fun z hz => h.2.2.2.2.1.mapsTo ⟨z.2, hz⟩
      map_target' := fun w hw => by
        have := h.2.2.2.2.2.1.mapsTo hw
        change (if hw : g w ∈ O then (⟨g w, hw⟩ : O) else x).1 ∈ V
        rw [dif_pos this.1]
        exact this.2
      left_inv' := fun z hz => by
        have h1 := h.2.2.2.2.2.2.1 z.1 ⟨z.2, hz⟩
        change (if hw : g (f z.1) ∈ O then (⟨g (f z.1), hw⟩ : O) else x) = z
        have h2 : g (f z.1) ∈ O := by rw [h1]; exact z.2
        rw [dif_pos h2]
        exact Subtype.ext h1
      right_inv' := fun w hw => by
        have := h.2.2.2.2.2.1.mapsTo hw
        change f (if hw : g w ∈ O then (⟨g w, hw⟩ : O) else x).1 = w
        rw [dif_pos this.1]
        exact h.2.2.2.2.2.2.2 w hw }
  isOpen_source := h.1.preimage continuous_subtype_val
  target_eq := rfl
  continuousOn_toFun :=
    (h.2.2.2.2.1.continuousOn (proposition_2_10_1 hO h.1)).comp
      continuous_subtype_val.continuousOn fun z hz => ⟨z.2, hz⟩
  continuousOn_invFun := by
    rw [Topology.IsInducing.subtypeVal.continuousOn_iff]
    refine (h.2.2.2.2.2.1.continuousOn (proposition_2_10_1 hO' h.2.1)).congr fun w hw => ?_
    have := h.2.2.2.2.2.1.mapsTo hw
    change (if hw : g w ∈ O then (⟨g w, hw⟩ : O) else x).1 = g w
    rw [dif_pos this.1]

open Classical in
/-- The chart of a germ is a chart of `toMPolyfold`. -/
lemma germChart_isChart (hne : O.Nonempty) {E' : ScBanach} {C' O' : Set (E'.lvl 0)}
    (hO' : IsScRetract E' C' O') (x : O) (f : E.lvl 0 → E'.lvl 0) (g : E'.lvl 0 → E.lvl 0)
    (V : Set (E.lvl 0)) (V' : Set (E'.lvl 0)) (h : IsGermDiffeoB C O C' O' x f g V V') :
    ((LocalModel.mk E C O hO).toMPolyfold hne).IsChart (germChart hO hO' x f g V V' h) := by
  intro φ hφ
  rw [mem_singleton_iff.1 hφ]
  set ψ := germChart hO hO' x f g V V' h
  set σ := (LocalModel.mk E C O hO).selfChart hne
  obtain ⟨hV, hV', -, -, hf, hg, hgf, hfg⟩ := h
  have hσ : σ.overlap ψ = O ∩ V := by
    rw [selfChart_overlap]
    ext z
    exact ⟨fun ⟨y, hy, hyz⟩ => hyz ▸ ⟨y.2, hy⟩, fun hz => ⟨⟨z, hz.1⟩, hz.2, rfl⟩⟩
  have hψ : ψ.overlap σ = O' ∩ V' := by
    change (fun z : O => f z.1) '' (Subtype.val ⁻¹' V ∩ univ) = O' ∩ V'
    ext w
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact hf.mapsTo ⟨z.2, hz.1⟩
    · intro hw
      have := hg.mapsTo hw
      exact ⟨⟨g w, this.1⟩, ⟨this.2, mem_univ _⟩, hfg w hw⟩
  constructor
  · -- `id ∘ ψ⁻¹ = g` on `O' ∩ V'`
    rw [hψ, hσ]
    refine hg.congr fun w hw => ?_
    change g w = (if hw : g w ∈ O then (⟨g w, hw⟩ : O) else x).1
    rw [dif_pos (hg.mapsTo hw).1]
  · -- `ψ ∘ id⁻¹ = f` on `O ∩ V`
    rw [hσ, hψ]
    refine hf.congr fun z hz => ?_
    change f z = f (σ.symm z).1
    rw [selfChart_symm_apply hO hne hz.1]

/-- A chart `ψ` of `toMPolyfold` around `x` gives a germ of sc-diffeomorphisms `ψ ∘ id⁻¹` on the
overlap. -/
lemma chartToGerm (hne : O.Nonempty) (ψ : MChart O)
    (hψ : ((LocalModel.mk E C O hO).toMPolyfold hne).IsChart ψ) (x : O) (hx : x ∈ ψ.source) :
    ∃ V V', IsGermDiffeoB C O ψ.model.C ψ.model.O (x : E.lvl 0)
      (((LocalModel.mk E C O hO).selfChart hne).transition ψ)
      (ψ.transition ((LocalModel.mk E C O hO).selfChart hne)) V V' := by
  set σ := (LocalModel.mk E C O hO).selfChart hne
  have hc : ψ.Compatible σ := hψ σ (mem_singleton _)
  obtain ⟨V, hV, hVeq⟩ := σ.exists_isOpen_image_eq (s := σ.source ∩ ψ.source) inter_subset_left
    (σ.isOpen_source.inter ψ.isOpen_source)
  obtain ⟨V', hV', hV'eq⟩ := ψ.exists_isOpen_image_eq (s := ψ.source ∩ σ.source) inter_subset_left
    (ψ.isOpen_source.inter σ.isOpen_source)
  have hσ : σ.overlap ψ = O ∩ V := hVeq
  have hψ' : ψ.overlap σ = ψ.model.O ∩ V' := hV'eq
  have hxσ : x ∈ σ.source := mem_univ _
  refine ⟨V, V', hV, hV', ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have : σ x ∈ σ.overlap ψ := σ.mem_overlap ψ hxσ hx
    rw [hσ] at this; exact this.2
  · have : ψ x ∈ ψ.overlap σ := ψ.mem_overlap σ hx hxσ
    rw [hψ'] at this
    show σ.transition ψ (σ x) ∈ V'
    rw [σ.transition_apply ψ hxσ]; exact this.2
  · rw [← hσ, ← hψ']; exact hc.2
  · rw [← hσ, ← hψ']; exact hc.1
  · rw [← hσ]
    rintro _ ⟨y, hy, rfl⟩
    rw [σ.transition_apply ψ hy.1, ψ.transition_apply σ hy.2]
  · rw [← hψ']
    rintro _ ⟨y, hy, rfl⟩
    rw [ψ.transition_apply σ hy.1, σ.transition_apply ψ hy.2]

end Glue

/-- `A → B`: proved outright (A is not used). -/
theorem A_to_B : A → B := by
  intro _ E C O hO
  refine ⟨?_, ?_⟩
  · by_cases hne : O.Nonempty
    · exact ⟨(LocalModel.mk E C O hO).toMPolyfold hne, fun _ =>
        ((LocalModel.mk E C O hO).toMPolyfold hne).isChart_of_mem (mem_singleton _)⟩
    · exact ⟨⟨⟨∅, fun _ h => h.elim, fun z => (hne ⟨z.1, z.2⟩).elim⟩⟩, fun hne' => (hne hne').elim⟩
  · intro hne x
    set P := (LocalModel.mk E C O hO).toMPolyfold hne
    set σ := (LocalModel.mk E C O hO).selfChart hne
    constructor
    · obtain ⟨ψ, hψ, hxψ, hd⟩ := P.exists_isChart_degIndex_eq x
      obtain ⟨V, V', hg⟩ := chartToGerm hO hne ψ hψ x hxψ
      refine ⟨ψ.model.E, ψ.model.C, ψ.model.O, ψ.model.isScRetract, _, _, V, V', hg, ?_⟩
      rw [hd]
      show degIndex _ _ (ψ x) = degIndex _ _ (σ.transition ψ (σ x))
      rw [σ.transition_apply ψ (mem_univ _)]
    · rintro d ⟨E', C', O', hO', f, g, V, V', hg, rfl⟩
      exact P.degIndex_le (germChart_isChart hO hne hO' x f g V V' hg) hg.2.2.1

/-- `B → A`: proved outright (B is not used). -/
theorem B_to_A : B → A := by
  intro _
  refine ⟨fun hU hne => (hU.toMPolyfold hne).isChart_of_mem (mem_singleton _), ?_⟩
  intro X _ φ ψ h R hR R' hR' W hW hWeq W' hW' hW'eq
  have h1 : (R.restrict hW).retract = φ.overlap ψ := by rw [R.restrict_retract, hR, hWeq]
  have h2 : (R'.restrict hW').retract = ψ.overlap φ := by rw [R'.restrict_retract, hR', hW'eq]
  refine ⟨(h.1.comp_isScSmooth _ h1).isSc1, (h.2.comp_isScSmooth _ h2).isSc1, ?_, ?_, ?_, ?_⟩
  · rw [h1, h2]; exact h.1.mapsTo
  · rw [h1, h2]; exact h.2.mapsTo
  · rw [h1]
    rintro _ ⟨x, hx, rfl⟩
    rw [φ.transition_apply ψ hx.1, ψ.transition_apply φ hx.2]
  · rw [h2]
    rintro _ ⟨x, hx, rfl⟩
    rw [ψ.transition_apply φ hx.1, φ.transition_apply ψ hx.2]

#rt_check RoundTrip.V2_36.A_to_B [Polyfold.IsRelOpenInQuadrant.selfChart_isChart, Polyfold.MChart.Compatible.isDiffeoGerm]
#rt_check RoundTrip.V2_36.B_to_A [Polyfold.IsRelOpenInQuadrant.selfChart_isChart, Polyfold.MChart.Compatible.isDiffeoGerm]
#rt_overlap RoundTrip.V2_36.B_to_A [Polyfold.IsRelOpenInQuadrant.selfChart_isChart, Polyfold.MChart.Compatible.isDiffeoGerm]

end RoundTrip.V2_36
