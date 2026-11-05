import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V4_2

/-!
Round trip for V4_2 (after Definition 4.1: the transition maps of a corner atlas are `C^∞`).  `A`
is the conjunction of the types of `MChart.IsCornerChart.contDiffOn_transition` and
`MChart.isRelOpenInQuadrant_overlap`, universe instantiated at `0`.

A ⇒ B: B's corner charts (any finite-dimensional sc-model with onto inclusions) are turned into
project corner charts `id ∘ χ` over `ScBanach.const E₀` (`toCorner`, the construction of
`exists_isCornerChart_of_finiteDimensional`), which have the same transition maps, so A's
`contDiffOn_transition` gives `C^∞`; the overlap is relatively open by A's second conjunct; the
sc-diffeomorphism clauses are the compatibility of the charts; the classical quadrant
`T⁻¹([0,∞)ᵏ × ℝˡ)` comes from the sc-presentation `C = T⁻¹([0,∞)ⁿ ⊕ W)` with `W₀ ≅ ℝˡ`.

B ⇒ A: for two compatible project corner charts `χ, χ'` on an arbitrary space `X` (not
Hausdorff or paracompact in A), B is applied to the M-polyfold `O = χ(V ∩ V')` (the retract
M-polyfold `IsRelOpenInQuadrant.toMPolyfold`, Hausdorff and paracompact as a subspace of `ℝⁿ`)
with the corner atlas `{id, χ' ∘ χ⁻¹}`; its transition map is `χ' ∘ χ⁻¹` on `O`.  A's second
conjunct (for charts on ANY sc-model, finite-dimensional or not, and any second chart) is not a
consequence of B, which only covers corner atlases; it is re-proved outright (`relOpen_overlap`,
a five-line topological fact also needed to build the model of `O`).
-/

namespace RoundTrip.V4_2
open Polyfold Set

def A : Prop :=
  type_of% @Polyfold.MChart.IsCornerChart.contDiffOn_transition.{0} ∧
  type_of% @Polyfold.MChart.isRelOpenInQuadrant_overlap.{0}

theorem A_holds : A :=
  ⟨@Polyfold.MChart.IsCornerChart.contDiffOn_transition.{0},
    @Polyfold.MChart.isRelOpenInQuadrant_overlap.{0}⟩

/-! ### A ⇒ B -/

section AtoB

/-- An sc-partial quadrant of a finite-dimensional space is a classical one. -/
theorem classical_of_partialQuadrant {E : ScBanach} [FiniteDimensional ℝ (E 0)] {C : Set (E 0)}
    (hC : IsPartialQuadrant E C) : IsClassicalQuadrantB C := by
  obtain ⟨n, W, T, rfl⟩ := hC
  have hfin : FiniteDimensional ℝ (W 0) := by
    have : FiniteDimensional ℝ ((Fin n → ℝ) × W 0) :=
      LinearEquiv.finiteDimensional (T 0).toLinearEquiv
    exact Module.Finite.of_surjective (LinearMap.snd ℝ (Fin n → ℝ) (W 0)) LinearMap.snd_surjective
  let e : W 0 ≃L[ℝ] (Fin (Module.finrank ℝ (W 0)) → ℝ) :=
    ContinuousLinearEquiv.ofFinrankEq (Module.finrank_fin_fun ℝ).symm
  refine ⟨n, Module.finrank ℝ (W 0),
    (T 0).trans ((ContinuousLinearEquiv.refl ℝ (Fin n → ℝ)).prodCongr e), ?_⟩
  ext x
  exact Iff.rfl

variable {X : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {P : MPolyfold X}

omit [T2Space X] [ParacompactSpace X] in
theorem relOpen_id {χ : MChart X} [FiniteDimensional ℝ (χ.model.E 0)]
    (hU : IsRelOpenInQuadrant χ.model.E χ.model.C χ.model.O) :
    IsRelOpenInQuadrant (ScBanach.const (χ.model.E 0)) χ.model.C
      ((id : (ScBanach.const (χ.model.E 0)) 0 → _) '' χ.model.O) := by
  rw [image_id]; exact hU.toConst

/-- The project corner chart `id ∘ χ` over `ScBanach.const E₀` of a chart `χ` modelled on a
relatively open subset of a partial quadrant in a finite-dimensional sc-space. -/
noncomputable def toCorner {χ : MChart X} [FiniteDimensional ℝ (χ.model.E 0)]
    (hU : IsRelOpenInQuadrant χ.model.E χ.model.C χ.model.O) : MChart X :=
  χ.compDiffeo hU.isScDiffeoQuadrant_toConst subset_rfl (relOpen_id hU).isScRetract

omit [T2Space X] [ParacompactSpace X] in
theorem toCorner_isCornerChart {χ : MChart X} [hfin : FiniteDimensional ℝ (χ.model.E 0)]
    (hU : IsRelOpenInQuadrant χ.model.E χ.model.C χ.model.O) : (toCorner hU).IsCornerChart :=
  ⟨χ.model.E 0, inferInstance, inferInstance, hfin, χ.model.C, _, relOpen_id hU, rfl⟩

theorem toCorner_isChart {χ : MChart X} [FiniteDimensional ℝ (χ.model.E 0)]
    (hU : IsRelOpenInQuadrant χ.model.E χ.model.C χ.model.O) (hχ : P.IsChart χ) :
    P.IsChart (toCorner hU) :=
  MChart.compDiffeo_isChart hχ _ subset_rfl _

/-- `C^∞` of the transition maps of B's corner charts, from A's `contDiffOn_transition`. -/
theorem contDiff_of_A (hA1 : type_of% @Polyfold.MChart.IsCornerChart.contDiffOn_transition.{0})
    {χ χ' : MChart X} (hχ : P.IsChart χ) (hχ' : P.IsChart χ') (h : IsCornerChartB χ)
    (h' : IsCornerChartB χ') :
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (transB χ χ') (overlapB χ χ') := by
  have := h.1
  have := h'.1
  have hc := hA1 (χ := toCorner h.2.2) (χ' := toCorner h'.2.2) (toCorner_isCornerChart h.2.2)
    (toCorner_isCornerChart h'.2.2)
    (MPolyfold.IsChart.compatible P (toCorner_isChart h.2.2 hχ) (toCorner_isChart h'.2.2 hχ'))
  exact hc

end AtoB

theorem A_to_B : A → B := by
  rintro ⟨hA1, hA2⟩ X _ _ _ P S hS
  have cd : ∀ χ ∈ S, ∀ χ' ∈ S,
      ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (transB χ χ') (overlapB χ χ') :=
    fun χ hχ χ' hχ' =>
      contDiff_of_A hA1 (hS.2.2.2 χ hχ) (hS.2.2.2 χ' hχ') (hS.1 χ hχ) (hS.1 χ' hχ')
  have ro : ∀ χ ∈ S, ∀ χ' : MChart X,
      IsRelOpenInQuadrant χ.model.E χ.model.C (overlapB χ χ') :=
    fun χ hχ χ' => hA2 (hS.1 χ hχ).2.2 χ'
  refine ⟨fun χ hχ χ' hχ' => ⟨ro χ hχ χ', χ.transition_mapsTo χ', ?_, ?_, cd χ hχ χ' hχ'⟩,
    fun χ hχ => ?_, hS.2.2.1, fun χ hχ χ' hχ' => ⟨(ro χ hχ χ').relOpen, cd χ hχ χ' hχ'⟩⟩
  · rintro _ ⟨x, hx, rfl⟩
    change χ'.transition χ (χ.transition χ' (χ x)) = χ x
    rw [χ.transition_apply χ' hx.1, χ'.transition_apply χ hx.2]
  · exact (hS.2.1 χ hχ χ' hχ').1.comp_isScSmooth (ScRetraction.id (ro χ hχ χ')) (image_id _)
  · have := (hS.1 χ hχ).1
    exact ⟨(hS.1 χ hχ).1, classical_of_partialQuadrant (hS.1 χ hχ).2.2.isPartialQuadrant,
      (hS.1 χ hχ).2.2.relOpen⟩

/-! ### B ⇒ A -/

section BtoA

variable {X : Type} [TopologicalSpace X]

/-- A's second conjunct, re-proved outright (B has no statement for non-corner charts). -/
theorem relOpen_overlap {χ : MChart X}
    (hχ : IsRelOpenInQuadrant χ.model.E χ.model.C χ.model.O) (χ' : MChart X) :
    IsRelOpenInQuadrant χ.model.E χ.model.C (χ.overlap χ') := by
  obtain ⟨W, hW, hWeq⟩ := χ.exists_isOpen_image_eq (s := χ.source ∩ χ'.source)
    inter_subset_left (χ.isOpen_source.inter χ'.isOpen_source)
  change IsRelOpenInQuadrant χ.model.E χ.model.C (χ '' (χ.source ∩ χ'.source))
  rw [hWeq]
  exact hχ.inter_isOpen hW

theorem trans_trans {χ χ' : MChart X} {z : χ.model.E 0} (hz : z ∈ χ.overlap χ') :
    χ'.transition χ (χ.transition χ' z) = z := by
  obtain ⟨x, hx, rfl⟩ := hz
  rw [χ.transition_apply χ' hx.1, χ'.transition_apply χ hx.2]

variable {χ χ' : MChart X} (h : χ.Compatible χ')
  (hov : IsRelOpenInQuadrant χ.model.E χ.model.C (χ.overlap χ'))
  (hov' : IsRelOpenInQuadrant χ'.model.E χ'.model.C (χ'.overlap χ))
  (hne : (χ.overlap χ').Nonempty)

/-- The identity chart of the M-polyfold `O = χ(V ∩ V')`. -/
noncomputable abbrev chart1 : MChart (LocalModel.ofRelOpen hov).O :=
  (LocalModel.ofRelOpen hov).selfChart hne

theorem chart1_val {z : χ.model.E 0} (hz : z ∈ χ.overlap χ') :
    ((chart1 hov hne).symm z).1 = z :=
  (chart1 hov hne).apply_symm_apply (z := z) hz

/-- The chart `χ' ∘ χ⁻¹ : O → χ'(V ∩ V')` of the M-polyfold `O`. -/
noncomputable def chart2 : MChart (LocalModel.ofRelOpen hov).O where
  model := LocalModel.ofRelOpen hov'
  toPartialEquiv :=
    { toFun := fun y => χ.transition χ' y.1
      invFun := fun w => (chart1 hov hne).symm (χ'.transition χ w)
      source := univ
      target := χ'.overlap χ
      map_source' := fun y _ => χ.transition_mapsTo χ' y.2
      map_target' := fun _ _ => mem_univ _
      left_inv' := fun y _ => by
        rw [trans_trans y.2]
        exact (chart1 hov hne).symm_apply_apply (mem_univ y)
      right_inv' := fun w hw => by
        change χ.transition χ' ((chart1 hov hne).symm (χ'.transition χ w)).1 = w
        have hw' : χ'.transition χ w ∈ χ.overlap χ' := χ'.transition_mapsTo χ hw
        rw [chart1_val hov hne hw']
        exact trans_trans hw }
  isOpen_source := isOpen_univ
  target_eq := rfl
  continuousOn_toFun :=
    ((h.1.continuousOn (χ.isScRetract_overlap χ')).comp_continuous continuous_subtype_val
      fun y => y.2).continuousOn
  continuousOn_invFun :=
    (chart1 hov hne).continuousOn_invFun.comp (h.2.continuousOn (χ'.isScRetract_overlap χ))
      (χ'.transition_mapsTo χ)

theorem overlap21 : (chart2 h hov hov' hne).overlap (chart1 hov hne) = χ'.overlap χ := by
  ext w
  constructor
  · rintro ⟨y, -, rfl⟩
    exact χ.transition_mapsTo χ' y.2
  · intro hw
    refine ⟨(chart1 hov hne).symm (χ'.transition χ w), ⟨mem_univ _, mem_univ _⟩, ?_⟩
    change χ.transition χ' ((chart1 hov hne).symm (χ'.transition χ w)).1 = w
    rw [chart1_val hov hne (χ'.transition_mapsTo χ hw)]
    exact trans_trans hw

theorem overlap12 : (chart1 hov hne).overlap (chart2 h hov hov' hne) = χ.overlap χ' := by
  ext z
  constructor
  · rintro ⟨y, -, rfl⟩
    exact y.2
  · intro hz
    exact ⟨⟨z, hz⟩, ⟨mem_univ _, mem_univ _⟩, rfl⟩

theorem chart2_compatible : (chart2 h hov hov' hne).Compatible (chart1 hov hne) := by
  unfold MChart.Compatible
  rw [overlap21, overlap12]
  constructor
  · refine h.2.congr fun w hw => ?_
    change χ'.transition χ w = ((chart1 hov hne).symm (χ'.transition χ w)).1
    rw [chart1_val hov hne (χ'.transition_mapsTo χ hw)]
  · refine h.1.congr fun z hz => ?_
    change χ.transition χ' z = χ.transition χ' ((chart1 hov hne).symm z).1
    rw [chart1_val hov hne hz]

theorem chart2_isChart : (hov.toMPolyfold hne).IsChart (chart2 h hov hov' hne) := by
  intro ψ hψ
  rw [mem_singleton_iff.1 hψ]
  exact chart2_compatible h hov hov' hne

include h hov hov' hne in
/-- `C^∞` of the transition map of two compatible project corner charts, from B applied to the
M-polyfold `O` with the corner atlas `{chart1, chart2}`. -/
theorem contDiff_of_B (hB : B) (hχ : χ.IsCornerChart) (hχ' : χ'.IsCornerChart) :
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (χ.transition χ') (χ.overlap χ') := by
  have := hχ.finiteDimensional
  have := hχ'.finiteDimensional
  set P := hov.toMPolyfold hne
  set S : Set (MChart (LocalModel.ofRelOpen hov).O) := {chart1 hov hne, chart2 h hov hov' hne}
  have h1 : P.IsChart (chart1 hov hne) := MPolyfold.isChart_of_mem _ (mem_singleton _)
  have h2 : P.IsChart (chart2 h hov hov' hne) := chart2_isChart h hov hov' hne
  have hS : IsCornerAtlasB P S := by
    refine ⟨?_, fun ψ hψ ψ' hψ' => ?_, fun y => ⟨chart1 hov hne, mem_insert _ _, mem_univ y⟩,
      ?_⟩
    · rintro ψ (rfl | rfl)
      · exact ⟨hχ.finiteDimensional, fun m => χ.model.E.toBase_surjective m, hov⟩
      · exact ⟨hχ'.finiteDimensional, fun m => χ'.model.E.toBase_surjective m, hov'⟩
    · have hc : ∀ ψ ∈ S, P.IsChart ψ := by
        rintro ψ (rfl | rfl)
        · exact h1
        · exact h2
      exact MPolyfold.IsChart.compatible P (hc ψ hψ) (hc ψ' hψ')
    · rintro ψ (rfl | rfl)
      · exact h1
      · exact h2
  have hc := ((hB _ P S hS).1 (chart1 hov hne) (mem_insert _ _) (chart2 h hov hov' hne)
    (mem_insert_of_mem _ (mem_singleton _))).2.2.2.2
  change ContDiffOn ℝ _ _ ((chart1 hov hne).overlap (chart2 h hov hov' hne)) at hc
  rw [overlap12] at hc
  refine hc.congr fun z hz => ?_
  change χ.transition χ' z = χ.transition χ' ((chart1 hov hne).symm z).1
  rw [chart1_val hov hne hz]

end BtoA

theorem B_to_A : B → A := by
  intro hB
  refine ⟨fun {X} _ {χ χ'} hχ hχ' h => ?_, fun {X} _ {χ} hχ χ' => relOpen_overlap hχ χ'⟩
  rcases (χ.overlap χ').eq_empty_or_nonempty with he | hne
  · rw [he]; exact contDiffOn_empty
  · exact contDiff_of_B h (relOpen_overlap hχ.isRelOpenInQuadrant χ')
      (relOpen_overlap hχ'.isRelOpenInQuadrant χ) hne hB hχ hχ'

#rt_check RoundTrip.V4_2.A_to_B [Polyfold.MChart.IsCornerChart.contDiffOn_transition, Polyfold.MChart.isRelOpenInQuadrant_overlap]
#rt_check RoundTrip.V4_2.B_to_A [Polyfold.MChart.IsCornerChart.contDiffOn_transition, Polyfold.MChart.isRelOpenInQuadrant_overlap]
#rt_overlap RoundTrip.V4_2.B_to_A [Polyfold.MChart.IsCornerChart.contDiffOn_transition, Polyfold.MChart.isRelOpenInQuadrant_overlap]

end RoundTrip.V4_2
