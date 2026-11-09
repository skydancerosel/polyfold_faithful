import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V2_10

/-! Round trip for V2_10 (Definition 2.11: charts and their compatibility).

`A` is the conjunction of the types of `Polyfold.MChart.isScRetract_overlap`,
`Polyfold.MChart.compatible_self`, `Polyfold.MChart.Compatible.restrict` and
`Polyfold.MChart.compatible_of_locally`, universe instantiated at `0` (B lives in `Type`).
`MChart`, `MChart.overlap`, `MChart.transition`, `MChart.Compatible` are definitions
(vocabulary); B characterizes them.

Glue: a project chart gives the homeomorphism `V ≃ₜ O` (`chartHomeo`), and B's chart data
`(V, M, φ, e)` with a point `x₀ ∈ V` gives a project chart (`mkChart`, junk value `x₀` for the
inverse off `O`).  Compatibility: B's transition `transB` agrees with `MChart.transition` on the
overlap, `ψ(V' ∩ V) = ψ(V ∩ V')`, and B's existential reading of Definition 2.7 is the project's
universal one on a retract (`isScSmoothRetractMap_iff_exists`, item V2_6), the overlap being a
retract by A's `isScRetract_overlap`.

`B → A`: `isScRetract_overlap` comes from B (a) + (d) (empty overlaps via Proposition 2.10 (1)
with `W = ∅`).  `compatible_self`, `Compatible.restrict` and `compatible_of_locally` are not in the
text's Definition 2.11 nor in B; they are re-proved directly (the project's arguments:
`isScSmoothRetractMap_id`, `Compatible.restrict_left/right`, the chain rule and locality), with
the overlap-retract fact taken from B. -/

namespace RoundTrip.V2_10
open Polyfold Set

/-- The project's statement, universe instantiated at `0`. -/
def A : Prop :=
  (type_of% @Polyfold.MChart.isScRetract_overlap.{0}) ∧
    (type_of% @Polyfold.MChart.compatible_self.{0}) ∧
    (type_of% @Polyfold.MChart.Compatible.restrict.{0}) ∧
    (type_of% @Polyfold.MChart.compatible_of_locally.{0})

theorem A_holds : A :=
  ⟨@Polyfold.MChart.isScRetract_overlap.{0}, @Polyfold.MChart.compatible_self.{0},
    @Polyfold.MChart.Compatible.restrict.{0}, @Polyfold.MChart.compatible_of_locally.{0}⟩

section Glue

variable {X : Type} [TopologicalSpace X]

/-- A project chart restricts to a homeomorphism `V ≃ₜ O`. -/
def chartHomeo (c : MChart X) : c.source ≃ₜ c.model.O where
  toFun v := ⟨c v, c.mapsTo_model v v.2⟩
  invFun z := ⟨c.symm z, c.symm_mapsTo z.2⟩
  left_inv v := Subtype.ext (c.symm_apply_apply v.2)
  right_inv z := Subtype.ext (c.apply_symm_apply z.2)
  continuous_toFun := (continuousOn_iff_continuous_domRestrict.1 c.continuousOn_toFun).subtype_mk _
  continuous_invFun :=
    (continuousOn_iff_continuous_domRestrict.1 c.continuousOn_invFun).subtype_mk _

theorem isChartB_of_chart (c : MChart X) :
    IsChartB c.source c.model (c.toPartialEquiv : X → c.model.E.lvl 0) :=
  ⟨c.isOpen_source, chartHomeo c, fun _ => rfl⟩

open Classical in
/-- B's chart data, with a point `x₀` (junk value of the inverse), as a project chart. -/
noncomputable def mkChart (x₀ : X) (V : Set X) (M : LocalModel) (φ : X → M.E.lvl 0)
    (hV : IsOpen V) (e : V ≃ₜ M.O) (he : ∀ x : V, (e x : M.E.lvl 0) = φ x) : MChart X where
  model := M
  toPartialEquiv :=
    { toFun := φ
      invFun := fun z => if h : z ∈ M.O then (e.symm ⟨z, h⟩ : X) else x₀
      source := V
      target := M.O
      map_source' := fun x hx => by rw [← he ⟨x, hx⟩]; exact (e ⟨x, hx⟩).2
      map_target' := fun z hz => by simp only [dif_pos hz]; exact (e.symm ⟨z, hz⟩).2
      left_inv' := fun x hx => by
        have h1 : φ x ∈ M.O := by rw [← he ⟨x, hx⟩]; exact (e ⟨x, hx⟩).2
        simp only [dif_pos h1]
        have : (⟨φ x, h1⟩ : M.O) = e ⟨x, hx⟩ := Subtype.ext (he ⟨x, hx⟩).symm
        rw [this, e.symm_apply_apply]
      right_inv' := fun z hz => by
        simp only [dif_pos hz]
        rw [← he (e.symm ⟨z, hz⟩), e.apply_symm_apply] }
  isOpen_source := hV
  target_eq := rfl
  continuousOn_toFun := by
    show ContinuousOn φ V
    rw [continuousOn_iff_continuous_domRestrict]
    have : V.domRestrict φ = fun v => (e v : M.E.lvl 0) := funext fun v => (he v).symm
    rw [this]; exact continuous_subtype_val.comp e.continuous
  continuousOn_invFun := by
    show ContinuousOn (fun z => if h : z ∈ M.O then (e.symm ⟨z, h⟩ : X) else x₀) M.O
    rw [continuousOn_iff_continuous_domRestrict]
    have : M.O.domRestrict (fun z => if h : z ∈ M.O then (e.symm ⟨z, h⟩ : X) else x₀) =
        fun z => (e.symm z : X) := funext fun z => by
      show (if h : (z : M.E.lvl 0) ∈ M.O then (e.symm ⟨z, h⟩ : X) else x₀) = _
      rw [dif_pos z.2]
    rw [this]; exact continuous_subtype_val.comp e.symm.continuous

/-- On a retract, the project's (universal) Definition 2.7 is B's (existential) one, for maps
agreeing on `O`. -/
theorem retractMap_iff {E E' : ScBanach} {C O : Set (E 0)} {C' O' : Set (E' 0)}
    (hO : IsScRetract E C O) {f g : E 0 → E' 0} (hfg : EqOn f g O) :
    IsScSmoothRetractMap E C O E' C' O' f ↔ IsScSmoothRetractMapB E C O E' O' g := by
  rw [isScSmoothRetractMap_iff_exists hO]
  unfold IsScSmoothRetractMapB
  constructor
  · rintro ⟨hm, R, hR, hs⟩
    refine ⟨fun x hx => hfg hx ▸ hm hx, R, hR, hs.congr R.isScDomain fun y hy => ?_⟩
    simp only [Function.comp_apply]
    exact hfg (hR ▸ R.apply_mem_retract hy)
  · rintro ⟨hm, R, hR, hs⟩
    refine ⟨fun x hx => (hfg hx).symm ▸ hm hx, R, hR, hs.congr R.isScDomain fun y hy => ?_⟩
    simp only [Function.comp_apply]
    exact (hfg (hR ▸ R.apply_mem_retract hy)).symm

/-- B's transition map is the project's on the overlap. -/
theorem transition_eqOn_transB (c c' : MChart X) :
    EqOn (c.transition c') (transB c.source (c.toPartialEquiv : X → c.model.E.lvl 0)
      (c'.toPartialEquiv : X → c'.model.E.lvl 0)) (c.overlap c') := by
  rintro _ ⟨x, hx, rfl⟩
  have h : ∃ y ∈ c.source, c.toPartialEquiv y = c x := ⟨x, hx.1, rfl⟩
  unfold transB
  rw [dif_pos h]
  have hy := Classical.choose_spec h
  rw [c.toPartialEquiv.injOn hy.1 hx.1 hy.2, c.transition_apply c' hx.1]

theorem overlap_comm (c c' : MChart X) :
    c'.overlap c = (c'.toPartialEquiv : X → c'.model.E.lvl 0) '' (c.source ∩ c'.source) := by
  unfold MChart.overlap; rw [inter_comm]

/-- The project's compatibility is B's, given that overlaps are retracts. -/
theorem compatible_iff (hret : ∀ c c' : MChart X, IsScRetract c.model.E c.model.C (c.overlap c'))
    (c c' : MChart X) :
    c.Compatible c' ↔
      CompatibleB c.source c.model (c.toPartialEquiv : X → c.model.E.lvl 0)
        c'.source c'.model (c'.toPartialEquiv : X → c'.model.E.lvl 0) := by
  unfold MChart.Compatible CompatibleB
  have h1 := retractMap_iff (C' := c'.model.C) (O' := c'.overlap c) (hret c c')
    (transition_eqOn_transB c c')
  have h2 := retractMap_iff (C' := c.model.C) (O' := c.overlap c') (hret c' c)
    (transition_eqOn_transB c' c)
  rw [h1, h2, overlap_comm c c']
  rfl

end Glue

theorem A_to_B : A → B := by
  rintro ⟨hret, -, -, -⟩ X _
  refine ⟨fun c x hx => ⟨hx, isChartB_of_chart c⟩, ?_, compatible_iff (hret (X := X)), ?_⟩
  · rintro x V M φ ⟨hx, hV, e, he⟩
    exact ⟨mkChart x V M φ hV e he, rfl, rfl, fun _ _ => rfl⟩
  · rintro V M φ V' M' ψ ⟨hV, e, he⟩ ⟨hV', e', he'⟩
    rcases (V ∩ V').eq_empty_or_nonempty with h | ⟨x, hx⟩
    · rw [h, image_empty, ← inter_empty M.O]
      exact proposition_2_3_1_one M.isScRetract isOpen_empty
    · exact hret (mkChart x V M φ hV e he) (mkChart x V' M' ψ hV' e' he')

/-! ### `B → A` -/

section Direct

variable {X : Type} [TopologicalSpace X]

/-- Overlaps are retracts, from B (a) and (d). -/
theorem retract_of_B (hB : B) (c c' : MChart X) :
    IsScRetract c.model.E c.model.C (c.overlap c') := by
  rcases (c.source ∩ c'.source).eq_empty_or_nonempty with h | ⟨x, hx⟩
  · unfold MChart.overlap
    rw [h, image_empty, ← inter_empty c.model.O]
    exact proposition_2_3_1_one c.model.isScRetract isOpen_empty
  · exact (hB X).2.2.2 _ _ _ _ _ _ ((hB X).1 c x hx.1).2 ((hB X).1 c' x hx.2).2

/-- Self-compatibility (the project's argument). -/
theorem compatible_self' (φ : MChart X) : φ.Compatible φ := by
  have h : IsScSmoothRetractMap φ.model.E φ.model.C (φ.overlap φ) φ.model.E φ.model.C
      (φ.overlap φ) (φ.transition φ) := by
    refine (isScSmoothRetractMap_id _).congr ?_
    rintro _ ⟨x, hx, rfl⟩
    rw [id, φ.transition_apply φ hx.1]
  exact ⟨h, h⟩

/-- Locality of compatibility (the project's argument, the overlap-retract fact from B). -/
theorem compatible_of_locally' (hret : ∀ c c' : MChart X, IsScRetract c.model.E c.model.C
      (c.overlap c')) (φ ψ : MChart X) (S : Set (MChart X)) (hφ : ∀ χ ∈ S, φ.Compatible χ)
    (hψ : ∀ χ ∈ S, χ.Compatible ψ)
    (hcover : ∀ x ∈ φ.source ∩ ψ.source, ∃ χ ∈ S, x ∈ χ.source) : φ.Compatible ψ := by
  have key : ∀ (φ ψ : MChart X), (∀ χ ∈ S, φ.Compatible χ) → (∀ χ ∈ S, χ.Compatible ψ) →
      (∀ x ∈ φ.source ∩ ψ.source, ∃ χ ∈ S, x ∈ χ.source) →
      IsScSmoothRetractMap φ.model.E φ.model.C (φ.overlap ψ) ψ.model.E ψ.model.C (ψ.overlap φ)
        (φ.transition ψ) := by
    intro φ ψ hφ hψ hcover
    refine IsScSmoothRetractMap.of_locally (φ.transition_mapsTo ψ) ?_
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨χ, hχS, hxχ⟩ := hcover x hx
    set s := φ.source ∩ ψ.source ∩ χ.source with hs
    have hso : IsOpen s := (φ.isOpen_source.inter ψ.isOpen_source).inter χ.isOpen_source
    have hsφ : s ⊆ φ.source := fun y hy => hy.1.1
    obtain ⟨W, hW, hWeq⟩ := φ.exists_isOpen_image_eq hsφ hso
    refine ⟨W, hW, ?_, ?_⟩
    · have : φ x ∈ φ '' s := ⟨x, ⟨hx, hxχ⟩, rfl⟩
      rw [hWeq] at this; exact this.2
    · have hover : φ.overlap ψ ∩ W = φ '' s := by
        rw [hWeq]
        exact inter_eq_inter_of_subset (φ.overlap_subset ψ)
          (hWeq ▸ image_mono fun y hy => ⟨hy.1.1, hy.1.2⟩)
      rw [hover]
      have h1 : IsScSmoothRetractMap φ.model.E φ.model.C (φ '' s) χ.model.E χ.model.C (χ '' s)
          (φ.transition χ) := by
        have := (hφ χ hχS).1.restrict (hret φ χ) (W := W)
        have hover' : φ.overlap χ ∩ W = φ '' s := by
          rw [hWeq]
          exact inter_eq_inter_of_subset (φ.overlap_subset χ)
            (hWeq ▸ image_mono fun y hy => ⟨hy.1.1, hy.2⟩)
        rw [hover'] at this
        refine this.mono_target ?_
        rintro _ ⟨y, hy, rfl⟩
        rw [φ.transition_apply χ hy.1.1]
        exact ⟨y, hy, rfl⟩
      have h2 : IsScSmoothRetractMap χ.model.E χ.model.C (χ '' s) ψ.model.E ψ.model.C
          (ψ.overlap φ) (χ.transition ψ) := by
        have hsχ : s ⊆ χ.source := fun y hy => hy.2
        obtain ⟨W', hW', hW'eq⟩ := χ.exists_isOpen_image_eq hsχ hso
        have := (hψ χ hχS).1.restrict (hret χ ψ) (W := W')
        have hover' : χ.overlap ψ ∩ W' = χ '' s := by
          rw [hW'eq]
          exact inter_eq_inter_of_subset (χ.overlap_subset ψ)
            (hW'eq ▸ image_mono fun y hy => ⟨hy.2, hy.1.2⟩)
        rw [hover'] at this
        refine this.mono_target ?_
        rintro _ ⟨y, hy, rfl⟩
        rw [χ.transition_apply ψ hy.2]
        exact ⟨y, ⟨hy.1.2, hy.1.1⟩, rfl⟩
      have hχs : IsScRetract χ.model.E χ.model.C (χ '' s) :=
        χ.isScRetract_image (fun y hy => hy.2) hso
      refine (h2.comp h1 hχs).congr ?_
      rintro _ ⟨y, hy, rfl⟩
      exact (φ.transition_eq_comp_on ψ χ hy.1.1 hy.2).symm
  refine ⟨key φ ψ hφ hψ hcover,
    key ψ φ (fun χ hχ => (hψ χ hχ).symm) (fun χ hχ => (hφ χ hχ).symm) ?_⟩
  intro x hx
  exact hcover x ⟨hx.2, hx.1⟩

variable {φ ψ : MChart X} in
/-- Compatibility passes to the restriction of the first chart (the project's argument, the
overlap-retract fact from B). -/
theorem restrict_left' (hret : ∀ c c' : MChart X, IsScRetract c.model.E c.model.C
      (c.overlap c')) (h : φ.Compatible ψ) {s : Set X} (hs : s ⊆ φ.source)
    (hso : IsOpen s) : (φ.restrict hs hso).Compatible ψ := by
  obtain ⟨W, hW, hWeq⟩ := φ.overlap_restrict_eq ψ hs hso
  constructor
  · rw [hWeq]
    refine (h.1.restrict (hret φ ψ)).mono_target ?_
    rw [← hWeq]
    exact (φ.restrict hs hso).transition_mapsTo ψ
  · obtain ⟨W', hW', hW'eq⟩ := ψ.exists_isOpen_image_eq (s := ψ.source ∩ s)
      inter_subset_left (ψ.isOpen_source.inter hso)
    have hover : ψ.overlap (φ.restrict hs hso) = ψ.overlap φ ∩ W' := by
      change ψ '' (ψ.source ∩ s) = ψ.overlap φ ∩ W'
      rw [hW'eq]
      ext z
      constructor
      · rintro ⟨hz, hzW⟩
        refine ⟨?_, hzW⟩
        have : z ∈ ψ '' (ψ.source ∩ s) := by rw [hW'eq]; exact ⟨hz, hzW⟩
        obtain ⟨x, hx, rfl⟩ := this
        exact ⟨x, ⟨hx.1, hs hx.2⟩, rfl⟩
      · rintro ⟨hz, hzW⟩
        exact ⟨ψ.overlap_subset φ hz, hzW⟩
    rw [hover]
    refine (h.2.restrict (hret ψ φ)).mono_target ?_
    rw [← hover]
    exact ψ.transition_mapsTo (φ.restrict hs hso)

end Direct

theorem B_to_A : B → A := by
  intro hB
  refine ⟨fun {X} _ c c' => retract_of_B hB c c', fun {X} _ φ => compatible_self' φ,
    fun {X} _ φ ψ h s hs hso t ht hto =>
      (restrict_left' (retract_of_B hB) (restrict_left' (retract_of_B hB) h hs hso).symm ht hto).symm,
    fun {X} _ φ ψ S hφ hψ hcover => compatible_of_locally' (retract_of_B hB) φ ψ S hφ hψ hcover⟩

#rt_check RoundTrip.V2_10.A_to_B [Polyfold.MChart.isScRetract_overlap,
  Polyfold.MChart.compatible_self, Polyfold.MChart.Compatible.restrict,
  Polyfold.MChart.compatible_of_locally]
#rt_check RoundTrip.V2_10.B_to_A [Polyfold.MChart.isScRetract_overlap,
  Polyfold.MChart.compatible_self, Polyfold.MChart.Compatible.restrict,
  Polyfold.MChart.compatible_of_locally]
#rt_overlap RoundTrip.V2_10.B_to_A [Polyfold.MChart.isScRetract_overlap,
  Polyfold.MChart.compatible_self, Polyfold.MChart.Compatible.restrict,
  Polyfold.MChart.compatible_of_locally]

end RoundTrip.V2_10
