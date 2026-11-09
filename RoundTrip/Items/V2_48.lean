import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V2_48

/-! Round trip for V2_48 (Proposition 2.42: local face count in a tame M-polyfold, and the global
bound).

`A` is the conjunction of the types of `Polyfold.proposition_2_5_14`,
`Polyfold.MPolyfold.faces_encard_le` and `Polyfold.MPolyfold.IsTame.exists_chart` (universe `0`).

The two sides express "the faces of `V`" differently.  A (`proposition_2_5_14`) takes `V = dom φ`
for a tame chart `φ : V → O` and states everything on the model: `d_X(y) = d_C(φ y) = d_O(φ y)` on
`V` and the M-polyfold `O` is face-structured.  B uses the induced sub-M-polyfold structure
`P.subPolyfold hV` on the subtype `↥V` itself: faces of that structure and its `d_V`.

`A → B` (glue, new): for `V = dom φ`, (i) `V` is a sub-M-polyfold (`r = id`), paracompact
(`paracompactSpace_subtype`); (ii) the inclusion `↥V → X` is an sc-diffeomorphism onto the open
`V` (`subPolyfold_inclusion_isScSmooth`, `subPolyfold_retraction_isScSmooth` with `r = id`), so
`d_V = d_X` by Proposition 2.24 (`proposition_2_4_4`, item V2_28); (iii) `φ : ↥V ≃ₜ ↥O` is a
homeomorphism with `d_O ∘ φ = d_X = d_V`, and a homeomorphism respecting the degeneracy indices
maps faces to faces (`faces_encard_homeomorph`), so the count of faces of `V` through `y` is the
count of faces of `O` through `φ y`, which is `d_O(φ y) = d_X(y)`.  The global bound is
`faces_encard_le`.

`B → A`: `faces_encard_le` is B's global clause.  `IsTame.exists_chart` is the definition of
tameness unpacked (proved directly).  The local clause of `proposition_2_5_14` is a statement about
the chart model `O`, not about `V`, and B's local clause (about `↥V`) does not give the chart; it
is proved from other items' theorems: a tame chart (direct), `d_X = d_C ∘ φ`
(`degIndex_eq_chartDegIndex_of_isTameRetract`, V2_42), `d_O = d_C`
(`degIndex_toMPolyfold_of_isTameWith`, V2_42) and `O` face-structured (`corollary_2_5_13`, V2_47). -/

namespace RoundTrip.V2_48
open Polyfold Set

/-- The project's statement (universe `0`). -/
def A : Prop :=
  (type_of% @Polyfold.proposition_2_5_14.{0}) ∧ (type_of% @Polyfold.MPolyfold.faces_encard_le.{0}) ∧
    (type_of% @Polyfold.MPolyfold.IsTame.exists_chart.{0})

theorem A_holds : A :=
  ⟨@Polyfold.proposition_2_5_14.{0}, @Polyfold.MPolyfold.faces_encard_le.{0},
    @Polyfold.MPolyfold.IsTame.exists_chart.{0}⟩

/-! ### Glue -/

section Homeo

variable {α β : Type} [TopologicalSpace α] [TopologicalSpace β]

/-- A homeomorphism respecting two "degeneracy indices" maps faces (closures of components of
`{d = 1}`) to faces; the numbers of faces through corresponding points agree. -/
theorem faces_encard_homeomorph (e : α ≃ₜ β) (dα : α → ℕ) (dβ : β → ℕ)
    (hd : ∀ a, dβ (e a) = dα a) (a : α) :
    {F : Set α | (∃ x, dα x = 1 ∧ F = closure (connectedComponentIn {y | dα y = 1} x)) ∧ a ∈ F}.encard
      = {G : Set β | (∃ z, dβ z = 1 ∧ G = closure (connectedComponentIn {w | dβ w = 1} z)) ∧
          e a ∈ G}.encard := by
  have hS : e '' {y | dα y = 1} = {w | dβ w = 1} := by
    ext w
    constructor
    · rintro ⟨y, hy, rfl⟩; change dβ (e y) = 1; rw [hd]; exact hy
    · intro hw
      refine ⟨e.symm w, ?_, e.apply_symm_apply w⟩
      change dα (e.symm w) = 1
      rw [← hd, e.apply_symm_apply]; exact hw
  have himg : ∀ x, dα x = 1 → e '' closure (connectedComponentIn {y | dα y = 1} x) =
      closure (connectedComponentIn {w | dβ w = 1} (e x)) := fun x hx => by
    rw [e.image_closure, e.image_connectedComponentIn (show x ∈ {y | dα y = 1} from hx), hS]
  have hinj : InjOn (fun F : Set α => e '' F) univ := fun s _ t _ hst =>
    (Set.image_injective.2 e.injective) hst
  have hset : (fun F : Set α => e '' F) ''
      {F : Set α | (∃ x, dα x = 1 ∧ F = closure (connectedComponentIn {y | dα y = 1} x)) ∧ a ∈ F}
      = {G : Set β | (∃ z, dβ z = 1 ∧ G = closure (connectedComponentIn {w | dβ w = 1} z)) ∧
          e a ∈ G} := by
    ext G
    constructor
    · rintro ⟨F, ⟨⟨x, hx, rfl⟩, haF⟩, rfl⟩
      exact ⟨⟨e x, by rw [hd]; exact hx, himg x hx⟩, mem_image_of_mem e haF⟩
    · rintro ⟨⟨z, hz, rfl⟩, haG⟩
      have hx : dα (e.symm z) = 1 := by rw [← hd, e.apply_symm_apply]; exact hz
      refine ⟨closure (connectedComponentIn {y | dα y = 1} (e.symm z)), ⟨⟨_, hx, rfl⟩, ?_⟩, ?_⟩
      · have := himg _ hx
        rw [e.apply_symm_apply] at this
        rw [← this] at haG
        obtain ⟨b, hb, hba⟩ := haG
        rwa [e.injective hba] at hb
      · have := himg _ hx
        rwa [e.apply_symm_apply] at this
  rw [← hset, (hinj.mono (subset_univ _)).encard_image]

end Homeo

section Glue

variable {X : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] (P : MPolyfold X)

/-- A chart `φ : V → O` as a homeomorphism `↥V ≃ₜ ↥O`. -/
noncomputable def chartHomeo (φ : MChart X) : φ.source ≃ₜ φ.model.O where
  toFun y := ⟨φ y, φ.mapsTo_model y y.2⟩
  invFun z := ⟨φ.symm z, φ.symm_mapsTo z.2⟩
  left_inv y := Subtype.ext (φ.symm_apply_apply y.2)
  right_inv z := Subtype.ext (φ.apply_symm_apply z.2)
  continuous_toFun :=
    (continuousOn_iff_continuous_domRestrict.1 φ.continuousOn_toFun).subtype_mk _
  continuous_invFun :=
    (continuousOn_iff_continuous_domRestrict.1 φ.continuousOn_invFun).subtype_mk _

/-- An open set is a sub-M-polyfold (`r = id`). -/
theorem isSubMPolyfold_of_isOpen {V : Set X} (hV : IsOpen V) : P.IsSubMPolyfold V := fun a ha =>
  ⟨V, hV, ha, id, mapsTo_id _, (P.isScSmoothMap_id).mono hV (subset_univ _), fun _ _ => rfl,
    by simp⟩

/-- The sub-M-polyfold data `(V, id)` of an open set. -/
def openSubData {V : Set X} (hV : IsOpen V) : P.SubData V where
  V := V
  r := id
  isOpen := hV
  mapsTo := mapsTo_id _
  isScSmoothOn := (P.isScSmoothMap_id).mono hV (subset_univ _)
  idem _ _ := rfl
  image := by simp

/-- For an open `V`, `d_V = d_X`: the inclusion `↥V → X` is an sc-diffeomorphism onto `V`
(Proposition 2.21 (1), (2) with `r = id`), and Proposition 2.24. -/
theorem degIndex_subPolyfold_of_isOpen {V : Set X} (hVo : IsOpen V) [ParacompactSpace V]
    (hV : P.IsSubMPolyfold V) (y : V) : (P.subPolyfold hV).degIndex y = P.degIndex y := by
  set d := openSubData P hVo
  have hdiff : (P.subPolyfold hV).IsScDiffeoOn P Subtype.val (d.retractInto y) univ V := by
    refine ⟨MPolyfold.subPolyfold_inclusion_isScSmooth hV,
      MPolyfold.subPolyfold_retraction_isScSmooth hV d y, fun z _ => z.2, fun _ _ => mem_univ _,
      fun z _ => ?_, fun x hx => ?_⟩
    · exact Subtype.ext (d.retractInto_val y (show z.1 ∈ d.V from z.2))
    · exact d.retractInto_val y (show x ∈ d.V from hx)
  exact proposition_2_4_4 hdiff (mem_univ y)

end Glue

theorem A_to_B : A → B := by
  intro hA X _ _ _ P hP
  obtain ⟨h242, hle, -⟩ := hA
  refine ⟨fun x => ?_, hle P hP⟩
  obtain ⟨⟨φ, hφ, hx, -, hdO, hfs⟩, -⟩ := h242 P hP x
  have : ParacompactSpace φ.source := P.paracompactSpace_subtype φ.source
  have hV : P.IsSubMPolyfold φ.source := isSubMPolyfold_of_isOpen P φ.isOpen_source
  refine ⟨φ.source, φ.isOpen_source, hx, hV, inferInstance, fun y => ?_⟩
  have hdV := degIndex_subPolyfold_of_isOpen P φ.isOpen_source hV y
  refine ⟨?_, hdV⟩
  have hne : φ.model.O.Nonempty := ⟨φ y, φ.mapsTo_model y y.2⟩
  have hd : ∀ z : φ.source, (φ.model.toMPolyfold hne).degIndex (chartHomeo φ z) =
      (P.subPolyfold hV).degIndex z := fun z => by
    rw [degIndex_subPolyfold_of_isOpen P φ.isOpen_source hV z]
    exact hdO z.1 z.2
  have := faces_encard_homeomorph (chartHomeo φ) ((P.subPolyfold hV).degIndex)
    ((φ.model.toMPolyfold hne).degIndex) hd y
  change {F : Set φ.source | (P.subPolyfold hV).IsFace F ∧ y ∈ F}.encard = _ at this
  rw [this]
  change {G : Set φ.model.O | (φ.model.toMPolyfold hne).IsFace G ∧ chartHomeo φ y ∈ G}.encard = _
  rw [hfs hne (chartHomeo φ y)]
  exact congrArg (fun k : ℕ => (k : ℕ∞)) (hdO y.1 y.2)

/-! ### `B → A` -/

/-- `IsTame.exists_chart`, directly from the definition of tameness. -/
theorem exists_chart' : type_of% @Polyfold.MPolyfold.IsTame.exists_chart.{0} := by
  intro X _ _ _ P hP x
  obtain ⟨A, hA, htame⟩ := hP
  obtain ⟨φ, hφ, hx⟩ := A.cover x
  exact ⟨φ, P.isChart_of_mem_equiv hA hφ, hx, htame φ hφ⟩

theorem B_to_A : B → A := by
  intro hB
  refine ⟨?_, @fun X _ _ _ P hP x => (hB X P hP).2 x, exists_chart'⟩
  intro X _ _ _ P hP x
  refine ⟨?_, (hB X P hP).2 x⟩
  obtain ⟨φ, hφ, hx, htame⟩ := exists_chart' P hP x
  obtain ⟨R, hRO, hRt⟩ := htame
  obtain ⟨n, W, T, hT⟩ := φ.model.isPartialQuadrant
  have hdX : ∀ y ∈ φ.source, P.degIndex y = Polyfold.degIndex φ.model.E φ.model.C (φ y) :=
    fun y hy => P.degIndex_eq_chartDegIndex_of_isTameRetract hφ ⟨R, hRO, hRt⟩ hy
  refine ⟨φ, hφ, hx, hdX, fun y hy => ?_, fun hne => corollary_2_5_13 φ.model hne ⟨R, hRO, hRt⟩⟩
  exact (φ.model.degIndex_toMPolyfold_of_isTameWith _ R hRO hT (hRt n W T hT) _).trans
    (hdX y hy).symm

#rt_check RoundTrip.V2_48.A_to_B [Polyfold.proposition_2_5_14, Polyfold.MPolyfold.faces_encard_le,
  Polyfold.MPolyfold.IsTame.exists_chart]
#rt_check RoundTrip.V2_48.B_to_A [Polyfold.proposition_2_5_14, Polyfold.MPolyfold.faces_encard_le,
  Polyfold.MPolyfold.IsTame.exists_chart]
#rt_overlap RoundTrip.V2_48.B_to_A [Polyfold.proposition_2_5_14, Polyfold.MPolyfold.faces_encard_le,
  Polyfold.MPolyfold.IsTame.exists_chart]

end RoundTrip.V2_48
