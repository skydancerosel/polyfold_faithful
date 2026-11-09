import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V2_50

/-! Round trip for V2_50 (Proposition 2.44: local faces and their intersections are tame).

`A` is the conjunction of the types of the theorems among the item's declarations:
`MPolyfold.proposition_2_5_16`, `proposition_2_5_14`, `MPolyfold.proposition_2_5_16_corner`
(universe `0`), `LocalModel.proposition_2_5_15_isTame`, `corner_retraction`, `corner_tameModel`
and `degIndexWith_eq_quadrantDeg_cornerProj_add_card`.  `cornerIncl`, `cornerProj`, `cornerKill`
are definitions (vocabulary).

Neither direction is proved.  Diagnosis:

* A states Proposition 2.44 on the model of a tame chart `φ : V → O`: the faces of the M-polyfold
  `O` through `φ x` (count `d_X(x)`, each a tame sub-M-polyfold OF `O` with `d_F(φ x) + 1 = d_X(x)`),
  and, for `σ ⊆ I(φ x)`, the GERM at `x` of the corner: `A_σ = φ⁻¹(B ∩ ⋂_{i ∈ σ} F_i)` for some
  small open `B ∋ φ x` is a tame sub-M-polyfold of `X` with `d_{A_σ} + #σ = d_X` on `A_σ`.
  "Codimension" is not stated (it is implicit as the number of quadrant coordinates removed).
* B takes an open `V ∋ x` with its induced structure, the faces of `V` through `x`, and asserts
  that each face `G` and each intersection `⋂₀ σ` of WHOLE faces of `V` is a tame
  sub-M-polyfold of `X`, plus a codimension statement (`HasCodimAtB`: cut out near `x`, in a
  chart, by a closed subspace of codimension `#σ`).

`A → B` is believed true (take `V = dom φ`) but needs work beyond glue: (i) the transfer between
faces of `↥V` (subPolyfold) and faces of `O` (done here for the count, `A_to_B_count`, with the
V2_48 glue); (ii) faces of `O` through `φ x` ↔ indices `I(φ x)` (Lemma 2.40); (iii) the germ-to-
global step: `⋂_{i∈σ} F_i` is a tame sub-M-polyfold at EVERY one of its points, which needs
`corner_retraction`/`corner_tameModel` at every point `z` of the intersection (identifying the
faces they produce at `z` with the `F_i`) and re-running the chart construction of the proof of
`proposition_2_5_16_corner` (`faceChart`, `isSubMPolyfold_of_local`, `isTame_of_forall_exists_chart`)
pointwise; likewise each whole face `φ⁻¹(F)` must be moved from a sub-M-polyfold of `O` to one of
`X`; (iv) the codimension: `rank(E₀/⋂_{i∈σ} ker λ_i) = #σ` and `φ(A ∩ W) = φ(W) ∩ L` with `W` from
`corner_retraction`.  None of (iii)–(iv) is in A.

`B → A` fails genuinely: B's `V` is an unspecified neighbourhood with no chart, so it says nothing
about the faces of a chart model `O` (`proposition_2_5_16`), about whole faces of a tame retract
(`proposition_2_5_15_isTame`), or the constructions `corner_retraction`, `corner_tameModel`,
`degIndexWith_eq_quadrantDeg_cornerProj_add_card`; the local corner of `proposition_2_5_16_corner`
also has `d_A + #σ = d_X` at every point of `A`, B only at `x`. -/

namespace RoundTrip.V2_50
open Polyfold Set

/-- The project's statement (universe `0`). -/
def A : Prop :=
  (type_of% @Polyfold.MPolyfold.proposition_2_5_16.{0}) ∧ (type_of% @Polyfold.proposition_2_5_14.{0}) ∧
    (type_of% @Polyfold.LocalModel.proposition_2_5_15_isTame) ∧
    (type_of% @Polyfold.MPolyfold.proposition_2_5_16_corner.{0}) ∧
    (type_of% @Polyfold.corner_retraction) ∧ (type_of% @Polyfold.corner_tameModel) ∧
    (type_of% @Polyfold.degIndexWith_eq_quadrantDeg_cornerProj_add_card)

theorem A_holds : A :=
  ⟨@Polyfold.MPolyfold.proposition_2_5_16.{0}, @Polyfold.proposition_2_5_14.{0},
    @Polyfold.LocalModel.proposition_2_5_15_isTame, @Polyfold.MPolyfold.proposition_2_5_16_corner.{0},
    @Polyfold.corner_retraction, @Polyfold.corner_tameModel,
    @Polyfold.degIndexWith_eq_quadrantDeg_cornerProj_add_card⟩

/-! ### Partial result: B's face count, from A (glue as in V2_48) -/

section Homeo

variable {α β : Type} [TopologicalSpace α] [TopologicalSpace β]

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

noncomputable def chartHomeo (φ : MChart X) : φ.source ≃ₜ φ.model.O where
  toFun y := ⟨φ y, φ.mapsTo_model y y.2⟩
  invFun z := ⟨φ.symm z, φ.symm_mapsTo z.2⟩
  left_inv y := Subtype.ext (φ.symm_apply_apply y.2)
  right_inv z := Subtype.ext (φ.apply_symm_apply z.2)
  continuous_toFun :=
    (continuousOn_iff_continuous_domRestrict.1 φ.continuousOn_toFun).subtype_mk _
  continuous_invFun :=
    (continuousOn_iff_continuous_domRestrict.1 φ.continuousOn_invFun).subtype_mk _

theorem isSubMPolyfold_of_isOpen {V : Set X} (hV : IsOpen V) : P.IsSubMPolyfold V := fun a ha =>
  ⟨V, hV, ha, id, mapsTo_id _, (P.isScSmoothMap_id).mono hV (subset_univ _), fun _ _ => rfl,
    by simp⟩

def openSubData {V : Set X} (hV : IsOpen V) : P.SubData V where
  V := V
  r := id
  isOpen := hV
  mapsTo := mapsTo_id _
  isScSmoothOn := (P.isScSmoothMap_id).mono hV (subset_univ _)
  idem _ _ := rfl
  image := by simp

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

/-- The first clause of `B` (the local face count), with the neighbourhood's existence. -/
def B_count : Prop :=
  ∀ (X : Type) [TopologicalSpace X] [T2Space X] [ParacompactSpace X] (P : MPolyfold X),
    P.IsTame → ∀ x : X, ∃ (V : Set X) (_ : IsOpen V) (hxV : x ∈ V) (hV : P.IsSubMPolyfold V)
      (_ : ParacompactSpace V),
      {G : Set V | (P.subPolyfold hV).IsFace G ∧ (⟨x, hxV⟩ : V) ∈ G}.encard = (P.degIndex x : ℕ∞)

theorem A_to_B_count : A → B_count := by
  intro hA X _ _ _ P hP x
  obtain ⟨-, h242, -⟩ := hA
  obtain ⟨⟨φ, hφ, hx, -, hdO, hfs⟩, -⟩ := h242 P hP x
  have : ParacompactSpace φ.source := P.paracompactSpace_subtype φ.source
  have hV : P.IsSubMPolyfold φ.source := isSubMPolyfold_of_isOpen P φ.isOpen_source
  refine ⟨φ.source, φ.isOpen_source, hx, hV, inferInstance, ?_⟩
  set y : φ.source := ⟨x, hx⟩
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

#rt_check RoundTrip.V2_50.A_to_B_count [Polyfold.MPolyfold.proposition_2_5_16,
  Polyfold.proposition_2_5_14, Polyfold.LocalModel.proposition_2_5_15_isTame,
  Polyfold.MPolyfold.proposition_2_5_16_corner, Polyfold.corner_retraction,
  Polyfold.corner_tameModel, Polyfold.degIndexWith_eq_quadrantDeg_cornerProj_add_card]

end RoundTrip.V2_50
