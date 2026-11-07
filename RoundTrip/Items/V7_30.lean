import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V7_30

/-! Round trip for V7_30 (the facts (1)–(4) of Proposition 2.6 recalled for the object set `A` of
an ep-subgroupoid, pp. 237–238).

`A` is the conjunction of the types of the listed theorems, at universe `0` (B lives in `Type`):
`EpGroupoid.isScSmoothMap_val_subObj` (fact (1): `i : A → X` sc-smooth and an embedding, for the
structure `subObjPolyfold hA`) and `EpGroupoid.isScSmoothOn_retractInto_subObj` (fact (2): the
project's `i⁻¹ ∘ r = retractInto a₀` is sc-smooth on `V` for every `SubData` `(V, r)`).
`EpGroupoid.subObjPolyfold` and `MPolyfold.subPolyfold` are definitions (vocabulary).

`A → B` (not proved).  B asserts ONE structure `Q` on `A` with (1), (2), (3) and (4).  With
`Q := subObjPolyfold hA` and paracompactness from the project's `paracompactSpace_subtype`, A gives
(1), (2) and the sc-smoothness half of (4) (`A_to_B_noTangent`, proved with the hypothesis; the
`(V, r)` of B is exactly a `SubData`, and every `g` agreeing with `r` on `V` is handled by
`IsScSmoothOn.congr`).  The tangent-space facts — (3) `T_aA` has an sc-complement in `T_aX`, and
`T_aA = Tr(a)T_aX` in (4) — are not in A at all: the project states them only in a chart for a
retract (`proposition_2_21_3`, `proposition_2_21_4` of Part I) and does not transport them to
`T_aX`, `T_aA` (its gap G.7; the module docstring of `SubGroupoid.lean` says so).  This is the
same missing glue as in item V2_25 (several hundred lines of tangent-map/chain-rule work:
identifying the chart image of `Ti(a)T_aA` for `subPolyfold`, and the mixed-chart computation for
`Tr(a)`); believed true, not attempted.  So the failure is proof effort, but A itself contributes
nothing to (3)/(4): those parts would be proved outright.

`B → A` (proved, outright — vacuous).  B only says SOME `Q` exists; A is about the project's
specific `subObjPolyfold hA`, so B cannot give it.  A follows from Part I's
`subPolyfold_inclusion_isScSmooth`, `subPolyfold_retraction_isScSmooth` (not items here) and
`IsEmbedding.subtypeVal`, without B. -/

namespace RoundTrip.V7_30
open Polyfold Set

/-- The project's statement (universe `0`). -/
def A : Prop :=
  (type_of% @Polyfold.EpGroupoid.isScSmoothMap_val_subObj.{0}) ∧
    (type_of% @Polyfold.EpGroupoid.isScSmoothOn_retractInto_subObj.{0})

theorem A_holds : A :=
  ⟨@Polyfold.EpGroupoid.isScSmoothMap_val_subObj.{0},
    @Polyfold.EpGroupoid.isScSmoothOn_retractInto_subObj.{0}⟩

/-- B without the tangent-space facts: (1), (2) and the sc-smoothness half of (4). -/
def B_noTangent : Prop :=
  ∀ (Obj Mor : Type) [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
    [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor]
    (X : EpGroupoid Obj Mor) (A : Set Obj),
    X.PObj.IsSubMPolyfold A → X.π ⁻¹' (X.π '' A) = A →
    ∃ (_ : ParacompactSpace A) (Q : MPolyfold A)
      (_ : Q.IsScSmoothMap X.PObj (Subtype.val : A → Obj)),
      Topology.IsEmbedding (Subtype.val : A → Obj) ∧
      (∀ a ∈ A, ∀ (V : Set Obj) (r : Obj → Obj), IsOpen V → a ∈ V → Set.MapsTo r V V →
        X.PObj.IsScSmoothOn X.PObj r V → (∀ y ∈ V, r (r y) = r y) → r '' V = A ∩ V →
        ∀ g : Obj → A, (∀ y ∈ V, (g y : Obj) = r y) → X.PObj.IsScSmoothOn Q g V) ∧
      (∀ (W : Set Obj) (r : Obj → Obj), IsOpen W → Set.MapsTo r W W →
        X.PObj.IsScSmoothOn X.PObj r W → (∀ y ∈ W, r (r y) = r y) → r '' W = A ∩ W →
        ∀ g : Obj → A, (∀ y ∈ W, (g y : Obj) = r y) → X.PObj.IsScSmoothOn Q g W)

/-- `B_noTangent` is a weakening of B. -/
theorem B_to_B_noTangent : B → B_noTangent := by
  intro hB Obj Mor _ _ _ _ _ _ X S hS hsat
  obtain ⟨hp, Q, hi, hemb, h2, -, h4⟩ := hB Obj Mor X S hS hsat
  exact ⟨hp, Q, hi, hemb, h2, fun W r hW hrW hsm hid him => (h4 W r hW hrW hsm hid him).1⟩

/-- **`A → B_noTangent`**, using A: `Q = subObjPolyfold hA`. -/
theorem A_to_B_noTangent : A → B_noTangent := by
  rintro ⟨h1, h2⟩ Obj Mor _ _ _ _ _ _ X S hS hsat
  have hA : X.IsEpSubgroupoid S := ⟨hS, hsat⟩
  have : ParacompactSpace S := X.PObj.paracompactSpace_subtype S
  have key : ∀ (V : Set Obj) (r : Obj → Obj), IsOpen V → Set.MapsTo r V V →
      X.PObj.IsScSmoothOn X.PObj r V → (∀ y ∈ V, r (r y) = r y) → r '' V = S ∩ V →
      ∀ g : Obj → S, (∀ y ∈ V, (g y : Obj) = r y) →
        X.PObj.IsScSmoothOn (EpGroupoid.subObjPolyfold hA) g V := by
    intro V r hV hrV hsm hid him g hg
    let d : X.PObj.SubData S := ⟨V, r, hV, hrV, hsm, hid, him⟩
    rcases V.eq_empty_or_nonempty with hV0 | ⟨x₀, _⟩
    · subst hV0
      exact MPolyfold.IsScSmoothOn.of_exists_charts isOpen_empty (continuousOn_empty _)
        fun x hx => absurd hx (notMem_empty x)
    · refine (h2 hA d (g x₀)).congr fun x hx => Subtype.ext ?_
      rw [MPolyfold.SubData.retractInto_val d (g x₀) hx, hg x hx]
  exact ⟨inferInstance, EpGroupoid.subObjPolyfold hA, (h1 hA).1, (h1 hA).2,
    fun _ _ V r hV _ hrV hsm hid him g hg => key V r hV hrV hsm hid him g hg, key⟩

/-- `B → A`, outright (B is not used: A concerns the specific structure `subObjPolyfold`). -/
theorem B_to_A : B → A := fun _ =>
  ⟨fun _ _ => ⟨MPolyfold.subPolyfold_inclusion_isScSmooth _, Topology.IsEmbedding.subtypeVal⟩,
    fun hA _ d a₀ => MPolyfold.subPolyfold_retraction_isScSmooth hA.isSubMPolyfold d a₀⟩

#rt_check RoundTrip.V7_30.A_to_B_noTangent [Polyfold.EpGroupoid.isScSmoothMap_val_subObj,
  Polyfold.EpGroupoid.isScSmoothOn_retractInto_subObj]
#rt_check RoundTrip.V7_30.B_to_A [Polyfold.EpGroupoid.isScSmoothMap_val_subObj,
  Polyfold.EpGroupoid.isScSmoothOn_retractInto_subObj]
#rt_overlap RoundTrip.V7_30.B_to_A [Polyfold.EpGroupoid.isScSmoothMap_val_subObj,
  Polyfold.EpGroupoid.isScSmoothOn_retractInto_subObj]

end RoundTrip.V7_30
