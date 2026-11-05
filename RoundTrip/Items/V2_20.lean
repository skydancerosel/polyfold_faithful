import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V2_20

/-! Round trip for V2_20 (Proposition 2.19: `TX` Hausdorff and metrizable, `p` continuous).

`A` is the conjunction of the types of the listed theorems
`Polyfold.MPolyfold.continuous_tangentProj`, `.continuous_levelVal_tangentProj`,
`.isOpen_tangentChartSet`, `.metrizableSpace_tangentSpace`, `.paracompactSpace_tangentSpace` and
`Polyfold.proposition_2_19_3`, all at universe `0` (B lives in `Type`).

B's topology `τB P = generateFrom 𝓑` is the project's instance on `P.TangentSpace`
(`τB_eq`, from `tangentChartMap_mk_self`: the project's `Tφ` agrees with B's `TφB` on `TV`).

* `B → A`: every conjunct of A is read off B.
* `A → B` is NOT proved: B's (2) asserts that `p : TX → X_1` is an OPEN map, which the project
  does not prove (its docstrings: gap G.8, "openness is not needed and not proved"), and A does not
  contain.  Everything else in B follows from A (`A_to_B_of_isOpenMap`): metrizable/paracompact
  and continuity are A; Hausdorff is the project's instance; "𝓑 is a basis" (closure under
  intersections, also not stated in the project) follows from the tangent charts
  `tangentChart hφ` being homeomorphisms `TV ≅ TO` (`MChart.exists_isOpen_image_eq`).
  Openness of `p` is true (in a chart `p` is `pr₁ : TO → O₁`, and `x ↦ Tr(x, h₀)` is a continuous
  local section through `(x₀, h₀)`), so the failure is proof effort, not a difference. -/

namespace RoundTrip.V2_20
open Polyfold Set MPolyfold TopologicalSpace

/-- The project's statement (universe `0`). -/
def A : Prop :=
  (type_of% @Polyfold.MPolyfold.continuous_tangentProj.{0}) ∧
    (type_of% @Polyfold.MPolyfold.continuous_levelVal_tangentProj.{0}) ∧
    (type_of% @Polyfold.MPolyfold.isOpen_tangentChartSet.{0}) ∧
    (type_of% @Polyfold.MPolyfold.metrizableSpace_tangentSpace.{0}) ∧
    (type_of% @Polyfold.MPolyfold.paracompactSpace_tangentSpace.{0}) ∧
    (type_of% @Polyfold.proposition_2_19_3.{0})

theorem A_holds : A :=
  ⟨@Polyfold.MPolyfold.continuous_tangentProj.{0},
    @Polyfold.MPolyfold.continuous_levelVal_tangentProj.{0},
    @Polyfold.MPolyfold.isOpen_tangentChartSet.{0},
    @Polyfold.MPolyfold.metrizableSpace_tangentSpace.{0},
    @Polyfold.MPolyfold.paracompactSpace_tangentSpace.{0}, @Polyfold.proposition_2_19_3.{0}⟩

section Glue

variable {X : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {P : MPolyfold X}

/-- Two equivalent tuples in the same chart have the same vector. -/
theorem cast_vecB {p q : P.TangentPre} (e : p.φ = q.φ)
    (hpq : TangentSpace.mk p = TangentSpace.mk q) :
    cast (congrArg (fun c : MChart X => (TEB c.model.E).lvl 0) e) (vecB p) = vecB q := by
  obtain ⟨x, φ, h, hφ, hx, hl, ht⟩ := p
  obtain ⟨x', φ', h', hφ', hx', hl', ht'⟩ := q
  simp only at e
  subst e
  have hr := (TangentSpace.mk_eq_mk.1 hpq).2
  rw [TangentPre.transport_self] at hr
  rw [cast_eq]
  exact hr

theorem TφB_eq (p : P.TangentPre) : TφB P p.φ (TangentSpace.mk p) = vecB p := by
  unfold TφB
  rw [dif_pos ⟨p, rfl, rfl⟩]
  generalize_proofs h
  exact cast_vecB h.choose_spec.1 h.choose_spec.2

theorem tangentChartSet_eq (φ : MChart X) : tangentChartSet (P := P) φ = TVB P φ := by
  ext α
  obtain ⟨p, rfl⟩ := TangentSpace.exists_rep α
  constructor
  · intro h; exact ⟨p, rfl, h⟩
  · rintro ⟨q, hq, hqx⟩
    rw [← hq]; exact hqx

/-- The project's `Tφ` and B's `TφB` agree on `TV`. -/
theorem tangentChartMap_eq_TφB {φ : MChart X} (hφ : P.IsChart φ) {α : P.TangentSpace}
    (hα : α ∈ TVB P φ) : tangentChartMap hφ α = TφB P φ α := by
  rw [← tangentChartSet_eq] at hα
  obtain ⟨p, hpφ, rfl⟩ : ∃ p : P.TangentPre, p.φ = φ ∧ TangentSpace.mk p = α :=
    ⟨TangentPre.ofVec hφ (tangentChartMap_mem hφ hα), rfl, mk_ofVec_tangentChartMap hφ hα⟩
  subst hpφ
  rw [TφB_eq]
  exact tangentChartMap_mk_self p

theorem basicSet_eq {φ : MChart X} (hφ : P.IsChart φ) (W : Set ((TEB φ.model.E).lvl 0)) :
    {α | α ∈ TVB P φ ∧ TφB P φ α ∈ W} =
      {α | α ∈ tangentChartSet φ ∧ tangentChartMap hφ α ∈ W} := by
  ext α
  simp only [mem_ofPred_eq, tangentChartSet_eq]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨h1, by rwa [tangentChartMap_eq_TφB hφ h1]⟩
  · rintro ⟨h1, h2⟩; exact ⟨h1, by rwa [← tangentChartMap_eq_TφB hφ h1]⟩

theorem tangentBasis_eq : P.tangentBasis = TfamB P := by
  ext s
  constructor
  · rintro ⟨φ, hφ, W, hW, rfl⟩
    exact ⟨φ, hφ, W, hW, (basicSet_eq hφ W).symm⟩
  · rintro ⟨φ, hφ, W, hW, rfl⟩
    exact ⟨φ, hφ, W, hW, basicSet_eq hφ W⟩

/-- B's topology on `TX` is the project's instance. -/
theorem τB_eq : τB P = (inferInstance : TopologicalSpace P.TangentSpace) := by
  unfold τB
  change _ = TopologicalSpace.generateFrom P.tangentBasis
  rw [tangentBasis_eq]

/-- `𝓑` is a basis of the project's topology on `TX` (the tangent charts are homeomorphisms). -/
theorem isTopologicalBasis_TfamB : IsTopologicalBasis (TfamB P) := by
  refine isTopologicalBasis_of_isOpen_of_nhds ?_ ?_
  · rintro _ ⟨φ, hφ, W, hW, rfl⟩
    rw [basicSet_eq hφ W]
    exact isOpen_tangent_basic hφ hW
  · intro α U hαU hU
    obtain ⟨p, rfl⟩ := TangentSpace.exists_rep α
    have hsub : U ∩ (tangentChart p.isChart (TangentSpace.mk p)).source ⊆
        (tangentChart p.isChart (TangentSpace.mk p)).source := inter_subset_right
    obtain ⟨W, hW, hWeq⟩ : ∃ W : Set ((TEB p.φ.model.E).lvl 0), IsOpen W ∧
        (tangentChart p.isChart (TangentSpace.mk p)) ''
          (U ∩ (tangentChart p.isChart (TangentSpace.mk p)).source) =
          (tangentChart p.isChart (TangentSpace.mk p)).model.O ∩ W :=
      (tangentChart p.isChart (TangentSpace.mk p)).exists_isOpen_image_eq hsub
        (hU.inter (tangentChart p.isChart (TangentSpace.mk p)).isOpen_source)
    refine ⟨{β | β ∈ TVB P p.φ ∧ TφB P p.φ β ∈ W}, ⟨p.φ, p.isChart, W, hW, rfl⟩, ?_, ?_⟩
    · rw [basicSet_eq p.isChart W]
      refine ⟨p.mem_source, ?_⟩
      have : tangentChart p.isChart (TangentSpace.mk p) (TangentSpace.mk p) ∈
          (tangentChart p.isChart (TangentSpace.mk p)) ''
            (U ∩ (tangentChart p.isChart (TangentSpace.mk p)).source) :=
        ⟨_, ⟨hαU, p.mem_source⟩, rfl⟩
      rw [hWeq] at this
      exact this.2
    · rw [basicSet_eq p.isChart W]
      rintro β ⟨hβ, hβW⟩
      have hβχ : β ∈ (tangentChart p.isChart (TangentSpace.mk p)).source := hβ
      have : tangentChart p.isChart (TangentSpace.mk p) β ∈
          (tangentChart p.isChart (TangentSpace.mk p)) ''
            (U ∩ (tangentChart p.isChart (TangentSpace.mk p)).source) := by
        rw [hWeq]; exact ⟨(tangentChart p.isChart (TangentSpace.mk p)).mapsTo_model β hβχ, hβW⟩
      obtain ⟨γ, hγ, hγeq⟩ := this
      have := (tangentChart p.isChart (TangentSpace.mk p)).toPartialEquiv.injOn hγ.2 hβχ hγeq
      rw [← this]; exact hγ.1

/-- `TX` is Hausdorff, given that the base point map `TX → X` is continuous (the project's proof of
its `T2Space` instance, with the continuity as a hypothesis). -/
theorem t2Space_of (hc : Continuous fun α : P.TangentSpace => P.levelVal 1 (P.tangentProj α)) :
    T2Space P.TangentSpace := by
  refine ⟨fun α β hne => ?_⟩
  obtain ⟨p, rfl⟩ := TangentSpace.exists_rep α
  obtain ⟨q, rfl⟩ := TangentSpace.exists_rep β
  by_cases hx : p.x = q.x
  · have hq : q.x ∈ p.φ.source := hx ▸ p.mem_source
    have hne' : tangentChartMap p.isChart (TangentSpace.mk p) ≠
        tangentChartMap p.isChart (TangentSpace.mk q) :=
      fun h => hne (tangentChartMap_injOn p.isChart p.mem_source hq h)
    obtain ⟨u, v, hu, hv, hαu, hβv, huv⟩ := t2_separation hne'
    refine ⟨{α | α ∈ tangentChartSet p.φ ∧ tangentChartMap p.isChart α ∈ u},
      {α | α ∈ tangentChartSet p.φ ∧ tangentChartMap p.isChart α ∈ v},
      isOpen_tangent_basic p.isChart hu, isOpen_tangent_basic p.isChart hv,
      ⟨p.mem_source, hαu⟩, ⟨hq, hβv⟩, ?_⟩
    exact Set.disjoint_left.2 fun γ h1 h2 => Set.disjoint_left.1 huv h1.2 h2.2
  · obtain ⟨A, B, hA, hB, hpA, hqB, hAB⟩ := t2_separation hx
    refine ⟨(fun α => P.levelVal 1 (P.tangentProj α)) ⁻¹' A,
      (fun α => P.levelVal 1 (P.tangentProj α)) ⁻¹' B, hA.preimage hc, hB.preimage hc,
      hpA, hqB, ?_⟩
    exact Set.disjoint_left.2 fun γ h1 h2 => Set.disjoint_left.1 hAB h1 h2

end Glue

/-- Everything in B except the openness of `p` follows from A. -/
theorem A_to_B_of_isOpenMap (hA : A)
    (hopen : ∀ (X : Type) [TopologicalSpace X] [T2Space X] [ParacompactSpace X] (P : MPolyfold X),
      @IsOpenMap _ _ _ (P.levelTopology 1) P.tangentProj) : B := by
  obtain ⟨hcont, hcont', -, hmet, hpara, -⟩ := hA
  intro X _ _ _ P
  rw [τB_eq]
  exact ⟨⟨isTopologicalBasis_TfamB, t2Space_of hcont'⟩, ⟨hcont, hopen X P⟩, ⟨hmet P, hpara P⟩⟩

theorem B_to_A : B → A := by
  intro hB
  have hB' : ∀ (X : Type) [TopologicalSpace X] [T2Space X] [ParacompactSpace X]
      (P : MPolyfold X),
      (IsTopologicalBasis (TfamB P) ∧ T2Space P.TangentSpace) ∧
      (@Continuous _ _ _ (P.levelTopology 1) P.tangentProj ∧
        @IsOpenMap _ _ _ (P.levelTopology 1) P.tangentProj) ∧
      (MetrizableSpace P.TangentSpace ∧ ParacompactSpace P.TangentSpace) := by
    intro X _ _ _ P
    have h := hB X P
    rw [τB_eq] at h
    exact h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro X _ _ _ P
    exact (hB' X P).2.1.1
  · intro X _ _ _ P
    exact (continuous_levelVal 1).comp (hB' X P).2.1.1
  · intro X _ _ _ P φ hφ
    have h : IsOpen {α | α ∈ TVB P φ ∧ TφB P φ α ∈ (univ : Set ((TEB φ.model.E).lvl 0))} :=
      (hB' X P).1.1.isOpen ⟨φ, hφ, univ, isOpen_univ, rfl⟩
    rw [basicSet_eq hφ univ] at h
    simpa using h
  · intro X _ _ _ P
    exact (hB' X P).2.2.1
  · intro X _ _ _ P
    exact (hB' X P).2.2.2
  · intro X _ _ _ P
    exact (hB' X P).2.2

-- `A_to_B_of_isOpenMap` is a diagnostic, not a round-trip direction.  It uses A's hypotheses for
-- continuity, metrizability and paracompactness (Hausdorff is re-proved from A's continuity,
-- `t2Space_of`), but the basis property uses the definition `tangentChart`, whose field
-- `isOpen_source := isOpen_tangentChartSet hφ` reaches that A-theorem (not as an abstracted
-- `_proof_`), so `#rt_check_soft` would flag `isOpen_tangentChartSet`.
#rt_check RoundTrip.V2_20.B_to_A [Polyfold.MPolyfold.continuous_tangentProj,
  Polyfold.MPolyfold.continuous_levelVal_tangentProj, Polyfold.MPolyfold.isOpen_tangentChartSet,
  Polyfold.MPolyfold.metrizableSpace_tangentSpace, Polyfold.MPolyfold.paracompactSpace_tangentSpace,
  Polyfold.proposition_2_19_3]
#rt_overlap RoundTrip.V2_20.B_to_A [Polyfold.MPolyfold.continuous_tangentProj,
  Polyfold.MPolyfold.continuous_levelVal_tangentProj, Polyfold.MPolyfold.isOpen_tangentChartSet,
  Polyfold.MPolyfold.metrizableSpace_tangentSpace, Polyfold.MPolyfold.paracompactSpace_tangentSpace,
  Polyfold.proposition_2_19_3]

end RoundTrip.V2_20
