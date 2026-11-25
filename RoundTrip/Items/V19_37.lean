import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V19_37

set_option maxSynthPendingDepth 3

/-! Round trip for V19_37 (2021 Proposition 19.5.7, p. 889).  Universes at `0`.

`A` speaks of the project's structure `toPolyfoldConstruction hm`; `B` of every natural polyfold
structure `P` (uniformizer sets those of `F`, `M(Ψ, Ψ')` with `T_{Ψ,Ψ'}`).
* `A_to_B`: `A` gives (ZHOU) of `toPolyfoldConstruction` and then (second conjunct) (ZHOU) of every
  `G ⋉ O`; for a natural `P`, (ZHOU) of every piece gives (ZHOU) of `P`'s model
  (`isZhou_of_pieces`: piece functors are full and local sc-diffeomorphisms on objects, `Ψ̂`
  continuous since `M(Ψ, Ψ)` carries `T_{Ψ,Ψ}`).
* `B_to_A`: `B` at `P = toPolyfoldConstruction` (natural) gives `proposition_19_5_7`;
  `isZhou_toEP_of_isZhou` (a converse step, not in `B`) is re-proved outright. -/

namespace RoundTrip.V19_37
open Polyfold Polyfold.GroupoidalCategory Set
open Polyfold.GroupoidalCategory.BasicConstruction Polyfold.GCT.PolyfoldConstruction

def A : Prop :=
  (type_of% @Polyfold.GroupoidalCategory.BasicConstruction.proposition_19_5_7.{0}) ∧
  (type_of% @Polyfold.GroupoidalCategory.BasicConstruction.isZhou_toEP_of_isZhou.{0})

theorem A_holds : A :=
  ⟨@Polyfold.GroupoidalCategory.BasicConstruction.proposition_19_5_7.{0},
    @Polyfold.GroupoidalCategory.BasicConstruction.isZhou_toEP_of_isZhou.{0}⟩

section
variable {C : GroupoidalCategory.{0}} {B : C.BasicConstruction} {hB : B.U.HasClassUniformizers}

/-- `isZhou_toEP_of_isZhou`, re-proved outright (the project's proof, non-item lemmas). -/
theorem isZhou_toEP' (hm : @TopologicalSpace.MetrizableSpace C.OrbitSpace (B.natTop hB))
    (h : (toPolyfoldConstruction hm).IsZhou) (Ψ : B.U.Unif) : Ψ.1.ep.IsZhou := by
  set S := toPolyfoldConstruction hm
  obtain ⟨c, hc⟩ := h
  let Φ : Option c.ι → S.Unif := fun o => o.elim (ofUnif hm Ψ) c.Ψ
  have hcov : ⋃ o, (Φ o).1.footprint = univ := eq_univ_of_forall fun z => by
    obtain ⟨i, hi⟩ := mem_iUnion.1 (c.cover.symm ▸ mem_univ z)
    exact mem_iUnion.2 ⟨some i, hi⟩
  have hZ : (S.modelEP Φ).X.IsZhou := IsZhou.model ⟨c, hc⟩ ⟨Option c.ι, Φ, hcov⟩
  have hd := isLocalScDiffeo_pieceFunctor_obj Φ none (continuous_hat hm (Φ none))
  exact (EpGroupoid.isZhou_iff_forall_isZhouAt _).2 fun x' =>
    (pieceFunctor Φ none (continuous_hat hm (Φ none))).isZhouAt_of_isZhouAt_obj hd x' (hZ _)

variable {hm : @TopologicalSpace.MetrizableSpace C.OrbitSpace (B.natTop hB)}
  {P : (B.toGCTOfMetrizable hB hm).PolyfoldConstruction}

/-- In a natural structure `Ψ̂ : G × O → M(Ψ, Ψ)` is continuous (`M(Ψ, Ψ)` carries `T_{Ψ,Ψ}`). -/
theorem hat_cont (hnat : IsNaturalStructure B hB hm P) (Ψ : P.Unif) : Continuous (P.hat Ψ) := by
  have hΨ : ∃ α, Ψ.1.toUniformizer ∈ B.U.F α := by
    obtain ⟨α, h⟩ := Ψ.2; exact ⟨α, (hnat.1 α Ψ.1).1 h⟩
  have ht : P.topM Ψ Ψ = B.rep.topology ⟨Ψ.1.toUniformizer, hΨ⟩ ⟨Ψ.1.toUniformizer, hΨ⟩ :=
    hnat.2.2 Ψ Ψ hΨ hΨ B.rep B.mk_rep
  have hc := (B.rep.hatHomeomorph ⟨Ψ.1.toUniformizer, hΨ⟩).continuous
  show @Continuous _ _ _ (P.topM Ψ Ψ) (P.hat Ψ)
  rw [ht]
  exact hc

/-- If every translation groupoid `G ⋉ O` of `F` has (ZHOU), so does every natural structure. -/
theorem isZhou_of_pieces (hnat : IsNaturalStructure B hB hm P)
    (hall : ∀ Ψ : B.U.Unif, Ψ.1.ep.IsZhou) : P.IsZhou := by
  have key : ∀ z : C.OrbitSpace, ∃ (α : C.Obj) (Ψl : (B.toGCTOfMetrizable hB hm).LocalUniformizer),
      Ψl ∈ P.F α ∧ z ∈ Ψl.footprint := by
    intro z
    obtain ⟨α, hα, Ψ, hΨ⟩ := hB z
    obtain ⟨Ψl, hΨl, rfl⟩ := hnat.2.1 α Ψ hΨ
    obtain ⟨o, ho⟩ := B.U.isAt α Ψl.toUniformizer hΨ
    exact ⟨α, Ψl, hΨl, Ψl.mem_footprint_iff.2 ⟨o, by rw [← hα]; exact congrArg C.π ho⟩⟩
  choose α Ψl hΨl hz using key
  let Φ : C.OrbitSpace → P.Unif := fun z => ⟨Ψl z, α z, hΨl z⟩
  have hcov : ⋃ z, (Φ z).1.footprint = univ :=
    eq_univ_of_forall fun z => mem_iUnion.2 ⟨z, hz z⟩
  refine ⟨⟨C.OrbitSpace, Φ, hcov⟩, (EpGroupoid.isZhou_iff_forall_isZhouAt _).2 fun y => ?_⟩
  rcases hyv : (P.modelEP Φ).X.PObj.smoothVal y with ⟨j, q⟩
  have hyS : (⟨j, q⟩ : P.ModelObj Φ) ∈ (P.modelEP Φ).X.PObj.smoothSet :=
    hyv ▸ (P.modelEP Φ).X.PObj.smoothVal_mem y
  have hq : q ∈ (Φ j).1.P.smoothSet :=
    ((MPolyfold.isLocalScDiffeo_sigmaMk (fun i => (Φ i).1.P) j).mem_smoothSet_iff q).1 hyS
  have hc := hat_cont hnat (Φ j)
  have hX := hall ⟨(Φ j).1.toUniformizer, α j, (hnat.1 (α j) (Ψl j)).1 (hΨl j)⟩
    ((Φ j).1.toUniformizer.ep.PObj.smoothMk q hq)
  exact (pieceFunctor Φ j hc).isZhouAt_of_isZhouAt (isLocalScDiffeo_pieceFunctor_obj Φ j hc)
    (full_pieceFunctor Φ j hc) hq hX y (ψ := (P.modelEP Φ).X.unit ⟨j, q⟩)
    ((P.modelEP Φ).X.src_unit _) (((P.modelEP Φ).X.tgt_unit _).trans hyv.symm)

end

theorem A_to_B (hA : A) : B := by
  intro C B hB hm P hnat hZ
  exact isZhou_of_pieces hnat fun Ψ => hA.2 hm (hA.1 hm hZ) Ψ

/-- The main conjunct alone does not reach an arbitrary natural `P` (it speaks of
`toPolyfoldConstruction`); with the step `isZhou_toEP_of_isZhou` it does (`A_to_B`).  Here the
step is replaced by its outright copy `isZhou_toEP'`. -/
theorem main_A_to_B
    (h1 : type_of% @Polyfold.GroupoidalCategory.BasicConstruction.proposition_19_5_7.{0}) : B := by
  intro C B hB hm P hnat hZ
  exact isZhou_of_pieces hnat fun Ψ => isZhou_toEP' hm (h1 hm hZ) Ψ

/-- The project's `(F, M)` is natural in `B`'s sense. -/
theorem natural_toPolyfoldConstruction {C : GroupoidalCategory.{0}} (B : C.BasicConstruction)
    (hB : B.U.HasClassUniformizers)
    (hm : @TopologicalSpace.MetrizableSpace C.OrbitSpace (B.natTop hB)) :
    IsNaturalStructure B hB hm (toPolyfoldConstruction hm) := by
  refine ⟨fun α Ψ => Iff.rfl, fun α Ψ hΨ => ⟨toLocalUniformizer hm hΨ, hΨ, rfl⟩,
    fun Ψ Ψ' hΨ hΨ' F hF => ?_⟩
  show B.rep.topology _ _ = _
  exact TopologicalSpace.ext (UniformizerConstruction.TransitionData.lemma_19_3_1
    (Quotient.exact (B.mk_rep.trans hF.symm)) ⟨Ψ.1.toUniformizer, hΨ⟩ ⟨Ψ'.1.toUniformizer, hΨ'⟩)

theorem main_B_to_A (hB' : B) :
    type_of% @Polyfold.GroupoidalCategory.BasicConstruction.proposition_19_5_7.{0} :=
  fun {_C} {B} {hB} hm h => hB' _ B hB hm _ (natural_toPolyfoldConstruction B hB hm) h

theorem B_to_A (hB' : B) : A := ⟨main_B_to_A hB', @isZhou_toEP'⟩

#rt_check RoundTrip.V19_37.A_to_B [Polyfold.GroupoidalCategory.BasicConstruction.proposition_19_5_7,
  Polyfold.GroupoidalCategory.BasicConstruction.isZhou_toEP_of_isZhou]
#rt_check RoundTrip.V19_37.B_to_A [Polyfold.GroupoidalCategory.BasicConstruction.proposition_19_5_7,
  Polyfold.GroupoidalCategory.BasicConstruction.isZhou_toEP_of_isZhou]
#rt_check RoundTrip.V19_37.main_A_to_B [Polyfold.GroupoidalCategory.BasicConstruction.proposition_19_5_7,
  Polyfold.GroupoidalCategory.BasicConstruction.isZhou_toEP_of_isZhou]
#rt_check RoundTrip.V19_37.main_B_to_A [Polyfold.GroupoidalCategory.BasicConstruction.proposition_19_5_7,
  Polyfold.GroupoidalCategory.BasicConstruction.isZhou_toEP_of_isZhou]
#rt_overlap RoundTrip.V19_37.B_to_A [Polyfold.GroupoidalCategory.BasicConstruction.proposition_19_5_7,
  Polyfold.GroupoidalCategory.BasicConstruction.isZhou_toEP_of_isZhou]
#rt_overlap RoundTrip.V19_37.A_to_B [Polyfold.GroupoidalCategory.BasicConstruction.proposition_19_5_7,
  Polyfold.GroupoidalCategory.BasicConstruction.isZhou_toEP_of_isZhou]

end RoundTrip.V19_37
