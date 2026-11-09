import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V8_7

/-! Round trip for V8_7 (Lemma 8.1.5 = 2017 Lemma 8.4: the units `1_q = (1_x, Ts(1_x)⁻¹ q)`).

`A` is the conjunction of the types of `EpGroupoid.tSrc_tUnit`, `tTgt_tUnit`, `tComp_tUnit`,
`tUnit_tComp` and `lemma_8_1_5`, universes at `0`.  The project's unit is `tUnit = Tu`, the
tangent of the unit map; B's unit is the text's `1_q`, characterized by `IsTUnitB q v` (`v` over
`1_x` with `Ts v = q`).

* `A → B`: `1_q` exists (`tUnit q`, by the project lemma `tBase_tUnit` and `tSrc_tUnit`); any
  `v` with B's characterization equals `tUnit q` (fibre injectivity `tangent_ext`, with
  `tSrc_tUnit` from the hypothesis), and then B's four properties are `lemma_8_1_5`.
* `B → A`: `Ts(Tu q) = q` is *not* a consequence of `B` (B never mentions `Tu`; it only
  characterizes `1_q` by its base point and its `Ts`), so `tSrc_tUnit` is re-proved outright by
  the chain rule for `s ∘ u = id` (`tangentMap_tangentMap_of_eq_id`).  With it `tUnit q` satisfies
  `IsTUnitB q`, and `tTgt_tUnit`, `tComp_tUnit`, `tUnit_tComp` and the last three clauses of
  `lemma_8_1_5` all come from B; the base point clause of `lemma_8_1_5` is `tBase_tUnit`. -/

namespace RoundTrip.V8_7
open Polyfold

/-- The project's statement (universes at `0`). -/
def A : Prop :=
  (type_of% @Polyfold.EpGroupoid.tSrc_tUnit.{0}) ∧
  (type_of% @Polyfold.EpGroupoid.tTgt_tUnit.{0}) ∧
  (type_of% @Polyfold.EpGroupoid.tComp_tUnit.{0}) ∧
  (type_of% @Polyfold.EpGroupoid.tUnit_tComp.{0}) ∧
  (type_of% @Polyfold.EpGroupoid.lemma_8_1_5.{0})

theorem A_holds : A :=
  ⟨@Polyfold.EpGroupoid.tSrc_tUnit.{0}, @Polyfold.EpGroupoid.tTgt_tUnit.{0},
    @Polyfold.EpGroupoid.tComp_tUnit.{0}, @Polyfold.EpGroupoid.tUnit_tComp.{0},
    @Polyfold.EpGroupoid.lemma_8_1_5.{0}⟩

/-! ### `A → B` -/

theorem A_to_B : A → B := by
  rintro ⟨hsu, -, -, -, h84⟩ Obj Mor _ _ _ _ _ _ X
  refine ⟨X.isScSmoothMap_src, X.isScSmoothMap_tgt, fun q =>
    ⟨⟨X.tUnit q, X.tBase_tUnit q, hsu X q⟩, ?_⟩⟩
  rintro v ⟨hb, hsv⟩
  have hv : X.tUnit q = v := X.tangent_ext ((X.tBase_tUnit q).trans hb.symm) ((hsu X q).trans hsv.symm)
  subst hv
  obtain ⟨-, h1, h2, h3, h4⟩ := h84 X q
  exact ⟨h1, h2, h3, h4⟩

/-! ### `B → A` -/

section FromB

variable {Obj Mor : Type} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] (X : EpGroupoid Obj Mor)

/-- `Ts(Tu q) = q`, re-proved: the chain rule for `s ∘ u = id` (not a consequence of `B`). -/
theorem tSrc_tUnit_chain (a : X.PObj.TangentSpace) : X.tSrc (X.tUnit a) = a :=
  MPolyfold.tangentMap_tangentMap_of_eq_id X.isScSmoothMap_src X.isScSmoothMap_unit
    (funext X.src_unit) a

/-- `tUnit q` is B's `1_q`, so B gives its properties. -/
theorem props_of_B (hB : B) (q : X.PObj.TangentSpace) :
    X.tSrc (X.tUnit q) = q ∧ X.tTgt (X.tUnit q) = q ∧
      (∀ k, X.tSrc k = q → X.tComp k (X.tUnit q) = k) ∧
      (∀ k, X.tTgt k = q → X.tComp (X.tUnit q) k = k) := by
  obtain ⟨_, _, hB'⟩ := hB Obj Mor X
  exact (hB' q).2 (X.tUnit q) ⟨X.tBase_tUnit q, tSrc_tUnit_chain X q⟩

end FromB

theorem B_to_A : B → A := by
  intro hB
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro Obj Mor _ _ _ _ _ _ X a
    exact tSrc_tUnit_chain X a
  · intro Obj Mor _ _ _ _ _ _ X a
    exact (props_of_B X hB a).2.1
  · intro Obj Mor _ _ _ _ _ _ X k
    exact (props_of_B X hB (X.tSrc k)).2.2.1 k rfl
  · intro Obj Mor _ _ _ _ _ _ X h
    exact (props_of_B X hB (X.tTgt h)).2.2.2 h rfl
  · intro Obj Mor _ _ _ _ _ _ X q
    exact ⟨X.tBase_tUnit q, props_of_B X hB q⟩

#rt_check RoundTrip.V8_7.A_to_B [Polyfold.EpGroupoid.tSrc_tUnit,
  Polyfold.EpGroupoid.tTgt_tUnit, Polyfold.EpGroupoid.tComp_tUnit,
  Polyfold.EpGroupoid.tUnit_tComp, Polyfold.EpGroupoid.lemma_8_1_5]
#rt_check RoundTrip.V8_7.B_to_A [Polyfold.EpGroupoid.tSrc_tUnit,
  Polyfold.EpGroupoid.tTgt_tUnit, Polyfold.EpGroupoid.tComp_tUnit,
  Polyfold.EpGroupoid.tUnit_tComp, Polyfold.EpGroupoid.lemma_8_1_5]
#rt_overlap RoundTrip.V8_7.B_to_A [Polyfold.EpGroupoid.tSrc_tUnit,
  Polyfold.EpGroupoid.tTgt_tUnit, Polyfold.EpGroupoid.tComp_tUnit,
  Polyfold.EpGroupoid.tUnit_tComp, Polyfold.EpGroupoid.lemma_8_1_5]

end RoundTrip.V8_7
