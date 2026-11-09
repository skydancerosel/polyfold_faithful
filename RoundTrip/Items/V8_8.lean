import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V8_8

/-! Round trip for V8_8 (Lemma 8.1.6 (2017: 8.5): `ι_T = Tι` is a two-sided inverse).

`A` is the conjunction of the types of the five listed theorems, universes instantiated at `0`
(`B` lives in `Type`): `tSrc_tInv`, `tTgt_tInv`, `tComp_tInv`, `tInv_tComp`, `lemma_8_1_6`.

The notions agree definitionally: `B`'s `baseB X.PMor` is the project's `X.tBase`, and by proof
irrelevance `tangentMap hs = X.tSrc`, `tangentMap ht = X.tTgt`, `tangentMap hι = X.tInv` and
`tCompB X hs = X.tComp` for any proofs `hs`, `ht`, `hι`.  `B` characterizes the unit by
`IsTUnitB` (over `1_{p(q)}`, `Ts = q`) plus uniqueness, the project names `X.tUnit q`; the two
are matched by the non-item lemmas `tBase_tUnit`, `tSrc_tUnit` and `tangent_ext`. -/

namespace RoundTrip.V8_8
open Polyfold

/-- The project's statement (universes at `0`). -/
def A : Prop :=
  (type_of% @Polyfold.EpGroupoid.tSrc_tInv.{0}) ∧
  (type_of% @Polyfold.EpGroupoid.tTgt_tInv.{0}) ∧
  (type_of% @Polyfold.EpGroupoid.tComp_tInv.{0}) ∧
  (type_of% @Polyfold.EpGroupoid.tInv_tComp.{0}) ∧
  (type_of% @Polyfold.EpGroupoid.lemma_8_1_6.{0})

theorem A_holds : A :=
  ⟨@Polyfold.EpGroupoid.tSrc_tInv.{0}, @Polyfold.EpGroupoid.tTgt_tInv.{0},
    @Polyfold.EpGroupoid.tComp_tInv.{0}, @Polyfold.EpGroupoid.tInv_tComp.{0},
    @Polyfold.EpGroupoid.lemma_8_1_6.{0}⟩

section
variable {Obj Mor : Type} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor]

/-- The project's unit satisfies `B`'s characterization. -/
theorem isTUnitB_tUnit (X : EpGroupoid Obj Mor) (q : X.PObj.TangentSpace) :
    IsTUnitB X X.isScSmoothMap_src q (X.tUnit q) :=
  ⟨X.tBase_tUnit q, X.tSrc_tUnit q⟩

/-- Every vector satisfying `B`'s unit characterization is the project's unit. -/
theorem eq_tUnit_of_isTUnitB (X : EpGroupoid Obj Mor) {q : X.PObj.TangentSpace}
    {v : X.PMor.TangentSpace} (hv : IsTUnitB X X.isScSmoothMap_src q v) : X.tUnit q = v :=
  X.tangent_ext ((X.tBase_tUnit q).trans hv.1.symm) ((X.tSrc_tUnit q).trans hv.2.symm)

end

theorem A_to_B : A → B := by
  intro hA Obj Mor _ _ _ _ _ _ X
  obtain ⟨-, -, -, -, h5⟩ := hA
  refine ⟨X.isScSmoothMap_src, X.isScSmoothMap_tgt, X.isScSmoothMap_inv, fun k => ?_⟩
  obtain ⟨hb, hs, ht, hl, hr⟩ := h5 X k
  refine ⟨hb, hs, ht, ?_, fun v hv => ?_, ?_, fun v hv => ?_⟩
  · change IsTUnitB X X.isScSmoothMap_src (X.tSrc k) (X.tComp (X.tInv k) k)
    rw [hl]
    exact isTUnitB_tUnit X _
  · change X.tComp (X.tInv k) k = v
    rw [hl]
    exact eq_tUnit_of_isTUnitB X hv
  · change IsTUnitB X X.isScSmoothMap_src (X.tTgt k) (X.tComp k (X.tInv k))
    rw [hr]
    exact isTUnitB_tUnit X _
  · change X.tComp k (X.tInv k) = v
    rw [hr]
    exact eq_tUnit_of_isTUnitB X hv

theorem B_to_A : B → A := by
  intro hB
  -- the five facts, for every `X` and `v`, read off `B`
  have key : ∀ (Obj Mor : Type) [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
      [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] (X : EpGroupoid Obj Mor)
      (v : X.PMor.TangentSpace),
      X.tBase (X.tInv v) = X.inv (X.tBase v) ∧ X.tSrc (X.tInv v) = X.tTgt v ∧
        X.tTgt (X.tInv v) = X.tSrc v ∧ X.tComp (X.tInv v) v = X.tUnit (X.tSrc v) ∧
        X.tComp v (X.tInv v) = X.tUnit (X.tTgt v) := by
    intro Obj Mor _ _ _ _ _ _ X v
    obtain ⟨hs, ht, hι, h⟩ := hB Obj Mor X
    obtain ⟨hb, h1, h2, -, hu1, -, hu2⟩ := h v
    exact ⟨hb, h1, h2, hu1 _ (isTUnitB_tUnit X _), hu2 _ (isTUnitB_tUnit X _)⟩
  exact ⟨fun X v => (key _ _ X v).2.1, fun X v => (key _ _ X v).2.2.1,
    fun X v => (key _ _ X v).2.2.2.2, fun X v => (key _ _ X v).2.2.2.1, fun X v => key _ _ X v⟩

#rt_check RoundTrip.V8_8.A_to_B [Polyfold.EpGroupoid.tSrc_tInv, Polyfold.EpGroupoid.tTgt_tInv,
  Polyfold.EpGroupoid.tComp_tInv, Polyfold.EpGroupoid.tInv_tComp, Polyfold.EpGroupoid.lemma_8_1_6]
#rt_check RoundTrip.V8_8.B_to_A [Polyfold.EpGroupoid.tSrc_tInv, Polyfold.EpGroupoid.tTgt_tInv,
  Polyfold.EpGroupoid.tComp_tInv, Polyfold.EpGroupoid.tInv_tComp, Polyfold.EpGroupoid.lemma_8_1_6]
#rt_overlap RoundTrip.V8_8.B_to_A [Polyfold.EpGroupoid.tSrc_tInv,
  Polyfold.EpGroupoid.tTgt_tInv, Polyfold.EpGroupoid.tComp_tInv, Polyfold.EpGroupoid.tInv_tComp,
  Polyfold.EpGroupoid.lemma_8_1_6]

end RoundTrip.V8_8
