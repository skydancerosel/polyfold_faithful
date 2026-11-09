import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V10_14

/-! Round trip for V10_14 (2021 Proposition 10.1.17, p. 475: the Zhou condition under
equivalences).

`A` is the conjunction of the types of the six listed theorems, universes instantiated at `0`
(`B` lives in `Type`): `EpGroupoid.mem_smoothSet_src_iff`, `mem_smoothSet_tgt_iff` (`s φ`, `t φ`
smooth iff `φ` is), `EpFunctor.tangentMor_mor` (naturality `T(F φ) ∘ TF = TF ∘ Tφ`),
`IsEquivalence.isZhou_of_isZhou`, `isZhou_of_isZhou_right` (the two halves) and
`EpFunctor.proposition_10_1_17` (the iff).

* `A_to_B`: `proposition_10_1_17` is `B` verbatim.
* `B_to_A`: the two halves and the iff come from `B`.  The two smoothness lemmas and the
  naturality lemma are general facts about ep-groupoids and sc-smooth functors (no equivalence
  involved), not consequences of `B`; they are re-proved outright (`mem_smoothSet_src_iff'`,
  `mem_smoothSet_tgt_iff'`, `tangentMor_mor'`: the project's proofs, copied, from non-item
  lemmas). -/

namespace RoundTrip.V10_14
open Polyfold Set

/-- The project's statement (universes at `0`). -/
def A : Prop :=
  (type_of% @Polyfold.EpGroupoid.mem_smoothSet_src_iff.{0}) ∧
  (type_of% @Polyfold.EpGroupoid.mem_smoothSet_tgt_iff.{0}) ∧
  (type_of% @Polyfold.EpFunctor.tangentMor_mor.{0, 0}) ∧
  (type_of% @Polyfold.EpFunctor.IsEquivalence.isZhou_of_isZhou.{0, 0}) ∧
  (type_of% @Polyfold.EpFunctor.IsEquivalence.isZhou_of_isZhou_right.{0, 0}) ∧
  (type_of% @Polyfold.EpFunctor.proposition_10_1_17.{0, 0})

theorem A_holds : A :=
  ⟨@Polyfold.EpGroupoid.mem_smoothSet_src_iff.{0},
    @Polyfold.EpGroupoid.mem_smoothSet_tgt_iff.{0},
    @Polyfold.EpFunctor.tangentMor_mor.{0, 0},
    @Polyfold.EpFunctor.IsEquivalence.isZhou_of_isZhou.{0, 0},
    @Polyfold.EpFunctor.IsEquivalence.isZhou_of_isZhou_right.{0, 0},
    @Polyfold.EpFunctor.proposition_10_1_17.{0, 0}⟩

theorem A_to_B : A → B := by
  rintro ⟨-, -, -, -, -, h⟩ Obj Mor Obj' Mor' _ _ _ _ _ _ _ _ _ _ _ _ X Y F hF
  exact h hF

/-! ### The general lemmas, re-proved outright (the project's proofs) -/

section General

variable {Obj Mor : Type} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor]
  {Obj' Mor' : Type} [TopologicalSpace Obj'] [T2Space Obj'] [ParacompactSpace Obj']
  [TopologicalSpace Mor'] [T2Space Mor'] [ParacompactSpace Mor']
  {X : EpGroupoid Obj Mor} {Y : EpGroupoid Obj' Mor'}

theorem mem_smoothSet_src_iff' (X : EpGroupoid Obj Mor) (φ : Mor) :
    X.src φ ∈ X.PObj.smoothSet ↔ φ ∈ X.PMor.smoothSet := by
  simp only [MPolyfold.smoothSet, mem_iInter, X.mem_levelSet_src_iff]

theorem mem_smoothSet_tgt_iff' (X : EpGroupoid Obj Mor) (φ : Mor) :
    X.tgt φ ∈ X.PObj.smoothSet ↔ φ ∈ X.PMor.smoothSet := by
  simp only [MPolyfold.smoothSet, mem_iInter, X.mem_levelSet_tgt_iff]

theorem tangentMor_mor' (F : EpFunctor X Y) {φ : Mor} (hφ : φ ∈ X.PMor.levelSet 1)
    {a : X.PObj.TangentSpace} (ha : X.PObj.levelVal 1 (X.PObj.tangentProj a) = X.src φ) :
    Y.tangentMor (F.mor φ) (F.tangent.obj a) = F.tangent.obj (X.tangentMor φ a) := by
  obtain ⟨h, rfl, rfl⟩ := X.exists_tSrc_eq' hφ ha
  have hTF : Y.tSrc (F.tangent.mor h) = F.tangent.obj (X.tSrc h) := F.tangent.src_mor h
  have hTF' : Y.tTgt (F.tangent.mor h) = F.tangent.obj (X.tTgt h) := F.tangent.tgt_mor h
  have hmor : Y.tBase (F.tangent.mor h) = F.mor (X.tBase h) :=
    Y.tBase_tangentMap F.isScSmoothMap_mor h
  rw [X.tangentMor_tSrc, ← hTF', ← hmor, ← hTF, Y.tangentMor_tSrc]

end General

theorem B_to_A : B → A := by
  intro hB
  refine ⟨@mem_smoothSet_src_iff', @mem_smoothSet_tgt_iff', @tangentMor_mor', ?_, ?_, ?_⟩
  · intro Obj Mor _ _ _ _ _ _ Obj' Mor' _ _ _ _ _ _ X Y F hF
    exact (hB Obj Mor Obj' Mor' X Y F hF).1
  · intro Obj Mor _ _ _ _ _ _ Obj' Mor' _ _ _ _ _ _ X Y F hF
    exact (hB Obj Mor Obj' Mor' X Y F hF).2
  · intro Obj Mor _ _ _ _ _ _ Obj' Mor' _ _ _ _ _ _ X Y F hF
    exact hB Obj Mor Obj' Mor' X Y F hF

#rt_check RoundTrip.V10_14.A_to_B [Polyfold.EpGroupoid.mem_smoothSet_src_iff,
  Polyfold.EpGroupoid.mem_smoothSet_tgt_iff, Polyfold.EpFunctor.tangentMor_mor,
  Polyfold.EpFunctor.IsEquivalence.isZhou_of_isZhou,
  Polyfold.EpFunctor.IsEquivalence.isZhou_of_isZhou_right,
  Polyfold.EpFunctor.proposition_10_1_17]
#rt_check RoundTrip.V10_14.B_to_A [Polyfold.EpGroupoid.mem_smoothSet_src_iff,
  Polyfold.EpGroupoid.mem_smoothSet_tgt_iff, Polyfold.EpFunctor.tangentMor_mor,
  Polyfold.EpFunctor.IsEquivalence.isZhou_of_isZhou,
  Polyfold.EpFunctor.IsEquivalence.isZhou_of_isZhou_right,
  Polyfold.EpFunctor.proposition_10_1_17]
#rt_overlap RoundTrip.V10_14.B_to_A [Polyfold.EpGroupoid.mem_smoothSet_src_iff,
  Polyfold.EpGroupoid.mem_smoothSet_tgt_iff, Polyfold.EpFunctor.tangentMor_mor,
  Polyfold.EpFunctor.IsEquivalence.isZhou_of_isZhou,
  Polyfold.EpFunctor.IsEquivalence.isZhou_of_isZhou_right,
  Polyfold.EpFunctor.proposition_10_1_17]

end RoundTrip.V10_14
