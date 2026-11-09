import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V9_25

/-! Round trip for V9_25 (Remark 9.2.14, p. 419 of the 2021 book; 2017: Remark 9.5): for a
submanifold `M`, `x ∈ ∂M` iff `x ∈ ∂X` and `T_xM ⊄ T^R_xX`.

`A` is the conjunction of the types of the six listed theorems, universe instantiated at `0`
(`B` lives in `Type`): `remark_9_2_14` (⇐), `remark_9_2_14_mem_boundary` (`∂M ⊆ ∂X` for every
sub-M-polyfold), `mem_boundary_subPolyfold_iff` (`a ∈ ∂M` of the induced structure is
`1 ≤ d_M(a)`, `Iff.rfl`), `remark_9_2_14_not_isTangentReducedAt` (⇒), `remark_9_2_14_iff` and
`remark_9_2_14_not_mem_boundary_iff`.

* B's `submanifoldBoundary P M` is, for a smooth `M` and `x ∈ M`, `1 ≤ subDegIndex`
  (`mem_submanifoldBoundary_iff_subDegIndex`, not an item theorem), which is the project's
  `a ∈ (subPolyfold _).boundary` by definition.
* `A_to_B`: `remark_9_2_14_iff`.
* `B_to_A`: the four conjuncts about a smooth submanifold come from `B`; the two others are
  re-proved outright: `mem_boundary_subPolyfold_iff` is `Iff.rfl`, and
  `remark_9_2_14_mem_boundary`, stated for an arbitrary sub-M-polyfold (wider than `B`'s smooth
  submanifolds), is Lemma 2.26 (`subDegIndex_le`, not an item theorem of V9_25). -/

namespace RoundTrip.V9_25
open Polyfold

/-- The project's statement (universes at `0`). -/
def A : Prop :=
  (type_of% @Polyfold.MPolyfold.remark_9_2_14.{0}) ∧
  (type_of% @Polyfold.MPolyfold.remark_9_2_14_mem_boundary.{0}) ∧
  (type_of% @Polyfold.MPolyfold.mem_boundary_subPolyfold_iff.{0}) ∧
  (type_of% @Polyfold.MPolyfold.remark_9_2_14_not_isTangentReducedAt.{0}) ∧
  (type_of% @Polyfold.MPolyfold.remark_9_2_14_iff.{0}) ∧
  (type_of% @Polyfold.MPolyfold.remark_9_2_14_not_mem_boundary_iff.{0})

theorem A_holds : A :=
  ⟨@Polyfold.MPolyfold.remark_9_2_14.{0}, @Polyfold.MPolyfold.remark_9_2_14_mem_boundary.{0},
    @Polyfold.MPolyfold.mem_boundary_subPolyfold_iff.{0},
    @Polyfold.MPolyfold.remark_9_2_14_not_isTangentReducedAt.{0},
    @Polyfold.MPolyfold.remark_9_2_14_iff.{0},
    @Polyfold.MPolyfold.remark_9_2_14_not_mem_boundary_iff.{0}⟩

theorem A_to_B : A → B := by
  intro hA Z _ _ _ P M x hM hx
  rw [MPolyfold.mem_submanifoldBoundary_iff_subDegIndex hM hx]
  exact hA.2.2.2.2.1 hM ⟨x, hx⟩

/-- `B` in the project's form: `1 ≤ d_M(a) ↔ a ∈ ∂X ∧ T_aM ⊄ T^R_aX`. -/
theorem B_iff (hB : B) {Z : Type} [TopologicalSpace Z] [T2Space Z] [ParacompactSpace Z]
    {P : MPolyfold Z} {M : Set Z} (hM : P.IsSmoothSubmanifold M) (a : M) :
    1 ≤ P.subDegIndex hM.isSubMPolyfold a ↔ a.1 ∈ P.boundary ∧ ¬ P.IsTangentReducedAt M a := by
  rw [← MPolyfold.mem_submanifoldBoundary_iff_subDegIndex hM a.2]
  exact hB Z P M a.1 hM a.2

theorem B_to_A : B → A := by
  intro hB
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro Z _ _ _ P M hM a h
    exact (B_iff hB hM a).2 h
  · intro Z _ _ _ P M hM a h
    exact h.trans (MPolyfold.subDegIndex_le hM a)
  · intro Z _ _ _ P M hM a
    exact Iff.rfl
  · intro Z _ _ _ P M hM a h
    exact (B_iff hB hM a).1 h
  · intro Z _ _ _ P M hM a
    exact B_iff hB hM a
  · intro Z _ _ _ P M hM a hb
    change ¬ 1 ≤ P.subDegIndex hM.isSubMPolyfold a ↔ _
    rw [B_iff hB hM a]
    exact ⟨fun h => by_contra fun hT => h ⟨hb, hT⟩, fun hT h => h.2 hT⟩

#rt_check RoundTrip.V9_25.A_to_B [Polyfold.MPolyfold.remark_9_2_14,
  Polyfold.MPolyfold.remark_9_2_14_mem_boundary, Polyfold.MPolyfold.mem_boundary_subPolyfold_iff,
  Polyfold.MPolyfold.remark_9_2_14_not_isTangentReducedAt, Polyfold.MPolyfold.remark_9_2_14_iff,
  Polyfold.MPolyfold.remark_9_2_14_not_mem_boundary_iff]
#rt_check RoundTrip.V9_25.B_to_A [Polyfold.MPolyfold.remark_9_2_14,
  Polyfold.MPolyfold.remark_9_2_14_mem_boundary, Polyfold.MPolyfold.mem_boundary_subPolyfold_iff,
  Polyfold.MPolyfold.remark_9_2_14_not_isTangentReducedAt, Polyfold.MPolyfold.remark_9_2_14_iff,
  Polyfold.MPolyfold.remark_9_2_14_not_mem_boundary_iff]
#rt_overlap RoundTrip.V9_25.B_to_A [Polyfold.MPolyfold.remark_9_2_14,
  Polyfold.MPolyfold.remark_9_2_14_mem_boundary, Polyfold.MPolyfold.mem_boundary_subPolyfold_iff,
  Polyfold.MPolyfold.remark_9_2_14_not_isTangentReducedAt, Polyfold.MPolyfold.remark_9_2_14_iff,
  Polyfold.MPolyfold.remark_9_2_14_not_mem_boundary_iff]

end RoundTrip.V9_25
