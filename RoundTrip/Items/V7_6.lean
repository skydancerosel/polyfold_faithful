import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V7_6

/-! Round trip for V7_6 (pp. 227–228: the levels of an ep-groupoid, the filtration of `|X|`, the
degeneracy indices).

The listed definitions are `MPolyfold.maxLevel` and `EpGroupoid.orbitLevel`; the listed theorems
are `EpGroupoid.mem_levelSet_src_iff`, `mem_levelSet_tgt_iff`, `degIndex_src`, `degIndex_tgt` (one
universe each) and `MPolyfold.IsLocalScDiffeo.maxLevel_eq`, `IsLocalScDiffeo.degIndex_eq` (two
universes each); `A` is the conjunction of their types, universes at `0`.

* `A → B`: **not proved**, for one conjunct only.  B's `FiltrationB` contains "`X_∞` is dense in
  every `X_k` (for the level-`k` topology `levelTopology k`)", for the object and the morphism
  M-polyfold.  `A` says nothing about density, and the project has no density theorem for the
  levels of an M-polyfold (only `ScBanach.dense_smooth` for sc-Banach spaces).  Proving it needs
  the density of smooth points of a partial quadrant `C ∩ E_k` near a point of `O_k`, the
  level-`k` continuity of the retraction and of the chart transitions, and the structure of the
  generated topology: real Part I mathematics, believed true (the text states it), not attempted.
  Everything else in `B` follows from `A` (`A_to_B_of_density`: `A` plus density gives `B`): the
  remaining filtration facts and `ml` are Part I lemmas (`levelSet_zero`, `levelSet_succ_subset`,
  `le_maxLevel_iff`); level preservation, `ml(s φ) = ml(φ) = ml(t φ)`, `d_X(s φ) = d_𝐗(φ) =
  d_X(t φ)` and `d` constant on orbits are the hypothesis; the filtration of `|X|` uses the
  hypothesis for `|X_∞| ⊇ ⋂ |X_k|` (an object isomorphic to points of every `X_k` lies in every
  `X_k`).
* `B → A`: the four ep-groupoid conjuncts are B's; `IsLocalScDiffeo.maxLevel_eq` and
  `IsLocalScDiffeo.degIndex_eq` are for arbitrary local sc-diffeomorphisms between arbitrary
  M-polyfolds, which `B` (only `s`, `t` of an ep-groupoid) does not give; they are re-proved
  outright (`IsLocalScDiffeo.mem_levelSet_iff`, Proposition 2.24). -/

namespace RoundTrip.V7_6
open Polyfold Set

/-- The project's statement (universes at `0`). -/
def A : Prop :=
  (type_of% @Polyfold.EpGroupoid.mem_levelSet_src_iff.{0}) ∧
  (type_of% @Polyfold.EpGroupoid.mem_levelSet_tgt_iff.{0}) ∧
  (type_of% @Polyfold.MPolyfold.IsLocalScDiffeo.maxLevel_eq.{0, 0}) ∧
  (type_of% @Polyfold.MPolyfold.IsLocalScDiffeo.degIndex_eq.{0, 0}) ∧
  (type_of% @Polyfold.EpGroupoid.degIndex_src.{0}) ∧
  (type_of% @Polyfold.EpGroupoid.degIndex_tgt.{0})

theorem A_holds : A :=
  ⟨@Polyfold.EpGroupoid.mem_levelSet_src_iff.{0}, @Polyfold.EpGroupoid.mem_levelSet_tgt_iff.{0},
    @Polyfold.MPolyfold.IsLocalScDiffeo.maxLevel_eq.{0, 0},
    @Polyfold.MPolyfold.IsLocalScDiffeo.degIndex_eq.{0, 0},
    @Polyfold.EpGroupoid.degIndex_src.{0}, @Polyfold.EpGroupoid.degIndex_tgt.{0}⟩

/-- The one claim of `B` that `A` lacks: `Z_∞` is dense in every `Z_k` (level-`k` topology), for
every M-polyfold `Z`. -/
def DensityB : Prop :=
  ∀ (Z : Type) [TopologicalSpace Z] [T2Space Z] [ParacompactSpace Z] (P : MPolyfold Z) (k : ℕ),
    @Dense ↥(P.levelSet k) (P.levelTopology k) {z | (z : Z) ∈ P.smoothSet}

/-! ### `A → B`, up to the density of `X_∞` in `X_k` -/

theorem A_to_B_of_density (hA : A) (hD : DensityB) : B := by
  intro Obj Mor _ _ _ _ _ _ X
  have hsrc := fun φ m => hA.1 X φ m
  have htgt := fun φ m => hA.2.1 X φ m
  refine ⟨⟨X.PObj.levelSet_zero, X.PObj.levelSet_succ_subset, rfl, hD Obj X.PObj⟩,
    ⟨X.PMor.levelSet_zero, X.PMor.levelSet_succ_subset, rfl, hD Mor X.PMor⟩,
    fun _ _ => MPolyfold.le_maxLevel_iff, fun _ _ => MPolyfold.le_maxLevel_iff,
    fun φ m => ⟨(hsrc φ m).symm, (htgt φ m).symm⟩,
    fun φ => ⟨hA.2.2.1 X.isLocalScDiffeo_src φ, (hA.2.2.1 X.isLocalScDiffeo_tgt φ).symm⟩,
    fun _ => rfl, ?_, fun k => image_mono (X.PObj.levelSet_succ_subset k), ?_,
    fun φ => ⟨(hA.2.2.2.2.1 X φ).symm, hA.2.2.2.2.2 X φ⟩, ?_⟩
  · rw [X.PObj.levelSet_zero, image_univ]
    exact range_eq_univ.2 X.surjective_π
  · ext z
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact mem_iInter.2 fun k => ⟨x, mem_iInter.1 hx k, rfl⟩
    · intro hz
      obtain ⟨x, rfl⟩ := X.surjective_π z
      refine ⟨x, mem_iInter.2 fun k => ?_, rfl⟩
      obtain ⟨y, hy, hyx⟩ := mem_iInter.1 hz k
      obtain ⟨φ, rfl, rfl⟩ := X.π_eq_π_iff.1 hyx
      exact (htgt φ k).2 ((hsrc φ k).1 hy)
  · rintro _ _ ⟨φ, rfl, rfl⟩
    exact (hA.2.2.2.2.1 X φ).symm.trans (hA.2.2.2.2.2 X φ)

/-! ### `B → A` -/

theorem B_to_A : B → A := by
  intro hB
  refine ⟨fun {Obj Mor} _ _ _ _ _ _ X φ m => ((hB Obj Mor X).2.2.2.2.1 φ m).1.symm,
    fun {Obj Mor} _ _ _ _ _ _ X φ m => ((hB Obj Mor X).2.2.2.2.1 φ m).2.symm, ?_, ?_,
    fun {Obj Mor} _ _ _ _ _ _ X φ => ((hB Obj Mor X).2.2.2.2.2.2.2.2.2.2.1 φ).1.symm,
    fun {Obj Mor} _ _ _ _ _ _ X φ => ((hB Obj Mor X).2.2.2.2.2.2.2.2.2.2.1 φ).2⟩
  · -- re-proved outright: a local sc-diffeomorphism preserves the levels
    intro Z _ _ _ P Y _ _ _ Q f hf x
    simp only [MPolyfold.maxLevel, hf.mem_levelSet_iff]
  · -- re-proved outright: Proposition 2.24 on a sheet of `f`
    intro Z _ _ _ P Y _ _ _ Q f hf x
    obtain ⟨U, V, g, hx, hd⟩ := hf x
    exact (proposition_2_24 hd hx).symm

#rt_check RoundTrip.V7_6.B_to_A [Polyfold.EpGroupoid.mem_levelSet_src_iff, Polyfold.EpGroupoid.mem_levelSet_tgt_iff, Polyfold.MPolyfold.IsLocalScDiffeo.maxLevel_eq, Polyfold.MPolyfold.IsLocalScDiffeo.degIndex_eq, Polyfold.EpGroupoid.degIndex_src, Polyfold.EpGroupoid.degIndex_tgt]
#rt_check RoundTrip.V7_6.A_to_B_of_density [Polyfold.EpGroupoid.mem_levelSet_src_iff, Polyfold.EpGroupoid.mem_levelSet_tgt_iff, Polyfold.MPolyfold.IsLocalScDiffeo.maxLevel_eq, Polyfold.MPolyfold.IsLocalScDiffeo.degIndex_eq, Polyfold.EpGroupoid.degIndex_src, Polyfold.EpGroupoid.degIndex_tgt]
#rt_overlap RoundTrip.V7_6.B_to_A [Polyfold.EpGroupoid.mem_levelSet_src_iff, Polyfold.EpGroupoid.mem_levelSet_tgt_iff, Polyfold.MPolyfold.IsLocalScDiffeo.maxLevel_eq, Polyfold.MPolyfold.IsLocalScDiffeo.degIndex_eq, Polyfold.EpGroupoid.degIndex_src, Polyfold.EpGroupoid.degIndex_tgt]

end RoundTrip.V7_6
