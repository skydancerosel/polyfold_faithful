import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V7_48

/-!
Round trip for V7_48 (p. 247, before Definition 7.14: subsets of `|X|` are locally metrizable,
regular and Hausdorff).

`A` is the conjunction of the types, at universe `0`, of
`Polyfold.EpGroupoid.exists_metrizable_nhds_subtype` (every point of a subset `S ⊆ |X|` has an
open neighbourhood in `S` which is metrizable) and
`Polyfold.EpGroupoid.metrizableSpace_of_paracompactSpace_subtype` (a paracompact subset of `|X|`
is metrizable).  `B` is, for every subset `S ⊆ |X|`: locally metrizable, regular (the text's
definition) and Hausdorff.

* `A → B`: the "locally metrizable" conjunct is `A`'s first theorem.  The "regular" and
  "Hausdorff" conjuncts are not stated by `A`'s two theorems; they are Mathlib's subtype instances
  applied to the project's instances `EpGroupoid.lemma_7_7` (`RegularSpace |X|`, Lemma 7.7) and
  `EpGroupoid.lemma_7_6` (`T2Space |X|`, Lemma 7.6), as the docstring of
  `exists_metrizable_nhds_subtype` says.  Those two conjuncts are proved outright here (from
  unbanned project lemmas), not from the hypothesis.  (A's two theorems alone, read abstractly,
  do not give regularity: a Hausdorff locally metrizable non-regular space, e.g. the plane with
  the neighbourhoods of `0` cut along the punctured `x`-axis, satisfies both.)
* `B → A`: the first theorem is B's local metrizability; the second is Smirnov's theorem
  (`Polyfold.metrizableSpace_of_locally`, Part I) in the subspace `S`, with `T2Space S` and the
  local metrizability both taken from `B`.
-/

namespace RoundTrip.V7_48
open Polyfold Set Filter Topology TopologicalSpace

/-- The project's two theorems, universes at `0`. -/
def A : Prop :=
  type_of% @Polyfold.EpGroupoid.exists_metrizable_nhds_subtype.{0} ∧
  type_of% @Polyfold.EpGroupoid.metrizableSpace_of_paracompactSpace_subtype.{0}

theorem A_holds : A :=
  ⟨@Polyfold.EpGroupoid.exists_metrizable_nhds_subtype.{0},
    @Polyfold.EpGroupoid.metrizableSpace_of_paracompactSpace_subtype.{0}⟩

/-- Mathlib's regularity gives the text's. -/
theorem text_of_regular (Y : Type) [TopologicalSpace Y] [RegularSpace Y] : IsRegularText Y := by
  intro S _ hS z hz
  have hd : Disjoint (𝓝ˢ S) (𝓝 z) := RegularSpace.regular hS hz
  obtain ⟨V, ⟨hVo, hSV⟩, U, ⟨hzU, hUo⟩, hVU⟩ :=
    ((hasBasis_nhdsSet S).disjoint_iff (nhds_basis_opens z)).1 hd
  exact ⟨U, V, hUo, hVo, hzU, hSV, by rw [inter_comm]; exact hVU.inter_eq⟩

theorem A_to_B : A → B := by
  intro hA Obj Mor _ _ _ _ _ _ X S
  refine ⟨fun y => hA.1 X S y, ?_, inferInstance⟩
  -- regularity of `S`: Mathlib's subtype instance on the project's `RegularSpace |X|` (Lemma 7.7)
  exact text_of_regular S

theorem B_to_A : B → A := by
  intro hB
  refine ⟨fun {Obj Mor} _ _ _ _ _ _ X S w => (hB Obj Mor X S).1 w, ?_⟩
  intro Obj Mor _ _ _ _ _ _ X S _
  obtain ⟨hlm, -, hT2⟩ := hB Obj Mor X S
  exact @metrizableSpace_of_locally _ _ hT2 ‹_› hlm

#rt_check RoundTrip.V7_48.A_to_B [Polyfold.EpGroupoid.exists_metrizable_nhds_subtype,
  Polyfold.EpGroupoid.metrizableSpace_of_paracompactSpace_subtype]
#rt_check RoundTrip.V7_48.B_to_A [Polyfold.EpGroupoid.exists_metrizable_nhds_subtype,
  Polyfold.EpGroupoid.metrizableSpace_of_paracompactSpace_subtype]
#rt_overlap RoundTrip.V7_48.B_to_A [Polyfold.EpGroupoid.exists_metrizable_nhds_subtype,
  Polyfold.EpGroupoid.metrizableSpace_of_paracompactSpace_subtype]
#rt_overlap RoundTrip.V7_48.A_to_B [Polyfold.EpGroupoid.exists_metrizable_nhds_subtype,
  Polyfold.EpGroupoid.metrizableSpace_of_paracompactSpace_subtype]

end RoundTrip.V7_48
