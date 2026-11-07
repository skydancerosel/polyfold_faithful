import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V7_51

/-!
Round trip for V7_51 (Corollary 7.2: neighbourhoods of component compact sets).

`A` is the conjunction of the types, at universe `0`, of
`Polyfold.EpGroupoid.locallyPathConnectedSpace_orbitSpace` (`|X|` is locally path connected),
`Polyfold.EpGroupoid.exists_isOpen_metrizableSpace_closure` (every neighbourhood `W` of `z`
contains `cl U(z)` for an open `U(z) ∋ z` with metrizable closure),
`Polyfold.EpGroupoid.corollary_7_2_of_isCompact` (the compact case, with `cl U ⊆ W` for a given
open `W ⊇ K`) and `Polyfold.EpGroupoid.corollary_7_2` (the text's statement).

* `A → B`: `corollary_7_2`, after identifying the project's `IsComponentCompact` with `B`'s
  `IsComponentCompactB` (the same as Definition 7.14, see V7_49).
* `B → A`:
  - `corollary_7_2` is `B`;
  - `exists_isOpen_metrizableSpace_closure`: `B` for the component compact `K = {z}` gives an open
    `U ∋ z` with metrizable `cl U`; the regularity of `|X|` (the project's instance
    `EpGroupoid.lemma_7_7`, Lemma 7.7, not banned here) gives a closed neighbourhood `t ⊆ W ∩ U`
    of `z`, and `U(z) := int t` has `cl U(z) ⊆ t ⊆ W ∩ cl U`, metrizable as a subspace of `cl U`;
  - `corollary_7_2_of_isCompact`: `B` for the compact (hence component compact: components are
    closed) `K` gives `U`; regularity gives an open `V ⊇ K` with `cl V ⊆ W ∩ U`
    (`IsCompact.exists_isOpen_closure_subset`), and `cl V` is a closed subset of the paracompact
    metrizable `cl U`, so paracompact and metrizable, and `V ⊆ U` is metrizable;
  - `locallyPathConnectedSpace_orbitSpace` is **not** a consequence of `B` (nor stated by the
    text's Corollary 7.2); it is proved outright from the unbanned
    `MPolyfold.locallyPathConnectedSpace_quotient` (`LocConnected.lean`), exactly as the project
    proves it.  This conjunct of `B → A` does not use the hypothesis.
-/

namespace RoundTrip.V7_51
open Polyfold Set Filter Topology TopologicalSpace

/-- The four listed theorems, universes at `0`. -/
def A : Prop :=
  type_of% @Polyfold.EpGroupoid.locallyPathConnectedSpace_orbitSpace.{0} ∧
  type_of% @Polyfold.EpGroupoid.exists_isOpen_metrizableSpace_closure.{0} ∧
  type_of% @Polyfold.EpGroupoid.corollary_7_2_of_isCompact.{0} ∧
  type_of% @Polyfold.EpGroupoid.corollary_7_2.{0}

theorem A_holds : A :=
  ⟨@Polyfold.EpGroupoid.locallyPathConnectedSpace_orbitSpace.{0},
    @Polyfold.EpGroupoid.exists_isOpen_metrizableSpace_closure.{0},
    @Polyfold.EpGroupoid.corollary_7_2_of_isCompact.{0},
    @Polyfold.EpGroupoid.corollary_7_2.{0}⟩

section
variable {Obj Mor : Type} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor]

theorem isComponentCompact_iff (X : EpGroupoid Obj Mor) (K : Set X.OrbitSpace) :
    X.IsComponentCompact K ↔ IsComponentCompactB X K :=
  ⟨fun h _ ⟨z, hz⟩ => hz ▸ h z, fun h z => h _ ⟨z, rfl⟩⟩

end

theorem A_to_B : A → B := fun hA _ _ _ _ _ _ _ _ X K hK =>
  hA.2.2.2 X ((isComponentCompact_iff X K).2 hK)

theorem B_to_A : B → A := by
  intro hB
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- not from `B`: the project's unbanned quotient lemma (`LocConnected.lean`)
    intro Obj Mor _ _ _ _ _ _ X
    exact X.PObj.locallyPathConnectedSpace_quotient X.orbitSetoid
  · intro Obj Mor _ _ _ _ _ _ X z W hW
    have hK : IsComponentCompactB X {z} := fun C _ =>
      ((finite_singleton z).subset inter_subset_left).isCompact
    obtain ⟨U, hUo, hzU, -, hUm, -⟩ := hB Obj Mor X {z} hK
    obtain ⟨t, ht, htc, htWU⟩ :=
      exists_mem_nhds_isClosed_subset (inter_mem hW (hUo.mem_nhds (hzU rfl)))
    have hcl : closure (interior t) ⊆ W ∩ U := (closure_minimal interior_subset htc).trans htWU
    exact ⟨interior t, isOpen_interior, mem_interior_iff_mem_nhds.2 ht,
      hcl.trans inter_subset_left,
      (IsEmbedding.inclusion ((hcl.trans inter_subset_right).trans subset_closure)).metrizableSpace⟩
  · intro Obj Mor _ _ _ _ _ _ X K W hK hW hKW
    have hKc : IsComponentCompactB X K := fun C ⟨z, hz⟩ =>
      hz ▸ hK.inter_right isClosed_connectedComponent
    obtain ⟨U, hUo, hKU, hUp, hUm, hUm'⟩ := hB Obj Mor X K hKc
    obtain ⟨V, hVo, hKV, hVWU⟩ :=
      hK.exists_isOpen_closure_subset ((hW.inter hUo).mem_nhdsSet.2 (subset_inter hKW hKU))
    have hVU : closure V ⊆ closure U := (hVWU.trans inter_subset_right).trans subset_closure
    exact ⟨V, hVo, hKV, hVWU.trans inter_subset_left,
      (IsClosedEmbedding.inclusion hVU
        (isClosed_closure.preimage continuous_subtype_val)).paracompactSpace,
      (IsEmbedding.inclusion hVU).metrizableSpace,
      (IsEmbedding.inclusion (subset_closure.trans (hVWU.trans inter_subset_right))).metrizableSpace⟩
  · intro Obj Mor _ _ _ _ _ _ X K hK
    exact hB Obj Mor X K ((isComponentCompact_iff X K).1 hK)

#rt_check RoundTrip.V7_51.A_to_B [Polyfold.EpGroupoid.locallyPathConnectedSpace_orbitSpace,
  Polyfold.EpGroupoid.exists_isOpen_metrizableSpace_closure,
  Polyfold.EpGroupoid.corollary_7_2_of_isCompact, Polyfold.EpGroupoid.corollary_7_2]
#rt_check RoundTrip.V7_51.B_to_A [Polyfold.EpGroupoid.locallyPathConnectedSpace_orbitSpace,
  Polyfold.EpGroupoid.exists_isOpen_metrizableSpace_closure,
  Polyfold.EpGroupoid.corollary_7_2_of_isCompact, Polyfold.EpGroupoid.corollary_7_2]
#rt_overlap RoundTrip.V7_51.B_to_A [Polyfold.EpGroupoid.locallyPathConnectedSpace_orbitSpace,
  Polyfold.EpGroupoid.exists_isOpen_metrizableSpace_closure,
  Polyfold.EpGroupoid.corollary_7_2_of_isCompact, Polyfold.EpGroupoid.corollary_7_2]

end RoundTrip.V7_51
