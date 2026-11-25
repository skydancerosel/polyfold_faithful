import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V17_49

set_option maxSynthPendingDepth 3

/-! Round trip for V17_49 (2021 Proposition 17.2.12, p. 776: the unique topology on
`M(TΨ₁, TΨ₂)` making the maps (17.42) open embeddings).

`A` is the conjunction of the types of `eq_chartTopology` (the generic uniqueness of a topology
for which a covering family of maps are open embeddings; universes `0, 0, 0`) and
`proposition_17_2_12` (universe `0`; `B` uses `GCT.{0}`).

* `A_to_B`: `τ := tangentTrTopology hU Ψ₁ Ψ₂`; existence is the first part of
  `proposition_17_2_12`, uniqueness the second.  The hypothesis `eq_chartTopology` is not needed.
* `B_to_A`: the generic `eq_chartTopology` is not about the GCT at all, so `B` cannot give it; it
  is re-proved here (`eq_chartTopology'`, the project's argument).  For `proposition_17_2_12`: `B`'s
  unique `τ` is, by `eq_chartTopology'` and Lemma 17.2.11 (1) (`lemma_17_2_11_one`, the maps
  (17.42) cover `M(TΨ₁, TΨ₂)`), equal to `tangentTrTopology`, so `tangentTrTopology` makes the
  maps open embeddings; any other such topology equals `τ` by uniqueness.
-/

namespace RoundTrip.V17_49
open Polyfold GCT.PolyfoldConstruction Topology

def A : Prop :=
  (type_of% @Polyfold.eq_chartTopology.{0, 0, 0}) ∧
  (type_of% @Polyfold.GCT.PolyfoldConstruction.proposition_17_2_12.{0})

theorem A_holds : A :=
  ⟨@Polyfold.eq_chartTopology.{0, 0, 0},
    @Polyfold.GCT.PolyfoldConstruction.proposition_17_2_12.{0}⟩

theorem A_to_B : A → B := by
  rintro ⟨-, h⟩ C S hU Ψ₁ Ψ₂
  refine ⟨S.tangentTrTopology hU Ψ₁ Ψ₂, fun o T => (h hU Ψ₁ Ψ₂).1 T, fun t ht => ?_⟩
  exact (h hU Ψ₁ Ψ₂).2 t fun {o} T => ht o T

/-- The project's `eq_chartTopology`, re-proved (generic topology). -/
theorem eq_chartTopology' {X : Type*} {ι : Type*} {U : ι → Type*} [∀ i, TopologicalSpace (U i)]
    (φ : ∀ i, U i → X) (hcover : ∀ x, ∃ i u, φ i u = x) (t : TopologicalSpace X)
    (ht : ∀ i, @IsOpenEmbedding _ _ _ t (φ i)) : t = chartTopology φ := by
  refine TopologicalSpace.ext (funext fun V => propext ?_)
  rw [isOpen_chartTopology_iff]
  refine ⟨fun hV i => (ht i).continuous.isOpen_preimage V hV, fun hV => ?_⟩
  have hV' : V = ⋃ i, φ i '' (φ i ⁻¹' V) := by
    ext x
    refine ⟨fun hx => ?_, fun hx => ?_⟩
    · obtain ⟨i, u, rfl⟩ := hcover x
      exact Set.mem_iUnion.2 ⟨i, u, hx, rfl⟩
    · obtain ⟨i, hi⟩ := Set.mem_iUnion.1 hx
      obtain ⟨u, hu, rfl⟩ := hi
      exact hu
  rw [hV']
  exact @isOpen_iUnion _ _ t _ fun i => (ht i).isOpenMap _ (hV i)

theorem B_to_A : B → A := by
  intro hB
  refine ⟨fun {X ι U} _ φ hcover t ht => eq_chartTopology' φ hcover t ht,
    fun {C S} hU Ψ₁ Ψ₂ => ?_⟩
  obtain ⟨τ, hτ, huniq⟩ := hB C S hU Ψ₁ Ψ₂
  have heq : τ = S.tangentTrTopology hU Ψ₁ Ψ₂ :=
    eq_chartTopology' (U := fun i : S.TTrIndex Ψ₁ Ψ₂ => Ψ₁.1.P.tangentPreimage i.2.srcSet)
      (fun i => S.tangentTrChart hU i.2)
      (fun x => by
        obtain ⟨o, T, k, -, hk⟩ := lemma_17_2_11_one hU x
        exact ⟨⟨o, T⟩, k, hk⟩) τ fun i => hτ i.1 i.2
  subst heq
  exact ⟨fun {o} T => hτ o T, fun t ht => huniq t fun o T => ht T⟩

/-- The main conjunct alone. -/
theorem main_to_B :
    (type_of% @Polyfold.GCT.PolyfoldConstruction.proposition_17_2_12.{0}) → B := fun h =>
  A_to_B ⟨fun {_ _ _} _ φ hc t ht => eq_chartTopology' φ hc t ht, h⟩

theorem B_to_main : B →
    (type_of% @Polyfold.GCT.PolyfoldConstruction.proposition_17_2_12.{0}) := fun h =>
  (B_to_A h).2

#rt_check RoundTrip.V17_49.A_to_B [Polyfold.eq_chartTopology,
  Polyfold.GCT.PolyfoldConstruction.proposition_17_2_12]
#rt_check RoundTrip.V17_49.B_to_A [Polyfold.eq_chartTopology,
  Polyfold.GCT.PolyfoldConstruction.proposition_17_2_12]
#rt_check RoundTrip.V17_49.main_to_B [Polyfold.eq_chartTopology,
  Polyfold.GCT.PolyfoldConstruction.proposition_17_2_12]
#rt_check RoundTrip.V17_49.B_to_main [Polyfold.eq_chartTopology,
  Polyfold.GCT.PolyfoldConstruction.proposition_17_2_12]
#rt_overlap RoundTrip.V17_49.B_to_A [Polyfold.eq_chartTopology,
  Polyfold.GCT.PolyfoldConstruction.proposition_17_2_12]

end RoundTrip.V17_49
