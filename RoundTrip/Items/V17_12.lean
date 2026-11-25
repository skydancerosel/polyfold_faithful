import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V17_12

set_option maxSynthPendingDepth 3

/-! Round trip for V17_12 (2021 Proposition 17.1.11, p. 750: the properness property).

`A` is the conjunction of the types of `proposition_17_1_11` (`S.HasPropernessProperty`, the main
conjunct), `GroupoidStr.exists_subseq_tendsto_smul` (convergence in `G\O` lifts to a subsequence,
the step (17.5) of the proof) and the example `reflection_hasPropernessProperty`, at universe `0`
(`B` is stated for `GCT.{0}`).

* `A_to_B`, `main_to_B`: `HasPropernessProperty` unfolds to `B` (`B`'s `srcT`, `tgtT` are the
  project's `a.src`, `a.tgt` by definition).
* `B_to_A`: `proposition_17_1_11` and the reflection example are `B` (specialised to
  `reflectionConstruction`); the proof-step lemma `exists_subseq_tendsto_smul` (pure topology of
  finite group actions) is not a consequence of `B`; it is re-proved outright (the project's
  proof, copied). -/

namespace RoundTrip.V17_12
open Polyfold Polyfold.GCT.PolyfoldConstruction
open Set Function Topology Filter

def A : Prop :=
  (type_of% @Polyfold.GCT.PolyfoldConstruction.proposition_17_1_11.{0}) ∧
  (type_of% @Polyfold.GroupoidStr.exists_subseq_tendsto_smul.{0}) ∧
  (type_of% @Polyfold.GCT.PolyfoldConstruction.reflection_hasPropernessProperty)

theorem A_holds : A :=
  ⟨@Polyfold.GCT.PolyfoldConstruction.proposition_17_1_11.{0},
    @Polyfold.GroupoidStr.exists_subseq_tendsto_smul.{0},
    @Polyfold.GCT.PolyfoldConstruction.reflection_hasPropernessProperty⟩

theorem main_to_B : type_of% @Polyfold.GCT.PolyfoldConstruction.proposition_17_1_11.{0} → B :=
  fun h _ S Ψ q => h S Ψ q

theorem B_to_main : B → type_of% @Polyfold.GCT.PolyfoldConstruction.proposition_17_1_11.{0} :=
  fun hB {C} S Ψ q => hB C S Ψ q

theorem A_to_B : A → B := fun hA => main_to_B hA.1

/-- `GroupoidStr.exists_subseq_tendsto_smul`, re-proved (the project's proof). -/
theorem exists_subseq_tendsto_smul' {G O : Type} [Group G] [Finite G]
    [TopologicalSpace O] [FirstCountableTopology O] [MulAction G O]
    (hc : ∀ g : G, Continuous fun y : O => g • y) {x : ℕ → O} {a : O}
    (h : Tendsto (fun k => (GroupoidStr.translation G O).π (x k)) atTop
      (𝓝 ((GroupoidStr.translation G O).π a))) :
    ∃ g : G, ∃ φ : ℕ → ℕ, StrictMono φ ∧ Tendsto (x ∘ φ) atTop (𝓝 (g • a)) := by
  obtain ⟨B, hB⟩ := (𝓝 a).exists_antitone_basis
  -- eventually some translate of `x k` lies in `B n`
  have hev : ∀ n, ∀ᶠ k in atTop, ∃ g : G, g • x k ∈ B n := by
    intro n
    have hO : IsOpen ((GroupoidStr.translation G O).π '' interior (B n)) :=
      GroupoidStr.isOpenMap_π_translation hc _ isOpen_interior
    have hmem : (GroupoidStr.translation G O).π a ∈
        (GroupoidStr.translation G O).π '' interior (B n) :=
      ⟨a, mem_interior_iff_mem_nhds.2 (hB.mem n), rfl⟩
    filter_upwards [h (hO.mem_nhds hmem)] with k hk
    obtain ⟨w, hw, hwk⟩ := hk
    obtain ⟨φ, h1, h2⟩ := (GroupoidStr.π_eq_π_iff _).1 hwk.symm
    refine ⟨φ.1, ?_⟩
    change φ.2 = x k at h1
    change φ.1 • φ.2 = w at h2
    rw [← h1, h2]
    exact interior_subset hw
  -- one translate works for every `n` infinitely often
  have hg : ∃ g : G, ∀ n, ∃ᶠ k in atTop, g • x k ∈ B n := by
    by_contra hne
    simp only [not_exists, not_forall, Filter.not_frequently] at hne
    choose n hn using hne
    obtain ⟨N, hN⟩ := (Set.finite_range n).bddAbove
    have hall : ∀ᶠ k in atTop, ∀ g : G, g • x k ∉ B N := Filter.eventually_all.2 fun g =>
      (hn g).mono fun k hk hkN => hk (hB.antitone (hN ⟨g, rfl⟩) hkN)
    obtain ⟨k, ⟨g, hgk⟩, hk⟩ := ((hev N).and hall).exists
    exact hk g hgk
  obtain ⟨g, hg⟩ := hg
  obtain ⟨φ, hφ, hφB⟩ := Filter.extraction_forall_of_frequently hg
  refine ⟨g⁻¹, φ, hφ, ?_⟩
  have h1 : Tendsto (fun n => g • x (φ n)) atTop (𝓝 a) := hB.tendsto hφB
  have h2 := ((hc g⁻¹).tendsto a).comp h1
  refine h2.congr fun n => ?_
  simp only [Function.comp_apply, inv_smul_smul]




theorem B_to_A : B → A := fun hB =>
  ⟨B_to_main hB, fun hc _ _ h => exists_subseq_tendsto_smul' hc h,
    B_to_main hB reflectionConstruction⟩

#rt_check RoundTrip.V17_12.A_to_B [Polyfold.GCT.PolyfoldConstruction.proposition_17_1_11,
  Polyfold.GroupoidStr.exists_subseq_tendsto_smul,
  Polyfold.GCT.PolyfoldConstruction.reflection_hasPropernessProperty]
#rt_check RoundTrip.V17_12.B_to_A [Polyfold.GCT.PolyfoldConstruction.proposition_17_1_11,
  Polyfold.GroupoidStr.exists_subseq_tendsto_smul,
  Polyfold.GCT.PolyfoldConstruction.reflection_hasPropernessProperty]
#rt_check RoundTrip.V17_12.main_to_B [Polyfold.GCT.PolyfoldConstruction.proposition_17_1_11,
  Polyfold.GroupoidStr.exists_subseq_tendsto_smul,
  Polyfold.GCT.PolyfoldConstruction.reflection_hasPropernessProperty]
#rt_check RoundTrip.V17_12.B_to_main [Polyfold.GCT.PolyfoldConstruction.proposition_17_1_11,
  Polyfold.GroupoidStr.exists_subseq_tendsto_smul,
  Polyfold.GCT.PolyfoldConstruction.reflection_hasPropernessProperty]
#rt_overlap RoundTrip.V17_12.B_to_A [Polyfold.GCT.PolyfoldConstruction.proposition_17_1_11,
  Polyfold.GroupoidStr.exists_subseq_tendsto_smul,
  Polyfold.GCT.PolyfoldConstruction.reflection_hasPropernessProperty]

end RoundTrip.V17_12
