import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V7_12

/-! Round trip for V7_12 (Proposition 7.2, p. 229: countable monotone neighbourhood bases of
`|X|`).

`A` is the conjunction of the types of the three listed declarations, universes instantiated at
`0` (`B` lives in `Type`): `EpGroupoid.proposition_7_2` (`∃ V, (∀ k, IsOpen (V k) ∧ z ∈ V k) ∧
(𝓝 z).HasAntitoneBasis V`), `EpGroupoid.proposition_7_2_of_hasAntitoneBasis` (the images
`π(O_k)` of an antitone basis at `x` are an antitone basis at `π(x)`) and the instance
`EpGroupoid.proposition_7_2_firstCountableTopology` (a `Prop`-valued class).  The project's
topology on `X.OrbitSpace` is Mathlib's quotient instance, definitionally `B`'s `orbitTop X`.

* `A → B`: from `proposition_7_2`: `HasAntitoneBasis` gives `V (k+1) ⊆ V k` (antitone) and, for
  an open `N ∋ z`, some `V k ⊆ N` (basis).
* `B → A`: `proposition_7_2` from `B` (an open `V k ∋ z` is a neighbourhood; a neighbourhood
  contains an open `N ∋ z`, hence some `V k`; antitone from the step condition), and first
  countability from it.  `proposition_7_2_of_hasAntitoneBasis` is not a consequence of `B` (it is
  about a *given* basis at a representative, and needs `map π (𝓝 x) = 𝓝 (π x)`, i.e. the openness
  of `π`); it is re-proved from Proposition 7.1 (`proposition_7_1_map_nhds`, not an item theorem
  here) and `HasAntitoneBasis.map`, without `B`. -/

namespace RoundTrip.V7_12
open Polyfold Topology Filter Set

/-- The project's statement (universes at `0`). -/
def A : Prop :=
  (type_of% @Polyfold.EpGroupoid.proposition_7_2.{0}) ∧
  (type_of% @Polyfold.EpGroupoid.proposition_7_2_of_hasAntitoneBasis.{0}) ∧
  (type_of% @Polyfold.EpGroupoid.proposition_7_2_firstCountableTopology.{0})

theorem A_holds : A :=
  ⟨@Polyfold.EpGroupoid.proposition_7_2.{0},
    @Polyfold.EpGroupoid.proposition_7_2_of_hasAntitoneBasis.{0},
    @Polyfold.EpGroupoid.proposition_7_2_firstCountableTopology.{0}⟩

/-! ### `A → B` -/

theorem A_to_B : A → B := by
  intro hA Obj Mor _ _ _ _ _ _ X z
  obtain ⟨V, hV, hB⟩ := hA.1 X z
  refine ⟨V, hV, fun k => hB.antitone (Nat.le_succ k), fun N hN hzN => ?_⟩
  exact hB.toHasBasis.mem_iff.1 (hN.mem_nhds hzN) |>.imp fun _ h => h.2

/-! ### `B → A` -/

theorem B_to_A : B → A := by
  intro hB
  have h72 : ∀ (Obj Mor : Type) [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
      [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] (X : EpGroupoid Obj Mor)
      (z : X.OrbitSpace), ∃ V : ℕ → Set X.OrbitSpace,
        (∀ k, IsOpen (V k) ∧ z ∈ V k) ∧ (𝓝 z).HasAntitoneBasis V := by
    intro Obj Mor _ _ _ _ _ _ X z
    obtain ⟨V, hV, hstep, hbasis⟩ := hB Obj Mor X z
    refine ⟨V, hV, ⟨⟨fun s => ⟨fun hs => ?_, fun ⟨k, _, hk⟩ =>
      Filter.mem_of_superset ((hV k).1.mem_nhds (hV k).2) hk⟩⟩, antitone_nat_of_succ_le hstep⟩⟩
    obtain ⟨N, hNs, hNo, hzN⟩ := mem_nhds_iff.1 hs
    obtain ⟨k, hk⟩ := hbasis N hNo hzN
    exact ⟨k, trivial, hk.trans hNs⟩
  refine ⟨fun {Obj Mor} _ _ _ _ _ _ X z => h72 Obj Mor X z, ?_, ?_⟩
  · intro Obj Mor _ _ _ _ _ _ X x O hO
    rw [← X.proposition_7_1_map_nhds x]
    exact hO.map X.π
  · intro Obj Mor _ _ _ _ _ _ X
    exact ⟨fun z => by
      obtain ⟨V, -, hV⟩ := h72 Obj Mor X z
      exact hV.toHasBasis.isCountablyGenerated⟩

#rt_check RoundTrip.V7_12.A_to_B [Polyfold.EpGroupoid.proposition_7_2,
  Polyfold.EpGroupoid.proposition_7_2_of_hasAntitoneBasis,
  Polyfold.EpGroupoid.proposition_7_2_firstCountableTopology]
#rt_check RoundTrip.V7_12.B_to_A [Polyfold.EpGroupoid.proposition_7_2,
  Polyfold.EpGroupoid.proposition_7_2_of_hasAntitoneBasis,
  Polyfold.EpGroupoid.proposition_7_2_firstCountableTopology]
#rt_overlap RoundTrip.V7_12.B_to_A [Polyfold.EpGroupoid.proposition_7_2,
  Polyfold.EpGroupoid.proposition_7_2_of_hasAntitoneBasis,
  Polyfold.EpGroupoid.proposition_7_2_firstCountableTopology]

end RoundTrip.V7_12
