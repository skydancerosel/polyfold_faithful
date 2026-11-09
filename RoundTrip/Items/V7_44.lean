import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V7_44

/-!
Round trip for V7_44 (Lemma 7.5: countable neighbourhood bases of `|X|`).

`A` is the type of `Polyfold.EpGroupoid.lemma_7_3_3` at universe `0`: for every ep-groupoid
`X : EpGroupoid Obj Mor` (`Obj Mor : Type`) and `z : X.OrbitSpace` there are `V : ℕ → Set |X|`,
all open and containing `z`, with `(𝓝 z).HasAntitoneBasis V`.  `B`: open `V k`, `z ∈ V (k+1) ⊆
V k`, and `(𝓝 z).HasBasis (fun _ ↦ True) V`.  Mathlib's `HasAntitoneBasis` is `HasBasis (fun _ ↦
True)` plus `Antitone`; on `ℕ` antitone is `V (k+1) ⊆ V k` (`antitone_nat_of_succ_le`); and
`z ∈ V 0` follows from `z ∈ V 1 ⊆ V 0`.  So the two are the same statement.
-/

namespace RoundTrip.V7_44
open Polyfold

/-- The project's Lemma 7.5, universes at `0`. -/
def A : Prop := type_of% @Polyfold.EpGroupoid.lemma_7_3_3.{0}

theorem A_holds : A := @EpGroupoid.lemma_7_3_3

theorem A_to_B : A → B := by
  intro hA Obj Mor _ _ _ _ _ _ X z
  obtain ⟨V, hV, hb⟩ := hA X z
  exact ⟨V, fun k => (hV k).1, fun k => ⟨(hV (k + 1)).2, hb.antitone (Nat.le_succ k)⟩,
    hb.toHasBasis⟩

theorem B_to_A : B → A := by
  intro hB Obj Mor _ _ _ _ _ _ X z
  obtain ⟨V, hVo, hVs, hb⟩ := hB Obj Mor X z
  refine ⟨V, fun k => ⟨hVo k, ?_⟩, ⟨hb, antitone_nat_of_succ_le fun k => (hVs k).2⟩⟩
  cases k with
  | zero => exact (hVs 0).2 (hVs 0).1
  | succ k => exact (hVs k).1

#rt_check RoundTrip.V7_44.A_to_B [Polyfold.EpGroupoid.lemma_7_3_3]
#rt_check RoundTrip.V7_44.B_to_A [Polyfold.EpGroupoid.lemma_7_3_3]
#rt_overlap RoundTrip.V7_44.B_to_A [Polyfold.EpGroupoid.lemma_7_3_3]

end RoundTrip.V7_44
