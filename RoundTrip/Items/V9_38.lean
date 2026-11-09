import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V9_38

/-! Round trip for V9_38 (Definition 9.3.10, 2021 p. 428; 2017: Definition 9.11: the oriented
boundary `T̂_{∂Θ}`, formula (9.12)).

The item lists only the definition `EpGroupoid.boundaryLift` (`T̂_{∂Θ}(y)` is the image under the
boundary operation `bd` of the degree-`1` part of `T̂_Θ(y)`), so `A = True`; the content of the
audit is the comparison of this definition with the text's two defining clauses, which is `B`
itself, proved outright here (`B_holds`, universes at `0`).

* "`= 0` off `supp(Θ)`": an orientation `T` vanishes at smooth points off `supp Θ`
  (`IsOrientation.eq_zero_of_not_mem`: its image `TΘ(y)` is `0` there and `Gr̂ → Gr` reflects
  `0`), so its degree-`1` part and the image under `bd` are `0`.
* (9.12) on `U(x)`: with `T y = ∑ σᵢ T_y(Mᵢ, oᵢ)` and tame sheets, the degree-`1` part is
  `∑_{d_{Mᵢ}(y) = 1} σᵢ T_y(Mᵢ, oᵢ)` (`degreePart_orientedSum`), and `mapDomain bd` turns each
  `single (T_y(Mᵢ, oᵢ)) σᵢ` into `single (bd T_y(Mᵢ, oᵢ)) σᵢ`.  B's filter quantifies over a proof
  `h` of `IsSubMPolyfold Mᵢ`; by proof irrelevance it is the project's filter.
* The proof does not use `proposition_9_3_9` (the project's statement of the same two clauses,
  item V9_37's theorem); `B`'s hypotheses "branched", "tame", `x ∈ supp Θ` are not needed.
-/

namespace RoundTrip.V9_38
open Polyfold

/-- Only a definition is listed: `A = True`. -/
def A : Prop := True

theorem A_holds : A := trivial

/-- **`B` holds outright**: the project's `boundaryLift` satisfies the two defining clauses of
Definition 9.3.10 for every boundary operation `bd`. -/
theorem B_holds : B := by
  intro Obj Mor _ _ _ _ _ _ X Θ T bd _ _ hT
  refine ⟨fun y hy hys => ?_, fun x _ Bs ht hB y hy hys => ?_⟩
  · rw [EpGroupoid.boundaryLift, hT.eq_zero_of_not_mem hy hys, EpGroupoid.degreePart,
      Finsupp.filter_zero, Finsupp.mapDomain_zero]
  · classical
    rw [EpGroupoid.boundaryLift, hB y hy hys, EpGroupoid.degreePart_orientedSum Bs ht,
      Finsupp.mapDomain_finsetSum, boundarySumB]
    refine Finset.sum_congr (Finset.filter_congr fun i _ => ?_) fun i _ => Finsupp.mapDomain_single
    exact ⟨fun ⟨hyi, hd⟩ => ⟨_, hyi, hd⟩, fun ⟨_, hyi, hd⟩ => ⟨hyi, hd⟩⟩

theorem A_to_B : A → B := fun _ => B_holds

theorem B_to_A : B → A := fun _ => trivial

#rt_check RoundTrip.V9_38.A_to_B []
#rt_check RoundTrip.V9_38.B_to_A []
#rt_overlap RoundTrip.V9_38.B_to_A []
-- the proof is independent of the project's own statement of the two clauses
#rt_check RoundTrip.V9_38.B_holds [Polyfold.EpGroupoid.proposition_9_3_9]
#rt_overlap RoundTrip.V9_38.B_holds [Polyfold.EpGroupoid.proposition_9_3_9]
#print axioms RoundTrip.V9_38.B_holds

end RoundTrip.V9_38
