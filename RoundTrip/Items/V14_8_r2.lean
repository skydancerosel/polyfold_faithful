import RoundTrip.Items.V14_8

set_option maxSynthPendingDepth 3

/-! Round trip for V14_8_r2 (refresh of V14_8: 2021 Theorem 14.1.9, p. 646, the ∂-extension
theorem).  `B` is the existing blind statement `RoundTrip.V14_8.B`, which assumes partitions of
unity in the ep-groupoid sense (Definition 7.5.5) where `theorem_14_1_9` assumes them for the object
M-polyfold, as the text does ("X, viewed as an M-polyfold, admits sc-smooth partitions of unity").

The project now proves that ep-groupoid partitions of unity give M-polyfold partitions of unity of
the object space (`EpGroupoid.admitsScPartitionsOfUnity_of_hasScPartitionsOfUnity`), so

* `A` is the first pass's `A` together with that lemma;
* `A_to_B`: proved (the lemma turns `B`'s hypothesis into `theorem_14_1_9`'s);
* `main_to_B` (`theorem_14_1_9` and the lemma) and `B_to_main` (from the first pass): proved, so
  the main conjunct and `B` are equivalent;
* `B → A` is not claimed: `A` lists proof steps and examples that `B` does not state. -/

namespace RoundTrip.V14_8_r2
open Polyfold

/-- The first pass's `A` and the lemma on partitions of unity (universe `0`). -/
def A : Prop :=
  RoundTrip.V14_8.A ∧
    (type_of% @Polyfold.EpGroupoid.admitsScPartitionsOfUnity_of_hasScPartitionsOfUnity.{0})

theorem A_holds : A :=
  ⟨RoundTrip.V14_8.A_holds,
    @Polyfold.EpGroupoid.admitsScPartitionsOfUnity_of_hasScPartitionsOfUnity.{0}⟩

/-- The main conjunct and the lemma. -/
def Amain : Prop :=
  (type_of% @Polyfold.SBLocalization.theorem_14_1_9.{0}) ∧
    (type_of% @Polyfold.EpGroupoid.admitsScPartitionsOfUnity_of_hasScPartitionsOfUnity.{0})

theorem main_to_B : Amain → RoundTrip.V14_8.B := by
  rintro ⟨hA, hL⟩ Aa hX hpara hep Λ hΛ N hN U hUo hUs hsub f hf hf0 hfinv hts hlt
  exact hA hX hpara (hL hep) Λ hΛ N hN U hUo hUs hsub f hf hf0 (fun φ => (hfinv φ).symm) hts hlt

theorem B_to_main_14_1_9 : RoundTrip.V14_8.B → type_of% @Polyfold.SBLocalization.theorem_14_1_9.{0} :=
  RoundTrip.V14_8.B_to_main

theorem A_to_B : A → RoundTrip.V14_8.B := fun h => main_to_B ⟨h.1.1, h.2⟩

#rt_check RoundTrip.V14_8_r2.A_to_B [Polyfold.SBLocalization.theorem_14_1_9,
  Polyfold.EpGroupoid.admitsScPartitionsOfUnity_of_hasScPartitionsOfUnity]
#rt_check RoundTrip.V14_8_r2.main_to_B [Polyfold.SBLocalization.theorem_14_1_9,
  Polyfold.EpGroupoid.admitsScPartitionsOfUnity_of_hasScPartitionsOfUnity]

end RoundTrip.V14_8_r2
