import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V17_112

set_option maxSynthPendingDepth 3

namespace RoundTrip.V17_112
open Polyfold
open Polyfold.GCT.PolyfoldConstruction

def A : Prop :=
  (type_of% @Polyfold.GCT.PolyfoldConstruction.OrientedSubcategory.theorem_17_6_6.{0}) ∧
  (type_of% @Polyfold.GCT.PolyfoldConstruction.OrientedSubcategory.theorem_17_6_6_dim1.{0}) ∧
  (type_of% @Polyfold.GCT.PolyfoldConstruction.OrientedSubcategory.theorem_17_6_6_book.{0}) ∧
  (type_of% @Polyfold.GCT.PolyfoldConstruction.OrientedSubcategory.theorem_17_6_6_dim1_book.{0})

theorem A_holds : A :=
  ⟨@Polyfold.GCT.PolyfoldConstruction.OrientedSubcategory.theorem_17_6_6.{0},
    @Polyfold.GCT.PolyfoldConstruction.OrientedSubcategory.theorem_17_6_6_dim1.{0},
    @Polyfold.GCT.PolyfoldConstruction.OrientedSubcategory.theorem_17_6_6_book.{0},
    @Polyfold.GCT.PolyfoldConstruction.OrientedSubcategory.theorem_17_6_6_dim1_book.{0}⟩

theorem A_to_B : A → B := by
  rintro ⟨h1, h2, -, -⟩ C S A hc
  exact ⟨fun m hm c c' ht ht' ω => h1 A c c' hm hc ht ht' ω,
    fun c c' ht ht' ω => h2 A c c' hc ht ht' ω⟩

theorem B_to_A : B → A := by
  intro hB
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro C S m A c c' hm hc ht ht' ω
    exact (hB C S A hc).1 m hm c c' ht ht' ω
  · intro C S A c c' hc ht ht' ω
    exact (hB C S A hc).2 c c' ht ht' ω
  · intro C S m A c c' hm hc ht ω
    exact (hB C S A hc).1 m hm c c' ht _ ω
  · intro C S A c c' hc ht ω
    exact (hB C S A hc).2 c c' ht _ ω

/-- Main conjunct: `theorem_17_6_6` together with `theorem_17_6_6_dim1` (the two cases). -/
theorem main_to_B :
    (type_of% @Polyfold.GCT.PolyfoldConstruction.OrientedSubcategory.theorem_17_6_6.{0}) ∧
    (type_of% @Polyfold.GCT.PolyfoldConstruction.OrientedSubcategory.theorem_17_6_6_dim1.{0}) →
    B := by
  rintro ⟨h1, h2⟩ C S A hc
  exact ⟨fun m hm c c' ht ht' ω => h1 A c c' hm hc ht ht' ω,
    fun c c' ht ht' ω => h2 A c c' hc ht ht' ω⟩

theorem B_to_main : B →
    (type_of% @Polyfold.GCT.PolyfoldConstruction.OrientedSubcategory.theorem_17_6_6.{0}) ∧
    (type_of% @Polyfold.GCT.PolyfoldConstruction.OrientedSubcategory.theorem_17_6_6_dim1.{0}) :=
  fun hB => ⟨(B_to_A hB).1, (B_to_A hB).2.1⟩

#rt_check RoundTrip.V17_112.A_to_B [Polyfold.GCT.PolyfoldConstruction.OrientedSubcategory.theorem_17_6_6, Polyfold.GCT.PolyfoldConstruction.OrientedSubcategory.theorem_17_6_6_dim1, Polyfold.GCT.PolyfoldConstruction.OrientedSubcategory.theorem_17_6_6_book, Polyfold.GCT.PolyfoldConstruction.OrientedSubcategory.theorem_17_6_6_dim1_book]
#rt_check RoundTrip.V17_112.B_to_A [Polyfold.GCT.PolyfoldConstruction.OrientedSubcategory.theorem_17_6_6, Polyfold.GCT.PolyfoldConstruction.OrientedSubcategory.theorem_17_6_6_dim1, Polyfold.GCT.PolyfoldConstruction.OrientedSubcategory.theorem_17_6_6_book, Polyfold.GCT.PolyfoldConstruction.OrientedSubcategory.theorem_17_6_6_dim1_book]
#rt_check RoundTrip.V17_112.main_to_B [Polyfold.GCT.PolyfoldConstruction.OrientedSubcategory.theorem_17_6_6, Polyfold.GCT.PolyfoldConstruction.OrientedSubcategory.theorem_17_6_6_dim1, Polyfold.GCT.PolyfoldConstruction.OrientedSubcategory.theorem_17_6_6_book, Polyfold.GCT.PolyfoldConstruction.OrientedSubcategory.theorem_17_6_6_dim1_book]
#rt_check RoundTrip.V17_112.B_to_main [Polyfold.GCT.PolyfoldConstruction.OrientedSubcategory.theorem_17_6_6, Polyfold.GCT.PolyfoldConstruction.OrientedSubcategory.theorem_17_6_6_dim1, Polyfold.GCT.PolyfoldConstruction.OrientedSubcategory.theorem_17_6_6_book, Polyfold.GCT.PolyfoldConstruction.OrientedSubcategory.theorem_17_6_6_dim1_book]
#rt_overlap RoundTrip.V17_112.B_to_A [Polyfold.GCT.PolyfoldConstruction.OrientedSubcategory.theorem_17_6_6, Polyfold.GCT.PolyfoldConstruction.OrientedSubcategory.theorem_17_6_6_dim1, Polyfold.GCT.PolyfoldConstruction.OrientedSubcategory.theorem_17_6_6_book, Polyfold.GCT.PolyfoldConstruction.OrientedSubcategory.theorem_17_6_6_dim1_book]

end RoundTrip.V17_112
