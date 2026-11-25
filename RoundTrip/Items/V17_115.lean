import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V17_115

set_option maxSynthPendingDepth 3

/-! Round trip for V17_115 (2021 Theorem 17.6.9, p. 824: under (LUC) the effective boundary
integral `∮_{∂(Γ^*Θ̂)} [ω_Ψ]` does not depend on the covering family).

The item lists the definition `boundaryIntegralEffVia` (vocabulary) and four theorems; `A` is the
conjunction of their types, at universe `0` (`B` lives on `GCT.{0}`).  Conjuncts:
**`theorem_17_6_9`** (`[ω]` of degree `m ≥ 1`, `Θ̂` tame oriented of dimension `m + 1` on both
families) and **`theorem_17_6_9_dim1`** (`n = 1`) together form the main claim; `theorem_17_6_9_book`
and `theorem_17_6_9_dim1_book` are the same with the hypothesis on the first family only (the
second one is supplied by `isTameOrientedVia_of_family`).

* `A_to_B`: the two conjuncts of `B` are `theorem_17_6_9` and `theorem_17_6_9_dim1`.
* `B_to_A`: conversely, and the `_book` forms from `B` with `isTameOrientedVia_of_family` (not an
  item theorem) supplying the tameness on the second family.

**Harness note.**  `boundaryIntegralEffVia` (and `boundaryIntegralEffDim1Via`) are defined with the
proof `isLUC_model hL c` of (LUC) on the model, abstracted as their `_proof_N` fields; `isLUC_model`
is not an item theorem here, so plain `#rt_check` applies. -/

namespace RoundTrip.V17_115
open Polyfold
open Polyfold.GCT.PolyfoldConstruction Polyfold.GCT.PolyfoldConstruction.OrientedSubcategory

/-- The project's statement (universe `0`). -/
def A : Prop :=
  (type_of% @Polyfold.GCT.PolyfoldConstruction.OrientedSubcategory.theorem_17_6_9.{0}) ∧
  (type_of% @Polyfold.GCT.PolyfoldConstruction.OrientedSubcategory.theorem_17_6_9_dim1.{0}) ∧
  (type_of% @Polyfold.GCT.PolyfoldConstruction.OrientedSubcategory.theorem_17_6_9_book.{0}) ∧
  (type_of% @Polyfold.GCT.PolyfoldConstruction.OrientedSubcategory.theorem_17_6_9_dim1_book.{0})

theorem A_holds : A :=
  ⟨@Polyfold.GCT.PolyfoldConstruction.OrientedSubcategory.theorem_17_6_9.{0},
    @Polyfold.GCT.PolyfoldConstruction.OrientedSubcategory.theorem_17_6_9_dim1.{0},
    @Polyfold.GCT.PolyfoldConstruction.OrientedSubcategory.theorem_17_6_9_book.{0},
    @Polyfold.GCT.PolyfoldConstruction.OrientedSubcategory.theorem_17_6_9_dim1_book.{0}⟩

/-- The main claim: `theorem_17_6_9` together with its `n = 1` case. -/
def AMain : Prop :=
  (type_of% @Polyfold.GCT.PolyfoldConstruction.OrientedSubcategory.theorem_17_6_9.{0}) ∧
  (type_of% @Polyfold.GCT.PolyfoldConstruction.OrientedSubcategory.theorem_17_6_9_dim1.{0})

theorem main_A_to_B (h : AMain) : B := by
  intro C S hL A hc
  exact ⟨fun m hm c c' ht ht' ω => h.1 A hL c c' hm hc ht ht' ω,
    fun c c' ht ht' ω => h.2 A hL c c' hc ht ht' ω⟩

theorem main_B_to_A (hB : B) : AMain :=
  ⟨fun {C S _m} A hL c c' hm hc ht ht' ω => (hB C S hL A hc).1 _ hm c c' ht ht' ω,
    fun {C S} A hL c c' hc ht ht' ω => (hB C S hL A hc).2 c c' ht ht' ω⟩

theorem A_to_B : A → B := fun h => main_A_to_B ⟨h.1, h.2.1⟩

theorem B_to_A : B → A := fun hB =>
  ⟨(main_B_to_A hB).1, (main_B_to_A hB).2,
    fun {C S _m} A hL c c' hm hc ht ω => (hB C S hL A hc).1 _ hm c c' ht _ ω,
    fun {C S} A hL c c' hc ht ω => (hB C S hL A hc).2 c c' ht _ ω⟩

#rt_check RoundTrip.V17_115.main_A_to_B
  [Polyfold.GCT.PolyfoldConstruction.OrientedSubcategory.theorem_17_6_9,
   Polyfold.GCT.PolyfoldConstruction.OrientedSubcategory.theorem_17_6_9_dim1,
   Polyfold.GCT.PolyfoldConstruction.OrientedSubcategory.theorem_17_6_9_book,
   Polyfold.GCT.PolyfoldConstruction.OrientedSubcategory.theorem_17_6_9_dim1_book]
#rt_check RoundTrip.V17_115.main_B_to_A
  [Polyfold.GCT.PolyfoldConstruction.OrientedSubcategory.theorem_17_6_9,
   Polyfold.GCT.PolyfoldConstruction.OrientedSubcategory.theorem_17_6_9_dim1,
   Polyfold.GCT.PolyfoldConstruction.OrientedSubcategory.theorem_17_6_9_book,
   Polyfold.GCT.PolyfoldConstruction.OrientedSubcategory.theorem_17_6_9_dim1_book]
#rt_check RoundTrip.V17_115.A_to_B
  [Polyfold.GCT.PolyfoldConstruction.OrientedSubcategory.theorem_17_6_9,
   Polyfold.GCT.PolyfoldConstruction.OrientedSubcategory.theorem_17_6_9_dim1,
   Polyfold.GCT.PolyfoldConstruction.OrientedSubcategory.theorem_17_6_9_book,
   Polyfold.GCT.PolyfoldConstruction.OrientedSubcategory.theorem_17_6_9_dim1_book]
#rt_check RoundTrip.V17_115.B_to_A
  [Polyfold.GCT.PolyfoldConstruction.OrientedSubcategory.theorem_17_6_9,
   Polyfold.GCT.PolyfoldConstruction.OrientedSubcategory.theorem_17_6_9_dim1,
   Polyfold.GCT.PolyfoldConstruction.OrientedSubcategory.theorem_17_6_9_book,
   Polyfold.GCT.PolyfoldConstruction.OrientedSubcategory.theorem_17_6_9_dim1_book]
#rt_overlap RoundTrip.V17_115.B_to_A
  [Polyfold.GCT.PolyfoldConstruction.OrientedSubcategory.theorem_17_6_9,
   Polyfold.GCT.PolyfoldConstruction.OrientedSubcategory.theorem_17_6_9_dim1,
   Polyfold.GCT.PolyfoldConstruction.OrientedSubcategory.theorem_17_6_9_book,
   Polyfold.GCT.PolyfoldConstruction.OrientedSubcategory.theorem_17_6_9_dim1_book]

end RoundTrip.V17_115
