import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V7_2

/-! Round trip for V7_2 (Definition 7.2: the isotropy group `G_x`).

The listed theorems are `GroupoidStr.Isotropy.val_mul`, `val_one`, `val_inv` (the other entries,
`Isotropy`, `isotropyEquivVertexGroup`, `isotropyEquivAut`, are definitions), so `A` is the
conjunction of their types, universes at `0`.

* `A → B`: the three operation conjuncts of `B` are `A`; closure of
  `G_x = {φ | s φ = x = t φ}` under `∘`, `1_x`, `ι`, injectivity of `val` (structure eta) and
  `range val = G_x` are glue from the groupoid axioms.
* `B → A`: the operation conjuncts of `B` are exactly `A`. -/

namespace RoundTrip.V7_2
open Polyfold

/-- The project's statement (universes at `0`). -/
def A : Prop :=
  (type_of% @Polyfold.GroupoidStr.Isotropy.val_mul.{0}) ∧
  (type_of% @Polyfold.GroupoidStr.Isotropy.val_one.{0}) ∧
  (type_of% @Polyfold.GroupoidStr.Isotropy.val_inv.{0})

theorem A_holds : A :=
  ⟨@Polyfold.GroupoidStr.Isotropy.val_mul.{0}, @Polyfold.GroupoidStr.Isotropy.val_one.{0},
    @Polyfold.GroupoidStr.Isotropy.val_inv.{0}⟩

theorem A_to_B : A → B := by
  intro hA Obj Mor G x
  refine ⟨?_, ⟨G.src_unit x, G.tgt_unit x⟩, ?_, ?_, ?_, fun g h => hA.1 g h, hA.2.1,
    fun g => hA.2.2 g⟩
  · rintro g ⟨hg1, hg2⟩ h ⟨hh1, hh2⟩
    have hc : G.src g = G.tgt h := hg1.trans hh2.symm
    exact ⟨(G.src_comp _ _ hc).trans hh1, (G.tgt_comp _ _ hc).trans hg2⟩
  · rintro g ⟨hg1, hg2⟩
    exact ⟨(G.src_inv g).trans hg2, (G.tgt_inv g).trans hg1⟩
  · rintro ⟨a, ha1, ha2⟩ ⟨b, hb1, hb2⟩ (h : a = b)
    subst h
    rfl
  · ext φ
    constructor
    · rintro ⟨g, rfl⟩
      exact ⟨g.src_val, g.tgt_val⟩
    · rintro ⟨h1, h2⟩
      exact ⟨⟨φ, h1, h2⟩, rfl⟩

theorem B_to_A : B → A := by
  intro hB
  refine ⟨fun {Obj Mor} {G} {x} g h => ?_, fun {Obj Mor} {G} {x} => ?_,
    fun {Obj Mor} {G} {x} g => ?_⟩
  · exact (hB Obj Mor G x).2.2.2.2.2.1 g h
  · exact (hB Obj Mor G x).2.2.2.2.2.2.1
  · exact (hB Obj Mor G x).2.2.2.2.2.2.2 g

#rt_check RoundTrip.V7_2.A_to_B [Polyfold.GroupoidStr.Isotropy.val_mul, Polyfold.GroupoidStr.Isotropy.val_one, Polyfold.GroupoidStr.Isotropy.val_inv]
#rt_check RoundTrip.V7_2.B_to_A [Polyfold.GroupoidStr.Isotropy.val_mul, Polyfold.GroupoidStr.Isotropy.val_one, Polyfold.GroupoidStr.Isotropy.val_inv]
#rt_overlap RoundTrip.V7_2.B_to_A [Polyfold.GroupoidStr.Isotropy.val_mul, Polyfold.GroupoidStr.Isotropy.val_one, Polyfold.GroupoidStr.Isotropy.val_inv]

end RoundTrip.V7_2
