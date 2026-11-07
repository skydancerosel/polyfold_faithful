import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V7_54

/-!
Round trip for V7_54 (Proposition 7.12: paracompactness under lifts).

`A` is the conjunction of the types of the eight listed theorems (universes at `0`):
`continuous_orbitIncl`, `orbitIncl_injective`, `range_orbitIncl` (the natural map `|X¹| → |X|`),
`NaturalRep.isOpenEmbedding_liftOrbitQuotientMap` (`G_x\U(x)₁ → |X¹|` is an open embedding, for
EVERY ep-groupoid and natural representation), `NaturalRep.metrizableSpace_preimage_orbitIncl`
(the preimage of `|U(x)|` in `|X¹|` is metrizable, again unconditionally),
`metrizableSpace_liftOne_orbitSpace` (`|X|` paracompact ⇒ `|X¹|` metrizable), Part I's
`metrizableSpace_of_pullback` (Smirnov's theorem pulled back along a continuous map) and
`proposition_7_12` (`|X|` paracompact ⇒ `|X¹|` paracompact, for the project's `liftOne`).

* `A → B` (proved): `Y = X.liftOne`; `IsLiftB` holds by `rfl` (the atlases of `liftOne` are those
  of `X.PObj.shift`, `X.PMor.shift`, the structure maps are the level-`1` restrictions) and
  `liftOne_comp_val`; paracompactness of `|X¹|` is `proposition_7_12` from the hypothesis.
* `B → A` (not proved).  What `B` gives: `proposition_7_12` for the project's `liftOne`
  (`B_gives_proposition_7_12`: B's `Y` has the same `s, t`, hence the same orbit setoid as
  `liftOne`, so the same orbit space) and then `metrizableSpace_liftOne_orbitSpace`
  (`B_gives_metrizable`, with the unbanned Theorem 7.2, `theorem_7_2_metrizable`).  What `B` does
  not give: the two unconditional local statements about `|X¹|` over `|U(x)|`
  (`isOpenEmbedding_liftOrbitQuotientMap`, `metrizableSpace_preimage_orbitIncl`), which hold for
  every ep-groupoid with no paracompactness hypothesis, and the general topology lemma
  `metrizableSpace_of_pullback`; these are the project's proof route (Smirnov pulled back along
  `|X¹| → |X|`), not content of the text's statement.  Re-proving
  `metrizableSpace_preimage_orbitIncl` needs the level-`1` Lemma 7.4 (metrizability of a quotient
  by a finite group of homeomorphisms; the project's version is private), i.e. redoing the
  project's proof, so we stop there.

**The banned lists below omit `Polyfold.metrizableSpace_of_pullback`.**  It cannot be avoided by
any statement of this item: the instance `MPolyfold.paracompactSpace_level` (Theorem 2.16,
`ParacompactSpace (P.Level m)`, needed to form the M-polyfold `X¹` and to write
`EpGroupoid (X.PObj.Level 1) (X.PMor.Level 1)` at all) is proved from `metrizableSpace_level`,
which is proved with `metrizableSpace_of_pullback`; so already `#rt_check RoundTrip.V7_54.B
[Polyfold.metrizableSpace_of_pullback]` fails (checked).  No proof below cites it.
-/

namespace RoundTrip.V7_54
open Polyfold Set

/-- The listed theorems (universes at `0`). -/
def A : Prop :=
  type_of% @Polyfold.EpGroupoid.continuous_orbitIncl.{0} ∧
  type_of% @Polyfold.EpGroupoid.orbitIncl_injective.{0} ∧
  type_of% @Polyfold.EpGroupoid.range_orbitIncl.{0} ∧
  type_of% @Polyfold.EpGroupoid.NaturalRep.isOpenEmbedding_liftOrbitQuotientMap.{0} ∧
  type_of% @Polyfold.EpGroupoid.NaturalRep.metrizableSpace_preimage_orbitIncl.{0} ∧
  type_of% @Polyfold.EpGroupoid.metrizableSpace_liftOne_orbitSpace.{0} ∧
  type_of% @Polyfold.metrizableSpace_of_pullback.{0, 0} ∧
  type_of% @Polyfold.EpGroupoid.proposition_7_12.{0}

theorem A_holds : A :=
  ⟨@Polyfold.EpGroupoid.continuous_orbitIncl.{0}, @Polyfold.EpGroupoid.orbitIncl_injective.{0},
    @Polyfold.EpGroupoid.range_orbitIncl.{0},
    @Polyfold.EpGroupoid.NaturalRep.isOpenEmbedding_liftOrbitQuotientMap.{0},
    @Polyfold.EpGroupoid.NaturalRep.metrizableSpace_preimage_orbitIncl.{0},
    @Polyfold.EpGroupoid.metrizableSpace_liftOne_orbitSpace.{0},
    @Polyfold.metrizableSpace_of_pullback.{0, 0}, @Polyfold.EpGroupoid.proposition_7_12.{0}⟩

theorem A_to_B : A → B := by
  rintro ⟨-, -, -, -, -, -, -, h8⟩ Obj Mor _ _ _ _ _ _ X hX
  exact ⟨X.liftOne, ⟨MAtlas.Equiv.refl _, MAtlas.Equiv.refl _, fun _ => rfl, fun _ => rfl,
    fun _ => rfl, fun _ => rfl, fun _ _ h => X.liftOne_comp_val h⟩, h8 X hX⟩

/-! ### What `B` does give (partial `B → A`) -/

/-- `B` gives `proposition_7_12` for the project's `liftOne`: `B`'s `Y` has the same `s, t` as
`liftOne`, hence the same orbit setoid and orbit space. -/
theorem B_gives_proposition_7_12 (hB : B) :
    type_of% @Polyfold.EpGroupoid.proposition_7_12.{0} := by
  intro Obj Mor _ _ _ _ _ _ X hX
  obtain ⟨Y, ⟨-, -, hs, ht, -, -, -⟩, hY⟩ := hB Obj Mor X hX
  have hs' : Y.src = X.liftOne.src := funext fun φ => MPolyfold.level_ext (hs φ)
  have ht' : Y.tgt = X.liftOne.tgt := funext fun φ => MPolyfold.level_ext (ht φ)
  have e : Y.toGroupoidStr.orbitSetoid = X.liftOne.toGroupoidStr.orbitSetoid := by
    ext a b
    change Y.Isomorphic a b ↔ X.liftOne.Isomorphic a b
    unfold GroupoidStr.Isomorphic
    rw [hs', ht']
  unfold EpGroupoid.HasParacompactOrbitSpace GroupoidStr.OrbitSpace at hY ⊢
  rw [e] at hY
  exact hY

/-- `B` gives `metrizableSpace_liftOne_orbitSpace`, with the unbanned Theorem 7.2. -/
theorem B_gives_metrizable (hB : B) :
    type_of% @Polyfold.EpGroupoid.metrizableSpace_liftOne_orbitSpace.{0} := by
  intro Obj Mor _ _ _ _ _ _ X hX
  exact X.liftOne.theorem_7_2_metrizable (B_gives_proposition_7_12 hB X hX)

#rt_check RoundTrip.V7_54.A_to_B [Polyfold.EpGroupoid.continuous_orbitIncl,
  Polyfold.EpGroupoid.orbitIncl_injective, Polyfold.EpGroupoid.range_orbitIncl,
  Polyfold.EpGroupoid.NaturalRep.isOpenEmbedding_liftOrbitQuotientMap,
  Polyfold.EpGroupoid.NaturalRep.metrizableSpace_preimage_orbitIncl,
  Polyfold.EpGroupoid.metrizableSpace_liftOne_orbitSpace, Polyfold.EpGroupoid.proposition_7_12]
#rt_check RoundTrip.V7_54.B_gives_proposition_7_12 [Polyfold.EpGroupoid.continuous_orbitIncl,
  Polyfold.EpGroupoid.orbitIncl_injective, Polyfold.EpGroupoid.range_orbitIncl,
  Polyfold.EpGroupoid.NaturalRep.isOpenEmbedding_liftOrbitQuotientMap,
  Polyfold.EpGroupoid.NaturalRep.metrizableSpace_preimage_orbitIncl,
  Polyfold.EpGroupoid.metrizableSpace_liftOne_orbitSpace, Polyfold.EpGroupoid.proposition_7_12]
#rt_check RoundTrip.V7_54.B_gives_metrizable [Polyfold.EpGroupoid.continuous_orbitIncl,
  Polyfold.EpGroupoid.orbitIncl_injective, Polyfold.EpGroupoid.range_orbitIncl,
  Polyfold.EpGroupoid.NaturalRep.isOpenEmbedding_liftOrbitQuotientMap,
  Polyfold.EpGroupoid.NaturalRep.metrizableSpace_preimage_orbitIncl,
  Polyfold.EpGroupoid.metrizableSpace_liftOne_orbitSpace, Polyfold.EpGroupoid.proposition_7_12]
#rt_overlap RoundTrip.V7_54.B_gives_metrizable [Polyfold.EpGroupoid.continuous_orbitIncl,
  Polyfold.EpGroupoid.orbitIncl_injective, Polyfold.EpGroupoid.range_orbitIncl,
  Polyfold.EpGroupoid.NaturalRep.isOpenEmbedding_liftOrbitQuotientMap,
  Polyfold.EpGroupoid.NaturalRep.metrizableSpace_preimage_orbitIncl,
  Polyfold.EpGroupoid.metrizableSpace_liftOne_orbitSpace, Polyfold.EpGroupoid.proposition_7_12]

end RoundTrip.V7_54
