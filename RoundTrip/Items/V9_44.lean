import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V9_44

/-! Round trip for V9_44 (Lemma 9.4.6, 2021 p. 431; 2017: Lemma 9.14): `K(i, i')^{ne}` has
measure zero.

`A` is the conjunction of the types of the five listed theorems, universes instantiated at `0`
(`B` lives in `Type`): `span_unitDirections`, `exists_pos_measure_cone_lt`,
`addHaar_setOf_span_tangentConeAt_ne_top`, `isMeasureZero_setOf_relTangent_ne_top` and
`lemma_9_4_6`.  `unitDirections` is a definition (vocabulary).

* `A → B`: `B`'s set `j⁻¹(K ∖ j(K'^e))`, `K' = j⁻¹(K)`, lies in `K' ∖ K'^e`, so it is
  `lemma_9_4_6` (the fifth conjunct of `A`) for the subset `K' = j⁻¹(Mᵢ ∩ Mᵢ')` of the
  `n`-manifold with corners `Nᵢ` (model `modelWithCornersEuclideanQuadrant n`).
* `B → A`: not proved.  `A`'s `lemma_9_4_6` and `isMeasureZero_setOf_relTangent_ne_top` are for
  every subset of every finite-dimensional manifold with corners (any model `I : H → E`), and
  `A` contains three Euclidean lemmas (`span_unitDirections`, the cone estimate, the density
  statement for every `A ⊆ E` and every Haar measure); `B` speaks only of the sets
  `j⁻¹(Mᵢ ∩ Mᵢ')` (closed in `Nᵢ`) of sheets modelled on `[0, ∞)ⁿ`.
-/

namespace RoundTrip.V9_44
open Polyfold

/-- The project's statement (universes at `0`). -/
def A : Prop :=
  (type_of% @Polyfold.span_unitDirections.{0}) ∧
  (type_of% @Polyfold.exists_pos_measure_cone_lt.{0}) ∧
  (type_of% @Polyfold.addHaar_setOf_span_tangentConeAt_ne_top.{0}) ∧
  (type_of% @Polyfold.isMeasureZero_setOf_relTangent_ne_top.{0, 0, 0}) ∧
  (type_of% @Polyfold.lemma_9_4_6.{0, 0, 0})

theorem A_holds : A :=
  ⟨@Polyfold.span_unitDirections.{0}, @Polyfold.exists_pos_measure_cone_lt.{0},
    @Polyfold.addHaar_setOf_span_tangentConeAt_ne_top.{0},
    @Polyfold.isMeasureZero_setOf_relTangent_ne_top.{0, 0, 0}, @Polyfold.lemma_9_4_6.{0, 0, 0}⟩

theorem A_to_B : A → B := by
  intro hA n F _ _ _ x L i i'
  set S := L.S i
  have h := hA.2.2.2.2 (I := Q n) (M := S.N) (S.j ⁻¹' L.K i i')
  refine IsMeasureZero.mono h ?_
  rintro w ⟨hwK, hwe⟩
  refine ⟨hwK, fun hess => hwe ⟨w, hess, rfl⟩⟩

#rt_check RoundTrip.V9_44.A_to_B [Polyfold.span_unitDirections,
  Polyfold.exists_pos_measure_cone_lt, Polyfold.addHaar_setOf_span_tangentConeAt_ne_top,
  Polyfold.isMeasureZero_setOf_relTangent_ne_top, Polyfold.lemma_9_4_6]

end RoundTrip.V9_44
