import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V2_26

/-! Round trip for V2_26 (Definition 2.22: the degeneracy index `d_X`).

`A` is the conjunction of the types of the listed theorems `Polyfold.MPolyfold.degIndex_le`,
`Polyfold.MPolyfold.exists_isChart_degIndex_eq` and `Polyfold.MPolyfold.eventually_chartDegIndex_le`,
instantiated at universe `0` (B lives in `Type`).  `chartDegIndex` and `degIndex` are definitions
(vocabulary), compared with B's notions:
* `chartDegIndex φ x` is `degIndex E C (φ x)` by definition (B (a), `rfl`);
* `P.degIndex x` is the `sInf` of exactly B's set `chartIndicesB P x` (the same charts
  `P.IsChart φ` around `x`, the same `d_C(φ(x))`); B (b) says it is the least element, i.e. that
  the `sInf` is attained, which is `degIndex_le` (lower bound) + `exists_isChart_degIndex_eq`
  (membership).

`eventually_chartDegIndex_le` (upper semicontinuity of `y ↦ d_C(φ(y))` on `dom φ`, the chart-level
ingredient of Lemma 2.23) is not part of Definition 2.22 nor of B; in `B → A` it is proved
directly from the Chapter 1 lemmas `eventually_degIndexWith_le` and `degIndex_eq`. -/

namespace RoundTrip.V2_26
open Polyfold Set Filter Topology

/-- The project's statement (universe `0`). -/
def A : Prop :=
  (type_of% @Polyfold.MPolyfold.degIndex_le.{0}) ∧
    (type_of% @Polyfold.MPolyfold.exists_isChart_degIndex_eq.{0}) ∧
    (type_of% @Polyfold.MPolyfold.eventually_chartDegIndex_le.{0})

theorem A_holds : A :=
  ⟨@Polyfold.MPolyfold.degIndex_le.{0}, @Polyfold.MPolyfold.exists_isChart_degIndex_eq.{0},
    @Polyfold.MPolyfold.eventually_chartDegIndex_le.{0}⟩

section Glue

/-- Upper semicontinuity of `d(·, φ)` on the source of a chart, proved directly from the Chapter 1
facts (`d_C` is computed by any presentation, and `degIndexWith T` is upper semicontinuous). -/
theorem eventually_chartDegIndex_le' {X : Type} [TopologicalSpace X] (φ : MChart X) {x : X}
    (hx : x ∈ φ.source) :
    ∀ᶠ y in 𝓝 x, MPolyfold.chartDegIndex φ y ≤ MPolyfold.chartDegIndex φ x := by
  obtain ⟨n, W, T, hT⟩ := φ.model.isPartialQuadrant
  have hcont : ContinuousAt φ x := φ.continuousOn_toFun.continuousAt (φ.isOpen_source.mem_nhds hx)
  filter_upwards [φ.isOpen_source.mem_nhds hx, hcont.eventually (eventually_degIndexWith_le T (φ x))]
    with y hy hle
  rw [MPolyfold.chartDegIndex, MPolyfold.chartDegIndex, degIndex_eq T hT (φ.apply_mem_C hy),
    degIndex_eq T hT (φ.apply_mem_C hx)]
  exact hle

/-- B's set `{d(x, φ)}` is the set whose `sInf` the project takes. -/
theorem chartIndicesB_eq {X : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X]
    (P : MPolyfold X) (x : X) :
    chartIndicesB P x =
      {d | ∃ φ : MChart X, P.IsChart φ ∧ x ∈ φ.source ∧ MPolyfold.chartDegIndex φ x = d} := rfl

end Glue

/-- `A → B`: (a) is definitional; (b) is A's lower bound and attained minimum. -/
theorem A_to_B : A → B := by
  rintro ⟨hle, hex, -⟩ X _ _ _ P x
  refine ⟨fun φ _ => rfl, ?_, ?_⟩
  · obtain ⟨φ, hφ, hx, hd⟩ := hex P x
    exact ⟨φ, hφ, hx, hd.symm⟩
  · rintro _ ⟨φ, hφ, hx, rfl⟩
    exact hle P hφ hx

/-- `B → A`: the lower bound and the attained minimum are B (b); upper semicontinuity of the chart
index is proved directly (`eventually_chartDegIndex_le'`). -/
theorem B_to_A : B → A := by
  intro hB
  refine ⟨?_, ?_, by intro X _ φ x hx; exact eventually_chartDegIndex_le' φ hx⟩
  · intro X _ _ _ P φ hφ x hx
    exact (hB X P x).2.2 ⟨φ, hφ, hx, rfl⟩
  · intro X _ _ _ P x
    obtain ⟨φ, hφ, hx, hd⟩ := (hB X P x).2.1
    exact ⟨φ, hφ, hx, hd.symm⟩

#rt_check RoundTrip.V2_26.A_to_B [Polyfold.MPolyfold.degIndex_le,
  Polyfold.MPolyfold.exists_isChart_degIndex_eq, Polyfold.MPolyfold.eventually_chartDegIndex_le]
#rt_check RoundTrip.V2_26.B_to_A [Polyfold.MPolyfold.degIndex_le,
  Polyfold.MPolyfold.exists_isChart_degIndex_eq, Polyfold.MPolyfold.eventually_chartDegIndex_le]
#rt_overlap RoundTrip.V2_26.B_to_A [Polyfold.MPolyfold.degIndex_le,
  Polyfold.MPolyfold.exists_isChart_degIndex_eq, Polyfold.MPolyfold.eventually_chartDegIndex_le]

end RoundTrip.V2_26
