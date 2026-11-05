import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V2_27

/-! Round trip for V2_27 (Lemma 2.23: upper semicontinuity of `d_X`).

`A` is the conjunction of the types of the listed theorems `Polyfold.lemma_2_23`,
`Polyfold.eventually_degIndexWith_le`, `Polyfold.MPolyfold.isOpen_setOf_degIndex_lt` and
`Polyfold.MPolyfold.isClosed_setOf_le_degIndex`, at universe `0` (B lives in `Type`;
`eventually_degIndexWith_le` has no universe parameter).

* `lemma_2_23` (`∀ᶠ y in 𝓝 x, d_X(y) ≤ d_X(x)`) is B (an open `U ∋ x` with `d_X ≤ d_X(x)` on `U`)
  up to `mem_nhds_iff`.
* `isOpen_setOf_degIndex_lt`, `isClosed_setOf_le_degIndex` are corollaries (sublevel sets open,
  superlevel sets closed), derived from B.
* `eventually_degIndexWith_le` is the Chapter 1 ingredient: for a presentation
  `T : E ≅ ℝⁿ ⊕ W` the number of vanishing `ℝⁿ`-coordinates of `T y` is upper semicontinuous on
  ALL of `E₀`.  It is not about M-polyfolds and not a consequence of B (B only sees points of
  M-polyfolds, i.e. of `C`, and `degIndex_X` is not `degIndexWith T` off `C`); in `B → A` it is
  proved directly (a coordinate that is nonzero at `x` stays nonzero nearby). -/

namespace RoundTrip.V2_27
open Polyfold Set Filter Topology

/-- The project's statement (universe `0`). -/
def A : Prop :=
  (type_of% @Polyfold.lemma_2_23.{0}) ∧ (type_of% @Polyfold.eventually_degIndexWith_le) ∧
    (type_of% @Polyfold.MPolyfold.isOpen_setOf_degIndex_lt.{0}) ∧
    (type_of% @Polyfold.MPolyfold.isClosed_setOf_le_degIndex.{0})

theorem A_holds : A :=
  ⟨@Polyfold.lemma_2_23.{0}, @Polyfold.eventually_degIndexWith_le,
    @Polyfold.MPolyfold.isOpen_setOf_degIndex_lt.{0},
    @Polyfold.MPolyfold.isClosed_setOf_le_degIndex.{0}⟩

section Glue

/-- Upper semicontinuity of `degIndexWith T` on `E₀`, proved directly. -/
theorem eventually_degIndexWith_le' {E : ScBanach} {n : ℕ} {W : ScBanach}
    (T : ScIso E ((ScBanach.const (Fin n → ℝ)).prod W)) (x : E 0) :
    ∀ᶠ y in 𝓝 x, degIndexWith T y ≤ degIndexWith T x := by
  classical
  have h : ∀ i : Fin n, ∀ᶠ y in 𝓝 x, (T 0 y).1 i = 0 → (T 0 x).1 i = 0 := by
    intro i
    by_cases hi : (T 0 x).1 i = 0
    · exact Eventually.of_forall fun _ _ => hi
    · have hc : Continuous fun y : E 0 => (T 0 y).1 i :=
        (continuous_apply i).comp (continuous_fst.comp (T 0).continuous)
      exact ((hc.tendsto x).eventually (isOpen_ne.mem_nhds hi)).mono fun y hy h0 => (hy h0).elim
  refine (eventually_all.2 h).mono fun y hy => ?_
  change (Finset.univ.filter fun i => (T 0 y).1 i = 0).card ≤
    (Finset.univ.filter fun i => (T 0 x).1 i = 0).card
  exact Finset.card_le_card fun i hi => by
    rw [Finset.mem_filter] at hi ⊢
    exact ⟨hi.1, hy i hi.2⟩

/-- B in filter form. -/
theorem eventually_of_B (hB : B) {X : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X]
    (P : MPolyfold X) (x : X) : ∀ᶠ y in 𝓝 x, P.degIndex y ≤ P.degIndex x := by
  obtain ⟨U, hU, hxU, hle⟩ := hB X P x
  exact Filter.mem_of_superset (hU.mem_nhds hxU) hle

end Glue

/-- `A → B`: `lemma_2_23` gives an open neighbourhood. -/
theorem A_to_B : A → B := by
  rintro ⟨h223, -, -, -⟩ X _ _ _ P x
  obtain ⟨U, hUsub, hU, hxU⟩ := mem_nhds_iff.1 (h223 P x)
  exact ⟨U, hU, hxU, hUsub⟩

/-- `B → A`: `lemma_2_23` and its two corollaries from B; `eventually_degIndexWith_le` directly. -/
theorem B_to_A : B → A := by
  intro hB
  have h1 : type_of% @Polyfold.MPolyfold.isOpen_setOf_degIndex_lt.{0} := by
    intro X _ _ _ P k
    rw [isOpen_iff_mem_nhds]
    intro x hx
    exact (eventually_of_B hB P x).mono fun y hy => lt_of_le_of_lt hy hx
  refine ⟨fun P x => eventually_of_B hB P x, @eventually_degIndexWith_le', h1, ?_⟩
  intro X _ _ _ P k
  have : {x | k ≤ P.degIndex x} = {x | P.degIndex x < k}ᶜ := by
    ext x; simp [not_lt]
  rw [this]
  exact (h1 P k).isClosed_compl

#rt_check RoundTrip.V2_27.A_to_B [Polyfold.lemma_2_23, Polyfold.eventually_degIndexWith_le,
  Polyfold.MPolyfold.isOpen_setOf_degIndex_lt, Polyfold.MPolyfold.isClosed_setOf_le_degIndex]
#rt_check RoundTrip.V2_27.B_to_A [Polyfold.lemma_2_23, Polyfold.eventually_degIndexWith_le,
  Polyfold.MPolyfold.isOpen_setOf_degIndex_lt, Polyfold.MPolyfold.isClosed_setOf_le_degIndex]
#rt_overlap RoundTrip.V2_27.B_to_A [Polyfold.lemma_2_23, Polyfold.eventually_degIndexWith_le,
  Polyfold.MPolyfold.isOpen_setOf_degIndex_lt, Polyfold.MPolyfold.isClosed_setOf_le_degIndex]

end RoundTrip.V2_27
