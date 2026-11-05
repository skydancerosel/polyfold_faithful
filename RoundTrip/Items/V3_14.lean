import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V3_14

/-!
Round trip for V3_14 (Theorem 3.12).  `A` is the conjunction of the types of
`Polyfold.theorem_3_12`, `Polyfold.theorem_3_12_local_subset`,
`Polyfold.IsStrongBundleIso.snd_eq_zero_iff`, `Polyfold.MPolyfold.continuousOn_levelChartSymm` and
`Polyfold.eq_of_mem_closure_of_continuousOn`, universes instantiated at `0`.

Refresh 2026-11-02 (HEAD after the germ reading, phase 2): `Polyfold.theorem_3_12` now denotes
the germ-reading statement (hypothesis `IsScFredholmGerm`: filling `IsFillingGerm`, sc⁺-germ
`IsScPlusGerm`), and B's `IsScFredholmGermTame` is the germ reading too; the proof below is
unchanged and still checks.

Glue for `A → B`:
* B's tame germ data are germ data (`IsScFredholmGermTame.isScFredholmGerm`, germ reading); an
  sc-smooth section is a section.  B's tameness of the bundle is not needed.
* A's compact `K ⊆ X_i` (type `PX.Level i := PX.levelSet i` with `PX.levelTopology i`) with
  `levelVal '' K = cl{…}` is B's `{p : levelSet i | ↑p ∈ cl{…}}` (by injectivity of `levelVal`).

`B → A` is not proved: `theorem_3_12` assumes neither a tame bundle nor tame germ data nor an
sc-smooth section, and the other conjuncts are auxiliary lemmas B does not state.
-/

namespace RoundTrip.V3_14
open Polyfold

/-- The project's statement: Theorem 3.12 and the four lemmas listed with it, universes at `0`. -/
def A : Prop :=
  type_of% @Polyfold.theorem_3_12.{0, 0} ∧ type_of% @Polyfold.theorem_3_12_local_subset ∧
    type_of% @Polyfold.IsStrongBundleIso.snd_eq_zero_iff ∧
    type_of% @Polyfold.MPolyfold.continuousOn_levelChartSymm.{0} ∧
    type_of% @Polyfold.eq_of_mem_closure_of_continuousOn.{0, 0}

theorem A_holds : A :=
  ⟨@Polyfold.theorem_3_12.{0, 0}, @Polyfold.theorem_3_12_local_subset,
    @Polyfold.IsStrongBundleIso.snd_eq_zero_iff, @Polyfold.MPolyfold.continuousOn_levelChartSymm.{0},
    @Polyfold.eq_of_mem_closure_of_continuousOn.{0, 0}⟩

theorem A_to_B : A → B := by
  intro hA X _ _ _ PX Y _ _ _ P _ _ Bd f x₀ _ hf hgerm hx₀
  obtain ⟨O, hOo, hOx, hOn, hK⟩ := hA.1 hf.1 hgerm.isScFredholmGerm hx₀
  refine ⟨O, fun i => ⟨hOo i, hOx i, hOn i⟩, fun i => ?_⟩
  obtain ⟨K, hKc, hKeq⟩ := hK i
  refine ⟨?_, ?_⟩
  · rw [← hKeq]
    rintro _ ⟨p, -, rfl⟩
    exact PX.levelVal_mem p
  · have hset : {p : PX.levelSet i | (p : X) ∈ closure {x | x ∈ O i ∧ IsZeroAt P f x}} = K := by
      ext p
      rw [← hKeq]
      constructor
      · rintro ⟨q, hq, hqp⟩
        have : q = p := PX.levelVal_injective i hqp
        exact this ▸ hq
      · intro hp
        exact ⟨p, hp, rfl⟩
    rw [hset]
    exact hKc

#rt_check RoundTrip.V3_14.A_to_B [Polyfold.theorem_3_12, Polyfold.theorem_3_12_local_subset,
  Polyfold.IsStrongBundleIso.snd_eq_zero_iff, Polyfold.MPolyfold.continuousOn_levelChartSymm,
  Polyfold.eq_of_mem_closure_of_continuousOn]

end RoundTrip.V3_14
