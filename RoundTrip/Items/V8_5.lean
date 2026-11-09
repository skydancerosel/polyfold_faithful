import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V8_5

/-! Round trip for V8_5 (Lemma 8.1.3 = 2017 Lemma 8.2: `s_T(Ψ ∘ Φ) = s_T(Φ)`,
`t_T(Ψ ∘ Φ) = t_T(Ψ)`).

`A` is the conjunction of the types of `EpGroupoid.lemma_8_2` and `EpGroupoid.tTgt_tangentMapOn`
(the target of `k ∘ h` computed on a sheet, the text's `α`-computation), universes at `0`.

* `A → B`: B's witnesses are the project's `isScSmoothMap_src/tgt`; B's `tCompB` is the project's
  `tComp` by `rfl` (same choice, `tangentMap hs` is `tSrc` by proof irrelevance), so B is
  `lemma_8_2`.
* `B → A`: `lemma_8_2` is B.  `tTgt_tangentMapOn` (for a sheet `s : W → V` with inverse `σ`,
  `Tt(Tg h) = Tt k`) follows from B's target clause and the sheet formula
  `tComp_eq_tangentMapOn` (`k ∘ h = Tg h`, a project lemma of Lemma 8.1, not of this item). -/

namespace RoundTrip.V8_5
open Polyfold

/-- The project's statement (universes at `0`). -/
def A : Prop :=
  (type_of% @Polyfold.EpGroupoid.lemma_8_2.{0}) ∧
  (type_of% @Polyfold.EpGroupoid.tTgt_tangentMapOn.{0})

theorem A_holds : A :=
  ⟨@Polyfold.EpGroupoid.lemma_8_2.{0}, @Polyfold.EpGroupoid.tTgt_tangentMapOn.{0}⟩

theorem A_to_B : A → B := by
  rintro ⟨h82, -⟩ Obj Mor _ _ _ _ _ _ X
  exact ⟨X.isScSmoothMap_src, X.isScSmoothMap_tgt, fun Ψ Φ hΨΦ => h82 X hΨΦ⟩

theorem B_to_A : B → A := by
  intro hB
  refine ⟨?_, ?_⟩
  · intro Obj Mor _ _ _ _ _ _ X k h hkh
    obtain ⟨_, _, hB'⟩ := hB Obj Mor X
    exact hB' k h hkh
  · intro Obj Mor _ _ _ _ _ _ X σ W V hd k h hkh hk
    obtain ⟨_, _, hB'⟩ := hB Obj Mor X
    rw [← EpGroupoid.tComp_eq_tangentMapOn hd hkh hk]
    exact (hB' k h hkh).2

#rt_check RoundTrip.V8_5.A_to_B [Polyfold.EpGroupoid.lemma_8_2,
  Polyfold.EpGroupoid.tTgt_tangentMapOn]
#rt_check RoundTrip.V8_5.B_to_A [Polyfold.EpGroupoid.lemma_8_2,
  Polyfold.EpGroupoid.tTgt_tangentMapOn]
#rt_overlap RoundTrip.V8_5.B_to_A [Polyfold.EpGroupoid.lemma_8_2,
  Polyfold.EpGroupoid.tTgt_tangentMapOn]

end RoundTrip.V8_5
