import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V8_6

/-! Round trip for V8_6 (Lemma 8.1.4 = 2017 Lemma 8.3: associativity of the composition of
`T𝐗`).

`A` is the type of `EpGroupoid.lemma_8_1_4` (universes at `0`):
`(l ∘ k) ∘ h = l ∘ (k ∘ h)` for `Ts l = Tt k`, `Ts k = Tt h`.

* `A → B`: B's `tCompB` is the project's `tComp` by `rfl`; the equality of the bracketings is
  `lemma_8_1_4`; B's extra description of the common value (over `σ ∘ (ψ ∘ φ)`, `Ts` equal to
  `Ts h`) is `tBase_tComp`, `tSrc_tComp` applied twice, `l` and `k ∘ h` being composable by
  Lemma 8.2 (`lemma_8_1_3`, a project lemma outside this item).
* `B → A`: B's first clause. -/

namespace RoundTrip.V8_6
open Polyfold

/-- The project's statement (universes at `0`). -/
def A : Prop := type_of% @Polyfold.EpGroupoid.lemma_8_1_4.{0}

theorem A_holds : A := @Polyfold.EpGroupoid.lemma_8_1_4.{0}

theorem A_to_B : A → B := by
  intro hA Obj Mor _ _ _ _ _ _ X
  refine ⟨X.isScSmoothMap_src, X.isScSmoothMap_tgt, fun l k h hlk' hkh' => ?_⟩
  have hlk : X.tSrc l = X.tTgt k := hlk'
  have hkh : X.tSrc k = X.tTgt h := hkh'
  have h2 : X.tSrc l = X.tTgt (X.tComp k h) := by rw [(X.lemma_8_1_3 hkh).2, hlk]
  refine ⟨(hA X hlk hkh).symm, ?_, ?_⟩
  · change X.tBase (X.tComp l (X.tComp k h)) =
      X.comp (X.tBase l) (X.comp (X.tBase k) (X.tBase h))
    rw [X.tBase_tComp h2, X.tBase_tComp hkh]
  · change X.tSrc (X.tComp l (X.tComp k h)) = X.tSrc h
    rw [X.tSrc_tComp h2, X.tSrc_tComp hkh]

theorem B_to_A : B → A := by
  intro hB Obj Mor _ _ _ _ _ _ X l k h hlk hkh
  obtain ⟨_, _, hB'⟩ := hB Obj Mor X
  exact (hB' l k h hlk hkh).1.symm

#rt_check RoundTrip.V8_6.A_to_B [Polyfold.EpGroupoid.lemma_8_1_4]
#rt_check RoundTrip.V8_6.B_to_A [Polyfold.EpGroupoid.lemma_8_1_4]
#rt_overlap RoundTrip.V8_6.B_to_A [Polyfold.EpGroupoid.lemma_8_1_4]

end RoundTrip.V8_6
