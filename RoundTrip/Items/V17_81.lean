import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V17_81

set_option maxSynthPendingDepth 3

/-! Round trip for V17_81 (2021 Theorem 17.4.16, p. 801: for the natural structures on the
`M(Ψ_θ, Ψ'_{θ'})` all structure maps are sc-smooth and `s, t` local sc-diffeomorphisms).

The item lists one theorem; `A` is its type at universe `0`: for a tame `S` with `F(α) ≠ ∅`, any
uniformizers `Ψ, Ψ', Ψ''` of `F`, ANY points `o, o', o''` with good neighbourhoods `V, V', V''`
and faces `θ, θ', θ''` of them, `s`, `t` on `M(Ψ_θ, Ψ'_{θ'})` (`GoodNbhd.ftrPolyfold`) are local
sc-diffeomorphisms onto the faces (`faceSubPolyfold`), and `ι`, `u`, `m` are sc-smooth.

* `A_to_B`: specialize to the data of `B`'s `FaceData` `d, d', d''` (whose `ō` is fixed by `G`);
  `B`'s `src/tgt/inv/unit/mul` unfold to the generic transition-set maps of `A`, and the proof
  arguments of `IsScSmoothOnFibredProduct` agree by proof irrelevance.
* `B_to_A`: `B` covers only points `ō` fixed by `G` (`FaceData.fix`), while `A` allows any point
  `o` of `O` with a good neighbourhood (a natural neighbourhood of `o` for the action groupoid,
  whose isotropy is `G_o`, not necessarily `G`).  No `FaceData` exists for a non-fixed `o`, so
  `B` says nothing there; `A` is re-proved outright from the non-item lemmas `ftr_*`
  (Lemma 17.4.15) — this direction does not use `B` (flagged). -/

namespace RoundTrip.V17_81
open Polyfold GCT.PolyfoldConstruction

def A : Prop := type_of% @Polyfold.GCT.PolyfoldConstruction.theorem_17_4_16.{0}

theorem A_holds : A := @Polyfold.GCT.PolyfoldConstruction.theorem_17_4_16.{0}

theorem A_to_B : A → B := by
  intro hA C S hT hS
  refine ⟨fun d d' => (hA hT hS d.V d'.V d'.V d.hθ d'.hθ d'.hθ).1,
    fun d d' => (hA hT hS d.V d'.V d'.V d.hθ d'.hθ d'.hθ).2.1,
    fun d d' => (hA hT hS d.V d'.V d'.V d.hθ d'.hθ d'.hθ).2.2.1,
    fun d => (hA hT hS d.V d.V d.V d.hθ d.hθ d.hθ).2.2.2.1,
    fun d d' d'' => ⟨(hA hT hS d.V d'.V d''.V d.hθ d'.hθ d''.hθ).2.1.isScSmoothMap,
      (hA hT hS d.V d'.V d''.V d.hθ d'.hθ d''.hθ).2.2.2.2⟩⟩

/-- `B ⇒ A`, by proving `A` outright (does not use `B`: `B` covers only fixed points `ō`). -/
theorem B_to_A : B → A := fun _ _ _ hT hS _ _ _ _ _ _ V V' V'' _ _ _ hθ hθ' hθ'' =>
  ⟨V.ftr_isLocalScDiffeo_src hT hS V' hθ hθ', V.ftr_isLocalScDiffeo_tgt hT hS V' hθ hθ',
    V.ftr_isScSmoothMap_inv hT hS V' hθ hθ', V.ftr_isScSmoothMap_unit hT hS hθ,
    V.ftr_isScSmoothMap_mul hT hS V' V'' hθ hθ' hθ''⟩

#rt_check RoundTrip.V17_81.A_to_B [Polyfold.GCT.PolyfoldConstruction.theorem_17_4_16]
#rt_check RoundTrip.V17_81.B_to_A [Polyfold.GCT.PolyfoldConstruction.theorem_17_4_16]
#rt_overlap RoundTrip.V17_81.B_to_A [Polyfold.GCT.PolyfoldConstruction.theorem_17_4_16]

end RoundTrip.V17_81
