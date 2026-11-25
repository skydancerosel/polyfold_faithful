import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V19_89

set_option maxSynthPendingDepth 3

/-! Round trip for V19_89 (2021 Theorem 19.7.29, p. 929; 2017 Theorem 19.10).

* `A`: the type of `theorem_19_7_29_hyp` (universe `0`), the only theorem of the item; the
  definitions `fibredMorP`, `gammaHat`, `gammaFib` are vocabulary.  It assumes
  `Bh.IsCompatible`; `B` does not.
* `A_to_B` is not proved, for two reasons: the hypothesis `IsCompatible`, and, even under it, `A`
  asserts only `Nonempty (ProperPolyfoldCoveringFunctor gctA gctB)`, with no statement that the
  functor is `P` or that its polyfold structure of `B` is that of `(F, 𝓕)`.
* `B_to_A` is not proved: `B` gives the `Nonempty` conjunct (`B_to_nonempty`), but not the
  other conjuncts of `A` (`HasCoveringUniformizers` of the polyfold construction of `B`, the open
  embeddings `|Ψ̂| : |E| → |A|` with `T_{|A|}`, their covering of `|A|`, the sheet-model identities of
  each `Ψ̂ ∈ F̂(β)`, and the description of `M(Ψ̂, Ψ̂')` as a fibred product through `gammaFib`). -/

namespace RoundTrip.V19_89
open Polyfold GroupoidalCategory

/-- The project's statement (universe `0`). -/
def A : Prop := type_of% @CoveringBasicConstruction.theorem_19_7_29_hyp.{0}

theorem A_holds : A := @CoveringBasicConstruction.theorem_19_7_29_hyp.{0}

/-- `B` gives the `Nonempty` conjunct of `A` (under `A`'s hypotheses). -/
theorem B_to_nonempty : B →
    ∀ {A B : GroupoidalCategory.{0}} {P : GroupoidFunctor A.toGroupoidStr B.toGroupoidStr}
      (Bh : CoveringBasicConstruction P) (hP : IsFiniteToOneCovering P)
      (hC : Bh.IsCompatible) (hU : Bh.HasClassUniformizers)
      (hm : @TopologicalSpace.MetrizableSpace B.OrbitSpace (Bh.toBasic.natTop hU.toBasic)),
      Nonempty (ProperPolyfoldCoveringFunctor (Bh.gctA hP hC hU hm) (Bh.gctB hU hm)) := by
  intro hB A B P Bh hP hC hU hm
  obtain ⟨hA', Q, -⟩ := hB A B P hP Bh hU.toBasic hm
  have ht : topA Bh = Bh.natTopA hP hC hU :=
    TopologicalSpace.generateFrom_setOfPred_isOpen (Bh.natTopA hP hC hU)
  suffices key : ∀ (t : TopologicalSpace A.OrbitSpace) (ht : t = Bh.natTopA hP hC hU)
      (hA' : @TopologicalSpace.MetrizableSpace A.OrbitSpace t),
      ProperPolyfoldCoveringFunctor (@GCT.mk A t hA')
          (Bh.toBasic.toGCTOfMetrizable hU.toBasic hm) →
      Nonempty (ProperPolyfoldCoveringFunctor (Bh.gctA hP hC hU hm) (Bh.gctB hU hm)) from
    key _ ht hA' Q
  intro t ht hA' Q
  subst ht
  exact ⟨Q⟩

#rt_check RoundTrip.V19_89.B_to_nonempty [Polyfold.GroupoidalCategory.CoveringBasicConstruction.theorem_19_7_29_hyp]
#rt_overlap RoundTrip.V19_89.B_to_nonempty [Polyfold.GroupoidalCategory.CoveringBasicConstruction.theorem_19_7_29_hyp]

end RoundTrip.V19_89
