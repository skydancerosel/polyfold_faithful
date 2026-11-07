import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V6_12

/-!
Round trip for V6_12 (Lemma 6.11).  `A` is the type of `lemma_6_11` (universes at `0`); the maps
`projSeqJ`, `projSeqPhi`, `projSeqPi` and `projSeq` are vocabulary.

The maps agree definitionally with B's: `jMap`/`projSeqJ` are `Submodule.inclusion` of the same
inclusion `ker T ⊆ ker(P T)` (different proofs), `PhiMap`/`projSeqPhi` are the same composite, and
`piMap`/`projSeqPi` the same `liftQ` (`jMap_eq`, `PhiMap_eq`, `piMap_eq`, all `rfl`).

* `A ⇒ B`: instantiation (B's Fredholm hypothesis is not needed).
* `B ⇒ A` is not proved: A has no Fredholm hypothesis on `T`, B does (the text's standing
  assumption).  It should follow from B by passing to `T̄ : E / ker T → F` (injective, range
  `R(T)` of finite codimension since `R(T) + ker P = F`, hence closed, so `T̄` is Fredholm, and
  `P ∈ Π_{T̄}`); exactness of `E(T̄, P)` gives that of `E(T, P)`.  This needs the quotient Banach
  space, the continuity of `T̄` and the closed-range lemma for finite-codimensional ranges, none
  available as project lemmas; not done.
-/

namespace RoundTrip.V6_12
open Polyfold

/-- The project's statement (Lemma 6.11), universes at `0`. -/
def A : Prop := type_of% @Polyfold.lemma_6_11.{0, 0}

theorem A_holds : A := @Polyfold.lemma_6_11

set_option linter.unusedSectionVars false

section Glue

variable {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F] [CompleteSpace E] [CompleteSpace F]

theorem jMap_eq (T : E →L[ℝ] F) (P : F →L[ℝ] F) : jMap T P = projSeqJ T P := rfl

theorem PhiMap_eq (T : E →L[ℝ] F) (P : F →L[ℝ] F) : PhiMap T P = projSeqPhi T P := rfl

theorem piMap_eq (T : E →L[ℝ] F) (P : F →L[ℝ] F) (hP : P ∘L P = P) :
    piMap T P hP = projSeqPi (T := T) hP := rfl

/-- B's good left-projections are the project's. -/
theorem isGLP_iff (T : E →L[ℝ] F) (P : F →L[ℝ] F) : IsGLP T P ↔ IsGoodLeftProj T P :=
  ⟨fun h => ⟨h.1, h.2.1, h.2.2⟩, fun h => ⟨h.isProj, h.finite_coker, h.range_comp⟩⟩

end Glue

theorem A_to_B : A → B := by
  intro hA E F _ _ _ _ _ _ T _ P hP
  exact hA ((isGLP_iff T P).1 hP)

#rt_check RoundTrip.V6_12.A_to_B [Polyfold.lemma_6_11]
#rt_check RoundTrip.V6_12.piMap_eq [Polyfold.lemma_6_11]

end RoundTrip.V6_12
