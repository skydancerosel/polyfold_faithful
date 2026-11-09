import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V10_53

/-! Round trip for V10_53 (2021 §10.5, pp. 504–505: the square `|𝒟|` of the symbolic diagram
(10.24), `|P'| ∘ |[D]| = |[d]| ∘ |P|`).

`A` is the conjunction of the types of the three listed theorems, universes at `0`:
`SDiagram.orbitMap_square` (the square for a diagram `D`), `GenSBMap.orbitMap_square` (for a
class `f`, with `f.base`), and `SDiagram.orbitMap_orbitMap_Φ` (`|D|(|Φ|(q)) = |Ψ|(q)`, the
lemma used in the project's proof of the square).

`B` states the square pointwise for `[D]`, `D` arbitrary: if `|[D]|(|w|) = |w'|` then
`|[d]|(|P(w)|) = |P'(w')|`, with `[d] = homMk (baseDiagB D)` (`baseDiagB D` is `D.base` up to
the proof field).

* `A_to_B`: `GenSBMap.orbitMap_square` at `D.cls`, evaluated at `|w|`
  (`|P|(|w|) = |P(w)|` by `GroupoidFunctor.orbitMap_π`).
* `B_to_A`: `SDiagram.orbitMap_square` from `B` (every `q = |w|`, and `|D|(|w|) = |w'|` for a
  representative `w'`); `GenSBMap.orbitMap_square` from it by `Quot.inductionOn`.
  `orbitMap_orbitMap_Φ` is not a consequence of `B` (it concerns the total spaces, not the
  projection to the base); it is re-proved outright, as in the project, from the non-item lemma
  `Diagram.orbitMap_orbitMap_F` for the total diagram. -/

namespace RoundTrip.V10_53
open Polyfold CategoryTheory SBLocalization

/-- The project's statement (universes at `0`). -/
def A : Prop :=
  (type_of% @Polyfold.SBLocalization.SDiagram.orbitMap_square.{0}) ∧
  (type_of% @Polyfold.SBLocalization.GenSBMap.orbitMap_square.{0}) ∧
  (type_of% @Polyfold.SBLocalization.SDiagram.orbitMap_orbitMap_Φ.{0})

theorem A_holds : A :=
  ⟨@Polyfold.SBLocalization.SDiagram.orbitMap_square.{0},
    @Polyfold.SBLocalization.GenSBMap.orbitMap_square.{0},
    @Polyfold.SBLocalization.SDiagram.orbitMap_orbitMap_Φ.{0}⟩

theorem A_to_B : A → B := by
  rintro ⟨-, hsq, -⟩ A A' D w w' h
  have e := congrFun (hsq D.cls) (A.E.toEpGroupoid.π w)
  simp only [Function.comp_apply] at e
  rw [h, GroupoidFunctor.orbitMap_π, GroupoidFunctor.orbitMap_π] at e
  exact e.symm

/-- The square for a diagram, from `B`. -/
theorem square_of_B (hB : B) {A A' : SEP.{0}} (D : SDiagram A A') :
    A'.E.projFunctor.orbitMap ∘ D.orbitMap = D.base.orbitMap ∘ A.E.projFunctor.orbitMap := by
  funext q
  obtain ⟨w, rfl⟩ := GroupoidStr.surjective_π _ q
  obtain ⟨w', hw'⟩ := GroupoidStr.surjective_π _ (D.orbitMap (A.E.toEpGroupoid.π w))
  have e := hB A A' D w w' hw'.symm
  simp only [Function.comp_apply]
  rw [← hw', GroupoidFunctor.orbitMap_π, GroupoidFunctor.orbitMap_π]
  exact e.symm

theorem B_to_A : B → A := by
  intro hB
  refine ⟨fun D => square_of_B hB D, fun f => ?_, fun D q => ?_⟩
  · exact Quot.inductionOn (motive := fun f : GenSBMap _ _ =>
      _ ∘ f.orbitMap = EPLocalization.EPLoc.orbitMap f.base ∘ _) f fun D => square_of_B hB D
  · -- `orbitMap_orbitMap_Φ`, re-proved outright (the project's proof)
    exact D.total.orbitMap_orbitMap_F q

#rt_check RoundTrip.V10_53.A_to_B [Polyfold.SBLocalization.SDiagram.orbitMap_square,
  Polyfold.SBLocalization.GenSBMap.orbitMap_square,
  Polyfold.SBLocalization.SDiagram.orbitMap_orbitMap_Φ]
#rt_check RoundTrip.V10_53.B_to_A [Polyfold.SBLocalization.SDiagram.orbitMap_square,
  Polyfold.SBLocalization.GenSBMap.orbitMap_square,
  Polyfold.SBLocalization.SDiagram.orbitMap_orbitMap_Φ]
#rt_overlap RoundTrip.V10_53.B_to_A [Polyfold.SBLocalization.SDiagram.orbitMap_square,
  Polyfold.SBLocalization.GenSBMap.orbitMap_square,
  Polyfold.SBLocalization.SDiagram.orbitMap_orbitMap_Φ]

end RoundTrip.V10_53
