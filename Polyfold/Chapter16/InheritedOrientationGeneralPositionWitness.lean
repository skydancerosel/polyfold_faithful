import Polyfold.Chapter16.InheritedOrientationGeneralPosition
import Polyfold.Chapter16.CanonicalModelTransferWitness
import Polyfold.Chapter16.CanonicalOrientationWitness
import Polyfold.Chapter16.HalfSpaceOrientedSection

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), §16.6 (p. 739), with
**Definition 15.3.5** (p. 693) and **Theorem 15.4.1** (p. 702).  Numbers and pages are the 2021
text's.

# An example with boundary for the model independence of the inherited orientation

The strong polyfold bundle is `|H × ℝ| → |H|` over the half-plane `H = [0, ∞) × ℝ`
(`halfPolyfoldBundle 1 1`, `∂Z ≠ ∅`, fibres `ℝ`), the section is the graph of
`(a, y) ↦ a² + y² − 1`, oriented by `halfOrientationRep`, and the perturbation is the zero
multisection with its canonical orientation; its solution set, the half circle, meets `∂H` at
`(0, ±1)`.

* `Correspondence.ofDiagram_id`: the identity diagram as a correspondence through
  `Correspondence.ofDiagram` (the middle section is sc-Fredholm by Theorem 10.4.5).
* **`isInheritedFrom_generalPosition_halfDisc`**: `∂Z ≠ ∅`, the fibres are non-zero, the
  canonically oriented perturbation is in general position with support meeting `∂H`, every
  hypothesis of `isInheritedFrom_of_correspondence_generalPosition` and of
  `isInheritedFrom_generalPosition_iff_of_correspondence` holds for the identity correspondence,
  and the conclusions follow.
-/

set_option maxSynthPendingDepth 3
set_option linter.unusedSectionVars false

open Set Function Topology
open scoped ContDiff

noncomputable section

namespace Polyfold

universe u

open SBLocalization

namespace StrongPolyfoldBundle.OrientationRep.Correspondence

variable {Y Z : Type u} [TopologicalSpace Y] [TopologicalSpace Z] {p : Y → Z}
  {c : StrongPolyfoldBundle p} {s : FredholmSection c}

/-- **The identity diagram as a correspondence through `ofDiagram`**: `|[1]| = id`,
`1^* F = 1^* F` and `1^* o = 1^* o`; the middle section is sc-Fredholm by Theorem 10.4.5. -/
def ofDiagram_id (o : OrientationRep s) : Correspondence o o :=
  ofDiagram (SDiagram.id o.a.S.A) (SEP.equivalences.id_mem _)
    (by rw [SDiagram.orbitMap_id']; rfl) rfl o.hsec rfl

end StrongPolyfoldBundle.OrientationRep.Correspondence

namespace HalfSpaceBundle

open StrongPolyfoldBundle OrientationRep

/-- **The half-disc example satisfies the hypotheses of the model independence with boundary**
(§16.6, p. 739): for `halfOrientationRep` over `|H × ℝ| → |H|`, the polyfold has non-empty
boundary, the fibres are non-zero, and the canonically oriented zero perturbation `P` is in
general position (Definition 15.3.5) with support meeting `∂H`.  With the identity
correspondence (`Correspondence.ofDiagram_id`), `isInheritedFrom_of_correspondence_generalPosition`
applies to `P`, and `isInheritedFrom_generalPosition_iff_of_correspondence` applies (tame strong
polyfold bundle, sc-smooth bump functions, tame germ data, index `1`). -/
theorem isInheritedFrom_generalPosition_halfDisc :
    (halfPolyfoldBundle 1 1).polyfold.boundary.Nonempty ∧
    (∀ y : (halfSEP 1 1).Obj, Nontrivial ((halfSEP 1 1).P ⁻¹' {y})) ∧
    ∃ P : OrientedRegularPerturbation (halfSEP 1 1) halfDiscSection 0,
      IsCanonicalInGeneralPosition (halfOrientationRep contDiff_halfDiscMap) P ∧
      (∃ x ∈ (halfSEP 1 1).X.PObj.boundary,
        x ∈ EpGroupoid.supp (fun z => (P.Λ (halfDiscSection z) : ℚ))) ∧
      IsInheritedFrom IsCanonicalInGeneralPosition (halfOrientationRep contDiff_halfDiscMap)
        ((ModelPerturbation.ofRegular P).toOrientedPerturbation
          (halfOrientationRep contDiff_halfDiscMap).ha) ∧
      ∀ Q : OrientedPerturbation (halfFredholmSection (m := 1) (k := 1)
          contDiff_halfDiscMap).1 0,
        IsInheritedFrom IsCanonicalInGeneralPosition (halfOrientationRep contDiff_halfDiscMap)
            Q ↔
          IsInheritedFrom IsCanonicalInGeneralPosition
            (halfOrientationRep contDiff_halfDiscMap) Q := by
  set o := halfOrientationRep (m := 1) (k := 1) contDiff_halfDiscMap
  have hF := isScFredholmSectionFunctor_graphSection_halfSEP (k := 1) contDiff_halfDiscMap
  have hΛ := isScPlusMultisection_zeroMultisection (halfSEP 1 1)
  have hidx : ∀ x ∈ (halfSEP 1 1).X.PObj.smoothSet,
      (halfSEP 1 1).B.IsIndexAt halfDiscSection x ((0 + 1 : ℕ) : ℤ) :=
    fun x _ => isIndexAt_halfDisc x
  obtain ⟨hc, hbump, -, hft, -, -, -⟩ := polyfold_hypotheses_halfSpace (m := 1) (k := 1)
    contDiff_halfDiscMap
  obtain ⟨P, hPΛ, hP, x, hxb, hx⟩ := exists_isCanonicalPerturbation_halfSEP
  have hgp : IsInGeneralPosition (halfSEP 1 1) halfDiscSection P.Λ := by
    rw [hPΛ]
    exact (isInGeneralPosition_iff_forall_at hF hΛ).2 fun _ hpos =>
      isInGeneralPositionAt_halfDisc hpos
  have hPg : IsCanonicalInGeneralPosition o P := ⟨hP, hgp⟩
  refine ⟨⟨_, ((mem_boundary_iff_obj o.a.hS _).2 (zero_mem_boundary_halfSEP 1 1))⟩,
    nontrivial_fibre_halfSEP 1 1, P, hPg, ⟨x, hxb, hx⟩, ?_, fun Q => ?_⟩
  · exact isInheritedFrom_of_correspondence_generalPosition (Correspondence.ofDiagram_id o)
      (isTame_halfSEP 1 1) (admitsBumpFunctions_halfSEP 1 1) hft hidx P hPg
  · exact isInheritedFrom_generalPosition_iff_of_correspondence hc hbump
      (Correspondence.ofDiagram_id o) hft hidx hidx Q

end HalfSpaceBundle

end Polyfold
