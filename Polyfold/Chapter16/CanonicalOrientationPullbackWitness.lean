import Polyfold.Chapter16.CanonicalModelPullback
import Polyfold.Chapter16.CircleSectionCobordism
import Polyfold.Chapter16.CanonicalOrientationWitness
import Polyfold.Chapter12.OrientationGeneralizedIsoExample
import Polyfold.Chapter14.LocalOrientationEquivalenceHalfSpace
import Polyfold.Chapter16.CircleSectionPolyfold

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), **Theorem 15.4.1** and
**Definition 15.4.2** (pp. 701–702), with the pull-back of orientations along strong bundle
equivalences (Definition 11.3.6, Theorem 12.5.7).

# Examples for the pull-back of the canonical orientation

* **`isCanonicalFor_pullSection_negSection`**: the circle section `f'(x) = (x, x₀² + x₁² − 1)`
  over `ℝ² × ℝ → ℝ²` and the strong bundle equivalence `(-id)^* W' → W'` covering `ϕ = -id`
  (not the identity): for a canonically oriented perturbation `(Λ', T̂')` of `f'` the
  pull-back `ϕ^* T̂'` is canonical for `(Λ' ∘ Φ, h^* o')` on `f = Φ^* f'`, and the pulled
  support `supp(Λ' ∘ Φ ∘ f)` is non-empty.
* **`isCanonicalFor_pullSection_halfDisc`**: the half-disc section over the half-space bundle
  `[0, ∞) × ℝ → [0, ∞)` and the identity equivalence: `ϕ^* T̂'` is canonical and a boundary
  point lies in the support.
* **`toCompact_eq_of_diagram_pullSection_circle`**: for the circle section over `|ℝ²|` and the
  identity diagram `W ←1 W →1 W`, a canonically oriented model perturbation with non-empty
  support satisfies every hypothesis of `ModelPerturbation.toCompact_eq_of_diagram_pullSection`.
-/

set_option maxSynthPendingDepth 3
set_option linter.unusedSectionVars false

open Set Function Topology
open scoped ContDiff

noncomputable section

namespace Polyfold

universe u

namespace CanonicalOrientationPullbackExamples

open SBLocalization EpGroupoid StrongBundleEquivalenceExamples StrongBundleLocalizationExamples

/-! ### The circle section and the fibre-and-base negation -/

section Circle

open TrivialBundle

/-- **The pull-back of the canonical orientation along a non-identity equivalence** (Theorem
15.4.1, Definition 15.4.2).  Over the circle section `f'` of `ℝ² × ℝ → ℝ²` there is a
canonically oriented perturbation `(Λ', T̂')` with non-empty support; along the strong bundle
equivalence `(-id)^* W' → W'` covering `ϕ = -id ≠ id`, the pull-back `ϕ^* T̂'` is canonical for
`(Λ' ∘ Φ, h^* o')` on `f = Φ^* f'`, and `supp(Λ' ∘ Φ ∘ f)` is non-empty. -/
theorem isCanonicalFor_pullSection_negSection :
    ∃ P : OrientedRegularPerturbation (epSEP 2 1) circleSection 0,
      IsCanonicalPerturbation isScFredholmSectionFunctor_circleSection.2
        (hasScPlusSectionsThrough_epSEP 2 1) circleSectionOrientation P ∧
      IsCanonicalFor (fun w => P.Λ ((SEP.Hom.Φ (negSEPHom 2 1)).obj w))
        (isScFredholmSectionFunctor_negSection contDiff_circleMap).2
        (hasScPlusSectionsThrough_negSEP 2 1)
        ((sbe (negSEPHom_mem_equivalences 2 1)).pullOr
          (isScFredholmSectionFunctor_negSection contDiff_circleMap)
          isScFredholmSectionFunctor_circleSection rfl (hasScPlusSectionsThrough_negSEP 2 1)
          (hasScPlusSectionsThrough_epSEP 2 1) circleSectionOrientation)
        1 ((SEP.Hom.ϕ (negSEPHom 2 1)).pullSection P.T) ∧
      (EpGroupoid.supp (fun z =>
        (P.Λ ((SEP.Hom.Φ (negSEPHom 2 1)).obj (negSection circleMap z)) : ℚ))).Nonempty ∧
      (SEP.Hom.ϕ (negSEPHom 2 1)).obj ≠ id := by
  obtain ⟨P, -, hP, y, hy⟩ := exists_isCanonicalPerturbation_circleSection
  refine ⟨P, hP, IsCanonicalFor.pullSection (sbe (negSEPHom_mem_equivalences 2 1))
    (isScFredholmSectionFunctor_negSection contDiff_circleMap)
    isScFredholmSectionFunctor_circleSection rfl (hasScPlusSectionsThrough_negSEP 2 1)
    (hasScPlusSectionsThrough_epSEP 2 1) hP, ⟨negMap 2 y, ?_⟩, trivialNeg_obj_ne_id 2⟩
  have h := multisection_pullback_apply (sbe (negSEPHom_mem_equivalences 2 1))
    (isScFredholmSectionFunctor_circleSection) (f := negSection circleMap) rfl
    (Λ' := P.Λ) (negMap 2 y)
  have hy' : (SEP.Hom.ϕ (negSEPHom 2 1)).obj (negMap 2 y) = y :=
    neg_neg (G := Fin 2 → ℝ) y
  rw [hy'] at h
  change (0 : ℚ) < ((P.Λ ((SEP.Hom.Φ (negSEPHom 2 1)).obj
    (negSection circleMap (negMap 2 y))) : ℚ≥0) : ℚ)
  rw [h]
  exact hy

end Circle

/-! ### The half-disc section with boundary -/

section HalfDisc

open HalfSpaceBundle

/-- **The pull-back of the canonical orientation over a bundle with boundary** (Theorem 15.4.1,
Definition 15.4.2).  Over the half-disc section of `[0, ∞) × ℝ → [0, ∞)` there is a canonically
oriented perturbation `(Λ', T̂')` whose support contains a boundary point; along the identity
equivalence, `ϕ^* T̂'` is canonical for `(Λ' ∘ Φ, h^* o')` and that boundary point lies in
`supp(Λ' ∘ Φ ∘ f)`. -/
theorem isCanonicalFor_pullSection_halfDisc :
    ∃ P : OrientedRegularPerturbation (halfSEP 1 1) halfDiscSection 0,
      IsCanonicalPerturbation
        (isScFredholmSectionFunctor_graphSection_halfSEP (k := 1) contDiff_halfDiscMap).2
        (hasScPlusSectionsThrough_halfSEP 1 1) (halfOrientation contDiff_halfDiscMap) P ∧
      IsCanonicalFor (fun w => P.Λ ((EpFunctor.id (halfSEP 1 1).E.toEpGroupoid).obj w))
        (isScFredholmSectionFunctor_graphSection_halfSEP (k := 1) contDiff_halfDiscMap).2
        (hasScPlusSectionsThrough_halfSEP 1 1)
        ((EpStrongBundle.isStrongBundleEquivalence_id (halfSEP 1 1).E).pullOr
          (isScFredholmSectionFunctor_graphSection_halfSEP (k := 1) contDiff_halfDiscMap)
          (isScFredholmSectionFunctor_graphSection_halfSEP (k := 1) contDiff_halfDiscMap)
          (eq_pullback_id contDiff_halfDiscMap) (hasScPlusSectionsThrough_halfSEP 1 1)
          (hasScPlusSectionsThrough_halfSEP 1 1) (halfOrientation contDiff_halfDiscMap))
        1 ((EpFunctor.id (halfSEP 1 1).X).pullSection P.T) ∧
      ∃ x ∈ (halfSEP 1 1).X.PObj.boundary, x ∈ EpGroupoid.supp (fun z =>
        (P.Λ ((EpFunctor.id (halfSEP 1 1).E.toEpGroupoid).obj (halfDiscSection z)) : ℚ)) := by
  obtain ⟨P, -, hP, x, hxb, hx⟩ := exists_isCanonicalPerturbation_halfSEP
  exact ⟨P, hP, IsCanonicalFor.pullSection
    (EpStrongBundle.isStrongBundleEquivalence_id (halfSEP 1 1).E)
    (isScFredholmSectionFunctor_graphSection_halfSEP (k := 1) contDiff_halfDiscMap)
    (isScFredholmSectionFunctor_graphSection_halfSEP (k := 1) contDiff_halfDiscMap)
    (eq_pullback_id contDiff_halfDiscMap) (hasScPlusSectionsThrough_halfSEP 1 1)
    (hasScPlusSectionsThrough_halfSEP 1 1) hP, x, hxb, hx⟩

end HalfDisc

/-! ### The identity diagram over the circle polyfold bundle -/

section CirclePolyfold

open TrivialBundle StrongPolyfoldBundle

/-- **The identity diagram `W ←1 W →1 W` satisfies the hypotheses of
`toCompact_eq_of_diagram_pullSection`** for a model perturbation `M` with the canonical
orientation of `(F, o)`: `|[1]| = id`, `1^* F` is sc-Fredholm (Theorem 10.4.5), and
`Λ ∘ 1 = Λ ∘ 1`, `1^* o = 1^* o`. -/
theorem toCompact_eq_of_diagram_pullSection_id {Y Z : Type u} [TopologicalSpace Y]
    [TopologicalSpace Z] {p : Y → Z} {c : StrongPolyfoldBundle p} {a : SectionRep c} {m : ℕ}
    (M : ModelPerturbation a m) (hF : a.S.A.E.IsScFredholmSectionFunctor a.F)
    (hsec : a.S.A.B.HasScPlusSectionsThrough)
    {o : ∀ x (hs : x ∈ a.S.A.X.PObj.smoothSet), Orx a.F hF.2 x hs}
    (hC : IsCanonicalPerturbation hF.2 hsec o M.toOrientedRegularPerturbation) :
    M.toCompact = M.toCompact :=
  ModelPerturbation.toCompact_eq_of_diagram_pullSection M M (SDiagram.id a.S.A)
    (SEP.equivalences.id_mem _) (by rw [SDiagram.orbitMap_id']; rfl) hF hF
    ((EpStrongBundle.theorem_10_4_5_fred (SDiagram.id a.S.A).hΦ).2.1 hF) rfl hsec hsec hsec
    (fun _ => rfl) rfl hC hC

/-- **The hypotheses of `toCompact_eq_of_diagram_pullSection` are satisfiable** (§16.6,
p. 739): over the circle section of `|ℝ² × ℝ| → |ℝ²|` there is a model perturbation `M` with the
canonical orientation of `(f, o)` and non-empty support, and the identity diagram
`W ←1 W →1 W` with `M₁ = M₂ = M` satisfies every hypothesis of the theorem. -/
theorem toCompact_eq_of_diagram_pullSection_circle :
    ∃ M : ModelPerturbation circleGraphRep 0,
      IsCanonicalPerturbation isScFredholmSectionFunctor_circleSection.2
        (hasScPlusSectionsThrough_epSEP 2 1) circleSectionOrientation
        M.toOrientedRegularPerturbation ∧
      (EpGroupoid.supp (fun z => (M.Λ (circleSection z) : ℚ))).Nonempty ∧
      M.toCompact = M.toCompact := by
  obtain ⟨P, -, hP, hne⟩ := exists_isCanonicalPerturbation_circleSection
  let M : ModelPerturbation circleGraphRep 0 :=
    { P with
      smooth := fun x hx => absurd
        (mem_smoothSet_of_isScSmoothMap (MPolyfold.isScSmoothMap_id (P := rnPolyfold 2)) x) hx }
  exact ⟨M, hP, hne, toCompact_eq_of_diagram_pullSection_id M
    isScFredholmSectionFunctor_circleSection (hasScPlusSectionsThrough_epSEP 2 1) hP⟩

end CirclePolyfold

end CanonicalOrientationPullbackExamples

end Polyfold
