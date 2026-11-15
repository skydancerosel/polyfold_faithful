import Polyfold.Chapter16.CanonicalModelTransfer
import Polyfold.Chapter16.CircleSectionPolyfold

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part III, §16.6 (p. 739)
and Definition 15.2.1.  Numbers and pages are the 2021 text's.

# Examples for the transfer of canonically oriented perturbations between models

* `OrientationRep.Correspondence.refl`: the identity diagram `W ←1 W →1 W` relates every
  orientation representative to itself, so `Correspondence` is satisfiable.
* **`isTransversal_iff_ofHom_z3InvHom`**: the hypotheses of
  `SDiagram.isTransversal_iff_of_pullback_eq` hold for the diagram `W ←1 W →Inv W` over
  `ℤ/3 × ℝ ⇉ ℝ`, whose right leg `Inv` is not the identity on morphisms (its class differs from
  `[1]`), with the graph section of a `C^∞` map and the zero multisection; the fibres are
  non-zero for `k ≥ 1`.
* **`isInheritedFrom_iff_circle`**: for the circle section over `|ℝ²|` (no boundary, sc-smooth
  partitions of unity, index `1`) every hypothesis of `isInheritedFrom_iff_of_correspondence`
  except `MiddleCanonical` holds for the identity correspondence.
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

/-- **The identity correspondence** `W ←1 W →1 W` of an orientation representative with itself:
`|[1]| = id`, `1^* F = 1^* F` is sc-Fredholm (Theorem 10.4.5), and `1^* o = 1^* o`. -/
def refl (o : OrientationRep s) : Correspondence o o where
  D := SDiagram.id o.a.S.A
  hΨ := SEP.equivalences.id_mem _
  hΓ := by rw [SDiagram.orbitMap_id']; rfl
  f'' := (SDiagram.id o.a.S.A).hΦ.pullback o.a.F
  hF'' := (EpStrongBundle.theorem_10_4_5_fred (SDiagram.id o.a.S.A).hΦ).2.1 o.hF
  hpb₁ := rfl
  hpb₂ := rfl
  hsec'' := o.hsec
  ho := rfl

end StrongPolyfoldBundle.OrientationRep.Correspondence

namespace StrongBundleLocalizationExamples

open StrongBundleEquivalenceExamples TrivialBundle StrongPolyfoldBundle

variable {k : ℕ} {φ : (Fin 1 → ℝ) → (Fin k → ℝ)}

/-- **Transversality along `W ←1 W →Inv W` over `ℤ/3 × ℝ ⇉ ℝ`** (Definition 15.2.1): for the
graph section `f` of a `C^∞` map and the zero multisection `Λ₀`, `1^* f = Inv^* f` and
`Λ₀(w) = Λ₀(w')` whenever `|[1, Inv]|(|w|) = |w'|`, so `SDiagram.isTransversal_iff_of_pullback_eq`
applies. -/
theorem isTransversal_iff_ofHom_z3InvHom (hφ : ContDiff ℝ ∞ φ) :
    IsTransversal (A := z3SEP k) (graphSection φ) (zeroMultisection (z3SEP k)) ↔
      IsTransversal (A := z3SEP k) (graphSection φ) (zeroMultisection (z3SEP k)) := by
  have hF : (z3SEP k).E.IsScFredholmSectionFunctor (graphSection φ) :=
    isScFredholmSectionFunctor_graphSection_z3 hφ
  have hΛ := isScPlusMultisection_zeroMultisection (z3SEP k)
  refine SDiagram.isTransversal_iff_of_pullback_eq (SDiagram.ofHom (z3InvHom k))
    (z3InvHom_mem_equivalences k) hF hF ?_ hΛ hΛ fun w w' h => hΛ.1.eq_of_π_eq ?_
  · funext x
    have h1 := (SDiagram.ofHom (z3InvHom k)).hΦ.obj_pullback hF.1.1.1 x
    have h2 := (sbe (z3InvHom_mem_equivalences k)).obj_pullback hF.1.1.1 x
    exact h1.trans h2.symm
  · rwa [orbitMap_ofHom_z3InvHom, SDiagram.orbitMap_id'] at h

/-- **The fibres of `ℤ/3 × ℝ ⇉ ℝ` are non-zero and the transversality hypothesis is met**: the
graph section of `x ↦ x² − 1` is transversal to `Λ₀`, so both sides of
`isTransversal_iff_ofHom_z3InvHom` hold. -/
theorem isTransversal_ofHom_z3InvHom_twoPoint :
    (∀ y : (z3SEP 1).Obj, Nontrivial ((z3SEP 1).P ⁻¹' {y})) ∧
      IsTransversal (A := z3SEP 1) (graphSection twoPointMap) (zeroMultisection (z3SEP 1)) :=
  ⟨theorem_16_6_6_index_zero_hypotheses_z3.2.1,
    (isTransversal_iff_ofHom_z3InvHom contDiff_twoPointMap).1
      (isTransversal_graphSection_z3 contDiff_twoPointMap fun _ h =>
        surjective_fderiv_twoPointMap h)⟩

end StrongBundleLocalizationExamples

namespace TrivialBundle

open StrongPolyfoldBundle OrientationRep

/-- **§16.6 for the circle section over `|ℝ²|` and the identity correspondence**: `Z` admits
sc-smooth partitions of unity, `∂Z = ∅`, and the model of `circleOrientationRep` is tame with
index `1` on `X_∞`, so `isInheritedFrom_iff_of_correspondence` applies given `MiddleCanonical`
in both directions. -/
theorem isInheritedFrom_iff_circle
    (hT : (Correspondence.refl circleOrientationRep).MiddleCanonical 0)
    (hT' : (Correspondence.refl circleOrientationRep).symm.MiddleCanonical 0)
    (Q : OrientedPerturbation circleFredholmSection.1 0) :
    IsInheritedFrom (fun o P => IsCanonicalPerturbation o.hF.2 o.hsec o.o P)
        circleOrientationRep Q ↔
      IsInheritedFrom (fun o P => IsCanonicalPerturbation o.hF.2 o.hsec o.o P)
        circleOrientationRep Q :=
  isInheritedFrom_iff_of_correspondence circlePolyfoldBundle_admitsScPartitionsOfUnity
    circlePolyfoldBundle_boundary_eq_empty (Correspondence.refl circleOrientationRep)
    canonicalInput_circleOrientationRep.tame canonicalInput_circleOrientationRep.tame
    canonicalInput_circleOrientationRep.index canonicalInput_circleOrientationRep.index hT hT' Q

end TrivialBundle

end Polyfold
