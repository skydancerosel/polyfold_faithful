import Polyfold.Examples.OrbifoldSquareInfStructure
import Polyfold.Examples.OrbifoldSquareInfFredholm
import Polyfold.Examples.OrbifoldSquareInfNorm

/-!
# The orbifold `(ℂ × H)/ℤ₅` and the section `(z, e) ↦ (z², e)`: the sc-Fredholm section

The infinite-dimensional version of the worked example `ℂ/ℤ₅`, `z ↦ z²`, for Hofer–Wysocki–Zehnder,
*Polyfold and Fredholm Theory* (Springer 2021), Theorem 16.6.6, 2021 p. 739.

## What is formalized (namespace `Polyfold.Examples.OrbifoldSquareInf`)

* `infRep`, `infFredholmSection`: the sc-Fredholm section `|(z, e)| ↦ |((z, z²), (e, e))|` of the
  strong polyfold bundle `infBundle` (Definitions 16.3.18, 16.6.1).
* `ninf`, `isAuxNorm_ninf`: the auxiliary norm of `infBundle` (Definition 16.3.9);
  `controlsCompactness_ninf`: `(n, Z)` controls compactness (Definition 16.6.3);
  `hasCompactSolutionSet_infFredholmSection`.
-/

set_option maxSynthPendingDepth 3
set_option linter.unusedSectionVars false

open Set Function Topology Filter

noncomputable section

namespace Polyfold.Examples.OrbifoldSquareInf

open TrivialBundle EpGroupoid.Examples StrongBundle MPolyfold StrongPolyfoldBundle
  StrongPolyfoldBundleStructure WeightedEllTwo OrbifoldSquare SBLocalization

/-- `|f|` is well defined on the orbit space. -/
theorem π_sqInf_eq {x y : Ainf.Obj} (h : Ainf.X.π x = Ainf.X.π y) :
    Ainf.E.toEpGroupoid.π (sqInf x) = Ainf.E.toEpGroupoid.π (sqInf y) := by
  obtain ⟨φ, hs, ht⟩ := (GroupoidStr.π_eq_π_iff _).1 h
  have hf := isScFredholmSectionFunctor_sqInf.1.2 φ
  refine (GroupoidStr.π_eq_π_iff _).2 ⟨⟨(φ, sqInf (Ainf.X.src φ)), rfl⟩, ?_, ?_⟩
  · change sqInf (Ainf.X.src φ) = sqInf x
    rw [hs]
  · change Ainf.E.μ ⟨(φ, sqInf (Ainf.X.src φ)), rfl⟩ = sqInf y
    rw [← ht]
    exact hf.symm

/-- **The representative `(infStructure, f)`** of the section `|(z, e)| ↦ |((z, z²), (e, e))|`
(Definition 16.3.18). -/
def infRep : SectionRep infBundle where
  S := infStructure
  hS := rfl
  F := sqInf
  hF := isScFredholmSectionFunctor_sqInf.1
  f := Quotient.lift (fun x : Ainf.Obj => Ainf.E.toEpGroupoid.π (sqInf x))
    fun _ _ h => π_sqInf_eq (Quotient.sound h)
  continuous_f := Continuous.quotient_lift (Ainf.E.toEpGroupoid.continuous_π.comp
    (continuousOn_univ.1 isScFredholmSectionFunctor_sqInf.1.1.2.continuousOn)) _
  isSection z := Quotient.inductionOn z fun _ => rfl
  comm _ := rfl

/-- **The sc-Fredholm section `|(z, e)| ↦ |((z, z²), (e, e))|`** of `infBundle`
(Definition 16.6.1). -/
def infFredholmSection : FredholmSection infBundle :=
  ⟨⟦infRep⟧, infRep, rfl, isScFredholmSectionFunctor_sqInf⟩

/-- **The auxiliary norm `n` of the strong polyfold bundle** (Definition 16.3.9). -/
def ninf : Ainf.E.toEpGroupoid.OrbitSpace → ℝ := infStructure.descend Ninf

theorem isAuxNorm_ninf : infBundle.IsAuxNorm ninf := isAuxNorm_descend rfl isAuxNorm_Ninf

theorem normOf_ninf : infStructure.normOf ninf = Ninf :=
  infStructure.normOf_descend isAuxNorm_Ninf.isOneInvariant

/-- **`(n, Z)` controls the compactness of the section** (Definition 16.6.3, with `U = Z`). -/
theorem controlsCompactness_ninf :
    infFredholmSection.1.ControlsCompactness ninf (univ : Set Ainf.X.OrbitSpace) := by
  refine (infRep.controlsCompactness_iff isAuxNorm_ninf isOpen_univ).2 ?_
  rw [preimage_univ]
  change ControlsCompactness Ainf sqInf (infStructure.normOf ninf) univ
  rw [normOf_ninf]
  exact controlsCompactness_sqInf_univ

/-- **The solution set is compact**: it is the point `|(0, 0)|`. -/
theorem hasCompactSolutionSet_infFredholmSection :
    infFredholmSection.1.HasCompactSolutionSet := by
  refine infRep.hasCompactSolutionSet_iff.2 ?_
  change IsCompact (Ainf.X.π '' solutionSet Ainf.P sqInf)
  rw [solutionSet_sqInf]
  exact (isCompact_singleton (x := (((0 : Fin 2 → ℝ), h0) : Ainf.Obj))).image
    Ainf.X.continuous_π

end Polyfold.Examples.OrbifoldSquareInf
