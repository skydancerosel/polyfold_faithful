import Polyfold.Chapter15.CylinderCobordism
import Polyfold.Chapter15.CubeLiftScPlus
import Polyfold.Chapter15.CubeLUC

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), **Corollary 15.4.4**
(p. 703) along the text's argument through the cylinder `[0, 1] × X`, with the structurability
of the glued data, partitions of unity and the local unique continuation property on the cylinder
proved.

# Corollary 15.4.4: the reduced cylinder forms

## What is formalized (namespace `Polyfold.SBLocalization`)

* **`corollary_15_4_4_of_rel_onto`**: `corollary_15_4_4_of_rel` with the structurability half of
  `hglue` discharged (`isBoundaryStructurable_cubeGlue`: the perturbations are structurable), and
  the partitions of unity on `X` and on `[0, 1] × X` both obtained from those of the object
  M-polyfold of `X` (`hPUX`, with `|X|` paracompact; Theorem 7.5.7 and
  `admitsScPartitionsOfUnity_cubeSEP`), with the relative step on the cylinder (`hrelC`), the
  face condition of the glued data (`honto`) and step (c) (`hor`) as hypotheses.  The face
  condition holds for transversal pairs (`isBoundaryFaceOnto_cubeGlue`, Chapter15/CylinderFaceOnto)
  and the relative step is `theorem_15_3_7_relative`; `corollary_15_4_4_of_or`
  (Chapter15/FaceOntoCorollaries) is the form with only `hor` left.
* **`corollary_15_4_4_eff_of_rel_onto`**: the effective version (p. 703), likewise, with the
  local unique continuation property of `[0, 1] × X` derived from that of `X`
  (`EpGroupoid.isLUC_cubeProd`), so the hypothesis `hLUCC` of
  `corollary_15_4_4_eff_cylinder_hyp` is gone, and with Theorem 15.3.9 on the cylinder and its
  tame strong bundle charts obtained as in `corollary_15_4_4_of_rel`.
-/

set_option maxSynthPendingDepth 3
set_option linter.unusedSectionVars false

open Set Function Topology Filter

noncomputable section

namespace Polyfold

universe u

namespace SBLocalization

open StrongBundle StrongRetr MPolyfold EpGroupoid SEP OrientedRegularPerturbation

variable {A : SEP.{u}}

/-- **The local unique continuation property of the cylinder** `[0, 1] × X` (the object
ep-groupoid of `A.cubeSEP 1`) from that of `X`. -/
theorem isLUC_cubeSEP (hLUC : A.X.IsLUC) : (A.cubeSEP 1).X.IsLUC := by
  have := MPolyfold.paracompactSpace_prod (cubePolyfold 1) A.X.PObj
  have := MPolyfold.paracompactSpace_prod (cubePolyfold 1) A.X.PMor
  exact A.X.isLUC_cubeProd 1 hLUC

/-- **Corollary 15.4.4 (2017: Corollary 15.2), p. 703, along the text's argument, with the glued
data structurable and the partitions of unity from `X`**: for `d_X ≡ 0`, `|X|` paracompact, the
object M-polyfold of `X` with sc-smooth partitions of unity (`hPUX`), `f` sc-Fredholm with tame
germ data and compact `|S_f|`, and a predicate `Can`, `Φ_{(f,o)}` is well defined in degree
`m + 1` given the relative step on `[0, 1] × X` (`hrelC`), the face condition of the glued data
of any two `Can`-perturbations (`honto`) and step (c) (`hor`). -/
theorem corollary_15_4_4_of_rel_onto
    (hrelC : theorem_15_3_7_relative_statement (A.cubeSEP 1))
    (hd : ∀ x, A.X.PObj.degIndex x = 0) (hpara : A.X.HasParacompactOrbitSpace)
    (hPUX : A.X.PObj.AdmitsScPartitionsOfUnity)
    {f : A.Obj → A.W} (hf : A.E.IsScFredholmSectionFunctor f)
    (hft : A.B.IsScFredholmSectionTame f) (hS : A.E.HasCompactSolutionSetEp f) {m : ℕ}
    (Can : OrientedRegularPerturbation A f m → Prop)
    (honto : ∀ P₀ P₁, Can P₀ → Can P₁ →
      IsBoundaryFaceOnto (cubeLiftEp (n := 1) f hf.1.1.1) (cubeGlue P₀.Λ P₁.Λ))
    (hor : ∀ P₀ P₁, Can P₀ → Can P₁ → CylinderOrientationStatement hf.1.1.1 P₀ P₁) :
    corollary_15_4_4_statement A f m Can :=
  corollary_15_4_4_of_rel hrelC hd hpara (A.X.theorem_7_5_7 hpara hPUX)
    (admitsScPartitionsOfUnity_cubeSEP 1 hPUX) hf hft hS Can
    (fun P₀ P₁ h₀ h₁ => ⟨isBoundaryStructurable_cubeGlue hd hpara P₀.isRegular.2.1
      P₁.isRegular.2.1, honto P₀ P₁ h₀ h₁⟩) hor

/-- **Corollary 15.4.4, effective version, p. 703, along the text's argument**, for `X` with the
local unique continuation property: as `corollary_15_4_4_of_rel_onto`, with the effective form of
step (c) (`hor`), whose LUC datum on `[0, 1] × X` is `isLUC_cubeSEP hLUC`. -/
theorem corollary_15_4_4_eff_of_rel_onto
    (hrelC : theorem_15_3_7_relative_statement (A.cubeSEP 1))
    (hd : ∀ x, A.X.PObj.degIndex x = 0) (hpara : A.X.HasParacompactOrbitSpace)
    (hPUX : A.X.PObj.AdmitsScPartitionsOfUnity) (hLUC : A.X.IsLUC)
    {f : A.Obj → A.W} (hf : A.E.IsScFredholmSectionFunctor f)
    (hft : A.B.IsScFredholmSectionTame f) (hS : A.E.HasCompactSolutionSetEp f) {m : ℕ}
    (Can : OrientedRegularPerturbation A f m → Prop)
    (honto : ∀ P₀ P₁, Can P₀ → Can P₁ →
      IsBoundaryFaceOnto (cubeLiftEp (n := 1) f hf.1.1.1) (cubeGlue P₀.Λ P₁.Λ))
    (hor : ∀ P₀ P₁, Can P₀ → Can P₁ →
      CylinderOrientationEffStatement hf.1.1.1 hLUC (isLUC_cubeSEP hLUC) P₀ P₁) :
    corollary_15_4_4_eff_statement A f m hLUC Can := by
  have := MPolyfold.paracompactSpace_prod (cubePolyfold 1) A.X.PObj
  have := MPolyfold.paracompactSpace_prod (cubePolyfold 1) A.X.PMor
  have hXC : (A.cubeSEP 1).X.IsTame :=
    A.X.isTame_cubeProd 1 (A.X.isTame_of_degIndex_eq_zero hd)
  exact corollary_15_4_4_eff_cylinder_hyp (theorem_15_3_9_charged_hyp hrelC)
    ((A.cubeSEP 1).exists_isTameChart hXC) hd hpara (A.X.theorem_7_5_7 hpara hPUX) hLUC
    (admitsScPartitionsOfUnity_cubeSEP 1 hPUX) (isLUC_cubeSEP hLUC) hf hft hS Can
    (fun P₀ P₁ h₀ h₁ => ⟨isBoundaryStructurable_cubeGlue hd hpara P₀.isRegular.2.1
      P₁.isRegular.2.1, honto P₀ P₁ h₀ h₁⟩) hor

end SBLocalization

end Polyfold
