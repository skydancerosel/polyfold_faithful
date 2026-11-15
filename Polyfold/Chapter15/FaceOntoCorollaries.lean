import Polyfold.Chapter15.TransversalExtensionCorollaries
import Polyfold.Chapter15.CylinderFaceOnto

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), **Corollary 15.3.10 (3)**
(p. 699) and **Corollary 15.4.4** (p. 703) with the face condition of the glued data proved.

# Corollaries 15.3.10 (3) and 15.4.4 on the cylinder

## What is formalized (namespace `Polyfold.SBLocalization`)

* **`corollary_15_3_10_3_regular`**: Corollary 15.3.10 (3): two regular perturbations
  `(N₀, U₀, Λ₀)`, `(N₁, U₁, Λ₁)` are joined by a regular perturbation of `f̃` over `[0, 1] × X`
  that is `Λᵢ` over `{i} × X`, with compact branched solution set.  The face condition of the
  glued data is `isBoundaryFaceOnto_cubeGlue` (the transversality of `(f, Λᵢ)` is part of
  regularity).  Added hypothesis: sc-smooth partitions of unity on the object M-polyfold of `X`.
* **`corollary_15_4_4_of_or`**, **`corollary_15_4_4_eff_of_or`**: Corollary 15.4.4 along the
  text's argument and its effective version; left: step (c) (`hor`, the oriented end identities
  of the cylinder).
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

/-- **Corollary 15.3.10 (3) (2017: Corollary 15.1 (3)), p. 699**: for `d_X ≡ 0`, paracompact
`|X|`, sc-smooth partitions of unity on the object M-polyfold, `f` sc-Fredholm with tame germ data
and compact `|S_f|`, and regular perturbations `(Nᵢ, Uᵢ, Λᵢ)`, `i = 0, 1`, there is a regular
perturbation of `f̃` over `[0, 1] × X` that agrees with `Λᵢ` over `{i} × X`; its solution set is a
compact branched ep⁺-subgroupoid. -/
theorem corollary_15_3_10_3_regular
    (hd : ∀ x, A.X.PObj.degIndex x = 0) (hpara : A.X.HasParacompactOrbitSpace)
    (hPU : A.X.PObj.AdmitsScPartitionsOfUnity) {f : A.Obj → A.W}
    (hf : A.E.IsScFredholmSectionFunctor f) (hft : A.B.IsScFredholmSectionTame f)
    (hS : A.E.HasCompactSolutionSetEp f) {N₀ N₁ : A.B.One → ℝ} {U₀ U₁ : Set A.Obj}
    {Λ₀ Λ₁ : A.W → ℚ≥0} (hr₀ : IsRegularPerturbation A f N₀ U₀ Λ₀)
    (hr₁ : IsRegularPerturbation A f N₁ U₁ Λ₁) :
    ∃ Λ' : (A.cubeSEP 1).W → ℚ≥0,
      IsRegularPerturbation (A.cubeSEP 1) (cubeLiftEp (n := 1) f hf.1.1.1)
        (interpAuxNorm A N₀ N₁) (interpSet A U₀ U₁) Λ' ∧
      (∀ w, ((cubeVal w).1.1 0 : ℝ) = 0 → Λ' w = Λ₀ (cubeVal w).2) ∧
      (∀ w, ((cubeVal w).1.1 0 : ℝ) = 1 → Λ' w = Λ₁ (cubeVal w).2) ∧
      (A.cubeSEP 1).X.IsBranchedEpSubgroupoid
        (fun z => (Λ' (cubeLiftEp (n := 1) f hf.1.1.1 z) : ℚ)) ∧
      (A.cubeSEP 1).X.IsCompactBranched
        (fun z => (Λ' (cubeLiftEp (n := 1) f hf.1.1.1 z) : ℚ)) :=
  corollary_15_3_10_3_of_onto hd hpara hPU hf hft hS hr₀ hr₁
    (isBoundaryFaceOnto_cubeGlue hd hf hft hr₀.2.2.2.2 hr₁.2.2.2.2)

/-- **Corollary 15.4.4 (2017: Corollary 15.2), p. 703, along the text's argument**: for
`d_X ≡ 0`, `|X|` paracompact, sc-smooth partitions of unity on the object M-polyfold, `f`
sc-Fredholm with tame germ data and compact `|S_f|`, and a predicate `Can`, `Φ_{(f,o)}` is well
defined in degree `m + 1` given step (c) of the proof (`hor`). -/
theorem corollary_15_4_4_of_or
    (hd : ∀ x, A.X.PObj.degIndex x = 0) (hpara : A.X.HasParacompactOrbitSpace)
    (hPUX : A.X.PObj.AdmitsScPartitionsOfUnity)
    {f : A.Obj → A.W} (hf : A.E.IsScFredholmSectionFunctor f)
    (hft : A.B.IsScFredholmSectionTame f) (hS : A.E.HasCompactSolutionSetEp f) {m : ℕ}
    (Can : OrientedRegularPerturbation A f m → Prop)
    (hor : ∀ P₀ P₁, Can P₀ → Can P₁ → CylinderOrientationStatement hf.1.1.1 P₀ P₁) :
    corollary_15_4_4_statement A f m Can :=
  corollary_15_4_4_of_onto_or hd hpara hPUX hf hft hS Can
    (fun P₀ P₁ _ _ => isBoundaryFaceOnto_cubeGlue hd hf hft P₀.isRegular.2.2.2.2
      P₁.isRegular.2.2.2.2) hor

/-- **Corollary 15.4.4, effective version, p. 703, along the text's argument**, for `X` with the
local unique continuation property: as `corollary_15_4_4_of_or`, with the effective form of
step (c) (`hor`). -/
theorem corollary_15_4_4_eff_of_or
    (hd : ∀ x, A.X.PObj.degIndex x = 0) (hpara : A.X.HasParacompactOrbitSpace)
    (hPUX : A.X.PObj.AdmitsScPartitionsOfUnity) (hLUC : A.X.IsLUC)
    {f : A.Obj → A.W} (hf : A.E.IsScFredholmSectionFunctor f)
    (hft : A.B.IsScFredholmSectionTame f) (hS : A.E.HasCompactSolutionSetEp f) {m : ℕ}
    (Can : OrientedRegularPerturbation A f m → Prop)
    (hor : ∀ P₀ P₁, Can P₀ → Can P₁ →
      CylinderOrientationEffStatement hf.1.1.1 hLUC (isLUC_cubeSEP hLUC) P₀ P₁) :
    corollary_15_4_4_eff_statement A f m hLUC Can :=
  corollary_15_4_4_eff_of_onto_or hd hpara hPUX hLUC hf hft hS Can
    (fun P₀ P₁ _ _ => isBoundaryFaceOnto_cubeGlue hd hf hft P₀.isRegular.2.2.2.2
      P₁.isRegular.2.2.2.2) hor

end SBLocalization

end Polyfold
