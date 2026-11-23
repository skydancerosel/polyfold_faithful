import Polyfold.Chapter15.CubeLiftScPlus
import Polyfold.Chapter12.ScPlusSectionFunctor

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), §6.6, **Proposition
6.6.3 (4)** (p. 263) and §15.3, **Corollary 15.3.10 (2)** (p. 699).

# Sc⁺-sections through the fibre points of `W̃ → [0, 1] × X`

## The text, paraphrased

(Proposition 6.6.3 (4)) The pull-back of a strong bundle to a product with a parameter space has
sc⁺-sections through its smooth fibre points.  (Corollary 15.3.10 (2)) `W̃ → [0, 1] × X` is the
pull-back of `W → X` along the projection.

## What is formalized (namespace `Polyfold.SBLocalization`)

* **`hasScPlusSectionsThrough_cubeSEP`**: if `W → X` has sc⁺-sections through its smooth fibre
  points (`StrongBundle.HasScPlusSectionsThrough`), so has `W̃ → [0, 1] × X`: the section through
  `((q, x), e)` is the lift `(q', y) ↦ ((q', y), s(y))` of a section `s` through `e`.  No bump
  functions are used.
-/

set_option maxSynthPendingDepth 3
set_option linter.unusedSectionVars false

open Set Function Topology

noncomputable section

namespace Polyfold

universe u

namespace SBLocalization

open StrongBundle MPolyfold EpGroupoid SEP

variable {A : SEP.{u}}

/-- **Sc⁺-sections through the smooth fibre points of `W̃ → [0, 1] × X`** (Proposition 6.6.3
(4), 2021 p. 263; Corollary 15.3.10 (2), p. 699), from those of `W → X`, by lifting. -/
theorem hasScPlusSectionsThrough_cubeSEP (hsec : A.B.HasScPlusSectionsThrough) :
    (A.cubeSEP 1).B.HasScPlusSectionsThrough := by
  have := MPolyfold.paracompactSpace_prod (cubePolyfold 1) A.X.PObj
  have := MPolyfold.paracompactSpace_prod (cubePolyfold 1) A.X.PMor
  intro z hz e he hez
  have := A.B.paracompactSpace_pullback ((cubePolyfold 1).prod A.X.PObj)
    (Prod.snd : (Fin 1 → unitInterval) × A.Obj → A.Obj)
  have hπ : ((cubePolyfold 1).prod A.X.PObj).IsScSmoothMap A.X.PObj
      (Prod.snd : (Fin 1 → unitInterval) × A.Obj → A.Obj) := (A.X.cubeProj 1).isScSmoothMap_obj
  have hx : z.2 ∈ A.X.PObj.smoothSet :=
    mem_iInter.2 fun m => hπ.mapsTo_levelSet m (mem_iInter.1 hz m)
  have he' : (cubeVal e).2 ∈ A.B.toMPolyfold0.smoothSet :=
    mem_iInter.2 fun m => (A.B.isScSmoothMap_pullbackProj' hπ).mapsTo_levelSet m
      (mem_iInter.1 he m)
  have hPe : A.P (cubeVal e).2 = z.2 :=
    (P_cubeVal_snd e).trans (congrArg Prod.snd ((cubeSEP_P A 1 e).symm.trans hez))
  obtain ⟨s, hs, hsx⟩ := hsec z.2 hx (cubeVal e).2 he' hPe
  have hon := isScPlusSectionOn_cubeLiftSec (IsScPlusSectionOn.of_isScPlusSection hs isOpen_univ)
    isOpen_univ
  obtain ⟨hP, G, hG, hGs⟩ := hon
  refine ⟨cubeLiftSec s, ?_, ?_⟩
  · exact StrongBundle.isScPlusSection_of_locally (fun p => P_cubeLiftSec s p) fun y₀ =>
      ⟨_, isOpen_univ.preimage continuous_snd, mem_univ _, G, hGs, fun y hy => hG y hy⟩
  · exact (cubeLiftSec_eq_iff (hs.1 z.2) hez).2 hsx

end SBLocalization

end Polyfold
