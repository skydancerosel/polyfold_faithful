import Polyfold.Chapter9.LocalPartitionsConstruction
import Polyfold.Chapter9.LocalFormsDimOneSystem
import Polyfold.Chapter9.StokesLocalFormsDimOne

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021; 2017 arXiv 1707.08941),
Part II, Chapter 9, §9.5, **Theorems 9.5.17 and 9.5.18 (Stokes), pp. 449–451, and Remark 9.5.19,
p. 451**, point G.153, the case `n = 1`.  Numbers and pages are the 2021 text's.

# Stokes' theorem with partitions of unity near `supp Θ` only (`n = 1`)

Remark 9.5.19 says that the sc-smooth partitions of unity of Theorems 9.5.17 and 9.5.18 are
very likely not needed.  `StokesLocalPartitions.lean` proves the two theorems for every
ep-groupoid when `n ≥ 2`; here is the case `n = 1`, in which `ω` is a function and `∂S` a finite
set of oriented points: the partition of unity is built near the compact `supp Θ`
(`EP.hasLocalPartitions`), the pieces `β_k ω` are functions near `supp Θ`
(`EP.LocalPartition.nonempty_localFormSystemDimOne`), and the proof on p. 451 is run with them
(`EP.stokes_of_localFormSystemsDimOne`).
-/

set_option maxSynthPendingDepth 3

open Set Function MeasureTheory

noncomputable section

namespace Polyfold

universe u

namespace EP

open EpGroupoid

variable (A : EP.{u}) {Θ : A.Obj → ℚ} {T : A.Obj → A.X.PObj.OrTangent →₀ ℚ}

/-- **Theorem 9.5.17 (Stokes), 2021 p. 449, for `n = 1`, with no sc-smooth partitions of unity on
`X`** (Remark 9.5.19, p. 451): `∫_Θ̂ dω = μ^{∂Θ̂}_ω(∂S)` for `ω ∈ Ω⁰_{ep,∞}(X)`. -/
theorem theorem_9_5_17_dim1_all (hΘ : A.X.IsBranchedEpSubgroupoid Θ)
    (hcpt : A.X.IsCompactBranched Θ) (hT : A.X.IsOrientation Θ T)
    (hloc : ∀ x ∈ supp Θ, ∃ C : A.X.OrientedTameStructure (0 + 1) Θ x, C.Represents T)
    (ω : A.epFormsInfty 0) :
    (A.epFormsInftyEval (0 + 1)).tameBranchedIntegral (Nat.succ_pos 0) hΘ hcpt hT hloc
        (A.epFormsInftyD 0 ω) =
      A.boundaryBranchedMeasureDim1 hΘ hcpt hT hloc ω univ :=
  A.stokes_of_localFormSystemsDimOne hΘ hcpt hT hloc ω fun N hN =>
    (A.hasLocalPartitions Θ hΘ hcpt N hN).elim fun L => L.nonempty_localFormSystemDimOne ω

/-- **Theorem 9.5.18 (effective Stokes), 2021 p. 450, for `n = 1`, with no sc-smooth partitions
of unity on `X`** (Remark 9.5.19, p. 451): `∮_Θ̂ dω = μ^{∂Θ̂,eff}_ω(∂S)` for
`ω ∈ Ω⁰_{ep,∞}(X)`, when every point of `supp Θ` has an oriented tame structure describing `T̂Θ`
whose `U(x)` has the local unique continuation property. -/
theorem theorem_9_5_18_dim1_all (hΘ : A.X.IsBranchedEpSubgroupoid Θ)
    (hcpt : A.X.IsCompactBranched Θ) (hT : A.X.IsOrientation Θ T)
    (hloc : ∀ x ∈ supp Θ, ∃ C : A.X.OrientedTameStructure (0 + 1) Θ x,
      C.Represents T ∧ C.rep.HasLUC)
    (ω : A.epFormsInfty 0) :
    (A.epFormsInftyEval (0 + 1)).tameBranchedIntegralEff (Nat.succ_pos 0) hΘ hcpt hT hloc
        (A.epFormsInftyD 0 ω) =
      A.boundaryBranchedMeasureEffDim1 hΘ hcpt hT hloc ω univ :=
  A.stokesEff_of_localFormSystemsDimOne hΘ hcpt hT hloc ω fun N hN =>
    (A.hasLocalPartitions Θ hΘ hcpt N hN).elim fun L => L.nonempty_localFormSystemDimOne ω

end EP

end Polyfold
