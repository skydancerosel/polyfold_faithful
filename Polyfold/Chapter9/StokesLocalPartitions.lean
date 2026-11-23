import Polyfold.Chapter9.LocalPartitionsConstruction
import Polyfold.Chapter9.LocalFormsSystem
import Polyfold.Chapter9.StokesLocalForms

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021; 2017 arXiv 1707.08941),
Part II, Chapter 9, §9.5, **Theorems 9.5.17 and 9.5.18 (Stokes), pp. 449–451, and Remark 9.5.19,
p. 451**, point G.153.  Numbers and pages are the 2021 text's.

# Stokes' theorem with partitions of unity near `supp Θ` only (`m ≥ 1`)

Remark 9.5.19 says that the sc-smooth partitions of unity of Theorems 9.5.17 and 9.5.18 are
very likely not needed.  Here the two theorems are proved for every ep-groupoid, for
`n = m + 1 ≥ 2`: the partition of unity is built near the compact `supp Θ`
(`EP.hasLocalPartitions`), the pieces `β_k ω` are forms near `supp Θ`
(`EP.LocalPartition.nonempty_localFormSystem`), and the proof on p. 451 is run with them
(`EP.stokes_of_localFormSystems`).
-/

set_option maxSynthPendingDepth 3

open Set Function MeasureTheory

noncomputable section

namespace Polyfold

universe u

namespace EP

open EpGroupoid

variable (A : EP.{u}) {m : ℕ} {Θ : A.Obj → ℚ} {T : A.Obj → A.X.PObj.OrTangent →₀ ℚ}

/-- **Theorem 9.5.17 (Stokes), 2021 p. 449, with no sc-smooth partitions of unity on `X`**
(Remark 9.5.19, p. 451), `m ≥ 1`: `∫_Θ̂ dω = μ^{∂Θ̂}_ω(∂S)`. -/
theorem theorem_9_5_17_all (hm : 0 < m) (hΘ : A.X.IsBranchedEpSubgroupoid Θ)
    (hcpt : A.X.IsCompactBranched Θ) (hT : A.X.IsOrientation Θ T)
    (hloc : ∀ x ∈ supp Θ, ∃ C : A.X.OrientedTameStructure (m + 1) Θ x, C.Represents T)
    (ω : A.epFormsInfty m) :
    (A.epFormsInftyEval (m + 1)).tameBranchedIntegral (Nat.succ_pos m) hΘ hcpt hT hloc
        (A.epFormsInftyD m ω) =
      A.boundaryMeasure hm hΘ hcpt hT hloc ω univ :=
  A.stokes_of_localFormSystems hm hΘ hcpt hT hloc ω fun N hN =>
    (A.hasLocalPartitions Θ hΘ hcpt N hN).elim fun L => L.nonempty_localFormSystem hm hΘ hcpt ω

/-- **Theorem 9.5.18 (effective Stokes), 2021 p. 450, with no sc-smooth partitions of unity on
`X`** (Remark 9.5.19, p. 451), `m ≥ 1`: `∮_Θ̂ dω = μ^{∂Θ̂,eff}_ω(∂S)`. -/
theorem theorem_9_5_18_all (hm : 0 < m) (hLUC : A.X.IsLUC) (hΘ : A.X.IsBranchedEpSubgroupoid Θ)
    (hcpt : A.X.IsCompactBranched Θ) (hT : A.X.IsOrientation Θ T)
    (hloc : ∀ x ∈ supp Θ, ∃ C : A.X.OrientedTameStructure (m + 1) Θ x, C.Represents T)
    (ω : A.epFormsInfty m) :
    (A.epFormsInftyEval (m + 1)).tameBranchedIntegralEff (Nat.succ_pos m) hΘ hcpt hT
        (A.hloc_hasLUC hLUC hloc) (A.epFormsInftyD m ω) =
      A.boundaryMeasureEff hm hLUC hΘ hcpt hT hloc ω univ :=
  A.stokesEff_of_localFormSystems hm hLUC hΘ hcpt hT hloc ω fun N hN =>
    (A.hasLocalPartitions Θ hΘ hcpt N hN).elim fun L => L.nonempty_localFormSystem hm hΘ hcpt ω

end EP

end Polyfold
