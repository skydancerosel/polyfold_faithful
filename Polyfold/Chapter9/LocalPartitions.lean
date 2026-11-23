import Polyfold.Chapter7.PartitionsOfUnity
import Polyfold.Chapter9.Basic

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021; 2017 arXiv 1707.08941),
Part II, Chapter 9, §9.5, **Remark 9.5.19, 2021 p. 451** (2017: Remark 9.8), point G.153.
Numbers and pages are the 2021 text's.

# Partitions of unity near a compact branched ep⁺-subgroupoid

## The text, paraphrased

Theorems 9.5.17 and 9.5.18 assume that `X` admits sc-smooth partitions of unity.  Remark 9.5.19
says that the assumption is very likely not needed: it suffices to have partitions of unity on
`supp Θ`, and `supp Θ` is compact in the orbit space.

## What is formalized

* `EP.LocalPartition A Θ N`: a saturated open neighbourhood `W` of `supp Θ`, finitely many points
  `x_k ∈ supp Θ` and functions `β_k`, sc-smooth on `W` and constant on the orbits in `W`, with
  `supp β_k ⊆ N(x_k)^*` in `W` and `∑ β_k = 1` on `W`; and a continuous function `χ`, constant on
  the orbits, equal to `1` near `supp Θ` and with support in `W`.
* `EP.HasLocalPartitions A`: every compact branched ep⁺-subgroupoid `Θ` and every choice of open
  neighbourhoods `N(x)` of the points of `supp Θ` has such a partition.
-/

set_option maxSynthPendingDepth 3

open Set Function Filter Topology

noncomputable section

namespace Polyfold

universe u

open MPolyfold EpGroupoid

namespace EP

variable (A : EP.{u})

/-- **A partition of unity near `supp Θ`** (Remark 9.5.19, 2021 p. 451), subordinate to the
saturations of the open sets `N(x)`, `x ∈ supp Θ`: a saturated open `W ⊇ supp Θ`, finitely many
`x_k ∈ supp Θ`, functions `β_k` sc-smooth on `W`, constant on the orbits in `W`, with
`W ∩ cl {β_k ≠ 0} ⊆ N(x_k)^*` and `∑ β_k = 1` on `W`; and a continuous `χ`, constant on the
orbits, with `χ = 1` near `supp Θ` and `supp χ ⊆ W`. -/
structure LocalPartition (Θ : A.Obj → ℚ) (N : A.Obj → Set A.Obj) where
  /-- The saturated open neighbourhood of `supp Θ`. -/
  W : Set A.Obj
  isOpen_W : IsOpen W
  isSaturated_W : A.X.IsSaturated W
  supp_subset_W : supp Θ ⊆ W
  /-- The finite index set. -/
  κ : Type u
  [fintype : Fintype κ]
  /-- The points `x_k`. -/
  pt : κ → A.Obj
  pt_mem : ∀ k, pt k ∈ supp Θ
  /-- The functions `β_k`. -/
  β : κ → A.Obj → ℝ
  isScSmoothOn_β : ∀ k, A.X.PObj.IsScSmoothOn realPolyfold (β k) W
  β_src_eq_tgt : ∀ k (φ : A.Mor), A.X.src φ ∈ W → β k (A.X.src φ) = β k (A.X.tgt φ)
  closure_subset : ∀ k, W ∩ closure (W ∩ {y | β k y ≠ 0}) ⊆ A.X.π ⁻¹' (A.X.π '' N (pt k))
  sum_β : ∀ y ∈ W, ∑ k, β k y = 1
  /-- The continuous cut-off. -/
  χ : A.Obj → ℝ
  continuous_χ : Continuous χ
  χ_src_eq_tgt : ∀ φ : A.Mor, χ (A.X.src φ) = χ (A.X.tgt φ)
  χ_eventually_eq_one : ∀ y ∈ supp Θ, ∀ᶠ z in 𝓝 y, χ z = 1
  tsupport_χ_subset : tsupport χ ⊆ W

attribute [instance] LocalPartition.fintype

/-- **Partitions of unity near the compact branched ep⁺-subgroupoids** (Remark 9.5.19, 2021
p. 451): for every compact branched ep⁺-subgroupoid `Θ` and open neighbourhoods `N(x)` of the
points `x ∈ supp Θ` there is a partition of unity near `supp Θ` subordinate to the `N(x)^*`. -/
def HasLocalPartitions : Prop :=
  ∀ (Θ : A.Obj → ℚ), A.X.IsBranchedEpSubgroupoid Θ → A.X.IsCompactBranched Θ →
    ∀ N : A.Obj → Set A.Obj, (∀ x ∈ supp Θ, IsOpen (N x) ∧ x ∈ N x) →
      Nonempty (A.LocalPartition Θ N)

end EP

end Polyfold
