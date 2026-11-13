import Polyfold.Chapter9.Basic
import Polyfold.Chapter7.OrbitTopology

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part II, Chapter 9,
§9.1, **Remark 9.1.4** (p. 403, new in the 2021 edition).

# Paracompact subsets of `|X|` are metrizable; the compactness criterion

## The text, paraphrased

(Remark 9.1.4) `|X|` is locally metrizable, regular and Hausdorff (Theorem 7.3.1), so a
paracompact `L ⊆ |X|` is metrizable (Smirnov).  By Corollary 7.3.8 a `K ⊆ |X|` meeting every
connected component of `|X|` in a compact set has a paracompact open neighbourhood in `|X|`;
hence the paracompactness of `|supp(Θ)|` in Definition 9.1.2 (1) is automatic when
`|supp(Θ)|` is component compact.

## What is formalized

* `EpGroupoid.remark_9_1_4_metrizable`: a paracompact `L ⊆ |X|` is metrizable (Chapter 7's
  `metrizableSpace_of_paracompactSpace_subtype`).
* `EpGroupoid.remark_9_1_4_exists_nhds`: a component compact `K` has an open neighbourhood `U`
  with `U` paracompact (and metrizable), from `corollary_7_3_8`.
* `EpGroupoid.remark_9_1_4_paracompactSpace`: a component compact `K` is itself paracompact (and
  metrizable): it lies in the metrizable `U`.
* **`EpGroupoid.remark_9_1_4`** (the consequence for Definition 9.1.2): if `|supp(Θ)|` is
  component compact, `|supp(Θ)|` is paracompact, and `isBranchedEpSubgroupoid_of_isComponentCompact`
  builds `IsBranchedEpSubgroupoid Θ` from the other conditions of Definition 9.1.2.
* `EpGroupoid.paracompactSpace_orbitSupp_of_isCompact`: the compact case (Remark 9.1.10's
  example, and Definition 9.1.6 (2)).

## How it relates to the text

Exactly the text's argument; "the paracompactness is automatic" is read as the implication
"component compact ⇒ paracompact" for the subspace `|supp(Θ)| ⊆ |X|`.  The step from the
paracompact neighbourhood `U` to `K ⊆ U` (a subspace of a paracompact space need not be
paracompact) goes through metrizability of `U`, which Corollary 7.3.8 provides.
-/

open Set Function Topology TopologicalSpace

noncomputable section

namespace Polyfold

universe u

namespace EpGroupoid

variable {Obj Mor : Type u} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] (X : EpGroupoid Obj Mor)

/-- **2021 Remark 9.1.4**, p. 403, first part: a paracompact subset `L ⊆ |X|` (with the induced
topology) is metrizable (Theorem 7.3.1 and Smirnov's theorem). -/
theorem remark_9_1_4_metrizable (L : Set X.OrbitSpace) [ParacompactSpace L] :
    MetrizableSpace L :=
  X.metrizableSpace_of_paracompactSpace_subtype L

/-- **2021 Remark 9.1.4**, p. 403, second part: a component compact `K ⊆ |X|` admits an open
neighbourhood `U` in `|X|` which is paracompact (and metrizable) (Corollary 7.3.8). -/
theorem remark_9_1_4_exists_nhds {K : Set X.OrbitSpace} (hK : X.IsComponentCompact K) :
    ∃ U : Set X.OrbitSpace, IsOpen U ∧ K ⊆ U ∧ ParacompactSpace U ∧ MetrizableSpace U := by
  obtain ⟨U, hUo, hKU, -, -, hUm⟩ := X.corollary_7_3_8 hK
  exact ⟨U, hUo, hKU, paracompactSpace_of_metrizableSpace U, hUm⟩

/-- A component compact `K ⊆ |X|` is metrizable, as a subspace of the metrizable neighbourhood of
Remark 9.1.4. -/
theorem metrizableSpace_of_isComponentCompact {K : Set X.OrbitSpace}
    (hK : X.IsComponentCompact K) : MetrizableSpace K := by
  obtain ⟨U, -, hKU, -, hUm⟩ := X.remark_9_1_4_exists_nhds hK
  exact (IsEmbedding.inclusion hKU).metrizableSpace

/-- A component compact `K ⊆ |X|` is paracompact. -/
theorem remark_9_1_4_paracompactSpace {K : Set X.OrbitSpace} (hK : X.IsComponentCompact K) :
    ParacompactSpace K :=
  have := X.metrizableSpace_of_isComponentCompact hK
  paracompactSpace_of_metrizableSpace K

/-- **2021 Remark 9.1.4**, p. 403, the consequence: if `|supp(Θ)|` meets every connected component
of `|X|` in a compact set, then `|supp(Θ)|` is paracompact (the second condition of
Definition 9.1.2 (1) is automatic). -/
theorem remark_9_1_4 {Θ : Obj → ℚ} (h : X.IsComponentCompact (X.orbitSupp Θ)) :
    ParacompactSpace (X.orbitSupp Θ) :=
  X.remark_9_1_4_paracompactSpace h

/-- Definition 9.1.2 with its paracompactness condition replaced by component compactness of
`|supp(Θ)|` (Remark 9.1.4). -/
theorem isBranchedEpSubgroupoid_of_isComponentCompact {Θ : Obj → ℚ} (hnn : ∀ x, 0 ≤ Θ x)
    (hf : X.IsFunctorial Θ) (hs : supp Θ ⊆ X.PObj.smoothSet)
    (hK : X.IsComponentCompact (X.orbitSupp Θ))
    (hb : ∀ x ∈ supp Θ, Nonempty (X.LocalBranchingStructure Θ x)) :
    X.IsBranchedEpSubgroupoid Θ :=
  ⟨hnn, hf, hs, X.remark_9_1_4 hK, hb⟩

/-- A compact subset of `|X|` is component compact. -/
theorem isComponentCompact_of_isCompact {K : Set X.OrbitSpace} (hK : IsCompact K) :
    X.IsComponentCompact K :=
  fun _ => hK.inter_right isClosed_connectedComponent

/-- **The compact case** (Remark 9.1.10's example): if `|supp(Θ)|` is compact, it is paracompact
and metrizable. -/
theorem paracompactSpace_orbitSupp_of_isCompact {Θ : Obj → ℚ} (h : IsCompact (X.orbitSupp Θ)) :
    ParacompactSpace (X.orbitSupp Θ) ∧ MetrizableSpace (X.orbitSupp Θ) :=
  ⟨X.remark_9_1_4 (X.isComponentCompact_of_isCompact h),
    X.metrizableSpace_of_isComponentCompact (X.isComponentCompact_of_isCompact h)⟩

end EpGroupoid

end Polyfold
