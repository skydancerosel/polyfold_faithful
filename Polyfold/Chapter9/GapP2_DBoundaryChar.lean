import Polyfold.Chapter9.GeneralCorollaries

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021; 2017 arXiv 1707.08941),
§9.2, **Definition 9.2.16**, p. 421 (2017: Definition 9.7, p. 309): the boundary `∂Θ`.

# What the properties (1), (2) of Definition 9.2.16 determine

The text calls `∂Θ` "the functor uniquely characterized by" (1) `supp(∂Θ) ⊆ ∂X` and (2) the local
formula on `U(x)` for `x ∈ supp(∂Θ)`.  As printed, (2) is asked only at the points of the support
of the functor, so the zero functor has (1) and (2) too
(`isBoundaryCharacterized_zero`, `not_unique_isBoundaryCharacterized_halfLine`,
`Chapter9/Boundary.lean`).

## What is formalized

* `IsBoundaryCharacterized.eq_boundaryTheta_on`: a function `F` with (1) and (2) agrees with `∂Θ`
  on `U(x)` for every `x ∈ supp(F)` and every local branching structure on `U(x)`.
* `IsBoundaryCharacterized.supp_subset`: for `F ≥ 0` vanishing off `supp(Θ)`,
  `supp(F) ⊆ supp(∂Θ)`.
* `IsBoundaryCharacterized.eq_boundaryTheta_iff`: such an `F` is `∂Θ` iff
  `supp(∂Θ) ⊆ supp(F)`.
* **Definition 9.2.16 in a reading where it holds** (`definition_9_2_16_existsUnique`): among the
  functions `F ≥ 0` vanishing off `supp(Θ)` with (1) and (2), `∂Θ` is the unique one with the
  largest support.  No hypothesis beyond `Θ` being a branched ep⁺-subgroupoid: the independence of
  the tangent sums is a theorem (`hasIndependentTangentSums`).
-/

open Set

universe u

namespace Polyfold

namespace EpGroupoid

variable {Obj Mor : Type u} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] {X : EpGroupoid Obj Mor}
  {Θ F : Obj → ℚ}

/-- **(2) of Definition 9.2.16 says `F = ∂Θ` on `U(x)`**, for `x ∈ supp(F)` and every local
branching structure of `Θ` on `U(x)`. -/
theorem IsBoundaryCharacterized.eq_boundaryTheta_on (hind : X.HasIndependentTangentSums Θ)
    (h : X.IsBoundaryCharacterized Θ F) {x : Obj} (hx : x ∈ supp F)
    (B : X.LocalBranchingStructure Θ x) {y : Obj} (hy : y ∈ B.U) :
    F y = X.boundaryTheta Θ y := by
  classical
  rw [h.2 x hx B y hy, X.boundaryTheta_eq hind B hy]

/-- A function `F ≥ 0` with (1), (2) that vanishes off `supp(Θ)` has `supp(F) ⊆ supp(∂Θ)`. -/
theorem IsBoundaryCharacterized.supp_subset (hΘ : X.IsBranchedEpSubgroupoid Θ)
    (hind : X.HasIndependentTangentSums Θ) (h : X.IsBoundaryCharacterized Θ F)
    (h0 : ∀ y ∉ supp Θ, F y = 0) : supp F ⊆ supp (X.boundaryTheta Θ) := fun y hy => by
  have hyΘ : y ∈ supp Θ := by
    by_contra hn
    have : 0 < F y := hy
    rw [h0 y hn] at this
    exact lt_irrefl _ this
  obtain ⟨B⟩ := hΘ.localBranching y hyΘ
  change 0 < X.boundaryTheta Θ y
  rw [← h.eq_boundaryTheta_on hind hy B B.mem_U]
  exact hy

/-- **Uniqueness in Definition 9.2.16, for the largest support**: a function `F ≥ 0` vanishing
off `supp(Θ)` with the properties (1), (2) is `∂Θ` iff its support contains `supp(∂Θ)`. -/
theorem IsBoundaryCharacterized.eq_boundaryTheta_iff (hΘ : X.IsBranchedEpSubgroupoid Θ)
    (hind : X.HasIndependentTangentSums Θ) (h : X.IsBoundaryCharacterized Θ F)
    (hF : ∀ y, 0 ≤ F y) (h0 : ∀ y ∉ supp Θ, F y = 0) :
    F = X.boundaryTheta Θ ↔ supp (X.boundaryTheta Θ) ⊆ supp F := by
  refine ⟨fun e => e ▸ subset_rfl, fun hs => funext fun y => ?_⟩
  by_cases hy : y ∈ supp F
  · have hyΘ : y ∈ supp Θ := (X.supp_boundaryTheta_subset Θ (h.supp_subset hΘ hind h0 hy)).2
    obtain ⟨B⟩ := hΘ.localBranching y hyΘ
    exact h.eq_boundaryTheta_on hind hy B B.mem_U
  · have h1 : F y = 0 := le_antisymm (not_lt.1 hy) (hF y)
    have h2 : X.boundaryTheta Θ y = 0 :=
      le_antisymm (not_lt.1 fun hpos => hy (hs hpos)) (X.boundaryTheta_nonneg Θ y)
    rw [h1, h2]

/-- **Definition 9.2.16, 2021 p. 421 (2017: Definition 9.7), in a reading where the
characterization holds**: for a branched ep⁺-subgroupoid `Θ` there is exactly one function
`F : X → ℚ⁺`, vanishing off `supp(Θ)`, with (1) `supp(F) ⊆ ∂X` and (2) the local formula on
`U(x)` for `x ∈ supp(F)`, whose support contains the support of every other such function; it is
`∂Θ`.  (As printed, without "largest support", the zero functor has (1) and (2) too:
`isBoundaryCharacterized_zero`.) -/
theorem definition_9_2_16_existsUnique (hΘ : X.IsBranchedEpSubgroupoid Θ) :
    ∃! F : Obj → ℚ, (X.IsBoundaryCharacterized Θ F ∧ (∀ y, 0 ≤ F y) ∧ ∀ y ∉ supp Θ, F y = 0) ∧
      ∀ G : Obj → ℚ, X.IsBoundaryCharacterized Θ G → (∀ y, 0 ≤ G y) →
        (∀ y ∉ supp Θ, G y = 0) → supp G ⊆ supp F := by
  have hind : X.HasIndependentTangentSums Θ := hasIndependentTangentSums Θ
  have hb : X.IsBoundaryCharacterized Θ (X.boundaryTheta Θ) :=
    isBoundaryCharacterized_boundaryTheta hind
  refine ⟨X.boundaryTheta Θ, ⟨⟨hb, X.boundaryTheta_nonneg Θ,
    fun y hy => boundaryTheta_eq_zero_of_not_mem_supp hy⟩,
    fun G hG _ hG0 => hG.supp_subset hΘ hind hG0⟩, ?_⟩
  rintro F ⟨⟨hF, hFn, hF0⟩, hmax⟩
  exact (hF.eq_boundaryTheta_iff hΘ hind hFn hF0).2
    (hmax _ hb (X.boundaryTheta_nonneg Θ) fun y hy => boundaryTheta_eq_zero_of_not_mem_supp hy)

end EpGroupoid

end Polyfold
