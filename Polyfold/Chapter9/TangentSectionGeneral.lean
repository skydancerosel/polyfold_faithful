import Polyfold.Chapter9.GeneralCorollaries

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), §9.2, pp. 409–410:
**Theorem 9.2.1** (2017: Theorem 9.1, p. 298) for every branched ep⁺-subgroupoid.

# Theorem 9.2.1 without the independence hypothesis

## The text, paraphrased

(Theorem 9.2.1) For a branched ep⁺-subgroupoid `Θ` the section functor `TΘ : X_∞ → Gr(X)`
satisfies `π ∘ TΘ = Id`, (1) `TΘ(x) = ∑ σᵢ · T_xMᵢ` for any local branching structure at
`x ∈ supp(Θ)`, and (2) `TΘ(φ) = (TΘ(s φ), φ)`.

## What is formalized

* **`EpGroupoid.theorem_9_2_1_general`**: `EpGroupoid.theorem_9_2_1` with its hypothesis
  `HasIndependentTangentSums Θ` discharged by `EpGroupoid.hasIndependentTangentSums` (the
  independence in (1), proved for every ep-groupoid and every `Θ`).
-/

open CategoryTheory

noncomputable section

namespace Polyfold

universe u

namespace EpGroupoid

variable {Obj Mor : Type u} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] {X : EpGroupoid Obj Mor}

/-- **2021 Theorem 9.2.1, p. 409 (2017: Theorem 9.1, p. 298), for every branched
ep⁺-subgroupoid**: the section functor `TΘ : X_∞ → Gr(X)` (built with the independence of the
tangent sums, `hasIndependentTangentSums`) satisfies `π ∘ TΘ = Id_{X_∞}`, (1)
`TΘ(x) = ∑ σᵢ · T_xMᵢ` for any local branching structure at `x ∈ supp(Θ)`, the zero-sum for
`x ∉ supp(Θ)`, and (2) `TΘ(φ) = (TΘ(s φ), φ)`. -/
theorem theorem_9_2_1_general {Θ : Obj → ℚ} (hΘ : X.IsBranchedEpSubgroupoid Θ) :
    X.tangentSection hΘ (X.hasIndependentTangentSums Θ) ⋙ X.grProj = 𝟭 X.SmoothCat ∧
      (∀ (x : X.SmoothCat), x.pt ∈ supp Θ → ∀ B : X.LocalBranchingStructure Θ x.pt,
        ((X.tangentSection hΘ (X.hasIndependentTangentSums Θ)).obj x).sum =
          ∑ i, Finsupp.single (X.PObj.submanifoldTangent (B.M i) x.pt) (B.σ i)) ∧
      (∀ (x : X.SmoothCat), x.pt ∉ supp Θ →
        ((X.tangentSection hΘ (X.hasIndependentTangentSums Θ)).obj x).sum = 0) ∧
      (∀ {x y : X.SmoothCat} (f : x ⟶ y),
        ((X.tangentSection hΘ (X.hasIndependentTangentSums Θ)).obj x).pt =
            X.src (SmoothCat.mor f) ∧
          ((X.tangentSection hΘ (X.hasIndependentTangentSums Θ)).map f).1 =
            SmoothCat.mor f) :=
  X.theorem_9_2_1 hΘ (X.hasIndependentTangentSums Θ)

end EpGroupoid

end Polyfold
