import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V9_23

/-! Round trip for V9_23 (Definition 9.2.12, p. 418 of the 2021 book; 2017: Definition 9.6): the
tangent `TΘ : TX → ℚ⁺` is a well-defined branched ep⁺-subgroupoid, `0` over `{Θ = 0}` and
`∑_{h ∈ TMᵢ} σᵢ` over every `U(x)`.

`A` is the conjunction of the types of the thirteen listed theorems (the listed `tangentSubmanifold`,
`tangentTheta`, `TangentBranchingHyp` are definitions, vocabulary shared with `B`), universe
instantiated at `0` where there is one: `tangentTheta_eq` (the local formula, under
`HasIndependentTangentSums Θ`), `sum_tangent_eq_sum_tangent` (independence of the structure, same
hypothesis), `tangentTheta_nonneg`, `isFunctorial_tangentTheta` (under independence),
`isBranchedEpSubgroupoid_tangentTheta` (under independence and `TangentBranchingHyp`),
`isClosed_tangentSubmanifold`, `paracompactSpace_orbitSupp_tangentTheta` (from paracompact `|X|`),
`tangentBranchingHyp_of_isSmoothSubmanifold`,
`isBranchedEpSubgroupoid_tangentTheta_of_isSmoothSubmanifold`,
`LocalBranchingStructure.isSubMPolyfold_tangentSubmanifold`,
`isBranchedEpSubgroupoid_tangentTheta_rn` (over `ℝᵐ`, with paracompact `|X|` and `TMᵢ` smooth
submanifolds), `tangentBranchingHyp_zero`, `isBranchedEpSubgroupoid_tangentTheta_zero`.

* `B` is about the same function `tangentTheta`, with no hypothesis besides `Θ` branched.
  Its (1) is the non-item lemma `tangentTheta_eq_zero`.
* `A_to_B` is not proved: (2) needs `HasIndependentTangentSums Θ` (Theorem 9.2.1 (1), proved in
  the project only over `ℝᵐ`, `hasIndependentTangentSums_rn`, or under the slice hypotheses), and
  (3) needs moreover `TangentBranchingHyp Θ`, of which the project leaves open that the `TMᵢ` are
  smooth (sc⁺) submanifolds of `TX` and derives the paracompactness of `|supp TΘ|` only from
  that of `|X|`.  `A_gives_B_of` proves `B`'s conclusion from `A` under `HasIndependentTangentSums`
  and `TangentBranchingHyp`; `A_gives_B_rn` over `ℝᵐ` under paracompact `|X|` and smooth `TMᵢ`.
* `B_to_A` is not proved: `A` contains Part I / Chapter 8 facts that `B` does not state
  (`TMᵢ` closed in `TU(x)`, `TMᵢ` a sub-M-polyfold of `TX`, paracompactness of `|supp TΘ|` from
  that of `|X|`, the `Θ = 0` instances). -/

namespace RoundTrip.V9_23
open Polyfold Set

/-- The project's statement (universes at `0`). -/
def A : Prop :=
  (type_of% @Polyfold.EpGroupoid.tangentTheta_eq.{0}) ∧
  (type_of% @Polyfold.EpGroupoid.sum_tangent_eq_sum_tangent.{0}) ∧
  (type_of% @Polyfold.EpGroupoid.tangentTheta_nonneg.{0}) ∧
  (type_of% @Polyfold.EpGroupoid.isFunctorial_tangentTheta.{0}) ∧
  (type_of% @Polyfold.EpGroupoid.isBranchedEpSubgroupoid_tangentTheta.{0}) ∧
  (type_of% @Polyfold.EpGroupoid.isClosed_tangentSubmanifold.{0}) ∧
  (type_of% @Polyfold.EpGroupoid.paracompactSpace_orbitSupp_tangentTheta.{0}) ∧
  (type_of% @Polyfold.EpGroupoid.tangentBranchingHyp_of_isSmoothSubmanifold.{0}) ∧
  (type_of% @Polyfold.EpGroupoid.isBranchedEpSubgroupoid_tangentTheta_of_isSmoothSubmanifold.{0}) ∧
  (type_of% @Polyfold.EpGroupoid.LocalBranchingStructure.isSubMPolyfold_tangentSubmanifold.{0}) ∧
  (type_of% @Polyfold.EpGroupoid.isBranchedEpSubgroupoid_tangentTheta_rn) ∧
  (type_of% @Polyfold.EpGroupoid.tangentBranchingHyp_zero.{0}) ∧
  (type_of% @Polyfold.EpGroupoid.isBranchedEpSubgroupoid_tangentTheta_zero.{0})

theorem A_holds : A :=
  ⟨@Polyfold.EpGroupoid.tangentTheta_eq.{0}, @Polyfold.EpGroupoid.sum_tangent_eq_sum_tangent.{0},
    @Polyfold.EpGroupoid.tangentTheta_nonneg.{0},
    @Polyfold.EpGroupoid.isFunctorial_tangentTheta.{0},
    @Polyfold.EpGroupoid.isBranchedEpSubgroupoid_tangentTheta.{0},
    @Polyfold.EpGroupoid.isClosed_tangentSubmanifold.{0},
    @Polyfold.EpGroupoid.paracompactSpace_orbitSupp_tangentTheta.{0},
    @Polyfold.EpGroupoid.tangentBranchingHyp_of_isSmoothSubmanifold.{0},
    @Polyfold.EpGroupoid.isBranchedEpSubgroupoid_tangentTheta_of_isSmoothSubmanifold.{0},
    @Polyfold.EpGroupoid.LocalBranchingStructure.isSubMPolyfold_tangentSubmanifold.{0},
    @Polyfold.EpGroupoid.isBranchedEpSubgroupoid_tangentTheta_rn,
    @Polyfold.EpGroupoid.tangentBranchingHyp_zero.{0},
    @Polyfold.EpGroupoid.isBranchedEpSubgroupoid_tangentTheta_zero.{0}⟩

open Classical in
/-- `B`'s conclusion for one `Θ`. -/
def BConcl {Obj Mor : Type} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
    [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor]
    (X : EpGroupoid Obj Mor) (Θ : Obj → ℚ) : Prop :=
  (∀ h : X.PObj.TangentSpace, Θ (baseB X h) = 0 → X.tangentTheta Θ h = 0) ∧
  (∀ x ∈ EpGroupoid.supp Θ, ∀ (B : X.LocalBranchingStructure Θ x) (h : X.PObj.TangentSpace),
    baseB X h ∈ B.U →
      X.tangentTheta Θ h =
        ∑ i with h ∈ X.PObj.submanifoldTangent (B.M i) (baseB X h), B.σ i) ∧
  X.tangentEpGroupoid.IsBranchedEpSubgroupoid (X.tangentTheta Θ)

/-- `B` is `BConcl` for every branched `Θ`. -/
theorem B_iff : B ↔ ∀ (Obj Mor : Type) [TopologicalSpace Obj] [T2Space Obj]
    [ParacompactSpace Obj] [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor]
    (X : EpGroupoid Obj Mor) (Θ : Obj → ℚ), X.IsBranchedEpSubgroupoid Θ → BConcl X Θ :=
  Iff.rfl

/-- `B`'s conclusion from `A`, granted independence of the tangent sums and
`TangentBranchingHyp`. -/
theorem A_gives_B_of (hA : A) {Obj Mor : Type} [TopologicalSpace Obj] [T2Space Obj]
    [ParacompactSpace Obj] [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor]
    {X : EpGroupoid Obj Mor} {Θ : Obj → ℚ} (hΘ : X.IsBranchedEpSubgroupoid Θ)
    (hind : X.HasIndependentTangentSums Θ) (hT : X.TangentBranchingHyp Θ) : BConcl X Θ :=
  ⟨fun _ h0 => EpGroupoid.tangentTheta_eq_zero h0,
    fun _ _ B _ hh => hA.1 hind B hh, hA.2.2.2.2.1 hΘ hind hT⟩

/-- `B`'s conclusion from `A` over `ℝᵐ`, granted paracompact `|X|` and smooth `TMᵢ`. -/
theorem A_gives_B_rn (hA : A) {m : ℕ} {Mor : Type} [TopologicalSpace Mor] [T2Space Mor]
    [ParacompactSpace Mor] {X : EpGroupoid (Fin m → ℝ) Mor} (hX : X.PObj = rnPolyfold m)
    {Θ : (Fin m → ℝ) → ℚ} (hΘ : X.IsBranchedEpSubgroupoid Θ) (hpar : X.HasParacompactOrbitSpace)
    (hsub : ∀ (x : Fin m → ℝ) (B : X.LocalBranchingStructure Θ x) (i : B.ι),
      X.tangentEpGroupoid.PObj.IsSmoothSubmanifold (X.tangentSubmanifold (B.M i))) :
    BConcl X Θ :=
  ⟨fun _ h0 => EpGroupoid.tangentTheta_eq_zero h0,
    fun _ _ B _ hh => hA.1 (EpGroupoid.hasIndependentTangentSums_rn hX Θ) B hh,
    hA.2.2.2.2.2.2.2.2.2.2.1 hX hΘ hpar hsub⟩

#rt_check RoundTrip.V9_23.A_gives_B_of [Polyfold.EpGroupoid.tangentTheta_eq,
  Polyfold.EpGroupoid.sum_tangent_eq_sum_tangent, Polyfold.EpGroupoid.tangentTheta_nonneg,
  Polyfold.EpGroupoid.isFunctorial_tangentTheta,
  Polyfold.EpGroupoid.isBranchedEpSubgroupoid_tangentTheta,
  Polyfold.EpGroupoid.isClosed_tangentSubmanifold,
  Polyfold.EpGroupoid.paracompactSpace_orbitSupp_tangentTheta,
  Polyfold.EpGroupoid.tangentBranchingHyp_of_isSmoothSubmanifold,
  Polyfold.EpGroupoid.isBranchedEpSubgroupoid_tangentTheta_of_isSmoothSubmanifold,
  Polyfold.EpGroupoid.LocalBranchingStructure.isSubMPolyfold_tangentSubmanifold,
  Polyfold.EpGroupoid.isBranchedEpSubgroupoid_tangentTheta_rn,
  Polyfold.EpGroupoid.tangentBranchingHyp_zero,
  Polyfold.EpGroupoid.isBranchedEpSubgroupoid_tangentTheta_zero]
#rt_check RoundTrip.V9_23.A_gives_B_rn [Polyfold.EpGroupoid.tangentTheta_eq,
  Polyfold.EpGroupoid.sum_tangent_eq_sum_tangent, Polyfold.EpGroupoid.tangentTheta_nonneg,
  Polyfold.EpGroupoid.isFunctorial_tangentTheta,
  Polyfold.EpGroupoid.isBranchedEpSubgroupoid_tangentTheta,
  Polyfold.EpGroupoid.isClosed_tangentSubmanifold,
  Polyfold.EpGroupoid.paracompactSpace_orbitSupp_tangentTheta,
  Polyfold.EpGroupoid.tangentBranchingHyp_of_isSmoothSubmanifold,
  Polyfold.EpGroupoid.isBranchedEpSubgroupoid_tangentTheta_of_isSmoothSubmanifold,
  Polyfold.EpGroupoid.LocalBranchingStructure.isSubMPolyfold_tangentSubmanifold,
  Polyfold.EpGroupoid.isBranchedEpSubgroupoid_tangentTheta_rn,
  Polyfold.EpGroupoid.tangentBranchingHyp_zero,
  Polyfold.EpGroupoid.isBranchedEpSubgroupoid_tangentTheta_zero]
#rt_overlap RoundTrip.V9_23.A_gives_B_rn [Polyfold.EpGroupoid.tangentTheta_eq,
  Polyfold.EpGroupoid.sum_tangent_eq_sum_tangent, Polyfold.EpGroupoid.tangentTheta_nonneg,
  Polyfold.EpGroupoid.isFunctorial_tangentTheta,
  Polyfold.EpGroupoid.isBranchedEpSubgroupoid_tangentTheta,
  Polyfold.EpGroupoid.isClosed_tangentSubmanifold,
  Polyfold.EpGroupoid.paracompactSpace_orbitSupp_tangentTheta,
  Polyfold.EpGroupoid.tangentBranchingHyp_of_isSmoothSubmanifold,
  Polyfold.EpGroupoid.isBranchedEpSubgroupoid_tangentTheta_of_isSmoothSubmanifold,
  Polyfold.EpGroupoid.LocalBranchingStructure.isSubMPolyfold_tangentSubmanifold,
  Polyfold.EpGroupoid.isBranchedEpSubgroupoid_tangentTheta_rn,
  Polyfold.EpGroupoid.tangentBranchingHyp_zero,
  Polyfold.EpGroupoid.isBranchedEpSubgroupoid_tangentTheta_zero]

end RoundTrip.V9_23
