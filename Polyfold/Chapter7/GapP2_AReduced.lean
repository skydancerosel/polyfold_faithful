import Polyfold.Chapter7.ReducedCriterion

/-!
# Proposition 7.2.10 and Theorem 7.2.14 in their 2021 form

2021 Proposition 7.2.10, p. 313 (2017: Proposition 7.9): `(𝐗^R, T_R)` admits a natural collection of
charts, and the transition maps are sc-smooth.  No Hausdorff or paracompactness claim is made there
(2021 Remark 7.2.8 says that the M-polyfold structure fails in general; Propositions 7.2.12 and
7.2.13 treat paracompactness and Hausdorffness).

2021 Theorem 7.2.14, p. 318 (2017: Proposition 7.10), with Proposition 7.2.16, p. 319, and the
isotropy statement before Definition 7.2.15, p. 319: if `T_R` is Hausdorff, `X_R = (X, 𝐗^R)` is in
a natural way an ep-groupoid, it is effective, and its isotropy group at `x` is `G_x/T_x`.

The project's `proposition_7_2_10` and `proposition_7_10_2017` (`Reduced.lean`) take
`[T2Space X.ReducedMor] [ParacompactSpace X.ReducedMor]`.  Paracompactness is now an instance
(`paracompactSpace_reducedMor`, 2021 Proposition 7.2.12), so the forms below need only what the
2021 text assumes: nothing for Proposition 7.2.10, `T_R` Hausdorff for Theorem 7.2.14.

* `EpGroupoid.proposition_7_2_10_natural_charts`: 2021 Proposition 7.2.10, no hypothesis.
* `EpGroupoid.theorem_7_2_14_reduced`: 2021 Theorem 7.2.14 with Proposition 7.2.16 and the
  isotropy groups, under `[T2Space X.ReducedMor]` only.
* `EpGroupoid.proposition_7_2_16`: `X_R` is effective, under `[T2Space X.ReducedMor]` only.
-/

open Set

noncomputable section

namespace Polyfold

namespace EpGroupoid

universe u

variable {Obj Mor : Type u} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] (X : EpGroupoid Obj Mor)

/-- **2021 Proposition 7.2.10, p. 313 (2017: Proposition 7.9)**, as printed, with no hypothesis:
`𝐗^R` with the quotient topology `T_R` has the natural charts `Ψ_φ = ψ ∘ σ ∘ s` (`reducedCharts`,
for charts `ψ` of `𝐗` inside a sheet `σ` of `s`); their domains cover `𝐗^R`, and any two are
sc-smoothly compatible.  They form the atlas `reducedAtlas`. -/
theorem proposition_7_2_10_natural_charts :
    (∀ q : X.ReducedMor, ∃ χ ∈ X.reducedCharts, q ∈ χ.source) ∧
    (∀ χ ∈ X.reducedCharts, ∀ χ' ∈ X.reducedCharts, χ.Compatible χ') ∧
    X.reducedAtlas.charts = X.reducedCharts :=
  ⟨X.reducedAtlas.cover, X.reducedAtlas.compatible, rfl⟩

section Hausdorff

variable [T2Space X.ReducedMor]

/-- **2021 Theorem 7.2.14, p. 318 (2017: Proposition 7.10)**, with **2021 Proposition 7.2.16,
p. 319** and the isotropy groups (p. 319): if `T_R` is Hausdorff, `X_R = (X, 𝐗^R)`
(`reducedEpGroupoid`) is an ep-groupoid with the structure maps of `X` descended to `𝐗^R`, the
object M-polyfold of `X` and the natural M-polyfold structure on `𝐗^R`; it is effective; its
isotropy group at `x` is `G_x/T_x`; and `π` is a morphism `X → X_R` of `EP`.  Only the Hausdorff
hypothesis of the text is taken: paracompactness of `T_R` is the instance
`paracompactSpace_reducedMor` (Proposition 7.2.12). -/
theorem theorem_7_2_14_reduced :
    X.reducedEpGroupoid.toGroupoidStr = X.reducedGroupoidStr ∧
    X.reducedEpGroupoid.PObj = X.PObj ∧ X.reducedEpGroupoid.PMor = X.reducedPolyfold ∧
    X.reducedEpGroupoid.PMor.atlas = X.reducedAtlas ∧
    X.reducedEpGroupoid.IsEffective ∧
    (∀ x, Nonempty (X.Isotropy x ⧸ X.trivialSubgroup x ≃* X.reducedEpGroupoid.Isotropy x)) ∧
    Nonempty (EpFunctor X X.reducedEpGroupoid) :=
  ⟨rfl, rfl, rfl, rfl, X.isEffective_reducedEpGroupoid,
    fun x => ⟨X.quotientTrivialSubgroupEquiv x⟩, ⟨X.reductionFunctor⟩⟩

/-- **2021 Proposition 7.2.16, p. 319**: the reduced ep-groupoid `X_R` of an ep-groupoid with
Hausdorff `T_R` is effective. -/
theorem proposition_7_2_16 : X.reducedEpGroupoid.IsEffective :=
  X.isEffective_reducedEpGroupoid

end Hausdorff

end EpGroupoid

end Polyfold
