import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V9_27

/-! Round trip for V9_27 (Definition 9.2.16, p. 421 of the 2021 book; 2017: Definition 9.7,
p. 309: the boundary `∂Θ`, "the functor uniquely characterized by (1) `supp(∂Θ) ⊆ ∂X` and (2)
`∂Θ(y) = ∑_{y ∈ ∂Mᵢ} σᵢ` on local branching structures at points of `supp(∂Θ)`").

The item lists the definition `IsBoundaryCharacterized` (the printed (1), (2): vocabulary) and
four theorems.  `A` is the conjunction of their types, universes at `0`:
`isBoundaryCharacterized_boundaryTheta` (`∂Θ` has (1), (2), given Theorem 9.2.1's independence
`hind`), `isBoundaryCharacterized_zero` (the zero function has (1), (2) for every `Θ`),
`eq_boundaryTheta` (uniqueness in the reading "zero off `supp Θ` and the local formula at the
points of `supp Θ`", given `hind`) and `not_unique_isBoundaryCharacterized_halfLine` (for
`Θ = 1` on `[0, ∞)`, both `0` and `∂Θ ≠ 0` have (1), (2)).

* `B` (the project's `∂Θ` is a functor `X → ℚ⁺` with (1), (2), and every functor `X → ℚ⁺` with
  (1), (2) equals it) is **false**, as its author predicted and as `A` itself records: (2) is
  only required at the points of `supp F`, so `F = 0` qualifies, while `∂Θ ≠ 0` for `Θ = 1` on
  `[0, ∞)`.  `not_B` uses the project's `isBranchedEpSubgroupoid_one` and
  `boundaryTheta_halfLine_one` (V9_28's theorems, not banned here).  So `A → B` is false
  (`not_A_to_B`, since `A` holds) and `B → A` holds only ex falso.
* `BRepaired` is the characterization in the reading the blind author proposes ("(2) at the
  points of `supp Θ` and `∂Θ = 0` off `supp Θ`"), with Theorem 9.2.1's independence `hind`
  added as a hypothesis (as in V9_26, `A` gives nothing about `∂Θ` without it).
  `A_to_BRepaired` is proved from `A`'s `isBoundaryCharacterized_boundaryTheta` and
  `eq_boundaryTheta` (plus the non-item `boundaryTheta_nonneg` and V9_26's
  `isFunctorial_boundaryTheta`). -/

namespace RoundTrip.V9_27
open Polyfold Set

/-- The project's statement (universes at `0`). -/
def A : Prop :=
  (type_of% @Polyfold.EpGroupoid.isBoundaryCharacterized_boundaryTheta.{0}) ∧
  (type_of% @Polyfold.EpGroupoid.isBoundaryCharacterized_zero.{0}) ∧
  (type_of% @Polyfold.EpGroupoid.eq_boundaryTheta.{0}) ∧
  (type_of% @Polyfold.not_unique_isBoundaryCharacterized_halfLine)

theorem A_holds : A :=
  ⟨@Polyfold.EpGroupoid.isBoundaryCharacterized_boundaryTheta.{0},
    @Polyfold.EpGroupoid.isBoundaryCharacterized_zero.{0},
    @Polyfold.EpGroupoid.eq_boundaryTheta.{0},
    @Polyfold.not_unique_isBoundaryCharacterized_halfLine⟩

/-! ### `B` is false -/

theorem not_B : ¬ B := by
  intro hB
  obtain ⟨hΘ, -, h1⟩ := boundaryTheta_halfLine_one
  have hu := (hB _ _ _ _ hΘ).2 0 ⟨fun _ => le_rfl, fun _ => rfl,
    fun _ h => (lt_irrefl (0 : ℚ) h).elim, fun _ h => (lt_irrefl (0 : ℚ) h).elim⟩
  have := congrFun hu halfLineCorner
  rw [h1] at this
  exact zero_ne_one this

theorem not_A_to_B : ¬ (A → B) := fun h => not_B (h A_holds)

/-- `B → A` only ex falso. -/
theorem B_to_A : B → A := fun h => absurd h not_B

/-! ### The repaired characterization -/

section
variable {Obj Mor : Type} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor]

/-- The characterization in the reading where it determines `∂Θ`: a functor `X → ℚ⁺` with
`supp F ⊆ ∂X`, the local formula on every local branching structure at every point of
`supp Θ`, and `F = 0` off `supp Θ`. -/
def IsCharacterizedRepaired (X : EpGroupoid Obj Mor) (Θ F : Obj → ℚ) : Prop :=
  (∀ y, 0 ≤ F y) ∧ (∀ φ : Mor, F (X.src φ) = F (X.tgt φ)) ∧
  EpGroupoid.supp F ⊆ X.PObj.boundary ∧
  (∀ x ∈ EpGroupoid.supp Θ, ∀ (B : X.LocalBranchingStructure Θ x), ∀ y ∈ B.U,
    F y = bsumB B y) ∧
  ∀ y ∉ EpGroupoid.supp Θ, F y = 0

end

/-- `B` with (2) read at the points of `supp Θ`, `F = 0` off `supp Θ`, and Theorem 9.2.1's
independence as a hypothesis. -/
def BRepaired : Prop :=
  ∀ (Obj Mor : Type) [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
    [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor]
    (X : EpGroupoid Obj Mor) (Θ : Obj → ℚ), X.IsBranchedEpSubgroupoid Θ →
    X.HasIndependentTangentSums Θ →
    IsCharacterizedB X Θ (X.boundaryTheta Θ) ∧
    ∀ F : Obj → ℚ, IsCharacterizedRepaired X Θ F → F = X.boundaryTheta Θ

theorem A_to_BRepaired : A → BRepaired := by
  intro hA Obj Mor _ _ _ _ _ _ X Θ hΘ hind
  obtain ⟨hex, -, huniq, -⟩ := hA
  obtain ⟨h1, h2⟩ := hex hind
  refine ⟨⟨X.boundaryTheta_nonneg Θ, X.isFunctorial_boundaryTheta hΘ hind, h1,
    fun x hx B y hy => h2 x hx B y hy⟩, fun F hF => ?_⟩
  obtain ⟨-, -, -, hloc, h0⟩ := hF
  refine huniq hind h0 fun x hx => ?_
  obtain ⟨Bs⟩ := hΘ.localBranching x hx
  exact ⟨Bs, hloc x hx Bs x Bs.mem_U⟩

#rt_check RoundTrip.V9_27.not_B [Polyfold.EpGroupoid.isBoundaryCharacterized_boundaryTheta,
  Polyfold.EpGroupoid.isBoundaryCharacterized_zero, Polyfold.EpGroupoid.eq_boundaryTheta,
  Polyfold.not_unique_isBoundaryCharacterized_halfLine]
#rt_check RoundTrip.V9_27.B_to_A [Polyfold.EpGroupoid.isBoundaryCharacterized_boundaryTheta,
  Polyfold.EpGroupoid.isBoundaryCharacterized_zero, Polyfold.EpGroupoid.eq_boundaryTheta,
  Polyfold.not_unique_isBoundaryCharacterized_halfLine]
#rt_check RoundTrip.V9_27.A_to_BRepaired [Polyfold.EpGroupoid.isBoundaryCharacterized_boundaryTheta,
  Polyfold.EpGroupoid.isBoundaryCharacterized_zero, Polyfold.EpGroupoid.eq_boundaryTheta,
  Polyfold.not_unique_isBoundaryCharacterized_halfLine]
#rt_overlap RoundTrip.V9_27.B_to_A [Polyfold.EpGroupoid.isBoundaryCharacterized_boundaryTheta,
  Polyfold.EpGroupoid.isBoundaryCharacterized_zero, Polyfold.EpGroupoid.eq_boundaryTheta,
  Polyfold.not_unique_isBoundaryCharacterized_halfLine]

end RoundTrip.V9_27
