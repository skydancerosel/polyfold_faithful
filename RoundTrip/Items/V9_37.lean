import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V9_37

/-! Round trip for V9_37 ((9.11), p. 427, and Proposition 9.3.9, p. 428 of the 2021 book: the
boundary orientation does not depend on the structure).

`A` is the conjunction of the types of the four listed theorems, universes instantiated at `0`
(`B` lives in `Type`): `SubmanifoldOrientation.hasSubDegree_tangent_iff` (the degree of an
oriented tangent space is `d_M(y)`), `EpGroupoid.degreePart_orientedSum`, `EpGroupoid.eq_9_11`
and `EpGroupoid.proposition_9_3_9`.  `HasSubDegree` and `degreePart` are definitions
(vocabulary).

* `B` (9.11) follows from `A`: `A_to_B_9_11`.  The two structures of `B`, with the dimensions
  `nᵢ` read off the orientations (`isSubmanifoldOfDim_of_orientation`: an orientation of
  dimension `n` of a smooth submanifold makes it `n`-dimensional), are project
  `OrientedBranchingStructure`s; at smooth `y ∈ U ∩ U'` both represent `T y`, so `eq_9_11`
  applies; at non-smooth `y` no sheet passes through `y` (`Mᵢ ⊆ supp Θ ⊆ X_∞`).
* `B`'s Proposition 9.3.9 does NOT follow from `A`.  The project's `proposition_9_3_9` is
  stated for an abstract boundary operation `bd : OrTangent → OrTangent`, a function of the
  oriented tangent space `T_y(Mᵢ, oᵢ)`.  `B`'s `T_y(∂Mᵢ, o_{∂Mᵢ})` (`bdOrB`) is built from the
  sheet `Mᵢ` itself: the set `T_y∂Mᵢ` and the outward vectors of `Mᵢ`.  To get `B` from (9.11)
  one needs `T_y(Mᵢ, oᵢ) = T_y(M'ⱼ, o'ⱼ)` and `d = 1` ⇒ `bdOrB (oᵢ) y = bdOrB (o'ⱼ) y`
  (that `T_y∂M = T^R_yM` and the outward half-space depend only on `T_yM` for tame `M`).  The
  project lists this as not formalized (partial cones of submanifolds).
* `B_to_A` cannot use `B`: `B` assumes the object M-polyfold tame and an orientation `T`, and
  `A`'s four conjuncts assume neither.  It re-proves them outright (copies of the project's
  proofs, from the unbanned `subDegIndex_eq_of_submanifoldTangent_eq`). -/

namespace RoundTrip.V9_37
open Polyfold Polyfold.MPolyfold Polyfold.EpGroupoid Set Module Submodule

/-- The project's statement (universes at `0`). -/
def A : Prop :=
  (type_of% @Polyfold.MPolyfold.SubmanifoldOrientation.hasSubDegree_tangent_iff.{0}) ∧
  (type_of% @Polyfold.EpGroupoid.degreePart_orientedSum.{0}) ∧
  (type_of% @Polyfold.EpGroupoid.eq_9_11.{0}) ∧
  (type_of% @Polyfold.EpGroupoid.proposition_9_3_9.{0})

theorem A_holds : A :=
  ⟨@Polyfold.MPolyfold.SubmanifoldOrientation.hasSubDegree_tangent_iff.{0},
    @Polyfold.EpGroupoid.degreePart_orientedSum.{0},
    @Polyfold.EpGroupoid.eq_9_11.{0},
    @Polyfold.EpGroupoid.proposition_9_3_9.{0}⟩

/-! ### Glue -/

/-- An orientation of dimension `n` of a smooth submanifold makes it `n`-dimensional (the chart
image of `T_aM` is the `n`-dimensional `N` of the chart orientation). -/
theorem isSubmanifoldOfDim_of_orientation {Z : Type} [TopologicalSpace Z] [T2Space Z]
    [ParacompactSpace Z] {P : MPolyfold Z} {M : Set Z} {n : ℕ} (hM : P.IsSmoothSubmanifold M)
    (o : P.SubmanifoldOrientation M n) : P.IsSubmanifoldOfDim M n := by
  refine ⟨hM, fun a ha => ?_⟩
  obtain ⟨φ, hφm, haφ⟩ := P.atlas.cover a
  have hφ := P.isChart_of_mem hφm
  have haV := hM.mem_data_V ha
  have ha1 : a ∈ P.levelSet 1 := (hM.data ha).mem_levelSet_one ha haV
  have hz := P.toBase_levelLift hφ haφ ha1
  obtain ⟨N, hN, -, hrank, -⟩ := (o.isOrientedAt a ha).isChartOrientation hφ haφ
  refine hasDimAt_of_finrank hM ha hφ ((hM.data ha).toSubData.isOpen_shrink φ)
    ((hM.data ha).toSubData.shrink_subset_source φ)
    ((hM.data ha).toSubData.isScRetract_image φ hφ)
    ((hM.data ha).toSubData.mem_shrink φ ha haV haφ) hz ?_
  rw [← chartVec_image_submanifoldTangent hφ (hM.data ha) ha haV haφ]
  change finrank ℝ (span ℝ (chartVec hφ '' (⟨n, P.submanifoldTangent M a, o.frames a⟩ :
    P.OrTangent).carrier)) = n
  rw [← hN, Submodule.span_eq]
  exact hrank

section
variable {Obj Mor : Type} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] {X : EpGroupoid Obj Mor}
  {Θ : Obj → ℚ} {x : Obj}

/-- The project's oriented branching structure from `B`'s data `(B, n, o)`. -/
def toOriented (B : X.LocalBranchingStructure Θ x) (n : B.ι → ℕ)
    (o : ∀ i, X.PObj.SubmanifoldOrientation (B.M i) (n i)) :
    X.OrientedBranchingStructure Θ x where
  toLocalBranchingStructure := B
  dim := n
  isSubmanifoldOfDim i := isSubmanifoldOfDim_of_orientation (B.isSmoothSubmanifold i) (o i)
  orient := o

theorem orientedSum_toOriented (B : X.LocalBranchingStructure Θ x) (n : B.ι → ℕ)
    (o : ∀ i, X.PObj.SubmanifoldOrientation (B.M i) (n i)) (y : Obj) :
    (toOriented B n o).orientedSum y = orSumB B n o y := rfl

open Classical in
/-- `B`'s degree-`ℓ` sum is the project's filtered sum. -/
theorem degSumB_eq (B : X.LocalBranchingStructure Θ x) (n : B.ι → ℕ)
    (o : ∀ i, X.PObj.SubmanifoldOrientation (B.M i) (n i)) (y : Obj) (ℓ : ℕ) :
    degSumB B n o y ℓ = ∑ i with ∃ hy : y ∈ (toOriented B n o).M i,
        X.PObj.subDegIndex ((toOriented B n o).isSmoothSubmanifold i).isSubMPolyfold
          ⟨y, hy⟩ = ℓ,
      Finsupp.single (((toOriented B n o).orient i).tangent y) ((toOriented B n o).σ i) := by
  unfold degSumB
  refine Finset.sum_congr (Finset.filter_congr fun i _ => ?_) fun i _ => rfl
  constructor
  · rintro ⟨hy, hd⟩
    exact ⟨hy, by rw [← hd, dMB_eq_of (B.isSmoothSubmanifold i).isSubMPolyfold hy]; rfl⟩
  · rintro ⟨hy, hd⟩
    exact ⟨hy, by rw [dMB_eq_of (B.isSmoothSubmanifold i).isSubMPolyfold hy]; exact hd⟩
where
  dMB_eq_of {M : Set Obj} (hM : X.PObj.IsSubMPolyfold M) {y : Obj} (hy : y ∈ M) :
      dMB X.PObj M y = X.PObj.subDegIndex hM ⟨y, hy⟩ := by
    unfold dMB; rw [dif_pos ⟨hM, hy⟩]

/-- Sheets lie in `X_∞`. -/
theorem mem_smoothSet_of_mem_M (hΘ : X.IsBranchedEpSubgroupoid Θ)
    (B : X.LocalBranchingStructure Θ x) {i : B.ι} {y : Obj} (hy : y ∈ B.M i) :
    y ∈ X.PObj.smoothSet := by
  have hMU : y ∈ B.MU := mem_iUnion.2 ⟨i, hy⟩
  rw [B.MU_eq] at hMU
  exact hΘ.support_subset hMU.1

end

/-- **`B`'s (9.11) part**, the first conjunct of `B`. -/
def B_9_11 : Prop :=
  ∀ (Obj Mor : Type) [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
    [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor]
    (X : EpGroupoid Obj Mor), X.PObj.IsTame →
    ∀ (Θ : Obj → ℚ), X.IsBranchedEpSubgroupoid Θ →
    ∀ T : Obj → X.PObj.OrTangent →₀ ℚ, IsOrientationB X Θ T →
    ∀ x ∈ EpGroupoid.supp Θ,
    ∀ (B : X.LocalBranchingStructure Θ x) (n : B.ι → ℕ)
      (o : ∀ i, X.PObj.SubmanifoldOrientation (B.M i) (n i))
      (B' : X.LocalBranchingStructure Θ x) (n' : B'.ι → ℕ)
      (o' : ∀ i, X.PObj.SubmanifoldOrientation (B'.M i) (n' i)),
      (∀ i, X.PObj.HasTameInducedStructure (B.M i)) →
      (∀ i, X.PObj.HasTameInducedStructure (B'.M i)) →
      (∀ y ∈ B.U, y ∈ X.PObj.smoothSet → T y = orSumB B n o y) →
      (∀ y ∈ B'.U, y ∈ X.PObj.smoothSet → T y = orSumB B' n' o' y) →
      ∀ y ∈ B.U ∩ B'.U, ∀ ℓ : ℕ, degSumB B n o y ℓ = degSumB B' n' o' y ℓ

theorem B_to_B_9_11 : B → B_9_11 := fun hB Obj Mor _ _ _ _ _ _ X hP Θ hΘ T hT x hx B n o B' n'
    o' ht ht' hr hr' y hy => (hB Obj Mor X hP Θ hΘ T hT x hx B n o B' n' o' ht ht' hr hr' y hy).1

open Classical in
/-- **`A ⇒ B`'s (9.11)**, from `eq_9_11` (the tameness of `X` is not used). -/
theorem A_to_B_9_11 : A → B_9_11 := by
  intro hA Obj Mor _ _ _ _ _ _ X _ Θ hΘ T _ x _ B n o B' n' o' ht ht' hr hr' y hy ℓ
  rw [degSumB_eq, degSumB_eq]
  by_cases hys : y ∈ X.PObj.smoothSet
  · have h : (toOriented B n o).orientedSum y = (toOriented B' n' o').orientedSum y := by
      rw [orientedSum_toOriented, orientedSum_toOriented, ← hr y hy.1 hys, ← hr' y hy.2 hys]
    exact hA.2.2.1 (toOriented B n o) (toOriented B' n' o') ht ht' h ℓ
  · have e : ∀ (B : X.LocalBranchingStructure Θ x) (n : B.ι → ℕ)
        (o : ∀ i, X.PObj.SubmanifoldOrientation (B.M i) (n i)),
        (∑ i with ∃ hy : y ∈ (toOriented B n o).M i,
          X.PObj.subDegIndex ((toOriented B n o).isSmoothSubmanifold i).isSubMPolyfold
            ⟨y, hy⟩ = ℓ,
          Finsupp.single (((toOriented B n o).orient i).tangent y)
            ((toOriented B n o).σ i)) = 0 := fun B n o =>
      Finset.sum_eq_zero fun i hi => by
        obtain ⟨hyi, -⟩ := (Finset.mem_filter.1 hi).2
        exact absurd (mem_smoothSet_of_mem_M hΘ B hyi) hys
    rw [e B n o, e B' n' o']

/-! ### `B → A`: re-proved outright (copies of the project's proofs) -/

section Copies

theorem hasSubDegree_tangent_iff_copy {X : Type} [TopologicalSpace X] [T2Space X]
    [ParacompactSpace X] {P : MPolyfold X} {A : Set X} {n : ℕ}
    (o : P.SubmanifoldOrientation A n) (hA : P.IsSmoothSubmanifold A)
    (ht : P.HasTameInducedStructure A) {y : X} (hy : y ∈ A) {ℓ : ℕ} :
    P.HasSubDegree y ℓ (o.tangent y) ↔ P.subDegIndex hA.isSubMPolyfold ⟨y, hy⟩ = ℓ := by
  constructor
  · rintro ⟨A', hA', hy', ht', hT, hd⟩
    rw [← hd]
    exact subDegIndex_eq_of_submanifoldTangent_eq hA hA' ht ht' hy hy' hT.symm
  · intro h
    exact ⟨A, hA, hy, ht, rfl, h⟩

variable {Obj Mor : Type} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] {X : EpGroupoid Obj Mor}
variable {Θ : Obj → ℚ}

open scoped Classical in
theorem degreePart_orientedSum_copy {x : Obj} (B : X.OrientedBranchingStructure Θ x)
    (ht : ∀ i, X.PObj.HasTameInducedStructure (B.M i)) (y : Obj) (ℓ : ℕ) :
    X.degreePart y ℓ (B.orientedSum y) =
      ∑ i with ∃ hy : y ∈ B.M i,
          X.PObj.subDegIndex (B.isSmoothSubmanifold i).isSubMPolyfold ⟨y, hy⟩ = ℓ,
        Finsupp.single ((B.orient i).tangent y) (B.σ i) := by
  rw [degreePart, OrientedBranchingStructure.orientedSum, Finsupp.filter_sum, Finset.sum_filter,
    Finset.sum_filter]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hiff := fun hy : y ∈ B.M i =>
    hasSubDegree_tangent_iff_copy (B.orient i) (B.isSmoothSubmanifold i) (ht i) hy (ℓ := ℓ)
  by_cases hy : y ∈ B.M i
  · rw [if_pos hy]
    by_cases hd : X.PObj.subDegIndex (B.isSmoothSubmanifold i).isSubMPolyfold ⟨y, hy⟩ = ℓ
    · rw [if_pos ⟨hy, hd⟩, Finsupp.filter_single_of_pos _ ((hiff hy).2 hd)]
    · rw [if_neg (show ¬∃ hy' : y ∈ B.M i,
          X.PObj.subDegIndex (B.isSmoothSubmanifold i).isSubMPolyfold ⟨y, hy'⟩ = ℓ
          from fun ⟨_, hd'⟩ => hd hd'),
        Finsupp.filter_single_of_neg _ fun h => hd ((hiff hy).1 h)]
  · rw [if_neg hy, if_neg (show ¬∃ hy' : y ∈ B.M i,
        X.PObj.subDegIndex (B.isSmoothSubmanifold i).isSubMPolyfold ⟨y, hy'⟩ = ℓ
        from fun ⟨hy', _⟩ => hy hy')]

open scoped Classical in
theorem eq_9_11_copy {x x' : Obj} (B : X.OrientedBranchingStructure Θ x)
    (B' : X.OrientedBranchingStructure Θ x') (ht : ∀ i, X.PObj.HasTameInducedStructure (B.M i))
    (ht' : ∀ i, X.PObj.HasTameInducedStructure (B'.M i)) {y : Obj}
    (h : B.orientedSum y = B'.orientedSum y) (ℓ : ℕ) :
    (∑ i with ∃ hy : y ∈ B.M i,
        X.PObj.subDegIndex (B.isSmoothSubmanifold i).isSubMPolyfold ⟨y, hy⟩ = ℓ,
      Finsupp.single ((B.orient i).tangent y) (B.σ i)) =
    ∑ i with ∃ hy : y ∈ B'.M i,
        X.PObj.subDegIndex (B'.isSmoothSubmanifold i).isSubMPolyfold ⟨y, hy⟩ = ℓ,
      Finsupp.single ((B'.orient i).tangent y) (B'.σ i) := by
  rw [← degreePart_orientedSum_copy B ht, ← degreePart_orientedSum_copy B' ht', h]

open scoped Classical in
theorem proposition_9_3_9_copy (bd : X.PObj.OrTangent → X.PObj.OrTangent)
    {T : Obj → X.PObj.OrTangent →₀ ℚ} (hT : X.IsOrientation Θ T) :
    (∀ y ∈ X.PObj.smoothSet, y ∉ supp Θ → X.boundaryLift bd T y = 0) ∧
    ∀ (x : Obj) (B : X.OrientedBranchingStructure Θ x),
      (∀ i, X.PObj.HasTameInducedStructure (B.M i)) →
      (∀ y ∈ B.U, y ∈ X.PObj.smoothSet → T y = B.orientedSum y) →
      ∀ y ∈ B.U, y ∈ X.PObj.smoothSet →
        X.boundaryLift bd T y = ∑ i with ∃ hy : y ∈ B.M i,
            X.PObj.subDegIndex (B.isSmoothSubmanifold i).isSubMPolyfold ⟨y, hy⟩ = 1,
          Finsupp.single (bd ((B.orient i).tangent y)) (B.σ i) := by
  refine ⟨fun y hy hys => ?_, fun x B ht hB y hy hys => ?_⟩
  · rw [boundaryLift, hT.eq_zero_of_not_mem hy hys, degreePart, Finsupp.filter_zero,
      Finsupp.mapDomain_zero]
  · rw [boundaryLift, hB y hy hys, degreePart_orientedSum_copy B ht, Finsupp.mapDomain_finsetSum]
    exact Finset.sum_congr rfl fun i _ => Finsupp.mapDomain_single

end Copies

/-- `B → A`, by re-proving `A` outright (`B`'s tameness of `X` and orientation `T` are absent
from `A`'s conjuncts, so `B` cannot be applied). -/
theorem B_to_A : B → A := fun _ =>
  ⟨@hasSubDegree_tangent_iff_copy, @degreePart_orientedSum_copy, @eq_9_11_copy,
    @proposition_9_3_9_copy⟩

#rt_check RoundTrip.V9_37.A_to_B_9_11 [
  Polyfold.MPolyfold.SubmanifoldOrientation.hasSubDegree_tangent_iff,
  Polyfold.EpGroupoid.degreePart_orientedSum, Polyfold.EpGroupoid.eq_9_11,
  Polyfold.EpGroupoid.proposition_9_3_9]
#rt_check RoundTrip.V9_37.B_to_A [
  Polyfold.MPolyfold.SubmanifoldOrientation.hasSubDegree_tangent_iff,
  Polyfold.EpGroupoid.degreePart_orientedSum, Polyfold.EpGroupoid.eq_9_11,
  Polyfold.EpGroupoid.proposition_9_3_9]
#rt_overlap RoundTrip.V9_37.B_to_A [
  Polyfold.MPolyfold.SubmanifoldOrientation.hasSubDegree_tangent_iff,
  Polyfold.EpGroupoid.degreePart_orientedSum, Polyfold.EpGroupoid.eq_9_11,
  Polyfold.EpGroupoid.proposition_9_3_9]

end RoundTrip.V9_37
