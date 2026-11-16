import Polyfold.Chapter3.NonVacuityCorner
import Polyfold.Chapter4.Recentre

/-!
# The half-space chart example

The chart `HalfSpaceBundle.chartAt` of the half-space bundle and the graph section on it: an
sc-Fredholm section, tame, in good position, satisfying the hypotheses of Theorem 3.6.11 in
whole-chart form (`theorem_3_6_11_halfSpace`). The corner examples are in
`Chapter3/NonVacuityCorner.lean`.
-/

open Set Filter Topology Function
open scoped ContDiff
noncomputable section
namespace Polyfold
namespace HalfSpaceBundle
variable (m k : ℕ)
variable {m k}

/-- The strong bundle chart centred at `x₀`. -/
def chartAt (x₀ : H m) : StrongBundleChart (basePoly m) (proj m k) :=
  chart₀.recentre (ScIso.refl (halfSpaceSc m)) hT₀ (x₀ : (halfSpaceSc m) 0) (mem_smooth _)

lemma isChart_chartAt (x₀ : H m) : (bundle m k).IsChart (chartAt x₀) :=
  StrongBundle.IsChart.recentre isChart_chart₀ _ hT₀ _ _

lemma r_chartAt (x₀ : H m) (u : (halfSpaceSc m) 0) :
    StrongRetr.r (chartAt (k := k) x₀).R u =
      u + (x₀ : (halfSpaceSc m) 0) - (x₀ : (halfSpaceSc m) 0) := rfl

lemma isTameChart_chartAt (x₀ : H m) : (bundle m k).IsTameChart (chartAt x₀) :=
  StrongBundle.isTameChart_of_eqOn_id (isChart_chartAt x₀) fun u _ =>
    add_sub_cancel_right (u : (halfSpaceSc m) 0) (x₀ : (halfSpaceSc m) 0)

lemma mem_source_chartAt (x₀ : H m) : x₀ ∈ (chartAt (k := k) x₀).φ.source :=
  ⟨mem_univ _, mem_recentreNbhd (T := ScIso.refl (halfSpaceSc m)) (hT₀ (m := m) (k := k)) x₀.2⟩

lemma chartAt_self (x₀ : H m) : (chartAt (k := k) x₀).φ x₀ = 0 := sub_self _

lemma mem_U_chartAt {x₀ : H m} {u : (halfSpaceSc m) 0} (hu : u ∈ (chartAt (k := k) x₀).U) :
    u + x₀ ∈ H m :=
  hu.1.1

lemma zero_mem_U_chartAt (x₀ : H m) : (0 : (halfSpaceSc m) 0) ∈ (chartAt (k := k) x₀).U := by
  have hG := mem_recentreNbhd (T := ScIso.refl (halfSpaceSc m)) (hT₀ (m := m) (k := k)) x₀.2
  show (0 : (halfSpaceSc m) 0) + (x₀ : (halfSpaceSc m) 0) ∈
    ((chart₀ (m := m) (k := k)).recentreBaseR (ScIso.refl _) (x₀ : (halfSpaceSc m) 0)).U
  rw [zero_add]
  exact ⟨⟨x₀.2, hG⟩, hG⟩

variable {φ : Pm m → (Fin k → ℝ)}

lemma principal_chartAt {x₀ : H m} {z : (halfSpaceSc m) 0}
    (hz : z + (x₀ : (halfSpaceSc m) 0) ∈ H m) :
    (chartAt (k := k) x₀).principal (graphSection φ) z = loc φ x₀ z := by
  change φ (((baseChart m).symm (z + (x₀ : (halfSpaceSc m) 0)) : H m) : (halfSpaceSc m) 0) =
    φ (z + (x₀ : (halfSpaceSc m) 0))
  rw [baseChart_symm_val hz]

lemma scDeriv_r_chartAt (x₀ : H m) :
    scDeriv (chartAt (k := k) x₀).U (StrongRetr.r (chartAt (k := k) x₀).R) 0 =
      ContinuousLinearMap.id ℝ _ := by
  refine scDeriv_zero_eq_of_hasFDerivAt (chartAt (k := k) x₀).relOpen ?_ (zero_mem_U_chartAt x₀) ?_
  · exact (isScSmooth_of_bijective_toBase bijective_toBase_E bijective_toBase_E
      (chartAt (k := k) x₀).relOpen.isScDomain (f := fun u : Pm m => u + (x₀ : Pm m) - (x₀ : Pm m))
      ((contDiff_id.add contDiff_const).sub contDiff_const).contDiffOn).isSc1
  · exact ((hasFDerivAt_id _).add_const _).sub_const _

lemma scDeriv_loc (hφ : ContDiff ℝ ∞ φ) (x₀ : H m) :
    scDeriv (F := (chartAt (k := k) x₀).F) (chartAt (k := k) x₀).U (loc φ x₀) 0 =
      fderiv ℝ φ (x₀ : Pm m) := by
  refine scDeriv_zero_eq_of_hasFDerivAt (chartAt (k := k) x₀).relOpen ?_ (zero_mem_U_chartAt x₀) ?_
  · exact (isScSmooth_of_bijective_toBase bijective_toBase_E (bijective_toBase_const _)
      (chartAt (k := k) x₀).relOpen.isScDomain (contDiff_loc hφ x₀).contDiffOn).isSc1
  · have hd : HasFDerivAt φ (fderiv ℝ φ (x₀ : Pm m)) (0 + (x₀ : Pm m)) := by
      rw [zero_add]; exact (hφ.differentiable (by simp)).differentiableAt.hasFDerivAt
    have := hd.comp (0 : Pm m) ((hasFDerivAt_id (0 : Pm m)).add_const (x₀ : Pm m))
    rw [ContinuousLinearMap.comp_id] at this
    exact this

/-- The partial quadrant of the chart centred at `x₀` (`C_{x₀}`, Definition 2.5.1 (preprint 2.33)): the half-space
at a boundary point, everything at an interior point. -/
lemma C_chartAt (x₀ : H m) : (chartAt (k := k) x₀).φ.model.C =
    if (x₀ : Pm m).1 0 = 0 then H m else univ := by
  ext v
  change (∀ i, (x₀ : Pm m).1 i = 0 → 0 ≤ (show Pm m from v).1 i) ↔ _
  rw [Fin.forall_fin_one]
  split_ifs with h
  · exact ⟨fun h' => mem_quadrant_one_iff.2 (h' h), fun h' _ => mem_quadrant_one_iff.1 h'⟩
  · exact iff_of_true (fun h' => absurd h' h) (mem_univ _)

lemma isPartialQuadrant_C_chartAt (x₀ : H m) :
    IsPartialQuadrant (ScBanach.const (Pm m)) (chartAt (k := k) x₀).φ.model.C := by
  rw [C_chartAt]
  split_ifs
  · exact ⟨1, rnSc m, constPmIso m, by ext; rfl⟩
  · exact isPartialQuadrant_univ _

/-- **The germ data of the graph section in the chart centred at `x₀`** (as
`TrivialBundle.germData_graphSection`, in the re-centred chart). -/
theorem germData_graphSection (hφ : ContDiff ℝ ∞ φ) (x₀ : H m) :
    IsFilledVersion (chartAt (k := k) x₀).relOpen (chartAt x₀).isRetraction
        (zero_mem_U_chartAt x₀) ((chartAt x₀).principal (graphSection φ)) (loc φ x₀) ∧
      IsScSmooth (E := halfSpaceSc m) (F := (rnSc k).shift) (chartAt (k := k) x₀).U
        (fun _ => (φ (x₀ : Pm m) : (rnSc k).shift 0)) ∧
      (rnSc k).toBase 1 (φ (x₀ : Pm m)) = loc φ x₀ 0 ∧
      IsConjugateToBasicGerm (E := halfSpaceSc m) (F := rnSc k) (chartAt (k := k) x₀).U
        (fun u => loc φ x₀ u - φ (x₀ : Pm m)) := by
  have hU := (chartAt (k := k) x₀).relOpen
  refine ⟨⟨isScSmooth_of_bijective_toBase bijective_toBase_E (bijective_toBase_const _)
      hU.isScDomain (contDiff_loc hφ x₀).contDiffOn, ⟨Eventually.of_forall fun z hz => ?_,
      Eventually.of_forall fun y hy _ => ⟨y, hy, add_sub_cancel_right _ _⟩, ?_,
      TrivialBundle.exists_kerEquiv_of_injective _ _ _ (fun v hv => by rwa [scDeriv_r_chartAt] at hv)
        fun v hv => hv⟩⟩,
    isScSmooth_of_bijective_toBase bijective_toBase_E
      (bijective_toBase_shift (bijective_toBase_const _)) hU.isScDomain contDiffOn_const,
    by rw [ScBanach.const_toBase]; exact congrArg φ (zero_add _).symm, ?_⟩
  · obtain ⟨u, hu, rfl⟩ := hz
    refine principal_chartAt (z := (show Pm m from u) + (x₀ : Pm m) - (x₀ : Pm m)) ?_
    rw [sub_add_cancel]; exact mem_U_chartAt hu
  · refine ((isScSmooth_of_bijective_toBase bijective_toBase_E (bijective_toBase_const _)
      hU.isScDomain (contDiffOn_const (c := (0 : Fin k → ℝ)))).congr hU.isScDomain
      fun y _ => ?_).isSc1
    change (0 : Fin k → ℝ) = loc φ x₀ y - loc φ x₀ y
    rw [sub_self]
  · refine isConjugateToBasicGerm_halfSpace ?_ hU (zero_mem_U_chartAt x₀)
      ((contDiff_loc hφ x₀).sub contDiff_const) ?_
    · exact isPartialQuadrant_C_chartAt x₀
    · change φ (0 + (x₀ : Pm m)) - φ x₀ = 0
      rw [zero_add, sub_self]

/-- **Tame germ data of the graph section at every point of `H`** (Definition 3.6.3 (preprint 3.50)), in the
re-centred chart. -/
theorem isScFredholmGermTame_graphSection_wholeChart (hφ : ContDiff ℝ ∞ φ) (x₀ : H m) :
    (bundle m k).IsScFredholmGermTameWholeChart (graphSection φ) x₀ := by
  obtain ⟨hfill, hs, hs0, hconj⟩ := germData_graphSection (k := k) hφ x₀
  exact ⟨by rw [smoothSet_eq_univ]; exact mem_univ x₀, chartAt x₀, isTameChart_chartAt x₀,
    mem_source_chartAt x₀, chartAt_self x₀, zero_mem_U_chartAt x₀, loc φ x₀, fun _ => φ x₀,
    hfill, hs, hs0, hconj⟩

/-- **Good position at a regular zero, including the boundary** (Definition 3.6.6 (preprint 3.53)): if `Dφ(x₀)` is
onto and, when `x₀` is on the boundary `{x₁ = 0}`, `ker Dφ(x₀)` contains a vector `v` with
`v₁ ≠ 0`, then the graph section is in good position at `x₀` in the (tame) re-centred chart:
`Tf̃(0) = Dφ(x₀)` is onto, and `ker Dφ(x₀)` is in good position to `C_{x₀}` (the half-space,
`isInGoodPositionIn_halfSpace`, or everything). -/
theorem isGoodPositionGermTame_graphSection_wholeChart (hφ : ContDiff ℝ ∞ φ) {x₀ : H m}
    (hsurj : Surjective (fderiv ℝ φ (x₀ : Pm m)))
    (hbd : (x₀ : Pm m).1 0 = 0 → ∃ v, fderiv ℝ φ (x₀ : Pm m) v = 0 ∧ v.1 0 ≠ 0) :
    (bundle m k).IsGoodPositionGermTameWholeChart (graphSection φ) x₀ := by
  obtain ⟨hfill, hs, hs0, hconj⟩ := germData_graphSection (k := k) hφ x₀
  have htop : rangeS (scDeriv (chartAt (k := k) x₀).U (StrongRetr.r (chartAt (k := k) x₀).R) 0) =
      ⊤ := by
    rw [rangeS, scDeriv_r_chartAt]; exact LinearMap.range_id
  refine ⟨by rw [smoothSet_eq_univ]; exact mem_univ x₀, chartAt x₀, isTameChart_chartAt x₀,
    mem_source_chartAt x₀, chartAt_self x₀, zero_mem_U_chartAt x₀, loc φ x₀, fun _ => φ x₀,
    hfill, hs, hs0, hconj, fun y _ => ?_, ?_⟩
  · obtain ⟨x, hx⟩ := hsurj y
    refine ⟨x, by rw [htop]; exact Submodule.mem_top, ?_⟩
    rw [scDeriv_loc hφ x₀]; exact hx
  · rw [htop, scDeriv_loc hφ x₀]
    by_cases h : (x₀ : Pm m).1 0 = 0
    · rw [C_chartAt, if_pos h]
      obtain ⟨v, hv, hv0⟩ := hbd h
      exact isInGoodPositionIn_halfSpace _ ⟨v, hv, hv0⟩
    · rw [C_chartAt, if_neg h]
      exact TrivialBundle.isInGoodPositionIn_univ _

/-- **The graph section of a `C^∞` map is an sc-Fredholm section over the half-space**. -/
theorem isScFredholmSection_graphSection_wholeChart (hφ : ContDiff ℝ ∞ φ) :
    (bundle m k).IsScFredholmSectionWholeChart (graphSection φ) where
  isScSmooth := isScSmoothSection_graphSection hφ
  regularizing j x _ _ := by rw [levelSet_eq_univ]; exact mem_univ x
  germ x _ := (isScFredholmGermTame_graphSection_wholeChart hφ x).isScFredholmGerm

/-- The graph section has tame germ data at every point (Definition 3.6.4 (preprint 3.51)). -/
theorem isScFredholmSectionTame_graphSection_wholeChart (hφ : ContDiff ℝ ∞ φ) :
    (bundle m k).IsScFredholmSectionTameWholeChart (graphSection φ) where
  toIsScFredholmSectionWholeChart := isScFredholmSection_graphSection_wholeChart hφ
  germTame x _ := isScFredholmGermTame_graphSection_wholeChart hφ x

/-- **The hypotheses of Theorem 3.6.11 (preprint 3.57) hold over the half-space**, at boundary zeros included. -/
theorem hypotheses_theorem_3_6_11_halfSpace_wholeChart (hφ : ContDiff ℝ ∞ φ) (hreg : IsRegularOnHalfSpace φ) :
    (bundle m k).IsScFredholmSectionWholeChart (graphSection φ) ∧
      ∀ x, IsZeroAt (proj m k) (graphSection φ) x →
        (bundle m k).IsGoodPositionGermTameWholeChart (graphSection φ) x :=
  ⟨isScFredholmSection_graphSection_wholeChart hφ, fun x hx =>
    isGoodPositionGermTame_graphSection_wholeChart hφ (hreg x (isZeroAt_graphSection_iff.1 hx)).1
      (hreg x (isZeroAt_graphSection_iff.1 hx)).2⟩

/-- **Theorem 3.6.11 (preprint 3.57) over the half-space (the regular value theorem for manifolds with boundary)**:
for `φ : ℝ ⊕ ℝᵐ → ℝᵏ` of class `C^∞` with `0` a regular value of `φ` on `H` and of `φ|∂H`, and
`φ⁻¹(0) ∩ H ≠ ∅`, the solution set is a tame sub-M-polyfold of `H` with the structure of a
manifold with corners, of locally constant dimension. -/
theorem theorem_3_6_11_halfSpace (hφ : ContDiff ℝ ∞ φ) (hreg : IsRegularOnHalfSpace φ)
    (hne : ∃ x : H m, φ (x : Pm m) = 0) :
    ∃ hsub : (basePoly m).IsSubMPolyfold (solutionSet (proj m k) (graphSection φ)),
      haveI := (basePoly m).paracompactSpace_subtype (solutionSet (proj m k) (graphSection φ))
      (MPolyfold.subPolyfold hsub).IsTame ∧
        (MPolyfold.subPolyfold hsub).IsManifoldWithCornersLoc ∧
        ∀ x ∈ solutionSet (proj m k) (graphSection φ), ∃ d : ℕ,
          ∃ D : (basePoly m).TangentGermChart (solutionSet (proj m k) (graphSection φ)) x d,
            D.IsRegular ∧ ∀ y ∈ solutionSet (proj m k) (graphSection φ) ∩ D.φ.source,
              ∀ (n' : ℕ) (_ : (basePoly m).TangentGermChart
                (solutionSet (proj m k) (graphSection φ)) y n'), n' = d := by
  obtain ⟨hf, hall⟩ := hypotheses_theorem_3_6_11_halfSpace_wholeChart hφ hreg
  obtain ⟨x, hx⟩ := hne
  exact theorem_3_6_11_wholeChart hf hall ⟨x, isZeroAt_graphSection_iff.2 hx⟩

/-- **A concrete instance with boundary**: for the section `(a, y) ↦ ((a, y), y)` of
`([0, ∞) × ℝ) × ℝ → [0, ∞) × ℝ`, the solution set (the half-line `[0, ∞) × {0}`, with the
boundary point `(0, 0)`) is a sub-M-polyfold of the half-plane with the structure of a manifold
with corners. -/
theorem theorem_3_6_11_halfSpace_example :
    ∃ hsub : (basePoly 1).IsSubMPolyfold (solutionSet (proj 1 1) (graphSection exampleMap)),
      haveI := (basePoly 1).paracompactSpace_subtype
        (solutionSet (proj 1 1) (graphSection exampleMap))
      (MPolyfold.subPolyfold hsub).IsManifoldWithCornersLoc := by
  have hreg : IsRegularOnHalfSpace (m := 1) (k := 1) exampleMap := fun x _ => by
    rw [exampleMap.fderiv]
    refine ⟨fun y => ⟨(0, fun _ => y 0), funext fun j => by fin_cases j; rfl⟩,
      fun _ => ⟨((fun _ => 1), 0), funext fun j => by fin_cases j; rfl, one_ne_zero⟩⟩
  obtain ⟨hsub, -, h2, -⟩ := theorem_3_6_11_halfSpace exampleMap.contDiff hreg
    ⟨⟨0, fun _ => le_rfl⟩, map_zero _⟩
  exact ⟨hsub, h2⟩

end HalfSpaceBundle
end Polyfold
end
