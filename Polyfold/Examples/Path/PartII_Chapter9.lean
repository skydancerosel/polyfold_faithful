import Polyfold.Chapter9.LocallyEquidimensional
import Polyfold.Chapter9.TangentSlicesRn
import Polyfold.Chapter9.SheetMeasure
import Polyfold.Chapter9.MeasureEffective
import Polyfold.Chapter19.BasicRegularity
import Polyfold.Examples.OrbifoldSquareStructure

/-!
# Chapter 9: examples and non-examples (rows V9.2, V9.13, V9.50, V9.54, V9.66)

* `v9_2_axis_isNDimensional_one_not_zero`: `1_L` (`L` the x-axis of `ℝ²`) is `1`-dimensional
  and not `0`-dimensional.
* `v9_13_tangentSum_origin`: two local branching structures at `0 ∈ ℝ²` with no common sheet
  near `0` have the same tangent sum.
* `v9_50_axis_orbitSupp_not_null`: `|supp 1_L|` does not have `1`-dimensional measure zero.
* `v9_54_X5_count_free`, `v9_54_X5_count_center`, `v9_54_X5_exists`: the count
  `#(G_x/H) · #G_y = #G_x` in `ℤ/5 ⋉ ℂ` at `x = 0`, as `5 · 1 = 5` for `y ≠ 0` and `1 · 5 = 5`
  for `y = 0`.
* `v9_66_axis_not_isCompactBranched`: `1_L` is not compact.
-/

set_option maxSynthPendingDepth 3

open Set Function Filter Topology

noncomputable section

namespace Polyfold.Examples.Path

open Polyfold.EpGroupoid

theorem zero_mem_supp_axis2 :
    (0 : Fin 2 → ℝ) ∈ supp (axis2.indicator (1 : (Fin 2 → ℝ) → ℚ)) := by
  simp [supp, zero_mem_axis2]

/-! ### Row V9.2 -/

/-- Row V9.2, Definition 9.1.2 (p. 402): `1_L`, `L` the x-axis of `ℝ²`, is `1`-dimensional and
not `0`-dimensional. -/
theorem v9_2_axis_isNDimensional_one_not_zero :
    (trivial (rnPolyfold 2)).IsNDimensional (axis2.indicator 1) 1 ∧
      ¬ (trivial (rnPolyfold 2)).IsNDimensional (axis2.indicator 1) 0 :=
  ⟨indicator_axis2_branched.2, fun h => absurd
    (definition_9_1_2_footnote indicator_axis2_branched.2 h ⟨0, zero_mem_supp_axis2⟩)
    (by norm_num)⟩

/-! ### Row V9.13 -/

/-- Row V9.13, Theorem 9.2.1 (p. 409): at `0 ∈ ℝ²` the two local branching structures of
Remark 9.1.3 (b) for `β₁ = expNegInvGlue`, `β₂(s) = β₁(-s)` share no sheet near `0` and have the
same tangent sum. -/
theorem v9_13_tangentSum_origin :
    (∀ V : Set (Fin 2 → ℝ), IsOpen V → (0 : Fin 2 → ℝ) ∈ V → ∀ i j,
      (remark913Hyp_expNegInvGlue.structureβ 0).M i ∩ V ≠
        (remark913Hyp_expNegInvGlue.structureγ 0).M j ∩ V) ∧
      (remark913Hyp_expNegInvGlue.structureβ 0).tangentSum =
        (remark913Hyp_expNegInvGlue.structureγ 0).tangentSum :=
  ⟨(remark_9_1_3_b remark913Hyp_expNegInvGlue).2.2.2,
    remark913Hyp_expNegInvGlue.tangentSum_structureβ_eq_structureγ 0⟩

/-! ### Row V9.50 -/

/-- Row V9.50, Lemma 9.5.2 (p. 437): `|supp 1_L|`, `L` the x-axis of `ℝ²`, does not have
`1`-dimensional measure zero. -/
theorem v9_50_axis_orbitSupp_not_null :
    ¬ (trivial (rnPolyfold 2)).IsMeasureZeroH 1 (axis2.indicator 1)
      ((trivial (rnPolyfold 2)).orbitSupp (axis2.indicator 1)) :=
  not_isMeasureZeroH_orbitSupp indicator_axis2_branched.2 indicator_axis2_branched.1.isFunctorial
    ⟨0, zero_mem_supp_axis2⟩

/-! ### Row V9.54 -/

section X5

open Polyfold.Examples.OrbifoldSquare

theorem card_isotropy_X5_zero : Nat.card (X5.Isotropy (0 : Fin 2 → ℝ)) = 5 := by
  rw [Nat.card_congr isotropyZeroEquiv.toEquiv, Nat.card_congr Multiplicative.toAdd,
    Nat.card_zmod]

theorem card_isotropy_X5_of_ne_zero {y : Fin 2 → ℝ} (hy : y ≠ 0) :
    Nat.card (X5.Isotropy y) = 1 :=
  Nat.card_eq_one_iff_exists.2 ⟨1, isRegular_X5_iff.2 hy⟩

/-- Row V9.54, Lemma 9.5.9 (p. 442): in `ℤ/5 ⋉ ℂ`, for a natural representation at `x = 0` and
`y ≠ 0` in `U(x)`, the stabilizer `H` of `y` is trivial and `#(G_x/H) · #G_y = #G_x` reads
`5 · 1 = 5`. -/
theorem v9_54_X5_count_free (R : X5.NaturalRep (0 : Fin 2 → ℝ)) (a : R.U)
    (ha : (a : Fin 2 → ℝ) ≠ 0) :
    MulAction.stabilizer (X5.Isotropy (0 : Fin 2 → ℝ)) a = ⊥ ∧
      Nat.card (X5.Isotropy (0 : Fin 2 → ℝ) ⧸
        MulAction.stabilizer (X5.Isotropy (0 : Fin 2 → ℝ)) a) = 5 ∧
      Nat.card (X5.Isotropy (a : Fin 2 → ℝ)) = 1 ∧ Nat.card (X5.Isotropy (0 : Fin 2 → ℝ)) = 5 := by
  have h1 := card_isotropy_X5_of_ne_zero ha
  have h5 := card_isotropy_X5_zero
  refine ⟨?_, ?_, h1, h5⟩
  · ext g
    rw [R.mem_stabilizer_iff_Φ, Subgroup.mem_bot,
      EpGroupoid.Examples.action_Φ_eq isScSmoothMap_smul R g a.2]
    constructor
    · intro h
      by_contra hg
      have hg1 : g.val.1 ≠ 1 := fun e =>
        hg (GroupoidStr.Isotropy.ext (Prod.ext e g.src_val))
      exact ha ((smul_eq_self_iff hg1 _).1 h)
    · rintro rfl
      exact one_smul G5 _
  · have h := R.card_quotient_stabilizer_mul_card_isotropy a
    rw [h1, h5, mul_one] at h
    exact h

/-- Row V9.54, Lemma 9.5.9 (p. 442): in `ℤ/5 ⋉ ℂ`, for a natural representation at `x = 0` and
`y = 0`, the stabilizer of `y` is all of `G_x` and the count reads `1 · 5 = 5`. -/
theorem v9_54_X5_count_center (R : X5.NaturalRep (0 : Fin 2 → ℝ)) :
    MulAction.stabilizer (X5.Isotropy (0 : Fin 2 → ℝ)) (⟨0, R.mem_U⟩ : R.U) = ⊤ ∧
      Nat.card (X5.Isotropy (0 : Fin 2 → ℝ) ⧸
        MulAction.stabilizer (X5.Isotropy (0 : Fin 2 → ℝ)) (⟨0, R.mem_U⟩ : R.U)) = 1 := by
  refine ⟨eq_top_iff.2 fun g _ => R.mem_stabilizer_iff_Φ.2 (R.Φ_self g), ?_⟩
  have h := R.card_quotient_stabilizer_mul_card_isotropy ⟨0, R.mem_U⟩
  have h5 : Nat.card (X5.Isotropy (((⟨0, R.mem_U⟩ : R.U)) : Fin 2 → ℝ)) = 5 :=
    card_isotropy_X5_zero
  rw [h5] at h
  omega

/-- Row V9.54, Lemma 9.5.9 (p. 442): `ℤ/5 ⋉ ℂ` has a natural representation at `0` whose
domain contains a point `y ≠ 0`. -/
theorem v9_54_X5_exists :
    ∃ (R : X5.NaturalRep (0 : Fin 2 → ℝ)) (a : R.U), (a : Fin 2 → ℝ) ≠ 0 := by
  obtain ⟨-, R, -⟩ := NatRepConstruction.exists_naturalRep_sheets (X := X5)
    (0 : Fin 2 → ℝ) isOpen_univ (mem_univ _)
  have hN : R.U ∈ 𝓝[≠] (0 : Fin 2 → ℝ) := mem_nhdsWithin_of_mem_nhds (R.isOpen_U.mem_nhds R.mem_U)
  obtain ⟨y, hyU, hy0⟩ := Filter.nonempty_of_mem (inter_mem hN self_mem_nhdsWithin)
  exact ⟨R, ⟨y, hyU⟩, hy0⟩

end X5

/-! ### Row V9.66 -/

/-- Row V9.66, Theorem 9.5.4 (p. 438): `1_L`, `L` the x-axis of `ℝ²`, is a `1`-dimensional
branched ep⁺-subgroupoid that is not compact. -/
theorem v9_66_axis_not_isCompactBranched :
    ¬ (trivial (rnPolyfold 2)).IsCompactBranched (axis2.indicator 1) := by
  intro h
  have h2 := (h.image (trivialOrbitHomeomorph (rnPolyfold 2)).continuous).image
    (continuous_apply (0 : Fin 2))
  have e : (fun v : Fin 2 → ℝ => v 0) '' (trivialOrbitHomeomorph (rnPolyfold 2) ''
      (trivial (rnPolyfold 2)).orbitSupp (axis2.indicator 1)) = univ := by
    refine eq_univ_of_forall fun t => ⟨![t, 0], ⟨(trivial (rnPolyfold 2)).π ![t, 0],
      ⟨![t, 0], ?_, rfl⟩, rfl⟩, by simp⟩
    simp [supp, graph2]
  rw [e] at h2
  exact noncompact_univ ℝ h2

end Polyfold.Examples.Path
