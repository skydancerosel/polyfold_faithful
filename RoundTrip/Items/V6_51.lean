import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V6_51

/-! Round trip for V6_51 (§6.5, the homotopy classes `[φ]`, pp. 227–228).

* `A`: the types of the item's theorems (universes at `0`): `mem_smoothSet_of_isScSmoothMap`,
  `contDiff_pt2_comp`, `isScHomotopyRel_reparam`, `reparam_mem`, `concatPath_halves`
  (`leftHalf`, `rightHalf`, `halvesReparam` are vocabulary).
* `B`: sc-smooth homotopy rel end points is an equivalence relation on the paths from `x` to `y`,
  homotopic paths have the same end points, and the composition through an arbitrary admissible
  `β` (with the corrected `ψ(β(s) − 1)`) exists and depends only on the classes, not on `β`.
* `A_to_B` is proved from `A`'s `contDiff_pt2_comp` and `isScHomotopyRel_reparam`.  The
  project's `IsScHomotopyRel.symm`, `.glue`, `.comp_smoothTransition`, `ScHomotopic.trans` and
  `isScHomotopyRel_concatHomotopy` all go through `contDiff_pt2_comp` (and `trans` through
  `isScHomotopyRel_reparam`), so they are re-derived here (`symm'`, `glue'`, `compKappa'`,
  `trans'`, `concatHomotopy'`) from the hypothesis, with the project's proofs.  The new glue is
  the comparison of a composite through an arbitrary `β` with `concatPath` (a straight-line
  homotopy of the reparametrizations, `lerpHomotopy`) and the remark that two paths agreeing on
  `[0, 1]` are homotopic (`agree_homotopic`, via `γ ∘ κ`).
* `B_to_A` is not proved: `A` consists of specific lemmas (an explicit homotopy formula for a
  reparametrization, the values of an sc-smooth map `ℝⁿ → X` being smooth points, the formula
  `concatPath (leftHalf γ) (rightHalf γ) = γ ∘ halvesReparam`, two calculus facts) which `B`,
  stating only the existence of homotopies and the class structure, does not contain; they are
  provable only outright, from the definitions.
-/

namespace RoundTrip.V6_51
open Polyfold Set Filter Topology
open scoped ContDiff

local notation "κ" => Real.smoothTransition

/-- The project's statement: the item's theorems, universes instantiated at `0`. -/
def A : Prop :=
  type_of% @Polyfold.mem_smoothSet_of_isScSmoothMap.{0} ∧
  type_of% @Polyfold.contDiff_pt2_comp ∧
  type_of% @Polyfold.isScHomotopyRel_reparam.{0} ∧
  type_of% @Polyfold.reparam_mem.{0} ∧
  type_of% @Polyfold.concatPath_halves.{0}

theorem A_holds : A :=
  ⟨@Polyfold.mem_smoothSet_of_isScSmoothMap.{0}, @Polyfold.contDiff_pt2_comp,
    @Polyfold.isScHomotopyRel_reparam.{0}, @Polyfold.reparam_mem.{0},
    @Polyfold.concatPath_halves.{0}⟩

section Glue

variable {X : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  (hpt2 : type_of% @Polyfold.contDiff_pt2_comp)
  {γ γ₀ γ₁ γ₂ : (Fin 1 → ℝ) → X} {Φ Ψ : (Fin 2 → ℝ) → X}

include hpt2

/-- `isScSmoothMap_comp_pt2` from the hypothesis `contDiff_pt2_comp`. -/
theorem compPt2 (hΦ : (rnPolyfold 2).IsScSmoothMap PX Φ) {σ₁ σ₂ : (Fin 2 → ℝ) → ℝ}
    (h₁ : ContDiff ℝ ∞ σ₁) (h₂ : ContDiff ℝ ∞ σ₂) :
    (rnPolyfold 2).IsScSmoothMap PX fun q => Φ (pt2 (σ₁ q) (σ₂ q)) :=
  hΦ.comp (isScSmoothMap_rn_rn_of_contDiff (hpt2 h₁ h₂))

/-- `IsScHomotopyRel.symm` (the project's proof). -/
theorem symm' (h : IsScHomotopyRel PX γ₀ γ₁ Φ) :
    IsScHomotopyRel PX γ₁ γ₀ fun q => Φ (pt2 (1 - q 0) (q 1)) where
  isScSmoothMap := compPt2 hpt2 h.isScSmoothMap
    (contDiff_const.sub (contDiff_apply ℝ ℝ 0)) (contDiff_apply ℝ ℝ 1)
  zero t ht := by simpa only [pt2_apply_zero, pt2_apply_one, sub_zero] using h.one t ht
  one t ht := by simpa only [pt2_apply_zero, pt2_apply_one, sub_self] using h.zero t ht
  start τ hτ := by
    simp only [pt2_apply_zero, pt2_apply_one]
    rw [h.start (1 - τ) ⟨by linarith [hτ.2], by linarith [hτ.1]⟩,
      ← h.start 1 ⟨zero_le_one, le_rfl⟩, h.one 0 ⟨le_rfl, zero_le_one⟩]
  finish τ hτ := by
    simp only [pt2_apply_zero, pt2_apply_one]
    rw [h.finish (1 - τ) ⟨by linarith [hτ.2], by linarith [hτ.1]⟩,
      ← h.finish 1 ⟨zero_le_one, le_rfl⟩, h.one 1 ⟨zero_le_one, le_rfl⟩]

/-- `IsScHomotopyRel.comp_smoothTransition` (the project's proof). -/
theorem compKappa' (h : IsScHomotopyRel PX γ₀ γ₁ Φ) :
    IsScHomotopyRel PX (fun s => γ₀ (pt1 (κ (s 0)))) (fun s => γ₁ (pt1 (κ (s 0))))
      fun q => Φ (pt2 (q 0) (κ (q 1))) where
  isScSmoothMap := compPt2 hpt2 h.isScSmoothMap (contDiff_apply ℝ ℝ 0)
    (Real.smoothTransition.contDiff.comp (contDiff_apply ℝ ℝ 1))
  zero t _ := by
    simp only [pt2_apply_zero, pt2_apply_one, pt1_apply]
    exact h.zero _ ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩
  one t _ := by
    simp only [pt2_apply_zero, pt2_apply_one, pt1_apply]
    exact h.one _ ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩
  start τ hτ := by
    simp only [pt2_apply_zero, pt2_apply_one, pt1_apply, Real.smoothTransition.zero]
    exact h.start τ hτ
  finish τ hτ := by
    simp only [pt2_apply_zero, pt2_apply_one, pt1_apply, Real.smoothTransition.one]
    exact h.finish τ hτ

/-- `IsScHomotopyRel.glue` (the project's proof). -/
theorem glue' (hΦ : IsScHomotopyRel PX γ₀ γ₁ Φ)
    (hΨ : IsScHomotopyRel PX γ₁ γ₂ Ψ) (h : ∀ t, Φ (pt2 1 t) = Ψ (pt2 0 t)) :
    IsScHomotopyRel PX γ₀ γ₂ (glueHomotopy Φ Ψ) where
  isScSmoothMap := by
    have h0 : ContDiff ℝ ∞ fun q : Fin 2 → ℝ => q 0 := contDiff_apply ℝ ℝ 0
    have h1 : ContDiff ℝ ∞ fun q : Fin 2 → ℝ => q 1 := contDiff_apply ℝ ℝ 1
    refine isScSmoothMap_ite (σ := fun q => q 0) (continuous_apply 0)
      (show (0 : ℝ) < 1 / 6 by norm_num)
      (compPt2 hpt2 hΦ.isScSmoothMap
        (Real.smoothTransition.contDiff.comp (contDiff_const.mul h0)) h1)
      (compPt2 hpt2 hΨ.isScSmoothMap
        (Real.smoothTransition.contDiff.comp ((contDiff_const.mul h0).sub contDiff_const)) h1)
      fun q hq => ?_
    obtain ⟨hq₁, hq₂⟩ := abs_sub_lt_iff.1 hq
    change Φ (pt2 (κ (3 * q 0)) (q 1)) = Ψ (pt2 (κ (3 * q 0 - 2)) (q 1))
    rw [Real.smoothTransition.one_of_one_le (by linarith),
      Real.smoothTransition.zero_of_nonpos (by linarith)]
    exact h _
  zero t ht := by
    simp only [glueHomotopy, pt2_apply_zero, pt2_apply_one, mul_zero,
      Real.smoothTransition.zero]
    rw [if_pos (by norm_num)]
    exact hΦ.zero t ht
  one t ht := by
    rw [glueHomotopy_one]
    exact hΨ.one t ht
  start τ hτ := by
    simp only [glueHomotopy, pt2_apply_zero, pt2_apply_one]
    split_ifs
    · exact hΦ.start _ ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩
    · rw [hΨ.start _ ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩,
        ← hΦ.one 0 ⟨le_rfl, zero_le_one⟩, hΦ.start 1 ⟨zero_le_one, le_rfl⟩]
  finish τ hτ := by
    simp only [glueHomotopy, pt2_apply_zero, pt2_apply_one]
    split_ifs
    · exact hΦ.finish _ ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩
    · rw [hΨ.finish _ ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩,
        ← hΦ.one 1 ⟨zero_le_one, le_rfl⟩, hΦ.finish 1 ⟨zero_le_one, le_rfl⟩]

/-- `ScHomotopic.symm`. -/
theorem homSymm (h : ScHomotopic PX γ₀ γ₁) : ScHomotopic PX γ₁ γ₀ :=
  let ⟨_, hΦ⟩ := h
  ⟨_, symm' hpt2 hΦ⟩

variable (hrep : type_of% @Polyfold.isScHomotopyRel_reparam.{0})
include hrep

/-- `ScHomotopic.trans` (the project's proof, with `isScHomotopyRel_reparam` from the
hypothesis). -/
theorem trans' (h₁ : ScHomotopic PX γ₀ γ₁) (h₂ : ScHomotopic PX γ₁ γ₂)
    (hγ₀ : (rnPolyfold 1).IsScSmoothMap PX γ₀) (hγ₂ : (rnPolyfold 1).IsScSmoothMap PX γ₂) :
    ScHomotopic PX γ₀ γ₂ := by
  obtain ⟨Φ, hΦ⟩ := h₁
  obtain ⟨Ψ, hΨ⟩ := h₂
  have hκ : ContDiff ℝ ∞ κ := Real.smoothTransition.contDiff
  have H₀ := symm' hpt2 (hrep hγ₀ hκ Real.smoothTransition.zero Real.smoothTransition.one)
  have H₂ := hrep hγ₂ hκ Real.smoothTransition.zero Real.smoothTransition.one
  have hI : ∀ t, κ t ∈ Icc (0 : ℝ) 1 := fun t =>
    ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩
  refine ⟨_, glue' hpt2 (glue' hpt2 (glue' hpt2 H₀ (compKappa' hpt2 hΦ) fun t => ?_)
    (compKappa' hpt2 hΨ) fun t => ?_) H₂ fun t => ?_⟩
  · simp only [pt2_apply_zero, pt2_apply_one, sub_self, sub_zero, one_mul, zero_mul, add_zero]
    exact (hΦ.zero _ (hI t)).symm
  · rw [glueHomotopy_one]
    simp only [pt2_apply_zero, pt2_apply_one]
    rw [hΦ.one _ (hI t), hΨ.zero _ (hI t)]
  · rw [glueHomotopy_one]
    simp only [pt2_apply_zero, pt2_apply_one, sub_zero, one_mul, zero_mul, add_zero]
    exact hΨ.one _ (hI t)

/-- **Two sc-smooth paths which agree on `[0, 1]` are homotopic**: `γ ≃ γ ∘ κ = γ' ∘ κ ≃ γ'`. -/
theorem agree_homotopic {γ γ' : (Fin 1 → ℝ) → X} (hγ : (rnPolyfold 1).IsScSmoothMap PX γ)
    (hγ' : (rnPolyfold 1).IsScSmoothMap PX γ') (h : ∀ t ∈ Icc (0 : ℝ) 1, γ (pt1 t) = γ' (pt1 t)) :
    ScHomotopic PX γ γ' := by
  have hκ : ContDiff ℝ ∞ κ := Real.smoothTransition.contDiff
  have H := hrep hγ hκ Real.smoothTransition.zero Real.smoothTransition.one
  have H' := hrep hγ' hκ Real.smoothTransition.zero Real.smoothTransition.one
  have heq : (fun s : Fin 1 → ℝ => γ (pt1 (κ (s 0)))) = fun s => γ' (pt1 (κ (s 0))) :=
    funext fun s => h _ ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩
  have hγκ : (rnPolyfold 1).IsScSmoothMap PX fun s => γ (pt1 (κ (s 0))) :=
    isScSmoothMap_reparam hγ hκ
  refine trans' hpt2 hrep (homSymm hpt2 ⟨_, H⟩) ?_ hγ hγ'
  rw [heq]
  exact ⟨_, H'⟩

end Glue

/-! ### Composites through `β` -/

section Comp

variable {X : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}

/-- The composite of `φ` and `ψ` through `β`, on all of `ℝ`. -/
noncomputable def F (β : ℝ → ℝ) (φ ψ : (Fin 1 → ℝ) → X) : (Fin 1 → ℝ) → X := fun s =>
  if s 0 ≤ 1 / 2 then φ (pt1 (β (s 0))) else ψ (pt1 (β (s 0) - 1))

omit [TopologicalSpace X] [T2Space X] [ParacompactSpace X] in
theorem F_of_le {β : ℝ → ℝ} {φ ψ : (Fin 1 → ℝ) → X} {s : Fin 1 → ℝ} (h : s 0 ≤ 1 / 2) :
    F β φ ψ s = φ (pt1 (β (s 0))) := if_pos h

omit [TopologicalSpace X] [T2Space X] [ParacompactSpace X] in
theorem F_of_gt {β : ℝ → ℝ} {φ ψ : (Fin 1 → ℝ) → X} {s : Fin 1 → ℝ} (h : 1 / 2 < s 0) :
    F β φ ψ s = ψ (pt1 (β (s 0) - 1)) := if_neg (not_le.2 h)

/-- What is used of an admissible `β`. -/
structure GoodBeta (β : ℝ → ℝ) : Prop where
  smooth : ContDiff ℝ ∞ β
  zero : β 0 = 0
  one : β 1 = 2
  mid : ∃ ε > 0, ∀ s, |s - 1 / 2| < ε → β s = 1

theorem goodBeta_of_admissible {β : ℝ → ℝ} (hβ : IsAdmissibleBetaB β) : GoodBeta β := by
  obtain ⟨hβs, hβ0, hβ1, hβ₁, hβ₂, hβc⟩ := hβ
  have hb : β (1 / 2) = 1 := by
    have h1 : β (1 / 2) ∈ Icc (0 : ℝ) 1 := hβ₁ ▸ mem_image_of_mem β ⟨by norm_num, le_rfl⟩
    have h2 : β (1 / 2) ∈ Icc (1 : ℝ) 2 := hβ₂ ▸ mem_image_of_mem β ⟨le_rfl, by norm_num⟩
    exact le_antisymm h1.2 h2.1
  obtain ⟨ε, hε, hεb⟩ := Metric.eventually_nhds_iff.1 hβc
  exact ⟨hβs, hβ0, hβ1, ε, hε, fun s hs => (hεb (by rwa [Real.dist_eq])).trans hb⟩

/-- The reparametrization of `concatPath`: `β_c(s) = κ(3s) + κ(3s − 2)`. -/
noncomputable def βc (s : ℝ) : ℝ := κ (3 * s) + κ (3 * s - 2)

theorem goodBeta_βc : GoodBeta βc where
  smooth := (Real.smoothTransition.contDiff.comp (contDiff_const.mul contDiff_id)).add
    (Real.smoothTransition.contDiff.comp ((contDiff_const.mul contDiff_id).sub contDiff_const))
  zero := by
    simp only [βc]
    rw [Real.smoothTransition.zero_of_nonpos (by norm_num),
      Real.smoothTransition.zero_of_nonpos (by norm_num)]
    norm_num
  one := by
    simp only [βc]
    rw [Real.smoothTransition.one_of_one_le (by norm_num),
      Real.smoothTransition.one_of_one_le (by norm_num)]
    norm_num
  mid := ⟨1 / 6, by norm_num, fun s hs => by
    obtain ⟨h1, h2⟩ := abs_sub_lt_iff.1 hs
    simp only [βc]
    rw [Real.smoothTransition.one_of_one_le (by linarith),
      Real.smoothTransition.zero_of_nonpos (by linarith)]
    norm_num⟩

theorem admissible_βc : IsAdmissibleBetaB βc := by
  have hκc : Continuous κ := Real.smoothTransition.continuous
  refine ⟨goodBeta_βc.smooth, goodBeta_βc.zero, goodBeta_βc.one, ?_, ?_, ?_⟩
  · have heq : EqOn βc (fun s => κ (3 * s)) (Icc 0 (1 / 2)) := fun s hs => by
      simp only [βc, Real.smoothTransition.zero_of_nonpos (by linarith [hs.2] : 3 * s - 2 ≤ 0),
        add_zero]
    rw [heq.image_eq]
    apply Subset.antisymm
    · rintro _ ⟨s, -, rfl⟩
      exact ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩
    · intro y hy
      have hcont : ContinuousOn (fun s => κ (3 * s)) (Icc 0 (1 / 3)) :=
        (hκc.comp (continuous_const.mul continuous_id)).continuousOn
      have hivt := intermediate_value_Icc (by norm_num : (0 : ℝ) ≤ 1 / 3) hcont
      have h0 : κ (3 * 0) = 0 := by simp
      have h1 : κ (3 * (1 / 3)) = 1 := by norm_num
      rw [h0, h1] at hivt
      obtain ⟨s, hs, hs'⟩ := hivt hy
      exact ⟨s, ⟨hs.1, by linarith [hs.2]⟩, hs'⟩
  · have heq : EqOn βc (fun s => 1 + κ (3 * s - 2)) (Icc (1 / 2) 1) := fun s hs => by
      simp only [βc, Real.smoothTransition.one_of_one_le (by linarith [hs.1] : 1 ≤ 3 * s)]
    rw [heq.image_eq]
    apply Subset.antisymm
    · rintro _ ⟨s, -, rfl⟩
      exact ⟨by linarith [Real.smoothTransition.nonneg (3 * s - 2)],
        by linarith [Real.smoothTransition.le_one (3 * s - 2)]⟩
    · intro y hy
      have hcont : ContinuousOn (fun s => 1 + κ (3 * s - 2)) (Icc (2 / 3) 1) :=
        (continuous_const.add (hκc.comp ((continuous_const.mul continuous_id).sub
          continuous_const))).continuousOn
      have hivt := intermediate_value_Icc (by norm_num : (2 / 3 : ℝ) ≤ 1) hcont
      have h0 : 1 + κ (3 * (2 / 3) - 2) = 1 := by norm_num
      have h1 : 1 + κ (3 * 1 - 2) = 2 := by norm_num
      rw [h0, h1] at hivt
      obtain ⟨s, hs, hs'⟩ := hivt hy
      exact ⟨s, ⟨by linarith [hs.1], hs.2⟩, hs'⟩
  · have hmem : Ioo (1 / 3 : ℝ) (2 / 3) ∈ 𝓝 (1 / 2 : ℝ) := Ioo_mem_nhds (by norm_num) (by norm_num)
    filter_upwards [hmem] with s hs
    simp only [βc]
    rw [Real.smoothTransition.one_of_one_le (by linarith [hs.1] : 1 ≤ 3 * s),
      Real.smoothTransition.zero_of_nonpos (by linarith [hs.2] : 3 * s - 2 ≤ 0),
      Real.smoothTransition.one_of_one_le (by norm_num : (1 : ℝ) ≤ 3 * (1 / 2)),
      Real.smoothTransition.zero_of_nonpos (by norm_num : 3 * (1 / 2 : ℝ) - 2 ≤ 0)]

theorem concatPath_eq_F (φ ψ : (Fin 1 → ℝ) → X) : concatPath φ ψ = F βc φ ψ := by
  funext s
  rcases le_or_gt (s 0) (1 / 2) with h | h
  · rw [concatPath_of_le h]
    simp only [F, βc, if_pos h,
      Real.smoothTransition.zero_of_nonpos (by linarith : 3 * s 0 - 2 ≤ 0), add_zero]
  · rw [concatPath_of_gt h]
    simp only [F, βc, if_neg (not_le.2 h),
      Real.smoothTransition.one_of_one_le (by linarith : 1 ≤ 3 * s 0), add_sub_cancel_left]

theorem isScSmoothMap_F {β : ℝ → ℝ} (hβ : GoodBeta β) {φ ψ : (Fin 1 → ℝ) → X}
    (hφ : (rnPolyfold 1).IsScSmoothMap PX φ) (hψ : (rnPolyfold 1).IsScSmoothMap PX ψ)
    (h : φ (pt1 1) = ψ (pt1 0)) : (rnPolyfold 1).IsScSmoothMap PX (F β φ ψ) := by
  obtain ⟨ε, hε, hεb⟩ := hβ.mid
  refine isScSmoothMap_ite (σ := fun s => s 0) (continuous_apply 0) hε
    (isScSmoothMap_reparam hφ hβ.smooth)
    (@isScSmoothMap_reparam X _ _ _ PX ψ hψ (fun t => β t - 1) (hβ.smooth.sub contDiff_const))
    fun q hq => ?_
  change φ (pt1 (β (q 0))) = ψ (pt1 (β (q 0) - 1))
  rw [hεb _ hq, sub_self]; exact h

/-- **The straight-line homotopy of the reparametrizations** between the composites through two
`β`s. -/
theorem lerpHomotopy {β₁ β₂ : ℝ → ℝ} (h₁ : GoodBeta β₁) (h₂ : GoodBeta β₂)
    {φ ψ : (Fin 1 → ℝ) → X}
    (hφ : (rnPolyfold 1).IsScSmoothMap PX φ) (hψ : (rnPolyfold 1).IsScSmoothMap PX ψ)
    (h : φ (pt1 1) = ψ (pt1 0)) : ScHomotopic PX (F β₁ φ ψ) (F β₂ φ ψ) := by
  obtain ⟨ε₁, hε₁, hb₁⟩ := h₁.mid
  obtain ⟨ε₂, hε₂, hb₂⟩ := h₂.mid
  set L : (Fin 2 → ℝ) → ℝ := fun q => (1 - q 0) * β₁ (q 1) + q 0 * β₂ (q 1) with hL
  have hLs : ContDiff ℝ ∞ L := contDiff_lerp h₁.smooth h₂.smooth
  refine ⟨fun q => if q 1 ≤ 1 / 2 then φ (pt1 (L q)) else ψ (pt1 (L q - 1)), ?_, ?_, ?_, ?_, ?_⟩
  · refine isScSmoothMap_ite (σ := fun q => q 1) (continuous_apply 1) (lt_min hε₁ hε₂)
      (isScSmoothMap_comp_pt1₂ hφ hLs) (isScSmoothMap_comp_pt1₂ hψ (hLs.sub contDiff_const))
      fun q hq => ?_
    have e : L q = 1 := by
      simp only [hL, hb₁ _ (lt_of_lt_of_le hq (min_le_left _ _)),
        hb₂ _ (lt_of_lt_of_le hq (min_le_right _ _))]
      ring
    rw [e, sub_self]; exact h
  · intro t _
    simp only [F, hL, pt2_apply_zero, pt2_apply_one, pt1_apply, sub_zero, one_mul, zero_mul,
      add_zero]
    by_cases ht : t ≤ 1 / 2 <;> simp
  · intro t _
    simp only [F, hL, pt2_apply_zero, pt2_apply_one, pt1_apply, sub_self, one_mul, zero_mul,
      zero_add]
    by_cases ht : t ≤ 1 / 2 <;> simp
  · intro τ _
    simp only [F, hL, pt2_apply_zero, pt2_apply_one, pt1_apply, h₁.zero, h₂.zero, mul_zero,
      add_zero, if_pos (by norm_num : (0 : ℝ) ≤ 1 / 2)]
  · intro τ _
    simp only [F, hL, pt2_apply_zero, pt2_apply_one, pt1_apply, h₁.one, h₂.one,
      if_neg (by norm_num : ¬ (1 : ℝ) ≤ 1 / 2)]
    congr 2
    ring

end Comp

section ConcatH

variable {X : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  (hpt2 : type_of% @Polyfold.contDiff_pt2_comp)
  {γ₁ γ₁' γ₂ γ₂' : (Fin 1 → ℝ) → X} {Φ Ψ : (Fin 2 → ℝ) → X}

include hpt2

/-- `isScHomotopyRel_concatHomotopy` (the project's proof). -/
theorem concatHomotopy' (hΦ : IsScHomotopyRel PX γ₁ γ₁' Φ)
    (hΨ : IsScHomotopyRel PX γ₂ γ₂' Ψ) (h : γ₁ (pt1 1) = γ₂ (pt1 0)) :
    IsScHomotopyRel PX (concatPath γ₁ γ₂) (concatPath γ₁' γ₂') (concatHomotopy Φ Ψ) where
  isScSmoothMap := by
    have h0 : ContDiff ℝ ∞ fun q : Fin 2 → ℝ => q 0 := contDiff_apply ℝ ℝ 0
    have h1 : ContDiff ℝ ∞ fun q : Fin 2 → ℝ => q 1 := contDiff_apply ℝ ℝ 1
    have hκ0 : ContDiff ℝ ∞ fun q : Fin 2 → ℝ => κ (q 0) := Real.smoothTransition.contDiff.comp h0
    refine isScSmoothMap_ite (σ := fun q => q 1) (continuous_apply 1)
      (show (0 : ℝ) < 1 / 6 by norm_num)
      (compPt2 hpt2 hΦ.isScSmoothMap hκ0
        (Real.smoothTransition.contDiff.comp (contDiff_const.mul h1)))
      (compPt2 hpt2 hΨ.isScSmoothMap hκ0
        (Real.smoothTransition.contDiff.comp ((contDiff_const.mul h1).sub contDiff_const)))
      fun q hq => ?_
    obtain ⟨hq₁, hq₂⟩ := abs_sub_lt_iff.1 hq
    change Φ (pt2 (κ (q 0)) (κ (3 * q 1))) = Ψ (pt2 (κ (q 0)) (κ (3 * q 1 - 2)))
    rw [Real.smoothTransition.one_of_one_le (x := 3 * q 1) (by linarith),
      Real.smoothTransition.zero_of_nonpos (x := 3 * q 1 - 2) (by linarith),
      hΦ.finish _ ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩,
      hΨ.start _ ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩, h]
  zero t _ := by
    simp only [concatHomotopy, pt2_apply_zero, pt2_apply_one, Real.smoothTransition.zero]
    rcases le_or_gt t (1 / 2) with ht | ht
    · rw [if_pos ht, concatPath_of_le (s := pt1 t) ht, pt1_apply]
      exact hΦ.zero _ ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩
    · rw [if_neg (not_le.2 ht), concatPath_of_gt (s := pt1 t) ht, pt1_apply]
      exact hΨ.zero _ ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩
  one t _ := by
    simp only [concatHomotopy, pt2_apply_zero, pt2_apply_one, Real.smoothTransition.one]
    rcases le_or_gt t (1 / 2) with ht | ht
    · rw [if_pos ht, concatPath_of_le (s := pt1 t) ht, pt1_apply]
      exact hΦ.one _ ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩
    · rw [if_neg (not_le.2 ht), concatPath_of_gt (s := pt1 t) ht, pt1_apply]
      exact hΨ.one _ ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩
  start τ _ := by
    simp only [concatHomotopy, pt2_apply_zero, pt2_apply_one, mul_zero,
      Real.smoothTransition.zero]
    rw [if_pos (by norm_num), concatPath_zero]
    exact hΦ.start _ ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩
  finish τ _ := by
    simp only [concatHomotopy, pt2_apply_zero, pt2_apply_one]
    rw [if_neg (by norm_num), show (3 : ℝ) * 1 - 2 = 1 by norm_num, Real.smoothTransition.one,
      concatPath_one]
    exact hΨ.finish _ ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩

end ConcatH

/-! ### `A ⇒ B` -/

theorem A_to_B : A → B := by
  rintro ⟨-, hpt2, hrep, -, -⟩ X _ _ _ PX
  -- the end points of a homotopic path
  have hends : ∀ (γ γ' : (Fin 1 → ℝ) → X) (x y : X), IsPathB PX γ x y →
      (rnPolyfold 1).IsScSmoothMap PX γ' → ScHomotopic PX γ γ' → IsPathB PX γ' x y := by
    rintro γ γ' x y ⟨-, h0, h1⟩ hγ' ⟨Φ, hΦ⟩
    refine ⟨hγ', ?_, ?_⟩
    · rw [← hΦ.one 0 ⟨le_rfl, zero_le_one⟩, hΦ.start 1 ⟨zero_le_one, le_rfl⟩, h0]
    · rw [← hΦ.one 1 ⟨zero_le_one, le_rfl⟩, hΦ.finish 1 ⟨zero_le_one, le_rfl⟩, h1]
  refine ⟨fun x y => ⟨fun γ => ScHomotopic.refl γ.2.1, fun h => homSymm hpt2 h,
    fun {a _ c} h₁ h₂ => trans' hpt2 hrep h₁ h₂ a.2.1 c.2.1⟩, hends, ⟨βc, admissible_βc⟩, ?_, ?_⟩
  · -- existence of the composite through `β`
    intro β hβ φ ψ x y z hφ hψ
    have hgβ := goodBeta_of_admissible hβ
    have hy : φ (pt1 1) = ψ (pt1 0) := hφ.2.2.trans hψ.2.1.symm
    refine ⟨F β φ ψ, ⟨isScSmoothMap_F hgβ hφ.1 hψ.1 hy, ?_, ?_⟩, ?_, ?_⟩
    · rw [F_of_le (s := pt1 0) (by norm_num [pt1_apply]), pt1_apply, hgβ.zero]; exact hφ.2.1
    · rw [F_of_gt (s := pt1 1) (by norm_num [pt1_apply]), pt1_apply, hgβ.one]
      norm_num; exact hψ.2.2
    · intro s hs
      rw [F_of_le (s := pt1 s) (by rw [pt1_apply]; exact hs.2), pt1_apply]
    · intro s hs
      rcases eq_or_lt_of_le hs.1 with h | h
      · subst h
        rw [F_of_le (s := pt1 (1 / 2)) (by rw [pt1_apply]), pt1_apply]
        obtain ⟨ε, hε, hεb⟩ := hgβ.mid
        rw [hεb _ (by simpa using hε), sub_self]; exact hy
      · rw [F_of_gt (s := pt1 s) (by rw [pt1_apply]; exact h), pt1_apply]
  · -- well defined on classes and independent of `β`
    intro β β' hβ hβ' φ φ' ψ ψ' γ γ' x y z hφ hφ' hψ hψ' hγ hγ' hφφ' hψψ' hc hc'
    have gβ := goodBeta_of_admissible hβ
    have gβ' := goodBeta_of_admissible hβ'
    have hy : φ (pt1 1) = ψ (pt1 0) := hφ.2.2.trans hψ.2.1.symm
    have hy' : φ' (pt1 1) = ψ' (pt1 0) := hφ'.2.2.trans hψ'.2.1.symm
    -- a path agreeing with the composite through `β` on `[0, 1]` is homotopic to it
    have hagree : ∀ {β : ℝ → ℝ} (gβ : GoodBeta β) {φ ψ γ : (Fin 1 → ℝ) → X},
        (rnPolyfold 1).IsScSmoothMap PX φ → (rnPolyfold 1).IsScSmoothMap PX ψ →
        φ (pt1 1) = ψ (pt1 0) → (rnPolyfold 1).IsScSmoothMap PX γ → IsConcatB β φ ψ γ →
        ScHomotopic PX γ (F β φ ψ) := by
      intro β gβ φ ψ γ hφs hψs hy hγs hc
      refine agree_homotopic hpt2 hrep hγs (isScSmoothMap_F gβ hφs hψs hy) fun t ht => ?_
      rcases le_or_gt t (1 / 2) with h | h
      · rw [F_of_le (s := pt1 t) (by rw [pt1_apply]; exact h), pt1_apply]
        exact hc.1 t ⟨ht.1, h⟩
      · rw [F_of_gt (s := pt1 t) (by rw [pt1_apply]; exact h), pt1_apply]
        exact hc.2 t ⟨h.le, ht.2⟩
    have s₁ := isScSmoothMap_F gβ hφ.1 hψ.1 hy
    have s₂ := isScSmoothMap_F goodBeta_βc hφ.1 hψ.1 hy
    have s₃ := isScSmoothMap_F goodBeta_βc hφ'.1 hψ'.1 hy'
    have s₄ := isScSmoothMap_F gβ' hφ'.1 hψ'.1 hy'
    have k₁ := hagree gβ hφ.1 hψ.1 hy hγ.1 hc
    have k₂ := lerpHomotopy gβ goodBeta_βc hφ.1 hψ.1 hy
    have k₃ : ScHomotopic PX (F βc φ ψ) (F βc φ' ψ') := by
      obtain ⟨Φ, hΦ⟩ := hφφ'
      obtain ⟨Ψ, hΨ⟩ := hψψ'
      rw [← concatPath_eq_F, ← concatPath_eq_F]
      exact ⟨_, concatHomotopy' hpt2 hΦ hΨ hy⟩
    have k₄ := homSymm hpt2 (lerpHomotopy gβ' goodBeta_βc hφ'.1 hψ'.1 hy')
    have k₅ := homSymm hpt2 (hagree gβ' hφ'.1 hψ'.1 hy' hγ'.1 hc')
    exact trans' hpt2 hrep (trans' hpt2 hrep (trans' hpt2 hrep (trans' hpt2 hrep k₁ k₂ hγ.1 s₂)
      k₃ hγ.1 s₃) k₄ hγ.1 s₄) k₅ hγ.1 hγ'.1

/-! ### `B ⇒ A` only outright

`A`'s lemmas are re-proved from the definitions (the project's proofs, under new names); `B` is
not used.  This only shows that `A`'s extra content is lemma-level, not that `B` contains it. -/

theorem A_outright : A := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro X _ _ _ PX n γ hγ p
    exact mem_iInter.2 fun m => hγ.mapsTo_levelSet m (by rw [rnPolyfold_levelSet]; exact mem_univ p)
  · intro k σ₁ σ₂ h₁ h₂
    refine contDiff_pi.2 fun i => ?_
    fin_cases i
    · simpa only [Fin.zero_eta, Fin.isValue, pt2_apply_zero] using h₁
    · simpa only [Fin.mk_one, Fin.isValue, pt2_apply_one] using h₂
  · intro X _ _ _ PX γ hγ θ hθ h0 h1
    exact
      { isScSmoothMap := by
          refine hγ.comp (isScSmoothMap_rn_rn_of_contDiff (contDiff_pt1_comp₂ ?_))
          have h0c : ContDiff ℝ ∞ fun q : Fin 2 → ℝ => q 0 := contDiff_apply ℝ ℝ 0
          have h1c : ContDiff ℝ ∞ fun q : Fin 2 → ℝ => q 1 := contDiff_apply ℝ ℝ 1
          exact ((contDiff_const.sub h0c).mul (hθ.comp h1c)).add (h0c.mul h1c)
        zero := fun t _ => by simp
        one := fun t _ => by simp
        start := fun τ _ => by simp [h0]
        finish := fun τ _ => by
          simp only [pt2_apply_zero, pt2_apply_one, h1, mul_one, pt1_apply]
          congr 2
          ring }
  · intro X γ U hγU θ hθI τ s hτ hs
    simp only [pt2_apply_zero, pt2_apply_one]
    apply hγU
    have hθs := hθI s hs
    constructor
    · nlinarith [hτ.1, hτ.2, hs.1, hθs.1]
    · nlinarith [hτ.1, hτ.2, hs.2, hθs.2]
  · intro X _ _ _ γ
    funext s
    rcases le_or_gt (s 0) (1 / 2) with hs | hs
    · rw [concatPath_of_le hs]
      simp only [leftHalf, pt1_apply, halvesReparam]
      rw [Real.smoothTransition.zero_of_nonpos (by linarith : 3 * s 0 - 2 ≤ 0), add_zero]
    · rw [concatPath_of_gt hs]
      simp only [rightHalf, pt1_apply, halvesReparam]
      rw [Real.smoothTransition.one_of_one_le (by linarith : 1 ≤ 3 * s 0)]

/-- Vacuous (the hypothesis is not used). -/
theorem B_to_A : B → A := fun _ => A_outright

#rt_check RoundTrip.V6_51.B_to_A [Polyfold.mem_smoothSet_of_isScSmoothMap,
  Polyfold.contDiff_pt2_comp, Polyfold.isScHomotopyRel_reparam, Polyfold.reparam_mem,
  Polyfold.concatPath_halves]
#rt_overlap RoundTrip.V6_51.B_to_A [Polyfold.mem_smoothSet_of_isScSmoothMap,
  Polyfold.contDiff_pt2_comp, Polyfold.isScHomotopyRel_reparam, Polyfold.reparam_mem,
  Polyfold.concatPath_halves]

#rt_check RoundTrip.V6_51.A_to_B [Polyfold.mem_smoothSet_of_isScSmoothMap,
  Polyfold.contDiff_pt2_comp, Polyfold.isScHomotopyRel_reparam, Polyfold.reparam_mem,
  Polyfold.concatPath_halves]

end RoundTrip.V6_51
