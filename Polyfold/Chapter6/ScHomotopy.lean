import Polyfold.Chapter6.PropagationWellDefined

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory I* (2014 preprint), Part I, §6.5, p. 228:
the sc-smooth homotopy classes of paths with end points fixed, before **Theorem 6.6.13 (preprint 6.37)**
*(book 2017: before Theorem 6.2; see `BookConcordance.md`)*.

# Reparametrizations of sc-smooth paths

## The text, paraphrased

"Let `X` be an M-polyfold and `φ : [0, 1] → X` a sc-smooth map. We denote by `[φ]` its sc-smooth
homotopy class with end points fixed" (p. 228).

## What is formalized

* `isScHomotopyRel_reparam`: for a `C^∞` map `θ : ℝ → ℝ` with `θ(0) = 0` and `θ(1) = 1`, the
  reparametrized path `γ ∘ θ` is sc-smoothly homotopic to `γ` with end points fixed, by the
  straight-line homotopy `(τ, s) ↦ γ((1 − τ) θ(s) + τ s)`; `reparam_mem` (if `θ([0, 1]) ⊆ [0, 1]`,
  the homotopy stays in every set containing `γ([0, 1])`).
* `leftHalf γ`, `rightHalf γ` (`s ↦ γ(s/2)`, `s ↦ γ((1 + s)/2)`), their sc-smoothness and end
  points, and `concatPath_halves`: the concatenation of the two halves is `γ ∘ θ` for
  `θ(s) = (κ(3s) + κ(3s − 2))/2`, `κ` the smooth transition function.

## Reading

Paths are on `ℝ` and only `[0, 1]` matters (decision D2).
-/

open Set Filter Topology Function
open scoped ContDiff

noncomputable section

namespace Polyfold

universe u

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}

/-- `q ↦ pt1 (σ q)` is `C^∞` for a `C^∞` `σ : ℝ² → ℝ`. -/
lemma contDiff_pt1_comp₂ {σ : (Fin 2 → ℝ) → ℝ} (hσ : ContDiff ℝ ∞ σ) :
    ContDiff ℝ ∞ fun q => pt1 (σ q) :=
  contDiff_pi.2 fun _ => hσ

/-- **The values of an sc-smooth map `ℝⁿ → X` are smooth points.** -/
theorem mem_smoothSet_of_isScSmoothMap {n : ℕ} {γ : (Fin n → ℝ) → X}
    (hγ : (rnPolyfold n).IsScSmoothMap PX γ) (p : Fin n → ℝ) : γ p ∈ PX.smoothSet :=
  mem_iInter.2 fun m => hγ.mapsTo_levelSet m (by rw [rnPolyfold_levelSet]; exact mem_univ p)

/-- `s ↦ pt2 (σ₁ s) (σ₂ s)` is `C^∞` for `C^∞` maps `σ₁, σ₂ : ℝᵏ → ℝ`. -/
theorem contDiff_pt2_comp {k : ℕ} {σ₁ σ₂ : (Fin k → ℝ) → ℝ} (h₁ : ContDiff ℝ ∞ σ₁)
    (h₂ : ContDiff ℝ ∞ σ₂) : ContDiff ℝ ∞ fun s => pt2 (σ₁ s) (σ₂ s) := by
  refine contDiff_pi.2 fun i => ?_
  fin_cases i
  · simpa only [Fin.zero_eta, Fin.isValue, pt2_apply_zero] using h₁
  · simpa only [Fin.mk_one, Fin.isValue, pt2_apply_one] using h₂

/-- **Reparametrization**: for a `C^∞` map `θ : ℝ → ℝ` with `θ(0) = 0` and `θ(1) = 1`, the path
`γ ∘ θ` is sc-smoothly homotopic to `γ` with end points fixed, by the straight-line homotopy
`(τ, s) ↦ γ((1 − τ) θ(s) + τ s)`. -/
theorem isScHomotopyRel_reparam {γ : (Fin 1 → ℝ) → X}
    (hγ : (rnPolyfold 1).IsScSmoothMap PX γ) {θ : ℝ → ℝ} (hθ : ContDiff ℝ ∞ θ) (h0 : θ 0 = 0)
    (h1 : θ 1 = 1) :
    IsScHomotopyRel PX (fun s => γ (pt1 (θ (s 0)))) γ
      (fun q => γ (pt1 ((1 - q 0) * θ (q 1) + q 0 * q 1))) where
  isScSmoothMap := by
    refine hγ.comp (isScSmoothMap_rn_rn_of_contDiff (contDiff_pt1_comp₂ ?_))
    have h0c : ContDiff ℝ ∞ fun q : Fin 2 → ℝ => q 0 := contDiff_apply ℝ ℝ 0
    have h1c : ContDiff ℝ ∞ fun q : Fin 2 → ℝ => q 1 := contDiff_apply ℝ ℝ 1
    exact ((contDiff_const.sub h0c).mul (hθ.comp h1c)).add (h0c.mul h1c)
  zero t _ := by simp
  one t _ := by simp
  start τ _ := by simp [h0]
  finish τ _ := by
    simp only [pt2_apply_zero, pt2_apply_one, h1, mul_one, pt1_apply]
    congr 2
    ring

omit [TopologicalSpace X] [T2Space X] [ParacompactSpace X] in
/-- The straight-line homotopy of `isScHomotopyRel_reparam` stays in every set containing
`γ([0, 1])` when `θ([0, 1]) ⊆ [0, 1]`. -/
theorem reparam_mem {γ : (Fin 1 → ℝ) → X} {U : Set X}
    (hγU : ∀ t ∈ Icc (0 : ℝ) 1, γ (pt1 t) ∈ U) {θ : ℝ → ℝ}
    (hθI : ∀ t ∈ Icc (0 : ℝ) 1, θ t ∈ Icc (0 : ℝ) 1) {τ s : ℝ} (hτ : τ ∈ Icc (0 : ℝ) 1)
    (hs : s ∈ Icc (0 : ℝ) 1) :
    γ (pt1 ((1 - pt2 τ s 0) * θ (pt2 τ s 1) + pt2 τ s 0 * pt2 τ s 1)) ∈ U := by
  simp only [pt2_apply_zero, pt2_apply_one]
  apply hγU
  have hθs := hθI s hs
  constructor
  · nlinarith [hτ.1, hτ.2, hs.1, hθs.1]
  · nlinarith [hτ.1, hτ.2, hs.2, hθs.2]

/-! ### The two halves of a path -/

/-- The first half `s ↦ γ(s/2)` of a path. -/
def leftHalf (γ : (Fin 1 → ℝ) → X) : (Fin 1 → ℝ) → X := fun s => γ (pt1 (s 0 / 2))

/-- The second half `s ↦ γ((1 + s)/2)` of a path. -/
def rightHalf (γ : (Fin 1 → ℝ) → X) : (Fin 1 → ℝ) → X := fun s => γ (pt1 ((1 + s 0) / 2))

variable {γ : (Fin 1 → ℝ) → X}

theorem isScSmoothMap_leftHalf (hγ : (rnPolyfold 1).IsScSmoothMap PX γ) :
    (rnPolyfold 1).IsScSmoothMap PX (leftHalf γ) :=
  isScSmoothMap_reparam hγ (contDiff_id.div_const 2)

theorem isScSmoothMap_rightHalf (hγ : (rnPolyfold 1).IsScSmoothMap PX γ) :
    (rnPolyfold 1).IsScSmoothMap PX (rightHalf γ) :=
  isScSmoothMap_reparam hγ ((contDiff_const.add contDiff_id).div_const 2)

omit [TopologicalSpace X] [T2Space X] [ParacompactSpace X] in
@[simp] theorem leftHalf_zero : leftHalf γ (pt1 0) = γ (pt1 0) := by simp [leftHalf]

omit [TopologicalSpace X] [T2Space X] [ParacompactSpace X] in
@[simp] theorem leftHalf_one : leftHalf γ (pt1 1) = γ (pt1 (1 / 2)) := by simp [leftHalf]

omit [TopologicalSpace X] [T2Space X] [ParacompactSpace X] in
@[simp] theorem rightHalf_zero : rightHalf γ (pt1 0) = γ (pt1 (1 / 2)) := by simp [rightHalf]

omit [TopologicalSpace X] [T2Space X] [ParacompactSpace X] in
@[simp] theorem rightHalf_one : rightHalf γ (pt1 1) = γ (pt1 1) := by
  simp only [rightHalf, pt1_apply]; norm_num

omit [TopologicalSpace X] [T2Space X] [ParacompactSpace X] in
theorem leftHalf_mem {U : Set X} (hγU : ∀ t ∈ Icc (0 : ℝ) 1, γ (pt1 t) ∈ U) :
    ∀ t ∈ Icc (0 : ℝ) 1, leftHalf γ (pt1 t) ∈ U := fun t ht =>
  hγU _ ⟨by simp only [pt1_apply]; linarith [ht.1], by simp only [pt1_apply]; linarith [ht.2]⟩

omit [TopologicalSpace X] [T2Space X] [ParacompactSpace X] in
theorem rightHalf_mem {U : Set X} (hγU : ∀ t ∈ Icc (0 : ℝ) 1, γ (pt1 t) ∈ U) :
    ∀ t ∈ Icc (0 : ℝ) 1, rightHalf γ (pt1 t) ∈ U := fun t ht =>
  hγU _ ⟨by simp only [pt1_apply]; linarith [ht.1], by simp only [pt1_apply]; linarith [ht.2]⟩

/-- The reparametrization `θ(s) = (κ(3s) + κ(3s − 2))/2` of `concatPath_halves`. -/
def halvesReparam (s : ℝ) : ℝ :=
  (Real.smoothTransition (3 * s) + Real.smoothTransition (3 * s - 2)) / 2

theorem contDiff_halvesReparam : ContDiff ℝ ∞ halvesReparam :=
  ((Real.smoothTransition.contDiff.comp (contDiff_const.mul contDiff_id)).add
    (Real.smoothTransition.contDiff.comp ((contDiff_const.mul contDiff_id).sub
      contDiff_const))).div_const 2

theorem halvesReparam_zero : halvesReparam 0 = 0 := by
  simp only [halvesReparam, mul_zero, zero_sub]
  rw [Real.smoothTransition.zero_of_nonpos le_rfl,
    Real.smoothTransition.zero_of_nonpos (by norm_num)]
  norm_num

theorem halvesReparam_one : halvesReparam 1 = 1 := by
  simp only [halvesReparam, mul_one]
  rw [Real.smoothTransition.one_of_one_le (by norm_num),
    Real.smoothTransition.one_of_one_le (by norm_num)]
  norm_num

theorem halvesReparam_mem {t : ℝ} (_ : t ∈ Icc (0 : ℝ) 1) : halvesReparam t ∈ Icc (0 : ℝ) 1 :=
  ⟨by unfold halvesReparam; linarith [Real.smoothTransition.nonneg (3 * t),
      Real.smoothTransition.nonneg (3 * t - 2)],
    by unfold halvesReparam; linarith [Real.smoothTransition.le_one (3 * t),
      Real.smoothTransition.le_one (3 * t - 2)]⟩

/-- **The concatenation of the two halves** of `γ` is the reparametrization `γ ∘ θ`,
`θ(s) = (κ(3s) + κ(3s − 2))/2`. -/
theorem concatPath_halves :
    concatPath (leftHalf γ) (rightHalf γ) = fun s => γ (pt1 (halvesReparam (s 0))) := by
  funext s
  rcases le_or_gt (s 0) (1 / 2) with hs | hs
  · rw [concatPath_of_le hs]
    simp only [leftHalf, pt1_apply, halvesReparam]
    rw [Real.smoothTransition.zero_of_nonpos (by linarith : 3 * s 0 - 2 ≤ 0), add_zero]
  · rw [concatPath_of_gt hs]
    simp only [rightHalf, pt1_apply, halvesReparam]
    rw [Real.smoothTransition.one_of_one_le (by linarith : 1 ≤ 3 * s 0)]

end Polyfold
