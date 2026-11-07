import Polyfold.Chapter6.ScHomotopy

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory I* (2014 preprint), Part I, §6.5, p. 228:
the category `PX` of sc-smooth homotopy classes of paths, before **Theorem 6.37**
*(book 2017: before Theorem 6.2; see `BookConcordance.md`)*.

# The path category `PX`

## The text, paraphrased

For an M-polyfold `X` and an sc-smooth `φ : [0, 1] → X`, `[φ]` is its sc-smooth homotopy class
with end points fixed; its source is `φ(0)` and its target `φ(1)`.  For `t([φ]) = s([ψ])` the
composition `[ψ] ∗ [φ]` is the class of `γ(s) = φ(β(s))` on `[0, 1/2]` and `γ(s) = ψ(β(s) − 1)`
on `[1/2, 1]`, for a smooth `β : [0, 1] → [0, 2]` with `β([0, 1/2]) = [0, 1]`, `β(0) = 0`,
`β(s) = 1` near `1/2`, `β([1/2, 1]) = [1, 2]` and `β(1) = 2`.  "This way we obtain a category
`PX` whose objects are the smooth points in `X` and whose morphisms `x → y` are the homotopy
classes `[φ]` with source `x` and target `y`" (p. 228).

## What is formalized

* `ScPath PX x y`: the sc-smooth paths from `x` to `y`; `ScPath.source_mem_smoothSet`,
  `ScPath.target_mem_smoothSet` (their end points are smooth points).
* `ScHomotopic PX γ₀ γ₁`: there is an sc-smooth homotopy with end points fixed
  (`IsScHomotopyRel`); it is an equivalence relation on sc-smooth paths: `ScHomotopic.refl`,
  `ScHomotopic.symm`, and `ScHomotopic.trans` (gluing in `τ` after reparametrizing all paths and
  homotopies by `κ` in `t`, so that the glued homotopies agree for all `t ∈ ℝ`, not only on
  `[0, 1]`).
* `ScPath.setoid`, `ScPathClass PX x y` (the classes `[φ]`), `ScPathClass.comp` (by
  `concatPath`, well defined by `ScPath.concat_congr`).
* The category laws: `ScPath.const_concat`, `ScPath.concat_const` (the constant path is a unit:
  the concatenation is a reparametrization of the other path), `ScPath.concat_assoc` (both
  sides are paths in three pieces, related by a straight-line homotopy of the inner
  reparametrizations, `isScHomotopyRel_triHomotopy`, after a polynomial reparametrization
  `assocReparam` of one side).
* `PathCat PX` (the smooth points of `X`) with `PathCat.category` (morphisms `x ⟶ y` the classes
  of paths from `x` to `y`, `𝟙 x` the class of the constant path, `[φ] ≫ [ψ] = [ψ] ∗ [φ]`);
  `PathCat.homMk φ = [φ]`, `PathCat.comp_mk`, `PathCat.id_eq_mk`, `PathCat.mk_eq_mk_iff`,
  `PathCat.exists_eq_mk`; and `PathCat.groupoid` (the class of the reversed path
  `s ↦ φ(1 − s)` is an inverse: `ScPath.concat_reverse`, `ScPath.reverse_concat`,
  `PathCat.inv_mk`).
* The tools: `isScSmoothMap_ite`, `isScSmoothMap_ite₃` (a map defined in two or three pieces
  along a continuous function, agreeing near the break points, is sc-smooth),
  `isScSmoothMap_const_of_mem_smoothSet`, `mem_smoothSet_of_isScSmoothMap`,
  `smoothTransition_half` (`κ(1/2) = 1/2`), and the concatenation formulas
  `concatPath_of_le_two_thirds`, `concatPath_of_one_third_le`.

## Reading

Paths are on `ℝ` and only `[0, 1]` matters (decision D2): a path is an sc-smooth map
`ℝ → X` and a homotopy an sc-smooth map `ℝ² → X` whose edge conditions are imposed on `[0, 1]`
(`IsScHomotopyRel`).  Since the edge conditions hold only for parameters in `[0, 1]`, two
homotopies need not agree off `[0, 1]` where they are glued; transitivity (`ScHomotopic.trans`)
is proved after reparametrizing in `t` by `κ`, and the classes `[φ]` are the equivalence
classes of "sc-smoothly homotopic with end points fixed".  The end points of an sc-smooth path
are smooth points, and the constant path at a smooth point is sc-smooth; the text does not name
the identities, and we take the classes of the constant paths.  The text writes
`ψ(β(s))` on `[1/2, 1]` with `β([1/2, 1]) = [1, 2]`; as we read it, this is `ψ(β(s) − 1)`.
`concatPath` is such a concatenation: `β(s) = κ(3s)` on `[0, 1/2]` and `β(s) = κ(3s − 2) + 1`
on `[1/2, 1]`, with `κ` the smooth transition function, so `β = 1` on `[1/3, 2/3]`.  In Mathlib's
convention `f ≫ g` is "first `f`, then `g`", so `[φ] ≫ [ψ]` is the text's `[ψ] ∗ [φ]`.
-/

open Set Filter Topology Function CategoryTheory
open scoped ContDiff

noncomputable section

namespace Polyfold

universe u

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}

local notation "κ" => Real.smoothTransition

/-! ### Tools -/

/-- `κ(1/2) = 1/2` for the smooth transition function `κ`. -/
theorem smoothTransition_half : κ (1 / 2) = 1 / 2 := by
  have h := expNegInvGlue.pos_of_pos (show (0 : ℝ) < 1 / 2 by norm_num)
  simp only [Real.smoothTransition, show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num]
  rw [div_eq_iff (add_pos h h).ne']
  ring

/-- **The constant map at a smooth point is sc-smooth.** -/
theorem isScSmoothMap_const_of_mem_smoothSet {m : ℕ} {x : X} (hx : x ∈ PX.smoothSet) :
    (rnPolyfold m).IsScSmoothMap PX fun _ => x := by
  obtain ⟨φ, hφ, hxφ⟩ := PX.exists_isChart_mem_source x
  have hsm : φ x ∈ φ.model.E.smooth := φ.model.E.mem_smooth_iff.2 fun k =>
    (PX.mem_levelSet_iff hφ hxφ).1 (mem_iInter.1 hx k)
  have h := isScSmoothMap_rn_chart_symm hφ
    (isScSmooth_const_of_mem_smooth (G := rnSc m) (isScDomain_univ (rnSc m)) hsm)
    fun _ => φ.mapsTo_model x hxφ
  simpa only [φ.symm_apply_apply hxφ] using h

/-- **A map in two pieces**: if `g₁`, `g₂` are sc-smooth and agree where `|σ − c| < ε`, then
the map equal to `g₁` on `{σ ≤ c}` and to `g₂` on `{σ > c}` is sc-smooth. -/
theorem isScSmoothMap_ite {m : ℕ} {σ : (Fin m → ℝ) → ℝ} (hσ : Continuous σ) {c ε : ℝ}
    (hε : 0 < ε) {g₁ g₂ : (Fin m → ℝ) → X} (hg₁ : (rnPolyfold m).IsScSmoothMap PX g₁)
    (hg₂ : (rnPolyfold m).IsScSmoothMap PX g₂) (h : ∀ q, |σ q - c| < ε → g₁ q = g₂ q) :
    (rnPolyfold m).IsScSmoothMap PX fun q => if σ q ≤ c then g₁ q else g₂ q := by
  refine MPolyfold.isScSmoothMap_of_eventuallyEq fun q => ?_
  rcases le_or_gt (σ q) c with hq | hq
  · refine ⟨g₁, hg₁, ?_⟩
    filter_upwards [(isOpen_lt hσ continuous_const).mem_nhds
      (show σ q < c + ε by linarith)] with p hp
    change σ p < c + ε at hp
    split_ifs with hpc
    · rfl
    · exact (h p (abs_sub_lt_iff.2 ⟨by linarith, by linarith [not_le.1 hpc]⟩)).symm
  · refine ⟨g₂, hg₂, ?_⟩
    filter_upwards [(isOpen_lt continuous_const hσ).mem_nhds hq] with p hp
    change c < σ p at hp
    rw [if_neg (not_le.2 hp)]

/-- **A map in three pieces** (`isScSmoothMap_ite` twice), for break points `c₁ + ε ≤ c₂`. -/
theorem isScSmoothMap_ite₃ {m : ℕ} {σ : (Fin m → ℝ) → ℝ} (hσ : Continuous σ) {c₁ c₂ ε : ℝ}
    (hε : 0 < ε) (hc : c₁ + ε ≤ c₂) {g₁ g₂ g₃ : (Fin m → ℝ) → X}
    (hg₁ : (rnPolyfold m).IsScSmoothMap PX g₁) (hg₂ : (rnPolyfold m).IsScSmoothMap PX g₂)
    (hg₃ : (rnPolyfold m).IsScSmoothMap PX g₃) (h₁₂ : ∀ q, |σ q - c₁| < ε → g₁ q = g₂ q)
    (h₂₃ : ∀ q, |σ q - c₂| < ε → g₂ q = g₃ q) :
    (rnPolyfold m).IsScSmoothMap PX fun q =>
      if σ q ≤ c₁ then g₁ q else if σ q ≤ c₂ then g₂ q else g₃ q :=
  isScSmoothMap_ite hσ hε hg₁ (isScSmoothMap_ite hσ hε hg₂ hg₃ h₂₃) fun q hq => by
    rw [if_pos (by linarith [(abs_sub_lt_iff.1 hq).1] : σ q ≤ c₂)]
    exact h₁₂ q hq

/-- `q ↦ Φ(σ₁(q), σ₂(q))` is sc-smooth for sc-smooth `Φ : ℝ² → X` and `C^∞` `σ₁, σ₂`. -/
theorem isScSmoothMap_comp_pt2 {Φ : (Fin 2 → ℝ) → X} (hΦ : (rnPolyfold 2).IsScSmoothMap PX Φ)
    {σ₁ σ₂ : (Fin 2 → ℝ) → ℝ} (h₁ : ContDiff ℝ ∞ σ₁) (h₂ : ContDiff ℝ ∞ σ₂) :
    (rnPolyfold 2).IsScSmoothMap PX fun q => Φ (pt2 (σ₁ q) (σ₂ q)) :=
  hΦ.comp (isScSmoothMap_rn_rn_of_contDiff (contDiff_pt2_comp h₁ h₂))

/-- `q ↦ γ(σ(q))` is sc-smooth for an sc-smooth path `γ` and a `C^∞` `σ : ℝ² → ℝ`. -/
theorem isScSmoothMap_comp_pt1₂ {γ : (Fin 1 → ℝ) → X} (hγ : (rnPolyfold 1).IsScSmoothMap PX γ)
    {σ : (Fin 2 → ℝ) → ℝ} (hσ : ContDiff ℝ ∞ σ) :
    (rnPolyfold 2).IsScSmoothMap PX fun q => γ (pt1 (σ q)) :=
  hγ.comp (isScSmoothMap_rn_rn_of_contDiff (contDiff_pt1_comp₂ hσ))

/-- The straight-line interpolation `q ↦ (1 − q₀) ρ(q₁) + q₀ ρ'(q₁)` is `C^∞`. -/
theorem contDiff_lerp {ρ ρ' : ℝ → ℝ} (hρ : ContDiff ℝ ∞ ρ) (hρ' : ContDiff ℝ ∞ ρ') :
    ContDiff ℝ ∞ fun q : Fin 2 → ℝ => (1 - q 0) * ρ (q 1) + q 0 * ρ' (q 1) := by
  have h0 : ContDiff ℝ ∞ fun q : Fin 2 → ℝ => q 0 := contDiff_apply ℝ ℝ 0
  have h1 : ContDiff ℝ ∞ fun q : Fin 2 → ℝ => q 1 := contDiff_apply ℝ ℝ 1
  exact ((contDiff_const.sub h0).mul (hρ.comp h1)).add (h0.mul (hρ'.comp h1))

/-! ### The concatenation, read off on larger intervals -/

section Concat

variable {γ₁ γ₂ : (Fin 1 → ℝ) → X}

/-- `concatPath γ₁ γ₂ (v) = γ₁(κ(3v))` for `v ≤ 2/3` (on `[1/2, 2/3]` both are `γ₁(1) = γ₂(0)`). -/
theorem concatPath_of_le_two_thirds (h : γ₁ (pt1 1) = γ₂ (pt1 0)) {v : ℝ} (hv : v ≤ 2 / 3) :
    concatPath γ₁ γ₂ (pt1 v) = γ₁ (pt1 (κ (3 * v))) := by
  rcases le_or_gt v (1 / 2) with h' | h'
  · rw [concatPath_of_le (s := pt1 v) h', pt1_apply]
  · rw [concatPath_of_gt (s := pt1 v) h', pt1_apply,
      Real.smoothTransition.zero_of_nonpos (by linarith : 3 * v - 2 ≤ 0),
      Real.smoothTransition.one_of_one_le (by linarith : 1 ≤ 3 * v), h]

/-- `concatPath γ₁ γ₂ (v) = γ₂(κ(3v − 2))` for `v ≥ 1/3` (on `[1/3, 1/2]` both are
`γ₁(1) = γ₂(0)`). -/
theorem concatPath_of_one_third_le (h : γ₁ (pt1 1) = γ₂ (pt1 0)) {v : ℝ} (hv : 1 / 3 ≤ v) :
    concatPath γ₁ γ₂ (pt1 v) = γ₂ (pt1 (κ (3 * v - 2))) := by
  rcases le_or_gt v (1 / 2) with h' | h'
  · rw [concatPath_of_le (s := pt1 v) h', pt1_apply,
      Real.smoothTransition.zero_of_nonpos (by linarith : 3 * v - 2 ≤ 0),
      Real.smoothTransition.one_of_one_le (by linarith : 1 ≤ 3 * v), h]
  · rw [concatPath_of_gt (s := pt1 v) h', pt1_apply]

end Concat

/-! ### Sc-smooth homotopy with end points fixed is an equivalence relation -/

variable (PX) in
/-- **Sc-smoothly homotopic with end points fixed**: there is an sc-smooth homotopy from `γ₀` to
`γ₁` with end points fixed (`IsScHomotopyRel`). -/
def ScHomotopic (γ₀ γ₁ : (Fin 1 → ℝ) → X) : Prop := ∃ Φ, IsScHomotopyRel PX γ₀ γ₁ Φ

section Homotopy

variable {γ γ₀ γ₁ γ₂ : (Fin 1 → ℝ) → X} {Φ Ψ : (Fin 2 → ℝ) → X}

/-- The constant homotopy `(τ, t) ↦ γ(t)`. -/
theorem isScHomotopyRel_refl (hγ : (rnPolyfold 1).IsScSmoothMap PX γ) :
    IsScHomotopyRel PX γ γ fun q => γ (pt1 (q 1)) where
  isScSmoothMap := isScSmoothMap_comp_pt1₂ hγ (contDiff_apply ℝ ℝ 1)
  zero _ _ := by simp only [pt2_apply_one]
  one _ _ := by simp only [pt2_apply_one]
  start _ _ := by simp only [pt2_apply_one]
  finish _ _ := by simp only [pt2_apply_one]

/-- The reversed homotopy `(τ, t) ↦ Φ(1 − τ, t)`. -/
theorem IsScHomotopyRel.symm (h : IsScHomotopyRel PX γ₀ γ₁ Φ) :
    IsScHomotopyRel PX γ₁ γ₀ fun q => Φ (pt2 (1 - q 0) (q 1)) where
  isScSmoothMap := isScSmoothMap_comp_pt2 h.isScSmoothMap
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

/-- A homotopy reparametrized by `κ` in `t`: `(τ, t) ↦ Φ(τ, κ(t))`, from `γ₀ ∘ κ` to
`γ₁ ∘ κ`. -/
theorem IsScHomotopyRel.comp_smoothTransition (h : IsScHomotopyRel PX γ₀ γ₁ Φ) :
    IsScHomotopyRel PX (fun s => γ₀ (pt1 (κ (s 0)))) (fun s => γ₁ (pt1 (κ (s 0))))
      fun q => Φ (pt2 (q 0) (κ (q 1))) where
  isScSmoothMap := isScSmoothMap_comp_pt2 h.isScSmoothMap (contDiff_apply ℝ ℝ 0)
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

/-- **Gluing two homotopies** in `τ`: `Φ(κ(3τ), t)` for `τ ≤ 1/2` and `Ψ(κ(3τ − 2), t)` for
`τ > 1/2`. -/
def glueHomotopy (Φ Ψ : (Fin 2 → ℝ) → X) : (Fin 2 → ℝ) → X := fun q =>
  if q 0 ≤ 1 / 2 then Φ (pt2 (κ (3 * q 0)) (q 1)) else Ψ (pt2 (κ (3 * q 0 - 2)) (q 1))

omit [TopologicalSpace X] [T2Space X] [ParacompactSpace X] in
/-- The glued homotopy at `τ = 1`. -/
theorem glueHomotopy_one (t : ℝ) : glueHomotopy Φ Ψ (pt2 1 t) = Ψ (pt2 1 t) := by
  simp only [glueHomotopy, pt2_apply_zero, pt2_apply_one]
  rw [if_neg (by norm_num), show (3 : ℝ) * 1 - 2 = 1 by norm_num, Real.smoothTransition.one]

/-- **The glued homotopy** is a homotopy with end points fixed when the two homotopies agree at
the junction for all `t ∈ ℝ`. -/
theorem IsScHomotopyRel.glue (hΦ : IsScHomotopyRel PX γ₀ γ₁ Φ)
    (hΨ : IsScHomotopyRel PX γ₁ γ₂ Ψ) (h : ∀ t, Φ (pt2 1 t) = Ψ (pt2 0 t)) :
    IsScHomotopyRel PX γ₀ γ₂ (glueHomotopy Φ Ψ) where
  isScSmoothMap := by
    have h0 : ContDiff ℝ ∞ fun q : Fin 2 → ℝ => q 0 := contDiff_apply ℝ ℝ 0
    have h1 : ContDiff ℝ ∞ fun q : Fin 2 → ℝ => q 1 := contDiff_apply ℝ ℝ 1
    refine isScSmoothMap_ite (σ := fun q => q 0) (continuous_apply 0)
      (show (0 : ℝ) < 1 / 6 by norm_num)
      (isScSmoothMap_comp_pt2 hΦ.isScSmoothMap
        (Real.smoothTransition.contDiff.comp (contDiff_const.mul h0)) h1)
      (isScSmoothMap_comp_pt2 hΨ.isScSmoothMap
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

/-- `ScHomotopic` is reflexive on sc-smooth paths. -/
theorem ScHomotopic.refl (hγ : (rnPolyfold 1).IsScSmoothMap PX γ) : ScHomotopic PX γ γ :=
  ⟨_, isScHomotopyRel_refl hγ⟩

/-- `ScHomotopic` is symmetric. -/
theorem ScHomotopic.symm (h : ScHomotopic PX γ₀ γ₁) : ScHomotopic PX γ₁ γ₀ :=
  let ⟨_, hΦ⟩ := h
  ⟨_, hΦ.symm⟩

/-- **`ScHomotopic` is transitive** on sc-smooth paths.  The edge conditions of a homotopy hold
only on `[0, 1]`, so two homotopies are not glued directly; reparametrized by `κ` in `t` they
agree at the junction for all `t ∈ ℝ`, and `γ₀ ≃ γ₀ ∘ κ ≃ γ₁ ∘ κ ≃ γ₂ ∘ κ ≃ γ₂` is glued from
four homotopies which agree at their junctions for all `t`. -/
theorem ScHomotopic.trans (h₁ : ScHomotopic PX γ₀ γ₁) (h₂ : ScHomotopic PX γ₁ γ₂)
    (hγ₀ : (rnPolyfold 1).IsScSmoothMap PX γ₀) (hγ₂ : (rnPolyfold 1).IsScSmoothMap PX γ₂) :
    ScHomotopic PX γ₀ γ₂ := by
  obtain ⟨Φ, hΦ⟩ := h₁
  obtain ⟨Ψ, hΨ⟩ := h₂
  have hκ : ContDiff ℝ ∞ κ := Real.smoothTransition.contDiff
  have H₀ := (isScHomotopyRel_reparam hγ₀ hκ Real.smoothTransition.zero
    Real.smoothTransition.one).symm
  have H₂ := isScHomotopyRel_reparam hγ₂ hκ Real.smoothTransition.zero
    Real.smoothTransition.one
  have hI : ∀ t, κ t ∈ Icc (0 : ℝ) 1 := fun t =>
    ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩
  refine ⟨_, ((H₀.glue hΦ.comp_smoothTransition fun t => ?_).glue
    hΨ.comp_smoothTransition fun t => ?_).glue H₂ fun t => ?_⟩
  · simp only [pt2_apply_zero, pt2_apply_one, sub_self, sub_zero, one_mul, zero_mul, add_zero]
    exact (hΦ.zero _ (hI t)).symm
  · rw [glueHomotopy_one]
    simp only [pt2_apply_zero, pt2_apply_one]
    rw [hΦ.one _ (hI t), hΨ.zero _ (hI t)]
  · rw [glueHomotopy_one]
    simp only [pt2_apply_zero, pt2_apply_one, sub_zero, one_mul, zero_mul, add_zero]
    exact hΨ.one _ (hI t)

end Homotopy

/-! ### Concatenation of homotopies: composition is well defined -/

section ConcatHomotopy

variable {γ₁ γ₁' γ₂ γ₂' : (Fin 1 → ℝ) → X} {Φ Ψ : (Fin 2 → ℝ) → X}

/-- **The concatenation of two homotopies**: `(τ, s) ↦ Φ(κ(τ), κ(3s))` for `s ≤ 1/2` and
`Ψ(κ(τ), κ(3s − 2))` for `s > 1/2`.  The clamp `κ(τ) ∈ [0, 1]` makes the two pieces agree near
`s = 1/2` for all `τ ∈ ℝ`. -/
def concatHomotopy (Φ Ψ : (Fin 2 → ℝ) → X) : (Fin 2 → ℝ) → X := fun q =>
  if q 1 ≤ 1 / 2 then Φ (pt2 (κ (q 0)) (κ (3 * q 1)))
  else Ψ (pt2 (κ (q 0)) (κ (3 * q 1 - 2)))

/-- **Composition respects homotopy**: homotopies `Φ : γ₁ ≃ γ₁'` and `Ψ : γ₂ ≃ γ₂'` with end
points fixed and `γ₁(1) = γ₂(0)` give the homotopy `concatHomotopy Φ Ψ` from `γ₁ γ₂` to
`γ₁' γ₂'`. -/
theorem isScHomotopyRel_concatHomotopy (hΦ : IsScHomotopyRel PX γ₁ γ₁' Φ)
    (hΨ : IsScHomotopyRel PX γ₂ γ₂' Ψ) (h : γ₁ (pt1 1) = γ₂ (pt1 0)) :
    IsScHomotopyRel PX (concatPath γ₁ γ₂) (concatPath γ₁' γ₂') (concatHomotopy Φ Ψ) where
  isScSmoothMap := by
    have h0 : ContDiff ℝ ∞ fun q : Fin 2 → ℝ => q 0 := contDiff_apply ℝ ℝ 0
    have h1 : ContDiff ℝ ∞ fun q : Fin 2 → ℝ => q 1 := contDiff_apply ℝ ℝ 1
    have hκ0 : ContDiff ℝ ∞ fun q : Fin 2 → ℝ => κ (q 0) := Real.smoothTransition.contDiff.comp h0
    refine isScSmoothMap_ite (σ := fun q => q 1) (continuous_apply 1)
      (show (0 : ℝ) < 1 / 6 by norm_num)
      (isScSmoothMap_comp_pt2 hΦ.isScSmoothMap hκ0
        (Real.smoothTransition.contDiff.comp (contDiff_const.mul h1)))
      (isScSmoothMap_comp_pt2 hΨ.isScSmoothMap hκ0
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

end ConcatHomotopy

/-! ### Paths in three pieces and associativity -/

section Assoc

variable {γ₁ γ₂ γ₃ : (Fin 1 → ℝ) → X}

/-- **A path in three pieces**: `γ₁(ρ₁(s))` for `s ≤ b₁`, `γ₂(ρ₂(s))` for `b₁ < s ≤ b₂` and
`γ₃(ρ₃(s))` for `s > b₂`. -/
def triPath (γ₁ γ₂ γ₃ : (Fin 1 → ℝ) → X) (b₁ b₂ : ℝ) (ρ₁ ρ₂ ρ₃ : ℝ → ℝ) :
    (Fin 1 → ℝ) → X := fun s =>
  if s 0 ≤ b₁ then γ₁ (pt1 (ρ₁ (s 0)))
  else if s 0 ≤ b₂ then γ₂ (pt1 (ρ₂ (s 0))) else γ₃ (pt1 (ρ₃ (s 0)))

/-- **The straight-line homotopy of the inner reparametrizations** of a path in three pieces:
`(τ, s) ↦` the path in three pieces with `ρᵢ` replaced by `(1 − τ) ρᵢ + τ ρᵢ'`. -/
def triHomotopy (γ₁ γ₂ γ₃ : (Fin 1 → ℝ) → X) (b₁ b₂ : ℝ) (ρ₁ ρ₂ ρ₃ ρ₁' ρ₂' ρ₃' : ℝ → ℝ) :
    (Fin 2 → ℝ) → X := fun q =>
  triPath γ₁ γ₂ γ₃ b₁ b₂ (fun s => (1 - q 0) * ρ₁ s + q 0 * ρ₁' s)
    (fun s => (1 - q 0) * ρ₂ s + q 0 * ρ₂' s) (fun s => (1 - q 0) * ρ₃ s + q 0 * ρ₃' s)
    (pt1 (q 1))

/-- **Changing the inner reparametrizations of a path in three pieces**: if near each break point
the inner reparametrizations `ρᵢ`, `ρᵢ'` of the two adjacent pieces are `1` (left piece) and `0`
(right piece), and `ρ₁(0) = ρ₁'(0) = 0`, `ρ₃(1) = ρ₃'(1) = 1`, then the straight-line homotopy is an
sc-smooth homotopy with end points fixed (sc-smooth since it is locally constant near the break
points, for all `τ ∈ ℝ`). -/
theorem isScHomotopyRel_triHomotopy (hγ₁ : (rnPolyfold 1).IsScSmoothMap PX γ₁)
    (hγ₂ : (rnPolyfold 1).IsScSmoothMap PX γ₂) (hγ₃ : (rnPolyfold 1).IsScSmoothMap PX γ₃)
    (h₁₂ : γ₁ (pt1 1) = γ₂ (pt1 0)) (h₂₃ : γ₂ (pt1 1) = γ₃ (pt1 0)) {b₁ b₂ ε : ℝ}
    (hε : 0 < ε) (hb : b₁ + ε ≤ b₂) (hb₁ : 0 ≤ b₁) (hb₂ : b₂ < 1)
    {ρ₁ ρ₂ ρ₃ ρ₁' ρ₂' ρ₃' : ℝ → ℝ} (hρ₁ : ContDiff ℝ ∞ ρ₁) (hρ₂ : ContDiff ℝ ∞ ρ₂)
    (hρ₃ : ContDiff ℝ ∞ ρ₃) (hρ₁' : ContDiff ℝ ∞ ρ₁') (hρ₂' : ContDiff ℝ ∞ ρ₂')
    (hρ₃' : ContDiff ℝ ∞ ρ₃')
    (hn₁ : ∀ s, |s - b₁| < ε → ρ₁ s = 1 ∧ ρ₁' s = 1 ∧ ρ₂ s = 0 ∧ ρ₂' s = 0)
    (hn₂ : ∀ s, |s - b₂| < ε → ρ₂ s = 1 ∧ ρ₂' s = 1 ∧ ρ₃ s = 0 ∧ ρ₃' s = 0)
    (h0 : ρ₁ 0 = 0) (h0' : ρ₁' 0 = 0) (h1 : ρ₃ 1 = 1) (h1' : ρ₃' 1 = 1) :
    IsScHomotopyRel PX (triPath γ₁ γ₂ γ₃ b₁ b₂ ρ₁ ρ₂ ρ₃) (triPath γ₁ γ₂ γ₃ b₁ b₂ ρ₁' ρ₂' ρ₃')
      (triHomotopy γ₁ γ₂ γ₃ b₁ b₂ ρ₁ ρ₂ ρ₃ ρ₁' ρ₂' ρ₃') where
  isScSmoothMap := by
    refine isScSmoothMap_ite₃ (σ := fun q => q 1) (continuous_apply 1) hε hb
      (isScSmoothMap_comp_pt1₂ hγ₁ (contDiff_lerp hρ₁ hρ₁'))
      (isScSmoothMap_comp_pt1₂ hγ₂ (contDiff_lerp hρ₂ hρ₂'))
      (isScSmoothMap_comp_pt1₂ hγ₃ (contDiff_lerp hρ₃ hρ₃')) (fun q hq => ?_) fun q hq => ?_
    · obtain ⟨e₁, e₁', e₂, e₂'⟩ := hn₁ _ hq
      change γ₁ (pt1 ((1 - q 0) * ρ₁ (q 1) + q 0 * ρ₁' (q 1))) =
        γ₂ (pt1 ((1 - q 0) * ρ₂ (q 1) + q 0 * ρ₂' (q 1)))
      rw [e₁, e₁', e₂, e₂', show (1 - q 0) * 1 + q 0 * 1 = 1 by ring,
        show (1 - q 0) * 0 + q 0 * 0 = 0 by ring, h₁₂]
    · obtain ⟨e₂, e₂', e₃, e₃'⟩ := hn₂ _ hq
      change γ₂ (pt1 ((1 - q 0) * ρ₂ (q 1) + q 0 * ρ₂' (q 1))) =
        γ₃ (pt1 ((1 - q 0) * ρ₃ (q 1) + q 0 * ρ₃' (q 1)))
      rw [e₂, e₂', e₃, e₃', show (1 - q 0) * 1 + q 0 * 1 = 1 by ring,
        show (1 - q 0) * 0 + q 0 * 0 = 0 by ring, h₂₃]
  zero t _ := by
    simp only [triHomotopy, pt2_apply_zero, pt2_apply_one, sub_zero, one_mul, zero_mul,
      add_zero]
  one t _ := by
    simp only [triHomotopy, pt2_apply_zero, pt2_apply_one, sub_self, one_mul, zero_mul,
      zero_add]
  start τ _ := by
    simp only [triHomotopy, triPath, pt2_apply_zero, pt2_apply_one, pt1_apply, hb₁, ↓reduceIte,
      h0, h0', mul_zero, add_zero]
  finish τ _ := by
    simp only [triHomotopy, triPath, pt2_apply_zero, pt2_apply_one, pt1_apply]
    have h₁ : ¬ (1 : ℝ) ≤ b₁ := by linarith
    have h₂ : ¬ (1 : ℝ) ≤ b₂ := by linarith
    simp only [h₁, h₂, ↓reduceIte, h1, h1', mul_one, sub_add_cancel]

/-- The reparametrization `θ(s) = (59 s − 92 s² + 48 s³)/15` of associativity: monotone, with
`θ(0) = 0`, `θ(1/6) = 1/2`, `θ(1/2) = 5/6`, `θ(1) = 1`, so it moves the break points `1/6`, `1/2`
of `(γ₁ γ₂) γ₃` onto the break points `1/2`, `5/6` of `γ₁ (γ₂ γ₃)`. -/
def assocReparam (s : ℝ) : ℝ := (59 * s - 92 * s ^ 2 + 48 * s ^ 3) / 15

/-- `assocReparam` is `C^∞` (a polynomial). -/
theorem contDiff_assocReparam : ContDiff ℝ ∞ assocReparam := by
  unfold assocReparam
  fun_prop

/-- `assocReparam` is monotone: `θ'(s) = (59 − 184 s + 144 s²)/15 > 0`. -/
theorem monotone_assocReparam : Monotone assocReparam := by
  intro s t hst
  have key : 0 < 59 - 92 * (t + s) + 48 * (t ^ 2 + t * s + s ^ 2) := by
    nlinarith [sq_nonneg (t + s - 23 / 18), sq_nonneg (t - s)]
  have e : assocReparam t - assocReparam s =
      (t - s) * (59 - 92 * (t + s) + 48 * (t ^ 2 + t * s + s ^ 2)) / 15 := by
    unfold assocReparam
    ring
  nlinarith [mul_nonneg (sub_nonneg.2 hst) key.le]

/-- `θ(0) = 0`. -/
theorem assocReparam_zero : assocReparam 0 = 0 := by norm_num [assocReparam]

/-- `θ(1) = 1`. -/
theorem assocReparam_one : assocReparam 1 = 1 := by norm_num [assocReparam]

/-- `θ(1/6) = 1/2`. -/
theorem assocReparam_sixth : assocReparam (1 / 6) = 1 / 2 := by norm_num [assocReparam]

/-- `θ(1/2) = 5/6`. -/
theorem assocReparam_half : assocReparam (1 / 2) = 5 / 6 := by norm_num [assocReparam]

/-- **`(γ₁ γ₂) γ₃` as a path in three pieces**, with break points `1/6`, `1/2`. -/
theorem concatPath_concatPath_eq_triPath (h₁₂ : γ₁ (pt1 1) = γ₂ (pt1 0)) :
    concatPath (concatPath γ₁ γ₂) γ₃ = triPath γ₁ γ₂ γ₃ (1 / 6) (1 / 2)
      (fun s => κ (3 * κ (3 * s))) (fun s => κ (3 * κ (3 * s) - 2)) (fun s => κ (3 * s - 2)) := by
  funext s
  simp only [triPath]
  rcases le_or_gt (s 0) (1 / 6) with hs | hs
  · have hκ : κ (3 * s 0) ≤ 1 / 2 := (Real.smoothTransition.monotone (by linarith)).trans_eq
      smoothTransition_half
    rw [if_pos hs, concatPath_of_le (by linarith), concatPath_of_le_two_thirds h₁₂ (by linarith)]
  rcases le_or_gt (s 0) (1 / 2) with hs' | hs'
  · have hκ : 1 / 2 ≤ κ (3 * s 0) := smoothTransition_half.symm.trans_le
      (Real.smoothTransition.monotone (by linarith))
    rw [if_neg (not_le.2 hs), if_pos hs', concatPath_of_le hs',
      concatPath_of_one_third_le h₁₂ (by linarith)]
  · rw [if_neg (not_le.2 hs), if_neg (not_le.2 hs'), concatPath_of_gt hs']

/-- **`γ₁ (γ₂ γ₃)` reparametrized by `θ = assocReparam` as a path in three pieces**, with break
points `1/6`, `1/2`. -/
theorem concatPath_concatPath_reparam_eq_triPath (h₁₂ : γ₁ (pt1 1) = γ₂ (pt1 0))
    (h₂₃ : γ₂ (pt1 1) = γ₃ (pt1 0)) :
    (fun s => concatPath γ₁ (concatPath γ₂ γ₃) (pt1 (assocReparam (s 0)))) =
      triPath γ₁ γ₂ γ₃ (1 / 6) (1 / 2) (fun s => κ (3 * assocReparam s))
        (fun s => κ (3 * κ (3 * assocReparam s - 2)))
        (fun s => κ (3 * κ (3 * assocReparam s - 2) - 2)) := by
  funext s
  simp only [triPath]
  have h₁ : γ₁ (pt1 1) = concatPath γ₂ γ₃ (pt1 0) := h₁₂.trans concatPath_zero.symm
  rcases le_or_gt (s 0) (1 / 6) with hs | hs
  · have hθ : assocReparam (s 0) ≤ 1 / 2 :=
      (monotone_assocReparam hs).trans_eq assocReparam_sixth
    rw [if_pos hs, concatPath_of_le (s := pt1 (assocReparam (s 0))) hθ, pt1_apply]
  have hθ₁ : 1 / 2 ≤ assocReparam (s 0) :=
    assocReparam_sixth.symm.trans_le (monotone_assocReparam hs.le)
  rcases le_or_gt (s 0) (1 / 2) with hs' | hs'
  · have hθ₂ : assocReparam (s 0) ≤ 5 / 6 :=
      (monotone_assocReparam hs').trans_eq assocReparam_half
    have hκ : κ (3 * assocReparam (s 0) - 2) ≤ 1 / 2 :=
      (Real.smoothTransition.monotone (by linarith)).trans_eq smoothTransition_half
    rw [if_neg (not_le.2 hs), if_pos hs', concatPath_of_one_third_le h₁ (by linarith),
      concatPath_of_le_two_thirds h₂₃ (by linarith)]
  · have hθ₂ : 5 / 6 ≤ assocReparam (s 0) :=
      assocReparam_half.symm.trans_le (monotone_assocReparam hs'.le)
    have hκ : 1 / 2 ≤ κ (3 * assocReparam (s 0) - 2) := smoothTransition_half.symm.trans_le
      (Real.smoothTransition.monotone (by linarith))
    rw [if_neg (not_le.2 hs), if_neg (not_le.2 hs'), concatPath_of_one_third_le h₁ (by linarith),
      concatPath_of_one_third_le h₂₃ (by linarith)]

omit [TopologicalSpace X] [T2Space X] [ParacompactSpace X] in
/-- Near a point where a continuous `f : ℝ → ℝ` is `1/2`, it takes values in `[1/3, 2/3]`. -/
theorem exists_forall_abs_sub_lt_mem_Icc {f : ℝ → ℝ} (hf : Continuous f) {s₀ : ℝ}
    (h : f s₀ = 1 / 2) : ∃ ε > 0, ∀ s, |s - s₀| < ε → 1 / 3 ≤ f s ∧ f s ≤ 2 / 3 := by
  obtain ⟨ε, hε, hfε⟩ := Metric.continuous_iff.1 hf s₀ (1 / 6) (by norm_num)
  refine ⟨ε, hε, fun s hs => ?_⟩
  have := hfε s (by rwa [Real.dist_eq])
  rw [Real.dist_eq, h, abs_sub_lt_iff] at this
  constructor <;> linarith [this.1, this.2]

/-- **Associativity, for paths**: `(γ₁ γ₂) γ₃` and `γ₁ (γ₂ γ₃)` are sc-smoothly homotopic with end
points fixed.  Both are paths in three pieces with break points `1/6`, `1/2` (the second after
the reparametrization `assocReparam`), related by `isScHomotopyRel_triHomotopy`. -/
theorem scHomotopic_concatPath_assoc (hγ₁ : (rnPolyfold 1).IsScSmoothMap PX γ₁)
    (hγ₂ : (rnPolyfold 1).IsScSmoothMap PX γ₂) (hγ₃ : (rnPolyfold 1).IsScSmoothMap PX γ₃)
    (h₁₂ : γ₁ (pt1 1) = γ₂ (pt1 0)) (h₂₃ : γ₂ (pt1 1) = γ₃ (pt1 0)) :
    ScHomotopic PX (concatPath (concatPath γ₁ γ₂) γ₃) (concatPath γ₁ (concatPath γ₂ γ₃)) := by
  have hκ : ContDiff ℝ ∞ κ := Real.smoothTransition.contDiff
  have hc : ∀ a : ℝ, ContDiff ℝ ∞ fun s : ℝ => 3 * s - a := fun a =>
    (contDiff_const.mul contDiff_id).sub contDiff_const
  have hc' : ContDiff ℝ ∞ fun s : ℝ => 3 * s := contDiff_const.mul contDiff_id
  have hθ := contDiff_assocReparam
  have hθc := hθ.continuous
  have hR₁₂ : (rnPolyfold 1).IsScSmoothMap PX (concatPath γ₁ γ₂) :=
    isScSmoothMap_concatPath hγ₁ hγ₂ h₁₂
  have hR₂₃ : (rnPolyfold 1).IsScSmoothMap PX (concatPath γ₂ γ₃) :=
    isScSmoothMap_concatPath hγ₂ hγ₃ h₂₃
  have hL : (rnPolyfold 1).IsScSmoothMap PX (concatPath (concatPath γ₁ γ₂) γ₃) :=
    isScSmoothMap_concatPath hR₁₂ hγ₃ (concatPath_one.trans h₂₃)
  have hR : (rnPolyfold 1).IsScSmoothMap PX (concatPath γ₁ (concatPath γ₂ γ₃)) :=
    isScSmoothMap_concatPath hγ₁ hR₂₃ (h₁₂.trans concatPath_zero.symm)
  -- the neighbourhoods of the break points
  obtain ⟨ε₁, hε₁, hn₁⟩ := exists_forall_abs_sub_lt_mem_Icc (s₀ := 1 / 6)
    (Real.smoothTransition.continuous.comp hc'.continuous)
    (by simp only [comp_apply]; norm_num [smoothTransition_half])
  obtain ⟨ε₂, hε₂, hn₂⟩ := exists_forall_abs_sub_lt_mem_Icc hθc assocReparam_sixth
  obtain ⟨ε₃, hε₃, hn₃⟩ := exists_forall_abs_sub_lt_mem_Icc (s₀ := 1 / 2)
    (Real.smoothTransition.continuous.comp ((hc 2).continuous.comp hθc))
    (by simp only [comp_apply, assocReparam_half]; norm_num [smoothTransition_half])
  set ε := min (min ε₁ ε₂) (min ε₃ (1 / 6)) with hεdef
  have hε : 0 < ε := lt_min (lt_min hε₁ hε₂) (lt_min hε₃ (by norm_num))
  have hεₗ : ε ≤ 1 / 6 := (min_le_right _ _).trans (min_le_right _ _)
  have H₁ : ScHomotopic PX (concatPath (concatPath γ₁ γ₂) γ₃)
      (fun s => concatPath γ₁ (concatPath γ₂ γ₃) (pt1 (assocReparam (s 0)))) := by
    rw [concatPath_concatPath_eq_triPath h₁₂,
      concatPath_concatPath_reparam_eq_triPath h₁₂ h₂₃]
    refine ⟨_, isScHomotopyRel_triHomotopy hγ₁ hγ₂ hγ₃ h₁₂ h₂₃ hε (by linarith) (by norm_num)
      (by norm_num) (hκ.comp (hc'.comp (hκ.comp hc'))) (hκ.comp ((hc 2).comp (hκ.comp hc')))
      (hκ.comp (hc 2)) (hκ.comp (hc'.comp hθ)) (hκ.comp (hc'.comp (hκ.comp ((hc 2).comp hθ))))
      (hκ.comp ((hc 2).comp (hκ.comp ((hc 2).comp hθ)))) (fun s hs => ?_) (fun s hs => ?_)
      ?_ ?_ ?_ ?_⟩
    · have hs₁ := hn₁ s (lt_of_lt_of_le hs ((min_le_left _ _).trans (min_le_left _ _)))
      have hs₂ := hn₂ s (lt_of_lt_of_le hs ((min_le_left _ _).trans (min_le_right _ _)))
      simp only [comp_apply] at hs₁ hs₂ ⊢
      refine ⟨Real.smoothTransition.one_of_one_le (by linarith),
        Real.smoothTransition.one_of_one_le (by linarith),
        Real.smoothTransition.zero_of_nonpos (by linarith), ?_⟩
      rw [Real.smoothTransition.zero_of_nonpos (by linarith : 3 * assocReparam s - 2 ≤ 0),
        mul_zero, Real.smoothTransition.zero]
    · have hs₃ := hn₃ s (lt_of_lt_of_le hs ((min_le_right _ _).trans (min_le_left _ _)))
      have hs₄ : |s - 1 / 2| < 1 / 6 := lt_of_lt_of_le hs hεₗ
      obtain ⟨hs₄₁, hs₄₂⟩ := abs_sub_lt_iff.1 hs₄
      simp only [comp_apply] at hs₃ ⊢
      refine ⟨?_, Real.smoothTransition.one_of_one_le (by linarith),
        Real.smoothTransition.zero_of_nonpos (by linarith),
        Real.smoothTransition.zero_of_nonpos (by linarith)⟩
      rw [Real.smoothTransition.one_of_one_le (by linarith : 1 ≤ 3 * s),
        show (3 : ℝ) * 1 - 2 = 1 by norm_num, Real.smoothTransition.one]
    · simp only [mul_zero, Real.smoothTransition.zero]
    · simp only [assocReparam_zero, mul_zero, Real.smoothTransition.zero]
    · norm_num [Real.smoothTransition.one]
    · norm_num [assocReparam_one, Real.smoothTransition.one]
  exact H₁.trans ⟨_, isScHomotopyRel_reparam hR contDiff_assocReparam assocReparam_zero
    assocReparam_one⟩ hL hR

end Assoc

/-! ### Reversed paths -/

section Reverse

variable {γ γ₀ γ₁ : (Fin 1 → ℝ) → X} {Φ : (Fin 2 → ℝ) → X}

/-- A homotopy reversed in `t`: `(τ, t) ↦ Φ(τ, 1 − t)`, from the reversed `γ₀` to the reversed
`γ₁`. -/
theorem IsScHomotopyRel.reverse (h : IsScHomotopyRel PX γ₀ γ₁ Φ) :
    IsScHomotopyRel PX (fun s => γ₀ (pt1 (1 - s 0))) (fun s => γ₁ (pt1 (1 - s 0)))
      fun q => Φ (pt2 (q 0) (1 - q 1)) where
  isScSmoothMap := isScSmoothMap_comp_pt2 h.isScSmoothMap (contDiff_apply ℝ ℝ 0)
    (contDiff_const.sub (contDiff_apply ℝ ℝ 1))
  zero t ht := by
    simp only [pt2_apply_zero, pt2_apply_one, pt1_apply]
    exact h.zero _ ⟨by linarith [ht.2], by linarith [ht.1]⟩
  one t ht := by
    simp only [pt2_apply_zero, pt2_apply_one, pt1_apply]
    exact h.one _ ⟨by linarith [ht.2], by linarith [ht.1]⟩
  start τ hτ := by
    simp only [pt2_apply_zero, pt2_apply_one, pt1_apply, sub_zero]
    exact h.finish τ hτ
  finish τ hτ := by
    simp only [pt2_apply_zero, pt2_apply_one, pt1_apply, sub_self]
    exact h.start τ hτ

/-- The homotopy `(τ, s) ↦ γ((1 − τ) κ(3s))` for `s ≤ 1/2` and `γ((1 − τ)(1 − κ(3s − 2)))` for
`s > 1/2`, contracting `γ` followed by its reverse to the constant path at `γ(0)`. -/
def reverseHomotopy (γ : (Fin 1 → ℝ) → X) : (Fin 2 → ℝ) → X := fun q =>
  if q 1 ≤ 1 / 2 then γ (pt1 ((1 - q 0) * κ (3 * q 1)))
  else γ (pt1 ((1 - q 0) * (1 - κ (3 * q 1 - 2))))

/-- **A path followed by its reverse** is sc-smoothly homotopic, with end points fixed, to the
constant path at its starting point. -/
theorem isScHomotopyRel_concatPath_reverse (hγ : (rnPolyfold 1).IsScSmoothMap PX γ) {x : X}
    (hx : γ (pt1 0) = x) :
    IsScHomotopyRel PX (concatPath γ fun s => γ (pt1 (1 - s 0))) (fun _ => x)
      (reverseHomotopy γ) where
  isScSmoothMap := by
    have h0 : ContDiff ℝ ∞ fun q : Fin 2 → ℝ => q 0 := contDiff_apply ℝ ℝ 0
    have h1 : ContDiff ℝ ∞ fun q : Fin 2 → ℝ => q 1 := contDiff_apply ℝ ℝ 1
    refine isScSmoothMap_ite (σ := fun q => q 1) (continuous_apply 1)
      (show (0 : ℝ) < 1 / 6 by norm_num)
      (isScSmoothMap_comp_pt1₂ hγ ((contDiff_const.sub h0).mul
        (Real.smoothTransition.contDiff.comp (contDiff_const.mul h1))))
      (isScSmoothMap_comp_pt1₂ hγ ((contDiff_const.sub h0).mul (contDiff_const.sub
        (Real.smoothTransition.contDiff.comp ((contDiff_const.mul h1).sub contDiff_const)))))
      fun q hq => ?_
    obtain ⟨hq₁, hq₂⟩ := abs_sub_lt_iff.1 hq
    change γ (pt1 ((1 - q 0) * κ (3 * q 1))) = γ (pt1 ((1 - q 0) * (1 - κ (3 * q 1 - 2))))
    rw [Real.smoothTransition.one_of_one_le (by linarith),
      Real.smoothTransition.zero_of_nonpos (by linarith), sub_zero]
  zero t _ := by
    simp only [reverseHomotopy, pt2_apply_zero, pt2_apply_one, sub_zero, one_mul]
    rcases le_or_gt t (1 / 2) with ht | ht
    · rw [if_pos ht, concatPath_of_le (s := pt1 t) ht, pt1_apply]
    · rw [if_neg (not_le.2 ht), concatPath_of_gt (s := pt1 t) ht]
      simp only [pt1_apply]
  one t _ := by
    simp only [reverseHomotopy, pt2_apply_zero, pt2_apply_one, sub_self, zero_mul, ite_self]
    exact hx
  start τ _ := by
    simp only [reverseHomotopy, pt2_apply_zero, pt2_apply_one, mul_zero,
      Real.smoothTransition.zero]
    rw [if_pos (by norm_num), concatPath_zero]
  finish τ _ := by
    simp only [reverseHomotopy, pt2_apply_zero, pt2_apply_one]
    rw [if_neg (by norm_num), show (3 : ℝ) * 1 - 2 = 1 by norm_num, Real.smoothTransition.one,
      concatPath_one, pt1_apply, sub_self, mul_zero]

end Reverse

/-! ### Sc-smooth paths from `x` to `y` and their classes -/

variable (PX) in
/-- **An sc-smooth path from `x` to `y`**: an sc-smooth `φ : ℝ → X` (only `[0, 1]` matters)
with `φ(0) = x` and `φ(1) = y`. -/
@[ext]
structure ScPath (x y : X) where
  /-- The path. -/
  toFun : (Fin 1 → ℝ) → X
  /-- It is sc-smooth. -/
  isScSmoothMap : (rnPolyfold 1).IsScSmoothMap PX toFun
  /-- It starts at `x`. -/
  source : toFun (pt1 0) = x
  /-- It ends at `y`. -/
  target : toFun (pt1 1) = y

namespace ScPath

variable {w x y z : X}

/-- The starting point of an sc-smooth path is a smooth point. -/
theorem source_mem_smoothSet (a : ScPath PX x y) : x ∈ PX.smoothSet :=
  a.source ▸ mem_smoothSet_of_isScSmoothMap a.isScSmoothMap _

/-- The end point of an sc-smooth path is a smooth point. -/
theorem target_mem_smoothSet (a : ScPath PX x y) : y ∈ PX.smoothSet :=
  a.target ▸ mem_smoothSet_of_isScSmoothMap a.isScSmoothMap _

variable (PX) in
/-- **Sc-smooth homotopy with end points fixed**, as a setoid on the paths from `x` to `y`. -/
instance setoid (x y : X) : Setoid (ScPath PX x y) where
  r a b := ScHomotopic PX a.toFun b.toFun
  iseqv :=
    { refl := fun a => ScHomotopic.refl a.isScSmoothMap
      symm := fun h => h.symm
      trans := fun {a _ c} h₁ h₂ => h₁.trans h₂ a.isScSmoothMap c.isScSmoothMap }

/-- Two paths are equivalent iff they are sc-smoothly homotopic with end points fixed. -/
theorem equiv_iff {a b : ScPath PX x y} : a ≈ b ↔ ScHomotopic PX a.toFun b.toFun := Iff.rfl

variable (x) in
/-- **The constant path** at a smooth point `x`. -/
@[simps]
def const (hx : x ∈ PX.smoothSet) : ScPath PX x x where
  toFun _ := x
  isScSmoothMap := isScSmoothMap_const_of_mem_smoothSet hx
  source := rfl
  target := rfl

/-- **The concatenation** of a path from `x` to `y` and a path from `y` to `z` (`concatPath`). -/
@[simps]
def concat (a : ScPath PX x y) (b : ScPath PX y z) : ScPath PX x z where
  toFun := concatPath a.toFun b.toFun
  isScSmoothMap := isScSmoothMap_concatPath a.isScSmoothMap b.isScSmoothMap
    (a.target.trans b.source.symm)
  source := concatPath_zero.trans a.source
  target := concatPath_one.trans b.target

/-- **The reversed path** `s ↦ φ(1 − s)`. -/
@[simps]
def reverse (a : ScPath PX x y) : ScPath PX y x where
  toFun s := a.toFun (pt1 (1 - s 0))
  isScSmoothMap := isScSmoothMap_reparam a.isScSmoothMap (contDiff_const.sub contDiff_id)
  source := by simpa only [pt1_apply, sub_zero] using a.target
  target := by simpa only [pt1_apply, sub_self] using a.source

/-- **Composition is well defined on classes**: homotopic paths have homotopic
concatenations. -/
theorem concat_congr ⦃a a' : ScPath PX x y⦄ (ha : a ≈ a') ⦃b b' : ScPath PX y z⦄
    (hb : b ≈ b') : a.concat b ≈ a'.concat b' := by
  obtain ⟨Φ, hΦ⟩ := ha
  obtain ⟨Ψ, hΨ⟩ := hb
  exact ⟨_, isScHomotopyRel_concatHomotopy hΦ hΨ (a.target.trans b.source.symm)⟩

/-- **The constant path is a left unit**: `x` followed by `φ` is `φ(κ(3s − 2))`, a
reparametrization of `φ`. -/
theorem const_concat (hx : x ∈ PX.smoothSet) (a : ScPath PX x y) : (const x hx).concat a ≈ a := by
  have e : concatPath (fun _ => x) a.toFun = fun s => a.toFun (pt1 (κ (3 * s 0 - 2))) := by
    funext s
    rcases le_or_gt (s 0) (1 / 2) with hs | hs
    · rw [concatPath_of_le hs, Real.smoothTransition.zero_of_nonpos (by linarith), a.source]
    · exact concatPath_of_gt hs
  change ScHomotopic PX (concatPath (fun _ => x) a.toFun) a.toFun
  rw [e]
  exact ⟨_, isScHomotopyRel_reparam a.isScSmoothMap
    (Real.smoothTransition.contDiff.comp ((contDiff_const.mul contDiff_id).sub contDiff_const))
    (Real.smoothTransition.zero_of_nonpos (by norm_num))
    (Real.smoothTransition.one_of_one_le (by norm_num))⟩

/-- **The constant path is a right unit**: `φ` followed by `y` is `φ(κ(3s))`, a
reparametrization of `φ`. -/
theorem concat_const (hy : y ∈ PX.smoothSet) (a : ScPath PX x y) : a.concat (const y hy) ≈ a := by
  have e : concatPath a.toFun (fun _ => y) = fun s => a.toFun (pt1 (κ (3 * s 0))) := by
    funext s
    rcases le_or_gt (s 0) (1 / 2) with hs | hs
    · exact concatPath_of_le hs
    · rw [concatPath_of_gt hs, Real.smoothTransition.one_of_one_le (by linarith), a.target]
  change ScHomotopic PX (concatPath a.toFun fun _ => y) a.toFun
  rw [e]
  exact ⟨_, isScHomotopyRel_reparam a.isScSmoothMap
    (Real.smoothTransition.contDiff.comp (contDiff_const.mul contDiff_id))
    (Real.smoothTransition.zero_of_nonpos (by norm_num))
    (Real.smoothTransition.one_of_one_le (by norm_num))⟩

/-- **Associativity of the composition** (`scHomotopic_concatPath_assoc`). -/
theorem concat_assoc (a : ScPath PX w x) (b : ScPath PX x y) (c : ScPath PX y z) :
    (a.concat b).concat c ≈ a.concat (b.concat c) :=
  scHomotopic_concatPath_assoc a.isScSmoothMap b.isScSmoothMap c.isScSmoothMap
    (a.target.trans b.source.symm) (b.target.trans c.source.symm)

/-- Reversal is well defined on classes. -/
theorem reverse_congr ⦃a a' : ScPath PX x y⦄ (h : a ≈ a') : a.reverse ≈ a'.reverse := by
  obtain ⟨Φ, hΦ⟩ := h
  exact ⟨_, hΦ.reverse⟩

/-- Reversing twice gives the path back. -/
@[simp] theorem reverse_reverse (a : ScPath PX x y) : a.reverse.reverse = a := by
  ext s
  simp only [reverse_toFun, pt1_apply, sub_sub_cancel, pt1_apply_zero]

/-- **A path followed by its reverse** is homotopic to the constant path. -/
theorem concat_reverse (hx : x ∈ PX.smoothSet) (a : ScPath PX x y) :
    a.concat a.reverse ≈ const x hx :=
  ⟨_, isScHomotopyRel_concatPath_reverse a.isScSmoothMap a.source⟩

/-- **The reverse of a path followed by the path** is homotopic to the constant path. -/
theorem reverse_concat (hy : y ∈ PX.smoothSet) (a : ScPath PX x y) :
    a.reverse.concat a ≈ const y hy := by
  have h := concat_reverse hy a.reverse
  rwa [reverse_reverse] at h

end ScPath

variable (PX) in
/-- **The sc-smooth homotopy classes `[φ]`** of paths from `x` to `y`, end points fixed. -/
def ScPathClass (x y : X) : Type u := Quotient (ScPath.setoid PX x y)

namespace ScPathClass

variable {w x y z : X}

/-- **The composition** of classes, `[φ], [ψ] ↦ [φ ψ]` (the text's `[ψ] ∗ [φ]`). -/
def comp : ScPathClass PX x y → ScPathClass PX y z → ScPathClass PX x z :=
  Quotient.map₂ ScPath.concat ScPath.concat_congr

/-- The reversal of classes, `[φ] ↦ [φ(1 − ·)]`. -/
def reverse : ScPathClass PX x y → ScPathClass PX y x :=
  Quotient.map ScPath.reverse ScPath.reverse_congr

/-- `[φ] [ψ] = [φ ψ]`. -/
theorem comp_mk (a : ScPath PX x y) (b : ScPath PX y z) :
    comp (⟦a⟧ : ScPathClass PX x y) ⟦b⟧ = ⟦a.concat b⟧ := rfl

/-- The reversal of `[φ]` is `[φ(1 − ·)]`. -/
theorem reverse_mk (a : ScPath PX x y) : reverse (⟦a⟧ : ScPathClass PX x y) = ⟦a.reverse⟧ :=
  rfl

end ScPathClass

/-! ### The path category -/

variable (PX) in
/-- **The objects of the path category `PX`**: the smooth points of `X`. -/
structure PathCat where
  /-- The point. -/
  pt : X
  /-- It is a smooth point. -/
  smooth : pt ∈ PX.smoothSet

namespace PathCat

/-- **The path category `PX`** (p. 228): objects the smooth points of `X`, morphisms `x ⟶ y` the
sc-smooth homotopy classes `[φ]` of paths from `x` to `y` with end points fixed, `𝟙 x` the class
of the constant path, and `[φ] ≫ [ψ] = [φ ψ]` the class of the concatenation (the text's
`[ψ] ∗ [φ]`). -/
instance category : Category (PathCat PX) where
  Hom x y := ScPathClass PX x.pt y.pt
  id x := ⟦ScPath.const x.pt x.smooth⟧
  comp f g := ScPathClass.comp f g
  id_comp {x _} f := Quotient.inductionOn f fun a => Quotient.sound (ScPath.const_concat x.smooth a)
  comp_id {_ y} f := Quotient.inductionOn f fun a => Quotient.sound (ScPath.concat_const y.smooth a)
  assoc f g h := Quotient.inductionOn₃ f g h fun a b c => Quotient.sound (ScPath.concat_assoc a b c)

variable {x y z : PathCat PX}

/-- **The morphism `[φ] : x ⟶ y`** of a path `φ` from `x` to `y` (its class `⟦φ⟧`). -/
def homMk (a : ScPath PX x.pt y.pt) : x ⟶ y := (⟦a⟧ : ScPathClass PX x.pt y.pt)

/-- **Composition of classes of paths**: `[φ] ≫ [ψ] = [φ ψ]` (the text's `[ψ] ∗ [φ]`). -/
@[simp] theorem comp_mk (a : ScPath PX x.pt y.pt) (b : ScPath PX y.pt z.pt) :
    homMk a ≫ homMk b = homMk (a.concat b) := rfl

/-- **The identity** is the class of the constant path. -/
theorem id_eq_mk (x : PathCat PX) : 𝟙 x = homMk (ScPath.const x.pt x.smooth) := rfl

/-- Two paths give the same morphism iff they are sc-smoothly homotopic with end points fixed. -/
theorem mk_eq_mk_iff {a b : ScPath PX x.pt y.pt} :
    homMk a = homMk b ↔ ScHomotopic PX a.toFun b.toFun :=
  Quotient.eq

/-- Every morphism `x ⟶ y` is the class of a path from `x` to `y`. -/
theorem exists_eq_mk (f : x ⟶ y) : ∃ a : ScPath PX x.pt y.pt, f = homMk a :=
  let ⟨a, ha⟩ := Quotient.exists_rep (s := ScPath.setoid PX x.pt y.pt) f
  ⟨a, ha.symm⟩

/-- **The path category is a groupoid**: the class of the reversed path `s ↦ φ(1 − s)` is an
inverse of `[φ]`. -/
instance groupoid : Groupoid (PathCat PX) where
  toCategory := category
  inv f := ScPathClass.reverse f
  inv_comp {_ y} f :=
    Quotient.inductionOn f fun a => Quotient.sound (ScPath.reverse_concat y.smooth a)
  comp_inv {x _} f :=
    Quotient.inductionOn f fun a => Quotient.sound (ScPath.concat_reverse x.smooth a)

/-- **The inverse** of `[φ]` is the class of the reversed path. -/
theorem inv_mk (a : ScPath PX x.pt y.pt) : Groupoid.inv (homMk a) = homMk a.reverse := rfl

end PathCat

end Polyfold
