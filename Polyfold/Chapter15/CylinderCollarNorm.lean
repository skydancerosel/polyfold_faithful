import Polyfold.Chapter15.CylinderGlue

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), **Corollary 15.3.10 (2)**
(p. 699): an auxiliary norm `Ñ` of `W̃ → [0, 1] × X` restricting to `Nⁱ` over `{i} × X` and a
saturated `Ũ` restricting to `Uⁱ`, such that `(Ñ, Ũ)` controls compactness, with `Ñ = Nⁱ` on a
collar of `{i} × X`.

# A controlling pair on the cylinder that is a product near the ends

## Reading

The statement (2) asks for one pair `(Ñ, Ũ)` restricting to `(N⁰, U⁰)` and `(N¹, U¹)` over the
ends.  `SEP.interpAuxNorm` (`α = min(1, 3(1 − t))`, `β = min(1, 3t)`) gives `N¹` a positive weight
for every `t > 0`.  Here the weights are `a(t) = min(1, max(0, 5 − 6t))` and
`b(t) = min(1, max(0, 6t − 1))`: `a = 1` on `[0, 2/3]`, `b = 1` on `[1/3, 1]`, and in addition
`b = 0` on `[0, 1/6]`, `a = 0` on `[5/6, 1]`, so `Ñ(t, x, h) = N⁰(h)` for `t ≤ 1/6` and
`Ñ(t, x, h) = N¹(h)` for `t ≥ 5/6`.  This is what an extension of the end data by a cut-off in
`t` needs (file `CylinderExtensionBump`).

## What is formalized (namespace `Polyfold.SEP`)

* `collarWeight₀`, `collarWeight₁` and their properties.
* `collarAuxNorm A N₀ N₁ = max(a(t)·N⁰, b(t)·N¹)`; **`isAuxNorm_collarAuxNorm`**
  (Definition 8.3.5); `collarAuxNorm_of_cubeTime_le`, `collarAuxNorm_of_cubeTime_ge` (the collars)
  and `collarAuxNorm_of_cubeTime_eq_zero/one` (the ends).
* **`controlsCompactness_collar`**: `(Ñ, Ũ)` with `Ũ = interpSet A U⁰ U¹` controls the compactness
  of `f̃` (Corollary 15.3.10 (2)).
-/

set_option maxSynthPendingDepth 3
set_option linter.unusedSectionVars false

open Set Function Topology Filter

noncomputable section

namespace Polyfold

universe u

namespace SEP

/-! ### The collar weights -/

/-- `a(s) = min(1, max(0, 5 − 6s))`: `1` on `[0, 2/3]`, `0` on `[5/6, 1]`. -/
def collarWeight₀ (s : ℝ) : ℝ := min 1 (max 0 (5 - 6 * s))

/-- `b(s) = min(1, max(0, 6s − 1))`: `0` on `[0, 1/6]`, `1` on `[1/3, 1]`. -/
def collarWeight₁ (s : ℝ) : ℝ := min 1 (max 0 (6 * s - 1))

theorem continuous_collarWeight₀ : Continuous collarWeight₀ :=
  continuous_const.min (continuous_const.max (continuous_const.sub
    (continuous_const.mul continuous_id)))

theorem continuous_collarWeight₁ : Continuous collarWeight₁ :=
  continuous_const.min (continuous_const.max ((continuous_const.mul continuous_id).sub
    continuous_const))

theorem collarWeight₀_nonneg (s : ℝ) : 0 ≤ collarWeight₀ s :=
  le_min zero_le_one (le_max_left _ _)

theorem collarWeight₁_nonneg (s : ℝ) : 0 ≤ collarWeight₁ s :=
  le_min zero_le_one (le_max_left _ _)

theorem collarWeight₀_eq_one {s : ℝ} (hs : s ≤ 2 / 3) : collarWeight₀ s = 1 :=
  min_eq_left (le_max_of_le_right (by linarith))

theorem collarWeight₁_eq_one {s : ℝ} (hs : 1 / 3 ≤ s) : collarWeight₁ s = 1 :=
  min_eq_left (le_max_of_le_right (by linarith))

theorem collarWeight₀_eq_zero {s : ℝ} (hs : 5 / 6 ≤ s) : collarWeight₀ s = 0 := by
  unfold collarWeight₀
  rw [max_eq_left (by linarith)]
  exact min_eq_right zero_le_one

theorem collarWeight₁_eq_zero {s : ℝ} (hs : s ≤ 1 / 6) : collarWeight₁ s = 0 := by
  unfold collarWeight₁
  rw [max_eq_left (by linarith)]
  exact min_eq_right zero_le_one

theorem collarWeight_pos (s : ℝ) : 0 < collarWeight₀ s ∨ 0 < collarWeight₁ s := by
  by_cases h : s ≤ 2 / 3
  · exact Or.inl (by rw [collarWeight₀_eq_one h]; exact one_pos)
  · exact Or.inr (by rw [collarWeight₁_eq_one (by linarith)]; exact one_pos)

/-! ### The collar norm -/

variable {A : SEP.{u}}

variable (A) in
/-- **The collar norm** `Ñ(t, x, h) = max(a(t)·N⁰(h), b(t)·N¹(h))`. -/
def collarAuxNorm (N₀ N₁ : A.B.One → ℝ) (w : (A.cubeSEP 1).B.One) : ℝ :=
  max (collarWeight₀ (cubeTime w) * cubeAuxNorm 1 N₀ w)
    (collarWeight₁ (cubeTime w) * cubeAuxNorm 1 N₁ w)

/-- **`Ñ` is an auxiliary norm of `(W̃, μ̃)`** (Definition 8.3.5) if `N⁰` and `N¹` are auxiliary
norms of `(W, μ)`. -/
theorem isAuxNorm_collarAuxNorm {N₀ N₁ : A.B.One → ℝ} (h₀ : A.E.IsAuxNorm N₀)
    (h₁ : A.E.IsAuxNorm N₁) : (A.cubeSEP 1).E.IsAuxNorm (collarAuxNorm A N₀ N₁) := by
  have p₀ := isAuxNorm_cubeAuxNorm' (n := 1) h₀.isAuxNorm
  have p₁ := isAuxNorm_cubeAuxNorm' (n := 1) h₁.isAuxNorm
  refine ⟨⟨?_, fun z => ?_, fun w z hw hNw => ?_⟩, fun h k φ hk hh => ?_⟩
  · exact (((continuous_collarWeight₀.comp continuous_cubeTime).mul p₀.continuous).max
      ((continuous_collarWeight₁.comp continuous_cubeTime).mul p₁.continuous))
  · refine ((StrongBundle.isAuxNorm_max_mul p₀ p₁ (collarWeight₀_nonneg _)
      (collarWeight₁_nonneg _) (collarWeight_pos ((z.1 0 : unitInterval) : ℝ))).fiber z).congr
      fun v => ?_
    simp only [collarAuxNorm, cubeTime_toOne]
  · have hc : Continuous fun p : (Fin 1 → unitInterval) × A.Obj => (p.1 0 : ℝ) :=
      continuous_subtype_val.comp ((continuous_apply 0).comp continuous_fst)
    set t₀ : ℝ := ((show (Fin 1 → unitInterval) × A.Obj from z).1 0 : ℝ)
    have ht : Tendsto (fun k => cubeTime (w k)) atTop (𝓝 t₀) := (hc.tendsto z).comp hw
    rcases collarWeight_pos t₀ with hpos | hpos
    · have hev : ∀ᶠ k in atTop, collarWeight₀ t₀ / 2 < collarWeight₀ (cubeTime (w k)) :=
        ((continuous_collarWeight₀.tendsto _).comp ht).eventually (lt_mem_nhds (by linarith))
      refine p₀.tendsto_zeroOne w z hw (squeeze_zero' (Eventually.of_forall fun k => p₀.nonneg _)
        (hev.mono fun k hk => ?_) (by simpa using hNw.const_mul (2 / collarWeight₀ t₀)))
      have h2 : collarWeight₀ t₀ / 2 * cubeAuxNorm 1 N₀ (w k) ≤ collarAuxNorm A N₀ N₁ (w k) :=
        (mul_le_mul_of_nonneg_right hk.le (p₀.nonneg _)).trans (le_max_left _ _)
      calc cubeAuxNorm 1 N₀ (w k)
          = 2 / collarWeight₀ t₀ * (collarWeight₀ t₀ / 2 * cubeAuxNorm 1 N₀ (w k)) := by
            field_simp
        _ ≤ 2 / collarWeight₀ t₀ * collarAuxNorm A N₀ N₁ (w k) :=
            mul_le_mul_of_nonneg_left h2 (by positivity)
    · have hev : ∀ᶠ k in atTop, collarWeight₁ t₀ / 2 < collarWeight₁ (cubeTime (w k)) :=
        ((continuous_collarWeight₁.tendsto _).comp ht).eventually (lt_mem_nhds (by linarith))
      refine p₁.tendsto_zeroOne w z hw (squeeze_zero' (Eventually.of_forall fun k => p₁.nonneg _)
        (hev.mono fun k hk => ?_) (by simpa using hNw.const_mul (2 / collarWeight₁ t₀)))
      have h2 : collarWeight₁ t₀ / 2 * cubeAuxNorm 1 N₁ (w k) ≤ collarAuxNorm A N₀ N₁ (w k) :=
        (mul_le_mul_of_nonneg_right hk.le (p₁.nonneg _)).trans (le_max_right _ _)
      calc cubeAuxNorm 1 N₁ (w k)
          = 2 / collarWeight₁ t₀ * (collarWeight₁ t₀ / 2 * cubeAuxNorm 1 N₁ (w k)) := by
            field_simp
        _ ≤ 2 / collarWeight₁ t₀ * collarAuxNorm A N₀ N₁ (w k) :=
            mul_le_mul_of_nonneg_left h2 (by positivity)
  · obtain ⟨-, -, hc⟩ := cubeVal_μ hk hh
    have e₀ := (isAuxNorm_cubeAuxNorm (n := 1) h₀).map_μ h k φ hk hh
    have e₁ := (isAuxNorm_cubeAuxNorm (n := 1) h₁).map_μ h k φ hk hh
    have et : cubeTime h = cubeTime k := by
      unfold cubeTime; rw [hc]
    simp only [collarAuxNorm, e₀, e₁, et]

/-- **On the collar `t ≤ 1/6`, `Ñ = N⁰`.** -/
theorem collarAuxNorm_of_cubeTime_le {N₀ N₁ : A.B.One → ℝ} (h₀ : A.B.IsAuxNorm N₀)
    {w : (A.cubeSEP 1).B.One} (hw : cubeTime w ≤ 1 / 6) :
    collarAuxNorm A N₀ N₁ w = cubeAuxNorm 1 N₀ w := by
  rw [collarAuxNorm, collarWeight₀_eq_one (by linarith), collarWeight₁_eq_zero hw, one_mul,
    zero_mul]
  exact max_eq_left ((isAuxNorm_cubeAuxNorm' h₀).nonneg w)

/-- **On the collar `t ≥ 5/6`, `Ñ = N¹`.** -/
theorem collarAuxNorm_of_cubeTime_ge {N₀ N₁ : A.B.One → ℝ} (h₁ : A.B.IsAuxNorm N₁)
    {w : (A.cubeSEP 1).B.One} (hw : 5 / 6 ≤ cubeTime w) :
    collarAuxNorm A N₀ N₁ w = cubeAuxNorm 1 N₁ w := by
  rw [collarAuxNorm, collarWeight₀_eq_zero hw, collarWeight₁_eq_one (by linarith), one_mul,
    zero_mul]
  exact max_eq_right ((isAuxNorm_cubeAuxNorm' h₁).nonneg w)

/-- **Over `t = 0`, `Ñ` restricts to `N⁰`.** -/
theorem collarAuxNorm_of_cubeTime_eq_zero {N₀ N₁ : A.B.One → ℝ} (h₀ : A.B.IsAuxNorm N₀)
    {w : (A.cubeSEP 1).B.One} (hw : cubeTime w = 0) :
    collarAuxNorm A N₀ N₁ w = cubeAuxNorm 1 N₀ w :=
  collarAuxNorm_of_cubeTime_le h₀ (by rw [hw]; norm_num)

/-- **Over `t = 1`, `Ñ` restricts to `N¹`.** -/
theorem collarAuxNorm_of_cubeTime_eq_one {N₀ N₁ : A.B.One → ℝ} (h₁ : A.B.IsAuxNorm N₁)
    {w : (A.cubeSEP 1).B.One} (hw : cubeTime w = 1) :
    collarAuxNorm A N₀ N₁ w = cubeAuxNorm 1 N₁ w :=
  collarAuxNorm_of_cubeTime_ge h₁ (by rw [hw]; norm_num)

open SBLocalization in
/-- **Corollary 15.3.10 (2), p. 699, with the collar norm**: if `(N⁰, U⁰)` and `(N¹, U¹)` control
the compactness of `f`, then `(Ñ, Ũ)` (`Ñ = collarAuxNorm A N⁰ N¹`, `Ũ = interpSet A U⁰ U¹`)
controls the compactness of `f̃(t, x) = (t, f(x))`, and it restricts to `(Nⁱ, Uⁱ)` over `t = i`
(`collarAuxNorm_of_cubeTime_eq_zero/one`, `mem_interpSet_zero/one`). -/
theorem controlsCompactness_collar {f : A.Obj → A.W} (hf : IsSection A.P f)
    {N₀ N₁ : A.B.One → ℝ} {U₀ U₁ : Set A.Obj} (h₀ : ControlsCompactness A f N₀ U₀)
    (h₁ : ControlsCompactness A f N₁ U₁) :
    ControlsCompactness (A.cubeSEP 1) (cubeLiftEp (n := 1) f hf) (collarAuxNorm A N₀ N₁)
      (interpSet A U₀ U₁) := by
  have := MPolyfold.paracompactSpace_prod (cubePolyfold 1) A.X.PObj
  have := MPolyfold.paracompactSpace_prod (cubePolyfold 1) A.X.PMor
  have hcc := corollary_15_3_10_2 hf h₀ h₁
  obtain ⟨hN₀, -, -, -, hC₀⟩ := h₀
  obtain ⟨hN₁, -, -, -, hC₁⟩ := h₁
  refine ⟨isAuxNorm_collarAuxNorm hN₀ hN₁, hcc.2.1, hcc.2.2.1, hcc.2.2.2.1, ?_⟩
  set S₀ := {x ∈ U₀ | A.B.AuxLe N₀ (f x) 1}
  set S₁ := {x ∈ U₁ | A.B.AuxLe N₁ (f x) 1}
  have hsub : {z ∈ interpSet A U₀ U₁ | (A.cubeSEP 1).B.AuxLe (collarAuxNorm A N₀ N₁)
      (cubeLiftEp (n := 1) f hf z) 1} ⊆ univ ×ˢ S₀ ∪ univ ×ˢ S₁ := by
    rintro ⟨q, x⟩ ⟨hz, hy, hle⟩
    have hy' := hy
    have hmem : f x ∈ A.B.oneSet := by
      have := A.B.paracompactSpace_pullback ((cubePolyfold 1).prod A.X.PObj)
        (A.X.cubeProj 1).obj
      exact (StrongBundle.pullback_mem_oneSet_iff (A.X.cubeProj 1).isScSmoothMap_obj _).1 hy'
    have ht : cubeTime ((A.cubeSEP 1).B.oneMk (cubeLiftEp (n := 1) f hf (q, x)) hy) =
        (q 0 : ℝ) := rfl
    rcases hz with ⟨hq0, hx⟩ | ⟨hq1, hx⟩
    · refine Or.inl ⟨mem_univ _, hx, hmem, ?_⟩
      refine le_trans ?_ ((le_max_left _ _).trans hle)
      rw [ht, collarWeight₀_eq_one (by change (q 0 : ℝ) < 2 / 3 at hq0; linarith), one_mul]
      exact (cubeAuxNorm_eq _ _ rfl).ge
    · refine Or.inr ⟨mem_univ _, hx, hmem, ?_⟩
      refine le_trans ?_ ((le_max_right _ _).trans hle)
      rw [ht, collarWeight₁_eq_one (by change 1 / 3 < (q 0 : ℝ) at hq1; linarith), one_mul]
      exact (cubeAuxNorm_eq _ _ rfl).ge
  have hK := (isCompact_closure_image_π_cube (n := 1) hC₀).union
    (isCompact_closure_image_π_cube (n := 1) hC₁)
  rw [← closure_union] at hK
  refine hK.of_isClosed_subset isClosed_closure (closure_mono ?_)
  rintro o ⟨z, hz, rfl⟩
  rcases hsub hz with h | h
  · exact Or.inl ⟨z, h, rfl⟩
  · exact Or.inr ⟨z, h, rfl⟩

end SEP

end Polyfold
