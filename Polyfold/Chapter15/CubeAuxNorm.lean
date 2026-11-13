import Polyfold.Chapter15.CubeEp
import Polyfold.Chapter15.ControllingPairs
import Polyfold.Chapter5.CylinderPerturbation2021

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Corollary 15.3.10 (2)
(p. 699) and the first step of its proof (pp. 699–700): **auxiliary norms and controlling pairs on
`W̃ → [0, 1] × X`**.

# Controlling compactness over `[0, 1] × X`

## Reading

`W̃ → X̃ = [0, 1] × X` is the pull-back `SEP.cubeSEP A 1` of `W` along the projection
(`CubeEp`), `f̃(t, x) = ((t, x), f(x))` is `SEP.cubeLiftEp`, and controlling compactness is
Definition 15.3.1 (`SBLocalization.ControlsCompactness`, `ControllingPairs`).

* The proof of Corollary 15.3.10 pulls an auxiliary norm `N` back to `W̃` (`Ñ(t, x, h) = N(h)`)
  and takes `Ũ = [0, 1] × U`: `controlsCompactness_cube` (any `n`; Part I's
  `StrongBundle.IsAuxNorm.pullback`).
* The statement (2) asks for one pair `(Ñ, Ũ)` restricting to `(N⁰, U⁰)` over `t = 0` and to
  `(N¹, U¹)` over `t = 1`.  We take
  `Ñ(t, x, h) = max(α(t)·N⁰(h), β(t)·N¹(h))` with `α = min(1, 3(1 − t))`, `β = min(1, 3t)`, and
  `Ũ = ([0, 2/3) × U⁰) ∪ ((1/3, 1] × U¹)`: `corollary_15_3_10_2`, with the restrictions
  `interpAuxNorm_of_cubeTime_eq_zero/one` and `mem_interpSet_zero/one`.

## What is formalized

* `StrongBundle.isAuxNorm_max_mul`: `max(a·N₀, b·N₁)` is an auxiliary norm for `a, b ≥ 0` not
  both `0`.
* `SEP.cubeAuxNorm`, `isAuxNorm_cubeAuxNorm` (Definition 8.3.5 on `W̃`, including invariance under
  `μ̃`), `auxLe_cubeAuxNorm_iff`.
* `SEP.controlsCompactness_cube`, `SEP.corollary_15_3_10_2`.
-/

set_option maxSynthPendingDepth 3
set_option linter.unusedSectionVars false

open Set Function Topology Filter

noncomputable section

namespace Polyfold

universe u v

/-! ### `max(a·N₀, b·N₁)` -/

section MaxMul

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle PX P}

namespace StrongBundle

/-- **`max(a·N₀, b·N₁)` is an auxiliary norm** (Definition 5.1.1, p. 205) for `a, b ≥ 0` not
both `0` (Part I's `IsAuxNorm.const_mul` and `IsAuxNorm.max`). -/
theorem isAuxNorm_max_mul {N₀ N₁ : B.One → ℝ} (h₀ : B.IsAuxNorm N₀) (h₁ : B.IsAuxNorm N₁)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : 0 < a ∨ 0 < b) :
    B.IsAuxNorm fun w => max (a * N₀ w) (b * N₁ w) := by
  rcases ha.lt_or_eq with ha' | rfl
  · rcases hb.lt_or_eq with hb' | rfl
    · exact (h₀.const_mul ha').max (h₁.const_mul hb')
    · have : (fun w => max (a * N₀ w) (0 * N₁ w)) = fun w => a * N₀ w :=
        funext fun w => by rw [zero_mul]; exact max_eq_left (mul_nonneg ha (h₀.nonneg w))
      rw [this]
      exact h₀.const_mul ha'
  · have hb' : 0 < b := hab.resolve_left (lt_irrefl 0)
    have : (fun w => max (0 * N₀ w) (b * N₁ w)) = fun w => b * N₁ w :=
      funext fun w => by rw [zero_mul]; exact max_eq_right (mul_nonneg hb (h₁.nonneg w))
    rw [this]
    exact h₁.const_mul hb'

/-- Completeness of the fibre norm over `x` only depends on the values on that fibre. -/
theorem IsCompleteFiberNorm.congr {N N' : B.One → ℝ} {x : X} (h : B.IsCompleteFiberNorm N x)
    (hN : ∀ v : B.oneFiber x, N' (B.toOne v) = N (B.toOne v)) : B.IsCompleteFiberNorm N' x where
  eq_zero v hv := h.eq_zero v (by rw [← hN]; exact hv)
  smul t v := by rw [hN, hN]; exact h.smul t v
  add_le v w := by rw [hN, hN, hN]; exact h.add_le v w
  complete u hu := by
    obtain ⟨v, hv⟩ := h.complete u fun ε hε => by
      obtain ⟨m, hm⟩ := hu ε hε
      exact ⟨m, fun i hi k hk => by rw [← hN]; exact hm i hi k hk⟩
    exact ⟨v, hv.congr fun k => (hN _).symm⟩

end StrongBundle

end MaxMul

/-! ### Interpolation weights -/

namespace SEP

/-- `α(s) = min(1, 3(1 − s))`: `1` on `[0, 2/3]`, `0` at `s = 1`. -/
def cubeWeight₀ (s : ℝ) : ℝ := min 1 (3 * (1 - s))

/-- `β(s) = min(1, 3s)`: `0` at `s = 0`, `1` on `[1/3, 1]`. -/
def cubeWeight₁ (s : ℝ) : ℝ := min 1 (3 * s)

theorem continuous_cubeWeight₀ : Continuous cubeWeight₀ :=
  continuous_const.min (continuous_const.mul (continuous_const.sub continuous_id))

theorem continuous_cubeWeight₁ : Continuous cubeWeight₁ :=
  continuous_const.min (continuous_const.mul continuous_id)

theorem cubeWeight₀_nonneg {s : ℝ} (hs : s ≤ 1) : 0 ≤ cubeWeight₀ s :=
  le_min zero_le_one (by linarith)

theorem cubeWeight₁_nonneg {s : ℝ} (hs : 0 ≤ s) : 0 ≤ cubeWeight₁ s :=
  le_min zero_le_one (by linarith)

theorem cubeWeight₀_eq_one {s : ℝ} (hs : s ≤ 2 / 3) : cubeWeight₀ s = 1 :=
  min_eq_left (by linarith)

theorem cubeWeight₁_eq_one {s : ℝ} (hs : 1 / 3 ≤ s) : cubeWeight₁ s = 1 :=
  min_eq_left (by linarith)

theorem cubeWeight₀_one : cubeWeight₀ 1 = 0 := by norm_num [cubeWeight₀]

theorem cubeWeight₁_zero : cubeWeight₁ 0 = 0 := by norm_num [cubeWeight₁]

theorem cubeWeight_pos (s : ℝ) : 0 < cubeWeight₀ s ∨ 0 < cubeWeight₁ s := by
  by_cases h : s ≤ 2 / 3
  · exact Or.inl (by rw [cubeWeight₀_eq_one h]; exact one_pos)
  · exact Or.inr (by rw [cubeWeight₁_eq_one (by linarith)]; exact one_pos)

/-! ### The pulled-back auxiliary norm on `W̃` -/

variable {A : SEP.{u}} {n : ℕ}

variable (n) in
/-- **`Ñ(q, x, h) = N(h)`** on `W̃_{0,1}` (the proof of Corollary 15.3.10, p. 699: "`N` defines an
auxiliary norm on `W̃`"); Part I's `StrongBundle.pullbackAuxNorm`. -/
def cubeAuxNorm (N : A.B.One → ℝ) : (A.cubeSEP n).B.One → ℝ :=
  have := MPolyfold.paracompactSpace_prod (cubePolyfold n) A.X.PObj
  have := A.B.paracompactSpace_pullback ((cubePolyfold n).prod A.X.PObj) (A.X.cubeProj n).obj
  A.B.pullbackAuxNorm (A.X.cubeProj n).isScSmoothMap_obj N

/-- `Ñ(w) = N(k)` when `k` is the `W`-component of `w`. -/
theorem cubeAuxNorm_eq {N : A.B.One → ℝ} (w : (A.cubeSEP n).B.One) (k : A.B.One)
    (hk : A.B.oneVal k = (cubeVal ((A.cubeSEP n).B.oneVal w)).2) : cubeAuxNorm n N w = N k :=
  congrArg N (A.B.oneVal_injective hk.symm)

/-- `AuxLe` for `Ñ` at `f̃(q, x)` is `AuxLe` for `N` at `f(x)`. -/
theorem auxLe_cubeAuxNorm_iff {N : A.B.One → ℝ} {f : A.Obj → A.W} (hf : IsSection A.P f)
    (z : (A.cubeSEP n).Obj) {r : ℝ} :
    (A.cubeSEP n).B.AuxLe (cubeAuxNorm n N) (cubeLiftEp (n := n) f hf z) r ↔
      A.B.AuxLe N (f z.2) r := by
  have := MPolyfold.paracompactSpace_prod (cubePolyfold n) A.X.PObj
  have := A.B.paracompactSpace_pullback ((cubePolyfold n).prod A.X.PObj) (A.X.cubeProj n).obj
  exact StrongBundle.auxLe_pullbackAuxNorm_iff (A.X.cubeProj n).isScSmoothMap_obj

/-- `Ñ` is an auxiliary norm of the strong bundle `W̃ → [0, 1]ⁿ × X`. -/
theorem isAuxNorm_cubeAuxNorm' {N : A.B.One → ℝ} (hN : A.B.IsAuxNorm N) :
    (A.cubeSEP n).B.IsAuxNorm (cubeAuxNorm n N) := by
  have := MPolyfold.paracompactSpace_prod (cubePolyfold n) A.X.PObj
  have := A.B.paracompactSpace_pullback ((cubePolyfold n).prod A.X.PObj) (A.X.cubeProj n).obj
  exact hN.pullback (A.X.cubeProj n).isScSmoothMap_obj

/-- The `[0, 1]ⁿ`-component of `P̃(w)`. -/
def cubeCoord (w : (A.cubeSEP n).B.One) : Fin n → unitInterval :=
  (cubeVal ((A.cubeSEP n).B.oneVal w)).1.1

theorem continuous_cubeCoord : Continuous (cubeCoord (A := A) (n := n)) :=
  continuous_fst.comp (continuous_fst.comp (continuous_subtype_val.comp
    (A.cubeSEP n).B.continuous_oneVal))

/-- `μ̃` keeps the `[0, 1]ⁿ`-coordinate and acts on the `W`-component by `μ`:
if `h = μ̃((q, φ), k)` then `h₂ = μ(φ, k₂)` and `q(h) = q(k)`. -/
theorem cubeVal_μ {h k : (A.cubeSEP n).B.One} {φ : (A.cubeSEP n).Mor}
    (hk : (A.cubeSEP n).P ((A.cubeSEP n).B.oneVal k) = (A.cubeSEP n).X.src φ)
    (hh : (A.cubeSEP n).B.oneVal h = (A.cubeSEP n).E.μ ⟨(φ, (A.cubeSEP n).B.oneVal k), hk⟩) :
    ∃ hk' : A.P (cubeVal ((A.cubeSEP n).B.oneVal k)).2 = A.X.src φ.2,
      (cubeVal ((A.cubeSEP n).B.oneVal h)).2 =
        A.E.μ ⟨(φ.2, (cubeVal ((A.cubeSEP n).B.oneVal k)).2), hk'⟩ ∧
      cubeCoord h = cubeCoord k := by
  have hk2 : (cubeVal ((A.cubeSEP n).B.oneVal k)).1 = (φ.1, A.X.src φ.2) := hk
  have hP : A.P (cubeVal ((A.cubeSEP n).B.oneVal k)).2 =
      (cubeVal ((A.cubeSEP n).B.oneVal k)).1.2 := ((A.cubeSEP n).B.oneVal k).2
  refine ⟨hP.trans (congrArg Prod.snd hk2), ?_, ?_⟩
  · exact congrArg (fun q : (A.cubeSEP n).W => (cubeVal q).2) hh
  · have h1 : (cubeVal ((A.cubeSEP n).B.oneVal h)).1.1 = φ.1 :=
      congrArg (fun q : (A.cubeSEP n).W => (cubeVal q).1.1) hh
    exact h1.trans (congrArg Prod.fst hk2).symm

/-- **`Ñ` is an auxiliary norm of the strong bundle `(W̃, μ̃)` over the ep-groupoid
`[0, 1]ⁿ × X`** (Definition 8.3.5, p. 379, including the invariance (3) under `μ̃`). -/
theorem isAuxNorm_cubeAuxNorm {N : A.B.One → ℝ} (hN : A.E.IsAuxNorm N) :
    (A.cubeSEP n).E.IsAuxNorm (cubeAuxNorm n N) := by
  refine ⟨isAuxNorm_cubeAuxNorm' hN.isAuxNorm, fun h k φ hk hh => ?_⟩
  obtain ⟨hk', hμ, -⟩ := cubeVal_μ hk hh
  have := MPolyfold.paracompactSpace_prod (cubePolyfold n) A.X.PObj
  have := A.B.paracompactSpace_pullback ((cubePolyfold n).prod A.X.PObj) (A.X.cubeProj n).obj
  exact hN.map_μ (StrongBundle.pullbackOneMap (A.X.cubeProj n).isScSmoothMap_obj h)
    (StrongBundle.pullbackOneMap (A.X.cubeProj n).isScSmoothMap_obj k) φ.2 hk' hμ

/-! ### Compactness over `[0, 1]ⁿ × X` -/

/-- `cl |[0, 1]ⁿ × S|` is compact if `cl |S|` is. -/
theorem isCompact_closure_image_π_cube {S : Set A.Obj} (hS : IsCompact (closure (A.X.π '' S))) :
    IsCompact (closure ((A.cubeSEP n).X.π '' (univ ×ˢ S))) := by
  have := MPolyfold.paracompactSpace_prod (cubePolyfold n) A.X.PObj
  have := MPolyfold.paracompactSpace_prod (cubePolyfold n) A.X.PMor
  have hK : IsCompact (A.X.cubeOrbitMap n '' (univ ×ˢ closure (A.X.π '' S))) :=
    (isCompact_univ.prod hS).image (A.X.continuous_cubeOrbitMap n)
  have hsub : (A.cubeSEP n).X.π '' (univ ×ˢ S) ⊆
      A.X.cubeOrbitMap n '' (univ ×ˢ closure (A.X.π '' S)) := by
    have := A.X.image_π_cubeProd n univ S
    intro o ho
    have ho' : o ∈ (A.X.cubeProd n).π '' (univ ×ˢ S) := ho
    rw [this] at ho'
    exact image_mono (prod_mono subset_rfl subset_closure) ho'
  exact hK.of_isClosed_subset isClosed_closure (closure_minimal hsub hK.isClosed)

open SBLocalization in
/-- **The proof of Corollary 15.3.10, p. 699**: if `(N, U)` controls the compactness of `f`, then
`(Ñ, [0, 1]ⁿ × U)` controls the compactness of `f̃`. -/
theorem controlsCompactness_cube {f : A.Obj → A.W} (hf : IsSection A.P f) {N : A.B.One → ℝ}
    {U : Set A.Obj} (h : ControlsCompactness A f N U) :
    ControlsCompactness (A.cubeSEP n) (cubeLiftEp (n := n) f hf) (cubeAuxNorm n N)
      (univ ×ˢ U) := by
  have := MPolyfold.paracompactSpace_prod (cubePolyfold n) A.X.PObj
  have := MPolyfold.paracompactSpace_prod (cubePolyfold n) A.X.PMor
  obtain ⟨hN, hUo, hUs, hSU, hC⟩ := h
  refine ⟨isAuxNorm_cubeAuxNorm hN, isOpen_univ.prod hUo, A.X.isSaturated_prod_cubeProd n univ hUs,
    ?_, ?_⟩
  · rw [solutionSet_cubeLiftEp]
    exact prod_mono subset_rfl hSU
  · refine (isCompact_closure_image_π_cube hC).of_isClosed_subset isClosed_closure
      (closure_mono (image_mono ?_))
    rintro z ⟨⟨-, hz⟩, hle⟩
    exact ⟨mem_univ _, hz, (auxLe_cubeAuxNorm_iff hf z).1 hle⟩

/-! ### Corollary 15.3.10 (2): interpolating two controlling pairs -/

/-- The time `t ∈ [0, 1]` of a point of `W̃_{0,1}` (`n = 1`). -/
def cubeTime (w : (A.cubeSEP 1).B.One) : ℝ := (cubeCoord w 0 : ℝ)

theorem continuous_cubeTime : Continuous (cubeTime (A := A)) :=
  continuous_subtype_val.comp ((continuous_apply 0).comp continuous_cubeCoord)

theorem cubeTime_mem (w : (A.cubeSEP 1).B.One) : cubeTime w ∈ Icc (0 : ℝ) 1 :=
  (cubeCoord w 0).2

variable (A) in
/-- **The interpolated norm** `Ñ(t, x, h) = max(α(t)·N⁰(h), β(t)·N¹(h))`. -/
def interpAuxNorm (N₀ N₁ : A.B.One → ℝ) (w : (A.cubeSEP 1).B.One) : ℝ :=
  max (cubeWeight₀ (cubeTime w) * cubeAuxNorm 1 N₀ w)
    (cubeWeight₁ (cubeTime w) * cubeAuxNorm 1 N₁ w)

/-- `cubeTime` of `toOne v` for `v` in the fibre over `z` is the time of `z`. -/
theorem cubeTime_toOne {z : (A.cubeSEP 1).Obj} (v : (A.cubeSEP 1).B.oneFiber z) :
    cubeTime ((A.cubeSEP 1).B.toOne v) = (z.1 0 : ℝ) := by
  have h : (A.cubeSEP 1).P ((A.cubeSEP 1).B.oneVal ((A.cubeSEP 1).B.toOne v)) = z :=
    (A.cubeSEP 1).B.proj_oneVal_toOne v
  change ((cubeVal ((A.cubeSEP 1).B.oneVal ((A.cubeSEP 1).B.toOne v))).1.1 0 : ℝ) = _
  rw [← cubeSEP_P, h]

/-- **`Ñ` is an auxiliary norm of `(W̃, μ̃)`** (Definition 8.3.5) if `N⁰` and `N¹` are auxiliary
norms of `(W, μ)`. -/
theorem isAuxNorm_interpAuxNorm {N₀ N₁ : A.B.One → ℝ} (h₀ : A.E.IsAuxNorm N₀)
    (h₁ : A.E.IsAuxNorm N₁) : (A.cubeSEP 1).E.IsAuxNorm (interpAuxNorm A N₀ N₁) := by
  have p₀ := isAuxNorm_cubeAuxNorm' (n := 1) h₀.isAuxNorm
  have p₁ := isAuxNorm_cubeAuxNorm' (n := 1) h₁.isAuxNorm
  refine ⟨⟨?_, fun z => ?_, fun w z hw hNw => ?_⟩, fun h k φ hk hh => ?_⟩
  · exact (((continuous_cubeWeight₀.comp continuous_cubeTime).mul p₀.continuous).max
      ((continuous_cubeWeight₁.comp continuous_cubeTime).mul p₁.continuous))
  · have hz := (z.1 0).2
    refine ((StrongBundle.isAuxNorm_max_mul p₀ p₁ (cubeWeight₀_nonneg hz.2)
      (cubeWeight₁_nonneg hz.1) (cubeWeight_pos _)).fiber z).congr fun v => ?_
    simp only [interpAuxNorm, cubeTime_toOne]
  · have hc : Continuous fun p : (Fin 1 → unitInterval) × A.Obj => (p.1 0 : ℝ) :=
      continuous_subtype_val.comp ((continuous_apply 0).comp continuous_fst)
    set t₀ : ℝ := ((show (Fin 1 → unitInterval) × A.Obj from z).1 0 : ℝ)
    have ht : Tendsto (fun k => cubeTime (w k)) atTop (𝓝 t₀) := (hc.tendsto z).comp hw
    rcases cubeWeight_pos t₀ with hpos | hpos
    · have hev : ∀ᶠ k in atTop, cubeWeight₀ t₀ / 2 < cubeWeight₀ (cubeTime (w k)) :=
        ((continuous_cubeWeight₀.tendsto _).comp ht).eventually (lt_mem_nhds (by linarith))
      refine p₀.tendsto_zeroOne w z hw (squeeze_zero' (Eventually.of_forall fun k => p₀.nonneg _)
        (hev.mono fun k hk => ?_) (by simpa using hNw.const_mul (2 / cubeWeight₀ t₀)))
      have h2 : cubeWeight₀ t₀ / 2 * cubeAuxNorm 1 N₀ (w k) ≤ interpAuxNorm A N₀ N₁ (w k) :=
        (mul_le_mul_of_nonneg_right hk.le (p₀.nonneg _)).trans (le_max_left _ _)
      calc cubeAuxNorm 1 N₀ (w k)
          = 2 / cubeWeight₀ t₀ * (cubeWeight₀ t₀ / 2 * cubeAuxNorm 1 N₀ (w k)) := by
            field_simp
        _ ≤ 2 / cubeWeight₀ t₀ * interpAuxNorm A N₀ N₁ (w k) :=
            mul_le_mul_of_nonneg_left h2 (by positivity)
    · have hev : ∀ᶠ k in atTop, cubeWeight₁ t₀ / 2 < cubeWeight₁ (cubeTime (w k)) :=
        ((continuous_cubeWeight₁.tendsto _).comp ht).eventually (lt_mem_nhds (by linarith))
      refine p₁.tendsto_zeroOne w z hw (squeeze_zero' (Eventually.of_forall fun k => p₁.nonneg _)
        (hev.mono fun k hk => ?_) (by simpa using hNw.const_mul (2 / cubeWeight₁ t₀)))
      have h2 : cubeWeight₁ t₀ / 2 * cubeAuxNorm 1 N₁ (w k) ≤ interpAuxNorm A N₀ N₁ (w k) :=
        (mul_le_mul_of_nonneg_right hk.le (p₁.nonneg _)).trans (le_max_right _ _)
      calc cubeAuxNorm 1 N₁ (w k)
          = 2 / cubeWeight₁ t₀ * (cubeWeight₁ t₀ / 2 * cubeAuxNorm 1 N₁ (w k)) := by
            field_simp
        _ ≤ 2 / cubeWeight₁ t₀ * interpAuxNorm A N₀ N₁ (w k) :=
            mul_le_mul_of_nonneg_left h2 (by positivity)
  · obtain ⟨-, -, hc⟩ := cubeVal_μ hk hh
    have e₀ := (isAuxNorm_cubeAuxNorm (n := 1) h₀).map_μ h k φ hk hh
    have e₁ := (isAuxNorm_cubeAuxNorm (n := 1) h₁).map_μ h k φ hk hh
    have et : cubeTime h = cubeTime k := by
      unfold cubeTime; rw [hc]
    simp only [interpAuxNorm, e₀, e₁, et]

/-- **Over `t = 0`, `Ñ` restricts to `N⁰`.** -/
theorem interpAuxNorm_of_cubeTime_eq_zero {N₀ N₁ : A.B.One → ℝ} (h₀ : A.B.IsAuxNorm N₀)
    {w : (A.cubeSEP 1).B.One} (hw : cubeTime w = 0) :
    interpAuxNorm A N₀ N₁ w = cubeAuxNorm 1 N₀ w := by
  rw [interpAuxNorm, hw, cubeWeight₀_eq_one (by norm_num), cubeWeight₁_zero, one_mul, zero_mul]
  exact max_eq_left ((isAuxNorm_cubeAuxNorm' h₀).nonneg w)

/-- **Over `t = 1`, `Ñ` restricts to `N¹`.** -/
theorem interpAuxNorm_of_cubeTime_eq_one {N₀ N₁ : A.B.One → ℝ} (h₁ : A.B.IsAuxNorm N₁)
    {w : (A.cubeSEP 1).B.One} (hw : cubeTime w = 1) :
    interpAuxNorm A N₀ N₁ w = cubeAuxNorm 1 N₁ w := by
  rw [interpAuxNorm, hw, cubeWeight₀_one, cubeWeight₁_eq_one (by norm_num), one_mul, zero_mul]
  exact max_eq_right ((isAuxNorm_cubeAuxNorm' h₁).nonneg w)

variable (A) in
/-- **The interpolated neighbourhood** `Ũ = ([0, 2/3) × U⁰) ∪ ((1/3, 1] × U¹)`. -/
def interpSet (U₀ U₁ : Set A.Obj) : Set ((Fin 1 → unitInterval) × A.Obj) :=
  ({q : Fin 1 → unitInterval | (q 0 : ℝ) < 2 / 3} ×ˢ U₀) ∪
    ({q : Fin 1 → unitInterval | 1 / 3 < (q 0 : ℝ)} ×ˢ U₁)

/-- **Over `t = 0`, `Ũ` restricts to `U⁰`.** -/
theorem mem_interpSet_zero {U₀ U₁ : Set A.Obj} {q : Fin 1 → unitInterval} (hq : (q 0 : ℝ) = 0)
    (x : A.Obj) : (q, x) ∈ interpSet A U₀ U₁ ↔ x ∈ U₀ := by
  simp only [interpSet, mem_union, mem_prod, mem_ofPred_eq, hq]
  norm_num

/-- **Over `t = 1`, `Ũ` restricts to `U¹`.** -/
theorem mem_interpSet_one {U₀ U₁ : Set A.Obj} {q : Fin 1 → unitInterval} (hq : (q 0 : ℝ) = 1)
    (x : A.Obj) : (q, x) ∈ interpSet A U₀ U₁ ↔ x ∈ U₁ := by
  simp only [interpSet, mem_union, mem_prod, mem_ofPred_eq, hq]
  norm_num

open SBLocalization in
/-- **Corollary 15.3.10 (2), p. 699 (2017: Corollary 15.1 (2))**: if `(N⁰, U⁰)` and `(N¹, U¹)`
control the compactness of `f`, then `(Ñ, Ũ)` controls the compactness of
`f̃(t, x) = (t, f(x))` on `W̃ → [0, 1] × X`, and `(Ñ, Ũ)` restricts to `(Nⁱ, Uⁱ)` over `t = i`
(`interpAuxNorm_of_cubeTime_eq_zero/one`, `mem_interpSet_zero/one`). -/
theorem corollary_15_3_10_2 {f : A.Obj → A.W} (hf : IsSection A.P f) {N₀ N₁ : A.B.One → ℝ}
    {U₀ U₁ : Set A.Obj} (h₀ : ControlsCompactness A f N₀ U₀)
    (h₁ : ControlsCompactness A f N₁ U₁) :
    ControlsCompactness (A.cubeSEP 1) (cubeLiftEp (n := 1) f hf) (interpAuxNorm A N₀ N₁)
      (interpSet A U₀ U₁) := by
  have := MPolyfold.paracompactSpace_prod (cubePolyfold 1) A.X.PObj
  have := MPolyfold.paracompactSpace_prod (cubePolyfold 1) A.X.PMor
  obtain ⟨hN₀, hU₀o, hU₀s, hSU₀, hC₀⟩ := h₀
  obtain ⟨hN₁, hU₁o, hU₁s, hSU₁, hC₁⟩ := h₁
  have hq : Continuous fun q : Fin 1 → unitInterval => (q 0 : ℝ) :=
    continuous_subtype_val.comp (continuous_apply 0)
  refine ⟨isAuxNorm_interpAuxNorm hN₀ hN₁, ?_, ?_, ?_, ?_⟩
  · exact ((isOpen_lt hq continuous_const).prod hU₀o).union
      ((isOpen_lt continuous_const hq).prod hU₁o)
  · have s₀ := A.X.isSaturated_prod_cubeProd 1 {q : Fin 1 → unitInterval | (q 0 : ℝ) < 2 / 3} hU₀s
    have s₁ := A.X.isSaturated_prod_cubeProd 1 {q : Fin 1 → unitInterval | 1 / 3 < (q 0 : ℝ)} hU₁s
    unfold GroupoidStr.IsSaturated at s₀ s₁ ⊢
    change (A.X.cubeProd 1).π ⁻¹' ((A.X.cubeProd 1).π '' interpSet A U₀ U₁) = interpSet A U₀ U₁
    rw [interpSet, image_union, preimage_union, s₀, s₁]
  · rw [solutionSet_cubeLiftEp]
    rintro ⟨q, x⟩ ⟨-, hx⟩
    by_cases h : (q 0 : ℝ) < 2 / 3
    · exact Or.inl ⟨h, hSU₀ hx⟩
    · exact Or.inr ⟨by change 1 / 3 < (q 0 : ℝ); linarith, hSU₁ hx⟩
  · set S₀ := {x ∈ U₀ | A.B.AuxLe N₀ (f x) 1}
    set S₁ := {x ∈ U₁ | A.B.AuxLe N₁ (f x) 1}
    have hsub : {z ∈ interpSet A U₀ U₁ | (A.cubeSEP 1).B.AuxLe (interpAuxNorm A N₀ N₁)
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
        rw [ht, cubeWeight₀_eq_one (by change (q 0 : ℝ) < 2 / 3 at hq0; linarith), one_mul]
        exact (cubeAuxNorm_eq _ _ rfl).ge
      · refine Or.inr ⟨mem_univ _, hx, hmem, ?_⟩
        refine le_trans ?_ ((le_max_right _ _).trans hle)
        rw [ht, cubeWeight₁_eq_one (by change 1 / 3 < (q 0 : ℝ) at hq1; linarith), one_mul]
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
