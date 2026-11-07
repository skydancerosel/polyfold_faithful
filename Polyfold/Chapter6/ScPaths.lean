import Polyfold.Chapter6.OrientableNbhd

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory I* (2014 preprint), Part I, §6.5,
pp. 226–227: the paths used after **Theorem 6.35** and in **Definition 6.36** (a path from `x` to
each `y ∈ U_∞`; propagation along a path from `y₁` to `y₂`) and the composition of paths of
p. 228 *(book 2017: after Theorem 6.1 and Definition 6.10; see `BookConcordance.md`)*.

# Sc-smooth paths in a chart and their concatenation

## The text, paraphrased

"We fix `x` and take for `y ∈ U` a sc-smooth path `φ : [0, 1] → U`, starting at `x` and ending at
`y`" (after Theorem 6.35).  (p. 228) For sc-smooth paths `φ`, `ψ` with `φ(1) = ψ(0)`, take a smooth
`β : [0, 1] → [0, 2]` with `β([0, 1/2]) = [0, 1]`, `β(0) = 0`, `β(s) = 1` near `1/2`,
`β([1/2, 1]) = [1, 2]`, `β(1) = 2`, and `γ(s) = φ(β(s))` on `[0, 1/2]`, `γ(s) = ψ(β(s) − 1)` on
`[1/2, 1]`.

## What is formalized

* `exists_nhds_scPath`: for an open `U` in the domain of a chart and `x ∈ U` there is an open
  `V ∋ x` in `U` such that any two smooth points of `V` are joined by an sc-smooth path with values
  in `U` (in the chart: `t ↦ r(u₁ + κ(t)(u₂ − u₁))` with `κ` the smooth transition function).
* `concatPath γ₁ γ₂`: the concatenation, with `κ(3s)` on `s ≤ 1/2` and `κ(3s − 2)` on `s > 1/2`
  (constant `γ₁(1) = γ₂(0)` for `s ∈ [1/3, 2/3]`); `isScSmoothMap_concatPath`, its end points, its
  values, and its two halves `s ↦ γ(s/2)`, `s ↦ γ((1 + s)/2)` (reparametrizations of `γ₁`, `γ₂`).
* `isScSmoothMap_reparam`: a path reparametrized by a `C^∞` map `ℝ → ℝ` is sc-smooth.
* The tools: `MPolyfold.isScSmoothMap_of_eventuallyEq` (a map which near every point coincides
  with an sc-smooth map is sc-smooth), `pt1_apply`, `contDiff_pt1_comp`, and the two formulas
  `concatPath_of_le`, `concatPath_of_gt`.

## Reading

Paths are on `ℝ` and only `[0, 1]` matters (decision D2).  The neighbourhood `U` of Proposition
6.28 is not shown to be sc-smoothly contractible (see `OrientableNbhd.lean`); the paths from `x`
to the points `y` of a smaller neighbourhood `V` run in `U` (`exists_nhds_scPath`).
-/

open Set Filter Topology Function
open scoped ContDiff

noncomputable section

namespace Polyfold

universe u v

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle PX P}

/-- **Sc-smoothness of maps is local**: a map which near every point coincides with an sc-smooth
map is sc-smooth. -/
theorem MPolyfold.isScSmoothMap_of_eventuallyEq {W : Type*} [TopologicalSpace W] [T2Space W]
    [ParacompactSpace W] {PW : MPolyfold W} {f : W → X}
    (h : ∀ w, ∃ g : W → X, PW.IsScSmoothMap PX g ∧ f =ᶠ[𝓝 w] g) : PW.IsScSmoothMap PX f := by
  refine MPolyfold.isScSmoothMap_of_local fun w => ?_
  obtain ⟨g, hg, hfg⟩ := h w
  obtain ⟨N, hN, hNo, hwN⟩ := eventually_nhds_iff.1 hfg
  obtain ⟨φ, hφ, hwφ⟩ := PW.exists_isChart_mem_source w
  obtain ⟨ψ, hψ, hgψ⟩ := PX.exists_isChart_mem_source (g w)
  have hgc : Continuous g := continuousOn_univ.1 hg.continuousOn
  set V := N ∩ φ.source ∩ g ⁻¹' ψ.source with hV
  have hVo : IsOpen V := (hNo.inter φ.isOpen_source).inter (ψ.isOpen_source.preimage hgc)
  have hfV : MapsTo f V ψ.source := fun y hy => by rw [hN y hy.1.1]; exact hy.2
  refine ⟨φ, ψ, V, hφ, hψ, hVo, ⟨⟨hwN, hwφ⟩, hgψ⟩, fun y hy => hy.1.2, hfV, ?_⟩
  refine (hg.smooth φ ψ hφ hψ V hVo (fun y hy => ⟨mem_univ _, hy.1.2⟩)
    fun y hy => hy.2).congr ?_
  rintro _ ⟨y, hy, rfl⟩
  simp only [Function.comp_apply, φ.symm_apply_apply hy.1.2, hN y hy.1.1]

@[simp] lemma pt1_apply (t : ℝ) (i : Fin 1) : pt1 t i = t := rfl

/-- `s ↦ pt1 (κ (s 0))` is `C^∞` for a `C^∞` `κ : ℝ → ℝ`. -/
lemma contDiff_pt1_comp {κ : ℝ → ℝ} (hκ : ContDiff ℝ ∞ κ) :
    ContDiff ℝ ∞ fun s : Fin 1 → ℝ => pt1 (κ (s 0)) :=
  contDiff_pi.2 fun _ => hκ.comp (contDiff_apply ℝ ℝ (0 : Fin 1))

-- `hc` is part of the statement; the construction only uses that `c.φ` is a chart of `PX`
set_option linter.unusedVariables false in
/-- **Smooth points near `x` are joined by sc-smooth paths in `U`**: for an open `U` in the domain
of a chart `c` and `x ∈ U`, there is an open `V ∋ x` in `U` such that any two smooth points
`y₁, y₂ ∈ V` are joined by an sc-smooth path `γ : ℝ → X` with values in `U`. -/
theorem exists_nhds_scPath {c : StrongBundleChart PX P} (hc : B.IsChart c) {U : Set X}
    (hU : IsOpen U) (hUc : U ⊆ c.φ.source) {x : X} (hx : x ∈ U) :
    ∃ V : Set X, IsOpen V ∧ x ∈ V ∧ V ⊆ U ∧ ∀ y₁ ∈ V, ∀ y₂ ∈ V, y₁ ∈ PX.smoothSet →
      y₂ ∈ PX.smoothSet → ∃ γ : (Fin 1 → ℝ) → X, (rnPolyfold 1).IsScSmoothMap PX γ ∧
        γ (pt1 0) = y₁ ∧ γ (pt1 1) = y₂ ∧ ∀ t, γ t ∈ U := by
  classical
  have hxc : x ∈ c.φ.source := hUc hx
  set u₀ := c.φ x with hu₀
  set r := StrongRetr.r c.R with hr
  have hu₀O : u₀ ∈ c.φ.model.O := c.φ.mapsTo_model x hxc
  have hOU : ∀ {u}, u ∈ c.φ.model.O → u ∈ c.U := fun hu =>
    StrongRetr.mem_U_of_mem_O c.isRetraction (c.r_image ▸ hu)
  have hrO : ∀ {u}, u ∈ c.U → r u ∈ c.φ.model.O := fun hu => c.r_mem_O hu
  have hrfix : ∀ {u}, u ∈ c.φ.model.O → r u = u := fun hu =>
    StrongRetr.r_eq_self c.isRetraction (c.r_image ▸ hu)
  have hCconv : Convex ℝ c.φ.model.C := c.relOpen.isPartialQuadrant.convex
  obtain ⟨O', hO'o, hO'⟩ := c.relOpen.relOpen
  have hUC : c.U ⊆ c.φ.model.C := by rw [hO']; exact inter_subset_right
  -- `B_δ ∩ C ⊆ U` (the domain of the retraction)
  obtain ⟨δ, hδ, hδO'⟩ := Metric.isOpen_iff.1 hO'o u₀ (by
    have := hOU hu₀O
    rw [hO'] at this
    exact this.1)
  have hballU : ∀ {u}, u ∈ Metric.ball u₀ δ → u ∈ c.φ.model.C → u ∈ c.U := fun h1 h2 => by
    rw [hO']; exact ⟨hδO' h1, h2⟩
  -- `φ⁻¹(r(B_{ε₁} ∩ U)) ⊆ U` (continuity of `r` at level `0` and of `φ⁻¹`)
  have hrcont : ContinuousOn r c.U :=
    (c.isRetraction.baseRetraction c.relOpen).isScSmooth.isSc1.isSc0.continuousOn_base
  have hsymm : c.φ.symm ⁻¹' U ∈ 𝓝[c.φ.model.O] u₀ :=
    (c.φ.continuousOn_invFun u₀ hu₀O).preimage_mem_nhdsWithin (hU.mem_nhds (by
      rw [show c.φ.toPartialEquiv.symm u₀ = x from c.φ.symm_apply_apply hxc]; exact hx))
  have hrt : Tendsto r (𝓝[c.U] u₀) (𝓝[c.φ.model.O] u₀) := by
    have := (hrcont u₀ (hOU hu₀O)).tendsto_nhdsWithin fun u hu => hrO hu
    rwa [hrfix hu₀O] at this
  have hpre : r ⁻¹' (c.φ.symm ⁻¹' U) ∈ 𝓝[c.U] u₀ := hrt hsymm
  obtain ⟨ε₁, hε₁, hε₁U⟩ := Metric.mem_nhdsWithin_iff.1 hpre
  set ε := min δ ε₁ with hεdef
  have hε : 0 < ε := lt_min hδ hε₁
  set V : Set X := c.φ.source ∩ c.φ ⁻¹' Metric.ball u₀ ε ∩ U with hVdef
  refine ⟨V, (c.φ.continuousOn_toFun.isOpen_inter_preimage c.φ.isOpen_source
    Metric.isOpen_ball).inter hU, ⟨⟨hxc, Metric.mem_ball_self hε⟩, hx⟩, inter_subset_right, ?_⟩
  intro y₁ hy₁ y₂ hy₂ hs₁ hs₂
  -- the segment `G(p) = (1 − κ(p)) u₁ + κ(p) u₂` lies in `B_ε ∩ C`
  set u₁ := c.φ y₁ with hu₁
  set u₂ := c.φ y₂ with hu₂
  set G : (Fin 1 → ℝ) → c.φ.model.E 0 := fun p =>
    (1 - Real.smoothTransition (p 0)) • u₁ + Real.smoothTransition (p 0) • u₂ with hGdef
  have hvB : ∀ {y}, y ∈ V → c.φ y ∈ Metric.ball u₀ ε ∩ c.φ.model.C := fun hy =>
    ⟨hy.1.2, hUC (hOU (c.φ.mapsTo_model _ hy.1.1))⟩
  have hGB : ∀ p, G p ∈ Metric.ball u₀ ε ∩ c.φ.model.C := fun p =>
    ((convex_ball u₀ ε).inter hCconv) (hvB hy₁) (hvB hy₂)
      (sub_nonneg.2 (Real.smoothTransition.le_one _)) (Real.smoothTransition.nonneg _)
      (sub_add_cancel 1 _)
  have hGU : ∀ p, G p ∈ c.U := fun p =>
    hballU (Metric.ball_subset_ball (min_le_left _ _) (hGB p).1) (hGB p).2
  have hGr : ∀ p, c.φ.symm (r (G p)) ∈ U := fun p =>
    hε₁U ⟨Metric.ball_subset_ball (min_le_right _ _) (hGB p).1, hGU p⟩
  -- smooth points of `X` are smooth points of the model
  have hsm : ∀ {y}, y ∈ c.φ.source → y ∈ PX.smoothSet → c.φ y ∈ c.φ.model.E.smooth :=
    fun hy hys => c.φ.model.E.mem_smooth_iff.2 fun m =>
      (PX.mem_levelSet_iff c.isChart hy).1 (mem_iInter.1 hys m)
  have hfix : ∀ y ∈ c.φ.source, c.φ.symm (r (c.φ y)) = y := fun y hy => by
    rw [hrfix (c.φ.mapsTo_model y hy), c.φ.symm_apply_apply hy]
  refine ⟨fun p => c.φ.symm (r (G p)), ?_, ?_, ?_, hGr⟩
  · -- sc-smoothness, read in the chart
    have hU1 := isScDomain_univ (rnSc 1)
    have hc₁ : IsScSmooth (E := rnSc 1) (F := c.φ.model.E) univ fun _ => u₁ :=
      isScSmooth_const_of_mem_smooth hU1 (hsm hy₁.1.1 hs₁)
    have hc₂ : IsScSmooth (E := rnSc 1) (F := c.φ.model.E) univ fun _ => u₂ :=
      isScSmooth_const_of_mem_smooth hU1 (hsm hy₂.1.1 hs₂)
    have hρ0 : IsScSmooth (E := rnSc 1) (F := ScBanach.const ℝ) univ
        fun p : Fin 1 → ℝ => Real.smoothTransition (p 0) :=
      IsScSmooth.of_contDiffOn_finiteDimensional (V := ℝ) hU1
        ((Real.smoothTransition.contDiff.comp (contDiff_apply ℝ ℝ (0 : Fin 1))).contDiffOn)
    have hρ1 : IsScSmooth (E := rnSc 1) (F := ScBanach.const ℝ) univ
        fun p : Fin 1 → ℝ => 1 - Real.smoothTransition (p 0) :=
      IsScSmooth.of_contDiffOn_finiteDimensional (V := ℝ) hU1 ((contDiff_const.sub
        (Real.smoothTransition.contDiff.comp (contDiff_apply ℝ ℝ (0 : Fin 1)))).contDiffOn)
    have hG : IsScSmooth (E := rnSc 1) (F := c.φ.model.E) univ G :=
      (hρ1.smul hU1 hc₁).add hU1 (hρ0.smul hU1 hc₂)
    have hrG : IsScSmooth (E := rnSc 1) (F := c.φ.model.E) univ fun p => r (G p) :=
      IsScSmooth.comp hU1 c.relOpen.isScDomain
        (c.isRetraction.baseRetraction c.relOpen).isScSmooth hG fun p _ => hGU p
    exact isScSmoothMap_rn_chart_symm c.isChart hrG fun p => hrO (hGU p)
  · change c.φ.symm (r ((1 - Real.smoothTransition 0) • u₁ + Real.smoothTransition 0 • u₂)) = y₁
    rw [Real.smoothTransition.zero, sub_zero, one_smul, zero_smul, add_zero]
    exact hfix _ hy₁.1.1
  · change c.φ.symm (r ((1 - Real.smoothTransition 1) • u₁ + Real.smoothTransition 1 • u₂)) = y₂
    rw [Real.smoothTransition.one, sub_self, zero_smul, one_smul, zero_add]
    exact hfix _ hy₂.1.1

/-- **The concatenation of two paths** (p. 228), reparametrized by the smooth transition
function `κ`: `γ₁(κ(3s))` for `s ≤ 1/2` and `γ₂(κ(3s − 2))` for `s > 1/2`. -/
def concatPath (γ₁ γ₂ : (Fin 1 → ℝ) → X) : (Fin 1 → ℝ) → X := fun s =>
  if s 0 ≤ 1 / 2 then γ₁ (pt1 (Real.smoothTransition (3 * s 0)))
  else γ₂ (pt1 (Real.smoothTransition (3 * s 0 - 2)))

variable {γ₁ γ₂ : (Fin 1 → ℝ) → X}

-- the topology of `X` plays no role in the two formulas
set_option linter.unusedSectionVars false in
/-- `concatPath` on `s ≤ 1/2`. -/
lemma concatPath_of_le {s : Fin 1 → ℝ} (hs : s 0 ≤ 1 / 2) :
    concatPath γ₁ γ₂ s = γ₁ (pt1 (Real.smoothTransition (3 * s 0))) := if_pos hs

set_option linter.unusedSectionVars false in
/-- `concatPath` on `s > 1/2`. -/
lemma concatPath_of_gt {s : Fin 1 → ℝ} (hs : 1 / 2 < s 0) :
    concatPath γ₁ γ₂ s = γ₂ (pt1 (Real.smoothTransition (3 * s 0 - 2))) := if_neg (not_le.2 hs)

/-- The concatenation of sc-smooth paths with `γ₁(1) = γ₂(0)` is sc-smooth (it is constant near
`s = 1/2`). -/
theorem isScSmoothMap_concatPath (h₁ : (rnPolyfold 1).IsScSmoothMap PX γ₁)
    (h₂ : (rnPolyfold 1).IsScSmoothMap PX γ₂) (h : γ₁ (pt1 1) = γ₂ (pt1 0)) :
    (rnPolyfold 1).IsScSmoothMap PX (concatPath γ₁ γ₂) := by
  have hκ₁ : ContDiff ℝ ∞ fun t : ℝ => Real.smoothTransition (3 * t) :=
    Real.smoothTransition.contDiff.comp (contDiff_const.mul contDiff_id)
  have hκ₂ : ContDiff ℝ ∞ fun t : ℝ => Real.smoothTransition (3 * t - 2) :=
    Real.smoothTransition.contDiff.comp ((contDiff_const.mul contDiff_id).sub contDiff_const)
  have hg₁ : (rnPolyfold 1).IsScSmoothMap PX
      fun s => γ₁ (pt1 (Real.smoothTransition (3 * s 0))) :=
    h₁.comp (isScSmoothMap_rn_rn_of_contDiff (contDiff_pt1_comp hκ₁))
  have hg₂ : (rnPolyfold 1).IsScSmoothMap PX
      fun s => γ₂ (pt1 (Real.smoothTransition (3 * s 0 - 2))) :=
    h₂.comp (isScSmoothMap_rn_rn_of_contDiff (contDiff_pt1_comp hκ₂))
  have hcont : Continuous fun s : Fin 1 → ℝ => s 0 := continuous_apply 0
  refine MPolyfold.isScSmoothMap_of_eventuallyEq fun s => ?_
  rcases lt_or_ge (s 0) (2 / 3) with hs | hs
  · -- on `{s < 2/3}` the concatenation is `γ₁(κ(3s))`
    refine ⟨_, hg₁, ?_⟩
    filter_upwards [(isOpen_lt hcont continuous_const).mem_nhds hs] with p hp
    change p 0 < 2 / 3 at hp
    rcases le_or_gt (p 0) (1 / 2) with hp' | hp'
    · exact concatPath_of_le hp'
    · have h0 : Real.smoothTransition (3 * p 0 - 2) = 0 :=
        Real.smoothTransition.zero_of_nonpos (by linarith)
      have h1 : Real.smoothTransition (3 * p 0) = 1 :=
        Real.smoothTransition.one_of_one_le (by linarith)
      rw [concatPath_of_gt hp', h0, h1, ← h]
  · -- on `{s > 1/3}` it is `γ₂(κ(3s − 2))`
    refine ⟨_, hg₂, ?_⟩
    filter_upwards [(isOpen_lt continuous_const hcont).mem_nhds
      (show (1 / 3 : ℝ) < s 0 by linarith)] with p hp
    change 1 / 3 < p 0 at hp
    rcases le_or_gt (p 0) (1 / 2) with hp' | hp'
    · have h0 : Real.smoothTransition (3 * p 0 - 2) = 0 :=
        Real.smoothTransition.zero_of_nonpos (by linarith)
      have h1 : Real.smoothTransition (3 * p 0) = 1 :=
        Real.smoothTransition.one_of_one_le (by linarith)
      rw [concatPath_of_le hp', h0, h1, h]
    · exact concatPath_of_gt hp'

theorem concatPath_zero : concatPath γ₁ γ₂ (pt1 0) = γ₁ (pt1 0) := by
  rw [concatPath_of_le (s := pt1 0) (show (0 : ℝ) ≤ 1 / 2 by norm_num), pt1_apply, mul_zero,
    Real.smoothTransition.zero]

theorem concatPath_one : concatPath γ₁ γ₂ (pt1 1) = γ₂ (pt1 1) := by
  rw [concatPath_of_gt (s := pt1 1) (show (1 / 2 : ℝ) < 1 by norm_num), pt1_apply,
    show (3 : ℝ) * 1 - 2 = 1 by norm_num, Real.smoothTransition.one]

/-- The concatenation takes its values on `[0, 1]` among those of `γ₁` and `γ₂` on `[0, 1]`. -/
theorem concatPath_mem {U : Set X} (hγ₁ : ∀ t ∈ Icc (0 : ℝ) 1, γ₁ (pt1 t) ∈ U)
    (hγ₂ : ∀ t ∈ Icc (0 : ℝ) 1, γ₂ (pt1 t) ∈ U) :
    ∀ s ∈ Icc (0 : ℝ) 1, concatPath γ₁ γ₂ (pt1 s) ∈ U := by
  intro s _
  rcases le_or_gt s (1 / 2) with h | h
  · rw [concatPath_of_le (s := pt1 s) h]
    exact hγ₁ _ ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩
  · rw [concatPath_of_gt (s := pt1 s) h]
    exact hγ₂ _ ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩

/-- The first half `s ↦ γ(s/2)` is `γ₁` reparametrized by `κ(3s/2)`. -/
theorem concatPath_half₁ (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) :
    concatPath γ₁ γ₂ (pt1 (s / 2)) = γ₁ (pt1 (Real.smoothTransition (3 * s / 2))) := by
  rw [concatPath_of_le (s := pt1 (s / 2)) (show s / 2 ≤ 1 / 2 by linarith [hs.2]), pt1_apply,
    show 3 * (s / 2) = 3 * s / 2 by ring]

/-- The second half `s ↦ γ((1 + s)/2)` is `γ₂` reparametrized by `κ((3s − 1)/2)`. -/
theorem concatPath_half₂ (h : γ₁ (pt1 1) = γ₂ (pt1 0)) (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) :
    concatPath γ₁ γ₂ (pt1 ((1 + s) / 2)) =
      γ₂ (pt1 (Real.smoothTransition ((3 * s - 1) / 2))) := by
  rcases le_or_gt ((1 + s) / 2) (1 / 2) with h' | h'
  · have h1 : Real.smoothTransition (3 * ((1 + s) / 2)) = 1 :=
      Real.smoothTransition.one_of_one_le (by linarith [hs.1])
    have h0 : Real.smoothTransition ((3 * s - 1) / 2) = 0 :=
      Real.smoothTransition.zero_of_nonpos (by linarith)
    rw [concatPath_of_le (s := pt1 ((1 + s) / 2)) h', pt1_apply, h1, h0, h]
  · rw [concatPath_of_gt (s := pt1 ((1 + s) / 2)) h', pt1_apply,
      show 3 * ((1 + s) / 2) - 2 = (3 * s - 1) / 2 by ring]

/-- **A path reparametrized by a smooth map** `κ : ℝ → ℝ` is sc-smooth. -/
theorem isScSmoothMap_reparam {γ : (Fin 1 → ℝ) → X} (hγ : (rnPolyfold 1).IsScSmoothMap PX γ)
    {κ : ℝ → ℝ} (hκ : ContDiff ℝ ∞ κ) :
    (rnPolyfold 1).IsScSmoothMap PX fun s => γ (pt1 (κ (s 0))) :=
  hγ.comp (isScSmoothMap_rn_rn_of_contDiff (contDiff_pt1_comp hκ))

end Polyfold
