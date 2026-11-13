import Polyfold.Chapter12.P3R2_ReflexiveAuxNormExtension
import Polyfold.Chapter12.P3E_AuxNormLocalExtension

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part III, Chapter 12,
§12.2, **Theorem 12.2.13** (extension of reflexive auxiliary norms), p. 578: the local step of the
proof, and the theorem with its local step proved.

# The reflexive local extension near `∂X`

## The text, paraphrased

(Proof of Theorem 12.2.13) The local extension of the proof of Theorem 12.2.7,
`N'(u, w) = N(rq(u), A(rq(u))w) + ‖w − A(rq(u))w‖_{F₁}`, is well behaved under mixed limits, "by
inspection".

## What is formalized

* Part I (`Polyfold.StrongBundle`):
  * `exists_norm_chartFibMap_le`: the fibre maps `A(u) = chartFibMap c u` of `R[1]` are locally
    uniformly bounded on `F₁` (joint continuity of `R[1]` at `(u, 0)` and linearity);
  * `weakTendsto_chartFibMap`: **if `u_k → u` in `O` and `h_k ⇀ h` in a reflexive `F₁`, then
    `A(u_k)h_k ⇀ A(u)h`** (bounded, and convergent in `F₀` through the level-`0` continuity of `R`
    and the compact inclusion `F₁ → F₀`);
  * `mixedLscAt_retractNorm`: **wave 2's local norm `N' = retractNorm` is lower semicontinuous
    along mixed convergent sequences** at every point over `V`, if `N` is so along mixed
    convergent sequences over `A` and the chart has reflexive `F₁`: the points
    `Φ[1]⁻¹(u_k, A(u_k)h_k)` over `A` are mixed convergent (first term), and
    `h_k − A(u_k)h_k ⇀ h − A(u)h` (second term, weak lower semicontinuity of the norm);
  * `exists_reflexiveLocalExtension_of_isTame`: the local step for tame `X`, in a strong bundle
    chart with reflexive `F₁` around the boundary point.
* Ep-groupoids (`Polyfold.EpStrongBundle`):
  * **`hasReflexiveLocalExtensions_of_isTame`**: for tame `X` and reflexive `1`-fibres, a
    reflexive auxiliary norm over `∂X` has reflexive local extensions, i.e. the hypothesis `hloc`
    of wave 2's `theorem_12_2_13_hyp` holds;
  * **`theorem_12_2_13`**: Theorem 12.2.13 with the hypotheses of the text plus the
    paracompactness of `|X|` (which the proof uses through the partition of unity of
    Theorem 12.2.11);
  * `theorem_12_2_13_witness`: all hypotheses together are satisfiable (the trivial bundle
    `ℝⁿ × ℝᵏ → ℝⁿ` over the tame trivial ep-groupoid of `ℝⁿ`).
-/

open Set Filter Topology Function TopologicalSpace

noncomputable section

namespace Polyfold

universe u v

/-! ### Weak convergence of differences -/

section Weak

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

lemma WeakTendsto.sub {a b : ℕ → F} {a₀ b₀ : F} (ha : WeakTendsto a a₀) (hb : WeakTendsto b b₀) :
    WeakTendsto (fun k => a k - b k) (a₀ - b₀) := fun g => by
  simp only [map_sub]
  exact (ha g).sub (hb g)

end Weak

namespace StrongBundle

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle PX P}

/-! ### The fibre maps `A(u)` -/

section FibMap

variable {c : StrongBundleChart PX P}

omit [T2Space Y] [ParacompactSpace Y] in
/-- **The fibre maps `A(u)` of `R[1]` are locally uniformly bounded**: near every `u ∈ U` there is
`C` with `‖A(u')h‖₁ ≤ C‖h‖₁` for all `u' ∈ U` nearby (joint continuity of `R[1]` on `U ⊕ F₁` at
`(u, 0)`, `A(u)0 = 0`, and linearity of `A(u')`). -/
theorem exists_norm_chartFibMap_le {u : c.φ.model.E 0} (hu : u ∈ c.U) :
    ∃ S ∈ 𝓝 u, ∃ C : ℝ, 0 < C ∧
      ∀ u' ∈ S ∩ c.U, ∀ h : c.F 1, ‖chartFibMap c u' h‖ ≤ C * ‖h‖ := by
  have hcont : ContinuousWithinAt (fun p : c.φ.model.E 0 × c.F 1 => (shiftFiber c.R p).2)
      (c.U ×ˢ univ) (u, 0) :=
    continuous_snd.continuousAt.comp_continuousWithinAt
      (continuousOn_shiftFiber_R (c := c) (u, 0) ⟨hu, mem_univ _⟩)
  have h0 : (shiftFiber c.R (u, 0)).2 = (0 : c.F 1) :=
    (isLinearMap_chartFibMap (c := c) hu).map_zero
  have hball := hcont (show Metric.ball (0 : c.F 1) 1 ∈ 𝓝 ((shiftFiber c.R (u, 0)).2) by
    rw [h0]; exact Metric.ball_mem_nhds (0 : c.F 1) one_pos)
  obtain ⟨t, ht, hxt, hts⟩ := mem_nhdsWithin.1 hball
  obtain ⟨S, hS, T, hT, hST⟩ := mem_nhds_prod_iff.1 (ht.mem_nhds hxt)
  obtain ⟨δ, hδ, hδT⟩ := Metric.mem_nhds_iff.1 hT
  refine ⟨S, hS, 2 / δ, by positivity, fun u' hu' h => ?_⟩
  have hlin := isLinearMap_chartFibMap (c := c) hu'.2
  rcases eq_or_ne h 0 with rfl | hh
  · rw [hlin.map_zero, norm_zero, mul_zero]
  have hnh : 0 < ‖h‖ := norm_pos_iff.2 hh
  set a : ℝ := δ / 2 / ‖h‖ with ha
  have ha0 : 0 < a := by positivity
  have hmem : ((u', a • h) : c.φ.model.E 0 × c.F 1) ∈ t ∩ c.U ×ˢ univ := by
    refine ⟨hST ⟨hu'.1, hδT ?_⟩, hu'.2, mem_univ _⟩
    rw [Metric.mem_ball, dist_zero_right, norm_smul, Real.norm_of_nonneg ha0.le, ha,
      div_mul_cancel₀ _ hnh.ne']
    linarith
  have h1 : ‖chartFibMap c u' (a • h)‖ < 1 := by
    have := hts hmem
    rw [mem_preimage, Metric.mem_ball, dist_zero_right] at this
    exact this
  rw [hlin.map_smul, norm_smul, Real.norm_of_nonneg ha0.le] at h1
  have h2 : ‖chartFibMap c u' h‖ < 1 / a := by
    rw [lt_div_iff₀ ha0]; linarith
  have h3 : 1 / a = 2 / δ * ‖h‖ := by
    rw [ha]; field_simp
  linarith

omit [T2Space Y] [ParacompactSpace Y] in
/-- `A(u)h` read on level `0`: `ι(A(u)h) = (R(u, ιh))₂`. -/
lemma toBase_chartFibMap {u : c.φ.model.E 0} (hu : u ∈ c.U) (h : c.F 1) :
    c.F.toBase 1 (chartFibMap c u h) = (c.R (u, c.F.toBase 1 h)).2 :=
  c.isRetraction.toBase_shiftFiber_snd (p := ((u, h) : (c.φ.model.E.prod c.F.shift) 0)) hu

omit [T2Space Y] [ParacompactSpace Y] in
/-- **`A(u_k)h_k ⇀ A(u)h`** for `u_k → u` in `U` and `h_k ⇀ h` in a reflexive `F₁`: the sequence
is bounded (`exists_norm_chartFibMap_le`) and converges on level `0` (`R` is continuous on
`U ⊕ F₀`, and the compact inclusion `F₁ → F₀` maps `h_k ⇀ h` to `h_k → h`). -/
theorem weakTendsto_chartFibMap (hF : IsReflexive (c.F 1)) {u : ℕ → c.φ.model.E 0}
    {u₀ : c.φ.model.E 0} (hu₀ : u₀ ∈ c.U) (hu : ∀ᶠ k in atTop, u k ∈ c.U)
    (hlim : Tendsto u atTop (𝓝 u₀)) {h : ℕ → c.F 1} {h₀ : c.F 1} (hh : WeakTendsto h h₀) :
    WeakTendsto (fun k => chartFibMap c (u k) (h k)) (chartFibMap c u₀ h₀) := by
  obtain ⟨S, hS, C, hC, hSC⟩ := exists_norm_chartFibMap_le (c := c) hu₀
  obtain ⟨D, hD0, hD⟩ := hh.exists_bound
  have hbd : ∀ᶠ k in atTop, ‖chartFibMap c (u k) (h k)‖ ≤ C * D :=
    ((hlim.eventually hS).and hu).mono fun k hk =>
      (hSC (u k) ⟨hk.1, hk.2⟩ (h k)).trans (mul_le_mul_of_nonneg_left (hD k) hC.le)
  refine weakTendsto_of_bounded_of_tendsto hF (c.F.toBase_injective 1) hbd ?_
  -- level `0`
  set R := c.isRetraction.toScRetraction c.relOpen with hRdef
  have hRc : ContinuousWithinAt R R.U (u₀, c.F.toBase 1 h₀) :=
    R.isSc1.isSc0.continuousOn_base _ ⟨hu₀, mem_univ _⟩
  have hh0 : Tendsto (fun k => c.F.toBase 1 (h k)) atTop (𝓝 (c.F.toBase 1 h₀)) :=
    hh.tendsto_of_isCompactOperator (isCompactOperator_toBase_one c.F)
  have hp : Tendsto (fun k => ((u k, c.F.toBase 1 (h k)) : c.φ.model.E 0 × c.F 0)) atTop
      (𝓝[R.U] (u₀, c.F.toBase 1 h₀)) :=
    tendsto_nhdsWithin_iff.2 ⟨hlim.prodMk_nhds hh0, hu.mono fun k hk => ⟨hk, mem_univ _⟩⟩
  have h1 := (continuous_snd.tendsto _).comp (hRc.tendsto.comp hp)
  rw [toBase_chartFibMap hu₀]
  exact h1.congr' (hu.mono fun k hk => (toBase_chartFibMap hk (h k)).symm)

end FibMap

/-! ### Lower semicontinuity of the local extension -/

section Lsc

variable {c : StrongBundleChart PX P} (hc : B.IsChart c) (y₀ : B.One)

/-- **The local norm `N'` of the proof of Theorem 12.2.7 is lower semicontinuous along mixed
convergent sequences** (the "inspection" of the proof of Theorem 12.2.13, p. 578), at every point
over `V`, if the chart has reflexive `F₁`, `ρ` is continuous on `V` with values in `A` and in the
chart domain, and `N` is lower semicontinuous along mixed convergent sequences over `A`. -/
theorem mixedLscAt_retractNorm (hF : IsReflexive (c.F 1)) {A V : Set X} (hV : IsOpen V)
    (hVc : V ⊆ c.φ.source) {ρ : X → X} (hρ : ContinuousOn ρ V) (hρA : MapsTo ρ V A)
    (hρc : MapsTo ρ V c.φ.source) {N : B.One → ℝ}
    (hNl : ∀ (w : ℕ → B.One) (y : B.One), (∀ k, P (B.oneVal (w k)) ∈ A) →
      P (B.oneVal y) ∈ A → B.MixedTendsto w y →
        (N y : EReal) ≤ liminf (fun k => (N (w k) : EReal)) atTop)
    {y : B.One} (hy : P (B.oneVal y) ∈ V) : B.MixedLscAt (retractNorm hc y₀ ρ N) y := by
  classical
  intro w hm ε hε
  set Φ := oneChartOf hc y₀ with hΦ
  set uf : B.One → c.φ.model.E 0 := fun v => c.φ (ρ (P (B.oneVal v))) with huf
  set af : B.One → c.F 1 := fun v => chartFibMap c (uf v) (Φ v).2 with haf
  set T : B.One → B.One := fun v => Φ.symm (uf v, af v) with hT
  have hMT : ∀ v, retractNorm hc y₀ ρ N v = N (T v) + ‖(Φ v).2 - af v‖ := fun _ => rfl
  have huO : ∀ v : B.One, P (B.oneVal v) ∈ V → uf v ∈ c.φ.model.O := fun v hv =>
    c.φ.mapsTo_model _ (hρc hv)
  have hzK : ∀ v : B.One, P (B.oneVal v) ∈ V → (uf v, af v) ∈ strongShiftOne c.K := fun v hv =>
    mem_K_chartFibMap (huO v hv) _
  have hPT : ∀ v : B.One, P (B.oneVal v) ∈ V → P (B.oneVal (T v)) = ρ (P (B.oneVal v)) :=
    fun v hv => proj_oneChartOf_symm hc y₀ (hρc hv) (hzK v hv)
  have hΦT : ∀ v : B.One, P (B.oneVal v) ∈ V → c.liftOneSnd (B.oneVal (T v)) = af v :=
    fun v hv => by
      change (Φ (Φ.symm (uf v, af v))).2 = af v
      rw [Φ.apply_symm_apply (hzK v hv)]
  have hev : ∀ᶠ k in atTop, P (B.oneVal (w k)) ∈ V := hm.1.eventually (hV.mem_nhds hy)
  -- the fibre parts and the base points
  have hweak : WeakTendsto (fun k => (Φ (w k)).2) (Φ y).2 :=
    hm.weakTendsto_of_isChart hc (hVc hy) hF
  have hρt : Tendsto (fun k => ρ (P (B.oneVal (w k)))) atTop (𝓝 (ρ (P (B.oneVal y)))) :=
    (hρ.continuousAt (hV.mem_nhds hy)).tendsto.comp hm.1
  have hu : Tendsto (fun k => uf (w k)) atTop (𝓝 (uf y)) :=
    (c.φ.continuousOn_toFun.continuousAt (c.φ.isOpen_source.mem_nhds (hρc hy))).tendsto.comp hρt
  have hA : WeakTendsto (fun k => af (w k)) (af y) :=
    weakTendsto_chartFibMap hF (mem_U_of_mem_O (huO y hy))
      (hev.mono fun k hk => mem_U_of_mem_O (huO _ hk)) hu hweak
  -- the second term
  have h2 := (hweak.sub hA).eventually_norm_gt (half_pos hε)
  -- the first term, through a sequence over `A`
  set w' : ℕ → B.One := fun k => if P (B.oneVal (w k)) ∈ V then T (w k) else T y with hw'
  have hw'A : ∀ k, P (B.oneVal (w' k)) ∈ A := fun k => by
    by_cases hk : P (B.oneVal (w k)) ∈ V
    · simp only [hw', if_pos hk]; rw [hPT _ hk]; exact hρA hk
    · simp only [hw', if_neg hk]; rw [hPT _ hy]; exact hρA hy
  have hm' : B.MixedTendsto w' (T y) := by
    refine ⟨?_, c, hc, by rw [hPT _ hy]; exact hρc hy, hF, ?_⟩
    · rw [hPT _ hy]
      refine hρt.congr' (hev.mono fun k hk => ?_)
      simp only [hw', if_pos hk]; rw [hPT _ hk]
    · rw [hΦT _ hy]
      refine hA.congr_eventually (hev.mono fun k hk => ?_)
      simp only [hw', if_pos hk]; exact (hΦT _ hk).symm
  have hle := hNl w' (T y) hw'A (by rw [hPT _ hy]; exact hρA hy) hm'
  have h1lt : ((N (T y) - ε / 2 : ℝ) : EReal) < liminf (fun k => (N (w' k) : EReal)) atTop :=
    lt_of_lt_of_le (EReal.coe_lt_coe_iff.2 (sub_lt_self _ (half_pos hε))) hle
  have h1 : ∀ᶠ k in atTop, N (T y) - ε / 2 < N (w' k) :=
    (eventually_lt_of_lt_liminf h1lt).mono fun k hk => EReal.coe_lt_coe_iff.1 hk
  filter_upwards [h1, h2, hev] with k hk1 hk2 hkV
  have e1 : N (w' k) = N (T (w k)) := by simp only [hw', if_pos hkV]
  rw [hMT, hMT]
  rw [e1] at hk1
  linarith

end Lsc

/-- **The reflexive local extension near `∂X`** (proofs of Theorems 12.2.7 and 12.2.13, Part I
form): for a strong bundle with reflexive `(0, 1)`-fibres over a tame M-polyfold and `N` an
auxiliary norm over `∂X` which is lower semicontinuous along mixed convergent sequences over `∂X`,
every boundary point has an open neighbourhood `V` and a local auxiliary norm on `V`, lower
semicontinuous along mixed convergent sequences at every point over `V`, equal to `N` over
`V ∩ ∂X`.  (Wave 2's construction `retractNorm`, in a strong bundle chart with reflexive `F₁`.) -/
theorem exists_reflexiveLocalExtension_of_isTame (hP : PX.IsTame) (hB : B.HasReflexiveFibers)
    {N : B.One → ℝ} (hNc : ContinuousOn N {w | P (B.oneVal w) ∈ PX.boundary})
    (hNs : ∀ y ∈ PX.boundary, B.IsFiberSeminorm N y)
    (hN2 : ∀ (w : ℕ → B.One) (y : X), y ∈ PX.boundary → (∀ k, P (B.oneVal (w k)) ∈ PX.boundary) →
      Tendsto (fun k => P (B.oneVal (w k))) atTop (𝓝 y) →
        Tendsto (fun k => N (w k)) atTop (𝓝 0) → Tendsto w atTop (𝓝 (B.zeroOne y)))
    (hNl : ∀ (w : ℕ → B.One) (y : B.One), (∀ k, P (B.oneVal (w k)) ∈ PX.boundary) →
      P (B.oneVal y) ∈ PX.boundary → B.MixedTendsto w y →
        (N y : EReal) ≤ liminf (fun k => (N (w k) : EReal)) atTop)
    {x₀ : X} (hx₀ : x₀ ∈ PX.boundary) :
    ∃ V : Set X, IsOpen V ∧ x₀ ∈ V ∧ ∃ M : B.One → ℝ, B.IsLocalAuxNorm V M ∧
      (∀ y : B.One, P (B.oneVal y) ∈ V → B.MixedLscAt M y) ∧
      ∀ w : B.One, P (B.oneVal w) ∈ V ∩ PX.boundary → M w = N w := by
  obtain ⟨V₁, ρ, hV₁, hx₀V₁, hρ, hρA, hfix⟩ := PX.exists_retraction_boundary hP hx₀
  obtain ⟨c, hc, hx₀c, hF⟩ := hB x₀
  set V := (V₁ ∩ c.φ.source) ∩ ρ ⁻¹' c.φ.source
  have hVo : IsOpen V :=
    (hρ.mono inter_subset_left).isOpen_inter_preimage (hV₁.inter c.φ.isOpen_source)
      c.φ.isOpen_source
  have hρx₀ : ρ x₀ = x₀ := hfix x₀ ⟨hx₀V₁, hx₀⟩
  have hx₀V : x₀ ∈ V := ⟨⟨hx₀V₁, hx₀c⟩, by rw [mem_preimage, hρx₀]; exact hx₀c⟩
  have hVc : V ⊆ c.φ.source := fun y hy => hy.1.2
  have hρV : ContinuousOn ρ V := hρ.mono fun y hy => hy.1.1
  have hρAV : MapsTo ρ V PX.boundary := fun y hy => hρA hy.1.1
  have hρcV : MapsTo ρ V c.φ.source := fun y hy => hy.2
  refine ⟨V, hVo, hx₀V, retractNorm hc (B.zeroOne x₀) ρ N, ?_, fun y hy => ?_, fun w hw => ?_⟩
  · exact isLocalAuxNorm_retractNorm hc _ hVo hVc hρV hρAV hρcV hNc hNs hN2
  · exact mixedLscAt_retractNorm hc _ hF hVo hVc hρV hρAV hρcV hNl hy
  · exact retractNorm_eq hc _ hVc (fun y hy => hfix y ⟨hy.1.1.1, hy.2⟩) N hw

end StrongBundle

/-! ### The local step and Theorem 12.2.13 -/

section Thm12213

variable {Obj Mor : Type u} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] {X : EpGroupoid Obj Mor}
  {W : Type u} [TopologicalSpace W] [T2Space W] [ParacompactSpace W] {P : W → Obj}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle X.PObj P}

namespace EpStrongBundle

variable {E : EpStrongBundle X B}

/-- **The local step of the proof of Theorem 12.2.13** (p. 578) for tame `X`: with reflexive
`1`-fibres, a reflexive auxiliary norm `N` for `W_{0,1}|∂X` has reflexive local extensions near
every boundary point (the hypothesis `hloc` of `theorem_12_2_13_hyp`). -/
theorem hasReflexiveLocalExtensions_of_isTame (hX : X.IsTame) (hB : E.HasReflexiveFibers)
    {N : B.One → ℝ} (hN : E.IsReflexiveAuxNormOn X.PObj.boundary N) :
    HasReflexiveLocalExtensions X B N := fun _ hx =>
  StrongBundle.exists_reflexiveLocalExtension_of_isTame hX hB hN.continuousOn
    (fun y hy => (hN.fiber y hy).isFiberSeminorm) hN.tendsto_zeroOne hN.le_liminf hx

/-- **Theorem 12.2.13 (extension of reflexive auxiliary norms), p. 578**: for a strong bundle
`(P : W → X, μ)` with reflexive `1`-fibres over a tame ep-groupoid with paracompact orbit space
`|X|`, every reflexive auxiliary norm `N` for `W_{0,1}|∂X` (Definition 12.2.10 over `∂X`) extends
to a reflexive auxiliary norm `Ñ` of `W_{0,1}` (Definition 12.2.10) which coincides with `N` over
`∂X`.  The paracompactness of `|X|` is not in the printed statement; the proof uses it through the
partition of unity of Theorem 12.2.11. -/
theorem theorem_12_2_13 (hX : X.IsTame) (h : X.HasParacompactOrbitSpace)
    (hB : E.HasReflexiveFibers) {N : B.One → ℝ} (hN : E.IsReflexiveAuxNormOn X.PObj.boundary N) :
    ∃ Ñ : B.One → ℝ, E.IsReflexiveAuxNorm Ñ ∧
      ∀ w : B.One, P (B.oneVal w) ∈ X.PObj.boundary → Ñ w = N w :=
  theorem_12_2_13_hyp h hB hN (hasReflexiveLocalExtensions_of_isTame hX hB hN)

end EpStrongBundle

end Thm12213

namespace TrivialBundle

/-- **The hypotheses of `theorem_12_2_13` are satisfiable together**: the trivial bundle
`ℝⁿ × ℝᵏ → ℝⁿ` over the trivial ep-groupoid of `ℝⁿ` is tame, has paracompact `|X|` and reflexive
`1`-fibres, and carries a reflexive auxiliary norm over `∂X`. -/
theorem theorem_12_2_13_witness (n k : ℕ) :
    (EpGroupoid.trivial (rnPolyfold n)).IsTame ∧
      (EpGroupoid.trivial (rnPolyfold n)).HasParacompactOrbitSpace ∧
      (epBundle n k).HasReflexiveFibers ∧
      ∃ N, (epBundle n k).IsReflexiveAuxNormOn (rnPolyfold n).boundary N := by
  obtain ⟨hB, h, -, N, hN, -⟩ := epBundle_reflexive_witness n k
  exact ⟨EpGroupoid.isTame_trivial_rn n, h, hB, N, hN⟩

end TrivialBundle

end Polyfold
