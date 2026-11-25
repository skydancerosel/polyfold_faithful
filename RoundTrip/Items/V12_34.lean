import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V12_34

/-! Round trip for V12_34 (2021 Theorem 12.2.13, p. 578: extension of reflexive auxiliary norms
from the boundary).

The item lists `theorem_12_2_13` (with the added hypothesis that `|X|` is paracompact) and the
pieces of its proof: `theorem_12_2_13_hyp` (no tameness; the reflexive local extension step as
the hypothesis `HasReflexiveLocalExtensions`), `theorem_12_2_13_hyp_witness`,
`hasReflexiveLocalExtensions_of_isTame`, the Part I local step
`exists_reflexiveLocalExtension_of_isTame`, `mixedLscAt_retractNorm`, `weakTendsto_chartFibMap`,
`exists_norm_chartFibMap_le`, `toBase_chartFibMap`, `WeakTendsto.sub`, the trivial-bundle
witnesses `TrivialBundle.theorem_12_2_13_witness`, `epBundle_reflexive_witness`, and
`HasReflexiveLocalExtensions.hasLocalExtensions`, `hasReflexiveLocalExtensions_of_isReflexiveAuxNorm`.
`A` is the conjunction of their types at universe `0` (`.{0, 0}` for the Part I lemmas; the
witnesses have no universe parameter).

* `A_to_B`: `theorem_12_2_13` is `B` (same hypotheses: `B`'s blind reading also adds `|X|`
  paracompact; hypotheses reordered; `B`'s pullback instance unused).
* `B_to_A`: `theorem_12_2_13` from `B` (pullback instance from
  `StrongBundle.paracompactSpace_pullback`).  The other conjuncts do not follow from `B` (no
  tameness in `_hyp`, no paracompactness in the local step, concrete witnesses); they are
  re-proved outright by copying the project's proofs, which use only non-item lemmas
  (`retractNorm` machinery and `exists_retraction_boundary` from Theorem 12.2.7,
  `mixedLscAt_avgNorm`/`transNorm`/`isReflexiveAuxNorm_glueNorm` and `theorem_12_2_11_exists`
  from Theorem 12.2.11, `weakTendsto_of_bounded_of_tendsto`, ...).
-/

namespace RoundTrip.V12_34
open Polyfold
open Set Filter Topology Function TopologicalSpace

universe u v

/-- The project's statement (universes at `0`). -/
def A : Prop :=
  (type_of% @Polyfold.EpStrongBundle.theorem_12_2_13.{0}) ∧
  (type_of% @Polyfold.EpStrongBundle.hasReflexiveLocalExtensions_of_isTame.{0}) ∧
  (type_of% @Polyfold.StrongBundle.exists_reflexiveLocalExtension_of_isTame.{0, 0}) ∧
  (type_of% @Polyfold.StrongBundle.mixedLscAt_retractNorm.{0, 0}) ∧
  (type_of% @Polyfold.StrongBundle.weakTendsto_chartFibMap.{0, 0}) ∧
  (type_of% @Polyfold.StrongBundle.exists_norm_chartFibMap_le.{0, 0}) ∧
  (type_of% @Polyfold.StrongBundle.toBase_chartFibMap.{0, 0}) ∧
  (type_of% @Polyfold.WeakTendsto.sub.{0}) ∧
  (type_of% @Polyfold.TrivialBundle.theorem_12_2_13_witness) ∧
  (type_of% @Polyfold.EpStrongBundle.theorem_12_2_13_hyp.{0}) ∧
  (type_of% @Polyfold.EpStrongBundle.HasReflexiveLocalExtensions.hasLocalExtensions.{0}) ∧
  (type_of% @Polyfold.EpStrongBundle.hasReflexiveLocalExtensions_of_isReflexiveAuxNorm.{0}) ∧
  (type_of% @Polyfold.EpStrongBundle.theorem_12_2_13_hyp_witness.{0}) ∧
  (type_of% @Polyfold.TrivialBundle.epBundle_reflexive_witness)

theorem A_holds : A :=
  ⟨@Polyfold.EpStrongBundle.theorem_12_2_13.{0}, @Polyfold.EpStrongBundle.hasReflexiveLocalExtensions_of_isTame.{0}, @Polyfold.StrongBundle.exists_reflexiveLocalExtension_of_isTame.{0, 0}, @Polyfold.StrongBundle.mixedLscAt_retractNorm.{0, 0}, @Polyfold.StrongBundle.weakTendsto_chartFibMap.{0, 0}, @Polyfold.StrongBundle.exists_norm_chartFibMap_le.{0, 0}, @Polyfold.StrongBundle.toBase_chartFibMap.{0, 0}, @Polyfold.WeakTendsto.sub.{0}, @Polyfold.TrivialBundle.theorem_12_2_13_witness, @Polyfold.EpStrongBundle.theorem_12_2_13_hyp.{0}, @Polyfold.EpStrongBundle.HasReflexiveLocalExtensions.hasLocalExtensions.{0}, @Polyfold.EpStrongBundle.hasReflexiveLocalExtensions_of_isReflexiveAuxNorm.{0}, @Polyfold.EpStrongBundle.theorem_12_2_13_hyp_witness.{0}, @Polyfold.TrivialBundle.epBundle_reflexive_witness⟩

theorem A_to_B : A → B := by
  rintro ⟨h, -⟩
  intro Obj Mor _ _ _ _ _ _ X W _ _ _ P _ _ B _ E hR hT hX N hN
  exact h hT hX hR hN

/-! ### The proof's pieces, re-proved outright (the project's proofs, copied) -/

section Weak

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem weakTendsto_sub' {a b : ℕ → F} {a₀ b₀ : F} (ha : WeakTendsto a a₀) (hb : WeakTendsto b b₀) :
    WeakTendsto (fun k => a k - b k) (a₀ - b₀) := fun g => by
  simp only [map_sub]
  exact (ha g).sub (hb g)

end Weak

section PartI
open Polyfold.StrongBundle Polyfold.MPolyfold

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
theorem exists_norm_chartFibMap_le' {u : c.φ.model.E 0} (hu : u ∈ c.U) :
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
theorem toBase_chartFibMap' {u : c.φ.model.E 0} (hu : u ∈ c.U) (h : c.F 1) :
    c.F.toBase 1 (chartFibMap c u h) = (c.R (u, c.F.toBase 1 h)).2 :=
  c.isRetraction.toBase_shiftFiber_snd (p := ((u, h) : (c.φ.model.E.prod c.F.shift) 0)) hu

omit [T2Space Y] [ParacompactSpace Y] in
/-- **`A(u_k)h_k ⇀ A(u)h`** for `u_k → u` in `U` and `h_k ⇀ h` in a reflexive `F₁`: the sequence
is bounded (`exists_norm_chartFibMap_le`) and converges on level `0` (`R` is continuous on
`U ⊕ F₀`, and the compact inclusion `F₁ → F₀` maps `h_k ⇀ h` to `h_k → h`). -/
theorem weakTendsto_chartFibMap' (hF : IsReflexive (c.F 1)) {u : ℕ → c.φ.model.E 0}
    {u₀ : c.φ.model.E 0} (hu₀ : u₀ ∈ c.U) (hu : ∀ᶠ k in atTop, u k ∈ c.U)
    (hlim : Tendsto u atTop (𝓝 u₀)) {h : ℕ → c.F 1} {h₀ : c.F 1} (hh : WeakTendsto h h₀) :
    WeakTendsto (fun k => chartFibMap c (u k) (h k)) (chartFibMap c u₀ h₀) := by
  obtain ⟨S, hS, C, hC, hSC⟩ := exists_norm_chartFibMap_le' (c := c) hu₀
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
  rw [toBase_chartFibMap' hu₀]
  exact h1.congr' (hu.mono fun k hk => (toBase_chartFibMap' hk (h k)).symm)

end FibMap

/-! ### Lower semicontinuity of the local extension -/

section Lsc

variable {c : StrongBundleChart PX P} (hc : B.IsChart c) (y₀ : B.One)

/-- **The local norm `N'` of the proof of Theorem 12.2.7 is lower semicontinuous along mixed
convergent sequences** (the "inspection" of the proof of Theorem 12.2.13, p. 578), at every point
over `V`, if the chart has reflexive `F₁`, `ρ` is continuous on `V` with values in `A` and in the
chart domain, and `N` is lower semicontinuous along mixed convergent sequences over `A`. -/
theorem mixedLscAt_retractNorm' (hF : IsReflexive (c.F 1)) {A V : Set X} (hV : IsOpen V)
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
    weakTendsto_chartFibMap' hF (mem_U_of_mem_O (huO y hy))
      (hev.mono fun k hk => mem_U_of_mem_O (huO _ hk)) hu hweak
  -- the second term
  have h2 := (weakTendsto_sub' hweak hA).eventually_norm_gt (half_pos hε)
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
`V ∩ ∂X`.  (The construction `retractNorm`, in a strong bundle chart with reflexive `F₁`.) -/
theorem exists_reflexiveLocalExtension_of_isTame' (hP : PX.IsTame) (hB : B.HasReflexiveFibers)
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
  · exact mixedLscAt_retractNorm' hc _ hF hVo hVc hρV hρAV hρcV hNl hy
  · exact retractNorm_eq hc _ hVc (fun y hy => hfix y ⟨hy.1.1.1, hy.2⟩) N hw

end PartI

section Ep
open Polyfold.EpStrongBundle

variable {Obj Mor : Type u} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] {X : EpGroupoid Obj Mor}
  {W : Type u} [TopologicalSpace W] [T2Space W] [ParacompactSpace W] {P : W → Obj}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle X.PObj P}
  {E : EpStrongBundle X B}

theorem hasLocalExtensions' {N : B.One → ℝ}
    (h : HasReflexiveLocalExtensions X B N) : HasLocalExtensions X B N := fun x hx => by
  obtain ⟨V, hVo, hxV, M, hM, -, hMN⟩ := h x hx
  exact ⟨V, hVo, hxV, M, hM, hMN⟩

theorem theorem_12_2_13_hyp' (h : X.HasParacompactOrbitSpace) (hB : E.HasReflexiveFibers)
    {N : B.One → ℝ} (hN : E.IsReflexiveAuxNormOn X.PObj.boundary N)
    (hloc : HasReflexiveLocalExtensions X B N) :
    ∃ Ñ : B.One → ℝ, E.IsReflexiveAuxNorm Ñ ∧
      ∀ w : B.One, P (B.oneVal w) ∈ X.PObj.boundary → Ñ w = N w := by
  classical
  have := B.paracompactSpace_pullback X.PMor X.src
  have : ParacompactSpace X.OrbitSpace := h
  have := X.theorem_7_3_1_metrizable h
  obtain ⟨N₀, hN₀⟩ := proposition_5_1_8_exists hB
  have hdata : ∀ x : Obj, ∃ (R : X.NaturalRep x) (M : B.One → ℝ), B.IsLocalAuxNorm R.U M ∧
      (∀ y : B.One, P (B.oneVal y) ∈ R.U → B.MixedLscAt M y) ∧
      (x ∈ X.PObj.boundary → ∀ w : B.One, P (B.oneVal w) ∈ R.U ∩ X.PObj.boundary → M w = N w) ∧
      (x ∉ X.PObj.boundary → R.U ⊆ X.PObj.boundaryᶜ) := by
    intro x
    by_cases hx : x ∈ X.PObj.boundary
    · obtain ⟨V, hVo, hxV, M, hM, hMl, hMN⟩ := hloc x hx
      obtain ⟨R, hRV⟩ := X.theorem_7_1_13 x hVo hxV
      exact ⟨R, M, hM.mono hRV, fun y hy => hMl y (hRV hy),
        fun _ w hw => hMN w ⟨hRV hw.1, hw.2⟩, fun h' => absurd hx h'⟩
    · obtain ⟨R, hRV⟩ := X.theorem_7_1_13 x X.isOpen_compl_boundary hx
      exact ⟨R, N₀, hN₀.toIsAuxNorm.isLocalAuxNorm _, fun y _ => hN₀.mixedLscAt y,
        fun h' => absurd h' hx, fun _ => hRV⟩
  choose R M hM hMl hMN hRint using hdata
  have hM' : ∀ x, B.IsLocalAuxNorm (R x).U (E.avgNorm (R x) (M x)) := fun x =>
    E.isLocalAuxNorm_avgNorm (R x) (hM x)
  have hinv : ∀ x g w, P (B.oneVal w) ∈ (R x).U →
      E.avgNorm (R x) (M x) (E.actOne ((R x).Γ g) w) = E.avgNorm (R x) (M x) w :=
    fun x g w hw => E.avgNorm_actOne (R x) (M x) g hw
  have hlscM : ∀ x (y : B.One), P (B.oneVal y) ∈ (R x).U →
      B.MixedLscAt (E.avgNorm (R x) (M x)) y := fun x _ hy =>
    E.mixedLscAt_avgNorm hB (R x) (hMl x) hy
  obtain ⟨β, hβ⟩ := PartitionOfUnity.exists_isSubordinate isClosed_univ
    (fun x => X.π '' X.satSet (R x).U)
    (fun x => by rw [EpGroupoid.image_π_satSet]; exact X.proposition_7_1_8 _ (R x).isOpen_U)
    fun z _ => by
      obtain ⟨y, rfl⟩ := X.surjective_π z
      exact mem_iUnion.2 ⟨y, y, EpGroupoid.subset_satSet _ (R y).mem_U, rfl⟩
  set T : Obj → B.One → ℝ := fun x => E.transNorm (R x) (E.avgNorm (R x) (M x)) with hT
  refine ⟨glueNorm β T, isReflexiveAuxNorm_glueNorm (E := E) (U := fun x => X.satSet (R x).U)
    (fun x => EpGroupoid.isOpen_satSet (R x).isOpen_U)
    (fun x => EpGroupoid.isSaturated_satSet _) hβ
    (fun x => isLocalAuxNorm_transNorm (hM' x) (hinv x))
    (fun x h k ψ hk _ hh => transNorm_μ (hinv x) h k ψ hk hh)
    (fun x _ hy => mixedLscAt_transNorm hB (hinv x) (hlscM x) hy), fun w hw => ?_⟩
  -- over `∂X` every nonzero term of the glued norm is `β_x · N` (as in Theorem 12.2.7)
  have key : ∀ x, β x (X.π (P (B.oneVal w))) * T x w = β x (X.π (P (B.oneVal w))) * N w := by
    intro x
    by_cases hβ0 : β x (X.π (P (B.oneVal w))) = 0
    · rw [hβ0, zero_mul, zero_mul]
    have hyU : P (B.oneVal w) ∈ X.satSet (R x).U :=
      EpGroupoid.mem_of_π_mem_image (EpGroupoid.isSaturated_satSet _)
        (hβ x (subset_tsupport _ hβ0))
    have hxb : x ∈ X.PObj.boundary := by
      by_contra hx
      obtain ⟨φ, hφs, hφt⟩ := hyU
      exact hRint x hx hφt ((X.tgt_mem_boundary_iff φ).2 (hφs ▸ hw))
    congr 1
    change E.transNorm (R x) (E.avgNorm (R x) (M x)) w = N w
    rw [transNorm, if_pos hyU]
    have hφs := X.src_selMor (R x).U (P (B.oneVal w))
    set v := E.actOne (X.selMor (R x).U) w with hv
    have hPv : P (B.oneVal v) = X.tgt (X.selMor (R x).U (P (B.oneVal w))) := E.P_actOne hφs
    have hvU : P (B.oneVal v) ∈ (R x).U := hPv ▸ X.tgt_selMor_mem hyU
    have hvb : P (B.oneVal v) ∈ X.PObj.boundary :=
      hPv ▸ (X.tgt_mem_boundary_iff _).2 (hφs.symm ▸ hw)
    have hNv : N v = N w :=
      hN.toIsAuxNormOn.map_μ v w _ hφs.symm hw (E.oneVal_actOne_of_eq hφs.symm)
    have hterm : ∀ g, M x (E.actOne ((R x).Γ g) v) = N w := fun g => by
      have hs := (R x).src_Γ g _ hvU
      have hgb : P (B.oneVal (E.actOne ((R x).Γ g) v)) ∈ X.PObj.boundary := by
        rw [E.P_actOne hs]; exact (X.tgt_mem_boundary_iff _).2 (hs.symm ▸ hvb)
      rw [hMN x hxb _ ⟨E.actOne_Γ_mem (R x) g hvU, hgb⟩,
        hN.toIsAuxNormOn.map_μ _ v _ hs.symm hvb (E.oneVal_actOne_of_eq hs.symm), hNv]
    have := Fintype.ofFinite (X.Isotropy x)
    rw [avgNorm, finsum_congr hterm, finsum_eq_sum_of_fintype, Finset.sum_const,
      Finset.card_univ, nsmul_eq_mul, ← Nat.card_eq_fintype_card,
      inv_mul_cancel_left₀ (card_isotropy_pos X (x := x)).ne']
  rw [glueNorm, finsum_congr key, ← finsum_mul, β.sum_eq_one (mem_univ _), one_mul]

theorem hasReflexiveLocalExtensions_of_isReflexiveAuxNorm' {N : B.One → ℝ}
    (hN : E.IsReflexiveAuxNorm N) : HasReflexiveLocalExtensions X B N := fun _ _ =>
  ⟨univ, isOpen_univ, mem_univ _, N, hN.isAuxNorm.isLocalAuxNorm univ,
    fun y _ => hN.mixedLscAt y, fun _ _ => rfl⟩

theorem theorem_12_2_13_hyp_witness' (h : X.HasParacompactOrbitSpace)
    (hB : E.HasReflexiveFibers) :
    ∃ N : B.One → ℝ, E.IsReflexiveAuxNormOn X.PObj.boundary N ∧
      HasReflexiveLocalExtensions X B N := by
  obtain ⟨N, hN⟩ := E.theorem_12_2_11_exists h hB
  exact ⟨N, hN.isReflexiveAuxNormOn _, hasReflexiveLocalExtensions_of_isReflexiveAuxNorm' hN⟩

theorem hasReflexiveLocalExtensions_of_isTame' (hX : X.IsTame) (hB : E.HasReflexiveFibers)
    {N : B.One → ℝ} (hN : E.IsReflexiveAuxNormOn X.PObj.boundary N) :
    HasReflexiveLocalExtensions X B N := fun _ hx =>
  exists_reflexiveLocalExtension_of_isTame' hX hB hN.continuousOn
    (fun y hy => (hN.fiber y hy).isFiberSeminorm) hN.tendsto_zeroOne hN.le_liminf hx

end Ep

section Triv
open Polyfold.TrivialBundle

theorem epBundle_reflexive_witness' (n k : ℕ) :
    (epBundle n k).HasReflexiveFibers ∧
      (EpGroupoid.trivial (rnPolyfold n)).HasParacompactOrbitSpace ∧
      (∃ N, (epBundle n k).IsReflexiveAuxNorm N) ∧
      ∃ N, (epBundle n k).IsReflexiveAuxNormOn (rnPolyfold n).boundary N ∧
        EpStrongBundle.HasReflexiveLocalExtensions (EpGroupoid.trivial (rnPolyfold n))
          (bundle n k) N :=
  ⟨hasReflexiveFibers_bundle, (EpGroupoid.admitsBumpFunctionsPointwise_trivial_rn n).2,
    (epBundle n k).theorem_12_2_11_exists (EpGroupoid.admitsBumpFunctionsPointwise_trivial_rn n).2
      hasReflexiveFibers_bundle,
    theorem_12_2_13_hyp_witness' (E := epBundle n k)
      (EpGroupoid.admitsBumpFunctionsPointwise_trivial_rn n).2 hasReflexiveFibers_bundle⟩

theorem theorem_12_2_13_witness' (n k : ℕ) :
    (EpGroupoid.trivial (rnPolyfold n)).IsTame ∧
      (EpGroupoid.trivial (rnPolyfold n)).HasParacompactOrbitSpace ∧
      (epBundle n k).HasReflexiveFibers ∧
      ∃ N, (epBundle n k).IsReflexiveAuxNormOn (rnPolyfold n).boundary N := by
  obtain ⟨hB, h, -, N, hN, -⟩ := epBundle_reflexive_witness' n k
  exact ⟨EpGroupoid.isTame_trivial_rn n, h, hB, N, hN⟩

end Triv

theorem B_to_A : B → A := by
  intro hB
  refine ⟨?_, @hasReflexiveLocalExtensions_of_isTame'.{0},
    @exists_reflexiveLocalExtension_of_isTame'.{0, 0}, @mixedLscAt_retractNorm'.{0, 0},
    @weakTendsto_chartFibMap'.{0, 0}, @exists_norm_chartFibMap_le'.{0, 0},
    @toBase_chartFibMap'.{0, 0}, @weakTendsto_sub'.{0}, theorem_12_2_13_witness',
    @theorem_12_2_13_hyp'.{0}, @hasLocalExtensions'.{0},
    @hasReflexiveLocalExtensions_of_isReflexiveAuxNorm'.{0}, @theorem_12_2_13_hyp_witness'.{0},
    epBundle_reflexive_witness'⟩
  intro Obj Mor _ _ _ _ _ _ X W _ _ _ P _ _ B E hT hX hR N hN
  have := B.paracompactSpace_pullback X.PMor X.src
  exact hB Obj Mor X W P B E hR hT hX N hN

#rt_check RoundTrip.V12_34.A_to_B [Polyfold.EpStrongBundle.theorem_12_2_13,
  Polyfold.EpStrongBundle.hasReflexiveLocalExtensions_of_isTame,
  Polyfold.StrongBundle.exists_reflexiveLocalExtension_of_isTame,
  Polyfold.StrongBundle.mixedLscAt_retractNorm,
  Polyfold.StrongBundle.weakTendsto_chartFibMap,
  Polyfold.StrongBundle.exists_norm_chartFibMap_le,
  Polyfold.StrongBundle.toBase_chartFibMap,
  Polyfold.WeakTendsto.sub,
  Polyfold.TrivialBundle.theorem_12_2_13_witness,
  Polyfold.EpStrongBundle.theorem_12_2_13_hyp,
  Polyfold.EpStrongBundle.HasReflexiveLocalExtensions.hasLocalExtensions,
  Polyfold.EpStrongBundle.hasReflexiveLocalExtensions_of_isReflexiveAuxNorm,
  Polyfold.EpStrongBundle.theorem_12_2_13_hyp_witness,
  Polyfold.TrivialBundle.epBundle_reflexive_witness]
#rt_check RoundTrip.V12_34.B_to_A [Polyfold.EpStrongBundle.theorem_12_2_13,
  Polyfold.EpStrongBundle.hasReflexiveLocalExtensions_of_isTame,
  Polyfold.StrongBundle.exists_reflexiveLocalExtension_of_isTame,
  Polyfold.StrongBundle.mixedLscAt_retractNorm,
  Polyfold.StrongBundle.weakTendsto_chartFibMap,
  Polyfold.StrongBundle.exists_norm_chartFibMap_le,
  Polyfold.StrongBundle.toBase_chartFibMap,
  Polyfold.WeakTendsto.sub,
  Polyfold.TrivialBundle.theorem_12_2_13_witness,
  Polyfold.EpStrongBundle.theorem_12_2_13_hyp,
  Polyfold.EpStrongBundle.HasReflexiveLocalExtensions.hasLocalExtensions,
  Polyfold.EpStrongBundle.hasReflexiveLocalExtensions_of_isReflexiveAuxNorm,
  Polyfold.EpStrongBundle.theorem_12_2_13_hyp_witness,
  Polyfold.TrivialBundle.epBundle_reflexive_witness]
#rt_overlap RoundTrip.V12_34.B_to_A [Polyfold.EpStrongBundle.theorem_12_2_13,
  Polyfold.EpStrongBundle.hasReflexiveLocalExtensions_of_isTame,
  Polyfold.StrongBundle.exists_reflexiveLocalExtension_of_isTame,
  Polyfold.StrongBundle.mixedLscAt_retractNorm,
  Polyfold.StrongBundle.weakTendsto_chartFibMap,
  Polyfold.StrongBundle.exists_norm_chartFibMap_le,
  Polyfold.StrongBundle.toBase_chartFibMap,
  Polyfold.WeakTendsto.sub,
  Polyfold.TrivialBundle.theorem_12_2_13_witness,
  Polyfold.EpStrongBundle.theorem_12_2_13_hyp,
  Polyfold.EpStrongBundle.HasReflexiveLocalExtensions.hasLocalExtensions,
  Polyfold.EpStrongBundle.hasReflexiveLocalExtensions_of_isReflexiveAuxNorm,
  Polyfold.EpStrongBundle.theorem_12_2_13_hyp_witness,
  Polyfold.TrivialBundle.epBundle_reflexive_witness]

end RoundTrip.V12_34
