import Polyfold.Chapter12.P3N_AuxNormEp
import Polyfold.Chapter5.P3R_Reflexive2021

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part III, Chapter 12,
§12.2, pp. 576–578: **Definition 12.2.8, Remark 12.2.9, Definition 12.2.10, Theorem 12.2.11,
Remark 12.2.12** (reflexive auxiliary norms on ep-groupoids).

# Reflexive auxiliary norms for strong bundles over ep-groupoids

## The text, paraphrased

A strong bundle `(P : W → X, μ)` over an ep-groupoid has reflexive `(0, 1)`-fibres if some strong
bundle atlas of `W → X` has local models `K ⊆ C ◁ F` with `F₁` reflexive.  (Definition 12.2.8)
`w_k ∈ W_{0,1}` is mixed convergent to `w ∈ W_{0,1}` if `P(w_k) → P(w)` in `X₀` and in some strong
bundle chart with reflexive `F₁` the fibre parts converge weakly in `F₁`.  (Remark 12.2.9) This
does not depend on the chart (Lemma 5.1.5).  (Definition 12.2.10) A reflexive auxiliary norm is a
continuous `N : W_{0,1} → [0, ∞)` which is (0) a functor, (1) a complete norm on the fibres, with
(2) `P(w_k) → x`, `N(w_k) → 0` ⟹ `w_k → 0_x`, and (3) `N(w) ≤ liminf N(w_k)` for `w_k →ᵐ w`.
(Theorem 12.2.11) With reflexive fibres and paracompact `|X|` a reflexive auxiliary norm exists;
`(f ∘ P)·N` is one for functorial continuous `f > 0`; every auxiliary norm `N'` lies between two
reflexive ones, `N₁ ≤ N' ≤ N₂`.  (Remark 12.2.12) (1) is the second clause; (2) for two auxiliary
norms `N₁ ≤ (f ∘ P)·N₂` for some functorial continuous `f > 0`; (3) a cut-off `f·N` of a reflexive
auxiliary norm on a saturated open `U` (zero off `U`) is lower semicontinuous along mixed
convergent sequences.  (Proof of 12.2.11) The average over `G_x` of a chart norm on `U'(x)`,
transported to the saturation, glued with a partition of unity.

## What is formalized

* Part I tools (namespace `StrongBundle`): `mixedTendsto_of_bounded` (level-0 convergence plus a
  bound of an auxiliary norm gives mixed convergence), `MixedTendsto.exists_eventually_le` (the
  converse bound), `exists_le_mul_auxNorm` (a continuous fibre seminorm is locally dominated by an
  auxiliary norm), the pointwise lower semicontinuity `MixedLscAt` with its algebra.
* **Morphisms preserve mixed convergence**: `EpStrongBundle.mixedTendsto_actOne` (the lifted
  action `w ↦ μ(α(P w), w)` of an sc-smooth local section `α` of `s` maps mixed convergent
  sequences to mixed convergent sequences).  This is what makes the transport of the proof of
  Theorem 12.2.11 keep the lower semicontinuity; `remark_12_2_9` collects it with the chart
  independence.
* **Definition 12.2.8**: `EpStrongBundle.HasReflexiveFibers`, `EpStrongBundle.MixedTendsto`
  (the object bundle's `StrongBundle.MixedTendsto`), `definition_12_2_8`.
* **Definition 12.2.10**: `EpStrongBundle.IsReflexiveAuxNorm` (an auxiliary norm of Definition
  12.2.1 with the `liminf` clause).
* **Theorem 12.2.11**: `theorem_12_2_11_exists`, `theorem_12_2_11_mul`, `theorem_12_2_11_sandwich`,
  and `theorem_12_2_11` (all three clauses).
* **Remark 12.2.12**: `remark_12_2_12_1`, `remark_12_2_12_2`, `remark_12_2_12_3`.
* The gluing tools for later use: `mixedLscAt_avgNorm`, `mixedLscAt_transNorm`,
  `mixedLscAt_glueNorm`, `isReflexiveAuxNorm_glueNorm`.

## Readings

* The local norm on `U'(x)` is a Part I reflexive auxiliary norm (Proposition 5.1.8) in place of
  the chart norm `‖pr₂ ∘ Ψ(g ∗ h)‖_{F₁}`, as in the wave-1 proof of Theorem 12.2.2.
* The `liminf` of Definition 12.2.10 (3) is printed `k → 0`; presumably `k → ∞` (as in Part I).
* Remark 12.2.12 (3): the lower semicontinuity holds without the support condition
  `supp f ⊆ U` and without the functoriality of `f` (they are used for continuity and functoriality
  of the cut-off, not for (3)).
-/

open Set Filter Topology Function TopologicalSpace

noncomputable section

namespace Polyfold

universe u v

/-! ### Part I: mixed convergence from bounds, and pointwise lower semicontinuity -/

section PartI

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})]

namespace StrongBundle

variable {B : StrongBundle PX P}

/-- **Bounded plus level-0 convergent is mixed convergent** (the last step of the argument of
Remark 12.2.9): with reflexive `(0, 1)`-fibres, if `w_k → w` in `Y` (level 0) and `N(w_k) ≤ r`
eventually for an auxiliary norm `N`, then `w_k →ᵐ w`. -/
theorem mixedTendsto_of_bounded (hB : B.HasReflexiveFibers) {N : B.One → ℝ} (hN : B.IsAuxNorm N)
    {w : ℕ → B.One} {y : B.One}
    (hY : Tendsto (fun k => B.oneVal (w k)) atTop (𝓝 (B.oneVal y))) {r : ℝ}
    (hr : ∀ᶠ k in atTop, N (w k) ≤ r) : B.MixedTendsto w y := by
  obtain ⟨c, hc, hx, hF⟩ := hB (P (B.oneVal y))
  obtain ⟨V, hVo, hxV, -, a, A, ha, haA, hV⟩ := hN.exists_bounds hc hx
  have hP : Tendsto (fun k => P (B.oneVal (w k))) atTop (𝓝 (P (B.oneVal y))) :=
    (B.continuous.tendsto _).comp hY
  have hev : ∀ᶠ k in atTop, P (B.oneVal (w k)) ∈ V := hP.eventually (hVo.mem_nhds hxV)
  have hbd : ∀ᶠ k in atTop, ‖c.liftOneSnd (B.oneVal (w k))‖ ≤ A * r :=
    (hev.and hr).mono fun k hk =>
      (hV (w k) hk.1).2.trans (mul_le_mul_of_nonneg_left hk.2 (ha.trans haA).le)
  exact ⟨hP, c, hc, hx, hF, weakTendsto_liftOneSnd_of_tendsto hc hF hx hY hbd⟩

/-- **A mixed convergent sequence is bounded in every auxiliary norm** (weakly convergent sequences
are bounded, and `N` is comparable to the chart norm `|·|₁`). -/
theorem MixedTendsto.exists_eventually_le {N : B.One → ℝ} (hN : B.IsAuxNorm N) {w : ℕ → B.One}
    {y : B.One} (hm : B.MixedTendsto w y) : ∃ r : ℝ, ∀ᶠ k in atTop, N (w k) ≤ r := by
  obtain ⟨hP, c, hc, hx, -, hh⟩ := hm
  obtain ⟨C, -, hC⟩ := hh.exists_bound
  obtain ⟨V, hVo, hxV, -, a, A, ha, -, hV⟩ := hN.exists_bounds hc hx
  refine ⟨C / a, (hP.eventually (hVo.mem_nhds hxV)).mono fun k hk => ?_⟩
  rw [le_div_iff₀ ha, mul_comm]
  exact (hV (w k) hk).1.trans (hC k)

/-- **A continuous fibre seminorm is locally dominated by an auxiliary norm**: if `M` is
continuous on `Y_{0,1}|S` and a seminorm on the fibres over the open set `S`, then near every
`x ∈ S`, `M ≤ C·N`. -/
theorem exists_le_mul_auxNorm {N : B.One → ℝ} (hN : B.IsAuxNorm N) {M : B.One → ℝ} {S : Set X}
    (hS : IsOpen S) (hMc : ContinuousOn M {w | P (B.oneVal w) ∈ S})
    (hMs : ∀ y ∈ S, B.IsFiberSeminorm M y) {x : X} (hx : x ∈ S) :
    ∃ V : Set X, IsOpen V ∧ x ∈ V ∧ ∃ C : ℝ, 0 < C ∧
      ∀ w : B.One, P (B.oneVal w) ∈ V → M w ≤ C * N w := by
  obtain ⟨c, hcm, hxc⟩ := exists_chart_mem B x
  have hc := B.isChart_of_mem hcm
  have hopen : IsOpen {w : B.One | P (B.oneVal w) ∈ S} :=
    hS.preimage (B.continuous.comp B.continuous_oneVal)
  have hMx : ContinuousAt M (B.zeroOne x) := hMc.continuousAt (hopen.mem_nhds (by
    change P (B.oneVal (B.zeroOne x)) ∈ S
    rw [proj_oneVal_zeroOne B]; exact hx))
  obtain ⟨V₁, hV₁o, hxV₁, -, C, hC, hV₁⟩ := exists_le_mul_norm_liftOne hc hxc hMx (hS.mem_nhds hx)
    fun y hy v t => (hMs y hy).smul t v
  obtain ⟨V₂, hV₂o, hxV₂, -, a, A, ha, haA, hV₂⟩ := hN.exists_bounds hc hxc
  refine ⟨V₁ ∩ V₂, hV₁o.inter hV₂o, ⟨hxV₁, hxV₂⟩, C * A, mul_pos hC (ha.trans haA),
    fun w hw => ?_⟩
  calc M w ≤ C * ‖(c.liftOne (B.oneVal w)).2‖ := hV₁ w hw.1
    _ ≤ C * (A * N w) := mul_le_mul_of_nonneg_left (hV₂ w hw.2).2 hC.le
    _ = C * A * N w := by ring

/-! #### Pointwise lower semicontinuity along mixed convergent sequences -/

variable (B) in
/-- `M` is **lower semicontinuous along mixed convergent sequences at `y`** (clause (3) of
Definitions 5.1.7 and 12.2.10 at one point, in the form `M(y) - ε < M(w_k)` eventually). -/
def MixedLscAt (M : B.One → ℝ) (y : B.One) : Prop :=
  ∀ w : ℕ → B.One, B.MixedTendsto w y → ∀ ε > 0, ∀ᶠ k in atTop, M y - ε < M (w k)

theorem IsReflexiveAuxNorm.mixedLscAt {N : B.One → ℝ} (hN : B.IsReflexiveAuxNorm N) (y : B.One) :
    B.MixedLscAt N y :=
  fun _ hm _ hε => hN.eventually_sub_lt hm hε

theorem MixedLscAt.le_liminf {M : B.One → ℝ} {y : B.One} (h : B.MixedLscAt M y)
    {w : ℕ → B.One} (hm : B.MixedTendsto w y) :
    (M y : EReal) ≤ liminf (fun k => (M (w k) : EReal)) atTop :=
  le_liminf_coe_of_eventually (h w hm)

/-- An auxiliary norm which is lower semicontinuous along mixed convergent sequences at every
point is a reflexive auxiliary norm. -/
theorem isReflexiveAuxNorm_of_mixedLscAt {N : B.One → ℝ} (hN : B.IsAuxNorm N)
    (h : ∀ y, B.MixedLscAt N y) : B.IsReflexiveAuxNorm N :=
  ⟨hN, fun _ y hm => (h y).le_liminf hm⟩

theorem mixedLscAt_const (a : ℝ) (y : B.One) : B.MixedLscAt (fun _ => a) y :=
  fun _ _ ε hε => Eventually.of_forall fun _ => by linarith

theorem MixedLscAt.add {M₁ M₂ : B.One → ℝ} {y : B.One} (h₁ : B.MixedLscAt M₁ y)
    (h₂ : B.MixedLscAt M₂ y) : B.MixedLscAt (fun w => M₁ w + M₂ w) y := by
  intro w hm ε hε
  filter_upwards [h₁ w hm (ε / 2) (half_pos hε), h₂ w hm (ε / 2) (half_pos hε)] with k hk₁ hk₂
  linarith

theorem mixedLscAt_finset_sum {ι : Type*} (s : Finset ι) {M : ι → B.One → ℝ} {y : B.One}
    (h : ∀ i ∈ s, B.MixedLscAt (M i) y) : B.MixedLscAt (fun w => ∑ i ∈ s, M i w) y := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa only [Finset.sum_empty] using mixedLscAt_const (B := B) 0 y
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self a s)).add
      (ih fun j hj => h j (Finset.mem_insert_of_mem hj))

theorem MixedLscAt.const_mul {M : B.One → ℝ} {y : B.One} (h : B.MixedLscAt M y) {c : ℝ}
    (hc : 0 ≤ c) : B.MixedLscAt (fun w => c * M w) y := by
  intro w hm ε hε
  rcases hc.eq_or_lt with rfl | hc
  · exact Eventually.of_forall fun _ => by simp only [zero_mul]; linarith
  filter_upwards [h w hm (ε / c) (div_pos hε hc)] with k hk
  have h1 : c * (M y - ε / c) < c * M (w k) := mul_lt_mul_of_pos_left hk hc
  have h2 : c * (ε / c) = ε := by field_simp
  rw [mul_sub, h2] at h1
  exact h1

/-- **Products with a continuous function of the base point** keep the lower semicontinuity
(for `M ≥ 0` near `P(y)`). -/
theorem MixedLscAt.mul_comp {M : B.One → ℝ} {y : B.One} (h : B.MixedLscAt M y) {g : X → ℝ}
    (hg : ContinuousAt g (P (B.oneVal y))) (hg0 : ∀ x, 0 ≤ g x) {V : Set X} (hV : IsOpen V)
    (hyV : P (B.oneVal y) ∈ V) (hM0 : ∀ w : B.One, P (B.oneVal w) ∈ V → 0 ≤ M w) :
    B.MixedLscAt (fun w => g (P (B.oneVal w)) * M w) y := by
  intro w hm ε hε
  set a := g (P (B.oneVal y)) with hadef
  set b := M y with hbdef
  have ha : 0 ≤ a := hg0 _
  have hb : 0 ≤ b := hM0 y hyV
  have hpos : (0 : ℝ) < a + b + 1 := by linarith
  set δ := ε / (a + b + 1) with hδ
  have hδ0 : 0 < δ := div_pos hε hpos
  have hgk : ∀ᶠ k in atTop, a - δ < g (P (B.oneVal (w k))) :=
    (tendsto_order.1 (hg.tendsto.comp hm.1)).1 _ (sub_lt_self _ hδ0)
  have hVk : ∀ᶠ k in atTop, P (B.oneVal (w k)) ∈ V := hm.1.eventually (hV.mem_nhds hyV)
  filter_upwards [hgk, h w hm δ hδ0, hVk] with k hk₁ hk₂ hk₃
  have h' := mul_sub_le_of_sub_lt ha hb (hg0 _) (hM0 _ hk₃) hδ0 hk₁ hk₂
  have h2 : δ * (a + b) < ε := by
    have : δ * (a + b + 1) = ε := div_mul_cancel₀ ε hpos.ne'
    nlinarith
  linarith

/-- A function which is `≥ 0` everywhere and `≤ 0` at `y` is lower semicontinuous at `y`. -/
theorem mixedLscAt_of_nonpos {M : B.One → ℝ} {y : B.One} (hy : M y ≤ 0) (h0 : ∀ w, 0 ≤ M w) :
    B.MixedLscAt M y :=
  fun w _ ε hε => Eventually.of_forall fun k => by linarith [h0 (w k)]

/-- Lower semicontinuity at `y` only depends on the values over a neighbourhood of `P(y)`. -/
theorem MixedLscAt.congr {M M' : B.One → ℝ} {y : B.One} (h : B.MixedLscAt M y) {V : Set X}
    (hV : IsOpen V) (hyV : P (B.oneVal y) ∈ V)
    (heq : ∀ w : B.One, P (B.oneVal w) ∈ V → M w = M' w) : B.MixedLscAt M' y := by
  intro w hm ε hε
  filter_upwards [h w hm ε hε, hm.1.eventually (hV.mem_nhds hyV)] with k hk hkV
  rw [← heq y hyV, ← heq _ hkV]; exact hk

end StrongBundle

end PartI

/-! ### Morphisms preserve mixed convergence -/

section Act

variable {Obj Mor : Type u} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] {X : EpGroupoid Obj Mor}
  {W : Type u} [TopologicalSpace W] [T2Space W] [ParacompactSpace W] {P : W → Obj}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle X.PObj P}
  [ParacompactSpace (pullbackSpace P X.src)]

namespace EpStrongBundle

variable (E : EpStrongBundle X B)

/-- **The lifted action of a local section of `s` preserves mixed convergence**: for an sc-smooth
`α` on an open `S` with `s(α(z)) = z`, `w_k →ᵐ w` and `P(w) ∈ S` give
`μ(α(P w_k), w_k) →ᵐ μ(α(P w), w)`.  (Level-0 continuity of `μ`, the local bound of the fibre maps
by an auxiliary norm, and `mixedTendsto_of_bounded`; the argument of Remark 12.2.9 for the
fibre maps of `μ`.) -/
theorem mixedTendsto_actOne (hB : B.HasReflexiveFibers) {α : Obj → Mor} {S : Set Obj}
    (hS : IsOpen S) (hα : X.PObj.IsScSmoothOn X.PMor α S) (hsrc : ∀ x ∈ S, X.src (α x) = x)
    {w : ℕ → B.One} {y : B.One} (hm : B.MixedTendsto w y) (hy : P (B.oneVal y) ∈ S) :
    B.MixedTendsto (fun k => E.actOne α (w k)) (E.actOne α y) := by
  obtain ⟨N₀, hN₀⟩ := proposition_5_1_3_exists (B := B)
  have hY : Tendsto (fun k => B.oneVal (E.actOne α (w k))) atTop
      (𝓝 (B.oneVal (E.actOne α y))) := by
    have hc : ContinuousAt (E.sectionAct α) (B.oneVal y) :=
      (E.isScSmoothOn_sectionAct hS hα hsrc).continuousOn.continuousAt
        ((hS.preimage B.continuous).mem_nhds hy)
    exact hc.tendsto.comp hm.tendsto_oneVal
  obtain ⟨r, hr⟩ := hm.exists_eventually_le hN₀
  obtain ⟨V, hVo, hyV, C, hC, hV⟩ := StrongBundle.exists_le_mul_auxNorm hN₀
    (M := N₀ ∘ E.actOne α) hS
    (hN₀.continuous.comp_continuousOn (E.continuousOn_actOne hS hα hsrc))
    (fun z hz => E.isFiberSeminorm_comp_actOne α (hsrc z hz) (hN₀.fiber _).isFiberSeminorm) hy
  refine StrongBundle.mixedTendsto_of_bounded hB hN₀ hY (r := C * r) ?_
  filter_upwards [hr, hm.1.eventually (hVo.mem_nhds hyV)] with k hk hkV
  exact (hV (w k) hkV).trans (mul_le_mul_of_nonneg_left hk hC.le)

/-- Lower semicontinuity is pulled back along the lifted action of a local section of `s`. -/
theorem mixedLscAt_comp_actOne (hB : B.HasReflexiveFibers) {α : Obj → Mor} {S : Set Obj}
    (hS : IsOpen S) (hα : X.PObj.IsScSmoothOn X.PMor α S) (hsrc : ∀ x ∈ S, X.src (α x) = x)
    {M : B.One → ℝ} {y : B.One} (hy : P (B.oneVal y) ∈ S) (hM : B.MixedLscAt M (E.actOne α y)) :
    B.MixedLscAt (M ∘ E.actOne α) y :=
  fun _ hm ε hε => hM _ (E.mixedTendsto_actOne hB hS hα hsrc hm hy) ε hε

/-- **Morphisms preserve mixed convergence, pointwise form**: for a morphism `φ` with
`s(φ) = P(w)` there is an sc-smooth local section `α` of `s` through `φ` on an open `S ∋ P(w)`
such that `w_k →ᵐ w` implies `μ(α(P w_k), w_k) →ᵐ μ(φ, w)`. -/
theorem exists_mixedTendsto_μ (hB : B.HasReflexiveFibers) {y : B.One} (φ : Mor)
    (hφ : P (B.oneVal y) = X.src φ) :
    ∃ (S : Set Obj) (α : Obj → Mor), IsOpen S ∧ P (B.oneVal y) ∈ S ∧ α (P (B.oneVal y)) = φ ∧
      (∀ x ∈ S, X.src (α x) = x) ∧ ∀ w : ℕ → B.One, B.MixedTendsto w y →
        B.MixedTendsto (fun k => E.actOne α (w k)) (E.actOne α y) := by
  obtain ⟨T, Vs, ρ, hφT, hρ⟩ := X.isLocalScDiffeo_src φ
  have hρs : ∀ z ∈ Vs, X.src (ρ z) = z := fun z hz => hρ.right_inv z hz
  have hyV : P (B.oneVal y) ∈ Vs := hφ ▸ hρ.mapsTo hφT
  have hρy : ρ (P (B.oneVal y)) = φ := by rw [hφ]; exact hρ.left_inv _ hφT
  exact ⟨Vs, ρ, hρ.isOpen_target, hyV, hρy, hρs, fun w hm =>
    E.mixedTendsto_actOne hB hρ.isOpen_target hρ.isScSmoothOn_inv hρs hm hyV⟩

end EpStrongBundle

end Act

/-! ### Definitions 12.2.8 and 12.2.10 -/

section Defs

variable {Obj Mor : Type u} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] {X : EpGroupoid Obj Mor}
  {W : Type u} [TopologicalSpace W] [T2Space W] [ParacompactSpace W] {P : W → Obj}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle X.PObj P}

namespace EpStrongBundle

/-- **Reflexive `(0, 1)`-fibres** (2021, p. 576, before Definition 12.2.8): the strong bundle
`W → X` over the object M-polyfold has a strong bundle atlas with reflexive `F₁` (Part I
Definition 5.1.4, `StrongBundle.HasReflexiveFibers`). -/
abbrev HasReflexiveFibers (_E : EpStrongBundle X B) : Prop := B.HasReflexiveFibers

/-- **Definition 12.2.8, p. 576** (mixed convergence): `w_k →ᵐ w` in `W_{0,1}` if `P(w_k) → P(w)` in
`X₀` and in some strong bundle chart around `P(w)` with `F₁` reflexive the fibre parts converge
weakly in `F₁` (Part I Definition 5.1.6 for the object bundle). -/
abbrev MixedTendsto (_E : EpStrongBundle X B) (w : ℕ → B.One) (y : B.One) : Prop :=
  B.MixedTendsto w y

/-- **Definition 12.2.8, p. 576**, unfolded. -/
theorem definition_12_2_8 (E : EpStrongBundle X B) (w : ℕ → B.One) (y : B.One) :
    E.MixedTendsto w y ↔
      Tendsto (fun k => P (B.oneVal (w k))) atTop (𝓝 (P (B.oneVal y))) ∧
        ∃ c : StrongBundleChart X.PObj P, B.IsChart c ∧ P (B.oneVal y) ∈ c.φ.source ∧
          IsReflexive (c.F 1) ∧
          WeakTendsto (fun k => c.liftOneSnd (B.oneVal (w k))) (c.liftOneSnd (B.oneVal y)) :=
  Iff.rfl

/-- **Definition 12.2.10, p. 577** (reflexive auxiliary norm): for a strong bundle over an
ep-groupoid with reflexive `1`-fibres, an auxiliary norm of Definition 12.2.1 (continuity, (0)
functoriality, (1) complete fibre norms, (2)) with (3) `N(w) ≤ liminf N(w_k)` whenever
`w_k →ᵐ w` (printed `k → 0`; the `liminf` in `EReal`). -/
structure IsReflexiveAuxNorm (E : EpStrongBundle X B) (N : B.One → ℝ) : Prop
    extends E.IsAuxNorm N where
  le_liminf : ∀ (w : ℕ → B.One) (y : B.One), E.MixedTendsto w y →
    (N y : EReal) ≤ liminf (fun k => (N (w k) : EReal)) atTop

variable {E : EpStrongBundle X B}

/-- A reflexive auxiliary norm of the ep-groupoid is one of the object bundle (Definition 5.1.7). -/
theorem IsReflexiveAuxNorm.toStrong {N : B.One → ℝ} (hN : E.IsReflexiveAuxNorm N) :
    B.IsReflexiveAuxNorm N :=
  ⟨hN.isAuxNorm, hN.le_liminf⟩

theorem IsReflexiveAuxNorm.mixedLscAt {N : B.One → ℝ} (hN : E.IsReflexiveAuxNorm N)
    (y : B.One) : B.MixedLscAt N y :=
  hN.toStrong.mixedLscAt y

/-- An auxiliary norm of Definition 12.2.1 which is lower semicontinuous along mixed convergent
sequences at every point is a reflexive auxiliary norm. -/
theorem isReflexiveAuxNorm_of_mixedLscAt {N : B.One → ℝ} (hN : E.IsAuxNorm N)
    (h : ∀ y, B.MixedLscAt N y) : E.IsReflexiveAuxNorm N :=
  ⟨hN, fun _ y hm => (h y).le_liminf hm⟩

end EpStrongBundle

end Defs

/-! ### Remark 12.2.9 -/

section Rem1229

variable {Obj Mor : Type u} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] {X : EpGroupoid Obj Mor}
  {W : Type u} [TopologicalSpace W] [T2Space W] [ParacompactSpace W] {P : W → Obj}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle X.PObj P}
  [ParacompactSpace (pullbackSpace P X.src)]

namespace EpStrongBundle

/-- **Remark 12.2.9, pp. 576–577**: mixed convergence does not depend on the chart: if `w_k →ᵐ w`,
the fibre parts converge weakly in every strong bundle chart around `P(w)` with reflexive `F₁`
(Lemma 5.1.5); moreover the limit is the point of `W_{0,1}` the definition names, `w_k → w` in `W`,
and (ep-groupoid form of the transition argument) the lifted action of every sc-smooth local
section of `s` around `P(w)` preserves mixed convergence. -/
theorem remark_12_2_9 (E : EpStrongBundle X B) (hB : E.HasReflexiveFibers) {w : ℕ → B.One}
    {y : B.One} (hm : E.MixedTendsto w y) :
    (∀ c : StrongBundleChart X.PObj P, B.IsChart c → P (B.oneVal y) ∈ c.φ.source →
      IsReflexive (c.F 1) →
        WeakTendsto (fun k => c.liftOneSnd (B.oneVal (w k))) (c.liftOneSnd (B.oneVal y))) ∧
    Tendsto (fun k => B.oneVal (w k)) atTop (𝓝 (B.oneVal y)) ∧
    ∀ (α : Obj → Mor) (S : Set Obj), IsOpen S → X.PObj.IsScSmoothOn X.PMor α S →
      (∀ x ∈ S, X.src (α x) = x) → P (B.oneVal y) ∈ S →
        E.MixedTendsto (fun k => E.actOne α (w k)) (E.actOne α y) :=
  ⟨fun _ hc hx hF => hm.weakTendsto_of_isChart hc hx hF, hm.tendsto_oneVal,
    fun _ _ hS hα hsrc hy => E.mixedTendsto_actOne hB hS hα hsrc hm hy⟩

end EpStrongBundle

end Rem1229

/-! ### Lower semicontinuity of the average, the transport and the gluing -/

section Glue

variable {Obj Mor : Type u} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] {X : EpGroupoid Obj Mor}
  {W : Type u} [TopologicalSpace W] [T2Space W] [ParacompactSpace W] {P : W → Obj}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle X.PObj P}
  [ParacompactSpace (pullbackSpace P X.src)]

namespace EpStrongBundle

variable (E : EpStrongBundle X B)

/-- **The average over `G_x` keeps the lower semicontinuity** (proof of Theorem 12.2.11). -/
theorem mixedLscAt_avgNorm (hB : B.HasReflexiveFibers) {x : Obj} (R : X.NaturalRep x)
    {M : B.One → ℝ} (hM : ∀ y : B.One, P (B.oneVal y) ∈ R.U → B.MixedLscAt M y) {y : B.One}
    (hy : P (B.oneVal y) ∈ R.U) : B.MixedLscAt (E.avgNorm R M) y := by
  classical
  have := Fintype.ofFinite (X.Isotropy x)
  have hsum : ∀ w, E.avgNorm R M w =
      (Nat.card (X.Isotropy x) : ℝ)⁻¹ * ∑ g, M (E.actOne (R.Γ g) w) := fun w => by
    rw [avgNorm, finsum_eq_sum_of_fintype]
  have h : B.MixedLscAt
      (fun w => (Nat.card (X.Isotropy x) : ℝ)⁻¹ * ∑ g, M (E.actOne (R.Γ g) w)) y :=
    (StrongBundle.mixedLscAt_finset_sum (M := fun g w => M (E.actOne (R.Γ g) w)) Finset.univ
      fun g _ => E.mixedLscAt_comp_actOne hB R.isOpen_U (R.isScSmoothOn_Γ g)
        (fun z hz => R.src_Γ g z hz) hy (hM _ (E.actOne_Γ_mem R g hy))).const_mul
      (inv_nonneg.2 (Nat.cast_nonneg _))
  exact h.congr isOpen_univ (mem_univ _) fun w _ => (hsum w).symm

variable {E}

/-- **The transport to the saturation keeps the lower semicontinuity** (proof of Theorem
12.2.11): near `P(y)` the transport is `M ∘ μ(ρ(·), ·)` for a local inverse `ρ` of `s`. -/
theorem mixedLscAt_transNorm (hB : B.HasReflexiveFibers) {x : Obj} {R : X.NaturalRep x}
    {M : B.One → ℝ} (hinv : ∀ g w, P (B.oneVal w) ∈ R.U → M (E.actOne (R.Γ g) w) = M w)
    (hM : ∀ y : B.One, P (B.oneVal y) ∈ R.U → B.MixedLscAt M y) {y : B.One}
    (hy : P (B.oneVal y) ∈ X.satSet R.U) : B.MixedLscAt (E.transNorm R M) y := by
  have hφs := X.src_selMor R.U (P (B.oneVal y))
  have hφt := X.tgt_selMor_mem hy
  obtain ⟨T, Vs, ρ, hφT, hρ⟩ := X.isLocalScDiffeo_src (X.selMor R.U (P (B.oneVal y)))
  have hρs : ∀ z ∈ Vs, X.src (ρ z) = z := fun z hz => hρ.right_inv z hz
  set S := Vs ∩ (X.tgt ∘ ρ) ⁻¹' R.U with hS
  have hSo : IsOpen S := (X.continuous_tgt.comp_continuousOn
    hρ.isScSmoothOn_inv.continuousOn).isOpen_inter_preimage hρ.isOpen_target R.isOpen_U
  have hy0 : P (B.oneVal y) ∈ S := by
    have h1 := hρ.mapsTo hφT
    rw [hφs] at h1
    refine ⟨h1, ?_⟩
    change X.tgt (ρ (P (B.oneVal y))) ∈ R.U
    have h2 := hρ.left_inv _ hφT
    rw [hφs] at h2
    rw [h2]; exact hφt
  have hc : B.MixedLscAt (M ∘ E.actOne ρ) y :=
    E.mixedLscAt_comp_actOne hB hρ.isOpen_target hρ.isScSmoothOn_inv hρs hy0.1
      (hM _ (by rw [E.P_actOne (hρs _ hy0.1)]; exact hy0.2))
  exact hc.congr hSo hy0 fun w hw => (transNorm_eq_of hinv (hρs _ hw.1) hw.2).symm

omit [ParacompactSpace (pullbackSpace P X.src)] in
/-- **The glued norm is lower semicontinuous along mixed convergent sequences** if the local
norms are, on their (saturated, open) domains. -/
theorem mixedLscAt_glueNorm {ι : Type*} {U : ι → Set Obj}
    {β : PartitionOfUnity ι X.OrbitSpace univ} {T : ι → B.One → ℝ} (hU : ∀ i, IsOpen (U i))
    (hsat : ∀ i, X.IsSaturated (U i)) (hβ : β.IsSubordinate fun i => X.π '' U i)
    (hT : ∀ i, B.IsLocalAuxNorm (U i) (T i))
    (hlsc : ∀ i (y : B.One), P (B.oneVal y) ∈ U i → B.MixedLscAt (T i) y) (y : B.One) :
    B.MixedLscAt (glueNorm β T) y := by
  classical
  set z := X.π (P (B.oneVal y)) with hz
  obtain ⟨n, hn, hfin⟩ := β.locallyFinite z
  set is := hfin.toFinset with his
  set O : Set Obj := X.π ⁻¹' interior n with hO
  have hOo : IsOpen O := isOpen_interior.preimage X.continuous_π
  have hyO : P (B.oneVal y) ∈ O := mem_interior_iff_mem_nhds.2 hn
  have hsupp : ∀ w : B.One, P (B.oneVal w) ∈ O →
      (support fun i => β i (X.π (P (B.oneVal w))) * T i w) ⊆ is := by
    intro w hw i hi
    simp only [his, Set.Finite.coe_toFinset]
    exact ⟨_, left_ne_zero_of_mul hi, interior_subset hw⟩
  have heq : ∀ w : B.One, P (B.oneVal w) ∈ O →
      (fun w => ∑ i ∈ is, β i (X.π (P (B.oneVal w))) * T i w) w = glueNorm β T w :=
    fun w hw => (finsum_eq_sum_of_support_subset _ (hsupp w hw)).symm
  have hterm : ∀ i ∈ is, B.MixedLscAt (fun w => β i (X.π (P (B.oneVal w))) * T i w) y := by
    intro i _
    by_cases hyU : P (B.oneVal y) ∈ U i
    · exact (hlsc i y hyU).mul_comp (g := fun x => β i (X.π x))
        ((β i).continuous.comp X.continuous_π).continuousAt (fun x => β.nonneg i _) (hU i) hyU
        fun w hw => (hT i).nonneg hw
    · refine StrongBundle.mixedLscAt_of_nonpos ?_ fun w => glue_term_nonneg hsat hβ hT i w
      rw [partition_eq_zero_of_not_mem hsat hβ hyU, zero_mul]
  exact (StrongBundle.mixedLscAt_finset_sum is hterm).congr hOo hyO heq

omit [ParacompactSpace (pullbackSpace P X.src)] in
/-- **The glued norm is a reflexive auxiliary norm** (the end of the proof of Theorem 12.2.11):
the hypotheses of `isAuxNorm_glueNorm` and the lower semicontinuity of the local norms. -/
theorem isReflexiveAuxNorm_glueNorm {ι : Type*} {U : ι → Set Obj}
    {β : PartitionOfUnity ι X.OrbitSpace univ} {T : ι → B.One → ℝ} (hU : ∀ i, IsOpen (U i))
    (hsat : ∀ i, X.IsSaturated (U i)) (hβ : β.IsSubordinate fun i => X.π '' U i)
    (hT : ∀ i, B.IsLocalAuxNorm (U i) (T i))
    (hinv : ∀ i (h k : B.One) (ψ : Mor) (hk : P (B.oneVal k) = X.src ψ),
      P (B.oneVal k) ∈ U i → B.oneVal h = E.μ ⟨(ψ, B.oneVal k), hk⟩ → T i h = T i k)
    (hlsc : ∀ i (y : B.One), P (B.oneVal y) ∈ U i → B.MixedLscAt (T i) y) :
    E.IsReflexiveAuxNorm (glueNorm β T) :=
  isReflexiveAuxNorm_of_mixedLscAt (isAuxNorm_glueNorm hU hsat hβ hT hinv)
    (mixedLscAt_glueNorm hU hsat hβ hT hlsc)

end EpStrongBundle

end Glue

/-! ### Theorem 12.2.11 and Remark 12.2.12 -/

section Thm12211

variable {Obj Mor : Type u} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] {X : EpGroupoid Obj Mor}
  {W : Type u} [TopologicalSpace W] [T2Space W] [ParacompactSpace W] {P : W → Obj}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle X.PObj P}

namespace EpStrongBundle

variable {E : EpStrongBundle X B}

/-- **Remark 12.2.12 (1), p. 577** (= the second clause of Theorem 12.2.11): for a reflexive
auxiliary norm `N` and a functorial continuous `f : X → (0, ∞)`, `(f ∘ P)·N` is a reflexive
auxiliary norm. -/
theorem remark_12_2_12_1 {N : B.One → ℝ} (hN : E.IsReflexiveAuxNorm N) {f : Obj → ℝ}
    (hf : Continuous f) (hf0 : ∀ x, 0 < f x) (hfun : ∀ φ, f (X.src φ) = f (X.tgt φ)) :
    E.IsReflexiveAuxNorm fun w => f (P (B.oneVal w)) * N w := by
  have h := hN.toStrong.comp_mul hf hf0
  refine ⟨⟨h.toIsAuxNorm, fun a b φ hb hab => ?_⟩, h.le_liminf⟩
  have hPa : P (B.oneVal a) = X.tgt φ := by rw [hab, E.P_μ]
  change f (P (B.oneVal a)) * N a = f (P (B.oneVal b)) * N b
  rw [hPa, hb, ← hfun φ, hN.map_μ a b φ hb hab]

/-- **Remark 12.2.12 (2), p. 577** (the ep-groupoid form of Proposition 5.1.3's comparison): for
two auxiliary norms `N₁`, `N₂` (Definition 12.2.1) over an ep-groupoid with paracompact `|X|` there
is a functorial continuous `f : X → (0, ∞)` with `N₁ ≤ (f ∘ P)·N₂`. -/
theorem remark_12_2_12_2 (h : X.HasParacompactOrbitSpace) {N₁ N₂ : B.One → ℝ}
    (hN₁ : E.IsAuxNorm N₁) (hN₂ : E.IsAuxNorm N₂) :
    ∃ f : Obj → ℝ, Continuous f ∧ (∀ x, 0 < f x) ∧ (∀ φ, f (X.src φ) = f (X.tgt φ)) ∧
      ∀ w : B.One, N₁ w ≤ f (P (B.oneVal w)) * N₂ w := by
  classical
  have := B.paracompactSpace_pullback X.PMor X.src
  have : ParacompactSpace X.OrbitSpace := h
  have := X.theorem_7_3_1_metrizable h
  -- the local comparison, on saturated open sets
  have hloc : ∀ y : Obj, ∃ V : Set Obj, IsOpen V ∧ y ∈ V ∧ ∃ C : ℝ, 0 < C ∧
      ∀ w : B.One, P (B.oneVal w) ∈ V → N₁ w ≤ C * N₂ w := fun y =>
    StrongBundle.exists_le_mul_auxNorm hN₂.isAuxNorm isOpen_univ
      hN₁.isAuxNorm.continuous.continuousOn
      (fun z _ => (hN₁.isAuxNorm.fiber z).isFiberSeminorm) (mem_univ y)
  choose V hVo hyV C hC hV using hloc
  have hsatV : ∀ y (w : B.One), P (B.oneVal w) ∈ X.satSet (V y) → N₁ w ≤ C y * N₂ w := by
    rintro y w ⟨φ, hφs, hφt⟩
    obtain ⟨k, hk⟩ := exists_oneVal_eq_μ E w φ hφs.symm
    have hPk : P (B.oneVal k) ∈ V y := by rw [hk, E.P_μ]; exact hφt
    rw [← hN₁.map_μ k w φ hφs.symm hk, ← hN₂.map_μ k w φ hφs.symm hk]
    exact hV y k hPk
  obtain ⟨β, hβ⟩ := PartitionOfUnity.exists_isSubordinate isClosed_univ
    (fun y => X.π '' X.satSet (V y))
    (fun y => by rw [EpGroupoid.image_π_satSet]; exact X.proposition_7_1_8 _ (hVo y))
    fun z _ => by
      obtain ⟨y, rfl⟩ := X.surjective_π z
      exact mem_iUnion.2 ⟨y, y, EpGroupoid.subset_satSet _ (hyV y), rfl⟩
  set g : X.OrbitSpace → ℝ := fun z => ∑ᶠ y, β y z * C y with hg
  have hfin : ∀ z, (support fun y => β y z).Finite := fun z => β.locallyFinite.point_finite z
  have hgc : Continuous g :=
    continuous_finsum (fun y => (β y).continuous.mul continuous_const)
      (β.locallyFinite.subset fun y => support_mul_subset_left _ _)
  have hg0 : ∀ z, 0 < g z := by
    intro z
    obtain ⟨i, hi⟩ : ∃ i, β i z ≠ 0 := by
      by_contra hall
      push Not at hall
      have h1 := β.sum_eq_one (mem_univ z)
      rw [finsum_eq_zero_of_forall_eq_zero hall] at h1
      exact zero_ne_one h1
    have hpos : 0 < β i z * C i := mul_pos (lt_of_le_of_ne (β.nonneg i z) (Ne.symm hi)) (hC i)
    exact hpos.trans_le (single_le_finsum i ((hfin z).subset (support_mul_subset_left _ _))
      fun j => mul_nonneg (β.nonneg j z) (hC j).le)
  refine ⟨g ∘ X.π, hgc.comp X.continuous_π, fun x => hg0 _,
    fun φ => by simp only [comp_apply, X.π_src_eq_π_tgt φ], fun w => ?_⟩
  set z := X.π (P (B.oneVal w)) with hz
  have hsum1 := β.sum_eq_one (mem_univ z)
  have hf1 : (support fun y => β y z * N₁ w).Finite := (hfin z).subset (support_mul_subset_left _ _)
  have hf2 : (support fun y => β y z * (C y * N₂ w)).Finite :=
    (hfin z).subset (support_mul_subset_left _ _)
  calc N₁ w = (∑ᶠ y, β y z) * N₁ w := by rw [hsum1, one_mul]
    _ = ∑ᶠ y, β y z * N₁ w := finsum_mul _ _
    _ ≤ ∑ᶠ y, β y z * (C y * N₂ w) := by
        refine finsum_le_finsum' hf1 hf2 fun y => ?_
        by_cases hβ0 : β y z = 0
        · simp only [hβ0, zero_mul, le_refl]
        have hmem : P (B.oneVal w) ∈ X.satSet (V y) :=
          EpGroupoid.mem_of_π_mem_image (EpGroupoid.isSaturated_satSet _)
            (hβ y (subset_tsupport _ hβ0))
        exact mul_le_mul_of_nonneg_left (hsatV y w hmem) (β.nonneg y z)
    _ = ∑ᶠ y, β y z * C y * N₂ w := finsum_congr fun y => by ring
    _ = (∑ᶠ y, β y z * C y) * N₂ w := (finsum_mul _ _).symm
    _ = (g ∘ X.π) (P (B.oneVal w)) * N₂ w := rfl

/-- **Remark 12.2.12 (3), p. 578**: for an open `U`, a function `N` which is `≥ 0` and lower
semicontinuous along mixed convergent sequences over `U` (e.g. a reflexive auxiliary norm for
`W_{0,1}|U`), and a continuous `f : X → [0, ∞)`, the cut-off `Ñ` (`= f·N` over `U`, `= 0` off `U`)
satisfies `Ñ(w) ≤ liminf Ñ(w_k)` for every mixed convergent sequence `w_k →ᵐ w`.  The text also
asks `U` saturated, `f` functorial and `supp f ⊆ U`; these are not needed for the estimate. -/
theorem remark_12_2_12_3 {U : Set Obj} (hU : IsOpen U) {N : B.One → ℝ}
    (hN0 : ∀ w : B.One, P (B.oneVal w) ∈ U → 0 ≤ N w)
    (hN : ∀ y : B.One, P (B.oneVal y) ∈ U → B.MixedLscAt N y) {f : Obj → ℝ} (hf : Continuous f)
    (hf0 : ∀ x, 0 ≤ f x) (w : ℕ → B.One) (y : B.One) (hm : E.MixedTendsto w y) :
    ((U.indicator (fun _ => (1 : ℝ)) (P (B.oneVal y)) * (f (P (B.oneVal y)) * N y) : ℝ) : EReal) ≤
      liminf (fun k => ((U.indicator (fun _ => (1 : ℝ)) (P (B.oneVal (w k))) *
        (f (P (B.oneVal (w k))) * N (w k)) : ℝ) : EReal)) atTop := by
  classical
  set Ñ : B.One → ℝ := fun v =>
    U.indicator (fun _ => (1 : ℝ)) (P (B.oneVal v)) * (f (P (B.oneVal v)) * N v) with hÑ
  have hÑ0 : ∀ v, 0 ≤ Ñ v := by
    intro v
    by_cases hv : P (B.oneVal v) ∈ U
    · simp only [hÑ, indicator_of_mem hv, one_mul]
      exact mul_nonneg (hf0 _) (hN0 v hv)
    · simp only [hÑ, indicator_of_notMem hv, zero_mul, le_refl]
  have hl : B.MixedLscAt Ñ y := by
    by_cases hy : P (B.oneVal y) ∈ U
    · refine ((hN y hy).mul_comp hf.continuousAt hf0 hU hy hN0).congr hU hy fun v hv => ?_
      simp only [hÑ, indicator_of_mem hv, one_mul]
    · exact StrongBundle.mixedLscAt_of_nonpos
        (by simp only [hÑ, indicator_of_notMem hy, zero_mul, le_refl]) hÑ0
  exact hl.le_liminf hm

/-- **Theorem 12.2.11, p. 577, existence**: a strong bundle with reflexive `1`-fibres over an
ep-groupoid with paracompact orbit space has a reflexive auxiliary norm.  The text's proof: the
average over `G_x` of a reflexive local norm on `U'(x)`, its transport to the saturation, and a
partition of unity of `|X|`; the lower semicontinuity survives the transport because morphisms
preserve mixed convergence (`mixedTendsto_actOne`). -/
theorem theorem_12_2_11_exists (E : EpStrongBundle X B) (h : X.HasParacompactOrbitSpace)
    (hB : E.HasReflexiveFibers) : ∃ N : B.One → ℝ, E.IsReflexiveAuxNorm N := by
  have := B.paracompactSpace_pullback X.PMor X.src
  have : ParacompactSpace X.OrbitSpace := h
  have := X.theorem_7_3_1_metrizable h
  obtain ⟨N₀, hN₀⟩ := proposition_5_1_8_exists hB
  choose R _ using fun x : Obj => X.theorem_7_1_13 x isOpen_univ (mem_univ x)
  obtain ⟨β, hβ⟩ := PartitionOfUnity.exists_isSubordinate isClosed_univ
    (fun x => X.π '' X.satSet (R x).U)
    (fun x => by rw [EpGroupoid.image_π_satSet]; exact X.proposition_7_1_8 _ (R x).isOpen_U)
    fun z _ => by
      obtain ⟨y, rfl⟩ := X.surjective_π z
      exact mem_iUnion.2 ⟨y, y, EpGroupoid.subset_satSet _ (R y).mem_U, rfl⟩
  have hM : ∀ x, B.IsLocalAuxNorm (R x).U (E.avgNorm (R x) N₀) := fun x =>
    E.isLocalAuxNorm_avgNorm (R x) (hN₀.toIsAuxNorm.isLocalAuxNorm _)
  have hinv : ∀ x g w, P (B.oneVal w) ∈ (R x).U →
      E.avgNorm (R x) N₀ (E.actOne ((R x).Γ g) w) = E.avgNorm (R x) N₀ w := fun x g w hw =>
    E.avgNorm_actOne (R x) N₀ g hw
  have hlscM : ∀ x (y : B.One), P (B.oneVal y) ∈ (R x).U →
      B.MixedLscAt (E.avgNorm (R x) N₀) y := fun x _ hy =>
    E.mixedLscAt_avgNorm hB (R x) (fun y' _ => hN₀.mixedLscAt y') hy
  exact ⟨_, isReflexiveAuxNorm_glueNorm (E := E) (U := fun x => X.satSet (R x).U)
    (fun x => EpGroupoid.isOpen_satSet (R x).isOpen_U)
    (fun x => EpGroupoid.isSaturated_satSet _) hβ
    (fun x => isLocalAuxNorm_transNorm (hM x) (hinv x))
    (fun x h k ψ hk _ hh => transNorm_μ (hinv x) h k ψ hk hh)
    fun x _ hy => mixedLscAt_transNorm hB (hinv x) (hlscM x) hy⟩

/-- **Theorem 12.2.11, p. 577, second clause**: `h ↦ f(P(h))·N(h)` is a reflexive auxiliary norm
for a reflexive auxiliary norm `N` and a functorial continuous `f : X → (0, ∞)`. -/
theorem theorem_12_2_11_mul {N : B.One → ℝ} (hN : E.IsReflexiveAuxNorm N) {f : Obj → ℝ}
    (hf : Continuous f) (hf0 : ∀ x, 0 < f x) (hfun : ∀ φ, f (X.src φ) = f (X.tgt φ)) :
    E.IsReflexiveAuxNorm fun w => f (P (B.oneVal w)) * N w :=
  remark_12_2_12_1 hN hf hf0 hfun

/-- **Theorem 12.2.11, p. 577, last clause**: with reflexive `1`-fibres and paracompact `|X|`,
every auxiliary norm `N'` lies between two reflexive auxiliary norms, `N₁ ≤ N' ≤ N₂`. -/
theorem theorem_12_2_11_sandwich (h : X.HasParacompactOrbitSpace) (hB : E.HasReflexiveFibers)
    {N' : B.One → ℝ} (hN' : E.IsAuxNorm N') :
    ∃ N₁ N₂ : B.One → ℝ, E.IsReflexiveAuxNorm N₁ ∧ E.IsReflexiveAuxNorm N₂ ∧
      ∀ w, N₁ w ≤ N' w ∧ N' w ≤ N₂ w := by
  obtain ⟨N, hN⟩ := E.theorem_12_2_11_exists h hB
  obtain ⟨f, hf, hf0, hfun, hfN⟩ := remark_12_2_12_2 h hN.toIsAuxNorm hN'
  obtain ⟨g, hg, hg0, hgun, hgN⟩ := remark_12_2_12_2 h hN' hN.toIsAuxNorm
  refine ⟨fun w => (f (P (B.oneVal w)))⁻¹ * N w, fun w => g (P (B.oneVal w)) * N w,
    remark_12_2_12_1 hN (hf.inv₀ fun x => (hf0 x).ne') (fun x => inv_pos.2 (hf0 x))
      (fun φ => by simp only [Pi.inv_apply, hfun φ]), remark_12_2_12_1 hN hg hg0 hgun,
      fun w => ⟨?_, hgN w⟩⟩
  rw [inv_mul_le_iff₀ (hf0 _)]
  exact hfN w

/-- **Theorem 12.2.11, p. 577** (all three clauses): with reflexive `1`-fibres over an ep-groupoid
with paracompact `|X|`: a reflexive auxiliary norm exists; `(f ∘ P)·N` is reflexive for every
reflexive `N` and functorial continuous `f > 0`; every auxiliary norm lies between two reflexive
ones. -/
theorem theorem_12_2_11 (E : EpStrongBundle X B) (h : X.HasParacompactOrbitSpace)
    (hB : E.HasReflexiveFibers) :
    (∃ N : B.One → ℝ, E.IsReflexiveAuxNorm N) ∧
    (∀ N : B.One → ℝ, E.IsReflexiveAuxNorm N → ∀ f : Obj → ℝ, Continuous f → (∀ x, 0 < f x) →
      (∀ φ, f (X.src φ) = f (X.tgt φ)) →
        E.IsReflexiveAuxNorm fun w => f (P (B.oneVal w)) * N w) ∧
    (∀ N' : B.One → ℝ, E.IsAuxNorm N' → ∃ N₁ N₂ : B.One → ℝ, E.IsReflexiveAuxNorm N₁ ∧
      E.IsReflexiveAuxNorm N₂ ∧ ∀ w, N₁ w ≤ N' w ∧ N' w ≤ N₂ w) :=
  ⟨E.theorem_12_2_11_exists h hB, fun _ hN _ hf hf0 hfun => theorem_12_2_11_mul hN hf hf0 hfun,
    fun _ hN' => theorem_12_2_11_sandwich h hB hN'⟩

end EpStrongBundle

end Thm12211

end Polyfold
