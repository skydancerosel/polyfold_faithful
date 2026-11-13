import Polyfold.Chapter10.FredholmEquivalence
import Polyfold.Chapter8.BundleOrbitParacompact2021

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part III, Chapter 12,
§12.2 (pp. 570–574): **Definition 12.2.1** (auxiliary norm; = 2021 Definition 8.3.5),
**Theorem 12.2.2** (existence of auxiliary norms), **Definition 12.2.3** (continuous partition of
unity of an ep-groupoid), **Definition 12.2.4** (subordinate), **Proposition 12.2.5** (existence of
subordinate continuous partitions of unity).  Numbers and pages are the 2021 text's.

# Auxiliary norms on strong bundles over ep-groupoids

## The text, paraphrased

(Definition 12.2.1) An auxiliary norm for `(P : W → X, μ)` is a continuous `N : W_{0,1} → [0, ∞)`
which is a complete norm on the fibres, has `h_k → 0_x` whenever `P(h_k) → x` and `N(h_k) → 0`,
and is invariant under the morphisms: `N(μ(φ, k)) = N(k)`.  (Theorem 12.2.2) If `|X|` is
paracompact, an auxiliary norm exists.  (Definition 12.2.3) A continuous partition of unity of `X`
is a family `β_λ : X → [0, 1]` of continuous functions, (1) constant along morphisms, (2) every
point has a saturated open neighbourhood meeting only finitely many supports, (3) summing to one.
Such families correspond to the partitions of unity of `|X|`.  (Definition 12.2.4) Subordinate to a
saturated open cover `(U_λ)`: `supp β_λ ⊆ U_λ`.  (Proposition 12.2.5) For paracompact `|X|` they
exist.  (Proof of Theorem 12.2.2) For a neighbourhood `U'(x)` with the natural `G_x`-action the
lift `g ∗ w = μ(Γ(g, P w), w)` is a group action; the average of a chart norm over `G_x` is
`G_x`-invariant; transported by morphisms it gives a norm on `W|U(x)` over the saturation; glued
with a partition of unity of `|X|` it is the auxiliary norm.

## What is formalized

* A Part I observation (`StrongBundle.isAuxNorm_of_tendsto`): for Definition 5.1.1, the
  completeness of the fibres follows from continuity, the seminorm properties and condition (2)
  (the norm is then comparable with the chart norm `|·|₁` near every point, Lemma 5.1.2).
* `EpStrongBundle.actOne α`, the action `w ↦ μ(α(P w), w)` of a local section `α` of `s` on
  `W[1]`, with its continuity and fibre linearity.
* `EpStrongBundle.IsLocalAuxNorm U M` (conditions (1)–(2) of Definition 12.2.1 over an open `U`,
  completeness not required), the average `avgNorm R M` over `G_x` (`isLocalAuxNorm_avgNorm`,
  `avgNorm_actOne`: invariant under the lifted action), its transport `transNorm R M` to the
  saturation of `U(x)` (`isLocalAuxNorm_transNorm`, `transNorm_μ`: invariant under all morphisms),
  and the gluing `glueNorm` with a partition of unity of `|X|` (`isAuxNorm_glueNorm`).
* `EpGroupoid.IsContPartitionOfUnity` (**Definition 12.2.3**),
  `IsContPartitionOfUnity.IsSubordinate` (**Definition 12.2.4**),
  `isContPartitionOfUnity_comp_π` and `IsContPartitionOfUnity.descend` (the two directions of
  the remark after Definition 12.2.3), `proposition_12_2_5`.
* **`EpStrongBundle.theorem_12_2_2`** (Theorem 12.2.2), as printed, no added hypothesis.

## How the proof relates to the text's

The text averages the chart norm `‖pr₂ ∘ Ψ(g ∗ w)‖_{F₁}` over `G_x` on `U'(x)` from the good
neighbourhood theorem; here a Part I auxiliary norm `N₀` of the object bundle
(`proposition_5_1_3_exists`) is averaged on the domain `U(x)` of any natural representation, which
avoids charts.  The cover `|U(x)|` of `|X|` already works (the closure condition (5) of
Theorem 12.2.6 is not needed: the support of `β_x = β̂_x ∘ π` lies in the saturation, which is
open).  The text's checks of the fibre norm and of condition (2) are done through
`isAuxNorm_of_tendsto`: continuity and homogeneity give the upper bound by `|·|₁`, condition (2)
the lower bound, and completeness follows.
-/

open Set Filter Topology Function TopologicalSpace

noncomputable section

namespace Polyfold

universe u v

/-! ### Part I: the completeness of the fibres is automatic -/

section PartI

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})]

namespace StrongBundle

variable (B : StrongBundle PX P)

/-- `N` is a seminorm on the fibre `(Y_{0,1})_y` (homogeneous and subadditive). -/
structure IsFiberSeminorm (N : B.One → ℝ) (y : X) : Prop where
  smul : ∀ (t : ℝ) (v : B.oneFiber y), N (B.toOne (t • v)) = |t| * N (B.toOne v)
  add_le : ∀ v w : B.oneFiber y, N (B.toOne (v + w)) ≤ N (B.toOne v) + N (B.toOne w)

variable {B}

lemma IsFiberSeminorm.map_zero {N : B.One → ℝ} {y : X} (h : B.IsFiberSeminorm N y) :
    N (B.zeroOne y) = 0 := by
  have := h.smul 0 0
  rwa [zero_smul, abs_zero, zero_mul] at this

lemma IsFiberSeminorm.nonneg {N : B.One → ℝ} {y : X} (h : B.IsFiberSeminorm N y)
    (v : B.oneFiber y) : 0 ≤ N (B.toOne v) := by
  have h1 := h.add_le v (-v)
  have h2 := h.smul (-1) v
  rw [neg_one_smul, abs_neg, abs_one, one_mul] at h2
  rw [add_neg_cancel, h2] at h1
  have h0 : N (B.toOne 0) = 0 := h.map_zero
  linarith

/-- A complete fibre norm is a fibre seminorm. -/
lemma IsCompleteFiberNorm.isFiberSeminorm {N : B.One → ℝ} {y : X}
    (h : B.IsCompleteFiberNorm N y) : B.IsFiberSeminorm N y :=
  ⟨h.smul, h.add_le⟩

/-- Pull-back of a fibre seminorm along a map `L` of `Y[1]` which is linear from the fibre over `y`
to the fibre over `z`. -/
lemma IsFiberSeminorm.comp {M : B.One → ℝ} {y z : X} (hM : B.IsFiberSeminorm M z)
    {L : B.One → B.One} (ℓ : B.oneFiber y →ₗ[ℝ] B.oneFiber z)
    (hL : ∀ v, L (B.toOne v) = B.toOne (ℓ v)) : B.IsFiberSeminorm (M ∘ L) y where
  smul t v := by simp only [comp_apply, hL, map_smul]; exact hM.smul t _
  add_le v w := by simp only [comp_apply, hL, map_add]; exact hM.add_le _ _

/-- Condition (2) of Definition 5.1.1 for a function on `Y[1]`. -/
def TendstoZeroOne (B : StrongBundle PX P) (N : B.One → ℝ) : Prop :=
  ∀ (w : ℕ → B.One) (x : X), Tendsto (fun k => P (B.oneVal (w k))) atTop (𝓝 x) →
    Tendsto (fun k => N (w k)) atTop (𝓝 0) → Tendsto w atTop (𝓝 (B.zeroOne x))

variable {c : StrongBundleChart PX P}

/-- **The lower bound of Lemma 5.1.2 from condition (2) alone** (the argument of
`IsAuxNorm.exists_norm_liftOne_le`, which uses only the seminorm properties and condition (2)). -/
theorem exists_norm_liftOne_le_of_tendsto {N : B.One → ℝ} (hsn : ∀ y, B.IsFiberSeminorm N y)
    (h2 : B.TendstoZeroOne N) (hc : B.IsChart c) {x : X} (hx : x ∈ c.φ.source) :
    ∃ V, IsOpen V ∧ x ∈ V ∧ V ⊆ c.φ.source ∧ ∃ A, 0 < A ∧
      ∀ w : B.One, P (B.oneVal w) ∈ V → ‖(c.liftOne (B.oneVal w)).2‖ ≤ A * N w := by
  have hNnn' : ∀ w, 0 ≤ N w := fun w => (hsn _).nonneg (B.ofOne w)
  by_contra H
  push Not at H
  set V : ℕ → Set X := fun k => c.φ.source ∩ c.φ ⁻¹' Metric.ball (c.φ x) (1 / ((k : ℝ) + 1))
    with hVdef
  have hVo : ∀ k, IsOpen (V k) := fun k =>
    c.φ.continuousOn_toFun.isOpen_inter_preimage c.φ.isOpen_source Metric.isOpen_ball
  have hxV : ∀ k, x ∈ V k := fun k => ⟨hx, Metric.mem_ball_self (by positivity)⟩
  choose w hwV hwlt using fun k : ℕ =>
    H (V k) (hVo k) (hxV k) inter_subset_left ((k : ℝ) + 1) (by positivity)
  set y : ℕ → X := fun k => P (B.oneVal (w k)) with hy
  have hyc : ∀ k, y k ∈ c.φ.source := fun k => (hwV k).1
  set h : ℕ → ℝ := fun k => ‖(c.liftOne (B.oneVal (w k))).2‖ with hh
  have hNnn : ∀ k, 0 ≤ N (w k) := fun k => hNnn' (w k)
  have hhpos : ∀ k, 0 < h k := fun k => by
    have := hwlt k
    have : 0 ≤ ((k : ℝ) + 1) * N (w k) := by have := hNnn k; positivity
    linarith
  set w' : ℕ → B.One := fun k => B.toOne ((h k)⁻¹ • B.ofOne (w k)) with hw'
  have hNw' : ∀ k, N (w' k) = (h k)⁻¹ * N (w k) := fun k => by
    rw [hw', (hsn _).smul, abs_inv, abs_of_pos (hhpos k)]; rfl
  have hNw'lt : ∀ k, N (w' k) < 1 / ((k : ℝ) + 1) := fun k => by
    rw [hNw', inv_mul_eq_div, div_lt_div_iff₀ (hhpos k) (by positivity), one_mul, mul_comm]
    exact hwlt k
  have hnorm1 : ∀ k, ‖(c.liftOne (B.oneVal (w' k))).2‖ = 1 := fun k => by
    change ‖liftOneFiber hc (hyc k) ((h k)⁻¹ • B.ofOne (w k))‖ = 1
    rw [map_smul, norm_smul, Real.norm_of_nonneg (inv_nonneg.2 (hhpos k).le),
      liftOneFiber_ofOne]
    exact inv_mul_cancel₀ (hhpos k).ne'
  have hφy : Tendsto (fun k => c.φ (y k)) atTop (𝓝 (c.φ x)) := by
    refine tendsto_iff_dist_tendsto_zero.2 (squeeze_zero (fun _ => dist_nonneg)
      (fun k => (Metric.mem_ball.1 (hwV k).2).le) tendsto_one_div_add_atTop_nhds_zero_nat)
  have hyx : Tendsto y atTop (𝓝 x) := by
    have h1 : ContinuousWithinAt c.φ.symm c.φ.model.O (c.φ x) :=
      c.φ.continuousOn_invFun _ (c.φ.mapsTo_model x hx)
    have h2 := h1.tendsto.comp (tendsto_nhdsWithin_iff.2
      ⟨hφy, Eventually.of_forall fun k => c.φ.mapsTo_model _ (hyc k)⟩)
    rw [c.φ.symm_apply_apply hx] at h2
    exact h2.congr fun k => c.φ.symm_apply_apply (hyc k)
  have hPw' : ∀ k, P (B.oneVal (w' k)) = y k := fun k => proj_oneVal_toOne B _
  have hN0 : Tendsto (fun k => N (w' k)) atTop (𝓝 0) :=
    squeeze_zero (fun k => hNnn' _) (fun k => (hNw'lt k).le)
      tendsto_one_div_add_atTop_nhds_zero_nat
  have hlim := h2 w' x (by simpa only [hPw'] using hyx) hN0
  set χ := oneChartOf hc (B.zeroOne x) with hχ
  have hy₀ : B.zeroOne x ∈ χ.source :=
    (mem_oneChartOf_source hc _).2 (by rw [proj_oneVal_zeroOne B]; exact hx)
  have hχc : ContinuousAt χ (B.zeroOne x) :=
    χ.continuousOn_toFun.continuousAt (χ.isOpen_source.mem_nhds hy₀)
  have hχy₀ : χ (B.zeroOne x) = (c.φ x, 0) := liftOne_fiberZero hx
  have h3 : Tendsto (fun k => χ (w' k)) atTop (𝓝 (c.φ x, 0)) := by
    have := hχc.tendsto.comp hlim
    rw [hχy₀] at this
    exact this
  have h3' : Tendsto (fun k => ‖(χ (w' k)).2‖) atTop (𝓝 0) := by
    have h := ((continuous_snd.tendsto _).comp h3).norm
    simp only [norm_zero] at h
    exact h
  have h4 : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 0) :=
    h3'.congr fun k => hnorm1 k
  exact one_ne_zero (tendsto_nhds_unique tendsto_const_nhds h4)

/-- **Definition 5.1.1: completeness is automatic.**  A continuous `N : Y_{0,1} → ℝ` which is a
seminorm on every fibre and satisfies condition (2) is an auxiliary norm: near every point it is
squeezed between multiples of the chart norm `|·|₁` (the upper bound from continuity at the zero
section, the lower bound from (2)), so it is a norm and the fibres are complete. -/
theorem isAuxNorm_of_tendsto {N : B.One → ℝ} (hcont : Continuous N)
    (hsn : ∀ y, B.IsFiberSeminorm N y) (h2 : B.TendstoZeroOne N) : B.IsAuxNorm N := by
  refine ⟨hcont, fun x => ?_, h2⟩
  obtain ⟨c, hcm, hx⟩ := exists_chart_mem B x
  have hc := B.isChart_of_mem hcm
  obtain ⟨V₁, -, hxV₁, -, C, hC, hV₁⟩ := exists_le_mul_norm_liftOne hc hx
    hcont.continuousAt univ_mem fun y _ v t => (hsn y).smul t v
  obtain ⟨V₂, -, hxV₂, -, A, hA, hV₂⟩ := exists_norm_liftOne_le_of_tendsto hsn h2 hc hx
  have hup : ∀ v : B.oneFiber x, N (B.toOne v) ≤ C * ‖liftOneFiber hc hx v‖ := fun v =>
    hV₁ (B.toOne v) (by rw [proj_oneVal_toOne B]; exact hxV₁)
  have hlow : ∀ v : B.oneFiber x, ‖liftOneFiber hc hx v‖ ≤ A * N (B.toOne v) := fun v =>
    hV₂ (B.toOne v) (by rw [proj_oneVal_toOne B]; exact hxV₂)
  refine ⟨fun v hv => ?_, (hsn x).smul, (hsn x).add_le,
    complete_of_bounds hc hx (a := 1 / A) (A := C) (by positivity) (fun v => ?_) hup⟩
  · have h0 := hlow v
    rw [hv, mul_zero] at h0
    exact (liftOneFiber_eq_zero_iff hc hx).1 (norm_le_zero_iff.1 h0)
  · rw [one_div_mul_eq_div, div_le_iff₀ hA, mul_comm]; exact hlow v

/-- **Conditions (1)–(2) of Definition 5.1.1 over an open set `U`**, completeness not required:
`M` is continuous on `Y[1]|U`, a seminorm on the fibres over `U`, and `w_k → 0_y` whenever
`P(w_k) → y ∈ U` and `M(w_k) → 0`.  (Local data for the gluing in the proof of Theorem 12.2.2.) -/
structure IsLocalAuxNorm (U : Set X) (M : B.One → ℝ) : Prop where
  continuousOn : ContinuousOn M {w | P (B.oneVal w) ∈ U}
  seminorm : ∀ y ∈ U, B.IsFiberSeminorm M y
  tendsto : ∀ (w : ℕ → B.One) (y : X), y ∈ U →
    Tendsto (fun k => P (B.oneVal (w k))) atTop (𝓝 y) →
      Tendsto (fun k => M (w k)) atTop (𝓝 0) → Tendsto w atTop (𝓝 (B.zeroOne y))

lemma IsLocalAuxNorm.nonneg {U : Set X} {M : B.One → ℝ} (h : B.IsLocalAuxNorm U M) {w : B.One}
    (hw : P (B.oneVal w) ∈ U) : 0 ≤ M w :=
  (h.seminorm _ hw).nonneg (B.ofOne w)

/-- An auxiliary norm is a local one on every open set. -/
lemma IsAuxNorm.isLocalAuxNorm {N : B.One → ℝ} (hN : B.IsAuxNorm N) (U : Set X) :
    B.IsLocalAuxNorm U N :=
  ⟨hN.continuous.continuousOn, fun y _ => (hN.fiber y).isFiberSeminorm,
    fun w y _ h1 h2 => hN.tendsto_zeroOne w y h1 h2⟩

lemma IsFiberSeminorm.congr {N N' : B.One → ℝ} {y : X} (h : B.IsFiberSeminorm N y)
    (he : ∀ v : B.oneFiber y, N' (B.toOne v) = N (B.toOne v)) : B.IsFiberSeminorm N' y where
  smul t v := by rw [he, he]; exact h.smul t v
  add_le v w := by rw [he, he, he]; exact h.add_le v w

lemma IsFiberSeminorm.const_mul {N : B.One → ℝ} {y : X} (h : B.IsFiberSeminorm N y) {c : ℝ}
    (hc : 0 ≤ c) : B.IsFiberSeminorm (fun w => c * N w) y where
  smul t v := by rw [h.smul]; ring
  add_le v w := by rw [← mul_add]; exact mul_le_mul_of_nonneg_left (h.add_le v w) hc

lemma IsFiberSeminorm.finset_sum {ι : Type*} (s : Finset ι) {N : ι → B.One → ℝ} {y : X}
    (h : ∀ i ∈ s, B.IsFiberSeminorm (N i) y) :
    B.IsFiberSeminorm (fun w => ∑ i ∈ s, N i w) y where
  smul t v := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i hi => (h i hi).smul t v
  add_le v w := by
    rw [← Finset.sum_add_distrib]; exact Finset.sum_le_sum fun i hi => (h i hi).add_le v w

end StrongBundle

end PartI

/-! ### The action of a local section of `s` on `W[1]` -/

section Act

variable {Obj Mor : Type u} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] {X : EpGroupoid Obj Mor}
  {W : Type u} [TopologicalSpace W] [T2Space W] [ParacompactSpace W] {P : W → Obj}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle X.PObj P}
  [ParacompactSpace (pullbackSpace P X.src)]

namespace EpStrongBundle

variable (E : EpStrongBundle X B)

/-- **The action `w ↦ μ(α(P w), w)` of a local section `α` of `s` on `W[1]`** (the level-`1`
restriction of `sectionAct`; for `α = Γ(g, ·)` it is the lift `g ∗ w` of p. 572). -/
def actOne (α : Obj → Mor) : B.One → B.One :=
  StrongBundle.oneRestrict B B (E.sectionAct α) (E.mapsTo_oneSet_sectionAct α)

@[simp] lemma oneVal_actOne (α : Obj → Mor) (w : B.One) :
    B.oneVal (E.actOne α w) = E.sectionAct α (B.oneVal w) := rfl

lemma P_actOne {α : Obj → Mor} {w : B.One} (h : X.src (α (P (B.oneVal w))) = P (B.oneVal w)) :
    P (B.oneVal (E.actOne α w)) = X.tgt (α (P (B.oneVal w))) :=
  E.P_sectionAct_of_eq α h.symm

lemma oneVal_actOne_of_eq {α : Obj → Mor} {w : B.One}
    (h : P (B.oneVal w) = X.src (α (P (B.oneVal w)))) :
    B.oneVal (E.actOne α w) = E.μ ⟨(α (P (B.oneVal w)), B.oneVal w), h⟩ :=
  E.sectionAct_of_eq α h

/-- `actOne α` is continuous on `W[1]|S` if `α` is an sc-smooth section of `s` over the open `S`. -/
theorem continuousOn_actOne {α : Obj → Mor} {S : Set Obj} (hS : IsOpen S)
    (hα : X.PObj.IsScSmoothOn X.PMor α S) (hsrc : ∀ x ∈ S, X.src (α x) = x) :
    ContinuousOn (E.actOne α) {w | P (B.oneVal w) ∈ S} :=
  (E.isScSmoothOn_sectionAct_one hS hα hsrc).continuousOn

/-- The fibre map `(W_{0,1})_y → (W_{0,1})_{t(α(y))}` of `actOne α`, linear. -/
def actFiber (α : Obj → Mor) {y : Obj} (hy : X.src (α y) = y) :
    B.oneFiber y →ₗ[ℝ] B.oneFiber (X.tgt (α y)) :=
  (IsLinearMap.mk' _ (E.isLinearMap_sectionAct (S := {y})
    (fun x hx => by rw [mem_singleton_iff.1 hx]; exact hy) rfl rfl)).restrict
    fun _ hv => E.mapsTo_oneSet_sectionAct α hv

lemma actOne_toOne (α : Obj → Mor) {y : Obj} (hy : X.src (α y) = y) (v : B.oneFiber y) :
    E.actOne α (B.toOne v) = B.toOne (E.actFiber α hy v) := rfl

lemma actOne_zeroOne (α : Obj → Mor) {y : Obj} (hy : X.src (α y) = y) :
    E.actOne α (B.zeroOne y) = B.zeroOne (X.tgt (α y)) := by
  change E.actOne α (B.toOne 0) = B.toOne 0
  rw [E.actOne_toOne α hy, map_zero]

/-- A fibre seminorm composed with `actOne α`. -/
lemma isFiberSeminorm_comp_actOne {M : B.One → ℝ} (α : Obj → Mor) {y : Obj}
    (hy : X.src (α y) = y) (hM : B.IsFiberSeminorm M (X.tgt (α y))) :
    B.IsFiberSeminorm (M ∘ E.actOne α) y :=
  hM.comp (E.actFiber α hy) (E.actOne_toOne α hy)

end EpStrongBundle

end Act

/-! ### Saturations -/

section Sat

variable {Obj Mor : Type u} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] (X : EpGroupoid Obj Mor)

namespace EpGroupoid

/-- `{y | ∃ φ : y → z, z ∈ U}`, the saturation of `U`. -/
def satSet (U : Set Obj) : Set Obj := {y | ∃ φ, X.src φ = y ∧ X.tgt φ ∈ U}

variable {X}

lemma subset_satSet (U : Set Obj) : U ⊆ X.satSet U := fun y hy =>
  ⟨X.unit y, X.src_unit y, by rw [X.tgt_unit]; exact hy⟩

lemma satSet_eq_saturation (U : Set Obj) : X.satSet U = X.π ⁻¹' (X.π '' U) := by
  ext y
  constructor
  · rintro ⟨φ, rfl, hφ⟩
    exact ⟨X.tgt φ, hφ, (X.π_src_eq_π_tgt φ).symm⟩
  · rintro ⟨z, hz, hzy⟩
    obtain ⟨φ, hs, ht⟩ := X.π_eq_π_iff.1 hzy
    exact ⟨X.inv φ, by rw [X.src_inv, ht], by rw [X.tgt_inv, hs]; exact hz⟩

lemma isSaturated_satSet (U : Set Obj) : X.IsSaturated (X.satSet U) := by
  rw [satSet_eq_saturation]
  change X.π ⁻¹' (X.π '' (X.π ⁻¹' (X.π '' U))) = X.π ⁻¹' (X.π '' U)
  rw [image_preimage_eq _ X.surjective_π]

lemma image_π_satSet (U : Set Obj) : X.π '' X.satSet U = X.π '' U := by
  rw [satSet_eq_saturation, image_preimage_eq _ X.surjective_π]

lemma isOpen_satSet {U : Set Obj} (hU : IsOpen U) : IsOpen (X.satSet U) := by
  rw [satSet_eq_saturation]
  exact (X.proposition_7_1_8 _ hU).preimage X.continuous_π

/-- On a saturated set, `π⁻¹(π(U)) = U`. -/
lemma mem_of_π_mem_image {U : Set Obj} (hU : X.IsSaturated U) {y : Obj}
    (hy : X.π y ∈ X.π '' U) : y ∈ U := by
  rw [← hU]; exact hy

open scoped Classical in
/-- A chosen morphism `y → z` with `z ∈ U` (the unit where there is none). -/
def selMor (U : Set Obj) (y : Obj) : Mor :=
  if h : ∃ φ, X.src φ = y ∧ X.tgt φ ∈ U then h.choose else X.unit y

lemma src_selMor (U : Set Obj) (y : Obj) : X.src (X.selMor U y) = y := by
  unfold selMor; split_ifs with h
  · exact h.choose_spec.1
  · exact X.src_unit y

lemma tgt_selMor_mem {U : Set Obj} {y : Obj} (h : y ∈ X.satSet U) : X.tgt (X.selMor U y) ∈ U := by
  have h' : ∃ φ, X.src φ = y ∧ X.tgt φ ∈ U := h
  unfold selMor; rw [dif_pos h']; exact h'.choose_spec.2

end EpGroupoid

end Sat

/-! ### The average over `G_x` and the transport to the saturation (proof of Theorem 12.2.2) -/

section Local

variable {Obj Mor : Type u} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] {X : EpGroupoid Obj Mor}
  {W : Type u} [TopologicalSpace W] [T2Space W] [ParacompactSpace W] {P : W → Obj}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle X.PObj P}
  [ParacompactSpace (pullbackSpace P X.src)]

namespace EpStrongBundle

variable (E : EpStrongBundle X B) {x : Obj} (R : X.NaturalRep x)

omit [ParacompactSpace (pullbackSpace P X.src)] in
theorem natLift_congr (g : X.Isotropy x) {v v' : W} (h : v = v') (hv : P v ∈ R.U)
    (hv' : P v' ∈ R.U) : E.natLift R g v hv = E.natLift R g v' hv' := by
  subst h; rfl

lemma P_actOne_Γ (g : X.Isotropy x) {w : B.One} (hw : P (B.oneVal w) ∈ R.U) :
    P (B.oneVal (E.actOne (R.Γ g) w)) = R.Φ g (P (B.oneVal w)) := by
  rw [E.P_actOne (R.src_Γ g _ hw), R.tgt_Γ g _ hw]

lemma actOne_Γ_mem (g : X.Isotropy x) {w : B.One} (hw : P (B.oneVal w) ∈ R.U) :
    P (B.oneVal (E.actOne (R.Γ g) w)) ∈ R.U := by
  rw [E.P_actOne_Γ R g hw]; exact R.mapsTo_Φ g hw

lemma oneVal_actOne_Γ (g : X.Isotropy x) {w : B.One} (hw : P (B.oneVal w) ∈ R.U) :
    B.oneVal (E.actOne (R.Γ g) w) = E.natLift R g (B.oneVal w) hw :=
  E.oneVal_actOne_of_eq (R.src_Γ g _ hw).symm

/-- `1 ∗ w = w`. -/
lemma actOne_Γ_one {w : B.One} (hw : P (B.oneVal w) ∈ R.U) : E.actOne (R.Γ 1) w = w :=
  B.oneVal_injective ((E.oneVal_actOne_Γ R 1 hw).trans (E.natLift_one R _ hw))

/-- `(g h) ∗ w = g ∗ (h ∗ w)`: the lift is a group action (the computation on p. 573). -/
lemma actOne_Γ_mul (g h : X.Isotropy x) {w : B.One} (hw : P (B.oneVal w) ∈ R.U) :
    E.actOne (R.Γ (g * h)) w = E.actOne (R.Γ g) (E.actOne (R.Γ h) w) := by
  apply B.oneVal_injective
  rw [E.oneVal_actOne_Γ R (g * h) hw, E.oneVal_actOne_Γ R g (E.actOne_Γ_mem R h hw),
    E.natLift_mul R g h _ hw]
  exact E.natLift_congr R g (E.oneVal_actOne_Γ R h hw).symm _ _

/-- **The average over `G_x`**, `(1/|G_x|) Σ_g M(g ∗ w)` (the text's `N'_x`, p. 573, with a Part I
auxiliary norm in place of the chart norm). -/
def avgNorm (M : B.One → ℝ) (w : B.One) : ℝ :=
  (Nat.card (X.Isotropy x) : ℝ)⁻¹ * ∑ᶠ g : X.Isotropy x, M (E.actOne (R.Γ g) w)

omit [ParacompactSpace (pullbackSpace P X.src)] in
variable (X) in
lemma card_isotropy_pos : (0 : ℝ) < Nat.card (X.Isotropy x) := by
  exact_mod_cast Nat.card_pos

/-- **The average is invariant under the lifted action**: `N'_x(h ∗ w) = N'_x(w)`. -/
theorem avgNorm_actOne (M : B.One → ℝ) (h : X.Isotropy x) {w : B.One}
    (hw : P (B.oneVal w) ∈ R.U) : E.avgNorm R M (E.actOne (R.Γ h) w) = E.avgNorm R M w := by
  unfold avgNorm
  congr 1
  calc ∑ᶠ g : X.Isotropy x, M (E.actOne (R.Γ g) (E.actOne (R.Γ h) w))
      = ∑ᶠ g : X.Isotropy x, (fun g => M (E.actOne (R.Γ g) w)) (Equiv.mulRight h g) :=
        finsum_congr fun g => by
          simp only [Equiv.coe_mulRight]; rw [E.actOne_Γ_mul R g h hw]
    _ = _ := finsum_comp_equiv (Equiv.mulRight h) (f := fun g => M (E.actOne (R.Γ g) w))

/-- **The average of a local auxiliary norm on `U(x)` is one.** -/
theorem isLocalAuxNorm_avgNorm {M : B.One → ℝ} (hM : B.IsLocalAuxNorm R.U M) :
    B.IsLocalAuxNorm R.U (E.avgNorm R M) := by
  classical
  have := Fintype.ofFinite (X.Isotropy x)
  have hsum : ∀ w, E.avgNorm R M w =
      (Nat.card (X.Isotropy x) : ℝ)⁻¹ * ∑ g, M (E.actOne (R.Γ g) w) := fun w => by
    rw [avgNorm, finsum_eq_sum_of_fintype]
  have hterm : ∀ g, ContinuousOn (fun w => M (E.actOne (R.Γ g) w)) {w | P (B.oneVal w) ∈ R.U} :=
    fun g => hM.continuousOn.comp (E.continuousOn_actOne R.isOpen_U (R.isScSmoothOn_Γ g)
      fun y hy => R.src_Γ g y hy) fun w hw => E.actOne_Γ_mem R g hw
  refine ⟨?_, fun y hy => ?_, fun w y hy h1 h2 => ?_⟩
  · refine (continuousOn_const.mul (continuousOn_finsetSum _ fun g _ => hterm g)).congr
      fun w _ => hsum w
  · have hg : ∀ g ∈ (Finset.univ : Finset (X.Isotropy x)),
        B.IsFiberSeminorm (M ∘ E.actOne (R.Γ g)) y := fun g _ =>
      E.isFiberSeminorm_comp_actOne (R.Γ g) (R.src_Γ g y hy)
        (hM.seminorm _ (by rw [R.tgt_Γ g y hy]; exact R.mapsTo_Φ g hy))
    exact ((StrongBundle.IsFiberSeminorm.finset_sum Finset.univ hg).const_mul
      (inv_nonneg.2 (card_isotropy_pos (X := X) (x := x)).le)).congr fun v => hsum _
  · have hc := card_isotropy_pos (X := X) (x := x)
    have hev : ∀ᶠ k in atTop, P (B.oneVal (w k)) ∈ R.U := h1 (R.isOpen_U.mem_nhds hy)
    have h3 : Tendsto (fun k => (Nat.card (X.Isotropy x) : ℝ) * E.avgNorm R M (w k)) atTop
        (𝓝 0) := by
      have := h2.const_mul (Nat.card (X.Isotropy x) : ℝ)
      rwa [mul_zero] at this
    refine hM.tendsto w y hy h1 (squeeze_zero' (hev.mono fun k hk => hM.nonneg hk)
      (hev.mono fun k hk => ?_) h3)
    rw [hsum, mul_inv_cancel_left₀ hc.ne']
    calc M (w k) = M (E.actOne (R.Γ 1) (w k)) := by rw [E.actOne_Γ_one R hk]
      _ ≤ ∑ g, M (E.actOne (R.Γ g) (w k)) :=
        Finset.single_le_sum (f := fun g => M (E.actOne (R.Γ g) (w k)))
          (fun g _ => hM.nonneg (E.actOne_Γ_mem R g hk)) (Finset.mem_univ _)

open scoped Classical in
/-- **The transport to the saturation `U(x)` of `U'(x)`** (the text's `N''_x`, p. 573):
`w ↦ M(μ(φ, w))` for a chosen `φ : P(w) → z ∈ U'(x)`, `0` off the saturation. -/
def transNorm (M : B.One → ℝ) (w : B.One) : ℝ :=
  if P (B.oneVal w) ∈ X.satSet R.U then M (E.actOne (X.selMor R.U) w) else 0

variable {E R}

/-- **The transport does not depend on the choice of `φ`** (the text's "well-defined", by the
`G_x`-invariance of `M`). -/
theorem transNorm_eq_of {M : B.One → ℝ}
    (hinv : ∀ g w, P (B.oneVal w) ∈ R.U → M (E.actOne (R.Γ g) w) = M w) {α : Obj → Mor}
    {w : B.One} (hs : X.src (α (P (B.oneVal w))) = P (B.oneVal w))
    (ht : X.tgt (α (P (B.oneVal w))) ∈ R.U) : E.transNorm R M w = M (E.actOne α w) := by
  have hsat : P (B.oneVal w) ∈ X.satSet R.U := ⟨_, hs, ht⟩
  rw [transNorm, if_pos hsat]
  have hφs := X.src_selMor R.U (P (B.oneVal w))
  have hφt := X.tgt_selMor_mem hsat
  set φ := X.selMor R.U (P (B.oneVal w)) with hφ
  set a := α (P (B.oneVal w)) with ha
  have hχ1 : X.src a = X.tgt (X.inv φ) := by rw [X.tgt_inv, hs, hφs]
  have hχs : X.src (X.comp a (X.inv φ)) = X.tgt φ := by rw [X.src_comp _ _ hχ1, X.src_inv]
  have hχt : X.tgt (X.comp a (X.inv φ)) = X.tgt a := X.tgt_comp _ _ hχ1
  obtain ⟨g, hg, -⟩ := R.existsUnique_Γ (X.comp a (X.inv φ)) (hχs ▸ hφt) (hχt ▸ ht)
  have hv : P (B.oneVal (E.actOne (X.selMor R.U) w)) = X.tgt φ := E.P_actOne hφs
  have hvU : P (B.oneVal (E.actOne (X.selMor R.U) w)) ∈ R.U := hv ▸ hφt
  have hcomp : X.comp (X.comp a (X.inv φ)) φ = a := by
    have := GroupoidStr.comp_inv_cancel_right (G := X.toGroupoidStr) (φ := X.inv φ) (ψ := a) hχ1
    rwa [GroupoidStr.inv_inv] at this
  have key : E.actOne α w = E.actOne (R.Γ g) (E.actOne (X.selMor R.U) w) := by
    apply B.oneVal_injective
    have h5 : P (B.oneVal (E.actOne (X.selMor R.U) w)) =
        X.src (R.Γ g (P (B.oneVal (E.actOne (X.selMor R.U) w)))) := (R.src_Γ g _ hvU).symm
    calc B.oneVal (E.actOne α w) = E.μ ⟨(a, B.oneVal w), hs.symm⟩ := E.oneVal_actOne_of_eq hs.symm
      _ = E.μ ⟨(X.comp (X.comp a (X.inv φ)) φ, B.oneVal w),
            hφs.symm.trans (X.src_comp _ _ hχs).symm⟩ := E.μ_congr (Prod.ext hcomp.symm rfl)
      _ = E.μ ⟨(X.comp a (X.inv φ), E.μ ⟨(φ, B.oneVal w), hφs.symm⟩),
            (E.P_μ _).trans hχs.symm⟩ := E.μ_comp _ φ (B.oneVal w) hφs.symm hχs
      _ = E.μ ⟨(R.Γ g (P (B.oneVal (E.actOne (X.selMor R.U) w))),
            B.oneVal (E.actOne (X.selMor R.U) w)), h5⟩ :=
          E.μ_congr (Prod.ext (hg.symm.trans (congrArg (R.Γ g) (hχs.trans hv.symm)))
            (E.oneVal_actOne_of_eq (α := X.selMor R.U) (w := w) hφs.symm).symm)
      _ = B.oneVal (E.actOne (R.Γ g) (E.actOne (X.selMor R.U) w)) :=
          (E.oneVal_actOne_of_eq h5).symm
  rw [key, hinv g _ hvU]

/-- **The transport is continuous on `W[1]|U(x)`** (the text's continuity argument on p. 573,
with a local inverse of `s` at `φ`). -/
theorem continuousOn_transNorm {M : B.One → ℝ} (hM : B.IsLocalAuxNorm R.U M)
    (hinv : ∀ g w, P (B.oneVal w) ∈ R.U → M (E.actOne (R.Γ g) w) = M w) :
    ContinuousOn (E.transNorm R M) {w | P (B.oneVal w) ∈ X.satSet R.U} := by
  intro w₀ hw₀
  refine ContinuousAt.continuousWithinAt ?_
  have hφs := X.src_selMor R.U (P (B.oneVal w₀))
  have hφt := X.tgt_selMor_mem hw₀
  obtain ⟨T, Vs, ρ, hφT, hρ⟩ := X.isLocalScDiffeo_src (X.selMor R.U (P (B.oneVal w₀)))
  have hρs : ∀ y ∈ Vs, X.src (ρ y) = y := fun y hy => hρ.right_inv y hy
  set S := Vs ∩ (X.tgt ∘ ρ) ⁻¹' R.U with hS
  have hSo : IsOpen S := (X.continuous_tgt.comp_continuousOn
    hρ.isScSmoothOn_inv.continuousOn).isOpen_inter_preimage hρ.isOpen_target R.isOpen_U
  have hy0 : P (B.oneVal w₀) ∈ S := by
    have h1 := hρ.mapsTo hφT
    rw [hφs] at h1
    refine ⟨h1, ?_⟩
    change X.tgt (ρ (P (B.oneVal w₀))) ∈ R.U
    have h2 := hρ.left_inv _ hφT
    rw [hφs] at h2
    rw [h2]; exact hφt
  have hcont : ContinuousOn (M ∘ E.actOne ρ) {w | P (B.oneVal w) ∈ S} :=
    hM.continuousOn.comp ((E.continuousOn_actOne hρ.isOpen_target hρ.isScSmoothOn_inv hρs).mono
      fun w hw => hw.1) fun w hw => by
        change P (B.oneVal (E.actOne ρ w)) ∈ R.U
        rw [E.P_actOne (hρs _ hw.1)]; exact hw.2
  have hopen : IsOpen {w : B.One | P (B.oneVal w) ∈ S} :=
    hSo.preimage (B.continuous.comp B.continuous_oneVal)
  have heq : M ∘ E.actOne ρ =ᶠ[𝓝 w₀] E.transNorm R M :=
    Filter.eventually_of_mem (hopen.mem_nhds hy0) fun w hw =>
      (transNorm_eq_of hinv (hρs _ hw.1) hw.2).symm
  exact (hcont.continuousAt (hopen.mem_nhds hy0)).congr heq

/-- The transport is a seminorm on the fibres over the saturation. -/
theorem isFiberSeminorm_transNorm {M : B.One → ℝ} (hM : B.IsLocalAuxNorm R.U M) {y : Obj}
    (hy : y ∈ X.satSet R.U) : B.IsFiberSeminorm (E.transNorm R M) y :=
  (E.isFiberSeminorm_comp_actOne (X.selMor R.U) (X.src_selMor _ y)
    (hM.seminorm _ (X.tgt_selMor_mem hy))).congr fun v => by
      rw [transNorm, if_pos (by rw [B.proj_oneVal_toOne]; exact hy)]; rfl

/-- **Condition (2) for the transport** (the text: "we find as above an isomorphic sequence
`(w'_k)`"): `w_k = μ(φ_k⁻¹, w'_k)` with `w'_k → 0` and `φ_k⁻¹` given by a local inverse of `t`. -/
theorem tendsto_transNorm {M : B.One → ℝ} (hM : B.IsLocalAuxNorm R.U M)
    (hinv : ∀ g w, P (B.oneVal w) ∈ R.U → M (E.actOne (R.Γ g) w) = M w) (w : ℕ → B.One)
    {y : Obj} (hy : y ∈ X.satSet R.U) (h1 : Tendsto (fun k => P (B.oneVal (w k))) atTop (𝓝 y))
    (h2 : Tendsto (fun k => E.transNorm R M (w k)) atTop (𝓝 0)) :
    Tendsto w atTop (𝓝 (B.zeroOne y)) := by
  have hφs := X.src_selMor R.U y
  have hφt := X.tgt_selMor_mem hy
  set φ₀ := X.selMor R.U y with hφ₀
  obtain ⟨T, Vs, ρ, hφT, hρ⟩ := X.isLocalScDiffeo_src φ₀
  obtain ⟨T', Vt, τ, hφT', hτ⟩ := X.isLocalScDiffeo_tgt φ₀
  have hρs : ∀ z ∈ Vs, X.src (ρ z) = z := fun z hz => hρ.right_inv z hz
  have hyVs : y ∈ Vs := hφs ▸ hρ.mapsTo hφT
  have hρy : ρ y = φ₀ := by have h := hρ.left_inv _ hφT; rwa [hφs] at h
  have hρc : ContinuousAt ρ y :=
    hρ.isScSmoothOn_inv.continuousOn.continuousAt (hρ.isOpen_target.mem_nhds hyVs)
  set S := Vs ∩ (X.tgt ∘ ρ) ⁻¹' R.U with hS
  have hSo : IsOpen S := (X.continuous_tgt.comp_continuousOn
    hρ.isScSmoothOn_inv.continuousOn).isOpen_inter_preimage hρ.isOpen_target R.isOpen_U
  have hyS : y ∈ S := ⟨hyVs, by change X.tgt (ρ y) ∈ R.U; rw [hρy]; exact hφt⟩
  have hev : ∀ᶠ k in atTop, P (B.oneVal (w k)) ∈ S := h1 (hSo.mem_nhds hyS)
  have hevT : ∀ᶠ k in atTop, ρ (P (B.oneVal (w k))) ∈ T' := by
    have := (hρc.tendsto.comp h1) (hτ.isOpen_source.mem_nhds (hρy ▸ hφT'))
    exact this
  set v : ℕ → B.One := fun k => E.actOne ρ (w k) with hvdef
  have hMv : Tendsto (fun k => M (v k)) atTop (𝓝 0) :=
    h2.congr' (hev.mono fun k hk => transNorm_eq_of hinv (hρs _ hk.1) hk.2)
  have hPv : Tendsto (fun k => P (B.oneVal (v k))) atTop (𝓝 (X.tgt φ₀)) := by
    have h3 := (X.continuous_tgt.continuousAt.comp hρc).tendsto.comp h1
    rw [Function.comp_apply, hρy] at h3
    exact h3.congr' (hev.mono fun k hk => (E.P_actOne (hρs _ hk.1)).symm)
  have hv0 := hM.tendsto v _ hφt hPv hMv
  set α' : Obj → Mor := fun z => X.inv (τ z) with hα'
  have hα'sm : X.PObj.IsScSmoothOn X.PMor α' Vt :=
    MPolyfold.IsScSmoothOn.comp X.isScSmoothMap_inv hτ.isScSmoothOn_inv (mapsTo_univ _ _)
  have hα's : ∀ z ∈ Vt, X.src (α' z) = z := fun z hz => by
    simp only [hα', X.src_inv]; exact hτ.right_inv z hz
  have hzVt : X.tgt φ₀ ∈ Vt := hτ.mapsTo hφT'
  have hτz : τ (X.tgt φ₀) = φ₀ := hτ.left_inv _ hφT'
  have hc : ContinuousAt (E.actOne α') (B.zeroOne (X.tgt φ₀)) :=
    (E.continuousOn_actOne hτ.isOpen_target hα'sm hα's).continuousAt
      ((hτ.isOpen_target.preimage (B.continuous.comp B.continuous_oneVal)).mem_nhds
        (by change P (B.oneVal (B.zeroOne _)) ∈ Vt; rw [B.proj_oneVal_zeroOne]; exact hzVt))
  have h0 : E.actOne α' (B.zeroOne (X.tgt φ₀)) = B.zeroOne y := by
    rw [E.actOne_zeroOne α' (hα's _ hzVt)]
    congr 1
    simp only [hα', X.tgt_inv, hτz, hφs]
  have h4 := hc.tendsto.comp hv0
  rw [h0] at h4
  refine h4.congr' ((hev.and hevT).mono fun k hk => ?_)
  obtain ⟨hkS, hkT⟩ := hk
  apply B.oneVal_injective
  set ψ := ρ (P (B.oneVal (w k))) with hψ
  have hψs : P (B.oneVal (w k)) = X.src ψ := (hρs _ hkS.1).symm
  have hPvk : P (B.oneVal (v k)) = X.tgt ψ := E.P_actOne (hρs _ hkS.1)
  have hα'v : α' (P (B.oneVal (v k))) = X.inv ψ := by
    simp only [hα', hPvk, hτ.left_inv _ hkT]
  have hsv : P (B.oneVal (v k)) = X.src (α' (P (B.oneVal (v k)))) :=
    (hα's _ (by rw [hPvk]; exact hτ.mapsTo hkT)).symm
  have hq : P (E.μ ⟨(ψ, B.oneVal (w k)), hψs⟩) = X.src (X.inv ψ) := by
    rw [E.P_μ, X.src_inv]
  calc B.oneVal (E.actOne α' (v k))
      = E.μ ⟨(α' (P (B.oneVal (v k))), B.oneVal (v k)), hsv⟩ := E.oneVal_actOne_of_eq hsv
    _ = E.μ ⟨(X.inv ψ, E.μ ⟨(ψ, B.oneVal (w k)), hψs⟩), hq⟩ :=
        E.μ_congr (Prod.ext hα'v (E.oneVal_actOne_of_eq hψs))
    _ = B.oneVal (w k) := E.μ_inv_μ ⟨(ψ, B.oneVal (w k)), hψs⟩ hq

/-- **The transport is a local auxiliary norm on the saturation.** -/
theorem isLocalAuxNorm_transNorm {M : B.One → ℝ} (hM : B.IsLocalAuxNorm R.U M)
    (hinv : ∀ g w, P (B.oneVal w) ∈ R.U → M (E.actOne (R.Γ g) w) = M w) :
    B.IsLocalAuxNorm (X.satSet R.U) (E.transNorm R M) :=
  ⟨continuousOn_transNorm hM hinv, fun _ hy => isFiberSeminorm_transNorm hM hy,
    fun w _ hy h1 h2 => tendsto_transNorm hM hinv w hy h1 h2⟩

/-- **The transport is invariant under all morphisms** (condition (3) of Definition 12.2.1):
`N''_x(μ(ψ, k)) = N''_x(k)`. -/
theorem transNorm_μ {M : B.One → ℝ}
    (hinv : ∀ g w, P (B.oneVal w) ∈ R.U → M (E.actOne (R.Γ g) w) = M w) (h k : B.One) (ψ : Mor)
    (hk : P (B.oneVal k) = X.src ψ) (hh : B.oneVal h = E.μ ⟨(ψ, B.oneVal k), hk⟩) :
    E.transNorm R M h = E.transNorm R M k := by
  have hPh : P (B.oneVal h) = X.tgt ψ := by rw [hh, E.P_μ]
  by_cases hs : P (B.oneVal k) ∈ X.satSet R.U
  · have hφs := X.src_selMor R.U (P (B.oneVal k))
    have hφt := X.tgt_selMor_mem hs
    set φ := X.selMor R.U (P (B.oneVal k)) with hφ
    have hc1 : X.src φ = X.tgt (X.inv ψ) := by rw [X.tgt_inv, hφs, hk]
    have hs' : X.src ((fun _ : Obj => X.comp φ (X.inv ψ)) (P (B.oneVal h))) = P (B.oneVal h) := by
      change X.src (X.comp φ (X.inv ψ)) = _
      rw [X.src_comp _ _ hc1, X.src_inv, hPh]
    have ht' : X.tgt ((fun _ : Obj => X.comp φ (X.inv ψ)) (P (B.oneVal h))) ∈ R.U := by
      change X.tgt (X.comp φ (X.inv ψ)) ∈ R.U
      rw [X.tgt_comp _ _ hc1]; exact hφt
    rw [transNorm_eq_of hinv (α := fun _ => X.comp φ (X.inv ψ)) hs' ht', transNorm, if_pos hs]
    congr 1
    apply B.oneVal_injective
    have h2 : X.src (X.comp φ (X.inv ψ)) = X.tgt ψ := by rw [X.src_comp _ _ hc1, X.src_inv]
    have hcomp : X.comp (X.comp φ (X.inv ψ)) ψ = φ := by
      have := GroupoidStr.comp_inv_cancel_right (G := X.toGroupoidStr) (φ := X.inv ψ) (ψ := φ) hc1
      rwa [GroupoidStr.inv_inv] at this
    calc B.oneVal (E.actOne (fun _ => X.comp φ (X.inv ψ)) h)
        = E.μ ⟨(X.comp φ (X.inv ψ), B.oneVal h), hs'.symm⟩ := E.oneVal_actOne_of_eq hs'.symm
      _ = E.μ ⟨(X.comp φ (X.inv ψ), E.μ ⟨(ψ, B.oneVal k), hk⟩), (E.P_μ _).trans h2.symm⟩ :=
          E.μ_congr (Prod.ext rfl hh)
      _ = E.μ ⟨(X.comp (X.comp φ (X.inv ψ)) ψ, B.oneVal k),
            hk.trans (X.src_comp _ _ h2).symm⟩ := (E.μ_comp _ ψ (B.oneVal k) hk h2).symm
      _ = E.μ ⟨(φ, B.oneVal k), hφs.symm⟩ := E.μ_congr (Prod.ext hcomp rfl)
      _ = B.oneVal (E.actOne (X.selMor R.U) k) :=
          (E.oneVal_actOne_of_eq (α := X.selMor R.U) (w := k) hφs.symm).symm
  · have hs' : P (B.oneVal h) ∉ X.satSet R.U := by
      rintro ⟨χ, hχs, hχt⟩
      refine hs ⟨X.comp χ ψ, ?_, ?_⟩
      · rw [X.src_comp _ _ (hχs.trans hPh), hk]
      · rw [X.tgt_comp _ _ (hχs.trans hPh)]; exact hχt
    rw [transNorm, transNorm, if_neg hs, if_neg hs']

end EpStrongBundle

end Local

/-! ### Definitions 12.2.3, 12.2.4 and Proposition 12.2.5: continuous partitions of unity -/

section PartitionOfUnity

variable {Obj Mor : Type u} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] (X : EpGroupoid Obj Mor)

namespace EpGroupoid

/-- **Definition 12.2.3** (continuous partition of unity of an ep-groupoid), p. 570: continuous
`β_λ : X → [0, 1]` on the object space with (1) `β_λ(x) = β_λ(y)` whenever there is a morphism
`x → y`, (2) every point has a saturated open neighbourhood meeting the supports of only finitely
many `β_λ`, (3) `Σ_λ β_λ = 1`. -/
structure IsContPartitionOfUnity {ι : Type*} (β : ι → Obj → ℝ) : Prop where
  continuous : ∀ i, Continuous (β i)
  mem_Icc : ∀ i y, β i y ∈ Icc (0 : ℝ) 1
  map_mor : ∀ i φ, β i (X.src φ) = β i (X.tgt φ)
  locallyFinite : ∀ y, ∃ U : Set Obj, IsOpen U ∧ X.IsSaturated U ∧ y ∈ U ∧
    {i | (tsupport (β i) ∩ U).Nonempty}.Finite
  sum_eq_one : ∀ y, ∑ᶠ i, β i y = 1

/-- **Definition 12.2.4** (subordinate), p. 571: `supp β_λ ⊆ U_λ` for the saturated open cover
`(U_λ)` indexed by the same set. -/
def IsContPartitionOfUnity.IsSubordinate {ι : Type*} {β : ι → Obj → ℝ}
    (_ : X.IsContPartitionOfUnity β) (U : ι → Set Obj) : Prop :=
  ∀ i, tsupport (β i) ⊆ U i

variable {X}

/-- **The remark after Definition 12.2.3, first direction**: for a partition of unity `(β̂_λ)` of
`|X|`, the functions `β_λ = β̂_λ ∘ π` form a continuous partition of unity of `X`. -/
theorem isContPartitionOfUnity_comp_π {ι : Type*} (β : PartitionOfUnity ι X.OrbitSpace univ) :
    X.IsContPartitionOfUnity fun i => β i ∘ X.π where
  continuous i := (β i).continuous.comp X.continuous_π
  mem_Icc i y := ⟨β.nonneg i _, β.le_one i _⟩
  map_mor i φ := by simp only [Function.comp_apply, X.π_src_eq_π_tgt]
  locallyFinite y := by
    obtain ⟨n, hn, hfin⟩ := β.locallyFinite.closure (X.π y)
    refine ⟨X.π ⁻¹' interior n, isOpen_interior.preimage X.continuous_π, ?_,
      mem_interior_iff_mem_nhds.2 hn, hfin.subset fun i ⟨z, hz, hzn⟩ => ?_⟩
    · change X.π ⁻¹' (X.π '' (X.π ⁻¹' interior n)) = X.π ⁻¹' interior n
      rw [image_preimage_eq _ X.surjective_π]
    · exact ⟨X.π z, tsupport_comp_subset_preimage (β i) X.continuous_π hz,
        interior_subset hzn⟩
  sum_eq_one y := β.sum_eq_one (mem_univ _)

theorem isSubordinate_comp_π {ι : Type*} {β : PartitionOfUnity ι X.OrbitSpace univ}
    {U : ι → Set Obj} (hsat : ∀ i, X.IsSaturated (U i))
    (hβ : β.IsSubordinate fun i => X.π '' U i) :
    (isContPartitionOfUnity_comp_π β).IsSubordinate X U := fun i =>
  (tsupport_comp_subset_preimage (β i) X.continuous_π).trans fun _ hy =>
    mem_of_π_mem_image (hsat i) (hβ i hy)

/-- **The remark after Definition 12.2.3, second direction**: a continuous partition of unity of
`X` descends, by (1), to a partition of unity of `|X|`. -/
theorem IsContPartitionOfUnity.descend {ι : Type*} {β : ι → Obj → ℝ}
    (hβ : X.IsContPartitionOfUnity β) :
    ∃ β' : PartitionOfUnity ι X.OrbitSpace univ, ∀ i y, β' i (X.π y) = β i y := by
  have hdesc : ∀ i, ∀ a b : Obj, X.Isomorphic a b → β i a = β i b := by
    rintro i _ _ ⟨φ, rfl, rfl⟩; exact hβ.map_mor i φ
  let f : ι → X.OrbitSpace → ℝ := fun i => Quotient.lift (β i) (hdesc i)
  have hf : ∀ i y, f i (X.π y) = β i y := fun _ _ => rfl
  have hfc : ∀ i, Continuous (f i) := fun i => continuous_quot_lift _ (hβ.continuous i)
  refine ⟨⟨fun i => ⟨f i, hfc i⟩, ?_, ?_, ?_, ?_⟩, hf⟩
  · intro z
    obtain ⟨y, rfl⟩ := X.surjective_π z
    obtain ⟨U, hUo, hUs, hyU, hfin⟩ := hβ.locallyFinite y
    refine ⟨X.π '' U, (X.proposition_7_1_8 U hUo).mem_nhds ⟨y, hyU, rfl⟩,
      hfin.subset fun i ⟨c, hc, hcU⟩ => ?_⟩
    obtain ⟨y', hy'U, rfl⟩ := hcU
    exact ⟨y', subset_tsupport _ hc, hy'U⟩
  · intro i z
    obtain ⟨y, rfl⟩ := X.surjective_π z
    exact (hβ.mem_Icc i y).1
  · intro z _
    obtain ⟨y, rfl⟩ := X.surjective_π z
    exact hβ.sum_eq_one y
  · intro z
    obtain ⟨y, rfl⟩ := X.surjective_π z
    exact (hβ.sum_eq_one y).le

/-- **Proposition 12.2.5**, p. 571: if `|X|` is paracompact, every open cover of `X` by saturated
sets has a subordinate continuous partition of unity (the text's proof: a partition of unity of
`|X|` subordinate to `(π(U_λ))`, composed with `π`). -/
theorem proposition_12_2_5 (h : X.HasParacompactOrbitSpace) {ι : Type*} (U : ι → Set Obj)
    (hU : ∀ i, IsOpen (U i)) (hsat : ∀ i, X.IsSaturated (U i)) (hcov : ⋃ i, U i = univ) :
    ∃ β : ι → Obj → ℝ, ∃ hβ : X.IsContPartitionOfUnity β, hβ.IsSubordinate X U := by
  have : ParacompactSpace X.OrbitSpace := h
  have := X.theorem_7_3_1_metrizable h
  obtain ⟨β, hβ⟩ := PartitionOfUnity.exists_isSubordinate isClosed_univ (fun i => X.π '' U i)
    (fun i => X.proposition_7_1_8 _ (hU i)) fun z _ => by
      obtain ⟨y, rfl⟩ := X.surjective_π z
      obtain ⟨i, hi⟩ := mem_iUnion.1 (hcov.symm ▸ mem_univ y : y ∈ ⋃ i, U i)
      exact mem_iUnion.2 ⟨i, y, hi, rfl⟩
  exact ⟨_, isContPartitionOfUnity_comp_π β, isSubordinate_comp_π hsat hβ⟩

end EpGroupoid

end PartitionOfUnity

/-! ### The gluing (proof of Theorem 12.2.2) -/

section Glue

variable {Obj Mor : Type u} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] {X : EpGroupoid Obj Mor}
  {W : Type u} [TopologicalSpace W] [T2Space W] [ParacompactSpace W] {P : W → Obj}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle X.PObj P}

namespace EpStrongBundle

variable (E : EpStrongBundle X B) {ι : Type*}

/-- **The glued norm** `N(w) = Σ_λ β_λ(|P(w)|)·N_λ(w)` (the text's `N = Σ_x N_x`, p. 574), for a
partition of unity `(β_λ)` of `|X|`. -/
def glueNorm (β : PartitionOfUnity ι X.OrbitSpace univ) (T : ι → B.One → ℝ) (w : B.One) : ℝ :=
  ∑ᶠ i, β i (X.π (P (B.oneVal w))) * T i w

variable {E} {U : ι → Set Obj} {β : PartitionOfUnity ι X.OrbitSpace univ} {T : ι → B.One → ℝ}

omit [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] in
lemma partition_eq_zero_of_not_mem (hsat : ∀ i, X.IsSaturated (U i))
    (hβ : β.IsSubordinate fun i => X.π '' U i) {i : ι} {y : Obj} (hy : y ∉ U i) :
    β i (X.π y) = 0 := by
  by_contra h
  exact hy (EpGroupoid.mem_of_π_mem_image (hsat i) (hβ i (subset_tsupport _ h)))

lemma glue_term_nonneg (hsat : ∀ i, X.IsSaturated (U i))
    (hβ : β.IsSubordinate fun i => X.π '' U i) (hT : ∀ i, B.IsLocalAuxNorm (U i) (T i)) (i : ι)
    (w : B.One) : 0 ≤ β i (X.π (P (B.oneVal w))) * T i w := by
  by_cases hw : P (B.oneVal w) ∈ U i
  · exact mul_nonneg (β.nonneg i _) ((hT i).nonneg hw)
  · rw [partition_eq_zero_of_not_mem hsat hβ hw, zero_mul]

/-- **The glued norm is an auxiliary norm** (the end of the proof of Theorem 12.2.2): local
auxiliary norms `N_λ` on saturated open sets `U_λ`, invariant under the morphisms, glued with a
partition of unity of `|X|` subordinate to `(|U_λ|)`. -/
theorem isAuxNorm_glueNorm (hU : ∀ i, IsOpen (U i)) (hsat : ∀ i, X.IsSaturated (U i))
    (hβ : β.IsSubordinate fun i => X.π '' U i) (hT : ∀ i, B.IsLocalAuxNorm (U i) (T i))
    (hinv : ∀ i (h k : B.One) (ψ : Mor) (hk : P (B.oneVal k) = X.src ψ),
      P (B.oneVal k) ∈ U i → B.oneVal h = E.μ ⟨(ψ, B.oneVal k), hk⟩ → T i h = T i k) :
    E.IsAuxNorm (glueNorm β T) := by
  have hP1 : Continuous fun w : B.One => P (B.oneVal w) := B.continuous.comp B.continuous_oneVal
  have hπP : Continuous fun w : B.One => X.π (P (B.oneVal w)) := X.continuous_π.comp hP1
  have hfin : ∀ y : Obj, ∃ s : Finset ι, (support fun i => β i (X.π y)) ⊆ s := fun y =>
    ⟨(β.locallyFinite.point_finite (X.π y)).toFinset, fun i hi =>
      (Set.Finite.mem_toFinset _).2 hi⟩
  have hsum : ∀ (y : Obj) (s : Finset ι), (support fun i => β i (X.π y)) ⊆ s → ∀ w : B.One,
      P (B.oneVal w) = y → glueNorm β T w = ∑ i ∈ s, β i (X.π y) * T i w := by
    intro y s hs w hw
    rw [glueNorm, hw]
    exact finsum_eq_sum_of_support_subset _ ((support_mul_subset_left _ _).trans hs)
  -- continuity
  have hcont : Continuous (glueNorm β T) := by
    apply continuous_finsum (f := fun i w => β i (X.π (P (B.oneVal w))) * T i w)
    · intro i
      have hc : ContinuousOn (fun w => β i (X.π (P (B.oneVal w))) * T i w)
          {w | P (B.oneVal w) ∈ U i} :=
        ((β i).continuous.comp hπP).continuousOn.mul (hT i).continuousOn
      refine hc.continuous_of_tsupport_subset ((hU i).preimage hP1) ?_
      refine tsupport_mul_subset_left.trans ?_
      exact (tsupport_comp_subset_preimage (β i) hπP).trans fun w hw =>
        EpGroupoid.mem_of_π_mem_image (hsat i) (hβ i hw)
    · exact (β.locallyFinite.preimage_continuous hπP).subset fun i =>
        support_mul_subset_left _ _
  -- the fibres
  have hsn : ∀ y, B.IsFiberSeminorm (glueNorm β T) y := by
    intro y
    obtain ⟨s, hs⟩ := hfin y
    have hterm : ∀ i ∈ s, B.IsFiberSeminorm (fun w => β i (X.π y) * T i w) y := by
      intro i _
      by_cases hy : y ∈ U i
      · exact ((hT i).seminorm y hy).const_mul (β.nonneg i _)
      · rw [partition_eq_zero_of_not_mem hsat hβ hy]
        exact ⟨fun t v => by simp, fun v w => by simp⟩
    exact (StrongBundle.IsFiberSeminorm.finset_sum s hterm).congr fun v =>
      hsum y s hs _ (B.proj_oneVal_toOne v)
  -- condition (2)
  have h2 : B.TendstoZeroOne (glueNorm β T) := by
    intro w y h1 h2
    obtain ⟨i, hi⟩ : ∃ i, β i (X.π y) ≠ 0 := by
      by_contra hall
      push Not at hall
      have h1 := β.sum_eq_one (mem_univ (X.π y))
      rw [finsum_eq_zero_of_forall_eq_zero hall] at h1
      exact zero_ne_one h1
    have hpos : 0 < β i (X.π y) := lt_of_le_of_ne (β.nonneg i _) (Ne.symm hi)
    have hyU : y ∈ U i := by
      by_contra hy; exact hi (partition_eq_zero_of_not_mem hsat hβ hy)
    have hβk : Tendsto (fun k => β i (X.π (P (B.oneVal (w k))))) atTop (𝓝 (β i (X.π y))) :=
      ((β i).continuous.comp X.continuous_π).continuousAt.tendsto.comp h1
    have hterm : Tendsto (fun k => β i (X.π (P (B.oneVal (w k)))) * T i (w k)) atTop (𝓝 0) := by
      refine squeeze_zero (fun k => glue_term_nonneg hsat hβ hT i (w k)) (fun k => ?_) h2
      refine single_le_finsum i ?_ fun j => glue_term_nonneg hsat hβ hT j (w k)
      exact (β.locallyFinite.point_finite (X.π (P (B.oneVal (w k))))).subset
        (support_mul_subset_left _ _)
    have hev : ∀ᶠ k in atTop, β i (X.π (P (B.oneVal (w k)))) ≠ 0 :=
      hβk.eventually (eventually_ne_nhds hpos.ne')
    have hT0 : Tendsto (fun k => T i (w k)) atTop (𝓝 0) := by
      have h3 := hterm.div hβk hpos.ne'
      rw [zero_div] at h3
      exact h3.congr' (hev.mono fun k hk => by
        change β i _ * T i (w k) / β i _ = T i (w k)
        exact mul_div_cancel_left₀ _ hk)
    exact (hT i).tendsto w y hyU h1 hT0
  refine ⟨StrongBundle.isAuxNorm_of_tendsto hcont hsn h2, fun h k ψ hk hh => ?_⟩
  -- condition (3)
  have hPh : P (B.oneVal h) = X.tgt ψ := by rw [hh, E.P_μ]
  have hπ : X.π (P (B.oneVal h)) = X.π (P (B.oneVal k)) := by
    rw [hPh, hk]; exact (X.π_src_eq_π_tgt ψ).symm
  refine finsum_congr fun i => ?_
  rw [hπ]
  by_cases hkU : P (B.oneVal k) ∈ U i
  · rw [hinv i h k ψ hk hkU hh]
  · rw [partition_eq_zero_of_not_mem hsat hβ hkU, zero_mul, zero_mul]

end EpStrongBundle

end Glue

/-! ### Theorem 12.2.2 -/

section Thm1222

variable {Obj Mor : Type u} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] {X : EpGroupoid Obj Mor}
  {W : Type u} [TopologicalSpace W] [T2Space W] [ParacompactSpace W] {P : W → Obj}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle X.PObj P}

namespace EpStrongBundle

/-- **Theorem 12.2.2**, p. 570: every strong bundle `(P : W → X, μ)` over an ep-groupoid with
paracompact orbit space admits an auxiliary norm (Definition 12.2.1).  As printed; the proof
follows the text's (average over `G_x`, transport to the saturation, gluing over `|X|`), with a
Part I auxiliary norm in place of the chart norm. -/
theorem theorem_12_2_2 (E : EpStrongBundle X B) (h : X.HasParacompactOrbitSpace) :
    ∃ N : B.One → ℝ, E.IsAuxNorm N := by
  have := B.paracompactSpace_pullback X.PMor X.src
  have : ParacompactSpace X.OrbitSpace := h
  have := X.theorem_7_3_1_metrizable h
  obtain ⟨N₀, hN₀⟩ := proposition_5_1_3_exists (B := B)
  choose R _ using fun x : Obj => X.theorem_7_1_13 x isOpen_univ (mem_univ x)
  obtain ⟨β, hβ⟩ := PartitionOfUnity.exists_isSubordinate isClosed_univ
    (fun x => X.π '' X.satSet (R x).U)
    (fun x => by rw [EpGroupoid.image_π_satSet]; exact X.proposition_7_1_8 _ (R x).isOpen_U)
    fun z _ => by
      obtain ⟨y, rfl⟩ := X.surjective_π z
      exact mem_iUnion.2 ⟨y, y, EpGroupoid.subset_satSet _ (R y).mem_U, rfl⟩
  have hM : ∀ x, B.IsLocalAuxNorm (R x).U (E.avgNorm (R x) N₀) := fun x =>
    E.isLocalAuxNorm_avgNorm (R x) (hN₀.isLocalAuxNorm _)
  have hinv : ∀ x g w, P (B.oneVal w) ∈ (R x).U →
      E.avgNorm (R x) N₀ (E.actOne ((R x).Γ g) w) = E.avgNorm (R x) N₀ w := fun x g w hw =>
    E.avgNorm_actOne (R x) N₀ g hw
  exact ⟨_, isAuxNorm_glueNorm (E := E) (U := fun x => X.satSet (R x).U)
    (fun x => EpGroupoid.isOpen_satSet (R x).isOpen_U)
    (fun x => EpGroupoid.isSaturated_satSet _) hβ
    (fun x => isLocalAuxNorm_transNorm (hM x) (hinv x))
    fun x h k ψ hk _ hh => transNorm_μ (hinv x) h k ψ hk hh⟩

end EpStrongBundle

/-- **Theorem 12.2.2** for a bundled strong bundle over an ep-groupoid (an object of `SEP`). -/
theorem SEP.theorem_12_2_2 (A : SEP.{u}) (h : A.X.HasParacompactOrbitSpace) :
    ∃ N : A.B.One → ℝ, A.E.IsAuxNorm N :=
  A.E.theorem_12_2_2 h

end Thm1222

end Polyfold
