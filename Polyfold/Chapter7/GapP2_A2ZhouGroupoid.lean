import Polyfold.Chapter7.GapP2_A2Family
import Polyfold.Chapter7.ReducedCriterion
import Polyfold.Chapter7.SmoothRegularAssembly

set_option maxSynthPendingDepth 3

/-!
# Appendix 7.6.3 (2021, p. 348): Zhou's example and its non-effective part

2021 Appendix 7.6.3, p. 348: on `F = ℝ ⊕ L²(ℝ)`, `F_m = ℝ ⊕ H^{m,δ_m}(ℝ)`, the sc-smooth
retraction `r(t, f) = (t, π_t f)` (`ZhouLine.zhouRetraction`) has the retract
`Y = {(t, 0) | t ≤ 0} ∪ {(t, a β(· + e^{1/t})) | t > 0}` (`mem_O_iff'`), which the text identifies
with `Σ = {(s, t) | t = 0 if s ≤ 0}`.  `G = ℤ/2` acts by `(t, f) ↦ (t, −f)`; with `ℤ/2 = ℤˣ`
written multiplicatively (`0 ↦ 1`, `1 ↦ −1`), the text computes

* `𝐗^T = ({0,1} × {(s, 0) | s < 0}) ∪ ({0} × Σ)`: `nonEffectivePart_eq`, i.e.
  `𝐗^T = ({1} × Y) ∪ ({−1} × {(t, 0) | t < 0})`;
* `cl(𝐗^T) ∖ 𝐗^T = {1} × {(0, 0)}`: `closure_nonEffectivePart_diff`, i.e. `{(−1, (0, 0))}`.

Consequences: `𝐗^R` is not Hausdorff (`not_t2Space_reducedMor`), (LUC) fails (`not_isLUC`, by
Proposition 7.2.21) and (ZHOU) fails (`not_isZhou`, by Proposition 7.4.10).  `appendix_7_6_3`
collects them.  The data (`Data`: the weights `δ_m` and `β`) are those of the text, with `β ≥ 0`
not needed; `Data.std` is one choice (`δ_m = m`, `β` from `ZhouLine.exists_beta`).
-/

open Set Filter Topology
open scoped InnerProductSpace

namespace Polyfold.EpGroupoid.Examples.ZhouRetract

open Polyfold.ZhouLine Polyfold.GapP1Sobolev

noncomputable section

/-- The data of 2021 Appendix 7.6.3 (Subsection 1.4.4, p. 18): weights `0 = δ₀ < δ₁ < ⋯` and a
smooth compactly supported `β` with `∫ β² = 1`. -/
structure Data where
  δ : ℕ → ℝ
  h0 : δ 0 = 0
  hmono : StrictMono δ
  β : ℝ → ℝ
  hβ : IsTest1 β
  hβ2 : ∫ s, β s ^ 2 = 1

/-- One choice of the data: `δ_m = m` and a normalized bump `β ≥ 0`. -/
def Data.std : Data where
  δ m := m
  h0 := Nat.cast_zero
  hmono := Nat.strictMono_cast
  β := Classical.choose exists_beta
  hβ := (Classical.choose_spec exists_beta).1
  hβ2 := (Classical.choose_spec exists_beta).2.2

variable (D : Data)

/-- `E = L²(ℝ)` with `E_m = H^{m,δ_m}(ℝ)`. -/
abbrev Z : ScBanach := lineSc D.δ D.h0 D.hmono

/-- `F = ℝ ⊕ E`. -/
abbrev E : ScBanach := (ScBanach.const ℝ).prod (Z D)

/-- Zhou's retraction `r(t, f) = (t, π_t f)`. -/
def Rt : ScRetraction (E D) univ := zhouRetraction D.h0 D.hmono D.hβ D.hβ2

/-- The retract `Y = r(F)`. -/
abbrev O : Set (E D 0) := (Rt D).retract

/-- `π_t` on level `0`. -/
abbrev pi (t : ℝ) : Z D 0 →L[ℝ] Z D 0 := zhouFam D.h0 D.hmono D.β t 0

lemma mem_O_iff (q : E D 0) : q ∈ O D ↔ pi D q.1 q.2 = q.2 := by
  constructor
  · rintro ⟨p, -, rfl⟩
    exact zhouFam_idem D.h0 D.hmono D.hβ D.hβ2 p.1 p.2
  · intro h
    exact ⟨q, mem_univ _, Prod.ext rfl h⟩

/-- The vector `β(· + e^{1/t})` spanning the fibre over `t > 0`. -/
def w (t : ℝ) : Z D 0 := trH 0 (nonneg_of_strictMono D.h0 D.hmono 0) D.β (Real.exp t⁻¹)

lemma pi_nonpos {t : ℝ} (ht : t ≤ 0) : pi D t = 0 := zhouFam_nonpos D.h0 D.hmono ht 0

lemma pi_apply_pos {t : ℝ} (ht : 0 < t) (f : Z D 0) :
    pi D t f = ⟪tr0 D.β (Real.exp t⁻¹), H1.val (show H1 0 _ from f)⟫_ℝ • w D t := by
  rw [pi, zhouFam_pos D.h0 D.hmono ht]; rfl

lemma pi_w {t : ℝ} (ht : 0 < t) : pi D t (w D t) = w D t := by
  rw [pi_apply_pos D ht]
  change ⟪_, H1.val (trH 0 _ D.β _)⟫_ℝ • w D t = _
  rw [val_trH, inner_tr0_self D.hβ D.hβ2, one_smul]

lemma w_ne_zero (t : ℝ) : w D t ≠ 0 := fun h => by
  have h1 : tr0 D.β (Real.exp t⁻¹) = 0 := by
    rw [← val_trH (m := 0) (hδ := nonneg_of_strictMono D.h0 D.hmono 0)]
    exact congrArg H1.val h
  have := inner_tr0_self D.hβ D.hβ2 (Real.exp t⁻¹)
  rw [h1, inner_zero_left] at this
  exact zero_ne_one this

/-- **The retract as printed**: `Y` is `{(t, 0)}` over `t ≤ 0` and the line
`ℝ · β(· + e^{1/t})` over each `t > 0`. -/
theorem mem_O_iff' (q : E D 0) :
    q ∈ O D ↔ (q.1 ≤ 0 ∧ q.2 = 0) ∨ (0 < q.1 ∧ ∃ a : ℝ, q.2 = a • w D q.1) := by
  rw [mem_O_iff]
  constructor
  · intro h
    rcases le_or_gt q.1 0 with ht | ht
    · refine Or.inl ⟨ht, ?_⟩
      rw [← h, pi_nonpos D ht]; rfl
    · exact Or.inr ⟨ht, _, by rw [← h, pi_apply_pos D ht]⟩
  · rintro (⟨ht, h⟩ | ⟨ht, a, h⟩)
    · rw [h, map_zero]
    · rw [h, map_smul, pi_w D ht]

lemma snd_eq_zero_of_nonpos (p : O D) (hp : p.1.1 ≤ 0) : p.1.2 = 0 := by
  rw [← (mem_O_iff D _).1 p.2, pi_nonpos D hp]; rfl

/-! ### The `ℤ/2`-action -/

/-- `±1` as a real number. -/
def c (k : ℤˣ) : ℝ := ((k : ℤ) : ℝ)

lemma smul_mem (k : ℤˣ) (y : O D) : ((y.1.1, c k • y.1.2) : E D 0) ∈ O D := by
  rw [mem_O_iff]
  change pi D y.1.1 (c k • y.1.2) = c k • y.1.2
  rw [map_smul, (mem_O_iff D _).1 y.2]

/-- `k • (t, f) = (t, ±f)`. -/
def smulO (k : ℤˣ) (y : O D) : O D := ⟨(y.1.1, c k • y.1.2), smul_mem D k y⟩

instance : MulAction ℤˣ (O D) where
  smul := smulO D
  one_smul y := Subtype.ext (Prod.ext rfl (show c 1 • y.1.2 = y.1.2 by simp [c]))
  mul_smul k l y := Subtype.ext (Prod.ext rfl
    (show c (k * l) • y.1.2 = c k • c l • y.1.2 by simp [c, mul_smul]))

lemma zero_mem : (0 : E D 0) ∈ O D := by rw [mem_O_iff]; exact map_zero _

/-- The base point `(0, 0)` of `Y`. -/
def o₀ : O D := ⟨0, zero_mem D⟩

/-- `Y` as an M-polyfold, with its one chart. -/
def P : MPolyfold (O D) := retractPolyfold (Rt D).isScRetract (o₀ D)

/-- `(t, f) ↦ (t, a f)` on `F`. -/
def scaleOp (a : ℝ) : ScOperator (E D) (E D) :=
  ScOperator.prodMap (ScOperator.id _)
    { lvl := fun m => a • ContinuousLinearMap.id ℝ _
      incl_comm := fun m x => by simp }

lemma continuous_smulO (k : ℤˣ) : Continuous fun y : O D => k • y := by
  change Continuous fun y : O D => (⟨(y.1.1, c k • y.1.2), smul_mem D k y⟩ : O D)
  exact Continuous.subtype_mk ((continuous_subtype_val (p := (· ∈ O D))).fst.prodMk
    ((continuous_subtype_val (p := (· ∈ O D))).snd.const_smul (c k))) _

/-- `ℤ/2` acts on `Y` sc-smoothly: `(t, f) ↦ (t, ±f)` is the restriction of an sc-operator. -/
theorem isScSmoothMap_smul (k : ℤˣ) : (P D).IsScSmoothMap (P D) fun y : O D => k • y := by
  refine MPolyfold.IsScSmoothOn.of_exists_charts isOpen_univ (continuous_smulO D k).continuousOn
    fun y _ => ⟨retractChart (Rt D).isScRetract (o₀ D), retractChart (Rt D).isScRetract (o₀ D),
      univ, isChart_retractChart _ _, isChart_retractChart _ _, isOpen_univ, mem_univ _,
      fun z _ => ⟨mem_univ _, mem_univ _⟩, fun z _ => mem_univ _, ?_⟩
  have key : IsScSmoothRetractMap (E D) univ (O D) (E D) univ (O D) (scaleOp D (c k) 0) :=
    (scaleOp D (c k)).isScSmoothRetractMap (Rt D).isScRetract
      (fun q hq => smul_mem D k ⟨q, hq⟩)
  have heq : EqOn (scaleOp D (c k) 0) (⇑(retractChart (Rt D).isScRetract (o₀ D)) ∘
      (fun y : O D => k • y) ∘ (retractChart (Rt D).isScRetract (o₀ D)).symm) (O D) := by
    intro q hq
    have hs : (retractChart (Rt D).isScRetract (o₀ D)).symm q = ⟨q, hq⟩ := by
      classical
      change (if h : q ∈ O D then (⟨q, h⟩ : O D) else o₀ D) = ⟨q, hq⟩
      rw [dif_pos hq]
    change (q.1, c k • q.2) = ((k • (retractChart (Rt D).isScRetract (o₀ D)).symm q : O D) : E D 0)
    rw [hs]
    rfl
  have h2 : IsScSmoothRetractMap (E D) univ (Subtype.val '' (univ : Set (O D))) (E D) univ (O D)
      (⇑(retractChart (Rt D).isScRetract (o₀ D)) ∘ (fun y : O D => k • y) ∘
        (retractChart (Rt D).isScRetract (o₀ D)).symm) := by
    rw [Subtype.coe_image_univ]
    exact key.congr heq
  exact h2

/-- **The ep-groupoid `ℤ/2 ⋉ Y` of 2021 Appendix 7.6.3, p. 348**. -/
abbrev X : EpGroupoid (O D) (ℤˣ × O D) :=
  Examples.actionEpGroupoid (P := P D) (isScSmoothMap_smul D)

lemma smul_eq_self_of_nonpos (k : ℤˣ) (p : O D) (hp : p.1.1 ≤ 0) : k • p = p := by
  apply Subtype.ext
  refine Prod.ext rfl ?_
  change c k • p.1.2 = p.1.2
  rw [snd_eq_zero_of_nonpos D p hp, smul_zero]

/-! ### The non-effective part -/

/-- `(−1, p) ∈ 𝐗^T` for every `p` over `t < 0`. -/
lemma neg_one_mem_nonEffectivePart {p : O D} (hp : p.1.1 < 0) :
    ((-1 : ℤˣ), p) ∈ (X D).nonEffectivePart := by
  rw [EpGroupoid.mem_nonEffectivePart_iff]
  have ho : IsOpen {q : ℤˣ × O D | q.2.1.1 < 0} :=
    isOpen_lt (continuous_fst.comp (continuous_subtype_val.comp continuous_snd)) continuous_const
  filter_upwards [ho.mem_nhds (show p.1.1 < 0 from hp)] with q hq
  exact (smul_eq_self_of_nonpos D q.1 q.2 (le_of_lt hq)).symm

lemma eq_zero_of_eq_neg (z : Z D 0) (hz : z = c (-1) • z) : z = 0 := by
  have h2 : (2 : ℝ) • z = 0 := by
    rw [two_smul]; nth_rw 1 [hz]; simp [c]
  exact (smul_eq_zero.1 h2).resolve_left two_ne_zero

/-- `(−1, p) ∉ 𝐗^T` for every `p` over `t ≥ 0`: either `−1` moves `p`, or `p = (t, 0)` and `−1`
moves the points `(t + 1/(n+1), ε_n β(· + e^{1/(t + 1/(n+1))}))` of `Y`, which tend to `p`. -/
lemma neg_one_not_mem_nonEffectivePart {p : O D} (hp : 0 ≤ p.1.1) :
    ((-1 : ℤˣ), p) ∉ (X D).nonEffectivePart := by
  intro h
  by_cases hz : p.1.2 = 0
  · set tn : ℕ → ℝ := fun n => p.1.1 + 1 / ((n : ℝ) + 1)
    have htn : ∀ n, 0 < tn n := fun n => by simp only [tn]; positivity
    set εn : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1) * (1 / (‖w D (tn n)‖ + 1))
    have hεn : ∀ n, 0 < εn n := fun n => by simp only [εn]; positivity
    have hmem : ∀ n, ((tn n, εn n • w D (tn n)) : E D 0) ∈ O D := fun n => by
      rw [mem_O_iff]
      change pi D (tn n) (εn n • w D (tn n)) = εn n • w D (tn n)
      rw [map_smul, pi_w D (htn n)]
    have hnode : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    have hpt : Tendsto (fun n => (⟨(tn n, εn n • w D (tn n)), hmem n⟩ : O D)) atTop (𝓝 p) := by
      rw [tendsto_subtype_rng]
      have h1 : Tendsto tn atTop (𝓝 p.1.1) := by
        have := (tendsto_const_nhds (x := p.1.1)).add hnode
        rw [add_zero] at this
        exact this
      have h2 : Tendsto (fun n => εn n • w D (tn n)) atTop (𝓝 (0 : Z D 0)) := by
        refine tendsto_zero_iff_norm_tendsto_zero.2 (squeeze_zero (fun _ => norm_nonneg _)
          (fun n => ?_) hnode)
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos (hεn n)]
        simp only [εn]
        have hw : ‖w D (tn n)‖ * (1 / (‖w D (tn n)‖ + 1)) ≤ 1 := by
          rw [mul_one_div, div_le_one (by positivity)]; linarith
        calc 1 / ((n : ℝ) + 1) * (1 / (‖w D (tn n)‖ + 1)) * ‖w D (tn n)‖
            = 1 / ((n : ℝ) + 1) * (‖w D (tn n)‖ * (1 / (‖w D (tn n)‖ + 1))) := by ring
          _ ≤ 1 / ((n : ℝ) + 1) * 1 := mul_le_mul_of_nonneg_left hw (by positivity)
          _ = 1 / ((n : ℝ) + 1) := mul_one _
      have h3 := h1.prodMk_nhds h2
      rw [← hz] at h3
      exact h3
    have h2 : Tendsto (fun n => ((-1 : ℤˣ), (⟨(tn n, εn n • w D (tn n)), hmem n⟩ : O D))) atTop
        (𝓝 ((-1 : ℤˣ), p)) := tendsto_const_nhds.prodMk_nhds hpt
    obtain ⟨n, hn⟩ := (h2.eventually ((EpGroupoid.mem_nonEffectivePart_iff _).1 h)).exists
    have hn' : εn n • w D (tn n) = c (-1) • (εn n • w D (tn n)) :=
      congrArg (fun q : O D => q.1.2) hn
    exact w_ne_zero D (tn n) ((smul_eq_zero.1 (eq_zero_of_eq_neg D _ hn')).resolve_left
      (hεn n).ne')
  · exact hz (eq_zero_of_eq_neg D _
      (congrArg (fun q : O D => q.1.2) (src_eq_tgt_of_mem_nonEffectivePart h)))

/-- **The non-effective part of Zhou's example, exactly** (2021 Appendix 7.6.3, p. 348):
`𝐗^T = ({1} × Y) ∪ ({−1} × {(t, f) ∈ Y | t < 0})`, the text's
`({0,1} × {(s, 0) | s < 0}) ∪ ({0} × Σ)` with `ℤ/2 = {1, −1}` written multiplicatively (over
`t < 0` the points of `Y` are `(t, 0)`, `snd_eq_zero_of_nonpos`). -/
theorem nonEffectivePart_eq :
    (X D).nonEffectivePart = {q | q.1 = 1} ∪ {q | q.1 = -1 ∧ q.2.1.1 < 0} := by
  ext ⟨k, p⟩
  simp only [mem_union, mem_ofPred_eq]
  constructor
  · intro h
    rcases Int.units_eq_one_or k with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr ⟨rfl, not_le.1 fun hp => neg_one_not_mem_nonEffectivePart D hp h⟩
  · rintro (rfl | ⟨rfl, hp⟩)
    · exact (X D).unit_mem_nonEffectivePart p
    · exact neg_one_mem_nonEffectivePart D hp

/-- The points `y_n = (−1/(n+1), 0)` of `Y`. -/
def yn (n : ℕ) : O D := ⟨(-(1 / ((n : ℝ) + 1)), 0), by rw [mem_O_iff]; exact map_zero _⟩

lemma tendsto_yn : Tendsto (yn D) atTop (𝓝 (o₀ D)) := by
  rw [tendsto_subtype_rng]
  have hnode : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have := hnode.neg.prodMk_nhds (tendsto_const_nhds (x := (0 : Z D 0)))
  rw [neg_zero] at this
  exact this

lemma yn_neg (n : ℕ) : (yn D n).1.1 < 0 := neg_neg_of_pos (by positivity)

lemma mem_closure_nonEffectivePart : ((-1 : ℤˣ), o₀ D) ∈ closure (X D).nonEffectivePart :=
  mem_closure_of_tendsto (tendsto_const_nhds.prodMk_nhds (tendsto_yn D))
    (Eventually.of_forall fun n => neg_one_mem_nonEffectivePart D (yn_neg D n))

lemma not_mem_nonEffectivePart : ((-1 : ℤˣ), o₀ D) ∉ (X D).nonEffectivePart :=
  neg_one_not_mem_nonEffectivePart D (le_refl 0)

/-- **`cl(𝐗^T) ∖ 𝐗^T` is one point** (2021 Appendix 7.6.3, p. 348): `(−1, (0, 0))`, the text's
`{1} × {(0, 0)}`. -/
theorem closure_nonEffectivePart_diff :
    closure (X D).nonEffectivePart \ (X D).nonEffectivePart = {((-1 : ℤˣ), o₀ D)} := by
  refine Subset.antisymm ?_ (singleton_subset_iff.2 ⟨mem_closure_nonEffectivePart D,
    not_mem_nonEffectivePart D⟩)
  have hS : IsClosed ({q : ℤˣ × O D | q.1 = 1} ∪ {q | q.2.1.1 ≤ 0}) :=
    (isClosed_eq continuous_fst continuous_const).union
      (isClosed_le (continuous_fst.comp (continuous_subtype_val.comp continuous_snd))
        continuous_const)
  have hsub : (X D).nonEffectivePart ⊆ {q : ℤˣ × O D | q.1 = 1} ∪ {q | q.2.1.1 ≤ 0} := by
    rw [nonEffectivePart_eq]
    exact union_subset_union subset_rfl fun q hq => le_of_lt hq.2
  rintro ⟨k, p⟩ ⟨hcl, hn⟩
  rcases hS.closure_subset_iff.2 hsub hcl with hk | hp
  · exact absurd ((nonEffectivePart_eq D).symm ▸ Or.inl hk :
      ((k, p) : ℤˣ × O D) ∈ (X D).nonEffectivePart) hn
  · change p.1.1 ≤ 0 at hp
    rcases Int.units_eq_one_or k with rfl | rfl
    · exact absurd ((X D).unit_mem_nonEffectivePart p) hn
    · rcases hp.lt_or_eq with hp | hp
      · exact absurd (neg_one_mem_nonEffectivePart D hp) hn
      · exact Prod.ext rfl (Subtype.ext (Prod.ext hp (snd_eq_zero_of_nonpos D p hp.le)))

/-! ### Consequences -/

lemma reducedπ_eq (n : ℕ) :
    (X D).reducedπ ((-1 : ℤˣ), yn D n) = (X D).reducedπ ((1 : ℤˣ), yn D n) := by
  rw [EpGroupoid.reducedπ_eq_iff, EpGroupoid.reducedRel_iff]
  refine ⟨((-1 : ℤˣ), yn D n), neg_one_mem_nonEffectivePart D (yn_neg D n), ?_, ?_⟩
  · change yn D n = (-1 : ℤˣ) • yn D n
    exact (smul_eq_self_of_nonpos D _ _ (yn_neg D n).le).symm
  · change ((-1 : ℤˣ), yn D n) = ((1 : ℤˣ) * (-1), yn D n)
    rw [one_mul]

lemma reducedπ_ne : (X D).reducedπ ((-1 : ℤˣ), o₀ D) ≠ (X D).reducedπ ((1 : ℤˣ), o₀ D) := by
  rw [Ne, EpGroupoid.reducedπ_eq_iff, EpGroupoid.reducedRel_iff]
  rintro ⟨k, hk, -, he⟩
  have he' : ((-1 : ℤˣ), o₀ D) = ((1 : ℤˣ) * k.1, k.2) := he
  rw [one_mul] at he'
  have hk' : k = ((-1 : ℤˣ), o₀ D) := he'.symm
  exact not_mem_nonEffectivePart D (hk' ▸ hk)

/-- **`𝐗^R` is not Hausdorff** for Zhou's example. -/
theorem not_t2Space_reducedMor : ¬ T2Space (X D).ReducedMor := by
  intro _
  have h1 : Tendsto (fun n => (X D).reducedπ ((-1 : ℤˣ), yn D n)) atTop
      (𝓝 ((X D).reducedπ ((-1 : ℤˣ), o₀ D))) :=
    ((X D).continuous_reducedπ.tendsto _).comp (tendsto_const_nhds.prodMk_nhds (tendsto_yn D))
  have h2 : Tendsto (fun n => (X D).reducedπ ((1 : ℤˣ), yn D n)) atTop
      (𝓝 ((X D).reducedπ ((1 : ℤˣ), o₀ D))) :=
    ((X D).continuous_reducedπ.tendsto _).comp (tendsto_const_nhds.prodMk_nhds (tendsto_yn D))
  have h1' : Tendsto (fun n => (X D).reducedπ ((1 : ℤˣ), yn D n)) atTop
      (𝓝 ((X D).reducedπ ((-1 : ℤˣ), o₀ D))) := h1.congr fun n => reducedπ_eq D n
  exact reducedπ_ne D (tendsto_nhds_unique h1' h2)

theorem not_isClosed_nonEffectivePart : ¬ IsClosed (X D).nonEffectivePart := fun h =>
  not_mem_nonEffectivePart D (h.closure_subset (mem_closure_nonEffectivePart D))

/-- **Zhou's example does not have (LUC)** (Proposition 7.2.21: (LUC) iff `𝐗^T` is closed). -/
theorem not_isLUC : ¬ (X D).IsLUC := fun h =>
  not_isClosed_nonEffectivePart D ((X D).proposition_7_2_21.1 h)

/-- **Zhou's example does not satisfy (ZHOU)** (2021 p. 331; Proposition 7.4.10: (ZHOU) ⇒ (LUC)
for an M-polyfold, all of which are `SmoothRegular`). -/
theorem not_isZhou : ¬ (X D).IsZhou := fun h =>
  not_isLUC D ((X D).proposition_7_4_10 (X D).PObj.smoothRegular h)

/-- **2021 Appendix 7.6.3, p. 348, for Zhou's example itself**: for the sc-smooth retraction
`r(t, f) = (t, π_t f)` on `ℝ ⊕ L²(ℝ)` with `ℤ/2` acting by `(t, f) ↦ (t, −f)`, the non-effective
part is `({1} × Y) ∪ ({−1} × {t < 0})` and `cl(𝐗^T) ∖ 𝐗^T = {(−1, (0, 0))}`, as the text computes;
`𝐗^R` is not Hausdorff and (LUC) and (ZHOU) fail. -/
theorem appendix_7_6_3 :
    (X D).nonEffectivePart = {q | q.1 = 1} ∪ {q | q.1 = -1 ∧ q.2.1.1 < 0} ∧
    closure (X D).nonEffectivePart \ (X D).nonEffectivePart = {((-1 : ℤˣ), o₀ D)} ∧
    ¬ T2Space (X D).ReducedMor ∧ ¬ (X D).IsLUC ∧ ¬ (X D).IsZhou :=
  ⟨nonEffectivePart_eq D, closure_nonEffectivePart_diff D, not_t2Space_reducedMor D, not_isLUC D,
    not_isZhou D⟩

end

end Polyfold.EpGroupoid.Examples.ZhouRetract
