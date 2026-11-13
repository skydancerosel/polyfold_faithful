import Polyfold.Chapter5.BonicFrampton
import Polyfold.Chapter5.PartitionsOfUnity

/-!
# The `Lᵖ` and Sobolev remark after Theorem 5.5.5 (2021, pp. 230–231): the abstract part

Hofer–Wysocki–Zehnder, 2021 §5.5, the remark after Theorem 5.5.5 (preprint after Theorem 5.32,
pp. 193–194).  The text deduces from the Bonic–Frampton theorem that

* the usual norms of `W^{k,p}(Ω)`, `‖u‖ᵖ = ∑_{|α| ≤ k} ‖D^α u‖ᵖ_{Lᵖ}`, have the differentiability
  of `‖·‖_{Lᵖ}`;
* `f(x) = β(‖x‖ᵖ)`, `β` a smooth function of compact support, is a bump function of `Lᵖ` whose
  smoothness is that of Theorem 5.5.5;
* consequences for sc-structures: `W^{1,4}(Ω)` with `E_m = W^{1+m,4}(Ω)` admits sc-smooth bump
  functions; for `W^{1,3/2}(Ω)` the straightforward bump is only sc¹.

This file proves the abstract part, for any normed space whose norm has the form
`‖u‖ᵖ = ∑ᵢ ‖Tᵢ u‖ᵖ_{Lᵖ}` with finitely many continuous linear `Tᵢ` (as the Sobolev norms do, with
`Tᵢ = D^α`):

* `contDiff_rpow_norm_of_sum`, `theorem_5_5_5_sum`: such a norm has the differentiability of the
  `Lᵖ` norm, in the three cases of Theorem 5.5.5;
* `bump_comp_rpow`: `β(‖x‖ᵖ)` is `C^n`, nonzero at `0`, of bounded support, for every `C^n` `β`
  of compact support with `β(0) ≠ 0`; `hasContDiffBump_of_rpow`, `hasContDiffBump_sum_cases`,
  `hasContDiffBump_Lp` (the three cases for `Lᵖ`);
* `HasContDiffBump.of_equiv` (transport along a linear isomorphism);
* the sc-consequences: `LocalModel.hasBumpProperty_of_hasContDiffBump` (a `C^∞` bump on `E₀` gives
  the sc-smooth bump function property of every local model on `E`, "by rescaling and
  translating", as in Proposition 5.5.8), its M-polyfold form
  `MPolyfold.admitsBumpFunctions_of_hasContDiffBump`, and `exists_isSck_bump` (a `C^{k+1}` bump on
  `E₀` is an sc^{k+1} function on `E`, Corollary 1.2.5).
-/

open MeasureTheory Set Function
open scoped ENNReal ContDiff

noncomputable section

namespace Polyfold

namespace SobolevRemark

/-! ### Norms that are sums of `Lᵖ` norms -/

section SumNorm

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {ι : Type*} [Fintype ι]
  {p : ℝ} [Fact (1 ≤ ENNReal.ofReal p)]

/-- If `‖u‖ᵖ = ∑ᵢ ‖Tᵢ u‖ᵖ` for continuous linear `Tᵢ : E → Lᵖ(μ)`, then `u ↦ ‖u‖ᵖ` is as
differentiable as `‖·‖ᵖ` on `Lᵖ(μ)`. -/
theorem contDiff_rpow_norm_of_sum (T : ι → E →L[ℝ] Lp ℝ (ENNReal.ofReal p) μ)
    (hT : ∀ u, ‖u‖ ^ p = ∑ i, ‖T i u‖ ^ p) {n : WithTop ℕ∞}
    (h : ContDiff ℝ n (fun f : Lp ℝ (ENNReal.ofReal p) μ => ‖f‖ ^ p)) :
    ContDiff ℝ n (fun u : E => ‖u‖ ^ p) := by
  have e : (fun u : E => ‖u‖ ^ p) = fun u => ∑ i, ‖T i u‖ ^ p := funext hT
  rw [e]
  exact ContDiff.sum fun i _ => h.comp (T i).contDiff

/-- **2021, p. 230 (preprint p. 193), the Sobolev sentence after Theorem 5.5.5**, for any norm of
the form `‖u‖ᵖ = ∑ᵢ ‖Tᵢ u‖ᵖ_{Lᵖ}`: it has the differentiability of `‖·‖_{Lᵖ}` in Theorem 5.5.5,
i.e. `‖·‖ᵖ` is `C^∞` for `p` even, `C^{p−1}` for `p` odd, and `C^{[p]}` for `p` not an integer. -/
theorem theorem_5_5_5_sum (T : ι → E →L[ℝ] Lp ℝ (ENNReal.ofReal p) μ)
    (hT : ∀ u, ‖u‖ ^ p = ∑ i, ‖T i u‖ ^ p) :
    ((∃ k : ℕ, p = 2 * k) → ContDiff ℝ (⊤ : ℕ∞) (fun u : E => ‖u‖ ^ p)) ∧
      (∀ k : ℕ, p = 2 * k + 1 → ContDiff ℝ ((2 * k : ℕ) : ℕ∞) (fun u : E => ‖u‖ ^ p)) ∧
      ((∀ k : ℕ, p ≠ k) → ContDiff ℝ (⌊p⌋₊ : ℕ∞) (fun u : E => ‖u‖ ^ p)) := by
  obtain ⟨h1, h2, h3⟩ := BonicFrampton.theorem_5_5_5 (μ := μ) p
  exact ⟨fun h => contDiff_rpow_norm_of_sum T hT (h1 h),
    fun k hk => contDiff_rpow_norm_of_sum T hT (h2 k hk),
    fun h => contDiff_rpow_norm_of_sum T hT (h3 h)⟩

end SumNorm

/-! ### Bump functions `β(‖x‖ᵖ)` -/

section Bump

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

omit [NormedSpace ℝ E] in
/-- The support of `β(‖x‖ᵖ)` is bounded when `β` has compact support. -/
lemma isBounded_support_comp_rpow {p : ℝ} (hp : 0 < p) {β : ℝ → ℝ} (hβc : HasCompactSupport β) :
    Bornology.IsBounded (support fun u : E => β (‖u‖ ^ p)) := by
  obtain ⟨R, hR⟩ := hβc.isBounded.subset_closedBall 0
  refine (Metric.isBounded_closedBall (x := (0 : E)) (r := R ^ p⁻¹)).subset fun u hu => ?_
  have h1 : ‖u‖ ^ p ∈ Metric.closedBall (0 : ℝ) R := hR (subset_tsupport _ hu)
  rw [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg (norm_nonneg u) p)] at h1
  rw [Metric.mem_closedBall, dist_zero_right]
  have h2 := Real.rpow_le_rpow (Real.rpow_nonneg (norm_nonneg u) p) h1 (inv_nonneg.2 hp.le)
  rwa [Real.rpow_rpow_inv (norm_nonneg u) hp.ne'] at h2

/-- **The bump function `β(‖x‖ᵖ)`** (2021, p. 230): if `‖·‖ᵖ` is `C^n` and `β : ℝ → ℝ` is `C^n`
with compact support and `β(0) ≠ 0`, then `f(x) = β(‖x‖ᵖ)` is `C^n`, nonzero at `0`, with bounded
support. -/
theorem bump_comp_rpow {p : ℝ} (hp : 0 < p) {n : WithTop ℕ∞}
    (hN : ContDiff ℝ n (fun u : E => ‖u‖ ^ p)) {β : ℝ → ℝ} (hβ : ContDiff ℝ n β)
    (hβc : HasCompactSupport β) (hβ0 : β 0 ≠ 0) :
    ContDiff ℝ n (fun u : E => β (‖u‖ ^ p)) ∧ β (‖(0 : E)‖ ^ p) ≠ 0 ∧
      Bornology.IsBounded (support fun u : E => β (‖u‖ ^ p)) := by
  refine ⟨hβ.comp hN, ?_, isBounded_support_comp_rpow hp hβc⟩
  rwa [norm_zero, Real.zero_rpow hp.ne']

/-- A smooth function `β : ℝ → ℝ` of compact support with `β(0) = 1`. -/
lemma exists_smooth_compact_one :
    ∃ β : ℝ → ℝ, ContDiff ℝ ∞ β ∧ HasCompactSupport β ∧ β 0 = 1 := by
  let b : ContDiffBump (0 : ℝ) := ⟨1, 2, one_pos, one_lt_two⟩
  exact ⟨b, b.contDiff, b.hasCompactSupport,
    b.one_of_mem_closedBall (Metric.mem_closedBall_self b.rIn_pos.le)⟩

/-- If `‖·‖ᵖ` is `C^k` on `E`, then `E` admits a `C^k`-bump function (Definition 5.5.4):
`β(‖x‖ᵖ)`. -/
theorem hasContDiffBump_of_rpow {p : ℝ} (hp : 0 < p) {k : ℕ∞}
    (hN : ContDiff ℝ k (fun u : E => ‖u‖ ^ p)) : HasContDiffBump E k := by
  obtain ⟨β, hβ, hβc, hβ0⟩ := exists_smooth_compact_one
  obtain ⟨h1, h2, h3⟩ := bump_comp_rpow hp hN (hβ.of_le (WithTop.coe_le_coe.2 le_top)) hβc
    (by rw [hβ0]; exact one_ne_zero)
  exact ⟨_, h1, fun h => h2 (congrFun h 0), h3⟩

/-- **Transport of bump functions** along a continuous linear isomorphism. -/
theorem _root_.Polyfold.HasContDiffBump.of_equiv {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] (e : E ≃L[ℝ] F) {k : ℕ∞} (h : HasContDiffBump F k) : HasContDiffBump E k := by
  obtain ⟨f, hf, hf0, hfb⟩ := h
  refine ⟨f ∘ e, hf.comp e.contDiff, fun h0 => hf0 (funext fun y => ?_), ?_⟩
  · simpa using congrFun h0 (e.symm y)
  · have : support (f ∘ e) = e.symm '' support f := by
      ext u
      simp only [mem_support, comp_apply, mem_image]
      exact ⟨fun hu => ⟨e u, hu, e.symm_apply_apply u⟩,
        fun ⟨y, hy, hyu⟩ => by rw [← hyu, e.apply_symm_apply]; exact hy⟩
    rw [this]
    exact (e.symm : F →L[ℝ] E).lipschitz.isBounded_image hfb

end Bump

/-! ### The three cases for norms of Sobolev type, and for `Lᵖ` -/

section Cases

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {ι : Type*} [Fintype ι]
  {p : ℝ} [Fact (1 ≤ ENNReal.ofReal p)]

/-- **Bump functions for norms of Sobolev type** (2021, p. 230): if `‖u‖ᵖ = ∑ᵢ ‖Tᵢ u‖ᵖ_{Lᵖ}`, then
`E` admits a `C^∞`-bump for `p` even, a `C^{p−1}`-bump for `p` odd and a `C^{[p]}`-bump for `p`
not an integer, namely `β(‖x‖ᵖ)`. -/
theorem hasContDiffBump_sum_cases (T : ι → E →L[ℝ] Lp ℝ (ENNReal.ofReal p) μ)
    (hT : ∀ u, ‖u‖ ^ p = ∑ i, ‖T i u‖ ^ p) :
    ((∃ k : ℕ, p = 2 * k) → HasContDiffBump E ⊤) ∧
      (∀ k : ℕ, p = 2 * k + 1 → HasContDiffBump E (2 * k : ℕ)) ∧
      ((∀ k : ℕ, p ≠ k) → HasContDiffBump E ⌊p⌋₊) := by
  have hp : 0 < p := BonicFrampton.p_pos
  obtain ⟨h1, h2, h3⟩ := theorem_5_5_5_sum T hT
  exact ⟨fun h => hasContDiffBump_of_rpow hp (h1 h),
    fun k hk => hasContDiffBump_of_rpow hp (h2 k hk),
    fun h => hasContDiffBump_of_rpow hp (h3 h)⟩

/-- **2021, p. 230 (preprint p. 193): `β(‖x‖ᵖ)` is a bump function of `Lᵖ`** whose smoothness is
that of Theorem 5.5.5: `Lᵖ(μ)` admits a `C^∞`-bump for `p` even, a `C^{p−1}`-bump for `p` odd and
a `C^{[p]}`-bump for `p ≥ 1` not an integer. -/
theorem hasContDiffBump_Lp :
    ((∃ k : ℕ, p = 2 * k) → HasContDiffBump (Lp ℝ (ENNReal.ofReal p) μ) ⊤) ∧
      (∀ k : ℕ, p = 2 * k + 1 → HasContDiffBump (Lp ℝ (ENNReal.ofReal p) μ) (2 * k : ℕ)) ∧
      ((∀ k : ℕ, p ≠ k) → HasContDiffBump (Lp ℝ (ENNReal.ofReal p) μ) ⌊p⌋₊) :=
  hasContDiffBump_sum_cases (ι := Unit) (fun _ => ContinuousLinearMap.id ℝ _)
    (fun u => by simp)

end Cases

end SobolevRemark

/-! ### Consequences for sc-structures -/

section Sc

variable {X : Type*} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}

/-- **A `C^∞` bump on `E₀` gives the sc-smooth bump function property** (Definition 5.5.6) of every
local model on `E`: rescale and translate the bump to `x`, as in the proof of Proposition 5.5.8;
the function is `C^∞` on `E₀`, hence sc-smooth (Corollary 1.2.5), and composed with the
retraction. -/
theorem LocalModel.hasBumpProperty_of_hasContDiffBump (M : LocalModel)
    (h : HasContDiffBump (M.E 0) ⊤) : M.HasBumpProperty := by
  obtain ⟨f₀, hf₀, hf₀0, hf₀b⟩ := h
  obtain ⟨a, ha⟩ : ∃ a, f₀ a ≠ 0 := by
    by_contra hne
    exact hf₀0 (funext fun a => by_contra fun h => hne ⟨a, h⟩)
  obtain ⟨R, hR⟩ := hf₀b.subset_ball 0
  intro x _ W hW hxW _
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 hW x hxW
  have hR0 : 0 < R := by
    have : a ∈ Metric.ball (0 : M.E 0) R := hR ha
    exact lt_of_le_of_lt (norm_nonneg a) (by simpa using this)
  set c : ℝ := 2 * (R + ‖a‖) / r with hc
  have hcpos : 0 < c := by positivity
  set f : M.E 0 → ℝ := fun v => f₀ (a + c • (v - x)) with hf
  have hfc : ContDiff ℝ ∞ f :=
    hf₀.comp (contDiff_const.add (contDiff_const.smul (contDiff_id.sub contDiff_const)))
  have hfsc : IsScSmooth (E := M.E) (F := realSc) univ f :=
    IsScSmooth.of_contDiffOn_finiteDimensional (V := ℝ) (isScDomain_univ _) hfc.contDiffOn
  refine ⟨f, ⟨mapsTo_univ _ _, fun R _ => IsScSmooth.comp R.isScDomain (isScDomain_univ _) hfsc
    R.isScSmooth (mapsTo_univ _ _)⟩, ?_, ?_⟩
  · simpa [hf] using ha
  · have hsupp : support f ⊆ Metric.ball x (r / 2) := by
      intro v hv
      have h1 : ‖a + c • (v - x)‖ < R := by simpa using hR hv
      have h2 : c * ‖v - x‖ < R + ‖a‖ := by
        have : ‖c • (v - x)‖ ≤ ‖a + c • (v - x)‖ + ‖a‖ := by
          have := norm_sub_le (a + c • (v - x)) a
          simpa using this
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos hcpos] at this
        linarith
      have h3 : ‖v - x‖ < r / 2 := by
        rw [hc] at h2
        have hRa : 0 < R + ‖a‖ := by positivity
        have : 2 * (R + ‖a‖) / r * ‖v - x‖ < R + ‖a‖ := h2
        rw [div_mul_eq_mul_div, div_lt_iff₀ hr] at this
        nlinarith
      rw [Metric.mem_ball, dist_eq_norm]; exact h3
    intro q hq
    have h1 : q ∈ Metric.closedBall x (r / 2) :=
      ((closure_mono (inter_subset_right.trans hsupp)).trans
        Metric.closure_ball_subset_closedBall) hq.1
    exact hball (Metric.closedBall_subset_ball (by linarith) h1)

/-- **M-polyfolds whose charts have `C^∞` bumps on `E₀` admit sc-smooth bump functions**
(Theorem 5.5.7 with `LocalModel.hasBumpProperty_of_hasContDiffBump`). -/
theorem MPolyfold.admitsBumpFunctions_of_hasContDiffBump
    (h : ∀ x, ∃ φ : MChart X, PX.IsChart φ ∧ x ∈ φ.source ∧ HasContDiffBump (φ.model.E 0) ⊤) :
    PX.AdmitsBumpFunctions := by
  refine theorem_5_5_7.2 ⟨{φ | PX.IsChart φ ∧ HasContDiffBump (φ.model.E 0) ⊤},
    fun φ hφ => hφ.1, fun x => ?_, fun φ hφ => φ.model.hasBumpProperty_of_hasContDiffBump hφ.2⟩
  obtain ⟨φ, hφ, hx, hb⟩ := h x
  exact ⟨φ, ⟨hφ, hb⟩, hx⟩

/-- **A `C^{k+1}` bump on `E₀` is an sc^{k+1} bump on `E`** (Corollary 1.2.5): the function is
sc^{k+1} on `E`, not identically zero, with support bounded in `E₀`. -/
theorem exists_isSck_bump (E : ScBanach) {k : ℕ} (h : HasContDiffBump (E 0) (k + 1 : ℕ)) :
    ∃ f : E 0 → ℝ, IsSck (k + 1) E realSc univ f ∧ f ≠ 0 ∧ Bornology.IsBounded (support f) := by
  obtain ⟨f, hf, hf0, hfb⟩ := h
  refine ⟨f, corollary_1_2_5_base (V := ℝ) (isScDomain_univ _) ?_, hf0, hfb⟩
  exact (by exact_mod_cast hf : ContDiff ℝ ((k : WithTop ℕ∞) + 1) f).contDiffOn

end Sc

end Polyfold
