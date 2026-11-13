import Polyfold.Chapter7.LineTranslates
import Polyfold.Chapter7.FlatGluing
import Polyfold.Chapter4.RemarkFourThreeExample

/-!
# Appendix 7.6.3 (2021, p. 348): Zhou's sc-smooth retraction

The 2021 book (Appendix 7.6.3, p. 348, from Part I's Subsection 1.4.4, p. 18) takes the
sc-Hilbert space `E = L²(ℝ)`, `E_m = H^{m,δ_m}(ℝ)` with `0 = δ₀ < δ₁ < ⋯` (`lineSc`), a smooth
compactly supported `β` with `∫ β² = 1`, and on `F = ℝ ⊕ E` the map `r(t, f) = (t, π_t f)` with
`π_t = 0` for `t ≤ 0` and `π_t f = ⟨f, β(· + e^{1/t})⟩ β(· + e^{1/t})` for `t > 0`.

* `zhouFam`: the level operators `π_t : E_m → E_m`.
* `isLossFamily_zhouFam`: they form a loss family (`IsLossFamily`, Remark 4.1.3's criterion):
  compatible with the inclusions, jointly continuous in `(t, f)`, and `t ↦ π_t ∘ ι : E_{m+1} → E_m`
  is `C^∞` in the operator norm.  The last point is the flatness at `t = 0`: the `c`-derivatives of
  `c ↦ ⟨·, β^{(i)}(· + c)⟩ β^{(j)}(· + c)` from `H^{m+1,δ_{m+1}}` to `H^{m,δ_m}` decay like
  `e^{-(δ_{m+1} - δ_m)c}` (`norm_iteratedFDeriv_zhouQ_le`), so `t ↦ Q(e^{1/t})` is flat
  (`ZhouFlat.contDiff_flat_comp`).
* `zhouRetraction`: `r` is an sc-smooth retraction of `ℝ ⊕ E` (`zhouRetraction_apply`: the
  formula as printed).
* `exists_beta`: a `β ≥ 0` with the book's properties exists.
-/

open MeasureTheory Set Filter Topology
open scoped ContDiff ENNReal InnerProductSpace

noncomputable section

namespace Polyfold.ZhouLine

open Polyfold.GapP1Sobolev Polyfold.ZhouFlat

/-! ### Joint continuity from a uniform bound and a dense set -/

/-- If `‖A t‖ ≤ K` for all `t` and `t ↦ A t ∘ ι` is continuous for a map `ι` of dense range,
then `(t, x) ↦ A t x` is continuous. -/
lemma continuous_apply_of_dense {E E' F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup E'] [NormedSpace ℝ E'] [NormedAddCommGroup F] [NormedSpace ℝ F]
    (A : ℝ → E →L[ℝ] F) (ι : E' →L[ℝ] E) (hι : DenseRange ι) {K : ℝ} (hK : ∀ t, ‖A t‖ ≤ K)
    (hc : Continuous fun t => (A t).comp ι) : Continuous fun q : ℝ × E => A q.1 q.2 := by
  rw [Metric.continuous_iff]
  rintro ⟨t0, x0⟩ ε hε
  have hK0 : 0 ≤ K := (norm_nonneg _).trans (hK 0)
  set η := ε / (4 * (K + 1)) with hη_def
  have hη : 0 < η := by positivity
  obtain ⟨_, hy, g, rfl⟩ := Metric.dense_iff.1 hι x0 η hη
  rw [Metric.mem_ball] at hy
  set s := ε / (4 * (‖g‖ + 1)) with hs_def
  have hs : 0 < s := by positivity
  obtain ⟨ρ, hρ, hρ'⟩ := Metric.continuous_iff.1 hc t0 s hs
  refine ⟨min ρ η, lt_min hρ hη, ?_⟩
  rintro ⟨t, x⟩ hq
  rw [Prod.dist_eq, max_lt_iff] at hq
  obtain ⟨ht, hx⟩ := hq
  have ht' : dist t t0 < ρ := ht.trans_le (min_le_left _ _)
  have hx' : dist x x0 < η := hx.trans_le (min_le_right _ _)
  rw [dist_eq_norm] at hx' hy
  have h1 : ‖A t (x - ι g)‖ ≤ K * (2 * η) := by
    refine ((A t).le_opNorm _).trans (mul_le_mul (hK t) ?_ (norm_nonneg _) hK0)
    have := norm_sub_le_norm_sub_add_norm_sub x x0 (ι g)
    rw [norm_sub_rev x0] at this
    linarith
  have h2 : ‖((A t).comp ι - (A t0).comp ι) g‖ ≤ s * ‖g‖ := by
    refine (ContinuousLinearMap.le_opNorm _ _).trans (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _))
    rw [← dist_eq_norm]; exact (hρ' t ht').le
  have h3 : ‖A t0 (ι g - x0)‖ ≤ K * η :=
    ((A t0).le_opNorm _).trans (mul_le_mul (hK t0) hy.le (norm_nonneg _) hK0)
  have e : A t x - A t0 x0 = A t (x - ι g) + ((A t).comp ι - (A t0).comp ι) g + A t0 (ι g - x0) := by
    simp only [map_sub, FunLike.coe_sub, Pi.sub_apply, ContinuousLinearMap.comp_apply]
    abel
  have hKη : K * η * 4 ≤ ε := by
    have : η * (4 * (K + 1)) = ε := by rw [hη_def]; field_simp
    nlinarith
  have hsg : s * ‖g‖ * 4 < ε := by
    have : s * (4 * (‖g‖ + 1)) = ε := by rw [hs_def]; field_simp
    nlinarith
  change dist (A t x) (A t0 x0) < ε
  rw [dist_eq_norm, e]
  calc _ ≤ ‖A t (x - ι g)‖ + ‖((A t).comp ι - (A t0).comp ι) g‖ + ‖A t0 (ι g - x0)‖ :=
        norm_add₃_le
    _ < ε := by nlinarith

/-! ### The rank-one projections -/

variable {m : ℕ} {δ : ℝ} {hδ : 0 ≤ δ}

/-- `f ↦ ⟨χ(· + c), f⟩ χ(· + c)` on `H^{m,δ}(ℝ)`. -/
def proj (m : ℕ) {δ : ℝ} (hδ : 0 ≤ δ) (χ : ℝ → ℝ) (c : ℝ) : H1 m hδ →L[ℝ] H1 m hδ :=
  (ellT m hδ χ c).smulRight (trH m hδ χ c)

lemma proj_apply (χ : ℝ → ℝ) (c : ℝ) (f : H1 m hδ) :
    proj m hδ χ c f = ⟪tr0 χ c, H1.val f⟫_ℝ • trH m hδ χ c := rfl

lemma val_proj (χ : ℝ → ℝ) (c : ℝ) (f : H1 m hδ) :
    H1.val (proj m hδ χ c f) = ⟪tr0 χ c, H1.val f⟫_ℝ • tr0 χ c := by
  rw [proj_apply, ← val_trH (m := m) (hδ := hδ)]; rfl

/-- `‖⟨χ₁(· + c), ·⟩‖ ‖χ₂(· + c)‖ ≤ K e^{-(δ' - δ)c}` from `H^{m',δ'}(ℝ)` to `H^{m,δ}(ℝ)`, `c ≥ 0`. -/
lemma norm_mul_norm_le {m' : ℕ} {δ' : ℝ} {hδ' : 0 ≤ δ'} {χ₁ χ₂ : ℝ → ℝ} (h₁ : IsTest1 χ₁)
    (h₂ : IsTest1 χ₂) {R M : ℝ} (hR0 : 0 ≤ R) (hR₁ : ∀ s, R ≤ |s| → χ₁ s = 0)
    (hR₂ : ∀ s, R ≤ |s| → χ₂ s = 0) (hM0 : 0 ≤ M) (hM₁ : ∀ s, |χ₁ s| ≤ M)
    (hM₂ : ∀ i ≤ m, ∀ s, |iteratedDeriv i χ₂ s| ≤ M) {c : ℝ} (hc : 0 ≤ c) :
    ‖ellT m' hδ' χ₁ c‖ * ‖trH m hδ χ₂ c‖ ≤
      ((idx m).card * (Real.exp ((δ' + δ) * R) * M ^ 2 * (2 * R))) *
        Real.exp (-((δ' - δ) * c)) := by
  calc _ ≤ ((Real.exp (-(δ' * (c - R))) * M) * Real.sqrt (2 * R)) *
        ((idx m).card * ((Real.exp (δ * (|c| + R)) * M) * Real.sqrt (2 * R))) :=
        mul_le_mul (norm_ellL_tr0_le h₁ hR0 hR₁ hM0 hM₁ c) (norm_trH_le h₂ hR0 hR₂ hM0 hM₂ c)
          (norm_nonneg _) (by positivity)
    _ = _ := by
        rw [abs_of_nonneg hc]
        have hs := Real.mul_self_sqrt (show 0 ≤ 2 * R by positivity)
        have he : Real.exp (-(δ' * (c - R))) * Real.exp (δ * (c + R)) =
            Real.exp ((δ' + δ) * R) * Real.exp (-((δ' - δ) * c)) := by
          rw [← Real.exp_add, ← Real.exp_add]; ring_nf
        calc _ = (idx m).card * M ^ 2 * (Real.sqrt (2 * R) * Real.sqrt (2 * R)) *
              (Real.exp (-(δ' * (c - R))) * Real.exp (δ * (c + R))) := by ring
          _ = _ := by rw [hs, he]; ring

/-- `‖⟨χ(· + c), ·⟩ χ(· + c)‖ ≤ K` on `H^{m,δ}(ℝ)` for `c ≥ 0`. -/
lemma norm_proj_le {χ : ℝ → ℝ} (h : IsTest1 χ) {R M : ℝ} (hR0 : 0 ≤ R)
    (hR : ∀ s, R ≤ |s| → χ s = 0) (hM0 : 0 ≤ M) (hM : ∀ i ≤ m, ∀ s, |iteratedDeriv i χ s| ≤ M)
    {c : ℝ} (hc : 0 ≤ c) :
    ‖proj m hδ χ c‖ ≤ (idx m).card * (Real.exp ((δ + δ) * R) * M ^ 2 * (2 * R)) := by
  rw [proj, ContinuousLinearMap.norm_smulRight_apply]
  have := norm_mul_norm_le (m' := m) (hδ' := hδ) (hδ := hδ) h h hR0 hR hR hM0
    (fun s => by simpa using hM 0 (Nat.zero_le _) s) hM hc
  rwa [sub_self, zero_mul, neg_zero, Real.exp_zero, mul_one] at this

/-! ### The family `π_t` -/

section Family

variable {δs : ℕ → ℝ} (h0 : δs 0 = 0) (hmono : StrictMono δs) {β : ℝ → ℝ}

/-- **The level operators `π_t : E_m → E_m` of 2021 Appendix 7.6.3, p. 348** (Subsection 1.4.4,
p. 18): `π_t = 0` for `t ≤ 0` and `π_t f = ⟨f, β(· + e^{1/t})⟩ β(· + e^{1/t})` for `t > 0`, on
`E_m = H^{m,δ_m}(ℝ)`. -/
def zhouFam (β : ℝ → ℝ) (t : ℝ) (m : ℕ) : lineSc δs h0 hmono m →L[ℝ] lineSc δs h0 hmono m :=
  if 0 < t then proj m (nonneg_of_strictMono h0 hmono m) β (Real.exp t⁻¹) else 0

lemma zhouFam_pos {t : ℝ} (ht : 0 < t) (m : ℕ) :
    zhouFam h0 hmono β t m = proj m (nonneg_of_strictMono h0 hmono m) β (Real.exp t⁻¹) :=
  if_pos ht

lemma zhouFam_nonpos {t : ℝ} (ht : t ≤ 0) (m : ℕ) : zhouFam h0 hmono β t m = 0 :=
  if_neg (not_lt.2 ht)

lemma val_zhouFam (t : ℝ) (m : ℕ) (f : lineSc δs h0 hmono m) :
    H1.val (show H1 m (nonneg_of_strictMono h0 hmono m) from zhouFam h0 hmono β t m f) =
      if 0 < t then ⟪tr0 β (Real.exp t⁻¹), H1.val (show H1 m _ from f)⟫_ℝ • tr0 β (Real.exp t⁻¹)
      else 0 := by
  by_cases ht : 0 < t
  · rw [if_pos ht, zhouFam_pos h0 hmono ht]; exact val_proj _ _ _
  · rw [if_neg ht, zhouFam_nonpos h0 hmono (not_lt.1 ht)]; rfl

lemma zhouFam_toBase (t : ℝ) (m : ℕ) (f : lineSc δs h0 hmono m) :
    (lineSc δs h0 hmono).toBase m (zhouFam h0 hmono β t m f) =
      zhouFam h0 hmono β t 0 ((lineSc δs h0 hmono).toBase m f) := by
  refine H1.val_injective ?_
  have e1 := val_toBase δs h0 hmono m (zhouFam h0 hmono β t m f)
  have e2 := val_toBase δs h0 hmono m f
  change H1.val ((lineScale δs h0 hmono).toBase m _) = _
  rw [e1]
  rw [val_zhouFam, val_zhouFam]
  change _ = if 0 < t then ⟪_, H1.val ((lineScale δs h0 hmono).toBase m f)⟫_ℝ • _ else 0
  rw [e2]

/-- The incoming loss map `Q(c) = ⟨·, β(· + c)⟩ β(· + c) : E_{m+1} → E_m`. -/
def zhouQ (β : ℝ → ℝ) (m : ℕ) (c : ℝ) :
    lineSc δs h0 hmono (m + 1) →L[ℝ] lineSc δs h0 hmono m :=
  ContinuousLinearMap.smulRightL ℝ (H1 (m + 1) (nonneg_of_strictMono h0 hmono (m + 1)))
    (H1 m (nonneg_of_strictMono h0 hmono m))
    (ellT (m + 1) (nonneg_of_strictMono h0 hmono (m + 1)) β c)
    (trH m (nonneg_of_strictMono h0 hmono m) β c)

lemma zhouFam_comp_incl (t : ℝ) (m : ℕ) :
    (zhouFam h0 hmono β t m).comp ((lineSc δs h0 hmono).incl m) =
      if 0 < t then zhouQ h0 hmono β m (Real.exp t⁻¹) else 0 := by
  by_cases ht : 0 < t
  · rw [if_pos ht, zhouFam_pos h0 hmono ht]; rfl
  · rw [if_neg ht, zhouFam_nonpos h0 hmono (not_lt.1 ht)]; exact ContinuousLinearMap.zero_comp _

variable (hβ : IsTest1 β)
include hβ

lemma contDiff_zhouQ (m : ℕ) : ContDiff ℝ ∞ (zhouQ h0 hmono β m) :=
  (ContinuousLinearMap.isBoundedBilinearMap _).contDiff.comp
    ((contDiff_ellT hβ).prodMk (contDiff_trH hβ))

/-- **The flatness estimate**: `‖D^n Q(c)‖ ≤ K e^{-(δ_{m+1} - δ_m)c}` for `c ≥ 0`. -/
theorem norm_iteratedFDeriv_zhouQ_le (m n : ℕ) :
    ∃ K : ℝ, ∀ c, 0 ≤ c → ‖iteratedFDeriv ℝ n (zhouQ h0 hmono β m) c‖ ≤
      K * Real.exp (-((δs (m + 1) - δs m) * c)) := by
  obtain ⟨R, hR0, hR⟩ := hβ.bdd
  obtain ⟨M, hM⟩ := bdd_iteratedDeriv hβ.smooth (win_hasCompactSupport hR) (n + m)
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0 (Nat.zero_le _) 0)
  set K1 : ℝ := (idx m).card *
    (Real.exp ((δs (m + 1) + δs m) * (R + 1)) * M ^ 2 * (2 * (R + 1)))
  refine ⟨(∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ)) * K1, fun c hc => ?_⟩
  have hR' : ∀ i : ℕ, ∀ s, R + 1 ≤ |s| → iteratedDeriv i β s = 0 := fun i s hs =>
    win_deriv_zero hR i (by linarith)
  refine (ContinuousLinearMap.norm_iteratedFDeriv_le_of_bilinear_of_le_one _ (contDiff_ellT hβ)
    (contDiff_trH hβ) c (by exact_mod_cast le_top) (ContinuousLinearMap.norm_smulRightL_le)).trans ?_
  rw [Finset.sum_mul, Finset.sum_mul]
  refine Finset.sum_le_sum fun i hi => ?_
  have hi' : i ≤ n := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, norm_iteratedFDeriv_eq_norm_iteratedDeriv,
    iteratedDeriv_ellT hβ, iteratedDeriv_trH hβ, mul_assoc, mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
  refine norm_mul_norm_le (hβ.iteratedDeriv i) (hβ.iteratedDeriv (n - i)) (by linarith)
    (hR' i) (hR' (n - i)) hM0 (fun s => hM i (by omega) s) (fun k hk s => ?_) hc
  rw [iteratedDeriv_eq_iterate, iteratedDeriv_eq_iterate, ← Function.iterate_add_apply,
    ← iteratedDeriv_eq_iterate]
  exact hM _ (by omega) s

/-- **`t ↦ π_t ∘ ι : E_{m+1} → E_m` is `C^∞`** in the operator norm, including at `t = 0`. -/
theorem contDiff_zhouFam_comp (m : ℕ) :
    ContDiff ℝ ∞ fun t => (zhouFam h0 hmono β t m).comp ((lineSc δs h0 hmono).incl m) := by
  have he : (fun t => (zhouFam h0 hmono β t m).comp ((lineSc δs h0 hmono).incl m)) =
      fun t => if 0 < t then zhouQ h0 hmono β m (Real.exp t⁻¹) else 0 :=
    funext fun t => zhouFam_comp_incl h0 hmono t m
  rw [he]
  refine contDiff_flat_comp (contDiff_zhouQ h0 hmono hβ m)
    (sub_pos.2 (hmono (Nat.lt_succ_self m))) fun n => ?_
  obtain ⟨K, hK⟩ := norm_iteratedFDeriv_zhouQ_le h0 hmono hβ m n
  exact ⟨K, 0, fun c hc => hK c hc⟩

omit hβ in
lemma denseRange_incl (m : ℕ) : DenseRange ((lineSc δs h0 hmono).incl m) := by
  refine (dense_ofTest1 m (nonneg_of_strictMono h0 hmono m)).mono ?_
  rintro _ ⟨g, hg, hg1, rfl⟩
  exact ⟨ofTest1 (m + 1) (nonneg_of_strictMono h0 hmono (m + 1)) hg hg1, H1.val_injective rfl⟩

lemma norm_zhouFam_le (m : ℕ) : ∃ K, ∀ t, ‖zhouFam h0 hmono β t m‖ ≤ K := by
  obtain ⟨R, hR0, hR⟩ := hβ.bdd
  obtain ⟨M, hM⟩ := bdd_iteratedDeriv hβ.smooth (win_hasCompactSupport hR) m
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0 (Nat.zero_le _) 0)
  refine ⟨(idx m).card * (Real.exp ((δs m + δs m) * R) * M ^ 2 * (2 * R)), fun t => ?_⟩
  by_cases ht : 0 < t
  · rw [zhouFam_pos h0 hmono ht]
    exact norm_proj_le hβ hR0 hR hM0 hM (Real.exp_pos _).le
  · rw [zhouFam_nonpos h0 hmono (not_lt.1 ht), norm_zero]; positivity

/-- **`π_t` is a loss family** (Remark 4.1.3's criterion `IsLossFamily`). -/
theorem isLossFamily_zhouFam : IsLossFamily (zhouFam h0 hmono β) where
  toBase t m f := zhouFam_toBase h0 hmono t m f
  continuous m := by
    obtain ⟨K, hK⟩ := norm_zhouFam_le h0 hmono hβ m
    exact continuous_apply_of_dense (fun t => zhouFam h0 hmono β t m) _
      (denseRange_incl h0 hmono m) hK (contDiff_zhouFam_comp h0 hmono hβ m).continuous
  contDiff m := contDiff_zhouFam_comp h0 hmono hβ m

omit hβ in
lemma inner_tr0_self (hβ : IsTest1 β) (hβ2 : ∫ s, β s ^ 2 = 1) (c : ℝ) :
    ⟪tr0 β c, tr0 β c⟫_ℝ = 1 := by
  rw [tr0_eq hβ, inner_toLp_left]
  calc ∫ x, ((hβ.shift c).memLp.toLp _ : Lp ℝ 2 (volume : Measure ℝ)) x * β (x + c)
      = ∫ x, (fun s => β s * β s) (x + c) := integral_congr_ae (by
        filter_upwards [(hβ.shift c).memLp.coeFn_toLp] with x hx
        rw [hx])
    _ = ∫ s, β s ^ 2 := by rw [integral_add_right_eq_self (fun s => β s * β s) c]; simp [sq]
    _ = 1 := hβ2

omit hβ in
lemma proj_idem {m : ℕ} {δ : ℝ} {hδ : 0 ≤ δ} (hβ : IsTest1 β) (hβ2 : ∫ s, β s ^ 2 = 1) (c : ℝ)
    (f : H1 m hδ) : proj m hδ β c (proj m hδ β c f) = proj m hδ β c f :=
  H1.val_injective (by rw [val_proj, val_proj, inner_smul_right, inner_tr0_self hβ hβ2, mul_one])

omit hβ in
/-- Each `π_t` is a projection. -/
theorem zhouFam_idem (hβ : IsTest1 β) (hβ2 : ∫ s, β s ^ 2 = 1) (t : ℝ)
    (f : lineSc δs h0 hmono 0) :
    zhouFam h0 hmono β t 0 (zhouFam h0 hmono β t 0 f) = zhouFam h0 hmono β t 0 f := by
  by_cases ht : 0 < t
  · rw [zhouFam_pos h0 hmono ht]; exact proj_idem hβ hβ2 _ f
  · rw [zhouFam_nonpos h0 hmono (not_lt.1 ht)]; rfl

/-- **Zhou's sc-smooth retraction (2021 Appendix 7.6.3, p. 348)**: `r(t, f) = (t, π_t f)` on
`ℝ ⊕ E`, `E_m = H^{m,δ_m}(ℝ)`, is an sc-smooth retraction. -/
def zhouRetraction (hβ2 : ∫ s, β s ^ 2 = 1) :
    ScRetraction ((ScBanach.const ℝ).prod (lineSc δs h0 hmono)) univ :=
  (isLossFamily_zhouFam h0 hmono hβ).retraction (zhouFam_idem h0 hmono hβ hβ2)

/-- **The retraction as printed**: `r(t, f) = (t, 0)` for `t ≤ 0` and
`r(t, f) = (t, ⟨f, β(· + e^{1/t})⟩ β(· + e^{1/t}))` for `t > 0` (in `L²(ℝ)`). -/
theorem zhouRetraction_apply (hβ2 : ∫ s, β s ^ 2 = 1)
    (q : ((ScBanach.const ℝ).prod (lineSc δs h0 hmono)) 0) :
    (zhouRetraction h0 hmono hβ hβ2 q).1 = q.1 ∧
    H1.val (show H1 0 (nonneg_of_strictMono h0 hmono 0) from (zhouRetraction h0 hmono hβ hβ2 q).2) =
      if 0 < q.1 then
        ⟪H1.val (show H1 0 (nonneg_of_strictMono h0 hmono 0) from q.2), tr0 β (Real.exp q.1⁻¹)⟫_ℝ •
          tr0 β (Real.exp q.1⁻¹)
      else 0 := by
  refine ⟨rfl, ?_⟩
  change H1.val (show H1 0 _ from zhouFam h0 hmono β q.1 0 q.2) = _
  rw [val_zhouFam, real_inner_comm]

end Family

/-! ### A `β` as in the book -/

/-- **A `β` as the book requires exists**: smooth, compactly supported, `β ≥ 0`, `∫ β² = 1`. -/
theorem exists_beta : ∃ β : ℝ → ℝ, IsTest1 β ∧ (∀ s, 0 ≤ β s) ∧ ∫ s, β s ^ 2 = 1 := by
  let b : ContDiffBump (0 : ℝ) := ⟨1, 2, one_pos, one_lt_two⟩
  have hb : ContDiff ℝ ∞ (b : ℝ → ℝ) := b.contDiff
  have hR : ∀ s, (2 : ℝ) ≤ |s| → b s = 0 := fun s hs =>
    b.zero_of_le_dist (by rw [Real.dist_eq, sub_zero]; exact hs)
  have hI : 0 < ∫ s, (b s) ^ 2 := by
    refine (hb.continuous.pow 2).integral_pos_of_hasCompactSupport_nonneg_nonzero
      (x := 0) (win_hasCompactSupport (R := 2) fun s hs => by rw [hR s hs]; norm_num)
      (fun s => sq_nonneg _) ?_
    rw [b.one_of_mem_closedBall (Metric.mem_closedBall_self zero_le_one)]; norm_num
  refine ⟨fun s => b s / Real.sqrt (∫ s, (b s) ^ 2), ⟨hb.div_const _, 2, by norm_num,
    fun s hs => by rw [hR s hs, zero_div]⟩, fun s => div_nonneg (b.nonneg' s)
    (Real.sqrt_nonneg _), ?_⟩
  simp_rw [div_pow, Real.sq_sqrt hI.le]
  rw [integral_div, div_self hI.ne']

end Polyfold.ZhouLine
