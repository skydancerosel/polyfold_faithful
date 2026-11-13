import Polyfold.Chapter5.SobolevRemarkAbstract

/-!
# The Sobolev spaces `W^{k,p}(Ω)` and the remark after Theorem 5.5.5 (2021, p. 230)

Hofer–Wysocki–Zehnder, 2021 §5.5, the remark after Theorem 5.5.5 (preprint pp. 193–194): "the usual
norms `‖u‖ᵖ_{W^{k,p}} = ∑_{|α| ≤ k} ‖D^α u‖ᵖ_{Lᵖ}` of the Sobolev spaces `W^{k,p}(Ω)` have the same
differentiability as `‖·‖_{Lᵖ}`".

## The space

For `Ω ⊆ ℝⁿ` and `p ≥ 1`, `W^{k,p}(Ω)` is modelled as usual by the tuples of weak derivatives: the
closed subspace `Wsub n k p Ω` of the `ℓᵖ`-product `∏_{|α| ≤ k} Lᵖ(Ω)` (`PiLp`, whose norm is
`(∑ ‖v_α‖ᵖ)^{1/p}`) of the tuples `(v_α)` with
`∫_Ω v₀ · ∂^α φ = (−1)^{|α|} ∫_Ω v_α · φ` for every test function `φ` (smooth, compact support in
`Ω`).  So `v_α = D^α v₀` weakly, and the norm is the usual one; `Dop α` is `u ↦ D^α u`.

* `MIdx n k`: multi-indices `α ∈ ℕⁿ` with `|α| ≤ k`; `Dm α φ = ∂₀^{α₀} ⋯ ∂_{n−1}^{α_{n−1}} φ`
  (for smooth `φ` the order of the partial derivatives does not matter, so this is `∂^α φ`).
* `isClosed_Wsub`, the `CompleteSpace` instance: `W^{k,p}(Ω)` is a Banach space.
* `norm_rpow_W`: `‖u‖ᵖ = ∑_{|α| ≤ k} ‖D^α u‖ᵖ_{Lᵖ}`.
* `Dop_zero_injective` (for `Ω` open): `u ↦ u = D⁰u` is injective (weak derivatives are unique), so
  `W^{k,p}(Ω)` is the space of `u ∈ Lᵖ(Ω)` whose weak derivatives up to order `k` lie in `Lᵖ(Ω)`.
* **`remark_5_5_5_sobolev`**: the remark, in the three cases of Theorem 5.5.5;
  `remark_5_5_5_sobolev_bump`: `β(‖u‖ᵖ_{W^{k,p}})` is a bump of the same class.
* `inclW`: the inclusion `W^{k+1,p}(Ω) → W^{k,p}(Ω)`, continuous, linear, injective (`Ω` open).
-/

open MeasureTheory Set Function
open scoped ENNReal ContDiff

noncomputable section

namespace Polyfold

namespace SobolevRemark

/-! ### Multi-indices, partial derivatives, test functions -/

/-- Multi-indices `α ∈ ℕⁿ` with `|α| = α₀ + ⋯ + α_{n−1} ≤ k` (stored with values in `Fin (k+1)`). -/
abbrev MIdx (n k : ℕ) : Type := {a : Fin n → Fin (k + 1) // ∑ i, (a i : ℕ) ≤ k}

/-- The multi-index `0`. -/
def MIdx.zero (n k : ℕ) : MIdx n k := ⟨0, by simp⟩

/-- The order `|α|`. -/
def MIdx.ord {n k : ℕ} (a : MIdx n k) : ℕ := ∑ i, (a.1 i : ℕ)

/-- The multi-index as a function `Fin n → ℕ`. -/
def MIdx.toFun {n k : ℕ} (a : MIdx n k) : Fin n → ℕ := fun i => (a.1 i : ℕ)

variable {n : ℕ}

/-- The partial derivative `∂ᵢ φ`. -/
def pd (i : Fin n) (φ : (Fin n → ℝ) → ℝ) : (Fin n → ℝ) → ℝ :=
  fun x => fderiv ℝ φ x (Pi.single i 1)

/-- `∂^α φ = ∂₀^{α₀} ⋯ ∂_{n−1}^{α_{n−1}} φ`. -/
def Dm (a : Fin n → ℕ) (φ : (Fin n → ℝ) → ℝ) : (Fin n → ℝ) → ℝ :=
  (List.finRange n).foldr (fun i g => (pd i)^[a i] g) φ

/-- Test functions on `Ω`: smooth, with compact support contained in `Ω`. -/
def IsTestOn (Ω : Set (Fin n → ℝ)) (φ : (Fin n → ℝ) → ℝ) : Prop :=
  ContDiff ℝ ∞ φ ∧ HasCompactSupport φ ∧ tsupport φ ⊆ Ω

lemma IsTestOn.partialD {Ω : Set (Fin n → ℝ)} {φ : (Fin n → ℝ) → ℝ} (h : IsTestOn Ω φ) (i : Fin n) :
    IsTestOn Ω (pd i φ) :=
  ⟨(h.1.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const,
    h.2.1.fderiv_apply ℝ _, (tsupport_fderiv_apply_subset ℝ _).trans h.2.2⟩

lemma IsTestOn.iterate_pd {Ω : Set (Fin n → ℝ)} {φ : (Fin n → ℝ) → ℝ} (h : IsTestOn Ω φ)
    (i : Fin n) (m : ℕ) : IsTestOn Ω ((pd i)^[m] φ) := by
  induction m with
  | zero => exact h
  | succ m ih => rw [iterate_succ_apply']; exact ih.partialD i

lemma IsTestOn.foldr {Ω : Set (Fin n → ℝ)} {φ : (Fin n → ℝ) → ℝ} (h : IsTestOn Ω φ)
    (a : Fin n → ℕ) (l : List (Fin n)) :
    IsTestOn Ω (l.foldr (fun i g => (pd i)^[a i] g) φ) := by
  induction l with
  | nil => exact h
  | cons i l ih => exact ih.iterate_pd i (a i)

lemma IsTestOn.Dm {Ω : Set (Fin n → ℝ)} {φ : (Fin n → ℝ) → ℝ} (h : IsTestOn Ω φ)
    (a : Fin n → ℕ) : IsTestOn Ω (Dm a φ) :=
  h.foldr a _

lemma Dm_zero (φ : (Fin n → ℝ) → ℝ) : Dm (0 : Fin n → ℕ) φ = φ := by
  unfold Dm
  induction (List.finRange n) with
  | nil => rfl
  | cons i l ih => simp

/-! ### The pairing with a test function -/

section Pairing

variable {Ω : Set (Fin n → ℝ)} {p : ℝ} [hP : Fact (1 ≤ ENNReal.ofReal p)]

/-- The measure of `Ω`: Lebesgue measure restricted to `Ω`. -/
abbrev μΩ (Ω : Set (Fin n → ℝ)) : Measure (Fin n → ℝ) := volume.restrict Ω

/-- The conjugate exponent `q`, `q⁻¹ = 1 − p⁻¹`. -/
def conjE (p : ℝ) : ℝ≥0∞ := (1 - (ENNReal.ofReal p)⁻¹)⁻¹

omit hP in
lemma conjE_hq [hP : Fact (1 ≤ ENNReal.ofReal p)] :
    (conjE p)⁻¹ + ((1 : ℕ) : ℝ≥0∞) * (ENNReal.ofReal p)⁻¹ = 1 := by
  rw [conjE, inv_inv, Nat.cast_one, one_mul]
  exact tsub_add_cancel_of_le (ENNReal.inv_le_one.2 hP.out)

omit hP in
lemma IsTestOn.memLp {φ : (Fin n → ℝ) → ℝ} (h : IsTestOn Ω φ) (q : ℝ≥0∞) :
    MemLp φ q (μΩ Ω) :=
  h.1.continuous.memLp_of_hasCompactSupport h.2.1

/-- `h ↦ ∫_Ω w h`, a continuous linear form on `Lᵖ(Ω)` for `w ∈ L^q`, `q` the conjugate exponent
(the form `wMul 1` of the Bonic–Frampton file). -/
def pair (w : (Fin n → ℝ) → ℝ) (hw : MemLp w (conjE p) (μΩ Ω)) :
    Lp ℝ (ENNReal.ofReal p) (μΩ Ω) →L[ℝ] ℝ :=
  (BonicFrampton.wMul 1 conjE_hq hw).toContinuousLinearMap (fun _ => 0) 0

lemma pair_apply (w : (Fin n → ℝ) → ℝ) (hw : MemLp w (conjE p) (μΩ Ω))
    (h : Lp ℝ (ENNReal.ofReal p) (μΩ Ω)) : pair w hw h = ∫ x, w x * h x ∂(μΩ Ω) := by
  simp [pair, BonicFrampton.wMul_apply]

end Pairing

/-! ### The space `W^{k,p}(Ω)` -/

section Sobolev

variable (n) (k : ℕ) (p : ℝ) [hP : Fact (1 ≤ ENNReal.ofReal p)] (Ω : Set (Fin n → ℝ))

/-- The ambient space `∏_{|α| ≤ k} Lᵖ(Ω)` with the `ℓᵖ` norm `(∑ ‖v_α‖ᵖ)^{1/p}`. -/
abbrev Amb : Type := PiLp (ENNReal.ofReal p) (fun _ : MIdx n k => Lp ℝ (ENNReal.ofReal p) (μΩ Ω))

variable {n k p Ω}

/-- The defining functional of a weak derivative:
`v ↦ ∫_Ω v₀ ∂^α φ − (−1)^{|α|} ∫_Ω v_α φ`. -/
def wk (a : MIdx n k) {φ : (Fin n → ℝ) → ℝ} (hφ : IsTestOn Ω φ) : Amb n k p Ω →L[ℝ] ℝ :=
  (pair (Dm a.toFun φ) ((hφ.Dm a.toFun).memLp _)).comp
      (PiLp.proj _ (fun _ : MIdx n k => Lp ℝ (ENNReal.ofReal p) (μΩ Ω)) (MIdx.zero n k)) -
    ((-1 : ℝ) ^ a.ord) • (pair φ (hφ.memLp _)).comp
      (PiLp.proj _ (fun _ : MIdx n k => Lp ℝ (ENNReal.ofReal p) (μΩ Ω)) a)

lemma wk_apply (a : MIdx n k) {φ : (Fin n → ℝ) → ℝ} (hφ : IsTestOn Ω φ) (v : Amb n k p Ω) :
    wk a hφ v = ∫ x, Dm a.toFun φ x * v.ofLp (MIdx.zero n k) x ∂(μΩ Ω) -
      (-1 : ℝ) ^ a.ord * ∫ x, φ x * v.ofLp a x ∂(μΩ Ω) := by
  simp [wk, pair_apply]

variable (n k p Ω)

/-- **`W^{k,p}(Ω)`**: the tuples `(v_α)_{|α| ≤ k}` in `∏ Lᵖ(Ω)` with `v_α = D^α v₀` weakly, i.e.
`∫_Ω v₀ ∂^α φ = (−1)^{|α|} ∫_Ω v_α φ` for all test functions `φ` on `Ω`. -/
def Wsub : Submodule ℝ (Amb n k p Ω) where
  carrier := {v | ∀ (a : MIdx n k) (φ : (Fin n → ℝ) → ℝ) (hφ : IsTestOn Ω φ), wk a hφ v = 0}
  add_mem' {v w} hv hw a φ hφ := by simp [map_add, hv a φ hφ, hw a φ hφ]
  zero_mem' a φ hφ := by simp
  smul_mem' c v hv a φ hφ := by simp [map_smul, hv a φ hφ]

/-- `W^{k,p}(Ω)` is closed in `∏ Lᵖ(Ω)`. -/
theorem isClosed_Wsub : IsClosed (Wsub n k p Ω : Set (Amb n k p Ω)) := by
  have : (Wsub n k p Ω : Set (Amb n k p Ω)) =
      ⋂ (a : MIdx n k) (φ : (Fin n → ℝ) → ℝ) (hφ : IsTestOn Ω φ), {v | wk a hφ v = 0} := by
    ext v; simp [Wsub]
  rw [this]
  exact isClosed_iInter fun a => isClosed_iInter fun φ => isClosed_iInter fun hφ =>
    isClosed_eq (wk a hφ).continuous continuous_const

/-- The Sobolev space `W^{k,p}(Ω)`. -/
abbrev W : Type := Wsub n k p Ω

/-- **`W^{k,p}(Ω)` is a Banach space.** -/
instance completeSpace_W : CompleteSpace (W n k p Ω) :=
  (isClosed_Wsub n k p Ω).completeSpace_coe

variable {n k p Ω}

/-- `D^α : W^{k,p}(Ω) → Lᵖ(Ω)`, `u ↦ D^α u`. -/
def Dop (a : MIdx n k) : W n k p Ω →L[ℝ] Lp ℝ (ENNReal.ofReal p) (μΩ Ω) :=
  (PiLp.proj _ (fun _ : MIdx n k => Lp ℝ (ENNReal.ofReal p) (μΩ Ω)) a).comp
    (Wsub n k p Ω).subtypeL

lemma Dop_apply (a : MIdx n k) (u : W n k p Ω) : Dop a u = (u : Amb n k p Ω).ofLp a := rfl

/-- **The usual norm**: `‖u‖ᵖ_{W^{k,p}} = ∑_{|α| ≤ k} ‖D^α u‖ᵖ_{Lᵖ}`. -/
theorem norm_rpow_W (u : W n k p Ω) : ‖u‖ ^ p = ∑ a, ‖Dop a u‖ ^ p := by
  have hp : 0 < p := BonicFrampton.p_pos
  have ht : (ENNReal.ofReal p).toReal = p := ENNReal.toReal_ofReal hp.le
  have hn : ‖u‖ = ‖(u : Amb n k p Ω)‖ := rfl
  rw [hn, PiLp.norm_eq_sum (by rw [ht]; exact hp), ht, ← Real.rpow_mul
    (Finset.sum_nonneg fun _ _ => Real.rpow_nonneg (norm_nonneg _) _), one_div_mul_cancel hp.ne',
    Real.rpow_one]
  rfl

/-- **2021, p. 230 (preprint p. 193): the usual norm of `W^{k,p}(Ω)` has the differentiability of
`‖·‖_{Lᵖ}`** (Theorem 5.5.5): `‖·‖ᵖ_{W^{k,p}}` is `C^∞` for `p` even, `C^{p−1}` for `p` odd and
`C^{[p]}` for `p ≥ 1` not an integer. -/
theorem remark_5_5_5_sobolev :
    ((∃ j : ℕ, p = 2 * j) → ContDiff ℝ (⊤ : ℕ∞) (fun u : W n k p Ω => ‖u‖ ^ p)) ∧
      (∀ j : ℕ, p = 2 * j + 1 →
        ContDiff ℝ ((2 * j : ℕ) : ℕ∞) (fun u : W n k p Ω => ‖u‖ ^ p)) ∧
      ((∀ j : ℕ, p ≠ j) → ContDiff ℝ (⌊p⌋₊ : ℕ∞) (fun u : W n k p Ω => ‖u‖ ^ p)) :=
  theorem_5_5_5_sum Dop norm_rpow_W

/-- **Bump functions on `W^{k,p}(Ω)`** (2021, p. 230): `β(‖u‖ᵖ_{W^{k,p}})` gives a `C^∞`-bump
for `p` even, a `C^{p−1}`-bump for `p` odd and a `C^{[p]}`-bump for `p` not an integer. -/
theorem remark_5_5_5_sobolev_bump :
    ((∃ j : ℕ, p = 2 * j) → HasContDiffBump (W n k p Ω) ⊤) ∧
      (∀ j : ℕ, p = 2 * j + 1 → HasContDiffBump (W n k p Ω) (2 * j : ℕ)) ∧
      ((∀ j : ℕ, p ≠ j) → HasContDiffBump (W n k p Ω) ⌊p⌋₊) :=
  hasContDiffBump_sum_cases Dop norm_rpow_W

/-! ### Uniqueness of weak derivatives -/

omit hP in
/-- A function of `Lᵖ(Ω)`, `Ω` open, that integrates to `0` against every test function on `Ω`
vanishes. -/
lemma Lp_eq_zero_of_pair {Ω : Set (Fin n → ℝ)} (hΩ : IsOpen Ω) [hP : Fact (1 ≤ ENNReal.ofReal p)]
    (h : Lp ℝ (ENNReal.ofReal p) (μΩ Ω))
    (hh : ∀ φ, IsTestOn Ω φ → ∫ x, φ x * h x ∂(μΩ Ω) = 0) : h = 0 := by
  rw [Lp.eq_zero_iff_ae_eq_zero]
  have hli : LocallyIntegrableOn (h : (Fin n → ℝ) → ℝ) Ω (μΩ Ω) :=
    ((Lp.memLp h).locallyIntegrable hP.out).locallyIntegrableOn Ω
  have := hΩ.ae_eq_zero_of_integral_contDiff_smul_eq_zero hli
    fun g hg hgc hgs => by simpa [smul_eq_mul] using hh g ⟨hg, hgc, hgs⟩
  filter_upwards [this, ae_restrict_mem hΩ.measurableSet] with x hx hxΩ
  exact hx hxΩ

/-- **Weak derivatives are unique** (`Ω` open): `u ↦ u = D⁰u` is injective on `W^{k,p}(Ω)`. -/
theorem Dop_zero_injective (hΩ : IsOpen Ω) :
    Function.Injective (Dop (p := p) (Ω := Ω) (MIdx.zero n k)) := by
  rw [injective_iff_map_eq_zero]
  intro u hu
  refine Subtype.ext (PiLp.ext fun a => ?_)
  refine Lp_eq_zero_of_pair hΩ _ fun φ hφ => ?_
  have h1 := u.2 a φ hφ
  rw [wk_apply] at h1
  have h0 : (u : Amb n k p Ω).ofLp (MIdx.zero n k) = 0 := hu
  rw [h0] at h1
  have h2 : ∫ x, Dm a.toFun φ x * (0 : Lp ℝ (ENNReal.ofReal p) (μΩ Ω)) x ∂(μΩ Ω) = 0 := by
    rw [← pair_apply _ ((hφ.Dm a.toFun).memLp _), map_zero]
  rw [h2, zero_sub, neg_eq_zero, mul_eq_zero] at h1
  rcases h1 with h1 | h1
  · exact absurd h1 (pow_ne_zero _ (by norm_num))
  · simpa using h1

/-! ### The inclusion `W^{k+1,p}(Ω) → W^{k,p}(Ω)` -/

/-- A multi-index of order `≤ k` as one of order `≤ k + 1`. -/
def MIdx.lift (a : MIdx n k) : MIdx n (k + 1) :=
  ⟨fun i => Fin.castSucc (a.1 i), by simpa using a.2.trans (Nat.le_succ k)⟩

lemma MIdx.toFun_lift (a : MIdx n k) : a.lift.toFun = a.toFun := rfl

lemma MIdx.ord_lift (a : MIdx n k) : a.lift.ord = a.ord := rfl

lemma MIdx.lift_zero : (MIdx.zero n k).lift = MIdx.zero n (k + 1) := rfl

/-- Restriction of a tuple to the multi-indices of order `≤ k`. -/
def resAmb : Amb n (k + 1) p Ω →L[ℝ] Amb n k p Ω :=
  (PiLp.continuousLinearEquiv (ENNReal.ofReal p) ℝ
      (fun _ : MIdx n k => Lp ℝ (ENNReal.ofReal p) (μΩ Ω))).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi fun a =>
      PiLp.proj _ (fun _ : MIdx n (k + 1) => Lp ℝ (ENNReal.ofReal p) (μΩ Ω)) a.lift)

lemma resAmb_apply (v : Amb n (k + 1) p Ω) (a : MIdx n k) :
    (resAmb v).ofLp a = v.ofLp a.lift := rfl

lemma resAmb_mem (u : W n (k + 1) p Ω) : resAmb (u : Amb n (k + 1) p Ω) ∈ Wsub n k p Ω := by
  intro a φ hφ
  have h := u.2 a.lift φ hφ
  rw [wk_apply] at h ⊢
  simpa only [resAmb_apply, MIdx.toFun_lift, MIdx.ord_lift, MIdx.lift_zero] using h

/-- **The inclusion `W^{k+1,p}(Ω) → W^{k,p}(Ω)`** (forget the derivatives of order `k + 1`). -/
def inclW : W n (k + 1) p Ω →L[ℝ] W n k p Ω :=
  (resAmb.comp (Wsub n (k + 1) p Ω).subtypeL).codRestrict _ resAmb_mem

lemma Dop_inclW (a : MIdx n k) (u : W n (k + 1) p Ω) : Dop a (inclW u) = Dop a.lift u := rfl

/-- The inclusion is injective (`Ω` open). -/
theorem inclW_injective (hΩ : IsOpen Ω) :
    Function.Injective (inclW (n := n) (k := k) (p := p) (Ω := Ω)) := by
  intro u v huv
  apply Dop_zero_injective hΩ
  have := congrArg (Dop (MIdx.zero n k)) huv
  simpa only [Dop_inclW, MIdx.lift_zero] using this

end Sobolev

end SobolevRemark

end Polyfold
