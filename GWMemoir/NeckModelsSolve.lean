import GWMemoir.NeckEstimate
import GWMemoir.NeckTestForms
import GWMemoir.Gluing

/-!
# Smooth solutions of `∂_s + J ∂_t = g` on `ℝ × S¹` for test functions `g`

HWZ, *Applications of Polyfold Theory I*, Memoirs AMS 248, no. 1179, §4.3: the explicit solutions
behind the ontoness in Propositions 4.15 (p. 109) and 4.16 (p. 110), on the translated cylinder
of p. 170.

* `SmoothW δ f`: `f` smooth, `1`-periodic in `t`, with every classical derivative in
  `L²(e^{2δ|s|})`; then `f ∈ H^{k,δ}` for all `k` (`mkH`), and `∂_s`, `∂_t` act classically
  (`dsH_mkH`, `dtH_mkH`).  Test functions (`IsTest.smoothW`), functions `H ∘ e^{-2π(s+it)}` of the
  neck class (`NeckCls.smoothW`, for `δ < 2π`) and their reflections `s ↦ -s` (`SmoothW.refl`)
  are of this kind.
* `jE J`: the matrix `J` acting on `ℝⁿ = EuclideanSpace ℝ (Fin n)`.
* **`exists_smooth_solution`**: for `J² = -1` and a tuple `φ` of test functions there are a
  constant `c ∈ ℝⁿ` and a smooth tuple `u` with `∂_s u + J ∂_t u = φ` pointwise, such that
  `u - c (1 - β(s))` lies in every `H^{k,δ}`, `0 ≤ δ < 2π` (`β` a cut-off of (2.1)).  It is the
  Cauchy transform of `φ` read in `z = e^{-2π(s+it)}`.
-/

set_option maxSynthPendingDepth 3
set_option linter.unusedSectionVars false

open scoped Manifold ContDiff Topology Real
open Set Function Filter MeasureTheory
open Polyfold Polyfold.CylinderSobolev GWMemoir.Neck

noncomputable section

namespace GWMemoir

/-! ## 1. Smooth functions with weighted derivatives -/

section Smooth

/-- `f` is smooth, `1`-periodic in `t`, and all its classical derivatives lie in
`L²(e^{2δ|s|})`. -/
structure SmoothW (δ : ℝ) (f : ℝ × ℝ → ℝ) : Prop where
  smPer : SmPer f
  memLp : ∀ a b, MemLp (fun x => wt δ x * pD a b f x) 2 cyl

variable {δ : ℝ} {f g : ℝ × ℝ → ℝ}

lemma SmoothW.memH (hf : SmoothW δ f) (k : ℕ) : MemH k δ f :=
  fun a b _ => ⟨pD a b f, hf.smPer.hasWeakDeriv a b, hf.memLp a b⟩

lemma SmoothW.memLp_two (hf : SmoothW δ f) (hδ : 0 ≤ δ) : MemLp f 2 cyl :=
  memLp_of_weighted hδ (by simpa using hf.memLp 0 0)

lemma SmoothW.ds (hf : SmoothW δ f) : SmoothW δ (Ds f) :=
  ⟨hf.smPer.ds, fun a b => by rw [← pD_succ_s hf.smPer.1]; exact hf.memLp (a + 1) b⟩

lemma SmoothW.dt (hf : SmoothW δ f) : SmoothW δ (Dt f) :=
  ⟨hf.smPer.dt, fun a b => by rw [← pD_succ_t]; exact hf.memLp a (b + 1)⟩

theorem _root_.Polyfold.CylinderSobolev.IsTest.smoothW {φ : ℝ × ℝ → ℝ} (hφ : IsTest φ) (δ : ℝ) : SmoothW δ φ :=
  ⟨hφ.smPer, fun a b => (hφ.pD a b).memLp_wt δ⟩

lemma memH_congr {k : ℕ} {u v : ℝ × ℝ → ℝ} (h : MemH k δ u) (huv : u =ᵐ[cyl] v) : MemH k δ v :=
  fun a b hab => let ⟨g, hg, hw⟩ := h a b hab; ⟨g, hg.congr_ae huv (ae_eq_refl _), hw⟩

/-- A function of `SmoothW δ` as an element of `H^{k,δ}`. -/
def mkH (k : ℕ) (hδ : 0 ≤ δ) (hf : SmoothW δ f) : H k hδ :=
  (⟨(hf.memLp_two hδ).toLp f,
    memH_congr (hf.memH k) (hf.memLp_two hδ).coeFn_toLp.symm⟩ : Hsub k hδ)

variable {k : ℕ} {hδ : 0 ≤ δ}

lemma val_mkH (hf : SmoothW δ f) : (H.val (mkH k hδ hf) : ℝ × ℝ → ℝ) =ᵐ[cyl] f :=
  (hf.memLp_two hδ).coeFn_toLp

lemma toH_eq_mkH {φ : ℝ × ℝ → ℝ} (hφ : IsTest φ) : toH k hδ hφ = mkH k hδ (hφ.smoothW δ) := rfl

lemma dsH_mkH (hf : SmoothW δ f) : dsH k hδ (mkH (k + 1) hδ hf) = mkH k hδ hf.ds := by
  refine Subtype.ext (Lp.ext ?_)
  refine (coeFn_dsH _).trans ((dv_unique _ _ ?_ (hf.ds.memLp_two hδ)).trans (val_mkH hf.ds).symm)
  exact (hf.smPer.hasWeakDeriv 1 0).congr_ae (val_mkH hf).symm (ae_eq_refl _)

lemma dtH_mkH (hf : SmoothW δ f) : dtH k hδ (mkH (k + 1) hδ hf) = mkH k hδ hf.dt := by
  refine Subtype.ext (Lp.ext ?_)
  refine (coeFn_dtH _).trans ((dv_unique _ _ ?_ (hf.dt.memLp_two hδ)).trans (val_mkH hf.dt).symm)
  exact (hf.smPer.hasWeakDeriv 0 1).congr_ae (val_mkH hf).symm (ae_eq_refl _)

lemma mkH_congr {f' : ℝ × ℝ → ℝ} (hf : SmoothW δ f) (hf' : SmoothW δ f') (h : f = f') :
    mkH k hδ hf = mkH k hδ hf' := by subst h; rfl

end Smooth

/-! ## 2. The reflection `s ↦ -s` -/

section Refl

variable {δ : ℝ} {f : ℝ × ℝ → ℝ}

/-- `(s, t) ↦ (-s, t)`. -/
def reflS (x : ℝ × ℝ) : ℝ × ℝ := (-x.1, x.2)

/-- `reflS` as a linear map. -/
def reflL : ℝ × ℝ →L[ℝ] ℝ × ℝ :=
  (-(ContinuousLinearMap.fst ℝ ℝ ℝ)).prod (ContinuousLinearMap.snd ℝ ℝ ℝ)

lemma reflL_eq : ⇑reflL = reflS := rfl

lemma wt_reflS (δ : ℝ) (x : ℝ × ℝ) : wt δ (reflS x) = wt δ x := by
  simp [wt, reflS, abs_neg]

lemma mp_reflS : MeasurePreserving reflS cyl cyl :=
  (Measure.measurePreserving_neg (volume : Measure ℝ)).prod
    (MeasurePreserving.id (volume.restrict (Ioc (0 : ℝ) 1)))

lemma Ds_comp_reflS (hf : Differentiable ℝ f) : Ds (f ∘ reflS) = fun x => -Ds f (reflS x) := by
  funext x
  simp only [Ds]
  rw [← reflL_eq, fderiv_comp x (hf _) reflL.differentiableAt, reflL.fderiv,
    ContinuousLinearMap.comp_apply]
  rw [show reflL (1, 0) = -((1 : ℝ), (0 : ℝ)) by simp [reflL]]
  rw [map_neg]

lemma Dt_comp_reflS (hf : Differentiable ℝ f) : Dt (f ∘ reflS) = fun x => Dt f (reflS x) := by
  funext x
  simp only [Dt]
  rw [← reflL_eq, fderiv_comp x (hf _) reflL.differentiableAt, reflL.fderiv,
    ContinuousLinearMap.comp_apply]
  rw [show reflL (0, 1) = ((0 : ℝ), (1 : ℝ)) by simp [reflL]]

lemma Ds_const_mul {h : ℝ × ℝ → ℝ} (hh : Differentiable ℝ h) (c : ℝ) :
    Ds (fun x => c * h x) = fun x => c * Ds h x := by
  funext x
  simp only [Ds]
  rw [fderiv_const_mul (hh x)]
  rfl

lemma pD_comp_reflS (hf : ContDiff ℝ ∞ f) (a b : ℕ) :
    pD a b (f ∘ reflS) = fun x => (-1) ^ a * pD a b f (reflS x) := by
  have ht : ∀ b, Dt^[b] (f ∘ reflS) = (Dt^[b] f) ∘ reflS := by
    intro b
    induction b with
    | zero => rfl
    | succ b ih =>
      rw [Function.iterate_succ_apply', ih, Function.iterate_succ_apply',
        Dt_comp_reflS ((contDiff_iterate_Dt hf b).differentiable (by simp))]
      rfl
  induction a with
  | zero => simp only [pD, Function.iterate_zero, id, pow_zero, one_mul]; rw [ht]; rfl
  | succ a ih =>
    have hd : Differentiable ℝ (pD a b f) := (contDiff_pD hf a b).differentiable (by simp)
    rw [pD, Function.iterate_succ_apply', ← pD, ih,
      Ds_const_mul (h := fun x => pD a b f (reflS x)) (hd.comp reflL.differentiable) ((-1) ^ a)]
    have e := Ds_comp_reflS hd
    change Ds (pD a b f ∘ reflS) = _ at e
    funext x
    change (-1) ^ a * Ds (pD a b f ∘ reflS) x = _
    rw [e]
    simp only [pD, Function.iterate_succ_apply']
    ring

lemma SmoothW.refl (hf : SmoothW δ f) : SmoothW δ (f ∘ reflS) where
  smPer := ⟨hf.smPer.1.comp reflL.contDiff, fun s t => hf.smPer.2 (-s) t⟩
  memLp a b := by
    rw [pD_comp_reflS hf.smPer.1]
    refine (((hf.memLp a b).comp_measurePreserving mp_reflS).const_mul ((-1) ^ a)).ae_eq
      (Eventually.of_forall fun x => ?_)
    simp only [Function.comp_apply, wt_reflS]
    ring

end Refl

/-! ## 3. Functions of `e^{-2π(s+it)}` -/

section Pol

lemma neckCls_one {H : ℂ → ℝ} (h : NeckCls 1 H) : NeckCls (Real.exp (-2 * Real.pi * 0)) H := by
  simpa using h

/-- For `H` in the neck class of radius `1` and `δ < 2π`, `H ∘ e^{-2π(s+it)}` is of class
`SmoothW δ`. -/
lemma NeckCls.smoothW {H : ℂ → ℝ} (hH : NeckCls 1 H) {δ : ℝ} (hδ : δ < 2 * Real.pi) :
    SmoothW δ (H ∘ ePol 0) := by
  refine ⟨⟨hH.smooth.comp (contDiff_ePol 0), fun s t => by simp only [comp_apply, ePol_add_one]⟩,
    fun a b => ?_⟩
  obtain ⟨G, hG, e⟩ := pD_comp_ePol (neckCls_one hH) 0 a b
  obtain ⟨C, hC⟩ := wt_mul_comp_ePol_le hG δ
  rw [e]
  refine ((memLp_expDecay (b := 2 * Real.pi - δ) (by linarith)).const_mul C).of_le
    (((continuous_wt δ).mul (hG.smooth.continuous.comp
      (contDiff_ePol 0).continuous)).aestronglyMeasurable) (Eventually.of_forall fun x => ?_)
  simp only [Real.norm_eq_abs, comp_apply]
  exact (hC x).trans (le_abs_self _)

end Pol

/-! ## 4. Sums -/

section Add

variable {δ : ℝ} {f g : ℝ × ℝ → ℝ}

lemma Ds_add_fun (hf : Differentiable ℝ f) (hg : Differentiable ℝ g) : Ds (f + g) = Ds f + Ds g := by
  funext x; simp only [Ds, Pi.add_apply]; rw [fderiv_add (hf x) (hg x)]; rfl

lemma Dt_add_fun (hf : Differentiable ℝ f) (hg : Differentiable ℝ g) : Dt (f + g) = Dt f + Dt g := by
  funext x; simp only [Dt, Pi.add_apply]; rw [fderiv_add (hf x) (hg x)]; rfl

lemma pD_add_fun (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (a b : ℕ) :
    pD a b (f + g) = pD a b f + pD a b g := by
  have ht : ∀ b, Dt^[b] (f + g) = Dt^[b] f + Dt^[b] g := by
    intro b
    induction b with
    | zero => rfl
    | succ b ih =>
      rw [Function.iterate_succ_apply', ih, Dt_add_fun
        ((contDiff_iterate_Dt hf b).differentiable (by simp))
        ((contDiff_iterate_Dt hg b).differentiable (by simp)), Function.iterate_succ_apply',
        Function.iterate_succ_apply']
  induction a with
  | zero => simp only [pD, Function.iterate_zero, id]; exact ht b
  | succ a ih =>
    rw [pD, Function.iterate_succ_apply', ← pD, ih, Ds_add_fun
      ((contDiff_pD hf a b).differentiable (by simp)) ((contDiff_pD hg a b).differentiable (by simp))]
    simp only [pD, Function.iterate_succ_apply']

lemma SmoothW.add (hf : SmoothW δ f) (hg : SmoothW δ g) : SmoothW δ (f + g) where
  smPer := ⟨hf.smPer.1.add hg.smPer.1, fun s t => by
    simp only [Pi.add_apply, hf.smPer.2, hg.smPer.2]⟩
  memLp a b := by
    rw [pD_add_fun hf.smPer.1 hg.smPer.1]
    refine ((hf.memLp a b).add (hg.memLp a b)).ae_eq (Eventually.of_forall fun x => ?_)
    simp only [Pi.add_apply]; ring

end Add

/-! ## 5. The solution through the Cauchy transform -/

section Solve

variable {n : ℕ} (J : Fin n → Fin n → ℝ)

/-- The matrix `J` acting on `ℝⁿ = EuclideanSpace ℝ (Fin n)`. -/
def jE : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) :=
  (EuclideanSpace.equiv (Fin n) ℝ).symm.toContinuousLinearMap.comp
    ((LinearMap.toContinuousLinearMap (Matrix.toLin' (Matrix.of J))).comp
      (EuclideanSpace.equiv (Fin n) ℝ).toContinuousLinearMap)

lemma jE_apply (v : EuclideanSpace ℝ (Fin n)) (k : Fin n) : jE J v k = ∑ l, J k l * v l := by
  simp [jE, Matrix.toLin'_apply, Matrix.mulVec, dotProduct]

variable {J}

lemma jE_sq (hJ : IsCxMat J) (v : EuclideanSpace ℝ (Fin n)) : jE J (jE J v) = -v := by
  ext k
  simp only [jE_apply, PiLp.neg_apply]
  calc ∑ l, J k l * ∑ j, J l j * v j = ∑ j, (∑ l, J k l * J l j) * v j := by
        simp only [Finset.mul_sum, Finset.sum_mul, mul_assoc]; exact Finset.sum_comm
    _ = -v k := by simp [hJ k, ite_mul]

/-- A cut-off on `ℂ`: `1` for `|w|² ≤ 1/4`, `0` for `|w|² ≥ 1/2`. -/
def cutC (w : ℂ) : ℝ := Real.smoothTransition (2 - 4 * ‖w‖ ^ 2)

lemma contDiff_cutC : ContDiff ℝ ∞ cutC :=
  Real.smoothTransition.contDiff.comp (contDiff_const.sub (contDiff_const.mul (contDiff_norm_sq ℝ)))

lemma cutC_one {w : ℂ} (h : ‖w‖ ^ 2 ≤ 1 / 4) : cutC w = 1 :=
  Real.smoothTransition.one_of_one_le (by linarith)

lemma cutC_zero {w : ℂ} (h : 1 / 2 ≤ ‖w‖ ^ 2) : cutC w = 0 :=
  Real.smoothTransition.zero_of_nonpos (by linarith)

lemma neckCls_cut {V : ℂ → EuclideanSpace ℝ (Fin n)} (hV : ContDiff ℝ ∞ V) (h0 : V 0 = 0)
    (k : Fin n) : NeckCls 1 (fun w => cutC w * V w k) where
  smooth := contDiff_cutC.mul ((EuclideanSpace.proj k : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ).contDiff.comp hV)
  zero := by simp [h0]
  vanish w hw := by
    rw [cutC_zero (by nlinarith [norm_nonneg w]), zero_mul]

lemma ePol_zero_eq (p : ℝ × ℝ) : ePol 0 p = expPolar p := by simp [ePol]

lemma ePol_ne_zero (p : ℝ × ℝ) : ePol 0 p ≠ 0 := by
  rw [ePol_zero_eq]; exact expPolar_ne_zero p

lemma conj_ePol_reflS (p : ℝ × ℝ) : (starRingEnd ℂ) (ePol 0 (reflS p)) = (ePol 0 p)⁻¹ := by
  simp only [ePol, expPolar, reflS, add_zero, ← Complex.exp_conj, ← Complex.exp_neg]
  congr 1
  simp only [map_mul, map_neg, map_add, Complex.conj_ofReal, Complex.conj_I, map_ofNat]
  push_cast
  ring

/-- Half of the tuple `φ`, as a map into `ℝⁿ`. -/
def halfE (φ : Fin n → ℝ × ℝ → ℝ) (p : ℝ × ℝ) : EuclideanSpace ℝ (Fin n) :=
  (EuclideanSpace.equiv (Fin n) ℝ).symm (fun k => φ k p / 2)

variable {φ : Fin n → ℝ × ℝ → ℝ}

lemma halfE_apply (p : ℝ × ℝ) (k : Fin n) : halfE φ p k = φ k p / 2 := by simp [halfE]

lemma contDiff_halfE (hφ : ∀ k, IsTest (φ k)) : ContDiff ℝ ∞ (halfE φ) :=
  (EuclideanSpace.equiv (Fin n) ℝ).symm.contDiff.comp
    (contDiff_pi.2 fun k => (hφ k).smooth.div_const 2)

lemma halfE_periodic (hφ : ∀ k, IsTest (φ k)) (s t : ℝ) : halfE φ (s, t + 1) = halfE φ (s, t) := by
  simp only [halfE, (hφ _).periodic]

lemma exists_halfE_supp (hφ : ∀ k, IsTest (φ k)) :
    ∃ R, 0 ≤ R ∧ ∀ p : ℝ × ℝ, R < |p.1| → halfE φ p = 0 := by
  choose R hR using fun k => (hφ k).bddSupp
  refine ⟨∑ k, |R k|, Finset.sum_nonneg fun k _ => abs_nonneg _, fun p hp => ?_⟩
  ext k
  have hk : R k < |p.1| := lt_of_le_of_lt ((le_abs_self _).trans
    (Finset.single_le_sum (f := fun k => |R k|) (fun _ _ => abs_nonneg _) (Finset.mem_univ k))) hp
  simp [halfE_apply, hR k p.1 p.2 hk]

variable (J φ) in
/-- The coefficient of `½ φ` read in `w = e^{-2π(s+it)}`. -/
def coefE : ℂ → EuclideanSpace ℝ (Fin n) := neckCoef (jE J) (halfE φ)

lemma contDiff_coefE (hφ : ∀ k, IsTest (φ k)) : ContDiff ℝ ∞ (coefE J φ) := by
  obtain ⟨R, hR0, hR⟩ := exists_halfE_supp hφ
  exact contDiff_neckCoef _ (contDiff_halfE hφ) (halfE_periodic hφ)
    ⟨R, fun p hp => hR p (lt_of_lt_of_le hp (le_abs_self _))⟩

lemma hasCompactSupport_coefE (hφ : ∀ k, IsTest (φ k)) : HasCompactSupport (coefE J φ) := by
  obtain ⟨R, hR0, hR⟩ := exists_halfE_supp hφ
  refine HasCompactSupport.intro (isCompact_closedBall (0 : ℂ) (Real.exp (2 * Real.pi * R)))
    fun w hw => ?_
  rw [Metric.mem_closedBall, dist_zero_right, not_le] at hw
  have hw0 : w ≠ 0 := by
    intro h; rw [h, norm_zero] at hw; exact absurd hw (not_lt.2 (Real.exp_pos _).le)
  have hn : ‖w‖ = Real.exp (-2 * Real.pi * (logE w).1) := by
    rw [← norm_expPolar, expPolar_logE hw0]
  rw [hn, Real.exp_lt_exp] at hw
  have : R < |(logE w).1| := by
    rw [abs_of_neg (by nlinarith [Real.pi_pos])]; nlinarith [Real.pi_pos]
  simp [coefE, neckCoef, hR _ this]

variable (J φ) in
/-- `F = T(c)`, the Cauchy transform of the coefficient. -/
def solF : ℂ → EuclideanSpace ℝ (Fin n) := cauchyT (jE J) (coefE J φ)

variable (J φ) in
/-- `F(1/w)`, `0` at `w = 0`. -/
def solG : ℂ → EuclideanSpace ℝ (Fin n) := cauchyTInv (jE J) (coefE J φ)

lemma contDiff_solF (hφ : ∀ k, IsTest (φ k)) : ContDiff ℝ ∞ (solF J φ) :=
  contDiff_cauchyT (J₀ := jE J) (hg := contDiff_coefE hφ) (hc := hasCompactSupport_coefE hφ)

lemma contDiff_solG (hφ : ∀ k, IsTest (φ k)) : ContDiff ℝ ∞ (solG J φ) :=
  contDiff_cauchyTInv (J₀ := jE J) (hg := contDiff_coefE hφ) (hc := hasCompactSupport_coefE hφ)

lemma solG_zero : solG J φ 0 = 0 := by simp [solG, cauchyTInv]

lemma solG_conj (p : ℝ × ℝ) : solG J φ ((starRingEnd ℂ) (ePol 0 (reflS p))) = solF J φ (ePol 0 p) := by
  rw [conj_ePol_reflS, solG, cauchyTInv_of_ne (inv_ne_zero (ePol_ne_zero p)), inv_inv]; rfl

end Solve

/-! ## 6. The pieces of the solution -/

section Pieces

variable {n : ℕ} {J : Fin n → Fin n → ℝ} {φ : Fin n → ℝ × ℝ → ℝ}

variable (J φ) in
/-- `u_k(s, t) = F(e^{-2π(s+it)})_k`. -/
def uK (k : Fin n) (p : ℝ × ℝ) : ℝ := solF J φ (ePol 0 p) k

lemma contDiff_uK (hφ : ∀ k, IsTest (φ k)) (k : Fin n) : ContDiff ℝ ∞ (uK J φ k) :=
  (EuclideanSpace.proj k : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ).contDiff.comp
    ((contDiff_solF hφ).comp (contDiff_ePol 0))

lemma fderiv_uK (hφ : ∀ k, IsTest (φ k)) (k : Fin n) (p v : ℝ × ℝ) :
    fderiv ℝ (uK J φ k) p v =
      fderiv ℝ (solF J φ) (ePol 0 p) (fderiv ℝ (ePol 0) p v) k := by
  have hF : Differentiable ℝ (solF J φ) := (contDiff_solF hφ).differentiable (by simp)
  have h := (EuclideanSpace.proj k : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ).hasFDerivAt.comp p
    ((hF _).hasFDerivAt.comp p ((contDiff_ePol 0).differentiable (by simp) p).hasFDerivAt)
  rw [show uK J φ k = fun p => (EuclideanSpace.proj k : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)
    (solF J φ (ePol 0 p)) from rfl]
  change fderiv ℝ ((EuclideanSpace.proj k : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) ∘ solF J φ ∘
    ePol 0) p v = _
  rw [h.fderiv]
  rfl

lemma Ds_uK (hφ : ∀ k, IsTest (φ k)) (k : Fin n) (p : ℝ × ℝ) :
    Ds (uK J φ k) p = fderiv ℝ (solF J φ) (ePol 0 p) (-2 * Real.pi * ePol 0 p) k := by
  rw [Ds, fderiv_uK hφ k p (1, 0), fderiv_ePol_s]

lemma Dt_uK (hφ : ∀ k, IsTest (φ k)) (k : Fin n) (p : ℝ × ℝ) :
    Dt (uK J φ k) p =
      fderiv ℝ (solF J φ) (ePol 0 p) (-2 * Real.pi * ePol 0 p * Complex.I) k := by
  rw [Dt, fderiv_uK hφ k p (0, 1), fderiv_ePol_t,
    show (-2 * Real.pi * Complex.I * ePol 0 p : ℂ) = -2 * Real.pi * ePol 0 p * Complex.I by ring]

/-- **`∂_s u + J ∂_t u = φ`** pointwise. -/
theorem dbar_uK (hJ : IsCxMat J) (hφ : ∀ k, IsTest (φ k)) (k : Fin n) (p : ℝ × ℝ) :
    Ds (uK J φ k) p + ∑ l, J k l * Dt (uK J φ l) p = φ k p := by
  simp only [Ds_uK hφ, Dt_uK hφ]
  set w := ePol 0 p
  set L := fderiv ℝ (solF J φ) w
  set c : ℂ := -2 * Real.pi * w
  have h1 : L c + jE J (L (c * Complex.I)) =
      (2 : ℝ) • cmulL (jE J) ((starRingEnd ℂ) c) (dbar (jE J) (solF J φ) w) := by
    rw [dbar_eq_dbarL, ← dbarL_comp_mul (jE_sq hJ)]
    simp only [dbarL, ContinuousLinearMap.comp_apply, ContinuousLinearMap.mul_apply', mul_one,
      smul_smul]
    norm_num
    rfl
  have h2 : dbar (jE J) (solF J φ) w = coefE J φ w :=
    dbar_cauchyT (jE_sq hJ) ((contDiff_coefE hφ).of_le (by simp)) (hasCompactSupport_coefE hφ) w
  have h3 : cmulL (jE J) ((starRingEnd ℂ) c) (coefE J φ w) = halfE φ p := by
    simp only [c, w, ePol_zero_eq]
    exact cmulL_neckCoef (jE_sq hJ) (halfE_periodic hφ) p
  have h4 := congrArg (fun v : EuclideanSpace ℝ (Fin n) => v k) h1
  simp only [PiLp.add_apply, jE_apply, h2, h3, PiLp.smul_apply, halfE_apply, smul_eq_mul] at h4
  rw [h4]; ring

lemma norm_ePol0 (p : ℝ × ℝ) : ‖ePol 0 p‖ = Real.exp (-2 * Real.pi * p.1) := by
  rw [norm_ePol, add_zero]

lemma sq_norm_ePol_small {p : ℝ × ℝ} (hp : 1 ≤ p.1) : ‖ePol 0 p‖ ^ 2 ≤ 1 / 4 := by
  rw [norm_ePol0]
  have h1 := Real.add_one_le_exp (2 * Real.pi * p.1)
  have h2 : Real.exp (-2 * Real.pi * p.1) * Real.exp (2 * Real.pi * p.1) = 1 := by
    rw [← Real.exp_add]; simp
  have h3 : 0 < Real.exp (-2 * Real.pi * p.1) := Real.exp_pos _
  have hx : 2 ≤ Real.exp (2 * Real.pi * p.1) := by nlinarith [Real.pi_gt_three]
  have h4 : Real.exp (-2 * Real.pi * p.1) ≤ 1 / 2 := by
    nlinarith [mul_le_mul_of_nonneg_left hx h3.le]
  nlinarith

lemma sq_norm_ePol_large {p : ℝ × ℝ} (hp : p.1 ≤ 0) : 1 / 2 ≤ ‖ePol 0 p‖ ^ 2 := by
  rw [norm_ePol0]
  have : 1 ≤ Real.exp (-2 * Real.pi * p.1) := Real.one_le_exp (by nlinarith [Real.pi_pos])
  nlinarith

variable (J φ) in
/-- The part of `u` near `s = +∞`: `χ(w) (F(w) - F(0))_k`, `w = e^{-2π(s+it)}`. -/
def aK (k : Fin n) : ℝ × ℝ → ℝ :=
  (fun w => cutC w * (fun w => solF J φ w - solF J φ 0) w k) ∘ ePol 0

variable (J φ) in
/-- The part of `u` near `s = -∞`: `χ(w̄) G(w̄)_k` at the reflected point, `G(w) = F(1/w)`. -/
def bK (k : Fin n) : ℝ × ℝ → ℝ :=
  ((fun w => cutC w * (fun w => solG J φ ((starRingEnd ℂ) w)) w k) ∘ ePol 0) ∘ reflS

variable (J φ) in
/-- `r_k = u_k - F(0)_k (1 - β(s))`. -/
def rK (β : ℝ → ℝ) (k : Fin n) (p : ℝ × ℝ) : ℝ := uK J φ k p - solF J φ 0 k * (1 - β p.1)

lemma neckCls_aK (hφ : ∀ k, IsTest (φ k)) (k : Fin n) :
    NeckCls 1 (fun w => cutC w * (fun w => solF J φ w - solF J φ 0) w k) :=
  neckCls_cut ((contDiff_solF hφ).sub contDiff_const) (sub_self _) k

lemma neckCls_bK (hφ : ∀ k, IsTest (φ k)) (k : Fin n) :
    NeckCls 1 (fun w => cutC w * (fun w => solG J φ ((starRingEnd ℂ) w)) w k) :=
  neckCls_cut ((contDiff_solG hφ).comp Complex.conjCLE.contDiff) (by simp [solG_zero]) k

lemma isTest_tK {β : ℝ → ℝ} (hβ : IsCutoff β) (hφ : ∀ k, IsTest (φ k)) (k : Fin n) :
    IsTest (rK J φ β k - aK J φ k - bK J φ k) where
  smooth := (((contDiff_uK hφ k).sub (contDiff_const.mul (contDiff_const.sub
    (hβ.smooth.comp contDiff_fst)))).sub ((neckCls_aK hφ k).smooth.comp (contDiff_ePol 0))).sub
    (((neckCls_bK hφ k).smooth.comp (contDiff_ePol 0)).comp reflL.contDiff)
  periodic s t := by
    simp only [Pi.sub_apply, rK, uK, aK, bK, Function.comp_apply, reflS, ePol_add_one]
  bddSupp := ⟨1, fun s t hs => by
    have hev := solG_conj (J := J) (φ := φ) (s, t)
    rcases lt_abs.1 hs with h | h
    · have ha := cutC_one (sq_norm_ePol_small (p := (s, t)) h.le)
      have hb := cutC_zero (sq_norm_ePol_large (p := reflS (s, t)) (by simp [reflS]; linarith))
      simp only [Pi.sub_apply, rK, uK, aK, bK, Function.comp_apply, ha, hb, hβ.zero_of_ge h.le,
        PiLp.sub_apply]
      ring
    · have ha := cutC_zero (sq_norm_ePol_large (p := (s, t)) (by simp; linarith))
      have hb := cutC_one (sq_norm_ePol_small (p := reflS (s, t)) (by simp [reflS]; linarith))
      simp only [Pi.sub_apply, rK, uK, aK, bK, Function.comp_apply, ha, hb,
        hβ.one_of_le s (by linarith), hev]
      ring⟩

lemma rK_eq (β : ℝ → ℝ) (k : Fin n) :
    rK J φ β k = aK J φ k + bK J φ k + (rK J φ β k - aK J φ k - bK J φ k) := by
  funext p; simp only [Pi.add_apply, Pi.sub_apply]; ring

lemma smoothW_rK {β : ℝ → ℝ} (hβ : IsCutoff β) (hφ : ∀ k, IsTest (φ k)) (k : Fin n) {δ : ℝ}
    (hδ : δ < 2 * Real.pi) : SmoothW δ (rK J φ β k) := by
  rw [rK_eq β k]
  exact (((neckCls_aK hφ k).smoothW hδ).add ((neckCls_bK hφ k).smoothW hδ).refl).add
    ((isTest_tK hβ hφ k).smoothW δ)

lemma Ds_fun_s {χ : ℝ → ℝ} (hχ : Differentiable ℝ χ) : Ds (fun x => χ x.1) = fun x => deriv χ x.1 := by
  funext ⟨s, t⟩
  exact (hasDerivAt_s (φ := fun x => χ x.1) (hχ.comp differentiable_fst) s t).unique
    (hχ s).hasDerivAt

lemma Dt_fun_s {χ : ℝ → ℝ} (hχ : Differentiable ℝ χ) : Dt (fun x => χ x.1) = fun _ => 0 := by
  funext ⟨s, t⟩
  exact (hasDerivAt_t (φ := fun x => χ x.1) (hχ.comp differentiable_fst) s t).unique
    (hasDerivAt_const t (χ s))

lemma Ds_sub_fun {f g : ℝ × ℝ → ℝ} (hf : Differentiable ℝ f) (hg : Differentiable ℝ g) :
    Ds (f - g) = Ds f - Ds g := by
  funext x; simp only [Ds, Pi.sub_apply]; rw [fderiv_sub (hf x) (hg x)]; rfl

lemma Dt_sub_fun {f g : ℝ × ℝ → ℝ} (hf : Differentiable ℝ f) (hg : Differentiable ℝ g) :
    Dt (f - g) = Dt f - Dt g := by
  funext x; simp only [Dt, Pi.sub_apply]; rw [fderiv_sub (hf x) (hg x)]; rfl

/-- **The classical equation for `r`**: `∂_s r_k + ∑_l J_{kl} ∂_t r_l = φ_k + F(0)_k β'(s)`. -/
theorem dbar_rK (hJ : IsCxMat J) {β : ℝ → ℝ} (hβ : IsCutoff β) (hφ : ∀ k, IsTest (φ k))
    (k : Fin n) (p : ℝ × ℝ) :
    Ds (rK J φ β k) p + ∑ l, J k l * Dt (rK J φ β l) p =
      φ k p + solF J φ 0 k * deriv β p.1 := by
  have hb : ∀ l, Differentiable ℝ (fun s : ℝ => solF J φ 0 l * (1 - β s)) := fun l =>
    (differentiable_const _).mul ((differentiable_const _).sub
      (hβ.smooth.differentiable (by simp)))
  have hu : ∀ l, Differentiable ℝ (uK J φ l) := fun l =>
    (contDiff_uK hφ l).differentiable (by simp)
  have e : ∀ l, rK J φ β l = uK J φ l - fun x => (fun s => solF J φ 0 l * (1 - β s)) x.1 :=
    fun l => rfl
  have hs : ∀ l, Ds (rK J φ β l) p = Ds (uK J φ l) p + solF J φ 0 l * deriv β p.1 := by
    intro l
    rw [e, Ds_sub_fun (g := fun x => (fun s => solF J φ 0 l * (1 - β s)) x.1) (hu l)
      ((hb l).comp differentiable_fst), Pi.sub_apply, Ds_fun_s (hb l)]
    have : deriv (fun s => solF J φ 0 l * (1 - β s)) p.1 = -(solF J φ 0 l * deriv β p.1) := by
      have hd := (((hasDerivAt_const p.1 (1 : ℝ)).sub
        (hβ.smooth.differentiable (by simp) p.1).hasDerivAt).const_mul (solF J φ 0 l))
      exact hd.deriv.trans (by ring)
    change Ds (uK J φ l) p - deriv (fun s => solF J φ 0 l * (1 - β s)) p.1 = _
    rw [this]; ring
  have ht : ∀ l, Dt (rK J φ β l) p = Dt (uK J φ l) p := by
    intro l
    rw [e, Dt_sub_fun (g := fun x => (fun s => solF J φ 0 l * (1 - β s)) x.1) (hu l)
      ((hb l).comp differentiable_fst), Pi.sub_apply, Dt_fun_s (hb l),
      sub_zero]
  simp only [hs, ht]
  have := dbar_uK hJ hφ k p
  linarith

/-- **Smooth solutions for test tuples**: for `J² = -1`, a cut-off `β` of (2.1) and a tuple `φ`
of test functions there are `c ∈ ℝⁿ` and smooth tuples `r`, in `SmoothW δ` for every `δ < 2π`,
with `∂_s r_k + ∑_l J_{kl} ∂_t r_l = φ_k + 2 c_k β'(s)`.  So `u = (1 - 2β(s)) c + r` solves
`∂_s u + J ∂_t u = φ`, with the antipodal asymptotic constants `±c`. -/
theorem exists_smooth_solution (hJ : IsCxMat J) {β : ℝ → ℝ} (hβ : IsCutoff β)
    (hφ : ∀ k, IsTest (φ k)) :
    ∃ (c : Fin n → ℝ) (r : Fin n → ℝ × ℝ → ℝ), (∀ k δ, δ < 2 * Real.pi → SmoothW δ (r k)) ∧
      ∀ k x, Ds (r k) x + ∑ l, J k l * Dt (r l) x = φ k x + 2 * c k * deriv β x.1 := by
  refine ⟨fun k => solF J φ 0 k / 2, rK J φ β, fun k δ hδ => smoothW_rK hβ hφ k hδ,
    fun k x => ?_⟩
  rw [dbar_rK hJ hβ hφ k x]; ring

end Pieces

end GWMemoir
