import GWMemoir.GluingUniformPi

/-!
# Memoir §4.3: the norm of the constant on `Z_a`, and `π_a` uniformly in `a`

HWZ, *Applications of Polyfold Theory I*, Memoirs AMS 248, no. 1179, §4.3, pp. 107–108 (with the
projection `π_a` of p. 50).

`constBound`: for `δ_m > 0` the class of the constant `χ_Z` in `H^{3+m}(Z_a)` has
`|χ_Z|²_{Z_a} ≤ K e^{δ_m R}` with `K` independent of `R ≥ 2`.  The representative is the bump
`ψ_R(s) = β(s + 1) β(R + 1 - s)` (`β` the smooth transition), equal to `1` on `[0, R]`, supported
in `[-1, R + 1]`, with derivatives bounded independently of `R`; on `[-1, R + 1]` the weight of
(4.7) is `≤ e^{2δ_m} e^{δ_m R/2} e^{-δ_m |s - R/2|}`.

`pi_uniform`, `pi_uniform_a`: for `δ_m > 0`, `‖π_a x‖ ≤ C ‖x‖` with `C` independent of `a`.  This
covers every level `m ≥ 1`, and the level `0` when `δ_0 > 0`.  For `δ_0 = 0` the norm of the constant
on `Z_a` at level `0` grows like `R`, and the bound at that level is not uniform.
-/

open Set Filter Topology MeasureTheory Finset
open scoped ENNReal NNReal ContDiff
open Polyfold Polyfold.CylinderSobolev

namespace GWMemoir.Neck

/-! ## Derivatives of functions of `s` alone -/

lemma Dt_fst {f : ℝ → ℝ} (hf : Differentiable ℝ f) : Dt (fun x : ℝ × ℝ => f x.1) = 0 := by
  funext x
  obtain ⟨s, t⟩ := x
  exact (hasDerivAt_t (φ := fun x : ℝ × ℝ => f x.1) (hf.comp differentiable_fst) s t).unique
    (hasDerivAt_const t (f s))

lemma Ds_fst {f : ℝ → ℝ} (hf : Differentiable ℝ f) :
    Ds (fun x : ℝ × ℝ => f x.1) = fun x => deriv f x.1 := by
  funext x
  obtain ⟨s, t⟩ := x
  exact (hasDerivAt_s (φ := fun x : ℝ × ℝ => f x.1) (hf.comp differentiable_fst) s t).unique
    (hf s).hasDerivAt

lemma iterate_Ds_fst {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) (a : ℕ) :
    Ds^[a] (fun x : ℝ × ℝ => f x.1) = fun x => iteratedDeriv a f x.1 := by
  induction a with
  | zero => simp
  | succ a ih =>
    rw [Function.iterate_succ_apply', ih,
      Ds_fst (hf.differentiable_iteratedDeriv a (by exact_mod_cast WithTop.coe_lt_top _)),
      iteratedDeriv_succ]

lemma pD_fst {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) (a b : ℕ) :
    pD a b (fun x : ℝ × ℝ => f x.1) = if b = 0 then fun x => iteratedDeriv a f x.1 else (0 : ℝ × ℝ → ℝ) := by
  rcases b with _ | b
  · simp [pD, iterate_Ds_fst hf a]
  · have hDt0 : Dt (0 : ℝ × ℝ → ℝ) = 0 := by funext x; simp [Dt]
    have hDs0 : Ds (0 : ℝ × ℝ → ℝ) = 0 := by funext x; simp [Ds]
    rw [pD, Function.iterate_succ_apply, Dt_fst (hf.differentiable (by simp)),
      Function.iterate_fixed hDt0, Function.iterate_fixed hDs0]
    simp

lemma dv_toH_fst {k : ℕ} {d : ℝ} {hd : 0 ≤ d} {f : ℝ → ℝ}
    (hφ : IsTest fun x : ℝ × ℝ => f x.1) (p : idx k) :
    dv (H.toSub (toH k hd hφ)) p =ᵐ[cyl] pD p.1.1 p.1.2 (fun x : ℝ × ℝ => f x.1) :=
  dv_unique _ p ((hφ.smPer.hasWeakDeriv _ _).congr_ae (hφ.memLp 2).coeFn_toLp.symm
    (ae_eq_refl _)) ((hφ.pD _ _).memLp 2)

/-! ## The bump `ψ_R` -/

/-- `ψ_R(s) = β(s + 1) β(R + 1 - s)`: `1` on `[0, R]`, `0` off `(-1, R + 1)`. -/
noncomputable def bumpZ (R s : ℝ) : ℝ := ηP (s + 1) * ηN (s - (R + 1))

lemma contDiff_bumpZ (R : ℝ) : ContDiff ℝ ∞ (bumpZ R) := by
  unfold bumpZ ηP ηN
  exact ((Real.smoothTransition.contDiff (n := ⊤)).comp (by fun_prop)).mul
    ((Real.smoothTransition.contDiff (n := ⊤)).comp (by fun_prop))

lemma bumpZ_lo {R s : ℝ} (hs : s ≤ -1) : bumpZ R s = 0 := by
  rw [bumpZ, ηP, Real.smoothTransition.zero_of_nonpos (by linarith), zero_mul]

lemma bumpZ_hi {R s : ℝ} (hs : R + 1 ≤ s) : bumpZ R s = 0 := by
  rw [bumpZ, ηN, Real.smoothTransition.zero_of_nonpos (by linarith), mul_zero]

lemma bumpZ_one {R s : ℝ} (hs : s ∈ Icc 0 R) : bumpZ R s = 1 := by
  rw [bumpZ, ηP, ηN, Real.smoothTransition.one_of_one_le (by linarith [hs.1]),
    Real.smoothTransition.one_of_one_le (by linarith [hs.2]), mul_one]

lemma isTest_bumpZ (R : ℝ) : IsTest fun x : ℝ × ℝ => bumpZ R x.1 :=
  isTest_of_s (contDiff_bumpZ R) (R := |R| + 1) fun s hs => by
    rcases le_abs'.1 hs with h | h
    · exact bumpZ_lo (by linarith [abs_nonneg R])
    · exact bumpZ_hi (by linarith [le_abs_self R])

/-- The derivatives of `ψ_R` are bounded independently of `R > 0`. -/
lemma bound_bumpZ (k : ℕ) : ∃ C, 0 ≤ C ∧ ∀ R, 0 < R → ∀ i ≤ k, ∀ s,
    |iteratedDeriv i (bumpZ R) s| ≤ C := by
  obtain ⟨CP, hP⟩ := (mult_ηP k).bdd
  obtain ⟨CN, hN⟩ := (mult_ηN k).bdd
  refine ⟨max (max CP CN) 0, le_max_right _ _, fun R hR i hi s => ?_⟩
  rcases lt_or_ge s R with hs | hs
  · have e : bumpZ R =ᶠ[𝓝 s] fun y => ηP (y + 1) := by
      filter_upwards [Iio_mem_nhds hs] with y hy
      rw [bumpZ, ηN, Real.smoothTransition.one_of_one_le (by linarith [show y < R from hy]), mul_one]
    rw [e.iteratedDeriv_eq i, iteratedDeriv_comp_add_const i ηP 1]
    exact (hP i hi _).trans ((le_max_left _ _).trans (le_max_left _ _))
  · have e : bumpZ R =ᶠ[𝓝 s] fun y => ηN (y - (R + 1)) := by
      filter_upwards [Ioi_mem_nhds (show 0 < s by linarith)] with y hy
      rw [bumpZ, ηP, Real.smoothTransition.one_of_one_le (by linarith [show 0 < y from hy]), one_mul]
    rw [e.iteratedDeriv_eq i, iteratedDeriv_comp_sub_const i ηN (R + 1)]
    exact (hN i hi _).trans ((le_max_right _ _).trans (le_max_left _ _))

lemma iteratedDeriv_bumpZ_out {R s : ℝ} (hs : s ∉ Icc (-1) (R + 1)) (i : ℕ) :
    iteratedDeriv i (bumpZ R) s = 0 := by
  simp only [Set.mem_Icc, not_and_or, not_le] at hs
  have h : bumpZ R =ᶠ[𝓝 s] 0 := by
    rcases hs with hs | hs
    · filter_upwards [Iio_mem_nhds hs] with y hy using bumpZ_lo hy.le
    · filter_upwards [Ioi_mem_nhds hs] with y hy using bumpZ_hi hy.le
  rw [h.iteratedDeriv_eq i]; simp

/-- On `[-1, R + 1]`: `min(|s|, |s - R|) ≤ R/2 + 2 - |s - R/2|`. -/
lemma min_abs_le {R s : ℝ} (hs : s ∈ Icc (-1) (R + 1)) :
    min |s| |s - R| ≤ R / 2 + 2 - |s - R / 2| := by
  obtain ⟨h1, h2⟩ := hs
  rcases le_total s (R / 2) with h | h
  · have := min_le_left |s| |s - R|
    rcases abs_cases s with ⟨e1, _⟩ | ⟨e1, _⟩ <;>
      rcases abs_cases (s - R / 2) with ⟨e2, _⟩ | ⟨e2, _⟩ <;> linarith
  · have := min_le_right |s| |s - R|
    rcases abs_cases (s - R) with ⟨e1, _⟩ | ⟨e1, _⟩ <;>
      rcases abs_cases (s - R / 2) with ⟨e2, _⟩ | ⟨e2, _⟩ <;> linarith

/-! ## The decaying weight -/

lemma integrable_exp_neg_abs {a : ℝ} (ha : 0 < a) :
    Integrable (fun s : ℝ => Real.exp (-a * |s|)) := by
  have hg : Integrable ((Ici (0 : ℝ)).indicator fun s => Real.exp (-a * s)) :=
    (integrable_indicator_iff measurableSet_Ici).2
      ((integrableOn_Ici_iff_integrableOn_Ioi (by simp)).2 (exp_neg_integrableOn_Ioi 0 ha))
  refine (hg.add hg.comp_neg).mono' (by fun_prop) (Eventually.of_forall fun s => ?_)
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  have h1 := Set.indicator_nonneg (s := Ici (0 : ℝ)) (f := fun s => Real.exp (-a * s))
    (fun _ _ => (Real.exp_pos _).le) s
  have h2 := Set.indicator_nonneg (s := Ici (0 : ℝ)) (f := fun s => Real.exp (-a * s))
    (fun _ _ => (Real.exp_pos _).le) (-s)
  simp only [Pi.add_apply]
  rcases le_total 0 s with h | h
  · rw [Set.indicator_of_mem (show s ∈ Ici (0 : ℝ) from h), abs_of_nonneg h]; linarith
  · rw [Set.indicator_of_mem (show -s ∈ Ici (0 : ℝ) by simp; linarith), abs_of_nonpos h]
    simp only [mul_neg] at *; linarith

lemma memLp_exp_neg_abs {d : ℝ} (hd : 0 < d) :
    MemLp (fun x : ℝ × ℝ => Real.exp (-d * |x.1|)) 2 cyl := by
  have h : MemLp (fun s : ℝ => Real.exp (-d * |s|)) 2 volume := by
    refine (memLp_two_iff_integrable_sq (by fun_prop)).2 ?_
    have e : (fun s : ℝ => Real.exp (-d * |s|) ^ 2) = fun s => Real.exp (-(2 * d) * |s|) := by
      funext s; rw [← Real.exp_nat_mul]; ring_nf
    rw [e]
    exact integrable_exp_neg_abs (by linarith)
  exact h.comp_fst _

/-- Translation in `s`. -/
lemma eLpNorm_exp_neg_abs_sub (d c : ℝ) :
    eLpNorm (fun x : ℝ × ℝ => Real.exp (-d * |x.1 - c|)) 2 cyl =
      eLpNorm (fun x : ℝ × ℝ => Real.exp (-d * |x.1|)) 2 cyl := by
  have hg : Continuous fun x : ℝ × ℝ => Real.exp (-d * |x.1|) := by fun_prop
  exact eLpNorm_comp_measurePreserving (p := 2) (μ := cyl) (ν := cyl) (f := shT c 0)
    (g := fun x : ℝ × ℝ => Real.exp (-d * |x.1|)) hg.aestronglyMeasurable
    (measurePreserving_shT c 0)

/-! ## The norm of the constant -/

/-- `δ_m > 0` for `m ≥ 1`. -/
lemma δ_pos_of_one_le {δ : ℕ → ℝ} (h0 : 0 ≤ δ 0) (hmono : StrictMono δ) {m : ℕ} (hm : 1 ≤ m) :
    0 < δ m :=
  lt_of_le_of_lt h0 (hmono (by omega))

section Const

variable {δ : ℕ → ℝ} {h0 : 0 ≤ δ 0} {hmono : StrictMono δ}

/-- `ψ_R` represents `χ_Z` on `Z_a`. -/
lemma qZo_bumpZ (R : ℝ) (m : ℕ) :
    qZo 3 δ h0 hmono (R := R) m (toH (3 + m) (δ_nonneg δ h0 hmono m) (isTest_bumpZ R)) =
      gZ δ h0 hmono (R := R) m := by
  refine (Submodule.Quotient.eq _).2 (memLo.2 ?_)
  have e := map_sub (valCLM (3 + m) (δ_nonneg δ h0 hmono m))
    (toH (3 + m) (δ_nonneg δ h0 hmono m) (isTest_bumpZ R))
    (toH (3 + m) (δ_nonneg δ h0 hmono m) (isTest_chiZ R))
  unfold Van
  filter_upwards [Lp.coeFn_sub (valCLM (3 + m) (δ_nonneg δ h0 hmono m)
        (toH (3 + m) (δ_nonneg δ h0 hmono m) (isTest_bumpZ R)))
      (valCLM (3 + m) (δ_nonneg δ h0 hmono m)
        (toH (3 + m) (δ_nonneg δ h0 hmono m) (isTest_chiZ R))),
    GWMemoir.Neck.val_toH (m := 3 + m) (hδ := δ_nonneg δ h0 hmono m) (isTest_bumpZ R),
    GWMemoir.Neck.val_toH (m := 3 + m) (hδ := δ_nonneg δ h0 hmono m) (isTest_chiZ R)]
    with x h1 h2 h3 hx
  erw [e, h1, Pi.sub_apply, h2, h3]
  rw [bumpZ_one ⟨hx.1.le, hx.2.le⟩, chiZ_one ⟨hx.1.le, hx.2.le⟩, sub_self]

theorem constBound (m : ℕ) (hd : 0 < δ m) : ConstBound δ h0 hmono m := by
  set d := δ m
  obtain ⟨C, hC, hb⟩ := bound_bumpZ (3 + m)
  have hE := memLp_exp_neg_abs hd
  set E0 := eLpNorm (fun x : ℝ × ℝ => Real.exp (-d * |x.1|)) 2 cyl
  have hE0 : E0 ≠ ⊤ := hE.eLpNorm_ne_top
  set N := Fintype.card (idx (3 + m))
  set A := C * Real.exp (2 * d)
  refine ⟨N * (A ^ 2 * E0.toReal ^ 2), by positivity, fun R hR2 => ?_⟩
  have hR : 0 < R := by linarith
  set u := toH (3 + m) (δ_nonneg δ h0 hmono m) (isTest_bumpZ R)
  set B := A * Real.exp (d * R / 2)
  have hB : 0 ≤ B := by positivity
  have hpt : ∀ p : idx (3 + m), guDv (guZ d R) u p ≤ ENNReal.ofReal B * E0 := fun p => by
    unfold guDv
    rw [show E0 = eLpNorm (fun x : ℝ × ℝ => Real.exp (-d * |x.1 - R / 2|)) 2 cyl from
      (eLpNorm_exp_neg_abs_sub d (R / 2)).symm, ← Real.enorm_eq_ofReal hB, ← eLpNorm_const_smul]
    rw [eLpNorm_congr_ae (g := fun x : ℝ × ℝ =>
      guZ d R x.1 * pD p.1.1 p.1.2 (fun x : ℝ × ℝ => bumpZ R x.1) x)]
    swap
    · filter_upwards [dv_toH_fst (isTest_bumpZ R) p] with x hx
      rw [hx]
    refine eLpNorm_mono fun x => ?_
    simp only [Pi.smul_apply, smul_eq_mul, Real.norm_eq_abs, abs_mul, abs_of_nonneg hB,
      abs_of_pos (Real.exp_pos _), abs_of_pos (guZ_pos _ _ _)]
    rw [pD_fst (contDiff_bumpZ R)]
    split_ifs with hb0
    swap
    · simp only [Pi.zero_apply, abs_zero, mul_zero]; positivity
    have hi : p.1.1 ≤ 3 + m := by have := mem_idx.1 p.2; omega
    beta_reduce
    by_cases hs : x.1 ∈ Icc (-1) (R + 1)
    · have hz : guZ d R x.1 ≤
          Real.exp (2 * d) * Real.exp (d * R / 2) * Real.exp (-d * |x.1 - R / 2|) := by
        rw [guZ, ← Real.exp_add, ← Real.exp_add]
        refine Real.exp_le_exp.2 ?_
        have := mul_le_mul_of_nonneg_left (min_abs_le hs) hd.le
        nlinarith
      calc guZ d R x.1 * |iteratedDeriv p.1.1 (bumpZ R) x.1|
          ≤ (Real.exp (2 * d) * Real.exp (d * R / 2) * Real.exp (-d * |x.1 - R / 2|)) * C :=
            mul_le_mul hz (hb R hR _ hi _) (abs_nonneg _) (by positivity)
        _ = B * Real.exp (-d * |x.1 - R / 2|) := by simp only [B, A]; ring
    · rw [iteratedDeriv_bumpZ_out hs, abs_zero, mul_zero]; positivity
  have hsq : guSq (guZ d R) u ≤ (N : ℝ≥0∞) * (ENNReal.ofReal B * E0) ^ 2 := by
    calc guSq (guZ d R) u ≤ ∑ _p : idx (3 + m), (ENNReal.ofReal B * E0) ^ 2 :=
          Finset.sum_le_sum fun p _ => pow_le_pow_left' (hpt p) 2
      _ = _ := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hE0' : E0 = ENNReal.ofReal E0.toReal := (ENNReal.ofReal_toReal hE0).symm
  have hexp : Real.exp (d * R / 2) ^ 2 = Real.exp (d * R) := by
    rw [← Real.exp_nat_mul]; ring_nf
  refine (guZSq_le u (qZo_bumpZ R m)).trans (hsq.trans (le_of_eq ?_))
  conv_lhs => rw [hE0']
  rw [← ENNReal.ofReal_mul hB, ← ENNReal.ofReal_pow (by positivity), ← ENNReal.ofReal_natCast,
    ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  simp only [B, mul_pow, hexp]; ring

variable {β : ℝ → ℝ} (hβ : IsCutoff β)

/-- **The projection `π_a`, uniformly in `a`** (Memoir pp. 50, 108), for `δ_m > 0`: there is `C > 0`
with `‖π_a x‖ ≤ C ‖x‖` for all `R ≥ 2` and twists `ϑ`. -/
theorem pi_uniform (m : ℕ) (hd : 0 < δ m) :
    ∃ C, 0 < C ∧ ∀ R (hR2 : 2 ≤ R) ϑ (x : (scPair δ h0 hmono) m),
      ‖piLvl δ h0 hmono hβ hR2 ϑ m x‖ ≤ C * ‖x‖ :=
  pi_uniform_of_traceBound hβ m (traceBound_of_constBound m (constBound m hd))

/-- The same in terms of the gluing parameter: for every `0 < |a| < 1/2`. -/
theorem pi_uniform_a (m : ℕ) (hd : 0 < δ m) :
    ∃ C, 0 < C ∧ ∀ {a : ℂ} (ha0 : a ≠ 0) (ha : ‖a‖ < 1 / 2) (x : (scPair δ h0 hmono) m),
      ‖piLvl δ h0 hmono hβ (two_le_glLength ha0 ha) (glTwist a) m x‖ ≤ C * ‖x‖ :=
  pi_uniform_of_traceBound_a hβ m (traceBound_of_constBound m (constBound m hd))

end Const

end GWMemoir.Neck
