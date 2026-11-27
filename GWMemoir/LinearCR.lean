import GWMemoir.FormsDensity
import GWMemoir.CompletenessForms

/-!
# The linearized Cauchy–Riemann operator at a constant map: the operator

HWZ, *Applications of Polyfold Theory I*, Memoirs AMS 248, no. 1179, §4 (Propositions 4.7, 4.23,
4.25 concern the linearizations of `∂̄_J`).  At a constant map `u ≡ q` the linearization of
`∂̄_J` in the direction of a section `η` of `u*TQ = S × T_qQ` is the standard operator
`D η = ½ (dη + J(q) ∘ dη ∘ j)`.  This file builds `D` on the level-`0` spaces of
`GWMemoir.SectionSpaces` and `GWMemoir.Fibres` (surfaces without nodes, charts onto `ℝ²`, e.g.
the three-pointed sphere).

* `dsH`, `dtH`: `∂_s, ∂_t : H^{k+1,δ}(ℝ × S¹) → H^{k,δ}(ℝ × S¹)`, of norm `≤ 1`.
* **`exists_C1_rep`** (`H³ ⊂ C¹`): every `w ∈ H^{3,δ}` has a continuous representative `g`,
  differentiable on the open strip with continuous partial derivatives representing `∂_s w`,
  `∂_t w`.  The test functions converging to `w` in `H³` converge uniformly with their first
  derivatives, by the sup bound of `GWMemoir.Completeness` on `H²`.
* `GlueData`: a smooth partition of unity subordinate to the discs and the changes of disc
  charts on its pieces (`exists_glueData`).
* `zOp`: the zeroth-order term `(Zv)_{i,d,k} = ∑_j (∂_d β)(ρ_j ∘ discPt_i)/(β ∘ trans_{ij}) ·
  (v_{j,k} ∘ trans_{ij})` (`ChartChange.op`); on the representative of any section it is
  `∂_d β · η_k` read in the disc (`zOp_rep`).
* `rOp`: `(Rv)_{i,d,k} = ε_i⁻¹ (∂_d v_{i,k} - (Zv)_{i,d,k})`, the derivative read in the disc
  charts without the derivative of the cut-off.  **`linOp J₀ = ½ (R + P R)`**, `P` the
  projection term of `GWMemoir.FormsDensity`: a bounded operator from the section blocks to the
  fibre blocks.
-/

set_option maxSynthPendingDepth 3
set_option linter.unusedSectionVars false

open scoped Manifold ContDiff Topology
open Set Function Filter MeasureTheory
open Polyfold Polyfold.CylinderSobolev

noncomputable section

namespace GWMemoir

/-! ## 1. The derivatives `∂_s, ∂_t : H^{k+1,δ} → H^{k,δ}` -/

section Deriv

variable {k : ℕ} {δ : ℝ} {hδ : 0 ≤ δ}

lemma HasWeakDeriv.shift_s {a b : ℕ} {U g h : ℝ × ℝ → ℝ} (hg : HasWeakDeriv 1 0 U g)
    (hh : HasWeakDeriv (a + 1) b U h) : HasWeakDeriv a b g h := fun φ hφ => by
  have h1 := hg (pD a b φ) (hφ.pD a b)
  have h2 := hh φ hφ
  simp only [pD, Function.iterate_one, Function.iterate_zero, id] at h1
  rw [show Ds (Ds^[a] (Dt^[b] φ)) = pD (a + 1) b φ from ChartChange.Ds_pD φ a b, h2] at h1
  change ∫ x, g x * (Ds^[a] (Dt^[b] φ)) x ∂cyl = _
  have e : ((-1 : ℝ) ^ (a + 1 + b)) = -(-1) ^ (a + b) := by ring
  rw [e] at h1
  norm_num at h1
  linarith

lemma HasWeakDeriv.shift_t {a b : ℕ} {U g h : ℝ × ℝ → ℝ} (hg : HasWeakDeriv 0 1 U g)
    (hh : HasWeakDeriv a (b + 1) U h) : HasWeakDeriv a b g h := fun φ hφ => by
  have h1 := hg (pD a b φ) (hφ.pD a b)
  have h2 := hh φ hφ
  simp only [pD, Function.iterate_one, Function.iterate_zero, id] at h1
  rw [show Dt (Ds^[a] (Dt^[b] φ)) = pD a (b + 1) φ from ChartChange.Dt_pD hφ.smooth a b, h2] at h1
  change ∫ x, g x * (Ds^[a] (Dt^[b] φ)) x ∂cyl = _
  have e : ((-1 : ℝ) ^ (a + (b + 1))) = -(-1) ^ (a + b) := by ring
  rw [e] at h1
  norm_num at h1
  linarith

/-- The multi-index `(1, 0)`. -/
def idxS (k : ℕ) : CylinderSobolev.idx (k + 1) := ⟨(1, 0), mem_idx.2 (by omega)⟩
/-- The multi-index `(0, 1)`. -/
def idxT (k : ℕ) : CylinderSobolev.idx (k + 1) := ⟨(0, 1), mem_idx.2 (by omega)⟩

lemma memH_ds (u : H (k + 1) hδ) : MemH k δ (dvCLM (k + 1) hδ (idxS k) u) := by
  intro a b hab
  refine ⟨dv (H.toSub u) ⟨(a + 1, b), mem_idx.2 (by omega)⟩, ?_,
    (dv_spec (H.toSub u) _).2⟩
  refine HasWeakDeriv.congr_ae ?_ (coeFn_dvCLM (idxS k) u).symm (ae_eq_refl _)
  exact HasWeakDeriv.shift_s (dv_spec (H.toSub u) (idxS k)).1
    (dv_spec (H.toSub u) ⟨(a + 1, b), mem_idx.2 (by omega)⟩).1

lemma memH_dt (u : H (k + 1) hδ) : MemH k δ (dvCLM (k + 1) hδ (idxT k) u) := by
  intro a b hab
  refine ⟨dv (H.toSub u) ⟨(a, b + 1), mem_idx.2 (by omega)⟩, ?_,
    (dv_spec (H.toSub u) _).2⟩
  refine HasWeakDeriv.congr_ae ?_ (coeFn_dvCLM (idxT k) u).symm (ae_eq_refl _)
  exact HasWeakDeriv.shift_t (dv_spec (H.toSub u) (idxT k)).1
    (dv_spec (H.toSub u) ⟨(a, b + 1), mem_idx.2 (by omega)⟩).1

/-- The norm of a shifted family of derivatives. -/
lemma norm_shift_le (u : H (k + 1) hδ) (w : H k hδ) (sh : ℕ × ℕ ↪ ℕ × ℕ)
    (hsh : ∀ p : CylinderSobolev.idx k, sh p.1 ∈ CylinderSobolev.idx (k + 1))
    (hw : ∀ p : CylinderSobolev.idx k, dv (H.toSub w) p =ᵐ[cyl] dv (H.toSub u) ⟨sh p.1, hsh p⟩) :
    ‖w‖ ≤ ‖u‖ := by
  set F : ℕ × ℕ → ℝ := fun q => if hq : q ∈ CylinderSobolev.idx (k + 1) then
    ‖wdv (H.toSub u) ⟨q, hq⟩‖ ^ 2 else 0
  have hpt : ∀ p : CylinderSobolev.idx k, ‖wdv (H.toSub w) p‖ ^ 2 = F (sh p.1) := by
    intro p
    simp only [F, dif_pos (hsh p)]
    have e : wdv (H.toSub w) p = wdv (H.toSub u) ⟨sh p.1, hsh p⟩ := by
      refine Lp.ext ?_
      filter_upwards [coeFn_wdv (H.toSub w) p, coeFn_wdv (H.toSub u) ⟨sh p.1, hsh p⟩, hw p]
        with x h1 h2 h3
      rw [h1, h2, h3]
    rw [e]
  have hsq : ‖w‖ ^ 2 ≤ ‖u‖ ^ 2 := by
    rw [norm_sq_H, norm_sq_H]
    calc ∑ p : CylinderSobolev.idx k, ‖wdv (H.toSub w) p‖ ^ 2 =
          ∑ p : CylinderSobolev.idx k, F (sh p.1) :=
          Finset.sum_congr rfl fun p _ => hpt p
      _ = ∑ q ∈ CylinderSobolev.idx k, F (sh q) :=
          Finset.sum_coe_sort (CylinderSobolev.idx k) (fun q => F (sh q))
      _ = ∑ q ∈ (CylinderSobolev.idx k).map sh, F q := (Finset.sum_map _ _ _).symm
      _ ≤ ∑ q ∈ CylinderSobolev.idx (k + 1), F q := by
          refine Finset.sum_le_sum_of_subset_of_nonneg (fun q hq => ?_) fun q _ _ => ?_
          · obtain ⟨p, hp, rfl⟩ := Finset.mem_map.1 hq
            exact hsh ⟨p, hp⟩
          · simp only [F]; split_ifs
            positivity
      _ = ∑ p : CylinderSobolev.idx (k + 1), F p.1 :=
          (Finset.sum_coe_sort (CylinderSobolev.idx (k + 1)) F).symm
      _ = ∑ p : CylinderSobolev.idx (k + 1), ‖wdv (H.toSub u) p‖ ^ 2 := by
          refine Finset.sum_congr rfl fun p _ => ?_
          simp only [F, dif_pos p.2]
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 hsq

/-- The shift `(a, b) ↦ (a + 1, b)`. -/
def shS : ℕ × ℕ ↪ ℕ × ℕ := ⟨fun p => (p.1 + 1, p.2), fun p q h => by
  simp only [Prod.mk.injEq, add_left_inj] at h; exact Prod.ext h.1 h.2⟩
/-- The shift `(a, b) ↦ (a, b + 1)`. -/
def shT : ℕ × ℕ ↪ ℕ × ℕ := ⟨fun p => (p.1, p.2 + 1), fun p q h => by
  simp only [Prod.mk.injEq, add_left_inj] at h; exact Prod.ext h.1 h.2⟩

/-- The `s`-derivative as a linear map. -/
def dsL (k : ℕ) (hδ : 0 ≤ δ) : H (k + 1) hδ →ₗ[ℝ] H k hδ where
  toFun u := (⟨dvCLM (k + 1) hδ (idxS k) u, memH_ds u⟩ : Hsub k hδ)
  map_add' u v := Subtype.ext (map_add (dvCLM (k + 1) hδ (idxS k)) u v)
  map_smul' c u := Subtype.ext (map_smul (dvCLM (k + 1) hδ (idxS k)) c u)

/-- The `t`-derivative as a linear map. -/
def dtL (k : ℕ) (hδ : 0 ≤ δ) : H (k + 1) hδ →ₗ[ℝ] H k hδ where
  toFun u := (⟨dvCLM (k + 1) hδ (idxT k) u, memH_dt u⟩ : Hsub k hδ)
  map_add' u v := Subtype.ext (map_add (dvCLM (k + 1) hδ (idxT k)) u v)
  map_smul' c u := Subtype.ext (map_smul (dvCLM (k + 1) hδ (idxT k)) c u)

lemma dv_dsL (u : H (k + 1) hδ) (p : CylinderSobolev.idx k) :
    dv (H.toSub (dsL k hδ u)) p =ᵐ[cyl]
      dv (H.toSub u) ⟨shS p.1, mem_idx.2 (by
        have := mem_idx.1 p.2; change p.1.1 + 1 + p.1.2 ≤ k + 1; omega)⟩ :=
  dv_unique _ p (HasWeakDeriv.congr_ae (HasWeakDeriv.shift_s (dv_spec (H.toSub u) (idxS k)).1
    (dv_spec (H.toSub u) ⟨shS p.1, _⟩).1) (coeFn_dvCLM (idxS k) u).symm (ae_eq_refl _))
    (dv_memLp _ _)

lemma dv_dtL (u : H (k + 1) hδ) (p : CylinderSobolev.idx k) :
    dv (H.toSub (dtL k hδ u)) p =ᵐ[cyl]
      dv (H.toSub u) ⟨shT p.1, mem_idx.2 (by
        have := mem_idx.1 p.2; change p.1.1 + (p.1.2 + 1) ≤ k + 1; omega)⟩ :=
  dv_unique _ p (HasWeakDeriv.congr_ae (HasWeakDeriv.shift_t (dv_spec (H.toSub u) (idxT k)).1
    (dv_spec (H.toSub u) ⟨shT p.1, _⟩).1) (coeFn_dvCLM (idxT k) u).symm (ae_eq_refl _))
    (dv_memLp _ _)

variable (k hδ) in
/-- **`∂_s : H^{k+1,δ} → H^{k,δ}`**, of norm `≤ 1`. -/
def dsH : H (k + 1) hδ →L[ℝ] H k hδ :=
  LinearMap.mkContinuous (dsL k hδ) 1 fun u => by
    rw [one_mul]
    exact norm_shift_le u _ shS _ (dv_dsL u)

variable (k hδ) in
/-- **`∂_t : H^{k+1,δ} → H^{k,δ}`**, of norm `≤ 1`. -/
def dtH : H (k + 1) hδ →L[ℝ] H k hδ :=
  LinearMap.mkContinuous (dtL k hδ) 1 fun u => by
    rw [one_mul]
    exact norm_shift_le u _ shT _ (dv_dtL u)

lemma norm_dsH_le (u : H (k + 1) hδ) : ‖dsH k hδ u‖ ≤ ‖u‖ :=
  norm_shift_le u _ shS _ (dv_dsL u)

lemma norm_dtH_le (u : H (k + 1) hδ) : ‖dtH k hδ u‖ ≤ ‖u‖ :=
  norm_shift_le u _ shT _ (dv_dtL u)

lemma coeFn_dsH (u : H (k + 1) hδ) :
    (H.val (dsH k hδ u) : ℝ × ℝ → ℝ) =ᵐ[cyl] dv (H.toSub u) (idxS k) :=
  coeFn_dvCLM (idxS k) u

lemma coeFn_dtH (u : H (k + 1) hδ) :
    (H.val (dtH k hδ u) : ℝ × ℝ → ℝ) =ᵐ[cyl] dv (H.toSub u) (idxT k) :=
  coeFn_dvCLM (idxT k) u

lemma dsH_toH {φ : ℝ × ℝ → ℝ} (hφ : IsTest φ) :
    dsH k hδ (toH (k + 1) hδ hφ) = toH k hδ hφ.ds := by
  refine Subtype.ext (Lp.ext ?_)
  refine (coeFn_dsH _).trans ((dv_unique _ _ ?_ (hφ.ds.memLp 2)).trans
    (hφ.ds.memLp 2).coeFn_toLp.symm)
  exact (hφ.smPer.hasWeakDeriv 1 0).congr_ae (hφ.memLp 2).coeFn_toLp.symm (ae_eq_refl _)

lemma dtH_toH {φ : ℝ × ℝ → ℝ} (hφ : IsTest φ) :
    dtH k hδ (toH (k + 1) hδ hφ) = toH k hδ hφ.dt := by
  refine Subtype.ext (Lp.ext ?_)
  refine (coeFn_dtH _).trans ((dv_unique _ _ ?_ (hφ.dt.memLp 2)).trans
    (hφ.dt.memLp 2).coeFn_toLp.symm)
  exact (hφ.smPer.hasWeakDeriv 0 1).congr_ae (hφ.memLp 2).coeFn_toLp.symm (ae_eq_refl _)

end Deriv

/-! ## 2. `H³ ⊂ C¹` on the open strip -/

section C1

variable {δ : ℝ} {hδ : 0 ≤ δ}

lemma isOpen_openStrip : IsOpen openStrip := isOpen_univ.prod isOpen_Ioo

lemma val_toH {m : ℕ} {φ : ℝ × ℝ → ℝ} (hφ : IsTest φ) :
    (H.val (toH m hδ hφ) : ℝ × ℝ → ℝ) =ᵐ[cyl] φ := (hφ.memLp 2).coeFn_toLp

lemma inclH_toH {m m' : ℕ} (hm : m ≤ m') {φ : ℝ × ℝ → ℝ} (hφ : IsTest φ) :
    inclH hδ hδ hm le_rfl (toH m' hδ hφ) = toH m hδ hφ :=
  valCLM_injective (by rw [valCLM_inclH]; rfl)

/-- Test functions converging in `H²` converge uniformly on the open strip to the continuous
representative of the limit. -/
lemma tendstoUniformlyOn_of_tendsto_H2 {F : ℕ → ℝ × ℝ → ℝ} (hF : ∀ n, IsTest (F n))
    {u : H 2 hδ} (h : Tendsto (fun n => toH 2 hδ (hF n)) atTop (𝓝 u)) :
    ∃ g, Continuous g ∧ (H.val u : ℝ × ℝ → ℝ) =ᵐ[cyl] g ∧
      TendstoUniformlyOn F g atTop openStrip := by
  obtain ⟨g, hg, hug, -⟩ := exists_continuous_rep u
  refine ⟨g, hg, hug, ?_⟩
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 h (ε / 4) (by positivity)
  filter_upwards [eventually_ge_atTop N] with n hn x hx
  have hae : (H.val (toH 2 hδ (hF n) - u) : ℝ × ℝ → ℝ) =ᵐ[cyl] fun y => F n y - g y := by
    filter_upwards [val_sub_ae (toH 2 hδ (hF n)) u, val_toH (m := 2) (hδ := hδ) (hF n), hug]
      with y h1 h2 h3
    rw [h1, h2, h3]
  have hb := abs_le_of_ae_eq (toH 2 hδ (hF n) - u) isOpen_openStrip subset_rfl
    ((hF n).smooth.continuous.sub hg).continuousOn hae x hx
  have hd := hN n hn
  rw [dist_eq_norm] at hd
  change |F n x - g x| ≤ _ at hb
  rw [Real.dist_eq, abs_sub_comm]
  linarith

/-- **`H³ ⊂ C¹`**: every `w ∈ H^{3,δ}(ℝ × S¹)` has a continuous representative `g`, differentiable
on the open strip `ℝ × (0,1)`, whose partial derivatives `g_s, g_t` are continuous and represent
`∂_s w, ∂_t w`. -/
theorem exists_C1_rep (w : H 3 hδ) : ∃ g gs gt : ℝ × ℝ → ℝ, Continuous g ∧ Continuous gs ∧
    Continuous gt ∧ (H.val w : ℝ × ℝ → ℝ) =ᵐ[cyl] g ∧
    (H.val (dsH 2 hδ w) : ℝ × ℝ → ℝ) =ᵐ[cyl] gs ∧ (H.val (dtH 2 hδ w) : ℝ × ℝ → ℝ) =ᵐ[cyl] gt ∧
    ∀ x ∈ openStrip, HasFDerivAt g
      (gs x • ContinuousLinearMap.fst ℝ ℝ ℝ + gt x • ContinuousLinearMap.snd ℝ ℝ ℝ) x := by
  have hw : w ∈ closure {u : H 3 hδ | ∃ φ, ∃ hφ : IsTest φ, u = toH 3 hδ hφ} := by
    rw [(dense_test 3 hδ).closure_eq]; exact mem_univ w
  obtain ⟨x, hxS, hx⟩ := mem_closure_iff_seq_limit.1 hw
  choose φ hφ hxφ using hxS
  have h3 : Tendsto (fun n => toH 3 hδ (hφ n)) atTop (𝓝 w) := by
    simpa [← hxφ] using hx
  have h2 : Tendsto (fun n => toH 2 hδ (hφ n)) atTop
      (𝓝 (inclH hδ hδ (by norm_num : 2 ≤ 3) le_rfl w)) := by
    have := ((inclH hδ hδ (by norm_num : 2 ≤ 3) le_rfl).continuous.tendsto w).comp h3
    simpa [Function.comp_def, inclH_toH] using this
  have hs : Tendsto (fun n => toH 2 hδ (hφ n).ds) atTop (𝓝 (dsH 2 hδ w)) := by
    have := ((dsH 2 hδ).continuous.tendsto w).comp h3
    simpa [Function.comp_def, dsH_toH] using this
  have ht : Tendsto (fun n => toH 2 hδ (hφ n).dt) atTop (𝓝 (dtH 2 hδ w)) := by
    have := ((dtH 2 hδ).continuous.tendsto w).comp h3
    simpa [Function.comp_def, dtH_toH] using this
  obtain ⟨g, hg, hwg, hug⟩ := tendstoUniformlyOn_of_tendsto_H2 hφ h2
  obtain ⟨gs, hgs, hwgs, hugs⟩ := tendstoUniformlyOn_of_tendsto_H2 (fun n => (hφ n).ds) hs
  obtain ⟨gt, hgt, hwgt, hugt⟩ := tendstoUniformlyOn_of_tendsto_H2 (fun n => (hφ n).dt) ht
  refine ⟨g, gs, gt, hg, hgs, hgt, hwg, hwgs, hwgt, fun x₀ hx₀ => ?_⟩
  have hder : ∀ n y, HasFDerivAt (φ n) (Ds (φ n) y • ContinuousLinearMap.fst ℝ ℝ ℝ +
      Dt (φ n) y • ContinuousLinearMap.snd ℝ ℝ ℝ) y := by
    intro n y
    have hd := ((hφ n).smooth.differentiable (by simp) y).hasFDerivAt
    have e : Ds (φ n) y • ContinuousLinearMap.fst ℝ ℝ ℝ +
        Dt (φ n) y • ContinuousLinearMap.snd ℝ ℝ ℝ = fderiv ℝ (φ n) y :=
      ContinuousLinearMap.ext fun v => by
        rw [ChartChange.fderiv_apply_eq]; simp; ring
    rw [e]; exact hd
  refine hasFDerivAt_of_tendstoUniformlyOn (g' := fun y => gs y • ContinuousLinearMap.fst ℝ ℝ ℝ +
    gt y • ContinuousLinearMap.snd ℝ ℝ ℝ) isOpen_openStrip ?_ (fun n y _ => hder n y)
    (fun y hy => hug.tendsto_at hy) hx₀
  rw [Metric.tendstoUniformlyOn_iff] at hugs hugt ⊢
  intro ε hε
  filter_upwards [hugs (ε / 2) (by positivity), hugt (ε / 2) (by positivity)] with n h1 h2 y hy
  have e : (gs y • ContinuousLinearMap.fst ℝ ℝ ℝ + gt y • ContinuousLinearMap.snd ℝ ℝ ℝ) -
      (Ds (φ n) y • ContinuousLinearMap.fst ℝ ℝ ℝ + Dt (φ n) y • ContinuousLinearMap.snd ℝ ℝ ℝ) =
      (gs y - Ds (φ n) y) • ContinuousLinearMap.fst ℝ ℝ ℝ +
        (gt y - Dt (φ n) y) • ContinuousLinearMap.snd ℝ ℝ ℝ := by
    rw [sub_smul, sub_smul]; abel
  rw [dist_eq_norm, e]
  have h1' := h1 y hy
  have h2' := h2 y hy
  rw [Real.dist_eq] at h1' h2'
  calc ‖(gs y - Ds (φ n) y) • ContinuousLinearMap.fst ℝ ℝ ℝ +
        (gt y - Dt (φ n) y) • ContinuousLinearMap.snd ℝ ℝ ℝ‖
      ≤ ‖(gs y - Ds (φ n) y) • ContinuousLinearMap.fst ℝ ℝ ℝ‖ +
        ‖(gt y - Dt (φ n) y) • ContinuousLinearMap.snd ℝ ℝ ℝ‖ := norm_add_le _ _
    _ ≤ |gs y - Ds (φ n) y| * 1 + |gt y - Dt (φ n) y| * 1 := by
        rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
        gcongr
        · exact ContinuousLinearMap.norm_fst_le ℝ ℝ ℝ
        · exact ContinuousLinearMap.norm_snd_le ℝ ℝ ℝ
    _ < ε := by linarith

end C1

/-! ## 3. The derivative of the cut-off and the gluing data -/

section Glue

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {Q : Type} [TopologicalSpace Q] [ChartedSpace E Q] [IsManifold 𝓘(ℝ, E) ∞ Q]
variable {m : ℕ} {X : NodalSurface m} (hT : ChartsOnto X) {u : X.S → Q}

/-- The unit vector of direction `d` in strip coordinates. -/
def dir2 (d : Fin 2) : ℝ × ℝ := if d = 0 then (1, 0) else (0, 1)

/-- `∂_d β`, the derivative of the cut-off of the disc semi-norms. -/
def dCut (d : Fin 2) (p : ℝ × ℝ) : ℝ := fderiv ℝ discCut p (dir2 d)

lemma contDiff_dCut (d : Fin 2) : ContDiff ℝ ∞ (dCut d) :=
  ChartChange.contDiff_dir contDiff_discCut _

lemma tsupport_discCut : tsupport discCut ⊆ closedDisc :=
  closure_minimal (fun _ hp => by_contra fun h => hp (discCut_eq_zero h))
    isCompact_closedDisc.isClosed

lemma dCut_eq_zero (d : Fin 2) {p : ℝ × ℝ} (hp : p ∉ closedDisc) : dCut d p = 0 :=
  image_eq_zero_of_notMem_tsupport fun h =>
    hp (tsupport_discCut (ChartChange.tsupport_dir_subset _ _ h))

/-- The coefficient of the zeroth-order term: `∂_d β · (ρ ∘ discPt) / (β ∘ dtrans)`. -/
def coefZ (d : Fin 2) (ρ : X.S → ℝ) (z : X.S) (ε : ℝ) (z' : X.S) (ε' : ℝ) (p : ℝ × ℝ) : ℝ :=
  dCut d p * ρ (X.discPt z ε p) / discCut (dtrans z ε z' ε' p)

lemma pieceZ_zero (d : Fin 2) {ρ : X.S → ℝ} {z : X.S} {ε : ℝ} {p : ℝ × ℝ}
    (hp : p ∉ pieceK ρ z ε) : dCut d p * ρ (X.discPt z ε p) = 0 := by
  by_cases hc : p ∈ closedDisc
  · rw [image_eq_zero_of_notMem_tsupport fun h => hp ⟨hc, h⟩, mul_zero]
  · rw [dCut_eq_zero d hc, zero_mul]

include hT in
lemma tsupport_coefZ_sub (d : Fin 2) (ρ : X.S → ℝ) (z : X.S) (ε : ℝ) (z' : X.S) (ε' : ℝ) :
    tsupport (coefZ d ρ z ε z' ε') ⊆ pieceK ρ z ε :=
  closure_minimal (fun p hp => by_contra fun h => hp (by rw [coefZ, pieceZ_zero d h, zero_div]))
    (isCompact_pieceK hT ρ z ε).isClosed

include hT in
lemma contDiff_coefZ (d : Fin 2) (ρ : C^∞⟮𝓘(ℝ, E2), X.S; 𝓘(ℝ), ℝ⟯) (z : X.S) (ε : ℝ)
    (z' : X.S) (ε' : ℝ) (hρ : tsupport ρ ⊆ discSet z' ε') :
    ContDiff ℝ ∞ (coefZ d ρ z ε z' ε') := by
  set V := pieceDom z ε z' ε'
  have hVo : IsOpen V := isOpen_pieceDom hT z ε z' ε'
  have hW : IsOpen (X.discPt z ε ⁻¹' tsupport ρ)ᶜ :=
    ((isClosed_tsupport ρ).preimage (continuous_discPt hT z ε)).isOpen_compl
  refine contDiff_of_open_cover hVo hW (fun p => ?_) ?_ ?_
  · by_cases h : X.discPt z ε p ∈ tsupport ρ
    · exact Or.inl (hρ h)
    · exact Or.inr h
  · have hdt : ContDiffOn ℝ ∞ (dtrans z ε z' ε') V :=
      (contDiffOn_trans hT z ε z' ε').mono fun p hp => (pieceDom_sub hp).1
    have hcut : ContDiffOn ℝ ∞ (fun p => discCut (dtrans z ε z' ε' p)) V :=
      contDiff_discCut.comp_contDiffOn hdt
    have hne : ∀ p ∈ V, discCut (dtrans z ε z' ε' p) ≠ 0 := fun p hp =>
      (discCut_pos (pieceDom_sub hp).2).ne'
    exact ((contDiff_dCut d).contDiffOn.mul (contDiff_comp_discPt hT ρ z ε).contDiffOn).div
      hcut hne
  · intro p hp
    simp [coefZ, image_eq_zero_of_notMem_tsupport hp]

variable (A : SectionAtlas (E := E) X u)

/-- **Gluing data** for an atlas: a smooth partition of unity subordinate to the discs, and
changes of disc charts on its pieces (as in `GWMemoir.ChartChangeDensity`). -/
structure GlueData where
  ρ : SmoothPartitionOfUnity (Fin A.nd) 𝓘(ℝ, E2) X.S univ
  hρ : ∀ j, tsupport (ρ j) ⊆ discSet (A.center j) (A.ε j)
  D : Fin A.nd → Fin A.nd → ChartChange
  hDK : ∀ i j, (D i j).K = pieceK (ρ j) (A.center i) (A.ε i)
  hDψ : ∀ i j, ∀ p ∈ (D i j).K,
    (D i j).ψ p = dtrans (A.center i) (A.ε i) (A.center j) (A.ε j) p

include hT in
/-- **Witness**: gluing data exist on a surface without nodes whose charts are onto `ℝ²`. -/
theorem exists_glueData (hX : X.nodes = ∅) : Nonempty (GlueData A) := by
  obtain ⟨ρ, hρ⟩ := exists_partition hX hT A
  have hρ' : ∀ j, tsupport (ρ j) ⊆ discSet (A.center j) (A.ε j) := hρ
  choose D hDK hDψ using fun i j : Fin A.nd =>
    exists_chartChange hT (ρ := ρ j) (A.ε_pos i).ne' (A.ε_pos j).ne' (hρ' j)
  exact ⟨⟨ρ, hρ', D, hDK, hDψ⟩⟩

variable {A} (G : GlueData A)

include hT in
lemma GlueData.hcZ (d : Fin 2) (i j : Fin A.nd) :
    ContDiff ℝ ∞ (coefZ d (G.ρ j) (A.center i) (A.ε i) (A.center j) (A.ε j)) :=
  contDiff_coefZ hT d (G.ρ j) _ _ _ _ (G.hρ j)

include hT in
lemma GlueData.hsZ (d : Fin 2) (i j : Fin A.nd) :
    tsupport (coefZ d (G.ρ j) (A.center i) (A.ε i) (A.center j) (A.ε j)) ⊆ (G.D i j).K :=
  (G.hDK i j).symm ▸ tsupport_coefZ_sub hT d _ _ _ _ _

variable {q : Q} (hu : ∀ x, u x = q)

include hT hu in
/-- One piece of the zeroth-order term, on the representative of a section. -/
lemma termZ_rep_eq (d : Fin 2) {i j : Fin A.nd} (kk : Fin (Module.finrank ℝ E))
    (η : Section E X) (p : ℝ × ℝ) :
    coefZ d (G.ρ j) (A.center i) (A.ε i) (A.center j) (A.ε j) p *
        discRep A j kk η ((G.D i j).ψ p) =
      dCut d p * G.ρ j (X.discPt (A.center i) (A.ε i) p) *
        crd kk (η (X.discPt (A.center i) (A.ε i) p)) := by
  by_cases hp : p ∈ pieceK (G.ρ j) (A.center i) (A.ε i)
  · have hpD := pieceK_sub (G.hρ j) hp
    rw [G.hDψ i j p (G.hDK i j ▸ hp), discRep_const hu,
      discPt_trans (A.ε_pos j).ne' (pieceDom_sub hpD).1]
    have hne := (discCut_pos (pieceDom_sub hpD).2).ne'
    rw [coefZ]
    field_simp
  · have h0 : coefZ d (G.ρ j) (A.center i) (A.ε i) (A.center j) (A.ε j) p = 0 :=
      image_eq_zero_of_notMem_tsupport fun h => hp (tsupport_coefZ_sub hT d _ _ _ _ _ h)
    rw [h0, zero_mul, pieceZ_zero d hp, zero_mul]

include hT hu in
/-- The pieces summed: `∑_j coefZ_{ij} · (rep_j ∘ trans_{ij}) = ∂_d β · η_k` in the disc `i`. -/
lemma sumZ_rep_eq (d : Fin 2) (i : Fin A.nd) (kk : Fin (Module.finrank ℝ E))
    (η : Section E X) (p : ℝ × ℝ) :
    ∑ j, coefZ d (G.ρ j) (A.center i) (A.ε i) (A.center j) (A.ε j) p *
        discRep A j kk η ((G.D i j).ψ p) =
      dCut d p * crd kk (η (X.discPt (A.center i) (A.ε i) p)) := by
  rw [Finset.sum_congr rfl fun j _ => termZ_rep_eq hT G hu d kk η p, ← Finset.sum_mul,
    ← Finset.mul_sum]
  have h := G.ρ.sum_eq_one (x := X.discPt (A.center i) (A.ε i) p) (mem_univ _)
  rw [finsum_eq_sum_of_fintype] at h
  rw [h, mul_one]

end Glue

/-! ## 4. The operators `Z`, `R` and `D` -/

section Operators

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {Q : Type} [TopologicalSpace Q] [ChartedSpace E Q] [IsManifold 𝓘(ℝ, E) ∞ Q]
variable {m : ℕ} {X : NodalSurface m} (hT : ChartsOnto X) {u : X.S → Q}
  {A : SectionAtlas (E := E) X u} (G : GlueData A)
  (δ : ℕ → ℝ) (h0 : 0 ≤ δ 0) (hmono : StrictMono δ)

/-- The block `(j, k)` of a level-`0` section tuple, as an element of `H³`. -/
def secProj (jk : Fin A.nd × Fin (Module.finrank ℝ E)) :
    (blocks A δ h0 hmono) 0 →L[ℝ] H 3 (Neck.δ_nonneg δ h0 hmono 0) :=
  (ContinuousLinearMap.proj jk).comp (ContinuousLinearMap.fst ℝ _ _)

/-- The inclusion `H³ → H²` at the weight `δ₀`. -/
abbrev incl32 : H 3 (Neck.δ_nonneg δ h0 hmono 0) →L[ℝ] H 2 (Neck.δ_nonneg δ h0 hmono 0) :=
  inclH _ _ (by norm_num : 2 ≤ 3) le_rfl

/-- The derivative `∂_d : H³ → H²`. -/
def dH (d : Fin 2) : H 3 (Neck.δ_nonneg δ h0 hmono 0) →L[ℝ] H 2 (Neck.δ_nonneg δ h0 hmono 0) :=
  ![dsH 2 (Neck.δ_nonneg δ h0 hmono 0), dtH 2 (Neck.δ_nonneg δ h0 hmono 0)] d

include hT in
/-- The disc block `(i, d, k)` of the zeroth-order term `Z`. -/
def zBlock (o : Ix A) : (blocks A δ h0 hmono) 0 →L[ℝ] H 2 (Neck.δ_nonneg δ h0 hmono 0) :=
  ∑ j, ((G.D o.1 j).op 2 (Neck.δ_nonneg δ h0 hmono 0) (G.hcZ hT o.2.1 o.1 j) (G.hsZ hT o.2.1 o.1 j)
      (Neck.δ_nonneg δ h0 hmono 0)).comp
        ((incl32 δ h0 hmono).comp (secProj δ h0 hmono (j, o.2.2)))

include hT in
/-- The disc block `(i, d, k)` of `R`: `ε_i⁻¹ (∂_d v_{i,k} - (Zv)_{i,d,k})`. -/
def rBlock (o : Ix A) : (blocks A δ h0 hmono) 0 →L[ℝ] H 2 (Neck.δ_nonneg δ h0 hmono 0) :=
  (A.ε o.1)⁻¹ • ((dH δ h0 hmono o.2.1).comp (secProj δ h0 hmono (o.1, o.2.2)) -
    zBlock hT G δ h0 hmono o)

include hT in
/-- **The derivative read in the disc charts**, `R`, from the section blocks to the fibre blocks
(`0` on the neck blocks). -/
def rOp : (blocks A δ h0 hmono) 0 →L[ℝ] (fibreBlocks A δ h0 hmono) 0 :=
  (ContinuousLinearMap.pi fun o => rBlock hT G δ h0 hmono o).prod 0

include hT in
/-- **The linearization `D = ½ (R + P R)`** at a constant map, `J₀ = J(q)`: a bounded operator
from the level-`0` section blocks to the level-`0` fibre blocks. -/
def linOp (J₀ : E →L[ℝ] E) : (blocks A δ h0 hmono) 0 →L[ℝ] (fibreBlocks A δ h0 hmono) 0 :=
  (1 / 2 : ℝ) • (rOp hT G δ h0 hmono + (fOp δ h0 hmono (fun _ _ => idCC) (aPI A J₀)
    (fun _ _ => contDiff_aP hT J₀ _ _ _ _ _ _) (fun _ _ => tsupport_aP J₀ _ _ _ _ _ _) (srcP A)
      0).comp (rOp hT G δ h0 hmono))

lemma val_secProj (v : (blocks A δ h0 hmono) 0) (jk : Fin A.nd × Fin (Module.finrank ℝ E)) :
    secProj δ h0 hmono jk v = v.1 jk := rfl

lemma coeFn_zBlock (v : (blocks A δ h0 hmono) 0) (o : Ix A) :
    (H.val (zBlock hT G δ h0 hmono o v) : ℝ × ℝ → ℝ) =ᵐ[cyl] fun x =>
      ∑ j, coefZ o.2.1 (G.ρ j) (A.center o.1) (A.ε o.1) (A.center j) (A.ε j) x *
        H.val (v.1 (j, o.2.2)) ((G.D o.1 j).ψ x) := by
  have e1 : H.val (zBlock hT G δ h0 hmono o v) = ∑ j, (G.D o.1 j).compMul
      (coefZ o.2.1 (G.ρ j) (A.center o.1) (A.ε o.1) (A.center j) (A.ε j))
        (H.val (v.1 (j, o.2.2))) := by
    rw [zBlock, _root_.sum_apply]
    refine (map_sum (valCLM 2 (Neck.δ_nonneg δ h0 hmono 0)) _ _).trans
      (Finset.sum_congr rfl fun j _ => ?_)
    exact ChartChange.val_op (G.hcZ hT o.2.1 o.1 j) (G.hsZ hT o.2.1 o.1 j)
      (Neck.δ_nonneg δ h0 hmono 0) _
  rw [e1]
  filter_upwards [Lp.coeFn_fun_finsetSum Finset.univ fun j => (G.D o.1 j).compMul
      (coefZ o.2.1 (G.ρ j) (A.center o.1) (A.ε o.1) (A.center j) (A.ε j))
        (H.val (v.1 (j, o.2.2))),
    ae_all_iff.2 fun j => (G.D o.1 j).coeFn_compMul (G.hcZ hT o.2.1 o.1 j).continuous
      (G.hsZ hT o.2.1 o.1 j) (H.val (v.1 (j, o.2.2)))] with x h1 h2
  rw [h1]
  exact Finset.sum_congr rfl fun j _ => h2 j

lemma coeFn_rBlock (v : (blocks A δ h0 hmono) 0) (o : Ix A) :
    (H.val (rBlock hT G δ h0 hmono o v) : ℝ × ℝ → ℝ) =ᵐ[cyl] fun x =>
      (A.ε o.1)⁻¹ * (H.val (dH δ h0 hmono o.2.1 (v.1 (o.1, o.2.2))) x -
        ∑ j, coefZ o.2.1 (G.ρ j) (A.center o.1) (A.ε o.1) (A.center j) (A.ε j) x *
          H.val (v.1 (j, o.2.2)) ((G.D o.1 j).ψ x)) := by
  have e : rBlock hT G δ h0 hmono o v = (A.ε o.1)⁻¹ • (dH δ h0 hmono o.2.1 (v.1 (o.1, o.2.2)) -
      zBlock hT G δ h0 hmono o v) := rfl
  rw [e]
  filter_upwards [val_smul_ae (A.ε o.1)⁻¹ (dH δ h0 hmono o.2.1 (v.1 (o.1, o.2.2)) -
      zBlock hT G δ h0 hmono o v), val_sub_ae (dH δ h0 hmono o.2.1 (v.1 (o.1, o.2.2)))
      (zBlock hT G δ h0 hmono o v), coeFn_zBlock hT G δ h0 hmono v o] with x h1 h2 h3
  rw [h1, smul_eq_mul, h2, h3]

end Operators

end GWMemoir
