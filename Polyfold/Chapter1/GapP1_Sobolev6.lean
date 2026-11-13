import Polyfold.Chapter1.GapP1_Sobolev5

/-!
# Example 1.1.3 (2021, p. 6; preprint Example 1.2), part 6: the inclusions are compact

`isCompactOperator_inclH`: for `0 ≤ δ < δ'`, the inclusion `H^{m+1,δ'}(ℝ × S¹) → H^{m,δ}(ℝ × S¹)`
is a compact operator. This is where "Sobolev's compact embedding theorem for bounded domains and
the assumption that the sequence `(δ_m)` is strictly increasing" enter:

* on `[-R, R] × S¹`, each `∂^p u` (`|p| ≤ m`) lies in a bounded set of `H¹`, so the restrictions
  form a totally bounded set (`rellich`);
* outside, `e^{δ|s|} |∂^p u| ≤ e^{-(δ'-δ) R} e^{δ'|s|} |∂^p u|` (the tail estimate).
-/

open MeasureTheory Set Filter Topology
open scoped ContDiff ENNReal

noncomputable section

namespace Polyfold.GapP1Sobolev

/-- An isometry reflects total boundedness. -/
lemma totallyBounded_of_isometry {X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y]
    {f : X → Y} (hf : Isometry f) {S : Set X} (h : TotallyBounded (f '' S)) : TotallyBounded S := by
  refine Metric.totallyBounded_iff.2 fun ε hε => ?_
  obtain ⟨t, htS, ht, hcov⟩ := Metric.finite_approx_of_totallyBounded h ε hε
  have hchoose : ∀ y : t, ∃ x ∈ S, f x = y := fun y => htS y.2
  choose g hgS hgf using hchoose
  have : Finite t := ht.to_subtype
  refine ⟨Set.range g, Set.finite_range _, fun x hx => ?_⟩
  have := hcov ⟨x, hx, rfl⟩
  rw [Set.mem_iUnion₂] at this
  obtain ⟨y, hy, hxy⟩ := this
  rw [Set.mem_iUnion₂]
  refine ⟨g ⟨y, hy⟩, ⟨⟨y, hy⟩, rfl⟩, ?_⟩
  rw [Metric.mem_ball] at hxy ⊢
  rwa [← hf.dist_eq, hgf]

variable {m : ℕ} {δ δ' : ℝ}

/-- `p ∈ idx m` as an index of `idx (m+1)`. -/
def liftIdx (p : idx m) : idx (m + 1) := ⟨p.1, mem_idx.2 ((mem_idx.1 p.2).trans (Nat.le_succ m))⟩

/-- `p + (1,0)`. -/
def sIdx (p : idx m) : idx (m + 1) :=
  ⟨(p.1.1 + 1, p.1.2), mem_idx.2 (by have := mem_idx.1 p.2; simp only; omega)⟩

/-- `p + (0,1)`. -/
def tIdx (p : idx m) : idx (m + 1) :=
  ⟨(p.1.1, p.1.2 + 1), mem_idx.2 (by have := mem_idx.1 p.2; simp only; omega)⟩

lemma norm_dvCLM_le {k : ℕ} {δ : ℝ} {hδ : 0 ≤ δ} (p : idx k) (u : H k hδ) :
    ‖dvCLM k hδ p u‖ ≤ ‖u‖ := by
  calc ‖dvCLM k hδ p u‖
      ≤ ‖mulOp (wt (-δ)) (continuous_wt _).aestronglyMeasurable 1 (abs_wt_neg_le hδ)‖ *
          ‖wdvCLM k hδ p u‖ :=
        ContinuousLinearMap.le_opNorm
          (mulOp (wt (-δ)) (continuous_wt _).aestronglyMeasurable 1 (abs_wt_neg_le hδ)) _
    _ ≤ 1 * ‖u‖ := mul_le_mul (norm_mulOp_le zero_le_one) (norm_wdv_le u p) (norm_nonneg _)
          zero_le_one
    _ = ‖u‖ := one_mul _

/-- The derivatives `∂^p u`, `|p| ≤ m`, of `u ∈ H^{m+1,δ'}` lie in the `H¹`-ball of radius `‖u‖`. -/
lemma dvCLM_mem_H1ball {hδ' : 0 ≤ δ'} (u : H (m + 1) hδ') (p : idx m) :
    dvCLM (m + 1) hδ' (liftIdx p) u ∈ H1ball ‖u‖ := by
  have hg := (dv_spec (H.toSub u) (liftIdx p)).1
  have hs := (dv_spec (H.toSub u) (sIdx p)).1
  have ht := (dv_spec (H.toSub u) (tIdx p)).1
  refine ⟨dvCLM (m + 1) hδ' (sIdx p) u, dvCLM (m + 1) hδ' (tIdx p) u, ?_, ?_,
    norm_dvCLM_le _ u, norm_dvCLM_le _ u, norm_dvCLM_le _ u⟩
  · exact (hg.of_succ_s hs).congr_ae (coeFn_dvCLM (liftIdx p) u).symm
      (coeFn_dvCLM (sIdx p) u).symm
  · exact (hg.of_succ_t ht).congr_ae (coeFn_dvCLM (liftIdx p) u).symm
      (coeFn_dvCLM (tIdx p) u).symm

lemma dv_inclH {hδ : 0 ≤ δ} {hδ' : 0 ≤ δ'} (hle : δ ≤ δ') (u : H (m + 1) hδ') (p : idx m) :
    dv (H.toSub (inclH hδ hδ' (Nat.le_succ m) hle u)) p =ᵐ[cyl] dv (H.toSub u) (liftIdx p) :=
  dv_unique _ p (dv_spec (H.toSub u) (liftIdx p)).1 (dv_memLp _ _)

/-- The multiplier `1_{|s| ≤ R} e^{δ|s|}`. -/
def cutWt (R δ : ℝ) (x : ℝ × ℝ) : ℝ := indR R x * wt δ x

lemma abs_cutWt_le {R δ : ℝ} (hδ : 0 ≤ δ) (x : ℝ × ℝ) : |cutWt R δ x| ≤ Real.exp (δ * R) := by
  unfold cutWt indR
  by_cases hx : x ∈ {y : ℝ × ℝ | |y.1| ≤ R}
  · rw [indicator_of_mem hx, one_mul, abs_of_pos (wt_pos _ _), wt]
    exact Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left hx hδ)
  · rw [indicator_of_notMem hx, zero_mul, abs_zero]; exact (Real.exp_pos _).le

lemma aesm_cutWt (R δ : ℝ) : AEStronglyMeasurable (cutWt R δ) cyl :=
  (aesm_indR R).mul (continuous_wt δ).aestronglyMeasurable

/-- The tail multiplier `1_{|s| > R} e^{δ|s|} e^{-δ'|s|}` is at most `e^{-(δ'-δ)R}`. -/
lemma tail_le {R δ δ' : ℝ} (hlt : δ ≤ δ') (x : ℝ × ℝ) :
    |(1 - indR R x) * wt δ x * wt (-δ') x| ≤ Real.exp (-(δ' - δ) * R) := by
  unfold indR
  by_cases hx : x ∈ {y : ℝ × ℝ | |y.1| ≤ R}
  · rw [indicator_of_mem hx]; simp only [sub_self, zero_mul, abs_zero]; exact (Real.exp_pos _).le
  · rw [indicator_of_notMem hx, sub_zero, one_mul, wt, wt, ← Real.exp_add,
      abs_of_pos (Real.exp_pos _)]
    simp only [mem_ofPred_eq, not_le] at hx
    apply Real.exp_le_exp.2
    nlinarith

/-- **The inclusion `H^{m+1,δ'} → H^{m,δ}` is compact** for `0 ≤ δ < δ'`. -/
theorem isCompactOperator_inclH (hδ : 0 ≤ δ) (hδ' : 0 ≤ δ') (hlt : δ < δ') :
    IsCompactOperator (inclH hδ hδ' (Nat.le_succ m) hlt.le) := by
  set Tm := inclH (m := m) hδ hδ' (Nat.le_succ m) hlt.le
  set B : Set (H (m + 1) hδ') := Metric.ball 0 1
  -- the component sets
  set Cp : idx m → Set (Lp ℝ 2 cyl) := fun p => (fun u => wdv (H.toSub (Tm u)) p) '' B
  have hCp : ∀ p, TotallyBounded (Cp p) := by
    intro p
    refine totallyBounded_of_approx fun ε hε => ?_
    -- choose `R`
    have hγ : 0 < δ' - δ := sub_pos.2 hlt
    have hlim : Tendsto (fun R : ℝ => Real.exp (-(δ' - δ) * R)) atTop (𝓝 0) := by
      have := Real.tendsto_exp_neg_atTop_nhds_zero.comp (tendsto_id.const_mul_atTop hγ)
      refine this.congr fun R => ?_
      simp only [Function.comp_apply, id]; ring_nf
    obtain ⟨R, hRε, hR⟩ := ((hlim.eventually (gt_mem_nhds hε)).and (eventually_gt_atTop 0)).exists
    set Mw := mulOp (cutWt R δ) (aesm_cutWt R δ) (Real.exp (δ * R)) (abs_cutWt_le hδ)
    refine ⟨Mw '' (cutR R '' H1ball 1), (rellich hR 1).image Mw.uniformContinuous, ?_⟩
    rintro _ ⟨u, hu, rfl⟩
    have hu1 : ‖u‖ < 1 := by simpa [B] using hu
    set v := dvCLM (m + 1) hδ' (liftIdx p) u
    have hv : v ∈ H1ball 1 := by
      obtain ⟨gs, gt, h1, h2, n0, n1, n2⟩ := dvCLM_mem_H1ball u p
      exact ⟨gs, gt, h1, h2, n0.trans hu1.le, n1.trans hu1.le, n2.trans hu1.le⟩
    refine ⟨Mw (cutR R v), ⟨cutR R v, ⟨v, hv, rfl⟩, rfl⟩, ?_⟩
    rw [dist_eq_norm]
    -- the difference is the tail
    have hle : ‖wdv (H.toSub (Tm u)) p - Mw (cutR R v)‖ ≤
        Real.exp (-(δ' - δ) * R) * ‖wdv (H.toSub u) (liftIdx p)‖ := by
      apply Lp.norm_le_mul_norm_of_ae_le_mul
      filter_upwards [Lp.coeFn_sub (wdv (H.toSub (Tm u)) p) (Mw (cutR R v)),
        coeFn_wdv (H.toSub (Tm u)) p, dv_inclH hlt.le u p,
        coeFn_mulOp (cutWt R δ) (aesm_cutWt R δ) _ (abs_cutWt_le hδ) (cutR R v),
        coeFn_mulOp (indR R) (aesm_indR R) 1 (abs_indR_le R) v,
        coeFn_dvCLM (liftIdx p) u, coeFn_wdv (H.toSub u) (liftIdx p)]
        with x e1 e2 e3 e4 e5 e6 e7
      rw [e1, Pi.sub_apply, e2, e3, e4]
      change ‖wt δ x * dv (H.toSub u) (liftIdx p) x - cutWt R δ x * (cutR R v) x‖ ≤ _
      rw [cutR, e5, e6, e7]
      have hid : indR R x * indR R x = indR R x := by
        unfold indR; by_cases h : x ∈ {y : ℝ × ℝ | |y.1| ≤ R} <;> simp [h]
      have key : wt δ x * dv (H.toSub u) (liftIdx p) x -
          cutWt R δ x * (indR R x * dv (H.toSub u) (liftIdx p) x) =
          ((1 - indR R x) * wt δ x * wt (-δ') x) *
            (wt δ' x * dv (H.toSub u) (liftIdx p) x) := by
        have h1 := wt_neg_mul δ' x
        unfold cutWt
        calc _ = (1 - indR R x * indR R x) * wt δ x * dv (H.toSub u) (liftIdx p) x := by ring
          _ = (1 - indR R x) * wt δ x * (wt (-δ') x * wt δ' x) *
                dv (H.toSub u) (liftIdx p) x := by rw [hid, h1, mul_one]
          _ = _ := by ring
      rw [key, norm_mul, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_right (tail_le hlt.le x) (norm_nonneg _)
    calc _ ≤ Real.exp (-(δ' - δ) * R) * ‖wdv (H.toSub u) (liftIdx p)‖ := hle
      _ ≤ Real.exp (-(δ' - δ) * R) * 1 := by
          gcongr; exact (norm_wdv_le u _).trans hu1.le
      _ < ε := by rw [mul_one]; exact hRε
  -- the product set is compact
  set K' : Set (PiLp 2 (fun _ : idx m => Lp ℝ 2 cyl)) :=
    (PiLp.homeomorph 2 (fun _ : idx m => Lp ℝ 2 cyl)) ⁻¹' Set.pi univ (fun p => closure (Cp p))
  have hK' : IsCompact K' := by
    refine (PiLp.homeomorph 2 (fun _ : idx m => Lp ℝ 2 cyl)).isCompact_preimage.2
      (isCompact_univ_pi fun p => ?_)
    exact isCompact_iff_totallyBounded_isComplete.2 ⟨(hCp p).closure, isClosed_closure.isComplete⟩
  have htb : TotallyBounded (Tm '' B) := by
    refine totallyBounded_of_isometry isometry_ΦH ?_
    refine hK'.totallyBounded.subset ?_
    rintro _ ⟨_, ⟨u, hu, rfl⟩, rfl⟩
    intro p _
    exact subset_closure ⟨u, hu, rfl⟩
  refine (isCompactOperator_iff_image_ball_subset_compact (Tm : H (m + 1) hδ' →ₗ[ℝ] H m hδ)
    one_pos).2 ⟨closure (Tm '' B), ?_, subset_closure⟩
  exact isCompact_iff_totallyBounded_isComplete.2 ⟨htb.closure, isClosed_closure.isComplete⟩

end Polyfold.GapP1Sobolev
