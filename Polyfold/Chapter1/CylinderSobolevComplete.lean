import Polyfold.Chapter1.CylinderSobolevSpaces

/-!
# Example 1.1.3 (2021, p. 6; preprint Example 1.2), part 4: completeness and inclusions

* `completeSpace_H`: `H^{m,δ}(ℝ × S¹)` is a Banach space. The image of the isometric embedding
  `Φ` is closed: if `e^{δ|s|} ∂^p u_n → G_p` in `L²`, then `u = e^{-δ|s|} G_{(0,0)}` has the weak
  derivatives `e^{-δ|s|} G_p` (pass to the limit in the defining identities).
* `inclH`: for `m ≤ m'` and `δ ≤ δ'`, `H^{m',δ'} ⊂ H^{m,δ}` with `‖u‖_{m,δ} ≤ ‖u‖_{m',δ'}`;
  the inclusion is injective and commutes with the inclusions into `L²`.
-/

open MeasureTheory Set Filter Topology
open scoped ContDiff ENNReal

noncomputable section

namespace Polyfold.GapP1Sobolev

variable {m : ℕ} {δ : ℝ} {hδ : 0 ≤ δ}

/-- An element of `Hsub` as an element of `H`. -/
def Hsub.toH (u : Hsub m hδ) : H m hδ := u

/-- `e^{-δ|s|}·` on `L²`. -/
abbrev Minv (hδ : 0 ≤ δ) : Lp ℝ 2 cyl →L[ℝ] Lp ℝ 2 cyl :=
  mulOp (wt (-δ)) (continuous_wt _).aestronglyMeasurable 1 (abs_wt_neg_le hδ)

lemma val_eq_Minv (u : H m hδ) :
    (H.toSub u : Lp ℝ 2 cyl) = Minv hδ (wdv (H.toSub u) (idx0 m)) :=
  val_eq_dvCLM u

lemma pairing_dv (u : H m hδ) (p : idx m) {φ : ℝ × ℝ → ℝ} (hφ : MemLp φ 2 cyl) :
    pairing φ hφ (Minv hδ (wdv (H.toSub u) p)) = ∫ x, dv (H.toSub u) p x * φ x ∂cyl := by
  rw [pairing_apply]
  refine integral_congr_ae ?_
  filter_upwards [coeFn_dvCLM p u] with x hx
  change (dvCLM m hδ p u) x * φ x = _
  rw [hx]

/-- The image of `Φ` is closed. -/
theorem isClosed_range_ΦH : IsClosed (Set.range (ΦH m hδ)) := by
  refine isClosed_of_closure_subset fun G hG => ?_
  obtain ⟨x, hx, hlim⟩ := mem_closure_iff_seq_limit.1 hG
  choose u hu using hx
  have hcomp : ∀ p, Tendsto (fun n => wdv (H.toSub (u n)) p) atTop (𝓝 (G p)) := by
    intro p
    have := ((PiLp.proj (𝕜 := ℝ) 2 (fun _ : idx m => Lp ℝ 2 cyl) p).continuous.tendsto G).comp hlim
    refine this.congr fun n => ?_
    simp only [Function.comp_apply, PiLp.proj_apply, ← hu n]
    rfl
  set v : Lp ℝ 2 cyl := Minv hδ (G (idx0 m)) with hvdef
  have hw : ∀ p, (fun x => wt δ x * Minv hδ (G p) x) =ᵐ[cyl] G p := by
    intro p
    filter_upwards [coeFn_mulOp (wt (-δ)) (continuous_wt _).aestronglyMeasurable 1
      (abs_wt_neg_le hδ) (G p)] with x hx
    rw [hx, ← mul_assoc, mul_comm (wt δ x), wt_neg_mul, one_mul]
  have hder : ∀ p : idx m, HasWeakDeriv p.1.1 p.1.2 v (Minv hδ (G p)) := by
    intro p φ hφ
    have hφ1 := (hφ.pD p.1.1 p.1.2).memLp 2
    have hφ2 := hφ.memLp 2
    have h1 : Tendsto (fun n => ∫ x, (H.toSub (u n) : Lp ℝ 2 cyl) x * pD p.1.1 p.1.2 φ x ∂cyl)
        atTop (𝓝 (∫ x, v x * pD p.1.1 p.1.2 φ x ∂cyl)) := by
      have := ((pairing _ hφ1).continuous.tendsto _).comp
        (((Minv hδ).continuous.tendsto _).comp (hcomp (idx0 m)))
      rw [← pairing_apply _ hφ1]
      refine this.congr fun n => ?_
      simp only [Function.comp_apply]
      rw [pairing_apply, val_eq_Minv]
    have h2 : Tendsto (fun n => ∫ x, dv (H.toSub (u n)) p x * φ x ∂cyl)
        atTop (𝓝 (∫ x, Minv hδ (G p) x * φ x ∂cyl)) := by
      have := ((pairing _ hφ2).continuous.tendsto _).comp
        (((Minv hδ).continuous.tendsto _).comp (hcomp p))
      rw [← pairing_apply _ hφ2]
      refine this.congr fun n => ?_
      simp only [Function.comp_apply]
      rw [pairing_dv]
    have h3 : ∀ n, ∫ x, (H.toSub (u n) : Lp ℝ 2 cyl) x * pD p.1.1 p.1.2 φ x ∂cyl =
        (-1) ^ (p.1.1 + p.1.2) * ∫ x, dv (H.toSub (u n)) p x * φ x ∂cyl :=
      fun n => (dv_spec (H.toSub (u n)) p).1 φ hφ
    exact tendsto_nhds_unique h1 ((h2.const_mul _).congr fun n => (h3 n).symm)
  have hv : v ∈ Hsub m hδ := by
    intro a b hab
    set p : idx m := ⟨(a, b), mem_idx.2 hab⟩
    exact ⟨Minv hδ (G p), hder p, (Lp.memLp (G p)).ae_eq (hw p).symm⟩
  refine ⟨Hsub.toH ⟨v, hv⟩, ?_⟩
  refine (WithLp.ext_iff 2).2 (funext fun p => ?_)
  change wdv (⟨v, hv⟩ : Hsub m hδ) p = G p
  refine Lp.ext ?_
  have hd := dv_unique (⟨v, hv⟩ : Hsub m hδ) p (hder p) (Lp.memLp _)
  filter_upwards [coeFn_wdv (⟨v, hv⟩ : Hsub m hδ) p, hd, hw p] with x h1 h2 h3
  rw [h1, h2, h3]

/-- **`H^{m,δ}(ℝ × S¹)` is a Banach space.** -/
instance completeSpace_H : CompleteSpace (H m hδ) := by
  rw [completeSpace_iff_isComplete_range isometry_ΦH.isUniformInducing]
  exact isClosed_range_ΦH.isComplete

/-! ### Inclusions -/

lemma Hsub_mono {m m' : ℕ} {δ δ' : ℝ} (hδ : 0 ≤ δ) (hδ' : 0 ≤ δ') (hm : m ≤ m')
    (hδδ : δ ≤ δ') : Hsub m' hδ' ≤ Hsub m hδ := by
  intro u hu a b hab
  obtain ⟨g, hg, hgw⟩ := hu a b (hab.trans hm)
  refine ⟨g, hg, ?_⟩
  have hm' : AEStronglyMeasurable (fun x => wt δ x * g x) cyl :=
    (continuous_wt δ).aestronglyMeasurable.mul (memLp_of_weighted hδ' hgw).1
  refine hgw.of_le hm' (ae_of_all _ fun x => ?_)
  simp only [Real.norm_eq_abs, abs_mul, abs_of_pos (wt_pos _ x)]
  exact mul_le_mul_of_nonneg_right (wt_mono hδδ x) (abs_nonneg _)

/-- The inclusion as a linear map. -/
def inclL {m m' : ℕ} {δ δ' : ℝ} (hδ : 0 ≤ δ) (hδ' : 0 ≤ δ') (hm : m ≤ m') (hδδ : δ ≤ δ') :
    H m' hδ' →ₗ[ℝ] H m hδ :=
  Submodule.inclusion (Hsub_mono hδ hδ' hm hδδ)

lemma inclL_val {m m' : ℕ} {δ δ' : ℝ} (hδ : 0 ≤ δ) (hδ' : 0 ≤ δ') (hm : m ≤ m')
    (hδδ : δ ≤ δ') (u : H m' hδ') :
    (H.toSub (inclL hδ hδ' hm hδδ u) : Lp ℝ 2 cyl) = (H.toSub u : Lp ℝ 2 cyl) := rfl

lemma norm_inclL_le {m m' : ℕ} {δ δ' : ℝ} (hδ : 0 ≤ δ) (hδ' : 0 ≤ δ') (hm : m ≤ m')
    (hδδ : δ ≤ δ') (u : H m' hδ') : ‖inclL hδ hδ' hm hδδ u‖ ≤ ‖u‖ := by
  set w := inclL hδ hδ' hm hδδ u
  have hidx : ∀ p : idx m, p.1 ∈ idx m' := fun p => mem_idx.2 ((mem_idx.1 p.2).trans hm)
  set F : ℕ × ℕ → ℝ := fun q => if hq : q ∈ idx m' then ‖wdv (H.toSub u) ⟨q, hq⟩‖ ^ 2 else 0
  have hpt : ∀ p : idx m, ‖wdv (H.toSub w) p‖ ^ 2 ≤ F p.1 := by
    intro p
    simp only [F, dif_pos (hidx p)]
    gcongr
    apply Lp.norm_le_norm_of_ae_le
    have hd : dv (H.toSub w) p =ᵐ[cyl] dv (H.toSub u) ⟨p.1, hidx p⟩ :=
      dv_unique (H.toSub w) p (dv_spec (H.toSub u) ⟨p.1, hidx p⟩).1 (dv_memLp _ _)
    filter_upwards [coeFn_wdv (H.toSub w) p, coeFn_wdv (H.toSub u) ⟨p.1, hidx p⟩, hd]
      with x h1 h2 h3
    rw [h1, h2, h3, Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_mul,
      abs_of_pos (wt_pos _ x), abs_of_pos (wt_pos _ x)]
    exact mul_le_mul_of_nonneg_right (wt_mono hδδ x) (abs_nonneg _)
  have hsq : ‖w‖ ^ 2 ≤ ‖u‖ ^ 2 := by
    rw [norm_sq_H, norm_sq_H]
    calc ∑ p : idx m, ‖wdv (H.toSub w) p‖ ^ 2 ≤ ∑ p : idx m, F p.1 :=
          Finset.sum_le_sum fun p _ => hpt p
      _ = ∑ q ∈ idx m, F q := Finset.sum_coe_sort (idx m) F
      _ ≤ ∑ q ∈ idx m', F q := by
          refine Finset.sum_le_sum_of_subset_of_nonneg (fun q hq => mem_idx.2
            ((mem_idx.1 hq).trans hm)) fun q _ _ => ?_
          simp only [F]; split_ifs; positivity
      _ = ∑ p : idx m', F p.1 := (Finset.sum_coe_sort (idx m') F).symm
      _ = ∑ p : idx m', ‖wdv (H.toSub u) p‖ ^ 2 := by
          refine Finset.sum_congr rfl fun p _ => ?_
          simp only [F, dif_pos p.2]
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 hsq

/-- **The inclusion `H^{m',δ'} → H^{m,δ}`** for `m ≤ m'`, `δ ≤ δ'`. -/
def inclH {m m' : ℕ} {δ δ' : ℝ} (hδ : 0 ≤ δ) (hδ' : 0 ≤ δ') (hm : m ≤ m') (hδδ : δ ≤ δ') :
    H m' hδ' →L[ℝ] H m hδ :=
  LinearMap.mkContinuous (inclL hδ hδ' hm hδδ) 1 fun u => by
    rw [one_mul]; exact norm_inclL_le hδ hδ' hm hδδ u

lemma valCLM_inclH {m m' : ℕ} {δ δ' : ℝ} (hδ : 0 ≤ δ) (hδ' : 0 ≤ δ') (hm : m ≤ m')
    (hδδ : δ ≤ δ') (u : H m' hδ') : valCLM m hδ (inclH hδ hδ' hm hδδ u) = valCLM m' hδ' u :=
  rfl

lemma inclH_injective {m m' : ℕ} {δ δ' : ℝ} (hδ : 0 ≤ δ) (hδ' : 0 ≤ δ') (hm : m ≤ m')
    (hδδ : δ ≤ δ') : Function.Injective (inclH hδ hδ' hm hδδ) := fun u v h => by
  apply valCLM_injective (m := m') (hδ := hδ')
  rw [← valCLM_inclH hδ hδ' hm hδδ, h, valCLM_inclH]

end Polyfold.GapP1Sobolev
