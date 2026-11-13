import Polyfold.Chapter5.GapP1_Torunczyk

/-!
# Hilbert spaces of any density admit smooth partitions of unity

The non-separable case of 2021 Theorem 5.5.16, p. 235 (preprint 5.43), for Hilbert spaces: every
real Hilbert space `V`, of any density, admits `C^k` partitions of unity for every `k`
(`admitsContDiffPartitionsOfUnity_of_hilbertSpace`).

*Proof*: for a Hilbert basis `(b_γ)`, the map `h(x) = (‖x‖², (⟨b_γ, x⟩)_γ)` into `c₀(Option Γ)` has
`C^∞` coordinates and is a homeomorphic embedding.  The inverse estimate is a Kadec–Klee argument
in `ℓ²` (`l2_inverse_estimate`): if the coordinates of `v` are within `δ` of those of `u` and
`|‖v‖² − ‖u‖²| ≤ δ`, then `‖v − u‖² ≤ nδ² + 2δ + 2nδ(2‖u‖ + δ) + 4 Σ_{γ ∉ F} u_γ²` for a finite `F`
with `n` elements.  Toruńczyk's theorem (`torunczyk_backward`) concludes.
-/

open Set Function Filter Topology Metric
open scoped ENNReal InnerProductSpace

noncomputable section

namespace Polyfold

universe u

section L2

variable {ι : Type*}

lemma l2_summable_sq (f : lp (fun _ : ι => ℝ) 2) : Summable fun γ => (f γ) ^ 2 := by
  have := (lp.memℓp f).summable (p := 2) (by norm_num)
  simpa [Real.norm_eq_abs, sq_abs] using this

lemma l2_norm_sq (f : lp (fun _ : ι => ℝ) 2) : ‖f‖ ^ 2 = ∑' γ, (f γ) ^ 2 := by
  have := lp.norm_rpow_eq_tsum (p := 2) (by norm_num) f
  simpa [Real.norm_eq_abs, sq_abs] using this

lemma l2_abs_apply_le (f : lp (fun _ : ι => ℝ) 2) (γ : ι) : |f γ| ≤ ‖f‖ := by
  have := lp.norm_apply_le_norm (p := 2) (by norm_num) f γ
  simpa [Real.norm_eq_abs] using this

/-- **The Kadec–Klee estimate in `ℓ²`.** -/
lemma l2_inverse_estimate (u : lp (fun _ : ι => ℝ) 2) {r : ℝ} (hr : 0 < r) :
    ∃ δ > 0, ∀ v : lp (fun _ : ι => ℝ) 2, (∀ γ, |v γ - u γ| ≤ δ) →
      |‖v‖ ^ 2 - ‖u‖ ^ 2| ≤ δ → ‖v - u‖ < r := by
  classical
  have hu := l2_summable_sq u
  -- a finite `F` with a small tail
  obtain ⟨F, hF⟩ : ∃ F : Finset ι, ∑' γ : ↥((F : Set ι)ᶜ), (u γ) ^ 2 < r ^ 2 / 16 := by
    have := tendsto_tsum_compl_atTop_zero fun γ => (u γ) ^ 2
    obtain ⟨F, hF⟩ := (this.eventually (gt_mem_nhds (by positivity : (0 : ℝ) < r ^ 2 / 16))).exists
    exact ⟨F, hF⟩
  set n : ℝ := (F.card : ℝ) with hn
  set M : ℝ := ‖u‖ with hM
  set K : ℝ := n + 2 + 2 * n * (2 * M + 1) with hK
  have hn0 : 0 ≤ n := Nat.cast_nonneg _
  have hM0 : 0 ≤ M := norm_nonneg _
  have hK0 : 0 < K := by positivity
  refine ⟨min 1 (r ^ 2 / (4 * K)), by positivity, fun v hcoord hnorm => ?_⟩
  set δ := min 1 (r ^ 2 / (4 * K)) with hδ
  have hδ0 : 0 < δ := by positivity
  have hδ1 : δ ≤ 1 := min_le_left _ _
  have hδK : δ * K ≤ r ^ 2 / 4 := by
    have := min_le_right 1 (r ^ 2 / (4 * K))
    rw [← hδ, le_div_iff₀ (by positivity)] at this
    linarith
  have hv := l2_summable_sq v
  have hvu := l2_summable_sq (v - u)
  have hTu0 : 0 ≤ ∑' γ : ↥((F : Set ι)ᶜ), (u γ) ^ 2 := tsum_nonneg fun _ => sq_nonneg _
  -- splitting the three sums
  have sU := hu.sum_add_tsum_compl (s := F)
  have sV := hv.sum_add_tsum_compl (s := F)
  have sVU := hvu.sum_add_tsum_compl (s := F)
  rw [← l2_norm_sq] at sU sV sVU
  -- the finite part of `v − u`
  have hfin1 : ∑ γ ∈ F, ((v - u : lp (fun _ : ι => ℝ) 2) γ) ^ 2 ≤ n * δ ^ 2 := by
    calc ∑ γ ∈ F, ((v - u : lp (fun _ : ι => ℝ) 2) γ) ^ 2 ≤ ∑ _γ ∈ F, δ ^ 2 := by
          refine Finset.sum_le_sum fun γ _ => ?_
          rw [lp.coeFn_sub, Pi.sub_apply, ← sq_abs]
          exact pow_le_pow_left₀ (abs_nonneg _) (hcoord γ) 2
      _ = n * δ ^ 2 := by rw [Finset.sum_const, nsmul_eq_mul]
  -- the finite part of `v` is close to that of `u`
  have hfin2 : ∑ γ ∈ F, (u γ) ^ 2 - n * (δ * (2 * M + δ)) ≤ ∑ γ ∈ F, (v γ) ^ 2 := by
    have : ∀ γ ∈ F, (u γ) ^ 2 - δ * (2 * M + δ) ≤ (v γ) ^ 2 := by
      intro γ _
      have h1 := hcoord γ
      have h2 := l2_abs_apply_le u γ
      have h3 : |(u γ) ^ 2 - (v γ) ^ 2| ≤ δ * (2 * M + δ) := by
        rw [sq_sub_sq, abs_mul]
        have h4 : |u γ - v γ| ≤ δ := by rw [abs_sub_comm]; exact h1
        have h5 : |u γ + v γ| ≤ 2 * M + δ := by
          have : u γ + v γ = 2 * u γ + (v γ - u γ) := by ring
          rw [this]
          calc |2 * u γ + (v γ - u γ)| ≤ |2 * u γ| + |v γ - u γ| := abs_add_le _ _
            _ ≤ 2 * M + δ := by rw [abs_mul, abs_two]; linarith
        calc |u γ + v γ| * |u γ - v γ| ≤ (2 * M + δ) * δ :=
              mul_le_mul h5 h4 (abs_nonneg _) (by positivity)
          _ = δ * (2 * M + δ) := mul_comm _ _
      linarith [le_abs_self ((u γ) ^ 2 - (v γ) ^ 2)]
    calc ∑ γ ∈ F, (u γ) ^ 2 - n * (δ * (2 * M + δ))
        = ∑ γ ∈ F, ((u γ) ^ 2 - δ * (2 * M + δ)) := by
          rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ γ ∈ F, (v γ) ^ 2 := Finset.sum_le_sum this
  -- the tail of `v − u`
  have htail : ∑' γ : ↥((F : Set ι)ᶜ), ((v - u : lp (fun _ : ι => ℝ) 2) γ) ^ 2 ≤
      2 * ∑' γ : ↥((F : Set ι)ᶜ), (v γ) ^ 2 + 2 * ∑' γ : ↥((F : Set ι)ᶜ), (u γ) ^ 2 := by
    have sv' : Summable fun γ : ↥((F : Set ι)ᶜ) => (v γ) ^ 2 := hv.subtype _
    have su' : Summable fun γ : ↥((F : Set ι)ᶜ) => (u γ) ^ 2 := hu.subtype _
    have svu' : Summable fun γ : ↥((F : Set ι)ᶜ) => ((v - u : lp (fun _ : ι => ℝ) 2) γ) ^ 2 :=
      hvu.subtype _
    calc ∑' γ : ↥((F : Set ι)ᶜ), ((v - u : lp (fun _ : ι => ℝ) 2) γ) ^ 2
        ≤ ∑' γ : ↥((F : Set ι)ᶜ), (2 * (v γ) ^ 2 + 2 * (u γ) ^ 2) := by
          refine Summable.tsum_le_tsum (fun γ => ?_) svu' ((sv'.mul_left 2).add (su'.mul_left 2))
          rw [lp.coeFn_sub, Pi.sub_apply]
          nlinarith [sq_nonneg ((v : ι → ℝ) γ + (u : ι → ℝ) γ)]
      _ = 2 * ∑' γ : ↥((F : Set ι)ᶜ), (v γ) ^ 2 + 2 * ∑' γ : ↥((F : Set ι)ᶜ), (u γ) ^ 2 := by
          rw [(sv'.mul_left 2).tsum_add (su'.mul_left 2), tsum_mul_left, tsum_mul_left]
  have hnorm' : ‖v‖ ^ 2 ≤ ‖u‖ ^ 2 + δ := by linarith [le_abs_self (‖v‖ ^ 2 - ‖u‖ ^ 2)]
  have hsq : ‖v - u‖ ^ 2 < r ^ 2 := by
    have e1 : ‖v - u‖ ^ 2 ≤ n * δ ^ 2 + 2 * δ + 2 * n * (δ * (2 * M + δ)) +
        4 * ∑' γ : ↥((F : Set ι)ᶜ), (u γ) ^ 2 := by
      rw [hM] at hfin2 ⊢
      linarith
    have e2 : n * δ ^ 2 + 2 * δ + 2 * n * (δ * (2 * M + δ)) ≤ δ * K := by
      rw [hK]
      have : δ ^ 2 ≤ δ := by nlinarith
      have : δ * (2 * M + δ) ≤ δ * (2 * M + 1) := by nlinarith
      nlinarith
    linarith
  exact lt_of_pow_lt_pow_left₀ 2 hr.le hsq

end L2

section Hilbert

variable (V : Type u) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]

set_option maxHeartbeats 800000 in
-- one construction: the embedding and its three properties
/-- **The non-separable Hilbert case of 2021 Theorem 5.5.16, p. 235 (preprint 5.43)**: every real
Hilbert space, of any density, admits `C^k` partitions of unity, for every `k`.  The map
`x ↦ (‖x‖², (⟨b_γ, x⟩)_γ)` for a Hilbert basis is a coordinate-wise `C^∞` homeomorphic embedding
into `c₀`, and Toruńczyk's theorem applies. -/
theorem admitsContDiffPartitionsOfUnity_of_hilbertSpace (k : ℕ∞) :
    AdmitsContDiffPartitionsOfUnity V k := by
  classical
  obtain ⟨w, b, -⟩ := exists_hilbertBasis ℝ V
  have hrepr : ∀ x γ, b.repr x γ = ⟪b γ, x⟫_ℝ := fun x γ => b.repr_apply_apply x γ
  have hb1 : ∀ γ, ‖b γ‖ = 1 := fun γ => b.orthonormal.1 γ
  have hcoef : ∀ x γ, |⟪b γ, x⟫_ℝ| ≤ ‖x‖ := fun x γ => by
    have := abs_real_inner_le_norm (b γ) x
    rwa [hb1, one_mul] at this
  set H₀ : V → Option w → ℝ := fun x o => o.elim (‖x‖ ^ 2) fun γ => ⟪b γ, x⟫_ℝ with hH₀
  have hmem : ∀ x, Memℓp (H₀ x) ∞ := fun x => memℓp_infty ⟨‖x‖ ^ 2 + ‖x‖, by
    rintro _ ⟨o, rfl⟩
    show ‖H₀ x o‖ ≤ ‖x‖ ^ 2 + ‖x‖
    rcases o with _ | γ
    · simp only [hH₀, Option.elim, Real.norm_eq_abs, abs_pow, abs_norm]
      linarith [norm_nonneg x]
    · simp only [hH₀, Option.elim, Real.norm_eq_abs]
      linarith [hcoef x γ, sq_nonneg ‖x‖]⟩
  set H₁ : V → lp (fun _ : Option w => ℝ) ∞ := fun x => ⟨H₀ x, hmem x⟩ with hH₁
  have hc0 : ∀ x, H₁ x ∈ cZero (Option w) := by
    intro x
    rw [mem_cZero_iff]
    intro ε hε
    have hfin : {γ : w | ε < |⟪b γ, x⟫_ℝ|}.Finite := by
      have ht := (l2_summable_sq (b.repr x)).tendsto_cofinite_zero
      have := (ht.eventually (gt_mem_nhds (by positivity : (0 : ℝ) < ε ^ 2)))
      rw [Filter.eventually_cofinite] at this
      refine this.subset fun γ hγ => ?_
      simp only [mem_ofPred_eq, not_lt]
      rw [hrepr]
      have hγ' : ε < |⟪b γ, x⟫_ℝ| := hγ
      have : ε ^ 2 < ⟪b γ, x⟫_ℝ ^ 2 := by
        rw [← sq_abs (⟪b γ, x⟫_ℝ)]
        exact pow_lt_pow_left₀ hγ' hε.le two_ne_zero
      exact this.le
    refine ((hfin.image some).insert none).subset fun o ho => ?_
    rcases o with _ | γ
    · exact mem_insert _ _
    · exact mem_insert_of_mem _ ⟨γ, ho, rfl⟩
  set h : V → cZero (Option w) := fun x => ⟨H₁ x, hc0 x⟩ with hh
  have hcz : ∀ x o, cz (h x) o = H₀ x o := fun x o => rfl
  -- the coordinate estimate
  have hdiff : ∀ x y, ‖h y - h x‖ ≤ |‖y‖ ^ 2 - ‖x‖ ^ 2| + ‖y - x‖ := by
    intro x y
    refine norm_sub_le_of_forall (by positivity) fun o => ?_
    rw [hcz, hcz]
    rcases o with _ | γ
    · simp only [hH₀, Option.elim]
      linarith [norm_nonneg (y - x)]
    · simp only [hH₀, Option.elim]
      rw [← inner_sub_right]
      linarith [hcoef (y - x) γ, abs_nonneg (‖y‖ ^ 2 - ‖x‖ ^ 2)]
  have hcont : Continuous h := by
    rw [continuous_iff_continuousAt]
    intro x
    rw [ContinuousAt, Metric.tendsto_nhds]
    intro ε hε
    have hf : Continuous fun y : V => |‖y‖ ^ 2 - ‖x‖ ^ 2| + ‖y - x‖ := by fun_prop
    have := (hf.tendsto x).eventually (gt_mem_nhds (by simp; exact hε))
    filter_upwards [this] with y hy
    rw [dist_eq_norm]
    exact lt_of_le_of_lt (hdiff x y) hy
  have hind : Topology.IsInducing h := by
    rw [Topology.isInducing_iff_nhds]
    intro x
    refine le_antisymm (tendsto_iff_comap.1 (hcont.tendsto x)) ?_
    intro U hU
    obtain ⟨r, hr, hrU⟩ := Metric.mem_nhds_iff.1 hU
    obtain ⟨δ, hδ, hδr⟩ := l2_inverse_estimate (b.repr x) hr
    refine Filter.mem_comap.2 ⟨ball (h x) δ, ball_mem_nhds _ hδ, fun y hy => hrU ?_⟩
    have hy' : ‖h y - h x‖ < δ := by rwa [mem_preimage, mem_ball, dist_eq_norm] at hy
    have h1 : ∀ γ, |b.repr y γ - b.repr x γ| ≤ δ := fun γ => by
      have := abs_cz_sub_le (h y) (h x) (some γ)
      rw [hcz, hcz] at this
      simp only [hH₀, Option.elim] at this
      rw [hrepr, hrepr]
      linarith
    have h2 : |‖b.repr y‖ ^ 2 - ‖b.repr x‖ ^ 2| ≤ δ := by
      have := abs_cz_sub_le (h y) (h x) none
      rw [hcz, hcz] at this
      simp only [hH₀, Option.elim] at this
      rw [LinearIsometryEquiv.norm_map, LinearIsometryEquiv.norm_map]
      linarith
    have := hδr (b.repr y) h1 h2
    rw [← map_sub, LinearIsometryEquiv.norm_map] at this
    rwa [mem_ball, dist_eq_norm]
  refine torunczyk_backward (h := h) ⟨⟨hind, hind.injective⟩, fun o => ?_⟩
  rcases o with _ | γ
  · exact contDiff_norm_sq ℝ
  · exact (innerSL ℝ (b γ)).contDiff

/-- **2021 Theorem 5.5.16 for Hilbert spaces of any density**: the statement holds for every real
Hilbert space (its conclusion holds outright). -/
theorem godefroyTroyanskiWhitfieldZizlerStatement_of_hilbertSpace (k : ℕ∞) :
    GodefroyTroyanskiWhitfieldZizlerStatement V k :=
  fun _ _ => admitsContDiffPartitionsOfUnity_of_hilbertSpace V k

end Hilbert

end Polyfold
