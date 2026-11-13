import Polyfold.Chapter5.GapP1_Torunczyk
import Polyfold.Chapter5.GapP1_SeparablePOU

/-!
# Locally `c₀`-finite bases of `C^k` functions, and the gluing lemma

A tool for the non-separable case of 2021 Theorem 5.5.16, p. 235 (preprint 5.43).

`IsRelC0Base k Q f` says that the family `f i : X → ℝ` has these properties:
* the `f i` are `C^k` with values in `[-1, 1]`;
* the family is *locally `c₀`-finite*: near each point, all but finitely many `|f i|` are `≤ ε`;
* its cozero sets are small relative to `Q`: for each `x` and `ε` there is an `i` with
  `f i x ≠ 0` and `dist (Q y) (Q x) < ε` whenever `f i y ≠ 0`.

## Results

* `admitsContDiffPartitionsOfUnity_of_isRelC0Base`: such a base (with `Q = id`) gives `C^k`
  partitions of unity, through the coordinate-wise embedding `x ↦ (f i x)_i` into `c₀` and
  Toruńczyk's theorem (`torunczyk_backward`).
* `exists_isRelC0Base_of_admits`: `C^k` partitions of unity give such a base.
* `isRelC0Base_glue`, the **gluing lemma**. Suppose `X` has a `C^k` bump and bounded operators
  `Δ i, Q i` such that:
  - `(‖Δ i x‖)_i ∈ c₀`;
  - every `x ≠ 0` is approximated by some `Q i x` with `Δ i x ≠ 0`;
  - each `Q i` carries a base relative to `Q i`.

  Then `X` has a base. With `Δ = P_{α+1} − P_α` and `Q = P_{α+1}`, for a projectional
  resolution of the identity, this is the inductive step of the proof of Theorem 5.5.16.
-/

open Set Function Filter Topology Metric
open scoped ENNReal

noncomputable section

namespace Polyfold

universe u

section C0Base

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] {k : ℕ∞}

/-- A **locally `c₀`-finite family of `C^k` functions whose cozero sets are `Q`-small** (a tool for
2021 Theorem 5.5.16, p. 235). -/
def IsRelC0Base {Y : Type*} [PseudoMetricSpace Y] (k : ℕ∞) (Q : X → Y) {I : Type*}
    (f : I → X → ℝ) : Prop :=
  (∀ i, ContDiff ℝ k (f i)) ∧ (∀ i x, |f i x| ≤ 1) ∧
    (∀ x, ∀ ε > 0, ∃ U ∈ 𝓝 x, ∃ F : Set I, F.Finite ∧ ∀ y ∈ U, ∀ i ∉ F, |f i y| ≤ ε) ∧
    (∀ x, ∀ ε > 0, ∃ i, f i x ≠ 0 ∧ ∀ y, f i y ≠ 0 → dist (Q y) (Q x) < ε)

/-- A base pulls back along a bounded linear operator. -/
theorem IsRelC0Base.comp {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y] {I : Type*}
    {g : I → Y → ℝ} (hg : IsRelC0Base k (id : Y → Y) g) (L : X →L[ℝ] Y) :
    IsRelC0Base k (fun x => L x) (fun i x => g i (L x)) := by
  obtain ⟨hc, hb, hlf, hbase⟩ := hg
  refine ⟨fun i => (hc i).comp L.contDiff, fun i x => hb i (L x), fun x ε hε => ?_,
    fun x ε hε => ?_⟩
  · obtain ⟨U, hU, F, hF, hUF⟩ := hlf (L x) ε hε
    exact ⟨L ⁻¹' U, L.continuous.continuousAt.preimage_mem_nhds hU, F, hF,
      fun y hy i hi => hUF (L y) hy i hi⟩
  · obtain ⟨i, hi, hsmall⟩ := hbase (L x) ε hε
    exact ⟨i, hi, fun y hy => hsmall (L y) hy⟩

/-- A base relative to `Q` is a base relative to any `Q'` with the same distances. -/
theorem IsRelC0Base.of_dist_eq {Y Y' : Type*} [PseudoMetricSpace Y] [PseudoMetricSpace Y']
    {Q : X → Y} {Q' : X → Y'} {I : Type*} {f : I → X → ℝ} (hf : IsRelC0Base k Q f)
    (hQ : ∀ x y, dist (Q' y) (Q' x) = dist (Q y) (Q x)) : IsRelC0Base k Q' f := by
  obtain ⟨hc, hb, hlf, hbase⟩ := hf
  refine ⟨hc, hb, hlf, fun x ε hε => ?_⟩
  obtain ⟨i, hi, hsmall⟩ := hbase x ε hε
  exact ⟨i, hi, fun y hy => (hQ x y).symm ▸ hsmall y hy⟩

end C0Base

/-! ### From partitions of unity to a base, and back -/

section POU

variable {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X] {k : ℕ∞}

/-- **`C^k` partitions of unity give a base** (`f (c, n) = ρₙ c / (n + 1)` for partitions of unity
`ρₙ` subordinate to the balls of radius `1 / (n + 1)`). -/
theorem exists_isRelC0Base_of_admits (hP : AdmitsContDiffPartitionsOfUnity X k) :
    ∃ (I : Type u) (f : I → X → ℝ), IsRelC0Base k (id : X → X) f := by
  classical
  have hex : ∀ n : ℕ, ∃ ρ : PartitionOfUnity X X,
      ρ.IsSubordinate (fun c => ball c (1 / ((n : ℝ) + 1))) ∧ ∀ c, ContDiff ℝ k (ρ c) :=
    fun n => hP X (fun c => ball c (1 / ((n : ℝ) + 1))) (fun c => isOpen_ball)
      (eq_univ_of_forall fun x => mem_iUnion.2 ⟨x, mem_ball_self (by positivity)⟩)
  choose ρ hρs hρc using hex
  have hcoef : ∀ n : ℕ, 0 < 1 / ((n : ℝ) + 1) ∧ 1 / ((n : ℝ) + 1) ≤ 1 := fun n =>
    ⟨by positivity, by rw [div_le_one (by positivity)]; linarith [n.cast_nonneg (α := ℝ)]⟩
  refine ⟨X × ℕ, fun p y => 1 / ((p.2 : ℝ) + 1) * ρ p.2 p.1 y,
    fun p => contDiff_const.mul (hρc p.2 p.1), fun p y => ?_, fun x ε hε => ?_,
    fun x ε hε => ?_⟩
  · rw [abs_mul, abs_of_pos (hcoef p.2).1, abs_of_nonneg ((ρ p.2).nonneg p.1 y)]
    exact mul_le_one₀ (hcoef p.2).2 ((ρ p.2).nonneg p.1 y) ((ρ p.2).le_one p.1 y)
  · obtain ⟨M, hM⟩ := exists_nat_one_div_lt hε
    have hlf := fun n => (ρ n).locallyFinite x
    choose t ht hfin using hlf
    refine ⟨⋂ n ∈ Iio M, t n, (biInter_mem (finite_Iio M)).2 fun n _ => ht n,
      ⋃ n ∈ Iio M, {c | (support (ρ n c) ∩ t n).Nonempty} ×ˢ {n},
      (finite_Iio M).biUnion fun n _ => (hfin n).prod (finite_singleton n),
      fun y hy p hp => ?_⟩
    change |1 / ((p.2 : ℝ) + 1) * ρ p.2 p.1 y| ≤ ε
    have hb1 : |1 / ((p.2 : ℝ) + 1) * ρ p.2 p.1 y| ≤ 1 / ((p.2 : ℝ) + 1) := by
      rw [abs_mul, abs_of_pos (hcoef p.2).1, abs_of_nonneg ((ρ p.2).nonneg p.1 y)]
      exact mul_le_of_le_one_right (hcoef p.2).1.le ((ρ p.2).le_one p.1 y)
    by_cases hpM : p.2 < M
    · have hy' : y ∈ t p.2 := mem_iInter₂.1 hy p.2 hpM
      have hz : ρ p.2 p.1 y = 0 := by
        by_contra hne
        exact hp (mem_iUnion₂.2 ⟨p.2, hpM, ⟨⟨y, hne, hy'⟩, rfl⟩⟩)
      rw [hz, mul_zero, abs_zero]
      exact hε.le
    · refine hb1.trans (le_trans ?_ hM.le)
      gcongr
      exact_mod_cast not_lt.1 hpM
  · obtain ⟨n, hn⟩ := exists_nat_one_div_lt (half_pos hε)
    obtain ⟨c, hc⟩ := (ρ n).exists_pos (mem_univ x)
    refine ⟨(c, n), mul_ne_zero (hcoef n).1.ne' hc.ne', fun y hy => ?_⟩
    have hy' : ρ n c y ≠ 0 := right_ne_zero_of_mul hy
    have h1 : y ∈ ball c (1 / ((n : ℝ) + 1)) := hρs n c (subset_tsupport _ hy')
    have h2 : x ∈ ball c (1 / ((n : ℝ) + 1)) := hρs n c (subset_tsupport _ hc.ne')
    rw [mem_ball] at h1 h2
    calc dist (id y) (id x) ≤ dist y c + dist x c := dist_triangle_right y x c
      _ < ε := by linarith

variable {I : Type u} {f : I → X → ℝ}

/-- **A base gives `C^k` partitions of unity**: `x ↦ (f i x)_i` is a coordinate-wise `C^k`
homeomorphic embedding into `c₀(I)`, and Toruńczyk's theorem (`torunczyk_backward`) applies. -/
theorem admitsContDiffPartitionsOfUnity_of_isRelC0Base (hf : IsRelC0Base k (id : X → X) f) :
    AdmitsContDiffPartitionsOfUnity X k := by
  classical
  obtain ⟨hc, hb, hlf, hbase⟩ := hf
  have hmem : ∀ x, Memℓp (fun i => f i x) ∞ := fun x =>
    memℓp_infty ⟨1, by rintro _ ⟨i, rfl⟩; simpa [Real.norm_eq_abs] using hb i x⟩
  have hc0 : ∀ x, (⟨fun i => f i x, hmem x⟩ : lp (fun _ : I => ℝ) ∞) ∈ cZero I := fun x =>
    mem_cZero_iff.2 fun ε hε => by
      obtain ⟨U, hU, F, hF, hUF⟩ := hlf x ε hε
      refine hF.subset fun i hi => ?_
      by_contra hiF
      exact (not_le.2 hi) (hUF x (mem_of_mem_nhds hU) i hiF)
  set h : X → cZero I := fun x => ⟨⟨fun i => f i x, hmem x⟩, hc0 x⟩ with hh
  have hcz : ∀ x i, cz (h x) i = f i x := fun x i => rfl
  -- continuity
  have hcont : Continuous h := by
    refine continuous_iff_continuousAt.2 fun x => Metric.tendsto_nhds.2 fun ε hε => ?_
    obtain ⟨U, hU, F, hF, hUF⟩ := hlf x (ε / 3) (by positivity)
    have hev : ∀ᶠ y in 𝓝 x, ∀ i ∈ F, |f i y - f i x| < ε / 3 :=
      (eventually_all_finite hF).2 fun i _ =>
        (((hc i).continuous.sub continuous_const).abs.tendsto' x 0 (by simp)).eventually
          (gt_mem_nhds (by positivity))
    filter_upwards [hev, hU] with y hy hyU
    rw [dist_eq_norm]
    refine (norm_sub_le_of_forall (by positivity) fun i => ?_).trans_lt
      (by linarith : 2 * (ε / 3) < ε)
    rw [hcz, hcz]
    by_cases hi : i ∈ F
    · linarith [hy i hi]
    · calc |f i y - f i x| ≤ |f i y| + |f i x| := abs_sub _ _
        _ ≤ ε / 3 + ε / 3 := add_le_add (hUF y hyU i hi) (hUF x (mem_of_mem_nhds hU) i hi)
        _ = 2 * (ε / 3) := by ring
  -- injectivity
  have hinj : Injective h := by
    intro x y hxy
    by_contra hne
    obtain ⟨i, hi, hsmall⟩ := hbase x (dist y x) (dist_pos.2 (Ne.symm hne))
    have : f i y = f i x := by rw [← hcz, ← hcz, hxy]
    exact (hsmall y (this ▸ hi)).false
  -- the topology is induced
  have hind : Topology.IsInducing h := by
    refine Topology.isInducing_iff_nhds.2 fun x => le_antisymm (hcont.tendsto x).le_comap ?_
    refine Metric.nhds_basis_ball.ge_iff.2 fun ε hε => ?_
    obtain ⟨i, hi, hsmall⟩ := hbase x ε hε
    refine mem_comap.2 ⟨{z | |cz z i - f i x| < |f i x|},
      IsOpen.mem_nhds (isOpen_lt ((continuous_cz i).sub continuous_const).abs continuous_const)
        (by simp only [mem_ofPred_eq, hcz, sub_self, abs_zero]; exact abs_pos.2 hi),
      fun y hy => ?_⟩
    have hy' : |f i y - f i x| < |f i x| := hy
    have hne : f i y ≠ 0 := fun h0 => by
      rw [h0, zero_sub, abs_neg] at hy'
      exact lt_irrefl _ hy'
    exact mem_ball.2 (hsmall y hne)
  exact torunczyk_backward (h := h) ⟨⟨hind, hinj⟩, fun i => hc i⟩

end POU

/-! ### The gluing lemma -/

section Glue

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] {k : ℕ∞}

/-- **A cut-off function from a bump**: `χ : X → [0, 1]`, `C^k`, with `χ = 1` on `B(0, δ)` and
`χ x ≠ 0 → ‖x‖ < 1`, for some `0 < δ ≤ 1`. -/
theorem HasContDiffBump.exists_cutoff (hb : HasContDiffBump X k) :
    ∃ (χ : X → ℝ) (δ : ℝ), ContDiff ℝ k χ ∧ (∀ x, χ x ∈ Icc (0 : ℝ) 1) ∧ 0 < δ ∧ δ ≤ 1 ∧
      (∀ x, ‖x‖ < δ → χ x = 1) ∧ ∀ x, χ x ≠ 0 → ‖x‖ < 1 := by
  obtain ⟨ψ, R, hψc, hψ01, hψ1, hψs⟩ := hb.exists_one_on_ball
  have hR : 0 < R := by
    have h0 : (0 : X) ∈ support ψ := by
      rw [mem_support, hψ1 0 (mem_ball_self one_pos)]; exact one_ne_zero
    simpa using hψs h0
  refine ⟨fun x => ψ (R • x), min (1 / R) 1, hψc.comp (contDiff_const.smul contDiff_id),
    fun x => hψ01 _, lt_min (by positivity) one_pos, min_le_right _ _, fun x hx => ?_,
    fun x hx => ?_⟩
  · refine hψ1 _ (mem_ball_zero_iff.2 ?_)
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hR]
    have : ‖x‖ < 1 / R := hx.trans_le (min_le_left _ _)
    rw [lt_div_iff₀ hR] at this
    linarith
  · have h1 := mem_ball_zero_iff.1 (hψs hx)
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hR] at h1
    nlinarith [norm_nonneg x]

lemma glue_abs_coef_mul_le {a b c d : ℝ} (ha : 0 < a) (hb : b ∈ Icc (0 : ℝ) 1)
    (hc : c ∈ Icc (0 : ℝ) 1) {e : ℝ} (hd : |d| ≤ e) : |a * (b * c * d)| ≤ a * e := by
  rw [abs_mul, abs_of_pos ha, abs_mul, abs_mul, abs_of_nonneg hb.1, abs_of_nonneg hc.1]
  gcongr
  calc b * c * |d| ≤ 1 * |d| := by gcongr; exact mul_le_one₀ hb.2 hc.1 hc.2
    _ ≤ e := by rw [one_mul]; exact hd

/-- **The gluing lemma** (the inductive step of 2021 Theorem 5.5.16, p. 235). Suppose:
* `X` has a `C^k` bump;
* `Δ i, Q i` are bounded operators with `‖Δ i‖ ≤ C`;
* `(‖Δ i x‖)_i ∈ c₀` for every `x`;
* every `x ≠ 0` is approximated by `Q i x` for some `i` with `Δ i x ≠ 0`;
* each `Q i` carries a base `g i` relative to `Q i`.

Then `X` has a base. The functions are
`(m+1)⁻¹(N+1)⁻¹ ψ((m+1) Δᵢ y) χ((N+1)(y − Qᵢ y)) gᵢⱼ(y)` and `(N+1)⁻¹ χ((N+1) y)`, with
`ψ = 1 − χ`. -/
theorem isRelC0Base_glue (hb : HasContDiffBump X k) {ι : Type*} (Δ Q : ι → X →L[ℝ] X) {C : ℝ}
    (hC : ∀ i, ‖Δ i‖ ≤ C) (hP1 : ∀ x, ∀ η > 0, {i | η < ‖Δ i x‖}.Finite)
    (hP2 : ∀ x ≠ 0, ∀ η > 0, ∃ i, Δ i x ≠ 0 ∧ ‖x - Q i x‖ < η)
    {J : ι → Type*} (g : ∀ i, J i → X → ℝ) (hg : ∀ i, IsRelC0Base k (fun x => Q i x) (g i)) :
    ∃ f : ((Σ i, J i) × ℕ × ℕ) ⊕ ℕ → X → ℝ, IsRelC0Base k (id : X → X) f := by
  classical
  obtain ⟨χ, δ, hχc, hχ01, hδ, hδ1, hχ1, hχ0⟩ := hb.exists_cutoff
  set ψ : X → ℝ := fun z => 1 - χ z with hψ
  have hψc : ContDiff ℝ k ψ := contDiff_const.sub hχc
  have hψ01 : ∀ z, ψ z ∈ Icc (0 : ℝ) 1 := fun z =>
    ⟨by simp only [hψ]; linarith [(hχ01 z).2], by simp only [hψ]; linarith [(hχ01 z).1]⟩
  have hψ0 : ∀ z, ‖z‖ < δ → ψ z = 0 := fun z hz => by simp only [hψ, hχ1 z hz, sub_self]
  have hψ1 : ∀ z, 1 ≤ ‖z‖ → ψ z = 1 := fun z hz => by
    have : χ z = 0 := by
      by_contra hne
      exact (not_lt.2 hz) (hχ0 z hne)
    simp only [hψ, this, sub_zero]
  have hcoef : ∀ m N : ℕ, 0 < 1 / (((m : ℝ) + 1) * ((N : ℝ) + 1)) := fun m N => by positivity
  set f : ((Σ i, J i) × ℕ × ℕ) ⊕ ℕ → X → ℝ := fun a => Sum.elim
    (fun p y => 1 / (((p.2.1 : ℝ) + 1) * ((p.2.2 : ℝ) + 1)) *
      (ψ (((p.2.1 : ℝ) + 1) • Δ p.1.1 y) * χ (((p.2.2 : ℝ) + 1) • (y - Q p.1.1 y)) *
        g p.1.1 p.1.2 y))
    (fun N y => 1 / ((N : ℝ) + 1) * χ (((N : ℝ) + 1) • y)) a with hf
  have hfl : ∀ (i : ι) (j : J i) (m N : ℕ) (y : X), f (Sum.inl (⟨i, j⟩, m, N)) y =
      1 / (((m : ℝ) + 1) * ((N : ℝ) + 1)) *
        (ψ (((m : ℝ) + 1) • Δ i y) * χ (((N : ℝ) + 1) • (y - Q i y)) * g i j y) :=
    fun _ _ _ _ _ => rfl
  have hfr : ∀ (N : ℕ) (y : X), f (Sum.inr N) y = 1 / ((N : ℝ) + 1) * χ (((N : ℝ) + 1) • y) :=
    fun _ _ => rfl
  have hfl_le : ∀ (i : ι) (j : J i) (m N : ℕ) (y : X), |f (Sum.inl (⟨i, j⟩, m, N)) y| ≤
      1 / (((m : ℝ) + 1) * ((N : ℝ) + 1)) * |g i j y| := fun i j m N y => by
    rw [hfl]; exact glue_abs_coef_mul_le (hcoef m N) (hψ01 _) (hχ01 _) le_rfl
  have hfr_le : ∀ (N : ℕ) (y : X), |f (Sum.inr N) y| ≤ 1 / ((N : ℝ) + 1) := fun N y => by
    rw [hfr, abs_mul, abs_of_pos (by positivity), abs_of_nonneg (hχ01 _).1]
    exact mul_le_of_le_one_right (by positivity) (hχ01 _).2
  refine ⟨f, fun a => ?_, fun a y => ?_, fun x ε hε => ?_, fun x ε hε => ?_⟩
  · -- smoothness
    rcases a with ⟨⟨i, j⟩, m, N⟩ | N
    · exact contDiff_const.mul (((hψc.comp (contDiff_const.smul (Δ i).contDiff)).mul
        (hχc.comp (contDiff_const.smul (contDiff_id.sub (Q i).contDiff)))).mul ((hg i).1 j))
    · exact contDiff_const.mul (hχc.comp (contDiff_const.smul contDiff_id))
  · -- bounded by one
    rcases a with ⟨⟨i, j⟩, m, N⟩ | N
    · refine (hfl_le i j m N y).trans ?_
      have h1 : 1 / (((m : ℝ) + 1) * ((N : ℝ) + 1)) ≤ 1 := by
        rw [div_le_one (by positivity)]
        nlinarith [m.cast_nonneg (α := ℝ), N.cast_nonneg (α := ℝ)]
      exact mul_le_one₀ h1 (abs_nonneg _) ((hg i).2.1 j y)
    · refine (hfr_le N y).trans ?_
      rw [div_le_one (by positivity)]; linarith [N.cast_nonneg (α := ℝ)]
  · -- locally `c₀`-finite
    obtain ⟨M, hM⟩ := exists_nat_one_div_lt hε
    set θ : ℝ := δ / ((M : ℝ) + 1) with hθ
    have hθ0 : 0 < θ := by positivity
    set Fi := {i | θ / 2 < ‖Δ i x‖} with hFi
    have hFifin : Fi.Finite := hP1 x (θ / 2) (by positivity)
    have hlf := fun i => (hg i).2.2.1 x ε hε
    choose U hU G hG hUG using hlf
    set r : ℝ := θ / (2 * (|C| + 1)) with hr
    have hr0 : 0 < r := by positivity
    refine ⟨ball x r ∩ ⋂ i ∈ Fi, U i, inter_mem (ball_mem_nhds x hr0)
      ((biInter_mem hFifin).2 fun i _ => hU i),
      Sum.inl '' ((⋃ i ∈ Fi, Sigma.mk i '' G i) ×ˢ (Iio M ×ˢ Iio M)) ∪ Sum.inr '' Iio M,
      (((hFifin.biUnion fun i _ => (hG i).image _).prod
        ((finite_Iio M).prod (finite_Iio M))).image _).union ((finite_Iio M).image _),
      fun y hy a ha => ?_⟩
    have hyx : ‖y - x‖ < r := by rw [← dist_eq_norm]; exact hy.1
    have hcoefM : ∀ m N : ℕ, ¬ (m < M ∧ N < M) →
        1 / (((m : ℝ) + 1) * ((N : ℝ) + 1)) ≤ 1 / ((M : ℝ) + 1) := fun m N hmN => by
      have hMle : (M : ℝ) + 1 ≤ ((m : ℝ) + 1) * ((N : ℝ) + 1) := by
        rcases not_and_or.1 hmN with h | h
        · have : (M : ℝ) ≤ m := by exact_mod_cast not_lt.1 h
          nlinarith [N.cast_nonneg (α := ℝ)]
        · have : (M : ℝ) ≤ N := by exact_mod_cast not_lt.1 h
          nlinarith [m.cast_nonneg (α := ℝ)]
      exact one_div_le_one_div_of_le (by positivity) hMle
    rcases a with ⟨⟨i, j⟩, m, N⟩ | N
    · by_cases hmN : m < M ∧ N < M
      · by_cases hi : i ∈ Fi
        · have hj : j ∉ G i := fun hj => ha (Or.inl ⟨_, ⟨mem_iUnion₂.2 ⟨i, hi, j, hj, rfl⟩,
            mem_Iio.2 hmN.1, mem_Iio.2 hmN.2⟩, rfl⟩)
          refine (hfl_le i j m N y).trans ?_
          calc 1 / (((m : ℝ) + 1) * ((N : ℝ) + 1)) * |g i j y|
              ≤ 1 * ε := by
                gcongr
                · rw [div_le_one (by positivity)]
                  nlinarith [m.cast_nonneg (α := ℝ), N.cast_nonneg (α := ℝ)]
                · exact hUG i y (mem_iInter₂.1 hy.2 i hi) j hj
            _ = ε := one_mul ε
        · -- the gate vanishes
          have hΔx : ‖Δ i x‖ ≤ θ / 2 := not_lt.1 hi
          have hΔyx : ‖Δ i y - Δ i x‖ < θ / 2 := by
            rw [← map_sub]
            calc ‖Δ i (y - x)‖ ≤ ‖Δ i‖ * ‖y - x‖ := (Δ i).le_opNorm _
              _ ≤ (|C| + 1) * ‖y - x‖ := by
                  gcongr; exact (hC i).trans ((le_abs_self C).trans (by linarith))
              _ < (|C| + 1) * r := by gcongr
              _ = θ / 2 := by rw [hr]; field_simp
          have hΔy : ‖Δ i y‖ < θ := by
            have := norm_le_norm_add_norm_sub' (Δ i y) (Δ i x)
            linarith
          have hgate : ψ (((m : ℝ) + 1) • Δ i y) = 0 := by
            refine hψ0 _ ?_
            rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity)]
            have hmM : (m : ℝ) + 1 ≤ (M : ℝ) + 1 := by
              have : (m : ℝ) < M := by exact_mod_cast hmN.1
              linarith
            calc ((m : ℝ) + 1) * ‖Δ i y‖ ≤ ((M : ℝ) + 1) * ‖Δ i y‖ := by gcongr
              _ < ((M : ℝ) + 1) * θ := by gcongr
              _ = δ := by rw [hθ]; field_simp
          rw [hfl, hgate, zero_mul, zero_mul, mul_zero, abs_zero]
          exact hε.le
      · refine (hfl_le i j m N y).trans ?_
        calc 1 / (((m : ℝ) + 1) * ((N : ℝ) + 1)) * |g i j y|
            ≤ 1 / ((M : ℝ) + 1) * 1 :=
              mul_le_mul (hcoefM m N hmN) ((hg i).2.1 j y) (abs_nonneg _) (by positivity)
          _ ≤ ε := by rw [mul_one]; exact hM.le
    · have hN : ¬ N < M := fun hN => ha (Or.inr ⟨N, mem_Iio.2 hN, rfl⟩)
      refine (hfr_le N y).trans (le_trans ?_ hM.le)
      exact one_div_le_one_div_of_le (by positivity) (by
        have : (M : ℝ) ≤ N := by exact_mod_cast not_lt.1 hN
        linarith)
  · -- the cozero sets are small
    by_cases hx : x = 0
    · obtain ⟨N, hN⟩ := exists_nat_one_div_lt hε
      refine ⟨Sum.inr N, ?_, fun y hy => ?_⟩
      · rw [hfr, hx, smul_zero, hχ1 0 (by simpa using hδ), mul_one]
        positivity
      · rw [hfr] at hy
        have h1 := hχ0 _ (right_ne_zero_of_mul hy)
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity)] at h1
        have h2 : ‖y‖ < 1 / ((N : ℝ) + 1) := by
          rw [lt_div_iff₀ (by positivity)]; linarith
        simp only [id, hx, dist_zero_right]
        linarith
    · obtain ⟨N, hN⟩ := exists_nat_one_div_lt (by positivity : 0 < ε / 3)
      obtain ⟨i, hΔ, hQ⟩ := hP2 x hx (δ / ((N : ℝ) + 1)) (by positivity)
      obtain ⟨m, hm⟩ := exists_nat_ge (1 / ‖Δ i x‖)
      obtain ⟨j, hj0, hjs⟩ := (hg i).2.2.2 x (ε / 3) (by positivity)
      have hΔpos : 0 < ‖Δ i x‖ := norm_pos_iff.2 hΔ
      refine ⟨Sum.inl (⟨i, j⟩, m, N), ?_, fun y hy => ?_⟩
      · rw [hfl]
        refine mul_ne_zero (hcoef m N).ne' (mul_ne_zero (mul_ne_zero ?_ ?_) hj0)
        · rw [hψ1]
          · exact one_ne_zero
          rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity)]
          rw [div_le_iff₀ hΔpos] at hm
          nlinarith
        · rw [hχ1]
          · exact one_ne_zero
          rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity)]
          rw [lt_div_iff₀ (by positivity)] at hQ
          linarith
      · rw [hfl] at hy
        have hy1 := right_ne_zero_of_mul hy
        have hχy : χ (((N : ℝ) + 1) • (y - Q i y)) ≠ 0 :=
          right_ne_zero_of_mul (left_ne_zero_of_mul hy1)
        have hgy : g i j y ≠ 0 := right_ne_zero_of_mul hy1
        have h1 := hχ0 _ hχy
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity)] at h1
        have h2 : ‖y - Q i y‖ < 1 / ((N : ℝ) + 1) := by
          rw [lt_div_iff₀ (by positivity)]; linarith
        have h3 : dist (Q i y) (Q i x) < ε / 3 := hjs y hgy
        have h4 : ‖x - Q i x‖ < 1 / ((N : ℝ) + 1) := hQ.trans_le
          (div_le_div_of_nonneg_right hδ1 (by positivity))
        rw [dist_eq_norm] at h3
        simp only [id, dist_eq_norm]
        calc ‖y - x‖ = ‖(y - Q i y) + (Q i y - Q i x) - (x - Q i x)‖ := by congr 1; abel
          _ ≤ ‖y - Q i y‖ + ‖Q i y - Q i x‖ + ‖x - Q i x‖ := norm_sub_le_of_le
              (norm_add_le _ _) le_rfl
          _ < ε := by linarith

end Glue

end Polyfold
