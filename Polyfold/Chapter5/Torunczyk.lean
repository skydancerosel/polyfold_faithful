import Polyfold.Chapter5.PartitionsOfUnity

/-!
# Toruńczyk's theorem (2021 Theorem 5.5.13)

2021 Theorem 5.5.13, p. 234 (preprint Theorem 5.40), cited from Toruńczyk: a Banach space `E`
admits `C^k` partitions of unity if and only if there are a set `Γ` and a coordinate-wise `C^k`
homeomorphic embedding of `E` into `c₀(Γ)`.  The project states it as `TorunczykStatement`; here it
is proved (`theorem_5_5_13`).

## (⇒)

For each `n`, a `C^k` partition of unity `(ρₙ,c)_{c ∈ E}` subordinate to the balls `B(c, 1/(n+1))`.
Then `h(x) = (ρₙ,c(x)/(n+1))_{(n, c)}` lies in `c₀(ℕ × E)` (local finiteness and the weights
`1/(n+1)`), is continuous (only finitely many `n` matter up to `ε`, and for each the family is
locally finite), and is an embedding: if `h(y)` is close to `h(x)` then `ρₙ,c(y) > 0` for a `c`
with `ρₙ,c(x) > 0`, so `y ∈ B(c, 1/(n+1))` together with `x`.

## (⇐)

Through `C^k` Urysohn functions (then Mathlib's bump coverings, `BumpCovering.toPartitionOfUnity`).
For a finitely supported `σ : Γ →₀ ℤ` and `n`, the lattice bump
`bₙ,σ(x) = ∏ᶠ_γ θ((n+1) h(x)(γ) − σ(γ))`, `θ = 1` on `[−1/2, 1/2]` and `θ > 0` exactly on
`(−3/5, 3/5)`, is locally a finite product (`h(x) ∈ c₀`), hence `C^k`; it is `1` at `x` for
`σ = round((n+1)h(x))`, and for fixed `n` the family `(bₙ,σ)_σ` is locally finite.  Keeping the
bumps whose support lies on one side of the two closed sets, the Michael-type products
`gₙ,σ = bₙ,σ ∏_{m<n} η((n+1)Fₘ)`, `Fₘ = Σ_σ bₘ,σ`, form a locally finite family with `Σ g > 0`,
and `Σ_{side 1} g / Σ g` is the Urysohn function.
-/

open Set Function Filter Topology Metric
open scoped ENNReal

noncomputable section

namespace Polyfold

universe u

/-! ### Facts on `c₀(Γ)` -/

section CZeroFacts

variable {Γ : Type*}

/-- The `γ`-th coordinate of an element of `c₀(Γ)`. -/
abbrev cz (a : cZero Γ) (γ : Γ) : ℝ := (a : lp (fun _ : Γ => ℝ) ∞) γ

lemma abs_cz_sub_le (a b : cZero Γ) (γ : Γ) : |cz a γ - cz b γ| ≤ ‖a - b‖ := by
  have := lp.norm_apply_le_norm (p := ∞) ENNReal.top_ne_zero
    ((a - b : cZero Γ) : lp (fun _ : Γ => ℝ) ∞) γ
  simpa [cz, Real.norm_eq_abs] using this

lemma abs_cz_le (a : cZero Γ) (γ : Γ) : |cz a γ| ≤ ‖a‖ := by
  have := lp.norm_apply_le_norm (p := ∞) ENNReal.top_ne_zero (a : lp (fun _ : Γ => ℝ) ∞) γ
  simpa [cz, Real.norm_eq_abs] using this

lemma norm_sub_le_of_forall {a b : cZero Γ} {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ γ, |cz a γ - cz b γ| ≤ C) : ‖a - b‖ ≤ C := by
  have := lp.norm_le_of_forall_le hC (f := ((a - b : cZero Γ) : lp (fun _ : Γ => ℝ) ∞))
    fun γ => by simpa [cz, Real.norm_eq_abs] using h γ
  simpa using this

lemma continuous_cz (γ : Γ) : Continuous fun a : cZero Γ => cz a γ :=
  LipschitzWith.continuous (K := 1) (LipschitzWith.of_dist_le_mul fun a b => by
    rw [Real.dist_eq, dist_eq_norm, NNReal.coe_one, one_mul]
    exact abs_cz_sub_le a b γ)

lemma finite_cz_gt (a : cZero Γ) {ε : ℝ} (hε : 0 < ε) : {γ | ε < |cz a γ|}.Finite :=
  mem_cZero_iff.1 a.2 ε hε

end CZeroFacts

/-! ### Generic tools -/

section Tools

variable {V : Type u} [NormedAddCommGroup V] [NormedSpace ℝ V] {k : ℕ∞}

/-- A locally finite sum of `C^k` functions is `C^k`. -/
lemma contDiff_finsum_of_locallyFinite {ι : Type*} {f : ι → V → ℝ} (hf : ∀ i, ContDiff ℝ k (f i))
    (hlf : ∀ x, ∃ W ∈ 𝓝 x, {i | ∃ y ∈ W, f i y ≠ 0}.Finite) :
    ContDiff ℝ k fun x => ∑ᶠ i, f i x := by
  classical
  refine contDiff_iff_contDiffAt.2 fun x => ?_
  obtain ⟨W, hW, hfin⟩ := hlf x
  have hloc : ContDiffAt ℝ k (fun y => ∑ i ∈ hfin.toFinset, f i y) x :=
    (ContDiff.sum fun i _ => hf i).contDiffAt
  refine hloc.congr_of_eventuallyEq ?_
  filter_upwards [hW] with y hy
  refine finsum_eq_sum_of_support_subset _ fun i hi => ?_
  rw [Set.Finite.coe_toFinset]
  exact ⟨y, hy, hi⟩

/-- **`C^k` Urysohn functions give `C^k` partitions of unity** (Mathlib's bump coverings and
`ρᵢ = fᵢ ∏_{j < i}(1 − fⱼ)`). -/
theorem admitsContDiffPartitionsOfUnity_of_urysohn
    (hU : ∀ s t : Set V, IsClosed s → IsClosed t → Disjoint s t →
      ∃ F : V → ℝ, ContDiff ℝ k F ∧ EqOn F 0 s ∧ EqOn F 1 t ∧ ∀ x, F x ∈ Icc (0 : ℝ) 1) :
    AdmitsContDiffPartitionsOfUnity V k := by
  classical
  intro ι U hUo hUcov
  obtain ⟨b, hbp, hbsub⟩ := BumpCovering.exists_isSubordinate_of_prop
    (fun g : V → ℝ => ContDiff ℝ k g) (fun s t hs ht hst => by
      obtain ⟨F, hF, hF0, hF1, hF01⟩ := hU s t hs ht hst
      exact ⟨⟨F, hF.continuous⟩, hF, hF0, hF1, hF01⟩)
    isClosed_univ U hUo (by rw [hUcov])
  refine ⟨b.toPartitionOfUnity, hbsub.toPartitionOfUnity, fun i => ?_⟩
  refine contDiff_iff_contDiffAt.2 fun x => ?_
  obtain ⟨T, hT⟩ := b.exists_finset_toPartitionOfUnity_eventuallyEq i x
  refine ContDiffAt.congr_of_eventuallyEq ?_ hT
  have h1 : (⇑(b i) * ⇑(∏ j ∈ T with WellOrderingRel j i, (1 - b j))) =
      fun y => b i y * ∏ j ∈ T with WellOrderingRel j i, (1 - b j y) := by
    funext y
    simp [ContinuousMap.coe_prod, Finset.prod_apply]
  rw [h1]
  exact ((hbp i).mul (contDiff_prod fun j _ => contDiff_const.sub (hbp j))).contDiffAt

end Tools

/-! ### (⇒): an embedding from partitions of unity -/

section Forward

variable {V : Type u} [NormedAddCommGroup V] [NormedSpace ℝ V] {k : ℕ∞}

/-- **Theorem 5.5.13, (⇒)**: `C^k` partitions of unity give a coordinate-wise `C^k` homeomorphic
embedding into `c₀(ℕ × V)`. -/
theorem torunczyk_forward (hP : AdmitsContDiffPartitionsOfUnity V k) :
    ∃ (Γ : Type u) (h : V → cZero Γ), IsCoordinatewiseContDiffEmbedding k h := by
  classical
  have hex : ∀ n : ℕ, ∃ ρ : PartitionOfUnity V V,
      ρ.IsSubordinate (fun c => ball c (1 / ((n : ℝ) + 1))) ∧ ∀ c, ContDiff ℝ k (ρ c) :=
    fun n => hP V (fun c => ball c (1 / ((n : ℝ) + 1))) (fun c => isOpen_ball)
      (eq_univ_of_forall fun x => mem_iUnion.2 ⟨x, mem_ball_self (by positivity)⟩)
  choose ρ hρsub hρc using hex
  set H₀ : V → ℕ × V → ℝ := fun x γ => ρ γ.1 γ.2 x / ((γ.1 : ℝ) + 1) with hH₀
  have hH₀0 : ∀ x γ, 0 ≤ H₀ x γ := fun x γ => div_nonneg ((ρ γ.1).nonneg γ.2 x) (by positivity)
  have hH₀1 : ∀ x γ, H₀ x γ ≤ 1 := fun x γ => by
    rw [hH₀, div_le_one (by positivity)]
    have := (ρ γ.1).le_one γ.2 x
    have : (0 : ℝ) ≤ γ.1 := Nat.cast_nonneg _
    linarith
  have hmem : ∀ x, Memℓp (H₀ x) ∞ := fun x => memℓp_infty ⟨1, by
    rintro _ ⟨γ, rfl⟩
    show ‖H₀ x γ‖ ≤ 1
    rw [Real.norm_eq_abs, abs_of_nonneg (hH₀0 x γ)]
    exact hH₀1 x γ⟩
  set H₁ : V → lp (fun _ : ℕ × V => ℝ) ∞ := fun x => ⟨H₀ x, hmem x⟩ with hH₁
  have hc0 : ∀ x, H₁ x ∈ cZero (ℕ × V) := by
    intro x
    rw [mem_cZero_iff]
    intro ε hε
    obtain ⟨N, hN⟩ := exists_nat_gt (1 / ε)
    refine ((Finset.range N).finite_toSet.biUnion fun n _ =>
      (Set.finite_singleton n).prod ((ρ n).locallyFinite.point_finite x)).subset ?_
    rintro ⟨n, c⟩ hγ
    have hγ' : ε < H₀ x (n, c) := by
      have := hγ
      change ε < |H₀ x (n, c)| at this
      rwa [abs_of_nonneg (hH₀0 x _)] at this
    have hρpos : ρ n c x ≠ 0 := by
      intro h0
      simp only [hH₀, h0, zero_div] at hγ'
      linarith
    have hnN : n < N := by
      by_contra hn
      push Not at hn
      have h1 : H₀ x (n, c) ≤ 1 / ((n : ℝ) + 1) := by
        simp only [hH₀]
        exact div_le_div_of_nonneg_right ((ρ n).le_one c x) (by positivity)
      have h2 : 1 / ((n : ℝ) + 1) ≤ ε := by
        rw [div_le_iff₀ (by positivity)]
        have : (N : ℝ) ≤ n := by exact_mod_cast hn
        rw [div_lt_iff₀ hε] at hN
        nlinarith
      linarith
    exact mem_iUnion₂.2 ⟨n, by simpa using hnN, rfl, hρpos⟩
  set H : V → cZero (ℕ × V) := fun x => ⟨H₁ x, hc0 x⟩ with hH
  have hcz : ∀ x γ, cz (H x) γ = H₀ x γ := fun x γ => rfl
  -- continuity
  have hcont : Continuous H := by
    rw [continuous_iff_continuousAt]
    intro x
    rw [ContinuousAt, Metric.tendsto_nhds]
    intro ε hε
    obtain ⟨N, hN⟩ := exists_nat_one_div_lt (half_pos hε)
    have hlf : ∀ n, ∃ t ∈ 𝓝 x, {c | (support (ρ n c) ∩ t).Nonempty}.Finite :=
      fun n => (ρ n).locallyFinite x
    choose t ht htfin using hlf
    have hev : ∀ᶠ y in 𝓝 x, ∀ n ∈ Finset.range N, y ∈ t n ∧
        ∀ c ∈ (htfin n).toFinset, |ρ n c y - ρ n c x| < ε / 2 := by
      rw [Finset.eventually_all]
      intro n _
      refine (Filter.eventually_mem_set.2 (ht n)).and ?_
      rw [Finset.eventually_all]
      intro c _
      have := ((ρ n c).continuous.tendsto x)
      rw [Metric.tendsto_nhds] at this
      filter_upwards [this (ε / 2) (half_pos hε)] with y hy
      rwa [Real.dist_eq] at hy
    filter_upwards [hev] with y hy
    rw [dist_eq_norm]
    refine lt_of_le_of_lt (norm_sub_le_of_forall (half_pos hε).le fun γ => ?_) (half_lt_self hε)
    obtain ⟨n, c⟩ := γ
    rw [hcz, hcz]
    simp only [hH₀]
    rw [← sub_div, abs_div, abs_of_pos (by positivity : (0 : ℝ) < (n : ℝ) + 1)]
    have hdiff : |ρ n c y - ρ n c x| ≤ 1 := by
      rw [abs_le]
      constructor <;> linarith [(ρ n).nonneg c x, (ρ n).nonneg c y, (ρ n).le_one c x,
        (ρ n).le_one c y]
    by_cases hn : n < N
    · have hyn := hy n (Finset.mem_range.2 hn)
      by_cases hc : c ∈ (htfin n).toFinset
      · refine (div_le_self (abs_nonneg _) (by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)])).trans
          (hyn.2 c hc).le
      · have hxt : x ∈ t n := mem_of_mem_nhds (ht n)
        have h0 : ∀ z ∈ t n, ρ n c z = 0 := fun z hz => by
          by_contra hne
          exact hc ((htfin n).mem_toFinset.2 ⟨z, hne, hz⟩)
        rw [h0 y hyn.1, h0 x hxt, sub_self, abs_zero, zero_div]
        exact (half_pos hε).le
    · push Not at hn
      calc |ρ n c y - ρ n c x| / ((n : ℝ) + 1) ≤ 1 / ((n : ℝ) + 1) :=
            div_le_div_of_nonneg_right hdiff (by positivity)
        _ ≤ 1 / ((N : ℝ) + 1) := by
            gcongr
        _ ≤ ε / 2 := hN.le
  -- the inverse is continuous
  have hind : Topology.IsInducing H := by
    rw [Topology.isInducing_iff_nhds]
    intro x
    refine le_antisymm (tendsto_iff_comap.1 (hcont.tendsto x)) ?_
    intro U hU
    obtain ⟨r, hr, hrU⟩ := Metric.mem_nhds_iff.1 hU
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt (half_pos hr)
    obtain ⟨c, hc⟩ : ∃ c, ρ n c x ≠ 0 := by
      by_contra hall
      push Not at hall
      have := (ρ n).sum_eq_one (Set.mem_univ x)
      rw [finsum_eq_zero_of_forall_eq_zero hall] at this
      exact zero_ne_one this
    have hcpos : 0 < ρ n c x := lt_of_le_of_ne ((ρ n).nonneg c x) (Ne.symm hc)
    refine Filter.mem_comap.2 ⟨ball (H x) (ρ n c x / ((n : ℝ) + 1)),
      ball_mem_nhds _ (by positivity), fun y hy => hrU ?_⟩
    have hy' : |cz (H y) (n, c) - cz (H x) (n, c)| < ρ n c x / ((n : ℝ) + 1) :=
      lt_of_le_of_lt (abs_cz_sub_le _ _ _) (by rwa [mem_preimage, mem_ball, dist_eq_norm] at hy)
    rw [hcz, hcz] at hy'
    simp only [hH₀] at hy'
    rw [← sub_div, abs_div, abs_of_pos (by positivity : (0 : ℝ) < (n : ℝ) + 1),
      div_lt_div_iff_of_pos_right (by positivity)] at hy'
    have hypos : ρ n c y ≠ 0 := by
      intro h0
      rw [h0, zero_sub, abs_neg, abs_of_pos hcpos] at hy'
      exact lt_irrefl _ hy'
    have hyc : y ∈ ball c (1 / ((n : ℝ) + 1)) := hρsub n c (subset_closure hypos)
    have hxc : x ∈ ball c (1 / ((n : ℝ) + 1)) := hρsub n c (subset_closure hc)
    rw [mem_ball] at hyc hxc ⊢
    calc dist y x ≤ dist y c + dist x c := dist_triangle_right y x c
      _ < 1 / ((n : ℝ) + 1) + 1 / ((n : ℝ) + 1) := add_lt_add hyc hxc
      _ < r / 2 + r / 2 := add_lt_add hn hn
      _ = r := add_halves r
  refine ⟨ℕ × V, H, ⟨hind, hind.injective⟩, fun γ => ?_⟩
  exact (hρc γ.1 γ.2).div_const _

end Forward

/-! ### (⇐): partitions of unity from an embedding -/

section Backward

variable {V : Type u} [NormedAddCommGroup V] [NormedSpace ℝ V] {k : ℕ∞} {Γ : Type u}

/-- The bump `θ`: `θ = 1` on `[−1/2, 1/2]`, `θ > 0` exactly on `(−3/5, 3/5)`. -/
def thetaB : ContDiffBump (0 : ℝ) := ⟨1 / 2, 3 / 5, by norm_num, by norm_num⟩

/-- The cut-off `η`: `η = 1` on `[−1/2, 1/2]`, `η = 0` off `(−1, 1)`. -/
def etaB : ContDiffBump (0 : ℝ) := ⟨1 / 2, 1, by norm_num, by norm_num⟩

lemma thetaB_one {t : ℝ} (ht : |t| ≤ 1 / 2) : thetaB t = 1 :=
  thetaB.one_of_mem_closedBall (by rw [mem_closedBall, Real.dist_eq, sub_zero]; exact ht)

lemma abs_lt_of_thetaB_ne_zero {t : ℝ} (ht : thetaB t ≠ 0) : |t| < 3 / 5 := by
  have : t ∈ support (thetaB : ℝ → ℝ) := ht
  rw [thetaB.support_eq, mem_ball, Real.dist_eq, sub_zero] at this
  exact this

lemma etaB_zero {t : ℝ} (ht : 1 ≤ t) : etaB t = 0 := by
  by_contra hne
  have : t ∈ support (etaB : ℝ → ℝ) := hne
  rw [etaB.support_eq, mem_ball, Real.dist_eq, sub_zero] at this
  have : |t| < 1 := this
  rw [abs_lt] at this
  linarith

lemma etaB_at_zero : etaB 0 = 1 := etaB.one_of_mem_closedBall (by simp; norm_num [etaB])

variable (h : V → cZero Γ)

/-- The lattice bump `bₙ,σ(x) = ∏ᶠ_γ θ((n+1) h(x)(γ) − σ(γ))`. -/
def latticeBump (n : ℕ) (σ : Γ →₀ ℤ) (x : V) : ℝ :=
  ∏ᶠ γ, thetaB (((n : ℝ) + 1) * cz (h x) γ - σ γ)

variable {h}

omit [NormedAddCommGroup V] [NormedSpace ℝ V] in
/-- Near `x` the lattice bump is a product over a fixed finite set. -/
lemma latticeBump_mulSupport_subset (n : ℕ) (σ : Γ →₀ ℤ) (x y : V)
    (hy : ‖h y - h x‖ < 1 / (4 * ((n : ℝ) + 1))) :
    mulSupport (fun γ => thetaB (((n : ℝ) + 1) * cz (h y) γ - σ γ)) ⊆
      ↑σ.support ∪ {γ | 1 / (4 * ((n : ℝ) + 1)) < |cz (h x) γ|} := by
  intro γ hγ
  by_contra hnot
  simp only [mem_union, Finset.mem_coe, Finsupp.mem_support_iff, ne_eq, not_or, not_not,
    mem_ofPred_eq, not_lt] at hnot
  apply hγ
  refine thetaB_one ?_
  rw [hnot.1, Int.cast_zero, sub_zero, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < (n : ℝ) + 1)]
  have h1 := abs_cz_sub_le (h y) (h x) γ
  have h2 : |cz (h y) γ| ≤ 1 / (2 * ((n : ℝ) + 1)) := by
    have := abs_sub_abs_le_abs_sub (cz (h y) γ) (cz (h x) γ)
    have h4 : 1 / (4 * ((n : ℝ) + 1)) + 1 / (4 * ((n : ℝ) + 1)) = 1 / (2 * ((n : ℝ) + 1)) := by
      field_simp; ring
    linarith
  calc ((n : ℝ) + 1) * |cz (h y) γ| ≤ ((n : ℝ) + 1) * (1 / (2 * ((n : ℝ) + 1))) := by gcongr
    _ = 1 / 2 := by field_simp

omit [NormedAddCommGroup V] [NormedSpace ℝ V] in
lemma finite_latticeSet (n : ℕ) (σ : Γ →₀ ℤ) (x : V) :
    (↑σ.support ∪ {γ | 1 / (4 * ((n : ℝ) + 1)) < |cz (h x) γ|}).Finite :=
  σ.support.finite_toSet.union (finite_cz_gt _ (by positivity))

omit [NormedAddCommGroup V] [NormedSpace ℝ V] in
lemma latticeBump_eq_prod (n : ℕ) (σ : Γ →₀ ℤ) (x y : V)
    (hy : ‖h y - h x‖ < 1 / (4 * ((n : ℝ) + 1))) :
    latticeBump h n σ y = ∏ γ ∈ (finite_latticeSet (h := h) n σ x).toFinset,
      thetaB (((n : ℝ) + 1) * cz (h y) γ - σ γ) := by
  refine finprod_eq_prod_of_mulSupport_subset _ ?_
  rw [Set.Finite.coe_toFinset]
  exact latticeBump_mulSupport_subset n σ x y hy

omit [NormedAddCommGroup V] [NormedSpace ℝ V] in
lemma latticeBump_mem_Icc (n : ℕ) (σ : Γ →₀ ℤ) (x : V) : latticeBump h n σ x ∈ Icc (0 : ℝ) 1 := by
  rw [latticeBump_eq_prod n σ x x (by simp; positivity)]
  exact ⟨Finset.prod_nonneg fun γ _ => thetaB.nonneg,
    Finset.prod_le_one (fun γ _ => thetaB.nonneg) fun γ _ => thetaB.le_one⟩

omit [NormedAddCommGroup V] [NormedSpace ℝ V] in
lemma latticeBump_eq_one (n : ℕ) (σ : Γ →₀ ℤ) (x : V)
    (hx : ∀ γ, |((n : ℝ) + 1) * cz (h x) γ - σ γ| ≤ 1 / 2) : latticeBump h n σ x = 1 :=
  finprod_eq_one_of_forall_eq_one fun γ => thetaB_one (hx γ)

omit [NormedAddCommGroup V] [NormedSpace ℝ V] in
lemma abs_lt_of_latticeBump_ne_zero {n : ℕ} {σ : Γ →₀ ℤ} {x : V} (hx : latticeBump h n σ x ≠ 0)
    (γ : Γ) : |((n : ℝ) + 1) * cz (h x) γ - σ γ| < 3 / 5 := by
  refine abs_lt_of_thetaB_ne_zero fun h0 => hx ?_
  refine finprod_eq_zero _ γ h0 ?_
  exact (finite_latticeSet (h := h) n σ x).subset
    (latticeBump_mulSupport_subset n σ x x (by simp; positivity))

variable (hcoord : ∀ γ, ContDiff ℝ k fun e => cz (h e) γ) (hcont : Continuous h)
include hcoord hcont

lemma contDiff_latticeBump (n : ℕ) (σ : Γ →₀ ℤ) : ContDiff ℝ k (latticeBump h n σ) := by
  refine contDiff_iff_contDiffAt.2 fun x => ?_
  have hloc : ContDiffAt ℝ k (fun y => ∏ γ ∈ (finite_latticeSet (h := h) n σ x).toFinset,
      thetaB (((n : ℝ) + 1) * cz (h y) γ - σ γ)) x :=
    (contDiff_prod fun γ _ => thetaB.contDiff.comp
      ((contDiff_const.mul (hcoord γ)).sub contDiff_const)).contDiffAt
  refine hloc.congr_of_eventuallyEq ?_
  have hW : {y | ‖h y - h x‖ < 1 / (4 * ((n : ℝ) + 1))} ∈ 𝓝 x :=
    (isOpen_lt (continuous_norm.comp (hcont.sub continuous_const)) continuous_const).mem_nhds
      (by simp; positivity)
  filter_upwards [hW] with y hy
  exact latticeBump_eq_prod n σ x y hy

omit hcoord [NormedSpace ℝ V] in
/-- The support of `bₙ,σ` lies in `{y | ∀ γ, |(n+1)h(y)(γ) − σ(γ)| ≤ 3/5}`. -/
lemma tsupport_latticeBump_subset (n : ℕ) (σ : Γ →₀ ℤ) :
    tsupport (latticeBump h n σ) ⊆ {y | ∀ γ, |((n : ℝ) + 1) * cz (h y) γ - σ γ| ≤ 3 / 5} := by
  refine closure_minimal (fun y hy γ => (abs_lt_of_latticeBump_ne_zero hy γ).le) ?_
  have : {y : V | ∀ γ, |((n : ℝ) + 1) * cz (h y) γ - σ γ| ≤ 3 / 5} =
      ⋂ γ, {y | |((n : ℝ) + 1) * cz (h y) γ - σ γ| ≤ 3 / 5} := by ext; simp
  rw [this]
  refine isClosed_iInter fun γ => isClosed_le ?_ continuous_const
  have hc : Continuous fun y : V => cz (h y) γ := (continuous_cz γ).comp hcont
  exact continuous_abs.comp ((continuous_const.mul hc).sub continuous_const)

omit hcoord [NormedSpace ℝ V] in
/-- **Local finiteness** of `(bₙ,σ)_σ` for fixed `n`. -/
lemma locallyFinite_latticeBump (n : ℕ) (x : V) :
    ∃ W ∈ 𝓝 x, {σ : Γ →₀ ℤ | ∃ y ∈ W, latticeBump h n σ y ≠ 0}.Finite := by
  classical
  set s : ℝ := (n : ℝ) + 1 with hs
  have hs0 : 0 < s := by positivity
  refine ⟨{y | ‖h y - h x‖ < 1 / (10 * s)},
    (isOpen_lt (continuous_norm.comp (hcont.sub continuous_const)) continuous_const).mem_nhds
      (by simp; positivity), ?_⟩
  set A := {γ | 1 / (5 * s) < |cz (h x) γ|} with hA
  have hAfin : A.Finite := finite_cz_gt _ (by positivity)
  set M : ℤ := ⌈s * ‖h x‖⌉ + 1 with hM
  have key : ∀ σ : Γ →₀ ℤ, (∃ y ∈ {y | ‖h y - h x‖ < 1 / (10 * s)}, latticeBump h n σ y ≠ 0) →
      (∀ γ ∉ A, σ γ = 0) ∧ ∀ γ, σ γ ∈ Icc (-M) M := by
    rintro σ ⟨y, hy, hne⟩
    have hb : ∀ γ, |(σ γ : ℝ) - s * cz (h x) γ| < 7 / 10 := by
      intro γ
      have h1 : |s * cz (h y) γ - σ γ| < 3 / 5 := abs_lt_of_latticeBump_ne_zero hne γ
      have h2 : |s * cz (h y) γ - s * cz (h x) γ| < 1 / 10 := by
        rw [← mul_sub, abs_mul, abs_of_pos hs0]
        have := lt_of_le_of_lt (abs_cz_sub_le (h y) (h x) γ) hy
        rw [lt_div_iff₀ (by positivity)] at this
        nlinarith [abs_nonneg (cz (h y) γ - cz (h x) γ)]
      have := abs_sub_le (σ γ : ℝ) (s * cz (h y) γ) (s * cz (h x) γ)
      rw [abs_sub_comm (σ γ : ℝ) (s * cz (h y) γ)] at this
      linarith
    refine ⟨fun γ hγ => ?_, fun γ => ?_⟩
    · simp only [hA, mem_ofPred_eq, not_lt] at hγ
      have h1 : |s * cz (h x) γ| ≤ 1 / 5 := by
        rw [abs_mul, abs_of_pos hs0]
        calc s * |cz (h x) γ| ≤ s * (1 / (5 * s)) := by gcongr
          _ = 1 / 5 := by field_simp
      have h2 : |(σ γ : ℝ)| < 1 := by
        have := abs_sub_abs_le_abs_sub (σ γ : ℝ) (s * cz (h x) γ)
        linarith [hb γ]
      have : |σ γ| < 1 := by exact_mod_cast h2
      have := abs_lt.1 this
      omega
    · have h1 : |s * cz (h x) γ| ≤ s * ‖h x‖ := by
        rw [abs_mul, abs_of_pos hs0]; gcongr; exact abs_cz_le _ _
      have h2 : |(σ γ : ℝ)| < s * ‖h x‖ + 1 := by
        have := abs_sub_abs_le_abs_sub (σ γ : ℝ) (s * cz (h x) γ)
        linarith [hb γ]
      have h3 : s * ‖h x‖ ≤ (⌈s * ‖h x‖⌉ : ℝ) := Int.le_ceil _
      have h4 : |(σ γ : ℝ)| < (M : ℝ) := by rw [hM]; push_cast; linarith
      have h5 : |σ γ| < M := by exact_mod_cast h4
      rw [mem_Icc]; constructor <;> [linarith [neg_abs_le (σ γ)]; linarith [le_abs_self (σ γ)]]
  -- finitely many such `σ`
  have hfinA : Finite A := hAfin.to_subtype
  have himg : ((fun σ : Γ →₀ ℤ => fun a : A => σ a) ''
      {σ | (∀ γ ∉ A, σ γ = 0) ∧ ∀ γ, σ γ ∈ Icc (-M) M}).Finite := by
    refine (Set.Finite.pi (t := fun _ : A => Icc (-M) M) fun _ => Set.finite_Icc _ _).subset ?_
    rintro _ ⟨σ, hσ, rfl⟩
    exact Set.mem_univ_pi.2 fun a => hσ.2 a
  have hinj : Set.InjOn (fun σ : Γ →₀ ℤ => fun a : A => σ a)
      {σ | (∀ γ ∉ A, σ γ = 0) ∧ ∀ γ, σ γ ∈ Icc (-M) M} := by
    intro σ hσ τ hτ heq
    ext γ
    by_cases hγ : γ ∈ A
    · exact congr_fun heq ⟨γ, hγ⟩
    · rw [hσ.1 γ hγ, hτ.1 γ hγ]
  exact (himg.of_finite_image hinj).subset fun σ hσ => key σ hσ

omit hcoord hcont [NormedAddCommGroup V] [NormedSpace ℝ V] in
/-- For each `x` and `n`, the bump of the rounded lattice point is `1` at `x`. -/
lemma exists_latticeBump_eq_one (n : ℕ) (x : V) :
    ∃ σ : Γ →₀ ℤ, (∀ γ, |((n : ℝ) + 1) * cz (h x) γ - σ γ| ≤ 1 / 2) := by
  classical
  set s : ℝ := (n : ℝ) + 1
  have hfin : (support fun γ => round (s * cz (h x) γ)).Finite := by
    refine (finite_cz_gt (h x) (ε := 1 / (4 * s)) (by positivity)).subset fun γ hγ => ?_
    by_contra hle
    simp only [mem_ofPred_eq, not_lt] at hle
    apply hγ
    rw [round_eq_zero_iff]
    have hs0 : (0 : ℝ) < s := by positivity
    have : |s * cz (h x) γ| ≤ 1 / 4 := by
      rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < s)]
      calc s * |cz (h x) γ| ≤ s * (1 / (4 * s)) := by gcongr
        _ = 1 / 4 := by field_simp
    rw [abs_le] at this
    constructor <;> linarith
  refine ⟨Finsupp.ofSupportFinite _ hfin, fun γ => ?_⟩
  rw [Finsupp.ofSupportFinite_coe]
  have := abs_sub_round (s * cz (h x) γ)
  exact this

omit hcoord [NormedSpace ℝ V] in
/-- The support of the bump of a lattice point near `h(x)` lies in a small `h`-ball around `x`. -/
lemma tsupport_latticeBump_subset_ball (n : ℕ) (σ : Γ →₀ ℤ) (x : V)
    (hx : ∀ γ, |((n : ℝ) + 1) * cz (h x) γ - σ γ| ≤ 1 / 2) :
    tsupport (latticeBump h n σ) ⊆ {y | ‖h y - h x‖ ≤ 2 / ((n : ℝ) + 1)} := by
  refine (tsupport_latticeBump_subset hcont n σ).trans fun y hy => ?_
  refine norm_sub_le_of_forall (by positivity) fun γ => ?_
  have h1 := hy γ
  have h2 := hx γ
  have h3 : |((n : ℝ) + 1) * (cz (h y) γ - cz (h x) γ)| ≤ 11 / 10 := by
    rw [mul_sub]
    calc |((n : ℝ) + 1) * cz (h y) γ - ((n : ℝ) + 1) * cz (h x) γ|
        ≤ |((n : ℝ) + 1) * cz (h y) γ - σ γ| + |((n : ℝ) + 1) * cz (h x) γ - σ γ| := by
          have := abs_sub_le (((n : ℝ) + 1) * cz (h y) γ) (σ γ : ℝ) (((n : ℝ) + 1) * cz (h x) γ)
          rwa [abs_sub_comm (σ γ : ℝ)] at this
      _ ≤ 11 / 10 := by linarith
  rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < (n : ℝ) + 1)] at h3
  rw [le_div_iff₀ (by positivity)]
  nlinarith

end Backward

section BackwardUrysohn

variable {V : Type u} [NormedAddCommGroup V] [NormedSpace ℝ V] {k : ℕ∞} {Γ : Type u}
  {h : V → cZero Γ}

set_option maxHeartbeats 1600000 in
-- one construction: the good bumps, the Michael products and the Urysohn quotient
/-- **`C^k` Urysohn functions from a coordinate-wise `C^k` embedding into `c₀(Γ)`.** -/
theorem exists_contDiff_urysohn_of_embedding (hemb : IsCoordinatewiseContDiffEmbedding k h)
    {s t : Set V} (hs : IsClosed s) (ht : IsClosed t) (hst : Disjoint s t) :
    ∃ F : V → ℝ, ContDiff ℝ k F ∧ EqOn F 0 s ∧ EqOn F 1 t ∧ ∀ x, F x ∈ Icc (0 : ℝ) 1 := by
  classical
  have hcont : Continuous h := hemb.1.continuous
  have hcoord : ∀ γ, ContDiff ℝ k fun e => cz (h e) γ := hemb.2
  set b := latticeBump h
  -- good bumps: support on one side
  set good1 : ℕ → (Γ →₀ ℤ) → Prop := fun n σ => tsupport (b n σ) ⊆ sᶜ
  set good2 : ℕ → (Γ →₀ ℤ) → Prop := fun n σ => tsupport (b n σ) ⊆ tᶜ
  set B : ℕ → (Γ →₀ ℤ) → V → ℝ := fun n σ x => if good1 n σ ∨ good2 n σ then b n σ x else 0
  have hBc : ∀ n σ, ContDiff ℝ k (B n σ) := fun n σ => by
    by_cases hg : good1 n σ ∨ good2 n σ
    · simp only [B, if_pos hg]; exact contDiff_latticeBump hcoord hcont n σ
    · simp only [B, if_neg hg]; exact contDiff_const
  have hB01 : ∀ n σ x, B n σ x ∈ Icc (0 : ℝ) 1 := fun n σ x => by
    by_cases hg : good1 n σ ∨ good2 n σ
    · simp only [B, if_pos hg]; exact latticeBump_mem_Icc n σ x
    · simp only [B, if_neg hg]; exact ⟨le_rfl, zero_le_one⟩
  have hBle : ∀ n σ x, B n σ x ≠ 0 → b n σ x ≠ 0 := fun n σ x hne => by
    by_cases hg : good1 n σ ∨ good2 n σ
    · simpa only [B, if_pos hg] using hne
    · simp only [B, if_neg hg] at hne; exact absurd rfl hne
  have hBlf : ∀ n x, ∃ W ∈ 𝓝 x, {σ | ∃ y ∈ W, B n σ y ≠ 0}.Finite := fun n x => by
    obtain ⟨W, hW, hfin⟩ := locallyFinite_latticeBump hcont (h := h) n x
    exact ⟨W, hW, hfin.subset fun σ ⟨y, hy, hne⟩ => ⟨y, hy, hBle n σ y hne⟩⟩
  -- `Fₘ = Σ_σ Bₘ,σ`
  set Fm : ℕ → V → ℝ := fun m x => ∑ᶠ σ, B m σ x
  have hFmc : ∀ m, ContDiff ℝ k (Fm m) := fun m =>
    contDiff_finsum_of_locallyFinite (hBc m) (hBlf m)
  have hFm0 : ∀ m x, 0 ≤ Fm m x := fun m x => finsum_nonneg fun σ => (hB01 m σ x).1
  have hsuppfin : ∀ m x, (support fun σ => B m σ x).Finite := fun m x => by
    obtain ⟨W, hW, hfin⟩ := hBlf m x
    exact hfin.subset fun σ hσ => ⟨x, mem_of_mem_nhds hW, hσ⟩
  -- every point has a good bump equal to `1`
  have hgood : ∀ x, ∃ m σ, B m σ x = 1 := by
    intro x
    have hWo : ∃ W, IsOpen W ∧ x ∈ W ∧ (W ⊆ sᶜ ∨ W ⊆ tᶜ) := by
      by_cases hxs : x ∈ s
      · exact ⟨tᶜ, ht.isOpen_compl, fun hxt => Set.disjoint_left.1 hst hxs hxt, Or.inr le_rfl⟩
      · exact ⟨sᶜ, hs.isOpen_compl, hxs, Or.inl le_rfl⟩
    obtain ⟨W, hWo, hxW, hside⟩ := hWo
    have hWn : W ∈ 𝓝 x := hWo.mem_nhds hxW
    rw [hemb.1.isInducing.nhds_eq_comap x, Filter.mem_comap] at hWn
    obtain ⟨T, hT, hTW⟩ := hWn
    obtain ⟨r, hr, hrT⟩ := Metric.mem_nhds_iff.1 hT
    obtain ⟨m, hm⟩ := exists_nat_one_div_lt (half_pos hr)
    obtain ⟨σ, hσ⟩ := exists_latticeBump_eq_one (h := h) m x
    have hsub : tsupport (b m σ) ⊆ W := by
      refine (tsupport_latticeBump_subset_ball hcont m σ x hσ).trans fun y hy => hTW (hrT ?_)
      rw [mem_ball, dist_eq_norm]
      refine lt_of_le_of_lt hy ?_
      have : 2 / ((m : ℝ) + 1) = 2 * (1 / ((m : ℝ) + 1)) := by ring
      rw [this]; linarith
    refine ⟨m, σ, ?_⟩
    have hg : good1 m σ ∨ good2 m σ := hside.imp (fun h' => hsub.trans h') fun h' => hsub.trans h'
    simp only [B, if_pos hg]
    exact latticeBump_eq_one m σ x hσ
  -- the Michael products
  set g : ℕ × (Γ →₀ ℤ) → V → ℝ := fun p x =>
    B p.1 p.2 x * ∏ m ∈ Finset.range p.1, etaB (((p.1 : ℝ) + 1) * Fm m x)
  have hgc : ∀ p, ContDiff ℝ k (g p) := fun p =>
    (hBc p.1 p.2).mul (contDiff_prod fun m _ => etaB.contDiff.comp (contDiff_const.mul (hFmc m)))
  have hg0 : ∀ p x, 0 ≤ g p x := fun p x =>
    mul_nonneg (hB01 p.1 p.2 x).1 (Finset.prod_nonneg fun m _ => etaB.nonneg)
  have hglf : ∀ x, ∃ W ∈ 𝓝 x, {p | ∃ y ∈ W, g p y ≠ 0}.Finite := by
    intro x
    obtain ⟨m, σ, hmσ⟩ := hgood x
    have hFx : 1 ≤ Fm m x := by
      have := single_le_finsum σ (hsuppfin m x) fun τ => (hB01 m τ x).1
      rwa [hmσ] at this
    have hev : ∀ᶠ y in 𝓝 x, 1 / 2 < Fm m y :=
      ((hFmc m).continuous.tendsto x).eventually (lt_mem_nhds (by linarith))
    choose W hW hWfin using fun n => hBlf n x
    refine ⟨{y | 1 / 2 < Fm m y} ∩ ⋂ n ∈ Finset.range (m + 1), W n, ?_, ?_⟩
    · exact inter_mem hev ((Finset.range (m + 1)).iInter_mem_sets.2 fun n _ => hW n)
    · refine ((Finset.range (m + 1)).finite_toSet.biUnion fun n _ =>
        (Set.finite_singleton n).prod (hWfin n)).subset ?_
      rintro ⟨n, τ⟩ ⟨y, ⟨hy1, hy2⟩, hne⟩
      have hnm : n ≤ m := by
        by_contra hnm
        push Not at hnm
        apply hne
        have h1n : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (Nat.one_le_of_lt hnm)
        have hy1' : 1 / 2 < Fm m y := hy1
        have hη : etaB (((n : ℝ) + 1) * Fm m y) = 0 := etaB_zero (by nlinarith [hFm0 m y])
        simp only [g]
        rw [Finset.prod_eq_zero (Finset.mem_range.2 hnm) hη, mul_zero]
      have hBne : B n τ y ≠ 0 := fun h0 => hne (by simp only [g, h0, zero_mul])
      refine mem_iUnion₂.2 ⟨n, by simpa [Nat.lt_succ_iff] using hnm, rfl, ?_⟩
      exact ⟨y, mem_iInter₂.1 hy2 n (by simpa [Nat.lt_succ_iff] using hnm), hBne⟩
  have hgsuppfin : ∀ x, (support fun p => g p x).Finite := fun x => by
    obtain ⟨W, hW, hfin⟩ := hglf x
    exact hfin.subset fun p hp => ⟨x, mem_of_mem_nhds hW, hp⟩
  -- the side weights
  set c : ℕ × (Γ →₀ ℤ) → ℝ := fun p => if good1 p.1 p.2 then 1 else 0
  set S : V → ℝ := fun x => ∑ᶠ p, g p x
  set N : V → ℝ := fun x => ∑ᶠ p, c p * g p x
  have hSc : ContDiff ℝ k S := contDiff_finsum_of_locallyFinite hgc hglf
  have hNc : ContDiff ℝ k N := by
    refine contDiff_finsum_of_locallyFinite (fun p => contDiff_const.mul (hgc p)) fun x => ?_
    obtain ⟨W, hW, hfin⟩ := hglf x
    exact ⟨W, hW, hfin.subset fun p ⟨y, hy, hne⟩ =>
      ⟨y, hy, fun h0 => hne (by simp only [h0, mul_zero])⟩⟩
  -- `S > 0`
  have hSpos : ∀ x, 0 < S x := by
    intro x
    have hex : ∃ n, ∃ σ, B n σ x ≠ 0 := by
      obtain ⟨m, σ, hmσ⟩ := hgood x
      exact ⟨m, σ, by rw [hmσ]; exact one_ne_zero⟩
    obtain ⟨σ, hσ⟩ := Nat.find_spec hex
    set n := Nat.find hex
    have hlow : ∀ m < n, Fm m x = 0 := fun m hm =>
      finsum_eq_zero_of_forall_eq_zero fun τ => by
        by_contra hne
        exact Nat.find_min hex hm ⟨τ, hne⟩
    have hgpos : 0 < g (n, σ) x := by
      simp only [g]
      rw [Finset.prod_eq_one fun m hm => by
        rw [hlow m (Finset.mem_range.1 hm), mul_zero, etaB_at_zero], mul_one]
      exact lt_of_le_of_ne (hB01 n σ x).1 (Ne.symm hσ)
    exact lt_of_lt_of_le hgpos (single_le_finsum (n, σ) (hgsuppfin x) fun p => hg0 p x)
  have hc01 : ∀ p, 0 ≤ c p ∧ c p ≤ 1 := fun p => by
    simp only [c]; split_ifs <;> norm_num
  refine ⟨fun x => N x / S x, hNc.div hSc fun x => (hSpos x).ne', fun x hx => ?_,
    fun x hx => ?_, fun x => ?_⟩
  · -- on `s`
    simp only [Pi.zero_apply]
    have : N x = 0 := by
      refine finsum_eq_zero_of_forall_eq_zero fun p => ?_
      by_cases h1 : good1 p.1 p.2
      · have hb0 : b p.1 p.2 x = 0 := image_eq_zero_of_notMem_tsupport fun hx' => h1 hx' hx
        have hB0 : B p.1 p.2 x = 0 := by
          by_contra hne; exact hBle _ _ _ hne hb0
        simp only [g, hB0, zero_mul, mul_zero]
      · simp only [c, if_neg h1, zero_mul]
    rw [this, zero_div]
  · -- on `t`
    simp only [Pi.one_apply]
    have : N x = S x := by
      refine finsum_congr fun p => ?_
      by_cases h1 : good1 p.1 p.2
      · simp only [c, if_pos h1, one_mul]
      · simp only [c, if_neg h1, zero_mul]
        by_cases h2 : good2 p.1 p.2
        · have hb0 : b p.1 p.2 x = 0 := image_eq_zero_of_notMem_tsupport fun hx' => h2 hx' hx
          have hB0 : B p.1 p.2 x = 0 := by
            by_contra hne; exact hBle _ _ _ hne hb0
          simp only [g, hB0, zero_mul]
        · have hB0 : B p.1 p.2 x = 0 := by simp only [B, if_neg (not_or.2 ⟨h1, h2⟩)]
          simp only [g, hB0, zero_mul]
    rw [this, div_self (hSpos x).ne']
  · -- values in `[0, 1]`
    have hN0 : 0 ≤ N x := finsum_nonneg fun p => mul_nonneg (hc01 p).1 (hg0 p x)
    have hNS : N x ≤ S x := by
      refine finsum_le_finsum' ?_ (hgsuppfin x) fun p => ?_
      · exact (hgsuppfin x).subset fun p hp => fun h0 => hp (by simp only [h0, mul_zero])
      · exact mul_le_of_le_one_left (hg0 p x) (hc01 p).2
    exact ⟨div_nonneg hN0 (hSpos x).le, (div_le_one (hSpos x)).2 hNS⟩

/-- **Theorem 5.5.13, (⇐)**: a coordinate-wise `C^k` homeomorphic embedding into `c₀(Γ)` gives
`C^k` partitions of unity. -/
theorem torunczyk_backward (hemb : IsCoordinatewiseContDiffEmbedding k h) :
    AdmitsContDiffPartitionsOfUnity V k :=
  admitsContDiffPartitionsOfUnity_of_urysohn fun _ _ hs ht hst =>
    exists_contDiff_urysohn_of_embedding hemb hs ht hst

end BackwardUrysohn

/-- **2021 Theorem 5.5.13, p. 234 (preprint 5.40), Toruńczyk**: a Banach space `V` admits `C^k`
partitions of unity if and only if there are a set `Γ` and a coordinate-wise `C^k` homeomorphic
embedding of `V` into `c₀(Γ)`. -/
theorem theorem_5_5_13 (V : Type u) [NormedAddCommGroup V] [NormedSpace ℝ V] (k : ℕ∞) :
    TorunczykStatement V k :=
  ⟨torunczyk_forward, fun ⟨_, _, hemb⟩ => torunczyk_backward hemb⟩

end Polyfold
