import Polyfold.Chapter5.AllowableSectionsMetric

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), §5.3, after Lemma 5.3.3
(preprint p. 174): the metric space `(Γ^{+,1}_U(P), ρ)` of allowable sections "is not complete"
(comparison item V5.21, point G.42).

# When `(Γ^{+,1}_U(P), ρ)` is complete, for the trivial bundles `ℝⁿ × ℝᵏ → ℝⁿ`

`AllowableSectionsMetric.lean` proves non-completeness for one bundle (`ℝ × ℝ → ℝ`, `U = ℝ`) and
completeness in two degenerate cases (`U = ∅`; `X` a point).  Here the example is generalized to
every trivial bundle `ℝⁿ × ℝᵏ → ℝⁿ` with the fibre norm `N(x, v) = |v|` and every `U`, and the
complete cases are characterized:

* `TrivialBundle.not_completeSpace_allowableSections_of_mem_interior`: if `n ≥ 1`, `k ≥ 1` and `U`
  has an interior point `a`, then `(Γ^{+,1}_U(P), ρ)` is not complete.  The Cauchy sequence is
  `s_j(x) = (x, χ(x) √(t² + 1/(j+1)²) w(t) e₁)` with `t = x₁ − a₁`, `χ` a smooth bump at `a` with
  support in `U` and `w(t) = 1/(2√(1 + t²))`; its uniform limit has fibre part
  `χ(x) |x₁ − a₁| w(x₁ − a₁) e₁`, not differentiable at `a`.
* `TrivialBundle.completeSpace_allowableSections_iff`: `(Γ^{+,1}_U(P), ρ)` is complete if and only
  if `n = 0`, `k = 0` or `U` has empty interior.  In the last two cases it is the single point `0`
  (`TrivialBundle.subsingleton_allowableSections_of_interior_eq_empty`,
  `TrivialBundle.subsingleton_allowableSections_fibre_zero`); for `n = 0` it is a closed ball of
  `ℝᵏ` or `{0}`.

So, for these bundles, "not complete" holds exactly when `U` contains a non-isolated point (every
point of `ℝⁿ`, `n ≥ 1`) in its interior and the fibre is nonzero.  For an open `U` (the text's
setting) the condition is `U ≠ ∅`, `n ≥ 1`, `k ≥ 1`.  The general strong bundle over an M-polyfold
is not treated: the construction uses a bump function and the coordinate `x₁` of `ℝⁿ`.
-/

open Set Filter Topology Function
open scoped ContDiff

noncomputable section

namespace Polyfold

namespace TrivialBundle

variable {n k : ℕ}

/-- The zero of the fibre over `x` is `(x, 0)`. -/
lemma fiberZero_eq (x : Fin n → ℝ) : fiberZero (proj n k) x = (x, 0) :=
  Prod.ext (fst_fiber _) (snd_zero x)

/-- A section of the trivial bundle is `x ↦ (x, (s x).2)`. -/
lemma section_fst {s : (Fin n → ℝ) → (Fin n → ℝ) × (Fin k → ℝ)} (hs : IsSection (proj n k) s)
    (x : Fin n → ℝ) : (s x).1 = x := hs x

/-- `√(t² + ε²) w(t) ≤ 1/2` for `0 ≤ ε ≤ 1`. -/
lemma sqrt_mul_wt_le_half (t : ℝ) {ε : ℝ} (hε1 : ε ≤ 1) (hε0 : 0 ≤ ε) :
    √(t ^ 2 + ε ^ 2) * wt t ≤ 1 / 2 := by
  have h1 : √(t ^ 2 + ε ^ 2) ≤ √(1 + t ^ 2) := Real.sqrt_le_sqrt (by nlinarith)
  rw [← wt_mul_sqrt t, mul_comm (wt t)]
  exact mul_le_mul_of_nonneg_right h1 (wt_pos _).le

/-! ### The complete cases -/

/-- **If `U` has empty interior, the only allowable section is the zero section**: the set where an
sc⁺-section of the trivial bundle is nonzero is open (its fibre part is differentiable,
`differentiable_snd_of_isScPlusSection`) and lies in `supp(s) ⊆ U`. -/
theorem subsingleton_allowableSections_of_interior_eq_empty {U : Set (Fin n → ℝ)}
    (hU : interior U = ∅) : Subsingleton ((bundle n k).allowableSections fibNorm U) := by
  have hz : ∀ t : (bundle n k).allowableSections fibNorm U, ∀ x,
      (t : (Fin n → ℝ) → (Fin n → ℝ) × (Fin k → ℝ)) x = (x, 0) := by
    intro t x
    by_contra hx
    set σ := (t : (Fin n → ℝ) → (Fin n → ℝ) × (Fin k → ℝ))
    have hσ1 : ∀ y, (σ y).1 = y := section_fst t.2.1.1
    have hx2 : (σ x).2 ≠ 0 := fun h => hx (Prod.ext (hσ1 x) h)
    have hcont : Continuous fun y => (σ y).2 :=
      (differentiable_snd_of_isScPlusSection t.2.1).continuous
    have hV : IsOpen {y | (σ y).2 ≠ 0} := isOpen_ne_fun hcont continuous_const
    have hVU : {y | (σ y).2 ≠ 0} ⊆ U := by
      intro y hy
      refine t.2.2.1 (subset_closure ?_)
      change σ y ≠ fiberZero (proj n k) y
      rw [fiberZero_eq]
      exact fun h => hy (congrArg Prod.snd h)
    have := interior_maximal hVU hV
    rw [hU] at this
    exact this hx2
  exact ⟨fun s s' => Subtype.ext (funext fun x => by rw [hz s, hz s'])⟩

/-- **With fibre `ℝ⁰` the only allowable section is the zero section.** -/
theorem subsingleton_allowableSections_fibre_zero (U : Set (Fin n → ℝ)) :
    Subsingleton ((bundle n 0).allowableSections fibNorm U) := by
  refine ⟨fun s s' => Subtype.ext (funext fun x => Prod.ext ?_ (Subsingleton.elim _ _))⟩
  rw [section_fst s.2.1.1, section_fst s'.2.1.1]

/-- A metric space with at most one point is complete. -/
lemma completeSpace_of_subsingleton' {α : Type*} [MetricSpace α] (h : Subsingleton α) :
    CompleteSpace α := by
  refine Metric.complete_of_cauchySeq_tendsto fun u _ => ⟨u 0, ?_⟩
  have : u = fun _ => u 0 := funext fun j => Subsingleton.elim _ _
  rw [this]; exact tendsto_const_nhds

/-! ### The incomplete case -/

section Incomplete

variable {a : Fin n → ℝ} (χ : ContDiffBump a) (i : Fin n) (l : Fin k)

lemma norm_single_le : ‖(Pi.single l (1 : ℝ) : Fin k → ℝ)‖ ≤ 1 := by
  refine (pi_norm_le_iff_of_nonneg zero_le_one).2 fun l' => ?_
  by_cases h : l' = l
  · subst h; simp
  · rw [Pi.single_eq_of_ne h]; simp

/-- The coordinate `t(x) = x_i − a_i`. -/
def tc (a : Fin n → ℝ) (i : Fin n) (x : Fin n → ℝ) : ℝ := x i - a i

lemma contDiff_tc : ContDiff ℝ ∞ (tc a i) :=
  (contDiff_apply ℝ ℝ i).sub contDiff_const

/-- The scalar parts `c_j(x) = χ(x) √(t² + ε_j²) w(t)`. -/
def cj (j : ℕ) (x : Fin n → ℝ) : ℝ :=
  χ x * (√(tc a i x ^ 2 + eps j ^ 2) * wt (tc a i x))

/-- The limit `c(x) = χ(x) |t| w(t)`. -/
def cl (x : Fin n → ℝ) : ℝ := χ x * (|tc a i x| * wt (tc a i x))

lemma contDiff_cj (j : ℕ) : ContDiff ℝ ∞ (cj χ i j) := by
  refine ContDiff.mul χ.contDiff (ContDiff.mul ?_ (contDiff_wt.comp (contDiff_tc (a := a) i)))
  refine ((contDiff_tc (a := a) i).pow 2).add contDiff_const |>.sqrt fun x => ?_
  have := eps_pos j; positivity

lemma abs_cj_le (j : ℕ) (x : Fin n → ℝ) : |cj χ i j x| ≤ 1 / 2 := by
  unfold cj
  rw [abs_mul, abs_of_nonneg χ.nonneg,
    abs_of_nonneg (mul_nonneg (Real.sqrt_nonneg _) (wt_pos _).le)]
  calc χ x * (√(tc a i x ^ 2 + eps j ^ 2) * wt (tc a i x)) ≤ 1 * (1 / 2) :=
        mul_le_mul χ.le_one (sqrt_mul_wt_le_half _ (eps_le_one j) (eps_pos j).le)
          (mul_nonneg (Real.sqrt_nonneg _) (wt_pos _).le) zero_le_one
    _ = 1 / 2 := one_mul _

lemma abs_cj_sub_cl (j : ℕ) (x : Fin n → ℝ) : |cj χ i j x - cl χ i x| ≤ eps j / 2 := by
  unfold cj cl
  rw [← mul_sub, ← sub_mul, abs_mul, abs_mul, abs_of_nonneg χ.nonneg, abs_of_pos (wt_pos _)]
  calc χ x * (abs (√(tc a i x ^ 2 + eps j ^ 2) - |tc a i x|) * wt (tc a i x))
      ≤ 1 * (eps j * (1 / 2)) :=
        mul_le_mul χ.le_one (mul_le_mul (abs_sqrt_sub_abs_le _ (eps_pos j).le) (wt_le_half _)
          (wt_pos _).le (eps_pos j).le) (mul_nonneg (abs_nonneg _) (wt_pos _).le) zero_le_one
    _ = eps j / 2 := by ring

/-- The fibre parts `φ_j(x) = c_j(x) e_l`. -/
def φj (j : ℕ) (x : Fin n → ℝ) : Fin k → ℝ := cj χ i j x • (Pi.single l (1 : ℝ) : Fin k → ℝ)

lemma φj_apply_self (j : ℕ) (x : Fin n → ℝ) : φj χ i l j x l = cj χ i j x := by
  unfold φj; rw [Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one]

lemma norm_φj_le (j : ℕ) (x : Fin n → ℝ) : ‖φj χ i l j x‖ ≤ 1 / 2 := by
  unfold φj
  rw [norm_smul, Real.norm_eq_abs]
  calc |cj χ i j x| * ‖(Pi.single l (1 : ℝ) : Fin k → ℝ)‖ ≤ 1 / 2 * 1 :=
        mul_le_mul (abs_cj_le χ i j x) (norm_single_le l) (norm_nonneg _) (by norm_num)
    _ = 1 / 2 := mul_one _

lemma norm_φj_sub_le (j j' : ℕ) (x : Fin n → ℝ) :
    ‖φj χ i l j x - φj χ i l j' x‖ ≤ (eps j + eps j') / 2 := by
  unfold φj
  rw [← sub_smul, norm_smul, Real.norm_eq_abs]
  have h : |cj χ i j x - cj χ i j' x| ≤ (eps j + eps j') / 2 := by
    calc |cj χ i j x - cj χ i j' x|
        ≤ |cj χ i j x - cl χ i x| + |cj χ i j' x - cl χ i x| := by
          rw [abs_sub_comm (cj χ i j' x)]; exact abs_sub_le _ _ _
      _ ≤ eps j / 2 + eps j' / 2 := add_le_add (abs_cj_sub_cl χ i j x) (abs_cj_sub_cl χ i j' x)
      _ = (eps j + eps j') / 2 := by ring
  have hpos : 0 ≤ (eps j + eps j') / 2 := by have := eps_pos j; have := eps_pos j'; positivity
  calc |cj χ i j x - cj χ i j' x| * ‖(Pi.single l (1 : ℝ) : Fin k → ℝ)‖
      ≤ (eps j + eps j') / 2 * 1 := mul_le_mul h (norm_single_le l) (norm_nonneg _) hpos
    _ = (eps j + eps j') / 2 := mul_one _

variable {χ} {U : Set (Fin n → ℝ)}

/-- The sections `s_j = (x, φ_j(x))` are allowable when `supp χ ⊆ U`. -/
lemma graphSection_φj_mem (hχU : tsupport χ ⊆ U) (j : ℕ) :
    graphSection (φj χ i l j) ∈ (bundle n k).allowableSections fibNorm U := by
  refine ⟨isScPlusSection_graphSection ((contDiff_cj χ i j).smul contDiff_const), ?_,
    fun x _ => ?_⟩
  · refine (closure_mono fun x hx => ?_).trans hχU
    by_contra h0
    have h0' : χ x = 0 := by rwa [Function.mem_support, not_not] at h0
    apply hx
    change (x, φj χ i l j x) = fiberZero (proj n k) x
    rw [fiberZero_eq]
    unfold φj cj
    rw [h0', zero_mul, zero_smul]
  · change ‖φj χ i l j x‖ ≤ 1
    linarith [norm_φj_le χ i l j x]

/-- `τ ↦ |τ| q(τ)` is not differentiable at `0` when `q` is differentiable at `0` with
`q(0) ≠ 0`. -/
lemma not_differentiableAt_abs_mul {q : ℝ → ℝ} (hq : DifferentiableAt ℝ q 0) (hq0 : q 0 ≠ 0) :
    ¬ DifferentiableAt ℝ (fun τ => |τ| * q τ) 0 := by
  intro h
  have h2 : DifferentiableAt ℝ (fun τ => |τ| * q τ / q τ) 0 := h.div hq hq0
  have hev : (fun τ => |τ| * q τ / q τ) =ᶠ[𝓝 0] abs := by
    filter_upwards [hq.continuousAt.eventually_ne hq0] with τ hτ
    rw [mul_div_assoc, div_self hτ, mul_one]
  exact not_differentiableAt_abs_zero (h2.congr_of_eventuallyEq hev.symm)

end Incomplete

/-- **`(Γ^{+,1}_U(P), ρ)` is not complete** (§5.3, after Lemma 5.3.3; comparison item V5.21, point
G.42) for the trivial bundle `ℝⁿ × ℝᵏ → ℝⁿ` (`n, k ≥ 1`) with the fibre norm, whenever `U` has an
interior point `a`: the allowable sections `s_j(x) = (x, χ(x) √(t² + 1/(j+1)²) w(t) e₁)`,
`t = x₁ − a₁`, form a `ρ`-Cauchy sequence whose limit would have fibre part
`χ(x) |x₁ − a₁| w(x₁ − a₁) e₁`, not differentiable at `a`, while sc⁺-sections have differentiable
fibre parts. -/
theorem not_completeSpace_allowableSections_of_mem_interior (hn : 0 < n) (hk : 0 < k)
    {U : Set (Fin n → ℝ)} {a : Fin n → ℝ} (ha : a ∈ interior U) :
    ¬ CompleteSpace (StrongBundle.AllowableSpace (B := bundle n k) U isAuxNorm_fibNorm) := by
  intro hc
  obtain ⟨ε, hε, hεU⟩ := Metric.mem_nhds_iff.1 (mem_interior_iff_mem_nhds.1 ha)
  let χ : ContDiffBump a := ⟨ε / 4, ε / 2, by positivity, by linarith⟩
  have hχU : tsupport χ ⊆ U := by
    rw [χ.tsupport_eq]
    exact (Metric.closedBall_subset_ball (by change ε / 2 < ε; linarith)).trans hεU
  have hχa : χ a = 1 := χ.one_of_mem_closedBall (Metric.mem_closedBall_self χ.rIn_pos.le)
  let i : Fin n := ⟨0, hn⟩
  let l : Fin k := ⟨0, hk⟩
  let S : ℕ → StrongBundle.AllowableSpace (B := bundle n k) U isAuxNorm_fibNorm := fun j =>
    StrongBundle.AllowableSpace.mk _ ⟨graphSection (φj χ i l j), graphSection_φj_mem i l hχU j⟩
  have hdist : ∀ i' j, dist (S i') (S j) ≤ (eps i' + eps j) / 2 := fun i' j => by
    rw [StrongBundle.AllowableSpace.dist_eq]
    refine Real.iSup_le (fun x => ?_) (by have := eps_pos i'; have := eps_pos j; positivity)
    rw [sectionDistAt_fibNorm]
    exact norm_φj_sub_le χ i l i' j x
  have heps : Tendsto eps atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hS : CauchySeq S := by
    refine Metric.cauchySeq_iff'.2 fun δ hδ => ?_
    obtain ⟨N₀, hN₀⟩ := eventually_atTop.1 (heps.eventually (gt_mem_nhds (half_pos hδ)))
    refine ⟨N₀, fun j hj => ?_⟩
    have h1 := hN₀ j hj
    have h2 := hN₀ N₀ le_rfl
    linarith [hdist j N₀]
  obtain ⟨s, hs⟩ := cauchySeq_tendsto_of_complete hS
  have hd : Tendsto (fun j => dist (S j) s) atTop (𝓝 0) := tendsto_iff_dist_tendsto_zero.1 hs
  set σ : (Fin n → ℝ) → (Fin n → ℝ) × (Fin k → ℝ) := s.sec.1 with hσ
  -- the `e₁`-coordinate of the fibre part of the limit is `c`
  have hval : ∀ x, (σ x).2 l = cl χ i x := by
    intro x
    have h1 : Tendsto (fun j => cj χ i j x) atTop (𝓝 ((σ x).2 l)) := by
      refine tendsto_iff_norm_sub_tendsto_zero.2 (squeeze_zero (fun _ => norm_nonneg _)
        (fun j => ?_) hd)
      have := StrongBundle.sectionDistAt_le_allowableDist isAuxNorm_fibNorm (S j).sec s.sec x
      rw [sectionDistAt_fibNorm] at this
      rw [StrongBundle.AllowableSpace.dist_eq]
      refine le_trans ?_ this
      have h3 := norm_le_pi_norm (φj χ i l j x - (σ x).2) l
      rw [Pi.sub_apply, φj_apply_self] at h3
      exact h3
    have h2 : Tendsto (fun j => cj χ i j x) atTop (𝓝 (cl χ i x)) := by
      have h3 : Tendsto (fun j => eps j / 2) atTop (𝓝 0) := by
        simpa using heps.div_const 2
      refine tendsto_iff_norm_sub_tendsto_zero.2 (squeeze_zero (fun _ => norm_nonneg _)
        (fun j => ?_) h3)
      rw [Real.norm_eq_abs]; exact abs_cj_sub_cl χ i j x
    exact tendsto_nhds_unique h1 h2
  have hdiff : Differentiable ℝ fun x => (σ x).2 := differentiable_snd_of_isScPlusSection s.sec.2.1
  -- along the line `τ ↦ a + τ e_{i₀}`
  let γ : ℝ → Fin n → ℝ := fun τ => a + τ • Pi.single i 1
  have hγ : Differentiable ℝ γ := (differentiable_id.smul_const _).const_add a
  have htγ : ∀ τ, tc a i (γ τ) = τ := fun τ => by
    simp [tc, γ]
  have hγ0 : γ 0 = a := by simp [γ]
  have h0 : DifferentiableAt ℝ (fun τ : ℝ => (σ (γ τ)).2 l) 0 :=
    ((differentiable_apply (𝕜 := ℝ) (F' := fun _ : Fin k => ℝ) l).comp (hdiff.comp hγ)) 0
  have h3 : (fun τ : ℝ => (σ (γ τ)).2 l) = fun τ => |τ| * (χ (γ τ) * wt τ) :=
    funext fun τ => by rw [hval, cl, htγ]; ring
  rw [h3] at h0
  refine not_differentiableAt_abs_mul (q := fun τ => χ (γ τ) * wt τ) ?_ ?_ h0
  · exact (((χ.contDiff (n := 1)).differentiable one_ne_zero).comp hγ 0).mul
      ((contDiff_wt.differentiable (by simp)) 0)
  · simp only [hγ0, hχa, one_mul]; exact (wt_pos 0).ne'

/-- **When `(Γ^{+,1}_U(P), ρ)` is complete, for the trivial bundles** (§5.3, after Lemma 5.3.3;
comparison item V5.21, point G.42): for `ℝⁿ × ℝᵏ → ℝⁿ` with the fibre norm, the metric space of
allowable sections is complete if and only if `n = 0` (`X` a point), `k = 0` (zero fibre), or `U`
has empty interior.  For an open `U`: it is not complete exactly when `U ≠ ∅`, `n ≥ 1`, `k ≥ 1`. -/
theorem completeSpace_allowableSections_iff (U : Set (Fin n → ℝ)) :
    CompleteSpace (StrongBundle.AllowableSpace (B := bundle n k) U isAuxNorm_fibNorm) ↔
      n = 0 ∨ k = 0 ∨ interior U = ∅ := by
  constructor
  · intro hc
    by_contra h
    push Not at h
    obtain ⟨hn, hk, hU⟩ := h
    obtain ⟨a, ha⟩ := hU
    exact not_completeSpace_allowableSections_of_mem_interior (Nat.pos_of_ne_zero hn)
      (Nat.pos_of_ne_zero hk) ha hc
  · rintro (hn | hk | hU)
    · subst hn; exact completeSpace_allowableSections_point U
    · subst hk
      exact completeSpace_of_subsingleton' (subsingleton_allowableSections_fibre_zero U)
    · exact completeSpace_of_subsingleton' (subsingleton_allowableSections_of_interior_eq_empty hU)

end TrivialBundle

end Polyfold
