import Polyfold.Basic

/-!
Infrastructure for Hofer–Wysocki–Zehnder, Part I, §1.4.1 (the proof of Proposition 1.10), which
opens with "Since `S : E_m → F_m` is compact for every level, the operator `T + S : E_m → F_m` is
Fredholm for every `m`" — the classical stability of Fredholm operators under compact
perturbations, which Mathlib (v4.33.1) does not have.

# Compact perturbations of Fredholm operators between Banach spaces

## What is formalized

For real Banach spaces `E`, `F`:

* `Polyfold.isStrictMap_of_isClosed_range`: a continuous linear map with
  closed range is a strict map (the open mapping theorem).
* `Polyfold.isFredholm_of_banach`: a continuous linear map with
  finite-dimensional kernel, closed range and range of finite codimension is Fredholm in the sense
  of Mathlib's `ContinuousLinearMap.IsFredholm` (the other two conditions, strictness and
  complementedness of the kernel, are automatic over `ℝ`).
* `Polyfold.isCompactOperator_of_finiteDimensional_range`: finite-rank operators are compact.
* **Riesz–Schauder**: for a compact `c : E →L[ℝ] E`, `1 + c` has finite-dimensional kernel
  (`finiteDimensional_ker_one_add`), closed range (`isClosed_range_one_add`) and range of finite
  codimension (`coFG_range_one_add`); hence it is Fredholm (`isFredholm_one_add`).
* `Polyfold.isFredholm_add_isCompactOperator`: if `u` is Fredholm and `k` is
  compact then `u + k` is Fredholm.

## Proofs

* Finite-dimensional kernel: on `N = ker(1 + c)` the compact operator `c` is `−id`, so `id_N` is
  compact and `N` is finite-dimensional.
* Closed range: on a closed complement `G` of `N`, `1 + c` is bounded below (otherwise unit
  vectors `g_n ∈ G` with `(1+c)g_n → 0` have `c g_n` converging along a subsequence, so `g_n`
  converges to a unit vector of `G ∩ N`), and a bounded-below operator on a Banach space has
  closed range; `(1 + c)(G) = (1 + c)(E)`.
* Finite codimension: if `R = (1 + c)(E)` had infinite codimension there would be closed subspaces
  `R = M₀ ⊊ M₁ ⊊ …` (each `M_{j+1} = M_j + ℝ x_j`) and, by Riesz's lemma, unit vectors
  `u_j ∈ M_{j+1}` at distance `≥ 1/2` from `M_j`; then `‖c u_l − c u_j‖ ≥ 1/2` for `j < l`
  (`c u_l − c u_j = u_l − (u_j + (1+c)u_l − (1+c)u_j)` with the bracket in `M_l`), contradicting
  the compactness of `c`.
* Perturbation: with a quasi-inverse `v` of `u` (`v u − 1`, `u v − 1` of finite rank),
  `v(u + k) = 1 + c₁` and `(u + k)v = 1 + c₂` with `c₁`, `c₂` compact, so `ker(u + k)` is
  contained in the finite-dimensional `ker(1 + c₁)` and `range(u + k)` contains the closed,
  finite-codimensional `range(1 + c₂)`, hence is closed and of finite codimension.
-/

open Set Filter Topology Function Metric

noncomputable section

namespace Polyfold

open ContinuousLinearMap

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-! ### Fredholm operators between Banach spaces -/

/-- The open mapping theorem: a continuous linear map between Banach spaces with closed range is a
strict map (induces a homeomorphism `E/ker u ≃ range u`). -/
theorem isStrictMap_of_isClosed_range (u : E →L[ℝ] F)
    (h : IsClosed (u.range : Set F)) : IsStrictMap u := by
  have : CompleteSpace u.range := h.completeSpace_coe
  rw [show (⇑u : E → F) = ⇑(u : E →ₗ[ℝ] F) from rfl,
    LinearMap.isStrictMap_iff_isOpenQuotientMap_rangeRestrict]
  refine ⟨LinearMap.surjective_rangeRestrict _, ?_, ?_⟩
  · exact (u.rangeRestrict).continuous
  · exact (u.rangeRestrict).isOpenMap (LinearMap.surjective_rangeRestrict _)

/-- Between Banach spaces, a continuous linear map with finite-dimensional kernel, closed range and
range of finite codimension is Fredholm. -/
theorem isFredholm_of_banach (u : E →L[ℝ] F)
    (hker : FiniteDimensional ℝ u.ker) (hrange : IsClosed (u.range : Set F))
    (hcoker : u.range.CoFG) : IsFredholm u where
  isStrictMap := isStrictMap_of_isClosed_range u hrange
  isClosed_range := hrange
  finite_ker := hker
  finite_coker := hcoker
  closedComplemented_ker := Submodule.ClosedComplemented.of_finiteDimensional _

omit [CompleteSpace E] [CompleteSpace F] in
/-- A finite-rank continuous linear map is compact. -/
theorem isCompactOperator_of_finiteDimensional_range (f : E →L[ℝ] F)
    [hf : FiniteDimensional ℝ f.range] : IsCompactOperator f := by
  have hbdd : Bornology.IsBounded (f.rangeRestrict '' closedBall (0 : E) 1) :=
    (f.rangeRestrict.lipschitz.isBounded_image isBounded_closedBall)
  have hK : IsCompact (closure (f.rangeRestrict '' closedBall (0 : E) 1)) :=
    Metric.isCompact_of_isClosed_isBounded isClosed_closure hbdd.closure
  refine ⟨Subtype.val '' closure (f.rangeRestrict '' closedBall (0 : E) 1),
    hK.image continuous_subtype_val, ?_⟩
  refine Filter.mem_of_superset (closedBall_mem_nhds (0 : E) zero_lt_one) fun x hx => ?_
  exact ⟨f.rangeRestrict x, subset_closure ⟨x, hx, rfl⟩, rfl⟩

/-! ### Riesz–Schauder: `1 + compact` is Fredholm -/

section RieszSchauder

variable {c : E →L[ℝ] E}

omit [CompleteSpace E] in
/-- The kernel of `1 + c`, `c` compact, is finite-dimensional. -/
theorem finiteDimensional_ker_one_add (hc : IsCompactOperator c) :
    FiniteDimensional ℝ (1 + c : E →L[ℝ] E).ker := by
  set N := (1 + c : E →L[ℝ] E).ker with hNdef
  have hN : ∀ v ∈ N, (c : E →ₗ[ℝ] E) v ∈ N := by
    intro v hv
    have hv' : v + c v = 0 := hv
    have : c v = -v := by rw [← neg_eq_of_add_eq_zero_right hv']
    have hv0 : (1 + c : E →L[ℝ] E) v = 0 := hv
    change (1 + c : E →L[ℝ] E) (c v) = 0
    rw [this, map_neg, hv0, neg_zero]
  have hcl : IsClosed (N : Set E) := (1 + c : E →L[ℝ] E).isClosed_ker
  have h1 : IsCompactOperator ((c : E →ₗ[ℝ] E).restrict hN) := hc.restrict hN hcl
  have h2 : ((c : E →ₗ[ℝ] E).restrict hN : N → N) = fun v => -v := by
    funext v
    apply Subtype.ext
    have hv' : (v : E) + c v = 0 := v.2
    change c v = -v
    rw [← neg_eq_of_add_eq_zero_right hv']
  rw [h2] at h1
  have h3 : IsCompactOperator (id : N → N) := by
    have := h1.neg
    have hid : (-fun v : N => -v) = id := by funext v; simp
    rwa [hid] at this
  exact FiniteDimensional.of_isCompactOperator_id h3

omit [CompleteSpace E] in
/-- `1 + c` is bounded below on a closed complement of its kernel. -/
private lemma exists_bound_below_on_compl (hc : IsCompactOperator c) {G : Submodule ℝ E}
    (hG : IsClosed (G : Set E))
    (hGN : Disjoint (1 + c : E →L[ℝ] E).ker G) :
    ∃ δ > 0, ∀ x ∈ G, δ * ‖x‖ ≤ ‖(1 + c : E →L[ℝ] E) x‖ := by
  by_contra hcon
  push Not at hcon
  -- unit vectors `u n ∈ G` with `‖(1 + c) (u n)‖ < 1/(n+1)`
  have hseq : ∀ n : ℕ, ∃ u : E, u ∈ G ∧ ‖u‖ = 1 ∧ ‖(1 + c : E →L[ℝ] E) u‖ < 1 / (n + 1) := by
    intro n
    obtain ⟨x, hxG, hx⟩ := hcon (1 / (n + 1)) (by positivity)
    have hx0 : x ≠ 0 := by
      rintro rfl
      simp at hx
    have hxn : 0 < ‖x‖ := norm_pos_iff.2 hx0
    refine ⟨‖x‖⁻¹ • x, G.smul_mem _ hxG, ?_, ?_⟩
    · rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hxn.ne']
    · rw [map_smul, norm_smul, norm_inv, norm_norm, ← div_eq_inv_mul, div_lt_iff₀ hxn]
      linarith
  choose u huG hu1 hu using hseq
  -- `c (u n)` lies in a compact set
  obtain ⟨K, hK, hKsub⟩ := hc.image_closedBall_subset_compact (f := (c : E →ₗ[ℝ] E)) 1
  have hmem : ∀ n, c (u n) ∈ K := fun n =>
    hKsub ⟨u n, by rw [mem_closedBall, dist_zero_right, hu1], rfl⟩
  obtain ⟨y, -, φ, hφ, hlim⟩ := hK.tendsto_subseq hmem
  -- `(1 + c) (u (φ n)) → 0`
  have hlim0 : Tendsto (fun n => (1 + c : E →L[ℝ] E) (u (φ n))) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have h1 : Tendsto (fun n : ℕ => (1 : ℝ) / ((φ n : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat.comp hφ.tendsto_atTop
    exact squeeze_zero (fun n => norm_nonneg _) (fun n => (hu (φ n)).le) h1
  -- hence `u (φ n) → -y`
  have hlimu : Tendsto (fun n => u (φ n)) atTop (𝓝 (-y)) := by
    have : (fun n => u (φ n)) = fun n => (1 + c : E →L[ℝ] E) (u (φ n)) - c (u (φ n)) := by
      funext n; simp
    rw [this]
    simpa using hlim0.sub hlim
  -- `-y ∈ G`, `‖-y‖ = 1`, `(1 + c) (-y) = 0`
  have hyG : -y ∈ G := hG.mem_of_tendsto hlimu (Eventually.of_forall fun n => huG (φ n))
  have hynorm : ‖-y‖ = 1 := by
    have := (continuous_norm.tendsto _).comp hlimu
    simp only [Function.comp_def, hu1] at this
    exact (tendsto_nhds_unique tendsto_const_nhds this).symm
  have hyN : -y ∈ (1 + c : E →L[ℝ] E).ker := by
    rw [LinearMap.mem_ker]
    have := ((1 + c : E →L[ℝ] E).continuous.tendsto _).comp hlimu
    exact tendsto_nhds_unique this hlim0
  have : -y = 0 := (Submodule.disjoint_def.1 hGN) _ hyN hyG
  rw [this, norm_zero] at hynorm
  exact zero_ne_one hynorm

/-- The range of `1 + c`, `c` compact, is closed. -/
theorem isClosed_range_one_add (hc : IsCompactOperator c) :
    IsClosed ((1 + c : E →L[ℝ] E).range : Set E) := by
  have := finiteDimensional_ker_one_add hc
  obtain ⟨G, hG, hGN⟩ := (Submodule.ClosedComplemented.of_finiteDimensional
    (1 + c : E →L[ℝ] E).ker).exists_isClosed_isCompl
  obtain ⟨δ, hδ, hbound⟩ := exists_bound_below_on_compl hc hG hGN.disjoint
  have : CompleteSpace G := hG.completeSpace_coe
  -- `(1 + c) ∘ subtype G` is bounded below, hence has closed range
  set f : G →L[ℝ] E := (1 + c : E →L[ℝ] E).comp G.subtypeL with hf
  have hanti : AntilipschitzWith ⟨δ⁻¹, by positivity⟩ f := by
    refine f.antilipschitz_of_bound fun x => ?_
    have := hbound x x.2
    change ‖(x : E)‖ ≤ δ⁻¹ * ‖(1 + c : E →L[ℝ] E) x‖
    rw [← div_eq_inv_mul, le_div_iff₀ hδ, mul_comm]
    exact this
  have hclosed : IsClosed (range f) := hanti.isClosed_range f.uniformContinuous
  have hrange : ((1 + c : E →L[ℝ] E).range : Set E) = range f := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      obtain ⟨n, hn, g, hg, rfl⟩ :=
        Submodule.mem_sup.1 (hGN.sup_eq_top ▸ Submodule.mem_top (x := x))
      refine ⟨⟨g, hg⟩, ?_⟩
      have hn' : (1 + c : E →L[ℝ] E) n = 0 := hn
      change (1 + c : E →L[ℝ] E) g = (1 + c : E →L[ℝ] E) (n + g)
      rw [map_add, hn', zero_add]
    · rintro ⟨g, rfl⟩
      exact ⟨g, rfl⟩
  rw [hrange]
  exact hclosed

omit [CompleteSpace E] in
/-- Riesz's lemma inside a subspace: for closed `M ⊊ M'` there is a unit vector of `M'` at distance
`≥ 1/2` from `M`. -/
private lemma exists_unit_far {M M' : Submodule ℝ E} (hM : IsClosed (M : Set E)) (hMM' : M ≤ M')
    {x : E} (hxM' : x ∈ M') (hxM : x ∉ M) :
    ∃ u ∈ M', ‖u‖ = 1 ∧ ∀ y ∈ M, 1 / 2 ≤ ‖u - y‖ := by
  have hne : (M : Set E).Nonempty := ⟨0, M.zero_mem⟩
  have hd : 0 < infDist x (M : Set E) := (hM.notMem_iff_infDist_pos hne).1 hxM
  obtain ⟨y, hy, hxy⟩ := (infDist_lt_iff hne).1 (show infDist x (M : Set E) < 2 * infDist x M by
    linarith)
  obtain ⟨z, hz⟩ : ∃ z, z = x - y := ⟨_, rfl⟩
  have hzM' : z ∈ M' := hz ▸ M'.sub_mem hxM' (hMM' hy)
  have hzfar : ∀ y' ∈ M, infDist x (M : Set E) ≤ ‖z - y'‖ := by
    intro y' hy'
    have := infDist_le_dist_of_mem (x := x) (M.add_mem hy hy')
    rw [dist_eq_norm, ← sub_sub, ← hz] at this
    exact this
  have hz0 : 0 < ‖z‖ := lt_of_lt_of_le hd (by simpa using hzfar 0 M.zero_mem)
  have hzlt : ‖z‖ < 2 * infDist x (M : Set E) := by rwa [hz, ← dist_eq_norm]
  refine ⟨‖z‖⁻¹ • z, M'.smul_mem _ hzM', ?_, fun y' hy' => ?_⟩
  · rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hz0.ne']
  · have h1 : ‖z‖⁻¹ • z - y' = ‖z‖⁻¹ • (z - ‖z‖ • y') := by
      rw [smul_sub, smul_smul, inv_mul_cancel₀ hz0.ne', one_smul]
    rw [h1, norm_smul, norm_inv, norm_norm, ← div_eq_inv_mul, le_div_iff₀ hz0]
    have h2 := hzfar (‖z‖ • y') (M.smul_mem _ hy')
    calc 1 / 2 * ‖z‖ ≤ 1 / 2 * (2 * infDist x (M : Set E)) := by gcongr
      _ = infDist x (M : Set E) := by ring
      _ ≤ ‖z - ‖z‖ • y'‖ := h2

open scoped Classical in
/-- A point outside a proper subspace (junk `0` for `⊤`). -/
private def pick (S : Submodule ℝ E) : E := if h : ∃ x, x ∉ S then h.choose else 0

omit [CompleteSpace E] in
private lemma pick_notMem {S : Submodule ℝ E} (hS : S ≠ ⊤) : pick S ∉ S := by
  have h : ∃ x, x ∉ S := by
    by_contra hcon
    push Not at hcon
    exact hS (Submodule.eq_top_iff'.2 hcon)
  rw [pick, dif_pos h]
  exact h.choose_spec

/-- The chain `M 0 = R`, `M (j+1) = M j + ℝ · pick (M j)`. -/
private def chain (R : Submodule ℝ E) : ℕ → Submodule ℝ E
  | 0 => R
  | j + 1 => chain R j ⊔ Submodule.span ℝ {pick (chain R j)}

omit [CompleteSpace E] in
private lemma chain_mono (R : Submodule ℝ E) : Monotone (chain R) :=
  monotone_nat_of_le_succ fun _ => le_sup_left

omit [CompleteSpace E] in
/-- Each `M j` is `R` plus a finite-dimensional subspace. -/
private lemma chain_eq_sup (R : Submodule ℝ E) (j : ℕ) :
    ∃ S : Submodule ℝ E, FiniteDimensional ℝ S ∧ chain R j = R ⊔ S := by
  induction j with
  | zero => exact ⟨⊥, inferInstance, by simp [chain]⟩
  | succ j ih =>
    obtain ⟨S, hS, hj⟩ := ih
    refine ⟨S ⊔ Submodule.span ℝ {pick (chain R j)}, ?_, ?_⟩
    · exact Submodule.finiteDimensional_sup _ _
    · rw [chain, hj, sup_assoc]

omit [CompleteSpace E] in
private lemma chain_ne_top {R : Submodule ℝ E} (hR : ¬ R.CoFG) (j : ℕ) : chain R j ≠ ⊤ := by
  intro htop
  obtain ⟨S, hS, hj⟩ := chain_eq_sup R j
  apply hR
  have hcod : Codisjoint S R := by
    rw [codisjoint_iff, sup_comm, ← hj, htop]
  exact Submodule.FG.cofg_of_codisjoint hcod ((Submodule.fg_iff_finiteDimensional S).2 hS)

omit [CompleteSpace E] in
private lemma chain_isClosed {R : Submodule ℝ E} (hR : IsClosed (R : Set E)) (j : ℕ) :
    IsClosed (chain R j : Set E) := by
  obtain ⟨S, hS, hj⟩ := chain_eq_sup R j
  rw [hj]
  exact Submodule.isClosed_sup_finiteDimensional R S hR

/-- The range of `1 + c`, `c` compact, has finite codimension. -/
theorem coFG_range_one_add (hc : IsCompactOperator c) : (1 + c : E →L[ℝ] E).range.CoFG := by
  by_contra hR
  set R := (1 + c : E →L[ℝ] E).range with hRdef
  have hRcl : IsClosed (R : Set E) := isClosed_range_one_add hc
  -- the chain `M j` and the unit vectors `u j ∈ M (j+1)` far from `M j`
  have hu : ∀ j, ∃ u ∈ chain R (j + 1), ‖u‖ = 1 ∧ ∀ y ∈ chain R j, 1 / 2 ≤ ‖u - y‖ := fun j =>
    exists_unit_far (chain_isClosed hRcl j) (chain_mono R (Nat.le_succ j))
      (Submodule.mem_sup_right (Submodule.mem_span_singleton_self _))
      (pick_notMem (chain_ne_top hR j))
  choose u huM hu1 hufar using hu
  -- separation: `‖c (u l) - c (u j)‖ ≥ 1/2` for `j < l`
  have hsep : ∀ j l, j < l → 1 / 2 ≤ ‖c (u l) - c (u j)‖ := by
    intro j l hjl
    have hmem : u j + (1 + c : E →L[ℝ] E) (u l) - (1 + c : E →L[ℝ] E) (u j) ∈ chain R l := by
      refine Submodule.sub_mem _ (Submodule.add_mem _ ?_ ?_) ?_
      · exact chain_mono R hjl (huM j)
      · exact chain_mono R (Nat.zero_le l) (LinearMap.mem_range_self _ (u l))
      · exact chain_mono R (Nat.zero_le l) (LinearMap.mem_range_self _ (u j))
    have := hufar l _ hmem
    have heq : u l - (u j + (1 + c : E →L[ℝ] E) (u l) - (1 + c : E →L[ℝ] E) (u j)) =
        -(c (u l) - c (u j)) := by
      simp only [add_apply, ContinuousLinearMap.one_apply]; abel
    rwa [heq, norm_neg] at this
  -- compactness contradiction
  obtain ⟨K, hK, hKsub⟩ := hc.image_closedBall_subset_compact (f := (c : E →ₗ[ℝ] E)) 1
  have hmem : ∀ n, c (u n) ∈ K := fun n =>
    hKsub ⟨u n, by rw [mem_closedBall, dist_zero_right, hu1], rfl⟩
  obtain ⟨y, -, φ, hφ, hlim⟩ := hK.tendsto_subseq hmem
  obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.1 hlim) (1 / 4) (by norm_num)
  have h1 := hN N le_rfl
  have h2 := hN (N + 1) (Nat.le_succ N)
  have h3 := hsep (φ N) (φ (N + 1)) (hφ (Nat.lt_succ_self N))
  have h4 : dist (c (u (φ (N + 1)))) (c (u (φ N))) < 1 / 2 := by
    calc dist (c (u (φ (N + 1)))) (c (u (φ N)))
        ≤ dist (c (u (φ (N + 1)))) y + dist y (c (u (φ N))) := dist_triangle _ _ _
      _ < 1 / 4 + 1 / 4 := by rw [dist_comm y]; exact add_lt_add h2 h1
      _ = 1 / 2 := by norm_num
  rw [dist_eq_norm] at h4
  exact absurd h3 (not_le.2 h4)

/-- **Riesz–Schauder**: `1 + c` is Fredholm for a compact operator `c` on a Banach space. -/
theorem isFredholm_one_add (hc : IsCompactOperator c) : IsFredholm (1 + c : E →L[ℝ] E) :=
  isFredholm_of_banach _ (finiteDimensional_ker_one_add hc) (isClosed_range_one_add hc)
    (coFG_range_one_add hc)

end RieszSchauder

/-! ### Compact perturbations of Fredholm operators -/

omit [CompleteSpace E] [CompleteSpace F] in
open scoped LinearMap.FiniteRangeSetoid in
/-- If `w ≈ id` (finite-rank difference) then `w - 1` is compact. -/
private lemma isCompactOperator_sub_one_of_equiv {w : E →L[ℝ] E}
    (h : (w : E →ₗ[ℝ] E) ≈ LinearMap.id) : IsCompactOperator ⇑(w - 1 : E →L[ℝ] E) := by
  rw [LinearMap.FiniteRangeSetoid.equiv_iff_hasFiniteRange] at h
  have hfg : (w - 1 : E →L[ℝ] E).range.FG := h
  have : FiniteDimensional ℝ (w - 1 : E →L[ℝ] E).range :=
    (Submodule.fg_iff_finiteDimensional _).1 hfg
  exact isCompactOperator_of_finiteDimensional_range (w - 1)

/-- **Compact perturbations of Fredholm operators**: if `u : E →L[ℝ] F` is Fredholm and
`k : E →L[ℝ] F` is compact, then `u + k` is Fredholm. -/
theorem isFredholm_add_isCompactOperator {u : E →L[ℝ] F} (hu : IsFredholm u)
    {k : E →L[ℝ] F} (hk : IsCompactOperator k) : IsFredholm (u + k) := by
  obtain ⟨v, hvu⟩ := hu.exists_isQuasiInverse
  -- `v (u + k) = 1 + c₁`, `(u + k) v = 1 + c₂` with `c₁`, `c₂` compact
  have hc₁ : IsCompactOperator ⇑((v ∘L u - 1) + v ∘L k : E →L[ℝ] E) :=
    (isCompactOperator_sub_one_of_equiv (w := v ∘L u) hvu.1).add (hk.clm_comp v)
  have hc₂ : IsCompactOperator ⇑((u ∘L v - 1) + k ∘L v : F →L[ℝ] F) :=
    (isCompactOperator_sub_one_of_equiv (w := u ∘L v) hvu.2).add (hk.comp_clm v)
  have e₁ : v ∘L (u + k) = 1 + ((v ∘L u - 1) + v ∘L k) := by
    ext x
    simp only [ContinuousLinearMap.comp_apply, add_apply, sub_apply, ContinuousLinearMap.one_apply,
      map_add]
    abel
  have e₂ : (u + k) ∘L v = 1 + ((u ∘L v - 1) + k ∘L v) := by
    ext x
    simp only [ContinuousLinearMap.comp_apply, add_apply, sub_apply, ContinuousLinearMap.one_apply]
    abel
  -- kernel
  have hker : FiniteDimensional ℝ (u + k).ker := by
    have : FiniteDimensional ℝ (v ∘L (u + k)).ker := by
      rw [e₁]; exact finiteDimensional_ker_one_add hc₁
    refine Submodule.finiteDimensional_of_le (S₂ := (v ∘L (u + k)).ker) fun x hx => ?_
    rw [LinearMap.mem_ker, ContinuousLinearMap.coe_coe] at hx ⊢
    change v ((u + k) x) = 0
    rw [hx, map_zero]
  -- range
  have hle : ((u + k) ∘L v).range ≤ (u + k).range := by
    rintro _ ⟨y, rfl⟩
    exact ⟨v y, rfl⟩
  have hcl₂ : IsClosed (((u + k) ∘L v).range : Set F) := by
    rw [e₂]; exact isClosed_range_one_add hc₂
  have hcofg₂ : ((u + k) ∘L v).range.CoFG := by
    rw [e₂]; exact coFG_range_one_add hc₂
  have hcofg : (u + k).range.CoFG := hcofg₂.of_le hle
  have hcl : IsClosed ((u + k).range : Set F) :=
    Submodule.isClosed_mono_of_finiteDimensional_quotient hcl₂ hle
  exact isFredholm_of_banach _ hker hcl hcofg

end Polyfold
