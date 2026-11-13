import Polyfold.Chapter7.ReducedCriterion

/-!
# Appendix 7.6.3: the exact non-effective part of the analogue of Zhou's example

2021 Appendix 7.6.3, p. 348 (new in the 2021 edition): for `ℤ/2` acting by `(s, f) ↦ (s, −f)` on
the retract of Part I's Subsection 1.4.4, identified with `Σ = {(s, t) | t = 0 if s ≤ 0}`, the text
computes `𝐗^T = ({0,1} × {(s, 0) | s < 0}) ∪ ({0} × Σ)` and `cl(𝐗^T) ∖ 𝐗^T = {1} × {(0, 0)}`.

The project's ep-groupoid `JumpingRetract.X` (`ReducedNotHausdorff.lean`) is `ℤ/2 = ℤˣ` acting by
`(t, z) ↦ (t, ±z)` on the retract `O` of Part I's Remark 4.2.2 (2017: 4.3), which is `{(t, 0)}` over
`t ≤ 0` and a line over each `t > 0`, as `Σ`.  It had one point of `cl(𝐗^T) ∖ 𝐗^T`.  Here the
text's computation is carried out for it, exactly:

* `JumpingRetract.nonEffectivePart_eq`: `𝐗^T = ({1} × O) ∪ ({−1} × {(t, z) ∈ O | t < 0})`.
* `JumpingRetract.closure_nonEffectivePart_diff`: `cl(𝐗^T) ∖ 𝐗^T = {(−1, (0, 0))}`, one point.
* `JumpingRetract.appendix_7_6_3`: both, with `T_R` not Hausdorff and (LUC) failing.

Zhou's retract itself (the sc-Hilbert space `ℝ ⊕ L²(ℝ)` with `F_m = ℝ ⊕ H^{m,δ_m}(ℝ)` and the
sc-smoothness of `r(s, f) = (s, π_s f)`, cited from [60]) is `GapP2_A2ZhouGroupoid.lean`
(`ZhouRetract.appendix_7_6_3`) and `GapP2_A2Sigma.lean` (`ZhouRetract.appendix_7_6_3_sigma`, on `Σ`).
-/

set_option maxSynthPendingDepth 3

open Set Filter Topology

namespace Polyfold.EpGroupoid.Examples.JumpingRetract

open Polyfold.RemarkFourThree Polyfold.ScOneExample

/-- On `O`, a point over `t ≤ 0` has `z = 0`. -/
lemma snd_eq_zero_of_nonpos (p : O) (hp : p.1.1 ≤ 0) : p.1.2 = 0 := by
  rw [← (mem_O_iff _).1 p.2, fam_of_nonpos hp]
  rfl

/-- Over every `t > 0` the fibre of `O` is non-zero: `L(t)` has a non-zero vector in its range. -/
lemma exists_fam_ne_zero {t : ℝ} (ht : 0 < t) : ∃ w : ScOneExample.X 0, fam t 0 w = w ∧ w ≠ 0 := by
  have hsq := cc_sq_add_ss_sq (kt t) t
  have hne := nk_ne (kt t)
  by_cases hc : cc (kt t) t = 0
  · have hs : ss (kt t) t ≠ 0 := by
      intro hs; rw [hc, hs] at hsq; norm_num at hsq
    refine ⟨fam t 0 (δv (nk (kt t + 1))), fam_idem t _, fun h => hs ?_⟩
    have h1 := congrArg (fun z : c0 => z (nk (kt t + 1))) h
    simp only [fam_zero_apply_of_pos ht, δv_apply, if_neg hne.symm, hc] at h1
    simpa using h1
  · refine ⟨fam t 0 (δv (nk (kt t))), fam_idem t _, fun h => hc ?_⟩
    have h1 := congrArg (fun z : c0 => z (nk (kt t))) h
    simp only [fam_zero_apply_of_pos ht, δv_apply, if_neg hne.symm, if_neg hne] at h1
    simpa using h1

/-- `(−1, p) ∈ 𝐗^T` for every `p` over `t < 0`. -/
lemma neg_one_mem_nonEffectivePart {p : O} (hp : p.1.1 < 0) :
    ((-1 : ℤˣ), p) ∈ X.nonEffectivePart := by
  rw [EpGroupoid.mem_nonEffectivePart_iff]
  have ho : IsOpen {q : ℤˣ × O | q.2.1.1 < 0} :=
    isOpen_lt (continuous_fst.comp (continuous_subtype_val.comp continuous_snd)) continuous_const
  filter_upwards [ho.mem_nhds (show p.1.1 < 0 from hp)] with q hq
  exact (smul_eq_self_of_nonpos q.1 q.2 (le_of_lt hq)).symm

/-- `(−1, p) ∉ 𝐗^T` for every `p` over `t > 0`: either `−1` moves `p`, or `p = (t, 0)` and `−1`
moves the points `(t, ε w)` of the fibre, which tend to `p`. -/
lemma neg_one_not_mem_nonEffectivePart {p : O} (hp : 0 < p.1.1) :
    ((-1 : ℤˣ), p) ∉ X.nonEffectivePart := by
  intro h
  have hneg : ∀ z : ScOneExample.X 0, z = c (-1) • z → z = 0 := fun z hz => by
    have h2 : (2 : ℝ) • z = 0 := by
      rw [two_smul]; nth_rw 1 [hz]; simp [c]
    exact (smul_eq_zero.1 h2).resolve_left two_ne_zero
  by_cases hz : p.1.2 = 0
  · obtain ⟨w, hw, hw0⟩ := exists_fam_ne_zero hp
    have hmem : ∀ n, ((p.1.1, node n • w) : E 0) ∈ O := fun n => by
      rw [mem_O_iff]
      change fam p.1.1 0 (node n • w) = node n • w
      rw [map_smul, hw]
    have hnode : Tendsto node atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
    have hpt : Tendsto (fun n => (⟨(p.1.1, node n • w), hmem n⟩ : O)) atTop (𝓝 p) := by
      rw [tendsto_subtype_rng]
      have h2 : Tendsto (fun n => node n • w) atTop (𝓝 (0 : ScOneExample.X 0)) := by
        simpa using hnode.smul_const w
      have h3 := (tendsto_const_nhds (x := p.1.1)).prodMk_nhds h2
      rw [← hz] at h3
      exact h3
    have h2 : Tendsto (fun n => ((-1 : ℤˣ), (⟨(p.1.1, node n • w), hmem n⟩ : O))) atTop
        (𝓝 ((-1 : ℤˣ), p)) := tendsto_const_nhds.prodMk_nhds hpt
    obtain ⟨n, hn⟩ := (h2.eventually ((EpGroupoid.mem_nonEffectivePart_iff _).1 h)).exists
    have hn' : node n • w = c (-1) • (node n • w) := congrArg (fun q : O => q.1.2) hn
    exact hw0 ((smul_eq_zero.1 (hneg _ hn')).resolve_left (node_pos n).ne')
  · exact hz (hneg _ (congrArg (fun q : O => q.1.2) (src_eq_tgt_of_mem_nonEffectivePart h)))

/-- **The non-effective part of the analogue of Zhou's example, exactly** (2021 Appendix 7.6.3,
p. 348): `𝐗^T = ({1} × O) ∪ ({−1} × {(t, z) ∈ O | t < 0})`, the text's
`({0,1} × {(s, 0) | s < 0}) ∪ ({0} × Σ)` with `ℤ/2 = {1, −1}` written multiplicatively. -/
theorem nonEffectivePart_eq :
    X.nonEffectivePart = {q | q.1 = 1} ∪ {q | q.1 = -1 ∧ q.2.1.1 < 0} := by
  ext ⟨k, p⟩
  simp only [mem_union, mem_ofPred_eq]
  constructor
  · intro h
    rcases Int.units_eq_one_or k with rfl | rfl
    · exact Or.inl rfl
    · refine Or.inr ⟨rfl, ?_⟩
      rcases lt_trichotomy p.1.1 0 with hp | hp | hp
      · exact hp
      · have hp0 : p = o₀ := Subtype.ext (Prod.ext hp (snd_eq_zero_of_nonpos p hp.le))
        exact absurd (hp0 ▸ h) not_mem_nonEffectivePart
      · exact absurd h (neg_one_not_mem_nonEffectivePart hp)
  · rintro (rfl | ⟨rfl, hp⟩)
    · exact X.unit_mem_nonEffectivePart p
    · exact neg_one_mem_nonEffectivePart hp

/-- **`cl(𝐗^T) ∖ 𝐗^T` is one point** (2021 Appendix 7.6.3, p. 348), `(−1, (0, 0))`, the text's
`{1} × {(0, 0)}`. -/
theorem closure_nonEffectivePart_diff :
    closure X.nonEffectivePart \ X.nonEffectivePart = {((-1 : ℤˣ), o₀)} := by
  refine Subset.antisymm ?_ (singleton_subset_iff.2 ⟨mem_closure_nonEffectivePart,
    not_mem_nonEffectivePart⟩)
  have hS : IsClosed ({q : ℤˣ × O | q.1 = 1} ∪ {q | q.2.1.1 ≤ 0}) :=
    (isClosed_eq continuous_fst continuous_const).union
      (isClosed_le (continuous_fst.comp (continuous_subtype_val.comp continuous_snd))
        continuous_const)
  have hsub : X.nonEffectivePart ⊆ {q : ℤˣ × O | q.1 = 1} ∪ {q | q.2.1.1 ≤ 0} := by
    rw [nonEffectivePart_eq]
    exact union_subset_union subset_rfl fun q hq => le_of_lt hq.2
  rintro ⟨k, p⟩ ⟨hcl, hn⟩
  rcases hS.closure_subset_iff.2 hsub hcl with hk | hp
  · exact absurd (nonEffectivePart_eq ▸ Or.inl hk : ((k, p) : ℤˣ × O) ∈ X.nonEffectivePart) hn
  · change p.1.1 ≤ 0 at hp
    rcases Int.units_eq_one_or k with rfl | rfl
    · exact absurd (X.unit_mem_nonEffectivePart p) hn
    · rcases hp.lt_or_eq with hp | hp
      · exact absurd (neg_one_mem_nonEffectivePart hp) hn
      · exact Prod.ext rfl (Subtype.ext (Prod.ext hp (snd_eq_zero_of_nonpos p hp.le)))

/-- **2021 Appendix 7.6.3, p. 348, for the analogue of Zhou's example**: `𝐗^T` is
`({1} × O) ∪ ({−1} × {t < 0})`, `cl(𝐗^T) ∖ 𝐗^T` is the one point `(−1, (0, 0))`, so `T_R` is not
Hausdorff and (LUC) fails. -/
theorem appendix_7_6_3 :
    X.nonEffectivePart = {q | q.1 = 1} ∪ {q | q.1 = -1 ∧ q.2.1.1 < 0} ∧
    closure X.nonEffectivePart \ X.nonEffectivePart = {((-1 : ℤˣ), o₀)} ∧
    ¬ T2Space X.ReducedMor ∧ ¬ X.IsLUC :=
  ⟨nonEffectivePart_eq, closure_nonEffectivePart_diff, not_t2Space_reducedMor, not_isLUC⟩

end Polyfold.EpGroupoid.Examples.JumpingRetract
