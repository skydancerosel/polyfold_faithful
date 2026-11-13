import Polyfold.Chapter5.SobolevCubeSpaces

/-!
# The sc-structure `W^{1+m,p}` on a cube, part 4: Rellich (compact inclusions)

Continuation of `SobolevCubeVolterra–3` (2021 §5.5, the remark after Theorem 5.5.5, pp. 230–231).

**`isCompactOperator_inclW_cube`** (`p > 1`): the inclusion `W^{k+1,p}(Ω1) → W^{k,p}(Ω1)` of the
Sobolev spaces of the open unit cube `Ω1 = (0,1)¹` is a compact operator.  Each component
`D^j u`, `j ≤ k`, of `u` in the unit ball of `W^{k+1,p}` is `c + V (D^{j+1} u)` with `|c| ≤ 2`
(`comp_eq_cst_add_V`), so the components range over the sum of a compact set of constants and
the image of the unit ball under the compact Volterra operator `V` (`isCompactOperator_V`).
-/

open MeasureTheory Set Function Filter Topology
open scoped ENNReal ContDiff

noncomputable section

namespace Polyfold

namespace SobolevCube

open SobolevRemark

variable {p : ℝ} [hP : Fact (1 ≤ ENNReal.ofReal p)]

lemma cst_sub (a b : ℝ) : (cst a : L p) - cst b = cst (a - b) := by
  rw [cst, cst, cst, ← toLpS_sub]; rfl

lemma isometry_cst : Isometry (cst : ℝ → L p) :=
  Isometry.of_dist_eq fun a b => by
    rw [dist_eq_norm, cst_sub, norm_cst, Real.dist_eq]

/-- The constant of `comp u j = c + V (comp u (j+1))` is bounded by `2‖u‖`. -/
lemma abs_cst_le {k : ℕ} (u : W 1 k p Ω1) (j : Fin k) {c : ℝ}
    (hc : comp u j.castSucc = cst c + V (comp u j.succ)) : |c| ≤ 2 * ‖u‖ := by
  have e : (cst c : L p) = comp u j.castSucc - V (comp u j.succ) := by rw [hc]; abel
  rw [← norm_cst (p := p), e]
  calc ‖comp u j.castSucc - V (comp u j.succ)‖
      ≤ ‖comp u j.castSucc‖ + ‖V (comp u j.succ)‖ := norm_sub_le _ _
    _ ≤ ‖u‖ + ‖u‖ := add_le_add (norm_comp_le u _) ((norm_V_le _).trans (norm_comp_le u _))
    _ = 2 * ‖u‖ := by ring

/-- The image of the unit ball under `V` lies in a compact set. -/
lemma exists_compact_V (hp : 1 < p) :
    ∃ K : Set (L p), IsCompact K ∧ V '' Metric.ball (0 : L p) 1 ⊆ K :=
  (isCompactOperator_iff_image_ball_subset_compact (V : L p →L[ℝ] L p).toLinearMap one_pos).1
    (isCompactOperator_V hp)

/-- **The components of the unit ball of `W^{k+1,p}(Ω1)` of order `≤ k` form a totally bounded
set** (`p > 1`). -/
lemma totallyBounded_comp (hp : 1 < p) {k : ℕ} (j : Fin (k + 1)) :
    TotallyBounded ((fun u : W 1 (k + 1) p Ω1 => comp u j.castSucc) ''
      Metric.ball 0 1) := by
  obtain ⟨K, hK, hVK⟩ := exists_compact_V hp
  set S : Set (L p) := (fun q : L p × L p => q.1 + q.2) ''
    ((cst '' Icc (-2) 2) ×ˢ K)
  have hS : IsCompact S :=
    ((isCompact_Icc.image isometry_cst.continuous).prod hK).image continuous_add
  refine hS.totallyBounded.subset ?_
  rintro _ ⟨u, hu, rfl⟩
  rw [Metric.mem_ball, dist_zero_right] at hu
  obtain ⟨c, hc⟩ := comp_eq_cst_add_V u j
  have hcb := abs_cst_le u j hc
  refine ⟨(cst c, V (comp u j.succ)), ⟨⟨c, abs_le.1 (hcb.trans (by linarith)), rfl⟩, hVK ?_⟩,
    hc.symm⟩
  refine ⟨comp u j.succ, ?_, rfl⟩
  rw [Metric.mem_ball, dist_zero_right]
  exact (norm_comp_le u _).trans_lt hu

/-- **Rellich on the cube**: the inclusion `W^{k+1,p}(Ω1) → W^{k,p}(Ω1)`, `Ω1 = (0,1)¹`, is a
compact operator for `p > 1`. -/
theorem isCompactOperator_inclW_cube (hp : 1 < p) (k : ℕ) :
    IsCompactOperator (inclW (n := 1) (k := k) (p := p) (Ω := Ω1)) := by
  set Tm := inclW (n := 1) (k := k) (p := p) (Ω := Ω1)
  set B : Set (W 1 (k + 1) p Ω1) := Metric.ball 0 1
  set Ca : MIdx 1 k → Set (Lp ℝ (ENNReal.ofReal p) (μΩ Ω1)) :=
    fun a => (fun u => Dop a (Tm u)) '' B
  have hCa : ∀ a, TotallyBounded (Ca a) := by
    intro a
    refine GapP1Sobolev.totallyBounded_of_isometry T.isometry ?_
    refine (totallyBounded_comp hp (a.1 0)).subset ?_
    rintro _ ⟨_, ⟨u, hu, rfl⟩, rfl⟩
    refine ⟨u, hu, ?_⟩
    simp only [comp]
    rw [Dop_inclW]
    exact congrArg (fun b => T (Dop b u)) (eq_midx a.lift).symm
  set K' : Set (Amb 1 k p Ω1) :=
    (PiLp.homeomorph (ENNReal.ofReal p) (fun _ : MIdx 1 k => Lp ℝ (ENNReal.ofReal p) (μΩ Ω1))) ⁻¹'
      Set.pi univ (fun a => closure (Ca a))
  have hK' : IsCompact K' := by
    refine (PiLp.homeomorph (ENNReal.ofReal p)
      (fun _ : MIdx 1 k => Lp ℝ (ENNReal.ofReal p) (μΩ Ω1))).isCompact_preimage.2
      (isCompact_univ_pi fun a => ?_)
    exact isCompact_iff_totallyBounded_isComplete.2
      ⟨(hCa a).closure, isClosed_closure.isComplete⟩
  have htb : TotallyBounded (Tm '' B) := by
    refine GapP1Sobolev.totallyBounded_of_isometry isometry_subtype_coe ?_
    refine hK'.totallyBounded.subset ?_
    rintro _ ⟨_, ⟨u, hu, rfl⟩, rfl⟩
    intro a _
    exact subset_closure ⟨u, hu, rfl⟩
  refine (isCompactOperator_iff_image_ball_subset_compact
    (Tm : W 1 (k + 1) p Ω1 →ₗ[ℝ] W 1 k p Ω1) one_pos).2 ⟨closure (Tm '' B), ?_, subset_closure⟩
  exact isCompact_iff_totallyBounded_isComplete.2 ⟨htb.closure, isClosed_closure.isComplete⟩

end SobolevCube

end Polyfold
