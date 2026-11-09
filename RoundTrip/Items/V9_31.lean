import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V9_31

set_option maxSynthPendingDepth 3

/-! Round trip for V9_31 (Remark 9.3.3, p. 423 of the 2021 book; 2017: Remark 9.8, p. 311: "the
local oriented representation (9.9) is not unique, and an orientation of `Θ` is not unique").

`A` is the type of the one listed theorem, `EpGroupoid.remark_9_3_3` (no universe parameters):
for the indicator `Θ = 1_{p}` of a point of `ℝⁿ`, `q ↦ T̂_q = q · (T_p{p}, +) + (1 - q) ·
(T_p{p}, -)` is an injective family of orientations for `q ∈ (0, 1) ∩ ℚ`.

* `B` (b) (two orientations of some `Θ` differing at a smooth object) follows from `A`:
  `T̂_{1/2} ≠ T̂_{1/3}` (`A_to_B`; points of `ℝⁿ` are smooth; the project's `IsOrientation`
  gives the blind `IsOrientationB` by forgetting the dimension proofs, as in V9_30).
* `B` (a) (an orientation with two oriented local representations (9.9) on the same `U(x)`
  whose families of sheets differ) does **not** follow from `A`: for `Θ = 1_{p}` every local
  branching structure has all sheets equal to `{p}` (a sheet through `y ≠ p` would give
  `Θ(y) > 0`), so the two representations always have the same sheets `{{p}}`.  `A_to_B`
  proves (a) from the project's Example 9.3.5 instead (V9_31 bans only `remark_9_3_3`): for
  `Θ` of Example 9.3.5 and all four graphs oriented by `+(1, β')`, the oriented sums of the two
  structures `{G⁺⁺, G⁻⁻}` and `{G⁺⁻, G⁻⁺}` coincide everywhere (`orientedLift1_eq_orientedLift2`:
  on `s ≤ 0` the graphs pair as `G⁺⁻ = G⁺⁺`, `G⁻⁺ = G⁻⁻`, on `s > 0` as `G⁻⁺ = G⁺⁺`,
  `G⁺⁻ = G⁻⁻`, with equal slopes, and at `s = 0` all slopes vanish), so `T̂ = orientedLift1 (+)`
  (an orientation, `orientedLift1_isOrientation_rn`) has both representations at `(0, 0)`, on
  `U = ℝ²`, and `G⁺⁺` is not among `{G⁺⁻, G⁻⁺}`.  So `A_to_B` uses `A` for (b) only, and (a)
  is extra content of `B` with respect to `A` (true, proved from other project material).
  (The 2021 text's first sentence of Remark 9.3.3 says that (9.9) amounts to the local
  continuity of the lift on `supp Θ`; (a) follows the item's quotation instead, so it is not a
  claim of the text as printed.  The project builds the continuity into
  `SubmanifoldOrientation`.)
* `B_to_A`: `B` is two existence statements; `A` is a specific infinite family on `1_{p}`, which
  does not follow from `B`.  Not proved from `B`; `A` holds (`A_holds`), so `B → A` is true
  but only trivially, and we do not include a vacuous copy of the project's proof. -/

namespace RoundTrip.V9_31
open Polyfold Set MPolyfold EpGroupoid

/-- The project's statement. -/
def A : Prop := type_of% @Polyfold.EpGroupoid.remark_9_3_3

theorem A_holds : A := @Polyfold.EpGroupoid.remark_9_3_3

/-! ### From the project's `IsOrientation` to the blind one -/

theorem isOrientationB_of {Obj Mor : Type} [TopologicalSpace Obj] [T2Space Obj]
    [ParacompactSpace Obj] [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor]
    {X : EpGroupoid Obj Mor} {Θ : Obj → ℚ} {T : Obj → X.PObj.OrTangent →₀ ℚ}
    (hT : X.IsOrientation Θ T) : IsOrientationB X Θ T := by
  refine ⟨fun x hx => hT.mem x hx, fun φ hφ => hT.natural φ hφ, fun x hx => hT.lifts x hx,
    fun x hx => ?_⟩
  obtain ⟨Bo, hBo⟩ := hT.locallyOriented x hx
  exact ⟨Bo.toLocalBranchingStructure, Bo.dim, Bo.orient, fun y hy hys => hBo y hy hys⟩

/-! ### Example 9.3.5 with all four graphs oriented by `+(1, β')` -/

open scoped Classical in
/-- One summand of the two oriented sums: equal if the graphs agree at `z` with equal slopes. -/
theorem summand_eq {b b' : Bool} {z : Fin 2 → ℝ}
    (hiff : z ∈ graph2 (beta1 b) ↔ z ∈ graph2 (beta2 b'))
    (hd : z ∈ graph2 (beta1 b) → deriv (beta1 b) (z 0) = deriv (beta2 b') (z 0)) :
    (if z ∈ graph2 (beta1 b) then
        Finsupp.single ((orient1 (fun _ => true) b).tangent z) ((fun _ => (1 : ℚ)) b) else 0) =
      (if z ∈ graph2 (beta2 b') then
        Finsupp.single ((orient2 (fun _ => true) b').tangent z) ((fun _ => (1 : ℚ)) b') else 0) := by
  by_cases h : z ∈ graph2 (beta1 b)
  · rw [if_pos h, if_pos (hiff.1 h)]
    exact congrArg (fun g => Finsupp.single g (1 : ℚ))
      (graphOrientation_tangent_eq (contDiff_beta1 b) (contDiff_beta2 b') (boolSign_ne_zero true)
        h (hiff.1 h) (hd h))
  · rw [if_neg h, if_neg fun h' => h (hiff.2 h')]

open scoped Classical in
/-- **With all graphs oriented by `+(1, β')`, the two structures of Example 9.3.5 give the same
oriented sum everywhere.** -/
theorem orientedLift1_eq_orientedLift2 :
    orientedLift1 (fun _ => true) = orientedLift2 (fun _ => true) := by
  funext z
  rw [orientedLift1, orientedLift2, orientedSumRn_bool, orientedSumRn_bool]
  rcases lt_trichotomy (z 0) 0 with hz | hz | hz
  · have h1 : z ∈ graph2 (beta1 true) ↔ z ∈ graph2 (beta2 true) := by
      change z 1 = betaPP (z 0) ↔ z 1 = betaPM (z 0)
      rw [betaPM_of_nonpos hz.le]
    have h2 : z ∈ graph2 (beta1 false) ↔ z ∈ graph2 (beta2 false) := by
      change z 1 = betaMM (z 0) ↔ z 1 = betaMP (z 0)
      rw [betaMP_of_nonpos hz.le]
    congr 1
    · exact summand_eq h1 fun _ =>
        deriv_eq_of_eqOn_Iio (fun t ht => (betaPM_of_nonpos ht.le).symm) hz
    · exact summand_eq h2 fun _ =>
        deriv_eq_of_eqOn_Iio (fun t ht => (betaMP_of_nonpos ht.le).symm) hz
  · have h1 : z ∈ graph2 (beta1 true) ↔ z ∈ graph2 (beta2 true) := by
      change z 1 = betaPP (z 0) ↔ z 1 = betaPM (z 0)
      rw [betaPM_of_nonpos hz.le]
    have h2 : z ∈ graph2 (beta1 false) ↔ z ∈ graph2 (beta2 false) := by
      change z 1 = betaMM (z 0) ↔ z 1 = betaMP (z 0)
      rw [betaMP_of_nonpos hz.le]
    congr 1
    · exact summand_eq h1 fun _ => by rw [hz, deriv_beta1_zero, deriv_beta2_zero]
    · exact summand_eq h2 fun _ => by rw [hz, deriv_beta1_zero, deriv_beta2_zero]
  · have h1 : z ∈ graph2 (beta1 true) ↔ z ∈ graph2 (beta2 false) := by
      change z 1 = betaPP (z 0) ↔ z 1 = betaMP (z 0)
      rw [betaMP_of_pos hz]
    have h2 : z ∈ graph2 (beta1 false) ↔ z ∈ graph2 (beta2 true) := by
      change z 1 = betaMM (z 0) ↔ z 1 = betaPM (z 0)
      rw [betaPM_of_pos hz]
    rw [add_comm (if z ∈ graph2 (beta2 true) then _ else _)]
    congr 1
    · exact summand_eq h1 fun _ =>
        deriv_eq_of_eqOn_Ioi (fun t ht => (betaMP_of_pos ht).symm) hz
    · exact summand_eq h2 fun _ =>
        deriv_eq_of_eqOn_Ioi (fun t ht => (betaPM_of_pos ht).symm) hz

open scoped Classical in
/-- The first oriented structure of Example 9.3.5 at `(0, 0)` (all graphs `+(1, β')`). -/
noncomputable def obs1 : (trivial (rnPolyfold 2)).OrientedBranchingStructure
    (fun y => ∑ i with y ∈ (fun b => graph2 (beta1 b)) i, (fun _ => (1 : ℚ)) i) 0 :=
  orientedBranchingStructure_sum_rn (fun b => graph2 (beta1 b)) (fun _ => 1) (fun _ => one_pos)
    (fun b => rnPolyfold_isSubmanifoldOfDim_graph2 (contDiff_beta1 b))
    (fun b => isClosed_graph2 (contDiff_beta1 b).continuous) (orient1 fun _ => true) 0

open scoped Classical in
/-- The second oriented structure of Example 9.3.5 at `(0, 0)` (all graphs `+(1, β')`). -/
noncomputable def obs2 : (trivial (rnPolyfold 2)).OrientedBranchingStructure
    (fun y => ∑ i with y ∈ (fun b => graph2 (beta2 b)) i, (fun _ => (1 : ℚ)) i) 0 :=
  orientedBranchingStructure_sum_rn (fun b => graph2 (beta2 b)) (fun _ => 1) (fun _ => one_pos)
    (fun b => rnPolyfold_isSubmanifoldOfDim_graph2 (contDiff_beta2 b))
    (fun b => isClosed_graph2 (contDiff_beta2 b).continuous) (orient2 fun _ => true) 0

/-- The second structure, as a local branching structure of `example935Theta`. -/
noncomputable def lbs2 : (trivial (rnPolyfold 2)).LocalBranchingStructure example935Theta 0 :=
  { obs2.toLocalBranchingStructure with
    eq_sum := fun y hy => (example_9_3_5_count y).trans (obs2.eq_sum y hy) }

theorem mem_U1 (y : Fin 2 → ℝ) : y ∈ obs1.U := fun i _ => zero_mem_graph2_beta1 i
theorem mem_U2 (y : Fin 2 → ℝ) : y ∈ obs2.U := fun i _ => zero_mem_graph2_beta2 i

theorem B_a : ∃ (Obj Mor : Type) (_ : TopologicalSpace Obj) (_ : T2Space Obj)
    (_ : ParacompactSpace Obj) (_ : TopologicalSpace Mor) (_ : T2Space Mor)
    (_ : ParacompactSpace Mor)
    (X : EpGroupoid Obj Mor) (Θ : Obj → ℚ) (T : Obj → X.PObj.OrTangent →₀ ℚ),
    X.IsBranchedEpSubgroupoid Θ ∧ IsOrientationB X Θ T ∧
    ∃ x ∈ EpGroupoid.supp Θ,
      ∃ (B₁ : X.LocalBranchingStructure Θ x) (n₁ : B₁.ι → ℕ)
        (o₁ : ∀ i, X.PObj.SubmanifoldOrientation (B₁.M i) (n₁ i))
        (B₂ : X.LocalBranchingStructure Θ x) (n₂ : B₂.ι → ℕ)
        (o₂ : ∀ i, X.PObj.SubmanifoldOrientation (B₂.M i) (n₂ i)),
        B₁.U = B₂.U ∧
        (∀ y ∈ B₁.U, y ∈ X.PObj.smoothSet → T y = orSumB B₁ n₁ o₁ y) ∧
        (∀ y ∈ B₂.U, y ∈ X.PObj.smoothSet → T y = orSumB B₂ n₂ o₂ y) ∧
        Set.range B₁.M ≠ Set.range B₂.M := by
  classical
  have hsupp : (0 : Fin 2 → ℝ) ∈ EpGroupoid.supp example935Theta := by
    change (0 : ℚ) < example935Theta 0
    rw [example935Theta, obs1.eq_sum 0 obs1.mem_U]
    exact Finset.sum_pos (fun i _ => obs1.σ_pos i)
      ⟨⟨true, zero_mem_graph2_beta1 true⟩, Finset.mem_filter.2 ⟨Finset.mem_univ _, obs1.mem_M _⟩⟩
  refine ⟨_, _, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, trivial (rnPolyfold 2), example935Theta, orientedLift1 (fun _ => true),
    example935Theta_isBranched, isOrientationB_of (orientedLift1_isOrientation_rn _), 0, hsupp,
    obs1.toLocalBranchingStructure, obs1.dim, obs1.orient, lbs2, obs2.dim, obs2.orient,
    ?_, ?_, ?_, ?_⟩
  · ext y
    exact ⟨fun _ => mem_U2 y, fun _ => mem_U1 y⟩
  · intro y hy _
    exact (orientedSum_sum_rn_eq _ _ _ _ _ _ hy).symm
  · intro y hy _
    rw [orientedLift1_eq_orientedLift2]
    exact (orientedSum_sum_rn_eq (fun b => graph2 (beta2 b)) (fun _ => 1) (fun _ => one_pos)
      (fun b => rnPolyfold_isSubmanifoldOfDim_graph2 (contDiff_beta2 b))
      (fun b => isClosed_graph2 (contDiff_beta2 b).continuous) (orient2 fun _ => true)
      (mem_U2 y)).symm
  · intro hr
    have hmem : obs1.M ⟨true, zero_mem_graph2_beta1 true⟩ ∈ Set.range lbs2.M := by
      rw [← hr]; exact ⟨_, rfl⟩
    obtain ⟨j, hjeq⟩ := hmem
    have hjeq' : graph2 (beta2 (j : obs2.ι).1) ∩ obs2.U = graph2 (beta1 true) ∩ obs1.U := hjeq
    generalize (j : obs2.ι).1 = b at hjeq'
    cases b
    · have h1 : ptPP (-1) ∈ graph2 (beta2 false) ∩ obs2.U := by
        rw [hjeq']; exact ⟨ptPP_mem _, mem_U1 _⟩
      exact (ptPP_mem_beta2_of_neg (by norm_num : (-1 : ℝ) < 0)).2 h1.1
    · have h1 : ptPP 1 ∈ graph2 (beta2 true) ∩ obs2.U := by
        rw [hjeq']; exact ⟨ptPP_mem _, mem_U1 _⟩
      exact (ptPP_mem_beta2 (by norm_num : (0 : ℝ) < 1)).2 h1.1

/-! ### `A → B` -/

theorem A_to_B : A → B := by
  intro hA
  refine ⟨B_a, ?_⟩
  obtain ⟨T, hT, hinj⟩ := @hA 0 (fun _ => 0)
  have hne : T (1 / 2) ≠ T (1 / 3) := fun h => by
    have := hinj _ _ h
    norm_num at this
  obtain ⟨y, hy⟩ := Function.ne_iff.1 hne
  refine ⟨_, _, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, trivial (rnPolyfold 0), _, T (1 / 2), T (1 / 3),
    isBranchedEpSubgroupoid_indicator 0 (fun _ => 0),
    isOrientationB_of (hT _ (by norm_num) (by norm_num)),
    isOrientationB_of (hT _ (by norm_num) (by norm_num)), y, ?_, hy⟩
  change y ∈ (rnPolyfold 0).smoothSet
  rw [TrivialBundle.rnPolyfold_smoothSet]
  exact mem_univ y

#rt_check RoundTrip.V9_31.A_to_B [Polyfold.EpGroupoid.remark_9_3_3]
#rt_check RoundTrip.V9_31.B_a [Polyfold.EpGroupoid.remark_9_3_3]

end RoundTrip.V9_31
