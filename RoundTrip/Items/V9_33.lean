import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V9_33

/-! Round trip for V9_33 (Example 9.3.5, p. 425 of the 2021 book; 2017: Example 9.1).

The item lists the definitions `betaPP`, `betaMM`, `betaPM`, `betaMP` (the project's
`β^{±±}`: `β⁺⁺(s) = e^{-1/s} + e^{1/s}`-glue, flat at `0`), `example935Theta`, `exampleT1`,
`exampleT2` (vocabulary) and eleven theorems; `A` is the conjunction of their types (no universe
parameters): the count identity, `Θ` branched, `example_9_3_5` (with Theorem 9.2.1's
independence as hypothesis) and `example_9_3_5_rn` (without), `T̂¹(0) = T̂²(0)`, `T̂¹ ≠ T̂²` at every
`(s, β⁺⁺(s))`, `s > 0`, and `T̂¹ = T̂²` for `s < 0`, injectivity of the sign choices of the first
structure, `T̂²` is none of the four orientations of the first structure, no sign choice of the
second structure coincides with `T̂¹`, and (via Lemma 9.3.4 on `ℝᵐ`) `T̂¹ ≠ T̂²` at some good point.

* `A → B` is not proved.  `B` quantifies over EVERY `β` with `β(0) = 0`, `β > 0` off `0` and all
  four `β^{±±}` smooth; `A` is about the one `β = betaPP`.  The project's general lemmas
  (`isOrientation_sum_rn`, `hasIndependentTangentSums_rn`, `graphOrientation_tangent_ne'`,
  general in `β`) suggest `B` holds for every such `β` by the same proofs; `A` does not state
  it.  Even at `β = betaPP`, `A` lacks two of `B`'s claims: that EVERY sign choice `ε` of the
  SECOND structure gives an orientation, and that these are pairwise different (`A` has
  injectivity for the first structure only); both hold by the project's unbanned lemmas
  (`orientedLift2_isOrientation_rn`, and the argument of `orientedLift1_injective`).
* At `B`'s instance `β = betaPP`, `A` gives `B`'s parts (a) (`Θ` branched, defined by the
  second structure too), (b) in full and (d) in full: `A_to_B_betaPP_part` (glue: `B`'s graphs
  `G1 betaPP`, `G2 betaPP` are the project's `beta1`, `beta2`, its `liftB` is the project's
  `orientedLift1/2`, its `ThetaB betaPP` is `example935Theta`); `B_to_B_betaPP_part` checks that
  this is a part of `B`.  Not covered there: (a)'s two local branching structures with `U = ℝ²`
  and (c).
* `B → A`: `A`'s claims are pointwise facts about `betaPP` (differences at every
  `(s, β⁺⁺(s))`, agreement on `s < 0`, `T̂²` not among the first structure's orientations) that
  `B` (existential differences) does not give; `B_to_A` re-proves `A` outright as verbatim copies
  of the project's proofs (renamed `…_c`), without using `B`. -/

namespace RoundTrip.V9_33
open Polyfold Polyfold.MPolyfold Polyfold.EpGroupoid Set Module Submodule Filter Topology
open scoped ContDiff

set_option maxSynthPendingDepth 3

/-- The project's statement (no universe parameters). -/
def A : Prop :=
  (type_of% @Polyfold.example_9_3_5_count) ∧
  (type_of% @Polyfold.example935Theta_isBranched) ∧
  (type_of% @Polyfold.example_9_3_5) ∧
  (type_of% @Polyfold.example_9_3_5_rn) ∧
  (type_of% @Polyfold.example_9_3_5_eq_origin) ∧
  (type_of% @Polyfold.example_9_3_5_ne_of_pos) ∧
  (type_of% @Polyfold.example_9_3_5_cannot_coincide) ∧
  (type_of% @Polyfold.example_9_3_5_eq_of_neg) ∧
  (type_of% @Polyfold.orientedLift1_injective) ∧
  (type_of% @Polyfold.exampleT2_ne_orientedLift1) ∧
  (type_of% @Polyfold.exists_goodSet_exampleT1_ne_exampleT2)

theorem A_holds : A :=
  ⟨@Polyfold.example_9_3_5_count, @Polyfold.example935Theta_isBranched, @Polyfold.example_9_3_5, @Polyfold.example_9_3_5_rn, @Polyfold.example_9_3_5_eq_origin, @Polyfold.example_9_3_5_ne_of_pos, @Polyfold.example_9_3_5_cannot_coincide, @Polyfold.example_9_3_5_eq_of_neg, @Polyfold.orientedLift1_injective, @Polyfold.exampleT2_ne_orientedLift1, @Polyfold.exists_goodSet_exampleT1_ne_exampleT2⟩


/-! ### `A` at `B`'s instance `β = betaPP`: parts (b), (d) and the first half of (a) -/

section Instance

theorem G1_betaPP (b : Bool) : G1 betaPP b = beta1 b := by cases b <;> rfl

theorem G2_betaPP (b : Bool) : G2 betaPP b = beta2 b := by
  funext s
  cases b
  · by_cases hs : s ≤ 0
    · simp only [G2, if_pos hs, beta2, cond_false, betaMP_of_nonpos hs, betaMM]
    · simp only [G2, if_neg hs, beta2, cond_false, betaMP_of_pos (lt_of_not_ge hs)]
  · by_cases hs : s ≤ 0
    · simp only [G2, if_pos hs, beta2, cond_true, betaPM_of_nonpos hs]
    · simp only [G2, if_neg hs, beta2, cond_true, betaPM_of_pos (lt_of_not_ge hs), betaMM]

theorem signB_eq_boolSign (b : Bool) : signB b = boolSign b := by cases b <;> rfl

/-- `B`'s oriented sums are the project's, for equal graphs and equal signs. -/
theorem liftB_eq (G G' : Bool → ℝ → ℝ) (hGG : ∀ b, G b = G' b)
    (hG : ∀ b, ContDiff ℝ (⊤ : ℕ∞) (G b)) (hG' : ∀ b, ContDiff ℝ ∞ (G' b)) (ε : Bool → Bool) :
    liftB G hG ε = orientedSumRn (fun b => graph2 (G' b)) (fun _ => 1)
      (fun b => graphOrientation (hG' b) (boolSign (ε b)) (boolSign_ne_zero _)) := by
  have h : G = G' := funext hGG
  subst h
  funext y
  unfold liftB orientedSumRn
  refine Finset.sum_congr rfl fun b _ => ?_
  change Finsupp.single (⟨1, _, graphFrames (G b) (signB (ε b)) y⟩ : (rnPolyfold 2).OrTangent) 1 =
    Finsupp.single ⟨1, _, graphFrames (G b) (boolSign (ε b)) y⟩ 1
  rw [signB_eq_boolSign]

theorem liftB1_eq (h1 : ∀ b, ContDiff ℝ (⊤ : ℕ∞) (G1 betaPP b)) (ε : Bool → Bool) :
    liftB (G1 betaPP) h1 ε = orientedLift1 ε :=
  liftB_eq _ _ G1_betaPP h1 contDiff_beta1 ε

theorem liftB2_eq (h2 : ∀ b, ContDiff ℝ (⊤ : ℕ∞) (G2 betaPP b)) (ε : Bool → Bool) :
    liftB (G2 betaPP) h2 ε = orientedLift2 ε :=
  liftB_eq _ _ G2_betaPP h2 contDiff_beta2 ε

open Classical in
theorem ThetaB_betaPP : ThetaB betaPP = example935Theta := by
  funext p
  unfold ThetaB example935Theta
  rw [Finset.sum_const, nsmul_eq_mul, mul_one]
  congr 3

/-- A project orientation is one in `B`'s sense (as in `RoundTrip/Items/V9_32.lean`). -/
theorem isOrientationB_of_isOrientation {Θ : (Fin 2 → ℝ) → ℚ}
    {T : (Fin 2 → ℝ) → (rnPolyfold 2).OrTangent →₀ ℚ} (h : X2.IsOrientation Θ T) :
    IsOrientationB X2 Θ T where
  mem x hx := h.mem x hx
  functor φ hφ := h.natural φ hφ
  lifts x hx := h.lifts x hx
  locRep x hx := by
    obtain ⟨OB, hOB⟩ := h.locallyOriented x hx
    exact ⟨OB.toLocalBranchingStructure, OB.dim, OB.orient, hOB⟩

theorem isOrientationB_congr {Θ : (Fin 2 → ℝ) → ℚ}
    {T T' : (Fin 2 → ℝ) → (rnPolyfold 2).OrTangent →₀ ℚ} (h : T = T')
    (hT : IsOrientationB X2 Θ T) : IsOrientationB X2 Θ T' := h ▸ hT

/-- Parts of `B` at `β = betaPP`: (a) `Θ` branched and given by the second structure, (b) in
full, (d) in full. -/
def B_betaPP_part : Prop :=
  open Classical in
  ∀ (h1 : ∀ b, ContDiff ℝ (⊤ : ℕ∞) (G1 betaPP b)) (h2 : ∀ b, ContDiff ℝ (⊤ : ℕ∞) (G2 betaPP b)),
    (X2.IsBranchedEpSubgroupoid (ThetaB betaPP) ∧
      ∀ p, ThetaB betaPP p =
        ((Finset.univ.filter (fun b : Bool => p ∈ graph2 (G2 betaPP b))).card : ℚ)) ∧
    (IsOrientationB X2 (ThetaB betaPP) (liftB (G1 betaPP) h1 id) ∧
      IsOrientationB X2 (ThetaB betaPP) (liftB (G2 betaPP) h2 id) ∧
      liftB (G1 betaPP) h1 id 0 = liftB (G2 betaPP) h2 id 0 ∧
      ∃ y, liftB (G1 betaPP) h1 id y ≠ liftB (G2 betaPP) h2 id y) ∧
    (∃ ε, ∀ ε', liftB (G1 betaPP) h1 ε ≠ liftB (G2 betaPP) h2 ε')

/-- `B_betaPP_part` is implied by `B` (it is `B` at `β = betaPP`, minus some conjuncts). -/
theorem B_to_B_betaPP_part : B → B_betaPP_part := fun hB h1 h2 => by
  obtain ⟨⟨ha1, ha2, -, -⟩, hb, -, hd⟩ := hB betaPP betaPP_zero (fun _ hs => betaPP_pos hs) h1 h2
  exact ⟨⟨ha1, ha2⟩, hb, hd⟩

open Classical in
/-- **`A` gives `B` at `β = betaPP`**, parts (a) (first half), (b), (d). -/
theorem A_to_B_betaPP_part : A → B_betaPP_part := by
  intro hA h1 h2
  obtain ⟨hcount, hbr, -, hrn, horig, hne, hcc, -, -, -, -⟩ := hA
  have e1 := liftB1_eq h1
  have e2 := liftB2_eq h2
  refine ⟨⟨?_, fun p => ?_⟩, ⟨?_, ?_, (congrFun (e1 id) 0).trans
    (horig.trans (congrFun (e2 id) 0).symm), ⟨ptPP 1, fun h => hne one_pos
      ((congrFun (e1 id) _).symm.trans (h.trans (congrFun (e2 id) _)))⟩⟩, ⟨id, fun ε' h => ?_⟩⟩
  · rw [ThetaB_betaPP]; exact hbr
  · rw [ThetaB_betaPP]
    unfold example935Theta
    rw [hcount p, Finset.sum_const, nsmul_eq_mul, mul_one]
    congr 3
    funext b
    rw [G2_betaPP]
  · have h := isOrientationB_of_isOrientation hrn.2.1
    rw [← ThetaB_betaPP] at h
    exact isOrientationB_congr (e1 id).symm h
  · have h := isOrientationB_of_isOrientation hrn.2.2.1
    rw [← ThetaB_betaPP] at h
    exact isOrientationB_congr (e2 id).symm h
  · have h' : orientedLift1 id = orientedLift2 ε' := (e1 id).symm.trans (h.trans (e2 ε'))
    rcases hcc ε' one_pos with h'' | h''
    · exact h'' (congrFun h' (ptPP 1)).symm
    · exact h'' (congrFun h' (ptMM (-1))).symm

end Instance

/-! ### Copies of the project's proofs (renamed `…_c`) -/

open scoped Classical in
/-- **The count identity of Example 9.3.5**: `|{i ∈ {++, --} | (x, y) ∈ Gᵢ}| =
|{j ∈ {+-, -+} | (x, y) ∈ Gⱼ}|` for all `(x, y) ∈ ℝ²`. -/
theorem example_9_3_5_count_c (y : Fin 2 → ℝ) :
    (∑ b with y ∈ graph2 (beta1 b), (1 : ℚ)) = ∑ b with y ∈ graph2 (beta2 b), (1 : ℚ) := by
  rw [Finset.sum_filter, Finset.sum_filter, Fintype.sum_bool, Fintype.sum_bool]
  by_cases hs : y 0 ≤ 0
  · have h1 : y ∈ graph2 (beta2 true) ↔ y ∈ graph2 (beta1 true) := by
      change y 1 = betaPM (y 0) ↔ y 1 = betaPP (y 0)
      rw [betaPM_of_nonpos hs]
    have h2 : y ∈ graph2 (beta2 false) ↔ y ∈ graph2 (beta1 false) := by
      change y 1 = betaMP (y 0) ↔ y 1 = betaMM (y 0)
      rw [betaMP_of_nonpos hs]
    by_cases ha : y ∈ graph2 (beta1 true) <;> by_cases hb : y ∈ graph2 (beta1 false) <;>
      simp [ha, hb, h1, h2]
  · have hs' : 0 < y 0 := lt_of_not_ge hs
    have h1 : y ∈ graph2 (beta2 true) ↔ y ∈ graph2 (beta1 false) := by
      change y 1 = betaPM (y 0) ↔ y 1 = betaMM (y 0)
      rw [betaPM_of_pos hs']
    have h2 : y ∈ graph2 (beta2 false) ↔ y ∈ graph2 (beta1 true) := by
      change y 1 = betaMP (y 0) ↔ y 1 = betaPP (y 0)
      rw [betaMP_of_pos hs']
    by_cases ha : y ∈ graph2 (beta1 true) <;> by_cases hb : y ∈ graph2 (beta1 false) <;>
      simp [ha, hb, h1, h2]

open scoped Classical in
/-- `Θ` is also `|{j ∈ {+-, -+} | (x, y) ∈ Gⱼ}|`. -/
theorem example935Theta_eq_two_c :
    example935Theta = fun y => ∑ b with y ∈ graph2 (beta2 b), (1 : ℚ) :=
  funext example_9_3_5_count_c

/-- **`Θ` is a branched ep⁺-subgroupoid** of the trivial ep-groupoid of `ℝ²`, of dimension `1`. -/
theorem example935Theta_isBranched_c :
    (trivial (rnPolyfold 2)).IsBranchedEpSubgroupoid example935Theta :=
  isBranchedEpSubgroupoid_sum_rn (fun b => graph2 (beta1 b)) (fun _ => 1) (fun _ => one_pos)
    (fun b => (rnPolyfold_isSubmanifoldOfDim_graph2 (contDiff_beta1 b)).1)
    (fun b => isClosed_graph2 (contDiff_beta1 b).continuous)

theorem orientedLift1_isOrientation_c
    (hind : (trivial (rnPolyfold 2)).HasIndependentTangentSums example935Theta)
    (ε : Bool → Bool) :
    (trivial (rnPolyfold 2)).IsOrientation example935Theta (orientedLift1 ε) :=
  isOrientation_sum_rn (fun b => graph2 (beta1 b)) (fun _ => 1) (fun _ => one_pos)
    (fun b => rnPolyfold_isSubmanifoldOfDim_graph2 (contDiff_beta1 b))
    (fun b => isClosed_graph2 (contDiff_beta1 b).continuous) (orient1 ε) hind

theorem orientedLift2_isOrientation_c
    (hind : (trivial (rnPolyfold 2)).HasIndependentTangentSums example935Theta)
    (ε : Bool → Bool) :
    (trivial (rnPolyfold 2)).IsOrientation example935Theta (orientedLift2 ε) :=
  isOrientation_sum_rn' (fun b => graph2 (beta2 b)) (fun _ => 1) (fun _ => one_pos)
    (fun b => rnPolyfold_isSubmanifoldOfDim_graph2 (contDiff_beta2 b))
    (fun b => isClosed_graph2 (contDiff_beta2 b).continuous) (orient2 ε)
    example935Theta_eq_two_c hind


theorem example_9_3_5_eq_origin_c : exampleT1 0 = exampleT2 0 := by
  rw [exampleT1, exampleT2, orientedLift1, orientedLift2, orientedSumRn_bool, orientedSumRn_bool,
    if_pos (zero_mem_graph2_beta1 true), if_pos (zero_mem_graph2_beta1 false),
    if_pos (zero_mem_graph2_beta2 true), if_pos (zero_mem_graph2_beta2 false)]
  congr 1
  · exact congrArg (fun g => Finsupp.single g ((fun _ => (1 : ℚ)) true))
      (graphOrientation_tangent_eq (contDiff_beta1 true) (contDiff_beta2 true) (boolSign_ne_zero _)
        (zero_mem_graph2_beta1 true) (zero_mem_graph2_beta2 true)
        ((deriv_beta1_zero true).trans (deriv_beta2_zero true).symm))
  · exact congrArg (fun g => Finsupp.single g ((fun _ => (1 : ℚ)) false))
      (graphOrientation_tangent_eq (contDiff_beta1 false) (contDiff_beta2 false)
        (boolSign_ne_zero _)
        (zero_mem_graph2_beta1 false) (zero_mem_graph2_beta2 false)
        ((deriv_beta1_zero false).trans (deriv_beta2_zero false).symm))

/-- **Example 9.3.5, "otherwise different", does not hold as we read it**: the two orientations
also coincide at every point `(s, t)` with `s < 0` (there `G⁺⁻ = G⁺⁺` and `G⁻⁺ = G⁻⁻`, with the
same orientations). -/
theorem example_9_3_5_eq_of_neg_c {z : Fin 2 → ℝ} (hz : z 0 < 0) : exampleT1 z = exampleT2 z := by
  have h1 : z ∈ graph2 (beta2 true) ↔ z ∈ graph2 (beta1 true) := by
    change z 1 = betaPM (z 0) ↔ z 1 = betaPP (z 0)
    rw [betaPM_of_nonpos hz.le]
  have h2 : z ∈ graph2 (beta2 false) ↔ z ∈ graph2 (beta1 false) := by
    change z 1 = betaMP (z 0) ↔ z 1 = betaMM (z 0)
    rw [betaMP_of_nonpos hz.le]
  have d1 : deriv (beta1 true) (z 0) = deriv (beta2 true) (z 0) :=
    deriv_eq_of_eqOn_Iio (fun t ht => (betaPM_of_nonpos ht.le).symm) hz
  have d2 : deriv (beta1 false) (z 0) = deriv (beta2 false) (z 0) :=
    deriv_eq_of_eqOn_Iio (fun t ht => (betaMP_of_nonpos ht.le).symm) hz
  rw [exampleT1, exampleT2, orientedLift1, orientedLift2, orientedSumRn_bool, orientedSumRn_bool]
  congr 1
  · by_cases ha : z ∈ graph2 (beta1 true)
    · rw [if_pos ha, if_pos (h1.2 ha)]
      exact congrArg (fun g => Finsupp.single g ((fun _ => (1 : ℚ)) true))
        (graphOrientation_tangent_eq (contDiff_beta1 true) (contDiff_beta2 true)
          (boolSign_ne_zero _)
          ha (h1.2 ha) d1)
    · rw [if_neg ha, if_neg fun h => ha (h1.1 h)]
  · by_cases ha : z ∈ graph2 (beta1 false)
    · rw [if_pos ha, if_pos (h2.2 ha)]
      exact congrArg (fun g => Finsupp.single g ((fun _ => (1 : ℚ)) false))
        (graphOrientation_tangent_eq (contDiff_beta1 false) (contDiff_beta2 false)
          (boolSign_ne_zero _)
          ha (h2.2 ha) d2)
    · rw [if_neg ha, if_neg fun h => ha (h2.1 h)]


theorem example_9_3_5_ne_of_pos_c {s : ℝ} (hs : 0 < s) :
    exampleT1 (ptPP s) ≠ exampleT2 (ptPP s) := by
  rw [exampleT1, exampleT2, orientedLift1_ptPP id hs.ne', orientedLift2_ptPP_of_pos id hs]
  intro h
  exact graphOrientation_tangent_ne' contDiff_betaPP (b := true) (b' := false) (by decide)
    (ptPP_mem s) ((Finsupp.single_left_inj one_ne_zero).1 h)

/-- **The sign choices of the first structure give four different orientations** (the text's
"four different possibilities to orient", Example 9.3.5). -/
theorem orientedLift1_injective_c : Function.Injective orientedLift1 := by
  intro ε ε' h
  funext b
  by_contra hb
  cases b
  · have h1 := congrFun h (ptMM 1)
    rw [orientedLift1_ptMM ε one_ne_zero, orientedLift1_ptMM ε' one_ne_zero] at h1
    exact graphOrientation_tangent_ne' (contDiff_beta1 false) hb (ptMM_mem 1)
      ((Finsupp.single_left_inj one_ne_zero).1 h1)
  · have h1 := congrFun h (ptPP 1)
    rw [orientedLift1_ptPP ε one_ne_zero, orientedLift1_ptPP ε' one_ne_zero] at h1
    exact graphOrientation_tangent_ne' (contDiff_beta1 true) hb (ptPP_mem 1)
      ((Finsupp.single_left_inj one_ne_zero).1 h1)

/-- **Example 9.3.5, "four different possibilities", does not hold as we read it**: the text's
second orientation `T̂²` is none of the four orientations of the first structure
(`orientedLift1_injective_c`), so `Θ` has at least five orientations with weights `1` (and infinitely
many with fractional weights, as in Remark 9.3.3). -/
theorem exampleT2_ne_orientedLift1_c (ε : Bool → Bool) : exampleT2 ≠ orientedLift1 ε := by
  intro h
  have hp := congrFun h (ptPP 1)
  have hm := congrFun h (ptPP (-1))
  rw [exampleT2, orientedLift2_ptPP_of_pos id one_pos, orientedLift1_ptPP ε one_ne_zero] at hp
  rw [exampleT2, orientedLift2_ptPP_of_neg id (by norm_num),
    orientedLift1_ptPP ε (by norm_num)] at hm
  have hp' := (Finsupp.single_left_inj one_ne_zero).1 hp
  have hm' := (Finsupp.single_left_inj one_ne_zero).1 hm
  cases hε : ε true
  · exact graphOrientation_tangent_ne' contDiff_betaPP (b := true) (b' := false) (by decide)
      (ptPP_mem (-1)) (by rw [← hε]; exact hm')
  · exact graphOrientation_tangent_ne' contDiff_betaPP (b := false) (b' := true) (by decide)
      (ptPP_mem 1) (by rw [← hε]; exact hp')

/-- **Example 9.3.5, last claim**: no choice of signs `δ` orients the second structure
`G⁺⁻, G⁻⁺` so as to coincide with `T̂¹`, even near `(0, 0)`: for every `s > 0` they differ at
`(s, β⁺⁺(s))` or at `(-s, β⁻⁻(-s))`. -/
theorem example_9_3_5_cannot_coincide_c (δ : Bool → Bool) {s : ℝ} (hs : 0 < s) :
    orientedLift2 δ (ptPP s) ≠ exampleT1 (ptPP s) ∨
      orientedLift2 δ (ptMM (-s)) ≠ exampleT1 (ptMM (-s)) := by
  by_contra h
  push Not at h
  obtain ⟨h1, h2⟩ := h
  rw [orientedLift2_ptPP_of_pos δ hs, exampleT1, orientedLift1_ptPP id hs.ne'] at h1
  rw [orientedLift2_ptMM_of_neg δ (neg_neg_of_pos hs), exampleT1,
    orientedLift1_ptMM id (neg_ne_zero.2 hs.ne')] at h2
  have h1' := (Finsupp.single_left_inj one_ne_zero).1 h1
  have h2' := (Finsupp.single_left_inj one_ne_zero).1 h2
  cases hδ : δ false
  · rw [hδ] at h1'
    exact graphOrientation_tangent_ne' contDiff_betaPP (b := false) (b' := true) (by decide)
      (ptPP_mem s) h1'
  · rw [hδ] at h2'
    exact graphOrientation_tangent_ne' contDiff_betaMM (b := true) (b' := false) (by decide)
      (ptMM_mem (-s)) h2'

/-- **Example 9.3.5, 2021 p. 425 (2017: Example 9.1)**, the claims that hold as we read them:
`Θ` is a branched ep⁺-subgroupoid; `G⁺⁺, G⁻⁻` and `G⁺⁻, G⁻⁺`, oriented by `±(1, 0)` at `(0, 0)`,
give two orientations `T̂¹`, `T̂²` (given Theorem 9.2.1's independence for `Θ`), which coincide at
`(0, 0)` and differ at the points `(s, β⁺⁺(s))`, `s > 0`; and no orientation of the second
structure coincides with `T̂¹` near `(0, 0)`. -/
theorem example_9_3_5_c
    (hind : (trivial (rnPolyfold 2)).HasIndependentTangentSums example935Theta) :
    (trivial (rnPolyfold 2)).IsBranchedEpSubgroupoid example935Theta ∧
    (trivial (rnPolyfold 2)).IsOrientation example935Theta exampleT1 ∧
    (trivial (rnPolyfold 2)).IsOrientation example935Theta exampleT2 ∧
    exampleT1 0 = exampleT2 0 ∧
    (∀ s : ℝ, 0 < s → exampleT1 (ptPP s) ≠ exampleT2 (ptPP s)) ∧
    ∀ (δ : Bool → Bool) (s : ℝ), 0 < s →
      orientedLift2 δ (ptPP s) ≠ exampleT1 (ptPP s) ∨
        orientedLift2 δ (ptMM (-s)) ≠ exampleT1 (ptMM (-s)) :=
  ⟨example935Theta_isBranched_c, orientedLift1_isOrientation_c hind id,
    orientedLift2_isOrientation_c hind id, example_9_3_5_eq_origin_c,
    fun _ hs => example_9_3_5_ne_of_pos_c hs, fun δ _ hs => example_9_3_5_cannot_coincide_c δ hs⟩

/-- The oriented lifts of Example 9.3.5 are `1`-dimensional orientations. -/
theorem orientedLift1_isOrientationOfDim_c
    (hind : (trivial (rnPolyfold 2)).HasIndependentTangentSums example935Theta)
    (ε : Bool → Bool) :
    (trivial (rnPolyfold 2)).IsOrientationOfDim example935Theta 1 (orientedLift1 ε) :=
  isOrientationOfDim_sum_rn (fun b => graph2 (beta1 b)) (fun _ => 1) (fun _ => one_pos)
    (fun b => rnPolyfold_isSubmanifoldOfDim_graph2 (contDiff_beta1 b))
    (fun b => isClosed_graph2 (contDiff_beta1 b).continuous) (orient1 ε) rfl hind

theorem orientedLift2_isOrientationOfDim_c
    (hind : (trivial (rnPolyfold 2)).HasIndependentTangentSums example935Theta)
    (ε : Bool → Bool) :
    (trivial (rnPolyfold 2)).IsOrientationOfDim example935Theta 1 (orientedLift2 ε) :=
  isOrientationOfDim_sum_rn (fun b => graph2 (beta2 b)) (fun _ => 1) (fun _ => one_pos)
    (fun b => rnPolyfold_isSubmanifoldOfDim_graph2 (contDiff_beta2 b))
    (fun b => isClosed_graph2 (contDiff_beta2 b).continuous) (orient2 ε)
    example935Theta_eq_two_c hind

/-- The lift `T̂¹` of Example 9.3.5 is a `1`-dimensional orientation (independence
discharged). -/
theorem orientedLift1_isOrientationOfDim_rn_c (ε : Bool → Bool) :
    (trivial (rnPolyfold 2)).IsOrientationOfDim example935Theta 1 (orientedLift1 ε) :=
  orientedLift1_isOrientationOfDim_c (hasIndependentTangentSums_rn rfl _) ε

/-- The lift `T̂²` of Example 9.3.5 is a `1`-dimensional orientation (independence
discharged). -/
theorem orientedLift2_isOrientationOfDim_rn_c (ε : Bool → Bool) :
    (trivial (rnPolyfold 2)).IsOrientationOfDim example935Theta 1 (orientedLift2 ε) :=
  orientedLift2_isOrientationOfDim_c (hasIndependentTangentSums_rn rfl _) ε

/-- **Example 9.3.5, 2021 p. 425 (2017: Example 9.1)**, the claims of `example_9_3_5_c` with
Theorem 9.2.1's independence discharged: `Θ` is a branched ep⁺-subgroupoid with the two
orientations `T̂¹`, `T̂²`, equal at `0` and different at `(s, β⁺⁺(s))`, `s > 0`, and no lift
`T̂²_δ` equals `T̂¹` on both branches. -/
theorem example_9_3_5_rn_c :
    (trivial (rnPolyfold 2)).IsBranchedEpSubgroupoid example935Theta ∧
    (trivial (rnPolyfold 2)).IsOrientation example935Theta exampleT1 ∧
    (trivial (rnPolyfold 2)).IsOrientation example935Theta exampleT2 ∧
    exampleT1 0 = exampleT2 0 ∧
    (∀ s : ℝ, 0 < s → exampleT1 (ptPP s) ≠ exampleT2 (ptPP s)) ∧
    ∀ (δ : Bool → Bool) (s : ℝ), 0 < s →
      orientedLift2 δ (ptPP s) ≠ exampleT1 (ptPP s) ∨
        orientedLift2 δ (ptMM (-s)) ≠ exampleT1 (ptMM (-s)) :=
  example_9_3_5_c (hasIndependentTangentSums_rn rfl _)


/-- **Lemma 9.3.4 applied to Example 9.3.5**: since the orientations `T̂¹`, `T̂²` differ at
`(s, β⁺⁺(s))`, `s > 0`, they differ at some good point of `Θ`. -/
theorem exists_goodSet_exampleT1_ne_exampleT2_c :
    ∃ y ∈ (trivial (rnPolyfold 2)).goodSet example935Theta, exampleT1 y ≠ exampleT2 y := by
  by_contra h
  push Not at h
  have hsm : ptPP 1 ∈ (trivial (rnPolyfold 2)).PObj.smoothSet :=
    mem_iInter.2 fun k => by
      change ptPP 1 ∈ (rnPolyfold 2).levelSet k
      rw [rnPolyfold_levelSet]; exact mem_univ _
  exact example_9_3_5_ne_of_pos_c one_pos (lemma_9_3_4_rn rfl example935Theta_isBranched_c
    (orientedLift1_isOrientationOfDim_rn_c id) (orientedLift2_isOrientationOfDim_rn_c id) h _ hsm)

/-- `B → A`, by re-proving `A` outright (`A`'s pointwise claims about `betaPP` are not
consequences of `B`). -/
theorem B_to_A : B → A := fun _ =>
  ⟨@example_9_3_5_count_c, @example935Theta_isBranched_c, @example_9_3_5_c, @example_9_3_5_rn_c, @example_9_3_5_eq_origin_c, @example_9_3_5_ne_of_pos_c, @example_9_3_5_cannot_coincide_c, @example_9_3_5_eq_of_neg_c, @orientedLift1_injective_c, @exampleT2_ne_orientedLift1_c, @exists_goodSet_exampleT1_ne_exampleT2_c⟩

#rt_check RoundTrip.V9_33.A_to_B_betaPP_part [Polyfold.example_9_3_5_count, Polyfold.example935Theta_isBranched, Polyfold.example_9_3_5, Polyfold.example_9_3_5_rn, Polyfold.example_9_3_5_eq_origin, Polyfold.example_9_3_5_ne_of_pos, Polyfold.example_9_3_5_cannot_coincide, Polyfold.example_9_3_5_eq_of_neg, Polyfold.orientedLift1_injective, Polyfold.exampleT2_ne_orientedLift1, Polyfold.exists_goodSet_exampleT1_ne_exampleT2]
#rt_check RoundTrip.V9_33.B_to_A [Polyfold.example_9_3_5_count, Polyfold.example935Theta_isBranched, Polyfold.example_9_3_5, Polyfold.example_9_3_5_rn, Polyfold.example_9_3_5_eq_origin, Polyfold.example_9_3_5_ne_of_pos, Polyfold.example_9_3_5_cannot_coincide, Polyfold.example_9_3_5_eq_of_neg, Polyfold.orientedLift1_injective, Polyfold.exampleT2_ne_orientedLift1, Polyfold.exists_goodSet_exampleT1_ne_exampleT2]
#rt_overlap RoundTrip.V9_33.B_to_A [Polyfold.example_9_3_5_count, Polyfold.example935Theta_isBranched, Polyfold.example_9_3_5, Polyfold.example_9_3_5_rn, Polyfold.example_9_3_5_eq_origin, Polyfold.example_9_3_5_ne_of_pos, Polyfold.example_9_3_5_cannot_coincide, Polyfold.example_9_3_5_eq_of_neg, Polyfold.orientedLift1_injective, Polyfold.exampleT2_ne_orientedLift1, Polyfold.exists_goodSet_exampleT1_ne_exampleT2]

end RoundTrip.V9_33
