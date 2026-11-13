import Polyfold.Chapter9.GapP2_D2Example935Sheets

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021; 2017 arXiv 1707.08941),
§9.3, **Example 9.3.5**, p. 425 (2017: Example 9.1, p. 313): "In this case we have in fact four
different possibilities to orient."

# Example 9.3.5: all orientations of `Θ`

`supp(Θ) ∖ {0}` consists of four open arcs: `G⁺⁺` and `G⁻⁻` over `s > 0` and over `s < 0`.  An
orientation of `Θ` (Definition 9.3.2, rational weights) is, at a point `y` of an arc,
`a · (1, β') + (1 − a) · (−(1, β'))` (`Θ(y) = 1`), and at the origin
`A · (1, 0) + (2 − A) · (−1, 0)` (`Θ(0) = 2`).

## What is formalized

* `eq_classOrient`, `isOrientation_classOrient`, **`example_9_3_5_classification`**:
  the orientations of `Θ` are exactly the `classOrient a`, for `a : Bool → Bool → ℚ` (side of the
  origin, branch) with `0 ≤ a ≤ 1` and `a(+,G⁺⁺) + a(+,G⁻⁻) = a(−,G⁺⁺) + a(−,G⁻⁻)`; the weight at
  the origin is this common value; `classOrient_injective`: different `a` give different
  orientations.
  - The coefficient is constant along each arc (`coef_pt_eq_of_pos`, `coef_pt_eq_of_neg`): near a
    point of an arc every sheet of a local branching structure is the arc, oriented by a locally
    constant sign (`exists_isOpen_tangent_eq_orTan_iff`).
  - At the origin (`coef_zero_eq`): every sheet of a local branching structure meets each
    vertical line near `0` (`exists_mem_fst_eq`), and the count `Θ(s, β⁺⁺(s)) + Θ(s, β⁻⁻(s)) =
    2 = Θ(0)` forces it to meet it exactly once; with the sign constancy this gives
    `A = a(+,G⁺⁺) + a(+,G⁻⁻)`, and likewise for `s < 0`.
  - Conversely `classOrient a` is the oriented sum of the four graphs `G⁺⁺, G⁻⁻, G⁺⁻, G⁻⁺` with
    both orientations and weights solving a `2 × 2` transport problem (`exists_transport`).
* `example_9_3_5_infinite`: `Θ` has infinitely many orientations.
* **`example_9_3_5_integral`**: the orientations with integer weights are exactly the six sign
  choices on the two structures of the text (`range orientedLift1 ∪ range orientedLift2`,
  `ncard_signOrientations`).

## Comparison with the text

"Four different possibilities to orient" holds for each of the two structures separately; for
`Θ` it does not hold as we read it: with rational weights there are infinitely many orientations,
a three-dimensional family (`example_9_3_5_classification`), and with integer weights six
(`example_9_3_5_integral`).
-/

set_option maxSynthPendingDepth 3

open Set Module Submodule Filter Topology
open scoped ContDiff Classical

noncomputable section

namespace Polyfold

open MPolyfold EpGroupoid

namespace Ex935

theorem mem_smoothSet (y : Fin 2 → ℝ) : y ∈ (trivial (rnPolyfold 2)).PObj.smoothSet :=
  mem_iInter.2 fun k => by
    change y ∈ (rnPolyfold 2).levelSet k
    rw [rnPolyfold_levelSet]; exact mem_univ _

/-- The coefficient of `orTan true y = (1, β'(y₀))` in `T(y)`. -/
def coef (T : (Fin 2 → ℝ) → (rnPolyfold 2).OrTangent →₀ ℚ) (y : Fin 2 → ℝ) : ℚ :=
  T y (orTan true y)

/-- A formal sum of the two oriented tangent lines at `y`. -/
theorem sum_single_eq {ι : Type*} (s : Finset ι) (g : ι → (rnPolyfold 2).OrTangent) (σ : ι → ℚ)
    {y : Fin 2 → ℝ} (hg : ∀ i ∈ s, g i = orTan true y ∨ g i = orTan false y) :
    ∑ i ∈ s, Finsupp.single (g i) (σ i) =
      Finsupp.single (orTan true y) (∑ i ∈ s.filter (fun i => g i = orTan true y), σ i) +
      Finsupp.single (orTan false y) (∑ i ∈ s.filter (fun i => g i ≠ orTan true y), σ i) := by
  rw [← Finset.sum_filter_add_sum_filter_not s (fun i => g i = orTan true y),
    Finsupp.single_finsetSum, Finsupp.single_finsetSum]
  congr 1
  · exact Finset.sum_congr rfl fun i hi => by rw [(Finset.mem_filter.1 hi).2]
  · refine Finset.sum_congr rfl fun i hi => ?_
    obtain ⟨his, hne⟩ := Finset.mem_filter.1 hi
    rw [(hg i his).resolve_left hne]

theorem single_add_single_apply_true {y : Fin 2 → ℝ} (hy : y ∈ Z) (c d : ℚ) :
    (Finsupp.single (orTan true y) c + Finsupp.single (orTan false y) d) (orTan true y) = c := by
  simp [(orTan_ne hy).symm]

theorem single_add_single_apply_false {y : Fin 2 → ℝ} (hy : y ∈ Z) (c d : ℚ) :
    (Finsupp.single (orTan true y) c + Finsupp.single (orTan false y) d) (orTan false y) = d := by
  simp [orTan_ne hy]

/-- If every index satisfies `p` or `q` and the weights of `p` and of `q` add up to the total,
no index satisfies both. -/
theorem not_and_of_sum_eq {ι : Type*} [Fintype ι] (σ : ι → ℚ) (hσ : ∀ i, 0 < σ i)
    (p q : ι → Prop) (hpq : ∀ i, p i ∨ q i)
    (h : (∑ i, if p i then σ i else 0) + (∑ i, if q i then σ i else 0) = ∑ i, σ i) (i : ι) :
    ¬ (p i ∧ q i) := by
  intro hi
  rw [← Finset.sum_add_distrib] at h
  have hlt : ∑ j, σ j < ∑ j, ((if p j then σ j else 0) + (if q j then σ j else 0)) := by
    refine Finset.sum_lt_sum (fun j _ => ?_) ⟨i, Finset.mem_univ _, ?_⟩
    · rcases hpq j with hj | hj
      · rw [if_pos hj]; split_ifs <;> linarith [hσ j]
      · rw [if_pos hj]; split_ifs <;> linarith [hσ j]
    · rw [if_pos hi.1, if_pos hi.2]; linarith [hσ i]
  linarith

/-! ### Oriented local branching structures of `Θ` -/

section Structure

variable {x : Fin 2 → ℝ} (B : (trivial (rnPolyfold 2)).OrientedBranchingStructure example935Theta x)

theorem sheet_subset_Z (i : B.ι) : B.M i ⊆ Z := fun y hy => by
  rw [← supp_example935Theta]
  exact (B.toLocalBranchingStructure.mem_supp_iff (B.subset_U i hy)).2 ⟨i, hy⟩

theorem sheet_dim (i : B.ι) : (rnPolyfold 2).IsSubmanifoldOfDim (B.M i) 1 :=
  B.toLocalBranchingStructure.isOfDim_of_isNDimensional example935Theta_isNDimensional i

theorem sheet_dim_eq (i : B.ι) : B.dim i = 1 :=
  (B.isSubmanifoldOfDim i).eq_of_hasDimAt ((sheet_dim B i).2 x (B.mem_M i))

/-- The oriented sum of a structure at a point `y ∈ supp(Θ)`. -/
theorem orientedSum_eq {y : Fin 2 → ℝ} : B.orientedSum y =
    Finsupp.single (orTan true y) (∑ i ∈ Finset.univ.filter
      (fun i => y ∈ B.M i ∧ (B.orient i).tangent y = orTan true y), B.σ i) +
    Finsupp.single (orTan false y) (∑ i ∈ Finset.univ.filter
      (fun i => y ∈ B.M i ∧ (B.orient i).tangent y ≠ orTan true y), B.σ i) := by
  rw [OrientedBranchingStructure.orientedSum]
  refine (sum_single_eq (y := y) _ _ _ (fun i hi =>
    tangent_eq_orTan_or (sheet_dim B i) (sheet_subset_Z B i) (B.orient i) (sheet_dim_eq B i)
      (Finset.mem_filter.1 hi).2)).trans ?_
  rw [Finset.filter_filter, Finset.filter_filter]
  congr

theorem sum_add_sum_eq {y : Fin 2 → ℝ} (hyU : y ∈ B.U) :
    (∑ i ∈ Finset.univ.filter
      (fun i => y ∈ B.M i ∧ (B.orient i).tangent y = orTan true y), B.σ i) +
    (∑ i ∈ Finset.univ.filter
      (fun i => y ∈ B.M i ∧ (B.orient i).tangent y ≠ orTan true y), B.σ i) =
      example935Theta y := by
  rw [B.eq_sum y hyU, ← Finset.filter_filter, ← Finset.filter_filter,
    Finset.sum_filter_add_sum_filter_not]

/-- If `Θ(z) = Θ(x)` then every sheet of a structure at `x` contains `z`. -/
theorem mem_M_of_eq {z : Fin 2 → ℝ} (hzU : z ∈ B.U) (h : example935Theta z = example935Theta x)
    (i : B.ι) : z ∈ B.M i := by
  by_contra hi
  have hx : example935Theta x = ∑ j, B.σ j := by
    rw [B.eq_sum x B.mem_U, Finset.filter_true_of_mem fun j _ => B.mem_M j]
  have hlt : ∑ j ∈ Finset.univ.filter (fun j => z ∈ B.M j), B.σ j < ∑ j, B.σ j :=
    Finset.sum_lt_sum_of_subset (Finset.filter_subset _ _) (Finset.mem_univ i)
      (fun hm => hi (Finset.mem_filter.1 hm).2) (B.σ_pos i) fun j _ _ => (B.σ_pos j).le
  rw [← B.eq_sum z hzU, h, hx] at hlt
  exact lt_irrefl _ hlt

variable {T : (Fin 2 → ℝ) → (rnPolyfold 2).OrTangent →₀ ℚ}

/-- **The local formula**: near `x`, the coefficient of `(1, β')` in `T` is the total weight of
the sheets through the point that are positively oriented at `x`. -/
theorem eventually_coef_eq
    (hB : ∀ y ∈ B.U, y ∈ (trivial (rnPolyfold 2)).PObj.smoothSet → T y = B.orientedSum y) :
    ∀ᶠ z in 𝓝 x, z ∈ B.U ∧ (z ∈ Z → coef T z = ∑ i ∈ Finset.univ.filter
      (fun i => z ∈ B.M i ∧ (B.orient i).tangent x = orTan true x), B.σ i) := by
  have h : ∀ i, ∀ᶠ z in 𝓝 x, ∀ _ : z ∈ B.M i,
      ((B.orient i).tangent z = orTan true z ↔ (B.orient i).tangent x = orTan true x) := by
    intro i
    obtain ⟨O, hO, hxO, hOz⟩ := exists_isOpen_tangent_eq_orTan_iff (sheet_dim B i)
      (sheet_subset_Z B i) (B.orient i) (sheet_dim_eq B i) (B.mem_M i)
    filter_upwards [hO.mem_nhds hxO] with z hz hzM using hOz z ⟨hzM, hz⟩
  filter_upwards [Filter.eventually_all.2 h, B.isOpen_U.mem_nhds B.mem_U] with z hz hzU
  refine ⟨hzU, fun hzZ => ?_⟩
  rw [coef, hB z hzU (mem_smoothSet z), orientedSum_eq B, single_add_single_apply_true hzZ]
  exact Finset.sum_congr (Finset.filter_congr fun i _ => and_congr_right fun hi => hz i hi)
    fun _ _ => rfl

end Structure

/-! ### The normal form of an orientation -/

variable {T : (Fin 2 → ℝ) → (rnPolyfold 2).OrTangent →₀ ℚ}

/-- **At `y ∈ supp(Θ)` an orientation is `c · (1, β') + (Θ(y) − c) · (−(1, β'))`.** -/
theorem eq_single_add_single
    (hT : (trivial (rnPolyfold 2)).IsOrientation example935Theta T) {y : Fin 2 → ℝ}
    (hy : y ∈ Z) : T y = Finsupp.single (orTan true y) (coef T y) +
      Finsupp.single (orTan false y) (example935Theta y - coef T y) := by
  obtain ⟨B, hB⟩ := hT.locallyOriented y (by rw [supp_example935Theta]; exact hy)
  have hTy := hB y B.mem_U (mem_smoothSet y)
  have hs := sum_add_sum_eq B B.mem_U
  rw [coef, hTy, orientedSum_eq B, single_add_single_apply_true hy, ← hs, add_sub_cancel_left]

theorem coef_nonneg (hT : (trivial (rnPolyfold 2)).IsOrientation example935Theta T)
    (y : Fin 2 → ℝ) : 0 ≤ coef T y :=
  (hT.mem y (mem_smoothSet y)).1 _

theorem coef_le (hT : (trivial (rnPolyfold 2)).IsOrientation example935Theta T) {y : Fin 2 → ℝ}
    (hy : y ∈ Z) : coef T y ≤ example935Theta y := by
  have h : 0 ≤ T y (orTan false y) := (hT.mem y (mem_smoothSet y)).1 (orTan false y)
  rw [eq_single_add_single hT hy, single_add_single_apply_false hy] at h
  linarith

/-! ### The arcs -/

/-- The point `(s, β_b(s))` of `G_b`. -/
def pt (b : Bool) (s : ℝ) : Fin 2 → ℝ := ![s, beta1 b s]

@[simp] theorem pt_zero_apply (b : Bool) (s : ℝ) : pt b s 0 = s := rfl

theorem pt_mem (b : Bool) (s : ℝ) : pt b s ∈ graph2 (beta1 b) := by
  simp [mem_graph2_iff, pt]

theorem pt_mem_Z (b : Bool) (s : ℝ) : pt b s ∈ Z := mem_Z_iff.2 ⟨b, pt_mem b s⟩

theorem continuous_pt (b : Bool) : Continuous (pt b) := by
  refine continuous_pi fun i => ?_
  fin_cases i
  · exact continuous_id
  · exact (contDiff_beta1 b).continuous

theorem pt_at_zero (b : Bool) : pt b 0 = 0 := by
  funext i
  fin_cases i
  · rfl
  · cases b
    · simp [pt, beta1_false_apply, betaPP_zero]
    · simp [pt, beta1_true_apply, betaPP_zero]

theorem eq_pt_of_mem {b : Bool} {y : Fin 2 → ℝ} (hy : y ∈ graph2 (beta1 b)) : y = pt b (y 0) := by
  funext i
  fin_cases i
  · rfl
  · exact hy

theorem decide_pt {b : Bool} {s : ℝ} (hs : s ≠ 0) : decide (0 ≤ pt b s 1) = b := by
  have hp := betaPP_pos hs
  cases b
  · have : ¬ (0 ≤ pt false s 1) := by
      simp only [pt, Matrix.cons_val_one, Matrix.cons_val_zero, beta1_false_apply]; linarith
    simp [this]
  · have : 0 ≤ pt true s 1 := by
      simp only [pt, Matrix.cons_val_one, Matrix.cons_val_zero, beta1_true_apply]; linarith
    simp [this]

theorem theta_pt {b : Bool} {s : ℝ} (hs : s ≠ 0) : example935Theta (pt b s) = 1 :=
  example935Theta_eq_one (pt_mem_Z b s) hs

/-- **The coefficient is locally constant along an arc.** -/
theorem coef_eventually_eq (hT : (trivial (rnPolyfold 2)).IsOrientation example935Theta T)
    (b : Bool) {s₀ : ℝ} (hs₀ : s₀ ≠ 0) :
    ∀ᶠ s in 𝓝 s₀, coef T (pt b s) = coef T (pt b s₀) := by
  obtain ⟨B, hB⟩ := hT.locallyOriented (pt b s₀)
    (by rw [supp_example935Theta]; exact pt_mem_Z b s₀)
  have hloc := eventually_coef_eq B hB
  have hx := hloc.self_of_nhds
  have h1 := ((continuous_pt b).tendsto s₀).eventually hloc
  filter_upwards [h1, isOpen_ne.mem_nhds hs₀] with s hs hs0
  have hall := mem_M_of_eq B hs.1 (by rw [theta_pt hs0, theta_pt hs₀])
  rw [hs.2 (pt_mem_Z b s), hx.2 (pt_mem_Z b s₀)]
  exact Finset.sum_congr (Finset.filter_congr fun i _ =>
    and_congr_left fun _ => iff_of_true (hall i) (B.mem_M i)) fun _ _ => rfl

theorem coef_pt_eq_of_pos (hT : (trivial (rnPolyfold 2)).IsOrientation example935Theta T)
    (b : Bool) {s t : ℝ} (hs : 0 < s) (ht : 0 < t) : coef T (pt b s) = coef T (pt b t) :=
  isPreconnected_Ioi.induction₂ (fun s t => coef T (pt b s) = coef T (pt b t))
    (fun _ hs => ((coef_eventually_eq hT b (ne_of_gt hs)).filter_mono nhdsWithin_le_nhds).mono
      fun _ h => h.symm)
    (fun _ _ _ _ _ _ h₁ h₂ => h₁.trans h₂) (fun _ _ _ _ h => h.symm) hs ht

theorem coef_pt_eq_of_neg (hT : (trivial (rnPolyfold 2)).IsOrientation example935Theta T)
    (b : Bool) {s t : ℝ} (hs : s < 0) (ht : t < 0) : coef T (pt b s) = coef T (pt b t) :=
  isPreconnected_Iio.induction₂ (fun s t => coef T (pt b s) = coef T (pt b t))
    (fun _ hs => ((coef_eventually_eq hT b (ne_of_lt hs)).filter_mono nhdsWithin_le_nhds).mono
      fun _ h => h.symm)
    (fun _ _ _ _ _ _ h₁ h₂ => h₁.trans h₂) (fun _ _ _ _ h => h.symm) hs ht

/-- **At the origin**: for `s ≠ 0` near `0`, the coefficient at `(0, 0)` is the sum of the
coefficients at `(s, β⁺⁺(s))` and `(s, β⁻⁻(s))`. -/
theorem coef_zero_eq (hT : (trivial (rnPolyfold 2)).IsOrientation example935Theta T) :
    ∀ᶠ s in 𝓝 (0 : ℝ), s ≠ 0 → coef T 0 = coef T (pt true s) + coef T (pt false s) := by
  obtain ⟨B, hB⟩ := hT.locallyOriented 0
    (by rw [supp_example935Theta]; exact pt_at_zero true ▸ pt_mem_Z true 0)
  have hloc := eventually_coef_eq B hB
  have h0 := hloc.self_of_nhds
  have hball : ∀ᶠ s in 𝓝 (0 : ℝ), ∀ i, ∃ a ∈ B.M i, a 0 = s := by
    refine Filter.eventually_all.2 fun i => ?_
    obtain ⟨r, hr, h⟩ := exists_mem_fst_eq (sheet_dim B i) (sheet_subset_Z B i) (B.mem_M i)
    filter_upwards [Metric.ball_mem_nhds (0 : ℝ) hr] with s hs
    exact h s (by simpa [Real.dist_eq] using hs)
  have ht : ∀ b, Tendsto (pt b) (𝓝 0) (𝓝 0) := fun b =>
    (continuous_pt b).tendsto' 0 0 (pt_at_zero b)
  filter_upwards [hball, (ht true).eventually hloc, (ht false).eventually hloc] with s hs h1 h2 hs0
  -- every sheet contains `(s, β⁺⁺(s))` or `(s, β⁻⁻(s))`
  have hor : ∀ i, pt true s ∈ B.M i ∨ pt false s ∈ B.M i := by
    intro i
    obtain ⟨a, ha, has⟩ := hs i
    obtain ⟨b, hb⟩ := mem_Z_iff.1 (sheet_subset_Z B i ha)
    have := eq_pt_of_mem hb
    rw [has] at this
    cases b
    · exact Or.inr (this ▸ ha)
    · exact Or.inl (this ▸ ha)
  -- and not both
  have hsum : (∑ i, if pt true s ∈ B.M i then B.σ i else 0) +
      (∑ i, if pt false s ∈ B.M i then B.σ i else 0) = ∑ i, B.σ i := by
    rw [← Finset.sum_filter, ← Finset.sum_filter, ← B.eq_sum _ h1.1, ← B.eq_sum _ h2.1,
      theta_pt hs0, theta_pt hs0, ← Finset.filter_true_of_mem (s := Finset.univ)
        (p := fun i => (0 : Fin 2 → ℝ) ∈ B.M i) fun i _ => B.mem_M i, ← B.eq_sum 0 B.mem_U,
      example935Theta_zero]
    norm_num
  have hnot := not_and_of_sum_eq B.σ B.σ_pos _ _ hor hsum
  rw [h1.2 (pt_mem_Z true s), h2.2 (pt_mem_Z false s),
    h0.2 (pt_at_zero true ▸ pt_mem_Z true 0), Finset.sum_filter, Finset.sum_filter,
    Finset.sum_filter, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases hq : (B.orient i).tangent 0 = orTan true 0
  · rcases hor i with hi | hi
    · have : pt false s ∉ B.M i := fun h => hnot i ⟨hi, h⟩
      simp [hq, hi, this, B.mem_M i]
    · have : pt true s ∉ B.M i := fun h => hnot i ⟨h, hi⟩
      simp [hq, hi, this, B.mem_M i]
  · simp [hq]

/-- The coefficient at the origin is the sum over the two arcs on each side. -/
theorem coef_zero_eq_pos (hT : (trivial (rnPolyfold 2)).IsOrientation example935Theta T) :
    coef T 0 = coef T (pt true 1) + coef T (pt false 1) := by
  obtain ⟨_, hs, hs0⟩ := ((coef_zero_eq hT).filter_mono nhdsWithin_le_nhds |>.and
    (self_mem_nhdsWithin (s := Ioi (0 : ℝ)))).exists
  rw [hs (ne_of_gt hs0), coef_pt_eq_of_pos hT true hs0 one_pos,
    coef_pt_eq_of_pos hT false hs0 one_pos]

theorem coef_zero_eq_neg (hT : (trivial (rnPolyfold 2)).IsOrientation example935Theta T) :
    coef T 0 = coef T (pt true (-1)) + coef T (pt false (-1)) := by
  obtain ⟨_, hs, hs0⟩ := ((coef_zero_eq hT).filter_mono nhdsWithin_le_nhds |>.and
    (self_mem_nhdsWithin (s := Iio (0 : ℝ)))).exists
  rw [hs (ne_of_lt hs0), coef_pt_eq_of_neg hT true hs0 (show (-1 : ℝ) < 0 by norm_num),
    coef_pt_eq_of_neg hT false hs0 (show (-1 : ℝ) < 0 by norm_num)]

/-! ### The family `classOrient a` -/

/-- The coefficient of `(1, β')` of `classOrient a`: `a(side, branch)` on the arcs, the common
value `a(+,G⁺⁺) + a(+,G⁻⁻)` at the origin. -/
def coefOf (a : Bool → Bool → ℚ) (y : Fin 2 → ℝ) : ℚ :=
  if 0 < y 0 then a true (decide (0 ≤ y 1)) else
    if y 0 < 0 then a false (decide (0 ≤ y 1)) else a true true + a true false

/-- **The orientation with coefficients `a`** (`a side branch`, `side = true` for `s > 0`,
`branch = true` for `G⁺⁺`): `coefOf a y · (1, β') + (Θ(y) − coefOf a y) · (−(1, β'))` on
`supp(Θ)`, `0` elsewhere. -/
def classOrient (a : Bool → Bool → ℚ) (y : Fin 2 → ℝ) : (rnPolyfold 2).OrTangent →₀ ℚ :=
  if y ∈ Z then Finsupp.single (orTan true y) (coefOf a y) +
    Finsupp.single (orTan false y) (example935Theta y - coefOf a y) else 0

theorem coefOf_pt_pos (a : Bool → Bool → ℚ) (b : Bool) {s : ℝ} (hs : 0 < s) :
    coefOf a (pt b s) = a true b := by
  rw [coefOf, if_pos (by simpa using hs), decide_pt hs.ne']

theorem coefOf_pt_neg (a : Bool → Bool → ℚ) (b : Bool) {s : ℝ} (hs : s < 0) :
    coefOf a (pt b s) = a false b := by
  rw [coefOf, if_neg (by simp; linarith), if_pos (by simpa using hs), decide_pt hs.ne]

theorem coefOf_zero (a : Bool → Bool → ℚ) : coefOf a 0 = a true true + a true false := by
  simp [coefOf]

theorem classOrient_coef (a : Bool → Bool → ℚ) {y : Fin 2 → ℝ} (hy : y ∈ Z) :
    coef (classOrient a) y = coefOf a y := by
  rw [coef, classOrient, if_pos hy, single_add_single_apply_true hy]

/-- The coefficients `a` of an orientation: its coefficients at `(±1, β_b(±1))`. -/
def coefs (T : (Fin 2 → ℝ) → (rnPolyfold 2).OrTangent →₀ ℚ) (side b : Bool) : ℚ :=
  coef T (pt b (cond side 1 (-1)))

/-- **Every orientation of `Θ` is `classOrient` of its coefficients.** -/
theorem eq_classOrient
    (hT : (trivial (rnPolyfold 2)).IsOrientation example935Theta T) :
    T = classOrient (coefs T) := by
  funext y
  by_cases hy : y ∈ Z
  · have hc : coef T y = coefOf (coefs T) y := by
      obtain ⟨b, hb⟩ := mem_Z_iff.1 hy
      have hyp := eq_pt_of_mem hb
      rcases lt_trichotomy (y 0) 0 with h | h | h
      · rw [hyp, coefOf_pt_neg _ b h]
        exact coef_pt_eq_of_neg hT b h (show (-1 : ℝ) < 0 by norm_num)
      · have hy0 : y = 0 := by rw [hyp, h, pt_at_zero]
        rw [hy0, coefOf_zero]
        exact coef_zero_eq_pos hT
      · rw [hyp, coefOf_pt_pos _ b h]
        exact coef_pt_eq_of_pos hT b h one_pos
    rw [eq_single_add_single hT hy, classOrient, if_pos hy, hc]
  · rw [hT.eq_zero_of_not_mem (mem_smoothSet y) (by rwa [supp_example935Theta]), classOrient,
      if_neg hy]
    rfl

theorem coefs_bounds (hT : (trivial (rnPolyfold 2)).IsOrientation example935Theta T)
    (side b : Bool) : 0 ≤ coefs T side b ∧ coefs T side b ≤ 1 := by
  refine ⟨coef_nonneg hT _, ?_⟩
  have h := coef_le hT (pt_mem_Z b (cond side 1 (-1)))
  rwa [theta_pt (by cases side <;> norm_num)] at h

theorem coefs_sum (hT : (trivial (rnPolyfold 2)).IsOrientation example935Theta T) :
    coefs T true true + coefs T true false = coefs T false true + coefs T false false := by
  show coef T (pt true 1) + coef T (pt false 1) = coef T (pt true (-1)) + coef T (pt false (-1))
  rw [← coef_zero_eq_pos hT, ← coef_zero_eq_neg hT]

/-! ### The construction: four graphs, both orientations, transport weights -/

/-- The four graphs `G^{pq}` of the text, `p` the branch over `s > 0`, `q` over `s < 0`:
`G⁺⁺`, `G⁻⁻`, `G⁺⁻` (`p = false`, `q = true`) and `G⁻⁺`. -/
def gr : Bool → Bool → ℝ → ℝ
  | true, true => betaPP
  | false, false => betaMM
  | false, true => betaPM
  | true, false => betaMP

theorem contDiff_gr : ∀ p q, ContDiff ℝ ∞ (gr p q)
  | true, true => contDiff_betaPP
  | false, false => contDiff_betaMM
  | false, true => contDiff_betaPM
  | true, false => contDiff_betaMP

theorem gr_of_pos {s : ℝ} (hs : 0 < s) : ∀ p q, gr p q s = beta1 p s
  | true, true => rfl
  | false, false => rfl
  | false, true => betaPM_of_pos hs
  | true, false => betaMP_of_pos hs

theorem gr_of_neg {s : ℝ} (hs : s < 0) : ∀ p q, gr p q s = beta1 q s
  | true, true => rfl
  | false, false => rfl
  | false, true => betaPM_of_nonpos hs.le
  | true, false => betaMP_of_nonpos hs.le

theorem gr_zero : ∀ p q, gr p q 0 = 0
  | true, true => betaPP_zero
  | false, false => by simp [gr, betaMM, betaPP_zero]
  | false, true => by simp [gr, betaPM]
  | true, false => by simp [gr, betaMP, betaPM]

theorem graph2_gr_subset_Z : ∀ p q, graph2 (gr p q) ⊆ Z
  | true, true => fun _ h => Or.inl h
  | false, false => fun _ h => Or.inr h
  | false, true => graph2_beta2_subset_Z true
  | true, false => graph2_beta2_subset_Z false

theorem gr_tangent (p q e : Bool) {y : Fin 2 → ℝ} (hy : y ∈ graph2 (gr p q)) :
    (graphOrientation (contDiff_gr p q) (boolSign e) (boolSign_ne_zero e)).tangent y =
      orTan e y := by
  cases p <;> cases q
  · exact gOr_tangent_eq_orTan (b := false) e hy
  · exact orient2_tangent_eq_orTan true e hy
  · exact orient2_tangent_eq_orTan false e hy
  · exact gOr_tangent_eq_orTan (b := true) e hy

theorem mem_beta1_iff {y : Fin 2 → ℝ} (hy : y ∈ Z) (h0 : y 0 ≠ 0) (p : Bool) :
    y ∈ graph2 (beta1 p) ↔ p = decide (0 ≤ y 1) := by
  obtain ⟨b, hb⟩ := mem_Z_iff.1 hy
  have hd : decide (0 ≤ y 1) = b := by rw [eq_pt_of_mem hb]; exact decide_pt h0
  rw [hd]
  constructor
  · intro hp
    by_contra hne
    have : p = !b := by cases p <;> cases b <;> simp_all
    exact not_mem_graph2_not hb h0 (this ▸ hp)
  · rintro rfl; exact hb

theorem mem_gr_iff_of_pos {y : Fin 2 → ℝ} (hy : y ∈ Z) (h : 0 < y 0) (p q : Bool) :
    y ∈ graph2 (gr p q) ↔ p = decide (0 ≤ y 1) := by
  rw [← mem_beta1_iff hy h.ne' p, mem_graph2_iff, mem_graph2_iff, gr_of_pos h]

theorem mem_gr_iff_of_neg {y : Fin 2 → ℝ} (hy : y ∈ Z) (h : y 0 < 0) (p q : Bool) :
    y ∈ graph2 (gr p q) ↔ q = decide (0 ≤ y 1) := by
  rw [← mem_beta1_iff hy h.ne q, mem_graph2_iff, mem_graph2_iff, gr_of_neg h]

theorem zero_mem_gr (p q : Bool) : (0 : Fin 2 → ℝ) ∈ graph2 (gr p q) := by
  rw [mem_graph2_iff]; simp [gr_zero]

/-- **The `2 × 2` transport problem**: nonnegative row sums `r` and column sums `c` with the same
total are the margins of a nonnegative `2 × 2` matrix. -/
theorem exists_transport (r c : Bool → ℚ) (hr : ∀ p, 0 ≤ r p) (hc : ∀ q, 0 ≤ c q)
    (h : r true + r false = c true + c false) :
    ∃ W : Bool → Bool → ℚ, (∀ p q, 0 ≤ W p q) ∧ (∀ p, W p true + W p false = r p) ∧
      ∀ q, W true q + W false q = c q := by
  set m := min (r true) (c true) with hm
  have h1 := min_le_left (r true) (c true)
  have h2 := min_le_right (r true) (c true)
  have h3 : 0 ≤ r false - c true + m := by
    rcases le_total (r true) (c true) with h' | h'
    · rw [hm, min_eq_left h']; linarith [hc false]
    · rw [hm, min_eq_right h']; linarith [hr false]
  refine ⟨fun p q => if p then (if q then m else r true - m) else
    (if q then c true - m else r false - c true + m), ?_, ?_, ?_⟩
  · intro p q
    cases p <;> cases q <;> simp only [if_true, if_false, Bool.false_eq_true] <;>
      linarith [le_min (hr true) (hc true)]
  · intro p; cases p <;> simp
  · intro q; cases q <;> simp; linarith

/-- The weighted count of the graphs `G^{pq}` through `y`. -/
def gsum (V : Bool → Bool → ℚ) (y : Fin 2 → ℝ) : ℚ :=
  ∑ p, ∑ q, if y ∈ graph2 (gr p q) then V p q else 0

theorem gsum_of_not_mem (V : Bool → Bool → ℚ) {y : Fin 2 → ℝ} (hy : y ∉ Z) : gsum V y = 0 :=
  Finset.sum_eq_zero fun p _ => Finset.sum_eq_zero fun q _ =>
    if_neg fun h => hy (graph2_gr_subset_Z p q h)

theorem gsum_of_pos (V : Bool → Bool → ℚ) {y : Fin 2 → ℝ} (hy : y ∈ Z) (h : 0 < y 0) :
    gsum V y = V (decide (0 ≤ y 1)) true + V (decide (0 ≤ y 1)) false := by
  simp only [gsum, Fintype.sum_bool, mem_gr_iff_of_pos hy h]
  cases decide (0 ≤ y 1) <;> simp

theorem gsum_of_neg (V : Bool → Bool → ℚ) {y : Fin 2 → ℝ} (hy : y ∈ Z) (h : y 0 < 0) :
    gsum V y = V true (decide (0 ≤ y 1)) + V false (decide (0 ≤ y 1)) := by
  simp only [gsum, Fintype.sum_bool, mem_gr_iff_of_neg hy h]
  cases decide (0 ≤ y 1) <;> simp

theorem gsum_zero (V : Bool → Bool → ℚ) :
    gsum V 0 = (V true true + V true false) + (V false true + V false false) := by
  simp [gsum, zero_mem_gr]

theorem eq_zero_of_mem_Z {y : Fin 2 → ℝ} (hy : y ∈ Z) (h : y 0 = 0) : y = 0 := by
  obtain ⟨b, hb⟩ := mem_Z_iff.1 hy
  rw [eq_pt_of_mem hb, h, pt_at_zero]

theorem example935Theta_of_not_mem {y : Fin 2 → ℝ} (hy : y ∉ Z) : example935Theta y = 0 := by
  rw [example935Theta_apply, if_neg fun h => hy (Or.inl h), if_neg fun h => hy (Or.inr h)]
  norm_num

/-- `Σ_{y ∈ Mₖ} Wₖ` over `{k | 0 < W k}` is the full sum of the terms vanishing when `Wₖ = 0`. -/
theorem sum_subtype_pos {κ α : Type*} [Fintype κ] [AddCommMonoid α] (W : κ → ℚ) (f : κ → α)
    (hf : ∀ k, f k ≠ 0 → 0 < W k) : ∑ i : {k // 0 < W k}, f i.1 = ∑ k, f k := by
  rw [← Finset.sum_subtype (Finset.univ.filter fun k => 0 < W k) (by simp) f,
    Finset.sum_filter_of_ne fun k _ h => hf k h]

theorem single_ite (g : (rnPolyfold 2).OrTangent) (P : Prop) [Decidable P] (w : ℚ) :
    Finsupp.single g (if P then w else 0) = if P then Finsupp.single g w else 0 := by
  split_ifs <;> simp

/-- **Every `classOrient a` with `0 ≤ a ≤ 1` and equal sums on the two sides is an orientation
of `Θ`**: it is the oriented sum of the four graphs `G^{pq}`, each with both orientations, with
weights solving the transport problems with margins `a` and `1 − a`. -/
theorem isOrientation_classOrient (a : Bool → Bool → ℚ) (h01 : ∀ s b, 0 ≤ a s b ∧ a s b ≤ 1)
    (hc : a true true + a true false = a false true + a false false) :
    (trivial (rnPolyfold 2)).IsOrientation example935Theta (classOrient a) := by
  obtain ⟨Wp, hWp0, hWpr, hWpc⟩ := exists_transport (a true) (a false) (fun p => (h01 _ _).1)
    (fun q => (h01 _ _).1) hc
  obtain ⟨Wm, hWm0, hWmr, hWmc⟩ := exists_transport (fun p => 1 - a true p)
    (fun q => 1 - a false q) (fun p => by linarith [(h01 true p).2])
    (fun q => by linarith [(h01 false q).2]) (by linarith)
  -- the values of the two weighted counts
  have hp : ∀ y ∈ Z, gsum Wp y = coefOf a y := by
    intro y hy
    rcases lt_trichotomy (y 0) 0 with h | h | h
    · rw [gsum_of_neg _ hy h, hWpc, coefOf, if_neg (by linarith), if_pos h]
    · rw [eq_zero_of_mem_Z hy h, gsum_zero, hWpr, hWpr, coefOf_zero]
    · rw [gsum_of_pos _ hy h, hWpr, coefOf, if_pos h]
  have hm : ∀ y ∈ Z, gsum Wm y = example935Theta y - coefOf a y := by
    intro y hy
    rcases lt_trichotomy (y 0) 0 with h | h | h
    · rw [gsum_of_neg _ hy h, hWmc, coefOf, if_neg (by linarith), if_pos h,
        example935Theta_eq_one hy h.ne]
    · rw [eq_zero_of_mem_Z hy h, gsum_zero, hWmr, hWmr, coefOf_zero, example935Theta_zero]
      ring
    · rw [gsum_of_pos _ hy h, hWmr, coefOf, if_pos h, example935Theta_eq_one hy h.ne']
  -- the sheets
  let W : Bool × Bool × Bool → ℚ := fun k => if k.2.2 then Wp k.1 k.2.1 else Wm k.1 k.2.1
  have hW0 : ∀ k, 0 ≤ W k := fun k => by
    simp only [W]; split_ifs
    exacts [hWp0 _ _, hWm0 _ _]
  let M : {k // 0 < W k} → Set (Fin 2 → ℝ) := fun i => graph2 (gr i.1.1 i.1.2.1)
  let o : ∀ i : {k // 0 < W k}, (rnPolyfold 2).SubmanifoldOrientation (M i) 1 := fun i =>
    graphOrientation (contDiff_gr _ _) (boolSign i.1.2.2) (boolSign_ne_zero _)
  have hpos : ∀ k, W k ≠ 0 → 0 < W k := fun k hk => lt_of_le_of_ne (hW0 k) (Ne.symm hk)
  -- the weighted count of the sheets is `Θ`
  have hcount : ∀ y, (∑ k : Bool × Bool × Bool, if y ∈ graph2 (gr k.1 k.2.1) then W k else 0) =
      gsum Wp y + gsum Wm y := by
    intro y
    simp only [gsum, W, Fintype.sum_prod_type, Fintype.sum_bool, if_true, Bool.false_eq_true,
      if_false]
    ring
  have hΘ : example935Theta = fun y => ∑ i with y ∈ M i, W i.1 := by
    funext y
    rw [Finset.sum_filter, sum_subtype_pos W (fun k => if y ∈ graph2 (gr k.1 k.2.1) then W k
      else 0) (fun k hk => hpos k (by intro h; apply hk; simp [h])), hcount]
    by_cases hy : y ∈ Z
    · rw [hp y hy, hm y hy]; ring
    · rw [gsum_of_not_mem _ hy, gsum_of_not_mem _ hy, example935Theta_of_not_mem hy]; ring
  -- the oriented sum is `classOrient a`
  have hT : classOrient a = orientedSumRn M (fun i => W i.1) o := by
    funext y
    have h1 : orientedSumRn M (fun i => W i.1) o y = ∑ k : Bool × Bool × Bool,
        if y ∈ graph2 (gr k.1 k.2.1) then Finsupp.single (orTan k.2.2 y) (W k) else 0 := by
      rw [orientedSumRn, Finset.sum_filter, ← sum_subtype_pos W (fun k =>
        if y ∈ graph2 (gr k.1 k.2.1) then Finsupp.single (orTan k.2.2 y) (W k) else 0)
        (fun k hk => hpos k (by intro h; apply hk; simp [h]))]
      refine Finset.sum_congr rfl fun i _ => ?_
      by_cases hyi : y ∈ M i
      · rw [if_pos hyi, if_pos hyi]
        exact congrArg (fun g => Finsupp.single g (W i.1)) (gr_tangent _ _ _ hyi)
      · rw [if_neg hyi, if_neg hyi]
    have h2 : (∑ k : Bool × Bool × Bool,
        if y ∈ graph2 (gr k.1 k.2.1) then Finsupp.single (orTan k.2.2 y) (W k) else 0) =
        Finsupp.single (orTan true y) (gsum Wp y) + Finsupp.single (orTan false y) (gsum Wm y) := by
      simp only [gsum, W, Fintype.sum_prod_type, Fintype.sum_bool, if_true, Bool.false_eq_true,
        if_false, Finsupp.single_add, single_ite]
      abel
    rw [h1, h2, classOrient]
    by_cases hy : y ∈ Z
    · rw [if_pos hy, hp y hy, hm y hy]
    · rw [if_neg hy, gsum_of_not_mem _ hy, gsum_of_not_mem _ hy, Finsupp.single_zero,
        Finsupp.single_zero, add_zero]
  rw [hT]
  exact isOrientation_sum_trivial_rn' M _ (fun i => i.2)
    (fun _ => rnPolyfold_isSubmanifoldOfDim_graph2 (contDiff_gr _ _))
    (fun _ => isClosed_graph2 (contDiff_gr _ _).continuous) o hΘ

/-! ### The classification -/

theorem coefs_classOrient (a : Bool → Bool → ℚ) : coefs (classOrient a) = a := by
  funext side b
  cases side
  · change coef (classOrient a) (pt b (-1)) = a false b
    rw [classOrient_coef a (pt_mem_Z _ _), coefOf_pt_neg a b (by norm_num)]
  · change coef (classOrient a) (pt b 1) = a true b
    rw [classOrient_coef a (pt_mem_Z _ _), coefOf_pt_pos a b one_pos]

/-- Different coefficients give different orientations. -/
theorem classOrient_injective : Function.Injective classOrient := fun a a' h => by
  rw [← coefs_classOrient a, ← coefs_classOrient a', h]

end Ex935

open Ex935

/-- **Example 9.3.5, 2021 p. 425 (2017: Example 9.1): all orientations of `Θ`.**  The
orientations of `Θ` (Definition 9.3.2, rational weights) are exactly the `classOrient a`: on the
arc of `G_b` over `s > 0` (`side = true`) or `s < 0` (`side = false`) the weight
`a side b ∈ [0, 1] ∩ ℚ` on `(1, β')` and `1 − a side b` on `−(1, β')`, at the origin the weight
`a(+,G⁺⁺) + a(+,G⁻⁻)` on `(1, 0)` and `2 − a(+,G⁺⁺) − a(+,G⁻⁻)` on `(−1, 0)`, where
`a(+,G⁺⁺) + a(+,G⁻⁻) = a(−,G⁺⁺) + a(−,G⁻⁻)`; `a` is unique (`classOrient_injective`). -/
theorem example_9_3_5_classification (T : (Fin 2 → ℝ) → (rnPolyfold 2).OrTangent →₀ ℚ) :
    (trivial (rnPolyfold 2)).IsOrientation example935Theta T ↔
      ∃ a : Bool → Bool → ℚ, (∀ side b, 0 ≤ a side b ∧ a side b ≤ 1) ∧
        a true true + a true false = a false true + a false false ∧ T = classOrient a :=
  ⟨fun hT => ⟨coefs T, coefs_bounds hT, coefs_sum hT, eq_classOrient hT⟩,
    fun ⟨a, h01, hc, hTa⟩ => hTa ▸ isOrientation_classOrient a h01 hc⟩

/-- **Example 9.3.5: `Θ` has infinitely many orientations** (`a ≡ q`, `q ∈ [0, 1] ∩ ℚ`). -/
theorem example_9_3_5_infinite :
    {T : (Fin 2 → ℝ) → (rnPolyfold 2).OrTangent →₀ ℚ |
      (trivial (rnPolyfold 2)).IsOrientation example935Theta T}.Infinite := by
  have hinj : Function.Injective fun q : ℚ => classOrient fun _ _ => q := fun q q' h =>
    congrFun (congrFun (classOrient_injective h) true) true
  refine ((Set.Icc_infinite (zero_lt_one' ℚ)).image hinj.injOn).mono ?_
  rintro _ ⟨q, hq, rfl⟩
  exact isOrientation_classOrient _ (fun _ _ => hq) rfl

namespace Ex935

theorem single_orTan_apply {y : Fin 2 → ℝ} (hy : y ∈ Z) (e : Bool) :
    Finsupp.single (orTan e y) (1 : ℚ) (orTan true y) = if e then 1 else 0 := by
  cases e
  · simp [orTan_ne hy]
  · simp

theorem coef_orientedLift1 (ε : Bool → Bool) (b : Bool) {s : ℝ} (hs : s ≠ 0) :
    coef (orientedLift1 ε) (pt b s) = if ε b then 1 else 0 := by
  have hZ := pt_mem_Z b s
  have hm : ∀ b', pt b s ∈ graph2 (beta1 b') ↔ b' = b := fun b' => by
    rw [mem_beta1_iff hZ hs, decide_pt hs]
  rw [coef, orientedLift1, orientedSumRn_bool]
  cases b
  · rw [if_neg (by rw [hm]; simp), if_pos ((hm false).2 rfl), zero_add]
    rw [show (orient1 ε false).tangent (pt false s) = orTan (ε false) (pt false s) from
      gOr_tangent_eq_orTan (ε false) ((hm false).2 rfl), single_orTan_apply hZ]
  · rw [if_pos ((hm true).2 rfl), if_neg (by rw [hm]; simp), add_zero]
    rw [show (orient1 ε true).tangent (pt true s) = orTan (ε true) (pt true s) from
      gOr_tangent_eq_orTan (ε true) ((hm true).2 rfl), single_orTan_apply hZ]

theorem coef_orientedLift2_pos (δ : Bool → Bool) (b : Bool) {s : ℝ} (hs : 0 < s) :
    coef (orientedLift2 δ) (pt b s) = if δ (!b) then 1 else 0 := by
  have hZ := pt_mem_Z b s
  have h0 : 0 < pt b s 0 := hs
  have hm : ∀ b', pt b s ∈ graph2 (beta2 b') ↔ (!b') = b := fun b' => by
    cases b'
    · exact (mem_gr_iff_of_pos hZ h0 true false).trans (by rw [decide_pt hs.ne']; simp)
    · exact (mem_gr_iff_of_pos hZ h0 false true).trans (by rw [decide_pt hs.ne']; simp)
  rw [coef, orientedLift2, orientedSumRn_bool]
  cases b
  · rw [if_pos ((hm true).2 rfl), if_neg (by rw [hm]; simp), add_zero]
    rw [show (orient2 δ true).tangent (pt false s) = orTan (δ true) (pt false s) from
      orient2_tangent_eq_orTan true (δ true) ((hm true).2 rfl), single_orTan_apply hZ]
    rfl
  · rw [if_neg (by rw [hm]; simp), if_pos ((hm false).2 rfl), zero_add]
    rw [show (orient2 δ false).tangent (pt true s) = orTan (δ false) (pt true s) from
      orient2_tangent_eq_orTan false (δ false) ((hm false).2 rfl), single_orTan_apply hZ]
    rfl

theorem coef_orientedLift2_neg (δ : Bool → Bool) (b : Bool) {s : ℝ} (hs : s < 0) :
    coef (orientedLift2 δ) (pt b s) = if δ b then 1 else 0 := by
  have hZ := pt_mem_Z b s
  have h0 : pt b s 0 < 0 := hs
  have hm : ∀ b', pt b s ∈ graph2 (beta2 b') ↔ b' = b := fun b' => by
    cases b'
    · exact (mem_gr_iff_of_neg hZ h0 true false).trans (by rw [decide_pt hs.ne])
    · exact (mem_gr_iff_of_neg hZ h0 false true).trans (by rw [decide_pt hs.ne])
  rw [coef, orientedLift2, orientedSumRn_bool]
  cases b
  · rw [if_neg (by rw [hm]; simp), if_pos ((hm false).2 rfl), zero_add]
    rw [show (orient2 δ false).tangent (pt false s) = orTan (δ false) (pt false s) from
      orient2_tangent_eq_orTan false (δ false) ((hm false).2 rfl), single_orTan_apply hZ]
  · rw [if_pos ((hm true).2 rfl), if_neg (by rw [hm]; simp), add_zero]
    rw [show (orient2 δ true).tangent (pt true s) = orTan (δ true) (pt true s) from
      orient2_tangent_eq_orTan true (δ true) ((hm true).2 rfl), single_orTan_apply hZ]

/-- The values of an oriented sum with weights `1` are natural numbers. -/
theorem orientedSumRn_apply_nat {ι : Type} [Fintype ι] (M : ι → Set (Fin 2 → ℝ)) {dim : ι → ℕ}
    (o : ∀ i, (rnPolyfold 2).SubmanifoldOrientation (M i) (dim i)) (y : Fin 2 → ℝ)
    (g : (rnPolyfold 2).OrTangent) : ∃ n : ℕ, orientedSumRn M (fun _ => 1) o y g = n := by
  refine ⟨((Finset.univ.filter fun i => y ∈ M i).filter fun i => (o i).tangent y = g).card, ?_⟩
  rw [orientedSumRn, Finsupp.finsetSum_apply]
  simp only [Finsupp.single_apply]
  rw [Finset.sum_boole]

theorem coefs_orientedLift1 (ε : Bool → Bool) :
    coefs (orientedLift1 ε) = fun _ b => if ε b then 1 else 0 := by
  funext side b
  cases side
  · exact coef_orientedLift1 ε b (by norm_num)
  · exact coef_orientedLift1 ε b one_ne_zero

theorem coefs_orientedLift2 (δ : Bool → Bool) :
    coefs (orientedLift2 δ) = fun side b => if side then (if δ (!b) then 1 else 0)
      else (if δ b then 1 else 0) := by
  funext side b
  cases side
  · exact coef_orientedLift2_neg δ b (by norm_num)
  · exact coef_orientedLift2_pos δ b one_pos

end Ex935

/-- **Example 9.3.5, "four different possibilities to orient", what holds as we read it**: the
orientations of `Θ` with integer weights are exactly the six given by sign choices on the two
local branching structures `G⁺⁺, G⁻⁻` and `G⁺⁻, G⁻⁺` of the text (`ncard_signOrientations`). -/
theorem example_9_3_5_integral :
    {T : (Fin 2 → ℝ) → (rnPolyfold 2).OrTangent →₀ ℚ |
      (trivial (rnPolyfold 2)).IsOrientation example935Theta T ∧ ∀ y g, ∃ n : ℕ, T y g = n} =
      range orientedLift1 ∪ range orientedLift2 := by
  ext T
  constructor
  · rintro ⟨hT, hint⟩
    have h01 : ∀ side b, coefs T side b = 0 ∨ coefs T side b = 1 := by
      intro side b
      obtain ⟨n, hn⟩ := hint (pt b (cond side 1 (-1))) (orTan true (pt b (cond side 1 (-1))))
      have e : coefs T side b = (n : ℚ) := hn
      have hle := (coefs_bounds hT side b).2
      rw [e] at hle
      have : n ≤ 1 := by exact_mod_cast hle
      rw [e]
      interval_cases n <;> simp
    have hc := coefs_sum hT
    have hcases : (coefs T true true = coefs T false true ∧
        coefs T true false = coefs T false false) ∨
        (coefs T true true = coefs T false false ∧ coefs T true false = coefs T false true) := by
      rcases h01 true true with h1 | h1 <;> rcases h01 true false with h2 | h2 <;>
        rcases h01 false true with h3 | h3 <;> rcases h01 false false with h4 | h4 <;>
        rw [h1, h2, h3, h4] at hc ⊢ <;> revert hc <;> norm_num
    rw [eq_classOrient hT]
    rcases hcases with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · left
      refine ⟨fun b => decide (coefs T false b = 1), ?_⟩
      rw [eq_classOrient (orientedLift1_isOrientation (hasIndependentTangentSums _) _),
        coefs_orientedLift1]
      congr 1
      funext side b
      have hfb : coefs T true b = coefs T false b := by cases b <;> assumption
      cases side
      · rcases h01 false b with h | h <;> simp [h]
      · rw [hfb]; rcases h01 false b with h | h <;> simp [h]
    · right
      refine ⟨fun b => decide (coefs T false b = 1), ?_⟩
      rw [eq_classOrient (orientedLift2_isOrientation (hasIndependentTangentSums _) _),
        coefs_orientedLift2]
      congr 1
      funext side b
      have hfb : coefs T true b = coefs T false (!b) := by cases b <;> assumption
      cases side
      · rcases h01 false b with h | h <;> simp [h]
      · rw [hfb]; rcases h01 false (!b) with h | h <;> simp [h]
  · rintro (⟨ε, rfl⟩ | ⟨δ, rfl⟩)
    · exact ⟨orientedLift1_isOrientation (hasIndependentTangentSums _) ε,
        fun y g => orientedSumRn_apply_nat _ _ y g⟩
    · exact ⟨orientedLift2_isOrientation (hasIndependentTangentSums _) δ,
        fun y g => orientedSumRn_apply_nat _ _ y g⟩

/-- **Example 9.3.5**: `Θ` has exactly six orientations with integer weights. -/
theorem example_9_3_5_integral_ncard :
    {T : (Fin 2 → ℝ) → (rnPolyfold 2).OrTangent →₀ ℚ |
      (trivial (rnPolyfold 2)).IsOrientation example935Theta T ∧
        ∀ y g, ∃ n : ℕ, T y g = n}.ncard = 6 := by
  rw [example_9_3_5_integral, ncard_signOrientations]

end Polyfold
