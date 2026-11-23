import Polyfold.Chapter9.LocalPartitions

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021; 2017 arXiv 1707.08941),
Part II, Chapter 9, §9.5, **Remark 9.5.19, 2021 p. 451** (point G.153).  Numbers and pages are
the 2021 text's.

# Sc-smooth functions near a locally compact subset of an M-polyfold

## What is formalized

* Sums, products and inverses of real functions which are sc-smooth on an open set
  (`LocalPart.real_add`, `real_mul`, `real_finsetSum`, `real_inv`).
* `LocalPart.isScSmoothOn_chart_contDiff`: a `C^∞` function of the level-`0` chart coordinate is
  sc-smooth on the chart domain.
* `LocalPart.exists_contDiff_separating`: a compact subset `S` of a normed space and a point
  `a ∉ S` are separated by a `C^∞` function which is a finite product of smooth functions of
  continuous linear functionals (Hahn–Banach).
* `LocalPart.exists_local_bump`: for a subset `S` of an M-polyfold which near `p` lies in a
  compact set, and an open `V ∋ p`, a function `f ≥ 0` with `f(p) = 1`, vanishing off a closed
  subset of `V`, and sc-smooth on an open set containing `S`.

## Reading

A general sc-Banach space need not carry sc-smooth functions with bounded support, so the
function of `exists_local_bump` is sc-smooth near `S` only: in a chart it is the restriction to a
small open `V₁ ∋ p` of a product of smooth functions of finitely many continuous linear
functionals, which vanishes near the compact set `S ∩ ∂V₁`.
-/

set_option maxSynthPendingDepth 3

open Set Function Filter Topology
open scoped ContDiff

noncomputable section

namespace Polyfold

universe u

namespace LocalPart

/-! ### Real functions sc-smooth on an open set -/

section ScFunctions

variable {Z : Type u} [TopologicalSpace Z] [T2Space Z] [ParacompactSpace Z] {P : MPolyfold Z}

/-- A function sc-smooth on `U`, read in a chart on an open `V ⊆ U ∩ dom φ`. -/
theorem real_chart_on {f : Z → ℝ} {U : Set Z} (hf : P.IsScSmoothOn realPolyfold f U)
    {φ : MChart Z} (hφ : P.IsChart φ) {V : Set Z} (hV : IsOpen V) (hVU : V ⊆ U ∩ φ.source) :
    IsScSmoothRetractMap φ.model.E φ.model.C (φ '' V) realSc univ univ (f ∘ φ.symm) :=
  hf.smooth φ realChart hφ isChart_realChart V hV hVU (mapsTo_univ _ _)

/-- A continuous function on the open set `U` which near every point of `U` is sc-smooth in some
chart is sc-smooth on `U`. -/
theorem isScSmoothOn_real_of_charts {f : Z → ℝ} {U : Set Z} (hU : IsOpen U)
    (hc : ContinuousOn f U)
    (h : ∀ x ∈ U, ∃ (φ : MChart Z) (V : Set Z), P.IsChart φ ∧ IsOpen V ∧ x ∈ V ∧
      V ⊆ U ∩ φ.source ∧
      IsScSmoothRetractMap φ.model.E φ.model.C (φ '' V) realSc univ univ (f ∘ φ.symm)) :
    P.IsScSmoothOn realPolyfold f U := by
  refine MPolyfold.IsScSmoothOn.of_exists_charts hU hc fun x hx => ?_
  obtain ⟨φ, V, hφ, hVo, hxV, hVφ, hrep⟩ := h x hx
  exact ⟨φ, realChart, V, hφ, isChart_realChart, hVo, hxV, hVφ, mapsTo_univ _ _, hrep⟩

/-- A constant is sc-smooth on every open set. -/
theorem real_const {U : Set Z} (hU : IsOpen U) (a : ℝ) :
    P.IsScSmoothOn realPolyfold (fun _ => a) U :=
  (isScSmoothMap_real_const (PX := P) a).mono hU (subset_univ _)

/-- The sum of two functions sc-smooth on `U`. -/
theorem real_add {f g : Z → ℝ} {U : Set Z} (hf : P.IsScSmoothOn realPolyfold f U)
    (hg : P.IsScSmoothOn realPolyfold g U) :
    P.IsScSmoothOn realPolyfold (fun x => f x + g x) U := by
  refine isScSmoothOn_real_of_charts hf.isOpen (hf.continuousOn.add hg.continuousOn)
    fun x hx => ?_
  obtain ⟨φ, hφ, hxφ⟩ := P.exists_isChart_mem_source x
  have hV : IsOpen (U ∩ φ.source) := hf.isOpen.inter φ.isOpen_source
  exact ⟨φ, U ∩ φ.source, hφ, hV, ⟨hx, hxφ⟩, subset_rfl,
    (real_chart_on hf hφ hV subset_rfl).real_add (real_chart_on hg hφ hV subset_rfl)⟩

/-- The product of two functions sc-smooth on `U`. -/
theorem real_mul {f g : Z → ℝ} {U : Set Z} (hf : P.IsScSmoothOn realPolyfold f U)
    (hg : P.IsScSmoothOn realPolyfold g U) :
    P.IsScSmoothOn realPolyfold (fun x => f x * g x) U := by
  refine isScSmoothOn_real_of_charts hf.isOpen (hf.continuousOn.mul hg.continuousOn)
    fun x hx => ?_
  obtain ⟨φ, hφ, hxφ⟩ := P.exists_isChart_mem_source x
  have hV : IsOpen (U ∩ φ.source) := hf.isOpen.inter φ.isOpen_source
  exact ⟨φ, U ∩ φ.source, hφ, hV, ⟨hx, hxφ⟩, subset_rfl,
    (real_chart_on hf hφ hV subset_rfl).real_mul (real_chart_on hg hφ hV subset_rfl)⟩

/-- A finite sum of functions sc-smooth on `U`. -/
theorem real_finsetSum {ι : Type*} (s : Finset ι) {f : ι → Z → ℝ} {U : Set Z} (hU : IsOpen U)
    (hf : ∀ i ∈ s, P.IsScSmoothOn realPolyfold (f i) U) :
    P.IsScSmoothOn realPolyfold (fun x => ∑ i ∈ s, f i x) U := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact real_const hU 0
  | insert a s ha ih =>
    have h := real_add (hf a (Finset.mem_insert_self a s))
      (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))
    have heq : (fun x => f a x + ∑ i ∈ s, f i x) = fun x => ∑ i ∈ insert a s, f i x :=
      funext fun x => by rw [Finset.sum_insert ha]
    rwa [heq] at h

/-- `σ ∘ f` for `f` sc-smooth on `U` and a `C^∞` function `σ`. -/
theorem comp_contDiff {f : Z → ℝ} {U : Set Z} (hf : P.IsScSmoothOn realPolyfold f U)
    {σ : ℝ → ℝ} (hσ : ContDiff ℝ ∞ σ) : P.IsScSmoothOn realPolyfold (σ ∘ f) U :=
  MPolyfold.IsScSmoothOn.comp (isScSmoothMap_real_of_contDiff hσ) hf (mapsTo_univ _ _)

/-- A `C^∞` function on `ℝ` which is `t ↦ t⁻¹` on `[c, ∞)`, `c > 0`. -/
theorem exists_contDiff_inv {c : ℝ} (hc : 0 < c) :
    ∃ ρ : ℝ → ℝ, ContDiff ℝ ∞ ρ ∧ ∀ t, c ≤ t → ρ t = t⁻¹ := by
  set m : ℝ → ℝ := fun t => c + (t - c) * Real.smoothTransition (2 * t / c - 1) with hm
  have hmc : ContDiff ℝ ∞ m :=
    contDiff_const.add ((contDiff_id.sub contDiff_const).mul
      (Real.smoothTransition.contDiff.comp
        (((contDiff_const.mul contDiff_id).div_const c).sub contDiff_const)))
  have hpos : ∀ t, 0 < m t := by
    intro t
    have h0 := Real.smoothTransition.nonneg (2 * t / c - 1)
    have h1 := Real.smoothTransition.le_one (2 * t / c - 1)
    by_cases ht : t ≤ c / 2
    · have : Real.smoothTransition (2 * t / c - 1) = 0 := by
        refine Real.smoothTransition.zero_of_nonpos ?_
        have : 2 * t / c ≤ 1 := by rw [div_le_one hc]; linarith
        linarith
      simp only [hm, this, mul_zero, add_zero]
      exact hc
    · have ht := not_le.1 ht
      by_cases htc : t ≤ c
      · have : (t - c) * Real.smoothTransition (2 * t / c - 1) ≥ t - c := by
          nlinarith
        simp only [hm]
        linarith
      · have htc := not_le.1 htc
        have : 0 ≤ (t - c) * Real.smoothTransition (2 * t / c - 1) :=
          mul_nonneg (by linarith) h0
        simp only [hm]
        linarith
  refine ⟨fun t => (m t)⁻¹, hmc.inv fun t => (hpos t).ne', fun t ht => ?_⟩
  have : Real.smoothTransition (2 * t / c - 1) = 1 := by
    refine Real.smoothTransition.one_of_one_le ?_
    have : 2 ≤ 2 * t / c := by rw [le_div_iff₀ hc]; linarith
    linarith
  simp only [hm, this, mul_one, add_sub_cancel]

/-- The inverse of a positive function sc-smooth on `U`. -/
theorem real_inv {f : Z → ℝ} {U : Set Z} (hf : P.IsScSmoothOn realPolyfold f U)
    (hpos : ∀ y ∈ U, 0 < f y) : P.IsScSmoothOn realPolyfold (fun y => (f y)⁻¹) U := by
  refine MPolyfold.IsScSmoothOn.of_locally hf.isOpen fun x hx => ?_
  have hc : 0 < f x / 2 := half_pos (hpos x hx)
  obtain ⟨ρ, hρ, hρe⟩ := exists_contDiff_inv hc
  have hU' : IsOpen (U ∩ f ⁻¹' Ioi (f x / 2)) :=
    hf.continuousOn.isOpen_inter_preimage hf.isOpen isOpen_Ioi
  refine ⟨U ∩ f ⁻¹' Ioi (f x / 2), hU', ⟨hx, ?_⟩, inter_subset_left, ?_⟩
  · change f x / 2 < f x
    linarith [hpos x hx]
  · refine (comp_contDiff (hf.mono hU' inter_subset_left) hρ).congr fun y hy => ?_
    exact hρe _ (le_of_lt hy.2)

/-- A function which is sc-smooth on an open neighbourhood, inside `U`, of every point of the
open set `U` is sc-smooth on `U`. -/
theorem isScSmoothOn_of_nhds {f : Z → ℝ} {U : Set Z} (hU : IsOpen U)
    (h : ∀ x ∈ U, ∃ N : Set Z, x ∈ N ∧ P.IsScSmoothOn realPolyfold f N) :
    P.IsScSmoothOn realPolyfold f U := by
  refine MPolyfold.IsScSmoothOn.of_locally hU fun x hx => ?_
  obtain ⟨N, hxN, hN⟩ := h x hx
  exact ⟨N ∩ U, hN.isOpen.inter hU, ⟨hxN, hx⟩, inter_subset_right,
    hN.mono (hN.isOpen.inter hU) inter_subset_left⟩

/-- **A `C^∞` function of the chart coordinate is sc-smooth on the chart domain**: for a chart
`φ` and `H : E₀ → ℝ` of class `C^∞` on the level-`0` Banach space, `H ∘ φ` is sc-smooth on
`dom φ`. -/
theorem isScSmoothOn_chart_contDiff {φ : MChart Z} (hφ : P.IsChart φ) {H : φ.model.E 0 → ℝ}
    (hH : ContDiff ℝ ∞ H) : P.IsScSmoothOn realPolyfold (fun y => H (φ y)) φ.source := by
  refine isScSmoothOn_real_of_charts φ.isOpen_source
    (hH.continuous.comp_continuousOn φ.continuousOn_toFun) fun x hx =>
      ⟨φ, φ.source, hφ, φ.isOpen_source, hx, fun y hy => ⟨hy, hy⟩, ?_⟩
  rw [φ.image_source]
  refine ⟨mapsTo_univ _ _, fun R hR => ?_⟩
  have hout : IsScSmooth (E := φ.model.E) (F := ScBanach.const ℝ) univ H :=
    IsScSmooth.of_contDiffOn_finiteDimensional (isScDomain_univ _) hH.contDiffOn
  have h2 : IsScSmooth (F := ScBanach.const ℝ) R.U (H ∘ R) :=
    IsScSmooth.comp R.isScDomain (isScDomain_univ _) hout R.isScSmooth (mapsTo_univ _ _)
  refine h2.congr R.isScDomain fun u hu => ?_
  have hRu : R u ∈ φ.model.O := hR ▸ R.apply_mem_retract hu
  change H (R u) = H (φ (φ.symm (R u)))
  rw [φ.apply_symm_apply hRu]

end ScFunctions

/-! ### Separation of a compact set from a point by functionals -/

section Separation

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **A compact set and a point outside it are separated by a `C^∞` function**: for `S` compact
and `a ∉ S` there is a `C^∞` function `H ≥ 0` with `H(a) = 1` which vanishes on an open set
containing `S`.  (`H` is a finite product of smooth functions of continuous linear functionals,
which exist by the Hahn–Banach theorem.) -/
theorem exists_contDiff_separating {S : Set E} (hS : IsCompact S) {a : E} (ha : a ∉ S) :
    ∃ H : E → ℝ, ContDiff ℝ ∞ H ∧ (∀ q, 0 ≤ H q) ∧ H a = 1 ∧
      ∃ Zs : Set E, IsOpen Zs ∧ S ⊆ Zs ∧ ∀ q ∈ Zs, H q = 0 := by
  classical
  have hex : ∀ x : E, ∃ g : E →L[ℝ] ℝ, x ≠ a → g (x - a) = ‖x - a‖ := fun x => by
    by_cases hx : x = a
    · exact ⟨0, fun h => absurd hx h⟩
    · obtain ⟨g, -, hg⟩ := exists_dual_vector ℝ (x - a) (norm_ne_zero_iff.2 (sub_ne_zero.2 hx))
      exact ⟨g, fun _ => by simpa using hg⟩
  choose g hg using hex
  have hne : ∀ x ∈ S, x ≠ a := fun x hx h => ha (h ▸ hx)
  have hnorm : ∀ x ∈ S, 0 < ‖x - a‖ := fun x hx => norm_pos_iff.2 (sub_ne_zero.2 (hne x hx))
  set Ux : E → Set E := fun x => {q | ‖x - a‖ / 2 < g x (q - a)} with hUx
  have hUo : ∀ x, IsOpen (Ux x) := fun x =>
    isOpen_lt continuous_const ((g x).continuous.comp (continuous_id.sub continuous_const))
  obtain ⟨t, htS, htc⟩ := hS.elim_nhds_subcover Ux fun x hx => (hUo x).mem_nhds (by
    change ‖x - a‖ / 2 < g x (x - a)
    rw [hg x (hne x hx)]
    linarith [hnorm x hx])
  refine ⟨fun q => ∏ x ∈ t, Real.smoothTransition (1 - 2 * g x (q - a) / ‖x - a‖), ?_,
    fun q => Finset.prod_nonneg fun x _ => Real.smoothTransition.nonneg _, ?_,
    ⋃ x ∈ t, Ux x, isOpen_biUnion fun x _ => hUo x, htc, fun q hq => ?_⟩
  · refine contDiff_prod fun x _ => Real.smoothTransition.contDiff.comp ?_
    exact contDiff_const.sub ((contDiff_const.mul
      ((g x).contDiff.comp (contDiff_id.sub contDiff_const))).div_const _)
  · refine Finset.prod_eq_one fun x _ => ?_
    rw [sub_self, map_zero, mul_zero, zero_div, sub_zero]
    exact Real.smoothTransition.one_of_one_le le_rfl
  · obtain ⟨x, hxt, hqx⟩ := mem_iUnion₂.1 hq
    refine Finset.prod_eq_zero hxt (Real.smoothTransition.zero_of_nonpos ?_)
    have hpos := hnorm x (htS x hxt)
    have hq' : ‖x - a‖ / 2 < g x (q - a) := hqx
    have : 1 ≤ 2 * g x (q - a) / ‖x - a‖ := by
      rw [le_div_iff₀ hpos]
      linarith
    linarith

end Separation

/-! ### The local function -/

section LocalBump

variable {Z : Type u} [TopologicalSpace Z] [T2Space Z] [ParacompactSpace Z] {P : MPolyfold Z}

/-- **A function concentrated near `p` and sc-smooth near `S`** (Remark 9.5.19, 2021 p. 451):
let `S ⊆ X` lie, near `p`, in a compact set, and let `V` be an open neighbourhood of `p`.  Then
there are `f : X → [0, ∞)` with `f(p) = 1`, vanishing off a closed subset `C ⊆ V`, and an open
`O ⊇ S` on which `f` is sc-smooth. -/
theorem exists_local_bump {S : Set Z} {p : Z} {V : Set Z} (hV : IsOpen V) (hpV : p ∈ V)
    (hloc : ∃ W : Set Z, IsOpen W ∧ p ∈ W ∧ ∃ K : Set Z, IsCompact K ∧ S ∩ W ⊆ K) :
    ∃ (f : Z → ℝ) (O C : Set Z), IsOpen O ∧ S ⊆ O ∧ P.IsScSmoothOn realPolyfold f O ∧
      (∀ y, 0 ≤ f y) ∧ f p = 1 ∧ IsClosed C ∧ support f ⊆ C ∧ C ⊆ V := by
  classical
  obtain ⟨W, hW, hpW, K, hK, hSK⟩ := hloc
  obtain ⟨φ, hφ, hpφ⟩ := P.exists_isChart_mem_source p
  have hG : V ∩ W ∩ φ.source ∈ 𝓝 p :=
    ((hV.inter hW).inter φ.isOpen_source).mem_nhds ⟨⟨hpV, hpW⟩, hpφ⟩
  obtain ⟨t, ht, htc, htG⟩ := exists_mem_nhds_isClosed_subset hG
  set V₁ := interior t with hV₁
  have hV₁o : IsOpen V₁ := isOpen_interior
  have hpV₁ : p ∈ V₁ := mem_interior_iff_mem_nhds.2 ht
  have hcl : closure V₁ ⊆ V ∩ W ∩ φ.source :=
    (closure_minimal interior_subset htc).trans htG
  have hfr : frontier V₁ ⊆ closure V₁ := frontier_subset_closure
  -- the compact set `φ(K ∩ ∂V₁)` does not contain `φ(p)`
  have hS₀ : IsCompact (φ '' (K ∩ frontier V₁)) :=
    (hK.inter_right isClosed_frontier).image_of_continuousOn
      (φ.continuousOn_toFun.mono fun y hy => (hcl (hfr hy.2)).2)
  have hp₀ : φ p ∉ φ '' (K ∩ frontier V₁) := by
    rintro ⟨y, ⟨-, hy⟩, hyp⟩
    have hyφ : y ∈ φ.source := (hcl (hfr hy)).2
    have : y = p := by rw [← φ.symm_apply_apply hyφ, hyp, φ.symm_apply_apply hpφ]
    rw [this, frontier, hV₁o.interior_eq] at hy
    exact hy.2 hpV₁
  obtain ⟨H, hH, hH0, hHp, Zs, hZs, hSZ, hHZ⟩ := exists_contDiff_separating hS₀ hp₀
  have hZ'o : IsOpen (φ.source ∩ φ ⁻¹' Zs) :=
    φ.continuousOn_toFun.isOpen_inter_preimage φ.isOpen_source hZs
  set f : Z → ℝ := V₁.indicator fun y => H (φ y) with hf
  have hclo : IsOpen (closure V₁)ᶜ := isClosed_closure.isOpen_compl
  refine ⟨f, V₁ ∪ (closure V₁)ᶜ ∪ (φ.source ∩ φ ⁻¹' Zs), closure V₁,
    (hV₁o.union hclo).union hZ'o, fun y hy => ?_, ?_,
    fun y => indicator_nonneg (fun z _ => hH0 _) y, ?_, isClosed_closure, ?_,
    fun y hy => (hcl hy).1.1⟩
  · by_cases h1 : y ∈ V₁
    · exact Or.inl (Or.inl h1)
    by_cases h2 : y ∈ closure V₁
    · have hyfr : y ∈ frontier V₁ := by
        rw [frontier, hV₁o.interior_eq]; exact ⟨h2, h1⟩
      refine Or.inr ⟨(hcl h2).2, hSZ ⟨y, ⟨hSK ⟨hy, (hcl h2).1.2⟩, hyfr⟩, rfl⟩⟩
    · exact Or.inl (Or.inr h2)
  · refine isScSmoothOn_of_nhds ((hV₁o.union hclo).union hZ'o) ?_
    rintro x ((hx | hx) | hx)
    · refine ⟨V₁, hx, ((isScSmoothOn_chart_contDiff hφ hH).mono hV₁o
        fun y hy => (hcl (subset_closure hy)).2).congr fun y hy => ?_⟩
      rw [hf, indicator_of_mem hy]
    · refine ⟨(closure V₁)ᶜ, hx, (real_const hclo 0).congr fun y hy => ?_⟩
      rw [hf, indicator_of_notMem fun h => hy (subset_closure h)]
    · refine ⟨φ.source ∩ φ ⁻¹' Zs, hx, (real_const hZ'o 0).congr fun y hy => ?_⟩
      by_cases h1 : y ∈ V₁
      · rw [hf, indicator_of_mem h1]; exact (hHZ _ hy.2).symm
      · rw [hf, indicator_of_notMem h1]
  · rw [hf, indicator_of_mem hpV₁]; exact hHp
  · intro y hy
    refine subset_closure ?_
    by_contra h
    have h0 : f y = 0 := indicator_of_notMem h _
    exact hy h0

end LocalBump

end LocalPart

end Polyfold
