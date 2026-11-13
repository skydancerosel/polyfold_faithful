import Polyfold.Chapter5.PartitionsOfUnity

/-!
# Theorem 5.5.10 "(1) ⇒ (2)" for every chart

2021 Theorem 5.5.10, p. 232 (2017: Theorem 5.12; preprint: Theorem 5.37).  The proof of
"(1) ⇒ (2)" takes an atlas of charts `φ : U → O` and shows that their local models have the
sc-smooth approximation property.  It extends `f ∘ φ` by `0` to `X` and uses `cl_X(φ⁻¹(V)) ⊆ U`.
That inclusion does not follow from `cl_C(V) ⊆ O` (Findings, Chapter 5, item 111), and the project
proved the property only for charts restricted to open sets `s` with `cl_X(s) ⊆ dom φ`
(`hasApproxProperty_restrict`).  This file proves it for **every** chart (row V5.55).

## What is formalized

* `MPolyfold.AdmitsScPartitionsOfUnity.exists_urysohn`: sc-smooth Urysohn functions.
* `MPolyfold.AdmitsScPartitionsOfUnity.exists_approx`: a continuous `F : X → [0, 1]` with support
  in an open `T` is uniformly approximated by sc-smooth `g : X → [0, 1]` with support in `T` (the
  core of the text's argument).
* `exists_continuous_pos_iff`: an open subset of a metrizable space is `{d > 0}` for a continuous
  `d ≥ 0`.
* `hasApproxProperty_of_isChart`: if `X` admits sc-smooth partitions of unity, the local model of
  every chart of `X` has the sc-smooth approximation property.
* `theorem_5_5_10_every_chart`: Theorem 5.5.10 with "(2)" for the atlas of all charts.

## The proof

The text's argument works on the chart domain `U` once partitions of unity are available on `U`.
Here they are replaced by a partition of unity of `U` in shells, built from functions on `X`.
With `d ≥ 0` continuous, `U = {d > 0}`, let `κₙ` be sc-smooth Urysohn functions on `X` with
`κₙ = 1` on `{d ≥ 1/(n+1)}` and `κₙ = 0` on `{d ≤ 1/(n+2)}`, and
`λₙ = κₙ ∏_{j<n}(1 − κⱼ)`.  The `λₙ` are sc-smooth on `X`, vanish off `U`, are locally finite on
`U` (not on `X`), and `Σₙ λₙ = 1` on `U`.  On the shell where `λₙ ≠ 0`, `F = f ∘ φ` (extended by
`0`) agrees with the continuous `Fₙ = F·κₙ₊₁` on `X`, whose support is a closed subset of `X`
inside `φ⁻¹(V)`; `Fₙ` is approximated within `ε` by `ĝₙ` (the text's argument, on `X`).  Then
`g = Σₙ λₙ ĝₙ` is within `ε` of `F` on `U`, and `g ∘ φ⁻¹` is sc-smooth on `O` because near every
point of `O` it is a finite sum (`IsScSmoothRetractMap.of_locally`).
-/

open Set Function Filter Topology

noncomputable section

namespace Polyfold

universe u

section Helpers

/-- A convex combination over a finite set: `Σ wᵢcᵢ` is within `δ` of `F` if every `cᵢ` with
`wᵢ ≠ 0` is. -/
lemma abs_sub_sum_mul_le {ι : Type*} (S : Finset ι) (w c : ι → ℝ) (hw : ∀ i, 0 ≤ w i)
    (hw1 : ∑ i ∈ S, w i = 1) (F : ℝ) {δ : ℝ} (h : ∀ i, w i ≠ 0 → |F - c i| ≤ δ) :
    |F - ∑ i ∈ S, w i * c i| ≤ δ := by
  have h2 : F - ∑ i ∈ S, w i * c i = ∑ i ∈ S, w i * (F - c i) := by
    simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hw1, one_mul]
  rw [h2]
  calc |∑ i ∈ S, w i * (F - c i)| ≤ ∑ i ∈ S, |w i * (F - c i)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ S, w i * δ := Finset.sum_le_sum fun i _ => by
        rw [abs_mul, abs_of_nonneg (hw i)]
        by_cases hi : w i = 0
        · rw [hi, zero_mul, zero_mul]
        · exact mul_le_mul_of_nonneg_left (h i hi) (hw i)
    _ = δ := by rw [← Finset.sum_mul, hw1, one_mul]

/-- A convex combination over a finite set of numbers in `[0, 1]` lies in `[0, 1]`. -/
lemma sum_mul_mem_Icc {ι : Type*} (S : Finset ι) (w c : ι → ℝ) (hw : ∀ i, 0 ≤ w i)
    (hw1 : ∑ i ∈ S, w i = 1) (hc : ∀ i, c i ∈ Icc (0 : ℝ) 1) :
    ∑ i ∈ S, w i * c i ∈ Icc (0 : ℝ) 1 := by
  refine ⟨Finset.sum_nonneg fun i _ => mul_nonneg (hw i) (hc i).1, ?_⟩
  calc ∑ i ∈ S, w i * c i ≤ ∑ i ∈ S, w i :=
        Finset.sum_le_sum fun i _ => mul_le_of_le_one_right (hw i) (hc i).2
    _ = 1 := hw1

/-- **An open subset of a metrizable space is a cozero set**: `U = {d > 0}` for a continuous
`d ≥ 0` (the distance to the complement). -/
theorem exists_continuous_pos_iff {X : Type*} [TopologicalSpace X]
    [TopologicalSpace.MetrizableSpace X] {U : Set X} (hU : IsOpen U) :
    ∃ d : X → ℝ, Continuous d ∧ (∀ x, 0 ≤ d x) ∧ ∀ x, x ∈ U ↔ 0 < d x := by
  let _ := TopologicalSpace.metrizableSpaceMetric X
  by_cases hne : (Uᶜ).Nonempty
  · refine ⟨fun x => Metric.infDist x Uᶜ, Metric.continuous_infDist_pt _,
      fun x => Metric.infDist_nonneg, fun x => ?_⟩
    rw [← hU.isClosed_compl.notMem_iff_infDist_pos hne, mem_compl_iff, not_not]
  · rw [not_nonempty_iff_eq_empty, compl_empty_iff] at hne
    exact ⟨fun _ => 1, continuous_const, fun _ => zero_le_one, fun x => by simp [hne]⟩

end Helpers

section ScFunctions

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}

/-- **Sc-smooth Urysohn functions** from sc-smooth partitions of unity: for disjoint closed
`s, t ⊆ X` there is an sc-smooth `F : X → [0, 1]` with `F = 0` on `s` and `F = 1` on `t` (the
function attached to `X ∖ s` of a partition of unity subordinate to `{X ∖ s, X ∖ t}`). -/
theorem MPolyfold.AdmitsScPartitionsOfUnity.exists_urysohn (h : PX.AdmitsScPartitionsOfUnity)
    {s t : Set X} (hs : IsClosed s) (ht : IsClosed t) (hst : Disjoint s t) :
    ∃ F : X → ℝ, PX.IsScSmoothMap realPolyfold F ∧ EqOn F 0 s ∧ EqOn F 1 t ∧
      ∀ x, F x ∈ Icc (0 : ℝ) 1 := by
  let V : ULift Bool → Set X := fun i => if i.down then sᶜ else tᶜ
  have hVo : ∀ i, IsOpen (V i) := by
    rintro ⟨_ | _⟩
    · exact ht.isOpen_compl
    · exact hs.isOpen_compl
  have hVcov : ⋃ i, V i = univ := by
    refine eq_univ_of_forall fun y => mem_iUnion.2 ?_
    by_cases hy : y ∈ s
    · exact ⟨⟨false⟩, fun hyt => Set.disjoint_left.1 hst hy hyt⟩
    · exact ⟨⟨true⟩, hy⟩
  obtain ⟨ρ, hρsub, hρsc⟩ := h _ V hVo hVcov
  refine ⟨ρ ⟨true⟩, hρsc _, fun y hy => ?_, fun y hy => ?_,
    fun y => ⟨ρ.nonneg _ y, ρ.le_one _ y⟩⟩
  · exact image_eq_zero_of_notMem_tsupport fun h' => (hρsub ⟨true⟩ h' : y ∈ sᶜ) hy
  · have h0 : ρ ⟨false⟩ y = 0 :=
      image_eq_zero_of_notMem_tsupport fun h' => (hρsub ⟨false⟩ h' : y ∈ tᶜ) hy
    have h1 := ρ.sum_eq_one (mem_univ y)
    rw [finsum_eq_sum_of_support_subset (s := Finset.univ) _ (by simp)] at h1
    have h2 : ∑ i : ULift Bool, ρ i y = ρ ⟨true⟩ y + ρ ⟨false⟩ y := by
      rw [← (Equiv.ulift (α := Bool)).symm.sum_comp]
      simp
    rw [h2, h0, add_zero] at h1
    exact h1

/-- **The approximation step of Theorem 5.5.10 (2021 p. 232) on `X`**: if `X` admits sc-smooth
partitions of unity, a continuous `F : X → [0, 1]` with support in an open `T` is within `δ` of an
sc-smooth `g : X → [0, 1]` with support in `T`.  (The text's argument: the cover `{F < δ}`,
`T ∩ {|F − F(x)| < δ}`, a subordinate sc-smooth partition of unity `(β₀, β_x)`, and
`g = Σ β_x F(x)`.) -/
theorem MPolyfold.AdmitsScPartitionsOfUnity.exists_approx (h : PX.AdmitsScPartitionsOfUnity)
    {F : X → ℝ} (hF : Continuous F) (hF01 : ∀ y, F y ∈ Icc (0 : ℝ) 1) {T : Set X} (hT : IsOpen T)
    (hFT : tsupport F ⊆ T) {δ : ℝ} (hδ : 0 < δ) :
    ∃ g : X → ℝ, PX.IsScSmoothMap realPolyfold g ∧ (∀ y, g y ∈ Icc (0 : ℝ) 1) ∧
      tsupport g ⊆ T ∧ ∀ y, |F y - g y| ≤ δ := by
  let U : Option X → Set X := fun i => match i with
    | none => {y | F y < δ}
    | some x => T ∩ {y | |F y - F x| < δ}
  have hUo : ∀ i, IsOpen (U i) := by
    rintro (_ | x)
    · exact isOpen_lt hF continuous_const
    · exact hT.inter (isOpen_lt ((hF.sub continuous_const).abs) continuous_const)
  have hUcov : ⋃ i, U i = univ := by
    refine eq_univ_of_forall fun y => mem_iUnion.2 ?_
    by_cases hy : F y < δ
    · exact ⟨none, hy⟩
    · have hFy : F y ≠ 0 := fun h' => hy (by rw [h']; exact hδ)
      refine ⟨some y, hFT (subset_closure hFy), ?_⟩
      change |F y - F y| < δ
      rw [sub_self, abs_zero]; exact hδ
  obtain ⟨ρ, hρsub, hρsc⟩ := h (Option X) U hUo hUcov
  let c : Option X → ℝ := fun i => match i with
    | none => 0
    | some x => F x
  have hc01 : ∀ i, c i ∈ Icc (0 : ℝ) 1 := by
    rintro (_ | x)
    · exact ⟨le_rfl, zero_le_one⟩
    · exact hF01 x
  refine ⟨fun y => ∑ᶠ i, ρ i y * c i,
    isScSmoothMap_real_finsum (fun i => (hρsc i).real_mul (isScSmoothMap_real_const (c i)))
      (PartitionOfUnity.locallyFinite_mul ρ c),
    fun y => PartitionOfUnity.finsum_mul_mem_Icc ρ c hc01 y, ?_, fun y => ?_⟩
  · refine PartitionOfUnity.tsupport_finsum_mul_subset ρ c fun i hci => ?_
    rcases i with _ | x
    · exact absurd rfl hci
    · exact (hρsub (some x)).trans inter_subset_left
  · refine PartitionOfUnity.abs_sub_finsum_mul_le ρ c (F y) y fun i hi => ?_
    have hyU : y ∈ U i := hρsub i (subset_closure hi)
    rcases i with _ | x
    · change F y < δ at hyU
      change |F y - 0| ≤ δ
      rw [sub_zero, abs_of_nonneg (hF01 y).1]; exact hyU.le
    · exact hyU.2.le

end ScFunctions

section EveryChart

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}

set_option maxHeartbeats 800000 in
-- one proof assembling the shells, the approximations and the chart transfer
/-- **2021 Theorem 5.5.10 "(1) ⇒ (2)", p. 232 (preprint 5.37), for every chart.**  If the
M-polyfold `X` admits sc-smooth partitions of unity, then the local model `(O, C, E)` of every
chart `φ : U → O` of `X` has the sc-smooth approximation property (Definition 5.5.9).  The text
proves this for the charts of an atlas with an extension by `0` that needs `cl_X(φ⁻¹(V)) ⊆ U`,
which does not follow from `cl_C(V) ⊆ O` (Findings, Chapter 5, item 111); the proof here uses a
partition of unity of `U` in shells (module docstring). -/
theorem hasApproxProperty_of_isChart (h : PX.AdmitsScPartitionsOfUnity) {φ : MChart X}
    (hφ : PX.IsChart φ) : φ.model.HasApproxProperty := by
  classical
  intro W hW hWcl f hf hf01 hfsupp ε hε
  have := PX.metrizableSpace
  set U := φ.source with hUdef
  have hUo : IsOpen U := φ.isOpen_source
  obtain ⟨d, hdc, hd0, hdU⟩ := exists_continuous_pos_iff hUo
  -- the shells: `κₙ = 1` on `{d ≥ 1/(n+1)}`, `κₙ = 0` on `{d ≤ 1/(n+2)}`
  have hκex : ∀ n : ℕ, ∃ κ : X → ℝ, PX.IsScSmoothMap realPolyfold κ ∧
      EqOn κ 0 {y | d y ≤ 1 / ((n : ℝ) + 2)} ∧ EqOn κ 1 {y | 1 / ((n : ℝ) + 1) ≤ d y} ∧
      ∀ y, κ y ∈ Icc (0 : ℝ) 1 := fun n =>
    h.exists_urysohn (isClosed_le hdc continuous_const) (isClosed_le continuous_const hdc)
      (Set.disjoint_left.2 fun y hy1 hy2 => by
        have h1 : 1 / ((n : ℝ) + 2) < 1 / ((n : ℝ) + 1) :=
          one_div_lt_one_div_of_lt (by positivity) (by linarith)
        exact absurd (hy2.trans hy1) (not_le.2 h1))
  choose κ hκsc hκ0 hκ1 hκ01 using hκex
  -- `λₙ = κₙ ∏_{j<n}(1 − κⱼ)`
  set lam : ℕ → X → ℝ := fun n y => κ n y * ∏ j ∈ Finset.range n, (1 - κ j y) with hlamdef
  have hlamsc : ∀ n, PX.IsScSmoothMap realPolyfold (lam n) := fun n =>
    (hκsc n).real_mul (isScSmoothMap_real_finsetProd _ fun j _ =>
      (isScSmoothMap_real_const 1).real_sub (hκsc j))
  have hprod01 : ∀ (N : ℕ) y, 0 ≤ ∏ j ∈ Finset.range N, (1 - κ j y) ∧
      ∏ j ∈ Finset.range N, (1 - κ j y) ≤ 1 := fun N y =>
    ⟨Finset.prod_nonneg fun j _ => by linarith [(hκ01 j y).2],
      Finset.prod_le_one (fun j _ => by linarith [(hκ01 j y).2])
        fun j _ => by linarith [(hκ01 j y).1]⟩
  have hlam0 : ∀ n y, 0 ≤ lam n y := fun n y => mul_nonneg (hκ01 n y).1 (hprod01 n y).1
  -- the telescoping sum
  have htel : ∀ (N : ℕ) y, ∑ n ∈ Finset.range N, lam n y =
      1 - ∏ j ∈ Finset.range N, (1 - κ j y) := by
    intro N y
    induction N with
    | zero => simp
    | succ N ih =>
      rw [Finset.sum_range_succ, ih, Finset.prod_range_succ]
      simp only [hlamdef]
      ring
  -- where `λₙ ≠ 0`
  have hlam_supp : ∀ n y, lam n y ≠ 0 → 1 / ((n : ℝ) + 2) < d y ∧
      ∀ j < n, d y < 1 / ((j : ℝ) + 1) := by
    intro n y hne
    refine ⟨?_, fun j hj => ?_⟩
    · by_contra hle
      exact hne (by simp only [hlamdef, hκ0 n (not_lt.1 hle), Pi.zero_apply, zero_mul])
    · by_contra hle
      refine hne ?_
      simp only [hlamdef]
      rw [Finset.prod_eq_zero (Finset.mem_range.2 hj)
        (by rw [hκ1 j (not_lt.1 hle), Pi.one_apply, sub_self]), mul_zero]
  -- near `y ∈ U` only `λ₀, …, λ_{K-1}` are non-zero, and they sum to `1` at `y`
  have hnum : ∀ r : ℝ, 0 < r → 1 / (((⌈2 / r⌉₊ : ℕ) : ℝ) + 1) < r / 2 := fun r hr => by
    have h1 : 2 / r ≤ ((⌈2 / r⌉₊ : ℕ) : ℝ) := Nat.le_ceil _
    rw [div_lt_iff₀ (by positivity)]
    have h2 : 2 / r * r = 2 := div_mul_cancel₀ 2 hr.ne'
    nlinarith
  have hloc : ∀ y ∈ U, ∀ z, d y / 2 < d z → ∀ n, ⌈2 / d y⌉₊ + 1 ≤ n → lam n z = 0 := by
    intro y hy z hz n hn
    by_contra hne
    have h1 := (hlam_supp n z hne).2 ⌈2 / d y⌉₊ (by omega)
    have h2 := hnum (d y) ((hdU y).1 hy)
    linarith
  have hsum1 : ∀ y ∈ U, ∑ n ∈ Finset.range (⌈2 / d y⌉₊ + 1), lam n y = 1 := by
    intro y hy
    have hdy := (hdU y).1 hy
    rw [htel, Finset.prod_eq_zero (Finset.mem_range.2 (Nat.lt_succ_self ⌈2 / d y⌉₊)), sub_zero]
    rw [hκ1 _ (show 1 / (((⌈2 / d y⌉₊ : ℕ) : ℝ) + 1) ≤ d y by
      linarith [hnum (d y) hdy]), Pi.one_apply, sub_self]
  -- `F = f ∘ φ` extended by `0`, and its support
  set F : X → ℝ := U.indicator (f ∘ φ) with hFdef
  have hFcU : ContinuousOn (f ∘ φ) U :=
    hf.comp φ.continuousOn_toFun fun y hy => φ.mapsTo_model y hy
  have hF01 : ∀ y, F y ∈ Icc (0 : ℝ) 1 := fun y => by
    by_cases hy : y ∈ U
    · rw [hFdef, indicator_of_mem hy]; exact hf01 _ (φ.mapsTo_model y hy)
    · rw [hFdef, indicator_of_notMem hy]; exact ⟨le_rfl, zero_le_one⟩
  set T := U ∩ φ ⁻¹' W with hTdef
  have hTo : IsOpen T := φ.continuousOn_toFun.isOpen_inter_preimage hUo hW
  have hclT : ∀ y ∈ U, y ∈ closure (support F) → y ∈ T := by
    intro y hy hcl
    have hcont : ContinuousAt φ y := φ.continuousOn_toFun.continuousAt (hUo.mem_nhds hy)
    have h1 := mem_closure_image hcont hcl
    have h2 : φ '' support F ⊆ φ.model.O ∩ support f := by
      rintro _ ⟨z, hz, rfl⟩
      have hzU : z ∈ U := by
        by_contra hzU; exact hz (by rw [hFdef, indicator_of_notMem hzU])
      refine ⟨φ.mapsTo_model z hzU, ?_⟩
      have := mem_support.1 hz
      rwa [hFdef, indicator_of_mem hzU] at this
    exact ⟨hy, hfsupp ⟨closure_mono h2 h1, φ.mapsTo_model y hy⟩⟩
  -- `Fₙ = F κₙ₊₁`: continuous on `X`, supported in `T`, equal to `F` where `λₙ ≠ 0`
  set Fn : ℕ → X → ℝ := fun n y => F y * κ (n + 1) y with hFndef
  have hFncont : ∀ n, Continuous (Fn n) := by
    intro n
    have hκc : Continuous (κ (n + 1)) := continuousOn_univ.1 (hκsc (n + 1)).continuousOn
    refine continuous_iff_continuousAt.2 fun y => ?_
    by_cases hy : y ∈ U
    · have hFat : ContinuousAt F y := by
        refine (hFcU.continuousAt (hUo.mem_nhds hy)).congr ?_
        filter_upwards [hUo.mem_nhds hy] with z hz
        rw [hFdef, indicator_of_mem hz]
      exact hFat.mul hκc.continuousAt
    · have hdy : d y = 0 := le_antisymm (not_lt.1 fun h' => hy ((hdU y).2 h')) (hd0 y)
      have hlt : d y < 1 / (((n + 1 : ℕ) : ℝ) + 2) := by rw [hdy]; positivity
      refine continuousAt_const.congr (f := fun _ => (0 : ℝ)) ?_
      filter_upwards [(isOpen_lt hdc continuous_const).mem_nhds hlt] with z hz
      simp only [hFndef, hκ0 (n + 1) (le_of_lt hz), Pi.zero_apply, mul_zero]
  have hFn01 : ∀ n y, Fn n y ∈ Icc (0 : ℝ) 1 := fun n y =>
    ⟨mul_nonneg (hF01 y).1 (hκ01 _ y).1,
      mul_le_one₀ (hF01 y).2 (hκ01 _ y).1 (hκ01 _ y).2⟩
  have hFnT : ∀ n, tsupport (Fn n) ⊆ T := by
    intro n
    have hsub : support (Fn n) ⊆ support F ∩ {y | 1 / (((n + 1 : ℕ) : ℝ) + 2) ≤ d y} := by
      intro y hy
      have hy' := mem_support.1 hy
      refine ⟨fun h0 => hy' (by simp only [hFndef, h0, zero_mul]), ?_⟩
      by_contra hle
      have hlt : d y < 1 / (((n + 1 : ℕ) : ℝ) + 2) := not_le.1 hle
      exact hy' (by simp only [hFndef, hκ0 (n + 1) (le_of_lt hlt), Pi.zero_apply, mul_zero])
    intro y hy
    have hy' := closure_mono hsub hy
    have h2 : y ∈ {y | 1 / (((n + 1 : ℕ) : ℝ) + 2) ≤ d y} :=
      (closure_minimal inter_subset_right (isClosed_le continuous_const hdc)) hy'
    have hyU : y ∈ U := (hdU y).2 (lt_of_lt_of_le (by positivity) h2)
    exact hclT y hyU (closure_mono inter_subset_left hy')
  have hFnF : ∀ n y, lam n y ≠ 0 → Fn n y = F y := by
    intro n y hne
    have h1 := (hlam_supp n y hne).1
    have he : ((n + 1 : ℕ) : ℝ) + 1 = (n : ℝ) + 2 := by push_cast; ring
    have h2 : 1 / (((n + 1 : ℕ) : ℝ) + 1) ≤ d y := by rw [he]; exact h1.le
    simp only [hFndef, hκ1 (n + 1) h2, Pi.one_apply, mul_one]
  -- the approximations `ĝₙ`
  have hgex : ∀ n, ∃ g : X → ℝ, PX.IsScSmoothMap realPolyfold g ∧ (∀ y, g y ∈ Icc (0 : ℝ) 1) ∧
      tsupport g ⊆ T ∧ ∀ y, |Fn n y - g y| ≤ ε := fun n =>
    h.exists_approx (hFncont n) (hFn01 n) hTo (hFnT n) hε
  choose gh hghsc hgh01 hghT hghF using hgex
  -- `g = Σ λₙ ĝₙ` and its local form
  set g : X → ℝ := fun y => ∑ᶠ n, lam n y * gh n y with hgdef
  have hgloc : ∀ y ∈ U, ∀ z, d y / 2 < d z →
      g z = ∑ n ∈ Finset.range (⌈2 / d y⌉₊ + 1), lam n z * gh n z := by
    intro y hy z hz
    refine finsum_eq_sum_of_support_subset _ fun n hn => ?_
    rw [Finset.coe_range, mem_Iio]
    by_contra hge
    exact hn (show lam n z * gh n z = 0 by rw [hloc y hy z hz n (not_lt.1 hge), zero_mul])
  -- the estimate and the values on `U`
  have hgU : ∀ y ∈ U, |F y - g y| ≤ ε ∧ g y ∈ Icc (0 : ℝ) 1 := by
    intro y hy
    have hdy := (hdU y).1 hy
    rw [hgloc y hy y (by linarith)]
    refine ⟨abs_sub_sum_mul_le _ _ _ (fun n => hlam0 n y) (hsum1 y hy) _ fun n hn => ?_,
      sum_mul_mem_Icc _ _ _ (fun n => hlam0 n y) (hsum1 y hy) fun n => hgh01 n y⟩
    rw [← hFnF n y hn]; exact hghF n y
  -- the open neighbourhoods `V_y = U ∩ {d > d(y)/2}`
  have hVo : ∀ y : X, IsOpen (U ∩ {z | d y / 2 < d z}) := fun y =>
    hUo.inter (isOpen_lt continuous_const hdc)
  refine ⟨g ∘ φ.symm, ?_, fun z hz => ?_, ?_, fun z hz => ?_⟩
  · -- sc-smooth: near every point of `O`, a finite sum
    refine IsScSmoothRetractMap.of_locally (mapsTo_univ _ _) fun z hz => ?_
    set y := φ.symm z with hy
    have hyU : y ∈ U := φ.symm_mapsTo hz
    have hdy := (hdU y).1 hyU
    obtain ⟨W', hW'o, hW'eq⟩ := φ.exists_isOpen_image_eq (s := U ∩ {z | d y / 2 < d z})
      inter_subset_left (hVo y)
    have hzW : z ∈ φ.model.O ∩ W' := by
      rw [← hW'eq]
      exact ⟨y, ⟨hyU, show d y / 2 < d y by linarith⟩, φ.apply_symm_apply hz⟩
    refine ⟨W', hW'o, hzW.2, ?_⟩
    rw [← hW'eq]
    have hG : PX.IsScSmoothMap realPolyfold
        fun x => ∑ n ∈ Finset.range (⌈2 / d y⌉₊ + 1), lam n x * gh n x :=
      isScSmoothMap_real_finsetSum _ fun n _ => (hlamsc n).real_mul (hghsc n)
    refine (hG.real_chart_on hφ (hVo y) inter_subset_left).congr ?_
    rintro _ ⟨x, hx, rfl⟩
    simp only [Function.comp_apply, φ.symm_apply_apply hx.1]
    exact (hgloc y hyU x hx.2).symm
  · -- values in `[0, 1]`
    exact (hgU _ (φ.symm_mapsTo hz)).2
  · -- the support lies in `W`
    rintro z ⟨hz, hzO⟩
    set y := φ.symm z with hy
    have hyU : y ∈ U := φ.symm_mapsTo hzO
    have hdy := (hdU y).1 hyU
    have hcw : ContinuousWithinAt φ.symm (φ.model.O ∩ support (g ∘ φ.symm)) z :=
      (φ.continuousOn_invFun z hzO).mono inter_subset_left
    have h1 := hcw.mem_closure_image hz
    have h2 : φ.symm '' (φ.model.O ∩ support (g ∘ φ.symm)) ⊆ support g := by
      rintro _ ⟨z', hz', rfl⟩; exact hz'.2
    have hycl : y ∈ closure (support g) := closure_mono h2 h1
    -- near `y`, `supp g` lies in the closed set `⋃_{n<K} supp ĝₙ ⊆ T`
    set K := ⌈2 / d y⌉₊ + 1 with hK
    set C := ⋃ n ∈ Finset.range K, tsupport (gh n) with hCdef
    have hCc : IsClosed C := isClosed_biUnion_finset fun n _ => isClosed_tsupport _
    have hyC : y ∈ C := by
      by_contra hyC
      have hN : (U ∩ {z | d y / 2 < d z}) ∩ Cᶜ ∈ 𝓝 y :=
        ((hVo y).inter hCc.isOpen_compl).mem_nhds ⟨⟨hyU, show d y / 2 < d y by linarith⟩, hyC⟩
      obtain ⟨x, ⟨hxV, hxC⟩, hxg⟩ := mem_closure_iff_nhds.1 hycl _ hN
      refine hxg ?_
      rw [hgloc y hyU x hxV.2]
      refine Finset.sum_eq_zero fun n hn => ?_
      have : gh n x = 0 := image_eq_zero_of_notMem_tsupport fun h' =>
        hxC (mem_iUnion₂.2 ⟨n, hn, h'⟩)
      rw [this, mul_zero]
    obtain ⟨n, -, hn⟩ := mem_iUnion₂.1 hyC
    have h3 : φ y ∈ W := (hghT n hn).2
    rwa [hy, φ.apply_symm_apply hzO] at h3
  · -- the estimate
    have hyU : φ.symm z ∈ U := φ.symm_mapsTo hz
    have h1 := (hgU _ hyU).1
    rw [hFdef, indicator_of_mem hyU, Function.comp_apply, φ.apply_symm_apply hz] at h1
    exact h1

/-- **2021 Theorem 5.5.10, p. 232 (preprint 5.37), with the atlas of all charts**: `X` admits
sc-smooth partitions of unity if and only if the local models of all charts of `X` have the
sc-smooth approximation property.  ("(1) ⇒ (2)" for every chart is `hasApproxProperty_of_isChart`;
"(2) ⇒ (1)" is `admitsScPartitionsOfUnity_of_approx`.) -/
theorem theorem_5_5_10_every_chart :
    PX.AdmitsScPartitionsOfUnity ↔ ∀ φ : MChart X, PX.IsChart φ → φ.model.HasApproxProperty := by
  constructor
  · exact fun h φ hφ => hasApproxProperty_of_isChart h hφ
  · intro h
    exact admitsScPartitionsOfUnity_of_approx (S := {φ | PX.IsChart φ}) (fun φ hφ => hφ)
      (fun x => PX.exists_isChart_mem_source x) fun φ hφ => h φ hφ

end EveryChart

end Polyfold
