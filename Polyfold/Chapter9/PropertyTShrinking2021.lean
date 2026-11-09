import Polyfold.Chapter9.BranchingGeometry
import Polyfold.Chapter9.BoundaryOrientationContinuity2021

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021; 2017 arXiv 1707.08941),
§9.4, Lemma 9.4.3, p. 430 (2017: Lemma 9.12, p. 316).

# Property (T) after shrinking `U(x)`

Lemma 9.4.3 says that an oriented local branching structure at `x` satisfies the technical
condition (T) once `U(x)` is replaced by a smaller neighbourhood.

## What is formalized

* `HasDimAt.eq_of_submanifoldTangent_eq`: two submanifolds with the same tangent set at `y` have the
  same dimension at `y` (so a pair of sheets of different dimensions never meets (T)'s hypothesis).
* `HasDimAt.exists_isOpen_eq_of_mem`: a point where a submanifold is `0`-dimensional is isolated in
  it (the chord estimate `ScRetraction.exists_approx` with `Dr = 0`).
* `exists_chartTangent_field`: the chart tangent spaces `T_zA` vary continuously (frames
  `z ↦ Dt(z) v` from the chart sc⁺-retraction `t` of `A`).
* `exists_isOpen_submanifoldTangent_ne`: if two `n`-dimensional submanifolds have different
  tangent spaces at `x`, they have different tangent spaces at every common point near `x` (a
  frame of one and a vector of the other off it give a nonzero determinant near `x`, which
  vanishes where the tangent spaces agree).
* `SubmanifoldOrientation.exists_isOpen_pairT`: Property (T) for one pair of sheets near `x`; with
  `SubmanifoldOrientation.exists_isOpen_tangent_eq_iff` (equal tangent spaces at `x`) this covers
  all cases.
* `OrientedBranchingStructure.restrict`, the restriction of an oriented branching structure to an
  open `V ∋ x`, and **Lemma 9.4.3** (`OrientedBranchingStructure.lemma_9_4_3`): some open
  `x ∈ U' ⊆ U(x)` has Property (T) for the restricted structure (and `lemma_9_4_3_propertyT`: for
  `B` on `U'`).

The book argues by contradiction along sequences `y_k`, `z_k → x` and the convergence of the
tangent spaces; the proof here is the direct form of the same argument: near `x` the relative
orientation of two sheets is constant where their tangent spaces agree, and the tangent spaces
of two sheets that differ at `x` differ near `x`.
-/

open Set Module Submodule Filter Topology

universe u

namespace Polyfold

namespace MPolyfold

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {P : MPolyfold X}

/-- The dimension of a submanifold at `y` is determined by its tangent set `T_yA`. -/
theorem HasDimAt.eq_of_submanifoldTangent_eq {A₁ A₂ : Set X} {y : X} {n₁ n₂ : ℕ}
    (hA₁ : P.IsSmoothSubmanifold A₁) (hA₂ : P.IsSmoothSubmanifold A₂) (h₁ : P.HasDimAt A₁ y n₁)
    (h₂ : P.HasDimAt A₂ y n₂) (hT : P.submanifoldTangent A₁ y = P.submanifoldTangent A₂ y) :
    n₁ = n₂ := by
  obtain ⟨φ, hφ, hyφ⟩ := P.exists_isChart_mem_source y
  obtain ⟨N₁, hN₁, -⟩ := exists_submodule_chartTangent hφ hA₁ h₁.1 hyφ
  obtain ⟨N₂, hN₂, -⟩ := exists_submodule_chartTangent hφ hA₂ h₂.1 hyφ
  have hN : N₁ = N₂ := SetLike.coe_injective (by
    rw [hN₁, hN₂, (chartTangent_eq_iff hφ hyφ).2 hT])
  rw [← finrank_chartTangent hφ h₁ hA₁ hyφ hN₁, ← finrank_chartTangent hφ h₂ hA₂ hyφ hN₂, hN]

/-- **A `0`-dimensional point is isolated**: if `A` has dimension `0` at `y`, some open `O ∋ y`
meets `A` only in `y`.  (In a chart, `Dt = 0` at `φ(y)` for the chart sc⁺-retraction `t` of `A`,
and the chord estimate gives `‖a − φ(y)‖ ≤ ½ ‖a − φ(y)‖` for `a` in the retract near `φ(y)`.) -/
theorem HasDimAt.exists_isOpen_eq_of_mem {A : Set X} {y : X} (hA : P.IsSmoothSubmanifold A)
    (h : P.HasDimAt A y 0) : ∃ O : Set X, IsOpen O ∧ y ∈ O ∧ ∀ z ∈ A ∩ O, z = y := by
  have hyA := h.1
  obtain ⟨φ, hφ, hyφ⟩ := P.exists_isChart_mem_source y
  set d := hA.data hyA
  have hyV : y ∈ d.V := hA.mem_data_V hyA
  obtain ⟨t, ht, htp⟩ := exists_plusRetraction hφ d hyA hyV
  obtain ⟨hz, hyt, hTr⟩ := chartTangent_eq_range hφ d ht hyA hyV hyφ
  obtain ⟨N, hN, hfin⟩ := exists_submodule_chartTangent hφ hA hyA hyφ
  have hN0 : N = ⊥ := Submodule.finrank_eq_zero.1 (finrank_chartTangent hφ h hA hyφ hN)
  have hD0 : ∀ v, scDeriv t.U t (levelLift φ 1 y) v = 0 := fun v => by
    have hv : scDeriv t.U t (levelLift φ 1 y) v ∈ (N : Set (φ.model.E 0)) := by
      rw [hN, hTr]; exact ⟨v, rfl⟩
    rw [hN0] at hv
    exact hv
  obtain ⟨δ, hδ, happ⟩ := ScRetraction.exists_approx htp (by rw [hz]; exact hyt)
    (ε := 1 / 2) (by norm_num)
  set W := d.toSubData.shrink φ
  refine ⟨W ∩ (φ.source ∩ φ ⁻¹' Metric.ball (φ y) δ), (d.toSubData.isOpen_shrink φ).inter
    (φ.continuousOn_toFun.isOpen_inter_preimage φ.isOpen_source Metric.isOpen_ball),
    ⟨d.toSubData.mem_shrink φ hyA hyV hyφ, hyφ, Metric.mem_ball_self hδ⟩, fun z hz' => ?_⟩
  obtain ⟨hzA, hzW, hzφ, hzδ⟩ := hz'
  have hzt : φ z ∈ t.retract := by rw [ht]; exact ⟨z, ⟨hzW, hzA⟩, rfl⟩
  have hzδ' : ‖φ z - φ.model.E.toBase 1 (levelLift φ 1 y)‖ < δ := by
    rw [hz, ← dist_eq_norm]; exact hzδ
  have hyδ : ‖φ y - φ.model.E.toBase 1 (levelLift φ 1 y)‖ < δ := by
    rw [hz, sub_self, norm_zero]; exact hδ
  have h2 := happ (φ z) hzt (φ y) hyt hzδ' hyδ
  rw [hD0, sub_zero] at h2
  have h0 : ‖φ z - φ y‖ = 0 := by linarith [norm_nonneg (φ z - φ y)]
  exact φ.toPartialEquiv.injOn hzφ hyφ (sub_eq_zero.1 (norm_eq_zero.1 h0))

/-- **The chart tangent spaces of a submanifold vary continuously**: in a chart `ψ` around
`x ∈ A` there are an open `W ∋ x` and continuous linear maps `D z` (`Dt` at the level-`1` lift of
`ψ(z)`, `t` the chart sc⁺-retraction of `A`) with `T_zA = range (D z)` in the chart for
`z ∈ A ∩ W`, `D x = id` on `T_xA`, and `z ↦ D z v` continuous on `A ∩ W` for `v ∈ T_xA`. -/
theorem exists_chartTangent_field {A : Set X} (hA : P.IsSmoothSubmanifold A) {x : X} (hx : x ∈ A)
    {ψ : MChart X} (hψ : P.IsChart ψ) (hxψ : x ∈ ψ.source) :
    ∃ W : Set X, IsOpen W ∧ x ∈ W ∧ W ⊆ ψ.source ∧
      ∃ D : X → ψ.model.E 0 →L[ℝ] ψ.model.E 0,
        (∀ z ∈ A ∩ W, P.chartTangent hψ A z = range (D z)) ∧
        (∀ v ∈ P.chartTangent hψ A x, D x v = v) ∧
        ∀ v ∈ P.chartTangent hψ A x, ContinuousOn (fun z => D z v) (A ∩ W) := by
  set d := hA.data hx
  have hxV : x ∈ d.V := hA.mem_data_V hx
  obtain ⟨t, ht, htp⟩ := exists_plusRetraction hψ d hx hxV
  set W := d.toSubData.shrink ψ
  have hWV : W ⊆ d.V := fun q hq => d.toSubData.shrink_subset_V ψ hq
  have hWψ : W ⊆ ψ.source := d.toSubData.shrink_subset_source ψ
  have hxW : x ∈ W := d.toSubData.mem_shrink ψ hx hxV hxψ
  set ι := ψ.model.E.toBase 1
  set D : X → ψ.model.E 0 →L[ℝ] ψ.model.E 0 := fun z => scDeriv t.U t (levelLift ψ 1 z) with hDdef
  have hrange : ∀ z ∈ A ∩ W, ι (levelLift ψ 1 z) = ψ z ∧ ψ z ∈ t.retract ∧
      P.chartTangent hψ A z = range (D z) := fun z hz =>
    chartTangent_eq_range hψ d ht hz.1 (hWV hz.2) (hWψ hz.2)
  have hret : ∀ z ∈ A ∩ W, ι (levelLift ψ 1 z) ∈ t.retract := fun z hz => by
    rw [(hrange z hz).1]; exact (hrange z hz).2.1
  have hT₀ := (hrange x ⟨hx, hxW⟩).2.2
  have hret₀ := hret x ⟨hx, hxW⟩
  have hmaps : MapsTo (levelLift ψ 1) (A ∩ W) (ψ.model.E.lvlSet t.U 1) := fun z hz =>
    t.retract_subset (hret z hz)
  refine ⟨W, d.toSubData.isOpen_shrink ψ, hxW, hWψ, D, fun z hz => (hrange z hz).2.2,
    fun v hv => ?_, fun v hv => ?_⟩
  · rw [hT₀] at hv
    obtain ⟨u, rfl⟩ := hv
    exact congrArg (fun L : ψ.model.E 0 →L[ℝ] ψ.model.E 0 => L u) (t.scDeriv_comp_self hret₀)
  · rw [hT₀] at hv
    set p := t.plusDeriv (levelLift ψ 1 x) v
    have hιp : ι p = v := ScRetraction.toBase_plusDeriv_of_mem_range htp hret₀ hv
    have hlz : ContinuousOn (levelLift ψ 1) (A ∩ W) :=
      (hasContinuousLevelOneOn hA ψ hψ).mono fun z hz => ⟨hz.1, hWψ hz.2⟩
    have h1 := (ScRetraction.continuousOn_plusDeriv htp).comp hlz hmaps
    have h2 : ContinuousOn (fun z => ι (((t.plusDeriv (levelLift ψ 1 z)).comp ι) p)) (A ∩ W) :=
      ι.continuous.comp_continuousOn
        ((ContinuousLinearMap.apply ℝ _ p).continuous.comp_continuousOn h1)
    refine h2.congr fun z hz => ?_
    change D z v = ι (t.plusDeriv (levelLift ψ 1 z) (ι p))
    rw [ScRetraction.toBase_plusDeriv htp (hmaps hz), hιp]

/-- A basis of a submodule, read in the ambient space, is linearly independent and lies in it. -/
theorem coe_basis_linearIndependent_mem {E : Type*} [AddCommGroup E] [Module ℝ E]
    {N : Submodule ℝ E} {n : ℕ} (b : Basis (Fin n) ℝ N) :
    LinearIndependent ℝ (fun i => (b i : E)) ∧ ∀ i, (b i : E) ∈ N :=
  ⟨b.linearIndependent.map' N.subtype N.ker_subtype, fun i => (b i).2⟩

/-- `frameDet Λ w ≠ 0` for some continuous linear `Λ`, if `w` is linearly independent. -/
theorem exists_frameDet_ne_zero {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {n : ℕ}
    {w : Fin n → E} (hw : LinearIndependent ℝ w) :
    ∃ Λ : E →L[ℝ] (Fin n → ℝ), frameDet Λ w ≠ 0 := by
  set K := span ℝ (range w)
  have : FiniteDimensional ℝ K := FiniteDimensional.span_of_finite ℝ (finite_range w)
  obtain ⟨Q', hQ'⟩ := Submodule.ClosedComplemented.of_finiteDimensional K
  let b : Basis (Fin n) ℝ K := Basis.span hw
  refine ⟨(b.equivFunL : K →L[ℝ] (Fin n → ℝ)).comp Q', ?_⟩
  have h := frameDet_ne_zero_of_basis b ((b.equivFunL : K →L[ℝ] (Fin n → ℝ)).comp Q')
    (fun v => by change b.equivFunL (Q' v) = _; rw [hQ' v]; rfl) b
  have hb : (fun i => (b i : E)) = w := funext fun i => by
    rw [show b i = Basis.span hw i from rfl, Basis.span_apply]
  rwa [hb] at h

/-- **Different tangent spaces stay different**: for `n`-dimensional submanifolds `A₁`, `A₂`
with `T_xA₁ ≠ T_xA₂`, the tangent spaces differ at every common point near `x`, i.e. the set of
common points with equal tangent spaces is closed in `A₁ ∩ A₂`.  (Continuous frames `f₁` of `A₁`
and `f₂` of `A₂` from `exists_chartTangent_field`, `f₂,k(x) ∉ T_xA₁`: the determinant of
`(f₂,k, f₁)` is nonzero near `x` and vanishes where `T_zA₁ = T_zA₂`, an `n`-dimensional space
containing `n + 1` vectors.) -/
theorem exists_isOpen_submanifoldTangent_ne {A₁ A₂ : Set X} {n : ℕ}
    (hA₁ : P.IsSubmanifoldOfDim A₁ n) (hA₂ : P.IsSubmanifoldOfDim A₂ n) {x : X}
    (hx₁ : x ∈ A₁) (hx₂ : x ∈ A₂)
    (hT : P.submanifoldTangent A₁ x ≠ P.submanifoldTangent A₂ x) :
    ∃ O : Set X, IsOpen O ∧ x ∈ O ∧ ∀ z ∈ A₁ ∩ A₂ ∩ O,
      P.submanifoldTangent A₁ z ≠ P.submanifoldTangent A₂ z := by
  obtain ⟨ψ, hψ, hxψ⟩ := P.exists_isChart_mem_source x
  obtain ⟨W₁, hW₁, hxW₁, hW₁ψ, D₁, hD₁, hD₁x, hD₁c⟩ := exists_chartTangent_field hA₁.1 hx₁ hψ hxψ
  obtain ⟨W₂, hW₂, hxW₂, -, D₂, hD₂, hD₂x, hD₂c⟩ := exists_chartTangent_field hA₂.1 hx₂ hψ hxψ
  obtain ⟨N₁, hN₁, hfin₁⟩ := exists_submodule_chartTangent hψ hA₁.1 hx₁ hxψ
  obtain ⟨N₂, hN₂, hfin₂⟩ := exists_submodule_chartTangent hψ hA₂.1 hx₂ hxψ
  have hr₁ := finrank_chartTangent hψ (hA₁.2 x hx₁) hA₁.1 hxψ hN₁
  have hr₂ := finrank_chartTangent hψ (hA₂.2 x hx₂) hA₂.1 hxψ hN₂
  obtain ⟨hb₁li, hb₁N⟩ := coe_basis_linearIndependent_mem (Module.finBasisOfFinrankEq ℝ N₁ hr₁)
  obtain ⟨hb₂li, hb₂N⟩ := coe_basis_linearIndependent_mem (Module.finBasisOfFinrankEq ℝ N₂ hr₂)
  set b₁ := fun i => ((Module.finBasisOfFinrankEq ℝ N₁ hr₁) i : ψ.model.E 0)
  set b₂ := fun i => ((Module.finBasisOfFinrankEq ℝ N₂ hr₂) i : ψ.model.E 0)
  have hb₁T : ∀ i, b₁ i ∈ P.chartTangent hψ A₁ x := fun i => by rw [← hN₁]; exact hb₁N i
  have hb₂T : ∀ i, b₂ i ∈ P.chartTangent hψ A₂ x := fun i => by rw [← hN₂]; exact hb₂N i
  -- a vector of the frame of `A₂` off `N₁`
  have hk : ∃ k, b₂ k ∉ N₁ := by
    by_contra hall
    push Not at hall
    have hspan : span ℝ (range b₂) = N₂ :=
      Submodule.eq_of_le_of_finrank_eq (span_le.2 (range_subset_iff.2 hb₂N))
        (by rw [finrank_span_eq_card hb₂li, Fintype.card_fin, hr₂])
    have hle : N₂ ≤ N₁ := hspan ▸ span_le.2 (range_subset_iff.2 hall)
    have hNN : N₂ = N₁ := Submodule.eq_of_le_of_finrank_eq hle (by rw [hr₁, hr₂])
    exact hT ((chartTangent_eq_iff hψ hxψ).1 (by rw [← hN₁, ← hN₂, hNN]))
  obtain ⟨k, hk⟩ := hk
  -- the determinant
  set F : X → Fin (n + 1) → ψ.model.E 0 := fun z =>
    Fin.cons (D₂ z (b₂ k)) (fun i => D₁ z (b₁ i)) with hFdef
  have hFx : F x = Fin.cons (b₂ k) b₁ := by
    have h1 : (fun i => D₁ x (b₁ i)) = b₁ := funext fun i => hD₁x _ (hb₁T i)
    rw [hFdef]
    dsimp only
    rw [h1, hD₂x _ (hb₂T k)]
  have hFli : LinearIndependent ℝ (F x) := by
    rw [hFx, linearIndependent_finCons]
    exact ⟨hb₁li, fun h => hk (span_le.2 (range_subset_iff.2 hb₁N) h)⟩
  obtain ⟨Λ, hΛ⟩ := exists_frameDet_ne_zero hFli
  set S := A₁ ∩ A₂ ∩ (W₁ ∩ W₂)
  have hFc : ContinuousOn F S := by
    refine continuousOn_pi.2 fun j => ?_
    refine Fin.cases ?_ (fun i => ?_) j
    · simp only [hFdef, Fin.cons_zero]
      exact (hD₂c _ (hb₂T k)).mono fun z hz => ⟨hz.1.2, hz.2.2⟩
    · simp only [hFdef, Fin.cons_succ]
      exact (hD₁c _ (hb₁T i)).mono fun z hz => ⟨hz.1.1, hz.2.1⟩
  obtain ⟨U, hU, hxU, hUs⟩ := exists_isOpen_sign_eq (ContinuousOn.frameDet Λ hFc)
    ⟨⟨hx₁, hx₂⟩, hxW₁, hxW₂⟩ hΛ
  refine ⟨W₁ ∩ W₂ ∩ U, (hW₁.inter hW₂).inter hU, ⟨⟨hxW₁, hxW₂⟩, hxU⟩, fun z hz hTz => ?_⟩
  obtain ⟨⟨hzA₁, hzA₂⟩, ⟨hzW₁, hzW₂⟩, hzU⟩ := hz
  have hzψ : z ∈ ψ.source := hW₁ψ hzW₁
  obtain ⟨Nz, hNz, hfinz⟩ := exists_submodule_chartTangent hψ hA₁.1 hzA₁ hzψ
  have hrz : finrank ℝ Nz = n := finrank_chartTangent hψ (hA₁.2 z hzA₁) hA₁.1 hzψ hNz
  have hFz : ∀ j, F z j ∈ Nz := fun j => by
    rw [← SetLike.mem_coe, hNz]
    refine Fin.cases ?_ (fun i => ?_) j
    · simp only [hFdef, Fin.cons_zero]
      rw [(chartTangent_eq_iff hψ hzψ).2 hTz, hD₂ z ⟨hzA₂, hzW₂⟩]
      exact ⟨_, rfl⟩
    · simp only [hFdef, Fin.cons_succ]
      rw [hD₁ z ⟨hzA₁, hzW₁⟩]
      exact ⟨_, rfl⟩
  exact (hUs z ⟨⟨⟨hzA₁, hzA₂⟩, hzW₁, hzW₂⟩, hzU⟩).1
    (frameDet_eq_zero_of_mem Λ hFz (by omega))

/-- **Property (T) for one pair of sheets near `x`** (the core of Lemma 9.4.3, 2021 p. 430): for
oriented submanifolds `(A₁, o₁)`, `(A₂, o₂)` of dimensions `n₁`, `n₂` through `x`, some open
`O ∋ x` has: at common points `y₀`, `y ∈ O` where the tangent spaces agree, `o₁ = o₂` at `y₀` iff
at `y`.  (Different dimensions: the tangent spaces never agree; dimension `0`: `x` is isolated;
equal tangent spaces at `x`: `exists_isOpen_tangent_eq_iff`; different ones: they stay different,
`exists_isOpen_submanifoldTangent_ne`.) -/
theorem SubmanifoldOrientation.exists_isOpen_pairT {A₁ A₂ : Set X} {n₁ n₂ : ℕ}
    (hA₁ : P.IsSubmanifoldOfDim A₁ n₁) (hA₂ : P.IsSubmanifoldOfDim A₂ n₂)
    (o₁ : P.SubmanifoldOrientation A₁ n₁) (o₂ : P.SubmanifoldOrientation A₂ n₂) {x : X}
    (hx₁ : x ∈ A₁) (hx₂ : x ∈ A₂) :
    ∃ O : Set X, IsOpen O ∧ x ∈ O ∧ ∀ y₀ ∈ O ∩ A₁ ∩ A₂, ∀ y ∈ O ∩ A₁ ∩ A₂,
      P.submanifoldTangent A₁ y₀ = P.submanifoldTangent A₂ y₀ →
      P.submanifoldTangent A₁ y = P.submanifoldTangent A₂ y →
        (o₁.tangent y₀ = o₂.tangent y₀ ↔ o₁.tangent y = o₂.tangent y) := by
  by_cases hn : n₁ = n₂
  swap
  · refine ⟨univ, isOpen_univ, mem_univ x, fun y₀ hy₀ y _ h₀ _ => ?_⟩
    exact (hn (HasDimAt.eq_of_submanifoldTangent_eq hA₁.1 hA₂.1 (hA₁.2 y₀ hy₀.1.2)
      (hA₂.2 y₀ hy₀.2) h₀)).elim
  subst hn
  rcases Nat.eq_zero_or_pos n₁ with rfl | hpos
  · obtain ⟨O, hO, hxO, hOx⟩ := (hA₁.2 x hx₁).exists_isOpen_eq_of_mem hA₁.1
    refine ⟨O, hO, hxO, fun y₀ hy₀ y hy _ _ => ?_⟩
    rw [hOx y₀ ⟨hy₀.1.2, hy₀.1.1⟩, hOx y ⟨hy.1.2, hy.1.1⟩]
  by_cases hT : P.submanifoldTangent A₁ x = P.submanifoldTangent A₂ x
  · obtain ⟨O, hO, hxO, hOp⟩ := o₁.exists_isOpen_tangent_eq_iff hpos o₂
      (hasContinuousLevelOneOn hA₂.1) hx₁ hx₂ hT
    exact ⟨O, hO, hxO, fun y₀ hy₀ y hy h₀ h =>
      (hOp y₀ ⟨⟨hy₀.1.2, hy₀.2⟩, hy₀.1.1⟩ h₀).trans (hOp y ⟨⟨hy.1.2, hy.2⟩, hy.1.1⟩ h).symm⟩
  · obtain ⟨O, hO, hxO, hOne⟩ :=
      exists_isOpen_submanifoldTangent_ne hA₁ hA₂ hx₁ hx₂ hT
    exact ⟨O, hO, hxO, fun y₀ hy₀ _ _ h₀ _ =>
      (hOne y₀ ⟨⟨hy₀.1.2, hy₀.2⟩, hy₀.1.1⟩ h₀).elim⟩

end MPolyfold

namespace EpGroupoid

open MPolyfold

variable {Obj Mor : Type u} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] {X : EpGroupoid Obj Mor}

namespace OrientedBranchingStructure

variable {Θ : Obj → ℚ} {x : Obj}

/-- **The restricted oriented branching structure** (2021 p. 404 for the unoriented one): on an
open `V ⊆ U(x)` containing `x`, the sheets `Mᵢ ∩ V` with the restricted orientations. -/
def restrict (B : X.OrientedBranchingStructure Θ x) {V : Set Obj} (hV : IsOpen V) (hxV : x ∈ V)
    (hVU : V ⊆ B.U) : X.OrientedBranchingStructure Θ x where
  toLocalBranchingStructure := B.toLocalBranchingStructure.restrict hV hxV hVU
  dim := B.dim
  isSubmanifoldOfDim i := (B.isSubmanifoldOfDim i).inter_isOpen hV
  orient i := (B.orient i).restrict hV

theorem restrict_M (B : X.OrientedBranchingStructure Θ x) {V : Set Obj} (hV : IsOpen V)
    (hxV : x ∈ V) (hVU : V ⊆ B.U) (i : B.ι) : (B.restrict hV hxV hVU).M i = B.M i ∩ V := rfl

/-- Property (T) of `B` on `V` is Property (T) of the restricted structure on `V`. -/
theorem propertyT_restrict_iff (B : X.OrientedBranchingStructure Θ x) {V : Set Obj}
    (hV : IsOpen V) (hxV : x ∈ V) (hVU : V ⊆ B.U) :
    (B.restrict hV hxV hVU).PropertyT V ↔ B.PropertyT V := by
  have hT : ∀ (i : B.ι) {z : Obj}, z ∈ V → X.PObj.submanifoldTangent
      ((B.restrict hV hxV hVU).M i) z = X.PObj.submanifoldTangent (B.M i) z := fun i z hz => by
    rw [restrict_M, submanifoldTangent_inter_isOpen hV hz]
  have hO : ∀ (i : B.ι) {z : Obj}, z ∈ V →
      ((B.restrict hV hxV hVU).orient i).tangent z = (B.orient i).tangent z := fun i z hz =>
    (B.orient i).restrict_tangent hV hz
  constructor
  · intro h i i' y₀ hy₀ y hy h₀ h₁
    have := h i i' y₀ ⟨⟨hy₀.1.1, hy₀.1.2, hy₀.1.1⟩, hy₀.2, hy₀.1.1⟩ y
      ⟨⟨hy.1.1, hy.1.2, hy.1.1⟩, hy.2, hy.1.1⟩
      (by rw [hT i hy₀.1.1, hT i' hy₀.1.1]; exact h₀) (by rw [hT i hy.1.1, hT i' hy.1.1]; exact h₁)
    rwa [hO i hy₀.1.1, hO i' hy₀.1.1, hO i hy.1.1, hO i' hy.1.1] at this
  · intro h i i' y₀ hy₀ y hy h₀ h₁
    have hy₀V : y₀ ∈ V := hy₀.1.1
    have hyV : y ∈ V := hy.1.1
    have := h i i' y₀ ⟨⟨hy₀V, hy₀.1.2.1⟩, hy₀.2.1⟩ y ⟨⟨hyV, hy.1.2.1⟩, hy.2.1⟩
      (by rw [← hT i hy₀V, ← hT i' hy₀V]; exact h₀) (by rw [← hT i hyV, ← hT i' hyV]; exact h₁)
    rwa [← hO i hy₀V, ← hO i' hy₀V, ← hO i hyV, ← hO i' hyV] at this

/-- **Lemma 9.4.3, 2021 p. 430 (2017: Lemma 9.12, p. 316)**, in the form "Property (T) of `B` on
a smaller neighbourhood": some open `U'` with `x ∈ U' ⊆ U(x)` has `B.PropertyT U'`.  (The open
sets of `exists_isOpen_pairT` for the finitely many pairs `(i, i')`, intersected.) -/
theorem lemma_9_4_3_propertyT (B : X.OrientedBranchingStructure Θ x) :
    ∃ U' : Set Obj, IsOpen U' ∧ x ∈ U' ∧ U' ⊆ B.U ∧ B.PropertyT U' := by
  choose O hO hxO hOT using fun i i' : B.ι => SubmanifoldOrientation.exists_isOpen_pairT
    (B.isSubmanifoldOfDim i) (B.isSubmanifoldOfDim i') (B.orient i) (B.orient i') (B.mem_M i)
    (B.mem_M i')
  refine ⟨B.U ∩ ⋂ i, ⋂ i', O i i', B.isOpen_U.inter (isOpen_iInter_of_finite fun i =>
    isOpen_iInter_of_finite fun i' => hO i i'),
    ⟨B.mem_U, mem_iInter.2 fun i => mem_iInter.2 fun i' => hxO i i'⟩, inter_subset_left, ?_⟩
  intro i i' y₀ hy₀ y hy h₀ h
  have hsub : ∀ {z}, z ∈ (B.U ∩ ⋂ i, ⋂ i', O i i') ∩ B.M i ∩ B.M i' →
      z ∈ O i i' ∩ B.M i ∩ B.M i' := fun hz =>
    ⟨⟨mem_iInter.1 (mem_iInter.1 hz.1.1.2 i) i', hz.1.2⟩, hz.2⟩
  exact hOT i i' y₀ (hsub hy₀) y (hsub hy) h₀ h

/-- **Lemma 9.4.3, 2021 p. 430 (2017: Lemma 9.12, p. 316)**: for an oriented branching structure
`B` on `U(x)` there is an open `U'(x) ⊆ U(x)` such that the restricted branching structure
satisfies Property (T) (on its whole neighbourhood `U'(x)`).  As in the book, with no further
hypothesis. -/
theorem lemma_9_4_3 (B : X.OrientedBranchingStructure Θ x) :
    ∃ (U' : Set Obj) (hU' : IsOpen U') (hxU' : x ∈ U') (hU'U : U' ⊆ B.U),
      (B.restrict hU' hxU' hU'U).PropertyT U' := by
  obtain ⟨U', hU', hxU', hU'U, hT⟩ := B.lemma_9_4_3_propertyT
  exact ⟨U', hU', hxU', hU'U, (B.propertyT_restrict_iff hU' hxU' hU'U).2 hT⟩

end OrientedBranchingStructure

end EpGroupoid

end Polyfold
