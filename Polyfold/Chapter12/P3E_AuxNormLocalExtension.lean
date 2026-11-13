import Polyfold.Chapter12.P3N_AuxNormExtension
import Polyfold.Chapter2.TameRetracts

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part III, Chapter 12,
§12.2, **Theorem 12.2.7** (extension of auxiliary norms), pp. 574–576: the local step of the proof
(p. 575), and the theorem as printed.

# The local extension of an auxiliary norm from `W|∂X`

## The text, paraphrased

(Proof of Theorem 12.2.7, p. 575) Near `x₀ ∈ ∂X`, work in a tame local model `O ⊆ C = [0, ∞)ⁿ ⊕ H`,
`O = r(U)`, with a strong bundle retraction `R(u, w) = (r(u), A(u)w)`.  With
`τ(t, h) = min(t₁, …, tₙ)` and `q(t, h) = (t, h) − τ(t, h)·(1, …, 1, 0)`, the map `r ∘ q` is defined
near `x₀`, takes values in `∂O` (tameness: `d_C(r(x)) = d_C(x)`) and fixes the points of `∂O`.  Then
`N'(u, w) = N(rq(u), A(rq(u))w) + ‖w − A(rq(u))w‖_{F₁}` is a local auxiliary norm which equals `N`
over `∂O`.  The rest of the proof (average over `G_{x₀}`, transport, gluing) is
`theorem_12_2_7_hyp` (P3N).

## What is formalized

* **The retraction `r ∘ q`** (Part I, `Polyfold.MPolyfold`): `exists_retraction_boundary`: in a
  tame M-polyfold every boundary point `x₀` has an open neighbourhood `V` and a map `ρ`
  continuous on `V`, with values in `∂X` and `ρ = id` on `V ∩ ∂X`.  It is `ψ⁻¹ ∘ r ∘ q ∘ ψ` in a
  tame chart `ψ` (with `τ = min` over the coordinates of a presentation `T` of `C`).
* **The norm `N'`** (Part I, `Polyfold.StrongBundle`): `retractNorm hc y₀ ρ N`, the formula of
  the text in a strong bundle chart `c` of the atlas through `Φ[1]` (`oneChartOf`), with
  `A(u) = chartFibMap c u` the fibre part of `R[1]`.  `isLocalAuxNorm_retractNorm`: for any `A ⊆ X`
  and any `ρ` continuous on an open `V` with values in `A` (and in the chart domain), `N'` is a
  local auxiliary norm on `V` whenever `N` is one over `A` (continuity on `W_{0,1}|A`, seminorms
  on the fibres over `A`, condition (2) for sequences in `A`); `retractNorm_eq`: `N' = N` over
  `V ∩ A` when `ρ = id` there.  `exists_localExtension_of_isTame` combines both.
* **The local step** (`Polyfold.EpStrongBundle`): `hasLocalExtensions_of_isTame` discharges the
  hypothesis `HasLocalExtensions` of `theorem_12_2_7_hyp` for tame `X`.
* **Theorem 12.2.7 as printed**: `theorem_12_2_7`.

## Reading

* **No tame strong bundle chart is needed.**  The text works in one local model in which the
  base retraction `r` is tame.  Here the retraction `r ∘ q` onto the boundary is built in a tame
  chart of `X` (from Definition 2.5.7, tameness of `X`), and the fibre formula is evaluated in an
  arbitrary strong bundle chart of the atlas around `x₀`: only the continuity of `ρ = ψ⁻¹rqψ`
  at level 0 and its two properties (values in `∂X`, identity on `∂X`) enter the fibre part.
* **Continuity of `A`.**  `(u, h) ↦ A(u)h` is the fibre part of `R[1]`, which is continuous
  `U ⊕ F₁ → F₁` (level 0 of the sc-smooth `R : (U ◁ F)[1] → (U ◁ F)[1]`); this joint continuity is
  what the continuity of `N'` on `W_{0,1}` uses.
* The invariance of `N` under morphisms is not used in the local step (it enters only through the
  average over `G_{x₀}` in `theorem_12_2_7_hyp`).
-/

open Set Filter Topology Function TopologicalSpace

noncomputable section

namespace Polyfold

universe u v

/-! ### The retraction `r ∘ q` onto the boundary (Part I) -/

section Retraction

variable {E : ScBanach} {n : ℕ} {W : ScBanach} (T : ScIso E ((ScBanach.const (Fin n → ℝ)).prod W))

/-- `d_C(z) ≥ 1` iff some half-line coordinate of `z` vanishes (presentation `T`). -/
lemma one_le_degIndexWith_iff (z : E 0) : 1 ≤ degIndexWith T z ↔ ∃ i, (T 0 z).1 i = 0 := by
  rw [degIndexWith_eq_card_zeroSet, Nat.one_le_iff_ne_zero, Ne, Finset.card_eq_zero,
    ← Ne, ← Finset.nonempty_iff_ne_empty]
  exact ⟨fun ⟨i, hi⟩ => ⟨i, (mem_zeroSet T).1 hi⟩, fun ⟨i, hi⟩ => ⟨i, (mem_zeroSet T).2 hi⟩⟩

variable (hne : (Finset.univ : Finset (Fin n)).Nonempty)

/-- `τ(t, h) = min(t₁, …, tₙ)` (proof of Theorem 12.2.7, p. 575), in the presentation `T`. -/
def minCoord (z : E 0) : ℝ := Finset.univ.inf' hne fun i => (T 0 z).1 i

/-- `q(t, h) = (t, h) − τ(t, h)·(1, …, 1, 0)` (proof of Theorem 12.2.7, p. 575). -/
def boundaryShift (z : E 0) : E 0 :=
  (T 0).symm (T 0 z - minCoord T hne z • (((fun _ => (1 : ℝ)), 0) :
    ((ScBanach.const (Fin n → ℝ)).prod W) 0))

lemma continuous_minCoord : Continuous (minCoord T hne) :=
  Continuous.finset_inf'_apply hne fun i _ => continuous_coord T i

lemma continuous_boundaryShift : Continuous (boundaryShift T hne) :=
  (T 0).symm.continuous.comp ((T 0).continuous.sub
    ((continuous_minCoord T hne).smul continuous_const))

lemma coord_boundaryShift (z : E 0) (i : Fin n) :
    (T 0 (boundaryShift T hne z)).1 i = (T 0 z).1 i - minCoord T hne z := by
  simp [boundaryShift]

lemma minCoord_le (z : E 0) (i : Fin n) : minCoord T hne z ≤ (T 0 z).1 i :=
  Finset.inf'_le _ (Finset.mem_univ i)

lemma exists_coord_eq_minCoord (z : E 0) : ∃ i, (T 0 z).1 i = minCoord T hne z := by
  obtain ⟨i, -, hi⟩ := Finset.exists_mem_eq_inf' hne fun i => (T 0 z).1 i
  exact ⟨i, hi.symm⟩

/-- `q` takes values in the partial quadrant. -/
lemma mem_quadrant_boundaryShift (z : E 0) :
    T 0 (boundaryShift T hne z) ∈ quadrant n W 0 := fun i => by
  change 0 ≤ (T 0 (boundaryShift T hne z)).1 i
  rw [coord_boundaryShift]; linarith [minCoord_le T hne z i]

lemma exists_coord_boundaryShift_eq_zero (z : E 0) :
    ∃ i, (T 0 (boundaryShift T hne z)).1 i = 0 := by
  obtain ⟨i, hi⟩ := exists_coord_eq_minCoord T hne z
  exact ⟨i, by rw [coord_boundaryShift, hi, sub_self]⟩

/-- `q` fixes the points of the quadrant with a vanishing coordinate. -/
lemma boundaryShift_eq_self {z : E 0} (hz : T 0 z ∈ quadrant n W 0) {i : Fin n}
    (hi : (T 0 z).1 i = 0) : boundaryShift T hne z = z := by
  have h0 : minCoord T hne z = 0 :=
    le_antisymm (hi ▸ minCoord_le T hne z i) (Finset.le_inf' _ _ fun j _ => hz j)
  simp [boundaryShift, h0]

end Retraction

namespace MPolyfold

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] (P : MPolyfold X)

/-- **The retraction `r ∘ q` of the proof of Theorem 12.2.7** (p. 575): in a tame M-polyfold every
boundary point `x₀` has an open neighbourhood `V` and a map `ρ`, continuous on `V`, with values in
`∂X` and equal to the identity on `V ∩ ∂X`.  (`ρ = ψ⁻¹ ∘ r ∘ q ∘ ψ` in a tame chart `ψ`; tameness
(1) `d_C(r(x)) = d_C(x)` gives the values in `∂X`.) -/
theorem exists_retraction_boundary (hP : P.IsTame) {x₀ : X} (hx₀ : x₀ ∈ P.boundary) :
    ∃ (V : Set X) (ρ : X → X), IsOpen V ∧ x₀ ∈ V ∧ ContinuousOn ρ V ∧
      MapsTo ρ V P.boundary ∧ ∀ y ∈ V ∩ P.boundary, ρ y = y := by
  obtain ⟨ψ, hψ, hx₀ψ, htame⟩ := IsTame.exists_chart P hP x₀
  obtain ⟨R, hRO, hRt⟩ := htame
  obtain ⟨n, W, T, hT⟩ := ψ.model.isPartialQuadrant
  have hR := hRt n W T hT
  have hdeg : ∀ z ∈ ψ.source, P.degIndex z = degIndexWith T (ψ z) := fun z hz => by
    rw [P.degIndex_eq_chartDegIndex_of_isTameWith hψ R hRO hT hR hz, chartDegIndex,
      degIndex_eq T hT (ψ.apply_mem_C hz)]
  have hbd : ∀ z ∈ ψ.source, z ∈ P.boundary ↔ ∃ i, (T 0 (ψ z)).1 i = 0 := fun z hz => by
    change 1 ≤ P.degIndex z ↔ _
    rw [hdeg z hz, one_le_degIndexWith_iff]
  obtain ⟨i₀, -⟩ := (hbd x₀ hx₀ψ).1 hx₀
  have hne : (Finset.univ : Finset (Fin n)).Nonempty := ⟨i₀, Finset.mem_univ _⟩
  set q := boundaryShift T hne with hq
  have hqC : ∀ z, q z ∈ ψ.model.C := fun z => by
    rw [hT]; exact mem_quadrant_boundaryShift T hne z
  obtain ⟨V₀, hV₀, hUV⟩ := R.relOpen.relOpen
  set V := ψ.source ∩ ψ ⁻¹' (q ⁻¹' V₀) with hV
  have hVo : IsOpen V := ψ.continuousOn_toFun.isOpen_inter_preimage ψ.isOpen_source
    (hV₀.preimage (continuous_boundaryShift T hne))
  have hqU : ∀ y ∈ V, q (ψ y) ∈ R.U := fun y hy => by
    rw [hUV]; exact ⟨hy.2, hqC _⟩
  have hRO' : ∀ y ∈ V, R (q (ψ y)) ∈ ψ.model.O := fun y hy => by
    rw [← hRO]; exact R.apply_mem_retract (hqU y hy)
  -- the points of `V ∩ ∂X` are fixed by `q`
  have hfixq : ∀ y ∈ ψ.source, y ∈ P.boundary → q (ψ y) = ψ y := fun y hy hyb => by
    obtain ⟨i, hi⟩ := (hbd y hy).1 hyb
    have hyC := ψ.apply_mem_C hy
    rw [hT] at hyC
    exact boundaryShift_eq_self T hne hyC hi
  have hx₀V : x₀ ∈ V := by
    refine ⟨hx₀ψ, ?_⟩
    change q (ψ x₀) ∈ V₀
    rw [hfixq x₀ hx₀ψ hx₀]
    have : ψ x₀ ∈ R.U := R.retract_subset (hRO ▸ ψ.mapsTo_model x₀ hx₀ψ)
    rw [hUV] at this; exact this.1
  refine ⟨V, fun y => ψ.symm (R (q (ψ y))), hVo, hx₀V, ?_, fun y hy => ?_, fun y hy => ?_⟩
  · -- continuity
    have h1 : ContinuousOn (fun y => q (ψ y)) V :=
      (continuous_boundaryShift T hne).comp_continuousOn
        (ψ.continuousOn_toFun.mono inter_subset_left)
    have h2 : ContinuousOn (fun y => R (q (ψ y))) V :=
      R.isSc1.isSc0.continuousOn_base.comp h1 hqU
    exact ψ.continuousOn_invFun.comp h2 hRO'
  · -- values in `∂X`
    have hmem := ψ.symm_mapsTo (hRO' y hy)
    refine (hbd _ hmem).2 ?_
    rw [ψ.apply_symm_apply (hRO' y hy), ← one_le_degIndexWith_iff]
    have hqUy := hqU y hy
    have h1 := hR.degIndex_apply _ hqUy
    rw [degIndex_eq T hT (R.U_subset_C (R.mapsTo hqUy)), degIndex_eq T hT (R.U_subset_C hqUy)]
      at h1
    rw [h1, one_le_degIndexWith_iff]
    exact exists_coord_boundaryShift_eq_zero T hne _
  · -- the identity on `V ∩ ∂X`
    change ψ.symm (R (q (ψ y))) = y
    rw [hfixq y hy.1.1 hy.2, R.apply_eq_self_of_mem_retract (hRO ▸ ψ.mapsTo_model y hy.1.1),
      ψ.symm_apply_apply hy.1.1]

end MPolyfold

/-! ### The norm `N'` in a strong bundle chart (Part I) -/

namespace StrongBundle

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle PX P}

section FibMap

variable (c : StrongBundleChart PX P)

/-- `A(u)h`, the fibre part of `R[1](u, h)` (`R(u, h) = (r(u), A(u)h)` at the level `F₁`). -/
def chartFibMap (u : c.φ.model.E 0) (h : c.F 1) : c.F 1 := (shiftFiber c.R (u, h)).2

variable {c}

omit [T2Space Y] [ParacompactSpace Y] in
lemma mem_U_of_mem_O {u : c.φ.model.E 0} (hu : u ∈ c.φ.model.O) : u ∈ c.U := by
  rw [← c.base_retract] at hu
  exact (c.isRetraction.baseRetraction c.relOpen).retract_subset hu

omit [T2Space Y] [ParacompactSpace Y] in
/-- `R[1](u, h) = (u, A(u)h)` for `u ∈ O`. -/
lemma shiftFiber_eq_chartFibMap {u : c.φ.model.E 0} (hu : u ∈ c.φ.model.O) (h : c.F 1) :
    shiftFiber c.R (u, h) = (u, chartFibMap c u h) := by
  refine Prod.ext ?_ rfl
  change (c.R (u, c.F.toBase 1 h)).1 = u
  rw [c.isRetraction.apply_fst (mem_U_of_mem_O hu)]
  have := (c.isRetraction.baseRetraction c.relOpen).apply_eq_self_of_mem_retract
    (by rw [c.base_retract]; exact hu)
  exact this

omit [T2Space Y] [ParacompactSpace Y] in
lemma retractOne_retract :
    (c.isRetraction.toScRetractionOne c.relOpen).retract = strongShiftOne c.K :=
  c.isRetraction.toScRetractionOne_retract c.relOpen

omit [T2Space Y] [ParacompactSpace Y] in
/-- `(u, A(u)h) ∈ K[1]` for `u ∈ O`. -/
lemma mem_K_chartFibMap {u : c.φ.model.E 0} (hu : u ∈ c.φ.model.O) (h : c.F 1) :
    (u, chartFibMap c u h) ∈ strongShiftOne c.K := by
  rw [← shiftFiber_eq_chartFibMap hu, ← retractOne_retract]
  exact (c.isRetraction.toScRetractionOne c.relOpen).apply_mem_retract
    (⟨mem_U_of_mem_O hu, mem_univ _⟩ : ((u, h) : (c.φ.model.E.prod c.F.shift) 0) ∈ c.U ×ˢ univ)

omit [T2Space Y] [ParacompactSpace Y] in
/-- `A(u)h = h` for `(u, h) ∈ K[1]`. -/
lemma chartFibMap_of_mem {u : c.φ.model.E 0} {h : c.F 1} (hp : (u, h) ∈ strongShiftOne c.K) :
    chartFibMap c u h = h := by
  have := (c.isRetraction.toScRetractionOne c.relOpen).apply_eq_self_of_mem_retract
    (by rw [retractOne_retract]; exact hp)
  exact congrArg Prod.snd this

omit [T2Space Y] [ParacompactSpace Y] in
/-- `h ↦ A(u)h` is linear on `F₁`. -/
lemma isLinearMap_chartFibMap {u : c.φ.model.E 0} (hu : u ∈ c.U) :
    IsLinearMap ℝ (chartFibMap c u) := by
  have key : ∀ h, c.F.toBase 1 (chartFibMap c u h) = (c.R (u, c.F.toBase 1 h)).2 := fun h =>
    c.isRetraction.toBase_shiftFiber_snd (p := ((u, h) : (c.φ.model.E.prod c.F.shift) 0)) hu
  have hl := c.isRetraction.fiber_linear u hu
  refine ⟨fun h h' => c.F.toBase_injective 1 ?_, fun t h => c.F.toBase_injective 1 ?_⟩
  · rw [map_add, key, key, key, map_add, hl.map_add]
  · rw [map_smul, key, key, map_smul, hl.map_smul]

omit [T2Space Y] [ParacompactSpace Y] in
/-- `R[1]` is continuous on `U ⊕ F₁`. -/
lemma continuousOn_shiftFiber_R : ContinuousOn (shiftFiber c.R) (c.U ×ˢ univ) :=
  (c.isRetraction.toScRetractionOne c.relOpen).isSc1.isSc0.continuousOn_base

end FibMap

section RetractNorm

variable {c : StrongBundleChart PX P} (hc : B.IsChart c) (y₀ : B.One)

/-- **The norm `N'` of the proof of Theorem 12.2.7** (p. 575), read in the chart `Φ[1]` of the
strong bundle chart `c`: for `w` over `y` with `Φ[1](w) = (φ(y), h)` and `u = φ(ρ(y))`,
`N'(w) = N(Φ[1]⁻¹(u, A(u)h)) + ‖h − A(u)h‖_{F₁}`. -/
def retractNorm (ρ : X → X) (N : B.One → ℝ) (w : B.One) : ℝ :=
  N ((oneChartOf hc y₀).symm (c.φ (ρ (P (B.oneVal w))),
      chartFibMap c (c.φ (ρ (P (B.oneVal w)))) (oneChartOf hc y₀ w).2)) +
    ‖(oneChartOf hc y₀ w).2 - chartFibMap c (c.φ (ρ (P (B.oneVal w)))) (oneChartOf hc y₀ w).2‖

/-- The point `Φ[1]⁻¹(φ(y'), h')` lies over `y'`. -/
lemma proj_oneChartOf_symm {y' : X} (hy' : y' ∈ c.φ.source) {h' : c.F 1}
    (hz : (c.φ y', h') ∈ strongShiftOne c.K) :
    P (B.oneVal ((oneChartOf hc y₀).symm (c.φ y', h'))) = y' := by
  set Φ := oneChartOf hc y₀
  have hzO : (c.φ y', h') ∈ Φ.model.O := hz
  have hs := Φ.symm_mapsTo hzO
  have hs' := (mem_oneChartOf_source hc y₀).1 hs
  have h1 : (Φ (Φ.symm (c.φ y', h'))).1 = c.φ y' := by rw [Φ.apply_symm_apply hzO]
  rw [oneChartOf_apply, fst_liftOne hs'] at h1
  exact c.φ.toPartialEquiv.injOn hs' hy' h1

/-- `Φ[1](v) = (φ(y), |v|-coordinates)` for `v` in the fibre over `y`. -/
lemma oneChartOf_toOne {y : X} (hy : y ∈ c.φ.source) (v : B.oneFiber y) :
    oneChartOf hc y₀ (B.toOne v) = (c.φ y, liftOneFiber hc hy v) := by
  refine Prod.ext ?_ rfl
  rw [oneChartOf_apply, fst_liftOne (by rw [proj_oneVal_toOne B v]; exact hy),
    proj_oneVal_toOne B v]

/-- The fibre transport `v ↦ Φ[1]⁻¹(φ(y'), A(φ(y'))·|v|)` from the fibre over `y` to the fibre
over `y'`, as a linear map. -/
def retractTransport {y y' : X} (hy : y ∈ c.φ.source) (hy' : y' ∈ c.φ.source) :
    B.oneFiber y →ₗ[ℝ] B.oneFiber y' :=
  (LinearEquiv.ofInjective _ (liftOneFiber_injective hc hy')).symm.toLinearMap ∘ₗ
    (((isLinearMap_chartFibMap (mem_U_of_mem_O (c.φ.mapsTo_model y' hy'))).mk' _) ∘ₗ
      liftOneFiber hc hy).codRestrict _ fun _ => LinearMap.mem_range.2
        (mem_range_liftOneFiber hc hy' (mem_K_chartFibMap (c.φ.mapsTo_model y' hy') _))

lemma liftOneFiber_retractTransport {y y' : X} (hy : y ∈ c.φ.source) (hy' : y' ∈ c.φ.source)
    (v : B.oneFiber y) :
    liftOneFiber hc hy' (retractTransport hc hy hy' v) =
      chartFibMap c (c.φ y') (liftOneFiber hc hy v) := by
  simp only [retractTransport, LinearMap.coe_comp, LinearEquiv.coe_coe, comp_apply]
  rw [← LinearEquiv.ofInjective_apply (h := liftOneFiber_injective hc hy'),
    LinearEquiv.apply_symm_apply]
  rfl

variable {hc y₀}

/-- **The formula of `N'` on a fibre**: over `y` with `ρ(y)` in the chart domain,
`N'(v) = N(transport v) + ‖h − A h‖`, `h = |v|` read in the chart. -/
lemma retractNorm_toOne {ρ : X → X} (N : B.One → ℝ) {y : X} (hy : y ∈ c.φ.source)
    (hρy : ρ y ∈ c.φ.source) (v : B.oneFiber y) :
    retractNorm hc y₀ ρ N (B.toOne v) =
      N (B.toOne (retractTransport hc hy hρy v)) +
        ‖liftOneFiber hc hy v - chartFibMap c (c.φ (ρ y)) (liftOneFiber hc hy v)‖ := by
  have hP : P (B.oneVal (B.toOne v)) = y := proj_oneVal_toOne B v
  unfold retractNorm
  rw [hP]
  have h2 : (oneChartOf hc y₀ (B.toOne v)).2 = liftOneFiber hc hy v := rfl
  rw [h2]
  congr 2
  rw [← liftOneFiber_retractTransport hc hy hρy, ← oneChartOf_toOne hc y₀ hρy,
    (oneChartOf hc y₀).symm_apply_apply ((mem_oneChartOf_source hc y₀).2
      (by rw [proj_oneVal_toOne B]; exact hρy))]

/-- **`N'` is a seminorm on the fibres over `V`** (where `ρ` takes values in `A` and in the chart
domain, and `N` is a seminorm on the fibres over `A`). -/
lemma isFiberSeminorm_retractNorm {ρ : X → X} {N : B.One → ℝ} {y : X} (hy : y ∈ c.φ.source)
    (hρy : ρ y ∈ c.φ.source) (hN : B.IsFiberSeminorm N (ρ y)) :
    B.IsFiberSeminorm (retractNorm hc y₀ ρ N) y where
  smul t v := by
    rw [retractNorm_toOne N hy hρy, retractNorm_toOne N hy hρy, map_smul, map_smul,
      (isLinearMap_chartFibMap (mem_U_of_mem_O (c.φ.mapsTo_model _ hρy))).map_smul, ← smul_sub,
      norm_smul, Real.norm_eq_abs, hN.smul, mul_add]
  add_le v w := by
    rw [retractNorm_toOne N hy hρy, retractNorm_toOne N hy hρy, retractNorm_toOne N hy hρy,
      map_add, map_add, (isLinearMap_chartFibMap (mem_U_of_mem_O (c.φ.mapsTo_model _ hρy))).map_add,
      add_sub_add_comm]
    have h1 := hN.add_le (retractTransport hc hy hρy v) (retractTransport hc hy hρy w)
    have h2 := norm_add_le (liftOneFiber hc hy v - chartFibMap c (c.φ (ρ y)) (liftOneFiber hc hy v))
      (liftOneFiber hc hy w - chartFibMap c (c.φ (ρ y)) (liftOneFiber hc hy w))
    linarith

/-- **`N' = N` over `A`** where `ρ` is the identity. -/
lemma retractNorm_eq_of_fix {ρ : X → X} (N : B.One → ℝ) {w : B.One}
    (hw : P (B.oneVal w) ∈ c.φ.source) (hfix : ρ (P (B.oneVal w)) = P (B.oneVal w)) :
    retractNorm hc y₀ ρ N w = N w := by
  have hws : w ∈ (oneChartOf hc y₀).source := (mem_oneChartOf_source hc y₀).2 hw
  have hΦw : oneChartOf hc y₀ w = (c.φ (P (B.oneVal w)), (oneChartOf hc y₀ w).2) :=
    Prod.ext (by rw [oneChartOf_apply, fst_liftOne hw]) rfl
  have hK : (c.φ (P (B.oneVal w)), (oneChartOf hc y₀ w).2) ∈ strongShiftOne c.K := by
    rw [← hΦw]; exact (oneChartOf hc y₀).mapsTo_model w hws
  have e1 : chartFibMap c (c.φ (P (B.oneVal w))) (oneChartOf hc y₀ w).2 = (oneChartOf hc y₀ w).2 :=
    chartFibMap_of_mem hK
  have e2 : (oneChartOf hc y₀).symm (c.φ (P (B.oneVal w)), (oneChartOf hc y₀ w).2) = w := by
    rw [← hΦw]; exact (oneChartOf hc y₀).symm_apply_apply hws
  unfold retractNorm
  rw [hfix, e1, e2, sub_self, norm_zero, add_zero]

end RetractNorm

/-- A chart detects convergence: if `w_k` is eventually in the domain of `Φ` and
`Φ(w_k) → Φ(w)`, then `w_k → w`. -/
lemma _root_.Polyfold.MChart.tendsto_of_tendsto_apply {Z : Type*} [TopologicalSpace Z]
    (Φ : MChart Z) {w : ℕ → Z} {w' : Z} (hw' : w' ∈ Φ.source)
    (hev : ∀ᶠ k in atTop, w k ∈ Φ.source) (h : Tendsto (fun k => Φ (w k)) atTop (𝓝 (Φ w'))) :
    Tendsto w atTop (𝓝 w') := by
  have hc := (Φ.continuousOn_invFun (Φ w') (Φ.mapsTo_model w' hw')).tendsto
  have e : Φ.toPartialEquiv.symm (Φ w') = w' := Φ.symm_apply_apply hw'
  rw [e] at hc
  have h2 := hc.comp (tendsto_nhdsWithin_iff.2 ⟨h, hev.mono fun k hk => Φ.mapsTo_model _ hk⟩)
  refine h2.congr' ?_
  filter_upwards [hev] with k hk
  exact Φ.symm_apply_apply hk

section LocalAux

variable {c : StrongBundleChart PX P} (hc : B.IsChart c) (y₀ : B.One)

/-- **The local step of the proof of Theorem 12.2.7** (p. 575), for any `A ⊆ X`: if `N` is an
auxiliary norm over `A` (continuous on `W_{0,1}|A`, a seminorm on the fibres over `A`, and
condition (2) for sequences over `A`) and `ρ` is continuous on an open `V` in the domain of the
chart, with values in `A` and in the domain of the chart, then `N'` is a local auxiliary norm on
`V` (`StrongBundle.IsLocalAuxNorm`). -/
theorem isLocalAuxNorm_retractNorm {A V : Set X} (hV : IsOpen V) (hVc : V ⊆ c.φ.source)
    {ρ : X → X} (hρ : ContinuousOn ρ V) (hρA : MapsTo ρ V A) (hρc : MapsTo ρ V c.φ.source)
    {N : B.One → ℝ} (hNc : ContinuousOn N {w | P (B.oneVal w) ∈ A})
    (hNs : ∀ y ∈ A, B.IsFiberSeminorm N y)
    (hN2 : ∀ (w : ℕ → B.One) (y : X), y ∈ A → (∀ k, P (B.oneVal (w k)) ∈ A) →
      Tendsto (fun k => P (B.oneVal (w k))) atTop (𝓝 y) →
        Tendsto (fun k => N (w k)) atTop (𝓝 0) → Tendsto w atTop (𝓝 (B.zeroOne y))) :
    B.IsLocalAuxNorm V (retractNorm hc y₀ ρ N) := by
  set Φ := oneChartOf hc y₀ with hΦ
  set S := {w : B.One | P (B.oneVal w) ∈ V}
  have hPc : Continuous fun w : B.One => P (B.oneVal w) := B.continuous.comp B.continuous_oneVal
  set u : B.One → c.φ.model.E 0 := fun w => c.φ (ρ (P (B.oneVal w))) with hu
  set z : B.One → (c.φ.model.E.prod c.F.shift) 0 := fun w => (u w, chartFibMap c (u w) (Φ w).2)
    with hz
  set T : B.One → B.One := fun w => Φ.symm (z w) with hT
  have huO : ∀ w ∈ S, u w ∈ c.φ.model.O := fun w hw => c.φ.mapsTo_model _ (hρc hw)
  have hzK : ∀ w ∈ S, z w ∈ strongShiftOne c.K := fun w hw => mem_K_chartFibMap (huO w hw) _
  have hPT : ∀ w ∈ S, P (B.oneVal (T w)) = ρ (P (B.oneVal w)) := fun w hw =>
    proj_oneChartOf_symm hc y₀ (hρc hw) (hzK w hw)
  have hMT : ∀ w, retractNorm hc y₀ ρ N w = N (T w) + ‖(Φ w).2 - (z w).2‖ := fun _ => rfl
  have hSsrc : ∀ w ∈ S, w ∈ Φ.source := fun w hw => (mem_oneChartOf_source hc y₀).2 (hVc hw)
  -- continuity of the pieces
  have hΦc : ContinuousOn Φ S := Φ.continuousOn_toFun.mono hSsrc
  have huc : ContinuousOn u S :=
    c.φ.continuousOn_toFun.comp (hρ.comp hPc.continuousOn fun _ hw => hw) fun _ hw => hρc hw
  have hzc : ContinuousOn z S := by
    have h1 : ContinuousOn (fun w => shiftFiber c.R (u w, (Φ w).2)) S :=
      continuousOn_shiftFiber_R.comp (huc.prodMk (continuous_snd.comp_continuousOn hΦc))
        fun w hw => ⟨mem_U_of_mem_O (huO w hw), mem_univ _⟩
    exact h1.congr fun w hw => (shiftFiber_eq_chartFibMap (huO w hw) _).symm
  have hTc : ContinuousOn T S := Φ.continuousOn_invFun.comp hzc hzK
  refine ⟨?_, fun y hy => ?_, fun w y hyV hy hM => ?_⟩
  · -- continuity of `N'` on `W_{0,1}|V`
    have h1 : ContinuousOn (fun w => N (T w)) S :=
      hNc.comp hTc fun w hw => by
        change P (B.oneVal (T w)) ∈ A
        rw [hPT w hw]; exact hρA hw
    have h2 : ContinuousOn (fun w => ‖(Φ w).2 - (z w).2‖) S :=
      continuous_norm.comp_continuousOn
        ((continuous_snd.comp_continuousOn hΦc).sub (continuous_snd.comp_continuousOn hzc))
    exact (h1.add h2).congr fun w _ => hMT w
  · -- seminorms on the fibres
    exact isFiberSeminorm_retractNorm (hVc hy) (hρc hy) (hNs _ (hρA hy))
  · -- condition (2)
    have hev : ∀ᶠ k in atTop, w k ∈ S := hy.eventually (hV.mem_nhds hyV)
    have hnn1 : ∀ᶠ k in atTop, 0 ≤ N (T (w k)) := hev.mono fun k hk => by
      have hs := hNs _ (hρA hk)
      rw [← hPT _ hk] at hs
      exact hs.nonneg (B.ofOne (T (w k)))
    have hle : ∀ᶠ k in atTop, N (T (w k)) ≤ retractNorm hc y₀ ρ N (w k) :=
      Eventually.of_forall fun k => by rw [hMT]; exact le_add_of_nonneg_right (norm_nonneg _)
    have hN0 : Tendsto (fun k => N (T (w k))) atTop (𝓝 0) :=
      tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hM hnn1 hle
    have hle2 : ∀ᶠ k in atTop, ‖(Φ (w k)).2 - (z (w k)).2‖ ≤ retractNorm hc y₀ ρ N (w k) :=
      hnn1.mono fun k hk => by rw [hMT]; linarith
    have hD0 : Tendsto (fun k => ‖(Φ (w k)).2 - (z (w k)).2‖) atTop (𝓝 0) :=
      tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hM
        (Eventually.of_forall fun _ => norm_nonneg _) hle2
    -- `T(w_k) → 0_{ρ(y)}`, through condition (2) of `N` on a tail of the sequence
    have hρt : Tendsto (fun k => ρ (P (B.oneVal (w k)))) atTop (𝓝 (ρ y)) :=
      (hρ.continuousAt (hV.mem_nhds hyV)).tendsto.comp hy
    obtain ⟨K₀, hK₀⟩ := eventually_atTop.1 hev
    have hTt : Tendsto (fun k => T (w k)) atTop (𝓝 (B.zeroOne (ρ y))) := by
      rw [← tendsto_add_atTop_iff_nat K₀]
      refine hN2 (fun k => T (w (k + K₀))) (ρ y) (hρA hyV)
        (fun k => by rw [hPT _ (hK₀ _ (Nat.le_add_left _ _))]; exact hρA (hK₀ _ (by omega)))
        ?_ ((tendsto_add_atTop_iff_nat K₀).2 hN0)
      have := (tendsto_add_atTop_iff_nat K₀).2 hρt
      refine this.congr fun k => ?_
      rw [hPT _ (hK₀ _ (by omega))]
    -- read in the chart: `A(u_k)h_k → 0` in `F₁`
    have hρyc : ρ y ∈ c.φ.source := hρc hyV
    have h0src : B.zeroOne (ρ y) ∈ Φ.source :=
      (mem_oneChartOf_source hc y₀).2 (by rw [proj_oneVal_zeroOne B]; exact hρyc)
    have hΦT : Tendsto (fun k => Φ (T (w k))) atTop (𝓝 (c.φ (ρ y), 0)) := by
      have := (Φ.continuousOn_toFun.continuousAt (Φ.isOpen_source.mem_nhds h0src)).tendsto.comp
        hTt
      rwa [oneChartOf_apply, oneVal_zeroOne B, liftOne_fiberZero hρyc] at this
    have hA0 : Tendsto (fun k => (z (w k)).2) atTop (𝓝 0) := by
      have := (continuous_snd.tendsto _).comp hΦT
      refine this.congr' ?_
      filter_upwards [hev] with k hk
      change (Φ (Φ.symm (z (w k)))).2 = (z (w k)).2
      rw [Φ.apply_symm_apply (hzK _ hk)]
    have hh0 : Tendsto (fun k => (Φ (w k)).2) atTop (𝓝 0) := by
      have h1 := (tendsto_zero_iff_norm_tendsto_zero.2 hD0).add hA0
      rw [add_zero] at h1
      exact h1.congr fun k => sub_add_cancel _ _
    have hyc : y ∈ c.φ.source := hVc hyV
    have h1 : Tendsto (fun k => (Φ (w k)).1) atTop (𝓝 (c.φ y)) := by
      have := (c.φ.continuousOn_toFun.continuousAt (c.φ.isOpen_source.mem_nhds hyc)).tendsto.comp
        hy
      refine this.congr' ?_
      filter_upwards [hev] with k hk
      rw [oneChartOf_apply, fst_liftOne (hVc hk)]; rfl
    have hy0src : B.zeroOne y ∈ Φ.source :=
      (mem_oneChartOf_source hc y₀).2 (by rw [proj_oneVal_zeroOne B]; exact hyc)
    refine Φ.tendsto_of_tendsto_apply hy0src (hev.mono fun _ hk => hSsrc _ hk) ?_
    rw [oneChartOf_apply, oneVal_zeroOne B, liftOne_fiberZero hyc]
    exact h1.prodMk_nhds hh0

/-- **`N' = N` on `V ∩ A`** when `ρ` is the identity there. -/
theorem retractNorm_eq {A V : Set X} (hVc : V ⊆ c.φ.source) {ρ : X → X}
    (hfix : ∀ y ∈ V ∩ A, ρ y = y) (N : B.One → ℝ) {w : B.One} (hw : P (B.oneVal w) ∈ V ∩ A) :
    retractNorm hc y₀ ρ N w = N w :=
  retractNorm_eq_of_fix N (hVc hw.1) (hfix _ hw)

end LocalAux

/-- **The local extension of an auxiliary norm from `∂X`** (proof of Theorem 12.2.7, p. 575,
Part I form): for a strong bundle over a tame M-polyfold and `N` an auxiliary norm over `∂X`
(continuous on `W_{0,1}|∂X`, seminorms on the fibres over `∂X`, condition (2) for sequences in
`∂X`), every boundary point has an open neighbourhood `V` and a local auxiliary norm on `V` equal
to `N` over `V ∩ ∂X`. -/
theorem exists_localExtension_of_isTame (hP : PX.IsTame) {N : B.One → ℝ}
    (hNc : ContinuousOn N {w | P (B.oneVal w) ∈ PX.boundary})
    (hNs : ∀ y ∈ PX.boundary, B.IsFiberSeminorm N y)
    (hN2 : ∀ (w : ℕ → B.One) (y : X), y ∈ PX.boundary → (∀ k, P (B.oneVal (w k)) ∈ PX.boundary) →
      Tendsto (fun k => P (B.oneVal (w k))) atTop (𝓝 y) →
        Tendsto (fun k => N (w k)) atTop (𝓝 0) → Tendsto w atTop (𝓝 (B.zeroOne y)))
    {x₀ : X} (hx₀ : x₀ ∈ PX.boundary) :
    ∃ V : Set X, IsOpen V ∧ x₀ ∈ V ∧ ∃ M : B.One → ℝ,
      B.IsLocalAuxNorm V M ∧ ∀ w : B.One, P (B.oneVal w) ∈ V ∩ PX.boundary → M w = N w := by
  obtain ⟨V₁, ρ, hV₁, hx₀V₁, hρ, hρA, hfix⟩ := PX.exists_retraction_boundary hP hx₀
  obtain ⟨c, hcm, hx₀c⟩ := exists_chart_mem B x₀
  have hc := B.isChart_of_mem hcm
  set V := (V₁ ∩ c.φ.source) ∩ ρ ⁻¹' c.φ.source
  have hVo : IsOpen V :=
    (hρ.mono inter_subset_left).isOpen_inter_preimage (hV₁.inter c.φ.isOpen_source)
      c.φ.isOpen_source
  have hρx₀ : ρ x₀ = x₀ := hfix x₀ ⟨hx₀V₁, hx₀⟩
  have hx₀V : x₀ ∈ V := ⟨⟨hx₀V₁, hx₀c⟩, by rw [mem_preimage, hρx₀]; exact hx₀c⟩
  have hVc : V ⊆ c.φ.source := fun y hy => hy.1.2
  refine ⟨V, hVo, hx₀V, retractNorm hc (B.zeroOne x₀) ρ N, ?_, fun w hw => ?_⟩
  · exact isLocalAuxNorm_retractNorm hc _ hVo hVc (hρ.mono fun y hy => hy.1.1)
      (fun y hy => hρA hy.1.1) (fun y hy => hy.2) hNc hNs hN2
  · exact retractNorm_eq hc _ hVc (fun y hy => hfix y ⟨hy.1.1.1, hy.2⟩) N hw

end StrongBundle

/-! ### The local step and Theorem 12.2.7 -/

section Thm1227

variable {Obj Mor : Type u} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] {X : EpGroupoid Obj Mor}
  {W : Type u} [TopologicalSpace W] [T2Space W] [ParacompactSpace W] {P : W → Obj}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle X.PObj P}

namespace EpStrongBundle

variable {E : EpStrongBundle X B}

/-- **The local extension step of the proof of Theorem 12.2.7** (p. 575) for tame `X`: an
auxiliary norm `N` for `W|∂X` has local extensions near every boundary point (the hypothesis
`HasLocalExtensions` of `theorem_12_2_7_hyp`). -/
theorem hasLocalExtensions_of_isTame (hX : X.IsTame) {N : B.One → ℝ}
    (hN : E.IsAuxNormOn X.PObj.boundary N) : HasLocalExtensions X B N := fun _ hx =>
  StrongBundle.exists_localExtension_of_isTame hX hN.continuousOn
    (fun y hy => (hN.fiber y hy).isFiberSeminorm) hN.tendsto_zeroOne hx

/-- **Theorem 12.2.7 (extension of auxiliary norms, pp. 574–576)**: for a strong bundle
`(P : W → X, μ)` over a tame ep-groupoid with paracompact orbit space `|X|`, every auxiliary norm
`N` for `W|∂X` (Definition 12.2.1 over `∂X`) extends to an auxiliary norm `Ñ` of `W` which
coincides with `N` over `∂X`. -/
theorem theorem_12_2_7 (hX : X.IsTame) (h : X.HasParacompactOrbitSpace) {N : B.One → ℝ}
    (hN : E.IsAuxNormOn X.PObj.boundary N) :
    ∃ Ñ : B.One → ℝ, E.IsAuxNorm Ñ ∧
      ∀ w : B.One, P (B.oneVal w) ∈ X.PObj.boundary → Ñ w = N w :=
  theorem_12_2_7_hyp h hN (hasLocalExtensions_of_isTame hX hN)

end EpStrongBundle

end Thm1227

end Polyfold
