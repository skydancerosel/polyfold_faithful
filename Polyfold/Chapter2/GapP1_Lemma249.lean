import Polyfold.Chapter2.PartialConeQuadrant
import Polyfold.Chapter1.Levels
import Polyfold.Chapter3.ParamPerturbation
import Polyfold.Chapter3.StrongBundleSections
import Polyfold.Chapter5.BumpFunctions

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), §2.4, Lemma 2.4.9,
pp. 48–49 (preprint Lemma 2.29).

# `T^R_xO` and `C_xO` through sc-smooth paths; `T_xO = C_xO − C_xO`

## The text, paraphrased

For a retract `(O, C, E)` with `C = [0,∞)^k ⊕ W` and a smooth `x ∈ O`:
(1) `T^R_xO` is the closure of the derivatives `α̇(0)` of sc-smooth paths `α : (−ε, ε) → O` with
`α(0) = x`; (2) `C_xO` is the closure of the derivatives `α̇(0)` of sc-smooth paths
`α : [0, ε) → O` with `α(0) = x`; (3) `T_xO = C_xO − C_xO`.

## What is formalized

Paths are maps `α : ℝ → E₀`, sc-smooth on `(−ε, ε)` or `[0, ε)` for the constant sc-structure
on `ℝ` (both are sc-domains, `isScDomain_const_real`); `α̇(0)` is `pathDeriv U α = Dα(0)·1`, the
derivative of Definition 1.1.15 (`hasDerivWithinAt_pathDeriv`: it is the classical one-sided or
two-sided derivative).  The partial quadrant is given by a presentation `T`, `C = T⁻¹([0,∞)ⁿ ⊕ W)`.

* `lemma_2_4_9_reduced` (1): `closure Γ₂(x) = T^R_xO` for `x ∈ O` smooth (`x ∈ O₁ ∩ E_∞`).
* `lemma_2_4_9_cone` (2): `closure Γ₁(x) = C_xO`.
* `lemma_2_4_9_tangent` (3): `T_xO = C_xO − C_xO`, for every `x ∈ O₁`.

The proof is the text's: `r ∘ α = α` gives `Dr(x)α̇(0) = α̇(0)` (chain rule, Theorem 1.3.1); the
sign of `α_i ≥ 0` at a zero gives `α̇_i(0) = 0` (two-sided) or `≥ 0` (one-sided); conversely
`α(t) = r(x + tv)` for smooth `v`; the smooth points of `T^R_xO` and `C_xO` are dense.
-/

open Set Filter Topology
open scoped Pointwise

noncomputable section

namespace Polyfold

namespace GapP1Lemma249

variable {E : ScBanach}

/-! ### Paths in the constant sc-structure on `ℝ` -/

lemma lvlSet_const_real (U : Set ℝ) (m : ℕ) : (ScBanach.const ℝ).lvlSet U m = U := by
  ext t
  rw [ScBanach.mem_lvlSet, ScBanach.const_toBase]

/-- A convex `U ⊆ ℝ` with unique derivatives is an sc-domain of the constant sc-structure. -/
lemma isScDomain_const_real {U : Set ℝ} (hc : Convex ℝ U) (hu : UniqueDiffOn ℝ U) :
    IsScDomain (ScBanach.const ℝ) U where
  relOpenConvex m := ⟨univ, U, isOpen_univ, hc, by rw [lvlSet_const_real, univ_inter]⟩
  uniqueDiffWithinAt m t ht := by
    rw [lvlSet_const_real] at ht ⊢
    exact hu t ht

lemma isScDomain_Ioo (ε : ℝ) : IsScDomain (ScBanach.const ℝ) (Ioo (-ε) ε) :=
  isScDomain_const_real (convex_Ioo _ _) (isOpen_Ioo.uniqueDiffOn)

lemma isScDomain_Ico (ε : ℝ) : IsScDomain (ScBanach.const ℝ) (Ico 0 ε) :=
  isScDomain_const_real (convex_Ico _ _) (uniqueDiffOn_Ico _ _)

/-- The derivative `α̇(0) = Dα(0)·1` of a path `α : U → E₀`, `U ⊆ ℝ`, at `t = 0`
(Definition 1.1.15 for the constant sc-structure on `ℝ`). -/
def pathDeriv (U : Set ℝ) (α : ℝ → E 0) : E 0 :=
  scDeriv (E := ScBanach.const ℝ) (F := E) U α (0 : ℝ) (1 : ℝ)

/-- `α̇(0)` is the classical derivative of `α` within `U` at `0`. -/
lemma hasDerivWithinAt_pathDeriv {U : Set ℝ} {α : ℝ → E 0}
    (h : IsSc1 (E := ScBanach.const ℝ) (F := E) U α) (h0 : (0 : ℝ) ∈ U) :
    HasDerivWithinAt α (pathDeriv U α) U 0 := by
  have h1 := h.isSc1With_scDeriv.hasFDerivWithinAt (0 : ℝ)
    (by rw [lvlSet_const_real]; exact h0)
  rw [lvlSet_const_real] at h1
  have h2 : (α ∘ (ScBanach.const ℝ).toBase 1) = α :=
    funext fun t => congrArg α (ScBanach.const_toBase ℝ 1 t)
  rw [h2] at h1
  have h3 := h1.hasDerivWithinAt
  have h4 : ((ScBanach.const ℝ).toBase 1) (1 : ℝ) = 1 := ScBanach.const_toBase ℝ 1 1
  rw [ContinuousLinearMap.comp_apply, h4] at h3
  exact h3

/-! ### The derivative of a path in `O` lies in `T_xO` -/

variable {n : ℕ} {W : ScBanach} {C : Set (E 0)} (R : ScRetraction E C)
  (T : ScIso E ((ScBanach.const (Fin n → ℝ)).prod W))

/-- For an sc¹ path `α` in `O` with `α(0) = x`: `Dr(x)α̇(0) = α̇(0)` (chain rule for
`r ∘ α = α`). -/
lemma scDeriv_pathDeriv {U : Set ℝ} (hU : IsScDomain (ScBanach.const ℝ) U) {α : ℝ → E 0}
    (hα : IsSc1 (E := ScBanach.const ℝ) (F := E) U α) (hαO : MapsTo α U R.retract)
    (h0 : (0 : ℝ) ∈ U) {x : E 1} (hx0 : α 0 = E.toBase 1 x) :
    scDeriv R.U R x (pathDeriv U α) = pathDeriv U α := by
  have hRU : MapsTo α U R.U := fun t ht => R.retract_subset (hαO ht)
  have hcomp := R.isSc1.isSc1With_scDeriv.comp (R.isScDomain.relOpenConvex 1)
    hα.isSc1With_scDeriv hRU
  have hcongr : IsSc1With (E := ScBanach.const ℝ) U (R ∘ α) (scDeriv U α) :=
    hα.isSc1With_scDeriv.congr fun t ht => (R.apply_eq_self_of_mem_retract (hαO ht)).symm
  have h01 : (0 : ℝ) ∈ (ScBanach.const ℝ).lvlSet U 1 := by rw [lvlSet_const_real]; exact h0
  have heq := hcomp.eq_of_uniqueDiffWithinAt hcongr h01 (hU.uniqueDiffWithinAt 1 _ h01)
  have hlev : levelMap (E := ScBanach.const ℝ) α 1 (0 : ℝ) = x := by
    apply E.toBase_injective 1
    rw [hα.isSc0.toBase_levelMap h01, ScBanach.const_toBase, hx0]
  rw [hlev] at heq
  exact congrArg (fun L : (ScBanach.const ℝ) 0 →L[ℝ] E 0 => L (1 : ℝ)) heq

/-- The coordinate `t ↦ (T α(t))_i` and its derivative. -/
lemma hasDerivWithinAt_coord {U : Set ℝ} {α : ℝ → E 0} {w : E 0}
    (h : HasDerivWithinAt α w U 0) (i : Fin n) :
    HasDerivWithinAt (fun t => (T 0 (α t)).1 i) ((T 0 w).1 i) U 0 := by
  let L : E 0 →L[ℝ] ℝ := ((ContinuousLinearMap.proj i).comp
    (ContinuousLinearMap.fst ℝ (Fin n → ℝ) (W 0))).comp (T 0 : E 0 →L[ℝ] _)
  exact L.hasFDerivAt.comp_hasDerivWithinAt 0 h

/-- **The sign argument, two-sided**: for an sc¹ path `α : (−ε, ε) → C`, `α̇(0) ∈ E_{α(0)}`. -/
lemma pathDeriv_mem_minimalSubspaceWith (hT : C = T 0 ⁻¹' quadrant n W 0) {ε : ℝ} (hε : 0 < ε)
    {α : ℝ → E 0} (hα : IsSc1 (E := ScBanach.const ℝ) (F := E) (Ioo (-ε) ε) α)
    (hαC : MapsTo α (Ioo (-ε) ε) C) :
    pathDeriv (Ioo (-ε) ε) α ∈ minimalSubspaceWith T (α 0) := by
  have h0 : (0 : ℝ) ∈ Ioo (-ε) ε := ⟨by linarith, hε⟩
  rw [mem_minimalSubspaceWith]
  intro i hi
  have hd := (hasDerivWithinAt_coord T (hasDerivWithinAt_pathDeriv hα h0) i).hasDerivAt
    (Ioo_mem_nhds (by linarith) hε)
  have hmin : IsLocalMin (fun t => (T 0 (α t)).1 i) 0 := by
    filter_upwards [Ioo_mem_nhds (by linarith : -ε < 0) hε] with t ht
    have := hαC ht
    rw [hT] at this
    simp only [hi]
    exact this i
  exact hmin.hasDerivAt_eq_zero hd

/-- **The sign argument, one-sided**: for an sc¹ path `α : [0, ε) → C`, `α̇(0) ∈ C_{α(0)}`. -/
lemma pathDeriv_mem_partialQuadrantAtWith (hT : C = T 0 ⁻¹' quadrant n W 0) {ε : ℝ}
    (hε : 0 < ε) {α : ℝ → E 0} (hα : IsSc1 (E := ScBanach.const ℝ) (F := E) (Ico 0 ε) α)
    (hαC : MapsTo α (Ico 0 ε) C) :
    pathDeriv (Ico 0 ε) α ∈ partialQuadrantAtWith T (α 0) := by
  have h0 : (0 : ℝ) ∈ Ico 0 ε := ⟨le_rfl, hε⟩
  intro i hi
  have hd := hasDerivWithinAt_coord T (hasDerivWithinAt_pathDeriv hα h0) i
  have hmin : IsLocalMinOn (fun t => (T 0 (α t)).1 i) (Ico 0 ε) 0 := by
    refine Filter.eventually_of_mem self_mem_nhdsWithin fun t ht => ?_
    have := hαC ht
    rw [hT] at this
    simp only [hi]
    exact this i
  have hy : ε / 2 ∈ posTangentConeAt (Ico 0 ε) (0 : ℝ) := by
    refine mem_posTangentConeAt_of_segment_subset ?_
    rw [zero_add, segment_eq_Icc (by linarith)]
    exact Icc_subset_Ico_right (by linarith)
  have := hmin.hasFDerivWithinAt_nonneg hd.hasFDerivWithinAt hy
  simp only [ContinuousLinearMap.toSpanSingleton_apply, smul_eq_mul] at this
  nlinarith

/-! ### The paths `t ↦ r(x + tv)` -/

/-- For a smooth `x ∈ O`, a smooth `v` and `U ∋ 0` with `x + tv ∈ U_r` on `U`, the path
`α(t) = r(x + tv)` is sc-smooth on `U`, lies in `O`, starts at `x`, and `α̇(0) = Dr(x)v`. -/
lemma path_retract_segment {U : Set ℝ} (hU : IsScDomain (ScBanach.const ℝ) U)
    (hUu : UniqueDiffWithinAt ℝ U 0) (h0 : (0 : ℝ) ∈ U) {x : E 1}
    (hx : x ∈ E.lvlSet R.retract 1) (hs : x ∈ E.smoothLvl 1) {v : E 0} (hv : v ∈ E.smooth)
    (hxv : ∀ t ∈ U, E.toBase 1 x + t • v ∈ R.U) :
    IsScSmooth (E := ScBanach.const ℝ) (F := E) U (fun t : ℝ => R (E.toBase 1 x + t • v)) ∧
      MapsTo (fun t : ℝ => R (E.toBase 1 x + t • v)) U R.retract ∧
      R (E.toBase 1 x + (0 : ℝ) • v) = E.toBase 1 x ∧
      pathDeriv U (fun t : ℝ => R (E.toBase 1 x + t • v)) = scDeriv R.U R x v := by
  set x0 := E.toBase 1 x with hx0
  have hx0s : x0 ∈ E.smooth := hs
  have hc₀ : IsScSmooth (E := ScBanach.const ℝ) (F := E) U fun _ => x0 :=
    isScSmooth_const_of_mem_smooth hU hx0s
  have hc₁ : IsScSmooth (E := ScBanach.const ℝ) (F := E) U fun _ => v :=
    isScSmooth_const_of_mem_smooth hU hv
  have hid : IsScSmooth (E := ScBanach.const ℝ) (F := ScBanach.const ℝ) U fun t : ℝ => t :=
    IsScSmooth.of_contDiffOn_finiteDimensional (V := ℝ) hU contDiffOn_id
  have hγ : IsScSmooth (E := ScBanach.const ℝ) (F := E) U fun t : ℝ => x0 + t • v :=
    hc₀.add hU (hid.smul hU hc₁)
  have hα : IsScSmooth (E := ScBanach.const ℝ) (F := E) U fun t : ℝ => R (x0 + t • v) :=
    IsScSmooth.comp hU R.isScDomain R.isScSmooth hγ hxv
  have hxO : x0 ∈ R.retract := hx
  have hfix : R x0 = x0 := R.apply_eq_self_of_mem_retract hxO
  refine ⟨hα, fun t ht => R.apply_mem_retract (hxv t ht), by rw [zero_smul, add_zero, hfix], ?_⟩
  -- the derivative, by the chain rule
  have hγ1 : IsSc1 (E := ScBanach.const ℝ) (F := E) U fun t : ℝ => x0 + t • v := hγ.isSc1
  have hα1 : IsSc1 (E := ScBanach.const ℝ) (F := E) U fun t : ℝ => R (x0 + t • v) := hα.isSc1
  have hcomp := R.isSc1.isSc1With_scDeriv.comp (R.isScDomain.relOpenConvex 1)
    hγ1.isSc1With_scDeriv hxv
  have h01 : (0 : ℝ) ∈ (ScBanach.const ℝ).lvlSet U 1 := by rw [lvlSet_const_real]; exact h0
  have heq := hα1.isSc1With_scDeriv.eq_of_uniqueDiffWithinAt hcomp h01
    (hU.uniqueDiffWithinAt 1 _ h01)
  have hlev : levelMap (E := ScBanach.const ℝ) (fun t : ℝ => x0 + t • v) 1 (0 : ℝ) = x := by
    apply E.toBase_injective 1
    rw [hγ1.isSc0.toBase_levelMap h01, ScBanach.const_toBase, zero_smul, add_zero]
  rw [hlev] at heq
  have hγd : pathDeriv U (fun t : ℝ => x0 + t • v) = v := by
    have h1 := hasDerivWithinAt_pathDeriv hγ1 h0
    have h2 : HasDerivWithinAt (fun t : ℝ => x0 + t • v) v U 0 := by
      have := ((hasDerivWithinAt_id (0 : ℝ) U).smul_const v).const_add x0
      simpa only [one_smul, id] using this
    exact hUu.eq_deriv _ h1 h2
  change scDeriv (E := ScBanach.const ℝ) U (fun t : ℝ => R (x0 + t • v)) (0 : ℝ) 1 = _
  rw [heq]
  change scDeriv R.U R x (pathDeriv U (fun t : ℝ => x0 + t • v)) = _
  rw [hγd]

/-! ### The sets of path derivatives -/

/-- `Γ₂(x)`: the derivatives `α̇(0)` of sc-smooth paths `α : (−ε, ε) → O` with `α(0) = x`. -/
def twoSidedPathDerivs (x : E 1) : Set (E 0) :=
  {w | ∃ ε > 0, ∃ α : ℝ → E 0, IsScSmooth (E := ScBanach.const ℝ) (F := E) (Ioo (-ε) ε) α ∧
    MapsTo α (Ioo (-ε) ε) R.retract ∧ α 0 = E.toBase 1 x ∧ pathDeriv (Ioo (-ε) ε) α = w}

/-- `Γ₁(x)`: the derivatives `α̇(0)` of sc-smooth paths `α : [0, ε) → O` with `α(0) = x`. -/
def oneSidedPathDerivs (x : E 1) : Set (E 0) :=
  {w | ∃ ε > 0, ∃ α : ℝ → E 0, IsScSmooth (E := ScBanach.const ℝ) (F := E) (Ico 0 ε) α ∧
    MapsTo α (Ico 0 ε) R.retract ∧ α 0 = E.toBase 1 x ∧ pathDeriv (Ico 0 ε) α = w}

variable {R T}

/-- `Dr(x)v = v` for `v = Dr(x)u`, `x ∈ O₁`. -/
lemma scDeriv_eq_self_of_eq {x : E 1} (hx : x ∈ E.lvlSet R.retract 1) {u v : E 0}
    (hu : scDeriv R.U R x u = v) : scDeriv R.U R x v = v := by
  rw [← hu]
  exact congrArg (fun L : E 0 →L[ℝ] E 0 => L u) (R.scDeriv_comp_self hx)

lemma mem_range_of_scDeriv_eq {x : E 1} {w : E 0} (h : scDeriv R.U R x w = w) :
    w ∈ range (scDeriv R.U R x) := ⟨w, h⟩

/-- The smooth points of `C_xO` are dense in `C_xO`, at a smooth `x ∈ O`. -/
lemma partialConeWith_subset_closure (hT : C = T 0 ⁻¹' quadrant n W 0) {x : E 1}
    (hx : x ∈ E.lvlSet R.retract 1) (hs : x ∈ E.smoothLvl 1) :
    partialConeWith R T x ⊆ closure (partialConeWith R T x ∩ E.smooth) := by
  rintro v ⟨⟨u, rfl⟩, hvC⟩
  set P := scDeriv R.U R x with hPdef
  have hop := R.isScOperator_scDeriv (R.lvlSet_retract_subset 1 hx) hs
  set Pop := hop.toScOperator with hPop
  have hP0 : ∀ v, Pop 0 v = P v := fun v => by rw [hPop, hop.toScOperator_zero]
  have hPP : ∀ v, P (P v) = P v := fun v =>
    congrArg (fun L : E 0 →L[ℝ] E 0 => L v) (R.scDeriv_comp_self hx)
  set a := (T 0 (P u)).1 with ha
  let φ : W 0 → E 0 := fun w' => P ((T 0).symm (a, w'))
  have hφc : Continuous φ :=
    P.continuous.comp ((T 0).symm.continuous.comp (continuous_const.prodMk continuous_id))
  have hφw : φ (T 0 (P u)).2 = P u := by
    change P ((T 0).symm ((T 0 (P u)).1, (T 0 (P u)).2)) = P u
    rw [Prod.mk.eta, ContinuousLinearEquiv.symm_apply_apply, hPP]
  have hφS : MapsTo φ (W.smoothLvl 0) (partialConeWith R T x ∩ E.smooth) := by
    intro w' hw'
    have hC : (T 0).symm (a, w') ∈ partialQuadrantAtWith T (E.toBase 1 x) := by
      intro i hi
      rw [ContinuousLinearEquiv.apply_symm_apply]
      exact hvC i hi
    refine ⟨⟨⟨_, rfl⟩, R.scDeriv_mapsTo_partialQuadrant T hT hx hC⟩, ?_⟩
    have hp : ((a, w') : ((ScBanach.const (Fin n → ℝ)).prod W) 0) ∈
        ((ScBanach.const (Fin n → ℝ)).prod W).smoothLvl 0 := by
      rw [ScBanach.prod_smoothLvl]
      exact ⟨by rw [ScBanach.constScale_smoothLvl]; exact mem_univ _, hw'⟩
    have h1 := Pop.mapsTo_smoothLvl 0 (T.symm.toScOperator.mapsTo_smoothLvl 0 hp)
    rw [hP0] at h1
    exact h1
  rw [← hφw]
  exact map_mem_closure hφc ((W.dense_smooth 0).closure_eq ▸ mem_univ _) hφS

/-- **Lemma 2.4.9 (1) (2021 p. 48; preprint 2.29)**: at a smooth `x ∈ O`, `T^R_xO` is the closure
of the derivatives `α̇(0)` of sc-smooth paths `α : (−ε, ε) → O` with `α(0) = x`. -/
theorem lemma_2_4_9_reduced (hT : C = T 0 ⁻¹' quadrant n W 0) {x : E 1}
    (hx : x ∈ E.lvlSet R.retract 1) (hs : x ∈ E.smoothLvl 1) :
    closure (twoSidedPathDerivs R x) = (reducedTangentSpaceWith R T x : Set (E 0)) := by
  have hB := R.isScSubspace_reducedTangentSpaceWith T hT hx hs
  apply Subset.antisymm
  · refine closure_minimal ?_ hB.isClosed
    rintro w ⟨ε, hε, α, hα, hαO, hα0, rfl⟩
    have h0 : (0 : ℝ) ∈ Ioo (-ε) ε := ⟨by linarith, hε⟩
    refine Submodule.mem_inf.2 ⟨?_, ?_⟩
    · obtain ⟨u, hu⟩ := mem_range_of_scDeriv_eq
        (scDeriv_pathDeriv R (isScDomain_Ioo ε) hα.isSc1 hαO h0 hα0)
      exact ⟨u, hu⟩
    · rw [← hα0]
      exact pathDeriv_mem_minimalSubspaceWith T hT hε hα.isSc1
        fun t ht => R.U_subset_C (R.retract_subset (hαO ht))
  · intro v hv
    have hcl := hB.2 0 (show E.toBase 0 v ∈ reducedTangentSpaceWith R T x from hv)
    refine closure_mono ?_ hcl
    rintro v ⟨hvB, hvs⟩
    have hvs' : v ∈ E.smooth := hvs
    have hvB' : v ∈ reducedTangentSpaceWith R T x := hvB
    obtain ⟨v₁, hv₁⟩ := E.mem_smooth_iff.1 hvs' 1
    have hvE : E.toBase 1 v₁ ∈ minimalSubspaceWith T (E.toBase 1 x) := by
      rw [hv₁]; exact (Submodule.mem_inf.1 hvB').2
    have hev := eventually_add_smul_mem_lvlSet T hT R.relOpen (R.lvlSet_retract_subset 1 hx) hvE
    obtain ⟨ε, hε, hεs⟩ := Metric.eventually_nhds_iff.1 hev
    have hxv : ∀ t ∈ Ioo (-ε) ε, E.toBase 1 x + t • v ∈ R.U := by
      intro t ht
      have h := hεs (show dist t 0 < ε by
        rw [Real.dist_eq, sub_zero, abs_lt]; exact ⟨ht.1, ht.2⟩)
      have h' : E.toBase 1 (x + t • v₁) ∈ R.U := h
      rwa [map_add, map_smul, hv₁] at h'
    have h0 : (0 : ℝ) ∈ Ioo (-ε) ε := ⟨by linarith, hε⟩
    obtain ⟨hα, hαO, hα0, hαd⟩ := path_retract_segment R (isScDomain_Ioo ε)
      (isOpen_Ioo.uniqueDiffWithinAt h0) h0 hx hs hvs' hxv
    refine ⟨ε, hε, _, hα, hαO, by simpa using hα0, ?_⟩
    rw [hαd]
    obtain ⟨u, hu⟩ := (Submodule.mem_inf.1 hvB').1
    exact scDeriv_eq_self_of_eq hx hu

/-- **Lemma 2.4.9 (2) (2021 p. 48; preprint 2.29)**: at a smooth `x ∈ O`, `C_xO` is the closure
of the derivatives `α̇(0)` of sc-smooth paths `α : [0, ε) → O` with `α(0) = x`. -/
theorem lemma_2_4_9_cone (hT : C = T 0 ⁻¹' quadrant n W 0) {x : E 1}
    (hx : x ∈ E.lvlSet R.retract 1) (hs : x ∈ E.smoothLvl 1) :
    closure (oneSidedPathDerivs R x) = partialConeWith R T x := by
  have hA := (R.isScSplitting_range_scDeriv hx hs).1
  have hclosed : IsClosed (partialConeWith R T x) := by
    refine IsClosed.inter ?_ (isClosed_partialQuadrantAtWith T _)
    have : range (scDeriv R.U R x) =
        (LinearMap.range (scDeriv R.U R x : E 0 →ₗ[ℝ] E 0) : Set (E 0)) := by
      ext; simp
    rw [this]; exact hA.isClosed
  apply Subset.antisymm
  · refine closure_minimal ?_ hclosed
    rintro w ⟨ε, hε, α, hα, hαO, hα0, rfl⟩
    have h0 : (0 : ℝ) ∈ Ico 0 ε := ⟨le_rfl, hε⟩
    refine ⟨mem_range_of_scDeriv_eq
      (scDeriv_pathDeriv R (isScDomain_Ico ε) hα.isSc1 hαO h0 hα0), ?_⟩
    rw [← hα0]
    exact pathDeriv_mem_partialQuadrantAtWith T hT hε hα.isSc1
      fun t ht => R.U_subset_C (R.retract_subset (hαO ht))
  · refine (partialConeWith_subset_closure hT hx hs).trans (closure_mono ?_)
    rintro v ⟨⟨⟨u, hu⟩, hvC⟩, hvs⟩
    obtain ⟨v₁, hv₁⟩ := E.mem_smooth_iff.1 hvs 1
    have hvC' : E.toBase 1 v₁ ∈ partialQuadrantAtWith T (E.toBase 1 x) := by rw [hv₁]; exact hvC
    have hev := eventually_add_smul_mem_lvlSet_of_cone T hT R.relOpen
      (R.lvlSet_retract_subset 1 hx) hvC'
    obtain ⟨ε, hε, hεs⟩ := mem_nhdsGE_iff_exists_Ico_subset.1 hev
    have hε0 : (0 : ℝ) < ε := hε
    have hxv : ∀ t ∈ Ico 0 ε, E.toBase 1 x + t • v ∈ R.U := by
      intro t ht
      have h' : E.toBase 1 (x + t • v₁) ∈ R.U := hεs ht
      rwa [map_add, map_smul, hv₁] at h'
    have h0 : (0 : ℝ) ∈ Ico 0 ε := ⟨le_rfl, hε0⟩
    obtain ⟨hα, hαO, hα0, hαd⟩ := path_retract_segment R (isScDomain_Ico ε)
      (uniqueDiffOn_Ico 0 ε 0 h0) h0 hx hs hvs hxv
    refine ⟨ε, hε0, _, hα, hαO, by simpa using hα0, ?_⟩
    rw [hαd]
    exact scDeriv_eq_self_of_eq hx hu

/-- **Lemma 2.4.9 (3) (2021 p. 48; preprint 2.29)**: `T_xO = C_xO − C_xO`, for every `x ∈ O₁`
(smoothness of `x` is not needed). -/
theorem lemma_2_4_9_tangent (hT : C = T 0 ⁻¹' quadrant n W 0) {x : E 1}
    (hx : x ∈ E.lvlSet R.retract 1) :
    tangentSpace E C R.retract x = partialConeWith R T x - partialConeWith R T x := by
  rw [tangentSpace_eq_range R hx]
  set P := scDeriv R.U R x with hPdef
  ext h
  constructor
  · rintro ⟨k, rfl⟩
    -- `k = k⁺ − k⁻` with `k^±` in the quadrant `C`
    set a := (T 0 k).1 with ha
    let am : Fin n → ℝ := fun i => max (-a i) 0
    let km : E 0 := (T 0).symm (am, 0)
    have hkm : ∀ i, 0 ≤ (T 0 km).1 i := fun i => by
      simp only [km, ContinuousLinearEquiv.apply_symm_apply]; exact le_max_right _ _
    have hkp : ∀ i, 0 ≤ (T 0 (k + km)).1 i := fun i => by
      rw [map_add, Prod.fst_add, Pi.add_apply]
      simp only [km, ContinuousLinearEquiv.apply_symm_apply, am]
      rw [← ha]
      have := le_max_left (-a i) 0
      linarith
    have hmem : ∀ y : E 0, (∀ i, 0 ≤ (T 0 y).1 i) →
        P y ∈ partialConeWith R T x := fun y hy =>
      ⟨⟨y, rfl⟩, R.scDeriv_mapsTo_partialQuadrant T hT hx fun i _ => hy i⟩
    refine ⟨P (k + km), hmem _ hkp, P km, hmem _ hkm, ?_⟩
    change P (k + km) - P km = P k
    rw [← map_sub, add_sub_cancel_right]
  · rintro ⟨_, ⟨⟨u, rfl⟩, -⟩, _, ⟨⟨u', rfl⟩, -⟩, rfl⟩
    exact ⟨u - u', map_sub _ _ _⟩

end GapP1Lemma249

end Polyfold
