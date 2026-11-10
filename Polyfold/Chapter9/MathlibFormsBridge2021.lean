import Polyfold.Chapter4.ScFormsPullback2021
import Polyfold.Chapter4.ManifoldForms2021
import Polyfold.Chapter4.ManifoldStokes2021
import Polyfold.Chapter6.SolutionSetOrientation
import Polyfold.Chapter9.TangentSubmanifoldSmooth

/-!
# Restriction of sc-forms to finite-dimensional sub-M-polyfolds (gap G.80)

The invariant of 2021 Theorem 6.7.1 (p. 277; preprint Theorem 6.43) integrates the restriction
`ω|_S` of an sc-differential form `ω ∈ Ωᵏ_∞(X)` (Definition 4.4.2, p. 195) over a solution set `S`,
a finite-dimensional manifold with boundary and corners (Theorem 6.6.18). The proof (p. 278) uses
that `ω|_S` is a smooth form on `S` and that `d(ω|_S) = (dω)|_S`, for Stokes' theorem. Here both
are proved for Mathlib's forms (`ManifoldForm`, `ManifoldForm.extDeriv`) on the charted space
`cornerChartedSpace` of a corner structure of dimension `n`.

* Finite dimensions: `contDiffOn_level_of_finiteDim` (a finite-dimensional sc-smooth map is `C^∞`
  into every level), `contDiffOn_alt_of_apply` (a family of alternating forms is `C^∞` when its
  evaluations are).
* `cornerForm hcs η`: an sc-form `η` on an M-polyfold `Q` with a corner structure of dimension `n`
  (then `Q = Q_∞`, `HasCornerStructureOfDim.mem_smoothSet`), read as a Mathlib form in the corner
  frames of `T_xQ = ℝⁿ`; `contMDiffForm_cornerForm` (`C^∞`); `extDeriv_cornerForm`:
  `d(η_M) = (j^*dη)_M`, `j : Q → Q¹` the identity on points (in corner coordinates both sides are
  the alternating sum of derivatives of `η_φ`).
* `alongLift`, `formsAlong`, `formsInftyAlong`: along an sc-smooth `g : Q → X`, the forms on `X^i`
  and on `Ωᵏ_∞(X)` pulled back with the pull-back API (`formPullback`, `extD_formPullback`,
  `formLower_formPullback`) and read on `Q`; compatible with the system (4.4), with `d` and with
  pull-backs (`formsInftyAlong_comp_formsInftyPullback`).
* The case `g = ι : S ↪ X`: `scFormRestrict`, `contMDiffForm_scFormRestrict`,
  `extDeriv_scFormRestrict`, `scFormRestrict_formLower`, `formsInftyRestrict` (with `_of`, its
  smoothness and `extDeriv_formsInftyRestrict`). `scFormRestrict_apply_modelDeriv`: in a chart `φ`
  of `X`, `ω|_S(x)(v) = ω_φ(φ(x), modelDeriv v₁, …, modelDeriv v_k)`, `modelDeriv` the tangent map
  of `ι` in charts (`SolutionSetOrientation.lean`). `stokes_formsInftyRestrict`: Theorem 4.4.7
  (p. 199) for `ω ∈ Ωⁿ_∞(X)` on a compact oriented `S`, `∫_S (dω)|_S = ∫_{∂S} ω|_S`.
* Hypotheses: a corner structure `hcs` of dimension `n` on `S` and `hch : inst = cornerChartedSpace
  hcs`. They give `S ⊆ X_∞` (`subset_smoothSet_of_hasCornerStructureOfDim`), and they are met by
  every submanifold in good position of a tame `X` (`exists_hasCornerStructureOfDim_of_tame`), in
  particular by the solution sets of Theorem 6.6.18 with the charted space of
  `theorem_6_6_18_oriented` (`exists_hasCornerStructureOfDim_solutionSet`, `hch` by `rfl`).

Our reading: `ω|_S` is the pull-back of `ω` along the inclusion `S → X^i` (`S ⊆ X_∞`), evaluated
on the frame of `T_xS` given by the corner coordinates; the text takes this restriction for
granted.
-/

open Set Filter Topology Manifold Module WithLp

/-- Smoothness `C^∞` (Mathlib's `∞` of the scope `ContDiff`). -/
local notation3 "∞" => ((⊤ : ℕ∞) : WithTop ℕ∞)

noncomputable section

namespace Polyfold

/-! ### Alternating maps on a finite-dimensional space -/

section FiniteDimAlt

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {k : ℕ}

/-- **A multilinear form in a basis**: `f(v) = ∑_r (∏ᵢ bᵢ*(vᵢ)) f(b_{r 1}, …, b_{r k})`. -/
theorem multilinear_eq_sum_basis {ι : Type*} [Fintype ι] (b : Basis ι ℝ E)
    (f : MultilinearMap ℝ (fun _ : Fin k => E) ℝ) (v : Fin k → E) :
    f v = ∑ r : Fin k → ι, (∏ i, b.repr (v i) (r i)) * f fun i => b (r i) := by
  classical
  conv_lhs => rw [show v = fun i => ∑ j, b.repr (v i) j • b j from
    funext fun i => (b.sum_repr (v i)).symm]
  rw [f.map_sum]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [f.map_smul_univ, smul_eq_mul]

variable [FiniteDimensional ℝ E]

/-- A multilinear form on a finite-dimensional space is continuous. -/
theorem continuous_multilinear_of_finiteDimensional
    (f : MultilinearMap ℝ (fun _ : Fin k => E) ℝ) : Continuous f := by
  set b := Module.finBasis ℝ E
  rw [show (f : (Fin k → E) → ℝ) = fun v => ∑ r : Fin k → Fin (finrank ℝ E),
    (∏ i, b.repr (v i) (r i)) * f fun i => b (r i) from funext (multilinear_eq_sum_basis b f)]
  refine continuous_finsetSum _ fun r _ =>
    (continuous_finsetProd _ fun i _ => ?_).mul continuous_const
  exact ((b.coord (r i)).continuous_of_finiteDimensional).comp (continuous_apply i)

/-- An alternating form on a finite-dimensional space, as a continuous alternating form. -/
def altCont (f : E [⋀^Fin k]→ₗ[ℝ] ℝ) : E [⋀^Fin k]→L[ℝ] ℝ :=
  ⟨⟨f.toMultilinearMap, continuous_multilinear_of_finiteDimensional _⟩, f.map_eq_zero_of_eq⟩

@[simp] lemma altCont_apply (f : E [⋀^Fin k]→ₗ[ℝ] ℝ) (v : Fin k → E) : altCont f v = f v := rfl

/-- **`C^r` alternating forms on a finite-dimensional space**: a family `Φ` of continuous
alternating forms is `C^r` on `s` once every evaluation `y ↦ Φ(y)(v)` is. -/
theorem contDiffOn_alt_of_apply {D : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
    {s : Set D} {r : WithTop ℕ∞} {Φ : D → E [⋀^Fin k]→L[ℝ] ℝ}
    (h : ∀ v, ContDiffOn ℝ r (fun y => Φ y v) s) : ContDiffOn ℝ r Φ s := by
  classical
  set b := Module.finBasis ℝ E
  let T : (E [⋀^Fin k]→L[ℝ] ℝ) →ₗ[ℝ] ((Fin k → Fin (finrank ℝ E)) → ℝ) :=
    { toFun := fun f r => f fun i => b (r i)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hT : LinearMap.ker T = ⊥ := by
    refine LinearMap.ker_eq_bot'.2 fun f hf => ?_
    ext v
    have h0 : ∀ r : Fin k → Fin (finrank ℝ E), f (fun i => b (r i)) = 0 := fun r =>
      congrFun hf r
    refine (multilinear_eq_sum_basis b f.toMultilinearMap v).trans
      (Finset.sum_eq_zero fun r _ => ?_)
    rw [show f.toMultilinearMap (fun i => b (r i)) = f (fun i => b (r i)) from rfl, h0 r,
      mul_zero]
  obtain ⟨L, hL⟩ := T.exists_leftInverse_of_injective hT
  have hΦ : Φ = fun y => LinearMap.toContinuousLinearMap L (T (Φ y)) :=
    funext fun y => (LinearMap.congr_fun hL (Φ y)).symm
  rw [hΦ]
  exact (LinearMap.toContinuousLinearMap L).contDiff.comp_contDiffOn
    (contDiffOn_pi.2 fun r => h _)

end FiniteDimAlt

/-! ### Finite-dimensional sc-smooth maps are `C^∞` into every level -/

section Levels

variable {E F : ScBanach} [FiniteDimensional ℝ (E 0)] {U : Set (E 0)} {f : E 0 → F 0}

/-- **A finite-dimensional sc-smooth parametrization is `C^∞` into every level**: for `E₀`
finite-dimensional, `U` an sc-domain and `f : U → F` sc-smooth, `f` takes values in `F_∞`, and
for every `m` the map `f : U → F_m` (read through the identification `E_m = E₀`,
`ScBanach.scIsoConst`) is `C^∞`. -/
theorem contDiffOn_level_of_finiteDim (hU : IsScDomain E U) (hf : IsScSmooth U f) :
    (∀ x ∈ U, ∀ m, f x ∈ range (F.toBase m)) ∧
      ∀ m, ContDiffOn ℝ ∞ (levelMap f m ∘ (E.scIsoConst m).symm) U := by
  have hsymm : ∀ m (x : E 0), E.toBase m ((E.scIsoConst m).symm x) = x := fun m x =>
    (E.scIsoConst m).apply_symm_apply x
  refine ⟨fun x hx m => ⟨levelMap f m ((E.scIsoConst m).symm x), ?_⟩, fun m => ?_⟩
  · rw [(hf 0).isSc0.toBase_levelMap (m := m) (x := (E.scIsoConst m).symm x)
      (by rw [ScBanach.mem_lvlSet, hsymm]; exact hx), hsymm]
  · refine contDiffOn_infty.2 fun k => ?_
    have h := hf.contDiffOn_levels hU m k
    have hg : MapsTo ((E.scIsoConst (m + k)).symm : E 0 → E (m + k)) U (E.lvlSet U (m + k)) :=
      fun x hx => by rw [ScBanach.mem_lvlSet, hsymm]; exact hx
    refine (h.comp (E.scIsoConst (m + k)).symm.contDiff.contDiffOn hg).congr fun x _ => ?_
    simp only [Function.comp_apply]
    congr 1
    apply E.toBase_injective m
    rw [E.toBase_inclK, hsymm, hsymm]

/-- The base level: a finite-dimensional sc-smooth map is `C^∞` on its sc-domain. -/
theorem contDiffOn_of_finiteDim (hU : IsScDomain E U) (hf : IsScSmooth U f) :
    ContDiffOn ℝ ∞ f U := by
  refine ((contDiffOn_level_of_finiteDim hU hf).2 0).congr fun x _ => ?_
  simp only [Function.comp_apply, levelMap_zero]
  exact congrArg f ((E.scIsoConst 0).apply_symm_apply x).symm

/-- The Whitney sum `E¹ ⊕ E^k` of a finite-dimensional sc-Banach space is finite-dimensional. -/
theorem finiteDimensional_whitney (E : ScBanach) [FiniteDimensional ℝ (E 0)] (k : ℕ) :
    FiniteDimensional ℝ ((E.whitney k) 0) := by
  have h1 := E.finiteDimensional_lvl 1
  have h2 : FiniteDimensional ℝ ((E.fiberPow k) 0) :=
    (E.fiberEquivL 0 k).symm.toLinearEquiv.finiteDimensional
  exact inferInstanceAs (FiniteDimensional ℝ (E 1 × (E.fiberPow k) 0))

end Levels

/-! ### Corner coordinates: the affine reading of a corner chart -/

local notation "𝓠" => modelWithCornersEuclideanQuadrant

namespace MPolyfold

universe u

variable {M : Type u} [TopologicalSpace M] [T2Space M] [ParacompactSpace M] {Q : MPolyfold M}
  {n k : ℕ}

namespace CornerCoords

variable (κ : CornerCoords Q n)

/-- The extended Mathlib chart of `κ` is `x ↦ Ψ χ(x) + c` on `s`. -/
theorem extend_eq_toLp_coord {x : M} (hx : x ∈ κ.s) :
    κ.toQuadrantChart.extend (𝓠 n) x = toLp 2 (κ.coord x) := by
  rw [OpenPartialHomeomorph.extend_coe, Function.comp_apply, κ.toQuadrantChart_apply]
  exact quadrant_right_inv fun i => κ.coord_nonneg hx i

/-- On `range I = [0,∞)ⁿ`, the inverse of the extended chart is `y ↦ χ⁻¹(Ψ⁻¹(y − c))`. -/
theorem extend_symm_eq_coordInv {y : EuclideanSpace ℝ (Fin n)} (hy : y ∈ range (𝓠 n)) :
    (κ.toQuadrantChart.extend (𝓠 n)).symm y = κ.coordInv (ofLp y) := by
  rw [OpenPartialHomeomorph.extend_coe_symm, Function.comp_apply, κ.toQuadrantChart_symm_apply]
  congr 2
  exact (𝓠 n).right_inv hy

/-- A point of the target of the extended chart lies over `W ∩ [0,∞)ⁿ`. -/
theorem coord_mem_of_mem_extend_target {y : EuclideanSpace ℝ (Fin n)}
    (hy : y ∈ (κ.toQuadrantChart.extend (𝓠 n)).target) : ofLp y ∈ κ.W ∧ ∀ i, 0 ≤ y i := by
  rw [OpenPartialHomeomorph.extend_target] at hy
  obtain ⟨hy1, q, rfl⟩ := hy
  refine ⟨?_, fun i => q.2 i⟩
  have h := κ.mem_toQuadrantChart_target.1 hy1
  rw [(𝓠 n).left_inv] at h
  exact h

/-- The linear part `Ψ⁻¹ : ℝⁿ → E₀` of the inverse coordinates. -/
def lin : EuclideanSpace ℝ (Fin n) →L[ℝ] κ.χ.model.E 0 :=
  κ.Ψ.symm.toContinuousLinearMap.comp (ofLpCLM n)

lemma lin_apply (v : EuclideanSpace ℝ (Fin n)) : κ.lin v = κ.Ψ.symm (ofLp v) := rfl

/-- The inverse coordinates `y ↦ Ψ⁻¹(y − c)`, an affine map `ℝⁿ → E₀`. -/
def aff (y : EuclideanSpace ℝ (Fin n)) : κ.χ.model.E 0 := κ.Ψ.symm (ofLp y - κ.c)

lemma aff_eq (y : EuclideanSpace ℝ (Fin n)) : κ.aff y = κ.lin y + κ.aff 0 := by
  simp only [aff, lin_apply, WithLp.ofLp_zero, sub_eq_add_neg, zero_add, map_add]

theorem hasFDerivAt_aff (y : EuclideanSpace ℝ (Fin n)) : HasFDerivAt κ.aff κ.lin y := by
  have h := (κ.lin.hasFDerivAt (x := y)).add_const (κ.aff 0)
  exact h.congr_of_eventuallyEq (Eventually.of_forall fun y' => κ.aff_eq y')

theorem aff_extend {x : M} (hx : x ∈ κ.s) :
    κ.aff (κ.toQuadrantChart.extend (𝓠 n) x) = κ.χ x := by
  rw [κ.extend_eq_toLp_coord hx]
  simp only [aff, CornerCoords.coord, add_sub_cancel_right,
    ContinuousLinearEquiv.symm_apply_apply]

/-- At a point `y` of the chart target, `x = κ⁻¹(y)` lies in `s` and `Ψ⁻¹(y − c) = χ(x)`. -/
theorem symm_mem_and_aff_eq {y : EuclideanSpace ℝ (Fin n)}
    (hy : y ∈ (κ.toQuadrantChart.extend (𝓠 n)).target) :
    (κ.toQuadrantChart.extend (𝓠 n)).symm y ∈ κ.s ∧
      κ.aff y = κ.χ ((κ.toQuadrantChart.extend (𝓠 n)).symm y) := by
  have hyr : y ∈ range (𝓠 n) := κ.toQuadrantChart.extend_target_subset_range hy
  obtain ⟨hyW, hy0⟩ := κ.coord_mem_of_mem_extend_target hy
  rw [κ.extend_symm_eq_coordInv hyr]
  exact ⟨κ.coordInv_mem hyW hy0, (κ.apply_coordInv hyW hy0).symm⟩

section Chart

variable {σ : MChart M} (hσ : Q.IsChart σ) {x : M} (hxκ : x ∈ κ.s) (hxσ : x ∈ σ.source)
  {z : κ.χ.model.E 1} (hz : κ.χ.model.E.toBase 1 z = κ.χ x)
include hσ hxκ hxσ hz

/-- **A chart of `Q` read in the corner coordinates `κ` is differentiable**, with derivative
`D(σ ∘ χ⁻¹)(z) ∘ Ψ⁻¹` within `[0,∞)ⁿ` (`transDeriv`; the case of a sub-M-polyfold is
`hasFDerivWithinAt_incl`). -/
theorem hasFDerivWithinAt_chart :
    HasFDerivWithinAt ((fun b => σ b) ∘ (κ.toQuadrantChart.extend (𝓠 n)).symm)
      ((transDeriv κ.isCornerChart σ z).comp κ.lin) (range (𝓠 n))
      (κ.toQuadrantChart.extend (𝓠 n) x) := by
  set e := κ.toQuadrantChart
  have hxe : x ∈ e.source := hxκ
  set T := (e.extend (𝓠 n)).target ∩ (e.extend (𝓠 n)).symm ⁻¹' σ.source
  have hT : T ∈ 𝓝[range (𝓠 n)] (e.extend (𝓠 n) x) := by
    refine inter_mem (e.extend_target_mem_nhdsWithin hxe) (nhdsWithin_le_nhds ?_)
    refine (e.continuousAt_extend_symm hxe).preimage_mem_nhds (σ.isOpen_source.mem_nhds ?_)
    rw [e.extend_left_inv hxe]; exact hxσ
  have hmaps : MapsTo κ.aff T (κ.χ.overlap σ) := fun y hy => by
    obtain ⟨h1, h3⟩ := κ.symm_mem_and_aff_eq hy.1
    rw [h3]; exact κ.χ.mem_overlap σ (κ.s_subset h1) hy.2
  have hF := hasFDerivWithinAt_transition κ.isCornerChart κ.isChart hσ (κ.s_subset hxκ) hxσ hz
  rw [← κ.aff_extend hxκ] at hF
  have h := hF.comp (e.extend (𝓠 n) x) (κ.hasFDerivAt_aff _).hasFDerivWithinAt hmaps
  refine (HasFDerivWithinAt.congr' h (fun y hy => ?_) ?_).mono_of_mem_nhdsWithin hT
  · obtain ⟨h1, h3⟩ := κ.symm_mem_and_aff_eq hy.1
    simp only [Function.comp_apply]
    rw [h3, κ.χ.transition_apply σ (κ.s_subset h1)]
  · exact ⟨(e.extend (𝓠 n)).map_source (by rwa [e.extend_source]),
      by rw [mem_preimage, e.extend_left_inv hxe]; exact hxσ⟩

end Chart

end CornerCoords

/-! ### Tangent vectors in a corner chart -/

section CornerFiber

/-- **In a corner chart, the tangent map of a chart change is `transDeriv`**: for `α ∈ T_xQ`,
the vector of `α` in a chart `σ` is `D(σ ∘ χ⁻¹)(χ(x))` of its vector in the corner chart `χ`. -/
theorem tangentChartMap_snd_eq_transDeriv {χ : MChart M} (hc : χ.IsCornerChart)
    (hχ : Q.IsChart χ) {σ : MChart M} (hσ : Q.IsChart σ) {x : Q.Level 1}
    (hx : Q.levelVal 1 x ∈ χ.source) (hx' : Q.levelVal 1 x ∈ σ.source) (α : Q.tangentFiber x) :
    (tangentChartMap hσ α.1).2 =
      transDeriv hc σ (levelLift χ 1 (Q.levelVal 1 x)) (tangentChartMap hχ α.1).2 := by
  have hα := mem_tangentChartSet_of_mem_fiber hx α.2
  have hα' := mem_tangentChartSet_of_mem_fiber hx' α.2
  rw [tangentChartMap_eq_transition hχ hσ hα hα',
    retractTangentMap_apply (hχ.compatible hσ (P := Q)).1 (overlapRet hc σ)
      (overlapRet_retract hc σ) (tangentChartMap_mem_overlap hχ hα hα'),
    tangentChartMap_fst_of_mem_fiber hχ hx α.2]
  rfl

/-- In a corner chart every vector of `E₀` is tangent: `T_{χ(x)}O = E₀`. -/
theorem mem_tangentFiberModel_of_isCornerChart {χ : MChart M} (hc : χ.IsCornerChart)
    (hχ : Q.IsChart χ) {x : Q.Level 1} (hx : Q.levelVal 1 x ∈ χ.source) (v : χ.model.E 0) :
    v ∈ tangentFiberModel hχ hx := by
  rw [← SetLike.mem_coe, coe_tangentFiberModel, tangentSpace_relOpen hc.isRelOpenInQuadrant]
  · exact mem_univ v
  · rw [Q.toBase_levelLift hχ hx (levelVal_mem x)]; exact χ.mapsTo_model _ hx

namespace CornerCoords

variable (κ : CornerCoords Q n)

/-- **The tangent vector at `x` with corner coordinates `v ∈ ℝⁿ`**: `(Tχ)⁻¹(χ(x), Ψ⁻¹v)`. -/
def fiberMap {x : Q.Level 1} (hx : Q.levelVal 1 x ∈ κ.χ.source) :
    EuclideanSpace ℝ (Fin n) →ₗ[ℝ] Q.tangentFiber x :=
  (tangentFiberLinearEquiv κ.isChart hx).symm.toLinearMap ∘ₗ
    LinearMap.codRestrict (tangentFiberModel κ.isChart hx)
      (κ.lin : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] κ.χ.model.E 0)
      fun _ => mem_tangentFiberModel_of_isCornerChart κ.isCornerChart κ.isChart hx _

theorem tangentChartMap_fiberMap {x : Q.Level 1} (hx : Q.levelVal 1 x ∈ κ.χ.source)
    (v : EuclideanSpace ℝ (Fin n)) :
    (tangentChartMap κ.isChart (κ.fiberMap hx v).1).2 = κ.lin v := by
  rw [← coe_tangentFiberLinearEquiv_apply κ.isChart hx]
  simp [fiberMap]

/-- The lift `E₀ → E₁` (the levels of the model of a corner chart are all `E₀`). -/
def liftOne : κ.χ.model.E 0 →L[ℝ] κ.χ.model.E 1 :=
  haveI := κ.isCornerChart.finiteDimensional
  ((κ.χ.model.E.scIsoConst 1).symm : κ.χ.model.E 0 →L[ℝ] κ.χ.model.E 1)

@[simp] lemma toBase_liftOne (u : κ.χ.model.E 0) : κ.χ.model.E.toBase 1 (κ.liftOne u) = u := by
  have := κ.isCornerChart.finiteDimensional
  exact (κ.χ.model.E.scIsoConst 1).apply_symm_apply u

lemma eq_liftOne {w : κ.χ.model.E 1} {u : κ.χ.model.E 0} (h : κ.χ.model.E.toBase 1 w = u) :
    w = κ.liftOne u :=
  κ.χ.model.E.toBase_injective 1 (by rw [h, toBase_liftOne])

end CornerCoords

end CornerFiber

/-! ### The level section `Q → Q¹` of a corner M-polyfold -/

namespace HasCornerStructureOfDim

variable (hcs : Q.HasCornerStructureOfDim n)

include hcs in
/-- **Every point of an M-polyfold with a corner structure is smooth** (the models are
finite-dimensional, `IsCornerChart.mem_smooth`). -/
theorem mem_smoothSet (x : M) : x ∈ Q.smoothSet := by
  obtain ⟨χ, hχ, hx, hc, -⟩ := hcs x
  exact (Q.mem_smoothSet_iff_of_isChart hχ hx).2 (hc.mem_smooth _)

/-- `x ∈ Q¹` for every `x`. -/
def levelOne (x : M) : Q.Level 1 := Q.levelMk 1 x (mem_iInter.1 (hcs.mem_smoothSet x) 1)

@[simp] lemma levelVal_levelOne (x : M) : Q.levelVal 1 (hcs.levelOne x) = x := rfl

lemma levelOne_levelVal (x : Q.Level 1) : hcs.levelOne (Q.levelVal 1 x) = x := level_ext rfl

/-- **`Q = Q¹`: the map `x ↦ x ∈ Q¹` is sc-smooth** (corner charts are sc⁺-retracts,
Remark 4.1.3; `isScSmoothMap_toLevelOne_of_cover`). -/
theorem isScSmoothMap_levelOne : Q.IsScSmoothMap Q.shift hcs.levelOne := by
  rcases isEmpty_or_nonempty M with hM | ⟨⟨x₀⟩⟩
  · exact IsScSmoothOn.of_exists_charts isOpen_univ (fun x _ => isEmptyElim x)
      fun x _ => isEmptyElim x
  · have h := (Q.isScSmoothMap_toLevelOne_of_cover (hcs.levelOne x₀) fun x => by
      obtain ⟨χ, hχ, hx, hc, -⟩ := hcs x
      exact ⟨χ, hχ, hx, hc.isScPlusRetract⟩).2
    rwa [show Q.toLevelOne (hcs.levelOne x₀) = hcs.levelOne from
      funext fun x => Q.toLevelOne_levelVal _ (hcs.levelOne x)] at h

/-- `T(Q¹) → TQ` undoes `T(x ↦ x ∈ Q¹)`. -/
theorem tangentLower_tangentMap_levelOne (β : Q.TangentSpace) :
    tangentLower (tangentMap hcs.isScSmoothMap_levelOne β) = β := by
  rw [← tangentMap_levelVal_one, ← Function.comp_apply (f := tangentMap _),
    ← tangentMap_comp]
  exact congrFun (tangentMap_id (P := Q)) β

/-- **The pull-back of `ι^*ω` along `x ↦ x ∈ Q¹` is `ω`**. -/
theorem formPullback_levelOne_formLower
    (η : ∀ x : Q.Level 1, Q.tangentFiber x [⋀^Fin k]→ₗ[ℝ] ℝ) :
    MPolyfold.formPullback hcs.isScSmoothMap_levelOne (formLower η) = η := by
  funext x
  ext α
  rw [formPullback_apply, formLower_apply]
  refine altFamily_congr η (hcs.levelOne_levelVal x) _ _ fun i => ?_
  rw [coe_lowerFiberCLM_apply, coe_tangentFiberMap_apply, tangentLower_tangentMap_levelOne]

/-- The chosen corner coordinates at `x` (those of the chart `chartAt x` of
`cornerChartedSpace`). -/
def coords (x : M) : CornerCoords Q n := (hcs.exists_cornerCoords x).choose

lemma mem_coords (x : M) : x ∈ (hcs.coords x).s := (hcs.exists_cornerCoords x).choose_spec

lemma levelOne_mem_coords (x : M) :
    Q.levelVal 1 (hcs.levelOne x) ∈ (hcs.coords x).χ.source :=
  (hcs.coords x).s_subset (hcs.mem_coords x)

end HasCornerStructureOfDim

/-! ### The reading of a chart form along the corner coordinates -/

/-- The local representative `ω_φ` extended to the domain of the chosen retraction,
`ω_φ ∘ ⊕ₖ Tr` (so that `d(ω_φ) = ambientD U (ω_φ ∘ ⊕ₖ Tr)`, `chartD`). -/
def chartFormExt {φ : MChart M} (hφ : Q.IsChart φ)
    (η : ∀ x : Q.Level 1, Q.tangentFiber x [⋀^Fin k]→ₗ[ℝ] ℝ) : (φ.model.E.whitney k) 0 → ℝ :=
  chartForm hφ η ∘ (chartRetraction φ).whitney k

/-- `ω_φ ∘ ⊕ₖ Tr` is sc-smooth on `⊕ₖ TU` for an sc-form `ω`. -/
theorem isScSmooth_chartFormExt {φ : MChart M} (hφ : Q.IsChart φ)
    {η : ∀ x : Q.Level 1, Q.tangentFiber x [⋀^Fin k]→ₗ[ℝ] ℝ} (hη : η ∈ Q.scForms k) :
    IsScSmooth (F := ScBanach.const ℝ) (φ.model.E.whitneySet k (chartRetraction φ).U)
      (chartFormExt hφ η) :=
  (mem_scForms.1 hη hφ).comp_isScSmooth ((chartRetraction φ).whitney k)
    (by rw [ScRetraction.whitney_retract, chartRetraction_retract])

namespace CornerCoords

variable (κ : CornerCoords Q n)

/-- The point `(Ψ⁻¹(y − c), Ψ⁻¹w₁, …, Ψ⁻¹w_k)` of the Whitney sum `E¹ ⊕ E^k` of the model. -/
def whitneyPt (w : Fin k → EuclideanSpace ℝ (Fin n)) (y : EuclideanSpace ℝ (Fin n)) :
    (κ.χ.model.E.whitney k) 0 :=
  ScBanach.whitneyMk (κ.liftOne (κ.aff y)) fun i => κ.lin (w i)

/-- The derivative of `whitneyPt w`: `u ↦ (Ψ⁻¹u, 0)`. -/
def whitneyPtDeriv : EuclideanSpace ℝ (Fin n) →L[ℝ] (κ.χ.model.E.whitney k) 0 :=
  (κ.liftOne.comp κ.lin).prod 0

lemma whitneyPtDeriv_apply (u : EuclideanSpace ℝ (Fin n)) :
    (κ.whitneyPtDeriv u : (κ.χ.model.E.whitney k) 0) =
      ScBanach.whitneyMk (κ.liftOne (κ.lin u)) 0 :=
  Prod.ext rfl (map_zero _).symm

lemma whitneyPt_eq (w : Fin k → EuclideanSpace ℝ (Fin n)) (y : EuclideanSpace ℝ (Fin n)) :
    κ.whitneyPt w y = κ.whitneyPtDeriv y + κ.whitneyPt w 0 := by
  refine Prod.ext ?_ (zero_add _).symm
  change κ.liftOne (κ.aff y) = κ.liftOne (κ.lin y) + κ.liftOne (κ.aff 0)
  rw [κ.aff_eq y, map_add]

theorem hasFDerivAt_whitneyPt (w : Fin k → EuclideanSpace ℝ (Fin n))
    (y : EuclideanSpace ℝ (Fin n)) : HasFDerivAt (κ.whitneyPt w) κ.whitneyPtDeriv y :=
  (κ.whitneyPtDeriv.hasFDerivAt.add_const _).congr_of_eventuallyEq
    (Eventually.of_forall fun y' => κ.whitneyPt_eq w y')

theorem contDiff_whitneyPt (w : Fin k → EuclideanSpace ℝ (Fin n)) :
    ContDiff ℝ ∞ (κ.whitneyPt w) := by
  rw [show κ.whitneyPt w = fun y => κ.whitneyPtDeriv y + κ.whitneyPt w 0 from
    funext (κ.whitneyPt_eq w)]
  exact κ.whitneyPtDeriv.contDiff.add contDiff_const

variable {κ} {y : EuclideanSpace ℝ (Fin n)} (hy : y ∈ (κ.toQuadrantChart.extend (𝓠 n)).target)
include hy

lemma liftOne_aff_mem :
    κ.liftOne (κ.aff y) ∈ κ.χ.model.E.lvlSet κ.χ.model.O 1 := by
  obtain ⟨hx', haff⟩ := κ.symm_mem_and_aff_eq hy
  rw [ScBanach.mem_lvlSet, κ.toBase_liftOne, haff]
  exact κ.χ.mapsTo_model _ (κ.s_subset hx')

/-- Over the chart target, `whitneyPt` lies in `⊕ₖ TO` (all vectors are tangent in a corner
chart). -/
theorem whitneyPt_mem (w : Fin k → EuclideanSpace ℝ (Fin n)) :
    κ.whitneyPt w y ∈ retractWhitney κ.χ.model.E κ.χ.model.C κ.χ.model.O k := by
  have h1 := liftOne_aff_mem hy
  refine mem_retractWhitney_mk.2 ⟨h1, fun i => ?_⟩
  change κ.lin (w i) ∈ tangentSpace κ.χ.model.E κ.χ.model.C κ.χ.model.O (κ.liftOne (κ.aff y))
  rw [tangentSpace_relOpen κ.isCornerChart.isRelOpenInQuadrant h1]
  exact mem_univ _

theorem whitneyPt_mem_whitneySet (w : Fin k → EuclideanSpace ℝ (Fin n)) :
    κ.whitneyPt w y ∈ κ.χ.model.E.whitneySet k (chartRetraction κ.χ).U :=
  ScBanach.mem_whitneySet.2 (κ.χ.model.E.lvlSet_mono
    ((chartRetraction_retract κ.χ).symm ▸ (chartRetraction κ.χ).retract_subset) 1
    (liftOne_aff_mem hy))

/-- Over the chart target, `ω_φ ∘ ⊕ₖ Tr = ω_φ` at `whitneyPt`. -/
theorem chartFormExt_whitneyPt (η : ∀ x : Q.Level 1, Q.tangentFiber x [⋀^Fin k]→ₗ[ℝ] ℝ)
    (w : Fin k → EuclideanSpace ℝ (Fin n)) :
    chartFormExt κ.isChart η (κ.whitneyPt w y) = chartForm κ.isChart η (κ.whitneyPt w y) := by
  rw [chartFormExt, Function.comp_apply, ScRetraction.whitney_apply,
    (chartRetraction κ.χ).whitneyMap_eq_self
      (by rw [chartRetraction_retract]; exact whitneyPt_mem hy w)]

omit hy in
/-- A level-`1` point of `E¹ ⊕ E^k` over `whitneyPt`: `(a, Ψ⁻¹w₁, …, Ψ⁻¹w_k)` with all entries
lifted one level. -/
def whitneyPtOne (a : κ.χ.model.E.shift 1) (w : Fin k → EuclideanSpace ℝ (Fin n)) :
    (κ.χ.model.E.whitney k) 1 :=
  (a, κ.χ.model.E.fiberPackL 1 k fun j => κ.liftOne (κ.lin (w j)))

omit hy in
lemma toBase_whitneyPtOne {a : κ.χ.model.E.shift 1}
    (ha : κ.χ.model.E.shift.toBase 1 a = κ.liftOne (κ.aff y))
    (w : Fin k → EuclideanSpace ℝ (Fin n)) :
    (κ.χ.model.E.whitney k).toBase 1 (κ.whitneyPtOne a w) = κ.whitneyPt w y := by
  rw [whitneyPtOne, whitney_toBase_mk, ha, whitneyPt]
  simp only [toBase_liftOne]

/-- The coordinates `u ↦ Ψ u` of `E₀`, with values in `ℝⁿ`. -/
def coordLin : κ.χ.model.E 0 →L[ℝ] EuclideanSpace ℝ (Fin n) :=
  (PiLp.continuousLinearEquiv 2 ℝ fun _ : Fin n => ℝ).symm.toContinuousLinearMap.comp
    κ.Ψ.toContinuousLinearMap

omit hy in
lemma lin_coordLin (u : κ.χ.model.E 0) : κ.lin (κ.coordLin u) = u := by
  change κ.Ψ.symm (ofLp (toLp 2 (κ.Ψ u))) = u
  rw [WithLp.ofLp_toLp, ContinuousLinearEquiv.symm_apply_apply]

omit hy in
theorem hasFDerivAt_coord (u : κ.χ.model.E 0) :
    HasFDerivAt (fun u => toLp 2 (κ.Ψ u + κ.c)) κ.coordLin u := by
  refine (κ.coordLin.hasFDerivAt.add_const (toLp 2 κ.c)).congr_of_eventuallyEq
    (Eventually.of_forall fun u' => ?_)
  simp [coordLin]

end CornerCoords

/-! ### Sc-forms on a corner M-polyfold as Mathlib forms -/

section MathlibForm

variable (hcs : Q.HasCornerStructureOfDim n) [inst : ChartedSpace (EuclideanQuadrant n) M]

/-- **An sc-form on a finite-dimensional corner M-polyfold, as a Mathlib form**: at `x`, the
alternating form `v ↦ η(x)((Tχ)⁻¹(χ(x), Ψ⁻¹v₁), …)` on `T_xM = ℝⁿ`, read in the corner
coordinates `κ = hcs.coords x` of Mathlib's chart at `x` (`cornerChartedSpace`). -/
def cornerForm (η : ∀ x : Q.Level 1, Q.tangentFiber x [⋀^Fin k]→ₗ[ℝ] ℝ) :
    ManifoldForm (𝓠 n) M k := fun x =>
  altCont ((η (hcs.levelOne x)).compLinearMap
    ((hcs.coords x).fiberMap (hcs.levelOne_mem_coords x)))

lemma cornerForm_apply (η : ∀ x : Q.Level 1, Q.tangentFiber x [⋀^Fin k]→ₗ[ℝ] ℝ) (x : M)
    (v : Fin k → EuclideanSpace ℝ (Fin n)) :
    cornerForm hcs η x v =
      η (hcs.levelOne x) fun i => (hcs.coords x).fiberMap (hcs.levelOne_mem_coords x) (v i) :=
  rfl

lemma cornerForm_add (η τ : ∀ x : Q.Level 1, Q.tangentFiber x [⋀^Fin k]→ₗ[ℝ] ℝ) :
    cornerForm hcs (η + τ) = cornerForm hcs η + cornerForm hcs τ := by
  funext x; ext v; rfl

lemma cornerForm_smul (c : ℝ) (η : ∀ x : Q.Level 1, Q.tangentFiber x [⋀^Fin k]→ₗ[ℝ] ℝ) :
    cornerForm hcs (c • η) = c • cornerForm hcs η := by
  funext x; ext v; rfl

variable {hcs} (hch : inst = Q.cornerChartedSpace hcs)
include hch

omit inst hch in
/-- **The Mathlib chart change between corner coordinates is `D(χ ∘ χ'⁻¹)`**:
`D(κ ∘ κ'⁻¹)(κ'(x)) = Ψ ∘ D(χ ∘ χ'⁻¹)(χ'(x)) ∘ Ψ'⁻¹`. -/
theorem chartChangeDeriv_cornerCoords (κ κ' : CornerCoords Q n) {x : M} (hx : x ∈ κ.s)
    (hx' : x ∈ κ'.s) {z' : κ'.χ.model.E 1} (hz' : κ'.χ.model.E.toBase 1 z' = κ'.χ x) :
    chartChangeDeriv (𝓠 n) κ'.toQuadrantChart κ.toQuadrantChart x =
      κ.coordLin.comp ((transDeriv κ'.isCornerChart κ.χ z').comp κ'.lin) := by
  set e' := κ'.toQuadrantChart
  have hxe' : x ∈ e'.source := hx'
  have hG := κ'.hasFDerivWithinAt_chart κ.isChart hx' (κ.s_subset hx) hz'
  have h := (κ.hasFDerivAt_coord _).comp_hasFDerivWithinAt (e'.extend (𝓠 n) x) hG
  set T := (e'.extend (𝓠 n)).target ∩ (e'.extend (𝓠 n)).symm ⁻¹' κ.s
  have hT : T ∈ 𝓝[range (𝓠 n)] (e'.extend (𝓠 n) x) := by
    refine inter_mem (e'.extend_target_mem_nhdsWithin hxe') (nhdsWithin_le_nhds ?_)
    refine (e'.continuousAt_extend_symm hxe').preimage_mem_nhds (κ.isOpen_s.mem_nhds ?_)
    rw [e'.extend_left_inv hxe']; exact hx
  have heq : ∀ y ∈ T, (𝓠 n).extendCoordChange e' κ.toQuadrantChart y =
      ((fun u => toLp 2 (κ.Ψ u + κ.c)) ∘ ((fun b => κ.χ b) ∘ (e'.extend (𝓠 n)).symm)) y :=
    fun y hy => by
    simp only [ModelWithCorners.extendCoordChange, PartialEquiv.coe_trans, Function.comp_apply]
    rw [κ.extend_eq_toLp_coord hy.2]; rfl
  have hxT : e'.extend (𝓠 n) x ∈ T :=
    ⟨(e'.extend (𝓠 n)).map_source (by rwa [e'.extend_source]),
      by rw [mem_preimage, e'.extend_left_inv hxe']; exact hx⟩
  refine (h.congr_of_eventuallyEq (Filter.mem_of_superset hT heq) (heq _ hxT)).fderivWithin ?_
  rw [OpenPartialHomeomorph.extend_coe]
  exact (𝓠 n).uniqueDiffWithinAt_image

/-- Inverting `chartChangeDeriv_cornerCoords`: `D(χ ∘ χ'⁻¹) Ψ'⁻¹ D(κ' ∘ κ⁻¹) v = Ψ⁻¹ v`. -/
theorem transDeriv_lin_chartChangeDeriv (κ κ' : CornerCoords Q n) {x : M} (hx : x ∈ κ.s)
    (hx' : x ∈ κ'.s) {z' : κ'.χ.model.E 1} (hz' : κ'.χ.model.E.toBase 1 z' = κ'.χ x)
    (v : EuclideanSpace ℝ (Fin n)) :
    transDeriv κ'.isCornerChart κ.χ z'
        (κ'.lin (chartChangeDeriv (𝓠 n) κ.toQuadrantChart κ'.toQuadrantChart x v)) = κ.lin v := by
  have := isManifold_of_eq hcs hch
  have hm := mem_maximalAtlas_of_eq hcs hch
  have h := chartChangeDeriv_comp_apply (I := 𝓠 n) (n := ∞) (by simp) (hm κ) (hm κ') (hm κ)
    hx hx' hx v
  rw [chartChangeDeriv_self hx, chartChangeDeriv_cornerCoords κ κ' hx hx' hz'] at h
  have h' := congrArg κ.lin h
  rwa [ContinuousLinearMap.comp_apply, κ.lin_coordLin] at h'

/-- **The tangent vector with coordinates `v` does not depend on the corner coordinates**, up to
Mathlib's chart change. -/
theorem fiberMap_chartChange (κ κ' : CornerCoords Q n) {x : M} (hx : x ∈ κ.s) (hx' : x ∈ κ'.s)
    (v : EuclideanSpace ℝ (Fin n)) :
    κ'.fiberMap (x := hcs.levelOne x) (κ'.s_subset hx')
        (chartChangeDeriv (𝓠 n) κ.toQuadrantChart κ'.toQuadrantChart x v) =
      κ.fiberMap (x := hcs.levelOne x) (κ.s_subset hx) v := by
  have hxχ : Q.levelVal 1 (hcs.levelOne x) ∈ κ.χ.source := κ.s_subset hx
  have hxχ' : Q.levelVal 1 (hcs.levelOne x) ∈ κ'.χ.source := κ'.s_subset hx'
  apply (tangentFiberLinearEquiv κ.isChart hxχ).injective
  apply Subtype.ext
  rw [coe_tangentFiberLinearEquiv_apply, coe_tangentFiberLinearEquiv_apply,
    κ.tangentChartMap_fiberMap,
    tangentChartMap_snd_eq_transDeriv κ'.isCornerChart κ'.isChart κ.isChart hxχ' hxχ,
    κ'.tangentChartMap_fiberMap]
  exact transDeriv_lin_chartChangeDeriv hch κ κ' hx hx'
    (Q.toBase_levelLift κ'.isChart hxχ' (levelVal_mem (hcs.levelOne x))) v

/-- **The expression of `cornerForm η` in the Mathlib chart of corner coordinates `κ`**. -/
theorem chartForm_cornerForm (κ : CornerCoords Q n)
    (η : ∀ x : Q.Level 1, Q.tangentFiber x [⋀^Fin k]→ₗ[ℝ] ℝ) {y : EuclideanSpace ℝ (Fin n)}
    (hy : y ∈ (κ.toQuadrantChart.extend (𝓠 n)).target) (w : Fin k → EuclideanSpace ℝ (Fin n)) :
    ManifoldForm.chartForm (𝓠 n) κ.toQuadrantChart (cornerForm hcs η) y w =
      chartForm κ.isChart η (κ.whitneyPt w y) := by
  obtain ⟨hx', haff⟩ := κ.symm_mem_and_aff_eq hy
  set x' := (κ.toQuadrantChart.extend (𝓠 n)).symm y
  change η (hcs.levelOne x') (fun i => (hcs.coords x').fiberMap (hcs.levelOne_mem_coords x')
    (chartChangeDeriv (𝓠 n) κ.toQuadrantChart (chartAt (EuclideanQuadrant n) x') x' (w i))) = _
  rw [chartAt_eq_of_eq hcs hch x']
  have hfib : ∀ i, (hcs.coords x').fiberMap (hcs.levelOne_mem_coords x')
      (chartChangeDeriv (𝓠 n) κ.toQuadrantChart (hcs.coords x').toQuadrantChart x' (w i)) =
      κ.fiberMap (x := hcs.levelOne x') (κ.s_subset hx') (w i) := fun i =>
    fiberMap_chartChange hch κ (hcs.coords x') hx' (hcs.mem_coords x') (w i)
  refine ((chartForm_eq κ.isChart η (x := hcs.levelOne x') (κ.s_subset hx') _ ?_
    fun i => ?_).trans
    (congrArg _ (funext hfib)).symm).symm
  · change κ.liftOne (κ.aff y) = _
    rw [haff]
    exact (κ.eq_liftOne (Q.toBase_levelLift κ.isChart (κ.s_subset hx')
      (levelVal_mem (hcs.levelOne x')))).symm
  · rw [CornerCoords.whitneyPt, ScBanach.whitneyVec_mk, κ.tangentChartMap_fiberMap]

/-- **`cornerForm η` is `C^∞` in the Mathlib chart of corner coordinates**: its evaluations are
`ω_φ ∘ ⊕ₖ Tr` (sc-smooth on a finite-dimensional space, hence `C^∞`,
`contDiffOn_of_finiteDim`) composed with the affine map `whitneyPt`. -/
theorem contDiffOn_chartForm_cornerForm (κ : CornerCoords Q n)
    {η : ∀ x : Q.Level 1, Q.tangentFiber x [⋀^Fin k]→ₗ[ℝ] ℝ} (hη : η ∈ Q.scForms k) :
    ContDiffOn ℝ ∞ (ManifoldForm.chartForm (𝓠 n) κ.toQuadrantChart (cornerForm hcs η))
      (κ.toQuadrantChart.extend (𝓠 n)).target := by
  refine contDiffOn_alt_of_apply fun w => ?_
  have := κ.isCornerChart.finiteDimensional
  have := finiteDimensional_whitney κ.χ.model.E k
  have hΩ := contDiffOn_of_finiteDim ((chartRetraction κ.χ).whitney k).isScDomain
    (isScSmooth_chartFormExt κ.isChart hη)
  refine (hΩ.comp (κ.contDiff_whitneyPt w).contDiffOn fun y hy =>
    CornerCoords.whitneyPt_mem_whitneySet hy w).congr fun y hy => ?_
  rw [chartForm_cornerForm hch κ η hy w, Function.comp_apply,
    CornerCoords.chartFormExt_whitneyPt hy]

/-- **`cornerForm η` is a `C^∞` form** on the Mathlib manifold `M`. -/
theorem contMDiffForm_cornerForm {η : ∀ x : Q.Level 1, Q.tangentFiber x [⋀^Fin k]→ₗ[ℝ] ℝ}
    (hη : η ∈ Q.scForms k) : ManifoldForm.ContMDiffForm (𝓠 n) ∞ (cornerForm hcs η) := fun x => by
  rw [extChartAt, chartAt_eq_of_eq hcs hch x]
  exact contDiffOn_chartForm_cornerForm hch _ hη

/-- The derivative of an evaluation of `cornerForm η` in corner coordinates: the sc-derivative of
`ω_φ ∘ ⊕ₖ Tr` (finite dimensions, `IsSc1.hasFDerivWithinAt_of_finiteDimensional`) composed with
the derivative of `whitneyPt`. -/
theorem hasFDerivWithinAt_chartForm_cornerForm (κ : CornerCoords Q n)
    {η : ∀ x : Q.Level 1, Q.tangentFiber x [⋀^Fin k]→ₗ[ℝ] ℝ} (hη : η ∈ Q.scForms k)
    {x : M} (hx : x ∈ κ.s) (w : Fin k → EuclideanSpace ℝ (Fin n))
    {p : (κ.χ.model.E.whitney k) 1}
    (hp : (κ.χ.model.E.whitney k).toBase 1 p = κ.whitneyPt w (κ.toQuadrantChart.extend (𝓠 n) x)) :
    HasFDerivWithinAt
      (fun y => ManifoldForm.chartForm (𝓠 n) κ.toQuadrantChart (cornerForm hcs η) y w)
      ((scDeriv (F := ScBanach.const ℝ) (κ.χ.model.E.whitneySet k (chartRetraction κ.χ).U)
        (chartFormExt κ.isChart η) p).comp κ.whitneyPtDeriv) (range (𝓠 n))
      (κ.toQuadrantChart.extend (𝓠 n) x) := by
  have := κ.isCornerChart.finiteDimensional
  have := finiteDimensional_whitney κ.χ.model.E k
  set e := κ.toQuadrantChart
  have hxt : e.extend (𝓠 n) x ∈ (e.extend (𝓠 n)).target :=
    (e.extend (𝓠 n)).map_source (by rw [OpenPartialHomeomorph.extend_source]; exact hx)
  have hD := (isScSmooth_chartFormExt κ.isChart hη).isSc1.hasFDerivWithinAt_of_finiteDimensional
    (x := p) (by rw [hp]; exact CornerCoords.whitneyPt_mem_whitneySet hxt w)
  rw [hp] at hD
  have h := hD.comp (e.extend (𝓠 n) x) (κ.hasFDerivAt_whitneyPt w _).hasFDerivWithinAt
    (fun y hy => CornerCoords.whitneyPt_mem_whitneySet hy w)
  refine (h.congr' (fun y hy => ?_) hxt).mono_of_mem_nhdsWithin
    (e.extend_target_mem_nhdsWithin hx)
  rw [chartForm_cornerForm hch κ η hy w, Function.comp_apply,
    CornerCoords.chartFormExt_whitneyPt hy]

/-- **`d(cornerForm η)` in corner coordinates**, through the local derivative of `ω_φ ∘ ⊕ₖ Tr`
at points `pᵢ` of `E¹ ⊕ E^k` over the `whitneyPt` of the vectors without the `i`-th. -/
theorem extDeriv_cornerForm_apply {η : ∀ x : Q.Level 1, Q.tangentFiber x [⋀^Fin k]→ₗ[ℝ] ℝ}
    (hη : η ∈ Q.scForms k) (x : M) (v : Fin (k + 1) → EuclideanSpace ℝ (Fin n))
    (p : Fin (k + 1) → ((hcs.coords x).χ.model.E.whitney k) 1)
    (hp : ∀ i, ((hcs.coords x).χ.model.E.whitney k).toBase 1 (p i) =
      (hcs.coords x).whitneyPt (i.removeNth v)
        ((hcs.coords x).toQuadrantChart.extend (𝓠 n) x)) :
    ManifoldForm.extDeriv (cornerForm hcs η) x v = ∑ i : Fin (k + 1), (-1 : ℝ) ^ i.val *
      scDeriv (F := ScBanach.const ℝ)
        ((hcs.coords x).χ.model.E.whitneySet k (chartRetraction (hcs.coords x).χ).U)
        (chartFormExt (hcs.coords x).isChart η) (p i) ((hcs.coords x).whitneyPtDeriv (v i)) := by
  set κ := hcs.coords x
  have hxκ : x ∈ κ.s := hcs.mem_coords x
  set e := κ.toQuadrantChart
  have hxt : e.extend (𝓠 n) x ∈ (e.extend (𝓠 n)).target :=
    (e.extend (𝓠 n)).map_source (by rw [OpenPartialHomeomorph.extend_source]; exact hxκ)
  have hdiff : DifferentiableWithinAt ℝ (ManifoldForm.chartForm (𝓠 n) e (cornerForm hcs η))
      (range (𝓠 n)) (e.extend (𝓠 n) x) :=
    (((contDiffOn_chartForm_cornerForm hch κ hη) _ hxt).differentiableWithinAt
      (by simp)).mono_of_mem_nhdsWithin (e.extend_target_mem_nhdsWithin hxκ)
  have huniq : UniqueDiffWithinAt ℝ (range (𝓠 n)) (e.extend (𝓠 n) x) := by
    rw [OpenPartialHomeomorph.extend_coe]; exact (𝓠 n).uniqueDiffWithinAt_image
  rw [ManifoldForm.extDeriv_apply, extChartAt, chartAt_eq_of_eq hcs hch x]
  change extDerivWithin (ManifoldForm.chartForm (𝓠 n) e (cornerForm hcs η)) (range (𝓠 n))
    (e.extend (𝓠 n) x) v = _
  rw [extDerivWithin_apply hdiff huniq]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [(hasFDerivWithinAt_chartForm_cornerForm hch κ hη hxκ (i.removeNth v) (hp i)).fderivWithin
    huniq]
  simp
  rfl

omit inst hch in
/-- The level-`2` point of the level chart over `x`: its image in `E₁` is `χ(x)`. -/
theorem toBase_levelLift_levelChart (x : M) :
    (hcs.coords x).χ.model.E.shift.toBase 1
        (levelLift (levelChart (hcs.coords x).isChart (hcs.levelOne x)) 1 (hcs.levelOne x)) =
      (hcs.coords x).liftOne ((hcs.coords x).aff
        ((hcs.coords x).toQuadrantChart.extend (𝓠 n) x)) := by
  have hxχ := hcs.levelOne_mem_coords x
  rw [(hcs.coords x).aff_extend (hcs.mem_coords x)]
  have h1 := Q.shift.toBase_levelLift (Q.shift_isChart (hcs.coords x).isChart (hcs.levelOne x))
    (x := hcs.levelOne x) hxχ ((mem_shift_levelSet_iff _).2 (mem_iInter.1 (hcs.mem_smoothSet x) 2))
  rw [levelChart_apply] at h1
  exact h1.trans ((hcs.coords x).eq_liftOne
    (Q.toBase_levelLift (hcs.coords x).isChart hxχ (levelVal_mem (hcs.levelOne x))))

omit hch in
/-- **`(j^*dη)_M` in corner coordinates**: by `extD_apply` in the corner chart, the local
exterior derivative of `η_φ` (`ambientD`) at the level-`1` vectors `Ψ⁻¹vᵢ`. -/
theorem cornerForm_formPullback_extD_apply
    {η : ∀ x : Q.Level 1, Q.tangentFiber x [⋀^Fin k]→ₗ[ℝ] ℝ} (hη : η ∈ Q.scForms k) (x : M)
    (v : Fin (k + 1) → EuclideanSpace ℝ (Fin n)) :
    cornerForm hcs (MPolyfold.formPullback hcs.isScSmoothMap_levelOne (extD η)) x v =
      ∑ i : Fin (k + 1), (-1 : ℝ) ^ i.val *
        scDeriv (F := ScBanach.const ℝ)
          ((hcs.coords x).χ.model.E.whitneySet k (chartRetraction (hcs.coords x).χ).U)
          (chartFormExt (hcs.coords x).isChart η)
          ((hcs.coords x).whitneyPtOne
            (levelLift (levelChart (hcs.coords x).isChart (hcs.levelOne x)) 1 (hcs.levelOne x))
            (i.removeNth v))
          (ScBanach.whitneyMk ((hcs.coords x).liftOne ((hcs.coords x).lin (v i))) 0) := by
  have hxχ := hcs.levelOne_mem_coords x
  have hb : ∀ j, (tangentChartMap (Q.shift_isChart (hcs.coords x).isChart (hcs.levelOne x))
      (tangentFiberMap hcs.isScSmoothMap_levelOne (hcs.levelOne x)
        ((hcs.coords x).fiberMap hxχ (v j))).1).2 =
      (hcs.coords x).liftOne ((hcs.coords x).lin (v j)) := fun j => by
    refine (hcs.coords x).eq_liftOne ?_
    rw [← tangentChartMap_tangentLower_snd (hcs.coords x).isChart
      (x := liftLevelOneMap hcs.isScSmoothMap_levelOne (hcs.levelOne x))
      (tangentFiberMap hcs.isScSmoothMap_levelOne (hcs.levelOne x)
        ((hcs.coords x).fiberMap hxχ (v j))) hxχ (hcs.levelOne x),
      coe_tangentFiberMap_apply, hcs.tangentLower_tangentMap_levelOne,
      (hcs.coords x).tangentChartMap_fiberMap]
  change extD η (liftLevelOneMap hcs.isScSmoothMap_levelOne (hcs.levelOne x))
    (fun i => tangentFiberMap hcs.isScSmoothMap_levelOne (hcs.levelOne x)
      ((hcs.coords x).fiberMap hxχ (v i))) = _
  rw [extD_apply (hcs.coords x).isChart (mem_scForms.1 hη) (hcs.levelOne x)
    (x := liftLevelOneMap hcs.isScSmoothMap_levelOne (hcs.levelOne x)) hxχ, chartD,
    retractD, ambientD_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  erw [ScBanach.whitneyVec_mk]
  simp only [hb]
  rfl

/-- **`d` commutes with the passage to Mathlib forms**: for an sc-form `η` on the corner
M-polyfold `Q`, `d(η_M) = (j^*dη)_M`, with `j : Q → Q¹`, `x ↦ x` (`Q = Q¹`), and
`dη ∈ Ωᵏ⁺¹(Q¹)` (`extD`).  Both sides are, in corner coordinates, the alternating sum of the
derivatives of `η_φ ∘ ⊕ₖ Tr` (`extDeriv_cornerForm_apply`, `cornerForm_formPullback_extD_apply`). -/
theorem extDeriv_cornerForm {η : ∀ x : Q.Level 1, Q.tangentFiber x [⋀^Fin k]→ₗ[ℝ] ℝ}
    (hη : η ∈ Q.scForms k) :
    ManifoldForm.extDeriv (cornerForm hcs η) =
      cornerForm hcs (MPolyfold.formPullback hcs.isScSmoothMap_levelOne (extD η)) := by
  funext x
  ext v
  refine (extDeriv_cornerForm_apply hch hη x v _ fun i => (hcs.coords x).toBase_whitneyPtOne
      (toBase_levelLift_levelChart x) (i.removeNth v)).trans
    ((Finset.sum_congr rfl fun i _ => ?_).trans (cornerForm_formPullback_extD_apply hη x v).symm)
  exact congrArg ((-1 : ℝ) ^ i.val * ·) (congrArg _ (CornerCoords.whitneyPtDeriv_apply _ _))

end MathlibForm

/-! ### Sc-forms of `X^i` along an sc-smooth map from the corner M-polyfold -/

section Along

universe w w'

variable (hcs : Q.HasCornerStructureOfDim n) {A : BundledMPolyfold.{w}} (g : ScMap Q A.P)

/-- **The index raises of `g : Q → X` along the levels of `Q`**: `Q = Q¹ = Q^i` as sets
(`HasCornerStructureOfDim.levelOne`), so `g` lifts to `g⁰ = g` and `g^{i+1} = (g^i)¹ ∘ j :
Q → X^{i+1}`, with `j : Q → Q¹`, `x ↦ x`. -/
def alongLift : ∀ i : ℕ, ScMap Q (A.lift i).P
  | 0 => g
  | i + 1 => ⟨liftLevelOneMap (alongLift i).isScSmoothMap ∘ hcs.levelOne,
      (isScSmoothMap_liftLevelOneMap _).comp hcs.isScSmoothMap_levelOne⟩

/-- `g^i` is `g` on the points: the inclusion `X^i → X` after `g^i` is `g`. -/
theorem incl_alongLift : ∀ (i : ℕ) (x : M), A.incl i (alongLift hcs g i x) = g x
  | 0, _ => rfl
  | i + 1, x => incl_alongLift i x

/-- **Naturality of the index raises**: `f^i ∘ g^i = (f ∘ g)^i`. -/
theorem liftMap_alongLift {B : BundledMPolyfold.{w'}} (f : ScMap A.P B.P) :
    ∀ (i : ℕ) (x : M), A.liftMap f i (alongLift hcs g i x) = alongLift hcs (f.comp g) i x
  | 0, _ => rfl
  | i + 1, x => level_ext (liftMap_alongLift f i x)

variable [inst : ChartedSpace (EuclideanQuadrant n) M]

/-- **`ω ↦ ((g^i)^*ω)_M`**: an sc-form on `X^i`, pulled back to `Q` along `g^i`
(`formPullback`, 2021 p. 198) and read as a Mathlib form on `M` (`cornerForm`). -/
def formsAlong (i : ℕ) : A.forms k i →ₗ[ℝ] ManifoldForm (𝓠 n) M k where
  toFun ω := cornerForm hcs (formPullback (alongLift hcs g i).isScSmoothMap ω.1)
  map_add' ω τ := cornerForm_add hcs (formPullback (alongLift hcs g i).isScSmoothMap ω.1)
    (formPullback (alongLift hcs g i).isScSmoothMap τ.1)
  map_smul' c ω := cornerForm_smul hcs c (formPullback (alongLift hcs g i).isScSmoothMap ω.1)

lemma formsAlong_apply (i : ℕ) (ω : A.forms k i) :
    formsAlong hcs g i ω = cornerForm hcs (formPullback (alongLift hcs g i).isScSmoothMap ω.1) :=
  rfl

/-- **`formsAlong` is compatible with the steps of the directed system (4.4)**: the form of
`ι^*ω ∈ Ωᵏ(X^{i+1})` is that of `ω ∈ Ωᵏ(X^i)` (`formLower_formPullback`,
`formPullback_levelOne_formLower`). -/
theorem formsAlong_formsStep (i : ℕ) (ω : A.forms k i) :
    formsAlong hcs g (i + 1) (A.formsStep k i ω) = formsAlong hcs g i ω := by
  rw [formsAlong_apply, formsAlong_apply]
  change cornerForm hcs (formPullback ((isScSmoothMap_liftLevelOneMap
    (alongLift hcs g i).isScSmoothMap).comp hcs.isScSmoothMap_levelOne) (formLower ω.1)) = _
  rw [formPullback_comp (isScSmoothMap_liftLevelOneMap _) hcs.isScSmoothMap_levelOne,
    formLower_formPullback (alongLift hcs g i).isScSmoothMap (fun _ => rfl)
    (isScSmoothMap_liftLevelOneMap _) ω.1, hcs.formPullback_levelOne_formLower]

/-- `formsAlong` is compatible with the maps `Ωᵏ(X^i) → Ωᵏ(X^j)` of the directed system (4.4). -/
theorem formsAlong_formsMap {i j : ℕ} (h : i ≤ j) (ω : A.forms k i) :
    formsAlong hcs g j (A.formsMap k i j h ω) = formsAlong hcs g i ω := by
  induction j, h using Nat.le_induction with
  | base => rw [A.formsMap_self k i]; rfl
  | succ j hij ih => rw [A.formsMap_succ k hij, LinearMap.comp_apply, formsAlong_formsStep, ih]

/-- `formsAlong` after the pull-back along `f : X → Y` is `formsAlong` along `f ∘ g`
(`formPullback_comp`). -/
theorem formsAlong_formsPullback {B : BundledMPolyfold.{w'}} (f : ScMap A.P B.P) (i : ℕ)
    (ω : B.forms k i) :
    formsAlong hcs g i (BundledMPolyfold.formsPullback f k i ω) =
      formsAlong hcs (f.comp g) i ω := by
  rw [formsAlong_apply, formsAlong_apply, BundledMPolyfold.coe_formsPullback,
    ← formPullback_comp]
  exact congrArg (cornerForm hcs) (formPullback_congr _ _ (liftMap_alongLift hcs g f i) ω.1)

variable (k) in
/-- **`Ωᵏ_∞(X) → Ωᵏ(M)`** along `g`: the map induced on the direct limit (2021 Definition 4.4.2,
p. 195) by the `formsAlong` (`formsAlong_formsMap`). -/
def formsInftyAlong : A.formsInfty k →ₗ[ℝ] ManifoldForm (𝓠 n) M k :=
  Module.DirectLimit.lift ℝ ℕ (fun i => ↥(A.forms k i)) (A.formsMap k) (formsAlong hcs g)
    fun _ _ h ω => formsAlong_formsMap hcs g h ω

theorem formsInftyAlong_of (i : ℕ) (ω : A.forms k i) :
    formsInftyAlong k hcs g (A.formsInftyOf k i ω) = formsAlong hcs g i ω :=
  Module.DirectLimit.lift_of _ _ _

/-- `formsInftyAlong g ∘ f^* = formsInftyAlong (f ∘ g)` on `Ωᵏ_∞(Y)`. -/
theorem formsInftyAlong_comp_formsInftyPullback {B : BundledMPolyfold.{w'}} (f : ScMap A.P B.P) :
    (formsInftyAlong k hcs g).comp (BundledMPolyfold.formsInftyPullback f k) =
      formsInftyAlong k hcs (f.comp g) := by
  refine Module.DirectLimit.hom_ext fun i => LinearMap.ext fun ω => ?_
  simp only [LinearMap.comp_apply]
  rw [BundledMPolyfold.formsInftyPullback_of, formsInftyAlong_of, formsInftyAlong_of,
    formsAlong_formsPullback]

variable {hcs} (hch : inst = Q.cornerChartedSpace hcs)
include hch

/-- `formsAlong` takes values in the `C^∞` forms (`contMDiffForm_cornerForm`). -/
theorem contMDiffForm_formsAlong (i : ℕ) (ω : A.forms k i) :
    ManifoldForm.ContMDiffForm (𝓠 n) ∞ (formsAlong hcs g i ω) :=
  contMDiffForm_cornerForm hch (formPullback_mem_scForms _ ω.2)

/-- **`d` commutes with `formsAlong`**: `d(((g^i)^*ω)_M) = ((g^{i+1})^* dω)_M`
(`extDeriv_cornerForm`, `extD_formPullback`). -/
theorem extDeriv_formsAlong (i : ℕ) (ω : A.forms k i) :
    ManifoldForm.extDeriv (formsAlong hcs g i ω) = formsAlong hcs g (i + 1) (A.formsD k i ω) := by
  rw [formsAlong_apply, extDeriv_cornerForm hch (formPullback_mem_scForms _ ω.2),
    extD_formPullback _ ω.2, ← formPullback_comp]
  rfl

theorem contMDiffForm_formsInftyAlong (ω : A.formsInfty k) :
    ManifoldForm.ContMDiffForm (𝓠 n) ∞ (formsInftyAlong k hcs g ω) := by
  obtain ⟨i, ω, rfl⟩ := Module.DirectLimit.exists_of ω
  rw [formsInftyAlong_of]
  exact contMDiffForm_formsAlong g hch i ω

/-- `d ∘ formsInftyAlong = formsInftyAlong ∘ d` on `Ωᵏ_∞(X)` (2021 pp. 197–198, `formsInftyD`). -/
theorem extDeriv_formsInftyAlong (ω : A.formsInfty k) :
    ManifoldForm.extDeriv (formsInftyAlong k hcs g ω) =
      formsInftyAlong (k + 1) hcs g (A.formsInftyD k ω) := by
  obtain ⟨i, ω, rfl⟩ := Module.DirectLimit.exists_of ω
  rw [formsInftyAlong_of, BundledMPolyfold.formsInftyD_of, formsInftyAlong_of,
    extDeriv_formsAlong g hch]

end Along

/-! ### The restriction to a finite-dimensional sub-M-polyfold `S ⊆ X` -/

section Restrict

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {S : Set X} [ParacompactSpace S] {hY : PX.IsSubMPolyfold S}
  (hcs : (subPolyfold hY).HasCornerStructureOfDim n)

variable (hY) in
/-- The inclusion `S → X` of a sub-M-polyfold (2021 Proposition 2.3.19 (1)), as an `ScMap`. -/
def subInclScMap : ScMap (subPolyfold hY) PX := ⟨Subtype.val, subPolyfold_inclusion_isScSmooth hY⟩

include hcs in
/-- **`S ⊆ X_∞`**: a sub-M-polyfold with a corner structure of finite dimension lies in `X_∞`
(`HasCornerStructureOfDim.mem_smoothSet`; the inclusion preserves the levels). -/
theorem subset_smoothSet_of_hasCornerStructureOfDim : S ⊆ PX.smoothSet := fun x hx =>
  mem_iInter.2 fun m => (subPolyfold_inclusion_isScSmooth hY).mapsTo_levelSet m
    (mem_iInter.1 (hcs.mem_smoothSet ⟨x, hx⟩) m)

/-- **The tangent map of `S ↪ X` read in charts is `modelDeriv`**: for `v ∈ ℝⁿ = T_xS` (in the
corner coordinates `κ`), the vector of `Tι(v)` in a chart `φ` of `X` is
`modelDeriv κ φ v = D(σ ∘ χ⁻¹)(χ(x)) Ψ⁻¹v`, `σ` the induced chart (`tangentChartMap_tangentMap`;
`φ ∘ ι ∘ σ⁻¹ = id` on the image of `σ`, `retractTangentMap_id`). -/
theorem tangentChartMap_tangentMap_fiberMap (κ : CornerCoords (subPolyfold hY) n)
    {x : (subPolyfold hY).Level 1} (hx : (subPolyfold hY).levelVal 1 x ∈ κ.χ.source)
    {φ : MChart X} (hφ : PX.IsChart φ) (d : PX.SubData S) (a₀ : S)
    (hxσ : (subPolyfold hY).levelVal 1 x ∈ (subChart d hφ a₀).source)
    (v : EuclideanSpace ℝ (Fin n)) :
    (tangentChartMap hφ (tangentMap (subPolyfold_inclusion_isScSmooth hY)
        (κ.fiberMap hx v).1)).2 =
      modelDeriv κ hφ d a₀ (levelLift κ.χ 1 ((subPolyfold hY).levelVal 1 x)) v := by
  set σ := subChart d hφ a₀ with hσdef
  have hσ : (subPolyfold hY).IsChart σ := subPolyfold_isChart hY d hφ a₀
  have hι := subPolyfold_inclusion_isScSmooth hY
  have hα := mem_tangentChartSet_of_mem_fiber hxσ (κ.fiberMap hx v).2
  have hxφ : ((subPolyfold hY).levelVal 1 x).1 ∈ φ.source := d.shrink_subset_source φ hxσ
  have hfα : Subtype.val ((subPolyfold hY).levelVal 1
      ((subPolyfold hY).tangentProj (κ.fiberMap hx v).1)) ∈ φ.source := by
    rw [tangentProj_eq_of_mem_fiber (κ.fiberMap hx v).2]; exact hxφ
  have hO : IsScRetract σ.model.E σ.model.C (σ '' TangentPre.fdom σ Subtype.val φ) :=
    σ.isScRetract_image inter_subset_left (TangentPre.isOpen_fdom hι σ φ)
  have hid : EqOn (φ ∘ Subtype.val ∘ σ.symm) id (σ '' TangentPre.fdom σ Subtype.val φ) := by
    rintro _ ⟨y, hy, rfl⟩
    change φ (σ.symm (σ y)).1 = σ y
    rw [σ.symm_apply_apply hy.1]
    rfl
  have hmem : tangentChartMap hσ (κ.fiberMap hx v).1 ∈
      retractTangent σ.model.E σ.model.C (σ '' TangentPre.fdom σ Subtype.val φ) := by
    refine (TangentPre.mem_retractTangent_image_iff inter_subset_left
      (TangentPre.isOpen_fdom hι σ φ) ?_).2 (tangentChartMap_mem hσ hα)
    rw [tangentChartMap_fst_of_mem_fiber hσ hxσ (κ.fiberMap hx v).2,
      (subPolyfold hY).toBase_levelLift hσ hxσ (levelVal_mem x)]
    exact ⟨_, ⟨hxσ, hxφ⟩, rfl⟩
  rw [tangentChartMap_tangentMap hι hσ hφ hα hfα]
  refine (congrArg Prod.snd (retractTangentMap_id hO hid hmem)).trans ?_
  exact (tangentChartMap_snd_eq_transDeriv κ.isCornerChart κ.isChart hσ hx hxσ _).trans
    (congrArg _ (κ.tangentChartMap_fiberMap hx v))

variable [inst : ChartedSpace (EuclideanQuadrant n) S]

variable (k) in
/-- **The restriction `ω ↦ ω|_S`** (2021 Theorem 6.7.1, p. 277, the integrand of `Ψ`; G.80): for
`ω ∈ Ωᵏ(X^i)`, the Mathlib `k`-form `x ↦ ω(x)(Tι v₁, …, Tι v_k)` on `S` (the pull-back along
`ι^i : S → X^i`, `formsAlong`), `vⱼ ∈ ℝⁿ = T_xS` read in the corner coordinates of `S`; in a
chart `φ` of `X` this is `ω_φ(φ(x), modelDeriv v₁, …)` (`scFormRestrict_apply_modelDeriv`). -/
def scFormRestrict (i : ℕ) : (BundledMPolyfold.of PX).forms k i →ₗ[ℝ] ManifoldForm (𝓠 n) S k :=
  formsAlong hcs (A := BundledMPolyfold.of PX) (subInclScMap hY) i

/-- `ω|_S` for `ω ∈ Ωᵏ(X)` is `ι^*ω` (`formPullback`) in the corner frame of `T_xS`. -/
lemma scFormRestrict_zero_apply (ω : (BundledMPolyfold.of PX).forms k 0) (x : S)
    (v : Fin k → EuclideanSpace ℝ (Fin n)) :
    scFormRestrict k hcs 0 ω x v =
      formPullback (subPolyfold_inclusion_isScSmooth hY) ω.1 (hcs.levelOne x)
        fun j => (hcs.coords x).fiberMap (hcs.levelOne_mem_coords x) (v j) :=
  rfl

/-- **`ω|_S` through `modelDeriv`**: for `ω ∈ Ωᵏ(X)`, a chart `φ` of `X` at `x` and the induced
chart `σ` of `S`, `ω|_S(x)(v) = ω_φ(φ(x), modelDeriv v₁, …, modelDeriv v_k)`, `modelDeriv` read
in the chosen corner coordinates `hcs.coords x` of `S` at `x` (`chartForm_eq`). -/
theorem scFormRestrict_apply_modelDeriv (ω : (BundledMPolyfold.of PX).forms k 0) (x : S)
    (v : Fin k → EuclideanSpace ℝ (Fin n)) {φ : MChart X} (hφ : PX.IsChart φ) (d : PX.SubData S)
    (a₀ : S) (hxσ : x ∈ (subChart d hφ a₀).source) :
    scFormRestrict k hcs 0 ω x v =
      chartForm hφ ω.1 (ScBanach.whitneyMk (levelLift φ 1 x.1) fun j =>
        modelDeriv (hcs.coords x) hφ d a₀ (levelLift (hcs.coords x).χ 1 x) (v j)) := by
  rw [scFormRestrict_zero_apply]
  refine (chartForm_eq hφ ω.1 (x := liftLevelOneMap (subPolyfold_inclusion_isScSmooth hY)
    (hcs.levelOne x)) (d.shrink_subset_source φ hxσ)
    (fun j => tangentFiberMap (subPolyfold_inclusion_isScSmooth hY) (hcs.levelOne x)
      ((hcs.coords x).fiberMap (hcs.levelOne_mem_coords x) (v j))) rfl fun j => ?_).symm
  rw [ScBanach.whitneyVec_mk, coe_tangentFiberMap_apply]
  exact (tangentChartMap_tangentMap_fiberMap (hcs.coords x) (hcs.levelOne_mem_coords x) hφ d a₀
    hxσ (v j)).symm

/-- **The restriction commutes with `ι^* : Ωᵏ(X^i) → Ωᵏ(X^{i+1})`**: `(ι^*ω)|_S = ω|_S`. -/
theorem scFormRestrict_formLower (i : ℕ) (ω : (BundledMPolyfold.of PX).forms k i) :
    scFormRestrict k hcs (i + 1) ((BundledMPolyfold.of PX).formsStep k i ω) =
      scFormRestrict k hcs i ω :=
  formsAlong_formsStep hcs _ i ω

variable (k) in
/-- **The restriction on `Ωᵏ_∞(X)`** (2021 Definition 4.4.2, p. 195): `[ω] ↦ ω|_S`, well defined
by `scFormRestrict_formLower`. -/
def formsInftyRestrict : (BundledMPolyfold.of PX).formsInfty k →ₗ[ℝ] ManifoldForm (𝓠 n) S k :=
  formsInftyAlong k hcs (A := BundledMPolyfold.of PX) (subInclScMap hY)

theorem formsInftyRestrict_of (i : ℕ) (ω : (BundledMPolyfold.of PX).forms k i) :
    formsInftyRestrict k hcs ((BundledMPolyfold.of PX).formsInftyOf k i ω) =
      scFormRestrict k hcs i ω :=
  formsInftyAlong_of hcs _ i ω

variable {hcs} (hch : inst = (subPolyfold hY).cornerChartedSpace hcs)
include hch

/-- **`ω|_S` is a `C^∞` form** on the Mathlib manifold `S` (`cornerChartedSpace`). -/
theorem contMDiffForm_scFormRestrict (i : ℕ) (ω : (BundledMPolyfold.of PX).forms k i) :
    ManifoldForm.ContMDiffForm (𝓠 n) ∞ (scFormRestrict k hcs i ω) :=
  contMDiffForm_formsAlong _ hch i ω

/-- **`d(ω|_S) = (dω)|_S`** (2021, proof of Theorem 6.7.1, p. 278, with Stokes): Mathlib's exterior
derivative of the restriction is the restriction of `dω ∈ Ωᵏ⁺¹(X^{i+1})`. -/
theorem extDeriv_scFormRestrict (i : ℕ) (ω : (BundledMPolyfold.of PX).forms k i) :
    ManifoldForm.extDeriv (scFormRestrict k hcs i ω) =
      scFormRestrict (k + 1) hcs (i + 1) ((BundledMPolyfold.of PX).formsD k i ω) :=
  extDeriv_formsAlong _ hch i ω

theorem contMDiffForm_formsInftyRestrict (ω : (BundledMPolyfold.of PX).formsInfty k) :
    ManifoldForm.ContMDiffForm (𝓠 n) ∞ (formsInftyRestrict k hcs ω) :=
  contMDiffForm_formsInftyAlong _ hch ω

/-- **`d(ω|_S) = (dω)|_S` on `Ωᵏ_∞(X)`** (`formsInftyD`, 2021 pp. 197–198). -/
theorem extDeriv_formsInftyRestrict (ω : (BundledMPolyfold.of PX).formsInfty k) :
    ManifoldForm.extDeriv (formsInftyRestrict k hcs ω) =
      formsInftyRestrict (k + 1) hcs ((BundledMPolyfold.of PX).formsInftyD k ω) :=
  extDeriv_formsInftyAlong _ hch ω

end Restrict

/-! ### Stokes' theorem for restricted sc-forms -/

section Stokes

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {S : Set X} [ParacompactSpace S] {hY : PX.IsSubMPolyfold S}
  {hcs : (subPolyfold hY).HasCornerStructureOfDim (n + 1)}
  [inst : ChartedSpace (EuclideanQuadrant (n + 1)) S]
  (hch : inst = (subPolyfold hY).cornerChartedSpace hcs)
include hch

/-- **Stokes' theorem for sc-forms on a compact sub-M-polyfold** (2021 Theorem 4.4.7, p. 199;
preprint Theorem 4.28, read with `∫_{∂S}` the boundary integral of the Mathlib manifold `S`): for
a compact `S ⊆ X` with a corner structure of dimension `n + 1`, a continuous tangent orientation
`o` and `ω ∈ Ωⁿ_∞(X)`, `∫_S (dω)|_S = ∫_{∂S} ω|_S` (`extDeriv_formsInftyRestrict`,
`stokes_of_compactSpace`). -/
theorem stokes_formsInftyRestrict [CompactSpace S]
    {o : TangentOrientation (𝓠 (n + 1)) S (n + 1)} (ho : o.IsContinuous (𝓠 (n + 1)) ∞)
    (ω : (BundledMPolyfold.of PX).formsInfty n) :
    haveI := isManifold_of_eq hcs hch
    ManifoldForm.integral o
        (formsInftyRestrict (n + 1) hcs ((BundledMPolyfold.of PX).formsInftyD n ω)) =
      ManifoldForm.boundaryIntegral o (formsInftyRestrict n hcs ω) := by
  have := isManifold_of_eq hcs hch
  rw [← extDeriv_formsInftyRestrict hch]
  exact ManifoldForm.stokes_of_compactSpace ho
    ((contMDiffForm_formsInftyRestrict hch ω).of_le (by exact_mod_cast le_top))

end Stokes

end MPolyfold

/-! ### The hypotheses are met by solution sets in general position -/

section Satisfiable

universe u₁ v₁

open MPolyfold

variable {X : Type u₁} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}

/-- **The hypotheses of `scFormRestrict` hold for a submanifold in good position** (2021
Theorem 4.2.7, p. 188; preprint Theorem 4.18): an `n`-dimensional submanifold `A` of a tame `X`,
in good position at every point, is a sub-M-polyfold with a corner structure of dimension `n`
(`hasCornerStructureOfDim_of_tame`); with `inst := cornerChartedSpace hcs` the hypothesis `hch`
holds by `rfl`.  The solution sets `S ∩ V` of Theorem 6.7.1 and the cobordism `S_F` (p. 278,
over `X × [0, 1]`, read over `ℝ × X`) are of this kind. -/
theorem exists_hasCornerStructureOfDim_of_tame {n : ℕ} (hX : PX.IsTame) {A : Set X}
    (hA : PX.IsSubmanifoldOfDim A n) [ParacompactSpace A] (hgp : ∀ a ∈ A, PX.IsGoodPositionAt A a) :
    ∃ hY : PX.IsSubMPolyfold A, (subPolyfold hY).HasCornerStructureOfDim n :=
  ⟨_, hA.hasCornerStructureOfDim_of_tame hX hgp⟩

variable {Y : Type v₁} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle PX P}
  {f : X → Y}

/-- **The hypotheses hold for the solution set of Theorem 6.6.18** (2021, p. 275; preprint
Theorem 6.41): for a proper sc-Fredholm section in general position with index `d` at every zero
over a tame `X`, `S = f⁻¹(0)` is a sub-M-polyfold with a corner structure of dimension `d`, and the
charted space of `theorem_6_6_18_oriented` is its `cornerChartedSpace` (so `hch` holds by
`rfl`). -/
theorem exists_hasCornerStructureOfDim_solutionSet (hX : PX.IsTame)
    (hft : B.IsScFredholmSectionTame f) (hP : B.IsProper f)
    (hgp : ∀ x, IsZeroAt P f x → B.IsGeneralPositionGerm f x) {d : ℕ}
    (hidx : ∀ y, IsZeroAt P f y → B.IsLinOfIndex f y d) :
    letI := PX.paracompactSpace_subtype (solutionSet P f)
    ∃ (hY : PX.IsSubMPolyfold (solutionSet P f))
      (hcs : (subPolyfold hY).HasCornerStructureOfDim d),
      (subPolyfold hY).cornerChartedSpace hcs =
        (subPolyfold ((theorem_6_6_18_solutionSet hX hft hP hgp).isSubmanifoldOfDim
          hft hidx).1.isSubMPolyfold).cornerChartedSpace
          (((theorem_6_6_18_solutionSet hX hft hP hgp).isSubmanifoldOfDim
            hft hidx).hasCornerStructureOfDim_of_tame
            hX ((theorem_6_6_18_solutionSet hX hft hP hgp).isGoodPositionAt hX)) :=
  ⟨_, _, rfl⟩

end Satisfiable

end Polyfold
