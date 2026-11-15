import Polyfold.Chapter15.GeneralPositionBoundaryWeight
import Polyfold.Chapter15.ParamOntoBridge
import Polyfold.Chapter14.HalfSpaceBundle

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), §15.3, Definition
15.3.5 (general position, p. 693), Definition 9.2.16 (`∂Θ`) and Remark 9.2.14: **an instance
with boundary and non-zero fibres** of `∂Θ = Θ` at a boundary point of general position
(`SBLocalization.boundaryTheta_eq_of_isInGeneralPositionAt`).

# General position at a boundary point of the half-space

## The example

The base is the half-space `H = [0, ∞) × ℝᵐ` with the trivial ep-groupoid, the bundle is
`H × ℝᵏ → H` (`HalfSpaceBundle.halfSEP m k`), the section is the graph section
`f(x) = (x, φ(x))` of a `C^∞` map `φ : ℝ ⊕ ℝᵐ → ℝᵏ`, and `Λ` is the multisection of the zero
section, so that `supp(Λ ∘ f) = φ⁻¹(0) ∩ H`.  At a boundary zero `x₀` (`x₀ ∈ {0} × ℝᵐ`,
`φ(x₀) = 0`) the reduced tangent space `T^R_{x₀}H` is the hyperplane `{0} × ℝᵐ`, and `(f, Λ)` is
in general position at `x₀` iff `Dφ(x₀)` maps `{0} × ℝᵐ` onto `ℝᵏ`.  Then the solution set is a
submanifold near `x₀` which meets `∂H` transversally, `x₀` lies in its boundary, and
`∂Θ(x₀) = Θ(x₀) = 1`.

## What is formalized (namespace `Polyfold.HalfSpaceBundle`)

* `isScFredholmSectionFunctor_graphSection_halfSEP`, `isScFredholmSectionTame_graphSection_halfSEP`:
  the graph section is an sc-Fredholm section functor of `halfSEP m k` with tame germ data.
* `zeroMultisection_graphSection_pos_iff`: `Λ(f(x)) > 0` iff `φ(x) = 0`.
* `scDeriv_principal_comp_r_chartAt`: in the chart centred at `x₀`, the chart linearization of
  `f` at `0` is `Dφ(x₀)`.
* **`isInGeneralPositionAt_graphSection`**: at a zero `x₀ ∈ ∂H` of `φ` with `Dφ(x₀)` onto on
  `{0} × ℝᵐ`, `(f, Λ)` is in general position (Definition 15.3.5: every operator of `T(f,Λ)(x₀)`
  is onto on `T^R_{x₀}H`, in every chart and presentation).
* **`boundaryTheta_halfSEP_graphSection`**: then `∂Θ(x₀) = 1` for `Θ = Λ ∘ f`.
* `hasFullBoundaryWeight_halfSEP_graphSection`: if this holds at all boundary zeros, `∂Θ = Θ`
  on `∂H ∩ supp Θ`.
* **`boundaryTheta_halfSEP_witness`**: for `k ≥ 1`, `m = k` and `φ(a, y) = y` (the solution set
  is the half-line `[0, ∞) × {0}`), all hypotheses of
  `boundaryTheta_eq_of_isInGeneralPositionAt` hold at the corner `0 ∈ ∂H`, the fibres are
  non-zero, `Λ(f(0)) = 1 > 0`, and `∂Θ(0) = Θ(0) = 1`.
-/

set_option maxSynthPendingDepth 3
set_option linter.unusedSectionVars false

open Set Function Topology Filter
open scoped ContDiff

noncomputable section

namespace Polyfold

namespace HalfSpaceBundle

open SBLocalization StrongBundle StrongRetr MPolyfold EpGroupoid Linearization15

variable {m k : ℕ} {φ : Pm m → (Fin k → ℝ)}

/-! ### The graph section over the trivial ep-groupoid of the half-space -/

/-- **The graph section of a `C^∞` map is an sc-Fredholm section functor** of `H × ℝᵏ → H` over
the trivial ep-groupoid of `H` (Definition 8.3.4 (3)). -/
theorem isScFredholmSectionFunctor_graphSection_halfSEP (hφ : ContDiff ℝ ∞ φ) :
    (halfSEP m k).E.IsScFredholmSectionFunctor (graphSection φ) :=
  EpStrongBundle.mem_fredholmSectionFunctors_trivial.2
    ⟨isScSmoothSection_graphSection hφ,
      (isScFredholmSection_graphSection_wholeChart hφ).isScFredholmSection⟩

/-- The graph section has germ data in tame charts at every point of `H`. -/
theorem isScFredholmSectionTame_graphSection_halfSEP (hφ : ContDiff ℝ ∞ φ) :
    (halfSEP m k).B.IsScFredholmSectionTame (graphSection φ) :=
  (isScFredholmSectionTame_graphSection_wholeChart hφ).isScFredholmSectionTame

/-- **`supp(Λ₀ ∘ f) = φ⁻¹(0) ∩ H`** for the multisection `Λ₀` of the zero section. -/
theorem zeroMultisection_graphSection_pos_iff (x : H m) :
    0 < zeroMultisection (halfSEP m k) (graphSection φ x) ↔ φ (x : Pm m) = 0 := by
  classical
  have aux : ∀ w : (halfSEP m k).W, w = graphSection φ x →
      (0 < zeroMultisection (halfSEP m k) w ↔ φ (x : Pm m) = 0) := by
    intro w hw
    have key : w = fiberZero (halfSEP m k).P ((halfSEP m k).P w) ↔ φ (x : Pm m) = 0 := by
      subst hw
      exact isZeroAt_graphSection_iff (k := k) (φ := φ) (x := x)
    unfold zeroMultisection
    constructor
    · intro h
      by_contra hne
      rw [if_neg (fun e => hne (key.1 e))] at h
      exact lt_irrefl _ h
    · intro h
      rw [if_pos (key.2 h)]
      exact one_pos
  exact aux _ rfl

/-- `Λ₀(f(x)) = 1` at a zero of `φ`. -/
theorem zeroMultisection_graphSection_eq_one {x : H m} (h0 : φ (x : Pm m) = 0) :
    zeroMultisection (halfSEP m k) (graphSection φ x) = 1 := by
  classical
  have aux : ∀ w : (halfSEP m k).W, w = graphSection φ x →
      zeroMultisection (halfSEP m k) w = 1 := by
    intro w hw
    have key : w = fiberZero (halfSEP m k).P ((halfSEP m k).P w) := by
      subst hw
      exact (isZeroAt_graphSection_iff (k := k) (φ := φ) (x := x)).2 h0
    unfold zeroMultisection
    rw [if_pos key]
  exact aux _ rfl

/-! ### The chart linearization -/

/-- **The chart linearization of the graph section at the centre of `chartAt x₀` is
`Dφ(x₀)`**: `D(f̂ ∘ r)(0) = Dφ(x₀)`. -/
theorem scDeriv_principal_comp_r_chartAt (hφ : ContDiff ℝ ∞ φ) (x₀ : H m) :
    scDeriv (chartAt (k := k) x₀).U
      ((chartAt (k := k) x₀).principal (graphSection φ) ∘ r (chartAt (k := k) x₀).R) 0 =
      fderiv ℝ φ (x₀ : Pm m) := by
  rw [← scDeriv_loc (k := k) hφ x₀]
  refine scDeriv_eq_of_eqOn_relOpen (chartAt (k := k) x₀).relOpen
    ((isScSmoothSection_graphSection hφ).isSc1_principal_comp_r (isChart_chartAt x₀))
    (isScSmooth_of_bijective_toBase bijective_toBase_E (bijective_toBase_const _)
      (chartAt (k := k) x₀).relOpen.isScDomain (contDiff_loc hφ x₀).contDiffOn).isSc1
    subset_rfl subset_rfl (fun u hu => ?_) ?_
  · change (chartAt (k := k) x₀).principal (graphSection φ)
      ((show Pm m from u) + (x₀ : Pm m) - (x₀ : Pm m)) = loc φ x₀ u
    rw [principal_chartAt (by rw [sub_add_cancel]; exact mem_U_chartAt hu), add_sub_cancel_right]
  · rw [ScBanach.mem_lvlSet, map_zero]
    exact zero_mem_U_chartAt x₀

/-! ### General position at a boundary zero -/

/-- **General position at a boundary zero** (Definition 15.3.5 at one point): if `x₀ ∈ ∂H`,
`φ(x₀) = 0` and `Dφ(x₀)` maps the hyperplane `{0} × ℝᵐ = T^R_{x₀}H` onto `ℝᵏ`, then the graph
section of `φ` and the multisection of the zero section are in general position at `x₀`. -/
theorem isInGeneralPositionAt_graphSection (hφ : ContDiff ℝ ∞ φ) {x₀ : H m}
    (h0 : φ (x₀ : Pm m) = 0) (hb : (x₀ : Pm m).1 0 = 0)
    (honto : ∀ w : Fin k → ℝ, ∃ v : Pm m, v.1 0 = 0 ∧ fderiv ℝ φ (x₀ : Pm m) v = w) :
    IsInGeneralPositionAt (A := halfSEP m k) (graphSection φ) (zeroMultisection (halfSEP m k))
      x₀ := by
  classical
  have hf := isScFredholmSectionFunctor_graphSection_halfSEP (k := k) hφ
  have hft := isScFredholmSectionTame_graphSection_halfSEP (k := k) hφ
  have hx1 : (show (halfSEP m k).Obj from x₀) ∈ (halfSEP m k).X.PObj.levelSet 1 := by
    change x₀ ∈ (basePoly m).levelSet 1
    rw [levelSet_eq_univ]; exact mem_univ _
  refine ⟨hx1, ?_⟩
  set x := (halfSEP m k).X.PObj.levelMk 1 x₀ hx1 with hxdef
  have hxv : (halfSEP m k).X.PObj.levelVal 1 x = x₀ := (halfSEP m k).X.PObj.levelVal_levelMk _ _ _
  set c : StrongBundleChart (halfSEP m k).X.PObj (halfSEP m k).P := chartAt (k := k) x₀ with hcdef
  have hc : (halfSEP m k).B.IsChart c := isChart_chartAt x₀
  have hx : (halfSEP m k).X.PObj.levelVal 1 x ∈ c.φ.source := by
    rw [hxv]; exact mem_source_chartAt x₀
  have hφ0 : c.φ ((halfSEP m k).X.PObj.levelVal 1 x) = 0 := by
    rw [hxv]; exact chartAt_self x₀
  have hx0 : graphSection φ ((halfSEP m k).X.PObj.levelVal 1 x) =
      fiberZero (halfSEP m k).P ((halfSEP m k).X.PObj.levelVal 1 x) := by
    rw [hxv]; exact (isZeroAt_graphSection_iff (k := k) (φ := φ) (x := x₀)).2 h0
  have hT : (chartAt (k := k) x₀).φ.model.C =
      (ScIso.refl (halfSpaceSc m)) 0 ⁻¹' quadrant 1 (rnSc m) 0 :=
    (C_chartAt x₀).trans (by rw [if_pos hb]; ext; rfl)
  intro L hL ψ hψ hxψ n V T' hT'
  rw [← reducedTangentFiber_eq (hφ := c.isChart) (hx := hx) (T := ScIso.refl (halfSpaceSc m))
    (hψ := hψ) (hx' := hxψ) (T' := T') hT hT']
  rw [← (mem_support_linearization_zero_iff hf hc hx hx0 L).1 hL]
  have key := (onto_chart_iff (A := halfSEP m k) (ℓ := 0) (s := fun j => j.elim0) (hft := hft)
    (hsec := fun j => j.elim0) (hc := hc) (hx := hx) (hφ0 := hφ0) (hx0 := hx0)
    (T := ScIso.refl (halfSpaceSc m))).2 ?_
  · intro w
    obtain ⟨v, hv, τ, he⟩ := key w
    refine ⟨⟨v, hv⟩, ?_⟩
    rw [Finset.univ_eq_empty, Finset.sum_empty, add_zero] at he
    exact he
  · intro q _
    obtain ⟨v, hv0, hvq⟩ := honto q
    have htop : rangeS (scDeriv c.U (r c.R) 0) = ⊤ := by
      rw [rangeS, hcdef, scDeriv_r_chartAt]; exact LinearMap.range_id
    refine ⟨⟨v, by rw [htop]; exact Submodule.mem_top⟩, ?_, fun j => j.elim0, ?_⟩
    · exact (mem_minimalSubspaceWith (ScIso.refl (halfSpaceSc m))).2 fun i _ => by
        rw [Subsingleton.elim i 0]; exact hv0
    · rw [linAt_apply, Finset.univ_eq_empty, Finset.sum_empty, add_zero]
      change scDeriv (chartAt (k := k) x₀).U ((chartAt (k := k) x₀).principal (graphSection φ) ∘
        r (chartAt (k := k) x₀).R) 0 v = q
      rw [scDeriv_principal_comp_r_chartAt hφ x₀]
      exact hvq

/-! ### `∂Θ = Θ` at the boundary zeros -/

/-- **`∂Θ(x₀) = Θ(x₀) = 1` at a boundary zero of general position** (Definition 9.2.16, Remark
9.2.14): for `Θ = Λ₀ ∘ f` on the half-space, `f` the graph section of `φ`, at `x₀ ∈ ∂H` with
`φ(x₀) = 0` and `Dφ(x₀)` onto on `{0} × ℝᵐ`. -/
theorem boundaryTheta_halfSEP_graphSection (hφ : ContDiff ℝ ∞ φ) {x₀ : H m}
    (h0 : φ (x₀ : Pm m) = 0) (hb : (x₀ : Pm m).1 0 = 0)
    (honto : ∀ w : Fin k → ℝ, ∃ v : Pm m, v.1 0 = 0 ∧ fderiv ℝ φ (x₀ : Pm m) v = w) :
    (halfSEP m k).X.boundaryTheta
      (fun z => (zeroMultisection (halfSEP m k) (graphSection φ z) : ℚ)) x₀ = 1 := by
  have h := boundaryTheta_eq_of_isInGeneralPositionAt (isTame_halfSEP m k)
    (isScFredholmSectionFunctor_graphSection_halfSEP hφ)
    (isScFredholmSectionTame_graphSection_halfSEP hφ)
    (isScPlusMultisection_zeroMultisection (halfSEP m k))
    ((mem_boundary_halfSEP_iff m k x₀).2 hb) (isInGeneralPositionAt_graphSection hφ h0 hb honto)
  rw [h, zeroMultisection_graphSection_eq_one h0]
  rfl

/-- **`∂Θ = Θ` on `∂H ∩ supp Θ`** for `Θ = Λ₀ ∘ f`, if `Dφ` is onto on `{0} × ℝᵐ` at every
boundary zero of `φ` (`0` is a regular value of `φ|∂H`). -/
theorem hasFullBoundaryWeight_halfSEP_graphSection (hφ : ContDiff ℝ ∞ φ)
    (hreg : ∀ x : H m, φ (x : Pm m) = 0 → (x : Pm m).1 0 = 0 →
      ∀ w : Fin k → ℝ, ∃ v : Pm m, v.1 0 = 0 ∧ fderiv ℝ φ (x : Pm m) v = w) :
    (halfSEP m k).X.HasFullBoundaryWeight
      (fun z => (zeroMultisection (halfSEP m k) (graphSection φ z) : ℚ)) :=
  hasFullBoundaryWeight_of_generalPosition (isTame_halfSEP m k)
    (isScFredholmSectionFunctor_graphSection_halfSEP hφ)
    (isScFredholmSectionTame_graphSection_halfSEP hφ)
    (isScPlusMultisection_zeroMultisection (halfSEP m k)) fun y hy hpos =>
      have h0 := (zeroMultisection_graphSection_pos_iff (k := k) (φ := φ) y).1 hpos
      have hb := (mem_boundary_halfSEP_iff m k y).1 hy
      isInGeneralPositionAt_graphSection hφ h0 hb (hreg y h0 hb)

/-! ### The concrete instance `φ(a, y) = y` -/

/-- The linear map `ℝ ⊕ ℝᵏ → ℝᵏ`, `(a, y) ↦ y`. -/
def sndProj (k : ℕ) : Pm k →L[ℝ] (Fin k → ℝ) := ContinuousLinearMap.snd ℝ _ _

/-- `D(sndProj)` is onto on the hyperplane `{0} × ℝᵏ`, at every point. -/
theorem sndProj_onto_hyperplane (x : Pm k) (w : Fin k → ℝ) :
    ∃ v : Pm k, v.1 0 = 0 ∧ fderiv ℝ (sndProj k) x v = w := by
  rw [(sndProj k).fderiv]
  exact ⟨(0, w), rfl, rfl⟩

/-- **A non-degenerate instance of `∂Θ = Θ` in general position**: on the half-space bundle
`([0, ∞) × ℝᵏ) × ℝᵏ → [0, ∞) × ℝᵏ`, `k ≥ 1`, with the section `f(a, y) = ((a, y), y)` and the
multisection `Λ₀` of the zero section, all hypotheses of
`boundaryTheta_eq_of_isInGeneralPositionAt` hold at the corner `0`: `X` is tame, `f` is an
sc-Fredholm section functor with tame germ data, `Λ₀` is an sc⁺-multisection, `0 ∈ ∂X`, and
`(f, Λ₀)` is in general position at `0`.  The boundary is non-empty, every fibre is a non-zero
vector space, and `Λ₀(f(0)) = 1 > 0`.  The conclusions: `∂Θ(0) = Θ(0) = 1`, and `∂Θ = Θ` on
`∂X ∩ supp Θ`, where `supp Θ` is the half-line `[0, ∞) × {0}`. -/
theorem boundaryTheta_halfSEP_witness (k : ℕ) [NeZero k] :
    (halfSEP k k).X.IsTame ∧
      (halfSEP k k).E.IsScFredholmSectionFunctor (graphSection (sndProj k)) ∧
      (halfSEP k k).B.IsScFredholmSectionTame (graphSection (sndProj k)) ∧
      IsScPlusMultisection (halfSEP k k) (zeroMultisection (halfSEP k k)) ∧
      (⟨0, fun _ => le_rfl⟩ : (halfSEP k k).Obj) ∈ (halfSEP k k).X.PObj.boundary ∧
      (∀ y : (halfSEP k k).Obj, Nontrivial ((halfSEP k k).P ⁻¹' {y})) ∧
      0 < zeroMultisection (halfSEP k k)
        (graphSection (sndProj k) (⟨0, fun _ => le_rfl⟩ : H k)) ∧
      IsInGeneralPositionAt (A := halfSEP k k) (graphSection (sndProj k))
        (zeroMultisection (halfSEP k k)) (⟨0, fun _ => le_rfl⟩ : H k) ∧
      (halfSEP k k).X.boundaryTheta
        (fun z => (zeroMultisection (halfSEP k k) (graphSection (sndProj k) z) : ℚ))
        (⟨0, fun _ => le_rfl⟩ : H k) = 1 ∧
      ((zeroMultisection (halfSEP k k)
        (graphSection (sndProj k) (⟨0, fun _ => le_rfl⟩ : H k)) : ℚ≥0) : ℚ) = 1 ∧
      (halfSEP k k).X.HasFullBoundaryWeight
        (fun z => (zeroMultisection (halfSEP k k) (graphSection (sndProj k) z) : ℚ)) := by
  have hφ : ContDiff ℝ ∞ (sndProj k) := (sndProj k).contDiff
  have h0 : sndProj k (((⟨0, fun _ => le_rfl⟩ : H k) : Pm k)) = 0 := map_zero _
  have hb : (((⟨0, fun _ => le_rfl⟩ : H k) : Pm k)).1 0 = 0 := rfl
  refine ⟨isTame_halfSEP k k, isScFredholmSectionFunctor_graphSection_halfSEP hφ,
    isScFredholmSectionTame_graphSection_halfSEP hφ,
    isScPlusMultisection_zeroMultisection _, zero_mem_boundary_halfSEP k k,
    nontrivial_fibre_halfSEP k k, (zeroMultisection_graphSection_pos_iff _).2 h0,
    isInGeneralPositionAt_graphSection hφ h0 hb (sndProj_onto_hyperplane _),
    boundaryTheta_halfSEP_graphSection hφ h0 hb (sndProj_onto_hyperplane _), ?_,
    hasFullBoundaryWeight_halfSEP_graphSection hφ fun x _ _ => sndProj_onto_hyperplane _⟩
  rw [zeroMultisection_graphSection_eq_one h0]
  rfl

end HalfSpaceBundle

end Polyfold
