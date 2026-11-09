import Polyfold.Chapter4.ScPlus

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory I* (2014 preprint), §4.1, Remark 4.1.3 (preprint 4.3), p. 176 (preprint p. 148):
"it is possible that `X¹ ≠ X` as M-polyfolds although the underlying sets agree".

# Remark 4.1.3 (preprint 4.3)'s example: what it needs, and an sc-smoothness criterion with loss

## The text, paraphrased

(Remark 4.1.3 (preprint 4.3)) If `X₀ = X_∞`, the identity `1₀¹ : X → X¹` has the inverse `1₁⁰ : X¹ → X`, which is
always sc-smooth, so if `1₀¹` is sc-smooth it is an sc-diffeomorphism.  "It is possible that
`X¹ ≠ X` as M-polyfolds although the underlying sets agree."  No example is given (comparison item
V4.6, gap G.31; Findings, Chapter 4, items 5, 125).

## Where an example must come from

By Proposition 4.1.8 (preprint 4.8) in charts (`MPolyfold.isScSmoothMap_toLevelOne_iff`), an example is an
sc-retract `O = r(U)` with `O = O_∞` which is not an sc⁺-retract, i.e. `r : U → E¹` is not
sc-smooth.  It cannot come from a retraction whose level maps `r : U_m → E_m` are `C¹` (the maps
produced by the text's Proposition 1.2.4 (preprint 1.19) and Corollary 1.2.5 (preprint 1.20), and their composites): for such `r`
a Baire category argument (`O ⊆ ⋃ₙ cl₀{|x|₁ ≤ n}`, compact sets) makes `T_oO` finite-dimensional,
and then the topologies of `O` in `E₀` and `E₁` agree (Findings, Chapter 4, item 141; not
formalized).  So `r` must lose a level in its first derivative, as the splicings of HWZ do, and
its sc-smoothness needs a criterion with loss, which the project did not have.

## What is formalized

* **An sc-smoothness criterion with loss.**  `IsLossFamily L`: level operators
  `L(p)_m : Z_m → W_m` (`p ∈ V`, finite-dimensional), compatible with the inclusions,
  `(p, z) ↦ L(p)_m z` continuous on `V × Z_m`, and `p ↦ L(p)_m ∘ ι ∈ L(Z_{m+1}, W_m)` of class
  `C^∞` in the operator norm.  `IsLossFamily.isScSmooth`: `(p, z) ↦ L(p) z` is sc-smooth on
  `V ⊕ Z`.  The proof is an induction on `k` (`isSck_lossFamMap`): the map is sc¹ with derivative
  `(π, ζ) ↦ ∂_pA_0(p)[π] z + L(p) ζ` (`IsLossFamily.isSc1With`), and its tangent map is the map of
  the **tangent family** `L̃(p, π)(z, ζ) = (L(p) z, ∂_pA(p)[π] z + L(p) ζ)` on `V × V`
  (`famTangent`, `tangentMapWith_lossFamMap_eq`) after the sc-isomorphism `famSwap`, and `L̃` is again
  a loss family (`IsLossFamily.tangent`).  `L(p)_m` need not depend continuously on `p` in the
  operator norm; this is the room the example needs.
* **The reduction of the example.**  For a loss family of projections (`L(p)₀² = L(p)₀`),
  `r(p, z) = (p, L(p) z)` is an sc-smooth retraction (`IsLossFamily.retraction`); if the ranges
  consist of smooth points, `O = O_∞` (`IsLossFamily.retract_subset_smooth`); if moreover the lift
  `O → E₁` is discontinuous, `O` is not an sc⁺-retract (`IsLossFamily.not_isScPlusRetract`, by
  Proposition 4.1.8 (preprint 4.8)).  `RemarkFourThreeData V Z` collects these hypotheses and
  `exists_retract_smooth_not_scPlus_of_data` gives the retract.

## The example

`RemarkFourThreeFamily.lean` supplies the data (`RemarkFourThree.remarkFourThreeData`): on the
weighted sequence space `X` of `ScOneNotNormContinuous.lean`, `L(t)` is the projection onto
`cos θ e_{n_k} + sin θ e_{n_{k+1}}` (`n_k = 2^k`), the angle `θ` turning from `0` to `π/2` with flat
ends while `t` runs through `[1/(k+2), 1/(k+1)]`, and `L(t) = 0` for `t ≤ 0`.  The resulting
M-polyfold with `X₀ = X_∞` and `1₀¹` not sc-smooth is `remark_4_1_3_example` there (Findings,
Chapter 4, items 142, 144–146).

## What the text leaves implicit, and the choices made

* The text's "`X¹ ≠ X` as M-polyfolds" is read as "`1₀¹` is not sc-smooth" (equivalently, by
  `remark_4_1_3_isScDiffeo`, the identity is not an sc-diffeomorphism `X → X¹`).
* Only one level of loss is allowed in `IsLossFamily` (all `p`-derivatives exist into
  `L(Z_{m+1}, W_m)`); maps whose `j`-th derivative needs `j` levels, such as
  `(t, x) ↦ (cos(kt)x_k)_k` of `ScOneNotNormContinuous.lean`, are not covered.  The criterion is
  stated for `U = V ⊕ Z` (no boundary).
-/

open Set Filter Topology Function
open scoped ContDiff

noncomputable section

namespace Polyfold

/-! ### Parameter families of level operators with one level of loss -/

section LossFamily

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  {Z W : ScBanach}

/-- **A parameter family of level operators with one level of loss**: continuous linear maps
`L(p)_m : Z_m → W_m`, `p ∈ V` (finite-dimensional), compatible with the inclusions, such that
`(p, z) ↦ L(p)_m z` is continuous on `V × Z_m` (strong continuity, *not* continuity of
`p ↦ L(p)_m` in the operator norm) and `p ↦ L(p)_m ∘ ι : V → L(Z_{m+1}, W_m)` is `C^∞` in the
operator norm (one level of loss buys all the `p`-derivatives). -/
structure IsLossFamily (L : V → ∀ m, Z m →L[ℝ] W m) : Prop where
  toBase : ∀ p m (z : Z m), W.toBase m (L p m z) = L p 0 (Z.toBase m z)
  continuous : ∀ m, Continuous fun q : V × Z m => L q.1 m q.2
  contDiff : ∀ m, ContDiff ℝ ∞ fun p => (L p m).comp (Z.incl m)

/-- The map `(p, z) ↦ L(p) z` on `V ⊕ Z` (level `0`). -/
def lossFamMap (L : V → ∀ m, Z m →L[ℝ] W m) : ((ScBanach.const V).prod Z) 0 → W 0 :=
  fun q => L q.1 0 q.2

/-- `A_m(p) = L(p)_m ∘ ι : Z_{m+1} → W_m`. -/
def famLoss (L : V → ∀ m, Z m →L[ℝ] W m) (m : ℕ) (p : V) : Z (m + 1) →L[ℝ] W m :=
  (L p m).comp (Z.incl m)

/-- The `p`-derivative `D_m(p)π = ∂_p A_m(p)[π] : Z_{m+1} → W_m`. -/
def famDeriv (L : V → ∀ m, Z m →L[ℝ] W m) (m : ℕ) (p π : V) : Z (m + 1) →L[ℝ] W m :=
  fderiv ℝ (famLoss L m) p π

/-- **The tangent family** on `V × V`: `L̃(p, π)_m (z, ζ) = (L(p)_{m+1} z, D_m(p)π z + L(p)_m ζ)`,
from `(Z¹ ⊕ Z)_m = Z_{m+1} × Z_m` to `(W¹ ⊕ W)_m = W_{m+1} × W_m`.  The tangent map of `lossFamMap L`
is `lossFamMap L̃` after reordering `(p, z, π, ζ) ↦ ((p, π), (z, ζ))`. -/
def famTangent (L : V → ∀ m, Z m →L[ℝ] W m) (q : V × V) (m : ℕ) :
    (Z.shift.prod Z) m →L[ℝ] (W.shift.prod W) m :=
  (ContinuousLinearMap.inl ℝ (W (m + 1)) (W m)).comp
      ((L q.1 (m + 1)).comp (ContinuousLinearMap.fst ℝ (Z (m + 1)) (Z m))) +
    (ContinuousLinearMap.inr ℝ (W (m + 1)) (W m)).comp
      ((famDeriv L m q.1 q.2).comp (ContinuousLinearMap.fst ℝ (Z (m + 1)) (Z m)) +
        (L q.1 m).comp (ContinuousLinearMap.snd ℝ (Z (m + 1)) (Z m)))

omit [FiniteDimensional ℝ V] in
/-- The tangent family in coordinates. -/
lemma famTangent_apply (L : V → ∀ m, Z m →L[ℝ] W m) (q : V × V) (m : ℕ)
    (z : (Z.shift.prod Z) m) :
    famTangent L q m z =
      ((L q.1 (m + 1) z.1, famDeriv L m q.1 q.2 z.1 + L q.1 m z.2) : W (m + 1) × W m) := by
  simp [famTangent]

/-- The inclusion `(V ⊕ Z)_m → (V ⊕ Z)₀` is `(p, z) ↦ (p, ι z)`. -/
lemma toBase_constProd (m : ℕ) (x : ((ScBanach.const V).prod Z) m) :
    ((ScBanach.const V).prod Z).toBase m x = ((x.1, Z.toBase m x.2) : V × Z 0) := by
  rw [ScBanach.prod_toBase, ScBanach.const_toBase]

/-- `Z₁ → Z₀` is the first inclusion. -/
lemma toBase_one_eq_incl (z : Z 1) : Z.toBase 1 z = Z.incl 0 z := rfl

variable {L : V → ∀ m, Z m →L[ℝ] W m}

namespace IsLossFamily

omit [FiniteDimensional ℝ V] in
/-- The loss maps `A_m(p)` are compatible with the inclusions. -/
lemma famLoss_toBase (h : IsLossFamily L) (m : ℕ) (p : V) (z : Z (m + 1)) :
    W.toBase m (famLoss L m p z) = famLoss L 0 p (Z.shift.toBase m z) := by
  change W.toBase m (L p m (Z.incl m z)) = L p 0 (Z.incl 0 (Z.shift.toBase m z))
  rw [h.toBase, ← toBase_one_eq_incl, ← ScBanach.shift_toBase, ScScale.toBase_succ]

omit [FiniteDimensional ℝ V] in
/-- `p ↦ A_m(p)` is differentiable. -/
lemma differentiable_famLoss (h : IsLossFamily L) (m : ℕ) : Differentiable ℝ (famLoss L m) :=
  (h.contDiff m).differentiable (by simp)

omit [FiniteDimensional ℝ V] in
/-- The `p`-derivatives `D_m(p)π` are compatible with the inclusions (differentiate
`famLoss_toBase` in `p`). -/
lemma famDeriv_toBase (h : IsLossFamily L) (m : ℕ) (p π : V) (z : Z (m + 1)) :
    W.toBase m (famDeriv L m p π z) = famDeriv L 0 p π (Z.shift.toBase m z) := by
  have h1 : HasFDerivAt (fun p => W.toBase m (famLoss L m p z))
      ((W.toBase m).comp ((fderiv ℝ (famLoss L m) p).flip z)) p := by
    have := ((h.differentiable_famLoss m p).hasFDerivAt.clm_apply (hasFDerivAt_const z p))
    have := (W.toBase m).hasFDerivAt.comp p this
    refine this.congr_fderiv ?_
    ext π; simp
  have h2 : HasFDerivAt (fun p => famLoss L 0 p (Z.shift.toBase m z))
      ((fderiv ℝ (famLoss L 0) p).flip (Z.shift.toBase m z)) p := by
    have := ((h.differentiable_famLoss 0 p).hasFDerivAt.clm_apply
      (hasFDerivAt_const (Z.shift.toBase m z) p))
    refine this.congr_fderiv ?_
    ext π; simp
  have e : (fun p => W.toBase m (famLoss L m p z)) =
      fun p => famLoss L 0 p (Z.shift.toBase m z) := funext fun p => h.famLoss_toBase m p z
  rw [e] at h1
  have := congrArg (fun T : V →L[ℝ] W 0 => T π) (h1.unique h2)
  simpa [famDeriv] using this

omit [FiniteDimensional ℝ V] in
/-- `(p, π, z) ↦ D_m(p)π z` is continuous. -/
lemma continuous_famDeriv (h : IsLossFamily L) (m : ℕ) :
    Continuous fun q : (V × V) × Z (m + 1) => famDeriv L m q.1.1 q.1.2 q.2 := by
  have hc : Continuous (fderiv ℝ (famLoss L m)) := (h.contDiff m).continuous_fderiv (by simp)
  exact ((hc.comp (continuous_fst.comp continuous_fst)).clm_apply
    (continuous_snd.comp continuous_fst)).clm_apply continuous_snd

omit [FiniteDimensional ℝ V] in
/-- `(p, π) ↦ D_m(p)π ∈ L(Z_{m+1}, W_m)` is `C^∞`. -/
lemma contDiff_famDeriv (h : IsLossFamily L) (m : ℕ) :
    ContDiff ℝ ∞ fun q : V × V => famDeriv L m q.1 q.2 :=
  (((h.contDiff m).fderiv_right (by simp)).comp contDiff_fst).clm_apply contDiff_snd

omit [FiniteDimensional ℝ V] in
/-- **The tangent family is again a loss family.** -/
theorem tangent (h : IsLossFamily L) : IsLossFamily (famTangent L) where
  toBase q m z := by
    rw [ScBanach.prod_toBase, ScBanach.prod_toBase, famTangent_apply, famTangent_apply]
    refine Prod.ext ?_ ?_
    · apply W.toBase_injective 1
      change W.toBase 1 (W.shift.toBase m (L q.1 (m + 1) z.1)) =
        W.toBase 1 (L q.1 1 (Z.shift.toBase m z.1))
      rw [← ScBanach.shift_toBase, h.toBase, h.toBase, ← ScBanach.shift_toBase]
    · change W.toBase m (famDeriv L m q.1 q.2 z.1 + L q.1 m z.2) =
        famDeriv L 0 q.1 q.2 (Z.shift.toBase m z.1) + L q.1 0 (Z.toBase m z.2)
      rw [map_add, h.famDeriv_toBase, h.toBase]
  continuous m := by
    have e : (fun q : (V × V) × (Z.shift.prod Z) m => famTangent L q.1 m q.2) =
        fun q => ((L q.1.1 (m + 1) q.2.1, famDeriv L m q.1.1 q.1.2 q.2.1 + L q.1.1 m q.2.2) :
          W (m + 1) × W m) := funext fun q => famTangent_apply L q.1 m q.2
    rw [e]
    refine Continuous.prodMk ?_ ?_
    · exact (h.continuous (m + 1)).comp ((continuous_fst.comp continuous_fst).prodMk
        (continuous_fst.comp continuous_snd))
    · refine Continuous.add ?_ ?_
      · exact (h.continuous_famDeriv m).comp (continuous_fst.prodMk
          (continuous_fst.comp continuous_snd))
      · exact (h.continuous m).comp ((continuous_fst.comp continuous_fst).prodMk
          (continuous_snd.comp continuous_snd))
  contDiff m := by
    have e : (fun q : V × V => (famTangent L q m).comp ((Z.shift.prod Z).incl m)) =
        fun q => (ContinuousLinearMap.inl ℝ (W (m + 1)) (W m)).comp
          ((famLoss L (m + 1) q.1).comp (ContinuousLinearMap.fst ℝ (Z (m + 1 + 1)) (Z (m + 1)))) +
        (ContinuousLinearMap.inr ℝ (W (m + 1)) (W m)).comp
          ((famDeriv L m q.1 q.2).comp ((Z.incl (m + 1)).comp
            (ContinuousLinearMap.fst ℝ (Z (m + 1 + 1)) (Z (m + 1)))) +
          (famLoss L m q.1).comp (ContinuousLinearMap.snd ℝ (Z (m + 1 + 1)) (Z (m + 1)))) := by
      funext q
      ext z <;> simp [famTangent, famLoss]
    rw [e]
    refine ContDiff.add (contDiff_const.clm_comp
      (((h.contDiff (m + 1)).comp contDiff_fst).clm_comp contDiff_const))
      (contDiff_const.clm_comp ((((h.contDiff_famDeriv m)).clm_comp contDiff_const).add
        (((h.contDiff m).comp contDiff_fst).clm_comp contDiff_const)))

/-- The level maps of `lossFamMap L` are `(p, z) ↦ L(p)_m z`. -/
lemma levelMap_lossFamMap (h : IsLossFamily L) (m : ℕ) (x : ((ScBanach.const V).prod Z) m) :
    levelMap (lossFamMap L) m x = L x.1 m x.2 := by
  apply levelMap_eq_of_toBase_eq
  rw [toBase_constProd, h.toBase]; rfl

/-- `lossFamMap L` is sc⁰: its level maps are `(p, z) ↦ L(p)_m z`. -/
theorem isSc0 (h : IsLossFamily L) : IsSc0 ((ScBanach.const V).prod Z) W univ (lossFamMap L) where
  mem_range m x _ := ⟨L x.1 m x.2, by rw [toBase_constProd, h.toBase]; rfl⟩
  continuousOn m := (h.continuous m).continuousOn.congr fun x _ => h.levelMap_lossFamMap m x

end IsLossFamily

/-- The derivative of `lossFamMap L` at `(p, z) ∈ V × Z₁`: `(π, ζ) ↦ D_0(p)π z + L(p) ζ`. -/
def famD (L : V → ∀ m, Z m →L[ℝ] W m) (x : ((ScBanach.const V).prod Z) 1) :
    ((ScBanach.const V).prod Z) 0 →L[ℝ] W 0 :=
  ((ContinuousLinearMap.apply ℝ (W 0) x.2).comp (fderiv ℝ (famLoss L 0) x.1)).comp
      (ContinuousLinearMap.fst ℝ V (Z 0)) +
    (L x.1 0).comp (ContinuousLinearMap.snd ℝ V (Z 0))

/-- The derivative `famD L` in coordinates. -/
lemma famD_apply (L : V → ∀ m, Z m →L[ℝ] W m) (x : ((ScBanach.const V).prod Z) 1)
    (v : ((ScBanach.const V).prod Z) 0) :
    famD L x v = famDeriv L 0 x.1 v.1 x.2 + L x.1 0 v.2 := rfl

/-- The reordering `T(V ⊕ Z) → (V × V) ⊕ (Z¹ ⊕ Z)`, `((p, z), (π, ζ)) ↦ ((p, π), (z, ζ))`. -/
def famSwap (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (Z : ScBanach) :
    ScOperator ((ScBanach.const V).prod Z).tangent
      ((ScBanach.const (V × V)).prod (Z.shift.prod Z)) where
  lvl m := (ContinuousLinearEquiv.prodProdProdComm ℝ V (Z (m + 1)) V (Z m) : _ →L[ℝ] _)
  incl_comm _ _ := rfl

/-- **The tangent map of `lossFamMap L` is `lossFamMap L̃` after the reordering `famSwap`.** -/
lemma tangentMapWith_lossFamMap_eq (h : IsLossFamily L) :
    tangentMapWith (lossFamMap L) (famD L) = lossFamMap (famTangent L) ∘ famSwap V Z 0 := by
  funext p
  change (levelMap (lossFamMap L) 1 p.1, famD L p.1 p.2) = famTangent L (p.1.1, p.2.1) 0 (p.1.2, p.2.2)
  rw [h.levelMap_lossFamMap, famTangent_apply, famD_apply]

namespace IsLossFamily

/-- `lossFamMap L` is sc¹ with derivative `famD L` (Definition 1.1.15 (preprint 1.14)). -/
theorem isSc1With (h : IsLossFamily L) :
    IsSc1With (E := (ScBanach.const V).prod Z) univ (lossFamMap L) (famD L) where
  isSc0 := h.isSc0
  hasFDerivWithinAt x _ := by
    rw [ScBanach.lvlSet_univ]
    refine HasFDerivAt.hasFDerivWithinAt ?_
    have e : (lossFamMap L ∘ ((ScBanach.const V).prod Z).toBase 1) =
        fun y : V × Z 1 => famLoss L 0 y.1 y.2 := by
      funext y
      change lossFamMap L (((ScBanach.const V).prod Z).toBase 1 y) = _
      rw [toBase_constProd]; rfl
    rw [e]
    have := ((h.differentiable_famLoss 0 x.1).hasFDerivAt.comp x hasFDerivAt_fst).clm_apply
      (hasFDerivAt_snd (p := x))
    refine this.congr_fderiv (ContinuousLinearMap.ext fun v => ?_)
    rw [ContinuousLinearMap.comp_apply, toBase_constProd, famD_apply]
    simp only [add_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.flip_apply, Function.comp_apply, ContinuousLinearMap.coe_snd',
      ContinuousLinearMap.coe_fst']
    rw [add_comm]; rfl
  tangent_isSc0 := by
    rw [tangentMapWith_lossFamMap_eq h]
    exact (h.tangent.isSc0).comp (((famSwap V Z).isSc0).mono (subset_univ _))
      (mapsTo_univ _ _)

end IsLossFamily

/-- **An sc-smoothness criterion with loss**: for a loss family `L`, the map `(p, z) ↦ L(p) z` on
`V ⊕ Z` is sc^k for every `k`.  Induction on `k`: its tangent map is the map of the tangent family
`L̃` (`IsLossFamily.famTangent`) after an sc-isomorphism. -/
theorem isSck_lossFamMap : ∀ (k : ℕ) {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] {Z W : ScBanach} {L : V → ∀ m, Z m →L[ℝ] W m},
    IsLossFamily L → IsSck k ((ScBanach.const V).prod Z) W univ (lossFamMap L)
  | 0, _, _, _, _, _, _, _, h => h.isSc0
  | k + 1, V, _, _, _, Z, W, L, h => by
    have hU : IsScDomain ((ScBanach.const V).prod Z) univ := isScDomain_univ _
    refine ⟨h.isSc1With.isSc1, ?_⟩
    have h2 : EqOn (tangentMap univ (lossFamMap L)) (lossFamMap (famTangent L) ∘ famSwap V Z 0)
        (ScBanach.tangentSet _ univ) := by
      rw [← tangentMapWith_lossFamMap_eq h]
      exact IsSc1.tangentMap_eqOn h.isSc1With (hU.uniqueDiffWithinAt 1)
    refine IsSck.congr hU.tangentSet h2.symm ?_
    exact IsSck.comp hU.tangentSet (isScDomain_univ _) (isSck_lossFamMap k h.tangent)
      ((famSwap V Z).isScSmooth hU.tangentSet k) (mapsTo_univ _ _)

/-- **An sc-smoothness criterion with loss** (sc-smooth form). -/
theorem IsLossFamily.isScSmooth (h : IsLossFamily L) :
    IsScSmooth (E := (ScBanach.const V).prod Z) univ (lossFamMap L) :=
  fun k => isSck_lossFamMap k h

end LossFamily

/-! ### Retractions from loss families, and the reduction of Remark 4.1.3 (preprint 4.3)'s example -/

section Retract

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  {Z : ScBanach} {L : V → ∀ m, Z m →L[ℝ] Z m}

/-- The map `r(p, z) = (p, L(p) z)` on `V ⊕ Z`. -/
def famRetr (L : V → ∀ m, Z m →L[ℝ] Z m) :
    ((ScBanach.const V).prod Z) 0 → ((ScBanach.const V).prod Z) 0 :=
  fun q => (q.1, L q.1 0 q.2)

/-- `r(p, z) = (p, L(p) z)` is sc-smooth for a loss family `L` (the pairing of the projection
`V ⊕ Z → V` with `lossFamMap L`). -/
theorem IsLossFamily.isScSmooth_famRetr (h : IsLossFamily L) :
    IsScSmooth (E := (ScBanach.const V).prod Z) univ (famRetr L) :=
  ((ScBanach.prodFstOp (ScBanach.const V) Z).isScSmooth (isScDomain_univ _)).scPair
    (isScDomain_univ _) h.isScSmooth

/-- **The sc-smooth retraction of a loss family of projections**: if every `L(p)₀` is idempotent,
`r(p, z) = (p, L(p) z)` is an sc-smooth retraction of `V ⊕ Z` (Definition 2.1.1 (preprint 2.1), `U = C = V ⊕ Z`). -/
def IsLossFamily.retraction (h : IsLossFamily L) (hidem : ∀ p z, L p 0 (L p 0 z) = L p 0 z) :
    ScRetraction ((ScBanach.const V).prod Z) univ where
  U := univ
  toFun := famRetr L
  relOpen := ⟨isPartialQuadrant_univ _, univ, isOpen_univ, (inter_univ _).symm⟩
  mapsTo := mapsTo_univ _ _
  isScSmooth := h.isScSmooth_famRetr
  idem q _ := Prod.ext rfl (hidem q.1 q.2)

/-- If the ranges of the `L(p)₀` consist of smooth points, so does the retract `O = r(V ⊕ Z)`:
`O = O_∞`. -/
theorem IsLossFamily.retract_subset_smooth (h : IsLossFamily L)
    (hidem : ∀ p z, L p 0 (L p 0 z) = L p 0 z) (hsm : ∀ p z, L p 0 z ∈ Z.smooth) :
    (h.retraction hidem).retract ⊆ ((ScBanach.const V).prod Z).smooth := by
  rintro _ ⟨q, -, rfl⟩
  change (q.1, L q.1 0 q.2) ∈ ((ScBanach.const V).prod Z).smoothLvl 0
  rw [ScBanach.prod_smoothLvl]
  refine ⟨?_, hsm q.1 q.2⟩
  change q.1 ∈ (ScBanach.constScale V).smoothLvl 0
  rw [ScBanach.constScale_smoothLvl]; exact mem_univ _

/-- **The reduction of Remark 4.1.3 (preprint 4.3)'s example**: a loss family of projections with smooth ranges
whose retract `O` carries a discontinuous lift `O → E₁` (i.e. the topologies of `O ⊆ E₀` and of
`O ⊆ E₁` differ) gives an sc-retract `O = O_∞` which is **not** an sc⁺-retract.  By Proposition 4.1.8 (preprint 4.8)
in charts (`MPolyfold.proposition_4_1_8_chart`, `MPolyfold.isScSmoothMap_toLevelOne_iff`), an
M-polyfold with a chart onto `O` then has `X₀ = X_∞` on that chart and `1₀¹ : X → X¹` not
sc-smooth, so `X¹ ≠ X` as M-polyfolds (§4.1, Remark 4.1.3 (preprint 4.3); comparison item V4.6, gap G.31). -/
theorem IsLossFamily.not_isScPlusRetract (h : IsLossFamily L)
    (hidem : ∀ p z, L p 0 (L p 0 z) = L p 0 z)
    (hdisc : ¬ ContinuousOn ((ScBanach.const V).prod Z).liftOne (h.retraction hidem).retract) :
    ¬ IsScPlusRetract ((ScBanach.const V).prod Z) univ (h.retraction hidem).retract := by
  intro hplus
  obtain ⟨-, hlift⟩ := (proposition_4_1_8 (h.retraction hidem).isScRetract).1 hplus
  exact hdisc (hlift.continuousOn (h.retraction hidem).isScRetract)

/-- **The data of Remark 4.1.3 (preprint 4.3)'s example**, the part left open: a loss family of projections on
`V ⊕ Z` with smooth ranges and a discontinuous lift of the retract into level `1`. -/
def RemarkFourThreeData (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (Z : ScBanach) : Prop :=
  ∃ (L : V → ∀ m, Z m →L[ℝ] Z m) (h : IsLossFamily L)
    (hidem : ∀ p z, L p 0 (L p 0 z) = L p 0 z),
    (∀ p z, L p 0 z ∈ Z.smooth) ∧
      ¬ ContinuousOn ((ScBanach.const V).prod Z).liftOne (h.retraction hidem).retract

/-- **Remark 4.1.3 (preprint 4.3)'s example from the data**: such data give an sc-Banach space `E`, an sc-retract
`O ⊆ E` with `O = O_∞` which is not an sc⁺-retract (Proposition 4.1.8 (preprint 4.8): `1₀¹ : O → O¹` is not
sc-smooth). -/
theorem exists_retract_smooth_not_scPlus_of_data (hd : RemarkFourThreeData V Z) :
    ∃ (E : ScBanach) (O : Set (E 0)), IsScRetract E univ O ∧ O ⊆ E.smooth ∧
      ¬ IsScPlusRetract E univ O := by
  obtain ⟨L, h, hidem, hsm, hdisc⟩ := hd
  exact ⟨_, _, (h.retraction hidem).isScRetract, h.retract_subset_smooth hidem hsm,
    h.not_isScPlusRetract hidem hdisc⟩

end Retract

end Polyfold
