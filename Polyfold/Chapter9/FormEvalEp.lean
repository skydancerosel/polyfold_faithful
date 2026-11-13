import Polyfold.Chapter9.GraphChart
import Polyfold.Chapter8.EpFormsObj

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021; 2017 arXiv 1707.08941),
Part II, Chapter 8, Definition 8.2.1 (p. 281) and Chapter 9, §9.5 (pp. 438–445): the values of
the sc-differential forms of an ep-groupoid on the tangent vectors of its submanifolds, as the
datum `EpGroupoid.FormEval` from which the integrals over oriented sheets are built (gap G.107).

# The pointwise evaluation of the sc-differential forms of an ep-groupoid

## What is formalized

* `MPolyfold.evalFamily ω α = ω_x(α₁, …, αₙ)` for a family `ω` of alternating forms on the
  tangent spaces and tangent vectors `αᵢ` over one point `x ∈ X₁` (`evalFamily_eq`); `0` if the
  vectors lie over different points, and `0` for `n = 0` (no vector, no base point).
* `alternatingMap_sum_smul`: `f(∑ᵢ Mᵢ₁ aᵢ, …, ∑ᵢ Mᵢₙ aᵢ) = det M · f(a₁, …, aₙ)`.
* `MPolyfold.continuousWithinAt_levelLift`: along a smooth finite-dimensional submanifold the
  level-`1` chart lift is continuous for the topology of `X` (the chart retraction is sc⁺).
* `EpGroupoid.epFormEval X n : X.FormEval n (X.epForms n)`: the forms `Ωⁿ_ep(X)` of Definition
  8.2.1 are a `FormEval`: linearity, the determinant rule, the invariance `(Tψ)^*ω = ω`
  (`IsMorCompatible`) and the continuity along continuous frame fields (the chart expression
  `ω_φ` is sc-smooth, hence continuous on `⊕ₙ TO ⊆ E¹ ⊕ Eⁿ`).

* `EP.formEvalInfty`: evaluations of the forms of the levels `Xⁱ` on the tangent vectors of `X`,
  compatible with the steps `Ωⁿ_ep(Xⁱ) → Ωⁿ_ep(Xⁱ⁺¹)`, give a `FormEval` of the direct limit
  `Ωⁿ_{ep,∞}(X)` (`EP.epFormsInfty`).

## Not formalized here

The evaluations of the forms of `Xⁱ`, `i ≥ 1`, on the tangent vectors of the submanifolds of
`X` (the input of `EP.formEvalInfty`): a form on `Xⁱ` is evaluated on tangent vectors of `Xⁱ`,
and the tangent vectors of a submanifold `N ⊆ X_∞` of `X` must first be lifted along
`tangentLower` (a submanifold of `X` is one of `Xⁱ`, with the same tangent spaces and the same
continuous frame fields).
-/

set_option maxSynthPendingDepth 3

open Set Function Filter Topology Module

noncomputable section

namespace Polyfold

universe u

/-- **The determinant rule for an alternating `n`-form on `n` combinations of `n` vectors.** -/
theorem alternatingMap_sum_smul {V : Type*} [AddCommGroup V] [Module ℝ V] {n : ℕ}
    (f : V [⋀^Fin n]→ₗ[ℝ] ℝ) (a : Fin n → V) (M : Matrix (Fin n) (Fin n) ℝ) :
    f (fun j => ∑ i, M i j • a i) = M.det * f a := by
  classical
  set L : (Fin n → ℝ) →ₗ[ℝ] V := Fintype.linearCombination ℝ a with hL
  set g : (Fin n → ℝ) [⋀^Fin n]→ₗ[ℝ] ℝ := f.compLinearMap L with hg
  have h := AlternatingMap.eq_smul_basis_det (Pi.basisFun ℝ (Fin n)) g
  have h1 := congrArg (fun F : (Fin n → ℝ) [⋀^Fin n]→ₗ[ℝ] ℝ => F fun j i => M i j) h
  simp only [AlternatingMap.smul_apply, smul_eq_mul] at h1
  rw [Pi.basisFun_det_apply] at h1
  have e1 : g (fun j i => M i j) = f (fun j => ∑ i, M i j • a i) := by
    simp only [hg, AlternatingMap.compLinearMap_apply, hL]
    congr 1
  have e2 : g (fun i => Pi.basisFun ℝ (Fin n) i) = f a := by
    simp only [hg, AlternatingMap.compLinearMap_apply, hL]
    congr 1
    funext j
    simp [Pi.basisFun_apply, Fintype.linearCombination_apply_single]
  have e3 : (Matrix.of fun j i => M i j).det = M.det := by
    rw [← Matrix.det_transpose M]; rfl
  rw [e1, e2, e3] at h1
  rw [h1]; ring

namespace MPolyfold

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {P : MPolyfold X}
  {n : ℕ}

open scoped Classical in
/-- **`ω(α₁, …, αₙ)`** for a family `ω` of alternating `n`-forms on the tangent spaces `T_xX`,
`x ∈ X₁`, and tangent vectors `αᵢ`: the value `ω_x(α)` if all `αᵢ` lie over the base point `x`
of `α₁`, and `0` otherwise (also for `n = 0`). -/
def evalFamily (ω : ∀ x : P.Level 1, P.tangentFiber x [⋀^Fin n]→ₗ[ℝ] ℝ)
    (α : Fin n → P.TangentSpace) : ℝ :=
  if hn : 0 < n then
    if h : ∀ i, α i ∈ P.tangentFiber (P.tangentProj (α ⟨0, hn⟩)) then
      ω (P.tangentProj (α ⟨0, hn⟩)) fun i => ⟨α i, h i⟩
    else 0
  else 0

theorem evalFamily_eq (hn : 0 < n) (ω : ∀ x : P.Level 1, P.tangentFiber x [⋀^Fin n]→ₗ[ℝ] ℝ)
    {x : P.Level 1} (a : Fin n → P.tangentFiber x) :
    evalFamily ω (fun i => (a i : P.TangentSpace)) = ω x a := by
  have hx : P.tangentProj (a ⟨0, hn⟩ : P.TangentSpace) = x := (a ⟨0, hn⟩).2
  have h : ∀ i, (a i : P.TangentSpace) ∈
      P.tangentFiber (P.tangentProj (a ⟨0, hn⟩ : P.TangentSpace)) := fun i => by
    rw [hx]; exact (a i).2
  rw [evalFamily, dif_pos hn, dif_pos h]
  exact altFamily_congr ω hx _ _ fun _ => rfl

theorem evalFamily_of_eq_zero (hn : n = 0)
    (ω : ∀ x : P.Level 1, P.tangentFiber x [⋀^Fin n]→ₗ[ℝ] ℝ) (α : Fin n → P.TangentSpace) :
    evalFamily ω α = 0 := by
  rw [evalFamily, dif_neg (by omega)]

theorem evalFamily_add (ω τ : ∀ x : P.Level 1, P.tangentFiber x [⋀^Fin n]→ₗ[ℝ] ℝ)
    (α : Fin n → P.TangentSpace) :
    evalFamily (ω + τ) α = evalFamily ω α + evalFamily τ α := by
  unfold evalFamily
  split_ifs <;> simp

theorem evalFamily_smul (c : ℝ) (ω : ∀ x : P.Level 1, P.tangentFiber x [⋀^Fin n]→ₗ[ℝ] ℝ)
    (α : Fin n → P.TangentSpace) : evalFamily (c • ω) α = c * evalFamily ω α := by
  unfold evalFamily
  split_ifs <;> simp

/-- Tangent vectors over one point `y`, as elements of the tangent space `T_xX` of the level-`1`
point `x` over `y`. -/
theorem exists_fiber_lift {y : X} {α : Fin n → P.TangentSpace}
    (hα : ∀ i, P.levelVal 1 (P.tangentProj (α i)) = y) (hn : 0 < n) :
    ∃ (x : P.Level 1) (a : Fin n → P.tangentFiber x), P.levelVal 1 x = y ∧
      ∀ i, (a i : P.TangentSpace) = α i :=
  ⟨P.tangentProj (α ⟨0, hn⟩), fun i => ⟨α i, level_ext ((hα i).trans (hα ⟨0, hn⟩).symm)⟩,
    hα ⟨0, hn⟩, fun _ => rfl⟩

/-- **The determinant rule for `evalFamily`**, with the combinations read in a chart. -/
theorem evalFamily_det (ω : ∀ x : P.Level 1, P.tangentFiber x [⋀^Fin n]→ₗ[ℝ] ℝ) {y : X}
    {φ : MChart X} (hφ : P.IsChart φ) (hyφ : y ∈ φ.source) (α β : Fin n → P.TangentSpace)
    (hα : ∀ i, P.levelVal 1 (P.tangentProj (α i)) = y)
    (hβ : ∀ i, P.levelVal 1 (P.tangentProj (β i)) = y) (M : Matrix (Fin n) (Fin n) ℝ)
    (h : ∀ j, chartVec hφ (β j) = ∑ i, M i j • chartVec hφ (α i)) :
    evalFamily ω β = M.det * evalFamily ω α := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · rw [evalFamily_of_eq_zero hn, evalFamily_of_eq_zero hn, mul_zero]
  obtain ⟨x, a, hx, ha⟩ := exists_fiber_lift hα hn
  have hb' : ∀ i, β i ∈ P.tangentFiber x := fun i => level_ext ((hβ i).trans hx.symm)
  set b : Fin n → P.tangentFiber x := fun i => ⟨β i, hb' i⟩ with hb
  have hxφ : P.levelVal 1 x ∈ φ.source := by rw [hx]; exact hyφ
  have hab : ∀ j, b j = ∑ i, M i j • a i := fun j => by
    apply (tangentFiberLinearEquiv hφ hxφ).injective
    apply Subtype.ext
    rw [map_sum, Submodule.coe_sum, coe_tangentFiberLinearEquiv_apply]
    refine (h j).trans (Finset.sum_congr rfl fun i _ => ?_)
    rw [map_smul, Submodule.coe_smul, coe_tangentFiberLinearEquiv_apply, ha i]
    rfl
  have e1 : evalFamily ω β = ω x b := evalFamily_eq hn ω b
  have e2 : evalFamily ω α = ω x a := by
    rw [← evalFamily_eq hn ω a]; congr 1; funext i; exact (ha i).symm
  rw [e1, e2, show b = fun j => ∑ i, M i j • a i from funext hab]
  exact alternatingMap_sum_smul (ω x) a M

/-- **Along a smooth finite-dimensional submanifold the level-`1` chart lift is continuous** for
the topology of `X`: near `z₀ ∈ N` it is the lift `1₀¹ ∘ t` of the chart sc⁺-retraction `t`
onto `φ(W ∩ N)`, an sc-smooth map into `E¹`. -/
theorem continuousWithinAt_levelLift {N : Set X} (hN : P.IsSmoothSubmanifold N) {φ : MChart X}
    (hφ : P.IsChart φ) {K : Set X} (hK : K ⊆ N ∩ φ.source) {z₀ : X} (hz₀ : z₀ ∈ K) :
    ContinuousWithinAt (fun z => levelLift φ 1 z) K z₀ := by
  have hz₀N : z₀ ∈ N := (hK hz₀).1
  have hz₀φ : z₀ ∈ φ.source := (hK hz₀).2
  set d := hN.data hz₀N
  have hz₀V : z₀ ∈ d.V := hN.mem_data_V hz₀N
  obtain ⟨t, ht, htp⟩ := exists_plusRetraction hφ d hz₀N hz₀V
  have hcont : ContinuousOn t.plusLift t.U :=
    htp.isScSmooth_lift.isSc1.isSc0.continuousOn_base
  have hmem : ∀ z ∈ K ∩ d.toSubData.shrink φ, φ z ∈ t.retract := fun z hz => by
    rw [ht]; exact ⟨z, ⟨hz.2, (hK hz.1).1⟩, rfl⟩
  have heq : ∀ z ∈ K ∩ d.toSubData.shrink φ, levelLift φ 1 z = t.plusLift (φ z) := by
    intro z hz
    have hzV : z ∈ d.V := d.toSubData.shrink_subset_V φ hz.2
    obtain ⟨h1, -, -⟩ := chartTangent_eq_range hφ d ht (hK hz.1).1 hzV (hK hz.1).2
    apply φ.model.E.toBase_injective 1
    rw [h1, ScRetraction.toBase_plusLift_of_mem_retract htp (hmem z hz)]
  have hsh : d.toSubData.shrink φ ∈ 𝓝 z₀ :=
    (d.toSubData.isOpen_shrink φ).mem_nhds (d.toSubData.mem_shrink φ hz₀N hz₀V hz₀φ)
  have hz₀' : z₀ ∈ K ∩ d.toSubData.shrink φ := ⟨hz₀, mem_of_mem_nhds hsh⟩
  have h1 : ContinuousWithinAt (fun z => t.plusLift (φ z)) (K ∩ d.toSubData.shrink φ) z₀ :=
    (hcont (φ z₀) (t.retract_subset (hmem z₀ hz₀'))).comp
      ((φ.continuousOn_toFun z₀ hz₀φ).mono fun z hz => (hK hz.1).2)
      fun z hz => t.retract_subset (hmem z hz)
  have h2 : ContinuousWithinAt (fun z => levelLift φ 1 z) (K ∩ d.toSubData.shrink φ) z₀ :=
    h1.congr heq (heq z₀ hz₀')
  exact (continuousWithinAt_inter hsh).1 h2

/-- **Continuity of `evalFamily` of an sc-form along a continuous frame field of a
submanifold.** -/
theorem continuousOn_evalFamily {ω : ∀ x : P.Level 1, P.tangentFiber x [⋀^Fin n]→ₗ[ℝ] ℝ}
    (hω : P.IsScForm n ω) {N : Set X} (hN : P.IsSmoothSubmanifold N) {φ : MChart X}
    (hφ : P.IsChart φ) {K : Set X} (hK : K ⊆ N ∩ φ.source) (e : X → Fin n → P.TangentSpace)
    (he : ∀ z ∈ K, ∀ i, P.levelVal 1 (P.tangentProj (e z i)) = z)
    (hc : ContinuousOn (fun z i => chartVec hφ (e z i)) K) :
    ContinuousOn (fun z => evalFamily ω (e z)) K := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · simp only [evalFamily_of_eq_zero hn]; exact continuousOn_const
  set F : X → (φ.model.E.whitney n) 0 := fun z =>
    ScBanach.whitneyMk (levelLift φ 1 z) fun i => chartVec hφ (e z i) with hF
  have hFc : ContinuousOn F K := fun z hz =>
    (continuousWithinAt_levelLift hN hφ hK hz).prodMk
      ((φ.model.E.fiberPackL 0 n).continuous.continuousAt.comp_continuousWithinAt (hc z hz))
  have key : ∀ z ∈ K, F z ∈ retractWhitney φ.model.E φ.model.C φ.model.O n ∧
      chartForm hφ ω (F z) = evalFamily ω (e z) := by
    intro z hz
    obtain ⟨x, a, hx, ha⟩ := exists_fiber_lift (he z hz) hn
    have hxφ : P.levelVal 1 x ∈ φ.source := by rw [hx]; exact (hK hz).2
    have hq1 : (F z).1 = levelLift φ 1 (P.levelVal 1 x) := by rw [hx]
    have hq2 : ∀ i, ScBanach.whitneyVec (F z) i = (tangentChartMap hφ (a i)).2 := fun i => by
      rw [hF, ScBanach.whitneyVec_mk, ha i]; rfl
    refine ⟨⟨by rw [hq1]; exact levelLift_mem_lvlSet_one hφ hxφ, fun i => ?_⟩, ?_⟩
    · have : ((F z).1, ScBanach.whitneyVec (F z) i) = tangentChartMap hφ (a i) :=
        Prod.ext (by rw [hq1, tangentChartMap_fst_of_mem_fiber hφ hxφ (a i).2]) (hq2 i)
      rw [this]
      exact tangentChartMap_mem hφ (mem_tangentChartSet_of_mem_fiber hxφ (a i).2)
    · rw [chartForm_eq hφ ω hxφ a hq1 hq2, ← evalFamily_eq hn ω a]
      congr 1; funext i; exact ha i
  have hcf : ContinuousOn (chartForm hφ ω)
      (retractWhitney φ.model.E φ.model.C φ.model.O n) :=
    (hω hφ).continuousOn (φ.model.isScRetract.whitney n)
  exact (hcf.comp hFc fun z hz => (key z hz).1).congr fun z hz => ((key z hz).2).symm

end MPolyfold

namespace EpGroupoid

variable {Obj Mor : Type u} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor]

/-- **The invariance of `evalFamily` under the tangent maps of the morphisms**, for a family
compatible with the morphisms (Definition 8.2.1). -/
theorem evalFamily_tangentMor (X : EpGroupoid Obj Mor) {n : ℕ}
    {ω : ∀ x : X.PObj.Level 1, X.PObj.tangentFiber x [⋀^Fin n]→ₗ[ℝ] ℝ}
    (hω : X.IsMorCompatible n ω) {y : Obj} (ψ : Mor) (hψ : X.src ψ = y)
    (α : Fin n → X.PObj.TangentSpace)
    (hα : ∀ i, X.PObj.levelVal 1 (X.PObj.tangentProj (α i)) = y) :
    MPolyfold.evalFamily ω (fun i => X.tangentMor ψ (α i)) = MPolyfold.evalFamily ω α := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · rw [MPolyfold.evalFamily_of_eq_zero hn, MPolyfold.evalFamily_of_eq_zero hn]
  obtain ⟨x, a, hx, ha⟩ := MPolyfold.exists_fiber_lift hα hn
  have hxs : X.PObj.levelVal 1 x = X.src ψ := hx.trans hψ.symm
  have hψ1 : ψ ∈ X.PMor.levelSet 1 :=
    (X.mem_levelSet_src_iff ψ 1).1 (hxs ▸ MPolyfold.levelVal_mem x)
  have ht1 : X.tgt ψ ∈ X.PObj.levelSet 1 := by
    have h := X.levelVal_tangentProj_tangentMor hψ1 (α := α ⟨0, hn⟩) ((hα _).trans hψ.symm)
    rw [← h]; exact MPolyfold.levelVal_mem _
  set x' : X.PObj.Level 1 := X.PObj.levelMk 1 (X.tgt ψ) ht1
  have hx' : X.PObj.levelVal 1 x' = X.tgt ψ := rfl
  have e1 : MPolyfold.evalFamily ω (fun i => X.tangentMor ψ (α i)) =
      ω x' fun i => X.tangentMorCLE hψ1 hxs hx' (a i) := by
    rw [← MPolyfold.evalFamily_eq hn ω]
    congr 1; funext i
    rw [X.tangentMorCLE_apply hψ1 hxs hx' (a i), ha i]
  have e2 : MPolyfold.evalFamily ω α = ω x a := by
    rw [← MPolyfold.evalFamily_eq hn ω a]; congr 1; funext i; exact (ha i).symm
  rw [e1, e2]
  exact IsMorCompatible.apply X hω hψ1 hxs hx' a

/-- **The sc-differential `n`-forms `Ωⁿ_ep(X)` of an ep-groupoid (Definition 8.2.1, p. 281) are
evaluated pointwise** (`FormEval`): `ev ω α = ω_x(α₁, …, αₙ)` for tangent vectors over one point
`x ∈ X₁` (`MPolyfold.evalFamily`; for `n = 0` the value is `0`). -/
def epFormEval (X : EpGroupoid Obj Mor) (n : ℕ) : X.FormEval n (X.epForms n) where
  ev ω α := MPolyfold.evalFamily ω.1 α
  ev_add ω τ α := MPolyfold.evalFamily_add ω.1 τ.1 α
  ev_smul c ω α := MPolyfold.evalFamily_smul c ω.1 α
  ev_det ω _ _ _ _ _ hφ hyφ α β hα hβ M h :=
    MPolyfold.evalFamily_det ω.1 hφ hyφ α β (fun i => (hα i).1) (fun i => (hβ i).1) M h
  ev_mor ω _ _ _ _ ψ hψ α hα := X.evalFamily_tangentMor ω.2.2 ψ hψ α fun i => (hα i).1
  ev_continuousOn ω _ hN _ hφ _ hK e he hc :=
    MPolyfold.continuousOn_evalFamily ω.2.1 hN hφ hK e (fun z hz i => (he z hz i).1) hc

@[simp] theorem epFormEval_ev (X : EpGroupoid Obj Mor) (n : ℕ) (ω : X.epForms n)
    (α : Fin n → X.PObj.TangentSpace) :
    (X.epFormEval n).ev ω α = MPolyfold.evalFamily ω.1 α := rfl

/-- `ev ω α = ω_x(α)` for `n ≥ 1` and tangent vectors `αᵢ ∈ T_xX`. -/
theorem epFormEval_ev_eq (X : EpGroupoid Obj Mor) {n : ℕ} (hn : 0 < n) (ω : X.epForms n)
    {x : X.PObj.Level 1} (a : Fin n → X.PObj.tangentFiber x) :
    (X.epFormEval n).ev ω (fun i => (a i : X.PObj.TangentSpace)) = ω.1 x a :=
  MPolyfold.evalFamily_eq hn ω.1 a

/-- The evaluation of a `FormEval`, as a linear map into the functions of the frames. -/
def FormEval.evₗ {X : EpGroupoid Obj Mor} {n : ℕ} {Ω : Type*} [AddCommGroup Ω] [Module ℝ Ω]
    (E : X.FormEval n Ω) : Ω →ₗ[ℝ] ((Fin n → X.PObj.TangentSpace) → ℝ) where
  toFun := E.ev
  map_add' ω τ := funext fun α => E.ev_add ω τ α
  map_smul' c ω := funext fun α => E.ev_smul c ω α

end EpGroupoid

namespace EP

variable (A : EP.{u}) {n : ℕ}

/-- Evaluations on the forms of the levels `Xⁱ`, compatible with the steps
`Ωⁿ_ep(Xⁱ) → Ωⁿ_ep(Xⁱ⁺¹)`, are compatible with the maps of the directed system. -/
theorem formEval_epFormsMap (E : ∀ i, A.X.FormEval n (A.epForms n i))
    (hE : ∀ i (ω : A.epForms n i) α, (E (i + 1)).ev (A.epFormsStep n i ω) α = (E i).ev ω α)
    {i j : ℕ} (h : i ≤ j) (ω : A.epForms n i) (α : Fin n → A.X.PObj.TangentSpace) :
    (E j).ev (A.epFormsMap n i j h ω) α = (E i).ev ω α := by
  induction j, h using Nat.le_induction with
  | base => rw [epFormsMap_self]; rfl
  | succ j h ih => rw [epFormsMap_succ A n h, LinearMap.comp_apply, hE, ih]

/-- **From the levels to `Ωⁿ_{ep,∞}(X)`**: evaluations `E i` of the forms of `Xⁱ` on the tangent
vectors of `X`, compatible with the steps of the directed system (a form on `Xⁱ` and its
pull-back to `Xⁱ⁺¹` have the same values), give an evaluation of the classes in the direct limit
`Ωⁿ_{ep,∞}(X)` (2021 p. 372), with `ev [ω] = (E i).ev ω` (`formEvalInfty_of`). -/
def formEvalInfty (E : ∀ i, A.X.FormEval n (A.epForms n i))
    (hE : ∀ i (ω : A.epForms n i) α, (E (i + 1)).ev (A.epFormsStep n i ω) α = (E i).ev ω α) :
    A.X.FormEval n (A.epFormsInfty n) where
  ev := Module.DirectLimit.lift ℝ ℕ (fun i => ↥(A.epForms n i)) (A.epFormsMap n)
    (fun i => (E i).evₗ) fun i j h ω => funext fun α => A.formEval_epFormsMap E hE h ω α
  ev_add ω τ α := congrFun (LinearMap.map_add _ ω τ) α
  ev_smul c ω α := congrFun (LinearMap.map_smul _ c ω) α
  ev_det a N hN y hy φ hφ hyφ α β hα hβ M h := by
    obtain ⟨i, ω, rfl⟩ := A.exists_epFormsInftyOf_eq n a
    rw [Module.DirectLimit.lift_of]
    exact (E i).ev_det ω hN hy hφ hyφ α β hα hβ M h
  ev_mor a N hN y hy ψ hψ α hα := by
    obtain ⟨i, ω, rfl⟩ := A.exists_epFormsInftyOf_eq n a
    rw [Module.DirectLimit.lift_of]
    exact (E i).ev_mor ω hN hy ψ hψ α hα
  ev_continuousOn a N hN φ hφ K hK e he hc := by
    obtain ⟨i, ω, rfl⟩ := A.exists_epFormsInftyOf_eq n a
    rw [Module.DirectLimit.lift_of]
    exact (E i).ev_continuousOn ω hN hφ hK e he hc

theorem formEvalInfty_of (E : ∀ i, A.X.FormEval n (A.epForms n i))
    (hE : ∀ i (ω : A.epForms n i) α, (E (i + 1)).ev (A.epFormsStep n i ω) α = (E i).ev ω α)
    (i : ℕ) (ω : A.epForms n i) (α : Fin n → A.X.PObj.TangentSpace) :
    (A.formEvalInfty E hE).ev (A.epFormsInftyOf n i ω) α = (E i).ev ω α := by
  change (Module.DirectLimit.lift ℝ ℕ (fun i => ↥(A.epForms n i)) (A.epFormsMap n)
    (fun i => (E i).evₗ) _ (A.epFormsInftyOf n i ω)) α = _
  rw [Module.DirectLimit.lift_of]; rfl

end EP

end Polyfold
