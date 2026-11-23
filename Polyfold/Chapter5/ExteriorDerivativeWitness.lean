import Polyfold.Chapter5.Poincare

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part I, §4.4,
Definition 4.4.1 (p. 195) and the exterior derivative (p. 197): **a nonzero sc-differential
form of degree `1`**, `df` for the coordinate function `f(y) = y` on the M-polyfold `ℝ`.

The file sits in Chapter 5 because it uses the forms of a relatively open local model
(`relOpenForm`, `Chapter5/Poincare.lean`).

## What is formalized (namespace `Polyfold.FormsWitness`)

* `extD_relOpenForm_apply`: on the M-polyfold `O` of a relatively open local model (one chart
  `id`), the exterior derivative of the form with local representative `τ₀` is the local
  exterior derivative `ambientD O τ₀` read in the chart (the computation inside
  `hasPoincare_relOpen`).
* `realModel`: `ℝ` as a relatively open local model; `realPolyfold`, its M-polyfold.
* `coordForm : Ω⁰(ℝ)`, the `0`-form `f(y) = y` (`coordForm_mem_scForms`, `coordForm_apply`).
* **`extD_coordForm_apply`**: `df(x)(α) = h`, where `Tφ¹(α) = (φ(x), h)`.
* **`exists_extD_coordForm_ne_zero`**: `df ∈ Ω¹(ℝ¹)` and `df ≠ 0`: a nonzero witness for
  Definition 4.4.1 in degree `1` (row V4.81).
-/

set_option maxSynthPendingDepth 3

open Set Function

noncomputable section

namespace Polyfold

namespace FormsWitness

open MPolyfold

section General

variable {M : LocalModel} (hM : IsRelOpenInQuadrant M.E M.C M.O) (hne : M.O.Nonempty) {k : ℕ}

include hM in
/-- **`d` of a form given by a local representative on a relatively open local model**: in the
chart `id`, `dτ(x)(α₀, …, α_k) = d τ₀(φ(x), h₀, …, h_k)` with the ambient local exterior
derivative of p. 197. -/
theorem extD_relOpenForm_apply (τ₀ : (M.E.whitney k) 0 → ℝ) (hτA : IsAmbientScForm M.E M.O k τ₀)
    (x : (M.toMPolyfold hne).shift.Level 1)
    (α : Fin (k + 1) → (M.toMPolyfold hne).shift.tangentFiber x) :
    extD (relOpenForm hne τ₀ hτA) x α =
      ambientD M.O τ₀ (ScBanach.whitneyMk
        (levelLift (levelChart (M.selfChart_isChart' hne)
          ((M.toMPolyfold hne).shift.levelVal 1 x)) 1 ((M.toMPolyfold hne).shift.levelVal 1 x))
        fun i => (tangentChartMap ((M.toMPolyfold hne).shift_isChart
          (M.selfChart_isChart' hne) ((M.toMPolyfold hne).shift.levelVal 1 x)) (α i)).2) := by
  have hφ := M.selfChart_isChart' hne
  have hτ := relOpenForm_mem_scForms hM hne _ hτA
  set y₀ := (M.toMPolyfold hne).shift.levelVal 1 x
  have hx : (M.toMPolyfold hne).shift.levelVal 1 x ∈ (levelChart hφ y₀).source := mem_univ _
  have hτ' : (M.toMPolyfold hne).IsScForm k (relOpenForm hne _ hτA) := hτ
  rw [extD_apply hφ hτ' y₀ hx α]
  have hmem := whitneyMk_tangentChartMap_mem hφ y₀ hx α
  have hQ := ScBanach.mem_whitneySet.2 hmem.1
  unfold chartD
  refine (retractD_eq_ambientD hM _ (chartRetraction_retract _) (hτ'.isRetractScForm hφ)
    hQ).trans ?_
  exact ambientD_congr (hM.whitneySet k).isScDomain hτA.isScSmooth.isSc1
    (fun p hp => (chartForm_relOpenForm hM hne _ hτA hp).symm) hQ

end General

/-! ### The M-polyfold `ℝ` and the coordinate function -/

/-- The sc-Banach space `ℝ` (constant scale). -/
abbrev realE : ScBanach := ScBanach.const ℝ

lemma realE_relOpen : IsRelOpenInQuadrant realE univ univ :=
  ⟨isPartialQuadrant_univ _, univ, isOpen_univ, (inter_univ _).symm⟩

/-- `ℝ` as a relatively open local model `(ℝ, ℝ, ℝ)`. -/
abbrev realModel : LocalModel := ⟨realE, univ, univ, realE_relOpen.isScRetract⟩

lemma realModel_relOpen : IsRelOpenInQuadrant realModel.E realModel.C realModel.O :=
  realE_relOpen

lemma realModel_nonempty : realModel.O.Nonempty := univ_nonempty

/-- The M-polyfold `ℝ`. -/
abbrev realPolyfold : MPolyfold realModel.O := realModel.toMPolyfold realModel_nonempty

/-- `(y, ·) ↦ y` on `⊕₀ Tℝ = ℝ¹`, an sc-operator. -/
def coordOp : ScOperator (realE.whitney 0) realE where
  lvl m := ContinuousLinearMap.fst ℝ (realE.shift m) ((realE.fiberPow 0) m)
  incl_comm _ _ := rfl

/-- The local representative `(y, ·) ↦ y`. -/
def coordFun : (realModel.E.whitney 0) 0 → ℝ := fun q => coordOp 0 q

lemma coordOp_isAmbientScForm : IsAmbientScForm realModel.E realModel.O 0 coordFun where
  isScSmooth := coordOp.isScSmooth (realE_relOpen.whitneySet 0).isScDomain
  alternating z _ := ⟨AlternatingMap.constOfIsEmpty ℝ _ (Fin 0) (z : ℝ), fun _ => rfl⟩

/-- **The coordinate function `f(y) = y` as a `0`-form** on the M-polyfold `ℝ`. -/
def coordForm : ∀ x : realPolyfold.Level 1, realPolyfold.tangentFiber x [⋀^Fin 0]→ₗ[ℝ] ℝ :=
  relOpenForm realModel_nonempty coordFun coordOp_isAmbientScForm

theorem coordForm_mem_scForms : coordForm ∈ realPolyfold.scForms 0 :=
  relOpenForm_mem_scForms realModel_relOpen realModel_nonempty _ coordOp_isAmbientScForm

/-- The derivative of `(y, ·) ↦ y` is `(h, ·) ↦ h`. -/
lemma scDeriv_coordOp {p : (realE.whitney 0) 1}
    (hp : p ∈ (realE.whitney 0).lvlSet (realE.whitneySet 0 univ) 1) :
    scDeriv (F := ScBanach.const ℝ) (realE.whitneySet 0 univ) coordFun p = coordOp 0 := by
  have hD := (realE_relOpen.whitneySet 0).isScDomain
  refine (coordOp.isScSmooth hD).isSc1.scDeriv_eq_of_hasFDerivWithinAt hp
    (hD.uniqueDiffWithinAt 1 p hp) ?_
  exact ((coordOp 0).comp ((realE.whitney 0).toBase 1)).hasFDerivAt.hasFDerivWithinAt

/-- **`df(x)(α) = h`** for `f(y) = y`, where `Tφ¹(α) = (φ(x), h)` in the chart `id`. -/
theorem extD_coordForm_apply (x : realPolyfold.shift.Level 1)
    (α : Fin 1 → realPolyfold.shift.tangentFiber x) :
    extD coordForm x α =
      (tangentChartMap (realPolyfold.shift_isChart (realModel.selfChart_isChart' realModel_nonempty)
        (realPolyfold.shift.levelVal 1 x)) (α 0)).2 := by
  refine (extD_relOpenForm_apply realModel_relOpen realModel_nonempty coordFun
    coordOp_isAmbientScForm x α).trans ?_
  rw [ambientD_apply, Fin.sum_univ_one, Fin.val_zero, pow_zero, one_mul]
  have hp : ((ScBanach.whitneyMk (E := realE.shift)
      (levelLift (levelChart (realModel.selfChart_isChart' realModel_nonempty)
        (realPolyfold.shift.levelVal 1 x)) 1 (realPolyfold.shift.levelVal 1 x))
      fun i => (tangentChartMap (realPolyfold.shift_isChart
        (realModel.selfChart_isChart' realModel_nonempty)
        (realPolyfold.shift.levelVal 1 x)) (α i)).2).1,
      realE.fiberPackL 1 0 ((0 : Fin 1).removeNth (ScBanach.whitneyVec (ScBanach.whitneyMk
        (E := realE.shift) (levelLift (levelChart (realModel.selfChart_isChart' realModel_nonempty)
          (realPolyfold.shift.levelVal 1 x)) 1 (realPolyfold.shift.levelVal 1 x))
        fun i => (tangentChartMap (realPolyfold.shift_isChart
          (realModel.selfChart_isChart' realModel_nonempty)
          (realPolyfold.shift.levelVal 1 x)) (α i)).2)))) ∈
      (realE.whitney 0).lvlSet (realE.whitneySet 0 univ) 1 := by
    exact ⟨mem_univ _, mem_univ _⟩
  rw [scDeriv_coordOp hp]
  rfl

/-- **A nonzero sc-differential `1`-form** (Definition 4.4.1 in degree `1`, 2021 p. 195):
for `f(y) = y` on the M-polyfold `ℝ`, `df ∈ Ω¹(ℝ¹)` and `df ≠ 0`. -/
theorem exists_extD_coordForm_ne_zero :
    extD coordForm ∈ realPolyfold.shift.scForms 1 ∧ extD coordForm ≠ 0 := by
  refine ⟨extD_mem_scForms coordForm_mem_scForms, fun h0 => ?_⟩
  have hφ := realModel.selfChart_isChart' realModel_nonempty
  obtain ⟨y, hy⟩ := realPolyfold.exists_mem_levelSet_one (⟨0, mem_univ _⟩ : realModel.O)
  obtain ⟨z, hz⟩ := realPolyfold.shift.exists_mem_levelSet_one (realPolyfold.levelMk 1 y hy)
  set x : realPolyfold.shift.Level 1 := realPolyfold.shift.levelMk 1 z hz
  have hχ := realPolyfold.shift_isChart hφ (realPolyfold.shift.levelVal 1 x)
  have hx : realPolyfold.shift.levelVal 1 x ∈
      (levelChart hφ (realPolyfold.shift.levelVal 1 x)).source := mem_univ _
  set v : (levelChart hφ (realPolyfold.shift.levelVal 1 x)).model.E 0 := (1 : ℝ) with hv
  have hmem : v ∈ tangentFiberModel hχ hx := by
    change v ∈ tangentSpace _ _ _ _
    exact (Set.eq_univ_iff_forall.1 (tangentSpace_relOpen realModel_relOpen.shift
      (x := levelLift (levelChart hφ (realPolyfold.shift.levelVal 1 x)) 1
        (realPolyfold.shift.levelVal 1 x)) trivial)) v
  set α : Fin 1 → realPolyfold.shift.tangentFiber x :=
    fun _ => (tangentFiberEquiv hχ hx).symm ⟨v, hmem⟩
  have h1 := extD_coordForm_apply x α
  have h2 : (tangentChartMap hχ (α 0).1).2 = v := by
    rw [← coe_tangentFiberEquiv_apply hχ hx, Equiv.apply_symm_apply]
  have h3 : extD coordForm x α = 0 := by rw [h0]; rfl
  rw [h1, h2] at h3
  exact one_ne_zero (show (1 : ℝ) = 0 from h3)

end FormsWitness

end Polyfold
