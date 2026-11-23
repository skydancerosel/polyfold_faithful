import Polyfold.Chapter9.LocalPartitions
import Polyfold.Chapter9.BoundaryCover

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021; 2017 arXiv 1707.08941),
Part II, Chapter 9, §9.5, **Remark 9.5.19, 2021 p. 451** (2017: Remark 9.8), point G.153.
Numbers and pages are the 2021 text's.

# The forms `β_k ω` near `supp Θ`

In the proof of Theorem 9.5.18 (2021 pp. 450–451) the form `ω` is cut into the pieces
`ω_k = β_k ω`.  With a partition of unity defined only near `supp Θ` (Remark 9.5.19) the pieces
are forms near `supp Θ`.  The integrals of §9.5 only use the values of a form on the tangent
spaces of the sheets (`EpGroupoid.FormEval`), so the pieces may live in any space of forms with
such values.  This file records what the proof uses.

* `EP.LocalFormSystem A m Θ N ω`: spaces `Ω¹`, `Ω⁰` with values on tangent vectors (degrees
  `m + 1` and `m`), containing the classes of `Ωᵐ⁺¹_{ep,∞}(X)` and `Ωᵐ_{ep,∞}(X)`, and finitely
  many pieces `u_k ∈ Ω⁰`, `v_k ∈ Ω¹` (`u_k = β_k ω`, `v_k = d(β_k ω)`) with `∑ u_k = ω`,
  `∑ v_k = dω`, vanishing off closed saturated sets `Z_k ⊆ N(x_k)^*`, and Stokes on every sheet.
-/

set_option maxSynthPendingDepth 3

open Set Function Filter Topology MeasureTheory

noncomputable section

namespace Polyfold

universe u

open MPolyfold EpGroupoid

namespace EP

variable (A : EP.{u})

/-- **The pieces `β_k ω`, `d(β_k ω)` of the proof of Theorem 9.5.18 for a partition of unity near
`supp Θ`** (Remark 9.5.19, 2021 p. 451), `m ≥ 1`, subordinate to the saturations of the open sets
`N(x)`. -/
structure LocalFormSystem (m : ℕ) (Θ : A.Obj → ℚ) (N : A.Obj → Set A.Obj)
    (ω : A.epFormsInfty m) where
  /-- The forms of degree `m + 1` near `supp Θ`. -/
  Ω1 : Type (max 1 u)
  /-- The forms of degree `m` near `supp Θ`. -/
  Ω0 : Type (max 1 u)
  [acg1 : AddCommGroup Ω1]
  [mod1 : Module ℝ Ω1]
  [acg0 : AddCommGroup Ω0]
  [mod0 : Module ℝ Ω0]
  /-- The values of the forms of degree `m + 1`. -/
  F1 : A.X.FormEval (m + 1) Ω1
  /-- The values of the forms of degree `m`. -/
  G0 : A.X.FormEval m Ω0
  /-- The class of a form of `X`, degree `m + 1`. -/
  j1 : A.epFormsInfty (m + 1) →ₗ[ℝ] Ω1
  /-- The class of a form of `X`, degree `m`. -/
  j0 : A.epFormsInfty m →ₗ[ℝ] Ω0
  j1_ev : ∀ (η : A.epFormsInfty (m + 1)) {M : Set A.Obj}, A.X.PObj.IsSmoothSubmanifold M →
    ∀ {y : A.Obj}, y ∈ M → y ∈ supp Θ → ∀ α : Fin (m + 1) → A.X.PObj.TangentSpace,
    (∀ i, α i ∈ A.X.PObj.submanifoldTangent M y) →
    F1.ev (j1 η) α = (A.epFormsInftyEval (m + 1)).ev η α
  j0_ev : ∀ (η : A.epFormsInfty m) {M : Set A.Obj}, A.X.PObj.IsSmoothSubmanifold M →
    ∀ {y : A.Obj}, y ∈ M → y ∈ supp Θ → ∀ α : Fin m → A.X.PObj.TangentSpace,
    (∀ i, α i ∈ A.X.PObj.submanifoldTangent M y) →
    G0.ev (j0 η) α = (A.epFormsInftyEval m).ev η α
  /-- The boundary strata of the tame sheets in `supp Θ` are in the class of `G0` (as
  `EP.boundaryStratum_inter_mem_msheets`). -/
  boundaryStratum_mem : ∀ {M : Set A.Obj}, A.X.PObj.IsSubmanifoldOfDim M (m + 1) →
    A.X.PObj.HasTameInducedStructure M → M ⊆ supp Θ → ∀ {V : Set A.Obj}, IsOpen V →
    ∀ {K : Set A.Obj}, IsCompact K → K ⊆ M → A.X.PObj.boundaryStratum M ∩ V ⊆ K →
    (A.X.PObj.boundaryStratum M ∩ V).Nonempty → A.X.PObj.boundaryStratum M ∩ V ∈ G0.msheets
  /-- The finite index set. -/
  κ : Type u
  [fintype : Fintype κ]
  /-- The points `x_k`. -/
  pt : κ → A.Obj
  pt_mem : ∀ k, pt k ∈ supp Θ
  /-- The closed saturated sets `Z_k ⊇ supp β_k`. -/
  Z : κ → Set A.Obj
  isClosed_Z : ∀ k, IsClosed (Z k)
  isSaturated_Z : ∀ k, A.X.IsSaturated (Z k)
  Z_subset : ∀ k, Z k ⊆ A.X.π ⁻¹' (A.X.π '' N (pt k))
  /-- The pieces `β_k ω`. -/
  u : κ → Ω0
  /-- The pieces `d(β_k ω)`. -/
  v : κ → Ω1
  sum_u : ∑ k, u k = j0 ω
  sum_v : ∑ k, v k = j1 (A.epFormsInftyD m ω)
  /-- `d(β_k ω)` has integral `0` over the parts of the sheets off `Z_k`. -/
  integ_v_eq_zero : ∀ k {x : A.Obj} (C : A.X.OrientedTameStructure (m + 1) Θ x) (i : C.ι),
    C.M i ∈ F1.sheets → ∀ B : Set A.Obj, B ⊆ C.M i → Disjoint B (Z k) →
    F1.integ (v k) (C.M i) (C.orient i).tangent B = 0
  /-- `β_k ω` has integral `0` over the parts of the boundary sheets off `Z_k`. -/
  msInteg_u_eq_zero : ∀ k {x : A.Obj} (C : A.X.OrientedTameStructure (m + 1) Θ x) (i : C.ι),
    ∀ B : Set A.Obj, B ⊆ C.boundarySheet i → Disjoint B (Z k) →
    G0.msInteg (u k) (C.boundarySheet i) (C.boundaryOrient i).tangent B = 0
  /-- Stokes on a sheet: `∫_{(Mᵢ,oᵢ)} d(β_k ω) = ∫_{∂₁Mᵢ} β_k ω`. -/
  stokes_sheet : ∀ k {x : A.Obj} (C : A.X.OrientedTameStructure (m + 1) Θ x) (i : C.ι),
    C.M i ∈ F1.sheets →
    ((C.boundarySheet i).Nonempty → C.boundarySheet i ∈ G0.msheets) →
    IsCompact (C.M i ∩ Z k) →
    F1.integ (v k) (C.M i) (C.orient i).tangent (C.M i) =
      G0.msInteg (u k) (C.boundarySheet i) (C.boundaryOrient i).tangent (C.boundarySheet i)

attribute [instance] LocalFormSystem.acg1 LocalFormSystem.mod1 LocalFormSystem.acg0
  LocalFormSystem.mod0 LocalFormSystem.fintype

end EP

end Polyfold
