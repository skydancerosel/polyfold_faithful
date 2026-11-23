import Polyfold.Chapter9.LocalFormSystem
import Polyfold.Chapter9.StokesDimOne

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021; 2017 arXiv 1707.08941),
Part II, Chapter 9, §9.5, **Remark 9.5.19, 2021 p. 451** (2017: Remark 9.8), point G.153, the
case `n = 1`.  Numbers and pages are the 2021 text's.

# The functions `β_k ω` near `supp Θ`, for a `1`-dimensional `Θ̂`

For `n = 1` the form `ω` is a function, the boundary `∂S` is a finite set of oriented points, and
the pieces `ω_k = β_k ω` of the proof of Theorem 9.5.18 (2021 pp. 450–451) are functions near
`supp Θ`.  This file records what the proof uses, as `LocalFormSystem.lean` does for `m ≥ 1`.

* `EP.LocalFormSystemDimOne A Θ N ω`: a space `Ω¹` of `1`-forms with values on tangent vectors, a
  space `Ω⁰` with values `val0` in the functions on the objects constant on the orbits, the
  classes of `Ω¹_{ep,∞}(X)` and `Ω⁰_{ep,∞}(X)`, and finitely many pieces `u_k ∈ Ω⁰`, `v_k ∈ Ω¹`
  (`u_k = β_k ω`, `v_k = d(β_k ω)`) with `∑ u_k = ω`, `∑ v_k = dω`, vanishing off closed
  saturated sets `Z_k ⊆ N(x_k)^*`, and Stokes on every sheet.
* `EP.LocalFormSystemDimOne.pointIntegration`: the integration of `Ω⁰` over oriented points,
  `∫_{{p}} a|({p}, o) = ± val0(a)(p)`.
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
`supp Θ`** (Remark 9.5.19, 2021 p. 451), `n = 1`, subordinate to the saturations of the open sets
`N(x)`. -/
structure LocalFormSystemDimOne (Θ : A.Obj → ℚ) (N : A.Obj → Set A.Obj)
    (ω : A.epFormsInfty 0) where
  /-- The forms of degree `1` near `supp Θ`. -/
  Ω1 : Type (max 1 u)
  /-- The functions near `supp Θ`. -/
  Ω0 : Type (max 1 u)
  [acg1 : AddCommGroup Ω1]
  [mod1 : Module ℝ Ω1]
  [acg0 : AddCommGroup Ω0]
  [mod0 : Module ℝ Ω0]
  /-- The values of the forms of degree `1`. -/
  F1 : A.X.FormEval (0 + 1) Ω1
  /-- The values of the functions (constant on the orbits). -/
  val0 : Ω0 →ₗ[ℝ] EpGroupoid.invariantFunctions A.X
  /-- The class of a form of `X`, degree `1`. -/
  j1 : A.epFormsInfty (0 + 1) →ₗ[ℝ] Ω1
  /-- The class of a function of `X`. -/
  j0 : A.epFormsInfty 0 →ₗ[ℝ] Ω0
  j1_ev : ∀ (η : A.epFormsInfty (0 + 1)) {M : Set A.Obj}, A.X.PObj.IsSmoothSubmanifold M →
    ∀ {y : A.Obj}, y ∈ M → y ∈ supp Θ → ∀ α : Fin (0 + 1) → A.X.PObj.TangentSpace,
    (∀ i, α i ∈ A.X.PObj.submanifoldTangent M y) →
    F1.ev (j1 η) α = (A.epFormsInftyEval (0 + 1)).ev η α
  j0_val : ∀ (η : A.epFormsInfty 0) {y : A.Obj}, y ∈ supp Θ →
    (val0 (j0 η) : A.Obj → ℝ) y = A.zeroFormEval η y
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
  sum_v : ∑ k, v k = j1 (A.epFormsInftyD 0 ω)
  /-- `d(β_k ω)` has integral `0` over the parts of the sheets off `Z_k`. -/
  integ_v_eq_zero : ∀ k {x : A.Obj} (C : A.X.OrientedTameStructure (0 + 1) Θ x) (i : C.ι),
    C.M i ∈ F1.sheets → ∀ B : Set A.Obj, B ⊆ C.M i → Disjoint B (Z k) →
    F1.integ (v k) (C.M i) (C.orient i).tangent B = 0
  /-- `β_k ω` vanishes at the points of `supp Θ` off `Z_k`. -/
  val_u_eq_zero : ∀ k {y : A.Obj}, y ∈ supp Θ → y ∉ Z k → (val0 (u k) : A.Obj → ℝ) y = 0
  /-- Stokes on a sheet whose boundary stratum has at most one point:
  `∫_{(Mᵢ,oᵢ)} d(β_k ω) = ± (β_k ω)(p)` for `∂₁Mᵢ = {p}`, and `= 0` for `∂₁Mᵢ = ∅`. -/
  stokes_sheet : ∀ k {x : A.Obj} (C : A.X.OrientedTameStructure (0 + 1) Θ x) (i : C.ι),
    C.M i ∈ F1.sheets → (C.boundarySheet i).Subsingleton → IsCompact (C.M i ∩ Z k) →
    F1.integ (v k) (C.M i) (C.orient i).tangent (C.M i) =
      EpGroupoid.pointInteg (val0 (u k) : A.Obj → ℝ) (C.boundarySheet i)
        (C.boundaryOrient i).tangent (C.boundarySheet i)

attribute [instance] LocalFormSystemDimOne.acg1 LocalFormSystemDimOne.mod1
  LocalFormSystemDimOne.acg0 LocalFormSystemDimOne.mod0 LocalFormSystemDimOne.fintype

namespace LocalFormSystemDimOne

variable {A} {Θ : A.Obj → ℚ} {N : A.Obj → Set A.Obj} {ω : A.epFormsInfty 0}
  (S : A.LocalFormSystemDimOne Θ N ω)

/-- **The integration of the functions near `supp Θ` over oriented points**:
`∫_{{p}} a|({p}, o) = ± val0(a)(p)` (as `EP.zeroFormIntegration`). -/
def pointIntegration :
    A.X.SheetIntegration (SheetNullSets.point (EpGroupoid.pointSheets A.X)) S.Ω0 :=
  (EpGroupoid.pointIntegration A.X).comap S.val0

theorem pointIntegration_integ (a : S.Ω0) (M : Set A.Obj) (g : A.Obj → A.X.PObj.OrTangent)
    (B : Set A.Obj) :
    S.pointIntegration.integ a M g B = EpGroupoid.pointInteg (S.val0 a : A.Obj → ℝ) M g B := rfl

end LocalFormSystemDimOne

end EP

end Polyfold
