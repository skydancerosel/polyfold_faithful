import Polyfold.Chapter9.ManifoldIntegralBridge
import Polyfold.Chapter9.FunctionTimesForm

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021; 2017 arXiv 1707.08941),
Part II, Chapter 9, §9.5, pp. 449–451 (Theorems 9.5.17, 9.5.18; gap G.110).  Numbers and pages
are the 2021 text's.

# The restriction of a class of `Ωⁿ_{ep,∞}(X)` to a tame sheet, at every level

The proof of Theorem 9.5.18 integrates `ω_k = β_k ω` and `dω_k` over the sheets `Mᵢ`.  A class of
`Ωⁿ_{ep,∞}(X)` (2021 p. 372) is represented by a form on some `Xⁱ`; `dω` of a form on `X` lives on
`X¹`.  The integral of §9.5 (`FormEval.integ`) reads a class through its values on the frames of
the tangent spaces `T_yN` (`EP.epFormsInftyEval`), Part I's manifold integral reads it through the
restricted Mathlib form `formsInftyRestrict`.

## What is formalized

* `BundledMPolyfold.lowerEvIter`, `lowerEvIter_tangentMap`: the value of an evaluation on
  `T(Xⁱ)`, read on `TX`, at the tangent vectors `Tg(a)` of an sc-smooth `g : Q → X` from a
  finite-dimensional corner M-polyfold, is its value at `T(gⁱ)(a)`.
* **`EP.formsInftyRestrict_epFormsInftyToObj`**: for a sheet `N` with a corner structure and
  `a ∈ Ωᵏ_{ep,∞}(X)`, `k ≥ 1`: `a|_N(y)(v) = a(Tι(v₁), …, Tι(v_k))`, for a representative on any
  level.
* **`EP.epFormsInftyEval_integ_eq_integral`**: `∫_N a|(N, o)` (§9.5) is Part I's manifold
  integral of `a|_N` for the tangent orientation `bridgeOrientation o`, when `a|_N` has compact
  support (all classes, not only those represented on level `0`).
* `EP.formsInftyRestrict_epFormsInftySmul`: `(β·a)|_N = β·(a|_N)`.
-/

set_option maxSynthPendingDepth 3

open Set Function Filter Topology MeasureTheory Module Manifold

local notation3 "∞" => ((⊤ : ℕ∞) : WithTop ℕ∞)

local notation "𝓠" => modelWithCornersEuclideanQuadrant

noncomputable section

namespace Polyfold

universe u

open MPolyfold

/-! ### Evaluations on the lifts of a bundled M-polyfold -/

namespace BundledMPolyfold

variable {n : ℕ}

/-- Transport of an evaluation along an equality of bundled M-polyfolds. -/
def castEv {B B' : BundledMPolyfold.{u}} (h : B = B')
    (f : (Fin n → B.P.TangentSpace) → ℝ) : (Fin n → B'.P.TangentSpace) → ℝ := by
  subst h
  exact f

theorem lowerEv_castEv {B B' : BundledMPolyfold.{u}} (h : B = B')
    (f : (Fin n → B.shift.P.TangentSpace) → ℝ) :
    MPolyfold.lowerEv (P := B'.P) (castEv (congrArg BundledMPolyfold.shift h) f) =
      castEv h (MPolyfold.lowerEv (P := B.P) f) := by
  subst h
  rfl

theorem evalFamily_castForms {B B' : BundledMPolyfold.{u}} (h : B = B') (ω : B.P.scForms n) :
    MPolyfold.evalFamily (BundledMPolyfold.castForms n h ω).1 =
      castEv h (MPolyfold.evalFamily ω.1) := by
  subst h
  rfl

/-- **An evaluation on the tangent vectors of `Xⁱ`, read on the tangent vectors of `X`**
(`MPolyfold.lowerEv`, `i` times), for a bundled M-polyfold. -/
def lowerEvIter (B : BundledMPolyfold.{u}) : ∀ i : ℕ,
    ((Fin n → (B.lift i).P.TangentSpace) → ℝ) → (Fin n → B.P.TangentSpace) → ℝ
  | 0, f => f
  | i + 1, f => lowerEvIter B i (MPolyfold.lowerEv (P := (B.lift i).P) f)

end BundledMPolyfold

namespace MPolyfold

variable {M : Type u} [TopologicalSpace M] [T2Space M] [ParacompactSpace M] {Q : MPolyfold M}
  {n k : ℕ} (hcs : Q.HasCornerStructureOfDim n) {B : BundledMPolyfold.{u}} (g : ScMap Q B.P)

/-- `T(X^{i+1}) → T(Xⁱ)` carries `T(g^{i+1})(a)` to `T(gⁱ)(a)`. -/
theorem tangentLower_tangentMap_alongLift (i : ℕ) (a : Q.TangentSpace) :
    tangentLower (tangentMap (alongLift hcs g (i + 1)).isScSmoothMap a) =
      tangentMap (alongLift hcs g i).isScSmoothMap a := by
  have h1 : tangentMap (alongLift hcs g (i + 1)).isScSmoothMap a =
      tangentMap (isScSmoothMap_liftLevelOneMap (alongLift hcs g i).isScSmoothMap)
        (tangentMap hcs.isScSmoothMap_levelOne a) :=
    congrFun (tangentMap_comp (isScSmoothMap_liftLevelOneMap (alongLift hcs g i).isScSmoothMap)
      hcs.isScSmoothMap_levelOne) a
  refine (congrArg tangentLower h1).trans ?_
  refine (tangentLower_tangentMap (alongLift hcs g i).isScSmoothMap (fun _ => rfl) _).trans ?_
  exact congrArg _ (hcs.tangentLower_tangentMap_levelOne a)

/-- **The value of an evaluation on `T(Xⁱ)`, read on `TX`, at `Tg(a₁), …, Tg(a_k)`** is its
value at `T(gⁱ)(a₁), …, T(gⁱ)(a_k)`. -/
theorem lowerEvIter_tangentMap : ∀ (i : ℕ) (f : (Fin k → (B.lift i).P.TangentSpace) → ℝ)
    (a : Fin k → Q.TangentSpace),
    B.lowerEvIter i f (fun j => tangentMap g.isScSmoothMap (a j)) =
      f fun j => tangentMap (alongLift hcs g i).isScSmoothMap (a j)
  | 0, _, _ => rfl
  | i + 1, f, a => by
    change B.lowerEvIter i (MPolyfold.lowerEv (P := (B.lift i).P) f) _ = _
    rw [lowerEvIter_tangentMap i]
    exact lowerEv_eq f _ fun j => tangentLower_tangentMap_alongLift hcs g i (a j)

end MPolyfold

/-! ### The restriction of a class to a sheet -/

namespace EP

variable (A : EP.{u}) {n : ℕ}

/-- The two iterated lowerings agree (the object M-polyfold of `Xⁱ` is `(Ob X)ⁱ`). -/
theorem lowerEvIter_castEv : ∀ (i : ℕ) (f : (Fin n → (A.lift i).X.PObj.TangentSpace) → ℝ),
    A.objPolyfold.lowerEvIter i
        (BundledMPolyfold.castEv (B := (A.lift i).objPolyfold) (A.objPolyfold_lift i) f) =
      A.lowerEvIter i f
  | 0, _ => rfl
  | i + 1, f => by
    change A.objPolyfold.lowerEvIter i (MPolyfold.lowerEv (P := (A.objPolyfold.lift i).P)
      (BundledMPolyfold.castEv (B := ((A.lift i).objPolyfold).shift)
        (congrArg BundledMPolyfold.shift (A.objPolyfold_lift i)) f)) = _
    exact (congrArg (A.objPolyfold.lowerEvIter i)
      (BundledMPolyfold.lowerEv_castEv (B := (A.lift i).objPolyfold) (A.objPolyfold_lift i)
        f)).trans (lowerEvIter_castEv i _)

variable {N : Set A.Obj} [ParacompactSpace N] {hY : A.X.PObj.IsSubMPolyfold N}
  {hcs : (subPolyfold hY).HasCornerStructureOfDim n}
  [inst : ChartedSpace (EuclideanQuadrant n) N] {k : ℕ}

/-- **The restriction of a form on `Xⁱ` to a sheet is its value on the frames `Tι(v)`**
(`levelEv`): for `ω ∈ Ωᵏ_ep(Xⁱ)`, `k ≥ 1`, and a sheet of any dimension `n`. -/
theorem scFormRestrict_epFormsToObj (hn : 0 < k) (i : ℕ) (ω : A.epForms k i) (y : N)
    (v : Fin k → EuclideanSpace ℝ (Fin n)) :
    scFormRestrict k hcs i (A.epFormsToObj k i ω) y v =
      A.levelEv i ω fun j => incFrame hcs (hcs.coords y) (hcs.mem_coords y) (v j) := by
  set g : ScMap (subPolyfold hY) A.objPolyfold.P := subInclScMap hY with hg
  have hω' : A.epFormsToObj k i ω =
      BundledMPolyfold.castForms k (A.objPolyfold_lift i) (A.epFormsToForms k i ω) := rfl
  have e0 : scFormRestrict k hcs i (A.epFormsToObj k i ω) =
      formsAlong hcs g i (A.epFormsToObj k i ω) := rfl
  rw [e0, formsAlong_apply, cornerForm_apply, MPolyfold.formPullback_apply,
    ← evalFamily_eq hn (A.epFormsToObj k i ω).1]
  simp only [coe_tangentFiberMap_apply]
  rw [hω']
  refine (congrFun (BundledMPolyfold.evalFamily_castForms (B := (A.lift i).objPolyfold)
    (A.objPolyfold_lift i) (A.epFormsToForms k i ω)) _).trans ?_
  refine (lowerEvIter_tangentMap hcs g i _ _).symm.trans ?_
  exact congrFun (A.lowerEvIter_castEv i _) _

/-- **The restriction of a class of `Ωⁿ_{ep,∞}(X)` to a sheet `N` with a corner structure**
(`formsInftyRestrict`, Part I) **is its value on the frames `Tι(v)`** (`epFormsInftyEval`, §9.5),
for a representative on any level. -/
theorem formsInftyRestrict_epFormsInftyToObj (hn : 0 < k)
    (hN : A.X.PObj.IsSmoothSubmanifold N) (a : A.epFormsInfty k) (y : N)
    (v : Fin k → EuclideanSpace ℝ (Fin n)) :
    formsInftyRestrict k hcs (A.epFormsInftyToObj k a) y v =
      (A.epFormsInftyEval k).ev a
        fun j => incFrame hcs (hcs.coords y) (hcs.mem_coords y) (v j) := by
  obtain ⟨i, ω, rfl⟩ := A.exists_epFormsInftyOf_eq k a
  rw [epFormsInftyToObj_of, A.epFormsInftyEval_of k i ω]
  have e : formsInftyRestrict k hcs (A.objPolyfold.formsInftyOf k i (A.epFormsToObj k i ω)) =
      scFormRestrict k hcs i (A.epFormsToObj k i ω) := formsInftyRestrict_of hcs i _
  rw [e, A.scFormRestrict_epFormsToObj hn i ω y v]
  exact (A.epFormsLevelEval_ev k i ω (Or.inl ⟨N, y.1, hN, y.2, fun j =>
    incFrame_mem hN (hcs.coords y) (hcs.mem_coords y) (v j)⟩)).symm

/-- **`(β·a)|_N = β·(a|_N)`** for an sc-smooth function `β` constant on the orbits (2021 p. 451:
`ω_k = β_k ω`). -/
theorem formsInftyRestrict_epFormsInftySmul (hn : 0 < k)
    (hN : A.X.PObj.IsSmoothSubmanifold N) {β : A.Obj → ℝ}
    (hβ : A.X.PObj.IsScSmoothMap realPolyfold β)
    (hinv : ∀ φ : A.Mor, β (A.X.src φ) = β (A.X.tgt φ)) (a : A.epFormsInfty k) (y : N)
    (v : Fin k → EuclideanSpace ℝ (Fin n)) :
    formsInftyRestrict k hcs (A.epFormsInftyToObj k (A.epFormsInftySmul β k hβ hinv a)) y v =
      β y.1 * formsInftyRestrict k hcs (A.epFormsInftyToObj k a) y v := by
  rw [A.formsInftyRestrict_epFormsInftyToObj hn hN, A.formsInftyRestrict_epFormsInftyToObj hn hN]
  exact A.epFormsInftyEval_epFormsInftySmul hβ hinv a hN y.2 fun j =>
    incFrame_mem hN (hcs.coords y) (hcs.mem_coords y) (v j)

/-- **`∫_N a|(N, o)` is Part I's manifold integral of `a|_N`**, for every class
`a ∈ Ωⁿ_{ep,∞}(X)` whose restriction to the tame sheet `N` has compact support (the tangent
orientation is `bridgeOrientation o`). -/
theorem epFormsInftyEval_integ_eq_integral
    (hch : inst = (subPolyfold hY).cornerChartedSpace hcs) [IsManifold (𝓠 n) ∞ N] [T2Space N]
    [SigmaCompactSpace N] (hn : 0 < n) (hN : N ∈ (A.epFormsInftyEval n).sheets)
    (o : A.X.PObj.SubmanifoldOrientation N n) (a : A.epFormsInfty n)
    (hc : IsCompact (ManifoldForm.tsupport
      (formsInftyRestrict n hcs (A.epFormsInftyToObj n a)))) :
    (A.epFormsInftyEval n).integ a N o.tangent N =
      ManifoldForm.integral (bridgeOrientation hcs o)
        (formsInftyRestrict n hcs (A.epFormsInftyToObj n a)) :=
  EpGroupoid.FormEval.integ_eq_manifoldIntegral (A.epFormsInftyEval n) hch hn hN o _ _
    ((contMDiffForm_formsInftyRestrict hch _).of_le (by simp)) hc fun y v =>
    A.formsInftyRestrict_epFormsInftyToObj hn hN.1.1 a y v

end EP

end Polyfold
