import Polyfold.Chapter11.GapP2_H4Compat
import Polyfold.Chapter11.GapP2_B2_EquivForms
import Polyfold.Chapter11.GapP2_B2_EquivFormsInfty
import Polyfold.Chapter11.BranchedEquivalenceTangent
import Polyfold.Chapter9.GapP2_E3_FormEvalInfty

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021; 2017 arXiv 1707.08941),
Part II: Definition 8.2.1 (p. 281), §11.2 (Definition 11.2.3, Lemma 11.2.4, pp. 527–529) and
§11.4 "Equivalences and Integration" (pp. 542–546), gap G.131.  Numbers and pages are the 2021
text's.

# The evaluations of forms are compatible with the pull-back along an equivalence

Instances of `EpGroupoid.FormEval.IsPullback` (`GapP2_H4Compat.lean`):

* `MPolyfold.evalFamily_formPullback`: `(f^*ω)(α₁, …, αₙ) = ω(Tf α₁, …, Tf αₙ)` for tangent
  vectors over one point (the definition of the pull-back, 2021 p. 198).
* `EpGroupoid.epFormEval_ev_formPullback` and
  **`EpFunctor.IsEquivalence.epFormEval_isPullback`**: the evaluation of the forms `Ωⁿ_ep` of
  Definition 8.2.1 is compatible with `Φ^*` for an equivalence `Φ` (surjectivity of `Φ^*`:
  Lemma 11.2.4 (3), `bijective_formPullback`).
* `EpFunctor.isSubTuple_tangent_obj`: a local sc-diffeomorphism on objects maps the tuples of a
  tangent space `T_yN` of a smooth finite-dimensional submanifold to such tuples
  (`T_{Φ(y)}Φ(N ∩ U) = TΦ(T_yN)`).
* `EP.lowerEvIter_tangent`, `EP.levelEv_epFormsPullback`: on level `i` the value of `(Φⁱ)^*ω` at
  vectors of `X` is that of `ω` at their images under `TΦ` (the lifts to `T(Xⁱ)` commute with
  `TΦⁱ`, `tangentLower_tangentMap`).
* **`EP.epFormsInftyEval_isPullback`**: the same for the direct limit `Ωⁿ_{ep,∞}` (§9.5, §11.4),
  with `F^* : Ωⁿ_{ep,∞}(Y) → Ωⁿ_{ep,∞}(X)` (`EP.epFormsInftyPullback`).
-/

set_option maxSynthPendingDepth 3

open Set Function

noncomputable section

namespace Polyfold

universe u

namespace MPolyfold

variable {X Y : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {P : MPolyfold X}
  [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {Q : MPolyfold Y} {f : X → Y} {n : ℕ}

/-- **`(f^*ω)(α₁, …, αₙ) = ω(Tf α₁, …, Tf αₙ)`** for tangent vectors `αᵢ` over one point. -/
theorem evalFamily_formPullback (hf : P.IsScSmoothMap Q f)
    (ω : ∀ y : Q.Level 1, Q.tangentFiber y [⋀^Fin n]→ₗ[ℝ] ℝ) {y : X}
    {α : Fin n → P.TangentSpace} (hα : ∀ i, P.levelVal 1 (P.tangentProj (α i)) = y) :
    evalFamily (formPullback hf ω) α = evalFamily ω (fun i => tangentMap hf (α i)) := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · rw [evalFamily_of_eq_zero hn, evalFamily_of_eq_zero hn]
  obtain ⟨x, a, -, ha⟩ := exists_fiber_lift hα hn
  have e1 : α = fun i => (a i : P.TangentSpace) := funext fun i => (ha i).symm
  subst e1
  rw [evalFamily_eq hn, formPullback_apply, ← evalFamily_eq hn]
  congr 1
  funext i
  exact coe_tangentFiberMap_apply hf (a i)

end MPolyfold

namespace EpGroupoid

variable {Obj Mor Obj' Mor' : Type u} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor]
  [TopologicalSpace Obj'] [T2Space Obj'] [ParacompactSpace Obj']
  [TopologicalSpace Mor'] [T2Space Mor'] [ParacompactSpace Mor']
  {X : EpGroupoid Obj Mor} {Y : EpGroupoid Obj' Mor'} {n : ℕ}

/-- **`(Φ^*ω')(α) = ω'(TΦ ∘ α)`** for the forms of Definition 8.2.1 and vectors over one point. -/
theorem epFormEval_ev_formPullback (Φ : EpFunctor X Y) (ω' : Y.epForms n) {y : Obj}
    {α : Fin n → X.PObj.TangentSpace} (hα : ∀ i, X.PObj.levelVal 1 (X.PObj.tangentProj (α i)) = y) :
    (X.epFormEval n).ev (Φ.formPullbackLin n ω') α =
      (Y.epFormEval n).ev ω' (fun i => Φ.tangent.obj (α i)) :=
  MPolyfold.evalFamily_formPullback Φ.isScSmoothMap_obj ω'.1 hα

end EpGroupoid

namespace EpFunctor

variable {Obj Mor Obj' Mor' : Type u} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor]
  [TopologicalSpace Obj'] [T2Space Obj'] [ParacompactSpace Obj']
  [TopologicalSpace Mor'] [T2Space Mor'] [ParacompactSpace Mor']
  {X : EpGroupoid Obj Mor} {Y : EpGroupoid Obj' Mor'} {n : ℕ}

/-- **The evaluation of `Ωⁿ_ep(X)` is the pull-back of that of `Ωⁿ_ep(Y)` along an
equivalence `Φ`.** -/
theorem IsEquivalence.epFormEval_isPullback {Φ : EpFunctor X Y} (hΦ : Φ.IsEquivalence) (n : ℕ) :
    (X.epFormEval n).IsPullback (Y.epFormEval n) Φ (Φ.formPullbackLin n) where
  ev_pull ω' _ _ _ _ _ hα :=
    EpGroupoid.epFormEval_ev_formPullback Φ ω' fun i => MPolyfold.levelVal_tangentProj_of_mem (hα i)
  surjective := (hΦ.bijective_formPullback n).2

/-- **A local sc-diffeomorphism on objects maps the tuples of `T_yN` to tuples of
`T_{Φ(y)}Φ(N ∩ U)`.** -/
theorem isSubTuple_tangent_obj {Φ : EpFunctor X Y} (hΦ : X.PObj.IsLocalScDiffeo Y.PObj Φ.obj)
    {α : Fin n → X.PObj.TangentSpace} (hα : MPolyfold.IsSubTuple X.PObj α) :
    MPolyfold.IsSubTuple Y.PObj (fun i => Φ.tangent.obj (α i)) := by
  obtain ⟨N, y, hN, hy, hαN⟩ := hα
  obtain ⟨U, V, g, hyU, hd⟩ := hΦ y
  have hU : IsOpen U := hd.isScSmoothOn.isOpen
  have hNU : X.PObj.IsSmoothSubmanifold (N ∩ U) := hN.inter_isOpen hU
  refine ⟨Φ.obj '' (N ∩ U), Φ.obj y, hNU.image_of_isScDiffeoOn hd inter_subset_right,
    ⟨y, ⟨hy, hyU⟩, rfl⟩, fun i => ?_⟩
  have hαU : α i ∈ X.PObj.tangentPreimage U := by
    change _ ∈ U; rw [MPolyfold.levelVal_tangentProj_of_mem (hαN i)]; exact hyU
  change Φ.tangent.obj (α i) ∈ _
  rw [tangent_obj_eq_tangentMapOn hd hαU,
    MPolyfold.submanifoldTangent_image_of_isScDiffeoOn hd hNU inter_subset_right ⟨hy, hyU⟩]
  refine ⟨α i, ?_, rfl⟩
  rw [MPolyfold.submanifoldTangent_inter_isOpen hU hyU]
  exact hαN i

end EpFunctor

namespace EP

variable {A B : EP.{u}} {n : ℕ}

/-- `ι ∘ TΦⁱ⁺¹ = TΦⁱ ∘ ι` for the inclusion `ι = tangentLower : T(Xⁱ⁺¹) → T(Xⁱ)`. -/
theorem tangentLower_tangent_obj_liftFunctor (F : EpFunctor A.X B.X) (i : ℕ)
    (β : (A.lift (i + 1)).X.PObj.TangentSpace) :
    MPolyfold.tangentLower ((liftFunctor F (i + 1)).tangent.obj β) =
      (liftFunctor F i).tangent.obj (MPolyfold.tangentLower β) :=
  MPolyfold.tangentLower_tangentMap (liftFunctor F i).isScSmoothMap_obj (fun _ => rfl) β

/-- **The values on level `i`, read on `X`, commute with `TΦ`**: if `f'(β) = f(TΦⁱ ∘ β)` on the
tuples of `Xⁱ`, then the lowered values satisfy the same on the tuples of `X`. -/
theorem lowerEvIter_tangent (F : EpFunctor A.X B.X) : ∀ (i : ℕ)
    (f : (Fin n → (B.lift i).X.PObj.TangentSpace) → ℝ)
    (f' : (Fin n → (A.lift i).X.PObj.TangentSpace) → ℝ),
    (∀ β, MPolyfold.IsSubTuple (A.lift i).X.PObj β →
      f' β = f (fun j => (liftFunctor F i).tangent.obj (β j))) →
    ∀ α, MPolyfold.IsSubTuple A.X.PObj α →
      A.lowerEvIter i f' α = B.lowerEvIter i f (fun j => F.tangent.obj (α j))
  | 0, _, _, h, α, hα => h α hα
  | i + 1, f, f', h, α, hα => by
    refine lowerEvIter_tangent F i (MPolyfold.lowerEv (P := (B.lift i).X.PObj) f)
      (MPolyfold.lowerEv (P := (A.lift i).X.PObj) f') (fun β hβ => ?_) α hα
    obtain ⟨γ, hγ, hγs⟩ := hβ.exists_lift
    rw [MPolyfold.lowerEv_eq f' γ hγ, h γ hγs,
      MPolyfold.lowerEv_eq f (fun j => (liftFunctor F (i + 1)).tangent.obj (γ j)) fun j =>
        (tangentLower_tangent_obj_liftFunctor F i (γ j)).trans (congrArg _ (hγ j))]

/-- **On level `i`, `(Φⁱ)^*ω` at `α` is `ω` at `TΦ ∘ α`** on the tuples of `T_yN`. -/
theorem levelEv_epFormsPullback (F : EpFunctor A.X B.X) (i : ℕ) (ω : B.epForms n i)
    {α : Fin n → A.X.PObj.TangentSpace} (hα : MPolyfold.IsSubTuple A.X.PObj α) :
    A.levelEv i (epFormsPullback F n i ω) α = B.levelEv i ω (fun j => F.tangent.obj (α j)) :=
  lowerEvIter_tangent F i _ _ (fun _ ⟨_, _, _, _, hβ⟩ =>
    MPolyfold.evalFamily_formPullback (liftFunctor F i).isScSmoothMap_obj ω.1
      fun j => MPolyfold.levelVal_tangentProj_of_mem (hβ j)) α hα

/-- The level-`i` evaluation `epFormsLevelEval` commutes with the pull-back. -/
theorem epFormsLevelEval_epFormsPullback {F : EpFunctor A.X B.X}
    (hF : A.X.PObj.IsLocalScDiffeo B.X.PObj F.obj) (i : ℕ) (ω : B.epForms n i)
    {α : Fin n → A.X.PObj.TangentSpace} (hα : MPolyfold.IsSubTuple A.X.PObj α) :
    (A.epFormsLevelEval n i).ev (epFormsPullback F n i ω) α =
      (B.epFormsLevelEval n i).ev ω (fun j => F.tangent.obj (α j)) := by
  rw [A.epFormsLevelEval_ev n i _ (Or.inl hα),
    B.epFormsLevelEval_ev n i _ (Or.inl (EpFunctor.isSubTuple_tangent_obj hF hα))]
  exact levelEv_epFormsPullback F i ω hα

/-- **The evaluation of `Ωⁿ_{ep,∞}(X)` is the pull-back of that of `Ωⁿ_{ep,∞}(Y)` along an
equivalence `Φ`.** -/
theorem epFormsInftyEval_isPullback {Φ : EpFunctor A.X B.X} (hΦ : Φ.IsEquivalence) (n : ℕ) :
    (A.epFormsInftyEval n).IsPullback (B.epFormsInftyEval n) Φ (epFormsInftyPullback Φ n) where
  ev_pull b N hN y hy α hα := by
    obtain ⟨i, ω, rfl⟩ := B.exists_epFormsInftyOf_eq n b
    rw [epFormsInftyPullback_of, A.epFormsInftyEval_of, B.epFormsInftyEval_of]
    exact epFormsLevelEval_epFormsPullback hΦ.isLocalScDiffeo_obj i ω ⟨N, y, hN, hy, hα⟩
  surjective a := ⟨epFormsInftyPush hΦ n a, epFormsInftyPullback_epFormsInftyPush hΦ n a⟩

end EP

end Polyfold
