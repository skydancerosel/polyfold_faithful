import Polyfold.Chapter9.GapP2_E3_TameOpen
import Polyfold.Chapter11.BranchedEquivalenceTangentOrientation

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021; 2017 arXiv 1707.08941),
Part II, Chapter 11, §11.4 "Equivalences and Integration" (pp. 542–546; 2017: pp. 396–397), gap
G.131.  Numbers and pages are the 2021 text's.

# Evaluations of forms compatible with the pull-back along an ep-functor

The integrals of §9.5 are built from an evaluation `F.ev ω α = ω(α₁, …, αₙ)` of the forms on
tangent vectors (`EpGroupoid.FormEval`, `GapP2_E3_GraphChart.lean`).  For an equivalence
`Φ : X → Y` the text's identity `µ^{Φ^*Θ̂'}_{Φ^*ω'} = |Φ|^* µ^{Θ̂'}_{ω'}` (Theorem 11.4.1) only uses
two facts about the pull-back of forms `P = Φ^*`:

* `ev_pull`: `(Φ^*ω')(α₁, …, αₙ) = ω'(TΦ α₁, …, TΦ αₙ)` on the tangent spaces `T_yN` of the smooth
  finite-dimensional submanifolds `N` of the object M-polyfold of `X` (the definition of the
  pull-back of forms);
* `surjective`: every form on `X` is a pull-back (for an equivalence `Φ^*` is a bijection,
  Lemma 11.2.4 (3); for the forms of Definition 8.2.1 this is
  `EpFunctor.IsEquivalence.bijective_formPullback`).

`FormEval.IsPullback FX FY Φ P` records them.  Instances: `GapP2_H4CompatInst.lean`.
-/

set_option maxSynthPendingDepth 3

open Set Function

noncomputable section

namespace Polyfold

universe u

namespace EpGroupoid

namespace FormEval

variable {Obj Mor Obj' Mor' : Type u} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor]
  [TopologicalSpace Obj'] [T2Space Obj'] [ParacompactSpace Obj']
  [TopologicalSpace Mor'] [T2Space Mor'] [ParacompactSpace Mor']
  {X : EpGroupoid Obj Mor} {Y : EpGroupoid Obj' Mor'} {n : ℕ}
  {Ω Ω' : Type*} [AddCommGroup Ω] [Module ℝ Ω] [AddCommGroup Ω'] [Module ℝ Ω']

/-- **The evaluation `FX` of the forms `Ω` on `X` is the pull-back of the evaluation `FY` of the
forms `Ω'` on `Y` along `Φ`, by the linear map `P = Φ^* : Ω' → Ω`** (2021 Definition 8.2.1 and
§11.2): `(Pω')(α) = ω'(TΦ ∘ α)` on the tangent spaces of smooth finite-dimensional submanifolds,
and every form of `Ω` is a pull-back. -/
structure IsPullback (FX : X.FormEval n Ω) (FY : Y.FormEval n Ω') (Φ : EpFunctor X Y)
    (P : Ω' →ₗ[ℝ] Ω) : Prop where
  ev_pull : ∀ (ω' : Ω') {N : Set Obj}, X.PObj.IsSmoothSubmanifold N → ∀ {y : Obj}, y ∈ N →
    ∀ α : Fin n → X.PObj.TangentSpace, (∀ i, α i ∈ X.PObj.submanifoldTangent N y) →
    FX.ev (P ω') α = FY.ev ω' (fun i => Φ.tangent.obj (α i))
  surjective : Surjective P

end FormEval

end EpGroupoid

end Polyfold
