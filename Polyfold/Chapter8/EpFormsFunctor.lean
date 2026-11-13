import Polyfold.Chapter8.EpForms
import Polyfold.Chapter10.EquivalenceReduced

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part II, §8.2
(pp. 372–373) and the functorial part of **Theorem 11.2.1 (1), (2)** (p. 526): the pull-back
`F^* : Ω*_{ep,∞}(Y) → Ω*_{ep,∞}(X)` of sc-differential forms on ep-groupoids by an sc-smooth
functor `F : X → Y`, with `d_X ∘ F^* = F^* ∘ d_Y` (gap G.74; used by §11.2, gap G.129).

# Pull-back of forms on ep-groupoids by sc-smooth functors

## What is formalized (namespace `Polyfold.EP`; `A`, `B`, `C` bundled ep-groupoids)

* `liftFunctor F i : Xⁱ → Yⁱ`, the `i`-th index raise of an sc-smooth functor `F : X → Y`
  (iterating `EpFunctor.liftOne` of Proposition 10.1.18), with `liftFunctor_id_obj`,
  `liftFunctor_comp_obj`.
* `epFormsPullback F k i : Ωᵏ_ep(Yⁱ) → Ωᵏ_ep(Xⁱ)`, commuting with the directed systems
  (`epFormsPullback_epFormsMap`) and with `d` (`epFormsD_epFormsPullback`).
* **`epFormsInftyPullback F k : Ωᵏ_{ep,∞}(Y) → Ωᵏ_{ep,∞}(X)`**, `F^*[ω] = [(Fⁱ)^*ω]`
  (`epFormsInftyPullback_of`), with **`epFormsInftyD_comp_epFormsInftyPullback`**
  (`d ∘ F^* = F^* ∘ d`), `epFormsInftyPullback_id`, `epFormsInftyPullback_comp`.
* `EpNatTrans.liftOne`, `liftNatTrans τ i` (the index raise of a natural transformation), and
  **`epFormsInftyPullback_eq_of_natTrans`**: naturally equivalent sc-smooth functors
  (Definition 8.1.13) induce the same map `Ω*_{ep,∞}(Y) → Ω*_{ep,∞}(X)`.

Not treated here: the pull-back by generalized maps and the push-forward by generalized
isomorphisms of Theorem 11.2.1 (2)–(4) (§11.2, gap G.129), which build on these maps; they are in
`Chapter11/EquivalenceForms*.lean` and `GeneralizedForms.lean` (2026-11-12).
-/

set_option maxSynthPendingDepth 3

open Set Function

noncomputable section

namespace Polyfold

open MPolyfold

universe u v w

/-! ### The index raise of a natural transformation -/

namespace EpNatTrans

variable {Obj Mor : Type u} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor]
  {Obj' Mor' : Type v} [TopologicalSpace Obj'] [T2Space Obj'] [ParacompactSpace Obj']
  [TopologicalSpace Mor'] [T2Space Mor'] [ParacompactSpace Mor']
  {X : EpGroupoid Obj Mor} {Y : EpGroupoid Obj' Mor'} {F G : EpFunctor X Y}

/-- **The lift `τ¹ : F¹ → G¹`** of a natural transformation to the index lifts `X¹`, `Y¹`. -/
def liftOne (τ : EpNatTrans F G) : EpNatTrans F.liftOne G.liftOne where
  app := MPolyfold.levelOneMap X.PObj Y.PMor τ.app (τ.isScSmoothMap_app.mapsTo_levelSet 1)
  isScSmoothMap_app := MPolyfold.IsScSmoothMap.levelOne τ.isScSmoothMap_app fun _ => rfl
  src_app x := MPolyfold.level_ext (τ.src_app (X.PObj.levelVal 1 x))
  tgt_app x := MPolyfold.level_ext (τ.tgt_app (X.PObj.levelVal 1 x))
  naturality h := by
    have h1 : Y.liftOne.src (MPolyfold.levelOneMap X.PObj Y.PMor τ.app
        (τ.isScSmoothMap_app.mapsTo_levelSet 1) (X.liftOne.tgt h)) =
        Y.liftOne.tgt (F.liftOne.mor h) :=
      MPolyfold.level_ext ((τ.src_app _).trans (F.tgt_mor _).symm)
    have h2 : Y.liftOne.src (G.liftOne.mor h) =
        Y.liftOne.tgt (MPolyfold.levelOneMap X.PObj Y.PMor τ.app
          (τ.isScSmoothMap_app.mapsTo_levelSet 1) (X.liftOne.src h)) :=
      MPolyfold.level_ext ((G.src_mor _).trans (τ.tgt_app _).symm)
    refine MPolyfold.level_ext ?_
    rw [Y.liftOne_comp_val h1, Y.liftOne_comp_val h2]
    exact τ.naturality (X.PMor.levelVal 1 h)

end EpNatTrans

namespace EP

variable {A : EP.{u}} {B : EP.{v}} {C : EP.{w}}

/-! ### The index raise of an sc-smooth functor -/

/-- **`Fⁱ : Xⁱ → Yⁱ`**, the `i`-th index raise of an sc-smooth functor `F : X → Y`. -/
def liftFunctor (F : EpFunctor A.X B.X) : (i : ℕ) → EpFunctor (A.lift i).X (B.lift i).X
  | 0 => F
  | i + 1 => (liftFunctor F i).liftOne

@[simp] lemma liftFunctor_zero (F : EpFunctor A.X B.X) : liftFunctor F 0 = F := rfl

lemma liftFunctor_succ (F : EpFunctor A.X B.X) (i : ℕ) :
    liftFunctor F (i + 1) = (liftFunctor F i).liftOne := rfl

theorem liftFunctor_id_obj :
    ∀ (i : ℕ) (y : (A.lift i).Obj), (liftFunctor (EpFunctor.id A.X) i).obj y = y
  | 0, _ => rfl
  | i + 1, y => MPolyfold.level_ext (liftFunctor_id_obj i ((A.lift i).X.PObj.levelVal 1 y))

theorem liftFunctor_comp_obj (G : EpFunctor B.X C.X) (F : EpFunctor A.X B.X) :
    ∀ (i : ℕ) (y : (A.lift i).Obj),
      (liftFunctor (G.comp F) i).obj y = (liftFunctor G i).obj ((liftFunctor F i).obj y)
  | 0, _ => rfl
  | i + 1, y =>
    MPolyfold.level_ext (liftFunctor_comp_obj G F i ((A.lift i).X.PObj.levelVal 1 y))

/-- The index raise of a natural transformation `τ : F → G`. -/
def liftNatTrans {F G : EpFunctor A.X B.X} (τ : EpNatTrans F G) :
    (i : ℕ) → EpNatTrans (liftFunctor F i) (liftFunctor G i)
  | 0 => τ
  | i + 1 => (liftNatTrans τ i).liftOne

/-! ### The pull-back on `Ωᵏ_ep(Xⁱ)` -/

variable (F : EpFunctor A.X B.X) (k : ℕ)

/-- The pull-back `(Fⁱ)^* : Ωᵏ_ep(Yⁱ) → Ωᵏ_ep(Xⁱ)` by the index raise of an sc-smooth functor. -/
def epFormsPullback (i : ℕ) : B.epForms k i →ₗ[ℝ] A.epForms k i :=
  LinearMap.codRestrict (A.epForms k i)
    ((formPullbackₗ k (liftFunctor F i).isScSmoothMap_obj).domRestrict (B.epForms k i))
    fun ω => EpGroupoid.formPullback_mem_epForms (liftFunctor F i) ω.2

lemma coe_epFormsPullback (i : ℕ) (ω : B.epForms k i) :
    (epFormsPullback F k i ω).1 = formPullback (liftFunctor F i).isScSmoothMap_obj ω.1 := rfl

/-- The pull-back commutes with the steps of the directed systems. -/
theorem epFormsPullback_epFormsStep (i : ℕ) (ω : B.epForms k i) :
    epFormsPullback F k (i + 1) (B.epFormsStep k i ω) =
      A.epFormsStep k i (epFormsPullback F k i ω) :=
  Subtype.ext (formLower_formPullback (liftFunctor F i).isScSmoothMap_obj
    (f₁ := (liftFunctor F (i + 1)).obj) (fun _ => rfl)
    (liftFunctor F (i + 1)).isScSmoothMap_obj ω.1)

/-- The pull-back commutes with the maps of the directed systems. -/
theorem epFormsPullback_epFormsMap {i j : ℕ} (h : i ≤ j) (ω : B.epForms k i) :
    epFormsPullback F k j (B.epFormsMap k i j h ω) =
      A.epFormsMap k i j h (epFormsPullback F k i ω) := by
  induction j, h using Nat.le_induction with
  | base => rw [epFormsMap_self, epFormsMap_self]; rfl
  | succ j hij ih =>
    rw [epFormsMap_succ B k hij, LinearMap.comp_apply, epFormsPullback_epFormsStep, ih,
      epFormsMap_succ A k hij, LinearMap.comp_apply]

/-- `d` commutes with the pull-back on `Ωᵏ_ep(Xⁱ) → Ωᵏ⁺¹_ep(Xⁱ⁺¹)`. -/
theorem epFormsD_epFormsPullback (i : ℕ) (ω : B.epForms k i) :
    A.epFormsD k i (epFormsPullback F k i ω) =
      epFormsPullback F (k + 1) (i + 1) (B.epFormsD k i ω) :=
  Subtype.ext ((extD_formPullback (liftFunctor F i).isScSmoothMap_obj ω.2.1).trans
    (formPullback_congr _ (liftFunctor F (i + 1)).isScSmoothMap_obj (fun _ => rfl) _))

/-! ### The pull-back on `Ωᵏ_{ep,∞}(X)` -/

/-- **The pull-back `F^* : Ωᵏ_{ep,∞}(Y) → Ωᵏ_{ep,∞}(X)`** by an sc-smooth functor `F : X → Y`
(the functor case of 2021 Theorem 11.2.1 (2)). -/
def epFormsInftyPullback : B.epFormsInfty k →ₗ[ℝ] A.epFormsInfty k :=
  Module.DirectLimit.lift ℝ ℕ (fun i => ↥(B.epForms k i)) (B.epFormsMap k)
    (fun i => (A.epFormsInftyOf k i).comp (epFormsPullback F k i)) fun i j h ω => by
      simp only [LinearMap.comp_apply]
      rw [epFormsPullback_epFormsMap, epFormsInftyOf_epFormsMap]

/-- `F^*[ω] = [(Fⁱ)^*ω]`. -/
theorem epFormsInftyPullback_of (i : ℕ) (ω : B.epForms k i) :
    epFormsInftyPullback F k (B.epFormsInftyOf k i ω) =
      A.epFormsInftyOf k i (epFormsPullback F k i ω) :=
  Module.DirectLimit.lift_of _ _ _

/-- **`d_X ∘ F^* = F^* ∘ d_Y` on `Ω*_{ep,∞}`** (the functor case of 2021 Theorem 11.2.1 (2)). -/
theorem epFormsInftyD_comp_epFormsInftyPullback :
    (A.epFormsInftyD k).comp (epFormsInftyPullback F k) =
      (epFormsInftyPullback F (k + 1)).comp (B.epFormsInftyD k) := by
  refine Module.DirectLimit.hom_ext fun i => LinearMap.ext fun ω => ?_
  simp only [LinearMap.comp_apply]
  rw [epFormsInftyPullback_of, epFormsInftyD_of, epFormsInftyD_of, epFormsInftyPullback_of,
    epFormsD_epFormsPullback]

theorem epFormsPullback_id (i : ℕ) (ω : A.epForms k i) :
    epFormsPullback (EpFunctor.id A.X) k i ω = ω :=
  Subtype.ext ((formPullback_congr _ isScSmoothMap_id (liftFunctor_id_obj i) ω.1).trans
    (formPullback_id ω.1))

theorem epFormsPullback_comp (G : EpFunctor B.X C.X) (i : ℕ) (ω : C.epForms k i) :
    epFormsPullback (G.comp F) k i ω = epFormsPullback F k i (epFormsPullback G k i ω) :=
  Subtype.ext ((formPullback_congr _ ((liftFunctor G i).isScSmoothMap_obj.comp
    (liftFunctor F i).isScSmoothMap_obj) (liftFunctor_comp_obj G F i) ω.1).trans
    (formPullback_comp _ _ ω.1))

/-- `id^* = id` on `Ωᵏ_{ep,∞}(X)`. -/
theorem epFormsInftyPullback_id :
    epFormsInftyPullback (EpFunctor.id A.X) k = LinearMap.id := by
  refine Module.DirectLimit.hom_ext fun i => LinearMap.ext fun ω => ?_
  rw [LinearMap.comp_apply, epFormsInftyPullback_of, epFormsPullback_id]
  rfl

/-- `(G ∘ F)^* = F^* ∘ G^*` on `Ωᵏ_{ep,∞}`. -/
theorem epFormsInftyPullback_comp (G : EpFunctor B.X C.X) :
    epFormsInftyPullback (G.comp F) k =
      (epFormsInftyPullback F k).comp (epFormsInftyPullback G k) := by
  refine Module.DirectLimit.hom_ext fun i => LinearMap.ext fun ω => ?_
  simp only [LinearMap.comp_apply]
  rw [epFormsInftyPullback_of, epFormsInftyPullback_of, epFormsInftyPullback_of,
    epFormsPullback_comp]

/-! ### Natural equivalence -/

variable {F}

theorem epFormsPullback_eq_of_natTrans {G : EpFunctor A.X B.X} (τ : EpNatTrans F G) (i : ℕ)
    (ω : B.epForms k i) : epFormsPullback F k i ω = epFormsPullback G k i ω :=
  Subtype.ext (EpGroupoid.formPullback_eq_of_natTrans (liftNatTrans τ i) ω.2)

/-- **Naturally equivalent sc-smooth functors (Definition 8.1.13) induce the same pull-back**
`Ωᵏ_{ep,∞}(Y) → Ωᵏ_{ep,∞}(X)`. -/
theorem epFormsInftyPullback_eq_of_natTrans {G : EpFunctor A.X B.X}
    (h : F.NaturallyEquivalent G) : epFormsInftyPullback F k = epFormsInftyPullback G k := by
  obtain ⟨τ⟩ := h
  refine Module.DirectLimit.hom_ext fun i => LinearMap.ext fun ω => ?_
  rw [LinearMap.comp_apply, LinearMap.comp_apply, epFormsInftyPullback_of,
    epFormsInftyPullback_of, epFormsPullback_eq_of_natTrans k τ]

end EP

end Polyfold
