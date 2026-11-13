import Polyfold.Chapter9.StokesSheetAllDegrees
import Polyfold.Chapter9.PointIntegration

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021; 2017 arXiv 1707.08941),
Part II, §9.5, Theorems 9.5.15–9.5.18 for `n = 1` (pp. 449–451; gaps G.109, G.110): the values
of the `0`-forms of `Ω⁰_{ep,∞}(X)` at the smooth points, and the integration of `0`-forms over
oriented points.  Numbers and pages are the 2021 text's.

# The values of `0`-forms at points

For `n = 1` the boundary sheets `∂₁Mᵢ` of an oriented tame structure are `0`-dimensional, and
`∫_{{p}} ω|({p}, o) = ±ω(p)` (2021 p. 422: an orientation of a point is a sign).  E3's
evaluation `epFormsInftyEval` of a class on `n` tangent vectors does not see the base point when
`n = 0`; the value `ω(p)` is built here directly.

* `BundledMPolyfold.zeroVal τ z`: the value of a `0`-form `τ` at a point of level `1`.
* `EP.liftPt i p`: the smooth point `p` as an object of `Xⁱ`; `EP.liftMor i φ`: a morphism with
  smooth source as a morphism of `Xⁱ`.
* **`EP.zeroFormEval : Ω⁰_{ep,∞}(X) →ₗ (Obj → ℝ)`**, `[ω] ↦ (p ↦ ω(p))` at the smooth points (and
  `0` elsewhere), well defined on the direct limit (`zeroLevelEval_step`).
* `EP.zeroFormEval_src_eq_tgt`: the value is invariant under the morphisms (Definition 8.2.1).
* **`EP.formsInftyRestrict_zero_eq`**: the restriction of `a` to a sheet `N` with a corner
  structure (Part I) takes the value `zeroFormEval a y` at a smooth point `y ∈ N`.
* `EP.zeroFormEval_epFormsInftySmul`: `(βa)(p) = β(p) a(p)`.
* `SheetIntegration.comap`: a sheet integration pulled back along a linear map of the forms.
* **`EP.zeroFormIntegration`**: the integration of `Ω⁰_{ep,∞}(X)` over oriented points, E1's
  `pointIntegration` along `zeroFormEval`.
-/

set_option maxSynthPendingDepth 3

open Set Function Filter Topology MeasureTheory Module Manifold

noncomputable section

open scoped Classical

namespace Polyfold

universe u

open MPolyfold

/-! ### The value of a `0`-form at a point -/

namespace BundledMPolyfold

/-- **The value of a `0`-form at a point** `z` of level `1` (`0` off level `1`). -/
def zeroVal (B : BundledMPolyfold.{u}) (τ : B.P.scForms 0) (z : B.carrier) : ℝ :=
  if h : z ∈ B.P.levelSet 1 then τ.1 (B.P.levelMk 1 z h) (fun j => Fin.elim0 j) else 0

theorem zeroVal_add (B : BundledMPolyfold.{u}) (τ τ' : B.P.scForms 0) (z : B.carrier) :
    B.zeroVal (τ + τ') z = B.zeroVal τ z + B.zeroVal τ' z := by
  unfold zeroVal
  split_ifs
  · rfl
  · rw [add_zero]

theorem zeroVal_smul (B : BundledMPolyfold.{u}) (c : ℝ) (τ : B.P.scForms 0) (z : B.carrier) :
    B.zeroVal (c • τ) z = c * B.zeroVal τ z := by
  unfold zeroVal
  split_ifs
  · rfl
  · rw [mul_zero]

/-- The value at a point of level `1`, through any tuple of `0` vectors. -/
theorem zeroVal_levelVal (B : BundledMPolyfold.{u}) (τ : B.P.scForms 0) (x : B.P.Level 1)
    (a : Fin 0 → B.P.tangentFiber x) : B.zeroVal τ (B.P.levelVal 1 x) = τ.1 x a := by
  unfold zeroVal
  rw [dif_pos (levelVal_mem x)]
  have hx : B.P.levelMk 1 (B.P.levelVal 1 x) (levelVal_mem x) = x := level_ext rfl
  rw [hx]
  congr 1
  funext j
  exact j.elim0

/-- `zeroVal` commutes with the transport along an equality of bundled M-polyfolds. -/
theorem castFun_zeroVal {B B' : BundledMPolyfold.{u}} (h : B = B') (τ : B.P.scForms 0) :
    castFun h (B.zeroVal τ) = B'.zeroVal (castForms 0 h τ) := by
  subst h
  rfl

end BundledMPolyfold

/-! ### Smooth points and morphisms on the levels `Xⁱ` -/

namespace EpGroupoid

variable {Obj Mor : Type u} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] (X : EpGroupoid Obj Mor)

/-- A morphism has a smooth source iff it has a smooth target. -/
theorem src_mem_smoothSet_iff (φ : Mor) :
    X.src φ ∈ X.PObj.smoothSet ↔ X.tgt φ ∈ X.PObj.smoothSet := by
  simp only [MPolyfold.smoothSet, mem_iInter]
  exact forall_congr' fun m => (X.mem_levelSet_src_iff φ m).trans (X.mem_levelSet_tgt_iff φ m).symm

end EpGroupoid

namespace EP

variable (A : EP.{u})

theorem levelBase_injective : ∀ i : ℕ, Injective (A.levelBase i)
  | 0 => injective_id
  | i + 1 => (levelBase_injective i).comp fun _ _ h => level_ext h

/-- **A smooth point `p` as an object of `Xⁱ`** (smooth, lying over `p`). -/
def liftPt : ∀ (i : ℕ) (p : A.Obj), p ∈ A.X.PObj.smoothSet →
    {z : (A.lift i).Obj // z ∈ (A.lift i).X.PObj.smoothSet ∧ A.levelBase i z = p}
  | 0, p, hp => ⟨p, hp, rfl⟩
  | i + 1, p, hp =>
    ⟨(A.lift i).X.PObj.levelMk 1 (liftPt i p hp).1 (mem_iInter.1 (liftPt i p hp).2.1 1),
      (MPolyfold.mem_shift_smoothSet_iff _).2 (by
        rw [levelVal_levelMk]; exact (liftPt i p hp).2.1),
      by
        change A.levelBase i ((A.lift i).X.PObj.levelVal 1 _) = p
        rw [levelVal_levelMk]; exact (liftPt i p hp).2.2⟩

theorem liftPt_succ (i : ℕ) (p : A.Obj) (hp : p ∈ A.X.PObj.smoothSet) :
    (A.liftPt (i + 1) p hp).1 =
      (A.lift i).X.PObj.levelMk 1 (A.liftPt i p hp).1 (mem_iInter.1 (A.liftPt i p hp).2.1 1) :=
  rfl

/-- **A morphism with smooth source as a morphism of `Xⁱ`**, from the lift of its source to the
lift of its target. -/
def liftMor : ∀ (i : ℕ) (φ : A.Mor) (hs : A.X.src φ ∈ A.X.PObj.smoothSet),
    {ψ : (A.lift i).Mor // (A.lift i).X.src ψ = (A.liftPt i _ hs).1 ∧
      (A.lift i).X.tgt ψ = (A.liftPt i _ ((A.X.src_mem_smoothSet_iff φ).1 hs)).1}
  | 0, φ, _ => ⟨φ, rfl, rfl⟩
  | i + 1, φ, hs =>
    have h1 : (liftMor i φ hs).1 ∈ (A.lift i).X.PMor.levelSet 1 :=
      ((A.lift i).X.mem_levelSet_src_iff _ 1).1 (by
        rw [(liftMor i φ hs).2.1]; exact mem_iInter.1 (A.liftPt i _ hs).2.1 1)
    ⟨(A.lift i).X.PMor.levelMk 1 (liftMor i φ hs).1 h1,
      level_ext (by
        change (A.lift i).X.src ((A.lift i).X.PMor.levelVal 1 _) = _
        rw [levelVal_levelMk, (liftMor i φ hs).2.1, liftPt_succ, levelVal_levelMk]),
      level_ext (by
        change (A.lift i).X.tgt ((A.lift i).X.PMor.levelVal 1 _) = _
        rw [levelVal_levelMk, (liftMor i φ hs).2.2, liftPt_succ, levelVal_levelMk])⟩

/-! ### The value on a level -/

/-- The value of `ω ∈ Ω⁰_ep(Xⁱ)` at the object of `Xⁱ` over `p` (if there is one). -/
def baseVal (i : ℕ) (ω : A.epForms 0 i) (p : A.Obj) : ℝ :=
  if h : ∃ z, A.levelBase i z = p then
    (A.lift i).objPolyfold.zeroVal (A.epFormsToForms 0 i ω) h.choose
  else 0

theorem baseVal_levelBase (i : ℕ) (ω : A.epForms 0 i) (z : (A.lift i).Obj) :
    A.baseVal i ω (A.levelBase i z) = (A.lift i).objPolyfold.zeroVal (A.epFormsToForms 0 i ω) z := by
  have h : ∃ z', A.levelBase i z' = A.levelBase i z := ⟨z, rfl⟩
  rw [baseVal, dif_pos h, A.levelBase_injective i h.choose_spec]

theorem baseVal_add (i : ℕ) (ω τ : A.epForms 0 i) (p : A.Obj) :
    A.baseVal i (ω + τ) p = A.baseVal i ω p + A.baseVal i τ p := by
  unfold baseVal
  split_ifs
  · rw [map_add]; exact BundledMPolyfold.zeroVal_add _ _ _ _
  · rw [add_zero]

theorem baseVal_smul (i : ℕ) (c : ℝ) (ω : A.epForms 0 i) (p : A.Obj) :
    A.baseVal i (c • ω) p = c * A.baseVal i ω p := by
  unfold baseVal
  split_ifs
  · rw [map_smul]; exact BundledMPolyfold.zeroVal_smul _ _ _ _
  · rw [mul_zero]

/-- On the object M-polyfold `(Ob X)ⁱ` the value of `ω` is `baseVal` after the inclusion. -/
theorem zeroVal_epFormsToObj (i : ℕ) (ω : A.epForms 0 i) :
    (A.objPolyfold.lift i).zeroVal (A.epFormsToObj 0 i ω) = A.baseVal i ω ∘ A.objPolyfold.incl i := by
  have e1 : (A.lift i).objPolyfold.zeroVal (A.epFormsToForms 0 i ω) = A.liftFun (A.baseVal i ω) i :=
    funext fun z => (A.baseVal_levelBase i ω z).symm
  have e2 := BundledMPolyfold.castFun_zeroVal (A.objPolyfold_lift i) (A.epFormsToForms 0 i ω)
  rw [e1, A.castFun_liftFun] at e2
  exact e2.symm

/-- **The value of `ω ∈ Ω⁰_ep(Xⁱ)` at the smooth points** (`0` elsewhere). -/
def zeroLevelEval (i : ℕ) : A.epForms 0 i →ₗ[ℝ] (A.Obj → ℝ) where
  toFun ω p := if p ∈ A.X.PObj.smoothSet then A.baseVal i ω p else 0
  map_add' ω τ := funext fun p => by
    simp only [Pi.add_apply]
    split_ifs
    · exact A.baseVal_add i ω τ p
    · rw [add_zero]
  map_smul' c ω := funext fun p => by
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    split_ifs
    · exact A.baseVal_smul i c ω p
    · rw [mul_zero]

theorem zeroLevelEval_apply (i : ℕ) (ω : A.epForms 0 i) {p : A.Obj}
    (hp : p ∈ A.X.PObj.smoothSet) : A.zeroLevelEval i ω p = A.baseVal i ω p := if_pos hp

theorem zeroLevelEval_of_not_mem (i : ℕ) (ω : A.epForms 0 i) {p : A.Obj}
    (hp : p ∉ A.X.PObj.smoothSet) : A.zeroLevelEval i ω p = 0 := if_neg hp

/-- The value at a smooth point is that of `ω` at the lift of the point. -/
theorem zeroLevelEval_eq (i : ℕ) (ω : A.epForms 0 i) {p : A.Obj} (hp : p ∈ A.X.PObj.smoothSet)
    (a : Fin 0 → (A.lift i).X.PObj.tangentFiber
      ((A.lift i).X.PObj.levelMk 1 (A.liftPt i p hp).1 (mem_iInter.1 (A.liftPt i p hp).2.1 1))) :
    A.zeroLevelEval i ω p =
      ω.1 ((A.lift i).X.PObj.levelMk 1 (A.liftPt i p hp).1
        (mem_iInter.1 (A.liftPt i p hp).2.1 1)) a := by
  rw [A.zeroLevelEval_apply i ω hp]
  conv_lhs => rw [← (A.liftPt i p hp).2.2]
  rw [A.baseVal_levelBase]
  exact BundledMPolyfold.zeroVal_levelVal (A.lift i).objPolyfold (A.epFormsToForms 0 i ω) _ a

/-- **A form on `Xⁱ` and its pull-back to `Xⁱ⁺¹` have the same values.** -/
theorem zeroLevelEval_step (i : ℕ) (ω : A.epForms 0 i) :
    A.zeroLevelEval (i + 1) (A.epFormsStep 0 i ω) = A.zeroLevelEval i ω := by
  funext p
  by_cases hp : p ∈ A.X.PObj.smoothSet
  · rw [A.zeroLevelEval_eq (i + 1) _ hp (fun j => Fin.elim0 j),
      A.zeroLevelEval_eq i _ hp (fun j => Fin.elim0 j), coe_epFormsStep]
    have h0 : ∀ (Y : (A.lift i).X.PObj.Level 1) (a b : Fin 0 → (A.lift i).X.PObj.tangentFiber Y),
        ω.1 Y a = ω.1 Y b := fun Y a b => congrArg _ (funext fun j => j.elim0)
    exact h0 _ _ _
  · rw [A.zeroLevelEval_of_not_mem _ _ hp, A.zeroLevelEval_of_not_mem _ _ hp]

theorem zeroLevelEval_epFormsMap {i j : ℕ} (h : i ≤ j) (ω : A.epForms 0 i) :
    A.zeroLevelEval j (A.epFormsMap 0 i j h ω) = A.zeroLevelEval i ω := by
  induction j, h using Nat.le_induction with
  | base => rw [epFormsMap_self]; rfl
  | succ j hij ih =>
    rw [epFormsMap_succ A 0 hij, LinearMap.comp_apply, zeroLevelEval_step, ih]

/-! ### The value of a class -/

/-- **The value `ω(p)` of a class `ω ∈ Ω⁰_{ep,∞}(X)` at the smooth points `p`** (`0` elsewhere):
the value of a representative `ω ∈ Ω⁰_ep(Xⁱ)` at the object of `Xⁱ` over `p`. -/
def zeroFormEval : A.epFormsInfty 0 →ₗ[ℝ] (A.Obj → ℝ) :=
  Module.DirectLimit.lift ℝ ℕ (fun i => ↥(A.epForms 0 i)) (A.epFormsMap 0)
    (fun i => A.zeroLevelEval i) fun _ _ h ω => A.zeroLevelEval_epFormsMap h ω

theorem zeroFormEval_of (i : ℕ) (ω : A.epForms 0 i) :
    A.zeroFormEval (A.epFormsInftyOf 0 i ω) = A.zeroLevelEval i ω :=
  Module.DirectLimit.lift_of _ _ _

theorem zeroFormEval_of_not_mem (a : A.epFormsInfty 0) {p : A.Obj}
    (hp : p ∉ A.X.PObj.smoothSet) : A.zeroFormEval a p = 0 := by
  obtain ⟨i, ω, rfl⟩ := A.exists_epFormsInftyOf_eq 0 a
  rw [zeroFormEval_of, A.zeroLevelEval_of_not_mem i ω hp]

/-- **The value is invariant under the morphisms** (Definition 8.2.1 for `k = 0`). -/
theorem zeroFormEval_src_eq_tgt (a : A.epFormsInfty 0) (φ : A.Mor) :
    A.zeroFormEval a (A.X.src φ) = A.zeroFormEval a (A.X.tgt φ) := by
  by_cases hs : A.X.src φ ∈ A.X.PObj.smoothSet
  · have ht := (A.X.src_mem_smoothSet_iff φ).1 hs
    obtain ⟨i, ω, rfl⟩ := A.exists_epFormsInftyOf_eq 0 a
    rw [zeroFormEval_of, A.zeroLevelEval_eq i ω hs (fun j => Fin.elim0 j),
      A.zeroLevelEval_eq i ω ht (fun j => Fin.elim0 j)]
    obtain ⟨ψ, hψs, hψt⟩ := A.liftMor i φ hs
    have h1 : ψ ∈ (A.lift i).X.PMor.levelSet 1 :=
      ((A.lift i).X.mem_levelSet_src_iff _ 1).1 (by
        rw [hψs]; exact mem_iInter.1 (A.liftPt i _ hs).2.1 1)
    have hx : (A.lift i).X.PObj.levelVal 1 ((A.lift i).X.PObj.levelMk 1 (A.liftPt i _ hs).1
        (mem_iInter.1 (A.liftPt i _ hs).2.1 1)) = (A.lift i).X.src ψ := by
      rw [levelVal_levelMk, hψs]
    have hy : (A.lift i).X.PObj.levelVal 1 ((A.lift i).X.PObj.levelMk 1 (A.liftPt i _ ht).1
        (mem_iInter.1 (A.liftPt i _ ht).2.1 1)) = (A.lift i).X.tgt ψ := by
      rw [levelVal_levelMk, hψt]
    have key := EpGroupoid.IsMorCompatible.apply (A.lift i).X ω.2.2 h1 hx hy (fun j => Fin.elim0 j)
    refine key.symm.trans ?_
    congr 1
    funext j
    exact j.elim0
  · have ht : A.X.tgt φ ∉ A.X.PObj.smoothSet := fun h => hs ((A.X.src_mem_smoothSet_iff φ).2 h)
    rw [A.zeroFormEval_of_not_mem a hs, A.zeroFormEval_of_not_mem a ht]

/-- `zeroFormEval` with values in the invariant functions (`EpGroupoid.invariantFunctions`). -/
def zeroFormEvalInv : A.epFormsInfty 0 →ₗ[ℝ] EpGroupoid.invariantFunctions A.X :=
  LinearMap.codRestrict _ A.zeroFormEval fun a φ => A.zeroFormEval_src_eq_tgt a φ

theorem coe_zeroFormEvalInv (a : A.epFormsInfty 0) :
    (A.zeroFormEvalInv a : A.Obj → ℝ) = A.zeroFormEval a := rfl

/-- **`(βa)(p) = β(p) a(p)`** for an sc-smooth `β` constant on the orbits. -/
theorem zeroFormEval_epFormsInftySmul {β : A.Obj → ℝ} (hβ : A.X.PObj.IsScSmoothMap realPolyfold β)
    (hinv : ∀ φ : A.Mor, β (A.X.src φ) = β (A.X.tgt φ)) (a : A.epFormsInfty 0) (p : A.Obj) :
    A.zeroFormEval (A.epFormsInftySmul β 0 hβ hinv a) p = β p * A.zeroFormEval a p := by
  by_cases hp : p ∈ A.X.PObj.smoothSet
  · obtain ⟨i, ω, rfl⟩ := A.exists_epFormsInftyOf_eq 0 a
    rw [epFormsInftySmul_of, zeroFormEval_of, zeroFormEval_of,
      A.zeroLevelEval_eq i _ hp (fun j => Fin.elim0 j), A.zeroLevelEval_eq i _ hp (fun j => Fin.elim0 j),
      coe_epFormsSmul, MPolyfold.formSmulFun_apply]
    congr 1
    change β (A.levelBase i ((A.lift i).X.PObj.levelVal 1 _)) = β p
    rw [levelVal_levelMk, (A.liftPt i p hp).2.2]
  · rw [A.zeroFormEval_of_not_mem _ hp, A.zeroFormEval_of_not_mem _ hp, mul_zero]

/-! ### The restriction of a `0`-form to a sheet -/

variable {n : ℕ} {N : Set A.Obj} [ParacompactSpace N] {hY : A.X.PObj.IsSubMPolyfold N}
  {hcs : (subPolyfold hY).HasCornerStructureOfDim n}
  [inst : ChartedSpace (EuclideanQuadrant n) N]

/-- **The restriction of `a ∈ Ω⁰_{ep,∞}(X)` to a sheet `N` with a corner structure (Part I's
`formsInftyRestrict`) takes the value `a(y)` at a smooth point `y ∈ N`.** -/
theorem formsInftyRestrict_zero_eq (a : A.epFormsInfty 0) (y : N)
    (hy : y.1 ∈ A.X.PObj.smoothSet) (v : Fin 0 → EuclideanSpace ℝ (Fin n)) :
    formsInftyRestrict 0 hcs (A.epFormsInftyToObj 0 a) y v = A.zeroFormEval a y.1 := by
  obtain ⟨i, ω, rfl⟩ := A.exists_epFormsInftyOf_eq 0 a
  rw [epFormsInftyToObj_of, zeroFormEval_of, A.zeroLevelEval_apply i ω hy]
  have e : formsInftyRestrict 0 hcs (A.objPolyfold.formsInftyOf 0 i (A.epFormsToObj 0 i ω)) =
      scFormRestrict 0 hcs i (A.epFormsToObj 0 i ω) := formsInftyRestrict_of hcs i _
  rw [e]
  set g : ScMap (subPolyfold hY) A.objPolyfold.P := subInclScMap hY with hg
  have e0 : scFormRestrict 0 hcs i (A.epFormsToObj 0 i ω) y v =
      (A.epFormsToObj 0 i ω).1 (liftLevelOneMap (alongLift hcs g i).isScSmoothMap
        (hcs.levelOne y)) fun j =>
        tangentFiberMap (alongLift hcs g i).isScSmoothMap (hcs.levelOne y)
          ((hcs.coords y).fiberMap (hcs.levelOne_mem_coords y) (v j)) := rfl
  rw [e0, ← BundledMPolyfold.zeroVal_levelVal, A.zeroVal_epFormsToObj]
  exact congrArg (A.baseVal i ω) (incl_alongLift hcs g i y)

end EP

/-! ### Pulling back a sheet integration along a linear map of the forms -/

namespace EpGroupoid

variable {Obj Mor : Type u} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] {X : EpGroupoid Obj Mor}
  {S : Set (Set Obj)} {G : SheetNullSets S} {Ω Ω' : Type*} [AddCommGroup Ω] [Module ℝ Ω]
  [AddCommGroup Ω'] [Module ℝ Ω']

/-- **A sheet integration pulled back along a linear map `L : Ω → Ω'` of the forms**:
`∫_A ω|(N, o) := ∫_A (Lω)|(N, o)`. -/
def SheetIntegration.comap (𝓘 : X.SheetIntegration G Ω') (L : Ω →ₗ[ℝ] Ω') :
    X.SheetIntegration G Ω where
  integ ω := 𝓘.integ (L ω)
  integ_add ω τ N g A := by rw [map_add, 𝓘.integ_add]
  integ_smul c ω N g A := by rw [map_smul, 𝓘.integ_smul]
  lindelof := 𝓘.lindelof
  inter_mem := 𝓘.inter_mem
  isMeasIn_inter := 𝓘.isMeasIn_inter
  isNull_tangent_ne := 𝓘.isNull_tangent_ne
  isMeasIn_tangent_eq := 𝓘.isMeasIn_tangent_eq
  integ_hasSum ω := 𝓘.integ_hasSum (L ω)
  integ_null ω := 𝓘.integ_null (L ω)
  integ_congr ω := 𝓘.integ_congr (L ω)
  integ_neg ω := 𝓘.integ_neg (L ω)
  image_mem := 𝓘.image_mem
  isMeasIn_image := 𝓘.isMeasIn_image
  integ_image ω := 𝓘.integ_image (L ω)

theorem SheetIntegration.comap_integ (𝓘 : X.SheetIntegration G Ω') (L : Ω →ₗ[ℝ] Ω') (ω : Ω)
    (N : Set Obj) (g : Obj → X.PObj.OrTangent) (A : Set Obj) :
    (𝓘.comap L).integ ω N g A = 𝓘.integ (L ω) N g A := rfl

end EpGroupoid

namespace EP

variable (A : EP.{u})

/-- **The integration of `0`-forms over oriented points** (2021 p. 422 and §9.5 for `n = 0`):
`∫_{{p}} a|({p}, o) = ±a(p)`, the sign that of the orientation `o` (`frameSign`), for the classes
`a ∈ Ω⁰_{ep,∞}(X)`; the sheets are the smooth points (`pointSheets`), the null sets those of
dimension `0` (`SheetNullSets.point`: the sets not meeting the sheet). -/
def zeroFormIntegration :
    A.X.SheetIntegration (SheetNullSets.point (EpGroupoid.pointSheets A.X)) (A.epFormsInfty 0) :=
  (EpGroupoid.pointIntegration A.X).comap A.zeroFormEvalInv

theorem zeroFormIntegration_integ (a : A.epFormsInfty 0) (N : Set A.Obj)
    (g : A.Obj → A.X.PObj.OrTangent) (B : Set A.Obj) :
    A.zeroFormIntegration.integ a N g B = EpGroupoid.pointInteg (A.zeroFormEval a) N g B := rfl

/-- `∫_{{p}} a|({p}, o) = ±a(p)`. -/
theorem zeroFormIntegration_integ_singleton (a : A.epFormsInfty 0) {p : A.Obj}
    (g : A.Obj → A.X.PObj.OrTangent) {B : Set A.Obj} (hp : p ∈ B) :
    A.zeroFormIntegration.integ a {p} g B = EpGroupoid.frameSign (g p) * A.zeroFormEval a p :=
  EpGroupoid.pointInteg_of_mem subsingleton_singleton ⟨hp, rfl⟩

/-- `∫_B a|(N, o) = 0` when `B ∩ N = ∅`. -/
theorem zeroFormIntegration_integ_of_empty (a : A.epFormsInfty 0) {N : Set A.Obj}
    (g : A.Obj → A.X.PObj.OrTangent) {B : Set A.Obj} (h : B ∩ N = ∅) :
    A.zeroFormIntegration.integ a N g B = 0 :=
  EpGroupoid.pointInteg_of_empty h

end EP

end Polyfold
