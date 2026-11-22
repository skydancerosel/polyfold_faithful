import Polyfold.Chapter17.TangentTransitionStructure

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part IV, Chapter 17,
§17.2 (pp. 781–783): the functor `TΓ : TX → TC` (17.52) and **Proposition 17.2.16**.  Numbers
and pages are the 2021 text's.

# The topology of `|TC|`

## The text, paraphrased

(**Proposition 17.2.16**, p. 782) The orbit space `|TC|` carries a natural metrizable topology;
in particular `TC` is in a natural way a GCT, and `|P| : |TC| → |C¹|` is continuous.  Proof: for a
covering family `Ψ` with model `X = X_Ψ` and equivalence `Γ : X → C`, define `TΓ : TX → TC`
(17.52) by `TΓ(h_λ) = [Ψ_λ(q_λ), Ψ, Tσ(h_λ)]` for `h_λ ∈ T_{q_λ}O_λ`, `Ψ ∈ F(Ψ_λ(q_λ))` and `σ` of
`(q_λ, 1, q)`; `|TΓ| : |TX| → |TC|` is a bijection, `|TX|` is metrizable (Theorem 8.1.15), which
defines the topology of `|TC|`; "it is easily verified" that it does not depend on `Ψ`.

## What is formalized (namespace `Polyfold.GCT.PolyfoldConstruction`)

* `MPolyfold.sigmaTangentElim`, `sigmaTangentElim_mk`, `exists_sigmaTangent`,
  `sigmaTangent_mk_inj`: Part I's tangent of a disjoint union `⊔ X_i` is `⊔ T X_i` through
  `T(Sigma.mk i)`.
* `modelTObjMk`, `modelTMorMk` (the summands of `T(X_Ψ)`) with `tSrc_modelTMorMk`,
  `tTgt_modelTMorMk`, `tUnit_modelTObjMk`, `tBase_modelTMorMk`.
* **`tangentModelFunctor hU Ψ : T(X_Ψ) → TC`** (17.52): a vector `h_λ` goes to `TΨ_λ(h_λ)`, a
  vector `w` of `TM(Ψ_λ, Ψ_λ')` to the morphism of `(Ts w, Φ, Tt w) ∈ M(TΨ_λ, TΨ_λ')`;
  `tangentModelFunctor_full`, `_faithful`, `_essSurj` (for a covering family),
  `exists_tangentUnifObj_eq` (every object of `TC` over `Ψ(q)` is `TΨ(k)`, `τ(k) = q`).
* `bijective_orbitMap_tangentModelFunctor`, `tangentModelOrbitEquiv`, `tangentOrbitTopology` (the
  topology transported along `|TΓ_Ψ|` for a chosen covering family),
  **`isHomeomorph_tangentModelOrbitEquiv`** (a homeomorphism for every covering family),
  `metrizableSpace_tangentOrbit`, `continuous_orbitMap_tangentCatProj`, `tangentGCT`,
  **`proposition_17_2_16`**.

## Readings and proof

* "`Ψ ∈ F(α)`" in (17.52) is read as the reference uniformizer of `α`, i.e. `TΓ(h_λ) = TΨ_λ(h_λ)`
  (T5's `tangentUnifObj`; Lemma 17.2.9: the class does not depend on the choice).
* "Natural topology" is read as the topology for which `|TΓ_Ψ|` is a homeomorphism; we take it
  for one chosen covering family and prove it is the same for all of them.
* Independence of the covering family: for covering families `Ψ`, `Ψ'` let `Ψ'' = Ψ ⊔ Ψ'`; then
  `TΓ_Ψ = TΓ_Ψ'' ∘ T(X_Ψ → X_Ψ'')` and `TΓ_Ψ' = TΓ_Ψ'' ∘ T(X_Ψ' → X_Ψ'')` on objects, and the two
  inclusions are equivalences, hence so are their tangents (Theorem 10.1.7), whose orbit maps are
  homeomorphisms.
* `|P|` is continuous because `|P| ∘ |TΓ_Ψ| = |Γ_Ψ¹| ∘ |p|` with `p : TX_Ψ → X_Ψ¹` the
  projection (Theorem 8.1.1) and `|Γ_Ψ¹|` the homeomorphism of p. 766.
-/

set_option maxSynthPendingDepth 3

open Set Function Topology

noncomputable section

namespace Polyfold

universe u

/-! ### The tangent of a disjoint union -/

namespace MPolyfold

section SigmaTangent

variable {ι : Type*} {X : ι → Type*} [∀ i, TopologicalSpace (X i)] [∀ i, T2Space (X i)]
  [∀ i, ParacompactSpace (X i)] (P : ∀ i, MPolyfold (X i))

/-- The summand of the base point of a vector of `T(⊔ X_i)`. -/
abbrev sigmaTangentIdx (v : (sigma P).TangentSpace) : ι :=
  ((sigma P).levelVal 1 ((sigma P).tangentProj v)).1

/-- The vector of `T X_i` (`i` the summand of the base point) which `T(Sigma.mk i)` maps to `v`. -/
def sigmaTangentComp (v : (sigma P).TangentSpace) : (P (sigmaTangentIdx P v)).TangentSpace :=
  tangentMapOn (isScSmoothOn_sigmaProj P (sigmaTangentIdx P v)
    ((sigma P).levelVal 1 ((sigma P).tangentProj v)).2) v

theorem tangentMap_sigmaMk_sigmaTangentComp (v : (sigma P).TangentSpace) :
    tangentMap (isScSmoothMap_sigmaMk P (sigmaTangentIdx P v)) (sigmaTangentComp P v) = v :=
  ((isScDiffeoOn_sigmaMk P _ _).tangentMap (isScSmoothMap_sigmaMk P _)).right_inv v
    ⟨_, rfl⟩

/-- **`T(⊔ X_i) = ⊔ T X_i`**: every vector is `T(Sigma.mk i)(k)`. -/
theorem exists_sigmaTangent (v : (sigma P).TangentSpace) :
    ∃ i k, tangentMap (isScSmoothMap_sigmaMk P i) k = v :=
  ⟨_, _, tangentMap_sigmaMk_sigmaTangentComp P v⟩

theorem basePt_tangentMap_sigmaMk (i : ι) (k : (P i).TangentSpace) :
    (sigma P).levelVal 1 ((sigma P).tangentProj (tangentMap (isScSmoothMap_sigmaMk P i) k)) =
      ⟨i, (P i).levelVal 1 ((P i).tangentProj k)⟩ :=
  levelVal_tangentProj_tangentMap _ k

/-- `T(Sigma.mk i)(k) = T(Sigma.mk j)(c)` forces `i = j` and `k = c`. -/
theorem sigmaTangent_mk_inj {i j : ι} {k : (P i).TangentSpace} {c : (P j).TangentSpace}
    (h : tangentMap (isScSmoothMap_sigmaMk P i) k = tangentMap (isScSmoothMap_sigmaMk P j) c) :
    i = j ∧ HEq k c := by
  have hb := congrArg (fun v => ((sigma P).levelVal 1 ((sigma P).tangentProj v)).1) h
  simp only [basePt_tangentMap_sigmaMk] at hb
  subst hb
  refine ⟨rfl, heq_of_eq ?_⟩
  exact ((isScDiffeoOn_sigmaMk P i ((P i).levelVal 1 ((P i).tangentProj k))).tangentMap
    (isScSmoothMap_sigmaMk P i)).injOn (mem_univ _) (mem_univ _) h

/-- A function on `⊔ T X_i`, read on `T(⊔ X_i)`. -/
def sigmaTangentElim {R : Sort*} (F : ∀ i, (P i).TangentSpace → R) (v : (sigma P).TangentSpace) :
    R :=
  F (sigmaTangentIdx P v) (sigmaTangentComp P v)

@[simp] theorem sigmaTangentElim_mk {R : Sort*} (F : ∀ i, (P i).TangentSpace → R) (i : ι)
    (k : (P i).TangentSpace) :
    sigmaTangentElim P F (tangentMap (isScSmoothMap_sigmaMk P i) k) = F i k := by
  have key : ∀ j (c : (P j).TangentSpace),
      tangentMap (isScSmoothMap_sigmaMk P j) c = tangentMap (isScSmoothMap_sigmaMk P i) k →
        F j c = F i k := by
    intro j c h
    obtain ⟨rfl, h2⟩ := sigmaTangent_mk_inj P h
    rw [eq_of_heq h2]
  exact key _ _ (tangentMap_sigmaMk_sigmaTangentComp P _)

end SigmaTangent

end MPolyfold


namespace GCT.PolyfoldConstruction

variable {C : GCT.{u}} {S : C.PolyfoldConstruction}

/-! ### The tangent `T(X_Ψ)` of the model, summand by summand -/

section ModelTangent

variable {ι : Type u} (Ψ : ι → S.Unif)

/-- `T(Sigma.mk λ) : TO_λ → T(⊔ O_λ)`. -/
abbrev modelTObjMk (i : ι) : (Ψ i).1.P.TangentSpace → (S.modelEpGroupoid Ψ).PObj.TangentSpace :=
  MPolyfold.tangentMap (MPolyfold.isScSmoothMap_sigmaMk (fun i => (Ψ i).1.P) i)

/-- `T(Sigma.mk (λ, λ')) : TM(Ψ_λ, Ψ_λ') → T(⊔ M(Ψ_λ, Ψ_λ'))`. -/
abbrev modelTMorMk (p : ι × ι) :
    (S.transPolyfold (Ψ p.1) (Ψ p.2)).TangentSpace → (S.modelEpGroupoid Ψ).PMor.TangentSpace :=
  MPolyfold.tangentMap
    (MPolyfold.isScSmoothMap_sigmaMk (fun p : ι × ι => S.transPolyfold (Ψ p.1) (Ψ p.2)) p)

variable {Ψ}

theorem exists_modelTObjMk (v : (S.modelEpGroupoid Ψ).PObj.TangentSpace) :
    ∃ i k, modelTObjMk Ψ i k = v :=
  MPolyfold.exists_sigmaTangent _ v

theorem exists_modelTMorMk (v : (S.modelEpGroupoid Ψ).PMor.TangentSpace) :
    ∃ p w, modelTMorMk Ψ p w = v :=
  MPolyfold.exists_sigmaTangent _ v

theorem tSrc_modelTMorMk (p : ι × ι) (w : (S.transPolyfold (Ψ p.1) (Ψ p.2)).TangentSpace) :
    (S.modelEpGroupoid Ψ).tSrc (modelTMorMk Ψ p w) = modelTObjMk Ψ p.1 (S.trTSrc _ _ w) :=
  MPolyfold.tangentMap_tangentMap_comm (S.modelEpGroupoid Ψ).isScSmoothMap_src
    (MPolyfold.isScSmoothMap_sigmaMk _ p) (MPolyfold.isScSmoothMap_sigmaMk _ p.1)
    (S.isLocalScDiffeo_trSrc _ _).isScSmoothMap rfl w

theorem tTgt_modelTMorMk (p : ι × ι) (w : (S.transPolyfold (Ψ p.1) (Ψ p.2)).TangentSpace) :
    (S.modelEpGroupoid Ψ).tTgt (modelTMorMk Ψ p w) = modelTObjMk Ψ p.2 (S.trTTgt _ _ w) :=
  MPolyfold.tangentMap_tangentMap_comm (S.modelEpGroupoid Ψ).isScSmoothMap_tgt
    (MPolyfold.isScSmoothMap_sigmaMk _ p) (MPolyfold.isScSmoothMap_sigmaMk _ p.2)
    (S.isLocalScDiffeo_trTgt _ _).isScSmoothMap rfl w

theorem tUnit_modelTObjMk (i : ι) (k : (Ψ i).1.P.TangentSpace) :
    (S.modelEpGroupoid Ψ).tUnit (modelTObjMk Ψ i k) = modelTMorMk Ψ (i, i) (trTUnit (Ψ i) k) :=
  MPolyfold.tangentMap_tangentMap_comm (S.modelEpGroupoid Ψ).isScSmoothMap_unit
    (MPolyfold.isScSmoothMap_sigmaMk _ i) (MPolyfold.isScSmoothMap_sigmaMk _ (i, i))
    (S.isScSmoothMap_trUnit _) rfl k

theorem tBase_modelTMorMk (p : ι × ι) (w : (S.transPolyfold (Ψ p.1) (Ψ p.2)).TangentSpace) :
    (S.modelEpGroupoid Ψ).tBase (modelTMorMk Ψ p w) = ⟨p, trBase w⟩ :=
  MPolyfold.levelVal_tangentProj_tangentMap _ w

theorem basePt_modelTObjMk (i : ι) (k : (Ψ i).1.P.TangentSpace) :
    (S.modelEpGroupoid Ψ).PObj.levelVal 1 ((S.modelEpGroupoid Ψ).PObj.tangentProj
      (modelTObjMk Ψ i k)) = ⟨i, basePt (Ψ i) k⟩ :=
  MPolyfold.levelVal_tangentProj_tangentMap _ k

end ModelTangent

/-! ### The functor `TΓ_Ψ : T(X_Ψ) → TC` (17.52) -/

section TangentModelFunctor

variable (hU : S.HasUniformizers) {ι : Type u} (Ψ : ι → S.Unif)

/-- `TΓ_Ψ` on objects: `T_{q_λ}O_λ ∋ h_λ ↦ [Ψ_λ(q_λ), Ψ_λ, h_λ]`. -/
def tangentModelObj (v : (S.modelEpGroupoid Ψ).PObj.TangentSpace) : S.TangentCatObj :=
  MPolyfold.sigmaTangentElim (fun i => (Ψ i).1.P) (fun i k => S.tangentUnifObj hU (Ψ i) k) v

/-- `TΓ_Ψ` on morphisms (17.52): `TΓ(h_λ) = [Ψ_λ(q_λ), Ψ_λ, Tσ(h_λ)]`, i.e. a vector `w` of
`TM(Ψ_λ, Ψ_λ')` goes to the morphism of `TC` underlying `(Ts w, Φ, Tt w) ∈ M(TΨ_λ, TΨ_λ')`. -/
def tangentModelMor (W : (S.modelEpGroupoid Ψ).PMor.TangentSpace) : S.TangentCatMor :=
  MPolyfold.sigmaTangentElim (fun p : ι × ι => S.transPolyfold (Ψ p.1) (Ψ p.2))
    (fun _ w => (tangentTrMap hU w).mor) W

variable {Ψ}

@[simp] theorem tangentModelObj_mk (i : ι) (k : (Ψ i).1.P.TangentSpace) :
    S.tangentModelObj hU Ψ (modelTObjMk Ψ i k) = S.tangentUnifObj hU (Ψ i) k :=
  MPolyfold.sigmaTangentElim_mk (fun i => (Ψ i).1.P) (fun i k => S.tangentUnifObj hU (Ψ i) k) i k

@[simp] theorem tangentModelMor_mk (p : ι × ι)
    (w : (S.transPolyfold (Ψ p.1) (Ψ p.2)).TangentSpace) :
    S.tangentModelMor hU Ψ (modelTMorMk Ψ p w) = (tangentTrMap hU w).mor :=
  MPolyfold.sigmaTangentElim_mk (fun p : ι × ι => S.transPolyfold (Ψ p.1) (Ψ p.2))
    (fun _ w => (tangentTrMap hU w).mor) p w

theorem tangentModelMor_src (W : (S.modelEpGroupoid Ψ).PMor.TangentSpace) :
    (S.tangentModelMor hU Ψ W).src = S.tangentModelObj hU Ψ ((S.modelEpGroupoid Ψ).tSrc W) := by
  obtain ⟨p, w, rfl⟩ := exists_modelTMorMk W
  rw [tangentModelMor_mk, tSrc_modelTMorMk, tangentModelObj_mk]
  exact (tangentTrMap hU w).src_mor

theorem tangentModelMor_tgt (W : (S.modelEpGroupoid Ψ).PMor.TangentSpace) :
    (S.tangentModelMor hU Ψ W).tgt = S.tangentModelObj hU Ψ ((S.modelEpGroupoid Ψ).tTgt W) := by
  obtain ⟨p, w, rfl⟩ := exists_modelTMorMk W
  rw [tangentModelMor_mk, tTgt_modelTMorMk, tangentModelObj_mk, ← tangentTrMap_tgt (hU := hU) w]
  exact (tangentTrMap hU w).tgt_mor

theorem tangentModelMor_mor (W : (S.modelEpGroupoid Ψ).PMor.TangentSpace) :
    (S.tangentModelMor hU Ψ W).mor = ((S.modelEpGroupoid Ψ).tBase W).2.mor := by
  obtain ⟨p, w, rfl⟩ := exists_modelTMorMk W
  rw [tangentModelMor_mk, tBase_modelTMorMk, tangentTrMap_mor]

variable (Ψ)

/-- **The functor `TΓ_Ψ : T(X_Ψ) → TC`** (2021 (17.52), p. 782). -/
def tangentModelFunctor :
    GroupoidFunctor (S.modelEpGroupoid Ψ).tangentGroupoidStr S.tangentCatGroupoid where
  obj := S.tangentModelObj hU Ψ
  mor := S.tangentModelMor hU Ψ
  src_mor W := tangentModelMor_src hU W
  tgt_mor W := tangentModelMor_tgt hU W
  mor_comp φ ψ h := by
    have h' : (S.modelEpGroupoid Ψ).tSrc φ = (S.modelEpGroupoid Ψ).tTgt ψ := h
    have hb := (S.modelEpGroupoid Ψ).src_tBase_eq h'
    have hm : C.toGroupoidStr.src (S.tangentModelMor hU Ψ φ).mor =
        C.toGroupoidStr.tgt (S.tangentModelMor hU Ψ ψ).mor := by
      refine TangentCatMor.mor_composable ?_
      rw [tangentModelMor_src, tangentModelMor_tgt, h']
    refine TangentCatMor.ext' ?_ ?_
    · change _ = ((S.tangentModelMor hU Ψ φ).comp (S.tangentModelMor hU Ψ ψ)).src
      rw [TangentCatMor.comp_src hm, tangentModelMor_src, tangentModelMor_src]
      exact congrArg _ ((S.modelEpGroupoid Ψ).tSrc_tComp h')
    · change _ = ((S.tangentModelMor hU Ψ φ).comp (S.tangentModelMor hU Ψ ψ)).mor
      rw [TangentCatMor.comp_mor hm, tangentModelMor_mor, tangentModelMor_mor,
        tangentModelMor_mor]
      change (((S.modelEpGroupoid Ψ).tBase ((S.modelEpGroupoid Ψ).tComp φ ψ))).2.mor = _
      rw [(S.modelEpGroupoid Ψ).tBase_tComp h']
      exact modelGroupoid_comp_mor hb
  mor_unit v := by
    obtain ⟨i, k, rfl⟩ := exists_modelTObjMk v
    change S.tangentModelMor hU Ψ ((S.modelEpGroupoid Ψ).tUnit (modelTObjMk Ψ i k)) = _
    rw [tUnit_modelTObjMk, tangentModelMor_mk, tangentTrMap_trTUnit, tangentModelObj_mk]
    rfl

@[simp] theorem tangentModelFunctor_obj (v : (S.modelEpGroupoid Ψ).PObj.TangentSpace) :
    (S.tangentModelFunctor hU Ψ).obj v = S.tangentModelObj hU Ψ v := rfl

@[simp] theorem tangentModelFunctor_mor (W : (S.modelEpGroupoid Ψ).PMor.TangentSpace) :
    (S.tangentModelFunctor hU Ψ).mor W = S.tangentModelMor hU Ψ W := rfl

/-- `TΓ_Ψ` is full. -/
theorem tangentModelFunctor_full : (S.tangentModelFunctor hU Ψ).toFunctor.Full := by
  refine (GroupoidFunctor.full_iff _).2 fun x x' ψ hs ht => ?_
  obtain ⟨i, k, rfl⟩ := exists_modelTObjMk x
  obtain ⟨j, k', rfl⟩ := exists_modelTObjMk x'
  rw [tangentModelFunctor_obj, tangentModelObj_mk] at hs ht
  let y : S.TTr hU (Ψ i) (Ψ j) := ⟨k, ψ, k', hs, ht⟩
  obtain ⟨w, hw⟩ := surjective_tangentTrMap (hU := hU) y
  refine ⟨modelTMorMk Ψ (i, j) w, ?_, ?_, ?_⟩
  · change (S.modelEpGroupoid Ψ).tSrc _ = _
    rw [tSrc_modelTMorMk]
    exact congrArg (modelTObjMk Ψ i) (congrArg GroupoidStr.TransitionSet.src hw)
  · change (S.modelEpGroupoid Ψ).tTgt _ = _
    rw [tTgt_modelTMorMk, ← tangentTrMap_tgt (hU := hU) w]
    exact congrArg (modelTObjMk Ψ j) (congrArg GroupoidStr.TransitionSet.tgt hw)
  · rw [tangentModelFunctor_mor, tangentModelMor_mk]
    exact congrArg GroupoidStr.TransitionSet.mor hw

/-- `TΓ_Ψ` is faithful. -/
theorem tangentModelFunctor_faithful : (S.tangentModelFunctor hU Ψ).toFunctor.Faithful := by
  refine (GroupoidFunctor.faithful_iff _).2 fun φ φ' hs ht he => ?_
  obtain ⟨⟨i, j⟩, w, rfl⟩ := exists_modelTMorMk φ
  obtain ⟨⟨i', j'⟩, w', rfl⟩ := exists_modelTMorMk φ'
  change (S.modelEpGroupoid Ψ).tSrc _ = (S.modelEpGroupoid Ψ).tSrc _ at hs
  change (S.modelEpGroupoid Ψ).tTgt _ = (S.modelEpGroupoid Ψ).tTgt _ at ht
  rw [tSrc_modelTMorMk, tSrc_modelTMorMk] at hs
  rw [tTgt_modelTMorMk, tTgt_modelTMorMk] at ht
  obtain ⟨rfl, hs'⟩ := MPolyfold.sigmaTangent_mk_inj (fun i => (Ψ i).1.P) hs
  obtain ⟨rfl, -⟩ := MPolyfold.sigmaTangent_mk_inj (fun i => (Ψ i).1.P) ht
  rw [tangentModelFunctor_mor, tangentModelFunctor_mor, tangentModelMor_mk,
    tangentModelMor_mk] at he
  refine congrArg _ (injective_tangentTrMap (hU := hU) (TTr.ext' (eq_of_heq hs') ?_))
  exact congrArg TangentCatMor.mor he

/-- Every object of `TC` over `Ψ(q)` is `TΨ(k)` for a `k ∈ T_qO`. -/
theorem exists_tangentUnifObj_eq (Ψ₀ : S.Unif) (e : S.TangentCatObj) (q : Ψ₀.1.O)
    (hq : Ψ₀.1.obj q = e.base) : ∃ k, basePt Ψ₀ k = q ∧ S.tangentUnifObj hU Ψ₀ k = e := by
  obtain ⟨α, hα, v⟩ := e
  dsimp only at hq
  subst hq
  have hv := levelVal_tangentProj_of_mem v.2
  set k := S.transMap (S.unitTr (S.refQ hα) q (obj_refPoint hα) rfl) v.1 with hk_def
  have hk : basePt Ψ₀ k = q := base_transMap _ hv
  refine ⟨k, hk, TangentCatObj.ext_of (congrArg Ψ₀.1.obj hk) ?_⟩
  refine transMap_three_eq_self _ _ (S.unitTr (S.refQ hα) q (obj_refPoint hα) rfl) rfl hk ?_ rfl hv
  change C.toGroupoidStr.comp (C.toGroupoidStr.comp (C.toGroupoidStr.unit (Ψ₀.1.obj q))
    (C.toGroupoidStr.unit (Ψ₀.1.obj (basePt Ψ₀ k)))) (C.toGroupoidStr.unit (Ψ₀.1.obj q)) =
      C.toGroupoidStr.unit ((S.refUnif hα).1.obj (S.refQ hα))
  rw [hk, obj_refPoint hα, GroupoidStr.unit_comp_of_eq (C.toGroupoidStr.tgt_unit _),
    GroupoidStr.unit_comp_of_eq (C.toGroupoidStr.tgt_unit _)]

variable {Ψ} in
/-- `TΓ_Ψ` is essentially surjective for a covering family. -/
theorem tangentModelFunctor_essSurj (hΨ : S.IsCoveringFamily Ψ) :
    (S.tangentModelFunctor hU Ψ).toFunctor.EssSurj := by
  refine (GroupoidFunctor.essSurj_iff _).2 fun e => ?_
  obtain ⟨i, hi⟩ := mem_iUnion.1 (hΨ.symm ▸ mem_univ (C.toGroupoidStr.π e.base))
  obtain ⟨q, hq⟩ := (Ψ i).1.mem_footprint_iff.1 hi
  obtain ⟨φ, hs, ht⟩ := (GroupoidStr.π_eq_π_iff _).1 hq
  have hreg : S.HasRegularity 1 ((Ψ i).1.obj q) :=
    e.isObj.1.of_isomorphic ⟨C.toGroupoidStr.inv φ, (C.toGroupoidStr.src_inv _).trans ht,
      (C.toGroupoidStr.tgt_inv _).trans hs⟩
  let Φ : S.TangentCatMor := ⟨e, C.toGroupoidStr.inv φ, (C.toGroupoidStr.src_inv _).trans ht,
    TangentObj.of_eq (hs.symm.trans (C.toGroupoidStr.tgt_inv _).symm) ⟨hreg, hU _⟩⟩
  obtain ⟨k, -, hk⟩ := exists_tangentUnifObj_eq hU (Ψ i) Φ.tgt q
    (hs.symm.trans (C.toGroupoidStr.tgt_inv _).symm)
  refine ⟨modelTObjMk Ψ i k, Φ.inv, ?_, Φ.tgt_inv⟩
  rw [tangentModelFunctor_obj, tangentModelObj_mk, hk]
  rfl

end TangentModelFunctor

/-! ### Proposition 17.2.16: the topology of `|TC|` -/

section TangentOrbit

variable (hU : S.HasUniformizers)

/-- `TΓ_Φ ∘ T(X_{Φ ∘ σ} → X_Φ) = TΓ_{Φ ∘ σ}` on objects. -/
theorem tangentModelObj_modelMap {ι κ : Type u} (Φ : ι → S.Unif) (σ : κ → ι)
    (v : (S.modelEpGroupoid (Φ ∘ σ)).PObj.TangentSpace) :
    S.tangentModelObj hU Φ ((S.modelMap Φ σ).tangent.obj v) = S.tangentModelObj hU (Φ ∘ σ) v := by
  obtain ⟨i, k, rfl⟩ := exists_modelTObjMk v
  have h : (S.modelMap Φ σ).tangent.obj (modelTObjMk (Φ ∘ σ) i k) = modelTObjMk Φ (σ i) k :=
    MPolyfold.tangentMap_tangentMap_of_eq (S.modelMap Φ σ).isScSmoothMap_obj
      (MPolyfold.isScSmoothMap_sigmaMk (fun j => ((Φ ∘ σ) j).1.P) i)
      (MPolyfold.isScSmoothMap_sigmaMk (fun j => (Φ j).1.P) (σ i)) (by rfl) k
  rw [h, tangentModelObj_mk, tangentModelObj_mk]
  rfl

/-- `|TΓ_Φ| ∘ |T(X_{Φ ∘ σ} → X_Φ)| = |TΓ_{Φ ∘ σ}|`. -/
theorem orbitMap_tangentModelFunctor_modelMap {ι κ : Type u} (Φ : ι → S.Unif) (σ : κ → ι) :
    (S.tangentModelFunctor hU Φ).orbitMap ∘ (S.modelMap Φ σ).tangent.orbitMap =
      (S.tangentModelFunctor hU (Φ ∘ σ)).orbitMap := by
  funext z
  induction z using Quotient.inductionOn with
  | h v => exact congrArg S.tangentCatGroupoid.π (tangentModelObj_modelMap hU Φ σ v)

/-- **`|TΓ_Ψ| : |T(X_Ψ)| → |TC|` is a bijection** for a covering family (p. 783). -/
theorem bijective_orbitMap_tangentModelFunctor (c : S.CoveringFamily) :
    Bijective (S.tangentModelFunctor hU c.Ψ).orbitMap :=
  ⟨GroupoidFunctor.injective_orbitMap_of_full _ (S.tangentModelFunctor_full hU c.Ψ),
    (GroupoidFunctor.surjective_orbitMap_iff _).2 (S.tangentModelFunctor_essSurj hU c.cover)⟩

/-- `|TΓ_Ψ|` as a bijection `|T(X_Ψ)| ≃ |TC|`. -/
def tangentModelOrbitEquiv (c : S.CoveringFamily) :
    (S.modelEpGroupoid c.Ψ).tangentEpGroupoid.OrbitSpace ≃ S.tangentCatGroupoid.OrbitSpace :=
  Equiv.ofBijective _ (S.bijective_orbitMap_tangentModelFunctor hU c)

@[simp] theorem tangentModelOrbitEquiv_apply (c : S.CoveringFamily)
    (z : (S.modelEpGroupoid c.Ψ).tangentEpGroupoid.OrbitSpace) :
    S.tangentModelOrbitEquiv hU c z = (S.tangentModelFunctor hU c.Ψ).orbitMap z := rfl

/-- The covering family chosen to transport the topology. -/
def tangentCover : S.CoveringFamily :=
  (S.exists_coveringFamily_iff.2 (S.hasCoveringUniformizers_of_hasUniformizers hU)).some

/-- **The natural topology of `|TC|`** (Proposition 17.2.16), transported from `|T(X_Ψ)|` along
`|TΓ_Ψ|` for the chosen covering family (`isHomeomorph_tangentModelOrbitEquiv`: the same for
every covering family). -/
@[instance_reducible]
def tangentOrbitTopology : TopologicalSpace S.tangentCatGroupoid.OrbitSpace :=
  TopologicalSpace.coinduced (S.tangentModelOrbitEquiv hU (S.tangentCover hU)) inferInstance

/-- The union of two covering families. -/
def CoveringFamily.union (c c' : S.CoveringFamily) : S.CoveringFamily where
  ι := c.ι ⊕ c'.ι
  Ψ := Sum.elim c.Ψ c'.Ψ
  cover := IsCoveringFamily.of_comp (σ := Sum.inl) c.cover

/-- `|T(X_Ψ) → T(X_Φ)|` is a homeomorphism for covering families `Ψ = Φ ∘ σ`. -/
theorem isHomeomorph_orbitMap_tangent_modelMap {ι κ : Type u} {Φ : ι → S.Unif} {σ : κ → ι}
    (h : S.IsCoveringFamily (Φ ∘ σ)) : IsHomeomorph (S.modelMap Φ σ).tangent.orbitMap :=
  (EpFunctor.theorem_10_1_7 (S.isEquivalence_modelMap h)).isHomeomorph_orbitMap

/-- **`|TΓ_Ψ| : |T(X_Ψ)| → |TC|` is a homeomorphism for every covering family** (Proposition
17.2.16: the topology does not depend on the covering family). -/
theorem isHomeomorph_tangentModelOrbitEquiv (c : S.CoveringFamily) :
    @IsHomeomorph _ _ _ (S.tangentOrbitTopology hU) (S.tangentModelOrbitEquiv hU c) := by
  let := S.tangentOrbitTopology hU
  set c₀ := S.tangentCover hU
  set d := CoveringFamily.union c c₀
  have h₀ : IsHomeomorph (S.tangentModelOrbitEquiv hU c₀) :=
    ((S.tangentModelOrbitEquiv hU c₀).toHomeomorph fun _ => isOpen_coinduced.symm).isHomeomorph
  have hA := S.isHomeomorph_orbitMap_tangent_modelMap (Φ := d.Ψ) (σ := Sum.inl) c.cover
  have hB := S.isHomeomorph_orbitMap_tangent_modelMap (Φ := d.Ψ) (σ := Sum.inr) c₀.cover
  have hc : ⇑(S.tangentModelOrbitEquiv hU c) =
      (S.tangentModelFunctor hU d.Ψ).orbitMap ∘ (S.modelMap d.Ψ Sum.inl).tangent.orbitMap :=
    (orbitMap_tangentModelFunctor_modelMap hU d.Ψ Sum.inl).symm
  have hc₀ : ⇑(S.tangentModelOrbitEquiv hU c₀) =
      (S.tangentModelFunctor hU d.Ψ).orbitMap ∘ (S.modelMap d.Ψ Sum.inr).tangent.orbitMap :=
    (orbitMap_tangentModelFunctor_modelMap hU d.Ψ Sum.inr).symm
  have hd : (S.tangentModelFunctor hU d.Ψ).orbitMap =
      S.tangentModelOrbitEquiv hU c₀ ∘ (hB.homeomorph _).symm := by
    rw [hc₀]
    funext y
    exact (congrArg (S.tangentModelFunctor hU d.Ψ).orbitMap
      ((hB.homeomorph _).apply_symm_apply y)).symm
  rw [hc, hd]
  exact (h₀.comp (hB.homeomorph _).symm.isHomeomorph).comp hA

/-- `|TΓ_Ψ|` as a homeomorphism `|T(X_Ψ)| ≃ₜ |TC|`. -/
def tangentModelOrbitHomeomorph (c : S.CoveringFamily) :
    @Homeomorph (S.modelEpGroupoid c.Ψ).tangentEpGroupoid.OrbitSpace
      S.tangentCatGroupoid.OrbitSpace _ (S.tangentOrbitTopology hU) :=
  @IsHomeomorph.homeomorph _ _ _ (S.tangentOrbitTopology hU) _
    (S.isHomeomorph_tangentModelOrbitEquiv hU c)

/-- **`|TC|` is metrizable** (Proposition 17.2.16). -/
theorem metrizableSpace_tangentOrbit :
    @TopologicalSpace.MetrizableSpace S.tangentCatGroupoid.OrbitSpace (S.tangentOrbitTopology hU) := by
  let := S.tangentOrbitTopology hU
  have := (S.modelEpGroupoid (S.tangentCover hU).Ψ).metrizableSpace_tangent_orbitSpace
    (S.hasParacompactOrbitSpace_model _)
  exact (S.tangentModelOrbitHomeomorph hU (S.tangentCover hU)).symm.isEmbedding.metrizableSpace

/-- `P ∘ TΓ_Ψ = Γ_Ψ¹ ∘ p` on objects. -/
theorem tangentCatProj_tangentModelObj {ι : Type u} (Ψ : ι → S.Unif)
    (v : (S.modelEpGroupoid Ψ).PObj.TangentSpace) :
    S.tangentCatProj.obj (S.tangentModelObj hU Ψ v) =
      (S.modelFunctorOne Ψ).obj ((S.modelEpGroupoid Ψ).PObj.tangentProj v) := by
  obtain ⟨i, k, rfl⟩ := exists_modelTObjMk v
  refine Subtype.ext ?_
  rw [tangentModelObj_mk]
  change (Ψ i).1.obj (basePt (Ψ i) k) =
    S.modelObjMap Ψ ((S.modelEpGroupoid Ψ).PObj.levelVal 1
      ((S.modelEpGroupoid Ψ).PObj.tangentProj (modelTObjMk Ψ i k)))
  rw [basePt_modelTObjMk]
  rfl

/-- **`|P| : |TC| → |C¹|` is continuous** (Proposition 17.2.16). -/
theorem continuous_orbitMap_tangentCatProj :
    @Continuous _ _ (S.tangentOrbitTopology hU)
      (S.levelOneTopology (S.hasCoveringUniformizers_of_hasUniformizers hU))
      S.tangentCatProj.orbitMap := by
  let := S.tangentOrbitTopology hU
  let hc := S.hasCoveringUniformizers_of_hasUniformizers hU
  let := S.levelOneTopology hc
  set c₀ := S.tangentCover hU
  rw [continuous_coinduced_dom]
  have h : S.tangentCatProj.orbitMap ∘ S.tangentModelOrbitEquiv hU c₀ =
      S.modelOrbitEquivOne c₀ ∘ (S.modelEpGroupoid c₀.Ψ).tangentProjFunctor.orbitMap := by
    funext z
    induction z using Quotient.inductionOn with
    | h v => exact congrArg (S.regSub 1).π (tangentCatProj_tangentModelObj hU c₀.Ψ v)
  rw [h]
  exact (S.isHomeomorph_modelOrbitEquivOne hc c₀).continuous.comp
    (EpFunctor.continuous_orbitMap _)

/-- **The GCT `TC`** (Proposition 17.2.16: "in particular `TC` is in a natural way a GCT"): the
groupoidal category `TC` (Lemma 17.2.7) with the natural metrizable topology on `|TC|`. -/
def tangentGCT : GCT.{max u 1} where
  toGroupoidalCategory := S.tangentCategory
  top := S.tangentOrbitTopology hU
  metrizable := S.metrizableSpace_tangentOrbit hU

theorem tangentGCT_toGroupoidStr : (S.tangentGCT hU).toGroupoidStr = S.tangentCatGroupoid := rfl

/-- **Proposition 17.2.16** (2021 p. 782): for a covering family `Ψ`, `TΓ_Ψ : T(X_Ψ) → TC` (17.52) is
full, faithful and essentially surjective, and `|TΓ_Ψ| : |T(X_Ψ)| → |TC|` is a bijection; the
orbit space `|TC|` carries a natural metrizable topology, for which `|TΓ_Ψ|` is a homeomorphism for
every covering family (so the topology does not depend on the covering family); `TC` is a GCT;
and `|P| : |TC| → |C¹|` is continuous. -/
theorem proposition_17_2_16 :
    (∀ c : S.CoveringFamily, (S.tangentModelFunctor hU c.Ψ).toFunctor.Full ∧
      (S.tangentModelFunctor hU c.Ψ).toFunctor.Faithful ∧
      (S.tangentModelFunctor hU c.Ψ).toFunctor.EssSurj ∧
      Bijective (S.tangentModelFunctor hU c.Ψ).orbitMap ∧
      @IsHomeomorph _ _ _ (S.tangentOrbitTopology hU) (S.tangentModelFunctor hU c.Ψ).orbitMap) ∧
    @TopologicalSpace.MetrizableSpace S.tangentCatGroupoid.OrbitSpace (S.tangentOrbitTopology hU) ∧
    (S.tangentGCT hU).toGroupoidStr = S.tangentCatGroupoid ∧
    @Continuous _ _ (S.tangentOrbitTopology hU)
      (S.levelOneTopology (S.hasCoveringUniformizers_of_hasUniformizers hU))
      S.tangentCatProj.orbitMap :=
  ⟨fun c => ⟨S.tangentModelFunctor_full hU c.Ψ, S.tangentModelFunctor_faithful hU c.Ψ,
      S.tangentModelFunctor_essSurj hU c.cover, S.bijective_orbitMap_tangentModelFunctor hU c,
      S.isHomeomorph_tangentModelOrbitEquiv hU c⟩,
    S.metrizableSpace_tangentOrbit hU, rfl, S.continuous_orbitMap_tangentCatProj hU⟩

end TangentOrbit

end GCT.PolyfoldConstruction

end Polyfold
