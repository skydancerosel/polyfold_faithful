import Polyfold.Chapter8.GeometricLift
import Polyfold.Chapter7.NonVacuity
import Polyfold.Chapter2.LocConnected

set_option maxSynthPendingDepth 3
set_option linter.unusedSectionVars false

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part IV, Chapter 17, §17.8
"Proper Covering Constructions": **Definition 17.8.4** (p. 831, proper ep-groupoid covering model),
**Remark 17.8.5** (p. 831), **Lemma 17.8.7** (p. 833), **Lemma 17.8.8** (pp. 833–834) and
**Lemma 17.8.9** (p. 834), with the maps `φ ∗` of p. 834.  Numbers and pages are the 2021 text's.

# Proper covering models

## The text, paraphrased

(Definition 17.8.4) A proper (ep-groupoid) covering model consists of a translation groupoid
`G ⋉ O` of a finite group acting by sc-diffeomorphisms on an M-polyfold `O`, a point `ō ∈ O` fixed
by `G`, an ep-groupoid `E` and an sc-smooth functor `τ̂ : E → G ⋉ O` with (1) `τ̂ : E → O` a
surjective local sc-diffeomorphism on objects; (2) mutually disjoint open neighbourhoods `U(y)` of
the `y ∈ τ̂⁻¹(ō)` with `E = ⊔_{y ∈ τ̂⁻¹(ō)} U(y)` and `τ̂ : U(y) → O` sc-diffeomorphisms; (3)
`Γ : 𝐄 → (G ⋉ O) ₛ×_τ̂ E`, `ψ ↦ (τ̂(ψ), s(ψ))`, an sc-diffeomorphism.  It is connected if `O` is.
(Remark 17.8.5) Compare with Definition 8.5.1 and Theorems 8.5.3, 8.5.8.
(Lemma 17.8.7) For `O` connected, `ψ ↦ (y_{s(ψ)}, y_{t(ψ)})` is locally constant, `y_e` the point of
`τ̂⁻¹(ō)` with `e ∈ U(y_e)`.  (Lemma 17.8.8) For `φ ∈ 𝐀_ō` (the morphisms between points of
`τ̂⁻¹(ō)`), `𝐄^φ` the connected component of `φ`: distinct `φ` have disjoint `𝐄^φ`, and
`𝐄 = ⋃ 𝐄^φ`; the proof joins `ψ` to `Γ⁻¹((g_ψ, ō), y)` by a path.  (Lemma 17.8.9) On `𝐄^φ`,
`φ : y → y'`, `t(ψ) = τ_{y'}⁻¹(g_φ ∗ τ_y(s(ψ)))`.  The maps `φ ∗ = τ_{t φ}⁻¹ ∘ (g_φ ∗) ∘ τ_{s φ}`
satisfy `(φ' ∘ φ) ∗ = φ' ∗ ∘ φ ∗`.

## What is formalized

* **Definition 17.8.4**: `ProperCoveringModel τ` for `τ : EpFunctor E (actionEpGroupoid hP)`, the
  data `pt` (`ō`), `U`, `σ` (`σ y = (τ̂|U(y))⁻¹`) and the properties (1)–(3); (3) is literally
  Definition 8.5.1 (3).  `ProperCoveringModel.Connected`.  The point `y_e`: `sheetIndex`
  (`sheetIndex_mem`, `mem_U_sheetIndex`, `sheetIndex_eq`, `isLocallyConstant_sheetIndex`).
* **Remark 17.8.5**: `ProperCoveringModel.remark_17_8_5`: `τ̂` is a proper covering functor in the
  sense of Definition 8.5.1 if and only if `τ̂⁻¹(ō)` is finite.  Definition 17.8.4 does not ask for
  finiteness: `sheetModel_int_not_isProperCovering` is a proper covering model with
  `τ̂⁻¹(ō) = ℤ × {0}` which is not a proper covering functor.  Conversely
  `ProperCoveringModel.ofIsProperCovering` builds a model from a proper covering functor, a fixed
  point and the decomposition (2).
* **The sheet models**: for a discrete `G`-set `S`, `sheetEp hP S = G ⋉ (S × O)` (diagonal action)
  and `sheetFunctor hP S : G ⋉ (S × O) → G ⋉ O`, `(s, o) ↦ o`; `sheetModel hP S ō` is a proper
  covering model for every `G`-fixed `ō` (`S` nonempty), with `U(s, ō) = {s} × O`;
  `sheetFunctor_isProperCovering` for finite `S`.  Witnesses: `sheetModel_units` (`ℤ/2` acting on
  `ℝ` by the reflection, `S = ℤ/2`, two sheets, `ō = 0`, connected; this is Chapter 19's
  `absP`) and `sheetModel_int` (`S = ℤ`).
* **Lemma 17.8.7**: `lemma_17_8_7`.
* **Lemma 17.8.8**: `lemma_17_8_8` (disjointness and covering), with `groupIndex` (`g_ψ`),
  `isLocallyConstant_groupIndex`, `eq_of_mem_morOn_fiber` (`φ ∈ 𝐀_ō` is determined by `g_φ` and
  `s(φ)`), `baseMor` (`φ_ψ = Γ⁻¹((g_ψ, ō), y_{s ψ})`), `baseMor_mem`,
  `mem_connectedComponent_baseMor`,
  and `constant_on_component` (the maps `ψ ↦ y_{s ψ}, y_{t ψ}, g_ψ` are constant on `𝐄^φ`).
* **Lemma 17.8.9**: `lemma_17_8_9`; `fiberAct` (`φ ∗`), `obj_fiberAct`, `fiberAct_mem_U`,
  `fiberAct_comp` (`(φ' ∘ φ) ∗ = φ' ∗ ∘ φ ∗`).

## Readings

* **`τ̂ : E → O`** in (1) and (2) is the object map of `τ̂`.  "Open neighbourhood `U(y)`" with
  `τ̂ : U(y) → O` an sc-diffeomorphism: `U(y)` is then open (`isOpen_U`), and only the points
  `y ∈ τ̂⁻¹(ō)` carry a `U(y)` (the function `U` is unconstrained elsewhere).
* **Finiteness.**  The proper covering functors of Definition 8.5.1 have finite fibres; Definition
  17.8.4 does not mention finiteness of `τ̂⁻¹(ō)`, and we read it without it.  Remark 17.8.5 is a
  comparison; as formalized, the two notions agree exactly when `τ̂⁻¹(ō)` is finite.  In the
  construction after Definition 17.8.3, and in Definition 17.8.10, `τ̂⁻¹(ō) ≅ P⁻¹(β)` is finite.
* **Lemma 17.8.8: paths.**  The text's proof uses paths in the connected `O` (M-polyfolds are
  locally path connected, `MPolyfold.locallyPathConnectedSpace`, so a connected M-polyfold is path
  connected).  We replace the path `γ` by the connected set `O` itself:
  `o ↦ Γ⁻¹((g_ψ, o), τ_y⁻¹(o))` is continuous on the connected `O`, so its image is a connected set
  containing `ψ` and `φ_ψ`.  The second half (distinct `φ` lie in distinct components) uses that
  `ψ ↦ (g_ψ, y_{s ψ})` is locally constant, instead of a path `γ̂`.  `𝐄^φ` is the connected
  component
  (`connectedComponent φ`) as printed; it is also the path component.
* **Lemma 17.8.7** does not use the connectedness of `O`; it is stated for every model.
* **Lemma 17.8.9** holds on every `ψ` with `y_{s ψ} = s φ`, `y_{t ψ} = t φ`, `g_ψ = g_φ`; on `𝐄^φ`
  these hold by `constant_on_component`.
* **`g ∗ q`** is the action `g • q`; `𝐀_ō` is `E.morOn (τ̂⁻¹(ō))`.
-/

open Set Function Topology

noncomputable section

namespace Polyfold

open EpGroupoid EpGroupoid.Examples

universe u v

section Model

variable {G : Type u} [Group G] [Finite G] [TopologicalSpace G] [DiscreteTopology G]
  {O : Type u} [TopologicalSpace O] [T2Space O] [ParacompactSpace O] [MulAction G O]
  {P : MPolyfold O} {hP : ∀ g : G, P.IsScSmoothMap P fun y => g • y}
  {ObjE MorE : Type v} [TopologicalSpace ObjE] [T2Space ObjE] [ParacompactSpace ObjE]
  [TopologicalSpace MorE] [T2Space MorE] [ParacompactSpace MorE] {E : EpGroupoid ObjE MorE}

/-- **Definition 17.8.4 (proper ep-groupoid covering model)**, p. 831: an sc-smooth functor
`τ̂ : E → G ⋉ O` into the translation ep-groupoid of a finite group `G` acting on `O` by
sc-diffeomorphisms, with a distinguished point `ō` (`pt`) fixed by `G`, such that (1) `τ̂` is a
surjective local sc-diffeomorphism on objects; (2) the points `y ∈ τ̂⁻¹(ō)` have mutually disjoint
open neighbourhoods `U(y)` with `E = ⊔ U(y)` and `τ̂ : U(y) → O` an sc-diffeomorphism with inverse
`σ y`; (3) `Γ : 𝐄 → (G ⋉ O) ₛ×_τ̂ E`, `ψ ↦ (τ̂(ψ), s(ψ))` (`EpFunctor.fibredMap`), is an
sc-diffeomorphism onto Part I's fibred-product sub-M-polyfold. -/
structure ProperCoveringModel (τ : EpFunctor E (actionEpGroupoid hP)) where
  /-- The distinguished point `ō`. -/
  pt : O
  /-- `ō` is fixed by `G`. -/
  smul_pt : ∀ g : G, g • pt = pt
  /-- (1) `τ̂` is surjective on objects. -/
  surjective : Surjective τ.obj
  /-- (1) `τ̂` is a local sc-diffeomorphism on objects. -/
  isLocalScDiffeo : E.PObj.IsLocalScDiffeo P τ.obj
  /-- (2) The neighbourhoods `U(y)`, `y ∈ τ̂⁻¹(ō)`. -/
  U : ObjE → Set ObjE
  /-- (2) The inverses `σ y = (τ̂|U(y))⁻¹ : O → U(y)`. -/
  σ : ObjE → O → ObjE
  mem_U : ∀ y ∈ τ.obj ⁻¹' {pt}, y ∈ U y
  pairwiseDisjoint_U : (τ.obj ⁻¹' {pt}).PairwiseDisjoint U
  iUnion_U : (⋃ y ∈ τ.obj ⁻¹' {pt}, U y) = univ
  isScDiffeoOn_U : ∀ y ∈ τ.obj ⁻¹' {pt}, E.PObj.IsScDiffeoOn P τ.obj (σ y) (U y) univ
  /-- (3) `Γ = τ.fibredMap` is an sc-diffeomorphism. -/
  isScDiffeo_fibredMap :
    letI := MPolyfold.paracompactSpace_prod (actionEpGroupoid hP).PMor E.PObj
    letI := ((actionEpGroupoid hP).PMor.prod E.PObj).paracompactSpace_subtype
      (MPolyfold.fibredProduct (actionEpGroupoid hP).src τ.obj)
    ∃ g : MPolyfold.fibredProduct (actionEpGroupoid hP).src τ.obj → MorE,
      E.PMor.IsScDiffeoOn (MPolyfold.subPolyfold
        (MPolyfold.isSubMPolyfold_fibredProduct (actionEpGroupoid hP).isLocalScDiffeo_src
          τ.isScSmoothMap_obj)) τ.fibredMap g univ univ

namespace ProperCoveringModel

variable {τ : EpFunctor E (actionEpGroupoid hP)} (M : ProperCoveringModel τ)

/-- **Definition 17.8.4**: the model is *connected* if the M-polyfold `O` is connected. -/
def Connected (_M : ProperCoveringModel τ) : Prop := ConnectedSpace O

/-- The fibre `τ̂⁻¹(ō)`, the object set `A_ō`. -/
def fiber : Set ObjE := τ.obj ⁻¹' {M.pt}

theorem mem_fiber_iff {y : ObjE} : y ∈ M.fiber ↔ τ.obj y = M.pt := Iff.rfl

theorem isOpen_U {y : ObjE} (hy : y ∈ M.fiber) : IsOpen (M.U y) :=
  (M.isScDiffeoOn_U y hy).isScSmoothOn.isOpen

theorem obj_σ {y : ObjE} (hy : y ∈ M.fiber) (o : O) : τ.obj (M.σ y o) = o :=
  (M.isScDiffeoOn_U y hy).right_inv o (mem_univ o)

theorem σ_mem_U {y : ObjE} (hy : y ∈ M.fiber) (o : O) : M.σ y o ∈ M.U y :=
  (M.isScDiffeoOn_U y hy).mapsTo_inv (mem_univ o)

theorem σ_obj {y : ObjE} (hy : y ∈ M.fiber) {e : ObjE} (he : e ∈ M.U y) :
    M.σ y (τ.obj e) = e :=
  (M.isScDiffeoOn_U y hy).left_inv e he

theorem σ_pt {y : ObjE} (hy : y ∈ M.fiber) : M.σ y M.pt = y := by
  have h := M.σ_obj hy (M.mem_U y hy)
  rwa [show τ.obj y = M.pt from hy] at h

theorem continuous_σ {y : ObjE} (hy : y ∈ M.fiber) : Continuous (M.σ y) :=
  continuousOn_univ.1 (M.isScDiffeoOn_U y hy).isScSmoothOn_inv.continuousOn

theorem exists_mem_U (e : ObjE) : ∃ y ∈ M.fiber, e ∈ M.U y := by
  have h : e ∈ ⋃ y ∈ τ.obj ⁻¹' {M.pt}, M.U y := M.iUnion_U ▸ mem_univ e
  simp only [mem_iUnion, exists_prop] at h
  obtain ⟨y, hy, he⟩ := h
  exact ⟨y, hy, he⟩

/-- **The point `y_e`** (p. 832): the unique `y ∈ τ̂⁻¹(ō)` with `e ∈ U(y)`. -/
def sheetIndex (e : ObjE) : ObjE := (M.exists_mem_U e).choose

theorem sheetIndex_mem (e : ObjE) : M.sheetIndex e ∈ M.fiber :=
  (M.exists_mem_U e).choose_spec.1

theorem mem_U_sheetIndex (e : ObjE) : e ∈ M.U (M.sheetIndex e) :=
  (M.exists_mem_U e).choose_spec.2

theorem sheetIndex_eq {e y : ObjE} (hy : y ∈ M.fiber) (he : e ∈ M.U y) : M.sheetIndex e = y := by
  by_contra h
  exact Set.disjoint_left.1 (M.pairwiseDisjoint_U (M.sheetIndex_mem e) hy h)
    (M.mem_U_sheetIndex e) he

theorem sheetIndex_of_mem_fiber {y : ObjE} (hy : y ∈ M.fiber) : M.sheetIndex y = y :=
  M.sheetIndex_eq hy (M.mem_U y hy)

theorem sheetIndex_σ {y : ObjE} (hy : y ∈ M.fiber) (o : O) : M.sheetIndex (M.σ y o) = y :=
  M.sheetIndex_eq hy (M.σ_mem_U hy o)

theorem σ_sheetIndex (e : ObjE) : M.σ (M.sheetIndex e) (τ.obj e) = e :=
  M.σ_obj (M.sheetIndex_mem e) (M.mem_U_sheetIndex e)

/-- `e ↦ y_e` is locally constant: it is constant on each open `U(y)`. -/
theorem isLocallyConstant_sheetIndex : IsLocallyConstant M.sheetIndex :=
  (IsLocallyConstant.iff_exists_open _).2 fun e => ⟨M.U (M.sheetIndex e),
    M.isOpen_U (M.sheetIndex_mem e), M.mem_U_sheetIndex e,
    fun _ he => M.sheetIndex_eq (M.sheetIndex_mem e) he⟩

/-- On `U(y)`, `τ̂` is injective. -/
theorem eq_of_obj_eq {e e' : ObjE} (hs : M.sheetIndex e = M.sheetIndex e')
    (ho : τ.obj e = τ.obj e') : e = e' := by
  rw [← M.σ_sheetIndex e, ← M.σ_sheetIndex e', hs, ho]

/-! ### Remark 17.8.5: comparison with Definition 8.5.1 -/

/-- Every fibre `τ̂⁻¹(x)` is the image of `τ̂⁻¹(ō)` under `y ↦ τ_y⁻¹(x)`. -/
theorem preimage_subset_image (x : O) : τ.obj ⁻¹' {x} ⊆ (fun y => M.σ y x) '' M.fiber := by
  intro e he
  refine ⟨M.sheetIndex e, M.sheetIndex_mem e, ?_⟩
  have he' : τ.obj e = x := he
  change M.σ (M.sheetIndex e) x = e
  rw [← he']
  exact M.σ_sheetIndex e

/-- **Remark 17.8.5**, the direction used: a proper covering model with finite `τ̂⁻¹(ō)` is a proper
covering functor in the sense of Definition 8.5.1. Definition 8.5.1 (2) holds with `U(x) = O` and
`U(e) = U(y_e)` for `e ∈ τ̂⁻¹(x)`. -/
theorem isProperCovering (hfin : M.fiber.Finite) : τ.IsProperCovering where
  surjective := M.surjective
  isLocalScDiffeo := M.isLocalScDiffeo
  finite_fiber x := (hfin.image _).subset (M.preimage_subset_image x)
  evenlyCovered x := by
    refine ⟨univ, fun e => M.U (M.sheetIndex e), fun e => M.σ (M.sheetIndex e), isOpen_univ,
      mem_univ x, ?_, fun e _ => ⟨M.mem_U_sheetIndex e,
        M.isScDiffeoOn_U _ (M.sheetIndex_mem e)⟩, ?_⟩
    · intro e he e' he' hne
      have hs : M.sheetIndex e ≠ M.sheetIndex e' := fun hs =>
        hne (M.eq_of_obj_eq hs ((he : τ.obj e = x).trans (he' : τ.obj e' = x).symm))
      exact M.pairwiseDisjoint_U (M.sheetIndex_mem e) (M.sheetIndex_mem e') hs
    · refine (eq_univ_of_forall fun e => ?_).symm
      simp only [mem_iUnion, exists_prop]
      refine ⟨M.σ (M.sheetIndex e) x, M.obj_σ (M.sheetIndex_mem e) x, ?_⟩
      rw [M.sheetIndex_σ (M.sheetIndex_mem e)]
      exact M.mem_U_sheetIndex e
  isScDiffeo_fibredMap := M.isScDiffeo_fibredMap

/-- **Remark 17.8.5** (comparison with Definition 8.5.1): a proper covering model `τ̂` is a proper
covering functor in the sense of Definition 8.5.1 if and only if `τ̂⁻¹(ō)` is finite.  The other
conditions of Definition 8.5.1 hold for every model; Definition 17.8.4 adds the fixed point `ō`
and the global decomposition (2) (`ofIsProperCovering` for the converse). -/
theorem remark_17_8_5 : τ.IsProperCovering ↔ M.fiber.Finite :=
  ⟨fun h => h.finite_fiber M.pt, M.isProperCovering⟩

/-! ### Lemma 17.8.7 -/

/-- **Lemma 17.8.7**: `ψ ↦ (y_{s(ψ)}, y_{t(ψ)})` is locally constant on `𝐄`.  *Proof*: `s`, `t`
are continuous and the `U(y)` are open. -/
theorem lemma_17_8_7 :
    IsLocallyConstant fun ψ : MorE => (M.sheetIndex (E.src ψ), M.sheetIndex (E.tgt ψ)) :=
  (IsLocallyConstant.iff_exists_open _).2 fun ψ =>
    ⟨E.src ⁻¹' M.U (M.sheetIndex (E.src ψ)) ∩ E.tgt ⁻¹' M.U (M.sheetIndex (E.tgt ψ)),
      ((M.isOpen_U (M.sheetIndex_mem _)).preimage E.continuous_src).inter
        ((M.isOpen_U (M.sheetIndex_mem _)).preimage E.continuous_tgt),
      ⟨M.mem_U_sheetIndex _, M.mem_U_sheetIndex _⟩,
      fun _ h => Prod.ext (M.sheetIndex_eq (M.sheetIndex_mem _) h.1)
        (M.sheetIndex_eq (M.sheetIndex_mem _) h.2)⟩

/-! ### The group index `g_ψ` and the inverse of `Γ` -/

/-- **The group index `g_ψ`** (p. 833): `Γ(ψ) = ((g_ψ, τ̂(s ψ)), s ψ)`. -/
def groupIndex (_M : ProperCoveringModel τ) (ψ : MorE) : G := (τ.mor ψ).1

theorem mor_eq (ψ : MorE) : τ.mor ψ = (M.groupIndex ψ, τ.obj (E.src ψ)) :=
  Prod.ext rfl (τ.src_mor ψ)

/-- `τ̂(t ψ) = g_ψ ∗ τ̂(s ψ)`. -/
theorem obj_tgt (ψ : MorE) : τ.obj (E.tgt ψ) = M.groupIndex ψ • τ.obj (E.src ψ) := by
  have h := τ.tgt_mor ψ
  rw [M.mor_eq ψ] at h
  exact h.symm

theorem isLocallyConstant_groupIndex : IsLocallyConstant M.groupIndex :=
  (IsLocallyConstant.iff_continuous _).2
    (continuous_fst.comp (continuousOn_univ.1 τ.isScSmoothMap_mor.continuousOn))

/-- `g` of a composition: `g_{φ' ∘ φ} = g_{φ'} g_φ`. -/
theorem groupIndex_comp {φ' φ : MorE} (h : E.src φ' = E.tgt φ) :
    M.groupIndex (E.comp φ' φ) = M.groupIndex φ' * M.groupIndex φ := by
  change (τ.mor (E.comp φ' φ)).1 = _
  rw [τ.mor_comp φ' φ h]
  rfl

theorem groupIndex_unit (e : ObjE) : M.groupIndex (E.unit e) = 1 := by
  change (τ.mor (E.unit e)).1 = _
  rw [τ.mor_unit e]
  rfl

/-- The inverse `Γ⁻¹` of Definition 17.8.4 (3). -/
def ΓInv : MPolyfold.fibredProduct (actionEpGroupoid hP).src τ.obj → MorE :=
  M.isScDiffeo_fibredMap.choose

theorem isScDiffeoOn_ΓInv :
    letI := MPolyfold.paracompactSpace_prod (actionEpGroupoid hP).PMor E.PObj
    letI := ((actionEpGroupoid hP).PMor.prod E.PObj).paracompactSpace_subtype
      (MPolyfold.fibredProduct (actionEpGroupoid hP).src τ.obj)
    E.PMor.IsScDiffeoOn (MPolyfold.subPolyfold
      (MPolyfold.isSubMPolyfold_fibredProduct (actionEpGroupoid hP).isLocalScDiffeo_src
        τ.isScSmoothMap_obj)) τ.fibredMap M.ΓInv univ univ :=
  M.isScDiffeo_fibredMap.choose_spec

theorem fibredMap_ΓInv (q : MPolyfold.fibredProduct (actionEpGroupoid hP).src τ.obj) :
    τ.fibredMap (M.ΓInv q) = q := by
  have := MPolyfold.paracompactSpace_prod (actionEpGroupoid hP).PMor E.PObj
  have := ((actionEpGroupoid hP).PMor.prod E.PObj).paracompactSpace_subtype
    (MPolyfold.fibredProduct (actionEpGroupoid hP).src τ.obj)
  exact M.isScDiffeoOn_ΓInv.right_inv q (mem_univ _)

theorem ΓInv_fibredMap (ψ : MorE) : M.ΓInv (τ.fibredMap ψ) = ψ := by
  have := MPolyfold.paracompactSpace_prod (actionEpGroupoid hP).PMor E.PObj
  have := ((actionEpGroupoid hP).PMor.prod E.PObj).paracompactSpace_subtype
    (MPolyfold.fibredProduct (actionEpGroupoid hP).src τ.obj)
  exact M.isScDiffeoOn_ΓInv.left_inv ψ (mem_univ _)

/-- **A morphism is determined by `g_ψ` and `s(ψ)`** (the injectivity of `Γ`). -/
theorem eq_of_groupIndex_eq {ψ ψ' : MorE} (hg : M.groupIndex ψ = M.groupIndex ψ')
    (hs : E.src ψ = E.src ψ') : ψ = ψ' := by
  have h : τ.fibredMap ψ = τ.fibredMap ψ' := Subtype.ext (by
    change ((τ.mor ψ, E.src ψ) : (G × O) × ObjE) = (τ.mor ψ', E.src ψ')
    rw [M.mor_eq ψ, M.mor_eq ψ', hg, hs])
  rw [← M.ΓInv_fibredMap ψ, ← M.ΓInv_fibredMap ψ', h]

theorem continuous_ΓInv : Continuous M.ΓInv := by
  have := MPolyfold.paracompactSpace_prod (actionEpGroupoid hP).PMor E.PObj
  have := ((actionEpGroupoid hP).PMor.prod E.PObj).paracompactSpace_subtype
    (MPolyfold.fibredProduct (actionEpGroupoid hP).src τ.obj)
  exact continuousOn_univ.1 M.isScDiffeoOn_ΓInv.isScSmoothOn_inv.continuousOn

/-- **The lift** `Γ⁻¹((g, τ̂(e)), e)`: the morphism with source `e` and group index `g`. -/
def liftMor (g : G) (e : ObjE) : MorE :=
  M.ΓInv ⟨((g, τ.obj e), e), rfl⟩

theorem src_liftMor (g : G) (e : ObjE) : E.src (M.liftMor g e) = e :=
  congrArg (fun q : MPolyfold.fibredProduct (actionEpGroupoid hP).src τ.obj =>
    (q : (G × O) × ObjE).2) (M.fibredMap_ΓInv ⟨((g, τ.obj e), e), rfl⟩)

theorem groupIndex_liftMor (g : G) (e : ObjE) : M.groupIndex (M.liftMor g e) = g :=
  congrArg (fun q : MPolyfold.fibredProduct (actionEpGroupoid hP).src τ.obj =>
    (q : (G × O) × ObjE).1.1) (M.fibredMap_ΓInv ⟨((g, τ.obj e), e), rfl⟩)

theorem liftMor_eq (ψ : MorE) : M.liftMor (M.groupIndex ψ) (E.src ψ) = ψ :=
  M.eq_of_groupIndex_eq (M.groupIndex_liftMor _ _) (M.src_liftMor _ _)

/-- `o ↦ Γ⁻¹((g, o), τ_y⁻¹(o))` is continuous. -/
theorem continuous_liftMor_σ (g : G) {y : ObjE} (hy : y ∈ M.fiber) :
    Continuous fun o : O => M.liftMor g (M.σ y o) := by
  refine M.continuous_ΓInv.comp (Continuous.subtype_mk ?_ _)
  have hc := M.continuous_σ hy
  refine (continuous_const.prodMk ?_).prodMk hc
  exact (continuousOn_univ.1 τ.isScSmoothMap_obj.continuousOn).comp hc

/-! ### Lemma 17.8.8 -/

/-- **`φ_ψ = Γ⁻¹((g_ψ, ō), y_{s ψ})`** (p. 833), the end point of the text's path. -/
def baseMor (ψ : MorE) : MorE := M.liftMor (M.groupIndex ψ) (M.sheetIndex (E.src ψ))

/-- `φ_ψ ∈ 𝐀_ō`: its source is `y_{s ψ}` and `τ̂(t φ_ψ) = g_ψ ∗ ō = ō`. -/
theorem baseMor_mem (ψ : MorE) : M.baseMor ψ ∈ E.morOn M.fiber := by
  refine ⟨?_, ?_⟩
  · rw [baseMor, M.src_liftMor]
    exact M.sheetIndex_mem _
  · change τ.obj (E.tgt (M.baseMor ψ)) = M.pt
    rw [M.obj_tgt, baseMor, M.src_liftMor, M.groupIndex_liftMor,
      show τ.obj (M.sheetIndex (E.src ψ)) = M.pt from M.sheetIndex_mem _, M.smul_pt]

/-- **The first half of Lemma 17.8.8**: for `O` connected, every `ψ` lies in the connected
component of `φ_ψ ∈ 𝐀_ō`: the image of the connected `O` under `o ↦ Γ⁻¹((g_ψ, o), τ_y⁻¹(o))`
(`y = y_{s ψ}`) contains `ψ` (at `o = τ̂(s ψ)`) and `φ_ψ` (at `o = ō`). -/
theorem mem_connectedComponent_baseMor (hO : M.Connected) (ψ : MorE) :
    ψ ∈ connectedComponent (M.baseMor ψ) := by
  have : ConnectedSpace O := hO
  set y := M.sheetIndex (E.src ψ)
  have hy : y ∈ M.fiber := M.sheetIndex_mem _
  set c : O → MorE := fun o => M.liftMor (M.groupIndex ψ) (M.σ y o)
  have hrange :=
    (isPreconnected_range (M.continuous_liftMor_σ (M.groupIndex ψ) hy)).subset_connectedComponent
    (x := M.baseMor ψ) ⟨M.pt, by
      change M.liftMor _ (M.σ y M.pt) = M.liftMor _ y
      rw [M.σ_pt hy]⟩
  refine hrange ⟨τ.obj (E.src ψ), ?_⟩
  change M.liftMor (M.groupIndex ψ) (M.σ y (τ.obj (E.src ψ))) = ψ
  rw [M.σ_sheetIndex, M.liftMor_eq]

/-- `ψ ↦ (g_ψ, y_{s ψ})` is locally constant. -/
theorem isLocallyConstant_groupIndex_sheetIndex :
    IsLocallyConstant fun ψ : MorE => (M.groupIndex ψ, M.sheetIndex (E.src ψ)) :=
  (IsLocallyConstant.iff_exists_open _).2 fun ψ => by
    obtain ⟨V, hV, hψV, hVc⟩ := (IsLocallyConstant.iff_exists_open _).1
      M.isLocallyConstant_groupIndex ψ
    obtain ⟨W, hW, hψW, hWc⟩ := (IsLocallyConstant.iff_exists_open _).1 M.lemma_17_8_7 ψ
    exact ⟨V ∩ W, hV.inter hW, ⟨hψV, hψW⟩, fun ψ' h => Prod.ext (hVc ψ' h.1)
      (congrArg Prod.fst (hWc ψ' h.2))⟩

/-- **The maps `ψ ↦ y_{s ψ}`, `ψ ↦ y_{t ψ}`, `ψ ↦ g_ψ` are constant on `𝐄^φ`** (p. 834). -/
theorem constant_on_component {φ ψ : MorE} (hψ : ψ ∈ connectedComponent φ) :
    M.sheetIndex (E.src ψ) = M.sheetIndex (E.src φ) ∧
      M.sheetIndex (E.tgt ψ) = M.sheetIndex (E.tgt φ) ∧ M.groupIndex ψ = M.groupIndex φ := by
  have h1 := M.lemma_17_8_7.apply_eq_of_isPreconnected isPreconnected_connectedComponent hψ
    mem_connectedComponent
  have h2 := M.isLocallyConstant_groupIndex.apply_eq_of_isPreconnected
    isPreconnected_connectedComponent hψ mem_connectedComponent
  exact ⟨congrArg Prod.fst h1, congrArg Prod.snd h1, h2⟩

/-- An element of `𝐀_ō` is determined by `g_φ` and `s(φ)`. -/
theorem eq_of_mem_morOn_fiber {φ φ' : MorE} (hφ : φ ∈ E.morOn M.fiber)
    (hφ' : φ' ∈ E.morOn M.fiber) (hg : M.groupIndex φ = M.groupIndex φ')
    (hs : M.sheetIndex (E.src φ) = M.sheetIndex (E.src φ')) : φ = φ' :=
  M.eq_of_groupIndex_eq hg (by
    rwa [M.sheetIndex_of_mem_fiber hφ.1, M.sheetIndex_of_mem_fiber hφ'.1] at hs)

/-- **Lemma 17.8.8**: the connected components `𝐄^φ` of the `φ ∈ 𝐀_ō` are pairwise disjoint, and
for `O` connected they cover `𝐄`. -/
theorem lemma_17_8_8 (hO : M.Connected) :
    (E.morOn M.fiber).PairwiseDisjoint (fun φ => connectedComponent φ) ∧
      (⋃ φ ∈ E.morOn M.fiber, connectedComponent φ) = univ := by
  refine ⟨fun φ hφ φ' hφ' hne => connectedComponent_disjoint fun heq => hne ?_, ?_⟩
  · have hmem : φ' ∈ connectedComponent φ := heq ▸ mem_connectedComponent
    have h := M.isLocallyConstant_groupIndex_sheetIndex.apply_eq_of_isPreconnected
      isPreconnected_connectedComponent (mem_connectedComponent (x := φ)) hmem
    exact M.eq_of_mem_morOn_fiber hφ hφ' (Prod.ext_iff.1 h).1 (Prod.ext_iff.1 h).2
  · refine eq_univ_of_forall fun ψ => ?_
    simp only [mem_iUnion, exists_prop]
    exact ⟨M.baseMor ψ, M.baseMor_mem ψ, M.mem_connectedComponent_baseMor hO ψ⟩

/-! ### Lemma 17.8.9 and the maps `φ ∗` -/

/-- **Lemma 17.8.9**: on `𝐄^φ`, `φ : y → y'` in `𝐀_ō`, `t(ψ) = τ_{y'}⁻¹(g_φ ∗ τ_y(s ψ))`. -/
theorem lemma_17_8_9 {φ ψ : MorE} (hφ : φ ∈ E.morOn M.fiber) (hψ : ψ ∈ connectedComponent φ) :
    E.tgt ψ = M.σ (E.tgt φ) (M.groupIndex φ • τ.obj (E.src ψ)) := by
  obtain ⟨-, ht, hg⟩ := M.constant_on_component hψ
  rw [M.sheetIndex_of_mem_fiber hφ.2] at ht
  rw [← hg, ← M.obj_tgt, ← ht, M.σ_sheetIndex]

/-- **The sc-diffeomorphism `φ ∗ : U(s φ) → U(t φ)`** (p. 834),
`φ ∗ q = τ_{t φ}⁻¹(g_φ ∗ τ_{s φ}(q))`. -/
def fiberAct (φ : MorE) (q : ObjE) : ObjE := M.σ (E.tgt φ) (M.groupIndex φ • τ.obj q)

theorem fiberAct_mem_U {φ : MorE} (hφ : φ ∈ E.morOn M.fiber) (q : ObjE) :
    M.fiberAct φ q ∈ M.U (E.tgt φ) :=
  M.σ_mem_U hφ.2 _

theorem obj_fiberAct {φ : MorE} (hφ : φ ∈ E.morOn M.fiber) (q : ObjE) :
    τ.obj (M.fiberAct φ q) = M.groupIndex φ • τ.obj q :=
  M.obj_σ hφ.2 _

/-- `φ ∗` maps `s(φ)` to `t(φ)`. -/
theorem fiberAct_src {φ : MorE} (hφ : φ ∈ E.morOn M.fiber) : M.fiberAct φ (E.src φ) = E.tgt φ := by
  rw [fiberAct, ← M.obj_tgt]
  exact M.σ_obj hφ.2 (M.mem_U _ hφ.2)

/-- `φ ∗` is an sc-diffeomorphism `U(s φ) → U(t φ)`, with inverse `φ⁻¹ ∗`. -/
theorem isScDiffeoOn_fiberAct {φ : MorE} (hφ : φ ∈ E.morOn M.fiber) :
    E.PObj.IsScDiffeoOn E.PObj (M.fiberAct φ) (M.fiberAct (E.inv φ)) (M.U (E.src φ))
      (M.U (E.tgt φ)) := by
  have hinv : M.groupIndex (E.inv φ) = (M.groupIndex φ)⁻¹ := by
    have h := M.groupIndex_comp (E.tgt_inv φ).symm
    rw [E.comp_inv, M.groupIndex_unit] at h
    exact eq_inv_of_mul_eq_one_right h.symm
  have hs := M.isScDiffeoOn_U _ hφ.1
  have ht := M.isScDiffeoOn_U _ hφ.2
  refine
    { isScSmoothOn := ?_
      isScSmoothOn_inv := ?_
      mapsTo := fun q _ => M.fiberAct_mem_U hφ q
      mapsTo_inv := fun q _ => by
        have := M.fiberAct_mem_U (φ := E.inv φ) ⟨by rw [E.src_inv]; exact hφ.2,
          by rw [E.tgt_inv]; exact hφ.1⟩ q
        rwa [E.tgt_inv] at this
      left_inv := fun q hq => ?_
      right_inv := fun q hq => ?_ }
  · exact MPolyfold.IsScSmoothOn.comp ht.isScSmoothOn_inv
      (MPolyfold.IsScSmoothOn.comp (hP _) hs.isScSmoothOn (mapsTo_univ _ _)) (mapsTo_univ _ _)
  · have h := MPolyfold.IsScSmoothOn.comp hs.isScSmoothOn_inv
      (MPolyfold.IsScSmoothOn.comp (hP (M.groupIndex φ)⁻¹) ht.isScSmoothOn (mapsTo_univ _ _))
      (mapsTo_univ _ _)
    refine h.congr fun q _ => ?_
    simp only [Function.comp_apply, fiberAct, E.tgt_inv, hinv]
  · simp only [fiberAct, E.tgt_inv, hinv]
    rw [M.obj_σ hφ.2, inv_smul_smul, M.σ_obj hφ.1 hq]
  · simp only [fiberAct, E.tgt_inv, hinv]
    rw [M.obj_σ hφ.1, smul_inv_smul, M.σ_obj hφ.2 hq]

/-- **Functoriality of `φ ∗`** (p. 834): `(φ' ∘ φ) ∗ q = φ' ∗ (φ ∗ q)` for `t(φ) = s(φ')`. -/
theorem fiberAct_comp {φ φ' : MorE} (hφ : φ ∈ E.morOn M.fiber) (h : E.src φ' = E.tgt φ)
    (q : ObjE) : M.fiberAct (E.comp φ' φ) q = M.fiberAct φ' (M.fiberAct φ q) := by
  simp only [fiberAct]
  rw [E.tgt_comp φ' φ h, M.groupIndex_comp h, M.obj_σ hφ.2, mul_smul]

/-- `(1_y) ∗ = id` on `U(y)`. -/
theorem fiberAct_unit {y : ObjE} (hy : y ∈ M.fiber) {q : ObjE} (hq : q ∈ M.U y) :
    M.fiberAct (E.unit y) q = q := by
  simp only [fiberAct]
  rw [E.tgt_unit, M.groupIndex_unit, one_smul, M.σ_obj hy hq]

end ProperCoveringModel

/-- **Remark 17.8.5**, converse: a proper covering functor `τ̂ : E → G ⋉ O` (Definition 8.5.1)
with a `G`-fixed point `ō` and a decomposition (2) of `E` over `τ̂⁻¹(ō)` is a proper covering
model. -/
def ProperCoveringModel.ofIsProperCovering {τ : EpFunctor E (actionEpGroupoid hP)}
    (hτ : τ.IsProperCovering) (pt : O) (smul_pt : ∀ g : G, g • pt = pt) (U : ObjE → Set ObjE)
    (σ : ObjE → O → ObjE) (mem_U : ∀ y ∈ τ.obj ⁻¹' {pt}, y ∈ U y)
    (pairwiseDisjoint_U : (τ.obj ⁻¹' {pt}).PairwiseDisjoint U)
    (iUnion_U : (⋃ y ∈ τ.obj ⁻¹' {pt}, U y) = univ)
    (isScDiffeoOn_U : ∀ y ∈ τ.obj ⁻¹' {pt}, E.PObj.IsScDiffeoOn P τ.obj (σ y) (U y) univ) :
    ProperCoveringModel τ where
  pt := pt
  smul_pt := smul_pt
  surjective := hτ.surjective
  isLocalScDiffeo := hτ.isLocalScDiffeo
  U := U
  σ := σ
  mem_U := mem_U
  pairwiseDisjoint_U := pairwiseDisjoint_U
  iUnion_U := iUnion_U
  isScDiffeoOn_U := isScDiffeoOn_U
  isScDiffeo_fibredMap := hτ.isScDiffeo_fibredMap

end Model

/-! ### The sheet models `G ⋉ (S × O) → G ⋉ O` -/

section Sheet

variable {G : Type u} [Group G] [Finite G] [TopologicalSpace G] [DiscreteTopology G]
  {O : Type u} [TopologicalSpace O] [T2Space O] [ParacompactSpace O] [MulAction G O]
  {P : MPolyfold O} (hP : ∀ g : G, P.IsScSmoothMap P fun y => g • y)
  (S : Type u) [TopologicalSpace S] [DiscreteTopology S] [MulAction G S]
  [ParacompactSpace (S × O)]

include hP in
/-- The diagonal action `g (s, o) = (g s, g o)` on `S × O` (`#S` copies of `O`) is sc-smooth. -/
theorem isScSmoothMap_sheet_smul' (g : G) :
    ((discretePolyfold S).prod P).IsScSmoothMap ((discretePolyfold S).prod P)
      fun p : S × O => g • p :=
  isScSmoothMap_prod_discrete_iff.2 fun s =>
    MPolyfold.IsScSmoothOn.prodMk (isScSmoothMap_const_discrete (g • s)) (hP g)

/-- **`G ⋉ (S × O)`**, the translation ep-groupoid of the diagonal action on `#S` copies of `O`. -/
def sheetEp : EpGroupoid (S × O) (G × (S × O)) :=
  actionEpGroupoid (isScSmoothMap_sheet_smul' hP S)

/-- **The projection `G ⋉ (S × O) → G ⋉ O`**, `(s, o) ↦ o`, `(g, (s, o)) ↦ (g, o)`. -/
def sheetFunctor : EpFunctor (sheetEp hP S) (actionEpGroupoid hP) where
  obj := Prod.snd
  mor φ := (φ.1, φ.2.2)
  src_mor _ := rfl
  tgt_mor _ := rfl
  mor_comp _ _ _ := rfl
  mor_unit _ := rfl
  isScSmoothMap_obj := MPolyfold.isScSmoothMap_snd _ _
  isScSmoothMap_mor := MPolyfold.IsScSmoothOn.prodMk (MPolyfold.isScSmoothMap_fst _ _)
    ((MPolyfold.isScSmoothMap_snd _ _).comp (MPolyfold.isScSmoothMap_snd _ _))

@[simp] theorem sheetFunctor_obj (p : S × O) : (sheetFunctor hP S).obj p = p.2 := rfl

@[simp] theorem sheetFunctor_mor (φ : G × (S × O)) : (sheetFunctor hP S).mor φ = (φ.1, φ.2.2) :=
  rfl

theorem preimage_sheetFunctor_obj (x : O) :
    (sheetFunctor hP S).obj ⁻¹' {x} = univ ×ˢ {x} := by
  ext p
  simp

/-- Definition 17.8.4 (3) for the sheet functor: `φ ↦ (τ̂ φ, s φ)` is an sc-diffeomorphism, with
inverse `((g, o), (s, o')) ↦ (g, (s, o'))`. -/
theorem isScDiffeoOn_sheetFunctor_fibredMap
    [ParacompactSpace ((G × O) × (S × O))]
    [ParacompactSpace (MPolyfold.fibredProduct (actionEpGroupoid hP).src (sheetFunctor hP S).obj)] :
    (sheetEp hP S).PMor.IsScDiffeoOn (MPolyfold.subPolyfold
      (MPolyfold.isSubMPolyfold_fibredProduct (actionEpGroupoid hP).isLocalScDiffeo_src
        (sheetFunctor hP S).isScSmoothMap_obj)) (sheetFunctor hP S).fibredMap
      (fun q => ((q : (G × O) × (S × O)).1.1, (q : (G × O) × (S × O)).2)) univ univ where
  isScSmoothOn := MPolyfold.isScSmoothOn_subPolyfold_of_val _
    (MPolyfold.IsScSmoothOn.prodMk (sheetFunctor hP S).isScSmoothMap_mor
      (sheetEp hP S).isScSmoothMap_src)
  isScSmoothOn_inv :=
    MPolyfold.IsScSmoothMap.comp
      (g := fun r : (G × O) × (S × O) => (r.1.1, r.2))
      (MPolyfold.IsScSmoothOn.prodMk
        ((MPolyfold.isScSmoothMap_fst (discretePolyfold G) P).comp
          (MPolyfold.isScSmoothMap_fst (actionEpGroupoid hP).PMor (sheetEp hP S).PObj))
        (MPolyfold.isScSmoothMap_snd (actionEpGroupoid hP).PMor (sheetEp hP S).PObj))
      (MPolyfold.subPolyfold_inclusion_isScSmooth _)
  mapsTo := mapsTo_univ _ _
  mapsTo_inv := mapsTo_univ _ _
  left_inv _ _ := rfl
  right_inv q _ := Subtype.ext (Prod.ext (Prod.ext rfl q.2.symm) rfl)

/-- **The sheet model** (Definition 17.8.4): for a nonempty discrete `G`-set `S` and a `G`-fixed
point `ō ∈ O`, the projection `G ⋉ (S × O) → G ⋉ O` is a proper covering model with
`τ̂⁻¹(ō) = S × {ō}`, `U(s, ō) = {s} × O`. -/
def sheetModel [Nonempty S] (pt : O) (hpt : ∀ g : G, g • pt = pt) :
    ProperCoveringModel (sheetFunctor hP S) where
  pt := pt
  smul_pt := hpt
  surjective x := ⟨(Classical.arbitrary S, x), rfl⟩
  isLocalScDiffeo p :=
    ⟨{p.1} ×ˢ univ, univ, fun y => (p.1, y), ⟨rfl, mem_univ _⟩, isScDiffeoOn_snd_sheet p.1⟩
  U y := {y.1} ×ˢ univ
  σ y o := (y.1, o)
  mem_U _ _ := ⟨rfl, mem_univ _⟩
  pairwiseDisjoint_U := by
    intro y hy z hz hyz
    refine Set.disjoint_left.2 fun p hp hp' => hyz (Prod.ext ?_ ?_)
    · exact (hp.1 : p.1 = y.1).symm.trans hp'.1
    · exact (hy : y.2 = pt).trans (hz : z.2 = pt).symm
  iUnion_U := by
    refine eq_univ_of_forall fun p => ?_
    simp only [mem_iUnion, exists_prop]
    exact ⟨(p.1, pt), rfl, ⟨rfl, mem_univ _⟩⟩
  isScDiffeoOn_U y _ := isScDiffeoOn_snd_sheet y.1
  isScDiffeo_fibredMap := by
    have := MPolyfold.paracompactSpace_prod (actionEpGroupoid hP).PMor (sheetEp hP S).PObj
    have := ((actionEpGroupoid hP).PMor.prod (sheetEp hP S).PObj).paracompactSpace_subtype
      (MPolyfold.fibredProduct (actionEpGroupoid hP).src (sheetFunctor hP S).obj)
    exact ⟨_, isScDiffeoOn_sheetFunctor_fibredMap hP S⟩

theorem sheetModel_fiber [Nonempty S] (pt : O) (hpt : ∀ g : G, g • pt = pt) :
    (sheetModel hP S pt hpt).fiber = univ ×ˢ {pt} :=
  preimage_sheetFunctor_obj hP S pt

/-- For finite `S` the sheet functor is a proper covering functor (Definition 8.5.1), by
Remark 17.8.5. -/
theorem sheetFunctor_isProperCovering [Nonempty S] [Finite S] (pt : O)
    (hpt : ∀ g : G, g • pt = pt) : (sheetFunctor hP S).IsProperCovering :=
  (sheetModel hP S pt hpt).isProperCovering (by
    rw [sheetModel_fiber]
    exact finite_univ.prod (finite_singleton pt))

/-- For infinite `S` the sheet functor is not a proper covering functor: its fibres
`S × {x}` are infinite. -/
theorem sheetFunctor_not_isProperCovering [Nonempty S] [Infinite S] (pt : O)
    (hpt : ∀ g : G, g • pt = pt) : ¬ (sheetFunctor hP S).IsProperCovering := by
  rw [(sheetModel hP S pt hpt).remark_17_8_5, sheetModel_fiber]
  intro h
  have : (univ : Set S).Finite := by
    have := h.image Prod.fst
    refine this.subset fun s _ => ⟨(s, pt), ⟨mem_univ _, rfl⟩, rfl⟩
  exact infinite_univ this

end Sheet

/-! ### Witnesses: `ℤ/2` acting on `ℝ` by the reflection -/

section Witness

/-- `0` is fixed by the reflection. -/
theorem units_smul_zero_rn (k : ℤˣ) : k • (0 : Fin 1 → ℝ) = 0 := smul_zero k

/-- **A connected proper covering model with two sheets and nontrivial group**: `ℤ/2 ⋉ (ℤ/2 × ℝ) →
ℤ/2 ⋉ ℝ` (the reflection on `ℝ`, the diagonal action upstairs, `ō = 0`). This is Chapter 19's
`absP`. -/
def sheetModel_units : ProperCoveringModel (sheetFunctor isScSmoothMap_units_smul ℤˣ) :=
  sheetModel isScSmoothMap_units_smul ℤˣ 0 units_smul_zero_rn

theorem sheetModel_units_connected : sheetModel_units.Connected :=
  (inferInstance : ConnectedSpace (Fin 1 → ℝ))

theorem sheetModel_units_nontrivial : (sheetModel_units.fiber).ncard = 2 ∧
    ∃ (k : ℤˣ) (x : Fin 1 → ℝ), k • x ≠ x := by
  refine ⟨?_, -1, fun _ => 1, fun h => ?_⟩
  · rw [show sheetModel_units = sheetModel isScSmoothMap_units_smul ℤˣ 0 units_smul_zero_rn
      from rfl, sheetModel_fiber, Set.ncard_eq_toFinset_card']
    rfl
  · have := congrFun h 0
    rw [units_smul_rn_neg_one] at this
    norm_num at this

/-- The model with `S = ℤ` (`ℤ/2` acting on `ℤ` by `±1`): infinitely many sheets. -/
def sheetModel_int : ProperCoveringModel (sheetFunctor isScSmoothMap_units_smul ℤ) :=
  sheetModel isScSmoothMap_units_smul ℤ 0 units_smul_zero_rn

/-- **Definition 17.8.4 does not imply Definition 8.5.1**: `ℤ/2 ⋉ (ℤ × ℝ) → ℤ/2 ⋉ ℝ` is a
(connected) proper covering model, with infinite fibre `τ̂⁻¹(0) = ℤ × {0}`, and it is not a proper
covering functor in the sense of Definition 8.5.1 (Remark 17.8.5). -/
theorem sheetModel_int_not_isProperCovering :
    sheetModel_int.Connected ∧ sheetModel_int.fiber.Infinite ∧
      ¬ (sheetFunctor isScSmoothMap_units_smul ℤ).IsProperCovering := by
  refine ⟨(inferInstance : ConnectedSpace (Fin 1 → ℝ)), fun h => ?_,
    sheetFunctor_not_isProperCovering isScSmoothMap_units_smul ℤ 0 units_smul_zero_rn⟩
  exact (sheetFunctor_not_isProperCovering isScSmoothMap_units_smul ℤ 0 units_smul_zero_rn)
    (sheetModel_int.isProperCovering h)

end Witness

end Polyfold
