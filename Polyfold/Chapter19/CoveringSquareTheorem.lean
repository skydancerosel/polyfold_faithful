import Polyfold.Chapter19.CoveringPullbackTheorem
import Polyfold.Chapter19.CoveringSquare
import Polyfold.Chapter10.StrongBundleLocalRegularity
import Polyfold.Chapter17.StrongBundleStructuresExamples

/-!
# Basic constructions for bundle covering squares (HWZ 2021 §19.8, pp. 948–957)

2021 Definitions 19.8.13–19.8.15 (uniformizer, compatible transition and basic constructions for
a bundle covering square `𝔈`), Lemma 19.8.16 (the bijection `U : M(Γ̂, Γ̂') → p*M(Γ, Γ')`),
Definition 19.8.17 (the strong bundle structure of `m̂ : M(Γ̂, Γ̂') → M(Ψ̂, Ψ̂')`), Lemma 19.8.18
(the map `S : p*M(Γ, Γ') → Ŵ` of (19.93) is a local strong bundle isomorphism covering
`s : M(Ψ̂, Ψ̂') → Ê`) and Definition 19.8.19 (proper strong bundle covering squares), pp. 948–955.

## What is formalized

* For a strong ep-bundle covering model `K` (Definition 19.8.8): `fiberCLEXi` (`Ξ` on the fibres,
  a topological linear isomorphism `Q̂⁻¹(ê) → Q⁻¹(τ ê)`), `liftPt` (the unique `ŵ` with
  `Q̂(ŵ) = ê`, `Ξ(ŵ) = w`), `liftK = ⟨Q̂, Ξ⟩ : Ŵ → τ*W` and **`isStrongBundleIso_liftK`**
  (`⟨Q̂, Ξ⟩` is a strong bundle isomorphism over `Ê`, p. 952).
* `SquareUniformizerConstruction` (**Definition 19.8.13**), `toPullback` (the underlying
  uniformizer construction for `(P, μ_B)`), `definition_19_8_13`.
* `CompatibleTransitionConstruction`, `definition_19_8_14` (**Definition 19.8.14**).
* `SquareBasicConstruction`, `definition_19_8_15` (**Definition 19.8.15**).
* `MSq` (`M(Γ̂, Γ̂')`), `mSq` (`m̂`), `pbarSq` (`p̂` of (19.87)), `USq` (`U` of (19.90)), `USqInv`,
  **`lemma_19_8_16`**.
* `bundleSq` (**Definition 19.8.17**), `isStrongBundleIso_USq`, `bundleSq_unique`.
* `SMap` (`S` of (19.93)), **`lemma_19_8_18`**, `xi_SMap` (`Ξ ∘ S = s ∘ π`), `SMap_USq`
  (`s = S ∘ U`), `isLocalStrongBundleIso_srcSq` (the source map `s : M(Γ̂, Γ̂') → Ŵ` is a local
  strong bundle isomorphism, p. 954).
* `IsProperStrongBundleCoveringSquare` (**Definition 19.8.19**, read as below),
  `IsProperStrongBundleCoveringSquareBook` (the printed conditions), `toBook`, and
  `StrongEpBundleCoveringModel.isProperSquare` (`Ξ` over `τ` is one).
* For `p̂ : M(Γ̂, Γ̂') → M(Γ, Γ')` (the top square of Theorem 19.8.22):
  `isStrongBundleMap_pbarSq`, `isLocalStrongBundleIso_pbarSq`, `surjective_pbarSq`.

## Readings

* Definition 19.8.13: "a set of uniformizers `F̃(β)` at `β` in the sense of Definition 19.8.13"
  refers to Definition 19.8.10 (`SquareUniformizer`).
* Definition 19.8.14 is Definition 19.8.4 for the underlying uniformizer construction
  `(Ψ, Ψ̂, Γ)` of `(P, μ_B)` (`toPullback`); we read (1)–(3) as there.
* Lemma 19.8.16: "fiber-wise a linear isomorphism" — the fibre of `m̂` over `(ê, φ̂, ê')`
  consists of the `(ŵ, (φ̂, Â(ŵ)), ŵ')` with `Q̂(ŵ) = ê`; `U` maps it to the fibre of `p*m` by
  `ŵ ↦ Ξ(ŵ)` in the first coordinate (`USq_src`), a linear isomorphism `Q̂⁻¹(ê) → Q⁻¹(τ ê)`
  (`fiberCLEXi`).  As in Theorem 19.8.6, the linear structure and the topology of the fibres of
  `m̂` are the ones making `U` fibrewise linear and a homeomorphism (Definition 19.8.17).
* The existence and uniqueness of `ŵ` with `Ξ(ŵ) = w`, `Q̂(ŵ) = ê` ("which follows from the
  properties of `K`, see (8.5.9)") is the fibrewise bijectivity of `Ξ`, part of the local strong
  bundle isomorphisms of Definition 8.5.9.
* Definition 19.8.19: besides the conditions printed, we read "proper" as including
  `a⁻¹(U(x)) = ⊔ᵢ U(x̂ᵢ)` (the `U(x̂ᵢ)` pairwise disjoint), as in Definition 8.5.1; the square `K`
  satisfies it.
-/

set_option maxSynthPendingDepth 3
set_option linter.unusedSectionVars false

namespace Polyfold

noncomputable section

universe u

open Set Function Topology TopologicalSpace

/-! ### Bijective local strong bundle isomorphisms over the identity -/

namespace StrongBundle

section IsoUniv

variable {X : Type*} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type*} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})]
  {Y' : Type*} [TopologicalSpace Y'] [T2Space Y'] [ParacompactSpace Y'] {P' : Y' → X}
  [∀ x, AddCommGroup (P' ⁻¹' {x})] [∀ x, Module ℝ (P' ⁻¹' {x})]
  {B : StrongBundle PX P} {B' : StrongBundle PX P'}

/-- **A strong bundle isomorphism over the whole base covering the identity is a strong bundle
isomorphism**, with inverse any two-sided inverse of the map. -/
theorem isStrongBundleIso_of_isStrongBundleIsoOn_univ {Φ : Y → Y'}
    (h : B.IsStrongBundleMap B' id Φ) (Φinv : Y' → Y) (hl : ∀ y, Φinv (Φ y) = y)
    (hr : ∀ y', Φ (Φinv y') = y') (hi : B.IsStrongBundleIsoOn B' h univ univ) :
    B.IsStrongBundleIso B' id Φ id Φinv := by
  obtain ⟨g, Ψ, hL⟩ := hi.exists_isLocalIso₂
  have hΨ : ∀ w, P' w ∈ univ → Φinv w = Ψ w := fun w _ => by
    calc Φinv w = Φinv (Φ (Ψ w)) := by rw [hL.right_inv (mem_univ (P' w))]
      _ = Ψ w := hl _
  have hg : ∀ y ∈ (univ : Set X), (id y : X) = g y := fun y _ =>
    (hL.base.right_inv y (mem_univ y)).symm
  have hL' := (hL.congr (fun _ _ => rfl) hΨ).congr_base (fun _ _ => rfl) hg
  refine ⟨h, IsStrongBundleMap.of_isLocalIso₂ (fun y' => hL'.symm.covers (mem_univ _))
    fun _ => ⟨univ, univ, id, Φ, mem_univ _, hL'.symm⟩, hl, hr⟩

/-- Over the identity of the base, a local strong bundle isomorphism `Y|U → Y'|U'` has
`U' = U`. -/
theorem IsStrongBundleIsoOn.target_eq_of_id {Φ : Y → Y'} {h : B.IsStrongBundleMap B' id Φ}
    {U U' : Set X} (hi : B.IsStrongBundleIsoOn B' h U U') : U' = U := by
  obtain ⟨g, hg⟩ := hi.isScDiffeoOn_base
  ext y
  refine ⟨fun hy => ?_, fun hy => hg.mapsTo hy⟩
  have := hg.mapsTo_inv hy
  rwa [← hg.right_inv y hy]

end IsoUniv

end StrongBundle

/-! ### Definition 19.8.19: proper strong bundle covering squares -/

section ProperSquare

variable {X : Type*} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {W : Type*} [TopologicalSpace W] [T2Space W] [ParacompactSpace W] {p : W → X}
  [∀ x, AddCommGroup (p ⁻¹' {x})] [∀ x, Module ℝ (p ⁻¹' {x})]
  {Xh : Type*} [TopologicalSpace Xh] [T2Space Xh] [ParacompactSpace Xh] {PXh : MPolyfold Xh}
  {Wh : Type*} [TopologicalSpace Wh] [T2Space Wh] [ParacompactSpace Wh] {ph : Wh → Xh}
  [∀ x, AddCommGroup (ph ⁻¹' {x})] [∀ x, Module ℝ (ph ⁻¹' {x})]

/-- **2021 Definition 19.8.19, p. 954, as printed**: strong bundles `p̂ : Ŵ → X̂`, `p : W → X`,
a surjective local sc-diffeomorphism `a : X̂ → X` with finite fibres `a⁻¹(x) = {x̂₁, …, x̂ₖ}`,
and `â : Ŵ → W` covering `a`, such that for every `x` there are open `U(x)`, `U(x̂ᵢ)` with
`â : Ŵ|U(x̂ᵢ) → W|U(x)` a strong bundle isomorphism over the sc-diffeomorphism
`a : U(x̂ᵢ) → U(x)`. -/
structure IsProperStrongBundleCoveringSquareBook (Bh : StrongBundle PXh ph) (B : StrongBundle PX p)
    (a : Xh → X) (ah : Wh → W) : Prop where
  isStrongBundleMap : Bh.IsStrongBundleMap B a ah
  surjective : Surjective a
  isLocalScDiffeo : PXh.IsLocalScDiffeo PX a
  finite_fiber : ∀ x, (a ⁻¹' {x}).Finite
  exists_sheets : ∀ x, ∃ (U : Set X) (U' : Xh → Set Xh), IsOpen U ∧ x ∈ U ∧
    ∀ y ∈ a ⁻¹' {x}, y ∈ U' y ∧ Bh.IsStrongBundleIsoOn B isStrongBundleMap (U' y) U

/-- **2021 Definition 19.8.19, p. 954 (proper strong bundle covering square)**, with "proper"
read as including `a⁻¹(U(x)) = ⊔ᵢ U(x̂ᵢ)` (the `U(x̂ᵢ)` pairwise disjoint), as in Definition 8.5.1
and Definition 8.5.9 (2). -/
structure IsProperStrongBundleCoveringSquare (Bh : StrongBundle PXh ph) (B : StrongBundle PX p)
    (a : Xh → X) (ah : Wh → W) : Prop where
  isStrongBundleMap : Bh.IsStrongBundleMap B a ah
  surjective : Surjective a
  isLocalScDiffeo : PXh.IsLocalScDiffeo PX a
  finite_fiber : ∀ x, (a ⁻¹' {x}).Finite
  evenlyCovered : ∀ x, ∃ (U : Set X) (U' : Xh → Set Xh), IsOpen U ∧ x ∈ U ∧
    (a ⁻¹' {x}).PairwiseDisjoint U' ∧
    (∀ y ∈ a ⁻¹' {x}, y ∈ U' y ∧ Bh.IsStrongBundleIsoOn B isStrongBundleMap (U' y) U) ∧
    a ⁻¹' U = ⋃ y ∈ a ⁻¹' {x}, U' y

/-- The reading of Definition 19.8.19 implies the printed conditions. -/
theorem IsProperStrongBundleCoveringSquare.toBook {Bh : StrongBundle PXh ph}
    {B : StrongBundle PX p} {a : Xh → X} {ah : Wh → W}
    (h : IsProperStrongBundleCoveringSquare Bh B a ah) :
    IsProperStrongBundleCoveringSquareBook Bh B a ah :=
  ⟨h.isStrongBundleMap, h.surjective, h.isLocalScDiffeo, h.finite_fiber, fun x => by
    obtain ⟨U, U', hU, hx, -, hs, -⟩ := h.evenlyCovered x
    exact ⟨U, U', hU, hx, hs⟩⟩

end ProperSquare

namespace GroupoidalCategory

open GroupoidStr (TransitionSet)
open EpGroupoid EpGroupoid.Examples

variable {A B : GroupoidalCategory.{u}}

/-! ### The fibres of `Ξ` and `⟨Q̂, Ξ⟩ : Ŵ → τ*W` -/

section ModelLift

variable {G O : Type u} [Group G] [Finite G] [TopologicalSpace G] [DiscreteTopology G]
  [TopologicalSpace O] [T2Space O] [ParacompactSpace O] [MulAction G O] {PO : MPolyfold O}
  {hP : ∀ g : G, PO.IsScSmoothMap PO fun y => g • y}
  {ObjE MorE : Type u} [TopologicalSpace ObjE] [T2Space ObjE] [ParacompactSpace ObjE]
  [TopologicalSpace MorE] [T2Space MorE] [ParacompactSpace MorE] {E : EpGroupoid ObjE MorE}
  {τ : EpFunctor E (actionEpGroupoid hP)}

namespace StrongEpBundleCoveringModel

variable {M : ProperCoveringModel τ} (K : StrongEpBundleCoveringModel M)

/-- `Ξ : Ŵ → W` is a strong bundle map covering `τ̂`. -/
theorem isStrongBundleMap_Ξ : K.BWh.IsStrongBundleMap K.BW τ.obj K.Ξ := by
  have := K.BW.paracompactSpace_pullback (actionEpGroupoid hP).PMor (actionEpGroupoid hP).src
  have := K.BWh.paracompactSpace_pullback E.PMor E.src
  exact K.isCovering.isMap.isStrongBundleMap

theorem Q_Ξ (w : K.Wh) : K.Q (K.Ξ w) = τ.obj (K.Qh w) := K.isStrongBundleMap_Ξ.covers w

/-- `Ξ` is near every point a strong bundle isomorphism (Definition 8.5.9 (1)). -/
theorem exists_isStrongBundleIsoOn_Ξ (e : ObjE) : ∃ (U : Set ObjE) (U' : Set O), e ∈ U ∧
    K.BWh.IsStrongBundleIsoOn K.BW K.isStrongBundleMap_Ξ U U' := by
  have := K.BW.paracompactSpace_pullback (actionEpGroupoid hP).PMor (actionEpGroupoid hP).src
  have := K.BWh.paracompactSpace_pullback E.PMor E.src
  exact K.isCovering.isLocalStrongBundleIso e

/-- **`Ξ` on the fibres**, a topological linear isomorphism `Q̂⁻¹(ê) → Q⁻¹(τ ê)`. -/
def fiberCLEXi (e : ObjE) : K.Qh ⁻¹' {e} ≃L[ℝ] K.Q ⁻¹' {τ.obj e} :=
  (Classical.choose_spec (Classical.choose_spec (K.exists_isStrongBundleIsoOn_Ξ e))).2.fiberEquiv
    (Classical.choose_spec (Classical.choose_spec (K.exists_isStrongBundleIsoOn_Ξ e))).1

@[simp] theorem fiberCLEXi_apply (e : ObjE) (v : K.Qh ⁻¹' {e}) :
    (K.fiberCLEXi e v : K.W) = K.Ξ v := rfl

/-- **The point `ŵ` over `ê` with `Ξ(ŵ) = w`**, for `Q(w) = τ̂(ê)` (p. 951). -/
def liftPt (e : ObjE) (w : K.W) (h : K.Q w = τ.obj e) : K.Wh :=
  ((K.fiberCLEXi e).symm ⟨w, h⟩ : K.Wh)

theorem Qh_liftPt (e : ObjE) (w : K.W) (h : K.Q w = τ.obj e) : K.Qh (K.liftPt e w h) = e :=
  ((K.fiberCLEXi e).symm ⟨w, h⟩).2

theorem Ξ_liftPt (e : ObjE) (w : K.W) (h : K.Q w = τ.obj e) : K.Ξ (K.liftPt e w h) = w := by
  rw [liftPt, ← fiberCLEXi_apply, ContinuousLinearEquiv.apply_symm_apply]

theorem liftPt_eq {e : ObjE} {w : K.W} (h : K.Q w = τ.obj e) {v : K.Wh} (he : K.Qh v = e)
    (hw : K.Ξ v = w) : K.liftPt e w h = v := by
  subst he hw
  have : (⟨K.Ξ v, h⟩ : K.Q ⁻¹' {τ.obj (K.Qh v)}) = K.fiberCLEXi (K.Qh v) ⟨v, rfl⟩ := rfl
  rw [liftPt, this, ContinuousLinearEquiv.symm_apply_apply]

/-- `ŵ` is determined by `Q̂(ŵ)` and `Ξ(ŵ)`. -/
theorem eq_of_Qh_Ξ {v v' : K.Wh} (h₁ : K.Qh v = K.Qh v') (h₂ : K.Ξ v = K.Ξ v') : v = v' := by
  have h : K.Q (K.Ξ v) = τ.obj (K.Qh v') := (K.Q_Ξ v).trans (congrArg τ.obj h₁)
  exact (K.liftPt_eq h h₁ rfl).symm.trans (K.liftPt_eq h rfl h₂.symm)

instance instParacompactSpaceTauW : ParacompactSpace (pullbackSpace K.Q τ.obj) :=
  K.BW.paracompactSpace_pullback E.PObj τ.obj

/-- **`⟨Q̂, Ξ⟩ : Ŵ → τ*W`**, `ŵ ↦ (Q̂(ŵ), Ξ(ŵ))` (p. 952). -/
def liftK : K.Wh → pullbackSpace K.Q τ.obj := pullbackPair K.Q τ.obj K.Qh K.Ξ K.Q_Ξ

/-- The inverse of `⟨Q̂, Ξ⟩`: `(ê, w) ↦ ŵ`. -/
def liftKinv (p : pullbackSpace K.Q τ.obj) : K.Wh :=
  K.liftPt (p : ObjE × K.W).1 (p : ObjE × K.W).2 p.2

theorem liftKinv_liftK (v : K.Wh) : K.liftKinv (K.liftK v) = v := K.liftPt_eq _ rfl rfl

theorem liftK_liftKinv (p : pullbackSpace K.Q τ.obj) : K.liftK (K.liftKinv p) = p :=
  Subtype.ext (Prod.ext (K.Qh_liftPt _ _ _) (K.Ξ_liftPt _ _ _))

theorem isStrongBundleMap_liftK :
    K.BWh.IsStrongBundleMap (K.BW.pullback τ.isScSmoothMap_obj) id K.liftK :=
  K.BW.isStrongBundleMap_pullbackPair τ.isScSmoothMap_obj MPolyfold.isScSmoothMap_id
    K.isStrongBundleMap_Ξ

theorem isStrongBundleIsoOn_liftK (e : ObjE) : ∃ U : Set ObjE, e ∈ U ∧
    K.BWh.IsStrongBundleIsoOn (K.BW.pullback τ.isScSmoothMap_obj) K.isStrongBundleMap_liftK
      U U := by
  obtain ⟨U, U', he, hi⟩ := K.exists_isStrongBundleIsoOn_Ξ e
  obtain ⟨V, V', σ, heV, hd⟩ := M.isLocalScDiffeo e
  have hπ := K.BW.isStrongBundleIsoOn_pullbackProj' τ.isScSmoothMap_obj hd e
  obtain ⟨g, hg⟩ := hi.isScDiffeoOn_base
  have hUV : IsOpen (U ∩ V) := hg.isOpen_source.inter hd.isOpen_source
  have hi' := hi.restrict hg hUV inter_subset_left
  have hc : K.BWh.IsStrongBundleIsoOn K.BW
      ((K.BW.isStrongBundleMap_pullbackProj' τ.isScSmoothMap_obj).comp K.isStrongBundleMap_liftK)
      (U ∩ V) (U' ∩ g ⁻¹' (U ∩ V)) := hi'
  have hres := hc.of_comp (h := K.isStrongBundleMap_liftK) hπ (fun x hx => hx.2)
  have ht := hres.target_eq_of_id
  rw [ht] at hres
  exact ⟨U ∩ V, ⟨he, heV⟩, hres⟩

/-- **`⟨Q̂, Ξ⟩ : Ŵ → τ*W` is a strong bundle isomorphism over `Ê`** (p. 952). -/
theorem isStrongBundleIso_liftK :
    K.BWh.IsStrongBundleIso (K.BW.pullback τ.isScSmoothMap_obj) id K.liftK id K.liftKinv :=
  StrongBundle.isStrongBundleIso_of_isStrongBundleIsoOn_univ K.isStrongBundleMap_liftK
    K.liftKinv K.liftKinv_liftK K.liftK_liftKinv
    (StrongBundle.isStrongBundleIsoOn_univ_of_local K.isStrongBundleMap_liftK K.liftKinv
      K.liftKinv_liftK K.liftK_liftKinv K.isStrongBundleIsoOn_liftK)

/-- **`K` is a proper strong bundle covering square** (p. 955, Definition 19.8.19): `Ξ` over
`τ̂ : Ê → O` (Definition 8.5.9). -/
theorem isProperSquare : IsProperStrongBundleCoveringSquare K.BWh K.BW τ.obj K.Ξ := by
  have := K.BW.paracompactSpace_pullback (actionEpGroupoid hP).PMor (actionEpGroupoid hP).src
  have := K.BWh.paracompactSpace_pullback E.PMor E.src
  exact ⟨K.isStrongBundleMap_Ξ, M.surjective, M.isLocalScDiffeo,
    K.isCovering.isProperCovering.finite_fiber, K.isCovering.evenlyCovered⟩

end StrongEpBundleCoveringModel

end ModelLift

/-! ### The pull-back `τ*W` of a uniformizer for `(P, μ_B)` -/

namespace PullbackUniformizer

variable {P : GroupoidFunctor A.toGroupoidStr B.toGroupoidStr} {μ : B.BanFunctor} {β : B.Obj}
  (x : PullbackUniformizer P μ β)

instance instParacompactSpaceTauW : ParacompactSpace x.TauW :=
  x.bun.bundle.paracompactSpace_pullback x.Ψh.E.PObj x.Ψh.τ.obj

instance instParacompactSpaceWMor :
    ParacompactSpace (pullbackSpace x.bun.Q (actionEpGroupoid x.Ψh.Ψ.smooth_smul).src) :=
  x.bun.bundle.paracompactSpace_pullback (actionEpGroupoid x.Ψh.Ψ.smooth_smul).PMor
    (actionEpGroupoid x.Ψh.Ψ.smooth_smul).src

instance instParacompactSpaceTauWMor :
    ParacompactSpace (pullbackSpace (pullbackProj x.bun.Q x.Ψh.τ.obj) x.Ψh.E.src) :=
  (x.bun.bundle.pullback x.Ψh.τ.isScSmoothMap_obj).paracompactSpace_pullback x.Ψh.E.PMor
    x.Ψh.E.src

end PullbackUniformizer

/-! ### Definitions 19.8.13–19.8.15 -/

/-- The covering functor of a bundle covering square is finite-to-one. -/
instance BundleCoveringSquare.instFactIsFiniteToOneCovering (S : BundleCoveringSquare A B) :
    Fact (IsFiniteToOneCovering S.P) := ⟨S.isFiniteToOneCovering⟩

/-- **2021 Definition 19.8.13, p. 948 (uniformizer construction for `𝔈`)**: a set `F̃(β)` of
uniformizers `Γ̂ : K → 𝔈` at `β` (Definition 19.8.10) for every object `β`. -/
structure SquareUniformizerConstruction (S : BundleCoveringSquare A B) : Type (u + 1) where
  /-- The sets `F̃(β)`. -/
  F : ∀ β : B.Obj, Set (SquareUniformizer S β)

namespace SquareUniformizerConstruction

variable {S : BundleCoveringSquare A B} (Ft : SquareUniformizerConstruction S)

/-- **The underlying uniformizer construction for `(P, μ_B)`** (Definition 19.8.2): the triples
`(Ψ, Ψ̂, Γ)` of the members of `F̃`. -/
def toPullback : PullbackUniformizerConstruction S.P S.μB :=
  ⟨fun β => (fun x : SquareUniformizer S β => x.toPullbackUniformizer) '' Ft.F β⟩

/-- A member of `F̃`: `β` and `Γ̂ ∈ F̃(β)`. -/
structure Unif where
  /-- The object `β`. -/
  β : B.Obj
  /-- The uniformizer `Γ̂ : K → 𝔈`. -/
  x : SquareUniformizer S β
  mem : x ∈ Ft.F β

variable {Ft}

/-- The underlying member `(Ψ, Ψ̂, Γ)` of the uniformizer construction for `(P, μ_B)`. -/
def Unif.toPU (X : Ft.Unif) : Ft.toPullback.Unif :=
  ⟨X.β, X.x.toPullbackUniformizer, ⟨X.x, X.mem, rfl⟩⟩

@[simp] theorem Unif.toPU_x (X : Ft.Unif) : X.toPU.x = X.x.toPullbackUniformizer := rfl

variable (Ft)

/-- **2021 Definition 19.8.13**: the members of `F̃(β)` are uniformizers at `β`, and their
triples `(Ψ, Ψ̂, Γ)` form the uniformizer construction `toPullback` for `(P, μ_B)`. -/
theorem definition_19_8_13 (β : B.Obj) :
    (∀ x ∈ Ft.F β, x.Ψh.Ψ.obj x.Ψh.model.pt = β) ∧
      ∀ x ∈ Ft.F β, x.toPullbackUniformizer ∈ Ft.toPullback.F β :=
  ⟨fun x _ => x.Ψh.obj_pt, fun x hx => ⟨x, hx, rfl⟩⟩

/-- **2021 Definition 19.8.14, p. 948 (compatible transition construction)**: a transition
construction `𝓕` for the underlying `F` with (1) a metrizable natural topology `T_{|B|}`, (2) the
coherence of `(F̄, 𝓕)` and (3) `(F̂, 𝓕)` a basic construction for `P`: a transition construction
for `toPullback` in the sense of Definition 19.8.4. -/
abbrev CompatibleTransitionConstruction : Type (u + 1) :=
  Ft.toPullback.PullbackTransitionConstruction

/-- **2021 Definition 19.8.14, (1)–(3).** -/
theorem definition_19_8_14 (T : Ft.CompatibleTransitionConstruction) :
    (Ft.toPullback.toCBC T.𝓕).HasClassUniformizers ∧
      @MetrizableSpace B.OrbitSpace
        ((Ft.toPullback.toCBC T.𝓕).toBasic.natTop T.hasClassUniformizers.toBasic) ∧
      Ft.toPullback.IsCoherent T.𝓕 ∧ T.toCoveringBasicConstruction.hatU = Ft.toPullback.hatU :=
  ⟨T.hasClassUniformizers, T.metrizable, T.isCoherent, rfl⟩

end SquareUniformizerConstruction

/-- **2021 Definition 19.8.15, p. 949 (basic construction for `𝔈`)**: a uniformizer
construction `F̃` for `𝔈` with a compatible transition construction. -/
structure SquareBasicConstruction (S : BundleCoveringSquare A B) : Type (u + 1) where
  /-- The uniformizer construction `F̃`. -/
  Ft : SquareUniformizerConstruction S
  /-- The compatible transition construction `𝓕`. -/
  T : Ft.CompatibleTransitionConstruction

/-- The underlying basic construction for `(P, μ_B)` (Definition 19.8.5). -/
def SquareBasicConstruction.toPullbackBasic {S : BundleCoveringSquare A B}
    (Bs : SquareBasicConstruction S) :
    PullbackUniformizerConstruction.PullbackBasicConstruction S.P S.μB :=
  ⟨Bs.Ft.toPullback, Bs.T⟩

/-- **2021 Definition 19.8.15.** -/
theorem definition_19_8_15 {S : BundleCoveringSquare A B} (Bs : SquareBasicConstruction S) :
    Bs.toPullbackBasic.Ft = Bs.Ft.toPullback ∧ Bs.Ft.toPullback.IsCoherent Bs.T.𝓕 :=
  ⟨rfl, Bs.T.isCoherent⟩

/-! ### Lemma 19.8.16 and Definition 19.8.17 -/

namespace SquareUniformizerConstruction

variable {S : BundleCoveringSquare A B} (Ft : SquareUniformizerConstruction S)
  (𝓕 : Ft.toPullback.toUniformizerConstruction.TransitionConstruction) (X Y : Ft.Unif)

/-- **The transition set `M(Γ̂, Γ̂')`** of the functors `Γ̂ : Ŵ → E_A`, `Γ̂' : Ŵ' → E_A`: the
triples `(ŵ, (φ̂, Â(ŵ)), ŵ')` with `μ_A(φ̂)(Â(ŵ)) = Â'(ŵ')`. -/
def MSq (_𝓕 : Ft.toPullback.toUniformizerConstruction.TransitionConstruction) (X Y : Ft.Unif) :
    Type u :=
  S.μA.cat.toGroupoidStr.TransitionSet X.x.Γh.obj Y.x.Γh.obj

variable {Ft 𝓕 X Y}

/-- The underlying element of the transition set. -/
abbrev MSq.toTrans (h : Ft.MSq 𝓕 X Y) :
    S.μA.cat.toGroupoidStr.TransitionSet X.x.Γh.obj Y.x.Γh.obj := h

variable (Ft 𝓕 X Y)

/-- **`m̂ : M(Γ̂, Γ̂') → M(Ψ̂, Ψ̂')`**: `(ŵ, (φ̂, Â(ŵ)), ŵ') ↦ (Q̂(ŵ), φ̂, Q̂'(ŵ'))` (p. 950). -/
def mSq (h : Ft.MSq 𝓕 X Y) : Ft.toPullback.MHatB 𝓕 X.toPU Y.toPU :=
  (⟨X.x.K.Qh h.toTrans.src, ((h.toTrans.mor : S.μA.cat.Mor) : A.Mor × S.μA.E).1,
    Y.x.K.Qh h.toTrans.tgt,
    (h.toTrans.mor.2 : S.μA.P _ = _).symm.trans
      ((congrArg S.μA.P h.toTrans.src_mor).trans (X.x.PA_obj h.toTrans.src)),
    (S.μA.P_act h.toTrans.mor).symm.trans
      ((congrArg S.μA.P h.toTrans.tgt_mor).trans (Y.x.PA_obj h.toTrans.tgt))⟩ :
    X.x.Ψh.Trans Y.x.Ψh)

/-- **`p̂ : M(Γ̂, Γ̂') → M(Γ, Γ')`** (19.87):
`(ŵ, (φ̂, Â(ŵ)), ŵ') ↦ (Ξ(ŵ), (P(φ̂), A(Ξ(ŵ))), Ξ'(ŵ'))`. -/
def pbarSq (h : Ft.MSq 𝓕 X Y) : Ft.toPullback.MG 𝓕 X.toPU Y.toPU :=
  (⟨X.x.K.Ξ h.toTrans.src, S.Phat.mor h.toTrans.mor, Y.x.K.Ξ h.toTrans.tgt,
    (congrArg S.ThetaE h.toTrans.src_mor).trans (X.x.comm_obj h.toTrans.src),
    (S.act_PhatMor h.toTrans.mor).trans
      ((congrArg S.ThetaE h.toTrans.tgt_mor).trans (Y.x.comm_obj h.toTrans.tgt))⟩ :
    X.toPU.x.TransG Y.toPU.x)

/-- **The diagram (19.86)**: `m ∘ p̂ = p ∘ m̂`. -/
theorem mGmap_pbarSq (h : Ft.MSq 𝓕 X Y) :
    Ft.toPullback.mGmap 𝓕 X.toPU Y.toPU (Ft.pbarSq 𝓕 X Y h) =
      Ft.toPullback.pBmap 𝓕 X.toPU Y.toPU (Ft.mSq 𝓕 X Y h) :=
  TransitionSet.ext (X.x.K.Q_Ξ h.toTrans.src) rfl (Y.x.K.Q_Ξ h.toTrans.tgt)

/-- **2021 (19.90): `U : M(Γ̂, Γ̂') → p*M(Γ, Γ')`**,
`U(ŵ, (φ̂, Â(ŵ)), ŵ') = ((Q̂(ŵ), φ̂, Q̂'(ŵ')), (Ξ(ŵ), (P(φ̂), A(Ξ(ŵ))), Ξ'(ŵ')))`. -/
def USq (h : Ft.MSq 𝓕 X Y) : Ft.toPullback.PB 𝓕 X.toPU Y.toPU :=
  ⟨(Ft.mSq 𝓕 X Y h, Ft.pbarSq 𝓕 X Y h), Ft.mGmap_pbarSq 𝓕 X Y h⟩

/-- **The inverse of `U`** (p. 951): `((ê, φ̂, ê'), (w, (P(φ̂), A(w)), w')) ↦ (ŵ, (φ̂, Â(ŵ)), ŵ')`
with `ŵ`, `ŵ'` the points over `ê`, `ê'` with `Ξ(ŵ) = w`, `Ξ'(ŵ') = w'`; it lies in
`M(Γ̂, Γ̂')` by (19.92), since `Θ` is injective on the fibres. -/
def USqInv (z : Ft.toPullback.PB 𝓕 X.toPU Y.toPU) : Ft.MSq 𝓕 X Y :=
  let a : X.x.Ψh.Trans Y.x.Ψh :=
    (z : Ft.toPullback.MHatB 𝓕 X.toPU Y.toPU × Ft.toPullback.MG 𝓕 X.toPU Y.toPU).1
  let g : X.toPU.x.TransG Y.toPU.x :=
    (z : Ft.toPullback.MHatB 𝓕 X.toPU Y.toPU × Ft.toPullback.MG 𝓕 X.toPU Y.toPU).2
  have hs : X.x.K.Q g.src = X.x.Ψh.τ.obj a.src := congrArg TransitionSet.src z.2
  have ht : Y.x.K.Q g.tgt = Y.x.Ψh.τ.obj a.tgt := congrArg TransitionSet.tgt z.2
  have hm : ((g.mor : S.μB.cat.Mor) : B.Mor × S.μB.E).1 = S.P.mor a.mor :=
    congrArg TransitionSet.mor z.2
  ⟨X.x.K.liftPt a.src g.src hs,
    ⟨(a.mor, X.x.Γh.obj (X.x.K.liftPt a.src g.src hs)),
      (X.x.PA_obj _).trans ((congrArg X.x.Ψh.hat.obj (X.x.K.Qh_liftPt _ _ _)).trans
        a.src_mor.symm)⟩,
    Y.x.K.liftPt a.tgt g.tgt ht, rfl, by
      refine S.ThetaE_injective_fiber ((S.μA.P_act _).trans (a.tgt_mor.trans
        ((congrArg Y.x.Ψh.hat.obj (Y.x.K.Qh_liftPt _ _ _)).symm.trans (Y.x.PA_obj _).symm)))
        ((S.act_PhatMor _).symm.trans ?_)
      refine (S.μB.act_congr (Prod.ext hm.symm ?_)).trans (g.tgt_mor.trans
        ((congrArg Y.x.Γ.obj (Y.x.K.Ξ_liftPt _ _ _)).symm.trans (Y.x.comm_obj _).symm))
      exact (X.x.comm_obj _).trans ((congrArg X.x.Γ.obj (X.x.K.Ξ_liftPt _ _ _)).trans
        g.src_mor.symm)⟩

theorem USqInv_USq (h : Ft.MSq 𝓕 X Y) : Ft.USqInv 𝓕 X Y (Ft.USq 𝓕 X Y h) = h :=
  TransitionSet.ext (X.x.K.liftPt_eq _ rfl rfl)
    (Subtype.ext (Prod.ext rfl ((congrArg X.x.Γh.obj (X.x.K.liftPt_eq _ rfl rfl)).trans
      h.toTrans.src_mor.symm)))
    (Y.x.K.liftPt_eq _ rfl rfl)

theorem USq_USqInv (z : Ft.toPullback.PB 𝓕 X.toPU Y.toPU) :
    Ft.USq 𝓕 X Y (Ft.USqInv 𝓕 X Y z) = z := by
  obtain ⟨⟨a, g⟩, hz⟩ := z
  have hm : ((g.mor : S.μB.cat.Mor) : B.Mor × S.μB.E).1 =
      S.P.mor (a : X.x.Ψh.Trans Y.x.Ψh).mor := congrArg TransitionSet.mor hz
  refine Subtype.ext (Prod.ext ?_ ?_)
  · exact TransitionSet.ext (X.x.K.Qh_liftPt _ _ _) rfl (Y.x.K.Qh_liftPt _ _ _)
  · refine TransitionSet.ext (X.x.K.Ξ_liftPt _ _ _) (Subtype.ext (Prod.ext hm.symm ?_))
      (Y.x.K.Ξ_liftPt _ _ _)
    exact (X.x.comm_obj _).trans ((congrArg X.x.Γ.obj (X.x.K.Ξ_liftPt _ _ _)).trans
      g.src_mor.symm)

/-- `U` as an equivalence. -/
def USqEquiv : Ft.MSq 𝓕 X Y ≃ Ft.toPullback.PB 𝓕 X.toPU Y.toPU where
  toFun := Ft.USq 𝓕 X Y
  invFun := Ft.USqInv 𝓕 X Y
  left_inv := Ft.USqInv_USq 𝓕 X Y
  right_inv := Ft.USq_USqInv 𝓕 X Y

/-- On the first coordinate `U` is `Ξ`: `(p̂ h).src = Ξ(h.src)`. -/
theorem USq_src (h : Ft.MSq 𝓕 X Y) : (Ft.pbarSq 𝓕 X Y h).src = X.x.K.Ξ h.toTrans.src := rfl

/-- **2021 Lemma 19.8.16, p. 951**: `U : M(Γ̂, Γ̂') → p*M(Γ, Γ')` is a bijection covering the
identity of `M(Ψ̂, Ψ̂')` (diagram (19.89)) whose second component is `p̂` (19.87); on the fibre
over `(ê, φ̂, ê')` it is `ŵ ↦ Ξ(ŵ)` in the first coordinate, and `Ξ : Q̂⁻¹(ê) → Q⁻¹(τ ê)` is a
topological linear isomorphism; the source `ŵ` of `h ∈ M(Γ̂, Γ̂')` is determined by `U(h)`. -/
theorem lemma_19_8_16 :
    Bijective (Ft.USq 𝓕 X Y) ∧
      (∀ h, pullbackProj (Ft.toPullback.mGmap 𝓕 X.toPU Y.toPU)
        (Ft.toPullback.pBmap 𝓕 X.toPU Y.toPU) (Ft.USq 𝓕 X Y h) = Ft.mSq 𝓕 X Y h) ∧
      (∀ h, pullbackProj' (Ft.toPullback.mGmap 𝓕 X.toPU Y.toPU)
        (Ft.toPullback.pBmap 𝓕 X.toPU Y.toPU) (Ft.USq 𝓕 X Y h) = Ft.pbarSq 𝓕 X Y h) ∧
      (∀ h, (Ft.pbarSq 𝓕 X Y h).src = X.x.K.Ξ h.toTrans.src ∧
        (Ft.mSq 𝓕 X Y h : X.x.Ψh.Trans Y.x.Ψh).src = X.x.K.Qh h.toTrans.src) ∧
      (∀ (e : X.x.Ψh.ObjE) (v : X.x.K.Qh ⁻¹' {e}),
        (X.x.K.fiberCLEXi e v : X.x.K.W) = X.x.K.Ξ v) :=
  ⟨(Ft.USqEquiv 𝓕 X Y).bijective, fun _ => rfl, fun _ => rfl, fun _ => ⟨rfl, rfl⟩,
    fun _ _ => rfl⟩

/-- **The topology of `M(Γ̂, Γ̂')`**: the one making `U` a homeomorphism. -/
instance instTopologicalSpaceMSq : TopologicalSpace (Ft.MSq 𝓕 X Y) :=
  TopologicalSpace.induced (Ft.USq 𝓕 X Y) inferInstance

/-- **`U` as a homeomorphism.** -/
def USqHomeo : Ft.MSq 𝓕 X Y ≃ₜ Ft.toPullback.PB 𝓕 X.toPU Y.toPU where
  toEquiv := Ft.USqEquiv 𝓕 X Y
  continuous_toFun := continuous_induced_dom
  continuous_invFun := continuous_induced_rng.2 (by
    have : Ft.USq 𝓕 X Y ∘ Ft.USqInv 𝓕 X Y = id := funext (Ft.USq_USqInv 𝓕 X Y)
    change Continuous (Ft.USq 𝓕 X Y ∘ Ft.USqInv 𝓕 X Y)
    rw [this]; exact continuous_id)

instance instT2SpaceMSq : T2Space (Ft.MSq 𝓕 X Y) := (Ft.USqHomeo 𝓕 X Y).isEmbedding.t2Space

instance instParacompactSpaceMSq : ParacompactSpace (Ft.MSq 𝓕 X Y) :=
  (Ft.USqHomeo 𝓕 X Y).isClosedEmbedding.paracompactSpace

/-- The fibres of `m̂` are those of `p*m` (via `U`). -/
def fiberSqEquiv (a : Ft.toPullback.MHatB 𝓕 X.toPU Y.toPU) :
    Ft.mSq 𝓕 X Y ⁻¹' {a} ≃ pullbackProj (Ft.toPullback.mGmap 𝓕 X.toPU Y.toPU)
      (Ft.toPullback.pBmap 𝓕 X.toPU Y.toPU) ⁻¹' {a} :=
  fiberEquivOver (Pr := pullbackProj (Ft.toPullback.mGmap 𝓕 X.toPU Y.toPU)
      (Ft.toPullback.pBmap 𝓕 X.toPU Y.toPU)) (Pr' := Ft.mSq 𝓕 X Y)
    (Ft.USqEquiv 𝓕 X Y) (fun _ => rfl) a

instance instAddCommGroupFiberSq (a : Ft.toPullback.MHatB 𝓕 X.toPU Y.toPU) :
    AddCommGroup (Ft.mSq 𝓕 X Y ⁻¹' {a}) :=
  (Ft.fiberSqEquiv 𝓕 X Y a).addCommGroup

instance instModuleFiberSq (a : Ft.toPullback.MHatB 𝓕 X.toPU Y.toPU) :
    Module ℝ (Ft.mSq 𝓕 X Y ⁻¹' {a}) :=
  (Ft.fiberSqEquiv 𝓕 X Y a).module ℝ

/-- `U⁻¹` on the fibres, a linear isomorphism. -/
def fiberSqLin (a : Ft.toPullback.MHatB 𝓕 X.toPU Y.toPU) :
    pullbackProj (Ft.toPullback.mGmap 𝓕 X.toPU Y.toPU) (Ft.toPullback.pBmap 𝓕 X.toPU Y.toPU) ⁻¹'
      {a} ≃ₗ[ℝ] Ft.mSq 𝓕 X Y ⁻¹' {a} :=
  (Equiv.linearEquiv ℝ (Ft.fiberSqEquiv 𝓕 X Y a)).symm

theorem fiberSqLin_apply (a : Ft.toPullback.MHatB 𝓕 X.toPU Y.toPU)
    (v : pullbackProj (Ft.toPullback.mGmap 𝓕 X.toPU Y.toPU)
      (Ft.toPullback.pBmap 𝓕 X.toPU Y.toPU) ⁻¹' {a}) :
    (Ft.fiberSqLin 𝓕 X Y a v : Ft.MSq 𝓕 X Y) = (Ft.USqHomeo 𝓕 X Y).symm v := rfl

/-- **2021 Definition 19.8.17, p. 952: the strong bundle structure of
`m̂ : M(Γ̂, Γ̂') → M(Ψ̂, Ψ̂')`**, transported from `p*M(Γ, Γ')` along `U⁻¹`. -/
def bundleSq : StrongBundle (Ft.toPullback.hatPoly 𝓕 X.toPU Y.toPU) (Ft.mSq 𝓕 X Y) :=
  (Ft.toPullback.pullBundle 𝓕 X.toPU Y.toPU).transport (Ft.USqHomeo 𝓕 X Y).symm
    (Ft.fiberSqLin 𝓕 X Y) (Ft.fiberSqLin_apply 𝓕 X Y)

/-- **`U` is a strong bundle isomorphism covering the identity of `M(Ψ̂, Ψ̂')`**
(Definition 19.8.17). -/
theorem isStrongBundleIso_USq :
    (Ft.bundleSq 𝓕 X Y).IsStrongBundleIso (Ft.toPullback.pullBundle 𝓕 X.toPU Y.toPU) id
      (Ft.USq 𝓕 X Y) id (Ft.USqInv 𝓕 X Y) :=
  (StrongBundle.isStrongBundleIso_transport (Ft.toPullback.pullBundle 𝓕 X.toPU Y.toPU)).symm

/-- **Uniqueness in Definition 19.8.17**: any strong bundle structure on `m̂` for which `U` is a
strong bundle isomorphism agrees with `bundleSq`. -/
theorem bundleSq_unique (B' : StrongBundle (Ft.toPullback.hatPoly 𝓕 X.toPU Y.toPU) (Ft.mSq 𝓕 X Y))
    (hB' : B'.IsStrongBundleIso (Ft.toPullback.pullBundle 𝓕 X.toPU Y.toPU) id (Ft.USq 𝓕 X Y) id
      (Ft.USqInv 𝓕 X Y)) :
    B'.IsStrongBundleIso (Ft.bundleSq 𝓕 X Y) id id id id :=
  StrongBundle.isStrongBundleIso_id_of_isStrongBundleIsoOn B' (Ft.bundleSq 𝓕 X Y) hB'.toMap
    (Ft.isStrongBundleIso_USq 𝓕 X Y).toMap
    (fun _ => ⟨univ, univ, mem_univ _, hB'.isStrongBundleIsoOn_univ⟩)
    (fun _ => ⟨univ, univ, mem_univ _, (Ft.isStrongBundleIso_USq 𝓕 X Y).isStrongBundleIsoOn_univ⟩)

end SquareUniformizerConstruction

/-! ### Lemma 19.8.18 -/

namespace SquareUniformizerConstruction

variable {S : BundleCoveringSquare A B} (Ft : SquareUniformizerConstruction S)
  (𝓕 : Ft.toPullback.toUniformizerConstruction.TransitionConstruction) (X Y : Ft.Unif)

/-- **The source map `s : M(Γ, Γ') → W`**, `(w, (φ, A(w)), w') ↦ w`. -/
def srcG (h : Ft.toPullback.MG 𝓕 X.toPU Y.toPU) : X.toPU.x.bun.W :=
  (h : X.toPU.x.TransG Y.toPU.x).src

/-- `s : M(Γ, Γ') → W` is a strong bundle map covering `s : M(Ψ, Ψ') → O`. -/
theorem isStrongBundleMap_srcG :
    (Ft.toPullback.bundleG 𝓕 X.toPU Y.toPU).IsStrongBundleMap X.x.K.BW
      (Ft.toPullback.srcB 𝓕 X.toPU Y.toPU) (Ft.srcG 𝓕 X Y) :=
  (X.toPU.x.bun.bundle.isStrongBundleMap_pullbackProj'
    (Ft.toPullback.isScSmoothMap_srcB 𝓕 X.toPU Y.toPU)).comp
    (Ft.toPullback.isStrongBundleIso_altH 𝓕 X.toPU Y.toPU).invMap

/-- **`s : M(Γ, Γ') → W` is a local strong bundle isomorphism** (p. 953): it is `H⁻¹` followed by
the projection of the pull-back along the local sc-diffeomorphism `s : M(Ψ, Ψ') → O`. -/
theorem isLocalStrongBundleIso_srcG (k : Ft.toPullback.MBase 𝓕 X.toPU Y.toPU) :
    ∃ (U : Set (Ft.toPullback.MBase 𝓕 X.toPU Y.toPU)) (U' : Set X.toPU.x.Ψh.Ψ.O), k ∈ U ∧
      (Ft.toPullback.bundleG 𝓕 X.toPU Y.toPU).IsStrongBundleIsoOn X.x.K.BW
        (Ft.isStrongBundleMap_srcG 𝓕 X Y) U U' := by
  obtain ⟨V, V', σ, hk, hd⟩ :=
    (Ft.toPullback.toCBC 𝓕).isLocalScDiffeo_srcB' X.toPU.toHat Y.toPU.toHat k
  have hπ := X.toPU.x.bun.bundle.isStrongBundleIsoOn_pullbackProj'
    (Ft.toPullback.isScSmoothMap_srcB 𝓕 X.toPU Y.toPU) hd k
  exact hπ.exists_comp
    (Ft.toPullback.isStrongBundleIso_altH 𝓕 X.toPU Y.toPU).symm.isStrongBundleIsoOn_univ
    (mem_univ k) hk

/-- The source `ŝ : M(Ψ̂, Ψ̂') → Ê`, `(ê, φ̂, ê') ↦ ê`. -/
abbrev srcH (a : Ft.toPullback.MHatB 𝓕 X.toPU Y.toPU) : X.toPU.x.Ψh.ObjE :=
  (Ft.toPullback.toCBC 𝓕).srcHat X.toPU.toHat Y.toPU.toHat a

theorem isLocalScDiffeo_srcH :
    (Ft.toPullback.hatPoly 𝓕 X.toPU Y.toPU).IsLocalScDiffeo X.toPU.x.Ψh.E.PObj (Ft.srcH 𝓕 X Y) :=
  (Ft.toPullback.toCBC 𝓕).isLocalScDiffeo_srcHat Fact.out X.toPU.toHat Y.toPU.toHat

/-- `(ê, w)` for `((ê, φ̂, ê'), (w, (φ, A(w)), w')) ∈ p*M(Γ, Γ')`, a point of `τ*W`. -/
def TMap : Ft.toPullback.PB 𝓕 X.toPU Y.toPU → pullbackSpace X.toPU.x.bun.Q X.toPU.x.Ψh.τ.obj :=
  pullbackPair X.toPU.x.bun.Q X.toPU.x.Ψh.τ.obj
    (Ft.srcH 𝓕 X Y ∘ pullbackProj (Ft.toPullback.mGmap 𝓕 X.toPU Y.toPU)
      (Ft.toPullback.pBmap 𝓕 X.toPU Y.toPU))
    (Ft.srcG 𝓕 X Y ∘ pullbackProj' (Ft.toPullback.mGmap 𝓕 X.toPU Y.toPU)
      (Ft.toPullback.pBmap 𝓕 X.toPU Y.toPU))
    fun z => congrArg TransitionSet.src z.2

theorem isStrongBundleMap_srcG_pullbackProj' :
    (Ft.toPullback.pullBundle 𝓕 X.toPU Y.toPU).IsStrongBundleMap X.x.K.BW
      (X.toPU.x.Ψh.τ.obj ∘ Ft.srcH 𝓕 X Y)
      (Ft.srcG 𝓕 X Y ∘ pullbackProj' (Ft.toPullback.mGmap 𝓕 X.toPU Y.toPU)
        (Ft.toPullback.pBmap 𝓕 X.toPU Y.toPU)) :=
  (Ft.isStrongBundleMap_srcG 𝓕 X Y).comp
    ((Ft.toPullback.bundleG 𝓕 X.toPU Y.toPU).isStrongBundleMap_pullbackProj'
      (Ft.toPullback.isLocalScDiffeo_pBmap 𝓕 X.toPU Y.toPU).isScSmoothMap)

theorem isStrongBundleMap_TMap :
    (Ft.toPullback.pullBundle 𝓕 X.toPU Y.toPU).IsStrongBundleMap
      (X.toPU.x.bun.bundle.pullback X.toPU.x.Ψh.τ.isScSmoothMap_obj) (Ft.srcH 𝓕 X Y)
      (Ft.TMap 𝓕 X Y) :=
  X.toPU.x.bun.bundle.isStrongBundleMap_pullbackPair X.toPU.x.Ψh.τ.isScSmoothMap_obj
    (Ft.isLocalScDiffeo_srcH 𝓕 X Y).isScSmoothMap (Ft.isStrongBundleMap_srcG_pullbackProj' 𝓕 X Y)

/-- `(ê, w) ↦ (ê, w)` is near every point a strong bundle isomorphism covering `ŝ`: its
composition with the projection `τ*W → W` is `s ∘ π`, and the projections are local strong bundle
isomorphisms. -/
theorem isLocalStrongBundleIso_TMap (a : Ft.toPullback.MHatB 𝓕 X.toPU Y.toPU) :
    ∃ (U : Set (Ft.toPullback.MHatB 𝓕 X.toPU Y.toPU)) (U' : Set X.toPU.x.Ψh.ObjE), a ∈ U ∧
      (Ft.toPullback.pullBundle 𝓕 X.toPU Y.toPU).IsStrongBundleIsoOn
        (X.toPU.x.bun.bundle.pullback X.toPU.x.Ψh.τ.isScSmoothMap_obj)
        (Ft.isStrongBundleMap_TMap 𝓕 X Y) U U' := by
  obtain ⟨U₁, U₁', σ₁, ha, hd₁⟩ := Ft.toPullback.isLocalScDiffeo_pBmap 𝓕 X.toPU Y.toPU a
  have hπ₁ := (Ft.toPullback.bundleG 𝓕 X.toPU Y.toPU).isStrongBundleIsoOn_pullbackProj'
    (Ft.toPullback.isLocalScDiffeo_pBmap 𝓕 X.toPU Y.toPU).isScSmoothMap hd₁ a
  obtain ⟨U₂, U₂', hk, hs⟩ := Ft.isLocalStrongBundleIso_srcG 𝓕 X Y
    (Ft.toPullback.pBmap 𝓕 X.toPU Y.toPU a)
  obtain ⟨U₀, U₀'', ha₀, hc₀⟩ := hs.exists_comp hπ₁ ha hk
  obtain ⟨V, V', σ, hV, hd⟩ := X.toPU.x.Ψh.model.isLocalScDiffeo (Ft.srcH 𝓕 X Y a)
  have hπ := X.toPU.x.bun.bundle.isStrongBundleIsoOn_pullbackProj'
    X.toPU.x.Ψh.τ.isScSmoothMap_obj hd (Ft.srcH 𝓕 X Y a)
  obtain ⟨g, hg⟩ := hc₀.isScDiffeoOn_base
  have hW : IsOpen (U₀ ∩ Ft.srcH 𝓕 X Y ⁻¹' V) := hg.isOpen_source.inter
    (hd.isOpen_source.preimage (Ft.isLocalScDiffeo_srcH 𝓕 X Y).continuous)
  have hc := hc₀.restrict hg hW inter_subset_left
  have hc' : (Ft.toPullback.pullBundle 𝓕 X.toPU Y.toPU).IsStrongBundleIsoOn X.x.K.BW
      ((X.toPU.x.bun.bundle.isStrongBundleMap_pullbackProj' X.toPU.x.Ψh.τ.isScSmoothMap_obj).comp
        (Ft.isStrongBundleMap_TMap 𝓕 X Y))
      (U₀ ∩ Ft.srcH 𝓕 X Y ⁻¹' V) (U₀'' ∩ g ⁻¹' (U₀ ∩ Ft.srcH 𝓕 X Y ⁻¹' V)) := hc
  exact ⟨U₀ ∩ Ft.srcH 𝓕 X Y ⁻¹' V, _, ⟨ha₀, hV⟩,
    hc'.of_comp (h := Ft.isStrongBundleMap_TMap 𝓕 X Y) hπ fun _ hx => hx.2⟩

/-- **2021 (19.93): `S : p*M(Γ, Γ') → Ŵ`**,
`((ê, φ̂, ê'), (w, (P(φ̂), A(w)), w')) ↦ ŵ` with `Ξ(ŵ) = w`, `Q̂(ŵ) = ê`. -/
def SMap (z : Ft.toPullback.PB 𝓕 X.toPU Y.toPU) : X.x.K.Wh :=
  X.x.K.liftKinv (Ft.TMap 𝓕 X Y z)

theorem isStrongBundleMap_SMap :
    (Ft.toPullback.pullBundle 𝓕 X.toPU Y.toPU).IsStrongBundleMap X.x.K.BWh (Ft.srcH 𝓕 X Y)
      (Ft.SMap 𝓕 X Y) :=
  X.x.K.isStrongBundleIso_liftK.invMap.comp (Ft.isStrongBundleMap_TMap 𝓕 X Y)

/-- **`Ξ ∘ S = s ∘ π`** (p. 953). -/
theorem xi_SMap (z : Ft.toPullback.PB 𝓕 X.toPU Y.toPU) :
    X.x.K.Ξ (Ft.SMap 𝓕 X Y z) = Ft.srcG 𝓕 X Y (pullbackProj' (Ft.toPullback.mGmap 𝓕 X.toPU Y.toPU)
      (Ft.toPullback.pBmap 𝓕 X.toPU Y.toPU) z) :=
  X.x.K.Ξ_liftPt _ _ _

/-- **`Q̂ ∘ S = ŝ ∘ p*m`** (the diagram of Lemma 19.8.18). -/
theorem Qh_SMap (z : Ft.toPullback.PB 𝓕 X.toPU Y.toPU) :
    X.x.K.Qh (Ft.SMap 𝓕 X Y z) = Ft.srcH 𝓕 X Y (pullbackProj
      (Ft.toPullback.mGmap 𝓕 X.toPU Y.toPU) (Ft.toPullback.pBmap 𝓕 X.toPU Y.toPU) z) :=
  X.x.K.Qh_liftPt _ _ _

/-- **2021 Lemma 19.8.18, p. 953**: `S : p*M(Γ, Γ') → Ŵ` is a local strong bundle isomorphism
covering `ŝ : M(Ψ̂, Ψ̂') → Ê`, with `Q̂ ∘ S = ŝ ∘ p*m` and `Ξ ∘ S = s ∘ π`. -/
theorem lemma_19_8_18 :
    (∀ a, ∃ (U : Set (Ft.toPullback.MHatB 𝓕 X.toPU Y.toPU)) (U' : Set X.toPU.x.Ψh.ObjE), a ∈ U ∧
      (Ft.toPullback.pullBundle 𝓕 X.toPU Y.toPU).IsStrongBundleIsoOn X.x.K.BWh
        (Ft.isStrongBundleMap_SMap 𝓕 X Y) U U') ∧
      (∀ z, X.x.K.Qh (Ft.SMap 𝓕 X Y z) = Ft.srcH 𝓕 X Y (pullbackProj
        (Ft.toPullback.mGmap 𝓕 X.toPU Y.toPU) (Ft.toPullback.pBmap 𝓕 X.toPU Y.toPU) z)) ∧
      ∀ z, X.x.K.Ξ (Ft.SMap 𝓕 X Y z) = Ft.srcG 𝓕 X Y (pullbackProj'
        (Ft.toPullback.mGmap 𝓕 X.toPU Y.toPU) (Ft.toPullback.pBmap 𝓕 X.toPU Y.toPU) z) := by
  refine ⟨fun a => ?_, Ft.Qh_SMap 𝓕 X Y, Ft.xi_SMap 𝓕 X Y⟩
  obtain ⟨U, U', ha, hT⟩ := Ft.isLocalStrongBundleIso_TMap 𝓕 X Y a
  exact X.x.K.isStrongBundleIso_liftK.symm.isStrongBundleIsoOn_univ.exists_comp hT ha
    (mem_univ _)

/-- **The source map `s : M(Γ̂, Γ̂') → Ŵ`**, `(ŵ, (φ̂, Â(ŵ)), ŵ') ↦ ŵ`. -/
def srcSq (h : Ft.MSq 𝓕 X Y) : X.x.K.Wh := h.toTrans.src

/-- **`s = S ∘ U`** (p. 954). -/
theorem SMap_USq (h : Ft.MSq 𝓕 X Y) : Ft.SMap 𝓕 X Y (Ft.USq 𝓕 X Y h) = Ft.srcSq 𝓕 X Y h :=
  X.x.K.liftPt_eq _ rfl rfl

theorem isStrongBundleMap_srcSq :
    (Ft.bundleSq 𝓕 X Y).IsStrongBundleMap X.x.K.BWh (Ft.srcH 𝓕 X Y) (Ft.srcSq 𝓕 X Y) := by
  have h := (Ft.isStrongBundleMap_SMap 𝓕 X Y).comp (Ft.isStrongBundleIso_USq 𝓕 X Y).toMap
  have e : Ft.SMap 𝓕 X Y ∘ Ft.USq 𝓕 X Y = Ft.srcSq 𝓕 X Y := funext (Ft.SMap_USq 𝓕 X Y)
  rw [e] at h
  exact h

/-- **The source map `s : M(Γ̂, Γ̂') → Ŵ` is a local strong bundle isomorphism** for the
structure of Definition 19.8.17 (p. 954): `s = S ∘ U` with `U` a strong bundle isomorphism. -/
theorem isLocalStrongBundleIso_srcSq (a : Ft.toPullback.MHatB 𝓕 X.toPU Y.toPU) :
    ∃ (U : Set (Ft.toPullback.MHatB 𝓕 X.toPU Y.toPU)) (U' : Set X.x.Ψh.ObjE), a ∈ U ∧
      (Ft.bundleSq 𝓕 X Y).IsStrongBundleIsoOn X.x.K.BWh (Ft.isStrongBundleMap_srcSq 𝓕 X Y)
        U U' := by
  obtain ⟨U, U', ha, hS⟩ := (Ft.lemma_19_8_18 𝓕 X Y).1 a
  obtain ⟨U₀, U₀', ha₀, hc⟩ := hS.exists_comp
    (Ft.isStrongBundleIso_USq 𝓕 X Y).isStrongBundleIsoOn_univ (mem_univ a) ha
  have e : Ft.SMap 𝓕 X Y ∘ Ft.USq 𝓕 X Y = Ft.srcSq 𝓕 X Y := funext (Ft.SMap_USq 𝓕 X Y)
  exact ⟨U₀, U₀', ha₀, StrongBundle.isStrongBundleIsoOn_of_eqOn hc (fun _ _ => rfl)
    fun z _ => congrFun e z⟩


/-- **`p̂ : M(Γ̂, Γ̂') → M(Γ, Γ')` is a strong bundle map covering `p`** (diagram of
Theorem 19.8.22): `p̂ = π ∘ U`. -/
theorem isStrongBundleMap_pbarSq :
    (Ft.bundleSq 𝓕 X Y).IsStrongBundleMap (Ft.toPullback.bundleG 𝓕 X.toPU Y.toPU)
      (Ft.toPullback.pBmap 𝓕 X.toPU Y.toPU) (Ft.pbarSq 𝓕 X Y) :=
  ((Ft.toPullback.bundleG 𝓕 X.toPU Y.toPU).isStrongBundleMap_pullbackProj'
    (Ft.toPullback.isLocalScDiffeo_pBmap 𝓕 X.toPU Y.toPU).isScSmoothMap).comp
    (Ft.isStrongBundleIso_USq 𝓕 X Y).toMap

/-- **`p̂` is a local strong bundle isomorphism** (Theorem 19.8.22: "the horizontal arrows
constitute a local strong bundle isomorphism"). -/
theorem isLocalStrongBundleIso_pbarSq (a : Ft.toPullback.MHatB 𝓕 X.toPU Y.toPU) :
    ∃ (U₀ : Set (Ft.toPullback.MHatB 𝓕 X.toPU Y.toPU))
      (U₀' : Set (Ft.toPullback.MBase 𝓕 X.toPU Y.toPU)), a ∈ U₀ ∧
      (Ft.bundleSq 𝓕 X Y).IsStrongBundleIsoOn (Ft.toPullback.bundleG 𝓕 X.toPU Y.toPU)
        (Ft.isStrongBundleMap_pbarSq 𝓕 X Y) U₀ U₀' := by
  obtain ⟨U, V, σ, ha, hd⟩ := Ft.toPullback.isLocalScDiffeo_pBmap 𝓕 X.toPU Y.toPU a
  have hi' := (Ft.toPullback.bundleG 𝓕 X.toPU Y.toPU).isStrongBundleIsoOn_pullbackProj'
    (Ft.toPullback.isLocalScDiffeo_pBmap 𝓕 X.toPU Y.toPU).isScSmoothMap hd a
  exact hi'.exists_comp (Ft.isStrongBundleIso_USq 𝓕 X Y).isStrongBundleIsoOn_univ (mem_univ a) ha

/-- **`p̂` is surjective.** -/
theorem surjective_pbarSq : Surjective (Ft.pbarSq 𝓕 X Y) := fun g => by
  obtain ⟨a, ha⟩ := Ft.toPullback.surjective_pBmap 𝓕 X.toPU Y.toPU
    (Ft.toPullback.mGmap 𝓕 X.toPU Y.toPU g)
  exact ⟨Ft.USqInv 𝓕 X Y ⟨(a, g), ha.symm⟩,
    congrArg (fun z : Ft.toPullback.PB 𝓕 X.toPU Y.toPU =>
      (z : Ft.toPullback.MHatB 𝓕 X.toPU Y.toPU × Ft.toPullback.MG 𝓕 X.toPU Y.toPU).2)
      (Ft.USq_USqInv 𝓕 X Y ⟨(a, g), ha.symm⟩)⟩

end SquareUniformizerConstruction

end GroupoidalCategory

end

end Polyfold
