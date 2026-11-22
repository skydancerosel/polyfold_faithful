import Polyfold.Chapter19.Metrizability
import Polyfold.Chapter9.DescentPolyfold
import Polyfold.Chapter8.TangentFibred
import Polyfold.Chapter17.PolyfoldConstructionExamples

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part IV, Chapter 19,
§19.5 "The Polyfold Structure for `(S, T)`" (pp. 886–888): **Theorem 19.5.1** (the natural
M-polyfold structure on `M(Ψ, Ψ')`, for which `s` and `t` are local sc-diffeomorphisms) and
**Corollary 19.5.2** (`u`, `ι`, `m` are sc-smooth).  Numbers and pages are the 2021 text's.
(Theorem 19.5.3 and the regularity conditions 19.5.5–19.5.11 are in `PolyfoldStructureGCT`.)

# The M-polyfold structure of the transition sets

## The text, paraphrased

(p. 886) Assume `T` is metrizable; then every `M(Ψ, Ψ')` is metrizable (Corollary 19.4.8), `s`, `t`
are local homeomorphisms and the other structure maps are continuous.  (Theorem 19.5.1)
`M(Ψ, Ψ')` carries a natural M-polyfold structure for which `s` and `t` are local
sc-diffeomorphisms.  *Proof* (text): for `M(Ψ, Ψ)` the homeomorphism
`Ψ̄ : G × O → M(Ψ, Ψ)`, `(g, o) ↦ (o, Ψ(g, o), g ∗ o)`, transports the structure of `G × O`; the
local inverses `s_h` of `F_h` form an atlas with transition maps `s_{h'} ∘ s_h⁻¹ = id`, and
`s_h ∘ Ψ̄(g, q) = q`, so both structures agree.  In general pick, for `h ∈ M(Ψ, Ψ')`, open
`U(h)`, `U(o)` with `s : U(h) → U(o)` a homeomorphism `s_h` with inverse `F_h`, and
`t(F_h(q)) = f_h(q)`; the overlaps are `s_{h'} ∘ s_h⁻¹(q) = q`, so `(s_h)` is an sc-smooth atlas,
`s` is a local sc-diffeomorphism by construction, and `t ∘ s_h⁻¹ = f_h` shows the same for `t`.
`F_h : V(o) → F_h(V(o))` is an sc-diffeomorphism.  (Corollary 19.5.2) The unit `u`, the inversion
`ι` and the multiplication `m` are sc-smooth: `s ∘ u = id`; `t(ι(F_h(q))) = t(F_{h'}(f_h(q)))`;
`m(F_{h'}(f_h(q)), F_h(q)) = F_{m(h', h)}(q)`, the inverse of a local chart of the fibred
product.

## What is formalized (namespace `Polyfold.GroupoidalCategory`)

For transition data `F` (namespace `UniformizerConstruction.TransitionData`):

* The instances `T2Space`, `MetrizableSpace`, `ParacompactSpace` on `F.Tr Ψ Ψ'` (Proposition
  19.3.4 (3) and `TransitionData.metrizableSpace`).
* `SheetSpace F Ψ Ψ' = Σ h, V(o_h)` (the disjoint union of the domains of the `F_h`, with the
  M-polyfold structure `sheetPolyfold` of the open subsets of `O`) and the map
  `sheetMap : (h, q) ↦ F_h(q)`; `isDescentMap_sheetMap` (the hypotheses of Chapter 9's descent:
  continuous, open, onto, locally injective, and `F_{h₁}(q) = F_{h₂}(q)` forces `F_{h₁} = F_{h₂}`
  near `q`, by (B)).  The charts of the descended structure are the text's charts `φ ∘ s_h`.
* **`transPolyfold F Ψ Ψ'`**, the M-polyfold structure of `M(Ψ, Ψ')`;
  `isLocalScDiffeo_sheetMap`, `isScDiffeoOn_map` (`F_h : V(o) → F_h(V(o))` is an
  sc-diffeomorphism with inverse `s`), `isLocalScDiffeo_src`, `isLocalScDiffeo_tgt`
  (**Theorem 19.5.1**).
* Naturality: `isScDiffeoOn_id_of_isLocalScDiffeo_src` (**the structure is the only M-polyfold
  structure on the topological space `M(Ψ, Ψ')` for which `s` is a local sc-diffeomorphism**),
  `isScDiffeoOn_of_equiv` (equivalent transition data, i.e. two representatives of `𝓕`, give the
  same structure: the identity is an sc-diffeomorphism), `isScDiffeoOn_hatHomeomorph` (the
  text's description of `M(Ψ, Ψ)`: `Ψ̄ : G × O → M(Ψ, Ψ)` is an sc-diffeomorphism).
* **Corollary 19.5.2**: `isScSmoothMap_unit`, `isScSmoothMap_inv`, `isScSmoothMap_mul` (in
  Chapter 17's form `MPolyfold.IsScSmoothOnFibredProduct`, Definition 17.1.8 (c)).
* Tameness: `isTame_transPolyfold` (`M(Ψ, Ψ')` is tame if `O` is).
* General lemmas: `MPolyfold.IsLocalScDiffeo.of_comp_surjective` (`s` is a local
  sc-diffeomorphism if `s ∘ p` is, for a surjective local sc-diffeomorphism `p`) and
  `MPolyfold.isScSmoothMap_of_isLocalScDiffeo_comp` (`u` is sc-smooth if `s ∘ u` is, for a local
  sc-diffeomorphism `s` and a continuous `u`): the text's "since `s` is a local
  sc-diffeomorphism we conclude".

For a basic construction `B` (namespace `BasicConstruction`): `B.transPolyfold Ψ Ψ'` on
`B.M Ψ Ψ'`, **`theorem_19_5_1`** (as printed, with `T` metrizable), `theorem_19_5_1_natural`
(the structure does not depend on the representative of `𝓕`), **`corollary_19_5_2`**.

## Readings

* Theorem 19.5.1 assumes `T` metrizable to know that `M(Ψ, Ψ')` is metrizable (Corollary
  19.4.8).  `M(Ψ, Ψ')` is metrizable for every basic construction (`metrizableSpace_M`,
  `Metrizability.lean`), so the M-polyfold structure and all statements hold without this
  hypothesis; `theorem_19_5_1` keeps it as printed (it is not used).
* "Natural M-polyfold structure": we prove that it is the unique structure (up to the identity
  being an sc-diffeomorphism) for which `s` is a local sc-diffeomorphism, that it does not depend
  on the representative `F` of `𝓕`, and that on `M(Ψ, Ψ)` it is the structure transported by
  `Ψ̄` from `G × O` (Chapter 7's `actionMorPolyfold`).
* The text's atlas `(s_h)` is the descended atlas of Chapter 9 (`MPolyfold.descend`) along
  `Σ_h V(o_h) → M(Ψ, Ψ')`; its transition maps are the identity in the coordinates of `O`, which
  is the text's computation `s_{h'} ∘ s_h⁻¹(q) = q`.
-/

set_option maxSynthPendingDepth 3

open Set Function Topology TopologicalSpace

noncomputable section

namespace Polyfold

universe u v w

/-! ### Two general lemmas on local sc-diffeomorphisms -/

namespace MPolyfold

variable {A : Type u} [TopologicalSpace A] [T2Space A] [ParacompactSpace A] {PA : MPolyfold A}
  {Z : Type v} [TopologicalSpace Z] [T2Space Z] [ParacompactSpace Z] {PZ : MPolyfold Z}
  {Y : Type w} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {PY : MPolyfold Y}

/-- **A map `s` is a local sc-diffeomorphism if `s ∘ p` is**, for a surjective local
sc-diffeomorphism `p`: near `z = p(a)`, `s = (s ∘ p) ∘ (p|U)⁻¹`. -/
theorem IsLocalScDiffeo.of_comp_surjective {p : A → Z} {s : Z → Y}
    (hp : PA.IsLocalScDiffeo PZ p) (hsurj : Surjective p) (hsp : PA.IsLocalScDiffeo PY (s ∘ p)) :
    PZ.IsLocalScDiffeo PY s := by
  intro z
  obtain ⟨a, rfl⟩ := hsurj z
  obtain ⟨U₁, V₁, g₁, ha₁, hd₁⟩ := hp a
  obtain ⟨U₂, V₂, g₂, ha₂, hd₂⟩ := hsp a
  have hU : IsOpen (U₁ ∩ U₂) := hd₁.isOpen_source.inter hd₂.isOpen_source
  have e₁ := hd₁.restrict hU inter_subset_left
  have e₂ := hd₂.restrict hU inter_subset_right
  have e := e₂.comp e₁.symm
  refine ⟨V₁ ∩ g₁ ⁻¹' (U₁ ∩ U₂), _, p ∘ g₂, ⟨hd₁.mapsTo ha₁, ?_⟩, e.congr_left fun y hy => ?_⟩
  · rw [mem_preimage, hd₁.left_inv a ha₁]; exact ⟨ha₁, ha₂⟩
  · change s (p (g₁ y)) = s y
    rw [hd₁.right_inv y hy.1]

/-- **A continuous `u` with `s ∘ u` sc-smooth is sc-smooth**, for a local sc-diffeomorphism `s`:
near `x`, `u = (s|U)⁻¹ ∘ (s ∘ u)` with `U` a sheet of `s` around `u(x)`. -/
theorem isScSmoothMap_of_isLocalScDiffeo_comp {s : Z → Y} {f : A → Z}
    (hs : PZ.IsLocalScDiffeo PY s) (hf : Continuous f) (hsf : PA.IsScSmoothMap PY (s ∘ f)) :
    PA.IsScSmoothMap PZ f := by
  refine IsScSmoothOn.of_locally isOpen_univ fun x _ => ?_
  obtain ⟨W, V, g, hxW, hd⟩ := hs (f x)
  have hWo : IsOpen (f ⁻¹' W) := hd.isOpen_source.preimage hf
  refine ⟨f ⁻¹' W, hWo, hxW, subset_univ _, ?_⟩
  refine (IsScSmoothOn.comp hd.isScSmoothOn_inv (hsf.mono hWo (subset_univ _))
    fun y hy => hd.mapsTo hy).congr fun y hy => ?_
  exact hd.left_inv (f y) hy

end MPolyfold

namespace GroupoidalCategory

variable {C : GroupoidalCategory.{u}}

namespace UniformizerConstruction

namespace TransitionData

open GroupoidStr (TransitionSet)

variable {U : C.UniformizerConstruction} (F : U.TransitionData)

/-! ### Instances on `M(Ψ, Ψ')` -/

instance instT2SpaceTr (Ψ Ψ' : U.Unif) : T2Space (F.Tr Ψ Ψ') := F.t2Space Ψ Ψ'

instance instMetrizableSpaceTr (Ψ Ψ' : U.Unif) : MetrizableSpace (F.Tr Ψ Ψ') :=
  F.metrizableSpace Ψ Ψ'

instance instParacompactSpaceTr (Ψ Ψ' : U.Unif) : ParacompactSpace (F.Tr Ψ Ψ') :=
  paracompactSpace_of_metrizableSpace _

instance instNonemptyDom (Ψ Ψ' : U.Unif) (h : Ψ.1.Trans Ψ'.1) : Nonempty (F.dom Ψ Ψ' h) :=
  ⟨⟨h.src, F.mem_dom Ψ Ψ' h⟩⟩

instance instParacompactSpaceDom (Ψ Ψ' : U.Unif) (h : Ψ.1.Trans Ψ'.1) :
    ParacompactSpace (F.dom Ψ Ψ' h) :=
  Ψ.1.P.paracompactSpace_subtype _

variable (Ψ Ψ' : U.Unif)

/-! ### The disjoint union of the domains `V(o_h)` -/

/-- **The disjoint union `Σ_h V(o_h)` of the domains of the maps `F_h`**, `h ∈ M(Ψ, Ψ')`. -/
abbrev SheetSpace : Type u := Σ h : Ψ.1.Trans Ψ'.1, F.dom Ψ Ψ' h

/-- The M-polyfold structure of `Σ_h V(o_h)`: each `V(o_h)` is an open subset of `O`. -/
def sheetPolyfold : MPolyfold (F.SheetSpace Ψ Ψ') :=
  MPolyfold.sigma fun h => Ψ.1.P.restrictOpen (F.isOpen_dom Ψ Ψ' h)

/-- **The map `Σ_h V(o_h) → M(Ψ, Ψ')`, `(h, q) ↦ F_h(q)`.** -/
def sheetMap (x : F.SheetSpace Ψ Ψ') : F.Tr Ψ Ψ' := F.toTr (F.map Ψ Ψ' x.1 x.2.1)

theorem sheetMap_mk (h : Ψ.1.Trans Ψ'.1) (q : F.dom Ψ Ψ' h) :
    F.sheetMap Ψ Ψ' ⟨h, q⟩ = F.toTr (F.map Ψ Ψ' h q.1) := rfl

theorem src_sheetMap (x : F.SheetSpace Ψ Ψ') :
    (F.sheetMap Ψ Ψ' x : Ψ.1.Trans Ψ'.1).src = x.2.1 :=
  F.src_map Ψ Ψ' x.1 x.2.1 x.2.2

theorem continuous_sheetMap : Continuous (F.sheetMap Ψ Ψ') := by
  refine continuous_sigma fun h => ?_
  exact (F.continuousOn_map Ψ Ψ' h).comp_continuous continuous_subtype_val fun q => q.2

theorem isOpenMap_sheetMap : IsOpenMap (F.sheetMap Ψ Ψ') := by
  refine isOpenMap_sigma.2 fun h W hW => ?_
  have hW' : IsOpen (Subtype.val '' W : Set Ψ.1.O) :=
    (F.isOpen_dom Ψ Ψ' h).isOpenMap_subtype_val W hW
  have heq : (fun q : F.dom Ψ Ψ' h => F.sheetMap Ψ Ψ' ⟨h, q⟩) '' W =
      F.map Ψ Ψ' h '' (Subtype.val '' W) := by
    rw [image_image]; rfl
  rw [heq]
  exact F.isOpen_image_map Ψ Ψ' h hW' (Subtype.coe_image_subset _ _)

theorem surjective_sheetMap : Surjective (F.sheetMap Ψ Ψ') := fun a =>
  ⟨⟨a, ⟨a.src, F.mem_dom Ψ Ψ' a⟩⟩, F.map_src Ψ Ψ' a⟩

/-- `F_h` is injective on `V(o)` (`s ∘ F_h = id`). -/
theorem injOn_sheetMap (h : Ψ.1.Trans Ψ'.1) :
    InjOn (F.sheetMap Ψ Ψ') (range (Sigma.mk h)) := by
  rintro _ ⟨q, rfl⟩ _ ⟨q', rfl⟩ he
  have h1 := congrArg (fun a : F.Tr Ψ Ψ' => (a : Ψ.1.Trans Ψ'.1).src) he
  simp only [src_sheetMap] at h1
  rw [Subtype.ext h1]

/-- **The descent hypotheses** (Chapter 9) for `(h, q) ↦ F_h(q)`; the transition condition is
Stability (B): `F_{h₁}(q) = F_{h₂}(q) = k` gives `F_{h₁} = F_k = F_{h₂}` near `q`. -/
theorem isDescentMap_sheetMap : (F.sheetPolyfold Ψ Ψ').IsDescentMap (F.sheetMap Ψ Ψ') := by
  refine ⟨F.continuous_sheetMap Ψ Ψ', F.isOpenMap_sheetMap Ψ Ψ', F.surjective_sheetMap Ψ Ψ',
    fun x => ⟨range (Sigma.mk x.1), isOpen_range_sigmaMk, ⟨x.2, rfl⟩, F.injOn_sheetMap Ψ Ψ' x.1⟩,
    ?_⟩
  rintro ⟨h₁, q₁⟩ ⟨h₂, q₂⟩ hab
  have hq : q₁.1 = q₂.1 := by
    have := congrArg (fun a : F.Tr Ψ Ψ' => (a : Ψ.1.Trans Ψ'.1).src) hab
    simpa only [src_sheetMap] using this
  set k := F.map Ψ Ψ' h₁ q₁.1 with hk
  have hk₂ : F.map Ψ Ψ' h₂ q₂.1 = k := hab.symm
  have hkd : q₁.1 ∈ F.dom Ψ Ψ' k := by
    have := F.mem_dom Ψ Ψ' k
    rwa [hk, F.src_map Ψ Ψ' h₁ q₁.1 q₁.2] at this
  -- the open piece `N = {(h₁, y) | y ∈ V(k) ∩ V(h₂)}` and the map `(h₁, y) ↦ (h₂, y)`
  set W : Set (F.dom Ψ Ψ' h₁) := Subtype.val ⁻¹' (F.dom Ψ Ψ' k ∩ F.dom Ψ Ψ' h₂) with hW
  have hWo : IsOpen W :=
    ((F.isOpen_dom Ψ Ψ' k).inter (F.isOpen_dom Ψ Ψ' h₂)).preimage continuous_subtype_val
  classical
  let f : F.SheetSpace Ψ Ψ' → F.SheetSpace Ψ Ψ' := fun x =>
    if hx : x.2.1 ∈ F.dom Ψ Ψ' h₂ then ⟨h₂, ⟨x.2.1, hx⟩⟩ else x
  refine ⟨Sigma.mk h₁ '' W, f, isOpenMap_sigmaMk _ hWo, ⟨q₁, ⟨hkd, hq ▸ q₂.2⟩, rfl⟩, ?_, ?_, ?_⟩
  · rw [sheetPolyfold, MPolyfold.isScSmoothOn_sigma_iff
      (X := fun h : Ψ.1.Trans Ψ'.1 => ↥(F.dom Ψ Ψ' h)) _ (isOpenMap_sigmaMk _ hWo)]
    intro i
    by_cases hi : i = h₁
    · subst hi
      rw [preimage_image_eq _ sigma_mk_injective]
      have hg : (Ψ.1.P.restrictOpen (F.isOpen_dom Ψ Ψ' i)).IsScSmoothOn
          (Ψ.1.P.restrictOpen (F.isOpen_dom Ψ Ψ' h₂))
          (fun y : F.dom Ψ Ψ' i => MPolyfold.openRetraction (F.dom Ψ Ψ' h₂) y.1) W :=
        (MPolyfold.isScSmoothOn_openRetraction (F.isOpen_dom Ψ Ψ' h₂)).comp
          ((MPolyfold.isScSmoothMap_subtypeVal (F.isOpen_dom Ψ Ψ' i)).mono hWo (subset_univ _))
          fun y hy => hy.2
      refine ((MPolyfold.isScSmoothOn_sigmaMk_comp_iff
        (X := fun h : Ψ.1.Trans Ψ'.1 => ↥(F.dom Ψ Ψ' h))
        (fun h => Ψ.1.P.restrictOpen (F.isOpen_dom Ψ Ψ' h))).2 hg).congr fun y hy => ?_
      change (⟨h₂, MPolyfold.openRetraction (F.dom Ψ Ψ' h₂) y.1⟩ : F.SheetSpace Ψ Ψ') =
        f ⟨i, y⟩
      simp only [f, dif_pos hy.2, MPolyfold.openRetraction_of_mem hy.2]
    · have : Sigma.mk i ⁻¹' (Sigma.mk h₁ '' W : Set (F.SheetSpace Ψ Ψ')) = ∅ := by
        ext y
        simp only [mem_preimage, mem_image, mem_empty_iff_false, iff_false, not_exists, not_and]
        intro z _ he
        exact hi (congrArg Sigma.fst he).symm
      rw [this]
      exact MPolyfold.isScSmoothOn_empty _
  · have hq₂ : q₁.1 ∈ F.dom Ψ Ψ' h₂ := hq ▸ q₂.2
    simp only [f, dif_pos hq₂]
    congr 1
    exact Subtype.ext hq
  · rintro _ ⟨y, hy, rfl⟩
    have hy₂ : y.1 ∈ F.dom Ψ Ψ' h₂ := hy.2
    simp only [f, dif_pos hy₂]
    change F.toTr (F.map Ψ Ψ' h₂ y.1) = F.toTr (F.map Ψ Ψ' h₁ y.1)
    have e₁ := F.stability Ψ Ψ' h₁ q₁.1 q₁.2 y.1 ⟨hy.1, y.2⟩
    have hkd₂ : y.1 ∈ F.dom Ψ Ψ' (F.map Ψ Ψ' h₂ q₂.1) := by rw [hk₂]; exact hy.1
    have e₂ := F.stability Ψ Ψ' h₂ q₂.1 q₂.2 y.1 ⟨hkd₂, hy₂⟩
    rw [← e₁, ← e₂, hk₂]

/-! ### Theorem 19.5.1: the M-polyfold structure of `M(Ψ, Ψ')` -/

/-- **2021 Theorem 19.5.1, p. 886: the natural M-polyfold structure of `M(Ψ, Ψ')`**, descended
from `Σ_h V(o_h)` along `(h, q) ↦ F_h(q)` (the atlas of the charts `s_h`). -/
def transPolyfold : MPolyfold (F.Tr Ψ Ψ') := MPolyfold.descend (F.isDescentMap_sheetMap Ψ Ψ')

/-- `(h, q) ↦ F_h(q)` is a local sc-diffeomorphism. -/
theorem isLocalScDiffeo_sheetMap :
    (F.sheetPolyfold Ψ Ψ').IsLocalScDiffeo (F.transPolyfold Ψ Ψ') (F.sheetMap Ψ Ψ') :=
  MPolyfold.isLocalScDiffeo_descend _

/-- `(h, q) ↦ q` is a local sc-diffeomorphism `Σ_h V(o_h) → O`. -/
theorem isLocalScDiffeo_sheetSrc :
    (F.sheetPolyfold Ψ Ψ').IsLocalScDiffeo Ψ.1.P fun x : F.SheetSpace Ψ Ψ' => x.2.1 :=
  (MPolyfold.isLocalScDiffeo_sigma_iff (X := fun h : Ψ.1.Trans Ψ'.1 => ↥(F.dom Ψ Ψ' h)) _).2
    fun h =>
    MPolyfold.isLocalScDiffeo_subtypeVal (F.isOpen_dom Ψ Ψ' h)

/-- `(h, q) ↦ f_h(q)` is a local sc-diffeomorphism `Σ_h V(o_h) → O'` ((A)). -/
theorem isLocalScDiffeo_sheetTgt :
    (F.sheetPolyfold Ψ Ψ').IsLocalScDiffeo Ψ'.1.P
      fun x : F.SheetSpace Ψ Ψ' => F.fmap Ψ Ψ' x.1 x.2.1 := by
  refine (MPolyfold.isLocalScDiffeo_sigma_iff
    (X := fun h : Ψ.1.Trans Ψ'.1 => ↥(F.dom Ψ Ψ' h)) _).2 fun h y => ?_
  obtain ⟨g, hg⟩ := F.diffeo Ψ Ψ' h
  exact ⟨univ, _, _, mem_univ y,
    hg.comp (MPolyfold.isScDiffeoOn_subtypeVal (F.isOpen_dom Ψ Ψ' h))⟩

/-- **2021 Theorem 19.5.1, p. 886: `s : M(Ψ, Ψ') → O` is a local sc-diffeomorphism.** -/
theorem isLocalScDiffeo_src :
    (F.transPolyfold Ψ Ψ').IsLocalScDiffeo Ψ.1.P fun a : F.Tr Ψ Ψ' => (a : Ψ.1.Trans Ψ'.1).src :=
  (F.isLocalScDiffeo_sheetMap Ψ Ψ').of_comp_surjective (F.surjective_sheetMap Ψ Ψ') <| by
    have : (fun a : F.Tr Ψ Ψ' => (a : Ψ.1.Trans Ψ'.1).src) ∘ F.sheetMap Ψ Ψ' =
        fun x : F.SheetSpace Ψ Ψ' => x.2.1 := funext (F.src_sheetMap Ψ Ψ')
    rw [this]; exact F.isLocalScDiffeo_sheetSrc Ψ Ψ'


/-- **2021 Theorem 19.5.1, p. 886: `t : M(Ψ, Ψ') → O'` is a local sc-diffeomorphism**
(`t ∘ F_h = f_h`). -/
theorem isLocalScDiffeo_tgt :
    (F.transPolyfold Ψ Ψ').IsLocalScDiffeo Ψ'.1.P fun a : F.Tr Ψ Ψ' => (a : Ψ.1.Trans Ψ'.1).tgt :=
  (F.isLocalScDiffeo_sheetMap Ψ Ψ').of_comp_surjective (F.surjective_sheetMap Ψ Ψ')
    (F.isLocalScDiffeo_sheetTgt Ψ Ψ')

/-- **2021 Theorem 19.5.1, p. 886 (proof): `F_h : V(o) → F_h(V(o))` is an sc-diffeomorphism**,
with inverse `s`; its inverse `s_h` is the text's chart at `h`. -/
theorem isScDiffeoOn_map (h : Ψ.1.Trans Ψ'.1) :
    Ψ.1.P.IsScDiffeoOn (F.transPolyfold Ψ Ψ') (fun q => F.toTr (F.map Ψ Ψ' h q))
      (fun a : F.Tr Ψ Ψ' => (a : Ψ.1.Trans Ψ'.1).src) (F.dom Ψ Ψ' h)
      (F.map Ψ Ψ' h '' F.dom Ψ Ψ' h) := by
  have hV := F.isOpen_dom Ψ Ψ' h
  have hsm : (F.sheetPolyfold Ψ Ψ').IsScSmoothMap (F.transPolyfold Ψ Ψ') (F.sheetMap Ψ Ψ') :=
    (F.isLocalScDiffeo_sheetMap Ψ Ψ').isScSmoothMap
  have hin : Ψ.1.P.IsScSmoothOn (F.sheetPolyfold Ψ Ψ')
      (fun q => (⟨h, MPolyfold.openRetraction (F.dom Ψ Ψ' h) q⟩ : F.SheetSpace Ψ Ψ'))
      (F.dom Ψ Ψ' h) :=
    (MPolyfold.isScSmoothOn_sigmaMk_comp_iff (X := fun h : Ψ.1.Trans Ψ'.1 => ↥(F.dom Ψ Ψ' h))
      (fun h => Ψ.1.P.restrictOpen (F.isOpen_dom Ψ Ψ' h))).2
      (MPolyfold.isScSmoothOn_openRetraction hV)
  refine ⟨(MPolyfold.IsScSmoothOn.comp hsm hin (mapsTo_univ _ _)).congr fun q hq => ?_,
    (F.isLocalScDiffeo_src Ψ Ψ').isScSmoothMap.mono
      (F.isOpen_image_map Ψ Ψ' h hV subset_rfl) (subset_univ _),
    fun q hq => mem_image_of_mem _ hq, ?_, fun q hq => F.src_map Ψ Ψ' h q hq, ?_⟩
  · change F.sheetMap Ψ Ψ' ⟨h, MPolyfold.openRetraction (F.dom Ψ Ψ' h) q⟩ = _
    rw [MPolyfold.openRetraction_of_mem hq]; rfl
  · rintro _ ⟨q, hq, rfl⟩
    change (F.map Ψ Ψ' h q).src ∈ _
    rw [F.src_map Ψ Ψ' h q hq]; exact hq
  · rintro _ ⟨q, hq, rfl⟩
    change F.toTr (F.map Ψ Ψ' h (F.map Ψ Ψ' h q).src) = F.toTr (F.map Ψ Ψ' h q)
    rw [F.src_map Ψ Ψ' h q hq]

/-! ### Naturality of the structure -/

/-- **The structure is characterized by `s`**: if `Θ : Z ≃ M(Ψ, Ψ')` is a homeomorphism from an
M-polyfold `Z` with `s ∘ Θ` a local sc-diffeomorphism, then `Θ` is an sc-diffeomorphism. -/
theorem isScDiffeoOn_of_isLocalScDiffeo_src_comp {Z : Type v} [TopologicalSpace Z] [T2Space Z]
    [ParacompactSpace Z] {Q : MPolyfold Z} (Θ : Z ≃ₜ F.Tr Ψ Ψ')
    (hs : Q.IsLocalScDiffeo Ψ.1.P fun z => (Θ z : Ψ.1.Trans Ψ'.1).src) :
    Q.IsScDiffeoOn (F.transPolyfold Ψ Ψ') Θ Θ.symm univ univ :=
  (MPolyfold.isLocalScDiffeo_of_comp_eq hs (F.isLocalScDiffeo_src Ψ Ψ') Θ.continuous
    fun _ => rfl).isScDiffeoOn_of_bijective Θ.toEquiv fun _ => rfl

/-- **Uniqueness ("natural")**: every M-polyfold structure `Q` on the topological space
`M(Ψ, Ψ')` for which `s` is a local sc-diffeomorphism agrees with `transPolyfold`: the identity
is an sc-diffeomorphism. -/
theorem isScDiffeoOn_id_of_isLocalScDiffeo_src (Q : MPolyfold (F.Tr Ψ Ψ'))
    (hs : Q.IsLocalScDiffeo Ψ.1.P fun a : F.Tr Ψ Ψ' => (a : Ψ.1.Trans Ψ'.1).src) :
    Q.IsScDiffeoOn (F.transPolyfold Ψ Ψ') id id univ univ :=
  F.isScDiffeoOn_of_isLocalScDiffeo_src_comp Ψ Ψ' (Homeomorph.refl _) hs

/-- The identity `M(Ψ, Ψ') → M(Ψ, Ψ')` from `T^{F₁}` to `T^{F₂}` for equivalent transition data
(Lemma 19.3.1). -/
def equivHomeomorph {F₁ F₂ : U.TransitionData} (e : F₁.Equiv F₂) (Ψ Ψ' : U.Unif) :
    F₁.Tr Ψ Ψ' ≃ₜ F₂.Tr Ψ Ψ' where
  toFun a := a
  invFun a := a
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := continuous_def.2 fun W hW => by
    have : F₂.IsOpenTr Ψ Ψ' W := F₂.isOpen_tr_iff.1 hW
    rw [← lemma_19_3_1 e] at this
    exact F₁.isOpen_tr_iff.2 this
  continuous_invFun := continuous_def.2 fun W hW => by
    have : F₁.IsOpenTr Ψ Ψ' W := F₁.isOpen_tr_iff.1 hW
    rw [lemma_19_3_1 e] at this
    exact F₂.isOpen_tr_iff.2 this

/-- **Independence of the representative**: equivalent transition data (two representatives of
`𝓕`) give the same M-polyfold structure on `M(Ψ, Ψ')`. -/
theorem isScDiffeoOn_of_equiv {F₁ F₂ : U.TransitionData} (e : F₁.Equiv F₂) (Ψ Ψ' : U.Unif) :
    (F₁.transPolyfold Ψ Ψ').IsScDiffeoOn (F₂.transPolyfold Ψ Ψ') (equivHomeomorph e Ψ Ψ')
      (equivHomeomorph e Ψ Ψ').symm univ univ :=
  F₂.isScDiffeoOn_of_isLocalScDiffeo_src_comp Ψ Ψ' (equivHomeomorph e Ψ Ψ')
    (F₁.isLocalScDiffeo_src Ψ Ψ')

/-- **2021 Theorem 19.5.1, p. 886 (proof): `Ψ̄ : G × O → M(Ψ, Ψ)`,
`(g, o) ↦ (o, Ψ(g, o), g ∗ o)`, is an sc-diffeomorphism** (`G × O` with the M-polyfold structure
of the translation groupoid `G ⋉ O`, `s ∘ Ψ̄ = pr₂`). -/
theorem isScDiffeoOn_hatHomeomorph (Ψ : U.Unif) :
    Ψ.1.ep.PMor.IsScDiffeoOn (F.transPolyfold Ψ Ψ) (F.hatHomeomorph Ψ) (F.hatHomeomorph Ψ).symm
      univ univ :=
  F.isScDiffeoOn_of_isLocalScDiffeo_src_comp Ψ Ψ (F.hatHomeomorph Ψ) Ψ.1.ep.isLocalScDiffeo_src

/-- `M(Ψ, Ψ')` is tame if `O` is (`s` is a local sc-diffeomorphism). -/
theorem isTame_transPolyfold (hO : Ψ.1.P.IsTame) : (F.transPolyfold Ψ Ψ').IsTame :=
  (F.isLocalScDiffeo_src Ψ Ψ').isTame hO

/-! ### Corollary 19.5.2: `u`, `ι`, `m` are sc-smooth -/

/-- **2021 Corollary 19.5.2, p. 887: the unit map `u : O → M(Ψ, Ψ)` is sc-smooth**
(`s ∘ u = id`). -/
theorem isScSmoothMap_unit (Ψ : U.Unif) :
    Ψ.1.P.IsScSmoothMap (F.transPolyfold Ψ Ψ)
      fun o => F.toTr (TransitionSet.unit o : Ψ.1.Trans Ψ.1) :=
  MPolyfold.isScSmoothMap_of_isLocalScDiffeo_comp (F.isLocalScDiffeo_src Ψ Ψ)
    (F.continuous_unit Ψ) (MPolyfold.isScSmoothMap_id (P := Ψ.1.P))

/-- **2021 Corollary 19.5.2, p. 887: the inversion `ι : M(Ψ, Ψ') → M(Ψ', Ψ)` is sc-smooth**
(`s ∘ ι = t`). -/
theorem isScSmoothMap_inv :
    (F.transPolyfold Ψ Ψ').IsScSmoothMap (F.transPolyfold Ψ' Ψ)
      fun a : F.Tr Ψ Ψ' => F.toTr (a : Ψ.1.Trans Ψ'.1).inv :=
  MPolyfold.isScSmoothMap_of_isLocalScDiffeo_comp (F.isLocalScDiffeo_src Ψ' Ψ)
    (F.continuous_inv Ψ Ψ') (F.isLocalScDiffeo_tgt Ψ Ψ').isScSmoothMap

/-- **2021 Corollary 19.5.2, p. 887: the multiplication
`m : M(Ψ', Ψ'') ₛ×ₜ M(Ψ, Ψ') → M(Ψ, Ψ'')` is sc-smooth** on the sub-M-polyfold fibred product
(Chapter 17's form, Definition 17.1.8 (c); `s ∘ m = s ∘ pr₂`). -/
theorem isScSmoothMap_mul (Ψ Ψ' Ψ'' : U.Unif) :
    MPolyfold.IsScSmoothOnFibredProduct (F.transPolyfold Ψ' Ψ'') (F.transPolyfold Ψ Ψ')
      (F.transPolyfold Ψ Ψ'') (F.isLocalScDiffeo_src Ψ' Ψ'')
      (F.isLocalScDiffeo_tgt Ψ Ψ').isScSmoothMap
      fun p => (F.toTr (GroupoidStr.TransitionSet.mul p) : F.Tr Ψ Ψ'') := by
  set M₁ := F.transPolyfold Ψ' Ψ''
  set M₂ := F.transPolyfold Ψ Ψ'
  have := MPolyfold.paracompactSpace_prod M₁ M₂
  have := (M₁.prod M₂).paracompactSpace_subtype (MPolyfold.fibredProduct
    (fun a : F.Tr Ψ' Ψ'' => (a : Ψ'.1.Trans Ψ''.1).src)
    (fun a : F.Tr Ψ Ψ' => (a : Ψ.1.Trans Ψ'.1).tgt))
  have hA := MPolyfold.isSubMPolyfold_fibredProduct (F.isLocalScDiffeo_src Ψ' Ψ'')
    (F.isLocalScDiffeo_tgt Ψ Ψ').isScSmoothMap
  have hval := MPolyfold.subPolyfold_inclusion_isScSmooth hA
  change (MPolyfold.subPolyfold hA).IsScSmoothMap (F.transPolyfold Ψ Ψ'') _
  refine MPolyfold.isScSmoothMap_of_isLocalScDiffeo_comp (F.isLocalScDiffeo_src Ψ Ψ'')
    F.continuous_mulMap ?_
  exact (F.isLocalScDiffeo_src Ψ Ψ').isScSmoothMap.comp
    ((MPolyfold.isScSmoothMap_snd M₁ M₂).comp hval)

end TransitionData

end UniformizerConstruction

/-! ### The basic construction -/

namespace BasicConstruction

open GroupoidStr (TransitionSet)

variable (B : C.BasicConstruction)

/-- **2021 Theorem 19.5.1, p. 886: the M-polyfold structure of `M(Ψ, Ψ')`** (carried by the
representative `B.rep`; `theorem_19_5_1_natural` for any other). -/
abbrev transPolyfold (Ψ Ψ' : B.U.Unif) : MPolyfold (B.M Ψ Ψ') := B.rep.transPolyfold Ψ Ψ'

/-- **2021 Theorem 19.5.1, p. 886**: assume `T` metrizable.  Then `M(Ψ, Ψ')` has a natural
M-polyfold structure for which `s` and `t` are local sc-diffeomorphisms; the maps
`F_h : V(o) → F_h(V(o))` are sc-diffeomorphisms (inverse `s`), and `Ψ̄ : G × O → M(Ψ, Ψ)` is an
sc-diffeomorphism.  (We read "natural" as `theorem_19_5_1_natural`; the metrizability of `T` is
not needed, see the module docstring.) -/
theorem theorem_19_5_1 (hB : B.U.HasClassUniformizers)
    (_hm : @MetrizableSpace C.OrbitSpace (B.natTop hB)) (Ψ Ψ' : B.U.Unif) :
    (B.transPolyfold Ψ Ψ').IsLocalScDiffeo Ψ.1.P
        (fun a : B.M Ψ Ψ' => (a : Ψ.1.Trans Ψ'.1).src) ∧
      (B.transPolyfold Ψ Ψ').IsLocalScDiffeo Ψ'.1.P
        (fun a : B.M Ψ Ψ' => (a : Ψ.1.Trans Ψ'.1).tgt) ∧
      (∀ h : Ψ.1.Trans Ψ'.1, Ψ.1.P.IsScDiffeoOn (B.transPolyfold Ψ Ψ')
        (fun q => B.rep.toTr (B.rep.map Ψ Ψ' h q)) (fun a : B.M Ψ Ψ' => (a : Ψ.1.Trans Ψ'.1).src)
        (B.rep.dom Ψ Ψ' h) (B.rep.map Ψ Ψ' h '' B.rep.dom Ψ Ψ' h)) ∧
      Ψ.1.ep.PMor.IsScDiffeoOn (B.transPolyfold Ψ Ψ) (B.rep.hatHomeomorph Ψ)
        (B.rep.hatHomeomorph Ψ).symm univ univ :=
  ⟨B.rep.isLocalScDiffeo_src Ψ Ψ', B.rep.isLocalScDiffeo_tgt Ψ Ψ', B.rep.isScDiffeoOn_map Ψ Ψ',
    B.rep.isScDiffeoOn_hatHomeomorph Ψ⟩

/-- **2021 Theorem 19.5.1, p. 886, "natural"**: (1) the structure is the only M-polyfold
structure on the space `M(Ψ, Ψ')` for which `s` is a local sc-diffeomorphism; (2) the structure
`F.transPolyfold` of any representative `F` of `𝓕` agrees with it (the identity
`trHomeomorph` is an sc-diffeomorphism). -/
theorem theorem_19_5_1_natural (Ψ Ψ' : B.U.Unif) :
    (∀ Q : MPolyfold (B.M Ψ Ψ'),
      Q.IsLocalScDiffeo Ψ.1.P (fun a : B.M Ψ Ψ' => (a : Ψ.1.Trans Ψ'.1).src) →
        Q.IsScDiffeoOn (B.transPolyfold Ψ Ψ') id id univ univ) ∧
      ∀ {F : B.U.TransitionData} (hF : (⟦F⟧ : B.U.TransitionConstruction) = B.𝓕),
        (F.transPolyfold Ψ Ψ').IsScDiffeoOn (B.transPolyfold Ψ Ψ') (B.trHomeomorph hF Ψ Ψ')
          (B.trHomeomorph hF Ψ Ψ').symm univ univ :=
  ⟨B.rep.isScDiffeoOn_id_of_isLocalScDiffeo_src Ψ Ψ', fun {F} hF =>
    B.rep.isScDiffeoOn_of_isLocalScDiffeo_src_comp Ψ Ψ' (B.trHomeomorph hF Ψ Ψ')
      (F.isLocalScDiffeo_src Ψ Ψ')⟩

/-- **2021 Corollary 19.5.2, p. 887**: the unit `u`, the inversion `ι` and the multiplication
`m` are sc-smooth. -/
theorem corollary_19_5_2 (Ψ Ψ' Ψ'' : B.U.Unif) :
    Ψ.1.P.IsScSmoothMap (B.transPolyfold Ψ Ψ)
        (fun o => B.rep.toTr (TransitionSet.unit o : Ψ.1.Trans Ψ.1)) ∧
      (B.transPolyfold Ψ Ψ').IsScSmoothMap (B.transPolyfold Ψ' Ψ)
        (fun a : B.M Ψ Ψ' => B.rep.toTr (a : Ψ.1.Trans Ψ'.1).inv) ∧
      MPolyfold.IsScSmoothOnFibredProduct (B.transPolyfold Ψ' Ψ'') (B.transPolyfold Ψ Ψ')
        (B.transPolyfold Ψ Ψ'') (B.rep.isLocalScDiffeo_src Ψ' Ψ'')
        (B.rep.isLocalScDiffeo_tgt Ψ Ψ').isScSmoothMap
        (fun p => (B.rep.toTr (GroupoidStr.TransitionSet.mul p) : B.M Ψ Ψ'')) :=
  ⟨B.rep.isScSmoothMap_unit Ψ, B.rep.isScSmoothMap_inv Ψ Ψ', B.rep.isScSmoothMap_mul Ψ Ψ' Ψ''⟩

end BasicConstruction

end GroupoidalCategory

end Polyfold
