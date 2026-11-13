import Polyfold.Chapter9.SupportGroupoidNaturality
import Polyfold.Chapter9.MathlibManifoldBridge

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part II, Chapter 9,
§9.1, **Remark 9.1.10** (p. 405; 2017: Remark 9.2, p. 295).

# The classical structures of Remark 9.1.10

## The text, paraphrased

(Remark 9.1.10) The manifolds and orbifolds of Proposition 9.1.9 are the M⁺-polyfold versions;
if `d_{|X|}(z) = 0` for every `z ∈ |supp(Θ)|`, then `S = |supp(Θ)|` has a natural classical
smooth manifold structure in case (1) and a natural classical smooth orbifold structure in
case (2).  Instead of the paracompactness of `|X|` it suffices that `|supp(Θ)|` is metrizable,
for instance compact.

## What is formalized

General facts on corner structures (Definition 4.1.1 with the dimension, `HasCornerStructureOfDim`
of `MathlibManifoldBridge.lean`):

* `MPolyfold.isCornerChart_transportChart`: a corner chart transported along an
  sc-diffeomorphism (`transportChart`, the proof of Proposition 2.4.4) is a corner chart.
* `MPolyfold.HasCornerStructureOfDim.of_isLocalScDiffeo` (pull-back along a local
  sc-diffeomorphism) and `HasCornerStructureOfDim.of_isLocalScDiffeo_surjective` (push-forward
  along a surjective one).

For `Θ` `n`-dimensional (Definition 9.1.2, `IsNDimensional`) with `d_{|X|} = 0` on `|supp(Θ)|`:

* `EpGroupoid.isSubmanifoldOfDim_supp`: `supp(Θ)` is an `n`-dimensional submanifold of `X`
  (orbifold-type); `degIndex_eq_zero_of_mem_supp`.
* **`EpGroupoid.remark_9_1_10_manifold`** (case (1)): for `Θ` of manifold-type, the M-polyfold
  structure `PZ` on `Z = |supp(Θ)|` of Proposition 9.1.9 (1) (`p : supp(Θ) → Z` a local
  sc-diffeomorphism) has a corner structure of dimension `n` without boundary, and with the charts
  of `MathlibManifoldBridge.lean` (`interiorChartedSpace`), `Z` is a classical smooth manifold,
  `IsManifold (𝓡 n) ∞ Z`.
* **`EpGroupoid.remark_9_1_10_orbifold`** (case (2)): for `Θ` of orbifold-type and every choice of
  local branching structures, the object space `⊔ M_x` and the morphism space of the text's
  groupoid `M` (`textGroupoid`) are classical smooth `n`-manifolds, `IsManifold (𝓡 n) ∞`, whose
  Mathlib charts are corner charts of the M-polyfold structures of `M`, `M` is an ep-groupoid (its
  structure maps are sc-smooth, `s` and `t` local sc-diffeomorphisms, and it is proper), and
  `|β| : |M| ≃ₜ Z` (Proposition 9.1.9 (2), `proposition_9_1_9_two_text`).

## How it relates to the text

Mathlib's manifolds have one model space, so the dimension is fixed: `Θ` is assumed
`n`-dimensional (for a general `Θ` the dimensional decomposition of Proposition 9.1.11 splits
`Θ` into `n`-dimensional pieces).  Neither Mathlib nor the project defines classical orbifolds
(étale proper Lie groupoids up to Morita equivalence); case (2) is stated as: the text's groupoid
`M` has classical smooth `n`-manifolds as object and morphism spaces (with the charts of the
bridge), is an étale proper ep-groupoid in the sc-smooth sense, and its orbit space is `Z`; the
source, target, unit and inverse maps are Mathlib local diffeomorphisms
(`remark_9_1_10_orbifold_etale` in `SupportGroupoidEtale.lean`); the composition is not stated
in Mathlib's language.  The second paragraph of the remark (metrizability of
`|supp(Θ)|` suffices) is Remark 9.1.4 (`OrbitSubsetMetrizable.lean`); our Proposition 9.1.9 uses no
paracompactness of `|X|` at all.
-/

set_option maxSynthPendingDepth 3

open Set Function Filter Topology Module Manifold
open scoped ContDiff

noncomputable section

namespace Polyfold

universe u v

namespace MPolyfold

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {P : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {Q : MPolyfold Y}

/-- A corner model (`LocalModel.ofRelOpen` of a relatively open subset of a partial quadrant in a
finite-dimensional space with the constant structure) restricted to `O ∩ W`, `W` open, is a corner
model. -/
theorem exists_ofRelOpen_inter {L : LocalModel}
    (hL : ∃ (V : Type) (_ : NormedAddCommGroup V) (_ : NormedSpace ℝ V)
      (_ : FiniteDimensional ℝ V) (C U : Set V) (hU : IsRelOpenInQuadrant (ScBanach.const V) C U),
      L = LocalModel.ofRelOpen hU)
    {W : Set (L.E 0)} (hW : IsOpen W) (h : IsScRetract L.E L.C (L.O ∩ W)) :
    ∃ (V : Type) (_ : NormedAddCommGroup V) (_ : NormedSpace ℝ V)
      (_ : FiniteDimensional ℝ V) (C U : Set V) (hU : IsRelOpenInQuadrant (ScBanach.const V) C U),
      (⟨L.E, L.C, L.O ∩ W, h⟩ : LocalModel) = LocalModel.ofRelOpen hU := by
  obtain ⟨V, _, _, _, C, U, hU, rfl⟩ := hL
  obtain ⟨O, hO, hOU⟩ := hU.relOpen
  refine ⟨V, _, _, _, C, U ∩ W, ⟨hU.isPartialQuadrant, O ∩ W, hO.inter hW, ?_⟩, rfl⟩
  rw [hOU]
  exact inter_right_comm O C W

/-- **A transported corner chart is a corner chart**: for an sc-diffeomorphism `f : U → V` and a
corner chart `ψ` of `Y`, the chart `ψ ∘ f` (`transportChart`) is a corner chart of `X`; its model
is the relatively open piece `ψ(V ∩ dom ψ)` of the model of `ψ`. -/
theorem isCornerChart_transportChart {f : X → Y} {g : Y → X} {U : Set X} {V : Set Y}
    (h : P.IsScDiffeoOn Q f g U V) {ψ : MChart Y} (hψ : ψ.IsCornerChart) :
    (transportChart h ψ).IsCornerChart := by
  have hso : IsOpen (V ∩ ψ.source) := h.isScSmoothOn_inv.isOpen.inter ψ.isOpen_source
  obtain ⟨W, hW, hWeq⟩ := ψ.exists_isOpen_image_eq inter_subset_right hso
  have hr : IsScRetract ψ.model.E ψ.model.C (ψ.model.O ∩ W) :=
    hWeq ▸ ψ.isScRetract_image inter_subset_right hso
  obtain ⟨V', i₁, i₂, i₃, C, U', hU', he⟩ := exists_ofRelOpen_inter hψ hW hr
  refine ⟨V', i₁, i₂, i₃, C, U', hU', Eq.trans ?_ he⟩
  change (⟨ψ.model.E, ψ.model.C, ψ '' (V ∩ ψ.source), _⟩ : LocalModel) = _
  congr 1

variable {n : ℕ}

/-- **A corner structure of dimension `n` pulls back along a local sc-diffeomorphism.** -/
theorem HasCornerStructureOfDim.of_isLocalScDiffeo {f : X → Y} (hf : P.IsLocalScDiffeo Q f)
    (hQ : Q.HasCornerStructureOfDim n) : P.HasCornerStructureOfDim n := by
  intro x
  obtain ⟨U, V, g, hx, hd⟩ := hf x
  obtain ⟨ψ, hψ, hfx, hc, hn⟩ := hQ (f x)
  exact ⟨transportChart hd ψ, transportChart_isChart hd hψ, ⟨hx, hfx⟩,
    isCornerChart_transportChart hd hc, hn⟩

/-- **A corner structure of dimension `n` pushes forward along a surjective local
sc-diffeomorphism.** -/
theorem HasCornerStructureOfDim.of_isLocalScDiffeo_surjective {f : X → Y}
    (hf : P.IsLocalScDiffeo Q f) (hs : Surjective f) (hP : P.HasCornerStructureOfDim n) :
    Q.HasCornerStructureOfDim n := by
  intro y
  obtain ⟨x, rfl⟩ := hs y
  obtain ⟨U, V, g, hx, hd⟩ := hf x
  obtain ⟨φ, hφ, hxφ, hc, hn⟩ := hP x
  refine ⟨transportChart hd.symm φ, transportChart_isChart hd.symm hφ, ⟨hd.mapsTo hx, ?_⟩,
    isCornerChart_transportChart hd.symm hc, hn⟩
  change g (f x) ∈ φ.source
  rw [hd.left_inv x hx]
  exact hxφ

end MPolyfold

namespace EpGroupoid

variable {Obj Mor : Type u} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] {X : EpGroupoid Obj Mor}
  {Θ : Obj → ℚ} {n : ℕ}

/-- For `Θ` of orbifold-type and `n`-dimensional, **`supp(Θ)` is an `n`-dimensional
submanifold** of `X` (near `a` it is a sheet `M_i ∩ U(a)` of dimension `n`). -/
theorem isSubmanifoldOfDim_supp (hΘ : X.IsBranchedEpSubgroupoid Θ) (ho : IsOrbifoldType Θ)
    (hn : X.IsNDimensional Θ n) : X.PObj.IsSubmanifoldOfDim (supp Θ) n := by
  have hS := isSmoothSubmanifold_supp_of_isOrbifoldType hΘ ho
  refine ⟨hS, fun a ha => ?_⟩
  obtain ⟨B, hB⟩ := hn a ha
  obtain ⟨i⟩ := nonempty_ι_of_mem_supp ha B
  have h1 := (hB i).2 a (B.mem_M i)
  rw [← supp_inter_eq_of_isOrbifoldType ho ha B i] at h1
  exact (MPolyfold.hasDimAt_inter_isOpen_iff hS B.isOpen_U B.mem_U).1 h1

/-- `d_{|X|} = 0` on `|supp(Θ)|` is `d_X = 0` on `supp(Θ)` (Definition 7.1.5). -/
theorem degIndex_eq_zero_of_mem_supp (h0 : ∀ z ∈ X.orbitSupp Θ, X.degIndexOrbit z = 0)
    {a : Obj} (ha : a ∈ supp Θ) : X.PObj.degIndex a = 0 :=
  h0 _ ⟨a, ha, rfl⟩

/-- The induced structure on `supp(Θ)` has a corner structure of dimension `n` without boundary. -/
theorem hasCornerStructureOfDim_subObj (hΘ : X.IsBranchedEpSubgroupoid Θ) (ho : IsOrbifoldType Θ)
    (hn : X.IsNDimensional Θ n) (h0 : ∀ z ∈ X.orbitSupp Θ, X.degIndexOrbit z = 0)
    (hA : X.IsEpSubgroupoid (supp Θ)) [ParacompactSpace (supp Θ)] :
    (subEpGroupoid hA).PObj.HasCornerStructureOfDim n ∧
      ∀ a, (subEpGroupoid hA).PObj.degIndex a = 0 := by
  have hS := isSubmanifoldOfDim_supp hΘ ho hn
  have h0' : ∀ a ∈ supp Θ, X.PObj.degIndex a = 0 := fun a ha => degIndex_eq_zero_of_mem_supp h0 ha
  exact ⟨hS.hasCornerStructureOfDim_of_degIndex_eq_zero h0',
    hS.1.subPolyfold_degIndex_eq_zero h0'⟩

/-- **2021 Remark 9.1.10, case (1)**, p. 405 (2017: Remark 9.2, p. 295): for `Θ` of manifold-type
and `n`-dimensional with `d_{|X|}(z) = 0` for every `z ∈ Z = |supp(Θ)|`, the M-polyfold structure
`PZ` of Proposition 9.1.9 (1) on `Z` (for which `p : supp(Θ) → Z`, `a ↦ |a|`, is a local
sc-diffeomorphism; unique by `proposition_9_1_9_one_unique`) has a corner structure of dimension
`n` without boundary, and `Z` with the Mathlib charts of these corner charts
(`interiorChartedSpace`) is a **classical smooth manifold**, `IsManifold (𝓡 n) ∞ Z`. -/
theorem remark_9_1_10_manifold (hΘ : X.IsBranchedEpSubgroupoid Θ) (hm : X.IsManifoldType Θ)
    (hn : X.IsNDimensional Θ n) (h0 : ∀ z ∈ X.orbitSupp Θ, X.degIndexOrbit z = 0) :
    haveI := X.PObj.paracompactSpace_subtype (supp Θ)
    haveI := hΘ.paracompactSpace_orbitSupp
    let hA := isEpSubgroupoid_supp_of_isOrbifoldType hΘ hm.1
    ∃ PZ : MPolyfold (X.orbitSupp Θ),
      (subEpGroupoid hA).PObj.IsLocalScDiffeo PZ (X.orbitSuppProj Θ) ∧
      ∃ (hc : PZ.HasCornerStructureOfDim n) (hd : ∀ z, PZ.degIndex z = 0),
        letI := PZ.interiorChartedSpace hc hd
        IsManifold (𝓡 n) ∞ (X.orbitSupp Θ) := by
  have := X.PObj.paracompactSpace_subtype (supp Θ)
  have := hΘ.paracompactSpace_orbitSupp
  obtain ⟨hA, -, PZ, hPZ⟩ := proposition_9_1_9_one hΘ hm
  obtain ⟨hc, hd⟩ := hasCornerStructureOfDim_subObj hΘ hm.1 hn h0 hA
  have hsurj : Surjective (X.orbitSuppProj Θ) := (isDescentMap_orbitSupp hm hA).surjective
  have hcZ : PZ.HasCornerStructureOfDim n := hc.of_isLocalScDiffeo_surjective hPZ hsurj
  have hdZ : ∀ z, PZ.degIndex z = 0 := fun z => by
    obtain ⟨a, rfl⟩ := hsurj z
    rw [hPZ.degIndex_eq a]
    exact hd a
  exact ⟨PZ, hPZ, hcZ, hdZ, MPolyfold.isManifold_interiorChartedSpace hcZ hdZ⟩

/-- **2021 Remark 9.1.10, case (2)**, p. 405 (2017: Remark 9.2, p. 295): for `Θ` of orbifold-type
and `n`-dimensional with `d_{|X|} = 0` on `Z = |supp(Θ)|`, and every choice `c` of local
branching structures, the text's groupoid `M = textGroupoid hA c` (objects `⊔ M_x`) has object
and morphism M-polyfolds with corner structures of dimension `n` without boundary, so both are
**classical smooth `n`-manifolds** (`IsManifold (𝓡 n) ∞`, with the charts of
`interiorChartedSpace`), `M` is an ep-groupoid (étale: `s`, `t` local sc-diffeomorphisms;
proper), and `|β| : |M| ≃ₜ Z` (Proposition 9.1.9 (2)).  This is what is shown of the "classical
smooth orbifold structure" (see the module docstring). -/
theorem remark_9_1_10_orbifold (hΘ : X.IsBranchedEpSubgroupoid Θ) (ho : IsOrbifoldType Θ)
    (hn : X.IsNDimensional Θ n) (h0 : ∀ z ∈ X.orbitSupp Θ, X.degIndexOrbit z = 0)
    [Nonempty (supp Θ)] (c : X.SheetChoice Θ) :
    haveI := X.PObj.paracompactSpace_subtype (supp Θ)
    let hA := isEpSubgroupoid_supp_of_isOrbifoldType hΘ ho
    ∃ (hcO : (textGroupoid hA c).PObj.HasCornerStructureOfDim n)
      (hdO : ∀ p, (textGroupoid hA c).PObj.degIndex p = 0)
      (hcM : (textGroupoid hA c).PMor.HasCornerStructureOfDim n)
      (hdM : ∀ q, (textGroupoid hA c).PMor.degIndex q = 0),
      (letI := (textGroupoid hA c).PObj.interiorChartedSpace hcO hdO;
        IsManifold (𝓡 n) ∞ (sheetCover hA c).objSet) ∧
      (letI := (textGroupoid hA c).PMor.interiorChartedSpace hcM hdM;
        IsManifold (𝓡 n) ∞ (sheetCover hA c).morSet) ∧
      Nonempty ((textGroupoid hA c).OrbitSpace ≃ₜ X.orbitSupp Θ) := by
  have := X.PObj.paracompactSpace_subtype (supp Θ)
  set hA := isEpSubgroupoid_supp_of_isOrbifoldType hΘ ho
  obtain ⟨hc, hd⟩ := hasCornerStructureOfDim_subObj hΘ ho hn h0 hA
  set M := textGroupoid hA c
  have hF := (sheetCover hA c).proposition_10_1_3.isLocalScDiffeo_obj
  have hcO : M.PObj.HasCornerStructureOfDim n := hc.of_isLocalScDiffeo hF
  have hdO : ∀ p, M.PObj.degIndex p = 0 := fun p => by
    rw [← hF.degIndex_eq p]; exact hd _
  have hcM : M.PMor.HasCornerStructureOfDim n := hcO.of_isLocalScDiffeo M.isLocalScDiffeo_src
  have hdM : ∀ q, M.PMor.degIndex q = 0 := fun q => by
    rw [← M.isLocalScDiffeo_src.degIndex_eq q]; exact hdO _
  exact ⟨hcO, hdO, hcM, hdM, MPolyfold.isManifold_interiorChartedSpace hcO hdO,
    MPolyfold.isManifold_interiorChartedSpace hcM hdM, ⟨textOrbitHomeomorph hA c⟩⟩

end EpGroupoid

end Polyfold
