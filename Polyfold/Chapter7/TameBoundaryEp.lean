import Polyfold.Chapter2.TameBoundaryTopology
import Polyfold.Chapter7.EpGroupoid
import Polyfold.Chapter7.LocalDiffeo

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part II, Chapter 7,
Appendix §7.6.5 "Boundary Structure of Tame Ep-Groupoids" (pp. 351–355), new in the 2021
edition: the structure maps **(7.25)–(7.29)** (pp. 354–355) and **Theorem 7.6.9** (p. 355).
The tame boundary `bX`, the sets `U(x, V, θ)` and the maps `Φ_{(x,V,θ)}`, `B` are those of
`Polyfold/Chapter2/TameBoundary.lean` and `Polyfold/Chapter2/TameBoundaryTopology.lean`.

# The boundary groupoid of a tame ep-groupoid

## The text, paraphrased

(§7.6.5.1, pp. 351–353) A recollection of Appendix 2.7.4, restated without change: Proposition
2.7.5, face-structured sets and `N_{X,x}` (Definition 2.7.6), the category `L_X` and the functor
`F_X` (Definition 2.7.8), admissible triples, `bX` and `B` (Definition 2.7.10), the sets
`U(x, V, θ)` with the bijections `Φ_{(x,V,θ)}` (Definition 2.7.11), Theorem 2.7.13 and
Definition 2.7.14.
(§7.6.5.2, pp. 353–355) For a tame ep-groupoid `(X, 𝐗)` the morphism M-polyfold is tame too, `s`
being a local sc-diffeomorphism; the tame boundary construction gives `B : bX → X` and
`B : b𝐗 → 𝐗`.  (7.25) For `[φ, 𝐕, θ] ∈ b𝐗` take `𝐕` so small that `s : 𝐕 → V` is an
sc-diffeomorphism onto a suitable neighbourhood `V` of `x = s(φ)`; then `s(θ)` is a face of `V`
through `x`, and `s([φ, 𝐕, θ]) = [x, V, s(θ)]`; similarly for `t`.  (7.26) A class is viewed as a
morphism from its source to its target.  (7.27) `ι([φ, 𝐕, θ]) = [φ⁻¹, 𝐕⁻¹, θ⁻¹]`.  (7.28) For `V`
small and `s : 𝐕 → V` an sc-diffeomorphism on a neighbourhood `𝐕` of `1ₓ`,
`u([x, V, θ]) = [1ₓ, 𝐕, θ̄]`, `θ̄` the preimage of `θ` under `s|𝐕`.  (7.29) For composable
`[ψ, 𝐖, σ]`, `[φ, 𝐕, θ]` choose representatives with `t : 𝐕 → V` and `s : 𝐖 → V`
sc-diffeomorphisms (and the maps `U(φ, 𝐕, θ) → θ`, `U(ψ, 𝐖, σ) → σ` sc-diffeomorphisms); then
`γ ↦ (s|𝐖)⁻¹(t(γ)) ∘ γ` is an sc-diffeomorphism of `𝐕` onto an open set `𝐖 ₛ∘ₜ 𝐕`, taking `θ`
to the face `σ ₛ∘ₜ θ`, and `m([ψ, 𝐖, σ], [φ, 𝐕, θ]) = [ψ ∘ φ, 𝐖 ₛ∘ₜ 𝐕, σ ₛ∘ₜ θ]`.
(Theorem 7.6.9, p. 355, verification left to the reader) For a tame ep-groupoid: (1) `bX`, `b𝐗`
have natural metrizable topologies; (2) natural tame M-polyfold structures; (3) both maps `B` are
sc-smooth; (4) `d_X(B(p)) − 1 = d_{bX}(p)`, and likewise on `b𝐗`; (5) `(bX, b𝐗)` with
`s, t, u, ι, m` is a tame ep-groupoid.  Topologies and structures are characterized as in
Theorem 2.7.13: every `U` is open and every `Φ` a homeomorphism and an sc-diffeomorphism onto its
face.  The sketch: with `s : 𝐕 → V` an sc-diffeomorphism, in the charts `Φ` the map `s` becomes
the sc-diffeomorphism `s : θ → s(θ)`.

## What is formalized

* Generic transport of the tame boundary (any `IsCornerIndex`) along index-preserving local
  homeomorphisms: `TameBoundary.IsDHomeoOn` (a homeomorphism of an open set onto an open set
  preserving the index; witness `isDHomeoOn_id`), its action on faces, on `N_{X,x}`, on the
  morphisms of `L_X` and on `F_X` (`isFaceIn_image`, `mem_faceStructuredNbhdsAt_image`,
  `isMor_image`, `image_faceExt`); the induced map of triples `BTriple.map`; the relation
  `IsLiftOf` (witness `isLiftOf_id`; `IsLiftOf.unique`, `IsLiftOf.comp`); and for an
  index-preserving local homeomorphism `f` the map `bLift f`, `[y, V, θ] ↦ [f y, f V, f θ]`
  (`bLift_cls`), continuous, open, a local homeomorphism (`isLocalHomeomorph_bLift`).
  `isCompact_preimage_bMap`: preimages of compact sets under `B` are compact.
* `MPolyfold.IsScDiffeoOn.isDHomeoOn`: an sc-diffeomorphism preserves the degeneracy index.
* `EpGroupoid.isTame_PMor` (§7.6.5.2); `bObj`, `bMor` (`bX`, `b𝐗`); `bSrc`, `bTgt` **(7.25)**,
  `bInv` **(7.27)**, `bUnit` **(7.28)**, `bComp` **(7.29)**, with the formulas `bSrc_cls`,
  `bTgt_cls`, `bInv_cls`, `bUnit_cls` and the characterization `bComp_eq`; `boundaryGroupoid`
  (the groupoid laws); `boundaryFunctor` (`B` is a functor).
* **Theorem 7.6.9**, `theorem_7_6_9`: (1) with the topological characterization (from
  `theorem_2_7_13_topology` for `X` and `𝐗`); (3) continuity of both maps `B`; (4) in the form "a
  point of index `d` has exactly `d` preimages under `B`"; (5) the groupoid `(bX, b𝐗)`: `s, t`
  local homeomorphisms (`isLocalHomeomorph_bSrc`, `isLocalHomeomorph_bTgt`), `u, ι` continuous,
  `m` continuous on the composable pairs (`continuousOn_bComp`), the properness property
  (`exists_isProperMap_bTgt`); `B` a functor.
* Witness: `trivial_quadrant_witness` (the trivial ep-groupoid of the tame quadrant
  `[0,∞)ⁿ ⊕ W` is tame, and for `n ≥ 1` its `bX` and `b𝐗` are nonempty, the corner having `n`
  preimages), and `bSrc_trivial`.

## What the text leaves implicit, and the choices made

* The sc-diffeomorphisms in (7.25)–(7.28) enter through their topological content: an
  sc-diffeomorphism between open sets is a homeomorphism preserving `d` (`IsDHomeoOn`), and the
  transported class does not depend on the chosen sheet (`map_cls_eq`), so (7.25)–(7.28) are well
  defined.  All four maps are defined uniformly as `bLift` of `s`, `t`, `ι`, `u`.
* (7.25): `s(𝐕) ∈ N_{X,x}` and `s(θ)` is a face of `s(𝐕)` through `x`
  (`mem_faceStructuredNbhdsAt_image`, `isFaceIn_image`), which is how we read "suitable open
  neighbourhood".
* (7.28) is read through `u` itself: `u` is a continuous section of the local homeomorphism `s`,
  hence an index-preserving homeomorphism onto the open set `u(X)` (`isDHomeoOn_unit`); near `x`
  it agrees with `(s|𝐖)⁻¹` for every sheet `𝐖 ∋ 1ₓ`, which gives the printed formula (`bUnit_cls`).
* (7.29): `m(a, b)` is the unique class over `ψ ∘ φ` with source `s(b)` (`exists_bComp`; a class
  of `b𝐗` is determined by its image under `B` and its source, `eq_of_bMap_eq_of_bSrc_eq`).  Near
  `φ` the map `γ ↦ (s|𝐖)⁻¹(t(γ)) ∘ γ` agrees with `(s|𝐔)⁻¹ ∘ s` for a sheet `𝐔 ∋ ψ ∘ φ` of `s`
  (`eventuallyEq_comp_sheet`), so the printed class `[ψ ∘ φ, 𝐖 ₛ∘ₜ 𝐕, σ ₛ∘ₜ θ]` has source
  `s([φ, 𝐕, θ])` and is this class.  Off the composable pairs `bComp` takes a junk value.
* As in Chapter 2, `Φ_{(x,V,θ)}` is onto `θ` only for `V` centred at `x` (2021 (2.44) does not
  hold as we read it for every `V ∈ N_{X,x}`, see `Polyfold/Chapter2/TameBoundary.lean`); in
  general it is an open embedding, the form used in the characterization.  Representatives are
  taken centred where needed (`exists_rep_centered`).
* "Tame ep-groupoid" is `EpGroupoid.IsTame` (2021 Definition 7.1.6: the object M-polyfold is
  tame).  The properness property is that of 2021 Definition 7.1.3 (3).
* The rest of Theorem 7.6.9, which needs the M-polyfold structure of `bX` (2021 Theorem 2.7.13 (2),
  in `Chapter2/TameBoundaryStructure.lean`), is in `Chapter7/TameBoundaryEpStructure.lean`: part (2),
  the sc-smoothness in (3) and (5), `d_{bX}` in (4), the tame ep-groupoid
  `EpGroupoid.boundaryEpGroupoid` and the ep-functor `EpGroupoid.boundaryEpFunctor`; the full
  statement is `EpGroupoid.theorem_7_6_9_full`.
-/

set_option maxSynthPendingDepth 3

open Set Filter Topology Function

noncomputable section

namespace Polyfold

namespace TameBoundary

universe u v w

/-! ### Index-preserving homeomorphisms between open sets -/

section DHomeo

variable {Y : Type u} [TopologicalSpace Y] {X : Type v} [TopologicalSpace X]
  {Z : Type w} [TopologicalSpace Z]

/-- `f` maps the open set `W` homeomorphically onto an open set (continuous on `W`, injective on
`W`, open on the open subsets of `W`) and preserves the index: `d_X(f(y)) = d_Y(y)` on `W`.  The
restriction of a local sc-diffeomorphism to a sheet has this property
(`MPolyfold.IsScDiffeoOn.isDHomeoOn`). -/
structure IsDHomeoOn (dY : Y → ℕ) (dX : X → ℕ) (f : Y → X) (W : Set Y) : Prop where
  isOpen : IsOpen W
  continuousOn : ContinuousOn f W
  injOn : InjOn f W
  isOpen_image : ∀ U, IsOpen U → U ⊆ W → IsOpen (f '' U)
  deg_eq : ∀ y ∈ W, dX (f y) = dY y

/-- Every point has a neighbourhood on which `f` is an index-preserving homeomorphism onto an open
set. -/
def IsDLocalHomeo (dY : Y → ℕ) (dX : X → ℕ) (f : Y → X) : Prop :=
  ∀ y, ∃ W, y ∈ W ∧ IsDHomeoOn dY dX f W

variable {dY : Y → ℕ} {dX : X → ℕ} {dZ : Z → ℕ}

theorem isDHomeoOn_id (d : Y → ℕ) : IsDHomeoOn d d id univ :=
  ⟨isOpen_univ, continuousOn_id, injOn_id _, fun U hU _ => by rwa [image_id], fun _ _ => rfl⟩

theorem isDLocalHomeo_id (d : Y → ℕ) : IsDLocalHomeo d d id :=
  fun y => ⟨univ, mem_univ y, isDHomeoOn_id d⟩

namespace IsDHomeoOn

variable {f : Y → X} {W : Set Y} (hf : IsDHomeoOn dY dX f W)
include hf

theorem mono {U : Set Y} (hU : IsOpen U) (hUW : U ⊆ W) : IsDHomeoOn dY dX f U :=
  ⟨hU, hf.continuousOn.mono hUW, hf.injOn.mono hUW,
    fun U' hU' h => hf.isOpen_image U' hU' (h.trans hUW), fun y hy => hf.deg_eq y (hUW hy)⟩

theorem congr {f' : Y → X} (h : EqOn f f' W) : IsDHomeoOn dY dX f' W where
  isOpen := hf.isOpen
  continuousOn := hf.continuousOn.congr h.symm
  injOn := fun a ha b hb hab => hf.injOn ha hb (by rw [h ha, h hb]; exact hab)
  isOpen_image U hU hUW := by
    rw [← (h.mono hUW).image_eq]; exact hf.isOpen_image U hU hUW
  deg_eq y hy := by rw [← h hy]; exact hf.deg_eq y hy

theorem comp {g : X → Z} {V : Set X} (hg : IsDHomeoOn dX dZ g V) (hfV : MapsTo f W V) :
    IsDHomeoOn dY dZ (g ∘ f) W where
  isOpen := hf.isOpen
  continuousOn := hg.continuousOn.comp hf.continuousOn hfV
  injOn := hg.injOn.comp hf.injOn hfV
  isOpen_image U hU hUW := by
    rw [image_comp]
    exact hg.isOpen_image _ (hf.isOpen_image U hU hUW) ((image_mono hUW).trans
      (image_subset_iff.2 hfV))
  deg_eq y hy := by rw [comp_apply, hg.deg_eq _ (hfV hy), hf.deg_eq y hy]

theorem isOpen_image_self : IsOpen (f '' W) := hf.isOpen_image W hf.isOpen subset_rfl

theorem continuousAt {y : Y} (hy : y ∈ W) : ContinuousAt f y :=
  hf.continuousOn.continuousAt (hf.isOpen.mem_nhds hy)

/-- The inverse of `f|W`, continuous on `f(W)`. -/
theorem exists_inv [Nonempty Y] :
    ∃ g : X → Y, ContinuousOn g (f '' W) ∧ ∀ y ∈ W, g (f y) = y := by
  refine ⟨invFunOn f W, ?_, fun y hy => hf.injOn.leftInvOn_invFunOn hy⟩
  rw [continuousOn_open_iff hf.isOpen_image_self]
  intro O hO
  have : f '' W ∩ invFunOn f W ⁻¹' O = f '' (W ∩ O) := by
    ext z
    constructor
    · rintro ⟨⟨y, hy, rfl⟩, hz⟩
      rw [mem_preimage, hf.injOn.leftInvOn_invFunOn hy] at hz
      exact ⟨y, ⟨hy, hz⟩, rfl⟩
    · rintro ⟨y, ⟨hy, hyO⟩, rfl⟩
      exact ⟨⟨y, hy, rfl⟩, by rw [mem_preimage, hf.injOn.leftInvOn_invFunOn hy]; exact hyO⟩
  rw [this]
  exact hf.isOpen_image _ (hf.isOpen.inter hO) inter_subset_left

/-- `f(V ∩ {d_Y = 1}) = f(V) ∩ {d_X = 1}`. -/
theorem image_inter_deg {V : Set Y} (hV : V ⊆ W) :
    f '' (V ∩ {y | dY y = 1}) = f '' V ∩ {x | dX x = 1} := by
  ext z
  constructor
  · rintro ⟨y, ⟨hy, hy1⟩, rfl⟩
    refine ⟨⟨y, hy, rfl⟩, ?_⟩
    change dX (f y) = 1
    rw [hf.deg_eq y (hV hy)]; exact hy1
  · rintro ⟨⟨y, hy, rfl⟩, h1⟩
    refine ⟨y, ⟨hy, ?_⟩, rfl⟩
    change dY y = 1
    rw [← hf.deg_eq y (hV hy)]; exact h1

/-- `f` maps connected components (inside `W`) to connected components. -/
theorem image_connectedComponentIn {S : Set Y} (hS : S ⊆ W) {p : Y} (hp : p ∈ W) :
    f '' connectedComponentIn S p = connectedComponentIn (f '' S) (f p) := by
  by_cases hpS : p ∈ S
  swap
  · rw [connectedComponentIn_eq_empty hpS, image_empty, connectedComponentIn_eq_empty]
    rintro ⟨q, hq, hqp⟩
    exact hpS (hf.injOn (hS hq) hp hqp ▸ hq)
  refine Subset.antisymm ((hf.continuousOn.mono hS).image_connectedComponentIn_subset hpS) ?_
  have : Nonempty Y := ⟨p⟩
  obtain ⟨g, hg, hgf⟩ := hf.exists_inv
  have hgS : g '' (f '' S) = S := by
    rw [image_image]
    exact (image_congr fun y hy => hgf y (hS hy)).trans (image_id' S)
  have h := (hg.mono (image_mono hS)).image_connectedComponentIn_subset (mem_image_of_mem f hpS)
  rw [hgS, hgf p hp] at h
  intro z hz
  obtain ⟨y, hy, rfl⟩ := connectedComponentIn_subset _ _ hz
  have : g (f y) ∈ connectedComponentIn S p := h ⟨f y, hz, rfl⟩
  rw [hgf y (hS hy)] at this
  exact ⟨y, this, rfl⟩

/-- `f(V ∩ cl A) = f(V) ∩ cl f(A)` for `A ⊆ V ⊆ W`. -/
theorem image_inter_closure {V A : Set Y} (hVW : V ⊆ W) (hAV : A ⊆ V) :
    f '' (V ∩ closure A) = f '' V ∩ closure (f '' A) := by
  ext z
  constructor
  · rintro ⟨y, ⟨hy, hyA⟩, rfl⟩
    exact ⟨⟨y, hy, rfl⟩, mem_closure_image (hf.continuousAt (hVW hy)) hyA⟩
  · rintro ⟨⟨y, hy, rfl⟩, hz⟩
    have : Nonempty Y := ⟨y⟩
    obtain ⟨g, hg, hgf⟩ := hf.exists_inv
    have hgc : ContinuousAt g (f y) :=
      hg.continuousAt (hf.isOpen_image_self.mem_nhds ⟨y, hVW hy, rfl⟩)
    have := mem_closure_image hgc hz
    rw [image_image, hgf y (hVW hy),
      (image_congr fun a ha => hgf a (hVW (hAV ha))).trans (image_id' A)] at this
    exact ⟨y, ⟨hy, this⟩, rfl⟩

/-- **Faces are transported**: `f(faceAt V p) = faceAt (f V) (f p)`. -/
theorem image_faceAt {V : Set Y} (hVW : V ⊆ W) {p : Y} (hp : p ∈ V) :
    f '' faceAt dY V p = faceAt dX (f '' V) (f p) := by
  unfold faceAt
  rw [hf.image_inter_closure hVW ((connectedComponentIn_subset _ _).trans inter_subset_left),
    hf.image_connectedComponentIn (inter_subset_left.trans hVW) (hVW hp), hf.image_inter_deg hVW]

theorem isFaceIn_image {V θ : Set Y} (hVW : V ⊆ W) (hθ : IsFaceIn dY V θ) :
    IsFaceIn dX (f '' V) (f '' θ) := by
  obtain ⟨p, hp, hp1, rfl⟩ := hθ
  exact ⟨f p, mem_image_of_mem f hp, (hf.deg_eq p (hVW hp)).trans hp1,
    hf.image_faceAt hVW hp⟩

theorem exists_isFaceIn_of_image {V : Set Y} (hVW : V ⊆ W) {θ' : Set X}
    (h : IsFaceIn dX (f '' V) θ') : ∃ θ, IsFaceIn dY V θ ∧ f '' θ = θ' := by
  obtain ⟨_, ⟨p, hp, rfl⟩, hp1, rfl⟩ := h
  exact ⟨faceAt dY V p, ⟨p, hp, (hf.deg_eq p (hVW hp)).symm.trans hp1, rfl⟩,
    hf.image_faceAt hVW hp⟩

/-- The faces of `f(V)` through `f(y)` are the images of the faces of `V` through `y`. -/
theorem facesThrough_image {V : Set Y} (hVW : V ⊆ W) {y : Y} (hy : y ∈ V) :
    facesThrough dX (f '' V) (f y) = image f '' facesThrough dY V y := by
  ext θ'
  constructor
  · rintro ⟨hθ', hyθ'⟩
    obtain ⟨θ, hθ, rfl⟩ := hf.exists_isFaceIn_of_image hVW hθ'
    refine ⟨θ, ⟨hθ, ?_⟩, rfl⟩
    obtain ⟨z, hz, hzy⟩ := hyθ'
    rwa [hf.injOn (hVW (hθ.subset hz)) (hVW hy) hzy] at hz
  · rintro ⟨θ, ⟨hθ, hyθ⟩, rfl⟩
    exact ⟨hf.isFaceIn_image hVW hθ, mem_image_of_mem f hyθ⟩

theorem encard_facesThrough_image {V : Set Y} (hVW : V ⊆ W) {y : Y} (hy : y ∈ V) :
    (facesThrough dX (f '' V) (f y)).encard = (facesThrough dY V y).encard := by
  rw [hf.facesThrough_image hVW hy]
  exact InjOn.encard_image fun θ₁ h₁ θ₂ h₂ h =>
    (hf.injOn.image_eq_image_iff (h₁.1.subset.trans hVW) (h₂.1.subset.trans hVW)).1 h

theorem isFaceStructuredOpen_image {V : Set Y} (hVW : V ⊆ W) (h : IsFaceStructuredOpen dY V) :
    IsFaceStructuredOpen dX (f '' V) := by
  refine ⟨hf.isOpen_image V h.1 hVW, ?_⟩
  rintro _ ⟨y, hy, rfl⟩
  rw [hf.encard_facesThrough_image hVW hy, h.2 y hy, hf.deg_eq y (hVW hy)]

theorem mem_faceStructuredNbhdsAt_image {V : Set Y} (hVW : V ⊆ W) {y : Y}
    (h : V ∈ faceStructuredNbhdsAt dY y) : f '' V ∈ faceStructuredNbhdsAt dX (f y) := by
  refine ⟨⟨hf.isFaceStructuredOpen_image hVW h.1.1, h.1.2.1.image f, ?_⟩,
    mem_image_of_mem f h.2.1, ?_⟩
  · obtain ⟨b, hb⟩ := h.1.2.2
    refine ⟨b, ?_⟩
    rintro _ ⟨_, ⟨z, hz, rfl⟩, rfl⟩
    rw [hf.deg_eq z (hVW hz)]
    exact hb (mem_image_of_mem dY hz)
  · rintro _ ⟨z, hz, rfl⟩
    rw [hf.deg_eq z (hVW hz), hf.deg_eq y (hVW h.2.1)]
    exact h.2.2 z hz

/-- `f(F_X(φ)(θ)) = F_X(f φ)(f θ)`: the extension of faces commutes with `f`. -/
theorem image_faceExt (hdY : IsCornerIndex dY) (hdX : IsCornerIndex dX) {U V θ : Set Y}
    (hV : IsOpen V) (hVW : V ⊆ W) (hUV : U ⊆ V) (hθ : IsFaceIn dY U θ) :
    f '' faceExt dY V θ = faceExt dX (f '' V) (f '' θ) := by
  obtain ⟨p, hp, hp1, rfl⟩ := hθ
  rw [faceExt_faceAt hdY hV hUV hp hp1, hf.image_faceAt hVW (hUV hp),
    hf.image_faceAt (hUV.trans hVW) hp,
    faceExt_faceAt hdX (hf.isOpen_image V hV hVW) (image_mono hUV) (mem_image_of_mem f hp)
      ((hf.deg_eq p (hVW (hUV hp))).trans hp1)]

/-- Morphisms of `L_Y` inside `W` are transported to morphisms of `L_X`. -/
theorem isMor_image {y z : Y} {U V : Set Y} (hVW : V ⊆ W) (hy : y ∈ U)
    (h : IsMor dY y U z V) : IsMor dX (f y) (f '' U) (f z) (f '' V) := by
  have hyV : y ∈ V := h.1 hy
  refine ⟨image_mono h.1, ?_, ?_⟩
  · rw [hf.encard_facesThrough_image hVW hyV, h.2.1, hf.deg_eq y (hVW hyV)]
  · intro θ' hθ'
    rw [hf.facesThrough_image hVW hyV] at hθ'
    obtain ⟨θ, hθ, rfl⟩ := hθ'
    exact mem_image_of_mem f (h.2.2 θ hθ)

end IsDHomeoOn

end DHomeo

/-! ### Classes of triples over nested neighbourhoods -/

section Classes

variable {X : Type u} [TopologicalSpace X] {d : X → ℕ} (hd : IsCornerIndex d)

/-- Two triples `(x, V, θ)`, `(x, W, σ)` with `V ⊆ W` are equivalent iff `F_X(φ)(θ) = σ` for the
morphism `φ : (x, V) → (x, W)`. -/
theorem cls_eq_iff_faceExt {a b : BTriple hd} (hx : a.x = b.x) (hV : a.V ⊆ b.V) :
    a.cls = b.cls ↔ faceExt d b.V a.θ = b.θ := by
  rw [BTriple.cls_eq_cls hd]
  constructor
  · rintro ⟨-, V'', -, hsub, θ'', hθ'', e₁, e₂⟩
    rw [← e₁, faceExt_faceExt hd a.mem.1.1.1 b.mem.1.1.1 (fun z hz => (hsub hz).1) hV hθ''.1, e₂]
  · intro h
    exact ⟨hx, a.V, a.mem, fun z hz => ⟨hz, hV hz⟩, a.θ, a.mem_faces,
      faceExt_self hd a.mem.1.1.1 a.mem_faces.1, h⟩

/-- Triples with the same data have the same class. -/
theorem cls_congr {a b : BTriple hd} (hx : a.x = b.x) (hV : a.V = b.V) (hθ : a.θ = b.θ) :
    a.cls = b.cls :=
  (cls_eq_iff_faceExt hd hx hV.subset).2
    (by rw [hθ]; exact faceExt_self hd b.mem.1.1.1 b.mem_faces.1)

theorem bMap_eq_of_cls_eq {a b : BTriple hd} (h : a.cls = b.cls) : a.x = b.x := by
  have := congrArg (bMap hd) h
  rwa [bMap_cls, bMap_cls] at this

/-- A representative of `p` with `V` inside a given open `N ∋ B(p)`, centred at its point
(`IsCenteredAt`, so that `Φ` is onto its face), with `U(x, V, θ)` inside a given open `O ∋ p`. -/
theorem exists_rep_centered (p : BSpace hd) {N : Set X} (hN : IsOpen N) (hpN : bMap hd p ∈ N)
    {O : Set (BSpace hd)} (hO : IsOpen O) (hpO : p ∈ O) :
    ∃ t : BTriple hd, t.cls = p ∧ t.V ⊆ N ∧ IsCenteredAt d t.x t.V ∧ uSet hd t ⊆ O := by
  obtain ⟨t₁, rfl, ht₁O⟩ := (isOpen_iff_forall_uSet hd).1 hO p hpO
  obtain ⟨t₂, ht₂, -, ht₂N, ht₂U⟩ := t₁.exists_shrink hd hN hpN
  have hR := reach_mem_faceStructuredNbhdsAt hd t₂.mem
  obtain ⟨θ, hθ, hθe⟩ :=
    exists_face_restrict hd t₂.mem hR.1.1.1 hR.2.1 (reach_subset _ _) t₂.mem_faces
  let t : BTriple hd := ⟨⟨t₂.x, reach d t₂.V t₂.x, hR, t₂.one_le⟩, θ, hθ⟩
  have hcls : t.cls = t₂.cls :=
    (cls_eq_iff_faceExt hd (a := t) (b := t₂) rfl (reach_subset _ _)).2 hθe
  exact ⟨t, hcls.trans ht₂, (reach_subset _ _).trans ht₂N,
    isCenteredAt_reach hd t₂.mem.1.1.1 t₂.mem.2.1,
    (uSet_subset hd (s := t) (t := t₂) (isMor_of_subset (reach_subset _ _) t₂.mem) hθe).trans
      (ht₂U.trans ht₁O)⟩

end Classes

/-! ### Transport of triples and the induced maps `bY → bX` -/

section Lift

variable {Y : Type u} [TopologicalSpace Y] {X : Type v} [TopologicalSpace X]
  {Z : Type w} [TopologicalSpace Z] {dY : Y → ℕ} {dX : X → ℕ} {dZ : Z → ℕ}
  (hdY : IsCornerIndex dY) (hdX : IsCornerIndex dX) (hdZ : IsCornerIndex dZ)

/-- The image `(f(x), f(V), f(θ))` of an admissible triple `(x, V, θ)` whose `V` lies in a domain
`W` of `f`: again an admissible triple. -/
def BTriple.map {hdY : IsCornerIndex dY} {f : Y → X} {W : Set Y} (hf : IsDHomeoOn dY dX f W)
    (t : BTriple hdY) (h : t.V ⊆ W) : BTriple hdX :=
  ⟨⟨f t.x, f '' t.V, hf.mem_faceStructuredNbhdsAt_image h t.mem,
    by rw [hf.deg_eq t.x (h t.mem.2.1)]; exact t.one_le⟩, f '' t.θ,
    ⟨hf.isFaceIn_image h t.mem_faces.1, mem_image_of_mem f t.mem_faces.2⟩⟩

section MapLemmas

variable {hdY} {f : Y → X} {W : Set Y} (hf : IsDHomeoOn dY dX f W) (t : BTriple hdY)
  (h : t.V ⊆ W)

@[simp] lemma BTriple.map_x : (t.map hdX hf h).x = f t.x := rfl
@[simp] lemma BTriple.map_V : (t.map hdX hf h).V = f '' t.V := rfl
@[simp] lemma BTriple.map_θ : (t.map hdX hf h).θ = f '' t.θ := rfl

end MapLemmas

/-- Two representatives `r`, `t` of one class with `r.V ⊆ t.V ⊆ W` have equivalent images. -/
theorem map_cls_eq_of_subset {f : Y → X} {W : Set Y} (hf : IsDHomeoOn dY dX f W)
    {r t : BTriple hdY} (hrt : r.cls = t.cls) (hV : r.V ⊆ t.V) (ht : t.V ⊆ W) :
    (r.map hdX hf (hV.trans ht)).cls = (t.map hdX hf ht).cls := by
  have hx : r.x = t.x := bMap_eq_of_cls_eq hdY hrt
  rw [cls_eq_iff_faceExt hdX (congrArg f hx) (image_mono hV)]
  change faceExt dX (f '' t.V) (f '' r.θ) = f '' t.θ
  rw [← hf.image_faceExt hdY hdX t.mem.1.1.1 ht hV r.mem_faces.1,
    (cls_eq_iff_faceExt hdY hx hV).1 hrt]

theorem map_cls_congr {f f' : Y → X} {W W' : Set Y} (hf : IsDHomeoOn dY dX f W)
    (hf' : IsDHomeoOn dY dX f' W') (t : BTriple hdY) (ht : t.V ⊆ W) (ht' : t.V ⊆ W')
    (h : EqOn f f' t.V) : (t.map hdX hf ht).cls = (t.map hdX hf' ht').cls :=
  cls_congr hdX (h t.mem.2.1) h.image_eq (h.mono t.mem_faces.1.subset).image_eq

/-- **The class of the image depends only on the class and on the germ of `f`.** -/
theorem map_cls_eq {f f' : Y → X} {W W' : Set Y} (hf : IsDHomeoOn dY dX f W)
    (hf' : IsDHomeoOn dY dX f' W') {t t' : BTriple hdY} (ht : t.V ⊆ W) (ht' : t'.V ⊆ W')
    (htt' : t.cls = t'.cls) {N : Set Y} (hN : IsOpen N) (hxN : t.x ∈ N) (hff' : EqOn f f' N) :
    (t.map hdX hf ht).cls = (t'.map hdX hf' ht').cls := by
  have hx : t.x = t'.x := bMap_eq_of_cls_eq hdY htt'
  have hxt' : t.x ∈ t'.V := by rw [hx]; exact t'.mem.2.1
  obtain ⟨r, hr, -, hrV, -⟩ := t.exists_shrink hdY ((t.mem.1.1.1.inter t'.mem.1.1.1).inter hN)
    ⟨⟨t.mem.2.1, hxt'⟩, hxN⟩
  rw [← map_cls_eq_of_subset hdY hdX hf hr (fun z hz => (hrV hz).1.1) ht,
    ← map_cls_eq_of_subset hdY hdX hf' (hr.trans htt') (fun z hz => (hrV hz).1.2) ht']
  exact map_cls_congr hdY hdX hf hf' r _ _ (hff'.mono fun z hz => (hrV hz).2)

/-- `q ∈ bX` is **the image of `p ∈ bY` under `f`**: `p = [y, V, θ]` with `V` inside an open `W`
on which `f` is an index-preserving homeomorphism onto an open set, and `q = [f(y), f(V), f(θ)]`
(the recipe of 2021 (7.25), (7.27)–(7.29)). -/
def IsLiftOf (f : Y → X) (p : BSpace hdY) (q : BSpace hdX) : Prop :=
  ∃ (W : Set Y) (hf : IsDHomeoOn dY dX f W) (t : BTriple hdY) (ht : t.V ⊆ W),
    t.cls = p ∧ (t.map hdX hf ht).cls = q

variable {hdY hdX hdZ} in
theorem IsLiftOf.bMap_eq {f : Y → X} {p : BSpace hdY} {q : BSpace hdX}
    (h : IsLiftOf hdY hdX f p q) : bMap hdX q = f (bMap hdY p) := by
  obtain ⟨W, hf, t, ht, rfl, rfl⟩ := h
  rfl

variable {hdY hdX hdZ} in
/-- **Uniqueness**: lifts along maps with the same germ at `B(p)` agree. -/
theorem IsLiftOf.unique {f f' : Y → X} {p : BSpace hdY} {q q' : BSpace hdX}
    (h : IsLiftOf hdY hdX f p q) (h' : IsLiftOf hdY hdX f' p q')
    (hff' : f =ᶠ[𝓝 (bMap hdY p)] f') : q = q' := by
  obtain ⟨W, hf, t, ht, rfl, rfl⟩ := h
  obtain ⟨W', hf', t', ht', htt', rfl⟩ := h'
  obtain ⟨N, hN, hNo, hxN⟩ := eventually_nhds_iff.1 hff'
  exact map_cls_eq hdY hdX hf hf' ht ht' htt'.symm hNo hxN hN

/-- **Existence** of the lift of `p` along `f` near `B(p)`. -/
theorem exists_isLiftOf {f : Y → X} {W : Set Y} (hf : IsDHomeoOn dY dX f W) {p : BSpace hdY}
    (hp : bMap hdY p ∈ W) : ∃ q, IsLiftOf hdY hdX f p q := by
  obtain ⟨t, rfl⟩ := BSpace.exists_rep hdY p
  obtain ⟨t', ht', -, ht'W, -⟩ := t.exists_shrink hdY hf.isOpen hp
  exact ⟨_, W, hf, t', ht'W, ht', rfl⟩

theorem isLiftOf_id (p : BSpace hdY) : IsLiftOf hdY hdY id p p := by
  obtain ⟨t, rfl⟩ := BSpace.exists_rep hdY p
  exact ⟨univ, isDHomeoOn_id dY, t, subset_univ _, rfl, cls_congr hdY rfl (image_id _) (image_id _)⟩

variable {hdY hdX hdZ} in
/-- **Functoriality** of lifts. -/
theorem IsLiftOf.comp {f : Y → X} {g : X → Z} {p : BSpace hdY} {q : BSpace hdX}
    {r : BSpace hdZ} (h₁ : IsLiftOf hdY hdX f p q) (h₂ : IsLiftOf hdX hdZ g q r) :
    IsLiftOf hdY hdZ (g ∘ f) p r := by
  obtain ⟨W, hf, t, ht, rfl, rfl⟩ := h₁
  obtain ⟨W', hg, t', ht', ht'q, rfl⟩ := h₂
  have hx : t'.x = f t.x := bMap_eq_of_cls_eq hdX ht'q
  have hN : IsOpen (t.V ∩ f ⁻¹' W') :=
    (hf.continuousOn.mono ht).isOpen_inter_preimage t.mem.1.1.1 hg.isOpen
  obtain ⟨r, hr, -, hrN, -⟩ := t.exists_shrink hdY hN
    ⟨t.mem.2.1, by rw [mem_preimage, ← hx]; exact ht' t'.mem.2.1⟩
  have hrW : r.V ⊆ W := fun z hz => ht (hrN hz).1
  have hrf : MapsTo f r.V W' := fun z hz => (hrN hz).2
  have hgf : IsDHomeoOn dY dZ (g ∘ f) r.V := (hf.mono r.mem.1.1.1 hrW).comp hg hrf
  refine ⟨r.V, hgf, r, subset_rfl, hr, ?_⟩
  have h1 : (r.map hdX hf hrW).cls = t'.cls :=
    (map_cls_eq_of_subset hdY hdX hf hr (fun z hz => (hrN hz).1) ht).trans ht'q.symm
  have h2 := map_cls_eq hdX hdZ hg hg (image_subset_iff.2 hrf) ht' h1 isOpen_univ (mem_univ _)
    (fun _ _ => rfl)
  rw [← h2]
  exact cls_congr hdZ rfl (image_comp g f r.V) (image_comp g f r.θ)

theorem IsDLocalHomeo.exists_isLiftOf {f : Y → X} (hf : IsDLocalHomeo dY dX f)
    (p : BSpace hdY) : ∃ q, IsLiftOf hdY hdX f p q := by
  obtain ⟨W, hW, hfW⟩ := hf (bMap hdY p)
  exact TameBoundary.exists_isLiftOf hdY hdX hfW hW

/-- **The induced map `bf : bY → bX`** of an index-preserving local homeomorphism `f`:
`[y, V, θ] ↦ [f(y), f(V), f(θ)]` for `V` inside a domain of `f` (`bLift_cls`). -/
def bLift {f : Y → X} (hf : IsDLocalHomeo dY dX f) (p : BSpace hdY) : BSpace hdX :=
  (hf.exists_isLiftOf hdY hdX p).choose

theorem isLiftOf_bLift {f : Y → X} (hf : IsDLocalHomeo dY dX f) (p : BSpace hdY) :
    IsLiftOf hdY hdX f p (bLift hdY hdX hf p) :=
  (hf.exists_isLiftOf hdY hdX p).choose_spec

theorem bLift_eq {f : Y → X} (hf : IsDLocalHomeo dY dX f) {p : BSpace hdY} {q : BSpace hdX}
    (h : IsLiftOf hdY hdX f p q) : bLift hdY hdX hf p = q :=
  (isLiftOf_bLift hdY hdX hf p).unique h EventuallyEq.rfl

theorem bMap_bLift {f : Y → X} (hf : IsDLocalHomeo dY dX f) (p : BSpace hdY) :
    bMap hdX (bLift hdY hdX hf p) = f (bMap hdY p) :=
  (isLiftOf_bLift hdY hdX hf p).bMap_eq

/-- The formula `bf([y, V, θ]) = [f(y), f(V), f(θ)]` for `V` in a domain of `f`. -/
theorem bLift_cls {f : Y → X} (hf : IsDLocalHomeo dY dX f) {W : Set Y}
    (hfW : IsDHomeoOn dY dX f W) (t : BTriple hdY) (ht : t.V ⊆ W) :
    bLift hdY hdX hf t.cls = (t.map hdX hfW ht).cls :=
  bLift_eq hdY hdX hf ⟨W, hfW, t, ht, rfl, rfl⟩

/-- The image of `U(x, V, θ)` lies in `U(f(x), f(V), f(θ))` for `V` in a domain of `f`. -/
theorem exists_isLiftOf_mem_uSet {f : Y → X} {W : Set Y} (hf : IsDHomeoOn dY dX f W)
    {t : BTriple hdY} (ht : t.V ⊆ W) {q : BSpace hdY} (hq : q ∈ uSet hdY t) :
    ∃ q' ∈ uSet hdX (t.map hdX hf ht), IsLiftOf hdY hdX f q q' := by
  obtain ⟨r, rfl, hr1, hr2, hr3⟩ := hq
  have hrW : r.V ⊆ W := hr2.1.trans ht
  refine ⟨(r.map hdX hf hrW).cls, ⟨r.map hdX hf hrW, rfl, mem_image_of_mem f hr1,
    hf.isMor_image ht r.mem.2.1 hr2, ?_⟩, W, hf, r, hrW, rfl, rfl⟩
  change faceExt dX (f '' t.V) (f '' r.θ) = f '' t.θ
  rw [← hf.image_faceExt hdY hdX t.mem.1.1.1 ht hr2.1 r.mem_faces.1, hr3]

/-- `bf` is continuous. -/
theorem continuous_bLift {f : Y → X} (hf : IsDLocalHomeo dY dX f) :
    Continuous (bLift hdY hdX hf) := by
  refine ⟨fun O hO => (isOpen_iff_forall_uSet hdY).2 fun p hp => ?_⟩
  obtain ⟨t₀, ht₀, ht₀O⟩ := (isOpen_iff_forall_uSet hdX).1 hO _ hp
  obtain ⟨W, hyW, hfW⟩ := hf (bMap hdY p)
  have hx₀ : t₀.x = f (bMap hdY p) := by
    rw [← bMap_bLift hdY hdX hf p, ← ht₀]; rfl
  obtain ⟨t, rfl, htN, -, -⟩ := exists_rep_centered hdY p
    (hfW.continuousOn.isOpen_inter_preimage hfW.isOpen t₀.mem.1.1.1)
    ⟨hyW, by rw [mem_preimage, ← hx₀]; exact t₀.mem.2.1⟩ isOpen_univ (mem_univ _)
  have htW : t.V ⊆ W := fun z hz => (htN hz).1
  have hcls : (t.map hdX hfW htW).cls = t₀.cls := by
    rw [ht₀, ← bLift_cls hdY hdX hf hfW t htW]
  have hsub : (t.map hdX hfW htW).V ⊆ t₀.V := image_subset_iff.2 fun z hz => (htN hz).2
  have hx : (t.map hdX hfW htW).x = t₀.x := bMap_eq_of_cls_eq hdX hcls
  have hU : uSet hdX (t.map hdX hfW htW) ⊆ uSet hdX t₀ :=
    uSet_subset hdX (by rw [hx]; exact isMor_of_subset hsub t₀.mem)
      ((cls_eq_iff_faceExt hdX hx hsub).1 hcls)
  refine ⟨t, rfl, fun q hq => ?_⟩
  obtain ⟨q', hq', hqq'⟩ := exists_isLiftOf_mem_uSet hdY hdX hfW htW hq
  change bLift hdY hdX hf q ∈ O
  rw [bLift_eq hdY hdX hf hqq']
  exact ht₀O (hU hq')

/-- `bf` is injective on `U(x, V, θ)` for `V` in a domain of `f`. -/
theorem bLift_injOn_uSet {f : Y → X} (hf : IsDLocalHomeo dY dX f) {W : Set Y}
    (hfW : IsDHomeoOn dY dX f W) {t : BTriple hdY} (ht : t.V ⊆ W) :
    InjOn (bLift hdY hdX hf) (uSet hdY t) := by
  intro p₁ h₁ p₂ h₂ h
  have h' := congrArg (bMap hdX) h
  rw [bMap_bLift, bMap_bLift] at h'
  have hB : ∀ {p}, p ∈ uSet hdY t → bMap hdY p ∈ W := fun hp =>
    ht (t.mem_faces.1.subset (bMap_mem_of_mem_uSet hdY hp))
  exact bMap_injOn_uSet hdY t h₁ h₂ (hfW.injOn (hB h₁) (hB h₂) h')

/-- For `V` centred at `x` and inside a domain of `f`, `bf` maps `U(x, V, θ)` onto
`U(f(x), f(V), f(θ))`. -/
theorem image_bLift_uSet {f : Y → X} (hf : IsDLocalHomeo dY dX f) {W : Set Y}
    (hfW : IsDHomeoOn dY dX f W) {t : BTriple hdY} (ht : t.V ⊆ W)
    (hc : IsCenteredAt dY t.x t.V) :
    bLift hdY hdX hf '' uSet hdY t = uSet hdX (t.map hdX hfW ht) := by
  have hsub : bLift hdY hdX hf '' uSet hdY t ⊆ uSet hdX (t.map hdX hfW ht) := by
    rintro _ ⟨p, hp, rfl⟩
    obtain ⟨q', hq', hpq'⟩ := exists_isLiftOf_mem_uSet hdY hdX hfW ht hp
    rw [bLift_eq hdY hdX hf hpq']; exact hq'
  refine Subset.antisymm hsub fun q hq => ?_
  have hBq : bMap hdX q ∈ f '' t.θ := bMap_mem_of_mem_uSet hdX hq
  obtain ⟨z, hz, hzq⟩ := hBq
  rw [← bMap_image_uSet_of_isCenteredAt hdY hc] at hz
  obtain ⟨p, hp, rfl⟩ := hz
  refine ⟨p, hp, bMap_injOn_uSet hdX _ (hsub ⟨p, hp, rfl⟩) hq ?_⟩
  rw [bMap_bLift, hzq]

/-- `bf` is an open map. -/
theorem isOpenMap_bLift {f : Y → X} (hf : IsDLocalHomeo dY dX f) :
    IsOpenMap (bLift hdY hdX hf) := by
  intro O hO
  refine (isOpen_iff_forall_uSet hdX).2 ?_
  rintro _ ⟨p, hpO, rfl⟩
  obtain ⟨W, hyW, hfW⟩ := hf (bMap hdY p)
  obtain ⟨t, rfl, htW, hc, htO⟩ := exists_rep_centered hdY p hfW.isOpen hyW hO hpO
  refine ⟨t.map hdX hfW htW, (bLift_cls hdY hdX hf hfW t htW).symm, ?_⟩
  rw [← image_bLift_uSet hdY hdX hf hfW htW hc]
  exact image_mono htO

/-- **`bf` is a local homeomorphism.** -/
theorem isLocalHomeomorph_bLift {f : Y → X} (hf : IsDLocalHomeo dY dX f) :
    IsLocalHomeomorph (bLift hdY hdX hf) := by
  rw [isLocalHomeomorph_iff_isOpenEmbedding_restrict]
  intro p
  obtain ⟨W, hyW, hfW⟩ := hf (bMap hdY p)
  obtain ⟨t, rfl, htW, -, -⟩ := exists_rep_centered hdY p hfW.isOpen hyW isOpen_univ (mem_univ _)
  refine ⟨uSet hdY t, (isOpen_uSet hdY t).mem_nhds (cls_mem_uSet hdY t), ?_⟩
  refine IsOpenEmbedding.of_continuous_injective_isOpenMap
    ((continuous_bLift hdY hdX hf).comp continuous_subtype_val)
    (fun a b h => Subtype.ext (bLift_injOn_uSet hdY hdX hf hfW htW a.2 b.2 h)) ?_
  intro O hO
  obtain ⟨O', hO', rfl⟩ := isOpen_induced_iff.1 hO
  have : (uSet hdY t).domRestrict (bLift hdY hdX hf) '' (Subtype.val ⁻¹' O') =
      bLift hdY hdX hf '' (O' ∩ uSet hdY t) := by
    ext z
    constructor
    · rintro ⟨a, ha, rfl⟩; exact ⟨a, ⟨ha, a.2⟩, rfl⟩
    · rintro ⟨a, ⟨ha, hat⟩, rfl⟩; exact ⟨⟨a, hat⟩, ha, rfl⟩
  rw [this]
  exact isOpenMap_bLift hdY hdX hf _ (hO'.inter (isOpen_uSet hdY t))

end Lift

/-! ### Properness of `B` -/

section Proper

variable {X : Type u} [TopologicalSpace X] {d : X → ℕ} (hd : IsCornerIndex d)

/-- A closed set inside the open set `V` meets a face of `V` in a closed set. -/
theorem isClosed_inter_of_isFaceIn {V C θ : Set X} (hC : IsClosed C) (hCV : C ⊆ V)
    (hθ : IsFaceIn d V θ) : IsClosed (C ∩ θ) := by
  obtain ⟨p, -, -, rfl⟩ := hθ
  have : C ∩ faceAt d V p = C ∩ closure (connectedComponentIn (V ∩ {y | d y = 1}) p) := by
    ext z
    exact ⟨fun h => ⟨h.1, h.2.2⟩, fun h => ⟨h.1, hCV h.1, h.2⟩⟩
  rw [this]
  exact hC.inter isClosed_closure

/-- Preimages of compact sets under `B : bX → X` are compact (`X` regular). -/
theorem isCompact_preimage_bMap [RegularSpace X] {K : Set X} (hK : IsCompact K) :
    IsCompact (bMap hd ⁻¹' K) := by
  have key : ∀ x : X, ∃ C ∈ 𝓝 x, IsCompact (bMap hd ⁻¹' (K ∩ C)) := by
    intro x
    obtain ⟨V, hV⟩ := faceStructuredNbhdsAt_nonempty hd x
    have hW := reach_mem_faceStructuredNbhdsAt hd hV
    have hc := isCenteredAt_reach hd hV.1.1.1 hV.2.1
    obtain ⟨C, hCn, hCc, hCW⟩ := exists_mem_nhds_isClosed_subset (hW.1.1.1.mem_nhds hW.2.1)
    refine ⟨C, hCn, ?_⟩
    have hfin : Finite (facesThrough d (reach d V x) x) := by
      have : (facesThrough d (reach d V x) x).encard ≠ ⊤ := by
        rw [hW.1.1.2 x hW.2.1]; exact ENat.natCast_ne_top _
      exact (Set.encard_ne_top_iff.1 this).to_subtype
    let S : facesThrough d (reach d V x) x → Set (BSpace hd) := fun θ =>
      (fun z => ((phiHomeomorph hd (t := tripleOf hd hW θ) hc).symm z : BSpace hd)) ''
        {z | (z : X) ∈ K ∩ C}
    have hS : bMap hd ⁻¹' (K ∩ C) = ⋃ θ, S θ := by
      ext p
      constructor
      · intro hp
        obtain ⟨θ, hpθ⟩ := exists_mem_uSet_tripleOf hd hW hc (hCW hp.2)
        exact mem_iUnion.2 ⟨θ, phiHomeomorph hd (t := tripleOf hd hW θ) hc ⟨p, hpθ⟩, hp,
          congrArg Subtype.val
            ((phiHomeomorph hd (t := tripleOf hd hW θ) hc).symm_apply_apply ⟨p, hpθ⟩)⟩
      · intro hp
        obtain ⟨θ, z, hz, rfl⟩ := mem_iUnion.1 hp
        have h := congrArg Subtype.val
          ((phiHomeomorph hd (t := tripleOf hd hW θ) hc).apply_symm_apply z)
        change bMap hd ((phiHomeomorph hd (t := tripleOf hd hW θ) hc).symm z : BSpace hd) =
          (z : X) at h
        rw [mem_preimage, h]
        exact hz
    rw [hS]
    refine isCompact_iUnion fun θ => IsCompact.image ?_
      (continuous_subtype_val.comp (phiHomeomorph hd _).symm.continuous)
    rw [Subtype.isCompact_iff]
    have : ((↑) : (tripleOf hd hW θ).θ → X) '' {z | (z : X) ∈ K ∩ C} = K ∩ (C ∩ θ.1) := by
      ext y
      constructor
      · rintro ⟨z, hz, rfl⟩; exact ⟨hz.1, hz.2, z.2⟩
      · rintro ⟨hyK, hyC, hyθ⟩; exact ⟨⟨y, hyθ⟩, ⟨hyK, hyC⟩, rfl⟩
    rw [this]
    exact hK.inter_right (isClosed_inter_of_isFaceIn hCc hCW θ.2.1)
  choose C hC hCK using key
  obtain ⟨s, -, hs⟩ := hK.elim_nhds_subcover C fun x _ => hC x
  have : bMap hd ⁻¹' K = ⋃ x ∈ s, bMap hd ⁻¹' (K ∩ C x) := by
    ext p
    constructor
    · intro hp
      obtain ⟨x, hx, hpx⟩ := mem_iUnion₂.1 (hs hp)
      exact mem_iUnion₂.2 ⟨x, hx, hp, hpx⟩
    · intro hp
      obtain ⟨x, -, hpx⟩ := mem_iUnion₂.1 hp
      exact hpx.1
  rw [this]
  exact s.isCompact_biUnion fun x _ => hCK x

end Proper

end TameBoundary

/-! ### Sheets of local sc-diffeomorphisms -/

namespace MPolyfold

open TameBoundary

variable {A : Type u} [TopologicalSpace A] [T2Space A] [ParacompactSpace A] {P : MPolyfold A}
  {B : Type v} [TopologicalSpace B] [T2Space B] [ParacompactSpace B] {Q : MPolyfold B}

/-- An sc-diffeomorphism `f : U → V` between open sets is an index-preserving homeomorphism onto
an open set (Proposition 2.4.4 (2017: 2.7) [2.24] of the preprint, `proposition_2_4_4`, for the index). -/
theorem IsScDiffeoOn.isDHomeoOn {f : A → B} {g : B → A} {U : Set A} {V : Set B}
    (h : P.IsScDiffeoOn Q f g U V) : IsDHomeoOn P.degIndex Q.degIndex f U where
  isOpen := h.isOpen_source
  continuousOn := h.isScSmoothOn.continuousOn
  injOn := h.injOn
  isOpen_image U' hU' hsub := by
    rw [(h.restrict hU' hsub).image_eq]; exact (h.restrict hU' hsub).isOpen_target
  deg_eq _ hy := (proposition_2_4_4 h hy).symm

/-- A local sc-diffeomorphism is an index-preserving local homeomorphism. -/
theorem IsLocalScDiffeo.isDLocalHomeo {f : A → B} (hf : P.IsLocalScDiffeo Q f) :
    IsDLocalHomeo P.degIndex Q.degIndex f := fun y => by
  obtain ⟨U, V, g, hy, hd⟩ := hf y
  exact ⟨U, hy, hd.isDHomeoOn⟩

end MPolyfold

/-! ### The boundary groupoid of a tame ep-groupoid -/

namespace EpGroupoid

open TameBoundary MPolyfold

variable {Obj Mor : Type u} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] (X : EpGroupoid Obj Mor)

/-- 2021 §7.6.5.2, p. 353 (and the remark after 2021 Definition 7.1.6, p. 290): in a tame
ep-groupoid the morphism M-polyfold is tame as well, `s` being a local sc-diffeomorphism
(`MPolyfold.IsLocalScDiffeo.isTame`). -/
theorem isTame_PMor (hX : X.IsTame) : X.PMor.IsTame := X.isLocalScDiffeo_src.isTame hX

/-- The corner axioms for the degeneracy index of the object M-polyfold. -/
abbrev cornerObj (hX : X.IsTame) : IsCornerIndex X.PObj.degIndex :=
  X.PObj.isCornerIndex_degIndex hX

/-- The corner axioms for the degeneracy index of the morphism M-polyfold. -/
abbrev cornerMor (hX : X.IsTame) : IsCornerIndex X.PMor.degIndex :=
  X.PMor.isCornerIndex_degIndex (X.isTame_PMor hX)

/-- **2021 §7.6.5.2, p. 353**: `bX`, the tame boundary of the object M-polyfold (2021
Definition 2.7.10, `MPolyfold.TameBoundarySpace`). -/
abbrev bObj (hX : X.IsTame) : Type u := BSpace (X.cornerObj hX)

/-- **2021 §7.6.5.2, p. 353**: `b𝐗`, the tame boundary of the morphism M-polyfold. -/
abbrev bMor (hX : X.IsTame) : Type u := BSpace (X.cornerMor hX)

theorem isDLocalHomeo_src : IsDLocalHomeo X.PMor.degIndex X.PObj.degIndex X.src :=
  X.isLocalScDiffeo_src.isDLocalHomeo

theorem isDLocalHomeo_tgt : IsDLocalHomeo X.PMor.degIndex X.PObj.degIndex X.tgt :=
  X.isLocalScDiffeo_tgt.isDLocalHomeo

/-- `ι` is an sc-diffeomorphism of `𝐗` (an involution). -/
theorem isScDiffeoOn_inv : X.PMor.IsScDiffeoOn X.PMor X.inv X.inv univ univ :=
  ⟨X.isScSmoothMap_inv, X.isScSmoothMap_inv, mapsTo_univ _ _, mapsTo_univ _ _,
    fun φ _ => GroupoidStr.inv_inv (G := X.toGroupoidStr) φ,
    fun φ _ => GroupoidStr.inv_inv (G := X.toGroupoidStr) φ⟩

theorem isDLocalHomeo_inv : IsDLocalHomeo X.PMor.degIndex X.PMor.degIndex X.inv :=
  fun φ => ⟨univ, mem_univ φ, X.isScDiffeoOn_inv.isDHomeoOn⟩

/-- `u` is an index-preserving homeomorphism onto the open set `u(X)` (a continuous section of the
local homeomorphism `s` is an open embedding). -/
theorem isDHomeoOn_unit : IsDHomeoOn X.PObj.degIndex X.PMor.degIndex X.unit univ where
  isOpen := isOpen_univ
  continuousOn := X.continuous_unit.continuousOn
  injOn a _ b _ h := by rw [← X.src_unit a, h, X.src_unit]
  isOpen_image O hO _ := by
    refine isOpen_iff_forall_mem_open.2 ?_
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨W, V, σ, hW, hd⟩ := X.isLocalScDiffeo_src (X.unit x)
    refine ⟨W ∩ X.src ⁻¹' (O ∩ X.unit ⁻¹' W), ?_, ?_, hW, ?_⟩
    · rintro χ ⟨hχW, hχO, hχu⟩
      refine ⟨X.src χ, hχO, hd.injOn hχu hχW ?_⟩
      rw [X.src_unit]
    · exact hd.isOpen_source.inter (X.continuous_src.isOpen_preimage _
        (hO.inter (X.continuous_unit.isOpen_preimage W hd.isOpen_source)))
    · change X.src (X.unit x) ∈ O ∧ X.unit (X.src (X.unit x)) ∈ W
      rw [X.src_unit]; exact ⟨hx, hW⟩
  deg_eq x _ := by rw [X.degIndex_src, X.src_unit]

theorem isDLocalHomeo_unit : IsDLocalHomeo X.PObj.degIndex X.PMor.degIndex X.unit :=
  fun x => ⟨univ, mem_univ x, X.isDHomeoOn_unit⟩

/-- **2021 (7.25), p. 354**: the source map `s : b𝐗 → bX`,
`s([φ, 𝐕, θ]) = [s(φ), s(𝐕), s(θ)]` for `𝐕` so small that `s|𝐕` is an sc-diffeomorphism
(`bSrc_cls`). -/
def bSrc (hX : X.IsTame) : X.bMor hX → X.bObj hX :=
  bLift (X.cornerMor hX) (X.cornerObj hX) X.isDLocalHomeo_src

/-- **2021 (7.25), p. 354**: the target map `t : b𝐗 → bX`. -/
def bTgt (hX : X.IsTame) : X.bMor hX → X.bObj hX :=
  bLift (X.cornerMor hX) (X.cornerObj hX) X.isDLocalHomeo_tgt

/-- **2021 (7.27), p. 354**: the inversion `ι([φ, 𝐕, θ]) = [φ⁻¹, 𝐕⁻¹, θ⁻¹]` (`bInv_cls`). -/
def bInv (hX : X.IsTame) : X.bMor hX → X.bMor hX :=
  bLift (X.cornerMor hX) (X.cornerMor hX) X.isDLocalHomeo_inv

/-- **2021 (7.28), p. 354**: the unit map `u([x, V, θ]) = [1_x, 𝐕, θ̄]`, `θ̄ = (s|𝐕)⁻¹(θ)`
(`bUnit_cls`). -/
def bUnit (hX : X.IsTame) : X.bObj hX → X.bMor hX :=
  bLift (X.cornerObj hX) (X.cornerMor hX) X.isDLocalHomeo_unit

variable {X}

theorem isLiftOf_bSrc (hX : X.IsTame) (a : X.bMor hX) :
    IsLiftOf (X.cornerMor hX) (X.cornerObj hX) X.src a (X.bSrc hX a) :=
  isLiftOf_bLift _ _ _ a

theorem isLiftOf_bTgt (hX : X.IsTame) (a : X.bMor hX) :
    IsLiftOf (X.cornerMor hX) (X.cornerObj hX) X.tgt a (X.bTgt hX a) :=
  isLiftOf_bLift _ _ _ a

theorem isLiftOf_bInv (hX : X.IsTame) (a : X.bMor hX) :
    IsLiftOf (X.cornerMor hX) (X.cornerMor hX) X.inv a (X.bInv hX a) :=
  isLiftOf_bLift _ _ _ a

theorem isLiftOf_bUnit (hX : X.IsTame) (p : X.bObj hX) :
    IsLiftOf (X.cornerObj hX) (X.cornerMor hX) X.unit p (X.bUnit hX p) :=
  isLiftOf_bLift _ _ _ p

theorem bMap_bSrc (hX : X.IsTame) (a : X.bMor hX) :
    bMap (X.cornerObj hX) (X.bSrc hX a) = X.src (bMap (X.cornerMor hX) a) := bMap_bLift _ _ _ a

theorem bMap_bTgt (hX : X.IsTame) (a : X.bMor hX) :
    bMap (X.cornerObj hX) (X.bTgt hX a) = X.tgt (bMap (X.cornerMor hX) a) := bMap_bLift _ _ _ a

theorem bMap_bInv (hX : X.IsTame) (a : X.bMor hX) :
    bMap (X.cornerMor hX) (X.bInv hX a) = X.inv (bMap (X.cornerMor hX) a) := bMap_bLift _ _ _ a

theorem bMap_bUnit (hX : X.IsTame) (p : X.bObj hX) :
    bMap (X.cornerMor hX) (X.bUnit hX p) = X.unit (bMap (X.cornerObj hX) p) := bMap_bLift _ _ _ p

theorem src_eq_tgt_of_bSrc_eq (hX : X.IsTame) {a b : X.bMor hX}
    (h : X.bSrc hX a = X.bTgt hX b) :
    X.src (bMap (X.cornerMor hX) a) = X.tgt (bMap (X.cornerMor hX) b) := by
  rw [← bMap_bSrc, ← bMap_bTgt, h]

/-- A local inverse `σ` of `s` (a sheet `s : W → V`) lifts `s(c)` back to `c`. -/
theorem isLiftOf_sheet (hX : X.IsTame) {W : Set Mor} {V : Set Obj} {σ : Obj → Mor}
    (hd : X.PMor.IsScDiffeoOn X.PObj X.src σ W V) {c : X.bMor hX}
    (hc : bMap (X.cornerMor hX) c ∈ W) :
    IsLiftOf (X.cornerObj hX) (X.cornerMor hX) σ (X.bSrc hX c) c := by
  obtain ⟨q, hq⟩ := exists_isLiftOf (X.cornerObj hX) (X.cornerMor hX) hd.symm.isDHomeoOn
    (p := X.bSrc hX c) (by rw [bMap_bSrc]; exact hd.mapsTo hc)
  have h1 := (isLiftOf_bSrc hX c).comp hq
  have : q = c := h1.unique (isLiftOf_id (X.cornerMor hX) c)
    (eventuallyEq_of_mem (hd.isOpen_source.mem_nhds hc) fun φ hφ => hd.left_inv φ hφ)
  rwa [this] at hq

/-- **`(B, s)` is injective on `b𝐗`**: a class over `φ` is determined by its source. -/
theorem eq_of_bMap_eq_of_bSrc_eq (hX : X.IsTame) {c c' : X.bMor hX}
    (hB : bMap (X.cornerMor hX) c = bMap (X.cornerMor hX) c') (hs : X.bSrc hX c = X.bSrc hX c') :
    c = c' := by
  obtain ⟨W, V, σ, hW, hd⟩ := X.isLocalScDiffeo_src (bMap (X.cornerMor hX) c)
  have h1 := isLiftOf_sheet hX hd hW
  have h2 := isLiftOf_sheet hX hd (c := c') (hB ▸ hW)
  rw [hs] at h1
  exact h1.unique h2 EventuallyEq.rfl

/-- For composable `[ψ, 𝐖, σ]`, `[φ, 𝐕, θ]` there is a class over `ψ ∘ φ` with the source of
`[φ, 𝐕, θ]` (it is unique, `eq_of_bMap_eq_of_bSrc_eq`). -/
theorem exists_bComp (hX : X.IsTame) {a b : X.bMor hX} (hab : X.bSrc hX a = X.bTgt hX b) :
    ∃ c, bMap (X.cornerMor hX) c = X.comp (bMap (X.cornerMor hX) a) (bMap (X.cornerMor hX) b) ∧
      X.bSrc hX c = X.bSrc hX b := by
  have hsψ := src_eq_tgt_of_bSrc_eq hX hab
  obtain ⟨W, V, σ, hW, hd⟩ :=
    X.isLocalScDiffeo_src (X.comp (bMap (X.cornerMor hX) a) (bMap (X.cornerMor hX) b))
  have hsrc := X.src_comp _ _ hsψ
  obtain ⟨c, hc⟩ := exists_isLiftOf (X.cornerObj hX) (X.cornerMor hX) hd.symm.isDHomeoOn
    (p := X.bSrc hX b) (by rw [bMap_bSrc, ← hsrc]; exact hd.mapsTo hW)
  refine ⟨c, ?_, ?_⟩
  · rw [hc.bMap_eq, bMap_bSrc, ← hsrc, hd.left_inv _ hW]
  · have h1 := hc.comp (isLiftOf_bSrc hX c)
    refine h1.unique (isLiftOf_id (X.cornerObj hX) (X.bSrc hX b))
      (eventuallyEq_of_mem (hd.isOpen_target.mem_nhds ?_) fun y hy => hd.right_inv y hy)
    rw [bMap_bSrc, ← hsrc]; exact hd.mapsTo hW

variable (X) in
open scoped Classical in
/-- **2021 (7.29), p. 355**: the multiplication `m([ψ, 𝐖, σ], [φ, 𝐕, θ])`, the unique class over
`ψ ∘ φ` whose source is `s([φ, 𝐕, θ])`; it is the text's `[ψ ∘ φ, 𝐖 ₛ∘ₜ 𝐕, σ ₛ∘ₜ θ]`
(`bComp_cls`).  Off composable pairs it takes the junk value `[φ, 𝐕, θ]`. -/
def bComp (hX : X.IsTame) (a b : X.bMor hX) : X.bMor hX :=
  if h : ∃ c, bMap (X.cornerMor hX) c = X.comp (bMap (X.cornerMor hX) a) (bMap (X.cornerMor hX) b) ∧
      X.bSrc hX c = X.bSrc hX b then h.choose else b

theorem bComp_spec (hX : X.IsTame) {a b : X.bMor hX} (hab : X.bSrc hX a = X.bTgt hX b) :
    bMap (X.cornerMor hX) (X.bComp hX a b) =
        X.comp (bMap (X.cornerMor hX) a) (bMap (X.cornerMor hX) b) ∧
      X.bSrc hX (X.bComp hX a b) = X.bSrc hX b := by
  rw [bComp, dif_pos (exists_bComp hX hab)]
  exact (exists_bComp hX hab).choose_spec

/-- Near `φ` the map `γ ↦ (s|𝐖)⁻¹(t(γ)) ∘ γ` of (7.29) agrees with `(s|𝐔)⁻¹ ∘ s` for a sheet
`𝐔 ∋ ψ ∘ φ` of `s`. -/
theorem eventuallyEq_comp_sheet {ψ φ : Mor} (hsψ : X.src ψ = X.tgt φ) {W₁ : Set Mor}
    {V₁ : Set Obj} {σ₁ : Obj → Mor} (hd₁ : X.PMor.IsScDiffeoOn X.PObj X.src σ₁ W₁ V₁)
    (hψ : ψ ∈ W₁) {W₂ : Set Mor} {V₂ : Set Obj} {σ₂ : Obj → Mor}
    (hd₂ : X.PMor.IsScDiffeoOn X.PObj X.src σ₂ W₂ V₂) (hψφ : X.comp ψ φ ∈ W₂) :
    ∀ᶠ γ in 𝓝 φ, X.tgt γ ∈ V₁ ∧ X.comp (σ₁ (X.tgt γ)) γ ∈ W₂ ∧
      σ₂ (X.src γ) = X.comp (σ₁ (X.tgt γ)) γ := by
  have hφV : X.tgt φ ∈ V₁ := by rw [← hsψ]; exact hd₁.mapsTo hψ
  have hM : ContinuousAt (fun γ => X.comp (σ₁ (X.tgt γ)) γ) φ :=
    (X.isScSmoothCompSheet σ₁ W₁ V₁ hd₁).continuousOn.continuousAt
      ((hd₁.isOpen_target.preimage X.continuous_tgt).mem_nhds hφV)
  have hMφ : X.comp (σ₁ (X.tgt φ)) φ = X.comp ψ φ := by rw [← hsψ, hd₁.left_inv ψ hψ]
  have h1 : ∀ᶠ γ in 𝓝 φ, X.comp (σ₁ (X.tgt γ)) γ ∈ W₂ :=
    hM.preimage_mem_nhds (by rw [hMφ]; exact hd₂.isOpen_source.mem_nhds hψφ)
  have h2 : ∀ᶠ γ in 𝓝 φ, X.tgt γ ∈ V₁ :=
    X.continuous_tgt.continuousAt.preimage_mem_nhds (hd₁.isOpen_target.mem_nhds hφV)
  filter_upwards [h1, h2] with γ hγ1 hγ2
  refine ⟨hγ2, hγ1, ?_⟩
  have hs : X.src (X.comp (σ₁ (X.tgt γ)) γ) = X.src γ := X.src_comp _ _ (hd₁.right_inv _ hγ2)
  rw [← hs, hd₂.left_inv _ hγ1]

/-- `t(m(a, b)) = t(a)`. -/
theorem bTgt_bComp (hX : X.IsTame) {a b : X.bMor hX} (hab : X.bSrc hX a = X.bTgt hX b) :
    X.bTgt hX (X.bComp hX a b) = X.bTgt hX a := by
  obtain ⟨hcB, hcs⟩ := bComp_spec hX hab
  have hsψ := src_eq_tgt_of_bSrc_eq hX hab
  obtain ⟨W₁, V₁, σ₁, hW₁, hd₁⟩ := X.isLocalScDiffeo_src (bMap (X.cornerMor hX) a)
  obtain ⟨W₂, V₂, σ₂, hW₂, hd₂⟩ :=
    X.isLocalScDiffeo_src (X.comp (bMap (X.cornerMor hX) a) (bMap (X.cornerMor hX) b))
  have ha := isLiftOf_sheet hX hd₁ hW₁
  rw [hab] at ha
  have hc := isLiftOf_sheet hX hd₂ (c := X.bComp hX a b) (hcB ▸ hW₂)
  rw [hcs] at hc
  have hTa := (isLiftOf_bTgt hX b).comp
    (ha.comp (isLiftOf_bTgt hX a))
  have hTc := ((isLiftOf_bSrc hX b).comp hc).comp
    (isLiftOf_bTgt hX (X.bComp hX a b))
  refine hTc.unique hTa ?_
  filter_upwards [eventuallyEq_comp_sheet hsψ hd₁ hW₁ hd₂ hW₂] with γ hγ
  obtain ⟨hγ1, -, hγ3⟩ := hγ
  change X.tgt (σ₂ (X.src γ)) = X.tgt (σ₁ (X.tgt γ))
  rw [hγ3, X.tgt_comp _ _ (hd₁.right_inv _ hγ1)]

theorem bSrc_bUnit (hX : X.IsTame) (p : X.bObj hX) : X.bSrc hX (X.bUnit hX p) = p :=
  ((isLiftOf_bUnit hX p).comp
    (isLiftOf_bSrc hX _)).unique (isLiftOf_id (X.cornerObj hX) p)
    (Filter.Eventually.of_forall fun x => X.src_unit x)

theorem bTgt_bUnit (hX : X.IsTame) (p : X.bObj hX) : X.bTgt hX (X.bUnit hX p) = p :=
  ((isLiftOf_bUnit hX p).comp
    (isLiftOf_bTgt hX _)).unique (isLiftOf_id (X.cornerObj hX) p)
    (Filter.Eventually.of_forall fun x => X.tgt_unit x)

theorem bSrc_bInv (hX : X.IsTame) (a : X.bMor hX) : X.bSrc hX (X.bInv hX a) = X.bTgt hX a :=
  ((isLiftOf_bInv hX a).comp
    (isLiftOf_bSrc hX _)).unique
    (isLiftOf_bTgt hX a) (Filter.Eventually.of_forall fun φ => X.src_inv φ)

theorem bTgt_bInv (hX : X.IsTame) (a : X.bMor hX) : X.bTgt hX (X.bInv hX a) = X.bSrc hX a :=
  ((isLiftOf_bInv hX a).comp
    (isLiftOf_bTgt hX _)).unique
    (isLiftOf_bSrc hX a) (Filter.Eventually.of_forall fun φ => X.tgt_inv φ)

variable (X) in
/-- **2021 Theorem 7.6.9 (5)**, the groupoid part: `(bX, b𝐗)` with `s, t, m, u, ι` of
(7.25)–(7.29) is a groupoid. -/
def boundaryGroupoid (hX : X.IsTame) : GroupoidStr (X.bObj hX) (X.bMor hX) where
  src := X.bSrc hX
  tgt := X.bTgt hX
  comp := X.bComp hX
  unit := X.bUnit hX
  inv := X.bInv hX
  src_comp _ _ h := (bComp_spec hX h).2
  tgt_comp _ _ h := bTgt_bComp hX h
  comp_assoc a b c h₁ h₂ := by
    have h₃ : X.bSrc hX (X.bComp hX a b) = X.bTgt hX c := (bComp_spec hX h₁).2.trans h₂
    have h₄ : X.bSrc hX a = X.bTgt hX (X.bComp hX b c) := h₁.trans (bTgt_bComp hX h₂).symm
    refine eq_of_bMap_eq_of_bSrc_eq hX ?_ ?_
    · rw [(bComp_spec hX h₃).1, (bComp_spec hX h₁).1, (bComp_spec hX h₄).1, (bComp_spec hX h₂).1,
        X.comp_assoc _ _ _ (src_eq_tgt_of_bSrc_eq hX h₁) (src_eq_tgt_of_bSrc_eq hX h₂)]
    · rw [(bComp_spec hX h₃).2, (bComp_spec hX h₄).2, (bComp_spec hX h₂).2]
  src_unit := bSrc_bUnit hX
  tgt_unit := bTgt_bUnit hX
  comp_unit a := by
    have h : X.bSrc hX a = X.bTgt hX (X.bUnit hX (X.bSrc hX a)) := (bTgt_bUnit hX _).symm
    refine eq_of_bMap_eq_of_bSrc_eq hX ?_ ?_
    · rw [(bComp_spec hX h).1, bMap_bUnit, bMap_bSrc, X.comp_unit]
    · rw [(bComp_spec hX h).2, bSrc_bUnit]
  unit_comp a := by
    have h : X.bSrc hX (X.bUnit hX (X.bTgt hX a)) = X.bTgt hX a := bSrc_bUnit hX _
    refine eq_of_bMap_eq_of_bSrc_eq hX ?_ ?_
    · rw [(bComp_spec hX h).1, bMap_bUnit, bMap_bTgt, X.unit_comp]
    · rw [(bComp_spec hX h).2]
  src_inv := bSrc_bInv hX
  tgt_inv := bTgt_bInv hX
  comp_inv a := by
    have h : X.bSrc hX a = X.bTgt hX (X.bInv hX a) := (bTgt_bInv hX a).symm
    refine eq_of_bMap_eq_of_bSrc_eq hX ?_ ?_
    · rw [(bComp_spec hX h).1, bMap_bInv, bMap_bUnit, bMap_bTgt, X.comp_inv]
    · rw [(bComp_spec hX h).2, bSrc_bInv, bSrc_bUnit]
  inv_comp a := by
    have h : X.bSrc hX (X.bInv hX a) = X.bTgt hX a := bSrc_bInv hX a
    refine eq_of_bMap_eq_of_bSrc_eq hX ?_ ?_
    · rw [(bComp_spec hX h).1, bMap_bInv, bMap_bUnit, bMap_bSrc, X.inv_comp]
    · rw [(bComp_spec hX h).2, bSrc_bUnit]


theorem bInv_bInv (hX : X.IsTame) (a : X.bMor hX) : X.bInv hX (X.bInv hX a) = a :=
  GroupoidStr.inv_inv (G := X.boundaryGroupoid hX) a

/-- `m` is determined by `B(m(a, b)) = B(a) ∘ B(b)` and `s(m(a, b)) = s(b)`. -/
theorem bComp_eq (hX : X.IsTame) {a b c : X.bMor hX} (hab : X.bSrc hX a = X.bTgt hX b)
    (hB : bMap (X.cornerMor hX) c =
      X.comp (bMap (X.cornerMor hX) a) (bMap (X.cornerMor hX) b))
    (hs : X.bSrc hX c = X.bSrc hX b) : X.bComp hX a b = c :=
  eq_of_bMap_eq_of_bSrc_eq hX ((bComp_spec hX hab).1.trans hB.symm)
    ((bComp_spec hX hab).2.trans hs.symm)

/-! #### The formulas (7.25), (7.27) and (7.28) -/

/-- **2021 (7.25), p. 354**: `s([φ, 𝐕, θ]) = [s(φ), s(𝐕), s(θ)]` when `s|𝐖` is an
sc-diffeomorphism onto an open set and `𝐕 ⊆ 𝐖`. -/
theorem bSrc_cls (hX : X.IsTame) {W : Set Mor} {V : Set Obj} {σ : Obj → Mor}
    (hd : X.PMor.IsScDiffeoOn X.PObj X.src σ W V) (t : BTriple (X.cornerMor hX))
    (ht : t.V ⊆ W) : X.bSrc hX t.cls = (t.map (X.cornerObj hX) hd.isDHomeoOn ht).cls :=
  bLift_cls _ _ _ hd.isDHomeoOn t ht

/-- **2021 (7.25), p. 354**: `t([φ, 𝐕, θ]) = [t(φ), t(𝐕), t(θ)]` when `t|𝐖` is an
sc-diffeomorphism onto an open set and `𝐕 ⊆ 𝐖`. -/
theorem bTgt_cls (hX : X.IsTame) {W : Set Mor} {V : Set Obj} {τ : Obj → Mor}
    (hd : X.PMor.IsScDiffeoOn X.PObj X.tgt τ W V) (t : BTriple (X.cornerMor hX))
    (ht : t.V ⊆ W) : X.bTgt hX t.cls = (t.map (X.cornerObj hX) hd.isDHomeoOn ht).cls :=
  bLift_cls _ _ _ hd.isDHomeoOn t ht

/-- **2021 (7.27), p. 354**: `ι([φ, 𝐕, θ]) = [φ⁻¹, 𝐕⁻¹, θ⁻¹]`. -/
theorem bInv_cls (hX : X.IsTame) (t : BTriple (X.cornerMor hX)) :
    X.bInv hX t.cls =
      (t.map (X.cornerMor hX) X.isScDiffeoOn_inv.isDHomeoOn (subset_univ _)).cls :=
  bLift_cls _ _ _ _ t _

/-- **2021 (7.28), p. 354**: `u([x, V, θ]) = [1ₓ, 𝐕, θ̄]`, where `s : 𝐖 → V'` is an
sc-diffeomorphism with `1ₓ ∈ 𝐖` and `V ⊆ V'`, `𝐕 = (s|𝐖)⁻¹(V)` and `θ̄ = (s|𝐖)⁻¹(θ)`; the
point of the new triple is `(s|𝐖)⁻¹(x) = 1ₓ`. -/
theorem bUnit_cls (hX : X.IsTame) {W : Set Mor} {V' : Set Obj} {σ : Obj → Mor}
    (hd : X.PMor.IsScDiffeoOn X.PObj X.src σ W V') (t : BTriple (X.cornerObj hX))
    (hx : X.unit t.x ∈ W) (ht : t.V ⊆ V') :
    σ t.x = X.unit t.x ∧
      X.bUnit hX t.cls = (t.map (X.cornerMor hX) hd.symm.isDHomeoOn ht).cls := by
  have heq : ∀ y ∈ V' ∩ X.unit ⁻¹' W, X.unit y = σ y := fun y hy =>
    hd.injOn hy.2 (hd.mapsTo_inv hy.1) (by rw [X.src_unit, hd.right_inv y hy.1])
  have hxV : t.x ∈ V' ∩ X.unit ⁻¹' W := ⟨ht t.mem.2.1, hx⟩
  refine ⟨(heq t.x hxV).symm, (isLiftOf_bUnit hX t.cls).unique
    ⟨V', hd.symm.isDHomeoOn, t, ht, rfl, rfl⟩ (eventuallyEq_of_mem ?_ heq)⟩
  exact (hd.isOpen_target.inter (X.continuous_unit.isOpen_preimage W hd.isOpen_source)).mem_nhds
    hxV

/-! #### The topology of the boundary groupoid -/

theorem continuous_bSrc (hX : X.IsTame) : Continuous (X.bSrc hX) := continuous_bLift _ _ _

theorem continuous_bTgt (hX : X.IsTame) : Continuous (X.bTgt hX) := continuous_bLift _ _ _

theorem continuous_bInv (hX : X.IsTame) : Continuous (X.bInv hX) := continuous_bLift _ _ _

theorem continuous_bUnit (hX : X.IsTame) : Continuous (X.bUnit hX) := continuous_bLift _ _ _

/-- `s : b𝐗 → bX` is a local homeomorphism (the topological content of "étale"). -/
theorem isLocalHomeomorph_bSrc (hX : X.IsTame) : IsLocalHomeomorph (X.bSrc hX) :=
  isLocalHomeomorph_bLift _ _ _

/-- `t : b𝐗 → bX` is a local homeomorphism. -/
theorem isLocalHomeomorph_bTgt (hX : X.IsTame) : IsLocalHomeomorph (X.bTgt hX) :=
  isLocalHomeomorph_bLift _ _ _

/-- `m` is continuous on the composable pairs `b𝐗 ₛ×ₜ b𝐗`. -/
theorem continuousOn_bComp (hX : X.IsTame) :
    ContinuousOn (fun p : X.bMor hX × X.bMor hX => X.bComp hX p.1 p.2)
      {p | X.bSrc hX p.1 = X.bTgt hX p.2} := by
  rw [continuousOn_iff]
  rintro ⟨a, b⟩ hab O hO hcO
  change X.bSrc hX a = X.bTgt hX b at hab
  change X.bComp hX a b ∈ O at hcO
  obtain ⟨hcB, hcs⟩ := bComp_spec hX hab
  have hsψ := src_eq_tgt_of_bSrc_eq hX hab
  obtain ⟨W₁, V₁, σ₁, hW₁, hd₁⟩ := X.isLocalScDiffeo_src (bMap (X.cornerMor hX) a)
  obtain ⟨W₂, V₂, σ₂, hW₂, hd₂⟩ :=
    X.isLocalScDiffeo_src (X.comp (bMap (X.cornerMor hX) a) (bMap (X.cornerMor hX) b))
  obtain ⟨E, hE, hEo, hbE⟩ :=
    eventually_nhds_iff.1 (eventuallyEq_comp_sheet hsψ hd₁ hW₁ hd₂ hW₂)
  obtain ⟨t, htc, htW, -, htO⟩ := exists_rep_centered (X.cornerMor hX) (X.bComp hX a b)
    hd₂.isOpen_source (by rw [hcB]; exact hW₂) hO hcO
  have hSo : IsOpen (X.bSrc hX '' uSet (X.cornerMor hX) t) :=
    isOpenMap_bLift _ _ _ _ (isOpen_uSet _ t)
  refine ⟨(bMap (X.cornerMor hX) ⁻¹' W₁) ×ˢ
    (bMap (X.cornerMor hX) ⁻¹' E ∩ X.bSrc hX ⁻¹' (X.bSrc hX '' uSet (X.cornerMor hX) t)),
    ?_, ?_, ?_⟩
  · exact ((continuous_bMap _).isOpen_preimage _ hd₁.isOpen_source).prod
      (((continuous_bMap _).isOpen_preimage _ hEo).inter
        ((continuous_bSrc hX).isOpen_preimage _ hSo))
  · refine ⟨hW₁, hbE, t.cls, cls_mem_uSet _ t, ?_⟩
    rw [htc, hcs]
  · rintro ⟨a', b'⟩ ⟨⟨ha'W, hb'E, p, hp, hps⟩, hab'⟩
    change X.bSrc hX a' = X.bTgt hX b' at hab'
    change X.bComp hX a' b' ∈ O
    obtain ⟨-, -, hE3⟩ := hE _ hb'E
    obtain ⟨hcB', hcs'⟩ := bComp_spec hX hab'
    have hpW : bMap (X.cornerMor hX) p ∈ W₂ :=
      htW (t.mem_faces.1.subset (bMap_mem_of_mem_uSet _ hp))
    suffices X.bComp hX a' b' = p from this ▸ htO hp
    refine eq_of_bMap_eq_of_bSrc_eq hX ?_ (hcs'.trans hps.symm)
    rw [hcB', ← hd₂.left_inv _ hpW, ← bMap_bSrc, hps, bMap_bSrc, hE3,
      ← src_eq_tgt_of_bSrc_eq hX hab', hd₁.left_inv _ ha'W]

theorem metrizableSpace_bObj (hX : X.IsTame) : TopologicalSpace.MetrizableSpace (X.bObj hX) := by
  have := X.PObj.metrizableSpace
  exact Polyfold.TameBoundary.proposition_2_7_16 _

theorem metrizableSpace_bMor (hX : X.IsTame) : TopologicalSpace.MetrizableSpace (X.bMor hX) := by
  have := X.PMor.metrizableSpace
  exact Polyfold.TameBoundary.proposition_2_7_16 _

variable (X) in
/-- **2021 Theorem 7.6.9 (3)–(5)**, the functor part: `B : (bX, b𝐗) → (X, 𝐗)` is a functor. -/
def boundaryFunctor (hX : X.IsTame) : GroupoidFunctor (X.boundaryGroupoid hX) X.toGroupoidStr where
  obj := bMap (X.cornerObj hX)
  mor := bMap (X.cornerMor hX)
  src_mor a := (bMap_bSrc hX a).symm
  tgt_mor a := (bMap_bTgt hX a).symm
  mor_comp _ _ h := (bComp_spec hX h).1
  mor_unit p := bMap_bUnit hX p


/-- The properness property of 2021 Definition 7.1.3 (3), p. 289 (2017: Definition 7.3 (3)), for
`(bX, b𝐗)`: every class has an open neighbourhood `V` with `t : s⁻¹(cl V) → bX` proper. -/
theorem exists_isProperMap_bTgt (hX : X.IsTame) (p : X.bObj hX) :
    ∃ V : Set (X.bObj hX), IsOpen V ∧ p ∈ V ∧
      IsProperMap ((X.bSrc hX ⁻¹' closure V).domRestrict (X.bTgt hX)) := by
  have := X.PObj.metrizableSpace
  have := X.PMor.metrizableSpace
  have := metrizableSpace_bObj hX
  obtain ⟨V, hVo, hpV, hV⟩ := X.exists_isProperMap (bMap (X.cornerObj hX) p)
  refine ⟨bMap (X.cornerObj hX) ⁻¹' V, (continuous_bMap _).isOpen_preimage _ hVo, hpV, ?_⟩
  rw [isProperMap_iff_isCompact_preimage]
  refine ⟨(continuous_bTgt hX).comp continuous_subtype_val, fun K hK => ?_⟩
  rw [Subtype.isCompact_iff]
  have himg : Subtype.val '' ((X.bSrc hX ⁻¹' closure (bMap (X.cornerObj hX) ⁻¹' V)).domRestrict
      (X.bTgt hX) ⁻¹' K) =
      X.bSrc hX ⁻¹' closure (bMap (X.cornerObj hX) ⁻¹' V) ∩ X.bTgt hX ⁻¹' K := by
    ext a
    constructor
    · rintro ⟨a, ha, rfl⟩; exact ⟨a.2, ha⟩
    · rintro ⟨h1, h2⟩; exact ⟨⟨a, h1⟩, h2, rfl⟩
  rw [himg]
  have hS : IsCompact (X.src ⁻¹' closure V ∩ X.tgt ⁻¹' (bMap (X.cornerObj hX) '' K)) := by
    have h := hV.isCompact_preimage (hK.image (continuous_bMap _))
    rw [Subtype.isCompact_iff] at h
    have : Subtype.val '' ((X.src ⁻¹' closure V).domRestrict X.tgt ⁻¹'
        (bMap (X.cornerObj hX) '' K)) =
        X.src ⁻¹' closure V ∩ X.tgt ⁻¹' (bMap (X.cornerObj hX) '' K) := by
      ext φ
      constructor
      · rintro ⟨φ, hφ, rfl⟩; exact ⟨φ.2, hφ⟩
      · rintro ⟨h1, h2⟩; exact ⟨⟨φ, h1⟩, h2, rfl⟩
    rwa [this] at h
  refine (isCompact_preimage_bMap (X.cornerMor hX) hS).of_isClosed_subset
    ((isClosed_closure.preimage (continuous_bSrc hX)).inter
      (hK.isClosed.preimage (continuous_bTgt hX))) ?_
  rintro a ⟨h1, h2⟩
  refine ⟨?_, X.bTgt hX a, h2, bMap_bTgt hX a⟩
  change X.src (bMap (X.cornerMor hX) a) ∈ closure V
  rw [← bMap_bSrc hX]
  exact (continuous_bMap _).closure_preimage_subset V h1

/-- **2021 Theorem 7.6.9, p. 355** (new in the 2021 edition), everything that does not need the
M-polyfold structures of `bX` and `b𝐗`: (1) metrizability, with the characterization of the
topologies (every `U` open, every `Φ` an open embedding, and uniqueness); (3) continuity of the
two maps `B`; (4) in counting form; (5) the groupoid `(bX, b𝐗)` of (7.25)–(7.29) with its
topological ep-groupoid properties (`s, t` local homeomorphisms, `u, ι, m` continuous, the
properness property) and `B` a functor.  Parts (2), the sc-smoothness in (3) and (5), and `d_{bX}`
in (4) are in `theorem_7_6_9_full` (`Chapter7/TameBoundaryEpStructure.lean`). -/
theorem theorem_7_6_9 (hX : X.IsTame) :
    -- (1), and the characterization of the topologies in the paragraph after the theorem
    TopologicalSpace.MetrizableSpace (X.bObj hX) ∧ TopologicalSpace.MetrizableSpace (X.bMor hX) ∧
      (∀ t, IsOpen (uSet (X.cornerObj hX) t) ∧ IsOpenEmbedding (phi (X.cornerObj hX) t)) ∧
      (∀ t, IsOpen (uSet (X.cornerMor hX) t) ∧ IsOpenEmbedding (phi (X.cornerMor hX) t)) ∧
      (∀ τ : TopologicalSpace (X.bObj hX), (∀ t, IsOpen[τ] (uSet (X.cornerObj hX) t)) →
        (∀ t U, IsOpen[τ] U → ∃ N, IsOpen N ∧
          bMap (X.cornerObj hX) '' (U ∩ uSet _ t) = N ∩ t.θ) →
        τ = bTopology (X.cornerObj hX)) ∧
      (∀ τ : TopologicalSpace (X.bMor hX), (∀ t, IsOpen[τ] (uSet (X.cornerMor hX) t)) →
        (∀ t U, IsOpen[τ] U → ∃ N, IsOpen N ∧
          bMap (X.cornerMor hX) '' (U ∩ uSet _ t) = N ∩ t.θ) →
        τ = bTopology (X.cornerMor hX)) ∧
      -- (3), the two maps `B` are continuous
      Continuous (bMap (X.cornerObj hX)) ∧ Continuous (bMap (X.cornerMor hX)) ∧
      -- (4), in counting form: a point of index `d` has `d` preimages under `B`
      (∀ x, (bMap (X.cornerObj hX) ⁻¹' {x}).encard = X.PObj.degIndex x) ∧
      (∀ φ, (bMap (X.cornerMor hX) ⁻¹' {φ}).encard = X.PMor.degIndex φ) ∧
      -- (5), the groupoid `(bX, b𝐗)`: `s, t` local homeomorphisms, `u, ι, m` continuous
      IsLocalHomeomorph (X.boundaryGroupoid hX).src ∧
      IsLocalHomeomorph (X.boundaryGroupoid hX).tgt ∧
      Continuous (X.boundaryGroupoid hX).unit ∧ Continuous (X.boundaryGroupoid hX).inv ∧
      ContinuousOn (fun p : X.bMor hX × X.bMor hX => (X.boundaryGroupoid hX).comp p.1 p.2)
        {p | (X.boundaryGroupoid hX).src p.1 = (X.boundaryGroupoid hX).tgt p.2} ∧
      -- the properness property of an ep-groupoid
      (∀ p, ∃ V : Set (X.bObj hX), IsOpen V ∧ p ∈ V ∧
        IsProperMap (((X.boundaryGroupoid hX).src ⁻¹' closure V).domRestrict
          (X.boundaryGroupoid hX).tgt)) ∧
      -- and `B : (bX, b𝐗) → (X, 𝐗)` is a functor
      ∃ F : GroupoidFunctor (X.boundaryGroupoid hX) X.toGroupoidStr,
        F.obj = bMap (X.cornerObj hX) ∧ F.mor = bMap (X.cornerMor hX) := by
  have := X.PObj.metrizableSpace
  have := X.PMor.metrizableSpace
  obtain ⟨m₀, u₀, p₀, e₀, c₀, -, f₀⟩ := theorem_2_7_13_topology (X.cornerObj hX)
  obtain ⟨m₁, u₁, p₁, e₁, c₁, -, f₁⟩ := theorem_2_7_13_topology (X.cornerMor hX)
  exact ⟨m₀, m₁, fun t => ⟨u₀ t, p₀ t⟩, fun t => ⟨u₁ t, p₁ t⟩, e₀, e₁, c₀, c₁, f₀, f₁,
    isLocalHomeomorph_bSrc hX, isLocalHomeomorph_bTgt hX, continuous_bUnit hX,
    continuous_bInv hX, continuousOn_bComp hX, exists_isProperMap_bTgt hX,
    X.boundaryFunctor hX, rfl, rfl⟩

/-! ### Witness -/

section Witness

variable {Z : Type u} [TopologicalSpace Z] [T2Space Z] [ParacompactSpace Z] (P : MPolyfold Z)

/-- For the trivial ep-groupoid of a tame `Z` the boundary source map is the identity of `bZ`. -/
theorem bSrc_trivial (hX : (trivial P).IsTame) (a : (trivial P).bMor hX) :
    (trivial P).bSrc hX a = a :=
  (isLiftOf_bSrc hX a).unique (isLiftOf_id _ a) (Eventually.of_forall fun _ => rfl)

/-- **Witness** for `theorem_7_6_9`: the trivial ep-groupoid of the tame quadrant
`[0, ∞)ⁿ ⊕ W` (`MPolyfold.quadrantPolyfold`) is tame; for `n ≥ 1` its boundary groupoid
`(bX, b𝐗)` is nonempty, and the corner `0` has exactly `n` preimages in `bX`. -/
theorem trivial_quadrant_witness (n : ℕ) (W : ScBanach) (hn : 1 ≤ n) :
    ∃ hX : (trivial (quadrantPolyfold n W)).IsTame,
      Nonempty ((trivial (quadrantPolyfold n W)).bObj hX) ∧
      Nonempty ((trivial (quadrantPolyfold n W)).bMor hX) ∧
      (bMap ((trivial (quadrantPolyfold n W)).cornerObj hX) ⁻¹'
        {⟨0, zero_mem_quadrant n W⟩}).encard = n :=
  ⟨isTame_trivial _ (quadrantPolyfold_isTame n W),
    quadrantPolyfold_tameBoundarySpace_nonempty n W hn,
    quadrantPolyfold_tameBoundarySpace_nonempty n W hn,
    quadrantPolyfold_encard_preimage n W⟩

end Witness

end EpGroupoid

end Polyfold
